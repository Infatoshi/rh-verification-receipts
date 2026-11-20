#!/usr/bin/env python3
"""
Resumable, critical-path-scheduled direct Lean 4.33.1 builder & multi-kernel verifier
for alpo.ge's RH/GRH Lean formalization (all 175,187 reachable modules).
Parameterized via RH_BASE (default /root/rh-lean), RH_WORKERS (default 192), RH_LEAN_J (default 1).
"""
import concurrent.futures
import hashlib
import heapq
import itertools
import json
import os
import re
import resource
import shutil
import signal
import subprocess
import sys
import threading
import time
from collections import defaultdict, deque

BASE = os.environ.get("RH_BASE", "/root/rh-lean")
ROOT = os.path.join(BASE, "lean")
SRC = os.path.join(ROOT, "src")
OUT_LIB = os.path.join(ROOT, ".lake/build/lib/lean")
STATE_DIR = os.path.join(BASE, "run_main")
STATUS_JSON = os.path.join(STATE_DIR, "status.json")
FAIL_LOG = os.path.join(STATE_DIR, "failures.log")
VERIFY_OUT = os.path.join(STATE_DIR, "VERIFICATION_RESULT.txt")
LEAN_BIN = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean")
LEANCHK_BIN = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/leanchecker")
EXPORT_BIN = os.path.join(BASE, "tools/lean4export/.lake/build/bin/lean4export")
NANODA_BIN = os.path.join(BASE, "tools/nanoda_lib/target/release/nanoda_bin")

PKG_LIBS = [
    ".lake/packages/Cli/.lake/build/lib/lean",
    ".lake/packages/batteries/.lake/build/lib/lean",
    ".lake/packages/Qq/.lake/build/lib/lean",
    ".lake/packages/aesop/.lake/build/lib/lean",
    ".lake/packages/proofwidgets/.lake/build/lib/lean",
    ".lake/packages/importGraph/.lake/build/lib/lean",
    ".lake/packages/LeanSearchClient/.lake/build/lib/lean",
    ".lake/packages/plausible/.lake/build/lib/lean",
    ".lake/packages/mathlib/.lake/build/lib/lean",
    ".lake/build/lib/lean",
]

WORKERS = int(os.environ.get("RH_WORKERS", "192"))
LEAN_THREADS = int(os.environ.get("RH_LEAN_J", "1"))
SHARD_DIR = os.environ.get("RH_SHARD_DIR", "")
SHARD_COUNT = int(os.environ.get("RH_SHARD_COUNT", "0"))
NUMA_PIN = os.environ.get("RH_NUMA_PIN", "0") == "1"
MEM_PAUSE_GIB = 32.0
MEM_RESUME_GIB = 48.0
DISK_MIN_GIB = 20.0

_tls = threading.local()
_wid_lock = threading.Lock()
_wid_counter = itertools.count()


def _get_wid():
    wid = getattr(_tls, "wid", None)
    if wid is None:
        with _wid_lock:
            wid = next(_wid_counter)
        _tls.wid = wid
    return wid


def _worker_env(base_env, wid):
    if SHARD_DIR and SHARD_COUNT > 0:
        shard = wid % SHARD_COUNT
        sroot = os.path.join(SHARD_DIR, f"pkg_{shard}")
        merged = os.path.join(sroot, "_merged")
        e = base_env.copy()
        if os.path.isdir(merged):
            e["LEAN_PATH"] = f"{merged}:{os.path.join(ROOT, PKG_LIBS[-1])}"
        else:
            paths = [os.path.join(sroot, p.replace(".lake/packages/", "", 1)) for p in PKG_LIBS[:-1]]
            paths.append(os.path.join(ROOT, PKG_LIBS[-1]))
            e["LEAN_PATH"] = ":".join(paths)
        return e, shard
    return base_env, 0


def mem_avail_gib():
    with open("/proc/meminfo") as f:
        for ln in f:
            if ln.startswith("MemAvailable:"):
                return int(ln.split()[1]) / (1024 * 1024)
    return 999.0


def disk_free_gib(path=None):
    st = shutil.disk_usage(path or BASE)
    return st.free / (1024 ** 3)


def parse_main_dag():
    t0 = time.time()
    mod_to_path = {}
    for r, _, fs in os.walk(SRC):
        for fn in fs:
            if fn.endswith(".lean"):
                p = os.path.join(r, fn)
                mod = os.path.relpath(p, SRC)[:-5].replace(os.sep, ".")
                mod_to_path[mod] = p

    all_mods = set(mod_to_path.keys())
    imp_re = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)")
    deps = {}
    lines = {}
    for mod, p in mod_to_path.items():
        with open(p, "rb") as f:
            raw = f.read()
        lines[mod] = raw.count(b"\n") + (1 if raw and not raw.endswith(b"\n") else 0)
        text = raw.decode("utf-8", errors="replace")
        loc = []
        in_blk = 0
        for ln in text.splitlines():
            s = ln
            if "/-" in s or "-/" in s or in_blk > 0:
                out = []
                i = 0
                n = len(s)
                while i < n:
                    if s[i : i + 2] == "/-":
                        in_blk += 1
                        i += 2
                    elif s[i : i + 2] == "-/" and in_blk > 0:
                        in_blk -= 1
                        i += 2
                    else:
                        if in_blk == 0:
                            out.append(s[i])
                        i += 1
                s = "".join(out)
            s = s.split("--", 1)[0].strip()
            if not s or s == "module":
                continue
            mm = imp_re.match(s)
            if mm:
                imp = mm.group(1).replace("«", "").replace("»", "")
                if imp in all_mods:
                    loc.append(imp)
            else:
                break
        deps[mod] = list(dict.fromkeys(loc))

    vis = set()
    q = deque(["Main"])
    while q:
        u = q.popleft()
        if u in vis:
            continue
        vis.add(u)
        for v in deps[u]:
            if v not in vis:
                q.append(v)

    sub_deps = {u: [v for v in deps[u] if v in vis] for u in vis}
    rdeps = defaultdict(list)
    for u, ds in sub_deps.items():
        for v in ds:
            rdeps[v].append(u)

    outdeg = {u: len(rdeps[u]) for u in vis}
    rq = deque([u for u, d in outdeg.items() if d == 0])
    height = {}
    while rq:
        u = rq.popleft()
        height[u] = 1 + max((height[w] for w in rdeps[u] if w in height), default=0)
        for v in sub_deps[u]:
            outdeg[v] -= 1
            if outdeg[v] == 0:
                rq.append(v)

    assert len(height) == len(vis), f"Cycle detected! {len(height)} vs {len(vis)}"
    print(
        f"[init] Parsed Main DAG in {time.time()-t0:.2f}s: "
        f"{len(vis):,} modules, {sum(lines[u] for u in vis):,} lines, max_height={max(height.values())}",
        flush=True,
    )
    return vis, sub_deps, rdeps, lines, height


def olean_path(mod):
    return os.path.join(OUT_LIB, mod.replace(".", "/") + ".olean")


def ok_marker(mod):
    return os.path.join(OUT_LIB, mod.replace(".", "/") + ".olean.ok")


def is_already_built(mod):
    op = olean_path(mod)
    if not (os.path.exists(op) and os.path.getsize(op) > 0):
        return False
    return os.path.exists(ok_marker(mod)) or os.path.exists(op + ".hash")


def compile_one(mod, base_env):
    wid = _get_wid()
    env, shard = _worker_env(base_env, wid)
    rel = mod.replace(".", "/")
    src = os.path.join(SRC, rel + ".lean")
    op = olean_path(mod)
    tmp_op = f"{op}.tmp.{os.getpid()}.{threading.get_ident()}"
    os.makedirs(os.path.dirname(op), exist_ok=True)

    cmd = []
    if NUMA_PIN:
        # Even shards live on NUMA node 0 (0-95), odd shards on NUMA node 1 (96-191)
        cpus = "0-95" if (shard % 2 == 0) else "96-191"
        cmd = ["taskset", "-c", cpus]
    cmd += [
        LEAN_BIN,
        "--tstack=400000",
        "-R", SRC,
        "-j", str(LEAN_THREADS),
        src,
        "-o", tmp_op,
        "-DautoImplicit=false",
        "-DrelaxedAutoImplicit=false",
        "-DmaxSynthPendingDepth=3",
        "-Dpp.unicode.fun=true",
        "-DmaxHeartbeats=4000000",
        "-Dlinter.all=false",
    ]
    if mod.startswith("GroundTheory.LocalFields.") or mod.startswith("GroundTheory.GlobalFields."):
        cmd += ["-DsynthInstance.maxHeartbeats=400000"]

    t0 = time.perf_counter()
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)
    dt = time.perf_counter() - t0

    if p.returncode == 0 and os.path.exists(tmp_op) and os.path.getsize(tmp_op) > 0:
        os.replace(tmp_op, op)
        with open(ok_marker(mod), "wb") as f:
            f.write(b"1\n")
        return mod, 0, dt, os.path.getsize(op), ""
    else:
        if os.path.exists(tmp_op):
            try:
                os.remove(tmp_op)
            except OSError:
                pass
        err = (p.stdout + b"\n" + p.stderr).decode("utf-8", errors="replace")[-4000:]
        return mod, p.returncode, dt, 0, err


def _unlimit_stack():
    try:
        resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
    except Exception:
        pass


def _stream_export_nanoda(label, decls, env, nan_threads):
    nan_cfg = os.path.join(STATE_DIR, f"nanoda_{label}.json")
    with open(nan_cfg, "w") as f:
        json.dump(
            {
                "use_stdin": True,
                "num_threads": nan_threads,
                "stack_size_bytes": 67108864,
                "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
                "unpermitted_axiom_hard_error": True,
                "nat_extension": True,
                "string_extension": True,
                "print_success_message": True,
                "print_axioms": True,
                "pp_to_stdout": True,
            },
            f,
            indent=2,
        )
    exp_cmd = [EXPORT_BIN, "Main", "--"] + decls
    t0 = time.perf_counter()
    p_exp = subprocess.Popen(
        exp_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env, cwd=ROOT, preexec_fn=_unlimit_stack
    )
    p_nan = subprocess.Popen(
        [NANODA_BIN, nan_cfg], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        env=env, cwd=ROOT, preexec_fn=_unlimit_stack
    )
    stats = {"bytes": 0, "lines": 0, "sha": hashlib.sha256(), "eof_s": 0.0}

    def pump():
        try:
            while True:
                chunk = p_exp.stdout.read(1 << 20)
                if not chunk:
                    break
                stats["bytes"] += len(chunk)
                stats["lines"] += chunk.count(b"\n")
                stats["sha"].update(chunk)
                try:
                    p_nan.stdin.write(chunk)
                except BrokenPipeError:
                    break
        finally:
            stats["eof_s"] = time.perf_counter() - t0
            try:
                p_nan.stdin.close()
            except Exception:
                pass
            try:
                p_exp.stdout.close()
            except Exception:
                pass

    nan_out_chunks, nan_err_chunks, exp_err_chunks = [], [], []

    def _drain(stream, buf):
        try:
            while True:
                b = stream.read(65536)
                if not b:
                    break
                buf.append(b)
        finally:
            try:
                stream.close()
            except Exception:
                pass

    threads = [
        threading.Thread(target=pump),
        threading.Thread(target=_drain, args=(p_nan.stdout, nan_out_chunks)),
        threading.Thread(target=_drain, args=(p_nan.stderr, nan_err_chunks)),
        threading.Thread(target=_drain, args=(p_exp.stderr, exp_err_chunks)),
    ]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    p_nan.wait()
    p_exp.wait()
    nan_out = b"".join(nan_out_chunks)
    nan_err = b"".join(nan_err_chunks)
    exp_err = b"".join(exp_err_chunks)
    dt = time.perf_counter() - t0
    rc = p_exp.returncode or p_nan.returncode
    txt = (
        f"=== INDEPENDENT RUST KERNEL ({label}: {', '.join(decls)}) ===\n"
        f"exp_rc={p_exp.returncode} nanoda_rc={p_nan.returncode} elapsed={dt:.2f}s (export_eof={stats['eof_s']:.2f}s)\n"
        f"export_bytes={stats['bytes']:,} ({stats['bytes']/(1024**3):.2f} GiB) export_lines={stats['lines']:,}\n"
        f"export_sha256={stats['sha'].hexdigest()}\n"
        f"--- nanoda stdout ---\n{nan_out.decode('utf-8', 'replace')[-4000:]}\n"
        f"--- nanoda stderr ---\n{nan_err.decode('utf-8', 'replace')[-4000:]}\n"
        f"--- export stderr ---\n{exp_err.decode('utf-8', 'replace')[-2000:]}\n"
    )
    return rc, txt


def run_final_verification(env, vis):
    sections = []

    # 0. Sorted SHA-256 manifest of all compiled .oleans + toolchain binary
    t0 = time.perf_counter()
    lean_sha = subprocess.check_output(["sha256sum", LEAN_BIN], text=True).strip()
    lean_ver = subprocess.check_output([LEAN_BIN, "--version"], text=True).strip()

    def _hash_mod(m):
        op = olean_path(m)
        h = hashlib.sha256()
        with open(op, "rb") as f:
            while True:
                b = f.read(1 << 20)
                if not b:
                    break
                h.update(b)
        return f"{h.hexdigest()}  {m}"

    sorted_mods = sorted(vis)
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(64, WORKERS)) as ex:
        manifest_lines = list(ex.map(_hash_mod, sorted_mods))
    manifest_path = os.path.join(STATE_DIR, "olean_sha256_manifest.txt")
    manifest_text = "\n".join(manifest_lines) + "\n"
    with open(manifest_path, "w") as f:
        f.write(manifest_text)
    root_hash = hashlib.sha256(manifest_text.encode("utf-8")).hexdigest()
    sections.append(
        f"=== [0] MANIFEST & TOOLCHAIN RECEIPT ===\n"
        f"timestamp: {time.strftime('%Y-%m-%d %H:%M:%S %Z')}\n"
        f"lean_version: {lean_ver}\n"
        f"lean_bin_sha256: {lean_sha}\n"
        f"modules_hashed: {len(manifest_lines):,} in {time.perf_counter()-t0:.2f}s\n"
        f"olean_manifest_root_sha256: {root_hash}\n"
    )
    with open(VERIFY_OUT, "w") as f:
        f.write("\n".join(sections))
    print(sections[-1], flush=True)

    # 1. #print axioms + clean Mathlib-only statement pin via unmodified stock Lean 4.33.1
    vfile = os.path.join(STATE_DIR, "verify_main.lean")
    with open(vfile, "w") as f:
        f.write(
            "import Mathlib\n"
            "import Main\n"
            "\n"
            "-- Direct statement pin against unmodified upstream Mathlib definitions:\n"
            "example : RiemannHypothesis := riemannHypothesis\n"
            "example : ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2 :=\n"
            "  riemannZeta_eq_zero_re\n"
            "example : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),\n"
            "    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0 :=\n"
            "  LFunction_ne_zero_of_half_lt_re\n"
            "example : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),\n"
            "    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2 :=\n"
            "  LFunction_eq_zero_re\n"
            "example : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →\n"
            "    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2 :=\n"
            "  LFunction_eq_zero_re_of_isPrimitive\n"
            "\n"
            "#check @riemannHypothesis\n"
            "#print axioms riemannHypothesis\n"
            "#print axioms riemannZeta_eq_zero_re\n"
            "#print axioms LFunction_ne_zero_of_half_lt_re\n"
            "#print axioms LFunction_eq_zero_re\n"
            "#print axioms LFunction_eq_zero_re_of_isPrimitive\n"
        )
    t0 = time.perf_counter()
    p1 = subprocess.run(
        [LEAN_BIN, "--tstack=400000", "-R", SRC, vfile],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env, text=True, preexec_fn=_unlimit_stack
    )
    dt1 = time.perf_counter() - t0
    sha = subprocess.check_output(["sha256sum", olean_path("Main")], text=True).strip()
    sections.append(
        f"=== [1] STOCK LEAN 4.33.1 STATEMENT PIN & #print axioms ===\n"
        f"timestamp: {time.strftime('%Y-%m-%d %H:%M:%S %Z')}\n"
        f"rc={p1.returncode} elapsed={dt1:.2f}s\n"
        f"main_olean_sha256: {sha}\n"
        f"--- stdout ---\n{p1.stdout}\n--- stderr ---\n{p1.stderr}\n"
    )
    with open(VERIFY_OUT, "w") as f:
        f.write("\n".join(sections))
    print(sections[-1], flush=True)

    # 2. Independent Rust kernel (nanoda_bin): run RH-only and all-5 IN PARALLEL so RH clears ASAP!
    rc2 = 0
    if os.path.exists(EXPORT_BIN) and os.path.exists(NANODA_BIN):
        all_five = [
            "riemannHypothesis",
            "riemannZeta_eq_zero_re",
            "LFunction_ne_zero_of_half_lt_re",
            "LFunction_eq_zero_re",
            "LFunction_eq_zero_re_of_isPrimitive",
        ]
        nan_threads = min(64, max(16, WORKERS // 3))
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as vex:
            f_rh = vex.submit(_stream_export_nanoda, "rh_only", ["riemannHypothesis"], env, nan_threads)
            f_all = vex.submit(_stream_export_nanoda, "all_five", all_five, env, nan_threads)
            for fut in concurrent.futures.as_completed([f_rh, f_all]):
                r_i, txt_i = fut.result()
                rc2 = rc2 or r_i
                sections.append(txt_i)
                with open(VERIFY_OUT, "w") as f:
                    f.write("\n".join(sections))
                print(txt_i, flush=True)

    # 3. Built-in leanchecker --fresh Main (after fast receipts are already written!)
    rc3 = 0
    if os.path.exists(LEANCHK_BIN):
        t0 = time.perf_counter()
        p3 = subprocess.run(
            [LEANCHK_BIN, "--fresh", "Main"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env, text=True, cwd=ROOT, preexec_fn=_unlimit_stack
        )
        dt3 = time.perf_counter() - t0
        rc3 = p3.returncode
        sections.append(
            f"=== [3] BUILT-IN LEANCHECKER --fresh Main ===\n"
            f"rc={rc3} elapsed={dt3:.2f}s\n"
            f"--- stdout ---\n{p3.stdout[-4000:]}\n--- stderr ---\n{p3.stderr[-4000:]}\n"
        )
        with open(VERIFY_OUT, "w") as f:
            f.write("\n".join(sections))
        print(sections[-1], flush=True)

    return p1.returncode or rc2 or rc3


def main():
    os.makedirs(STATE_DIR, exist_ok=True)
    vis, sub_deps, rdeps, lines, height = parse_main_dag()
    total_mods = len(vis)

    env = os.environ.copy()
    env["LEAN_PATH"] = ":".join(os.path.join(ROOT, p) for p in PKG_LIBS)
    toolchain_bin = os.path.dirname(LEAN_BIN)
    env["PATH"] = f"{toolchain_bin}:{os.path.expanduser('~/.elan/bin')}:{env.get('PATH', '')}"

    pre_built = {u for u in vis if is_already_built(u)}
    indeg = {u: sum(1 for v in sub_deps[u] if v not in pre_built) for u in vis if u not in pre_built}
    ready = []
    for u, d in indeg.items():
        if d == 0:
            heapq.heappush(ready, (-height[u], -lines[u], u))

    print(
        f"[start] base={BASE} workers={WORKERS} lean-j={LEAN_THREADS} | total={total_mods:,} | "
        f"pre_built={len(pre_built):,} | remaining={len(indeg):,} | initial_ready={len(ready):,} | "
        f"MemAvail={mem_avail_gib():.1f}G | DiskFree={disk_free_gib():.1f}G",
        flush=True,
    )

    t_start = time.time()
    built_now = 0
    failed = {}
    retried = set()
    sum_worker_s = 0.0
    total_olean_bytes = 0
    slowest = []
    recent_completions = deque()
    stop_requested = False

    def handle_sig(signum, frame):
        nonlocal stop_requested
        stop_requested = True
        print(f"[signal] Received signal {signum}, draining in-flight workers...", flush=True)

    signal.signal(signal.SIGTERM, handle_sig)
    signal.signal(signal.SIGINT, handle_sig)

    last_log = t_start
    mem_paused = False
    disk_paused = False

    def write_status(state="running"):
        now = time.time()
        elapsed = max(1e-6, now - t_start)
        while recent_completions and now - recent_completions[0] > 60.0:
            recent_completions.popleft()
        roll_mps = len(recent_completions) / min(60.0, elapsed)
        avg_mps = built_now / elapsed
        done_total = len(pre_built) + built_now
        rem = total_mods - done_total - len(failed)
        eta_s = rem / roll_mps if roll_mps > 0.1 else (rem / avg_mps if avg_mps > 0.1 else -1)
        st = {
            "state": state,
            "pid": os.getpid(),
            "updated_at": time.strftime("%Y-%m-%d %H:%M:%S %Z"),
            "elapsed_s": round(elapsed, 1),
            "workers": WORKERS,
            "lean_j": LEAN_THREADS,
            "total_mods": total_mods,
            "pre_built": len(pre_built),
            "built_now": built_now,
            "done_total": done_total,
            "pct_done": round(100.0 * done_total / total_mods, 3),
            "failed_count": len(failed),
            "remaining": rem,
            "ready_queue": len(ready),
            "rolling_60s_mod_per_s": round(roll_mps, 2),
            "avg_mod_per_s": round(avg_mps, 2),
            "eta_hours": round(eta_s / 3600.0, 2) if eta_s >= 0 else None,
            "sum_worker_hours": round(sum_worker_s / 3600.0, 2),
            "olean_gib_written_now": round(total_olean_bytes / (1024 ** 3), 2),
            "mem_avail_gib": round(mem_avail_gib(), 1),
            "disk_free_gib": round(disk_free_gib(), 1),
            "mem_paused": mem_paused,
            "disk_paused": disk_paused,
            "slowest_top10": sorted(slowest, reverse=True)[:10],
        }
        tmp = STATUS_JSON + ".tmp"
        with open(tmp, "w") as f:
            json.dump(st, f, indent=2)
        os.replace(tmp, STATUS_JSON)
        return st

    with concurrent.futures.ThreadPoolExecutor(max_workers=WORKERS) as ex:
        futs = {}
        while (ready or futs) and not (stop_requested and not futs):
            ma = mem_avail_gib()
            df = disk_free_gib()
            if ma < MEM_PAUSE_GIB:
                mem_paused = True
            elif mem_paused and ma >= MEM_RESUME_GIB:
                mem_paused = False
            if df < DISK_MIN_GIB:
                disk_paused = True
                print(f"[DISK GUARD] Disk free={df:.1f}G < {DISK_MIN_GIB}G!", flush=True)
                stop_requested = True

            while ready and len(futs) < WORKERS and not stop_requested and not mem_paused and not disk_paused:
                _, _, mod = heapq.heappop(ready)
                futs[ex.submit(compile_one, mod, env)] = mod

            if not futs:
                if mem_paused:
                    time.sleep(1.0)
                    continue
                break

            done, _ = concurrent.futures.wait(futs.keys(), timeout=5.0, return_when=concurrent.futures.FIRST_COMPLETED)
            now = time.time()
            for fut in done:
                mod = futs.pop(fut)
                mod, rc, dt, sz, err = fut.result()
                sum_worker_s += dt
                if rc == 0:
                    built_now += 1
                    total_olean_bytes += sz
                    recent_completions.append(now)
                    if len(slowest) < 20 or dt > slowest[0][0]:
                        heapq.heappush(slowest, (round(dt, 2), mod, lines[mod]))
                        if len(slowest) > 20:
                            heapq.heappop(slowest)
                    for w in rdeps[mod]:
                        if w in indeg:
                            indeg[w] -= 1
                            if indeg[w] == 0:
                                heapq.heappush(ready, (-height[w], -lines[w], w))
                else:
                    if (rc < 0 or rc == 137) and mod not in retried:
                        retried.add(mod)
                        print(f"[retry] {mod} killed rc={rc} after {dt:.1f}s", flush=True)
                        heapq.heappush(ready, (-height[mod], -lines[mod], mod))
                    else:
                        failed[mod] = (rc, dt, err)
                        with open(FAIL_LOG, "a") as fl:
                            fl.write(f"\n=== FAIL {mod} (rc={rc}, {dt:.2f}s) ===\n{err}\n")
                        print(f"[FAIL] {mod} rc={rc} ({dt:.1f}s) | total_failed={len(failed)}", flush=True)

            if now - last_log >= 15.0:
                st = write_status("running")
                print(
                    f"[progress] {st['done_total']:,}/{total_mods:,} ({st['pct_done']:5.2f}%) | "
                    f"rate={st['rolling_60s_mod_per_s']:5.2f} mod/s (avg {st['avg_mod_per_s']:5.2f}) | "
                    f"in_flight={len(futs):3d} ready={len(ready):5d} fail={len(failed)} | "
                    f"ETA={st['eta_hours']}h | MemAvail={st['mem_avail_gib']}G DiskFree={st['disk_free_gib']}G",
                    flush=True,
                )
                last_log = now

    if not failed and (len(pre_built) + built_now == total_mods):
        print("[done] ALL 175,187 modules compiled! Running multi-kernel verification...", flush=True)
        write_status("verifying")
        vrc = run_final_verification(env, vis)
        write_status("verified_ok" if vrc == 0 else "verify_failed")
        sys.exit(vrc)
    else:
        st = write_status("stopped" if stop_requested else "failed")
        print(f"[finished-incomplete] state={st['state']} done={st['done_total']:,}/{total_mods:,} failed={len(failed)}", flush=True)
        sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
