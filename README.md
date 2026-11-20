# Independent Verification Receipts: Alpöge (2026) Lean 4.33.1 Proof of RH and Dirichlet GRH

Independent end-to-end compilation, statement pinning, axiom audit, and second-kernel (Rust `nanoda_bin`) verification of Levent Alpöge's November 20, 2026 formalization of the Riemann Hypothesis and Generalized Riemann Hypothesis for Dirichlet L-functions (`https://alpo.ge/remark.pdf`, `https://alpo.ge/lean.tar.gz.part01`..`part14`).

## Summary of Results

| Check | Status | Key Receipt |
|---|---|---|
| Source archive provenance (`lean.tar.gz`, 14 parts joined, 239,275,554 bytes) | Verified | SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` (matches MIT's `math.mit.edu/~drew/grh/`) |
| Announcement PDF (`remark.pdf`) | Verified | SHA-256 `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d` |
| Unmodified stock Lean toolchain (`v4.33.1`, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) | Verified | Binary SHA-256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` |
| Upstream `mathlib4` dependency | Verified | Commit `0df444a360eaa60ab8c11dca51a86af692955474` (8,690 cached `.olean` files) |
| Full DAG compile (all `Main`-reachable modules) | PASS | 175,187 / 175,187 modules (17,374,215 lines), 0 failures, finished 2026-11-20 19:05:21 UTC |
| Sorted 175,187-file `.olean` manifest root | Verified | SHA-256 `248bb64b6f59ebcdb1298b3e9f47598f06e14a2da83cb4058f9fa99e79882bca` (`olean_sha256_manifest.txt.zst`) |
| `Main.olean` | Verified | SHA-256 `ce9a2006adda570c7404866ff3ceb4a7341c6c5d8ae7b56b6d8600b4c312d1ab` |
| Statement pin + `#print axioms` (`verify_main.lean`, stock Lean 4.33.1) | PASS | `rc=0` in 76.05 s; all 5 theorems inhabit unmodified Mathlib statements on strictly `[propext, Classical.choice, Quot.sound]` |
| Independent Rust kernel (`lean4export Main -- <all 5> \| nanoda_bin`, commit `0da9f98f`, 64 threads) | PASS | `exp_rc=0`, `nanoda_rc=0`; **1,484,729 declarations** across **61,571,290,481 bytes** (**1,080,769,494 lines**) checked with **0 errors**, strictly `propext`, `Quot.sound`, `Classical.choice` |

## What Was Checked

1. **Static archive audit**: Zero occurrences of `sorry`, `admit`, `sorryAx`, custom `axiom`, `native_decide`, `unsafe`, `opaque`, `implemented_by`, `csimp`, `@[extern`, `ofReduceBool`, `trustCompiler`, `debug.skipKernelTC`, `debug.byAsSorry`, `addDeclWithoutChecking`, `polyrith`, or Lean 4.33 `module` side-files across all 175,187 files.
2. **Direct stock Lean 4.33.1 compilation**: Invoked unmodified `lean` (`v4.33.1`) with exact `lakefile.toml` options (`--tstack=400000`, `-DautoImplicit=false`, `-DrelaxedAutoImplicit=false`, `-DmaxSynthPendingDepth=3`, `-Dpp.unicode.fun=true`, `-DmaxHeartbeats=4000000`, plus `-DsynthInstance.maxHeartbeats=400000` for `GroundTheory.LocalFields.*` and `GroundTheory.GlobalFields.*`, `-Dlinter.all=false`) using a critical-path DAG scheduler (`build_and_verify.py`) writing `.olean` files directly (avoiding Lake's ~943 GiB `.setup.json` overhead).
3. **Mathlib statement pinning (`verify_main.lean`)**: Typechecked `example : RiemannHypothesis := riemannHypothesis` and all four explicit Dirichlet L-function GRH statements directly against unmodified upstream Mathlib (`0df444a3`).
4. **Independent Rust kernel replay (`lean4export` v4.33.0 + `nanoda_bin` commit `0da9f98f`)**: Streamed all 5 theorems' transitive kernel proof closure (`61,571,290,481` bytes, `1,080,769,494` NDJSON lines, stream SHA-256 `4301ce4828d397c728e87f3e6a1251aa42abe5e12809bb9e0b73cc3d33072e7e`) directly into `nanoda_bin` configured with `unpermitted_axiom_hard_error: true` and `permitted_axioms: ["propext", "Classical.choice", "Quot.sound"]`. Result: `Checked 1484729 declarations with no errors`.

## Included Files

- `VERIFICATION_RESULT.txt`: Full verification output (manifest receipt, statement pin & `#print axioms`, and `nanoda_bin` Rust kernel output).
- `verify_main.lean`: Exact Mathlib statement-pin and `#print axioms` test file.
- `nanoda_all_five.json`: Exact JSON configuration passed to `nanoda_bin`.
- `build_and_verify.py`: Reproducible direct Lean 4.33.1 DAG builder and streaming multi-kernel verifier script.
- `olean_sha256_manifest.txt.zst`: Zstd-compressed sorted SHA-256 manifest of all 175,187 compiled `.olean` files (decompresses to SHA-256 `248bb64b6f59ebcdb1298b3e9f47598f06e14a2da83cb4058f9fa99e79882bca`).
- `SHA256SUMS.txt`: SHA-256 checksums for all receipt files and source artifacts.

## Caveat / Scope

This verifies at the machine-kernel level (both Lean's C++ kernel and the independent Rust `nanoda` kernel) that the five formal statements in `Main.lean` follow logically from Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) using upstream Mathlib's definitions of `RiemannHypothesis`, `riemannZeta`, and `DirichletCharacter.LFunction`. Note that GRH here refers specifically to Dirichlet L-functions (not general Dedekind zeta or automorphic L-functions). Compilation ran unsandboxed via direct `lean` invocations rather than `lake build`; the independent `nanoda` replay re-checks every exported proof term from scratch independent of how `.olean` files were scheduled.
