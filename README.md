<!-- AQIDA_CONSTITUTIONAL_SCOPE: gate | CLAIM_BOUNDARY: release packaging of already recorded results; states nothing new | FALSIFICATION_TESTS: lake build, check_axioms.sh, verify_certificates.py -->

# A quadratic lower bound for real orthogonal representations of the graph of triples

Author: Babar Ahmed Khan. Draft of 26 November 2026. **Not peer reviewed.**

This folder holds the paper (LaTeX source and PDF), a Lean 4 formalisation of its main result, and
seven exact certificates for small cases, with a standalone script that re-checks them.

## The result in plain words

Give every 3-element subset of {1, ..., t} a non-zero real vector, and require two vectors to be
orthogonal whenever their subsets share exactly one element. How large must the dimension d of the
space be? The paper shows

    d  >=  floor(t/3)^2 / 5 .

This is a lower bound of the order (quadratic in t) asked for in Problem 1 of P. Hrubes and S. Iyer,
ECCC TR26-151 (2026). The same bound holds for complex vectors with the Hermitian inner product, and for
subspaces in place of vectors (projective representations).

## The Lean statement of `corollary_L_real`

Copied from `lean/TheoremL.lean`, lines 778 to 782 (the proof follows on the next lines of the file):

```lean
theorem corollary_L_real {t d : ℕ}
    (v : {A : Finset (Fin t) // A.card = 3} → EuclideanSpace ℝ (Fin d))
    (h_ne : ∀ A, v A ≠ 0)
    (h_orth : ∀ A B, (A.1 ∩ B.1).card = 1 → inner ℝ (v A) (v B) = 0) :
    (t / 3) ^ 2 ≤ 5 * d := by
```

Here `t / 3` is division of natural numbers (that is, floor(t/3)). The minimum dimension itself is not
defined in the Lean files; the theorem says that every valid family in dimension d satisfies the bound.

## Main Lean declarations

All in namespace `TheoremL`. Files: `lean/TheoremL.lean` (1065 lines) and
`lean/TheoremL_LayerRanks.lean` (1354 lines, whose first 1065 lines are `TheoremL.lean` byte for byte).
The statements in this table are machine-checked in Lean 4 (Lean 4.30.0-rc2, Mathlib tag v4.30.0-rc2),
subject to the conditions in "Verification status" below.

| declaration | file | statement, in words |
|---|---|---|
| `core_bound` | both | orthonormal r-frames on the points of [n]^3 in a real space E, orthogonal on points that agree in exactly one coordinate: `r * n ^ 2 ≤ 5 * finrank ℝ E` |
| `theorem_L_real` | both | unit vectors in ℝ^d on [n]^3, same orthogonality: `n ^ 2 ≤ 5 * d` |
| `theorem_L_real_nine` | both | the same with the weaker conclusion `n ^ 2 ≤ 9 * d` |
| `corollary_L_real` | both | non-zero vectors in ℝ^d on the 3-subsets of `Fin t`, orthogonal when two subsets share exactly one element: `(t / 3) ^ 2 ≤ 5 * d` |
| `corollary_L_real_nine` | both | the same with `9 * d` |
| `theorem_L_projective` | both | subspaces of dimension r of a real space on [n]^3: `r * n ^ 2 ≤ 5 * finrank ℝ E` |
| `theorem_L_complex_hermitian` | both | unit vectors in ℂ^d with the Hermitian product on [n]^3: `n ^ 2 ≤ 5 * d` |
| `theorem_L_projectors` | both | self-adjoint operators of rank r with vanishing products on adjacent points: `r * n ^ 2 ≤ 5 * D` |
| `theorem_L_projective_complex` | both | complex subspaces of dimension r on [n]^3: `r * n ^ 2 ≤ 5 * finrank ℂ E` |
| `hypotheses_satisfiable` | both | the hypotheses of `theorem_L_real` hold for some family, for every n (non-vacuity check) |
| `core_layer_ranks` | `TheoremL_LayerRanks.lean` | layer-rank form: `3 * (r * n ^ 3) ≤ 5 * ∑ i, ∑ a, finrank (layerSpan u i a)` |
| `theorem_L_real_layer_ranks` | `TheoremL_LayerRanks.lean` | layer-rank form for unit vectors in ℝ^d: `3 * n ^ 3 ≤ 5 * ∑ i, ∑ a, finrank (span of the vectors of layer (i, a))` |
| `theorem_L_real_layer_ranks_three` | `TheoremL_LayerRanks.lean` | the same with the weaker constant 3 |
| `corollary_L_complex_hermitian` | `TheoremL_LayerRanks.lean` | 3-subsets of `Fin t`, non-zero vectors in ℂ^d, Hermitian product: `(t / 3) ^ 2 ≤ 5 * d` |
| `corollary_L_projective_complex` | `TheoremL_LayerRanks.lean` | 3-subsets of `Fin t`, complex subspaces of dimension r: `r * (t / 3) ^ 2 ≤ 5 * finrank ℂ E` |
| `corollary_L_projective` | `TheoremL_LayerRanks.lean` | the real analogue of the previous line |
| `upper_bound_triples` | `TheoremL_LayerRanks.lean` | a valid family of non-zero vectors exists in `EuclideanSpace ℝ (Fin t × Fin t)` (dimension t^2) |

Together, `corollary_L_real` and `upper_bound_triples` give floor(t/3)^2 / 5 <= d <= t^2 for the least
dimension d of a real representation.

## How to verify

1. **Hashes.** `cd lean && sha256sum TheoremL.lean TheoremL_LayerRanks.lean` must print
   `3019bee14ed972d72cf0759bc36aca2c096a9d742649efff15afcbf06b3cef92` and
   `a1b16696a0fbef1aec580a126b5a9bd3ca6c0066129296af9e26c32c21adeefd` (recorded in `lean/SHA256SUMS.txt`).
2. **Lean.** Build and run the axiom check with the runbook below. `lean/check_axioms.sh` compiles both
   files, requires exit code 0 and that every `#print axioms` line lists only `propext`,
   `Classical.choice`, `Quot.sound` (no `sorryAx`), and requires the negative control
   `lean/NegativeControl.lean` (a planted `sorry`) to be reported as depending on `sorryAx`.
3. **Certificates.** `python certificates/verify_certificates.py` (Python 3, standard library only).
   It re-derives every cut of the seven certificates from the definitions and checks, in exact rational
   arithmetic, that the positive multipliers combine the cuts into `d - beta >= 0`. Its output on the
   authoring machine is `certificates/verify_output.txt`: all seven certificates pass, with
   integer bounds 11, 14, 16, 17, 19, 21, 23 for t = 10, ..., 16 (beta = 10.1337..., 13.6347...,
   15.3793..., 16.7398..., 18.4288..., 20.3160..., 22.2756...). The script does not check that the
   blocks are positive semidefinite for every representation; that is the argument of the paper,
   section "Linear bounds for small t". These certificates are checked by this script, not by Lean.
4. **Continuous integration.** `.github/workflows/lean_verify.yml` runs steps 2 and 3 on GitHub. Its first
   run (27 November 2026, run 1, commit `7592328`) succeeded in every step; the record is
   `lean/records/ci_run_1.md`.

## Clean-machine runbook

The workflow runs these commands on a fresh GitHub runner (first run 27 November 2026, all steps
succeeded; `lean/records/ci_run_1.md`). They have not been run by hand on a second personal machine.
Prerequisite: elan (the Lean toolchain manager) and git.

```bash
git clone https://github.com/aqida-ai/tr26-151-problem1.git tr26_151
cd tr26_151/lean
lake exe cache get
lake build
bash check_axioms.sh
```

## Verification status

- Lean: Lean 4 version 4.30.0-rc2, Mathlib tag v4.30.0-rc2. `TheoremL.lean` and
  `TheoremL_LayerRanks.lean` both compile with exit code 0 and no `sorry`; `#print axioms` gives
  `[propext, Classical.choice, Quot.sound]` for every main theorem; `NegativeControl.lean` (a planted
  `sorry`) is reported as depending on `sorryAx`. These checks were first run against an existing local
  Mathlib build, and then on a fresh GitHub Actions runner (27 November 2026, run 1, commit `7592328`):
  `lake exe cache get`, `lake build`, `check_axioms.sh` and the certificate verifier all succeeded. The
  Mathlib binaries of that run were downloaded from the Mathlib cache, not rebuilt from source.
- The proofs were read by isolated AI referees; the Lean statements were audited against the definitions
  of TR26-151 by isolated AI readers; no human mathematician has checked the work.

**AI-assistance disclosure.** The mathematics, computations and text were produced with an AI system
(Claude) under the direction of the author.

## What is not formalised

From the section "Formal verification" of the paper (`paper/PAPER_TR26_151_PROBLEM1_lean.tex`):

- The formal proof follows the paper's proof in the frame form and over ℝ; the complex statements are
  derived inside Lean from the real ones (a complex subspace of dimension r is a real subspace of
  dimension 2r), not by repeating the proof over ℂ.
- Not formalised: the definitions of ξ_f and χ_q and the inequality ξ_f ≤ χ_q quoted from the
  reference [MR] of the paper; the passage from complex projectors with P_A P_B = 0 to orthogonal ranges
  (formalised over ℝ only); the remark "More coordinates" (the case [n]^k, k ≥ 3); the statements of the
  section "The complex bilinear representation"; and all of the section "Linear bounds for small t"
  (its certificates are checked by exact-arithmetic scripts, see `certificates/`, not by Lean).
- No proof checker other than the Lean kernel was used.
- The minimum dimension d(t) is not defined in Lean (see above).

Note: the paper's Lean section refers to the folder `lean_theorem_l` and to record files there
(build record, axiom outputs, referee folders). In this package the Lean files are in `lean/` and the
build record with the recorded compiler outputs is in `lean/records/`. The referee folders are not part
of this package. `MANIFEST_before_records.md` is the first manifest, kept for the record; it can be left
out of a public copy.

## Contents

| path | what |
|---|---|
| `paper/` | `PAPER_TR26_151_PROBLEM1.tex` with its four input files (`_lean`, `_audit`, `_lit`, `_bib`) and the compiled PDF, copied unchanged |
| `lean/` | `lean-toolchain`, `lakefile.toml` (two libraries, `TheoremL` and `TheoremL_LayerRanks`; Mathlib `v4.30.0-rc2`), `lake-manifest.json` (commit pins of Mathlib and its dependencies, the ones the files were compiled against), the two Lean files, `NegativeControl.lean` (not built by default), `check_axioms.sh`, `SHA256SUMS.txt`, `records/` (local build record, recorded compiler outputs, record of the first CI run) |
| `certificates/` | `three_point_cert_t10_proj.json` ... `three_point_cert_t16_proj.json`, `verify_certificates.py`, `verify_output.txt` |
| `.github/workflows/lean_verify.yml` | CI workflow (first run 27 November 2026: success) |
| `MANIFEST.md` | size and SHA-256 of every file |

## Licences and citation

- Code (Lean files, scripts, workflow): MIT, see `LICENSE`.
- Paper text and PDF: CC BY 4.0, see `LICENSE-PAPER.md`.
- Citation metadata: `CITATION.cff`. The DOI is a TODO placeholder; a Zenodo DOI will be created by the
  owner later.
