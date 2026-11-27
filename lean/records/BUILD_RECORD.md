<!--
AQIDA_CONSTITUTIONAL_SCOPE: gate
THEORY_BINDING_MAP: CORE_LOGIC v3 A9/A10 (an energy has no cross-cancellation): Bessel's inequality is the only inequality used; section 2.2 (a zero carries its witness): N is the space of layer-wise linear relations. Other theory sources: not used.
CLAIM_BOUNDARY: machine check of the statements listed in this file and of nothing else.
FALSIFICATION_TESTS: the Lean kernel; `#print axioms`; NegativeControl.lean.
-->

# BUILD_RECORD : Lean 4 formalisation of Theorem L

STATUS: FINAL for this run (2026-11-26). All targets P1 to P5 and the optional complex projective
form compiled clean: zero `sorry`, exit code 0, no warning, and `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound` for every main theorem.

> **CORRECTION, 2026-11-26 (added after an isolated audit of `TheoremL.lean`; the text above and
> the sections 1 to 11 below are left as first written).**
> `BLUEPRINT.md`, section 1, lists under P5 "projectors as operators; and the layer-rank form".
> `TheoremL.lean` contains the projector form (`theorem_L_projectors`) but does NOT contain the
> layer-rank form. This record nevertheless says "All targets P1 to P5" (status line above) and
> "Nothing was abandoned and nothing was left out" (section 5). Both sentences are wrong on that
> point: the layer-rank form was overlooked in the first run (the blueprint names it but gives no
> statement for it), so P5 was only half done when those sentences were written.
> The layer-rank form now lives in a separate file, `TheoremL_LayerRanks.lean`, section 12:
> `core_layer_ranks`, `theorem_L_real_layer_ranks`, `theorem_L_real_layer_ranks_three`. That file
> compiles clean; see section 12 of this record. `TheoremL.lean` itself was not changed
> (sha256 `3019bee1…cef92`), so it still does not contain the layer-rank form.

What this record claims: the Lean kernel accepted the statements listed under "Targets".
What it does not claim: anything about novelty, priority, or the sharpness of the constant 5;
any human check; any run of the standalone build kit.

## 1. Versions

| item | value |
|---|---|
| Lean | `Lean (version 4.30.0-rc2, x86_64-w64-windows-gnu, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)` |
| toolchain file | `leanprover/lean4:v4.30.0-rc2` |
| Mathlib | tag `v4.30.0-rc2`, commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6` (read from `lake-manifest.json` of the existing project) |
| Mathlib location | `C:\AQiDA\Easy_Problems\aqida_lean_phase_math\.lake\packages\mathlib` (already compiled; used read-only; that project was not modified) |
| OS | Windows 11 Home 10.0.26300, Git Bash |

Nothing was installed, downloaded or updated. `lake build`, `lake update` and `lake exe cache get`
were not run.

## 2. Commands (exact)

Final compile of the development (run from `/c/AQiDA/Easy_Problems/aqida_lean_phase_math`):

```
lake env lean -M 2500 "C:/AQiDA/Easy_Problems/RESEARCH_NOTES/FINAL_SYNTHESIS_20261125/lean_theorem_l/TheoremL.lean"
```

Negative control (same directory):

```
lake env lean -M 2500 "C:/AQiDA/Easy_Problems/RESEARCH_NOTES/FINAL_SYNTHESIS_20261125/lean_theorem_l/NegativeControl.lean"
```

Hash: `sha256sum TheoremL.lean`. One Lean process at a time, always in the foreground. The memory
cap `-M 2500` was never exceeded; the fallback `-M 3000` was not needed.

`lake env lean` does not apply the `[leanOptions]` of the host project, so the file is checked
with Lean's default options plus its own `set_option autoImplicit false`.

## 3. Wall-clock times

Whole session: about 50 minutes (first file written 15:04, final compile 15:46, local time).

| run | content of `TheoremL.lean` | seconds | exit | result |
|---|---|---|---|---|
| 1 | P1 only (642 lines) | 160 | 0 | clean at the first attempt (cold import load) |
| 2 | P1 to P5 and the optional form, first version | 128 | 1 | P2, P3, P4, P5 clean at the first attempt; 4 linter warnings in one helper; 5 instance errors and one resulting unsolved-goal error, all in the optional theorem |
| 3 | helper simplified; local instance added | 16 | 1 | 1 instance error left, in the optional theorem |
| probes | `_probe_complex.lean` (two runs) | 17, 17 | 1 | diagnostic only |
| 4 | optional form through the type synonym `RealForm` | 17 | 1 | 2 errors, in the optional part |
| 5 | two ascriptions fixed | 17 | 0 | all nine main theorems clean |
| 5b | unused import removed | 16 | 0 | clean (sha256 `47ea9bc4…eb9c`, kept as `TheoremL_clean_before_sanity_section.lean`) |
| 6 | section 11 (sanity checks) added | 16 | 0 | clean at the first attempt |
| final | heading of section 4 corrected (comment only) | 16 | 0 | clean; this is the recorded run, see `axioms_output.txt` |
| negative control | `NegativeControl.lean` | 13 | 0 | `sorryAx` reported, see `negative_control_output.txt` |

The first import load took about 150 s; later runs took 13 to 17 s because the compiled Mathlib
files were in the operating-system file cache.

## 4. SHA-256

```
3019bee14ed972d72cf0759bc36aca2c096a9d742649efff15afcbf06b3cef92  TheoremL.lean   (1065 lines)
```

`axioms_output.txt` records the same hash before and after the final compile.

Other files, for reference:

```
875d72d4ab36dcc423a99b366066fc6cad037c9641bb9a06008bf5907d2f2a63  NegativeControl.lean
8610fe7a49cf93fcc272133a2ff252c4a09381ce2ad4557dfc401df8c54c372b  lakefile.toml
ce4c4e3d87434b9663f46de25ce34b48a0cf0d392e0a320a0787b4674a2d7b61  lean-toolchain
a630da03340a466d8fa3a14a2fd7e590c81e388787a8837ace075e1df1314433  BLUEPRINT.md (as read; not modified)
```

## 5. Targets

| target | priority | status | axioms printed |
|---|---|---|---|
| `core_bound` | P1 | compiled clean | propext, Classical.choice, Quot.sound |
| `theorem_L_real` | P1 | compiled clean | propext, Classical.choice, Quot.sound |
| `theorem_L_real_nine` | P1 | compiled clean | propext, Classical.choice, Quot.sound |
| `corollary_L_real` | P2 | compiled clean | propext, Classical.choice, Quot.sound |
| `corollary_L_real_nine` | P2 | compiled clean | propext, Classical.choice, Quot.sound |
| `theorem_L_projective` | P3 | compiled clean | propext, Classical.choice, Quot.sound |
| `theorem_L_complex_hermitian` | P4 | compiled clean | propext, Classical.choice, Quot.sound |
| `theorem_L_projectors` | P5 | compiled clean | propext, Classical.choice, Quot.sound |
| `theorem_L_projective_complex` (optional complex projective form) | after P4 | compiled clean | propext, Classical.choice, Quot.sound |
| `hypotheses_satisfiable` (extra, not a target) | none | compiled clean | propext, Classical.choice, Quot.sound |

Nothing was abandoned and nothing was left out. No target is stated with `sorry`.

Forbidden constructs in the final file: none. A text scan for `sorry`, `admit`, `axiom`,
`native_decide`, `unsafe`, `implemented_by`, `opaque` finds nothing. The only `set_option` is
`autoImplicit false`, which makes checking stricter. The file uses `decide` (kernel evaluation,
not `native_decide`) in `pair_one` and in the eight `example`s of section 11.

No mathematical gap was found in the blueprint. Every step of sections 2 and 3 went through.

## 6. Deviations from the blueprint

### 6.1 Statements

None in content. The six statements written out in section 1 of `BLUEPRINT.md` (`core_bound`,
`theorem_L_real`, `corollary_L_real`, `theorem_L_projective`, `theorem_L_complex_hermitian`,
`theorem_L_projectors`) appear with the same token sequence; only line breaks differ. The
definitions `Pt` and `AgreeOne` are the blueprint's. No notational adaptation to this Mathlib was
needed: `inner ℝ x y`, `⟂`, `.card`, `→L[ℝ]`, `IsSelfAdjoint` all parse as written.

This is checked by a script, not by eye: `check_statements_vs_blueprint.py` extracts the statements
from both files, normalises whitespace and compares them. Its output is `statements_check_output.txt`
(eight lines `IDENTICAL`, two lines for the constant-9 variants, then `ALL OK`). The script was
itself tested: with the constant 5 changed to 4 in a temporary copy it printed `DIFFERENT` for the
two statements concerned. The statement and the two definitions in `NegativeControl.lean` were
compared with those of `TheoremL.lean` in the same way and are identical.

- `theorem_L_real_nine` and `corollary_L_real_nine`: the blueprint says "same hypotheses"; they
  are written out in full, with conclusions `n ^ 2 ≤ 9 * d` and `(t / 3) ^ 2 ≤ 9 * d`.
- Optional complex projective form: the blueprint gives no name. It is `theorem_L_projective_complex`,
  with `E` a complex inner-product space, `[FiniteDimensional ℂ E]`, `V : Pt n → Submodule ℂ E`,
  `h_rank : ∀ p, Module.finrank ℂ (V p) = r`, `h_orth : ∀ p q, AgreeOne p q → V p ⟂ V q`
  (orthogonality for the Hermitian product), conclusion `r * n ^ 2 ≤ 5 * Module.finrank ℂ E`.

### 6.2 Proof route (no effect on any statement)

1. Blueprint 2.1. `N` is `LinearMap.ker (Phi u)` inside `EuclideanSpace ℝ (Pt n × Fin r)`. The
   algebra of 2.2 and 2.3 is done on plain coefficient functions `c : Pt n × Fin r → ℝ` under the
   predicate `InN` (the three families of layer relations); `inN_of_mem_ker` links the two.
2. Blueprint 2.3, step 3 (cross terms). Instead of the two-case computation, the splitting lemma
   is applied to `f x' y' = ⟪syn (x',y,z), syn (x,y',z)⟫` (lemma `cross_eq`). This gives
   `⟪a₁, a₂⟫ = ⟪syn p, a₂⟫ + ⟪a₁, syn p⟫ - ⟪syn p, syn p⟫ = W/2 + W/2 - W = 0`. Same content.
3. Blueprint 2.3, step 6 (counting). Proved by two uses of `sub_single_le_sum_sub`.
4. Blueprint 2.4 (Lemma D). The orthonormal basis of `N` is moved to the ambient space first
   (`exists_orthonormal_in_submodule`), so no norm or inner product is computed inside a subtype.
5. P3. The orthonormal family is `b p (Fin.cast _ k)` with `b p` from
   `exists_orthonormal_in_submodule`, instead of `OrthonormalBasis.reindex (finCongr _)`.
6. P4. The real structure is made explicit: `realify` sends `EuclideanSpace ℂ (Fin d)` to
   `EuclideanSpace ℝ (Fin d ⊕ Fin d)` (real parts, then imaginary parts), and
   `inner_realify : ⟪realify x, realify y⟫_ℝ = re ⟪x, y⟫_ℂ`. The blueprint suggested
   `InnerProductSpace.complexToReal`; Mathlib's own docstring says that structure makes a diamond
   with the inner product of `PiLp`, so it was avoided. The family is `pair (realify (u p))
   (realify (I • u p))`, as in the blueprint.
7. Optional complex projective form. Restriction of scalars is done through a type synonym
   `RealForm E` carrying only the real structure `re ⟪x, y⟫_ℂ`, and `realSub W` (the complex
   subspace as a real subspace). A first version with `letI := InnerProductSpace.rclikeToReal ℂ E`
   and `Submodule.restrictScalars` failed on instance resolution (`IsScalarTower ℝ ℂ _`); it is
   kept as `TheoremL_attempt3_letI_route.lean` and is not part of the result.

### 6.3 Additions not in the blueprint

- Section 11 of the file: eight `example`s checking `AgreeOne` on the cube of side 2 (adjacent
  exactly when one coordinate is shared), `ne_of_agreeOne`, and `hypotheses_satisfiable` (for every
  `n` the hypotheses of `theorem_L_real` hold for the standard basis vectors in dimension `n ^ 3`).
  These guard against a vacuous statement. They are not targets.
- `set_option autoImplicit false`.

### 6.4 A note on the mandated header

The header says "Bessel's inequality is the only inequality used". Precisely: Bessel's inequality
(`Orthonormal.sum_inner_products_le`, in `pointwise_bound`) is the only inequality between inner
products and norms. The file also uses the elementary fact that one term of a sum of non-negative
reals is at most the sum (`Finset.single_le_sum`, in `count3`, `sub_single_le_sum_sub`,
`ker_pointwise`), `Submodule.finrank_le` in rank-nullity, and order arithmetic on reals and
naturals. The binding-map text itself is taken from the task and from `BLUEPRINT.md`; it was not
re-derived from `CORE_LOGIC.md` in this run.

## 7. Declarations of `TheoremL.lean`

63 theorems, 15 definitions (one of them a structure), 3 instances, 8 examples. Namespace
`TheoremL`.

### Section 0: points and adjacency
| name | kind | meaning |
|---|---|---|
| `Pt` | abbrev | points of the cube: `Fin n × Fin n × Fin n` |
| `AgreeOne` | def | adjacency: the two points agree in exactly one coordinate |
| `agreeOne_z` | theorem | `(x,y,z)` and `(x',y',z)` are adjacent when `x ≠ x'`, `y ≠ y'` |
| `agreeOne_y` | theorem | `(x,y,z)` and `(x',y,z')` are adjacent when `x ≠ x'`, `z ≠ z'` |
| `agreeOne_x` | theorem | `(x,y,z)` and `(x,y',z')` are adjacent when `y ≠ y'`, `z ≠ z'` |

### Section 1: finite sums
| name | kind | meaning |
|---|---|---|
| `sum_split` | theorem | splitting lemma: a double sum vanishing off a cross is row plus column minus centre |
| `sub_single_le_sum_sub` | theorem | if `k' ≤ k` pointwise then `k a - k' a ≤ ∑ k - ∑ k'` |
| `count3` | theorem | counting step: three line sums of a non-negative function are at most the total plus twice the value at the point |
| `five_mul_le_two_of_sq` | theorem | `0 ≤ s` and `5 s² ≤ 2 s` give `5 s ≤ 2` |

### Section 2: the core algebra
| name | kind | meaning |
|---|---|---|
| `syn` | def | point synthesis `∑ k, c (p,k) • u p k` |
| `wt` | def | point weight `∑ k, c (p,k) ^ 2` |
| `wt_nonneg` | theorem | the weight is non-negative |
| `syn_add` | theorem | `syn` is additive in the coefficients |
| `syn_smul` | theorem | `syn` commutes with real scalars |
| `inner_u_syn_self` | theorem | `⟪u p l, syn p⟫ = c (p,l)` |
| `inner_u_syn_adj` | theorem | `⟪u p l, syn q⟫ = 0` for adjacent `p`, `q` |
| `inner_syn_left` | theorem | `⟪syn p, x⟫ = ∑ k, c (p,k) * ⟪u p k, x⟫` |
| `inner_syn_syn_adj` | theorem | `⟪syn p, syn q⟫ = 0` for adjacent `p`, `q` |
| `inner_syn_self` | theorem | `⟪syn p, syn p⟫ = wt p` |
| `a1`, `a2`, `a3` | defs | the line sums through a point in the three directions |
| `InN` | structure | the three families of layer relations (membership in `N` for a coefficient array) |
| `layer_eq` | theorem | one layer relation tested against a vector: row term plus column term equals centre term |
| `S2` | theorem | step S2: the three line sums tested against `u p l` are all `c (p,l) / 2` |
| `inner_syn_a1`, `inner_syn_a2`, `inner_syn_a3` | theorems | `⟪syn q, aᵢ q⟫ = wt q / 2` |
| `inner_a1_a1`, `inner_a2_a2`, `inner_a3_a3` | theorems | `⟪aᵢ, aᵢ⟫` is half the weight of the line |
| `cross_eq` | theorem | inner product of two sums whose terms are orthogonal off a cross |
| `pointwise_bound` | theorem | step PB in weight form: `5 * wt p ≤ 2 * ∑ q, wt q` (Bessel is used here) |

### Section 3: Lemma D
| name | kind | meaning |
|---|---|---|
| `exists_orthonormal_in_submodule` | theorem | a subspace contains an orthonormal family of `finrank` vectors |
| `lemma_D` | theorem | Lemma D: `5 vᵢ² ≤ 2 ‖v‖²` on `N` gives `5 * finrank N ≤ 2 * card ι` |

### Section 4: the map Φ, its kernel, rank-nullity
| name | kind | meaning |
|---|---|---|
| `Phi` | def | the three layer maps as one linear map on `EuclideanSpace ℝ (Pt n × Fin r)` |
| `inN_of_mem_ker` | theorem | an element of `ker Φ` satisfies the layer relations |
| `ker_pointwise` | theorem | `5 * (v i) ^ 2 ≤ 2 * ‖v‖ ^ 2` on `ker Φ` |
| `rn_bound` | theorem | (RN): `r * n ^ 3 ≤ finrank (ker Φ) + 3 * (n * finrank E)` |

### Section 5: main theorems (P1)
| name | kind | meaning |
|---|---|---|
| `core_bound` | theorem | **P1**: `r * n ^ 2 ≤ 5 * finrank ℝ E` |
| `orthonormal_fin_one` | theorem | a unit vector is an orthonormal family indexed by `Fin 1` |
| `theorem_L_real` | theorem | **P1**: unit vectors in `ℝ^d`, `n ^ 2 ≤ 5 * d` |
| `theorem_L_real_nine` | theorem | **P1**: the same with `9 * d` |

### Section 6: projective form (P3)
| name | kind | meaning |
|---|---|---|
| `theorem_L_projective` | theorem | **P3**: subspaces of dimension `r`, `r * n ^ 2 ≤ 5 * finrank ℝ E` |

### Section 7: the triple graph (P2)
| name | kind | meaning |
|---|---|---|
| `agreeOne_iff` | theorem | adjacency as a three-case disjunction |
| `emb3` | def | the 3-subset `{x, n + y, 2n + z}` of `Fin t`, with `n = t / 3` |
| `mem_emb3` | theorem | membership in `emb3` in terms of values |
| `card_emb3` | theorem | `emb3` has three elements |
| `inter_emb3_eq_singleton` | theorem | criterion for two such sets to meet in one given element |
| `card_inter_emb3` | theorem | adjacent points give sets meeting in exactly one element |
| `emb3S` | def | `emb3` as an element of `{A // A.card = 3}` |
| `norm_normalize` | theorem | `‖‖x‖⁻¹ • x‖ = 1` for `x ≠ 0` |
| `corollary_L_real` | theorem | **P2**: `(t / 3) ^ 2 ≤ 5 * d` |
| `corollary_L_real_nine` | theorem | **P2**: the same with `9 * d` |

### Section 8: complex Hermitian unit vectors (P4)
| name | kind | meaning |
|---|---|---|
| `pair` | def | the family `Fin 2 → F` with values `a`, `b` |
| `pair_zero`, `pair_one` | theorems | its two values |
| `norm_eq_one_of_inner_self` | theorem | `⟪a, a⟫ = 1` gives `‖a‖ = 1` |
| `orthonormal_pair` | theorem | two orthogonal unit vectors form an orthonormal family |
| `inner_pair_pair` | theorem | two pairs are orthogonal when the four inner products vanish |
| `realify` | def | real and imaginary parts: `EuclideanSpace ℂ (Fin d) → EuclideanSpace ℝ (Fin d ⊕ Fin d)` |
| `realify_inl`, `realify_inr` | theorems | the coordinates of `realify` |
| `real_inner_real` | theorem | the inner product of two real numbers is their product |
| `inner_realify` | theorem | `⟪realify x, realify y⟫_ℝ = re ⟪x, y⟫_ℂ` |
| `inner_realify_self` | theorem | `⟪realify x, realify x⟫_ℝ = ‖x‖ ^ 2` |
| `theorem_L_complex_hermitian` | theorem | **P4**: Hermitian unit vectors in `ℂ^d`, `n ^ 2 ≤ 5 * d` |

### Section 9: projectors (P5)
| name | kind | meaning |
|---|---|---|
| `theorem_L_projectors` | theorem | **P5**: self-adjoint operators of rank `r` with vanishing products, `r * n ^ 2 ≤ 5 * D` |

### Section 10: complex projective form (optional)
| name | kind | meaning |
|---|---|---|
| `RealForm` | def | type synonym: a complex space seen as a real one |
| `instNormedAddCommGroupRealForm` | instance | the norm of `E` on `RealForm E` |
| `instInnerProductSpaceRealForm` | instance | the real inner product `re ⟪x, y⟫_ℂ` |
| `realForm_inner` | theorem | that formula, as a statement |
| `instFiniteDimensionalRealForm` | instance | finite dimension over `ℝ` |
| `finrank_realForm` | theorem | `finrank ℝ (RealForm E) = 2 * finrank ℂ E` |
| `realSub` | def | a complex subspace as a real subspace of `RealForm E` |
| `mem_realSub` | theorem | membership is unchanged |
| `finrank_realSub` | theorem | `finrank ℝ (realSub W) = 2 * finrank ℂ W` |
| `realSub_isOrtho` | theorem | Hermitian-orthogonal subspaces stay orthogonal |
| `theorem_L_projective_complex` | theorem | **optional**: `r * n ^ 2 ≤ 5 * finrank ℂ E` |

### Section 11: sanity checks (not targets)
| name | kind | meaning |
|---|---|---|
| 8 × `example` | examples | on the cube of side 2, `(0,0,0)` is adjacent to `(1,1,0)`, `(1,0,1)`, `(0,1,1)` and to none of `(0,0,0)`, `(1,0,0)`, `(0,1,0)`, `(0,0,1)`, `(1,1,1)` |
| `ne_of_agreeOne` | theorem | adjacent points are distinct |
| `hypotheses_satisfiable` | theorem | the hypotheses of `theorem_L_real` hold for some family, for every `n` |

## 8. Negative control

`NegativeControl.lean` states `theorem_L_real` with the same statement (its own copies of `Pt` and
`AgreeOne`, namespace `TheoremLNegativeControl`) and proves it by `sorry`. Output, in
`negative_control_output.txt`:

```
warning: declaration uses `sorry`
'TheoremLNegativeControl.theorem_L_real' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

So the axiom check detects a faked proof. The exit code of that compile is 0: the exit code alone
does not detect `sorry`. The test is the axiom list.

During development, compile runs 2, 3 and 4 gave a second, unplanned confirmation: the optional
theorem had errors, and `#print axioms` listed `sorryAx` for it (see `_compile2.txt`,
`_compile3.txt`, `_compile4.txt`).

## 9. Standalone build kit

`lakefile.toml` (package `theorem_l`, Mathlib at `v4.30.0-rc2`, one `lean_lib` named `TheoremL`),
`lean-toolchain`, `README_BUILD.md`.

**The kit was NOT run on this machine.** No `lake build`, no `lake update`, no `lake exe cache get`.
Its expected output in `README_BUILD.md` is the output of the single-file compile recorded here.
`lean-toolchain` carries no header comment because the file format allows only the toolchain name.

## 10. Not done, not checked

- The standalone kit was not executed (previous section).
- No independent proof checker (for example an external re-check of exported proofs) was run. The
  evidence is the Lean kernel as invoked by `lean`, plus `#print axioms`.
- No human has read the Lean file.
- Non-vacuity is machine-checked only for the hypotheses of `theorem_L_real`
  (`hypotheses_satisfiable`), not separately for the other forms.
- The file says nothing about whether the constant 5 is best possible, and nothing about the
  literature.

## 11. Files in this folder

Deliverables: `TheoremL.lean`, `axioms_output.txt`, `NegativeControl.lean`,
`negative_control_output.txt`, `BUILD_RECORD.md`, `lakefile.toml`, `lean-toolchain`,
`README_BUILD.md`. Extra evidence: `check_statements_vs_blueprint.py`,
`statements_check_output.txt`. Working memory: `NOTES.md`. Input: `BLUEPRINT.md`, `_probe.lean`
(both present before this run, not modified).

Superseded or scratch files, kept because nothing is deleted in this folder. They are not
deliverables:

| file | what it is |
|---|---|
| `TheoremL_P1_snapshot.lean` | P1 only, clean (run 1), sha256 `ba0cae5b…0a7f` |
| `TheoremL_attempt2_with_errors.lean` | run 2: the optional theorem does NOT compile |
| `TheoremL_attempt3_letI_route.lean` | run 3: the optional theorem does NOT compile |
| `TheoremL_clean_before_sanity_section.lean` | run 5b, clean, without section 11, sha256 `47ea9bc4…eb9c` |
| `_compile1.txt` … `_compile6.txt` | raw compiler output of runs 1 to 6 |
| `_final_stdout.txt`, `_final_stdout_before_sanity_section.txt`, `_neg_stdout.txt` | raw outputs behind the two output files |
| `_probe_complex.lean`, `_probe_complex_out.txt` | instance-resolution probe; contains failing `have`s on purpose; proves nothing |

## 12. Follow-up of 2026-11-26: `TheoremL_LayerRanks.lean`

Added after the audit (see the correction near the top). Sections 1 to 11 describe the first run
and are unchanged. `TheoremL.lean` was not touched in the follow-up.

### 12.1 The file

`TheoremL_LayerRanks.lean` is a byte-for-byte copy of `TheoremL.lean` followed by three new
sections in the same namespace: 12 (layer ranks), 13 (triple graph: complex Hermitian and
projective forms), 14 (the elementary upper bound).

```
a1b16696a0fbef1aec580a126b5a9bd3ca6c0066129296af9e26c32c21adeefd  TheoremL_LayerRanks.lean   (1354 lines, 64096 bytes)
3019bee14ed972d72cf0759bc36aca2c096a9d742649efff15afcbf06b3cef92  TheoremL.lean              (1065 lines, 49218 bytes; unchanged)
```

Identity of the first 49218 bytes (lines 1 to 1065) with `TheoremL.lean`, commands and their
output as run in this folder:

```
$ cmp -n 49218 TheoremL.lean TheoremL_LayerRanks.lean
cmp exit code: 0                       (no output: no differing byte)
$ head -c 49218 TheoremL_LayerRanks.lean | sha256sum
3019bee14ed972d72cf0759bc36aca2c096a9d742649efff15afcbf06b3cef92 *-
$ head -n 1065 TheoremL_LayerRanks.lean | diff - TheoremL.lean
diff exit code: 0                      (no output: no differing line)
```

Both files have LF line endings and no CR byte.

### 12.2 Compile runs

Command, from `/c/AQiDA/Easy_Problems/aqida_lean_phase_math`:

```
lake env lean -M 2500 "C:/AQiDA/Easy_Problems/RESEARCH_NOTES/FINAL_SYNTHESIS_20261125/lean_theorem_l/TheoremL_LayerRanks.lean"
```

| run | seconds | exit | result |
|---|---|---|---|
| lr1 | 38 | 0 | clean at the first attempt, all seven new theorems (`_compile_lr1.txt`) |
| recorded | 52 | 0 | same file, same hash before and after; `axioms_output_layer_ranks.txt` |

No warning, no error, no `sorryAx`. There was no failed attempt, so there is no `_partial.lean` file.
Text scan of the file for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`,
`opaque`: nothing. The only `set_option` is `autoImplicit false` (in the copied part).

### 12.3 Targets of the follow-up

| target | origin | status | axioms printed |
|---|---|---|---|
| `coord`, `layerSpan` | definitions, first follow-up message | as given | (definitions) |
| `core_layer_ranks` | layer-rank form (blueprint P5, second half) | compiled clean | propext, Classical.choice, Quot.sound |
| `theorem_L_real_layer_ranks` | layer-rank form, unit vectors | compiled clean | propext, Classical.choice, Quot.sound |
| `theorem_L_real_layer_ranks_three` | the same with the weaker constant 3 | compiled clean | propext, Classical.choice, Quot.sound |
| `corollary_L_complex_hermitian` | A | compiled clean | propext, Classical.choice, Quot.sound |
| `corollary_L_projective_complex` | B | compiled clean | propext, Classical.choice, Quot.sound |
| `corollary_L_projective` | real analogue of B | compiled clean | propext, Classical.choice, Quot.sound |
| `upper_bound_triples` | C | compiled clean | propext, Classical.choice, Quot.sound |

### 12.4 Deviations

Statements: none. `check_followup_statements.py` compares the two definitions (bodies included)
and the seven statements with `FOLLOWUP_TARGETS.md`, up to whitespace; its output
`followup_statements_check_output.txt` has nine lines `IDENTICAL` and `ALL OK`. The script printed
`DIFFERENT` when the constant 5 of `core_layer_ranks` was changed to 4 in a temporary copy.
Limit of this check: `FOLLOWUP_TARGETS.md` is a transcription by hand of the statements in the
coordinator's two messages. In it, `theorem_L_real_layer_ranks_three` ("same hypotheses") is
written out in full, and `corollary_L_projective` is obtained from B by putting ℝ for ℂ.
No notational adaptation to this Mathlib was needed.

Proof route (the message left it open):

1. Layer ranks. `PhiR u` is `Phi u` with its codomain restricted to the product of the `3 n`
   layer spans; this is possible because each component of `Phi u v` lies in the layer span
   (`Phi_fst_mem`, `Phi_snd_fst_mem`, `Phi_snd_snd_mem`). Rank-nullity for `PhiR u` gives
   `finrank (range) + finrank (ker) = r n³`, the range has dimension at most the sum of the layer
   ranks (`finrank_PhiR_target`, `Fin.sum_univ_three`), and `5 * finrank (ker) ≤ 2 r n³` comes
   from `lemma_D` and `ker_pointwise`, both from the copied part, through
   `mem_ker_Phi_of_mem_ker_PhiR`. Then `3 r n³ ≤ 5 * finrank (range)`.
2. `theorem_L_real_layer_ranks`: `r = 1`, and `layerSpan_single` identifies the layer span with
   `Submodule.span ℝ (u '' {p | coord i p = a})`. The constant-3 form follows by arithmetic.
3. A: normalise with the scalar `((‖x‖⁻¹ : ℝ) : ℂ)`, then `theorem_L_complex_hermitian` and the
   embedding lemmas of `corollary_L_real` (`emb3S`, `card_inter_emb3`).
4. B and its real analogue: one line each from `theorem_L_projective_complex` and
   `theorem_L_projective`, with the same embedding.
5. C: the vector of a 3-subset `A` is the basis vector `EuclideanSpace.single (min' A, max' A) 1`.
   If two 3-subsets had the same minimum and maximum, these two distinct elements would lie in
   the intersection, which then has more than one element.

### 12.5 New declarations (lines 1066 to 1354)

19 theorems and 3 definitions.

| name | kind | meaning |
|---|---|---|
| `coord` | def | the `i`-th coordinate of a point, `i : Fin 3` |
| `layerSpan` | def | span of the vectors attached to the points of the layer `coord i = a` |
| `coord_zero`, `coord_one`, `coord_two` | theorems | `coord 0 p = p.1`, `coord 1 p = p.2.1`, `coord 2 p = p.2.2` |
| `syn_mem_layerSpan` | theorem | a point synthesis lies in each layer span through its point |
| `Phi_fst_mem`, `Phi_snd_fst_mem`, `Phi_snd_snd_mem` | theorems | each component of `Phi u v` lies in its layer span |
| `PhiR` | def | `Phi` with codomain the product of the layer spans |
| `mem_ker_Phi_of_mem_ker_PhiR` | theorem | `ker (PhiR u) ⊆ ker (Phi u)` |
| `finrank_PhiR_target` | theorem | the dimension of that product is the sum of the layer ranks |
| `core_layer_ranks` | theorem | **layer-rank form**: `3 * (r * n ^ 3) ≤ 5 * ∑ i, ∑ a, finrank (layerSpan u i a)` |
| `layerSpan_single` | theorem | for single vectors the layer span is the span of the image of the layer |
| `finrank_layerSpan_single` | theorem | the same, for the dimensions |
| `theorem_L_real_layer_ranks` | theorem | **layer-rank form**, unit vectors in `ℝ^d` |
| `theorem_L_real_layer_ranks_three` | theorem | **layer-rank form**, weaker constant 3 |
| `norm_normalize_complex` | theorem | normalising a non-zero vector of a complex space gives norm 1 |
| `corollary_L_complex_hermitian` | theorem | **A**: triple graph, Hermitian vectors, `(t / 3) ^ 2 ≤ 5 * d` |
| `corollary_L_projective_complex` | theorem | **B**: triple graph, complex subspaces of dimension `r` |
| `corollary_L_projective` | theorem | real analogue of B |
| `upper_bound_triples` | theorem | **C**: a valid family of non-zero vectors exists in dimension `t ^ 2` |

### 12.6 Not done in the follow-up

- The build kit was not changed: `lakefile.toml` still builds only the module `TheoremL`. On a
  clean machine the new file can be checked, after steps 2 and 3 of `README_BUILD.md`, with
  `lake env lean TheoremL_LayerRanks.lean` (expected: the seventeen lines of
  `axioms_output_layer_ranks.txt`). This was not executed either.
- No independent proof checker, no human review (as in section 10).
- No separate negative control was written for the new file; the control of section 8 concerns
  the same mechanism (`#print axioms`).

### 12.7 Files added in the follow-up

`TheoremL_LayerRanks.lean`, `axioms_output_layer_ranks.txt`, `FOLLOWUP_TARGETS.md`,
`check_followup_statements.py`, `followup_statements_check_output.txt`; raw outputs
`_compile_lr1.txt`, `_final_stdout_layer_ranks.txt`. The file `verify_by_main_session.txt` was
written by the coordinating session, not by this run.
