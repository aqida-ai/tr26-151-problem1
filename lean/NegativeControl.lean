import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-
AQIDA_CONSTITUTIONAL_SCOPE: gate
THEORY_BINDING_MAP: CORE_LOGIC v3 A9/A10 (an energy has no cross-cancellation): Bessel's inequality is the only inequality used; section 2.2 (a zero carries its witness): N is the space of layer-wise linear relations. Other theory sources: not used.
CLAIM_BOUNDARY: machine check of the statements listed in BUILD_RECORD.md and of nothing else.
FALSIFICATION_TESTS: the Lean kernel; `#print axioms`; NegativeControl.lean.

NEGATIVE CONTROL. This file proves NOTHING. It states `theorem_L_real` with exactly the statement
used in `TheoremL.lean` and "proves" it by `sorry` on purpose. The expected result is that
`#print axioms` reports `sorryAx`. This shows that the axiom check used for `TheoremL.lean` does
detect a faked proof. Never import this file and never cite it as evidence for the theorem.
-/

set_option autoImplicit false

namespace TheoremLNegativeControl

/-- Points of the cube `[n]^3` (same definition as in `TheoremL.lean`). -/
abbrev Pt (n : ℕ) := Fin n × Fin n × Fin n

/-- Two points are adjacent when they agree in exactly one coordinate (same definition as in
`TheoremL.lean`). -/
def AgreeOne {n : ℕ} (p q : Pt n) : Prop :=
  (if p.1 = q.1 then 1 else 0) + (if p.2.1 = q.2.1 then 1 else 0)
    + (if p.2.2 = q.2.2 then 1 else 0) = (1 : ℕ)

/-- PLANTED FAKE: the statement of `theorem_L_real`, with `sorry` in place of a proof. -/
theorem theorem_L_real {n d : ℕ} (u : Pt n → EuclideanSpace ℝ (Fin d))
    (h_unit : ∀ p, ‖u p‖ = 1)
    (h_orth : ∀ p q, AgreeOne p q → inner ℝ (u p) (u q) = 0) :
    n ^ 2 ≤ 5 * d := by
  sorry

end TheoremLNegativeControl

#print axioms TheoremLNegativeControl.theorem_L_real
