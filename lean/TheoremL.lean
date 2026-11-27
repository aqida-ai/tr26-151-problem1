import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

/-
AQIDA_CONSTITUTIONAL_SCOPE: gate
THEORY_BINDING_MAP: CORE_LOGIC v3 A9/A10 (an energy has no cross-cancellation): Bessel's inequality is the only inequality used; section 2.2 (a zero carries its witness): N is the space of layer-wise linear relations. Other theory sources: not used.
CLAIM_BOUNDARY: machine check of the statements listed in BUILD_RECORD.md and of nothing else.
FALSIFICATION_TESTS: the Lean kernel; `#print axioms`; NegativeControl.lean.
-/

set_option autoImplicit false

namespace TheoremL

/-! ## 0. Points and adjacency -/

/-- Points of the cube `[n]^3`. -/
abbrev Pt (n : ℕ) := Fin n × Fin n × Fin n

/-- Two points are adjacent when they agree in exactly one coordinate. -/
def AgreeOne {n : ℕ} (p q : Pt n) : Prop :=
  (if p.1 = q.1 then 1 else 0) + (if p.2.1 = q.2.1 then 1 else 0)
    + (if p.2.2 = q.2.2 then 1 else 0) = (1 : ℕ)

/-- Two points of a layer `z = const` that differ in both other coordinates are adjacent. -/
theorem agreeOne_z {n : ℕ} {x x' y y' z : Fin n} (hx : x ≠ x') (hy : y ≠ y') :
    AgreeOne (x, y, z) (x', y', z) := by
  simp [AgreeOne, hx, hy]

/-- Two points of a layer `y = const` that differ in both other coordinates are adjacent. -/
theorem agreeOne_y {n : ℕ} {x x' y z z' : Fin n} (hx : x ≠ x') (hz : z ≠ z') :
    AgreeOne (x, y, z) (x', y, z') := by
  simp [AgreeOne, hx, hz]

/-- Two points of a layer `x = const` that differ in both other coordinates are adjacent. -/
theorem agreeOne_x {n : ℕ} {x y y' z z' : Fin n} (hy : y ≠ y') (hz : z ≠ z') :
    AgreeOne (x, y, z) (x, y', z') := by
  simp [AgreeOne, hy, hz]

/-! ## 1. Finite sums: the splitting lemma and the counting step -/

section FiniteSums

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Splitting lemma (blueprint 2.2): a double sum whose terms vanish off the cross through
`(x, y)` is the sum over the row plus the sum over the column minus the centre. -/
theorem sum_split (f : α → β → ℝ) (x : α) (y : β)
    (h : ∀ x' y', x' ≠ x → y' ≠ y → f x' y' = 0) :
    ∑ x', ∑ y', f x' y' = ∑ y', f x y' + ∑ x', f x' y - f x y := by
  have h1 : ∑ x', (∑ y', f x' y' - f x' y) = ∑ y', f x y' - f x y := by
    apply Fintype.sum_eq_single x
    intro x' hx'
    rw [sub_eq_zero]
    apply Fintype.sum_eq_single y
    intro y' hy'
    exact h x' y' hx' hy'
  rw [Finset.sum_sub_distrib] at h1
  linarith

/-- If `k' ≤ k` pointwise, the difference of the sums dominates each single difference. -/
theorem sub_single_le_sum_sub (k k' : α → ℝ) (hk : ∀ b, k' b ≤ k b) (a : α) :
    k a - k' a ≤ ∑ b, k b - ∑ b, k' b := by
  have h3 : k a - k' a ≤ ∑ b, (k b - k' b) :=
    Finset.single_le_sum (f := fun b => k b - k' b) (fun b _ => sub_nonneg.mpr (hk b))
      (Finset.mem_univ a)
  have h2 : ∑ b, (k b - k' b) = ∑ b, k b - ∑ b, k' b := Finset.sum_sub_distrib _ _
  linarith

end FiniteSums

/-- Counting step (blueprint 2.3, step 6): the three lines through a point of the cube meet only
in that point, so the three line sums of a non-negative function are at most the total sum plus
twice the value at the point. -/
theorem count3 {n : ℕ} (g : Pt n → ℝ) (hg : ∀ q, 0 ≤ g q) (x y z : Fin n) :
    ∑ x', g (x', y, z) + ∑ y', g (x, y', z) + ∑ z', g (x, y, z')
      ≤ ∑ q, g q + 2 * g (x, y, z) := by
  have hT : ∑ q, g q = ∑ x', ∑ y', ∑ z', g (x', y', z') := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x' _
    rw [Fintype.sum_prod_type]
  have h1 : (∑ y', ∑ z', g (x, y', z')) - g (x, y, z)
      ≤ ∑ x', ∑ y', ∑ z', g (x', y', z') - ∑ x', g (x', y, z) :=
    sub_single_le_sum_sub (fun x' => ∑ y', ∑ z', g (x', y', z')) (fun x' => g (x', y, z))
      (fun x' => by
        have e1 : g (x', y, z) ≤ ∑ z', g (x', y, z') :=
          Finset.single_le_sum (f := fun z' => g (x', y, z')) (fun z' _ => hg _)
            (Finset.mem_univ z)
        have e2 : ∑ z', g (x', y, z') ≤ ∑ y', ∑ z', g (x', y', z') :=
          Finset.single_le_sum (f := fun y' => ∑ z', g (x', y', z'))
            (fun y' _ => Finset.sum_nonneg (fun z' _ => hg _)) (Finset.mem_univ y)
        exact le_trans e1 e2) x
  have h2 : (∑ z', g (x, y, z')) - g (x, y, z)
      ≤ ∑ y', ∑ z', g (x, y', z') - ∑ y', g (x, y', z) :=
    sub_single_le_sum_sub (fun y' => ∑ z', g (x, y', z')) (fun y' => g (x, y', z))
      (fun y' => Finset.single_le_sum (f := fun z' => g (x, y', z')) (fun z' _ => hg _)
        (Finset.mem_univ z)) y
  rw [hT]
  linarith

/-- From `5 s² ≤ 2 s` and `s ≥ 0` one gets `5 s ≤ 2`. -/
theorem five_mul_le_two_of_sq {s : ℝ} (hs0 : 0 ≤ s) (h : 5 * s ^ 2 ≤ 2 * s) : 5 * s ≤ 2 := by
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    norm_num
  · have h5 : 5 * s * s ≤ 2 * s := by
      have e : 5 * s * s = 5 * s ^ 2 := by ring
      rw [e]
      exact h
    exact le_of_mul_le_mul_right h5 hpos

/-! ## 2. The core algebra on coefficient arrays -/

section Core

variable {n r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Point synthesis: the vector `∑ k, c (p, k) • u p k`. -/
noncomputable def syn (u : Pt n → Fin r → E) (c : Pt n × Fin r → ℝ) (p : Pt n) : E :=
  ∑ k, c (p, k) • u p k

/-- Point weight: `∑ k, c (p, k) ^ 2`. -/
noncomputable def wt (c : Pt n × Fin r → ℝ) (p : Pt n) : ℝ := ∑ k, c (p, k) ^ 2

theorem wt_nonneg (c : Pt n × Fin r → ℝ) (p : Pt n) : 0 ≤ wt c p := by
  unfold wt
  exact Finset.sum_nonneg (fun k _ => sq_nonneg _)

theorem syn_add (u : Pt n → Fin r → E) (c c' : Pt n × Fin r → ℝ) (p : Pt n) :
    syn u (c + c') p = syn u c p + syn u c' p := by
  unfold syn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Pi.add_apply, add_smul]

theorem syn_smul (u : Pt n → Fin r → E) (a : ℝ) (c : Pt n × Fin r → ℝ) (p : Pt n) :
    syn u (a • c) p = a • syn u c p := by
  unfold syn
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Pi.smul_apply, smul_eq_mul, mul_smul]

/-- (F1) `⟪u p l, syn p⟫ = c (p, l)` by orthonormality of `u p`. -/
theorem inner_u_syn_self (u : Pt n → Fin r → E) (h_on : ∀ p, Orthonormal ℝ (u p))
    (c : Pt n × Fin r → ℝ) (p : Pt n) (l : Fin r) :
    inner ℝ (u p l) (syn u c p) = c (p, l) := by
  unfold syn
  exact (h_on p).inner_right_fintype (fun k => c (p, k)) l

/-- (F2) `⟪u p l, syn q⟫ = 0` when `p`, `q` are adjacent. -/
theorem inner_u_syn_adj (u : Pt n → Fin r → E)
    (h_orth : ∀ p q, AgreeOne p q → ∀ k l, inner ℝ (u p k) (u q l) = 0)
    (c : Pt n × Fin r → ℝ) {p q : Pt n} (hpq : AgreeOne p q) (l : Fin r) :
    inner ℝ (u p l) (syn u c q) = 0 := by
  unfold syn
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [inner_smul_right, h_orth p q hpq l k, mul_zero]

/-- (F3) expansion of the left factor. -/
theorem inner_syn_left (u : Pt n → Fin r → E) (c : Pt n × Fin r → ℝ) (p : Pt n) (x : E) :
    inner ℝ (syn u c p) x = ∑ k, c (p, k) * inner ℝ (u p k) x := by
  unfold syn
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro k _
  rw [real_inner_smul_left]

/-- (F4) `⟪syn p, syn q⟫ = 0` when `p`, `q` are adjacent. -/
theorem inner_syn_syn_adj (u : Pt n → Fin r → E)
    (h_orth : ∀ p q, AgreeOne p q → ∀ k l, inner ℝ (u p k) (u q l) = 0)
    (c : Pt n × Fin r → ℝ) {p q : Pt n} (hpq : AgreeOne p q) :
    inner ℝ (syn u c p) (syn u c q) = 0 := by
  rw [inner_syn_left]
  apply Finset.sum_eq_zero
  intro k _
  rw [inner_u_syn_adj u h_orth c hpq k, mul_zero]

/-- (F5) `⟪syn p, syn p⟫ = wt p`. -/
theorem inner_syn_self (u : Pt n → Fin r → E) (h_on : ∀ p, Orthonormal ℝ (u p))
    (c : Pt n × Fin r → ℝ) (p : Pt n) :
    inner ℝ (syn u c p) (syn u c p) = wt c p := by
  rw [inner_syn_left]
  unfold wt
  apply Finset.sum_congr rfl
  intro k _
  rw [inner_u_syn_self u h_on c p k, sq]

/-- Line sum through `p` in the first direction. -/
noncomputable def a1 (u : Pt n → Fin r → E) (c : Pt n × Fin r → ℝ) (p : Pt n) : E :=
  ∑ x', syn u c (x', p.2.1, p.2.2)

/-- Line sum through `p` in the second direction. -/
noncomputable def a2 (u : Pt n → Fin r → E) (c : Pt n × Fin r → ℝ) (p : Pt n) : E :=
  ∑ y', syn u c (p.1, y', p.2.2)

/-- Line sum through `p` in the third direction. -/
noncomputable def a3 (u : Pt n → Fin r → E) (c : Pt n × Fin r → ℝ) (p : Pt n) : E :=
  ∑ z', syn u c (p.1, p.2.1, z')

/-- Membership in the space `N` of blueprint 2.1: the restriction of the coefficient array to
every layer (in each of the three directions) is a linear relation of that layer. -/
structure InN (u : Pt n → Fin r → E) (c : Pt n × Fin r → ℝ) : Prop where
  hz : ∀ z, ∑ x', ∑ y', syn u c (x', y', z) = 0
  hy : ∀ y, ∑ x', ∑ z', syn u c (x', y, z') = 0
  hx : ∀ x, ∑ y', ∑ z', syn u c (x, y', z') = 0

/-- One layer relation, tested against a vector `e` that is orthogonal to all terms off the cross
through `(x, y)`. -/
theorem layer_eq {α β : Type*} [Fintype α] [Fintype β] (e : E) (g : α → β → E) (x : α) (y : β)
    (hsum : ∑ x', ∑ y', g x' y' = 0)
    (hvan : ∀ x' y', x' ≠ x → y' ≠ y → inner ℝ e (g x' y') = 0) :
    inner ℝ e (∑ y', g x y') + inner ℝ e (∑ x', g x' y) = inner ℝ e (g x y) := by
  have h0 : inner ℝ e (∑ x', ∑ y', g x' y') = 0 := by
    rw [hsum, inner_zero_right]
  have h1 : ∑ x', ∑ y', inner ℝ e (g x' y') = 0 := by
    rw [← h0, inner_sum]
    apply Finset.sum_congr rfl
    intro x' _
    rw [inner_sum]
  have h2 : ∑ x', ∑ y', inner ℝ e (g x' y')
      = ∑ y', inner ℝ e (g x y') + ∑ x', inner ℝ e (g x' y) - inner ℝ e (g x y) :=
    sum_split (fun x' y' => inner ℝ e (g x' y')) x y hvan
  rw [inner_sum, inner_sum]
  linarith

/-- Step S2 (blueprint 2.2): the three line sums tested against `u p l` are all `c (p, l) / 2`. -/
theorem S2 (u : Pt n → Fin r → E) (h_on : ∀ p, Orthonormal ℝ (u p))
    (h_orth : ∀ p q, AgreeOne p q → ∀ k l, inner ℝ (u p k) (u q l) = 0)
    (c : Pt n × Fin r → ℝ) (hc : InN u c) (x y z : Fin n) (l : Fin r) :
    inner ℝ (u (x, y, z) l) (a1 u c (x, y, z)) = c ((x, y, z), l) / 2 ∧
    inner ℝ (u (x, y, z) l) (a2 u c (x, y, z)) = c ((x, y, z), l) / 2 ∧
    inner ℝ (u (x, y, z) l) (a3 u c (x, y, z)) = c ((x, y, z), l) / 2 := by
  have hself : inner ℝ (u (x, y, z) l) (syn u c (x, y, z)) = c ((x, y, z), l) :=
    inner_u_syn_self u h_on c (x, y, z) l
  have ez : inner ℝ (u (x, y, z) l) (∑ y', syn u c (x, y', z))
      + inner ℝ (u (x, y, z) l) (∑ x', syn u c (x', y, z))
      = inner ℝ (u (x, y, z) l) (syn u c (x, y, z)) :=
    layer_eq (u (x, y, z) l) (fun x' y' => syn u c (x', y', z)) x y (hc.hz z)
      (fun x' y' hx' hy' =>
        inner_u_syn_adj u h_orth c (agreeOne_z (Ne.symm hx') (Ne.symm hy')) l)
  have ey : inner ℝ (u (x, y, z) l) (∑ z', syn u c (x, y, z'))
      + inner ℝ (u (x, y, z) l) (∑ x', syn u c (x', y, z))
      = inner ℝ (u (x, y, z) l) (syn u c (x, y, z)) :=
    layer_eq (u (x, y, z) l) (fun x' z' => syn u c (x', y, z')) x z (hc.hy y)
      (fun x' z' hx' hz' =>
        inner_u_syn_adj u h_orth c (agreeOne_y (Ne.symm hx') (Ne.symm hz')) l)
  have ex : inner ℝ (u (x, y, z) l) (∑ z', syn u c (x, y, z'))
      + inner ℝ (u (x, y, z) l) (∑ y', syn u c (x, y', z))
      = inner ℝ (u (x, y, z) l) (syn u c (x, y, z)) :=
    layer_eq (u (x, y, z) l) (fun y' z' => syn u c (x, y', z')) y z (hc.hx x)
      (fun y' z' hy' hz' =>
        inner_u_syn_adj u h_orth c (agreeOne_x (Ne.symm hy') (Ne.symm hz')) l)
  have d1 : a1 u c (x, y, z) = ∑ x', syn u c (x', y, z) := rfl
  have d2 : a2 u c (x, y, z) = ∑ y', syn u c (x, y', z) := rfl
  have d3 : a3 u c (x, y, z) = ∑ z', syn u c (x, y, z') := rfl
  rw [d1, d2, d3]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- (F6) `⟪syn q, a1 q⟫ = wt q / 2`. -/
theorem inner_syn_a1 (u : Pt n → Fin r → E) (h_on : ∀ p, Orthonormal ℝ (u p))
    (h_orth : ∀ p q, AgreeOne p q → ∀ k l, inner ℝ (u p k) (u q l) = 0)
    (c : Pt n × Fin r → ℝ) (hc : InN u c) (x y z : Fin n) :
    inner ℝ (syn u c (x, y, z)) (a1 u c (x, y, z)) = wt c (x, y, z) / 2 := by
  rw [inner_syn_left]
  unfold wt
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [(S2 u h_on h_orth c hc x y z k).1]
  ring

/-- (F6) `⟪syn q, a2 q⟫ = wt q / 2`. -/
theorem inner_syn_a2 (u : Pt n → Fin r → E) (h_on : ∀ p, Orthonormal ℝ (u p))
    (h_orth : ∀ p q, AgreeOne p q → ∀ k l, inner ℝ (u p k) (u q l) = 0)
    (c : Pt n × Fin r → ℝ) (hc : InN u c) (x y z : Fin n) :
    inner ℝ (syn u c (x, y, z)) (a2 u c (x, y, z)) = wt c (x, y, z) / 2 := by
  rw [inner_syn_left]
  unfold wt
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [(S2 u h_on h_orth c hc x y z k).2.1]
  ring

/-- (F6) `⟪syn q, a3 q⟫ = wt q / 2`. -/
theorem inner_syn_a3 (u : Pt n → Fin r → E) (h_on : ∀ p, Orthonormal ℝ (u p))
    (h_orth : ∀ p q, AgreeOne p q → ∀ k l, inner ℝ (u p k) (u q l) = 0)
    (c : Pt n × Fin r → ℝ) (hc : InN u c) (x y z : Fin n) :
    inner ℝ (syn u c (x, y, z)) (a3 u c (x, y, z)) = wt c (x, y, z) / 2 := by
  rw [inner_syn_left]
  unfold wt
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [(S2 u h_on h_orth c hc x y z k).2.2]
  ring

/-- Step PB.2: `⟪a1, a1⟫` is half the weight of the line. -/
theorem inner_a1_a1 (u : Pt n → Fin r → E) (h_on : ∀ p, Orthonormal ℝ (u p))
    (h_orth : ∀ p q, AgreeOne p q → ∀ k l, inner ℝ (u p k) (u q l) = 0)
    (c : Pt n × Fin r → ℝ) (hc : InN u c) (x y z : Fin n) :
    inner ℝ (a1 u c (x, y, z)) (a1 u c (x, y, z)) = (∑ x', wt c (x', y, z)) / 2 := by
  have h : ∀ x' : Fin n,
      inner ℝ (syn u c (x', y, z)) (a1 u c (x, y, z)) = wt c (x', y, z) / 2 :=
    fun x' => inner_syn_a1 u h_on h_orth c hc x' y z
  calc inner ℝ (a1 u c (x, y, z)) (a1 u c (x, y, z))
      = inner ℝ (∑ x', syn u c (x', y, z)) (a1 u c (x, y, z)) := rfl
    _ = ∑ x', inner ℝ (syn u c (x', y, z)) (a1 u c (x, y, z)) := by rw [sum_inner]
    _ = ∑ x', wt c (x', y, z) / 2 := Finset.sum_congr rfl (fun x' _ => h x')
    _ = (∑ x', wt c (x', y, z)) / 2 := by rw [Finset.sum_div]

/-- Step PB.2: `⟪a2, a2⟫` is half the weight of the line. -/
theorem inner_a2_a2 (u : Pt n → Fin r → E) (h_on : ∀ p, Orthonormal ℝ (u p))
    (h_orth : ∀ p q, AgreeOne p q → ∀ k l, inner ℝ (u p k) (u q l) = 0)
    (c : Pt n × Fin r → ℝ) (hc : InN u c) (x y z : Fin n) :
    inner ℝ (a2 u c (x, y, z)) (a2 u c (x, y, z)) = (∑ y', wt c (x, y', z)) / 2 := by
  have h : ∀ y' : Fin n,
      inner ℝ (syn u c (x, y', z)) (a2 u c (x, y, z)) = wt c (x, y', z) / 2 :=
    fun y' => inner_syn_a2 u h_on h_orth c hc x y' z
  calc inner ℝ (a2 u c (x, y, z)) (a2 u c (x, y, z))
      = inner ℝ (∑ y', syn u c (x, y', z)) (a2 u c (x, y, z)) := rfl
    _ = ∑ y', inner ℝ (syn u c (x, y', z)) (a2 u c (x, y, z)) := by rw [sum_inner]
    _ = ∑ y', wt c (x, y', z) / 2 := Finset.sum_congr rfl (fun y' _ => h y')
    _ = (∑ y', wt c (x, y', z)) / 2 := by rw [Finset.sum_div]

/-- Step PB.2: `⟪a3, a3⟫` is half the weight of the line. -/
theorem inner_a3_a3 (u : Pt n → Fin r → E) (h_on : ∀ p, Orthonormal ℝ (u p))
    (h_orth : ∀ p q, AgreeOne p q → ∀ k l, inner ℝ (u p k) (u q l) = 0)
    (c : Pt n × Fin r → ℝ) (hc : InN u c) (x y z : Fin n) :
    inner ℝ (a3 u c (x, y, z)) (a3 u c (x, y, z)) = (∑ z', wt c (x, y, z')) / 2 := by
  have h : ∀ z' : Fin n,
      inner ℝ (syn u c (x, y, z')) (a3 u c (x, y, z)) = wt c (x, y, z') / 2 :=
    fun z' => inner_syn_a3 u h_on h_orth c hc x y z'
  calc inner ℝ (a3 u c (x, y, z)) (a3 u c (x, y, z))
      = inner ℝ (∑ z', syn u c (x, y, z')) (a3 u c (x, y, z)) := rfl
    _ = ∑ z', inner ℝ (syn u c (x, y, z')) (a3 u c (x, y, z)) := by rw [sum_inner]
    _ = ∑ z', wt c (x, y, z') / 2 := Finset.sum_congr rfl (fun z' _ => h z')
    _ = (∑ z', wt c (x, y, z')) / 2 := by rw [Finset.sum_div]

/-- Cross terms: the inner product of two sums whose terms are orthogonal off the cross through
`(x, y)`. -/
theorem cross_eq {α β : Type*} [Fintype α] [Fintype β] (g : α → E) (h : β → E) (x : α) (y : β)
    (hvan : ∀ x' y', x' ≠ x → y' ≠ y → inner ℝ (g x') (h y') = 0) :
    inner ℝ (∑ x', g x') (∑ y', h y')
      = inner ℝ (g x) (∑ y', h y') + inner ℝ (∑ x', g x') (h y) - inner ℝ (g x) (h y) := by
  have h2 : ∑ x', ∑ y', inner ℝ (g x') (h y')
      = ∑ y', inner ℝ (g x) (h y') + ∑ x', inner ℝ (g x') (h y) - inner ℝ (g x) (h y) :=
    sum_split (fun x' y' => inner ℝ (g x') (h y')) x y hvan
  have h3 : inner ℝ (∑ x', g x') (∑ y', h y') = ∑ x', ∑ y', inner ℝ (g x') (h y') := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro x' _
    rw [inner_sum]
  have h4 : inner ℝ (g x) (∑ y', h y') = ∑ y', inner ℝ (g x) (h y') := by
    rw [inner_sum]
  have h5 : inner ℝ (∑ x', g x') (h y) = ∑ x', inner ℝ (g x') (h y) := by
    rw [sum_inner]
  rw [h3, h2, h4, h5]

/-- Step PB (blueprint 2.3), in weight form: `5 W(p) ≤ 2 ∑ W`. -/
theorem pointwise_bound (u : Pt n → Fin r → E) (h_on : ∀ p, Orthonormal ℝ (u p))
    (h_orth : ∀ p q, AgreeOne p q → ∀ k l, inner ℝ (u p k) (u q l) = 0)
    (c : Pt n × Fin r → ℝ) (hc : InN u c) (x y z : Fin n) :
    5 * wt c (x, y, z) ≤ 2 * ∑ q, wt c q := by
  have d1 : a1 u c (x, y, z) = ∑ x', syn u c (x', y, z) := rfl
  have d2 : a2 u c (x, y, z) = ∑ y', syn u c (x, y', z) := rfl
  have d3 : a3 u c (x, y, z) = ∑ z', syn u c (x, y, z') := rfl
  have hW : inner ℝ (syn u c (x, y, z)) (syn u c (x, y, z)) = wt c (x, y, z) :=
    inner_syn_self u h_on c (x, y, z)
  have w1 := inner_syn_a1 u h_on h_orth c hc x y z
  have w2 := inner_syn_a2 u h_on h_orth c hc x y z
  have w3 := inner_syn_a3 u h_on h_orth c hc x y z
  have w1' : inner ℝ (a1 u c (x, y, z)) (syn u c (x, y, z)) = wt c (x, y, z) / 2 := by
    rw [real_inner_comm]
    exact w1
  have w2' : inner ℝ (a2 u c (x, y, z)) (syn u c (x, y, z)) = wt c (x, y, z) / 2 := by
    rw [real_inner_comm]
    exact w2
  have n11 := inner_a1_a1 u h_on h_orth c hc x y z
  have n22 := inner_a2_a2 u h_on h_orth c hc x y z
  have n33 := inner_a3_a3 u h_on h_orth c hc x y z
  -- the three cross terms vanish
  have n12 : inner ℝ (a1 u c (x, y, z)) (a2 u c (x, y, z)) = 0 := by
    have hcr : inner ℝ (∑ x', syn u c (x', y, z)) (∑ y', syn u c (x, y', z))
        = inner ℝ (syn u c (x, y, z)) (∑ y', syn u c (x, y', z))
          + inner ℝ (∑ x', syn u c (x', y, z)) (syn u c (x, y, z))
          - inner ℝ (syn u c (x, y, z)) (syn u c (x, y, z)) :=
      cross_eq (fun x' => syn u c (x', y, z)) (fun y' => syn u c (x, y', z)) x y
        (fun x' y' hx' hy' => inner_syn_syn_adj u h_orth c (agreeOne_z hx' (Ne.symm hy')))
    rw [← d1, ← d2] at hcr
    linarith
  have n13 : inner ℝ (a1 u c (x, y, z)) (a3 u c (x, y, z)) = 0 := by
    have hcr : inner ℝ (∑ x', syn u c (x', y, z)) (∑ z', syn u c (x, y, z'))
        = inner ℝ (syn u c (x, y, z)) (∑ z', syn u c (x, y, z'))
          + inner ℝ (∑ x', syn u c (x', y, z)) (syn u c (x, y, z))
          - inner ℝ (syn u c (x, y, z)) (syn u c (x, y, z)) :=
      cross_eq (fun x' => syn u c (x', y, z)) (fun z' => syn u c (x, y, z')) x z
        (fun x' z' hx' hz' => inner_syn_syn_adj u h_orth c (agreeOne_y hx' (Ne.symm hz')))
    rw [← d1, ← d3] at hcr
    linarith
  have n23 : inner ℝ (a2 u c (x, y, z)) (a3 u c (x, y, z)) = 0 := by
    have hcr : inner ℝ (∑ y', syn u c (x, y', z)) (∑ z', syn u c (x, y, z'))
        = inner ℝ (syn u c (x, y, z)) (∑ z', syn u c (x, y, z'))
          + inner ℝ (∑ y', syn u c (x, y', z)) (syn u c (x, y, z))
          - inner ℝ (syn u c (x, y, z)) (syn u c (x, y, z)) :=
      cross_eq (fun y' => syn u c (x, y', z)) (fun z' => syn u c (x, y, z')) y z
        (fun y' z' hy' hz' => inner_syn_syn_adj u h_orth c (agreeOne_x hy' (Ne.symm hz')))
    rw [← d2, ← d3] at hcr
    linarith
  have n21 : inner ℝ (a2 u c (x, y, z)) (a1 u c (x, y, z)) = 0 := by
    rw [real_inner_comm]
    exact n12
  have n31 : inner ℝ (a3 u c (x, y, z)) (a1 u c (x, y, z)) = 0 := by
    rw [real_inner_comm]
    exact n13
  have n32 : inner ℝ (a3 u c (x, y, z)) (a2 u c (x, y, z)) = 0 := by
    rw [real_inner_comm]
    exact n23
  -- step 4: the norm of the sum of the three line sums
  have hnorm : ‖a1 u c (x, y, z) + a2 u c (x, y, z) + a3 u c (x, y, z)‖ ^ 2
      = (∑ x', wt c (x', y, z) + ∑ y', wt c (x, y', z) + ∑ z', wt c (x, y, z')) / 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right]
    linarith
  -- step 1: the inner products with the orthonormal family at the point
  have hin : ∀ l, inner ℝ (u (x, y, z) l)
      (a1 u c (x, y, z) + a2 u c (x, y, z) + a3 u c (x, y, z)) = 3 / 2 * c ((x, y, z), l) := by
    intro l
    obtain ⟨h1, h2, h3⟩ := S2 u h_on h_orth c hc x y z l
    rw [inner_add_right, inner_add_right, h1, h2, h3]
    ring
  -- step 5: Bessel's inequality
  have bess : ∑ l, (inner ℝ (u (x, y, z) l)
      (a1 u c (x, y, z) + a2 u c (x, y, z) + a3 u c (x, y, z))) ^ 2
      ≤ ‖a1 u c (x, y, z) + a2 u c (x, y, z) + a3 u c (x, y, z)‖ ^ 2 := by
    have hb := Orthonormal.sum_inner_products_le
      (x := a1 u c (x, y, z) + a2 u c (x, y, z) + a3 u c (x, y, z)) (s := Finset.univ)
      (h_on (x, y, z))
    simpa [Real.norm_eq_abs, sq_abs] using hb
  have hsum : ∑ l, (inner ℝ (u (x, y, z) l)
      (a1 u c (x, y, z) + a2 u c (x, y, z) + a3 u c (x, y, z))) ^ 2
      = 9 / 4 * wt c (x, y, z) := by
    unfold wt
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [hin l]
    ring
  -- step 6: counting
  have hcount := count3 (wt c) (wt_nonneg c) x y z
  rw [hsum, hnorm] at bess
  linarith

end Core

/-! ## 3. Lemma D: dimension from a pointwise bound -/

/-- A subspace of a finite-dimensional real inner-product space has an orthonormal family of
`finrank` vectors lying in it. -/
theorem exists_orthonormal_in_submodule {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (N : Submodule ℝ F) :
    ∃ b : Fin (Module.finrank ℝ N) → F, Orthonormal ℝ b ∧ ∀ j, b j ∈ N := by
  refine ⟨fun j => ((stdOrthonormalBasis ℝ N j : N) : F), ?_,
    fun j => (stdOrthonormalBasis ℝ N j).2⟩
  exact (stdOrthonormalBasis ℝ N).orthonormal.comp_linearIsometry N.subtypeₗᵢ

/-- Lemma D (blueprint 2.4). -/
theorem lemma_D {ι : Type*} [Fintype ι] (N : Submodule ℝ (EuclideanSpace ℝ ι))
    (hN : ∀ v ∈ N, ∀ i, 5 * (v i) ^ 2 ≤ 2 * ‖v‖ ^ 2) :
    5 * Module.finrank ℝ N ≤ 2 * Fintype.card ι := by
  obtain ⟨b, hb, hbN⟩ := exists_orthonormal_in_submodule N
  have key : ∀ i : ι, 5 * ∑ j, (b j i) ^ 2 ≤ 2 := by
    intro i
    have hs0 : 0 ≤ ∑ j, (b j i) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ ι, w = ∑ j, (b j i) • b j := ⟨_, rfl⟩
    have hwN : w ∈ N := by
      rw [hw]
      exact Submodule.sum_mem N (fun j _ => Submodule.smul_mem N _ (hbN j))
    have hwi : w i = ∑ j, (b j i) ^ 2 := by
      rw [hw, WithLp.ofLp_sum, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, sq]
    have hwn : ‖w‖ ^ 2 = ∑ j, (b j i) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hw, sum_inner]
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_smul_left, hb.inner_right_fintype (fun j => b j i) j, sq]
    have h := hN w hwN i
    rw [hwi, hwn] at h
    exact five_mul_le_two_of_sq hs0 h
  have hnorm1 : ∀ j, ∑ i, (b j i) ^ 2 = 1 := by
    intro j
    have h1 : ‖b j‖ = 1 := hb.1 j
    have h2 := EuclideanSpace.real_norm_sq_eq (b j)
    rw [h1, one_pow] at h2
    exact h2.symm
  have hreal : (5 : ℝ) * (Module.finrank ℝ N : ℝ) ≤ 2 * (Fintype.card ι : ℝ) := by
    have e1 : (Module.finrank ℝ N : ℝ) = ∑ i, ∑ j, (b j i) ^ 2 := by
      rw [Finset.sum_comm]
      simp [hnorm1]
    rw [e1, Finset.mul_sum]
    calc ∑ i, 5 * ∑ j, (b j i) ^ 2 ≤ ∑ _i : ι, (2 : ℝ) :=
          Finset.sum_le_sum (fun i _ => key i)
      _ = 2 * (Fintype.card ι : ℝ) := by simp [mul_comm]
  exact_mod_cast hreal

/-! ## 4. The linear map `Φ`, its kernel `N`, and rank-nullity -/

section Assembly

variable {n r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The three layer maps (blueprint 2.1), bundled as one linear map on the coefficient space. -/
noncomputable def Phi (u : Pt n → Fin r → E) :
    EuclideanSpace ℝ (Pt n × Fin r) →ₗ[ℝ] (Fin n → E) × (Fin n → E) × (Fin n → E) where
  toFun v :=
    (fun z => ∑ x', ∑ y', syn u v.ofLp (x', y', z),
     fun y => ∑ x', ∑ z', syn u v.ofLp (x', y, z'),
     fun x => ∑ y', ∑ z', syn u v.ofLp (x, y', z'))
  map_add' v w := by
    have h : ∀ p, syn u (v + w).ofLp p = syn u v.ofLp p + syn u w.ofLp p := by
      intro p
      rw [WithLp.ofLp_add]
      exact syn_add u _ _ p
    simp only [h, Finset.sum_add_distrib]
    rfl
  map_smul' a v := by
    have h : ∀ p, syn u (a • v).ofLp p = a • syn u v.ofLp p := by
      intro p
      rw [WithLp.ofLp_smul]
      exact syn_smul u a _ p
    simp only [h, ← Finset.smul_sum, RingHom.id_apply]
    rfl

/-- The kernel of `Φ` consists of coefficient arrays satisfying the three families of layer
relations. -/
theorem inN_of_mem_ker (u : Pt n → Fin r → E) (v : EuclideanSpace ℝ (Pt n × Fin r))
    (hv : v ∈ LinearMap.ker (Phi u)) : InN u v.ofLp := by
  rw [LinearMap.mem_ker] at hv
  have h1 : (Phi u v).1 = 0 := congrArg Prod.fst hv
  have h2 : (Phi u v).2.1 = 0 := congrArg (fun t => t.2.1) hv
  have h3 : (Phi u v).2.2 = 0 := congrArg (fun t => t.2.2) hv
  exact ⟨fun z => congrFun h1 z, fun y => congrFun h2 y, fun x => congrFun h3 x⟩

/-- Step PB (blueprint 2.3) for elements of the kernel, in coordinate form. -/
theorem ker_pointwise (u : Pt n → Fin r → E) (h_on : ∀ p, Orthonormal ℝ (u p))
    (h_orth : ∀ p q, AgreeOne p q → ∀ k l, inner ℝ (u p k) (u q l) = 0)
    (v : EuclideanSpace ℝ (Pt n × Fin r)) (hv : v ∈ LinearMap.ker (Phi u))
    (i : Pt n × Fin r) : 5 * (v i) ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  have hc : InN u v.ofLp := inN_of_mem_ker u v hv
  obtain ⟨⟨x, y, z⟩, k⟩ := i
  have h1 := pointwise_bound u h_on h_orth v.ofLp hc x y z
  have h2 : (v.ofLp ((x, y, z), k)) ^ 2 ≤ wt v.ofLp (x, y, z) :=
    Finset.single_le_sum (f := fun k => (v.ofLp ((x, y, z), k)) ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ k)
  have h3 : ‖v‖ ^ 2 = ∑ q, wt v.ofLp q := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
    rfl
  rw [h3]
  linarith

/-- Rank-nullity (blueprint 2.1, (RN)). -/
theorem rn_bound [FiniteDimensional ℝ E] (u : Pt n → Fin r → E) :
    r * n ^ 3 ≤ Module.finrank ℝ (LinearMap.ker (Phi u)) + 3 * (n * Module.finrank ℝ E) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Phi u)
  have h2 : Module.finrank ℝ (LinearMap.range (Phi u))
      ≤ Module.finrank ℝ ((Fin n → E) × (Fin n → E) × (Fin n → E)) := Submodule.finrank_le _
  have h3 : Module.finrank ℝ ((Fin n → E) × (Fin n → E) × (Fin n → E))
      = 3 * (n * Module.finrank ℝ E) := by
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have h4 : Module.finrank ℝ (EuclideanSpace ℝ (Pt n × Fin r)) = r * n ^ 3 := by
    rw [finrank_euclideanSpace]
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  omega

end Assembly

/-! ## 5. Main theorems -/

/-- **Core theorem** (P1). -/
theorem core_bound {n r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (u : Pt n → Fin r → E)
    (h_on : ∀ p, Orthonormal ℝ (u p))
    (h_orth : ∀ p q, AgreeOne p q → ∀ k l, inner ℝ (u p k) (u q l) = 0) :
    r * n ^ 2 ≤ 5 * Module.finrank ℝ E := by
  have hD : 5 * Module.finrank ℝ (LinearMap.ker (Phi u)) ≤ 2 * Fintype.card (Pt n × Fin r) :=
    lemma_D (LinearMap.ker (Phi u)) (fun v hv i => ker_pointwise u h_on h_orth v hv i)
  have hcard : Fintype.card (Pt n × Fin r) = r * n ^ 3 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  have hRN := rn_bound u
  have h5 : r * n ^ 3 ≤ 5 * (n * Module.finrank ℝ E) := by omega
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have h6 : n * (r * n ^ 2) ≤ n * (5 * Module.finrank ℝ E) := by
      calc n * (r * n ^ 2) = r * n ^ 3 := by ring
        _ ≤ 5 * (n * Module.finrank ℝ E) := h5
        _ = n * (5 * Module.finrank ℝ E) := by ring
    exact Nat.le_of_mul_le_mul_left h6 hn

/-- A single unit vector is an orthonormal family indexed by `Fin 1`. -/
theorem orthonormal_fin_one {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (x : F)
    (hx : ‖x‖ = 1) : Orthonormal ℝ (fun _ : Fin 1 => x) := by
  unfold Orthonormal
  refine ⟨fun _ => hx, ?_⟩
  intro i j hij
  exact absurd (Subsingleton.elim i j) hij

/-- **Theorem L, real vector form, constant 5** (P1). -/
theorem theorem_L_real {n d : ℕ} (u : Pt n → EuclideanSpace ℝ (Fin d))
    (h_unit : ∀ p, ‖u p‖ = 1)
    (h_orth : ∀ p q, AgreeOne p q → inner ℝ (u p) (u q) = 0) :
    n ^ 2 ≤ 5 * d := by
  have h := core_bound (r := 1) (fun p _ => u p)
    (fun p => orthonormal_fin_one (u p) (h_unit p))
    (fun p q hpq _ _ => h_orth p q hpq)
  rw [finrank_euclideanSpace_fin, one_mul] at h
  exact h

/-- **Theorem L, real vector form, constant 9** (P1; weaker than the constant 5). -/
theorem theorem_L_real_nine {n d : ℕ} (u : Pt n → EuclideanSpace ℝ (Fin d))
    (h_unit : ∀ p, ‖u p‖ = 1)
    (h_orth : ∀ p q, AgreeOne p q → inner ℝ (u p) (u q) = 0) :
    n ^ 2 ≤ 9 * d := by
  have h := theorem_L_real u h_unit h_orth
  omega

/-! ## 6. Projective representations (P3) -/

/-- **Theorem L, projective form** (P3): subspaces of dimension `r`, orthogonal on adjacent
points. -/
theorem theorem_L_projective {n r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (V : Pt n → Submodule ℝ E)
    (h_rank : ∀ p, Module.finrank ℝ (V p) = r)
    (h_orth : ∀ p q, AgreeOne p q → V p ⟂ V q) :
    r * n ^ 2 ≤ 5 * Module.finrank ℝ E := by
  choose b hb hbV using fun p => exists_orthonormal_in_submodule (V p)
  have h_on : ∀ p, Orthonormal ℝ (fun k : Fin r => b p (Fin.cast (h_rank p).symm k)) :=
    fun p => (hb p).comp (Fin.cast (h_rank p).symm) (Fin.cast_injective _)
  have h_or : ∀ p q, AgreeOne p q → ∀ k l : Fin r,
      inner ℝ (b p (Fin.cast (h_rank p).symm k)) (b q (Fin.cast (h_rank q).symm l)) = 0 :=
    fun p q hpq k l => (h_orth p q hpq).inner_eq (hbV p _) (hbV q _)
  exact core_bound (fun p k => b p (Fin.cast (h_rank p).symm k)) h_on h_or

/-! ## 7. The triple graph (P2) -/

/-- Adjacency spelled out: exactly one of the three coordinates agrees. -/
theorem agreeOne_iff {n : ℕ} (p q : Pt n) : AgreeOne p q ↔
    (p.1 = q.1 ∧ p.2.1 ≠ q.2.1 ∧ p.2.2 ≠ q.2.2) ∨
    (p.1 ≠ q.1 ∧ p.2.1 = q.2.1 ∧ p.2.2 ≠ q.2.2) ∨
    (p.1 ≠ q.1 ∧ p.2.1 ≠ q.2.1 ∧ p.2.2 = q.2.2) := by
  unfold AgreeOne
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2.1 = q.2.1 <;> by_cases h3 : p.2.2 = q.2.2 <;>
    simp [h1, h2, h3]

/-- The 3-subset `{x, n + y, 2n + z}` of `Fin t` attached to a point `(x, y, z)` of the cube of
side `n = t / 3`. -/
def emb3 (t : ℕ) (p : Pt (t / 3)) : Finset (Fin t) :=
  {⟨p.1.val, by have := p.1.isLt; omega⟩,
   ⟨t / 3 + p.2.1.val, by have := p.2.1.isLt; omega⟩,
   ⟨2 * (t / 3) + p.2.2.val, by have := p.2.2.isLt; omega⟩}

theorem mem_emb3 {t : ℕ} (p : Pt (t / 3)) (e : Fin t) :
    e ∈ emb3 t p ↔
      e.val = p.1.val ∨ e.val = t / 3 + p.2.1.val ∨ e.val = 2 * (t / 3) + p.2.2.val := by
  constructor
  · intro h
    unfold emb3 at h
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr (Or.inl (congrArg Fin.val h))
    · exact Or.inr (Or.inr (congrArg Fin.val h))
  · intro h
    unfold emb3
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    rcases h with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))

/-- The set attached to a point has exactly three elements. -/
theorem card_emb3 {t : ℕ} (p : Pt (t / 3)) : (emb3 t p).card = 3 := by
  have h1 := p.1.isLt
  have h2 := p.2.1.isLt
  have h3 := p.2.2.isLt
  rw [Finset.card_eq_three]
  refine ⟨⟨p.1.val, by omega⟩, ⟨t / 3 + p.2.1.val, by omega⟩,
    ⟨2 * (t / 3) + p.2.2.val, by omega⟩, ?_, ?_, ?_, rfl⟩
  · intro h
    rw [Fin.mk.injEq] at h
    omega
  · intro h
    rw [Fin.mk.injEq] at h
    omega
  · intro h
    rw [Fin.mk.injEq] at h
    omega

/-- A criterion for the intersection of two attached sets to be a singleton. -/
theorem inter_emb3_eq_singleton {t : ℕ} (p q : Pt (t / 3)) (a : Fin t)
    (h : ∀ e : Fin t, (e ∈ emb3 t p ∧ e ∈ emb3 t q) ↔ e.val = a.val) :
    emb3 t p ∩ emb3 t q = {a} := by
  ext e
  rw [Finset.mem_inter, Finset.mem_singleton, Fin.ext_iff]
  exact h e

/-- Adjacent points of the cube give 3-subsets meeting in exactly one element. -/
theorem card_inter_emb3 {t : ℕ} (p q : Pt (t / 3)) (hpq : AgreeOne p q) :
    (emb3 t p ∩ emb3 t q).card = 1 := by
  have hp1 := p.1.isLt
  have hp2 := p.2.1.isLt
  have hp3 := p.2.2.isLt
  have hq1 := q.1.isLt
  have hq2 := q.2.1.isLt
  have hq3 := q.2.2.isLt
  rw [Finset.card_eq_one]
  rcases (agreeOne_iff p q).mp hpq with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · have f1 : p.1.val = q.1.val := congrArg Fin.val e1
    have f2 : p.2.1.val ≠ q.2.1.val := fun h => e2 (Fin.ext h)
    have f3 : p.2.2.val ≠ q.2.2.val := fun h => e3 (Fin.ext h)
    refine ⟨⟨p.1.val, by omega⟩, inter_emb3_eq_singleton p q _ ?_⟩
    intro e
    rw [mem_emb3, mem_emb3]
    show _ ↔ e.val = p.1.val
    constructor
    · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> omega
    · intro h
      exact ⟨Or.inl h, Or.inl (by omega)⟩
  · have f1 : p.1.val ≠ q.1.val := fun h => e1 (Fin.ext h)
    have f2 : p.2.1.val = q.2.1.val := congrArg Fin.val e2
    have f3 : p.2.2.val ≠ q.2.2.val := fun h => e3 (Fin.ext h)
    refine ⟨⟨t / 3 + p.2.1.val, by omega⟩, inter_emb3_eq_singleton p q _ ?_⟩
    intro e
    rw [mem_emb3, mem_emb3]
    show _ ↔ e.val = t / 3 + p.2.1.val
    constructor
    · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> omega
    · intro h
      exact ⟨Or.inr (Or.inl h), Or.inr (Or.inl (by omega))⟩
  · have f1 : p.1.val ≠ q.1.val := fun h => e1 (Fin.ext h)
    have f2 : p.2.1.val ≠ q.2.1.val := fun h => e2 (Fin.ext h)
    have f3 : p.2.2.val = q.2.2.val := congrArg Fin.val e3
    refine ⟨⟨2 * (t / 3) + p.2.2.val, by omega⟩, inter_emb3_eq_singleton p q _ ?_⟩
    intro e
    rw [mem_emb3, mem_emb3]
    show _ ↔ e.val = 2 * (t / 3) + p.2.2.val
    constructor
    · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> omega
    · intro h
      exact ⟨Or.inr (Or.inr h), Or.inr (Or.inr (by omega))⟩

/-- The attached 3-subset as an element of the vertex type of the triple graph. -/
def emb3S (t : ℕ) (p : Pt (t / 3)) : {A : Finset (Fin t) // A.card = 3} :=
  ⟨emb3 t p, card_emb3 p⟩

/-- Normalising a non-zero vector gives a unit vector. -/
theorem norm_normalize {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {x : F}
    (hx : x ≠ 0) : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- **Corollary L, the triple graph, constant 5** (P2): non-zero real vectors on the 3-subsets of
`Fin t`, orthogonal whenever two subsets meet in exactly one element. -/
theorem corollary_L_real {t d : ℕ}
    (v : {A : Finset (Fin t) // A.card = 3} → EuclideanSpace ℝ (Fin d))
    (h_ne : ∀ A, v A ≠ 0)
    (h_orth : ∀ A B, (A.1 ∩ B.1).card = 1 → inner ℝ (v A) (v B) = 0) :
    (t / 3) ^ 2 ≤ 5 * d := by
  have hu : ∀ p : Pt (t / 3), ‖(‖v (emb3S t p)‖⁻¹ : ℝ) • v (emb3S t p)‖ = 1 :=
    fun p => norm_normalize (h_ne (emb3S t p))
  have ho : ∀ p q : Pt (t / 3), AgreeOne p q →
      inner ℝ ((‖v (emb3S t p)‖⁻¹ : ℝ) • v (emb3S t p))
        ((‖v (emb3S t q)‖⁻¹ : ℝ) • v (emb3S t q)) = 0 := by
    intro p q hpq
    rw [real_inner_smul_left, real_inner_smul_right,
      h_orth (emb3S t p) (emb3S t q) (card_inter_emb3 p q hpq), mul_zero, mul_zero]
  exact theorem_L_real (fun p => (‖v (emb3S t p)‖⁻¹ : ℝ) • v (emb3S t p)) hu ho

/-- **Corollary L, the triple graph, constant 9** (P2; weaker than the constant 5). -/
theorem corollary_L_real_nine {t d : ℕ}
    (v : {A : Finset (Fin t) // A.card = 3} → EuclideanSpace ℝ (Fin d))
    (h_ne : ∀ A, v A ≠ 0)
    (h_orth : ∀ A B, (A.1 ∩ B.1).card = 1 → inner ℝ (v A) (v B) = 0) :
    (t / 3) ^ 2 ≤ 9 * d := by
  have h := corollary_L_real v h_ne h_orth
  omega

/-! ## 8. Complex Hermitian unit vectors (P4) -/

/-- A two-element family. -/
def pair {F : Type*} (a b : F) : Fin 2 → F := fun k => if k = 0 then a else b

theorem pair_zero {F : Type*} (a b : F) : pair a b 0 = a := by
  unfold pair
  exact if_pos rfl

theorem pair_one {F : Type*} (a b : F) : pair a b 1 = b := by
  unfold pair
  exact if_neg (by decide)

theorem norm_eq_one_of_inner_self {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {a : F} (h : inner ℝ a a = 1) : ‖a‖ = 1 := by
  have h2 : ‖a‖ ^ 2 = 1 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, h, one_pow]
  exact (sq_eq_sq₀ (norm_nonneg a) zero_le_one).mp h2

/-- Two unit vectors that are orthogonal form an orthonormal family indexed by `Fin 2`. -/
theorem orthonormal_pair {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (a b : F)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    Orthonormal ℝ (pair a b) := by
  have hba : inner ℝ b a = 0 := by
    rw [real_inner_comm]
    exact hab
  unfold Orthonormal
  refine ⟨?_, ?_⟩
  · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [pair_zero]
      exact norm_eq_one_of_inner_self ha
    · rw [pair_one]
      exact norm_eq_one_of_inner_self hb
  · have key : ∀ i j : Fin 2, i ≠ j → inner ℝ (pair a b i) (pair a b j) = 0 := by
      refine Fin.forall_fin_two.mpr
        ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
      · intro h
        exact absurd rfl h
      · intro _
        rw [pair_zero, pair_one]
        exact hab
      · intro _
        rw [pair_one, pair_zero]
        exact hba
      · intro h
        exact absurd rfl h
    intro i j hij
    exact key i j hij

theorem inner_pair_pair {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (a b a' b' : F) (h1 : inner ℝ a a' = 0) (h2 : inner ℝ a b' = 0)
    (h3 : inner ℝ b a' = 0) (h4 : inner ℝ b b' = 0) (k l : Fin 2) :
    inner ℝ (pair a b k) (pair a' b' l) = 0 := by
  simp only [pair]
  split_ifs <;> assumption

/-- Realification of complex coordinates: real parts on the left summand, imaginary parts on the
right summand. -/
noncomputable def realify {d : ℕ} (x : EuclideanSpace ℂ (Fin d)) :
    EuclideanSpace ℝ (Fin d ⊕ Fin d) :=
  WithLp.toLp 2 (Sum.elim (fun i => (x i).re) (fun i => (x i).im))

theorem realify_inl {d : ℕ} (x : EuclideanSpace ℂ (Fin d)) (i : Fin d) :
    (realify x) (Sum.inl i) = (x i).re := rfl

theorem realify_inr {d : ℕ} (x : EuclideanSpace ℂ (Fin d)) (i : Fin d) :
    (realify x) (Sum.inr i) = (x i).im := rfl

/-- The inner product of two real numbers. -/
theorem real_inner_real (a b : ℝ) : inner ℝ a b = b * a := rfl

/-- The real inner product of the realifications is the real part of the Hermitian product. -/
theorem inner_realify {d : ℕ} (x y : EuclideanSpace ℂ (Fin d)) :
    inner ℝ (realify x) (realify y) = (inner ℂ x y).re := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_sum_type, Complex.re_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [realify_inl, realify_inl, realify_inr, realify_inr, real_inner_real, real_inner_real,
    RCLike.inner_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem inner_realify_self {d : ℕ} (x : EuclideanSpace ℂ (Fin d)) :
    inner ℝ (realify x) (realify x) = ‖x‖ ^ 2 := by
  rw [inner_realify]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) x

/-- **Theorem L, complex Hermitian unit vectors** (P4). -/
theorem theorem_L_complex_hermitian {n d : ℕ} (u : Pt n → EuclideanSpace ℂ (Fin d))
    (h_unit : ∀ p, ‖u p‖ = 1)
    (h_orth : ∀ p q, AgreeOne p q → inner ℂ (u p) (u q) = 0) :
    n ^ 2 ≤ 5 * d := by
  have h_on : ∀ p, Orthonormal ℝ (pair (realify (u p)) (realify (Complex.I • u p))) := by
    intro p
    refine orthonormal_pair _ _ ?_ ?_ ?_
    · rw [inner_realify_self, h_unit p, one_pow]
    · rw [inner_realify_self, norm_smul, Complex.norm_I, one_mul, h_unit p, one_pow]
    · rw [inner_realify, inner_smul_right, inner_self_eq_norm_sq_to_K, h_unit p]
      simp
  have h_or : ∀ p q, AgreeOne p q → ∀ k l : Fin 2,
      inner ℝ (pair (realify (u p)) (realify (Complex.I • u p)) k)
        (pair (realify (u q)) (realify (Complex.I • u q)) l) = 0 := by
    intro p q hpq k l
    have h0 := h_orth p q hpq
    refine inner_pair_pair _ _ _ _ ?_ ?_ ?_ ?_ k l
    · rw [inner_realify, h0, Complex.zero_re]
    · rw [inner_realify, inner_smul_right, h0, mul_zero, Complex.zero_re]
    · rw [inner_realify, inner_smul_left, h0, mul_zero, Complex.zero_re]
    · rw [inner_realify, inner_smul_left, inner_smul_right, h0, mul_zero, mul_zero,
        Complex.zero_re]
  have h := core_bound (r := 2)
    (fun p => pair (realify (u p)) (realify (Complex.I • u p))) h_on h_or
  rw [finrank_euclideanSpace, Fintype.card_sum, Fintype.card_fin] at h
  omega

/-! ## 9. Projectors as operators (P5) -/

/-- **Theorem L, projector form** (P5): self-adjoint operators of rank `r` whose products vanish
on adjacent points. -/
theorem theorem_L_projectors {n r D : ℕ}
    (P : Pt n → (EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D)))
    (h_sa : ∀ p, IsSelfAdjoint (P p))
    (h_rank : ∀ p, Module.finrank ℝ (LinearMap.range (P p).toLinearMap) = r)
    (h_orth : ∀ p q, AgreeOne p q → (P p).comp (P q) = 0) :
    r * n ^ 2 ≤ 5 * D := by
  have hV : ∀ p q, AgreeOne p q →
      LinearMap.range (P p).toLinearMap ⟂ LinearMap.range (P q).toLinearMap := by
    intro p q hpq
    rw [Submodule.isOrtho_iff_inner_eq]
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have hsym : ∀ a b, inner ℝ ((P p) a) b = inner ℝ a ((P p) b) :=
      fun a b => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (h_sa p) a b
    have hzero : (P p) ((P q) y) = 0 := DFunLike.congr_fun (h_orth p q hpq) y
    show inner ℝ ((P p) x) ((P q) y) = 0
    rw [hsym, hzero, inner_zero_right]
  have h := theorem_L_projective (fun p => LinearMap.range (P p).toLinearMap) h_rank hV
  rw [finrank_euclideanSpace_fin] at h
  exact h

/-! ## 10. Complex projective form (optional target) -/

/-- A complex inner-product space regarded as a real one. This is a type synonym, so that the
complex structure of `E` contributes no competing instance. -/
def RealForm (E : Type*) : Type _ := E

section RealFormSection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable instance instNormedAddCommGroupRealForm : NormedAddCommGroup (RealForm E) :=
  inferInstanceAs (NormedAddCommGroup E)

/-- The real inner product `re ⟪x, y⟫_ℂ` on the real form. -/
noncomputable instance instInnerProductSpaceRealForm : InnerProductSpace ℝ (RealForm E) :=
  InnerProductSpace.rclikeToReal ℂ E

theorem realForm_inner (x y : RealForm E) :
    inner ℝ x y = (@inner ℂ E _ x y).re := rfl

instance instFiniteDimensionalRealForm [FiniteDimensional ℂ E] :
    FiniteDimensional ℝ (RealForm E) :=
  FiniteDimensional.complexToReal E

theorem finrank_realForm : Module.finrank ℝ (RealForm E) = 2 * Module.finrank ℂ E :=
  finrank_real_of_complex E

/-- A complex subspace regarded as a real subspace of the real form. -/
def realSub (W : Submodule ℂ E) : Submodule ℝ (RealForm E) where
  carrier := {x : RealForm E | (x : E) ∈ W}
  add_mem' := by
    intro a b ha hb
    exact W.add_mem ha hb
  zero_mem' := W.zero_mem
  smul_mem' := by
    intro c x hx
    exact W.smul_mem (c : ℂ) hx

theorem mem_realSub (W : Submodule ℂ E) (x : RealForm E) : x ∈ realSub W ↔ (x : E) ∈ W :=
  Iff.rfl

/-- The real dimension of a complex subspace is twice its complex dimension. -/
theorem finrank_realSub (W : Submodule ℂ E) :
    Module.finrank ℝ (realSub W) = 2 * Module.finrank ℂ W := by
  have e : (realSub W) ≃ₗ[ℝ] W :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq]
  exact finrank_real_of_complex W

/-- Hermitian-orthogonal complex subspaces are orthogonal as real subspaces of the real form. -/
theorem realSub_isOrtho {W W' : Submodule ℂ E} (h : W ⟂ W') : realSub W ⟂ realSub W' := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro x hx y hy
  have h0 : @inner ℂ E _ x y = 0 := h.inner_eq hx hy
  rw [realForm_inner, h0, Complex.zero_re]

end RealFormSection

/-- **Theorem L, complex projective form**: complex subspaces of complex dimension `r`,
Hermitian-orthogonal on adjacent points. Obtained from the real projective form by restricting
scalars to `ℝ`. -/
theorem theorem_L_projective_complex {n r : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (V : Pt n → Submodule ℂ E)
    (h_rank : ∀ p, Module.finrank ℂ (V p) = r)
    (h_orth : ∀ p q, AgreeOne p q → V p ⟂ V q) :
    r * n ^ 2 ≤ 5 * Module.finrank ℂ E := by
  have hrank : ∀ p, Module.finrank ℝ (realSub (V p)) = 2 * r := by
    intro p
    rw [finrank_realSub, h_rank p]
  have h := theorem_L_projective (E := RealForm E) (r := 2 * r) (fun p => realSub (V p)) hrank
    (fun p q hpq => realSub_isOrtho (h_orth p q hpq))
  rw [finrank_realForm, mul_assoc] at h
  omega

/-! ## 11. Sanity checks (not targets): the meaning of adjacency, and non-vacuity -/

/-! On the cube of side 2, the point `(0, 0, 0)` is adjacent exactly to the points that share one
coordinate with it. -/

example : AgreeOne ((0, 0, 0) : Pt 2) (1, 1, 0) := by unfold AgreeOne; decide
example : AgreeOne ((0, 0, 0) : Pt 2) (1, 0, 1) := by unfold AgreeOne; decide
example : AgreeOne ((0, 0, 0) : Pt 2) (0, 1, 1) := by unfold AgreeOne; decide
example : ¬ AgreeOne ((0, 0, 0) : Pt 2) (0, 0, 0) := by unfold AgreeOne; decide
example : ¬ AgreeOne ((0, 0, 0) : Pt 2) (1, 0, 0) := by unfold AgreeOne; decide
example : ¬ AgreeOne ((0, 0, 0) : Pt 2) (0, 1, 0) := by unfold AgreeOne; decide
example : ¬ AgreeOne ((0, 0, 0) : Pt 2) (0, 0, 1) := by unfold AgreeOne; decide
example : ¬ AgreeOne ((0, 0, 0) : Pt 2) (1, 1, 1) := by unfold AgreeOne; decide

/-- Adjacent points are distinct. -/
theorem ne_of_agreeOne {n : ℕ} {p q : Pt n} (h : AgreeOne p q) : p ≠ q := by
  rintro rfl
  simp [AgreeOne] at h

/-- Non-vacuity: for every `n` the hypotheses of `theorem_L_real` are satisfiable (standard basis
vectors indexed by the points, in dimension `n ^ 3`). -/
theorem hypotheses_satisfiable (n : ℕ) :
    ∃ (d : ℕ) (u : Pt n → EuclideanSpace ℝ (Fin d)),
      (∀ p, ‖u p‖ = 1) ∧ ∀ p q, AgreeOne p q → inner ℝ (u p) (u q) = 0 := by
  have hon : Orthonormal ℝ
      (fun i : Fin (Fintype.card (Pt n)) => EuclideanSpace.single i (1 : ℝ)) :=
    EuclideanSpace.orthonormal_single
  refine ⟨Fintype.card (Pt n),
    fun p => EuclideanSpace.single (Fintype.equivFin (Pt n) p) (1 : ℝ), ?_, ?_⟩
  · intro p
    exact hon.1 (Fintype.equivFin (Pt n) p)
  · intro p q hpq
    exact hon.2 (fun h => ne_of_agreeOne hpq ((Fintype.equivFin (Pt n)).injective h))

end TheoremL

#print axioms TheoremL.core_bound
#print axioms TheoremL.theorem_L_real
#print axioms TheoremL.theorem_L_real_nine
#print axioms TheoremL.corollary_L_real
#print axioms TheoremL.corollary_L_real_nine
#print axioms TheoremL.theorem_L_projective
#print axioms TheoremL.theorem_L_complex_hermitian
#print axioms TheoremL.theorem_L_projectors
#print axioms TheoremL.theorem_L_projective_complex
#print axioms TheoremL.hypotheses_satisfiable
