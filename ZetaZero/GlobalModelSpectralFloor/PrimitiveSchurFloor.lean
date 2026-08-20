import Mathlib.Tactic

/-!
# Primitive Schur floor for the global model

This file isolates the spectral mechanism used in Section 08 after the two
integrations by parts.  Once the completed lag form has the shape

`a * primitiveEnergy - regularForm`

and the regular term is Schur-dominated by `M * primitiveEnergy`, the surviving
floor is `a - M`.  The triangular reference form in the manuscript is twice the
primitive energy, so a gap `2 * c ≤ a - M` yields a `c`-floor against that
reference form.

The statements are deliberately independent of the analytic construction of the
kernel.  Later files only have to supply the certified cusp coefficient and the
Schur bound.
-/

namespace ZetaZero
namespace GlobalModelSpectralFloor

section AbstractFloor

variable {V W : Type*}

/-- Pointwise Loewner-style lower bound for real-valued quadratic forms. -/
def LowerBound (q g : V → ℝ) (c : ℝ) : Prop :=
  ∀ x, c * g x ≤ q x

/-- A Schur bound on the regular primitive term leaves the difference
`a - M` as the exact primitive-energy floor. -/
theorem cusp_minus_regular_lowerBound
    {primitive regular : V → ℝ} {a M : ℝ}
    (hregular : ∀ x, |regular x| ≤ M * primitive x) :
    LowerBound
      (fun x => a * primitive x - regular x)
      primitive (a - M) := by
  intro x
  have hr : regular x ≤ M * primitive x :=
    (le_abs_self (regular x)).trans (hregular x)
  calc
    (a - M) * primitive x = a * primitive x - M * primitive x := by ring
    _ ≤ a * primitive x - regular x := sub_le_sub_left hr _

/-- The manuscript's triangular primitive reference is `2 * primitiveEnergy`.
Thus a primitive gap of at least `2c` gives a `c` spectral floor in the
triangular metric. -/
theorem cusp_minus_regular_triangular_floor
    {primitive regular : V → ℝ} {a M c : ℝ}
    (hprimitive : ∀ x, 0 ≤ primitive x)
    (hregular : ∀ x, |regular x| ≤ M * primitive x)
    (hgap : 2 * c ≤ a - M) :
    LowerBound
      (fun x => a * primitive x - regular x)
      (fun x => 2 * primitive x) c := by
  intro x
  have hbase := cusp_minus_regular_lowerBound (V := V) (a := a) (M := M) hregular x
  have hscale : (2 * c) * primitive x ≤ (a - M) * primitive x :=
    mul_le_mul_of_nonneg_right hgap (hprimitive x)
  calc
    c * (2 * primitive x) = (2 * c) * primitive x := by ring
    _ ≤ (a - M) * primitive x := hscale
    _ ≤ a * primitive x - regular x := hbase

/-- Numerical specialization of the certified bounds in Proposition
`model-floor`: `a_G > 5.677` and Schur row sum `< 5.535` already imply the
advertised `0.06 * Q_triangle` floor. -/
theorem certified_point_zero_six_floor
    {primitive regular : V → ℝ} {a : ℝ}
    (hprimitive : ∀ x, 0 ≤ primitive x)
    (hcusp : (5677 : ℝ) / 1000 ≤ a)
    (hregular : ∀ x, |regular x| ≤ ((5535 : ℝ) / 1000) * primitive x) :
    LowerBound
      (fun x => a * primitive x - regular x)
      (fun x => 2 * primitive x) ((6 : ℝ) / 100) := by
  apply cusp_minus_regular_triangular_floor hprimitive hregular
  linarith

/-- A whole-space floor survives any common pullback.  This is the abstract
congruence step used when both `A_T^G` and the triangular reference Gram form are
pulled back through the same normalized core analysis map. -/
theorem lowerBound_common_pullback
    {q g : V → ℝ} {c : ℝ}
    (h : LowerBound q g c) (U : W → V) :
    LowerBound (fun w => q (U w)) (fun w => g (U w)) c := by
  intro w
  exact h (U w)

/-- Restricting the domain cannot destroy a pointwise spectral floor. -/
theorem lowerBound_restrict
    {q g : V → ℝ} {c : ℝ} (h : LowerBound q g c)
    (S : Set V) :
    ∀ x ∈ S, c * g x ≤ q x := by
  intro x _
  exact h x

/-- A relative form perturbation of size `ε` subtracts at most `ε` from the
available floor.  This is the finite-`T` stability mechanism of Section 08. -/
theorem lowerBound_add_relative_error
    {q g err : V → ℝ} {c ε : ℝ}
    (hq : LowerBound q g c)
    (herr : ∀ x, |err x| ≤ ε * g x) :
    LowerBound (fun x => q x + err x) g (c - ε) := by
  intro x
  have herrLower : -(ε * g x) ≤ err x := (abs_le.mp (herr x)).1
  calc
    (c - ε) * g x = c * g x - ε * g x := by ring
    _ ≤ q x - ε * g x := sub_le_sub_right (hq x) _
    _ ≤ q x + err x := by
      simpa [sub_eq_add_neg] using add_le_add_left herrLower (q x)

/-- The exact numerical end of the manuscript's principal comparison: a
`0.06` model floor plus a relative error bounded by `0.03` leaves the chosen
`c₀ = 0.03` principal floor. -/
theorem point_zero_three_floor_after_relative_error
    {q g err : V → ℝ}
    (hq : LowerBound q g ((6 : ℝ) / 100))
    (herr : ∀ x, |err x| ≤ ((3 : ℝ) / 100) * g x) :
    LowerBound (fun x => q x + err x) g ((3 : ℝ) / 100) := by
  have h := lowerBound_add_relative_error hq herr
  norm_num at h ⊢
  exact h

end AbstractFloor

end GlobalModelSpectralFloor
end ZetaZero
