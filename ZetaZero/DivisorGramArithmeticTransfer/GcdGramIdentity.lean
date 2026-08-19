import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
# Concrete gcd/totient Gram coordinates

This module formalizes the arithmetic kernel in Section 09.  The finite label
space is `1 ≤ n ≤ Y`.  Totient-weighted divisibility coordinates produce the
kernel `gcd(m,n)/(mn)`, and the abstract operator-valued Gram lift then gives
Hilbert-valued positivity.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace ZetaZero
namespace DivisorGramArithmeticTransfer

/-- Positive integer labels `1 ≤ n ≤ Y`. -/
abbrev DivisorIndex (Y : ℕ) := {n : ℕ // n ∈ Finset.Icc 1 Y}

lemma divisorIndex_pos {Y : ℕ} (n : DivisorIndex Y) : 0 < n.1 := by
  exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp n.2).1

lemma divisorIndex_le {Y : ℕ} (n : DivisorIndex Y) : n.1 ≤ Y :=
  (Finset.mem_Icc.mp n.2).2

/-- Inside the finite label interval, the common divisors of `m,n` are exactly
all divisors of `gcd m n`. -/
lemma commonDivisors_eq_gcdDivisors {Y : ℕ} (m n : DivisorIndex Y) :
    (Finset.Icc 1 Y).filter (fun d => d ∣ m.1 ∧ d ∣ n.1) =
      (Nat.gcd m.1 n.1).divisors := by
  ext d
  have hgpos : 0 < Nat.gcd m.1 n.1 :=
    Nat.gcd_pos_of_pos_left n.1 (divisorIndex_pos m)
  constructor
  · intro hd
    have hmem := Finset.mem_filter.mp hd
    have hdg : d ∣ Nat.gcd m.1 n.1 := Nat.dvd_gcd hmem.2.1 hmem.2.2
    exact Nat.mem_divisors.mpr ⟨hdg, hgpos.ne'⟩
  · intro hd
    have hdiv := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdiv hgpos
    have hdle_g : d ≤ Nat.gcd m.1 n.1 := Nat.le_of_dvd hgpos hdiv
    have hg_le_m : Nat.gcd m.1 n.1 ≤ m.1 :=
      Nat.le_of_dvd (divisorIndex_pos m) (Nat.gcd_dvd_left _ _)
    have hdY : d ≤ Y := hdle_g.trans (hg_le_m.trans (divisorIndex_le m))
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hdpos, hdY⟩,
      ⟨dvd_trans hdiv (Nat.gcd_dvd_left _ _), dvd_trans hdiv (Nat.gcd_dvd_right _ _)⟩⟩

/-- Euler's totient identity, specialized to common divisors in the finite
label interval. -/
theorem sum_totient_common_divisors {Y : ℕ} (m n : DivisorIndex Y) :
    (∑ d ∈ Finset.Icc 1 Y with d ∣ m.1 ∧ d ∣ n.1, Nat.totient d) =
      Nat.gcd m.1 n.1 := by
  rw [show (Finset.Icc 1 Y).filter (fun d => d ∣ m.1 ∧ d ∣ n.1) =
      (Nat.gcd m.1 n.1).divisors from commonDivisors_eq_gcdDivisors m n]
  exact Nat.sum_totient _

/-- Divisibility Gram coordinate at a natural divisor label `d`.  The
square-root totient factor is exactly what turns the coordinate Gram into the
gcd kernel. -/
def gcdGramCoordinateNat {Y : ℕ} (d : ℕ) (n : DivisorIndex Y) : ℂ :=
  if d ∣ n.1 then
    (Real.sqrt (Nat.totient d) : ℂ) / (n.1 : ℂ)
  else 0

/-- The same coordinate when the divisor label itself belongs to the finite
positive interval. -/
def gcdGramCoordinate {Y : ℕ} (d n : DivisorIndex Y) : ℂ :=
  gcdGramCoordinateNat d.1 n

/-- The scalar Gram kernel attached to the divisor coordinates. -/
def gcdScalarKernel {Y : ℕ} (m n : DivisorIndex Y) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Y,
    conj (gcdGramCoordinateNat d m) * gcdGramCoordinateNat d n

lemma sqrtTotient_coordinate_product {d m n : ℕ} :
    ((Real.sqrt (Nat.totient d) : ℂ) / (m : ℂ)) *
        ((Real.sqrt (Nat.totient d) : ℂ) / (n : ℂ)) =
      (Nat.totient d : ℂ) / ((m : ℂ) * (n : ℂ)) := by
  rw [div_mul_div_comm]
  congr 1
  norm_cast
  exact Real.mul_self_sqrt (by positivity)

/-- Exact arithmetic kernel identity `H(m,n)=gcd(m,n)/(mn)`. -/
theorem gcdScalarKernel_eq {Y : ℕ} (m n : DivisorIndex Y) :
    gcdScalarKernel m n =
      (Nat.gcd m.1 n.1 : ℂ) / ((m.1 : ℂ) * (n.1 : ℂ)) := by
  unfold gcdScalarKernel
  calc
    (∑ d ∈ Finset.Icc 1 Y,
        conj (gcdGramCoordinateNat d m) * gcdGramCoordinateNat d n) =
        ∑ d ∈ Finset.Icc 1 Y,
          if d ∣ m.1 ∧ d ∣ n.1 then
            (Nat.totient d : ℂ) / ((m.1 : ℂ) * (n.1 : ℂ))
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdm : d ∣ m.1
      · by_cases hdn : d ∣ n.1
        · simpa [gcdGramCoordinateNat, hdm, hdn] using
            (sqrtTotient_coordinate_product (d := d) (m := m.1) (n := n.1))
        · simp [gcdGramCoordinateNat, hdm, hdn]
      · simp [gcdGramCoordinateNat, hdm]
    _ = ∑ d ∈ Finset.Icc 1 Y with d ∣ m.1 ∧ d ∣ n.1,
          (Nat.totient d : ℂ) / ((m.1 : ℂ) * (n.1 : ℂ)) := by
      rw [Finset.sum_filter]
    _ = (∑ d ∈ Finset.Icc 1 Y with d ∣ m.1 ∧ d ∣ n.1,
          (Nat.totient d : ℂ)) / ((m.1 : ℂ) * (n.1 : ℂ)) := by
      rw [Finset.sum_div]
    _ = (Nat.gcd m.1 n.1 : ℂ) / ((m.1 : ℂ) * (n.1 : ℂ)) := by
      congr 1
      exact_mod_cast sum_totient_common_divisors m n

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The `d`-th divisor-analysis channel for a Hilbert-valued family. -/
def gcdDivisorChannel {Y : ℕ} (b : DivisorIndex Y → H) (d : ℕ) : H :=
  ∑ n : DivisorIndex Y, gcdGramCoordinateNat d n • b n

/-- The unweighted divisibility channel appearing literally in the manuscript. -/
def divisorTailChannel {Y : ℕ} (b : DivisorIndex Y → H) (d : ℕ) : H :=
  ∑ n : DivisorIndex Y,
    if d ∣ n.1 then ((1 : ℂ) / (n.1 : ℂ)) • b n else 0

/-- Vanishing of all finite divisor tails forces the Hilbert-valued family to
vanish.  This is the injectivity mechanism behind the finite divisor map; the
proof uses a maximal nonzero index, so no asymptotic input is involved. -/
theorem divisorTailChannel_joint_kernel {Y : ℕ}
    (b : DivisorIndex Y → H)
    (hzero : ∀ d ∈ Finset.Icc 1 Y, divisorTailChannel b d = 0) :
    ∀ n, b n = 0 := by
  classical
  by_contra hnot
  push Not at hnot
  let s : Finset (DivisorIndex Y) := Finset.univ.filter (fun n => b n ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨n, hn⟩ := hnot
    refine ⟨n, ?_⟩
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hn
  obtain ⟨n, hns, hnmax⟩ :=
    Finset.exists_max_image s (fun j : DivisorIndex Y => j.1) hs
  have hchan : divisorTailChannel b n.1 = 0 := hzero n.1 n.2
  have hsum :
      divisorTailChannel b n.1 = ((1 : ℂ) / (n.1 : ℂ)) • b n := by
    unfold divisorTailChannel
    rw [Finset.sum_eq_single n]
    · simp
    · intro j hj hjne
      by_cases hdiv : n.1 ∣ j.1
      · have hbj : b j = 0 := by
          by_contra hbjne
          have hjs : j ∈ s := by
            simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hbjne
          have hjle : j.1 ≤ n.1 := hnmax j hjs
          have hnle : n.1 ≤ j.1 := Nat.le_of_dvd (divisorIndex_pos j) hdiv
          have hval : j.1 = n.1 := Nat.le_antisymm hjle hnle
          have hjn : j = n := Subtype.ext hval
          exact hjne hjn
        simp [hdiv, hbj]
      · simp [hdiv]
    · simp
  have hsmul : ((1 : ℂ) / (n.1 : ℂ)) • b n = 0 := by
    rw [← hsum, hchan]
  have hscalar : ((1 : ℂ) / (n.1 : ℂ)) ≠ 0 := by
    simp [(divisorIndex_pos n).ne']
  have hbn : b n = 0 := (smul_eq_zero.mp hsmul).resolve_left hscalar
  exact (Finset.mem_filter.mp hns).2 hbn

/-- The weighted Gram channel is exactly `sqrt(phi(d))` times the manuscript's
unweighted divisor tail. -/
theorem gcdDivisorChannel_eq_sqrtTotient_smul {Y : ℕ}
    (b : DivisorIndex Y → H) (d : ℕ) :
    gcdDivisorChannel b d =
      (Real.sqrt (Nat.totient d) : ℂ) • divisorTailChannel b d := by
  unfold gcdDivisorChannel divisorTailChannel
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hdn : d ∣ n.1
  · simp [gcdGramCoordinateNat, hdn, smul_smul]
    ring
  · simp [gcdGramCoordinateNat, hdn]

/-- Squaring the weighted channel produces the totient weight exactly. -/
theorem norm_sq_gcdDivisorChannel {Y : ℕ}
    (b : DivisorIndex Y → H) (d : ℕ) :
    ‖gcdDivisorChannel b d‖ ^ 2 =
      (Nat.totient d : ℝ) * ‖divisorTailChannel b d‖ ^ 2 := by
  rw [gcdDivisorChannel_eq_sqrtTotient_smul, norm_smul]
  have hsqrt : 0 ≤ Real.sqrt (Nat.totient d) := Real.sqrt_nonneg _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt]
  rw [mul_pow, Real.sq_sqrt (by positivity)]

/-- The concrete Hilbert-valued gcd quadratic form from Section 09. -/
def gcdHilbertForm {Y : ℕ} (b : DivisorIndex Y → H) : ℂ :=
  ∑ m : DivisorIndex Y, ∑ n : DivisorIndex Y,
    ((Nat.gcd m.1 n.1 : ℂ) / ((m.1 : ℂ) * (n.1 : ℂ))) * inner ℂ (b m) (b n)

/-- Expanding the divisor-analysis channels reproduces the scalar Gram kernel. -/
theorem sum_inner_gcdDivisorChannel_eq_scalarKernel {Y : ℕ}
    (b : DivisorIndex Y → H) :
    (∑ d ∈ Finset.Icc 1 Y,
      inner ℂ (gcdDivisorChannel b d) (gcdDivisorChannel b d)) =
      ∑ m : DivisorIndex Y, ∑ n : DivisorIndex Y,
        gcdScalarKernel m n * inner ℂ (b m) (b n) := by
  unfold gcdDivisorChannel gcdScalarKernel
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    (∑ d ∈ Finset.Icc 1 Y,
      conj (gcdGramCoordinateNat d m) *
        (gcdGramCoordinateNat d n * inner ℂ (b m) (b n))) =
        ∑ d ∈ Finset.Icc 1 Y,
          (conj (gcdGramCoordinateNat d m) * gcdGramCoordinateNat d n) *
            inner ℂ (b m) (b n) := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = (∑ d ∈ Finset.Icc 1 Y,
          conj (gcdGramCoordinateNat d m) * gcdGramCoordinateNat d n) *
            inner ℂ (b m) (b n) := by
      rw [Finset.sum_mul]

/-- Hilbert-valued gcd identity in Gram-coordinate form. -/
theorem gcdHilbertForm_eq_sum_inner_channels {Y : ℕ}
    (b : DivisorIndex Y → H) :
    gcdHilbertForm b =
      ∑ d ∈ Finset.Icc 1 Y,
        inner ℂ (gcdDivisorChannel b d) (gcdDivisorChannel b d) := by
  rw [sum_inner_gcdDivisorChannel_eq_scalarKernel]
  unfold gcdHilbertForm
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [gcdScalarKernel_eq]

/-- The manuscript's boxed Hilbert-valued gcd identity, written on real
quadratic forms. -/
theorem gcdHilbertForm_re_eq_totient_norm_sum {Y : ℕ}
    (b : DivisorIndex Y → H) :
    (gcdHilbertForm b).re =
      ∑ d ∈ Finset.Icc 1 Y,
        (Nat.totient d : ℝ) * ‖divisorTailChannel b d‖ ^ 2 := by
  rw [gcdHilbertForm_eq_sum_inner_channels, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    (inner ℂ (gcdDivisorChannel b d) (gcdDivisorChannel b d)).re =
        ‖gcdDivisorChannel b d‖ ^ 2 := by
      simpa using
        (@inner_self_eq_norm_sq ℂ H _ _ _ (gcdDivisorChannel b d))
    _ = (Nat.totient d : ℝ) * ‖divisorTailChannel b d‖ ^ 2 :=
      norm_sq_gcdDivisorChannel b d

/-- Positivity of the Hilbert-valued gcd kernel. -/
theorem gcdHilbertForm_re_nonnegative {Y : ℕ}
    (b : DivisorIndex Y → H) :
    0 ≤ (gcdHilbertForm b).re := by
  rw [gcdHilbertForm_eq_sum_inner_channels, Complex.re_sum]
  exact Finset.sum_nonneg fun d hd =>
    (@inner_self_nonneg ℂ H _ _ _ (gcdDivisorChannel b d))

end Hilbert

end DivisorGramArithmeticTransfer
end ZetaZero
