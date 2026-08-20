import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Finite-level Minkowski interface for carrier coefficients

This module isolates the finite-dimensional Hilbert-space step used when several
HLP levels are assembled into one radial carrier.  It is completely independent
of the arithmetic estimates: those only have to bound the norm of each level.
-/

open Finset Real
open scoped BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- A finite scalar coefficient family viewed in the Euclidean coordinate space
indexed by a `Finset`. -/
def carrierVector
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) : EuclideanSpace ℝ {i // i ∈ s} :=
  WithLp.toLp 2 (fun i : {i // i ∈ s} => f i.1)

/-- The Euclidean norm of `carrierVector` is exactly the finite `ℓ²` norm. -/
theorem carrierVector_norm_sq
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) :
    ‖carrierVector s f‖ ^ 2 = ∑ i ∈ s, (f i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i : {i // i ∈ s}, (f i.1) ^ 2) = ∑ i ∈ s, (f i) ^ 2
  rw [← s.sum_attach, Finset.univ_eq_attach]

/-- Summing scalar carrier levels before forming the Euclidean vector is the same
as summing the corresponding Euclidean vectors. -/
theorem carrierVector_sum_levels
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (K : Finset κ) (a : κ → ι → ℝ) :
    carrierVector s (fun i => ∑ k ∈ K, a k i) =
      ∑ k ∈ K, carrierVector s (a k) := by
  ext i
  simp [carrierVector]

/-- Finite-dimensional Minkowski inequality in exactly the form needed for the
HLP carrier assembly. -/
theorem carrierVector_norm_sum_levels_le
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (K : Finset κ) (a : κ → ι → ℝ) :
    ‖carrierVector s (fun i => ∑ k ∈ K, a k i)‖ ≤
      ∑ k ∈ K, ‖carrierVector s (a k)‖ := by
  rw [carrierVector_sum_levels s K a]
  exact norm_sum_le K (fun k => carrierVector s (a k))

/-- Scalar square-sum version of finite Minkowski. -/
theorem sqrt_sum_sq_sum_levels_le
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (K : Finset κ) (a : κ → ι → ℝ) :
    Real.sqrt (∑ i ∈ s, (∑ k ∈ K, a k i) ^ 2) ≤
      ∑ k ∈ K, Real.sqrt (∑ i ∈ s, (a k i) ^ 2) := by
  have hnorm : ∀ f : ι → ℝ,
      ‖carrierVector s f‖ = Real.sqrt (∑ i ∈ s, (f i) ^ 2) := by
    intro f
    rw [← carrierVector_norm_sq s f, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  calc
    Real.sqrt (∑ i ∈ s, (∑ k ∈ K, a k i) ^ 2) =
        ‖carrierVector s (fun i => ∑ k ∈ K, a k i)‖ := by
      rw [hnorm]
    _ ≤ ∑ k ∈ K, ‖carrierVector s (a k)‖ :=
      carrierVector_norm_sum_levels_le s K a
    _ = ∑ k ∈ K, Real.sqrt (∑ i ∈ s, (a k i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hnorm]

/-- Support restriction cannot increase a nonnegative coefficient square sum. -/
theorem sum_sq_mono_of_subset
    {ι : Type*} [DecidableEq ι]
    {s t : Finset ι} (hst : s ⊆ t) (f : ι → ℝ) :
    (∑ i ∈ s, (f i) ^ 2) ≤ ∑ i ∈ t, (f i) ^ 2 := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hst
    (fun i hi hit => sq_nonneg (f i))

end HLPLocalModel
end ZetaZero
