import ZetaZero.FiniteDimensionalInertiaReduction.FiniteRankPerturbation
import Mathlib.Tactic

/-!
# M08: coefficient-free fixed edge range

The revised unconditional route uses the fact that all retained low-sideband
pieces of the direct exact--model residual land in one fixed edge coordinate
space.  Hence changing coefficients, signs, or the number of retained HLP
levels does not enlarge the deletion space.

This file isolates that algebraic mechanism.  It deliberately proves the
finite-partial-sum statement first; this is the stable rank interface needed
before adding the topological passage to a norm-convergent infinite hierarchy.
-/

namespace ZetaZero
namespace FrameCompression

section Basic

variable {𝕜 V W : Type*} [DivisionRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W]

/-- If two operators land in the same fixed subspace, then so does their sum. -/
theorem range_add_le_fixed
    (S : Submodule 𝕜 W) (A B : V →ₗ[𝕜] W)
    (hA : LinearMap.range A ≤ S) (hB : LinearMap.range B ≤ S) :
    LinearMap.range (A + B) ≤ S := by
  rintro y ⟨x, rfl⟩
  rw [LinearMap.add_apply]
  exact S.add_mem (hA ⟨x, rfl⟩) (hB ⟨x, rfl⟩)

/-- Every finite sum of operators whose ranges lie in one fixed edge space has
range in that same space.  In particular the rank cost is coefficient-count
independent. -/
theorem range_finset_sum_le_fixed
    {ι : Type*} (s : Finset ι) (E : ι → V →ₗ[𝕜] W)
    (S : Submodule 𝕜 W)
    (hE : ∀ i ∈ s, LinearMap.range (E i) ≤ S) :
    LinearMap.range (∑ i ∈ s, E i) ≤ S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply range_add_le_fixed S
      · exact hE a (Finset.mem_insert_self a s)
      · exact ih (fun i hi => hE i (Finset.mem_insert_of_mem hi))

/-- A finite family sharing a fixed edge space has rank bounded by the dimension
of that space, not by the number of summands. -/
theorem finrank_range_finset_sum_le_fixed
    [FiniteDimensional 𝕜 W]
    {ι : Type*} (s : Finset ι) (E : ι → V →ₗ[𝕜] W)
    (S : Submodule 𝕜 W) {r : ℕ}
    (hE : ∀ i ∈ s, LinearMap.range (E i) ≤ S)
    (hS : Module.finrank 𝕜 S ≤ r) :
    Module.finrank 𝕜 (LinearMap.range (∑ i ∈ s, E i)) ≤ r := by
  exact (Submodule.finrank_mono (range_finset_sum_le_fixed s E S hE)).trans hS

/-- Kernel/codimension form of the same coefficient-free deletion budget. -/
theorem codim_ker_finset_sum_le_fixed
    [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    {ι : Type*} (s : Finset ι) (E : ι → V →ₗ[𝕜] W)
    (S : Submodule 𝕜 W) {r : ℕ}
    (hE : ∀ i ∈ s, LinearMap.range (E i) ≤ S)
    (hS : Module.finrank 𝕜 S ≤ r) :
    FiniteDimensionalInertiaReduction.codim
        (LinearMap.ker (∑ i ∈ s, E i)) ≤ r := by
  apply FiniteDimensionalInertiaReduction.codim_ker_le
  exact finrank_range_finset_sum_le_fixed s E S hE hS

end Basic

end FrameCompression
end ZetaZero
