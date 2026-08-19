import ZetaZero.FiniteDimensionalInertiaReduction.RealNegativeIndex
import Mathlib.Tactic

/-!
# Finite-dimensional inertia reduction: congruence transport

The manuscript whitens a positive reference form before applying the spectral
argument.  M01 should not depend on a particular matrix-square-root API, so this
module records the invariant algebraic content: an invertible linear change of
coordinates preserves subspace dimensions and negative-index bounds.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section CongruenceTransport

variable {𝕜 V W : Type*} [DivisionRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W]

/-- Pull a real-valued form back along an invertible linear change of
coordinates. -/
def pullbackForm (e : V ≃ₗ[𝕜] W) (q : W → ℝ) : V → ℝ :=
  fun x => q (e x)

/-- Transport a subspace in whitened coordinates back to physical
coordinates. -/
def transportedSubspace (e : V ≃ₗ[𝕜] W) (S : Submodule 𝕜 W) :
    Submodule 𝕜 V :=
  S.map e.symm.toLinearMap

/-- Membership in the transported subspace is tested after applying the forward
coordinate change. -/
theorem mem_transportedSubspace_iff
    (e : V ≃ₗ[𝕜] W) (S : Submodule 𝕜 W) {x : V} :
    x ∈ transportedSubspace e S ↔ e x ∈ S := by
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    refine ⟨e x, hx, ?_⟩
    simp

/-- Codimension is unchanged by an invertible linear coordinate change. -/
theorem codim_transportedSubspace_eq
    [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    (e : V ≃ₗ[𝕜] W) (S : Submodule 𝕜 W) :
    codim (transportedSubspace e S) = codim S := by
  have hmap := e.symm.finrank_map_eq S
  have hambient := e.finrank_eq
  have hleft := (transportedSubspace e S).finrank_quotient_add_finrank
  have hright := S.finrank_quotient_add_finrank
  unfold transportedSubspace at hleft ⊢
  unfold codim
  lia

/-- A strictly negative subspace for a pulled-back form maps to a strictly
negative subspace in the new coordinates. -/
theorem strictlyNegativeOn_map_linearEquiv
    (e : V ≃ₗ[𝕜] W) {q : W → ℝ} {N : Submodule 𝕜 V}
    (hN : StrictlyNegativeOn (pullbackForm e q) N) :
    StrictlyNegativeOn q (N.map e.toLinearMap) := by
  intro y hy hy0
  rcases hy with ⟨x, hx, rfl⟩
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hy0
    simp [hzero]
  simpa [pullbackForm] using hN x hx hx0

/-- A negative-index bound is invariant under invertible linear congruence. -/
theorem negativeIndexBound_pullback
    (e : V ≃ₗ[𝕜] W) {q : W → ℝ} {b : ℝ}
    (hq : NegativeIndexBound (𝕜 := 𝕜) q b) :
    NegativeIndexBound (𝕜 := 𝕜) (pullbackForm e q) b := by
  intro N hN
  have hneg := strictlyNegativeOn_map_linearEquiv e hN
  have hbound := hq (N.map e.toLinearMap) hneg
  rw [e.finrank_map_eq N] at hbound
  exact hbound

/-- The pulled-back formulation is equivalent to the original one. -/
theorem negativeIndexBound_pullback_iff
    (e : V ≃ₗ[𝕜] W) {q : W → ℝ} {b : ℝ} :
    NegativeIndexBound (𝕜 := 𝕜) (pullbackForm e q) b ↔
      NegativeIndexBound (𝕜 := 𝕜) q b := by
  constructor
  · intro h
    have hback := negativeIndexBound_pullback (e := e.symm) h
    have heq : pullbackForm e.symm (pullbackForm e q) = q := by
      funext y
      simp [pullbackForm]
    rw [heq] at hback
    exact hback
  · exact negativeIndexBound_pullback e

/-- Nonnegativity on a good subspace is preserved when that subspace is
transported back to physical coordinates. -/
theorem nonnegativeOn_pullback_transportedSubspace
    (e : V ≃ₗ[𝕜] W) {q : W → ℝ} {S : Submodule 𝕜 W}
    (hS : NonnegativeOn q S) :
    NonnegativeOn (pullbackForm e q) (transportedSubspace e S) := by
  intro x hx
  exact hS (e x) ((mem_transportedSubspace_iff e S).1 hx)

/-- Any pointwise lower bound on a whitened good space transports verbatim to
its physical-coordinate pullback. -/
theorem lower_bound_on_transportedSubspace
    (e : V ≃ₗ[𝕜] W) {a g : W → ℝ} {c : ℝ} {S : Submodule 𝕜 W}
    (h : ∀ y, y ∈ S → c * g y ≤ a y) :
    ∀ x, x ∈ transportedSubspace e S →
      c * pullbackForm e g x ≤ pullbackForm e a x := by
  intro x hx
  exact h (e x) ((mem_transportedSubspace_iff e S).1 hx)

end CongruenceTransport

end FiniteDimensionalInertiaReduction
end ZetaZero
