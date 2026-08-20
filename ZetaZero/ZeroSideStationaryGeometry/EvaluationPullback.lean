import ZetaZero.FiniteDimensionalInertiaReduction.NegativeIndex

/-!
# Finite evaluation pullback

This file isolates the finite-dimensional algebra needed before the analytic
packet evaluation theorem.  A strictly negative subspace cannot contain a
nonzero vector killed by the evaluation map when the target form vanishes at
zero.  Its image is therefore a strictly negative target subspace of the same
dimension.  The result is an upper-bound interface for the zero-side residue
pullback; surjectivity of the analytic packet evaluation map is intentionally
left as a later hypothesis.
-/

namespace ZetaZero
namespace ZeroSideStationaryGeometry

open FiniteDimensionalInertiaReduction

section EvaluationPullback

variable {𝕜 V W : Type*} [DivisionRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W]
  [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]

/-! Pull a real-valued target form back along a finite evaluation map. -/
def evaluationPullback (E : V →ₗ[𝕜] W) (q : W → ℝ) : V → ℝ :=
  fun x => q (E x)

/-! A witness records an actual strictly negative subspace of the indicated
dimension.  It is the lower-bound companion to `NegativeIndexLE`. -/
def NegativeIndexWitness (q : V → ℝ) (n : ℕ) : Prop :=
  ∃ N : Submodule 𝕜 V,
    StrictlyNegativeOn q N ∧ Module.finrank 𝕜 N = n

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
@[simp] theorem evaluationPullback_apply
    (E : V →ₗ[𝕜] W) (q : W → ℝ) (x : V) :
    evaluationPullback E q x = q (E x) := rfl

/-! A strictly negative source subspace maps to a strictly negative target
subspace.  Nonzero target vectors are enough to avoid any injectivity
assumption on the ambient evaluation map. -/
omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
theorem evaluationPullback_strictlyNegativeOn_map
    {E : V →ₗ[𝕜] W} {q : W → ℝ} {N : Submodule 𝕜 V}
    (hN : StrictlyNegativeOn (evaluationPullback E q) N) :
    StrictlyNegativeOn q (N.map E) := by
  intro y hy hy0
  rcases hy with ⟨x, hx, rfl⟩
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply hy0
    simp [hxzero]
  exact hN x hx hx0

/-! The evaluation map is injective after restricting to a strictly negative
subspace whenever the target form is zero at the origin. -/
omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
theorem evaluationPullback_domRestrict_injective
    {E : V →ₗ[𝕜] W} {q : W → ℝ} {N : Submodule 𝕜 V}
    (hq0 : q 0 = 0)
    (hN : StrictlyNegativeOn (evaluationPullback E q) N) :
    Function.Injective (E.domRestrict N) := by
  apply LinearMap.ker_eq_bot.mp
  refine (Submodule.eq_bot_iff _).2 ?_
  intro x hx
  apply Subtype.ext
  by_contra hx0
  have hneg := hN (x : V) x.property hx0
  have hzero : E (x : V) = 0 := hx
  have hqneg : q 0 < 0 := by
    simpa [evaluationPullback, hzero] using hneg
  rw [hq0] at hqneg
  exact (lt_irrefl 0) hqneg

/-! Main G2 acceptance theorem: a finite evaluation pullback cannot have more
strictly negative directions than its target form, provided the target form
vanishes at zero. -/
omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
theorem evaluationPullback_negativeIndexLE
    {E : V →ₗ[𝕜] W} {q : W → ℝ} {n : ℕ}
    (hq0 : q 0 = 0)
    (hq : NegativeIndexLE (𝕜 := 𝕜) q n) :
    NegativeIndexLE (𝕜 := 𝕜) (evaluationPullback E q) n := by
  intro N hN
  have hdom := evaluationPullback_domRestrict_injective hq0 hN
  have hdim := LinearMap.finrank_range_of_inj hdom
  have hrange : LinearMap.range (E.domRestrict N) = N.map E := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange] at hdim
  calc
    Module.finrank 𝕜 N = Module.finrank 𝕜 (N.map E) := hdim.symm
    _ ≤ n := hq (N.map E) (evaluationPullback_strictlyNegativeOn_map hN)

/-! A surjective evaluation map lifts an explicit target negative subspace by a
linear right inverse.  This is the lower-bound half of the future exact
`B(H) + P(H')` count; the analytic construction of the surjective map is not
part of this theorem. -/
omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
theorem evaluationPullback_negativeWitness_of_surjective
    {E : V →ₗ[𝕜] W} {q : W → ℝ} {n : ℕ}
    (hEsurj : Function.Surjective E)
    (hq : NegativeIndexWitness (𝕜 := 𝕜) q n) :
    NegativeIndexWitness (𝕜 := 𝕜) (evaluationPullback E q) n := by
  rcases hq with ⟨N, hN, hdimN⟩
  rcases E.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hEsurj) with
    ⟨s, hs⟩
  have hs_apply : ∀ y : W, E (s y) = y := by
    intro y
    have hy := congrArg (fun f => f y) hs
    simpa [LinearMap.comp_apply] using hy
  have hs_inj : Function.Injective (s.domRestrict N) := by
    intro x y hxy
    apply Subtype.ext
    change s (x : W) = s (y : W) at hxy
    calc
      (x : W) = E (s (x : W)) := (hs_apply (x : W)).symm
      _ = E (s (y : W)) := by rw [hxy]
      _ = (y : W) := hs_apply (y : W)
  have hstrict : StrictlyNegativeOn (evaluationPullback E q) (N.map s) := by
    intro x hx hx0
    rcases hx with ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := by
      intro hyzero
      apply hx0
      simp [hyzero]
    have hneg := hN y hy hy0
    simpa [evaluationPullback, hs_apply y] using hneg
  have hdim_map := LinearMap.finrank_range_of_inj hs_inj
  rw [LinearMap.range_domRestrict] at hdim_map
  refine ⟨N.map s, hstrict, ?_⟩
  calc
    Module.finrank 𝕜 (N.map s) = Module.finrank 𝕜 N := hdim_map
    _ = n := hdimN

/-! Acceptance certificate for the finite evaluation pullback: the upper bound
always transfers, and a target witness transfers when evaluation is surjective.
-/
omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
theorem evaluationPullback_negativeIndex_certificate
    {E : V →ₗ[𝕜] W} {q : W → ℝ} {n : ℕ}
    (hq0 : q 0 = 0)
    (hq : NegativeIndexLE (𝕜 := 𝕜) q n)
    (hEsurj : Function.Surjective E)
    (hqwitness : NegativeIndexWitness (𝕜 := 𝕜) q n) :
    NegativeIndexLE (𝕜 := 𝕜) (evaluationPullback E q) n ∧
      NegativeIndexWitness (𝕜 := 𝕜) (evaluationPullback E q) n := by
  exact ⟨evaluationPullback_negativeIndexLE hq0 hq,
    evaluationPullback_negativeWitness_of_surjective hEsurj hqwitness⟩

end EvaluationPullback

end ZeroSideStationaryGeometry
end ZetaZero
