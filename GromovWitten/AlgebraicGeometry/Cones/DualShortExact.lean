/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.DerivedCriteria
import GromovWitten.AlgebraicGeometry.ObstructionTheory.DeformationMeaning

/-!
# Dualising a short exact sequence of two-term complexes

A distinguished triangle with perfect third term becomes, in the two-term model of
`Cones/Criteria.lean`, a degreewise *split* short exact sequence `0 → K' → K → K'' → 0`.  Since
`Hom(-, N)` is exact on split sequences, the dual sequence is again short exact, both in the
fibrewise model `PicardCriteria.dualPoints _ B` of `Cones/CriteriaBundle.lean` and in the
module-coefficient model `PicardCriteria.dualComplex _ N` of
`ObstructionTheory/DeformationMeaning.lean`.  All the Picard-groupoid consequences of
`Cones/Criteria.lean` then apply to the duals, which is the statement "a distinguished triangle
with perfect third term gives a short exact sequence of abelian cone stacks".

## Main results

* `PicardCriteria.ShortExact.IsDegreewiseSplit`: the injection admits degreewise retractions;
  `ShortExact.isDegreewiseSplit_of_sections` and `ShortExact.exists_section_degreeZero` /
  `exists_section_degreeOne` prove the equivalence with the existence of degreewise sections
  (the splitting lemma, `exists_section_of_retraction` and `exists_retraction_of_section`), and
  `ShortExact.isDegreewiseSplit_of_projective` proves that a sequence with **projective** third
  term is automatically split.
* `PicardCriteria.ShortExact.shortExact_dualComplexHom` and `ShortExact.shortExact_dualHom`: the
  dual of a degreewise split short exact sequence is short exact, for every coefficient module
  `N` and for every test algebra `B`; all six fields are checked.
* `PicardCriteria.ShortExact.shortExactPicard_dualComplexHom` and `shortExactPicard_dualHom`:
  the resulting `ShortExactPicard` package — the functor `h¹/h⁰(Kᵛ) → h¹/h⁰(K'ᵛ)` induced by
  `i` is essentially surjective, its hom-fibres are torsors under `h⁰(K''ᵛ)` and its fibres on
  isomorphism classes are the orbits of the translation action of `h¹/h⁰(K''ᵛ)`.
* `PicardCriteria.ShortExact.injective_precompModule_cokernelMap`,
  `ker_precompModule_cokernelMap`, `dualDelta`, `ker_dualDelta`: the beginning of the six-term
  sequence of the duals, rewritten with `PicardCriteria.dualModuleH0Equiv` as
  `0 → Hom(h¹K'', N) → Hom(h¹K, N) → Hom(h¹K', N) → h¹(K''ᵛ) → h¹(Kᵛ) → h¹(K'ᵛ) → 0`
  (the last three terms are `exact_h1_left`, `exact_h1_middle`, `surjective_cokernelMap` of the
  dual sequence).  The first two statements need no splitting hypothesis.
* `PicardCriteria.ShortExact.isQuasiIsomorphism_of_acyclic_left` and
  `acyclic_of_isQuasiIsomorphism`: the two complements of
  `ShortExact.isQuasiIsomorphism_of_acyclic`.
* `PicardCriteria.shortExact_dualComplexHom_toCoker`, `shortExact_dualHom_toCoker` and their
  `ShortExactPicard` versions: the derived-triangle input.  A degreewise injective `φ` whose
  cokernel has projective terms ("perfect third term") gives, through
  `PicardCriteria.shortExact_toCoker`, a dual short exact sequence for every `N` and every `B`.
* `PicardCriteria.IsObstructionTheory.acyclic_coker`: for an obstruction theory which is
  degreewise injective the cokernel is acyclic — **both** `h⁰(coker φ)` and `h¹(coker φ)`
  vanish, because such a `φ` is already a quasi-isomorphism
  (`IsObstructionTheory.isQuasiIsomorphism`).  Hence the long exact sequence degenerates and,
  with a splitting, `IsObstructionTheory.isQuasiIsomorphism_dualComplexHom` /
  `isQuasiIsomorphism_dualHom` upgrade the fully faithful comparison of
  `IsObstructionTheory.isCohomologicalMono_dualComplexHom` to an **equivalence** of the dual
  Picard groupoids (`IsObstructionTheory.dualQuotientEquivalence`,
  `dualPointsQuotientEquivalence`).
-/

open CategoryTheory

universe u

namespace GromovWitten.AlgebraicGeometry

namespace PicardCriteria

open LinearTwoTermComplex

variable {R : Type u} [CommRing R]

/-! ## Splitting lemmas for modules -/

section Splitting

variable {M₁ M₂ M₃ N : Type u} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃] [AddCommGroup N] [Module R N]

/-- Precomposition with a surjection is injective on functionals. -/
theorem injective_comp_right_of_surjective {g : M₁ →ₗ[R] M₂} (hg : Function.Surjective g) :
    Function.Injective (fun l : M₂ →ₗ[R] N => l.comp g) := by
  intro l l' hll
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := hg y
  exact congrArg (fun m : M₁ →ₗ[R] N => m x) hll

/-- Precomposition with a split injection is surjective on functionals. -/
theorem surjective_comp_right_of_retraction {g : M₁ →ₗ[R] M₂} {r : M₂ →ₗ[R] M₁}
    (hr : ∀ x, r (g x) = x) : Function.Surjective (fun l : M₂ →ₗ[R] N => l.comp g) :=
  fun m => ⟨m.comp r, LinearMap.ext fun x => congrArg m (hr x)⟩

/-- **`Hom(-, N)` is exact in the middle on a sequence admitting a section.**  A functional
killed by the injection factors through the surjection. -/
theorem comp_eq_zero_iff_exists_comp {ι : M₁ →ₗ[R] M₂} {π : M₂ →ₗ[R] M₃}
    (hexact : LinearMap.ker π = LinearMap.range ι) {s : M₃ →ₗ[R] M₂} (hs : ∀ y, π (s y) = y)
    (l : M₂ →ₗ[R] N) : l.comp ι = 0 ↔ ∃ m : M₃ →ₗ[R] N, m.comp π = l := by
  constructor
  · intro hl
    refine ⟨l.comp s, LinearMap.ext fun x => ?_⟩
    have hmem : x - s (π x) ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, hs, sub_self]
    rw [hexact] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hzero : l (x - s (π x)) = 0 := by
      rw [← hy]
      exact congrArg (fun m : M₁ →ₗ[R] N => m y) hl
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  · rintro ⟨m, rfl⟩
    refine LinearMap.ext fun x => ?_
    have hzero : π (ι x) = 0 := by
      rw [← LinearMap.mem_ker, hexact]
      exact ⟨x, rfl⟩
    change m (π (ι x)) = 0
    rw [hzero, map_zero]

/-- **`Hom(-, N)` is left exact.**  For a surjection `π` whose kernel is the image of `ι`, a
functional killed by `ι` factors through `π`.  No splitting is needed here, only surjectivity. -/
theorem comp_eq_zero_iff_exists_comp_of_surjective {ι : M₁ →ₗ[R] M₂} {π : M₂ →ₗ[R] M₃}
    (hπ : Function.Surjective π) (hexact : LinearMap.ker π = LinearMap.range ι)
    (l : M₂ →ₗ[R] N) : l.comp ι = 0 ↔ ∃ m : M₃ →ₗ[R] N, m.comp π = l := by
  constructor
  · intro hl
    have hle : LinearMap.ker π ≤ LinearMap.ker l := by
      rw [hexact]
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      exact congrArg (fun m : M₁ →ₗ[R] N => m y) hl
    refine ⟨(Submodule.liftQ _ l hle).comp
      (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap, LinearMap.ext fun x => ?_⟩
    have hmk : (LinearMap.quotKerEquivOfSurjective π hπ).symm (π x) =
        Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    change (Submodule.liftQ _ l hle)
      ((LinearMap.quotKerEquivOfSurjective π hπ).symm (π x)) = l x
    rw [hmk, Submodule.liftQ_apply]
  · rintro ⟨m, rfl⟩
    refine LinearMap.ext fun x => ?_
    have hzero : π (ι x) = 0 := by
      rw [← LinearMap.mem_ker, hexact]
      exact ⟨x, rfl⟩
    change m (π (ι x)) = 0
    rw [hzero, map_zero]

/-- **Splitting lemma.**  A retraction of the injection of a short exact sequence of modules
produces a section of the surjection. -/
theorem exists_section_of_retraction {ι : M₁ →ₗ[R] M₂} {π : M₂ →ₗ[R] M₃}
    (hπ : Function.Surjective π) (hexact : LinearMap.ker π = LinearMap.range ι)
    {r : M₂ →ₗ[R] M₁} (hr : ∀ x, r (ι x) = x) :
    ∃ s : M₃ →ₗ[R] M₂, ∀ y, π (s y) = y := by
  have hcomp : ∀ z : M₁, π (ι z) = 0 := by
    intro z
    rw [← LinearMap.mem_ker, hexact]
    exact ⟨z, rfl⟩
  have hq : LinearMap.ker π ≤ LinearMap.ker (LinearMap.id - ι.comp r) := by
    intro x hx
    rw [hexact] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [LinearMap.mem_ker]
    change ι y - ι (r (ι y)) = 0
    rw [hr, sub_self]
  refine ⟨(Submodule.liftQ _ (LinearMap.id - ι.comp r) hq).comp
    (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hπ y
  have hmk : (LinearMap.quotKerEquivOfSurjective π hπ).symm (π x) =
      Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  change π ((Submodule.liftQ _ (LinearMap.id - ι.comp r) hq)
    ((LinearMap.quotKerEquivOfSurjective π hπ).symm (π x))) = π x
  rw [hmk, Submodule.liftQ_apply]
  change π (x - ι (r x)) = π x
  rw [map_sub, hcomp, sub_zero]

/-- **Splitting lemma.**  A section of the surjection of a short exact sequence of modules
produces a retraction of the injection. -/
theorem exists_retraction_of_section {ι : M₁ →ₗ[R] M₂} {π : M₂ →ₗ[R] M₃}
    (hι : Function.Injective ι) (hexact : LinearMap.ker π = LinearMap.range ι)
    {s : M₃ →ₗ[R] M₂} (hs : ∀ y, π (s y) = y) :
    ∃ r : M₂ →ₗ[R] M₁, ∀ x, r (ι x) = x := by
  have hcomp : ∀ z : M₁, π (ι z) = 0 := by
    intro z
    rw [← LinearMap.mem_ker, hexact]
    exact ⟨z, rfl⟩
  have hmem : ∀ x : M₂, ((LinearMap.id : M₂ →ₗ[R] M₂) - s.comp π) x ∈ LinearMap.range ι := by
    intro x
    rw [← hexact, LinearMap.mem_ker]
    change π (x - s (π x)) = 0
    rw [map_sub, hs, sub_self]
  refine ⟨(LinearEquiv.ofInjective ι hι).symm.toLinearMap.comp
    (((LinearMap.id : M₂ →ₗ[R] M₂) - s.comp π).codRestrict _ hmem), fun x => ?_⟩
  have hval : (((LinearMap.id : M₂ →ₗ[R] M₂) - s.comp π).codRestrict
      (LinearMap.range ι) hmem) (ι x) = LinearEquiv.ofInjective ι hι x := by
    apply Subtype.ext
    change ι x - s (π (ι x)) = ι x
    rw [hcomp, map_zero, sub_zero]
  change (LinearEquiv.ofInjective ι hι).symm
    ((((LinearMap.id : M₂ →ₗ[R] M₂) - s.comp π).codRestrict _ hmem) (ι x)) = x
  rw [hval, LinearEquiv.symm_apply_apply]

end Splitting

/-! ## Degreewise split short exact sequences of two-term complexes -/

section ShortExactSequences

variable {K' K K'' : LinearTwoTermComplex R} {i : Hom K' K} {p : Hom K K''}

namespace ShortExact

/-- A short exact sequence of two-term complexes is *degreewise split* when its injection admits
`R`-linear retractions in both degrees.  By the splitting lemma this is equivalent to the
existence of degreewise sections of the surjection
(`ShortExact.exists_section_degreeZero`, `ShortExact.isDegreewiseSplit_of_sections`). -/
def IsDegreewiseSplit (i : Hom K' K) : Prop :=
  (∃ r : K.degreeZero →ₗ[R] K'.degreeZero, ∀ x, r (i.degreeZero x) = x) ∧
    (∃ r : K.degreeOne →ₗ[R] K'.degreeOne, ∀ x, r (i.degreeOne x) = x)

/-- A degreewise split sequence has a section in degree zero. -/
theorem exists_section_degreeZero (h : ShortExact i p) (hs : IsDegreewiseSplit i) :
    ∃ s : K''.degreeZero →ₗ[R] K.degreeZero, ∀ y, p.degreeZero (s y) = y :=
  exists_section_of_retraction h.surjective_degreeZero h.exact_degreeZero hs.1.choose_spec

/-- A degreewise split sequence has a section in degree one. -/
theorem exists_section_degreeOne (h : ShortExact i p) (hs : IsDegreewiseSplit i) :
    ∃ s : K''.degreeOne →ₗ[R] K.degreeOne, ∀ y, p.degreeOne (s y) = y :=
  exists_section_of_retraction h.surjective_degreeOne h.exact_degreeOne hs.2.choose_spec

/-- Degreewise sections of the surjection give a degreewise splitting. -/
theorem isDegreewiseSplit_of_sections (h : ShortExact i p)
    (hzero : ∃ s : K''.degreeZero →ₗ[R] K.degreeZero, ∀ y, p.degreeZero (s y) = y)
    (hone : ∃ s : K''.degreeOne →ₗ[R] K.degreeOne, ∀ y, p.degreeOne (s y) = y) :
    IsDegreewiseSplit i :=
  ⟨exists_retraction_of_section h.injective_degreeZero h.exact_degreeZero hzero.choose_spec,
    exists_retraction_of_section h.injective_degreeOne h.exact_degreeOne hone.choose_spec⟩

/-- **A short exact sequence with projective third term is degreewise split.**  This is the
two-term form of "a distinguished triangle with perfect third term splits degreewise". -/
theorem isDegreewiseSplit_of_projective (h : ShortExact i p)
    [Module.Projective R K''.degreeZero] [Module.Projective R K''.degreeOne] :
    IsDegreewiseSplit i := by
  obtain ⟨s₀, hs₀⟩ := LinearMap.exists_rightInverse_of_surjective p.degreeZero
    (LinearMap.range_eq_top.2 h.surjective_degreeZero)
  obtain ⟨s₁, hs₁⟩ := LinearMap.exists_rightInverse_of_surjective p.degreeOne
    (LinearMap.range_eq_top.2 h.surjective_degreeOne)
  refine h.isDegreewiseSplit_of_sections ⟨s₀, fun y => ?_⟩ ⟨s₁, fun y => ?_⟩
  · exact congrArg (fun m : K''.degreeZero →ₗ[R] K''.degreeZero => m y) hs₀
  · exact congrArg (fun m : K''.degreeOne →ₗ[R] K''.degreeOne => m y) hs₁

/-! ### The dual sequence with module coefficients -/

/-- **The dual of a degreewise split short exact sequence is short exact**, for coefficients in
an arbitrary `R`-module `N`.  `Hom_R(-, N)` is exact on degreewise split sequences; all six
conditions are checked. -/
theorem shortExact_dualComplexHom (h : ShortExact i p) (hs : IsDegreewiseSplit i)
    (N : Type u) [AddCommGroup N] [Module R N] :
    ShortExact (dualComplexHom N p) (dualComplexHom N i) where
  injective_degreeZero := injective_comp_right_of_surjective h.surjective_degreeOne
  injective_degreeOne := injective_comp_right_of_surjective h.surjective_degreeZero
  surjective_degreeZero := surjective_comp_right_of_retraction hs.2.choose_spec
  surjective_degreeOne := surjective_comp_right_of_retraction hs.1.choose_spec
  exact_degreeZero := by
    refine SetLike.ext fun l => ?_
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    exact comp_eq_zero_iff_exists_comp h.exact_degreeOne
      (h.exists_section_degreeOne hs).choose_spec l
  exact_degreeOne := by
    refine SetLike.ext fun l => ?_
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    exact comp_eq_zero_iff_exists_comp h.exact_degreeZero
      (h.exists_section_degreeZero hs).choose_spec l

/-- **The dual sequence of `B`-points of a degreewise split short exact sequence is short
exact**, for every `R`-algebra `B`: the fibrewise dual model of
`Cones/CriteriaBundle.lean` turns a degreewise split short exact sequence of two-term complexes
into a short exact sequence of complexes of `B`-points. -/
theorem shortExact_dualHom (h : ShortExact i p) (hs : IsDegreewiseSplit i)
    (B : Type u) [CommRing B] [Algebra R B] :
    ShortExact (dualHom p B) (dualHom i B) where
  injective_degreeZero := injective_comp_right_of_surjective h.surjective_degreeOne
  injective_degreeOne := injective_comp_right_of_surjective h.surjective_degreeZero
  surjective_degreeZero := surjective_comp_right_of_retraction hs.2.choose_spec
  surjective_degreeOne := surjective_comp_right_of_retraction hs.1.choose_spec
  exact_degreeZero := by
    refine SetLike.ext fun l => ?_
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    exact comp_eq_zero_iff_exists_comp h.exact_degreeOne
      (h.exists_section_degreeOne hs).choose_spec l
  exact_degreeOne := by
    refine SetLike.ext fun l => ?_
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    exact comp_eq_zero_iff_exists_comp h.exact_degreeZero
      (h.exists_section_degreeZero hs).choose_spec l

/-! ### Consequences for the dual Picard groupoids -/

/-- **The dual sequence of Picard groupoids.**  For coefficients in a module `N`, the functor
`h¹/h⁰(Kᵛ) → h¹/h⁰(K'ᵛ)` induced by `i` is essentially surjective, its fibres on hom-sets are
torsors under `h⁰(K''ᵛ)` and its fibres on isomorphism classes are the orbits of the translation
action of `h¹/h⁰(K''ᵛ)`. -/
theorem shortExactPicard_dualComplexHom (h : ShortExact i p) (hs : IsDegreewiseSplit i)
    (N : Type u) [AddCommGroup N] [Module R N] :
    ShortExactPicard (dualComplexHom N p) (dualComplexHom N i) :=
  (h.shortExact_dualComplexHom hs N).shortExactPicard

/-- **The dual sequence of Picard groupoids of `B`-points**, that is, of the fibres of the
abelian cone stacks `h¹/h⁰(Kᵛ)` over the affine test scheme `Spec B`. -/
theorem shortExactPicard_dualHom (h : ShortExact i p) (hs : IsDegreewiseSplit i)
    (B : Type u) [CommRing B] [Algebra R B] :
    ShortExactPicard (dualHom p B) (dualHom i B) :=
  (h.shortExact_dualHom hs B).shortExactPicard

/-! ### The six-term sequence of the duals -/

/-- `Hom(-, N)` applied to `h¹K' → h¹K → h¹K'' → 0` is injective on the right: no splitting
hypothesis is needed for this part of the six-term sequence. -/
theorem injective_precompModule_cokernelMap (h : ShortExact i p)
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Injective (precompModule p.cokernelMap N) :=
  injective_comp_right_of_surjective h.surjective_cokernelMap

/-- Exactness of `Hom(h¹K'', N) → Hom(h¹K, N) → Hom(h¹K', N)` in the middle; again no splitting
hypothesis is needed. -/
theorem ker_precompModule_cokernelMap (h : ShortExact i p)
    (N : Type u) [AddCommGroup N] [Module R N] :
    LinearMap.ker (precompModule i.cokernelMap N) =
      LinearMap.range (precompModule p.cokernelMap N) := by
  refine SetLike.ext fun l => ?_
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  exact comp_eq_zero_iff_exists_comp_of_surjective h.surjective_cokernelMap h.exact_h1_middle l

/-- The connecting homomorphism of the dual sequence, read through
`PicardCriteria.dualModuleH0Equiv` as a map `Hom(h¹K', N) → h¹(K''ᵛ)`.  Together with
`injective_precompModule_cokernelMap`, `ker_precompModule_cokernelMap` and `ker_dualDelta` this
is the beginning of the six-term sequence

`0 → Hom(h¹K'', N) → Hom(h¹K, N) → Hom(h¹K', N) → h¹(K''ᵛ) → h¹(Kᵛ) → h¹(K'ᵛ) → 0`. -/
noncomputable def dualDelta (h : ShortExact i p) (hs : IsDegreewiseSplit i)
    (N : Type u) [AddCommGroup N] [Module R N] :
    (h1 K' →ₗ[R] N) →ₗ[R] h1 (dualComplex K'' N) :=
  (h.shortExact_dualComplexHom hs N).delta.comp (dualModuleH0Equiv N K').symm.toLinearMap

/-- Exactness of the six-term sequence of the duals at `Hom(h¹K', N)`. -/
theorem ker_dualDelta (h : ShortExact i p) (hs : IsDegreewiseSplit i)
    (N : Type u) [AddCommGroup N] [Module R N] :
    LinearMap.ker (dualDelta h hs N) = LinearMap.range (precompModule i.cokernelMap N) := by
  refine SetLike.ext fun l => ?_
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hl
    have hmem : (dualModuleH0Equiv N K').symm l ∈
        LinearMap.ker (h.shortExact_dualComplexHom hs N).delta := hl
    rw [(h.shortExact_dualComplexHom hs N).exact_h0_right] at hmem
    obtain ⟨m, hm⟩ := hmem
    refine ⟨dualModuleH0Equiv N K m, ?_⟩
    have hcomm := dualModuleH0Equiv_kernelMap N i m
    rw [hm, LinearEquiv.apply_symm_apply] at hcomm
    exact hcomm.symm
  · rintro ⟨m, rfl⟩
    have hcomm := dualModuleH0Equiv_kernelMap N i ((dualModuleH0Equiv N K).symm m)
    rw [LinearEquiv.apply_symm_apply] at hcomm
    have hmem : (dualModuleH0Equiv N K').symm (precompModule i.cokernelMap N m) ∈
        LinearMap.range (dualComplexHom N i).kernelMap := by
      refine ⟨(dualModuleH0Equiv N K).symm m, ?_⟩
      apply (dualModuleH0Equiv N K').injective
      rw [LinearEquiv.apply_symm_apply]
      exact hcomm
    rw [← (h.shortExact_dualComplexHom hs N).exact_h0_right, LinearMap.mem_ker] at hmem
    exact hmem

/-! ### Acyclic sub- and quotient complexes -/

/-- **If the sub-complex of a short exact sequence is acyclic then the surjection is a
quasi-isomorphism.**  This is the counterpart of
`PicardCriteria.ShortExact.isQuasiIsomorphism_of_acyclic`, for the other end of the sequence. -/
theorem isQuasiIsomorphism_of_acyclic_left (h : ShortExact i p)
    (hzero : ∀ c : h0 K', c = 0) (hone : ∀ q : h1 K', q = 0) :
    p.IsQuasiIsomorphism := by
  refine ⟨⟨?_, ?_⟩, ?_, h.surjective_cokernelMap⟩
  · intro a b hab
    have hmem : a - b ∈ LinearMap.ker p.kernelMap := by
      rw [LinearMap.mem_ker, map_sub, hab, sub_self]
    rw [h.exact_h0_middle] at hmem
    obtain ⟨c, hc⟩ := hmem
    rw [hzero c, map_zero] at hc
    exact sub_eq_zero.1 hc.symm
  · intro c
    have hmem : c ∈ LinearMap.ker h.delta := by
      rw [LinearMap.mem_ker]
      exact hone _
    rw [h.exact_h0_right] at hmem
    exact hmem
  · intro a b hab
    have hmem : a - b ∈ LinearMap.ker p.cokernelMap := by
      rw [LinearMap.mem_ker, map_sub, hab, sub_self]
    rw [h.exact_h1_middle] at hmem
    obtain ⟨q, hq⟩ := hmem
    rw [hone q, map_zero] at hq
    exact sub_eq_zero.1 hq.symm

/-- **If the injection of a short exact sequence is a quasi-isomorphism then the quotient
complex is acyclic.**  This is the converse of
`PicardCriteria.ShortExact.isQuasiIsomorphism_of_acyclic`. -/
theorem acyclic_of_isQuasiIsomorphism (h : ShortExact i p) (hi : i.IsQuasiIsomorphism) :
    (∀ c : h0 K'', c = 0) ∧ (∀ q : h1 K'', q = 0) := by
  constructor
  · intro c
    have hdelta : h.delta c = 0 := by
      have hmem : h.delta c ∈ LinearMap.range h.delta := ⟨c, rfl⟩
      rw [← h.exact_h1_left, LinearMap.mem_ker] at hmem
      have := hi.2.1 (a₁ := h.delta c) (a₂ := 0)
      rw [map_zero] at this
      exact this hmem
    have hmem : c ∈ LinearMap.ker h.delta := by
      rw [LinearMap.mem_ker]
      exact hdelta
    rw [h.exact_h0_right] at hmem
    obtain ⟨a, rfl⟩ := hmem
    obtain ⟨b, rfl⟩ := hi.1.2 a
    apply Subtype.ext
    change p.degreeZero (i.degreeZero (b : K'.degreeZero)) = 0
    exact h.comp_degreeZero _
  · intro q
    obtain ⟨t, rfl⟩ := h.surjective_cokernelMap q
    obtain ⟨s, rfl⟩ := hi.2.2 t
    obtain ⟨b, rfl⟩ := h1mk_surjective s
    change p.cokernelMap (h1mk K (i.degreeOne b)) = 0
    rw [cokernelMap_h1mk, h.comp_degreeOne]
    exact h1mk_zero

end ShortExact

end ShortExactSequences

/-! ## Perfect third term -/

section Coker

variable {E L : LinearTwoTermComplex R} (φ : Hom E L)

/-- **The dual of the cokernel sequence of a degreewise injective chain map with projective
cokernel.**  This is the two-term form of "a distinguished triangle with perfect third term
dualises to a short exact sequence of abelian cone stacks", with module coefficients. -/
theorem shortExact_dualComplexHom_toCoker (hzero : Function.Injective φ.degreeZero)
    (hone : Function.Injective φ.degreeOne)
    [Module.Projective R (coker φ).degreeZero] [Module.Projective R (coker φ).degreeOne]
    (N : Type u) [AddCommGroup N] [Module R N] :
    ShortExact (dualComplexHom N (toCoker φ)) (dualComplexHom N φ) :=
  (shortExact_toCoker φ hzero hone).shortExact_dualComplexHom
    (shortExact_toCoker φ hzero hone).isDegreewiseSplit_of_projective N

/-- The same for the complexes of `B`-points: the dual sequence of abelian cone stacks over the
affine test scheme `Spec B`. -/
theorem shortExact_dualHom_toCoker (hzero : Function.Injective φ.degreeZero)
    (hone : Function.Injective φ.degreeOne)
    [Module.Projective R (coker φ).degreeZero] [Module.Projective R (coker φ).degreeOne]
    (B : Type u) [CommRing B] [Algebra R B] :
    ShortExact (dualHom (toCoker φ) B) (dualHom φ B) :=
  (shortExact_toCoker φ hzero hone).shortExact_dualHom
    (shortExact_toCoker φ hzero hone).isDegreewiseSplit_of_projective B

/-- **The dual sequence of Picard groupoids attached to a perfect third term.**  For every
coefficient module `N`, the functor `h¹/h⁰(Lᵛ) → h¹/h⁰(Eᵛ)` is essentially surjective with
hom-fibres torsors under `h⁰((coker φ)ᵛ)` and iso-fibres the orbits of `h¹/h⁰((coker φ)ᵛ)`. -/
theorem shortExactPicard_dualComplexHom_toCoker (hzero : Function.Injective φ.degreeZero)
    (hone : Function.Injective φ.degreeOne)
    [Module.Projective R (coker φ).degreeZero] [Module.Projective R (coker φ).degreeOne]
    (N : Type u) [AddCommGroup N] [Module R N] :
    ShortExactPicard (dualComplexHom N (toCoker φ)) (dualComplexHom N φ) :=
  (shortExact_dualComplexHom_toCoker φ hzero hone N).shortExactPicard

/-- The same over an arbitrary affine test scheme `Spec B`. -/
theorem shortExactPicard_dualHom_toCoker (hzero : Function.Injective φ.degreeZero)
    (hone : Function.Injective φ.degreeOne)
    [Module.Projective R (coker φ).degreeZero] [Module.Projective R (coker φ).degreeOne]
    (B : Type u) [CommRing B] [Algebra R B] :
    ShortExactPicard (dualHom (toCoker φ) B) (dualHom φ B) :=
  (shortExact_dualHom_toCoker φ hzero hone B).shortExactPicard

end Coker

/-! ## The case of an obstruction theory -/

section Obstruction

variable {E L : LinearTwoTermComplex R} {φ : Hom E L}

/-- **A degreewise injective obstruction theory is a quasi-isomorphism.**  `H⁰(φ)` is bijective
by assumption and `H⁻¹(φ)` is surjective by assumption and injective because `φ` is injective in
degree zero. -/
theorem IsObstructionTheory.isQuasiIsomorphism (h : IsObstructionTheory φ)
    (hzero : Function.Injective φ.degreeZero) : φ.IsQuasiIsomorphism :=
  ⟨⟨fun _ _ hab => Subtype.ext (hzero (congrArg Subtype.val hab)), h.surjective_kernelMap⟩,
    h.bijective_cokernelMap⟩

/-- **The cokernel of a degreewise injective obstruction theory is acyclic**: both `h⁰` and `h¹`
of `coker φ` vanish.  So the long exact sequence of the cokernel sequence degenerates
completely; in particular it is *not* only `h¹(coker φ)` that vanishes. -/
theorem IsObstructionTheory.acyclic_coker (h : IsObstructionTheory φ)
    (hzero : Function.Injective φ.degreeZero) (hone : Function.Injective φ.degreeOne) :
    (∀ c : h0 (coker φ), c = 0) ∧ (∀ q : h1 (coker φ), q = 0) :=
  (shortExact_toCoker φ hzero hone).acyclic_of_isQuasiIsomorphism (h.isQuasiIsomorphism hzero)

/-- The differential of an acyclic two-term complex is bijective. -/
theorem bijective_differential_of_acyclic (C : LinearTwoTermComplex R)
    (hzero : ∀ c : h0 C, c = 0) (hone : ∀ q : h1 C, q = 0) :
    Function.Bijective C.differential := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    refine le_antisymm (fun x hx => ?_) bot_le
    have hx0 : (⟨x, hx⟩ : h0 C) = 0 := hzero _
    exact congrArg Subtype.val hx0
  · intro y
    have hy : h1mk C y = 0 := hone _
    exact (h1mk_eq_zero_iff (E := C) y).1 hy

/-- **The dual of an acyclic two-term complex is acyclic**, for every coefficient module: the
differential of an acyclic two-term complex is bijective, hence so is precomposition with it. -/
theorem acyclic_dualComplex (C : LinearTwoTermComplex R) (hzero : ∀ c : h0 C, c = 0)
    (hone : ∀ q : h1 C, q = 0) (N : Type u) [AddCommGroup N] [Module R N] :
    (∀ c : h0 (dualComplex C N), c = 0) ∧ (∀ q : h1 (dualComplex C N), q = 0) := by
  have hbij := bijective_differential_of_acyclic C hzero hone
  have hdualInj : Function.Injective (precompModule C.differential N) :=
    injective_comp_right_of_surjective hbij.2
  have hdualSurj : Function.Surjective (precompModule C.differential N) :=
    surjective_comp_right_of_retraction (r := (LinearEquiv.ofBijective _ hbij).symm.toLinearMap)
      (fun x => (LinearEquiv.ofBijective _ hbij).symm_apply_apply x)
  constructor
  · intro c
    apply Subtype.ext
    have hc : precompModule C.differential N (c : (dualComplex C N).degreeZero) = 0 := c.2
    have hz := hdualInj (a₁ := (c : (dualComplex C N).degreeZero)) (a₂ := 0)
    rw [map_zero] at hz
    exact hz hc
  · intro q
    obtain ⟨l, rfl⟩ := h1mk_surjective q
    obtain ⟨m, hm⟩ := hdualSurj l
    rw [h1mk_eq_zero_iff]
    exact ⟨m, hm⟩

/-- **The complex of `B`-points of the dual of an acyclic two-term complex is acyclic**, for
every `R`-algebra `B`. -/
theorem acyclic_dualPoints (C : LinearTwoTermComplex R) (hzero : ∀ c : h0 C, c = 0)
    (hone : ∀ q : h1 C, q = 0) (B : Type u) [CommRing B] [Algebra R B] :
    (∀ c : h0 (dualPoints C B), c = 0) ∧ (∀ q : h1 (dualPoints C B), q = 0) := by
  have hbij := bijective_differential_of_acyclic C hzero hone
  have hdualInj : Function.Injective (precomp C.differential B) :=
    injective_comp_right_of_surjective hbij.2
  have hdualSurj : Function.Surjective (precomp C.differential B) :=
    surjective_comp_right_of_retraction (r := (LinearEquiv.ofBijective _ hbij).symm.toLinearMap)
      (fun x => (LinearEquiv.ofBijective _ hbij).symm_apply_apply x)
  constructor
  · intro c
    apply Subtype.ext
    have hc : precomp C.differential B (c : (dualPoints C B).degreeZero) = 0 := c.2
    have hz := hdualInj (a₁ := (c : (dualPoints C B).degreeZero)) (a₂ := 0)
    rw [map_zero] at hz
    exact hz hc
  · intro q
    obtain ⟨l, rfl⟩ := h1mk_surjective q
    obtain ⟨m, hm⟩ := hdualSurj l
    rw [h1mk_eq_zero_iff]
    exact ⟨m, hm⟩

/-- **For a degreewise injective obstruction theory with degreewise split cokernel sequence, the
dual chain map is a quasi-isomorphism**, for every coefficient module.  The six-term sequence of
the dual sequence degenerates because the dual of the acyclic complex `coker φ` is acyclic. -/
theorem IsObstructionTheory.isQuasiIsomorphism_dualComplexHom (h : IsObstructionTheory φ)
    (hzero : Function.Injective φ.degreeZero) (hone : Function.Injective φ.degreeOne)
    (hs : ShortExact.IsDegreewiseSplit φ) (N : Type u) [AddCommGroup N] [Module R N] :
    (dualComplexHom N φ).IsQuasiIsomorphism := by
  obtain ⟨hc0, hc1⟩ := h.acyclic_coker hzero hone
  obtain ⟨hd0, hd1⟩ := acyclic_dualComplex (coker φ) hc0 hc1 N
  exact ((shortExact_toCoker φ hzero hone).shortExact_dualComplexHom hs N)
    |>.isQuasiIsomorphism_of_acyclic_left hd0 hd1

/-- **The dual Picard groupoids of a degreewise injective obstruction theory with split cokernel
sequence are equivalent**: `h¹/h⁰(Lᵛ)(N) ≌ h¹/h⁰(Eᵛ)(N)`.  Without the injectivity and
splitting hypotheses only the fully faithful comparison of
`PicardCriteria.IsObstructionTheory.isCohomologicalMono_dualComplexHom` is available. -/
noncomputable def IsObstructionTheory.dualQuotientEquivalence (h : IsObstructionTheory φ)
    (hzero : Function.Injective φ.degreeZero) (hone : Function.Injective φ.degreeOne)
    (hs : ShortExact.IsDegreewiseSplit φ) (N : Type u) [AddCommGroup N] [Module R N] :
    (dualComplex L N).quotient ≌ (dualComplex E N).quotient :=
  (h.isQuasiIsomorphism_dualComplexHom hzero hone hs N).quotientEquivalence

/-- **The same over an arbitrary affine test scheme.**  For a degreewise injective obstruction
theory with degreewise split cokernel sequence, the dualised chain map of `B`-points is a
quasi-isomorphism, so `h¹/h⁰(Lᵛ)(B) ≌ h¹/h⁰(Eᵛ)(B)`. -/
theorem IsObstructionTheory.isQuasiIsomorphism_dualHom (h : IsObstructionTheory φ)
    (hzero : Function.Injective φ.degreeZero) (hone : Function.Injective φ.degreeOne)
    (hs : ShortExact.IsDegreewiseSplit φ) (B : Type u) [CommRing B] [Algebra R B] :
    (dualHom φ B).IsQuasiIsomorphism := by
  obtain ⟨hc0, hc1⟩ := h.acyclic_coker hzero hone
  obtain ⟨hd0, hd1⟩ := acyclic_dualPoints (coker φ) hc0 hc1 B
  exact ((shortExact_toCoker φ hzero hone).shortExact_dualHom hs B)
    |>.isQuasiIsomorphism_of_acyclic_left hd0 hd1

/-- The equivalence of the fibres over `Spec B` of the two abelian cone stacks. -/
noncomputable def IsObstructionTheory.dualPointsQuotientEquivalence (h : IsObstructionTheory φ)
    (hzero : Function.Injective φ.degreeZero) (hone : Function.Injective φ.degreeOne)
    (hs : ShortExact.IsDegreewiseSplit φ) (B : Type u) [CommRing B] [Algebra R B] :
    (dualPoints L B).quotient ≌ (dualPoints E B).quotient :=
  (h.isQuasiIsomorphism_dualHom hzero hone hs B).quotientEquivalence

/-- The splitting hypothesis is automatic when the cokernel has projective terms. -/
theorem IsObstructionTheory.isQuasiIsomorphism_dualComplexHom_of_projective
    (h : IsObstructionTheory φ) (hzero : Function.Injective φ.degreeZero)
    (hone : Function.Injective φ.degreeOne)
    [Module.Projective R (coker φ).degreeZero] [Module.Projective R (coker φ).degreeOne]
    (N : Type u) [AddCommGroup N] [Module R N] :
    (dualComplexHom N φ).IsQuasiIsomorphism :=
  h.isQuasiIsomorphism_dualComplexHom hzero hone
    (shortExact_toCoker φ hzero hone).isDegreewiseSplit_of_projective N

end Obstruction

end PicardCriteria

end GromovWitten.AlgebraicGeometry
