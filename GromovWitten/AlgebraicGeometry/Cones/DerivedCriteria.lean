/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.Criteria
import GromovWitten.AlgebraicGeometry.Cones.DerivedPicard
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Derived-category form of the `h¹/h⁰` criteria

`Cones/Picard.lean` and `Cones/Criteria.lean` develop the Picard groupoid `[E¹/E⁰]` of a
two-term complex of modules through the elementwise cohomology modules `h⁰ = ker` and
`h¹ = coker`.  This file identifies that elementwise theory with Mathlib's homological algebra
and transports it to the derived category of `R`-modules.

## Main results

* `LinearTwoTermComplex.toCochainComplexHom`: a chain map of two-term complexes as a morphism of
  cochain complexes; `ofCochainComplex_toCochainComplex` and
  `ofCochainComplexHom_toCochainComplexHom` say that this is inverse to the restriction functor
  of `Cones/DerivedPicard.lean`.
* `LinearTwoTermComplex.homologyNegOneIso`, `homologyZeroIso`: the homology of a complex of
  modules supported in degrees `-1` and `0` is the kernel, respectively the cokernel, of its
  differential; `isZero_homology_toCochainComplex` kills every other degree.
* `LinearTwoTermComplex.isQuasiIsomorphism_iff_quasiIso` and
  `isQuasiIsomorphism_ofCochainComplexHom_iff`: the elementwise predicate
  `Hom.IsQuasiIsomorphism` (bijectivity on `h⁰` and `h¹`) is *equivalent* to Mathlib's `QuasiIso`;
  `isIso_Q_map_toCochainComplexHom_iff` restates this as invertibility in `D(R)`.
* `PicardCriteria.ShortExact.cochainShortExact`: a degreewise short exact sequence of two-term
  complexes is a short exact sequence of cochain complexes, hence
  `ShortExact.triangleOfSES_distinguished` gives a distinguished triangle in `D(R)` and
  `ShortExact.quasiIso_descShortComplex` identifies the mapping cone of the inclusion with the
  quotient complex.  Conversely `PicardCriteria.shortExact_toCoker` produces a short exact
  sequence from any degreewise injective chain map, with `LinearTwoTermComplex.coker` as
  quotient, and `ShortExact.shortExactPicard` packages the Picard-groupoid content.
* `CotangentComplex.PerfectComplex.GlobalTwoTermResolution.Comparison.nonempty_homotopy` and
  `picardEquivalence_unique_up_to_natIso`: the chain map realizing the comparison of two global
  two-term resolutions is unique up to homotopy, so the induced equivalence of Picard groupoids
  is canonical up to natural isomorphism (and so is its inverse).

What is *not* proved here: the connecting homomorphism `PicardCriteria.ShortExact.delta` is not
yet identified with Mathlib's connecting map `ShortComplex.ShortExact.δ` of the long exact
homology sequence (both exist, and the exact sequences they sit in are proved, but the
comparison of the two constructions is missing).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace GromovWitten.AlgebraicGeometry

namespace LinearTwoTermComplex

variable {R : Type u} [CommRing R] {E F : LinearTwoTermComplex R}

/-! ## The cochain map attached to a chain map of two-term complexes -/

/-- The degreewise component of the cochain realization of a chain map of two-term complexes:
the degree-zero part in cohomological degree `-1`, the degree-one part in cohomological degree
`0` and zero elsewhere. -/
noncomputable def cochainHomComponent (f : Hom E F) (i : ℤ) :
    E.toCochainComplex.X i ⟶ F.toCochainComplex.X i := by
  by_cases hneg : i = -1
  · subst hneg
    exact ModuleCat.ofHom f.degreeZero
  · by_cases hzero : i = 0
    · subst hzero
      exact ModuleCat.ofHom f.degreeOne
    · exact 0

@[simp]
theorem cochainHomComponent_negOne (f : Hom E F) :
    cochainHomComponent f (-1) = ModuleCat.ofHom f.degreeZero :=
  rfl

@[simp]
theorem cochainHomComponent_zero (f : Hom E F) :
    cochainHomComponent f 0 = ModuleCat.ofHom f.degreeOne :=
  rfl

/-- Outside the two displayed degrees the component is zero, because its target is a zero
object. -/
theorem cochainHomComponent_eq_zero (f : Hom E F) (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    cochainHomComponent f i = 0 :=
  (toCochainComplex_X_isZero F i hneg hzero).eq_of_tgt _ _

/-- A chain map of two-term complexes, realized as a morphism of cochain complexes of modules
supported in degrees `-1` and `0`. -/
noncomputable def toCochainComplexHom (f : Hom E F) :
    E.toCochainComplex ⟶ F.toCochainComplex :=
  CochainComplex.ofHom (cochainHomComponent f) (by
    intro i
    by_cases hneg : i = -1
    · subst hneg
      change cochainHomComponent f (-1) ≫ F.toCochainComplex.d (-1) 0 =
        E.toCochainComplex.d (-1) 0 ≫ cochainHomComponent f 0
      rw [cochainHomComponent_negOne, cochainHomComponent_zero,
        toCochainComplex_d_negOne_zero, toCochainComplex_d_negOne_zero]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (f.comm x).symm
    · by_cases hzero : i = 0
      · subst hzero
        refine (toCochainComplex_X_isZero F 1 (by norm_num) (by norm_num)).eq_of_tgt _ _
      · exact (toCochainComplex_X_isZero E i hneg hzero).eq_of_src _ _)

@[simp]
theorem toCochainComplexHom_f (f : Hom E F) (i : ℤ) :
    (toCochainComplexHom f).f i = cochainHomComponent f i :=
  rfl

/-- The two-term complex underlying the cochain realization of `E` is `E` itself. -/
theorem ofCochainComplex_toCochainComplex (E : LinearTwoTermComplex R) :
    ofCochainComplex E.toCochainComplex = E :=
  rfl

/-- The two-term chain map underlying the cochain realization of `f` is `f` itself. -/
theorem ofCochainComplexHom_toCochainComplexHom (f : Hom E F) :
    ofCochainComplexHom (toCochainComplexHom f) = f :=
  rfl

/-! ## Comparison of the elementwise and the homological quasi-isomorphism predicates -/

section QuasiIso

/-- A morphism of short complexes of modules whose first maps vanish is a quasi-isomorphism
exactly when the induced map on the kernels of the second maps is bijective.  The induced map is
given as data `u` together with the compatibility `hu`. -/
theorem quasiIso_iff_bijective_of_f_eq_zero {S₁ S₂ : ShortComplex (ModuleCat.{u} R)}
    (ψ : S₁ ⟶ S₂) (h₁ : S₁.f = 0) (h₂ : S₂.f = 0)
    (u : LinearMap.ker S₁.g.hom →ₗ[R] LinearMap.ker S₂.g.hom)
    (hu : ∀ x : LinearMap.ker S₁.g.hom, (u x : S₂.X₂) = ψ.τ₂ (x : S₁.X₂)) :
    ShortComplex.QuasiIso ψ ↔ Function.Bijective u := by
  have comm : (ModuleCat.kernelCone S₁.g).ι ≫ ψ.τ₂ =
      ModuleCat.ofHom u ≫ (ModuleCat.kernelCone S₂.g).ι := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (hu x).symm
  have key := (ShortComplex.LeftHomologyMapData.ofIsLimitKernelFork ψ h₁ _
    (ModuleCat.kernelIsLimit S₁.g) h₂ _ (ModuleCat.kernelIsLimit S₂.g)
    (ModuleCat.ofHom u) comm).quasiIso_iff
  rw [key, ConcreteCategory.isIso_iff_bijective]
  exact Iff.rfl

/-- A morphism of short complexes of modules whose second maps vanish is a quasi-isomorphism
exactly when the induced map on the cokernels of the first maps is bijective.  The induced map is
given as data `u` together with the compatibility `hu`. -/
theorem quasiIso_iff_bijective_of_g_eq_zero {S₁ S₂ : ShortComplex (ModuleCat.{u} R)}
    (ψ : S₁ ⟶ S₂) (h₁ : S₁.g = 0) (h₂ : S₂.g = 0)
    (u : (S₁.X₂ ⧸ LinearMap.range S₁.f.hom) →ₗ[R] (S₂.X₂ ⧸ LinearMap.range S₂.f.hom))
    (hu : ∀ x : S₁.X₂, u (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ψ.τ₂ x)) :
    ShortComplex.QuasiIso ψ ↔ Function.Bijective u := by
  have comm : ψ.τ₂ ≫ (ModuleCat.cokernelCocone S₂.f).π =
      (ModuleCat.cokernelCocone S₁.f).π ≫ ModuleCat.ofHom u := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (hu x).symm
  have key := (ShortComplex.LeftHomologyMapData.ofIsColimitCokernelCofork ψ h₁ _
    (ModuleCat.cokernelIsColimit S₁.f) h₂ _ (ModuleCat.cokernelIsColimit S₂.f)
    (ModuleCat.ofHom u) comm).quasiIso_iff
  rw [key, ConcreteCategory.isIso_iff_bijective]
  exact Iff.rfl

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- **Homology in degree `-1` is the kernel of the differential.**  For a complex of modules
whose term in degree `-2` vanishes, the homology in degree `-1` is the kernel of the differential
from degree `-1` to degree `0`, that is, `h⁰` of the underlying two-term complex. -/
noncomputable def homologyNegOneIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsZero (K.X (-2))) :
    K.homology (-1) ≅ ModuleCat.of R (LinearMap.ker (K.d (-1) 0).hom) :=
  ShortComplex.homologyMapIso (K.isoSc' (-2) (-1) 0
      (by rw [CochainComplex.prev]; norm_num) (by rw [CochainComplex.next]; norm_num)) ≪≫
    (ShortComplex.LeftHomologyData.ofIsLimitKernelFork (K.sc' (-2) (-1) 0)
      (hK.eq_of_src _ _) _ (ModuleCat.kernelIsLimit _)).homologyIso

/-- **Homology in degree `0` is the cokernel of the differential.**  For a complex of modules
whose term in degree `1` vanishes, the homology in degree `0` is the cokernel of the differential
from degree `-1` to degree `0`, that is, `h¹` of the underlying two-term complex. -/
noncomputable def homologyZeroIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsZero (K.X 1)) :
    K.homology 0 ≅ ModuleCat.of R (K.X 0 ⧸ LinearMap.range (K.d (-1) 0).hom) :=
  ShortComplex.homologyMapIso (K.isoSc' (-1) 0 1
      (by rw [CochainComplex.prev]; norm_num) (by rw [CochainComplex.next]; norm_num)) ≪≫
    (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork (K.sc' (-1) 0 1)
      (hK.eq_of_tgt _ _) _ (ModuleCat.cokernelIsColimit _)).homologyIso

/-- The homology of the cochain realization of a two-term complex in degree `-1` is `h⁰`. -/
noncomputable def homologyNegOneIsoKer (E : LinearTwoTermComplex R) :
    E.toCochainComplex.homology (-1) ≅ ModuleCat.of R (LinearMap.ker E.differential) :=
  homologyNegOneIso E.toCochainComplex
    (toCochainComplex_X_isZero E (-2) (by norm_num) (by norm_num))

/-- The homology of the cochain realization of a two-term complex in degree `0` is `h¹`. -/
noncomputable def homologyZeroIsoCoker (E : LinearTwoTermComplex R) :
    E.toCochainComplex.homology 0 ≅
      ModuleCat.of R (E.degreeOne ⧸ (LinearMap.range E.differential :
        Submodule R E.degreeOne)) :=
  homologyZeroIso E.toCochainComplex
    (toCochainComplex_X_isZero E 1 (by norm_num) (by norm_num))

/-- Outside the degrees `-1` and `0` the cochain realization of a two-term complex has vanishing
homology. -/
theorem isZero_homology_toCochainComplex (E : LinearTwoTermComplex R) (n : ℤ)
    (hneg : n ≠ -1) (hzero : n ≠ 0) : IsZero (E.toCochainComplex.homology n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (toCochainComplex_X_isZero E n hneg hzero)).isZero_homology

/-- In cohomological degree `-1`, a morphism of complexes vanishing in degree `-2` is a
quasi-isomorphism exactly when the elementwise map on the kernels of the differentials of the
underlying two-term complexes is bijective. -/
theorem quasiIsoAt_negOne_iff (φ : K ⟶ L) (hK : IsZero (K.X (-2))) (hL : IsZero (L.X (-2))) :
    QuasiIsoAt φ (-1) ↔ Function.Bijective (ofCochainComplexHom φ).kernelMap := by
  rw [quasiIsoAt_iff' φ (-2) (-1) 0 (by rw [CochainComplex.prev]; norm_num)
    (by rw [CochainComplex.next]; norm_num)]
  exact quasiIso_iff_bijective_of_f_eq_zero
    ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (-2) (-1) 0).map φ) (hK.eq_of_src _ _) (hL.eq_of_src _ _)
    (ofCochainComplexHom φ).kernelMap (fun _ => rfl)

/-- In cohomological degree `0`, a morphism of complexes vanishing in degree `1` is a
quasi-isomorphism exactly when the elementwise map on the cokernels of the differentials of the
underlying two-term complexes is bijective. -/
theorem quasiIsoAt_zero_iff (φ : K ⟶ L) (hK : IsZero (K.X 1)) (hL : IsZero (L.X 1)) :
    QuasiIsoAt φ 0 ↔ Function.Bijective (ofCochainComplexHom φ).cokernelMap := by
  rw [quasiIsoAt_iff' φ (-1) 0 1 (by rw [CochainComplex.prev]; norm_num)
    (by rw [CochainComplex.next]; norm_num)]
  exact quasiIso_iff_bijective_of_g_eq_zero
    ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (-1) 0 1).map φ) (hK.eq_of_tgt _ _) (hL.eq_of_tgt _ _)
    (ofCochainComplexHom φ).cokernelMap (fun _ => rfl)

/-- **The elementwise quasi-isomorphism predicate is Mathlib's.**  For complexes of modules
supported in cohomological degrees `-1` and `0`, a morphism induces bijections on the kernel and
the cokernel of the differential exactly when it is a quasi-isomorphism of cochain complexes. -/
theorem isQuasiIsomorphism_ofCochainComplexHom_iff (φ : K ⟶ L)
    (hK : ∀ i : ℤ, i < -1 ∨ 0 < i → IsZero (K.X i))
    (hL : ∀ i : ℤ, i < -1 ∨ 0 < i → IsZero (L.X i)) :
    (ofCochainComplexHom φ).IsQuasiIsomorphism ↔ QuasiIso φ := by
  rw [quasiIso_iff]
  constructor
  · rintro ⟨hker, hcoker⟩ i
    by_cases hneg : i = -1
    · subst hneg
      exact (quasiIsoAt_negOne_iff φ (hK _ (by norm_num)) (hL _ (by norm_num))).2 hker
    · by_cases hzero : i = 0
      · subst hzero
        exact (quasiIsoAt_zero_iff φ (hK 1 (by norm_num)) (hL 1 (by norm_num))).2 hcoker
      · rw [quasiIsoAt_iff_exactAt φ i
          (HomologicalComplex.ExactAt.of_isZero (hK i (by omega)))]
        exact HomologicalComplex.ExactAt.of_isZero (hL i (by omega))
  · intro h
    exact ⟨(quasiIsoAt_negOne_iff φ (hK _ (by norm_num)) (hL _ (by norm_num))).1 (h (-1)),
      (quasiIsoAt_zero_iff φ (hK 1 (by norm_num)) (hL 1 (by norm_num))).1 (h 0)⟩

/-- **The elementwise quasi-isomorphism predicate is Mathlib's**, in the form of the cochain
realization of a chain map of two-term complexes. -/
theorem isQuasiIsomorphism_iff_quasiIso (f : Hom E F) :
    f.IsQuasiIsomorphism ↔ QuasiIso (toCochainComplexHom f) :=
  isQuasiIsomorphism_ofCochainComplexHom_iff (toCochainComplexHom f)
    (fun i hi => toCochainComplex_X_isZero E i (by omega) (by omega))
    (fun i hi => toCochainComplex_X_isZero F i (by omega) (by omega))

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **A chain map of two-term complexes is a quasi-isomorphism exactly when its cochain
realization becomes an isomorphism in the derived category of `R`-modules.** -/
theorem isIso_Q_map_toCochainComplexHom_iff (f : Hom E F) :
    IsIso (DerivedCategory.Q.map (toCochainComplexHom f)) ↔ f.IsQuasiIsomorphism := by
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso, isQuasiIsomorphism_iff_quasiIso]

/-- The isomorphism of the derived category induced by a quasi-isomorphism of two-term
complexes. -/
noncomputable def derivedIso (f : Hom E F) (hf : f.IsQuasiIsomorphism) :
    DerivedCategory.Q.obj E.toCochainComplex ≅ DerivedCategory.Q.obj F.toCochainComplex :=
  have _hiso : IsIso (DerivedCategory.Q.map (toCochainComplexHom f)) :=
    (isIso_Q_map_toCochainComplexHom_iff f).2 hf
  asIso (DerivedCategory.Q.map (toCochainComplexHom f))

end Derived

end QuasiIso

/-! ## Cokernels of chain maps of two-term complexes -/

/-- The cokernel of a chain map of two-term complexes, formed degreewise. -/
def coker (φ : Hom E F) : LinearTwoTermComplex R where
  degreeZero := F.degreeZero ⧸ (LinearMap.range φ.degreeZero : Submodule R F.degreeZero)
  degreeOne := F.degreeOne ⧸ (LinearMap.range φ.degreeOne : Submodule R F.degreeOne)
  differential :=
    Submodule.mapQ _ _ F.differential (by
      rintro _ ⟨y, rfl⟩
      exact ⟨E.differential y, φ.comm y⟩)

/-- The projection of a two-term complex onto the cokernel of a chain map into it. -/
def toCoker (φ : Hom E F) : Hom F (coker φ) where
  degreeZero := (LinearMap.range φ.degreeZero : Submodule R F.degreeZero).mkQ
  degreeOne := (LinearMap.range φ.degreeOne : Submodule R F.degreeOne).mkQ
  comm _ := rfl

@[simp]
theorem toCoker_degreeZero_apply (φ : Hom E F) (x : F.degreeZero) :
    (toCoker φ).degreeZero x = Submodule.Quotient.mk x :=
  rfl

@[simp]
theorem toCoker_degreeOne_apply (φ : Hom E F) (x : F.degreeOne) :
    (toCoker φ).degreeOne x = Submodule.Quotient.mk x :=
  rfl

end LinearTwoTermComplex

namespace PicardCriteria

open LinearTwoTermComplex

variable {R : Type u} [CommRing R]

/-! ## Short exact sequences of two-term complexes in the derived category -/

section ShortExactSequences

variable {K' K K'' : LinearTwoTermComplex R} {ι : Hom K' K} {π : Hom K K''}

/-- A degreewise injective chain map of two-term complexes sits in a short exact sequence with
its cokernel. -/
theorem shortExact_toCoker {E F : LinearTwoTermComplex R} (φ : Hom E F)
    (hzero : Function.Injective φ.degreeZero) (hone : Function.Injective φ.degreeOne) :
    ShortExact φ (toCoker φ) where
  injective_degreeZero := hzero
  injective_degreeOne := hone
  surjective_degreeZero := Submodule.mkQ_surjective _
  surjective_degreeOne := Submodule.mkQ_surjective _
  exact_degreeZero := Submodule.ker_mkQ _
  exact_degreeOne := Submodule.ker_mkQ _

namespace ShortExact

/-- The cochain realizations of the two maps of a short exact sequence compose to zero. -/
theorem toCochainComplexHom_comp_eq_zero (h : ShortExact ι π) :
    toCochainComplexHom ι ≫ toCochainComplexHom π = 0 := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  by_cases hneg : n = -1
  · subst hneg
    change cochainHomComponent ι (-1) ≫ cochainHomComponent π (-1) = 0
    rw [cochainHomComponent_negOne, cochainHomComponent_negOne]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact h.comp_degreeZero x
  · by_cases hzero : n = 0
    · subst hzero
      change cochainHomComponent ι 0 ≫ cochainHomComponent π 0 = 0
      rw [cochainHomComponent_zero, cochainHomComponent_zero]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact h.comp_degreeOne x
    · exact (toCochainComplex_X_isZero K' n hneg hzero).eq_of_src _ _

/-- The short complex of cochain complexes of modules attached to a degreewise short exact
sequence of two-term complexes. -/
noncomputable def cochainShortComplex (h : ShortExact ι π) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk _ _ h.toCochainComplexHom_comp_eq_zero

@[simp]
theorem cochainShortComplex_f (h : ShortExact ι π) :
    h.cochainShortComplex.f = toCochainComplexHom ι :=
  rfl

@[simp]
theorem cochainShortComplex_g (h : ShortExact ι π) :
    h.cochainShortComplex.g = toCochainComplexHom π :=
  rfl

/-- **A short exact sequence of two-term complexes is a short exact sequence of complexes.**
Degreewise this is the given exactness in degrees `-1` and `0`, and the trivial statement about
zero objects in every other degree. -/
theorem cochainShortExact (h : ShortExact ι π) : h.cochainShortComplex.ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
  by_cases hneg : n = -1
  · subst hneg
    exact { exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
              h.exact_degreeZero.symm
            mono_f := (ModuleCat.mono_iff_injective _).2 h.injective_degreeZero
            epi_g := (ModuleCat.epi_iff_surjective _).2 h.surjective_degreeZero }
  · by_cases hzero : n = 0
    · subst hzero
      exact { exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
                h.exact_degreeOne.symm
              mono_f := (ModuleCat.mono_iff_injective _).2 h.injective_degreeOne
              epi_g := (ModuleCat.epi_iff_surjective _).2 h.surjective_degreeOne }
    · have hK' := toCochainComplex_X_isZero K' n hneg hzero
      have hK'' := toCochainComplex_X_isZero K'' n hneg hzero
      have hK := toCochainComplex_X_isZero K n hneg hzero
      exact { exact := ShortComplex.exact_of_isZero_X₂ _ hK
              mono_f := ⟨fun g₁ g₂ _ => hK'.eq_of_tgt g₁ g₂⟩
              epi_g := ⟨fun g₁ g₂ _ => hK''.eq_of_src g₁ g₂⟩ }

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The mapping cone realizes the quotient complex.**  For a short exact sequence of two-term
complexes, the canonical map from the mapping cone of the cochain realization of `ι` to the
cochain realization of `K''` is a quasi-isomorphism. -/
theorem quasiIso_descShortComplex (h : ShortExact ι π) :
    QuasiIso (CochainComplex.mappingCone.descShortComplex h.cochainShortComplex) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex h.cochainShortExact

/-- **The derived-category form of a short exact sequence of two-term complexes.**  The images
of the two chain maps in the derived category of `R`-modules fit into a distinguished triangle
`K' → K → K'' → K'[1]`. -/
theorem triangleOfSES_distinguished (h : ShortExact ι π) :
    DerivedCategory.triangleOfSES h.cochainShortExact ∈
      distTriang (DerivedCategory (ModuleCat.{u} R)) :=
  DerivedCategory.triangleOfSES_distinguished _

/-- **A short exact sequence with acyclic quotient is an isomorphism in the derived category.**
This is the two-term form of "a distinguished triangle with zero third term is an
isomorphism". -/
theorem isIso_Q_map_of_acyclic (h : ShortExact ι π)
    (hzero : ∀ c : h0 K'', c = 0) (hone : ∀ q : h1 K'', q = 0) :
    IsIso (DerivedCategory.Q.map (toCochainComplexHom ι)) :=
  (LinearTwoTermComplex.isIso_Q_map_toCochainComplexHom_iff ι).2
    (h.isQuasiIsomorphism_of_acyclic hzero hone)

end Derived

end ShortExact

/-! ## The Picard-groupoid package of a short exact sequence -/

/-- The Picard-groupoid content of a degreewise short exact sequence of two-term complexes.
Every field is a conclusion, proved in `ShortExact.shortExactPicard`; nothing is assumed. -/
structure ShortExactPicard (ι : Hom K' K) (π : Hom K K'') : Prop where
  /-- The quotient functor of the surjection is essentially surjective. -/
  essSurj : π.quotientFunctor.EssSurj
  /-- Fibres on hom-sets are torsors under `h⁰(K')`. -/
  hom_fibre_torsor : ∀ {x y : K.quotient} (a b : x ⟶ y),
    π.quotientFunctor.map a = π.quotientFunctor.map b →
      ∃! e : h0 K', ι.degreeZero (e : K'.degreeZero) = a.val - b.val
  /-- Fibres on isomorphism classes are the orbits of the translation action of `K'`. -/
  nonempty_iso_map_iff : ∀ x y : K.quotient,
    Nonempty (π.quotientFunctor.obj x ≅ π.quotientFunctor.obj y) ↔
      ∃ t : K'.degreeOne, Nonempty (x ≅ (ShortExact.translate ι t).obj y)

/-- **A short exact sequence of two-term complexes exhibits `[K''¹/K''⁰]` as the quotient of
`[K¹/K⁰]` by `[K'¹/K'⁰]`.**  All three statements are theorems of `Cones/Criteria.lean`. -/
theorem ShortExact.shortExactPicard (h : ShortExact ι π) : ShortExactPicard ι π where
  essSurj := h.essSurj_quotientFunctor
  hom_fibre_torsor a b hab := h.hom_fibre_torsor a b hab
  nonempty_iso_map_iff := h.nonempty_iso_map_iff

end ShortExactSequences

end PicardCriteria

namespace CotangentComplex.PerfectComplex

open CotangentComplex.PerfectComplex LinearTwoTermComplex

attribute [local instance] HasDerivedCategory.standard

namespace GlobalTwoTermResolution

variable {R : Type u} [CommRing R] {E : DerivedCategory (ModuleCat.{u} R)}

/-! ## Canonicity of the comparison of two global two-term resolutions -/

/-- **Chain-level realizations of a derived morphism are unique up to homotopy.**  Two chain maps
between the resolving complexes of global two-term resolutions which have the same image in the
derived category are homotopic, because the source is K-projective. -/
theorem nonempty_homotopy_of_Q_map_eq (F F' : GlobalTwoTermResolution E)
    (φ ψ : F.complex ⟶ F'.complex)
    (h : DerivedCategory.Q.map φ = DerivedCategory.Q.map ψ) :
    Nonempty (Homotopy φ ψ) := by
  have hK := F.isKProjective
  have hq : (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map φ =
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map ψ := by
    apply (CochainComplex.IsKProjective.Qh_map_bijective F.complex
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj
        F'.complex)).injective
    have h1 := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality φ
    have h2 := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality ψ
    rw [Functor.comp_map] at h1 h2
    rw [h, ← h2] at h1
    exact (cancel_mono _).mp h1
  exact ⟨HomotopyCategory.homotopyOfEq _ _ hq⟩

namespace Comparison

variable {F F' : GlobalTwoTermResolution E}

/-- **Two chain-level comparisons of the same pair of resolutions are homotopic.**  Both realize
the same isomorphism of the derived category, so this is the previous theorem. -/
theorem nonempty_homotopy (c c' : Comparison F F') : Nonempty (Homotopy c.map c'.map) :=
  nonempty_homotopy_of_Q_map_eq F F' c.map c'.map (c.realizes.trans c'.realizes.symm)

/-- **The comparison equivalence of Picard groupoids is canonical.**  The functors induced by
any two chain-level comparisons of the same pair of global two-term resolutions are naturally
isomorphic; the natural isomorphism comes from a homotopy between the two comparison chain
maps, restricted to the displayed degrees. -/
theorem picardEquivalence_unique_up_to_natIso (c c' : Comparison F F') :
    Nonempty (c.picardEquivalence.functor ≅ c'.picardEquivalence.functor) := by
  obtain ⟨H⟩ := c.nonempty_homotopy c'
  have hK1 : IsZero (F.complex.X 1) := F.supported 1 (Or.inr (by norm_num))
  have hL2 : IsZero (F'.complex.X (-2)) := F'.supported (-2) (Or.inl (by norm_num))
  exact ⟨(LinearTwoTermComplex.ofHomotopy hK1 hL2 H).natIso.symm⟩

/-- **The inverse comparison equivalence is canonical too.**  Naturally isomorphic equivalences
have naturally isomorphic inverses, by uniqueness of right adjoints. -/
theorem picardEquivalence_inverse_unique_up_to_natIso (c c' : Comparison F F') :
    Nonempty (c.picardEquivalence.inverse ≅ c'.picardEquivalence.inverse) := by
  obtain ⟨α⟩ := c.picardEquivalence_unique_up_to_natIso c'
  exact ⟨Adjunction.rightAdjointUniq
    (Adjunction.ofNatIsoLeft c.picardEquivalence.toAdjunction α)
    c'.picardEquivalence.toAdjunction⟩

end Comparison

end GlobalTwoTermResolution

end CotangentComplex.PerfectComplex

end GromovWitten.AlgebraicGeometry
