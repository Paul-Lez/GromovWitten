/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.SquareZeroDerivedExt
import GromovWitten.AlgebraicGeometry.Cones.DerivedCriteria

/-! # The derived obstruction cokernel without conormal projectivity

Naturality of the short-exact-sequence triangle for the map `[C → F] → [F → F]`
identifies the kernel of the derived projection map with the image of `Hom(F,M)`.
Thus the explicit obstruction cokernel embeds in derived degree-one Hom without
projectivity assumptions. Combined with `SquareZeroDerivedExt`, it is an equivalence
when only `F` is projective. Polynomial presentations have a constructed free basis
for `F`, yielding the derived obstruction criterion without additional hypotheses.

These results concern the two-term presentation complex. They do not identify it with
the full cotangent complex or assert a deformation theorem for arbitrary stacks.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex.SquareZero

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex
open GromovWitten.AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false

attribute [local instance] HasDerivedCategory.standard

namespace TwoTerm

variable {A : Type u} [CommRing A]

abbrev identityComplex (F : Type u) [AddCommGroup F] [Module A F] :
    LinearTwoTermComplex A where
  degreeZero := F
  degreeOne := F
  differential := LinearMap.id

noncomputable def identityMap {E : LinearTwoTermComplex A} :
    E.Hom (identityComplex (A := A) E.degreeOne) where
  degreeZero := E.differential
  degreeOne := LinearMap.id
  comm x := by simp

noncomputable def sesMap {E : LinearTwoTermComplex A} :
    TwoTerm.shortComplex E ⟶ TwoTerm.shortComplex (identityComplex (A := A) E.degreeOne) := by
  let J := identityComplex (A := A) E.degreeOne
  let φ : E.Hom J := identityMap (A := A)
  refine ShortComplex.homMk
    (𝟙 _)
    (LinearTwoTermComplex.toCochainComplexHom φ)
    ((CochainComplex.singleFunctor (ModuleCat A) (-1)).map
      (ModuleCat.ofHom E.differential)) ?_ ?_
  · apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = 0
    · subst i
      change (HomologicalComplex.Hom.f
        (𝟙 ((CochainComplex.singleFunctor (ModuleCat A) 0).obj
          (ModuleCat.of A E.degreeOne))) 0) ≫
          (TwoTerm.inclusion (identityComplex (A := A) E.degreeOne)).f 0 =
        (TwoTerm.inclusion E).f 0 ≫
          (LinearTwoTermComplex.toCochainComplexHom φ).f 0
      rw [TwoTerm.inclusion_f_zero, TwoTerm.inclusion_f_zero,
        LinearTwoTermComplex.toCochainComplexHom_f,
        LinearTwoTermComplex.cochainHomComponent_zero]
      rw [show φ.degreeOne = LinearMap.id by rfl]
      apply ModuleCat.hom_ext
      rfl
    · exact (isZero_single_obj_X _ _ _ i (by omega)).eq_of_src _ _
  · apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = -1
    · subst i
      change (LinearTwoTermComplex.toCochainComplexHom φ).f (-1) ≫
          (TwoTerm.projection (identityComplex (A := A) E.degreeOne)).f (-1) =
        (TwoTerm.projection E).f (-1) ≫
          ((CochainComplex.singleFunctor (ModuleCat A) (-1)).map
            (ModuleCat.ofHom E.differential)).f (-1)
      rw [TwoTerm.projection_f_negOne, TwoTerm.projection_f_negOne,
        LinearTwoTermComplex.toCochainComplexHom_f,
        LinearTwoTermComplex.cochainHomComponent_negOne]
      apply ModuleCat.hom_ext
      rfl
    · exact (isZero_single_obj_X _ _ _ i (by omega)).eq_of_tgt _ _

theorem delta_factorization (E : LinearTwoTermComplex A) :
    (DerivedCategory.triangleOfSES (TwoTerm.shortExact E)).mor₃ =
      DerivedCategory.Q.map
          ((CochainComplex.singleFunctor (ModuleCat A) (-1)).map
            (ModuleCat.ofHom E.differential)) ≫
        (DerivedCategory.triangleOfSES
          (TwoTerm.shortExact (identityComplex (A := A) E.degreeOne))).mor₃ := by
  have h := DerivedCategory.triangleOfSESδ_naturality
    (TwoTerm.shortExact E)
    (TwoTerm.shortExact (identityComplex (A := A) E.degreeOne)) (sesMap (E := E))
  change (DerivedCategory.triangleOfSES (shortExact E)).mor₃ ≫
    (DerivedCategory.Q.map (𝟙 _))⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map
        ((CochainComplex.singleFunctor (ModuleCat A) (-1)).map
          (ModuleCat.ofHom E.differential)) ≫
        (DerivedCategory.triangleOfSES
          (shortExact (identityComplex (A := A) E.degreeOne))).mor₃ at h
  have hi : (DerivedCategory.Q.map (𝟙 (shortComplex E).X₁))⟦(1 : ℤ)⟧' =
      𝟙 ((DerivedCategory.Q.obj (shortComplex E).X₁)⟦(1 : ℤ)⟧) :=
    (congrArg (fun k => (shiftFunctor (DerivedCategory (ModuleCat A)) (1 : ℤ)).map k)
      (DerivedCategory.Q.map_id (shortComplex E).X₁)).trans
      ((shiftFunctor (DerivedCategory (ModuleCat A)) (1 : ℤ)).map_id _)
  have he : (DerivedCategory.triangleOfSES (shortExact E)).mor₃ ≫
      (DerivedCategory.Q.map (𝟙 (shortComplex E).X₁))⟦(1 : ℤ)⟧' =
      (DerivedCategory.triangleOfSES (shortExact E)).mor₃ :=
    (congrArg (fun k => (DerivedCategory.triangleOfSES (shortExact E)).mor₃ ≫ k) hi).trans
      (Category.comp_id _)
  exact he.symm.trans h

/-- A derived-zero map out of the quotient single complex factors through the differential.
Neither term is assumed projective. -/
theorem factor_of_projection_comp_eq_zero (E : LinearTwoTermComplex A) (N : ModuleCat A)
    (k : ModuleCat.of A E.degreeZero ⟶ N)
    (hk : DerivedCategory.Q.map (projection E) ≫
      (DerivedCategory.singleFunctor (ModuleCat A) (-1)).map k = 0) :
    ∃ l : ModuleCat.of A E.degreeOne ⟶ N, k = ModuleCat.ofHom E.differential ≫ l := by
  obtain ⟨t, ht⟩ := Triangle.yoneda_exact₃ (derivedTriangle E)
    (derivedTriangle_distinguished E)
    ((DerivedCategory.singleFunctor (ModuleCat A) (-1)).map k) hk
  obtain ⟨l, hl⟩ := (DerivedCategory.singleFunctor (ModuleCat A) (-1)).map_surjective
    ((derivedTriangle (identityComplex (A := A) E.degreeOne)).mor₃ ≫ t)
  refine ⟨l, ?_⟩
  apply (DerivedCategory.singleFunctor (ModuleCat A) (-1)).map_injective
  rw [Functor.map_comp, hl]
  change _ = DerivedCategory.Q.map
    ((CochainComplex.singleFunctor (ModuleCat A) (-1)).map
      (ModuleCat.ofHom E.differential)) ≫ _ ≫ t
  rw [← Category.assoc]
  exact ht.trans (congrArg (fun a => a ≫ t) (delta_factorization E))

end TwoTerm

section Presentation

universe v
variable (R : Type v) {A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (M : Ideal B) [Algebra A (B ⧸ M)]
  [IsScalarTower R A (B ⧸ M)] [IsSquareZero M] (P : Algebra.Extension.{u} R A)

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
/-- The chain representative of a conormal map is its composition with the canonical projection. -/
theorem chainHomEquiv_symm_eq_projection (θ : P.Cotangent →ₗ[A] Coeff M) :
    (chainHomEquiv R M P).symm θ =
      TwoTerm.projection (AffinePresentation.twoTerm R A P) ≫
        (CochainComplex.singleFunctor (ModuleCat A) (-1)).map (ModuleCat.ofHom θ) := by
  apply hom_ext_to_coeffComplex M
  apply ModuleCat.hom_ext
  rfl

/-- The explicit obstruction map is the canonical derived map induced by the conormal term. -/
theorem obstructionToDerivedHom_mk (θ : P.Cotangent →ₗ[A] Coeff M) :
    obstructionToDerivedHom R M P (Submodule.Quotient.mk θ) =
      DerivedCategory.Q.map (TwoTerm.projection (AffinePresentation.twoTerm R A P)) ≫
        (DerivedCategory.singleFunctor (ModuleCat A) (-1)).map (ModuleCat.ofHom θ) := by
  change DerivedCategory.Q.map ((chainHomEquiv R M P).symm θ) = _
  rw [chainHomEquiv_symm_eq_projection, Functor.map_comp]
  rfl

/-- The explicit obstruction cokernel always embeds in derived degree-one Hom. -/
theorem obstructionToDerivedHom_injective :
    Function.Injective (obstructionToDerivedHom R M P) := by
  intro x y h
  obtain ⟨θ, rfl⟩ := Submodule.Quotient.mk_surjective (coboundary R M P) x
  obtain ⟨η, rfl⟩ := Submodule.Quotient.mk_surjective (coboundary R M P) y
  rw [obstructionToDerivedHom_mk, obstructionToDerivedHom_mk] at h
  have hz : DerivedCategory.Q.map (TwoTerm.projection (AffinePresentation.twoTerm R A P)) ≫
      (DerivedCategory.singleFunctor (ModuleCat A) (-1)).map
        (ModuleCat.ofHom (θ - η)) = 0 := by
    change DerivedCategory.Q.map (TwoTerm.projection (AffinePresentation.twoTerm R A P)) ≫
      (DerivedCategory.singleFunctor (ModuleCat A) (-1)).map
        (ModuleCat.ofHom θ - ModuleCat.ofHom η) = 0
    rw [Functor.map_sub, Preadditive.comp_sub, h, sub_self]
  obtain ⟨l, hl⟩ := TwoTerm.factor_of_projection_comp_eq_zero
    (AffinePresentation.twoTerm R A P) (ModuleCat.of A (Coeff M))
    (ModuleCat.ofHom (θ - η)) hz
  apply (Submodule.Quotient.eq _).2
  rw [mem_coboundary_iff_comp_cotangentComplex]
  exact ⟨l.hom, congrArg ModuleCat.Hom.hom hl.symm⟩

/-- Derived degree-one Hom is the obstruction cokernel when only the cotangent-space term
is projective. The conormal term is arbitrary. -/
noncomputable def derivedExtOneEquivOfProjectiveCotangentSpace
    [Projective (ModuleCat.of A P.CotangentSpace)] :
    ObstructionGroup R M P ≃
      (DerivedCategory.Q.obj (AffinePresentation.cochainComplex R A P) ⟶
        DerivedCategory.Q.obj (coeffComplex M A)) :=
  Equiv.ofBijective _ ⟨obstructionToDerivedHom_injective R M P,
    obstructionToDerivedHom_surjective R M P⟩

/-- The obstruction cokernel as the actual derived `Ext¹` of the presentation complex,
assuming projectivity only of its cotangent-space term. -/
noncomputable def obstructionGroupEquivDerivedExtOfProjectiveCotangentSpace
    [Projective (ModuleCat.of A P.CotangentSpace)] :
    ObstructionGroup R M P ≃
      DerivedExt (AffinePresentation.derivedObject R A P)
        ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
          (ModuleCat.of A (Coeff M))) 1 :=
  (derivedExtOneEquivOfProjectiveCotangentSpace R M P).trans
    (Iso.homCongr (Iso.refl _) (coeffComplexIso M (A := A)))

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

/-- The canonical derived obstruction vanishes exactly when an algebra lift exists. -/
theorem derivedObstruction_eq_zero_iff [Nonempty (Lift R M P.Ring)] :
    obstructionToDerivedHom R M P (obstruction R M P) = 0 ↔ Nonempty (Lift R M A) := by
  rw [← obstruction_eq_zero_iff R M P]
  constructor
  · intro h
    apply obstructionToDerivedHom_injective R M P
    simpa only [obstructionToDerivedHom_zero] using h
  · intro h
    rw [h, obstructionToDerivedHom_zero]

end Presentation

section PolynomialPresentation

variable (R : Type u) {A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (M : Ideal B) [Algebra A (B ⧸ M)]
  [IsScalarTower R A (B ⧸ M)] [IsSquareZero M]

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

/-- A polynomial presentation computes derived degree-one Hom with no extra projectivity
hypothesis, because its cotangent-space term has a constructed free basis. -/
noncomputable def generatorsDerivedExtOneEquiv {ι : Type u}
    (G : Algebra.Generators R A ι) :
    ObstructionGroup R M G.toExtension ≃
      (DerivedCategory.Q.obj (AffinePresentation.cochainComplex R A G.toExtension) ⟶
        DerivedCategory.Q.obj (coeffComplex M A)) := by
  letI : Projective (ModuleCat.of A G.toExtension.CotangentSpace) :=
    ModuleCat.projective_of_free G.cotangentSpaceBasis
  exact derivedExtOneEquivOfProjectiveCotangentSpace R M G.toExtension

/-- For polynomial presentations the derived obstruction criterion has no ambient-lift
hypothesis; formal smoothness of the ambient polynomial ring supplies it. -/
theorem generatorsDerivedObstruction_eq_zero_iff {ι : Type u}
    (G : Algebra.Generators R A ι) :
    obstructionToDerivedHom R M G.toExtension (obstruction R M G.toExtension) = 0 ↔
      Nonempty (Lift R M A) :=
  derivedObstruction_eq_zero_iff R M G.toExtension

end PolynomialPresentation
end GromovWitten.AlgebraicGeometry.CotangentComplex.SquareZero

