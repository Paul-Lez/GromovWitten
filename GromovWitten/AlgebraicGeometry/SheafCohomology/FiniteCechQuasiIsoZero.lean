/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechComplex
import GromovWitten.CategoryTheory.MappingCoconeQuasiIsoAt
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Degree-zero comparisons for finite Čech complexes

A map of presheaf complexes supported in nonnegative degrees induces a
degree-zero quasi-isomorphism on every finite Čech complex if it does so on
every open. The statement concerns only degree zero, so no higher acyclicity
hypothesis is needed.
-/

open CategoryTheory Limits HomologicalComplex CochainComplex TopologicalSpace Opposite

noncomputable section

namespace GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

variable {X : TopCat} {R : Type*} [Ring R]

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise quasi-isomorphisms in degree zero induce the same property for every
finite Čech complex when both input complexes are supported in nonnegative degrees. -/
lemma finiteCechMap_quasiIsoAt_zero_of_pointwise
    {F G : PresheafComplex X R} (f : F ⟶ G)
    (hF : ∀ i : ℤ, i < 0 → IsZero (F.X i))
    (hG : ∀ i : ℤ, i < 0 → IsZero (G.X i))
    (hf : ∀ W, QuasiIsoAt
      ((evaluatePresheafComplexMap f).app (Opposite.op W)) 0)
    (V : Opens X) (U : List (Opens X)) :
    QuasiIsoAt
      ((evaluatePresheafComplexMap (finiteCechMap f U)).app (Opposite.op V)) 0 := by
  induction U generalizing V with
  | nil =>
      let H : Presheaves X R ⥤ ModuleCat R :=
        (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (Opposite.op V)
      let E := H.mapHomologicalComplex (.up ℤ)
      change QuasiIsoAt (E.map
        (0 : (HomologicalComplex.zero : PresheafComplex X R) ⟶
          (HomologicalComplex.zero : PresheafComplex X R))) 0
      have hzero : IsZero (E.obj (HomologicalComplex.zero : PresheafComplex X R)) :=
        Functor.map_isZero E (HomologicalComplex.isZero_zero)
      have hmap : IsIso (E.map
          (0 : (HomologicalComplex.zero : PresheafComplex X R) ⟶
            (HomologicalComplex.zero : PresheafComplex X R))) := by
        rw [Functor.map_zero]
        exact (isIsoZero_iff_source_target_isZero _ _).2 ⟨hzero, hzero⟩
      let : IsIso (E.map
          (0 : (HomologicalComplex.zero : PresheafComplex X R) ⟶
            (HomologicalComplex.zero : PresheafComplex X R))) := hmap
      exact quasiIsoAt_of_isIso _ 0
  | cons head tail ih =>
      let H : Presheaves X R ⥤ ModuleCat R :=
        (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (Opposite.op V)
      let E := H.mapHomologicalComplex (.up ℤ)
      let Ftail := finiteCechData F tail
      let Gtail := finiteCechData G tail
      let tailMap := finiteCechMapData f tail
      let restrict := restrictionComplexFunctor (X := X) (R := R) head
      let resTailF := (restrictionComplexNatTrans (X := X) (R := R) head).app Ftail.complex
      let resTailG := (restrictionComplexNatTrans (X := X) (R := R) head).app Gtail.complex
      let aMap : (restrict.obj F) ⊞ Ftail.complex ⟶ (restrict.obj G) ⊞ Gtail.complex :=
        biprod.map (restrict.map f) tailMap.hom
      let bMap : restrict.obj Ftail.complex ⟶ restrict.obj Gtail.complex :=
        restrict.map tailMap.hom
      let φF : (restrict.obj F) ⊞ Ftail.complex ⟶ restrict.obj Ftail.complex :=
        biprod.desc (restrict.map Ftail.augmentation) (-resTailF)
      let φG : (restrict.obj G) ⊞ Gtail.complex ⟶ restrict.obj Gtail.complex :=
        biprod.desc (restrict.map Gtail.augmentation) (-resTailG)
      have hFtail : ∀ i : ℤ, i < 0 → IsZero (Ftail.complex.X i) :=
        finiteCechData_boundedBelow F 0 hF tail
      have hGtail : ∀ i : ℤ, i < 0 → IsZero (Gtail.complex.X i) :=
        finiteCechData_boundedBelow G 0 hG tail
      have hRestr : QuasiIsoAt (E.map (restrict.map f)) 0 := by
        change QuasiIsoAt ((evaluatePresheafComplexMap f).app
          (Opposite.op (V ⊓ head))) 0
        exact hf (V ⊓ head)
      have hTailAtV : QuasiIsoAt (E.map tailMap.hom) 0 := by
        change QuasiIsoAt ((evaluatePresheafComplexMap (finiteCechMap f tail)).app
          (Opposite.op V)) 0
        exact ih V
      have hInter : QuasiIsoAt
          ((evaluatePresheafComplexMap (finiteCechMap f tail)).app
            (Opposite.op (V ⊓ head))) 0 := ih (V ⊓ head)
      have hTailAtInter : QuasiIsoAt (E.map bMap) 0 := by
        change QuasiIsoAt ((evaluatePresheafComplexMap (finiteCechMap f tail)).app
          (Opposite.op (V ⊓ head))) 0
        exact hInter
      have hL₁ : (E.obj (restrict.obj Ftail.complex)).ExactAt (-1 : ℤ) := by
        apply HomologicalComplex.ExactAt.of_isZero
        change IsZero (H.obj ((restrictionFunctor (X := X) (R := R) head).obj
          (Ftail.complex.X (-1))))
        exact Functor.map_isZero H
          (Functor.map_isZero (restrictionFunctor (X := X) (R := R) head)
            (hFtail (-1) (by omega)))
      have hL₂ : (E.obj (restrict.obj Gtail.complex)).ExactAt (-1 : ℤ) := by
        apply HomologicalComplex.ExactAt.of_isZero
        change IsZero (H.obj ((restrictionFunctor (X := X) (R := R) head).obj
          (Gtail.complex.X (-1))))
        exact Functor.map_isZero H
          (Functor.map_isZero (restrictionFunctor (X := X) (R := R) head)
            (hGtail (-1) (by omega)))
      have hA : QuasiIsoAt (E.map aMap) 0 := by
        exact @CochainComplex.biprod_map_quasiIsoAt_after_additive
          (Presheaves X R) (ModuleCat R) inferInstance inferInstance inferInstance
          inferInstance inferInstance H inferInstance
          (restrict.obj F) Ftail.complex (restrict.obj G) Gtail.complex
          (restrict.map f) tailMap.hom 0 hRestr hTailAtV
      have hresTail : tailMap.hom ≫ resTailG = resTailF ≫ restrict.map tailMap.hom := by
        simpa only [Functor.id_map] using
          (restrictionComplexNatTrans (X := X) (R := R) head).naturality tailMap.hom
      have hsq : φF ≫ bMap = aMap ≫ φG := by
        apply biprod.hom_ext'
        · calc
            biprod.inl ≫ φF ≫ bMap =
                restrict.map Ftail.augmentation ≫ restrict.map tailMap.hom := by
              simp [φF, bMap]
            _ = restrict.map (Ftail.augmentation ≫ tailMap.hom) :=
              (Functor.map_comp restrict _ _).symm
            _ = restrict.map (f ≫ Gtail.augmentation) := by
              rw [tailMap.augmentation_natural]
            _ = restrict.map f ≫ restrict.map Gtail.augmentation := Functor.map_comp _ _ _
            _ = biprod.inl ≫ aMap ≫ φG := by simp [aMap, φG]
        · calc
            biprod.inr ≫ φF ≫ bMap = -resTailF ≫ restrict.map tailMap.hom := by
              simp [φF, bMap]
            _ = -(resTailF ≫ restrict.map tailMap.hom) := by simp
            _ = -(tailMap.hom ≫ resTailG) := by rw [← hresTail]
            _ = tailMap.hom ≫ (-resTailG) := by simp
            _ = biprod.inr ≫ aMap ≫ φG := by simp [aMap, φG]
      have hC : QuasiIsoAt (E.map (mappingCoconeMap φF φG aMap bMap hsq)) 0 := by
        let : QuasiIsoAt (E.map aMap) 0 := hA
        let : QuasiIsoAt (E.map bMap) 0 := hTailAtInter
        exact @CochainComplex.mappingCoconeMap_quasiIsoAt_after_additive_of_exact_below
          (Presheaves X R) (ModuleCat R) inferInstance inferInstance inferInstance
          inferInstance inferInstance H inferInstance
          (restrict.obj F ⊞ Ftail.complex) (restrict.obj Ftail.complex)
          (restrict.obj G ⊞ Gtail.complex) (restrict.obj Gtail.complex)
          φF φG aMap bMap hsq 0 hA hTailAtInter hL₁ hL₂
      change QuasiIsoAt (E.map (mappingCoconeMap φF φG aMap bMap hsq)) 0
      exact hC

end GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

end
