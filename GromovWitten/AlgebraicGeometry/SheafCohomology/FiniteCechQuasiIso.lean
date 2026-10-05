/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechComplex
import GromovWitten.CategoryTheory.MappingCoconeQuasiIso
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Local quasi-isomorphisms induce finite Čech quasi-isomorphisms

A morphism which is a quasi-isomorphism on the intersections appearing in a finite
cover induces a quasi-isomorphism of its finite Čech complexes.
-/

open CategoryTheory Limits HomologicalComplex CochainComplex TopologicalSpace Opposite

universe u v

namespace GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

variable {X : TopCat.{u}} {R : Type v} [Ring R]

set_option backward.isDefEq.respectTransparency false in
/-- Local quasi-isomorphisms on a family of opens closed under intersection induce
quasi-isomorphisms of the corresponding finite Čech complexes. -/
lemma finiteCechMap_quasiIso_at
    {F G : PresheafComplex X R} (f : F ⟶ G)
    (P : Opens X → Prop)
    (hPinf : ∀ A B, P A → P B → P (A ⊓ B))
    (hf : ∀ W, P W → QuasiIso ((evaluatePresheafComplexMap f).app (Opposite.op W)))
    (V : Opens X) (U : List (Opens X))
    (hU : ∀ W ∈ U, P (V ⊓ W)) :
    QuasiIso ((evaluatePresheafComplexMap (finiteCechMap f U)).app (Opposite.op V)) := by
  induction U generalizing V with
  | nil =>
      let H : Presheaves X R ⥤ ModuleCat R :=
        (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (Opposite.op V)
      let E := H.mapHomologicalComplex (.up ℤ)
      change QuasiIso (E.map
        (0 : (HomologicalComplex.zero : PresheafComplex X R) ⟶
          (HomologicalComplex.zero : PresheafComplex X R)))
      have hzero : IsZero (E.obj (HomologicalComplex.zero : PresheafComplex X R)) :=
        Functor.map_isZero E (HomologicalComplex.isZero_zero)
      have hmap : IsIso (E.map
          (0 : (HomologicalComplex.zero : PresheafComplex X R) ⟶
            (HomologicalComplex.zero : PresheafComplex X R))) := by
        rw [Functor.map_zero]
        exact (isIsoZero_iff_source_target_isZero _ _).2 ⟨hzero, hzero⟩
      exact @quasiIso_of_isIso ℤ (ModuleCat R) inferInstance inferInstance
        (ComplexShape.up ℤ) _ _ (E.map
          (0 : (HomologicalComplex.zero : PresheafComplex X R) ⟶
            (HomologicalComplex.zero : PresheafComplex X R)))
        hmap inferInstance inferInstance
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
      have htail : ∀ W ∈ tail, P ((V ⊓ head) ⊓ W) := by
        intro W hW
        have hhead : P (V ⊓ head) := hU head (by simp)
        have hW' : P (V ⊓ W) := hU W (by simp [hW])
        simpa [inf_assoc, inf_left_comm, inf_comm] using hPinf (V ⊓ head) (V ⊓ W) hhead hW'
      have hInter : QuasiIso ((evaluatePresheafComplexMap (finiteCechMap f tail)).app
          (Opposite.op (V ⊓ head))) := ih (V ⊓ head) htail
      have hTailV : QuasiIso ((evaluatePresheafComplexMap (finiteCechMap f tail)).app
          (Opposite.op V)) := by
        apply ih V
        intro W hW
        exact hU W (by simp [hW])
      have hFhead : P (V ⊓ head) := hU head (by simp)
      have hRestr : QuasiIso (E.map (restrict.map f)) := by
        change QuasiIso ((evaluatePresheafComplexMap f).app (Opposite.op (V ⊓ head)))
        exact hf (V ⊓ head) hFhead
      have hTailAtV : QuasiIso (E.map tailMap.hom) := by
        change QuasiIso ((evaluatePresheafComplexMap (finiteCechMap f tail)).app (Opposite.op V))
        exact hTailV
      have hTailAtInter : QuasiIso (E.map bMap) := by
        change QuasiIso ((evaluatePresheafComplexMap (finiteCechMap f tail)).app
          (Opposite.op (V ⊓ head)))
        exact hInter
      have hA : QuasiIso (E.map aMap) :=
        @biprod_map_quasiIso_after_additive
          (Presheaves X R) (ModuleCat R) inferInstance inferInstance inferInstance
          inferInstance inferInstance
          H inferInstance (restrict.obj F) Ftail.complex (restrict.obj G) Gtail.complex
          (restrict.map f) tailMap.hom hRestr hTailAtV
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
      have hC : QuasiIso (E.map (mappingCoconeMap φF φG aMap bMap hsq)) :=
        @mappingCocone_map_quasiIso_after_additive
          (Presheaves X R) (ModuleCat R) inferInstance inferInstance inferInstance
          inferInstance inferInstance
          H inferInstance (restrict.obj F ⊞ Ftail.complex) (restrict.obj Ftail.complex)
          (restrict.obj G ⊞ Gtail.complex) (restrict.obj Gtail.complex)
          φF φG aMap bMap hsq hA hTailAtInter
      change QuasiIso (E.map (mappingCoconeMap φF φG aMap bMap hsq))
      exact hC


end GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
