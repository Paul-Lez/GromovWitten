/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeMate
import GromovWitten.AlgebraicGeometry.Curves.OpenPullbackSections

/-!
# Naturality of sections on affine open pullbacks

This file records the coherence identities needed to compare sections after
composing open immersions and affine base change.
-/

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
noncomputable section

namespace GromovWitten.AlgebraicGeometry.Curves

section RestrictionCoherence

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsOpenImmersion f] [IsOpenImmersion g]

private lemma restrict_map_app {M N : Y.Modules} (a : M ⟶ N) (U : X.Opens) :
    ((restrictFunctor f).map a).app U = a.app (f ''ᵁ U) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The restriction composition comparison is conjugate to pushforward composition. -/
lemma conjugateEquiv_restrictFunctorComp_hom :
    conjugateEquiv ((restrictAdjunction g).comp (restrictAdjunction f))
      (restrictAdjunction (f ≫ g)) (restrictFunctorComp f g).hom =
      (pushforwardComp f g).hom := by
  ext M U
  simp only [conjugateEquiv_apply_app, Adjunction.comp_counit_app,
    Hom.comp_app, pushforward_map_app,
    restrictAdjunction_unit_app_app, restrictFunctorComp_hom_app_app,
    restrictAdjunction_counit_app_app, pushforwardComp_hom_app_app,
    restrict_map_app, Functor.comp_obj, pushforward_obj_presheaf_map]
  simp only [← Functor.map_comp]
  congr 2
  change M.presheaf.map _ = 𝟙 (Γ(M, f ⁻¹ᵁ (g ⁻¹ᵁ U)))
  rw [← M.presheaf.map_id (Opposite.op (f ⁻¹ᵁ (g ⁻¹ᵁ U)))]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The restriction/pullback comparison is conjugate to the identity. -/
lemma conjugateEquiv_restrictFunctorIsoPullback_hom (h : X ⟶ Y) [IsOpenImmersion h] :
    conjugateEquiv (pullbackPushforwardAdjunction h) (restrictAdjunction h)
      (restrictFunctorIsoPullback h).hom = 𝟙 _ := by
  ext M
  simp only [conjugateEquiv_apply_app, restrictFunctorIsoPullback,
    NatTrans.id_app]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The pullback restriction comparison is coherent under composition. -/
lemma restrictFunctorIsoPullback_comp :
    (restrictFunctorIsoPullback (f ≫ g)).hom =
      (restrictFunctorComp f g).hom ≫
      Functor.whiskerRight (restrictFunctorIsoPullback g).hom (restrictFunctor f) ≫
      Functor.whiskerLeft (pullback g) (restrictFunctorIsoPullback f).hom ≫
      (pullbackComp f g).hom := by
  apply (conjugateEquiv (pullbackPushforwardAdjunction (f ≫ g))
    (restrictAdjunction (f ≫ g))).injective
  rw [conjugateEquiv_restrictFunctorIsoPullback_hom]
  rw [← conjugateEquiv_comp _ ((restrictAdjunction g).comp (restrictAdjunction f))]
  rw [← conjugateEquiv_comp _ ((pullbackPushforwardAdjunction g).comp (restrictAdjunction f))]
  rw [← conjugateEquiv_comp _ ((pullbackPushforwardAdjunction g).comp
    (pullbackPushforwardAdjunction f))]
  rw [conjugateEquiv_pullbackComp_hom, conjugateEquiv_whiskerLeft,
    conjugateEquiv_whiskerRight, conjugateEquiv_restrictFunctorIsoPullback_hom,
    conjugateEquiv_restrictFunctorIsoPullback_hom,
    conjugateEquiv_restrictFunctorComp_hom]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The pullback unit agrees with the restriction unit after pullback comparison. -/
lemma pullbackPushforwardAdjunction_unit_restrict (h : X ⟶ Y) [IsOpenImmersion h]
    (M : Y.Modules) :
    (pullbackPushforwardAdjunction h).unit.app M ≫
      (pushforward h).map ((restrictFunctorIsoPullback h).inv.app M) =
    (restrictAdjunction h).unit.app M := by
  change _ ≫ (pushforward h).map (((restrictAdjunction h).leftAdjointUniq
    (pullbackPushforwardAdjunction h)).inv.app M) = _
  rw [Adjunction.leftAdjointUniq_inv_app]
  exact Adjunction.unit_leftAdjointUniq_hom_app _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The inverse pullback comparison after composition of open immersions. -/
lemma pullbackComp_restrictFunctorIsoPullback_inv :
    (pullbackComp f g).hom ≫ (restrictFunctorIsoPullback (f ≫ g)).inv =
      Functor.whiskerLeft (pullback g) (restrictFunctorIsoPullback f).inv ≫
      Functor.whiskerRight (restrictFunctorIsoPullback g).inv (restrictFunctor f) ≫
      (restrictFunctorComp f g).inv := by
  apply (cancel_mono (restrictFunctorIsoPullback (f ≫ g)).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, restrictFunctorIsoPullback_comp]
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc]
  dsimp only [Functor.comp_obj]
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The pullback unit is compatible with composition of open immersions. -/
lemma pullbackPushforwardAdjunction_unit_comp_restrict (M : Z.Modules) :
    (pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M) ≫
      (pushforward f).map ((pullbackComp f g).hom.app M) ≫
      (pushforward f).map ((restrictFunctorIsoPullback (f ≫ g)).inv.app M) =
    (restrictFunctorIsoPullback g).inv.app M ≫
      (restrictAdjunction f).unit.app ((restrictFunctor g).obj M) ≫
      (pushforward f).map ((restrictFunctorComp f g).inv.app M) := by
  rw [← Functor.map_comp]
  have he := congr_app (pullbackComp_restrictFunctorIsoPullback_inv f g) M
  rw [NatTrans.comp_app] at he
  rw [he]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, ← Category.assoc]
  rw [pullbackPushforwardAdjunction_unit_restrict]
  have hn := (restrictAdjunction f).unit.naturality
    ((restrictFunctorIsoPullback g).inv.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [hn]

end RestrictionCoherence

section Affine
variable {A B : CommRingCat.{u}} {W : Scheme.{u}}
  (φ : A ⟶ B) (j : Spec A ⟶ W)
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion j]

/-- The image of a composite affine open immersion lies in the image of its second map. -/
lemma range_comp_le : (Spec.map φ ≫ j).opensRange ≤ j.opensRange := by
  rw [Scheme.Hom.opensRange_comp, ← j.image_top_eq_opensRange]
  exact j.image_mono le_top

set_option backward.isDefEq.respectTransparency false in
/-- The affine pullback section map agrees with restriction along the image inclusion. -/
lemma openPullbackSectionsIso_comp_unit (M : W.Modules)
    (x : (moduleSpecΓFunctor (R := A)).obj ((pullback j).obj M)) :
    (openPullbackSectionsIso (Spec.map φ ≫ j) M).hom
      (((moduleSpecΓFunctor (R := B)).map ((pullbackComp (Spec.map φ) j).hom.app M))
        (affinePullbackGammaUnit φ ((pullback j).obj M) x)) =
    M.presheaf.map (homOfLE (range_comp_le φ j)).op
      ((openPullbackSectionsIso j M).hom x) := by
  have he := congrArg (fun k => k.app (⊤ : (Spec A).Opens))
    (pullbackPushforwardAdjunction_unit_comp_restrict (Spec.map φ) j M)
  simp only [Hom.comp_app, pushforward_map_app,
    restrictAdjunction_unit_app_app, restrictFunctorComp_inv_app_app] at he
  have hx := ConcreteCategory.congr_hom he x
  dsimp only [openPullbackSectionsIso]
  change M.presheaf.map _
      (((restrictFunctorIsoPullback (Spec.map φ ≫ j)).inv.app M).app ⊤
        (((pullbackComp (Spec.map φ) j).hom.app M).app ⊤
          (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
            ((pullback j).obj M)).app ⊤ x))) = _
  simp only [ConcreteCategory.comp_apply] at hx
  change ((restrictFunctorIsoPullback (Spec.map φ ≫ j)).inv.app M).app ⊤
      (((pullbackComp (Spec.map φ) j).hom.app M).app ⊤
        (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
          ((pullback j).obj M)).app ⊤ x)) = _ at hx
  erw [hx]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _
      (((restrictFunctorIsoPullback j).inv.app M).app ⊤ x))) =
    M.presheaf.map _ (M.presheaf.map _
      (((restrictFunctorIsoPullback j).inv.app M).app ⊤ x))
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the section identification under equality of affine open maps. -/
lemma openPullbackSectionsIso_congr {j k : Spec A ⟶ W}
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) (M : W.Modules)
    (x : (moduleSpecΓFunctor (R := A)).obj ((pullback j).obj M)) :
    (openPullbackSectionsIso k M).hom
      (((moduleSpecΓFunctor (R := A)).map ((pullbackCongr h).hom.app M)) x) =
      M.presheaf.map (eqToHom (show k.opensRange = j.opensRange from by subst k; rfl)).op
        ((openPullbackSectionsIso j M).hom x) := by
  subst k
  simp [pullbackCongr]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of affine pullback sections after identifying a composite with its target map. -/
lemma openPullbackSectionsIso_unit_comp_congr (k : Spec B ⟶ W)
    [IsOpenImmersion k] (h : Spec.map φ ≫ j = k) (M : W.Modules)
    (x : (moduleSpecΓFunctor (R := A)).obj ((pullback j).obj M)) :
    (openPullbackSectionsIso k M).hom
      (((moduleSpecΓFunctor (R := B)).map
        (((pullbackComp (Spec.map φ) j).hom.app M) ≫ ((pullbackCongr h).hom.app M)))
        (affinePullbackGammaUnit φ ((pullback j).obj M) x)) =
    M.presheaf.map (homOfLE (show k.opensRange ≤ j.opensRange from
      h ▸ range_comp_le φ j)).op ((openPullbackSectionsIso j M).hom x) := by
  rw [CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply,
    openPullbackSectionsIso_congr, openPullbackSectionsIso_comp_unit]
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

end Affine

end GromovWitten.AlgebraicGeometry.Curves
