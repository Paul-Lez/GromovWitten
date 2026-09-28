/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.OpenSectionsBaseChange
import GromovWitten.AlgebraicGeometry.Curves.OpenPullbackSectionsNaturality

/-!
# The unit formula for open-section comparison

The affine-open section comparison sends the pullback-pushforward adjunction unit to the original
section.  The proof keeps the explicit restriction maps in the categorical composite.
-/

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The open-section comparison carries the pullback-pushforward unit to the original section. -/
lemma openSectionsOverBaseIso_unit (s : X ⟶ Spec R) (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) :
    (openSectionsOverBaseIso s M U).hom
      (((pullback U.ι).obj M).presheaf.map (eqToHom U.ι_preimage_self.symm).op
        (((pullbackPushforwardAdjunction U.ι).unit.app M).app U m)) = m := by
  let P := (pullback U.ι).obj M
  let e := (restrictFunctorIsoPullback U.ι).inv.app M
  have hn := e.mapPresheaf.naturality (eqToHom U.ι_preimage_self.symm).op
  change P.presheaf.map (eqToHom U.ι_preimage_self.symm).op ≫ e.app ⊤ =
    e.app (U.ι ⁻¹ᵁ U) ≫ (M.restrict U.ι).presheaf.map
      (eqToHom U.ι_preimage_self.symm).op at hn
  have hu := congrArg (fun k => k.app U)
    (pullbackPushforwardAdjunction_unit_restrict U.ι M)
  simp only [Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app] at hu
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    (e.app ⊤ (P.presheaf.map (eqToHom U.ι_preimage_self.symm).op
      (((pullbackPushforwardAdjunction U.ι).unit.app M).app U m))) = m
  have hne (z : Γ(P, U.ι ⁻¹ᵁ U)) :
      e.app ⊤ (P.presheaf.map (eqToHom U.ι_preimage_self.symm).op z) =
        (M.restrict U.ι).presheaf.map (eqToHom U.ι_preimage_self.symm).op
          (e.app (U.ι ⁻¹ᵁ U) z) := ConcreteCategory.congr_hom hn z
  have hue : e.app (U.ι ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction U.ι).unit.app M).app U m) =
        M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op m :=
    ConcreteCategory.congr_hom hu m
  rw [hne, hue]
  rw [Scheme.Modules.restrict_map]
  have hmaps : M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op ≫
      M.presheaf.map (U.ι.opensFunctor.map (eqToHom U.ι_preimage_self.symm)).op ≫
      M.presheaf.map (eqToHom U.ι_image_top.symm).op = 𝟙 Γ(M, U) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact M.presheaf.map_id (op U)
  exact ConcreteCategory.congr_hom hmaps m

/-- The inverse of the open-section comparison is given by the transported
pullback-pushforward adjunction unit. -/
lemma openSectionsOverBaseIso_inv (s : X ⟶ Spec R) (M : X.Modules) (U : X.Opens)
    (m : baseSectionModule s U M) :
    (openSectionsOverBaseIso s M U).inv m =
      ((pullback U.ι).obj M).presheaf.map (eqToHom U.ι_preimage_self.symm).op
        (((pullbackPushforwardAdjunction U.ι).unit.app M).app U
          (show Γ(M, U) from m)) := by
  apply (ConcreteCategory.bijective_of_isIso
    (openSectionsOverBaseIso s M U).hom).1
  calc
    (openSectionsOverBaseIso s M U).hom ((openSectionsOverBaseIso s M U).inv m) = m :=
      ConcreteCategory.congr_hom (openSectionsOverBaseIso s M U).inv_hom_id m
    _ = (openSectionsOverBaseIso s M U).hom
        (((pullback U.ι).obj M).presheaf.map (eqToHom U.ι_preimage_self.symm).op
          (((pullbackPushforwardAdjunction U.ι).unit.app M).app U
            (show Γ(M, U) from m))) :=
      (openSectionsOverBaseIso_unit s M U (show Γ(M, U) from m)).symm

end GromovWitten.AlgebraicGeometry.Curves
