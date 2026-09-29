/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.MateRotation
import GromovWitten.AlgebraicGeometry.Curves.ModuleOpenBaseChange
import GromovWitten.AlgebraicGeometry.Curves.OpenPullbackSectionsNaturality

/-!
# Restriction-pullback mates

The restriction-pullback comparison is identified with the canonical
pushforward square and its adjunction-unit formula.
-/

open CategoryTheory AlgebraicGeometry Scheme.Modules
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X Y : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false in
/-- The restriction-pullback comparison is the canonical functor isomorphism. -/
def restrictPullbackIso (p : Y ⟶ X) (U : X.Opens) :
    restrictFunctor U.ι ⋙ pullback (p ∣_ U) ≅
      pullback p ⋙ restrictFunctor (p ⁻¹ᵁ U).ι :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι) (pullback (p ∣_ U)) ≪≫
    pullbackComp (p ∣_ U) U.ι ≪≫ pullbackCongr (morphismRestrict_ι p U) ≪≫
    (pullbackComp (p ⁻¹ᵁ U).ι p).symm ≪≫
    Functor.isoWhiskerLeft (pullback p) (restrictFunctorIsoPullback (p ⁻¹ᵁ U).ι).symm
set_option backward.isDefEq.respectTransparency false in
/-- The mate of the restriction-pullback comparison is the pushforward square. -/
lemma restrictPullback_conjugate (p : Y ⟶ X) (U : X.Opens) :
    conjugateEquiv
      ((pullbackPushforwardAdjunction p).comp (restrictAdjunction (p ⁻¹ᵁ U).ι))
      ((restrictAdjunction U.ι).comp (pullbackPushforwardAdjunction (p ∣_ U)))
      (restrictPullbackIso p U).hom =
      (modulePushforwardSquare p U.ι (p ⁻¹ᵁ U).ι (p ∣_ U)
        (morphismRestrict_ι p U).symm).hom := by
  dsimp only [restrictPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction U.ι).comp
      (pullbackPushforwardAdjunction (p ∣_ U)))]
  rw [conjugateEquiv_whiskerRight, conjugateEquiv_restrictFunctorIsoPullback_hom]
  simp only [Functor.whiskerLeft_id', Category.comp_id]
  rw [← Category.assoc, ← Category.assoc]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction p).comp
      (pullbackPushforwardAdjunction (p ⁻¹ᵁ U).ι))]
  rw [conjugateEquiv_whiskerLeft]
  have hi : conjugateEquiv (restrictAdjunction (p ⁻¹ᵁ U).ι)
      (pullbackPushforwardAdjunction (p ⁻¹ᵁ U).ι)
      (restrictFunctorIsoPullback (p ⁻¹ᵁ U).ι).inv = 𝟙 _ := by
    have he := conjugateEquiv_comm (restrictAdjunction (p ⁻¹ᵁ U).ι)
      (pullbackPushforwardAdjunction (p ⁻¹ᵁ U).ι)
      (restrictFunctorIsoPullback (p ⁻¹ᵁ U).ι).hom_inv_id
    rw [conjugateEquiv_restrictFunctorIsoPullback_hom] at he
    simpa using he
  rw [hi]
  simp only [Functor.whiskerRight_id', Category.id_comp]
  simpa only [Category.assoc] using
    modulePullbackSquare_conjugate p U.ι (p ⁻¹ᵁ U).ι (p ∣_ U)
      (morphismRestrict_ι p U).symm
end GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves

open CategoryTheory AlgebraicGeometry Scheme.Modules

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The restriction-pullback mate is given by the restriction of the pullback unit. -/
lemma restrictPullback_homEquiv (p : Y ⟶ X) (U : X.Opens) (M : X.Modules) :
    (pullbackPushforwardAdjunction (p ∣_ U)).homEquiv _ _
        ((restrictPullbackIso p U).hom.app M) =
      (restrictFunctor U.ι).map ((pullbackPushforwardAdjunction p).unit.app M) ≫
        (modulePushforwardOpenRestrictIso p U).hom.app
          ((pullback p).obj M) := by
  apply mate_rotation (restrictAdjunction U.ι)
    (pullbackPushforwardAdjunction p)
    (pullbackPushforwardAdjunction (p ∣_ U))
    (restrictAdjunction (p ⁻¹ᵁ U).ι)
    (restrictPullbackIso p U).hom
    (modulePushforwardOpenRestrictIso p U).hom
  intro N
  rw [restrictPullback_conjugate p U]
  exact moduleOpenRestrictIso_unit p U N

end GromovWitten.AlgebraicGeometry.Curves
