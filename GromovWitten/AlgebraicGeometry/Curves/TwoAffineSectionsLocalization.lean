/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.LocalizedScalarExtension
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineFlatBaseChange

/-!
# Localization of sections base change on a two-affine cover

For a ring localization and a Cartesian base change, the degree-zero sections base-change unit is
localized when the source module is quasi-coherent and the source has a two-affine cover with
affine overlap.  No Noetherian hypotheses are used.
-/

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open scoped ChangeOfRings

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- The degree-zero sections base-change map viewed as the adjunction unit over the base ring. -/
def sectionsBaseChangeUnit (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ)) (M : X.Modules) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward s).obj M) ⟶
      (ModuleCat.restrictScalars φ.hom).obj
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward g).obj
          ((Scheme.Modules.pullback p).obj M))) :=
  (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
    (sectionsBaseChangeMap s φ p g h M)

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the sections base-change unit is the pullback-pushforward adjunction unit. -/
lemma sectionsBaseChangeUnit_apply (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ)) (M : X.Modules)
    (m : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward s).obj M)) :
    sectionsBaseChangeUnit s φ p g h M m =
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤ m := by
  change sectionsBaseChangeMap s φ p g h M ((1 : T) ⊗ₜ[R, φ.hom] m) = _
  exact sectionsBaseChangeMap_one_tmul s φ p g h M m

set_option backward.isDefEq.respectTransparency false in
/-- The sections base-change unit is localized for a two-affine cover over a ring localization. -/
lemma sectionsBaseChangeUnit_isLocalizedModule_of_twoAffine
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (S : Submonoid R) [IsLocalization S T]
    (s : X ⟶ Spec (CommRingCat.of R))
    (p : Y ⟶ X) (g : Y ⟶ Spec (CommRingCat.of T))
    (h : IsPullback p g s (Spec.map (CommRingCat.ofHom (algebraMap R T))))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤) :
    IsLocalizedModule S
      (sectionsBaseChangeUnit s (CommRingCat.ofHom (algebraMap R T)) p g h M).hom := by
  let φ := CommRingCat.ofHom (algebraMap R T)
  have hφ : φ.hom.Flat := RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat T S)
  have := sectionsBaseChangeMap_isIso_of_twoAffine_flat_base s φ hφ p g h M U V
    hU hV hI hcover
  exact ModuleCat.isLocalizedModule_adjunct_of_isIso S _ _
    (sectionsBaseChangeMap s φ p g h M)

end GromovWitten.AlgebraicGeometry.Curves
