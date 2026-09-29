/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.LocalizedScalarExtension
import GromovWitten.AlgebraicGeometry.Curves.AffinePullbackGamma

/-!
# Localization of affine pullback global sections

The localization criterion for the affine pullback/global-sections unit only needs the comparison
map itself to be an isomorphism.  This separates that algebraic criterion from geometric
quasi-coherence hypotheses that may be used to establish the comparison.
-/

open CategoryTheory Limits TensorProduct
open scoped ChangeOfRings
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u
noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- The affine pullback/global-sections unit is localized whenever its comparison map is an
isomorphism. -/
theorem affinePullbackGammaUnit_isLocalizedModule_of_isIso
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : Submonoid R) [IsLocalization p S]
    (M : (Spec (CommRingCat.of R)).Modules)
    [IsIso (affinePullbackGammaMap (CommRingCat.ofHom (algebraMap R S)) M)] :
    IsLocalizedModule p
      ((affinePullbackGammaUnit (CommRingCat.ofHom (algebraMap R S)) M).hom) := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of S :=
    CommRingCat.ofHom (algebraMap R S)
  let N : ModuleCat.{u} R := (moduleSpecΓFunctor (R := CommRingCat.of R)).obj M
  let P : ModuleCat.{u} S :=
    (moduleSpecΓFunctor (R := CommRingCat.of S)).obj
      ((Scheme.Modules.pullback (Spec.map φ)).obj M)
  let e : (ModuleCat.extendScalars (algebraMap R S)).obj N ⟶ P :=
    affinePullbackGammaMap φ M
  have hloc := ModuleCat.isLocalizedModule_adjunct_of_isIso p N P e
  change IsLocalizedModule p
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
      (affinePullbackGammaMap φ M)).hom) at hloc
  rw [affinePullbackGammaMap_homEquiv] at hloc
  change IsLocalizedModule p (affinePullbackGammaUnit φ M).hom at hloc
  exact hloc

end
end GromovWitten.AlgebraicGeometry.Curves
