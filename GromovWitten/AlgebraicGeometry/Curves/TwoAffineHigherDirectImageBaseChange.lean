/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeCechGlobalSectionsDerived
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineCohomologyBaseChange
import GromovWitten.AlgebraicGeometry.Curves.AffineBaseChange

/-!
# Two-affine higher-direct-image base change

For an affine base and an affine two-open cover with affine intersection, this file transports
the relative Čech degree-one comparison to an isomorphism of the actual module-valued first
higher direct images.  The construction assumes local Noetherianity on both schemes and makes no
flatness assumption on the base ring map.  It is a Čech-constructed isomorphism; no comparison
with a separately defined canonical derived base-change morphism is asserted here.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false in
/-- The actual module-valued first higher direct images are isomorphic after an affine-base
two-affine Čech base change.  The isomorphism is constructed through the affine tilde and
global-sections comparisons, so the ring map need not be flat. -/
def twoAffineHigherDirectImageOneBaseChangeIso
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤) :
    (Scheme.Modules.pullback (Spec.map φ)).obj (higherDirectImageModule s M 1) ≅
      higherDirectImageModule g ((Scheme.Modules.pullback p).obj M) 1 := by
  let _ : IsAffineHom p :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  have hUp : IsAffineOpen (p ⁻¹ᵁ U) := IsAffineHom.isAffine_preimage _ hU
  have hVp : IsAffineOpen (p ⁻¹ᵁ V) := IsAffineHom.isAffine_preimage _ hV
  have hIp : IsAffineOpen ((p ⁻¹ᵁ U) ⊓ (p ⁻¹ᵁ V)) :=
    IsAffineHom.isAffine_preimage (f := p) _ hI
  have hc : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤ := by
    change p ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  let _ : IsAffine U.toScheme := hU
  let _ : IsAffine V.toScheme := hV
  let _ : IsAffine (U ⊓ V).toScheme := hI
  let _ : IsAffine (p ⁻¹ᵁ U).toScheme := hUp
  let _ : IsAffine (p ⁻¹ᵁ V).toScheme := hVp
  let _ : IsAffine ((p ⁻¹ᵁ U) ⊓ (p ⁻¹ᵁ V)).toScheme := hIp
  let N := (Scheme.Modules.pullback p).obj M
  let A := higherDirectImageModule s M 1
  let B := higherDirectImageModule g N 1
  let _ : A.IsQuasicoherent :=
    isQuasicoherent_higherDirectImageModule_one_of_twoAffine s M U V hcover
  let _ : B.IsQuasicoherent :=
    isQuasicoherent_higherDirectImageModule_one_of_twoAffine g N (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hc
  let eSource : (tilde.functor R).obj (moduleSpecΓFunctor.obj A) ≅ A := asIso A.fromTildeΓ
  let eTarget : (tilde.functor T).obj (moduleSpecΓFunctor.obj B) ≅ B := asIso B.fromTildeΓ
  let eA := higherDirectImageOneSectionsIsoCohomology s M U V hU hV hI hcover
  let eB := higherDirectImageOneSectionsIsoCohomology g N (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)
    hUp hVp hIp hc
  exact (Scheme.Modules.pullback (Spec.map φ)).mapIso eSource.symm ≪≫
    (affinePullbackTildeIso φ).app ((moduleSpecΓFunctor (R := R)).obj A) ≪≫
    (tilde.functor T).mapIso ((ModuleCat.extendScalars φ.hom).mapIso eA) ≪≫
    (tilde.functor T).mapIso
      (twoAffineCohomologyOneBaseChangeIso s φ p g h M U V hU hV hI hcover) ≪≫
    (tilde.functor T).mapIso eB.symm ≪≫ eTarget
end GromovWitten.AlgebraicGeometry.Curves
