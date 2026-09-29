/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineSectionsExact
import GromovWitten.AlgebraicGeometry.SheafCohomology.QuasiCoherentLocality
import GromovWitten.AlgebraicGeometry.SheafCohomology.TildeExact
import GromovWitten.AlgebraicGeometry.Curves.ModulePullbackExact
import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeIsomorphism
import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPushforward

/-!
# Extension closure of quasicoherent modules

A short exact sequence of modules on a locally Noetherian scheme has a
quasicoherent middle term when its two outer terms are quasicoherent.  The
proof reduces to the affine-spectrum statement by exact pullback and then
uses affine-locality.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {R : CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- On an affine spectrum, quasicoherence of the two outer terms of a short
exact sequence forces quasicoherence of its middle term. -/
theorem isQuasicoherent_middle_of_shortExact_of_spec
    [IsNoetherianRing R]
    (S : ShortComplex (Spec (CommRingCat.of (R : Type u))).Modules)
    (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.X₂.IsQuasicoherent := by
  let _ : PreservesFiniteLimits (moduleSpecΓFunctor (R := R)) :=
    ⟨fun J _ _ =>
      (tilde.adjunction (R := R)).rightAdjoint_preservesLimits.preservesLimitsOfShape⟩
  let hΓ := moduleSpecΓFunctor_map_shortExact_of_isQuasicoherent S hS
  let Φ : (S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R) ⟶ S :=
    { τ₁ := S.X₁.fromTildeΓ
      τ₂ := S.X₂.fromTildeΓ
      τ₃ := S.X₃.fromTildeΓ
      comm₁₂ := by
        change S.X₁.fromTildeΓ ≫ S.f =
          (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map S.f) ≫
            S.X₂.fromTildeΓ
        exact ((tilde.adjunction (R := R)).counit.naturality S.f).symm
      comm₂₃ := by
        change S.X₂.fromTildeΓ ≫ S.g =
          (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map S.g) ≫
            S.X₃.fromTildeΓ
        exact ((tilde.adjunction (R := R)).counit.naturality S.g).symm }
  let htildeS : ((S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R)).ShortExact :=
    hΓ.map_of_exact (tilde.functor R)
  let _ : IsIso Φ.τ₁ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₁
  let _ : IsIso Φ.τ₃ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₃
  let _ : IsIso Φ.τ₂ :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ Φ htildeS hS
  apply (AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ S.X₂).mpr
  change IsIso Φ.τ₂
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- On an affine locally Noetherian scheme, quasicoherence of the two outer
terms of a short exact sequence forces quasicoherence of its middle term. -/
theorem isQuasicoherent_middle_of_shortExact_of_isAffine
    {X : Scheme.{u}} [IsAffine X] [IsLocallyNoetherian X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.X₂.IsQuasicoherent := by
  let p := X.isoSpec.inv
  let F := Scheme.Modules.pullback p
  let _ : F.PreservesHomology := moduleFlatPullback_preservesHomology p
  let _ : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  let _ : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  have hSF : (S.map F).ShortExact := hS.map_of_exact F
  let _ : IsNoetherianRing (affineGlobalRing X) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have hX1 : (F.obj S.X₁).IsQuasicoherent := by
    dsimp [F]
    infer_instance
  have hX3 : (F.obj S.X₃).IsQuasicoherent := by
    dsimp [F]
    infer_instance
  let _ : (S.map F).X₁.IsQuasicoherent := hX1
  let _ : (S.map F).X₃.IsQuasicoherent := hX3
  have hmid : (F.obj S.X₂).IsQuasicoherent :=
    isQuasicoherent_middle_of_shortExact_of_spec (S.map F) hSF
  have hpush : ((Scheme.Modules.pushforward p).obj (F.obj S.X₂)).IsQuasicoherent :=
    inferInstance
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app S.X₂)).symm hpush

set_option backward.isDefEq.respectTransparency false in
/-- On a locally Noetherian scheme, quasicoherence of the two outer terms of a
short exact sequence forces quasicoherence of its middle term. -/
theorem isQuasicoherent_middle_of_shortExact
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.X₂.IsQuasicoherent := by
  exact isQuasicoherent_of_affine_pullback S.X₂ fun U => by
    let _ : IsAffine U.1.toScheme := U.2
    let F := Scheme.Modules.pullback U.1.ι
    let _ : F.PreservesHomology := moduleFlatPullback_preservesHomology U.1.ι
    let _ : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
    let _ : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
    have hSF : (S.map F).ShortExact := hS.map_of_exact F
    have hX1 : (F.obj S.X₁).IsQuasicoherent := by
      dsimp [F]
      infer_instance
    have hX3 : (F.obj S.X₃).IsQuasicoherent := by
      dsimp [F]
      infer_instance
    let _ : (S.map F).X₁.IsQuasicoherent := hX1
    let _ : (S.map F).X₃.IsQuasicoherent := hX3
    exact isQuasicoherent_middle_of_shortExact_of_isAffine (S.map F) hSF

end GromovWitten.AlgebraicGeometry.SheafCohomology
