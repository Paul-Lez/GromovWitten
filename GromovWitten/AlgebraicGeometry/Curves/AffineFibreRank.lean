/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.TwoTermSemicontinuity
import GromovWitten.AlgebraicGeometry.Curves.AffineFinitePresentation
import GromovWitten.AlgebraicGeometry.Curves.AffinePullbackGamma
import GromovWitten.Algebra.ReducedFibreFlatness

/-!
# Upper semicontinuity of affine fibre ranks

For a finitely presented module on an affine Noetherian scheme, the dimension of
the module of sections after pullback to residue fields is upper semicontinuous.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct

universe u
noncomputable section

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
private theorem privateFibreFinrankEq (M : (Spec (CommRingCat.of R)).Modules)
    [M.IsQuasicoherent] (p : PrimeSpectrum R) :
    Module.finrank p.asIdeal.ResidueField
        ((moduleSpecΓFunctor (R := CommRingCat.of p.asIdeal.ResidueField)).obj
          ((Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)))).obj M)) =
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R]
          ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M)) := by
  let N := (moduleSpecΓFunctor (R := CommRingCat.of R)).obj M
  let φ : CommRingCat.of R ⟶ CommRingCat.of p.asIdeal.ResidueField :=
    CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)
  have : IsIso (affinePullbackGammaMap φ M) :=
    affinePullbackGammaMap_isIso φ M
  let e := (asIso (affinePullbackGammaMap φ M)).symm ≪≫
    ModuleCat.extendScalarsAlgebraIso (C := p.asIdeal.ResidueField) N
  exact e.toLinearEquiv.finrank_eq

set_option backward.isDefEq.respectTransparency false in
/-- Residue-field dimensions of affine fibres of a finitely presented module are upper
semicontinuous on the base spectrum. -/
theorem upperSemicontinuous_affine_fibreFinrank_of_finitePresentation
    [IsNoetherianRing R] (M : (Spec (CommRingCat.of R)).Modules)
    [M.IsFinitePresentation] :
    UpperSemicontinuous (fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField
        ((moduleSpecΓFunctor (R := CommRingCat.of p.asIdeal.ResidueField)).obj
          ((Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)))).obj M))) := by
  let _ : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  let N := (moduleSpecΓFunctor (R := CommRingCat.of R)).obj M
  have : Module.FinitePresentation R N := moduleSpecΓ_isFinitePresentation M
  have h := upperSemicontinuous_fibreFinrank_of_finitePresentation N
  convert h using 1
  funext p
  exact privateFibreFinrankEq M p

set_option backward.isDefEq.respectTransparency false in
/-- A locally constant actual affine fibre rank makes the global section module projective. -/
theorem moduleSpecΓ_projective_of_locallyConstant_fibreRank
    [IsNoetherianRing R] [IsReduced R] (M : (Spec (CommRingCat.of R)).Modules)
    [M.IsFinitePresentation]
    (hd : IsLocallyConstant (fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField
        ((moduleSpecΓFunctor (R := CommRingCat.of p.asIdeal.ResidueField)).obj
          ((Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)))).obj M)))) :
    Module.Projective R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M) := by
  let _ : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  let N := (moduleSpecΓFunctor (R := CommRingCat.of R)).obj M
  have : Module.FinitePresentation R N := moduleSpecΓ_isFinitePresentation M
  have hd' : IsLocallyConstant (fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R] N)) := by
    convert hd using 1
    funext p
    exact (privateFibreFinrankEq M p).symm
  exact GromovWitten.Algebra.reduced_fibre_projective hd'

end GromovWitten.AlgebraicGeometry.Curves
