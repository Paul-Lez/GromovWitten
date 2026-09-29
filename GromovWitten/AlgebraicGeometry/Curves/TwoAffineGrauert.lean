/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TwoAffineFibreCohomologyOne
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineCohomologyProjective

/-!
# Two-affine Grauert conclusions

These results combine projectivity of degree-one cohomology from locally
constant actual fibre dimensions with the two-affine degree-zero projectivity
and base-change theorem. The hypotheses retain the affine cover and stalk
flatness data explicitly.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Both degree-zero and degree-one cohomology are projective under the two-affine Grauert
hypotheses and locally constant actual fibre H¹ dimensions. -/
theorem projective_cohomology_zero_one_of_locallyConstant_fibre
    [IsNoetherianRing R] [IsReduced R] [IsLocallyNoetherian X]
    (s : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType s]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    [Module.Finite R (cohomologyModuleCat R s M 0)]
    [Module.Finite R (cohomologyModuleCat R s M 1)]
    (hd : IsLocallyConstant (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 1))) :
    Module.Projective R (cohomologyModuleCat R s M 0) ∧
      Module.Projective R (cohomologyModuleCat R s M 1) := by
  have hp := projective_cohomology_one_of_locallyConstant_fibre
    s M U V hU hV hI hcover hd
  have : Module.Flat R (cohomologyModuleCat R s M 1) := inferInstance
  exact ⟨projective_cohomology_zero_of_twoAffine s M U V hU hV hI hcover hflat
    inferInstance inferInstance, hp⟩

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero cohomology admits arbitrary scalar base change under the same two-affine Grauert
hypotheses. -/
def twoAffineCohomologyZeroBaseChangeIso_of_locallyConstant_fibre
    [IsNoetherianRing R] [IsReduced R] [IsLocallyNoetherian X]
    (s : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType s]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    [Module.Finite R (cohomologyModuleCat R s M 1)]
    (hd : IsLocallyConstant (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 1)))
    {T : CommRingCat.{u}} {Y : Scheme.{u}} (φ : CommRingCat.of R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ)) :
    (ModuleCat.extendScalars φ.hom).obj (cohomologyModuleCat R s M 0) ≅
      cohomologyModuleCat T g ((Scheme.Modules.pullback p).obj M) 0 := by
  have hp := projective_cohomology_one_of_locallyConstant_fibre
    s M U V hU hV hI hcover hd
  exact twoAffineCohomologyZeroBaseChangeIso_of_flat s φ p g h M U V hU hV hI hcover hflat

end GromovWitten.AlgebraicGeometry.Curves
