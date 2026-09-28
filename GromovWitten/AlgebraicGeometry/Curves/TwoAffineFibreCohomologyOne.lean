/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineBaseFibreCohomology
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineCohomologyBaseChange
import GromovWitten.AlgebraicGeometry.TwoTermSemicontinuity
import GromovWitten.Algebra.ReducedFibreFlatness

/-!
# Fibre degree-one cohomology on a two-affine cover

The actual scheme-theoretic fibre cohomology in degree one is compared with
the scalar extension of the base cohomology. This yields upper semicontinuity
under finite presentation and projectivity when the fibre dimensions are
locally constant over a reduced Noetherian base.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Degree-one cohomology of an affine-base fibre is the scalar extension of base cohomology. -/
def affineBaseFibreCohomologyOneIso [IsLocallyNoetherian X]
    (s : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType s]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤) (q : PrimeSpectrum R) :
    ModuleCat.of q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[R] cohomologyModuleCat R s M 1) ≅
        affineBaseFibreCohomology s M q 1 := by
  let φ := CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField)
  have := affineBaseFibre_isLocallyNoetherian s q
  exact (ModuleCat.extendScalarsAlgebraIso (cohomologyModuleCat R s M 1)).symm ≪≫
    twoAffineCohomologyOneBaseChangeIso s φ
      (pullback.fst s (Spec.map φ)) (pullback.snd s (Spec.map φ))
      (IsPullback.of_hasPullback _ _) M U V hU hV hI hcover

set_option backward.isDefEq.respectTransparency false in
/-- Degree-one fibre dimensions are upper semicontinuous when base degree-one cohomology is
finite over a Noetherian affine base. -/
theorem upperSemicontinuous_affineBaseFibreCohomology_one
    [IsNoetherianRing R] [IsLocallyNoetherian X]
    (s : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType s]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤) [Module.Finite R (cohomologyModuleCat R s M 1)] :
    UpperSemicontinuous (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 1)) := by
  have : Module.FinitePresentation R (cohomologyModuleCat R s M 1) :=
    Module.finitePresentation_of_finite R _
  have h := upperSemicontinuous_fibreFinrank_of_finitePresentation
    (cohomologyModuleCat R s M 1)
  convert h using 1
  funext q
  exact (affineBaseFibreCohomologyOneIso s M U V hU hV hI hcover q).toLinearEquiv.finrank_eq.symm

set_option backward.isDefEq.respectTransparency false in
/-- Finite base degree-one cohomology is projective when the actual fibre dimensions are locally
constant over a reduced Noetherian affine base. -/
theorem projective_cohomology_one_of_locallyConstant_fibre
    [IsNoetherianRing R] [IsReduced R] [IsLocallyNoetherian X]
    (s : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType s]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤) [Module.Finite R (cohomologyModuleCat R s M 1)]
    (hd : IsLocallyConstant (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 1))) :
    Module.Projective R (cohomologyModuleCat R s M 1) := by
  have : Module.FinitePresentation R (cohomologyModuleCat R s M 1) :=
    Module.finitePresentation_of_finite R _
  apply GromovWitten.Algebra.reduced_fibre_projective
  convert hd using 1
  funext q
  exact (affineBaseFibreCohomologyOneIso s M U V hU hV hI hcover q).toLinearEquiv.finrank_eq

end GromovWitten.AlgebraicGeometry.Curves
