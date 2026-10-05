/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteCohomologyBaseChange
import GromovWitten.AlgebraicGeometry.Curves.AffineBaseFibreCohomology
import GromovWitten.AlgebraicGeometry.TwoTermSemicontinuity
import GromovWitten.Algebra.ReducedFibreFlatness

/-!
# Degree-one Grauert conclusions with finite cohomology

For relatively flat quasi-coherent modules on curve families over Noetherian
affine bases, finite actual cohomology gives upper semicontinuity of the actual
fibre H¹ dimensions. Over a reduced base, local constancy implies projectivity
of actual base H¹. Proper-family finite generation remains an explicit input.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- For a flat quasi-coherent module on a curve family, with actual cohomology finite in
all degrees at least two, tensoring base H¹ with a residue field computes the actual
H¹ of the scheme-theoretic fibre. -/
noncomputable def familyAffineBaseFibreCohomologyOneIso
    [IsNoetherianRing R]
    (s : X ⟶ Spec (CommRingCat.of R)) [FamilyOfCurves s]
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    (q : PrimeSpectrum R) :
    ModuleCat.of q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[R] cohomologyModuleCat R s M 1) ≅
        affineBaseFibreCohomology s M q 1 := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of q.asIdeal.ResidueField :=
    CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField)
  let p := Limits.pullback.fst s (Spec.map φ)
  let g := Limits.pullback.snd s (Spec.map φ)
  let h : IsPullback p g s (Spec.map φ) := IsPullback.of_hasPullback _ _
  let : IsLocallyNoetherian (Limits.pullback s (Spec.map φ)) :=
    affineBaseFibre_isLocallyNoetherian s q
  exact (ModuleCat.extendScalarsAlgebraIso (cohomologyModuleCat R s M 1)).symm ≪≫
    family_cohomology_baseChangeIso_pos s φ p g h M hflat hfinite 1 (by omega)

/-- Fibre dimensions of H¹ are upper semicontinuous under the explicit finite actual
cohomology hypothesis in degrees at least two and finite actual base H¹. -/
theorem upperSemicontinuous_familyAffineBaseFibreCohomology_one
    [IsNoetherianRing R]
    (s : X ⟶ Spec (CommRingCat.of R)) [FamilyOfCurves s]
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    (hfiniteOne : Module.Finite R (cohomologyModuleCat R s M 1)) :
    UpperSemicontinuous (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 1)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let : Module.Finite R (cohomologyModuleCat R s M 1) := hfiniteOne
  have : Module.FinitePresentation R (cohomologyModuleCat R s M 1) :=
    Module.finitePresentation_of_finite R _
  have h := upperSemicontinuous_fibreFinrank_of_finitePresentation
    (cohomologyModuleCat R s M 1)
  convert h using 1
  funext q
  exact (familyAffineBaseFibreCohomologyOneIso s M hflat hfinite q).toLinearEquiv.finrank_eq.symm

/-- Over a reduced Noetherian base, finite actual H¹ with locally constant actual fibre
H¹ dimensions is projective, provided the relative stalks are flat and actual cohomology
is finite in all degrees at least two. -/
theorem family_projective_cohomology_one_of_locallyConstant_fibre
    [IsNoetherianRing R] [IsReduced R]
    (s : X ⟶ Spec (CommRingCat.of R)) [FamilyOfCurves s]
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    (hfiniteOne : Module.Finite R (cohomologyModuleCat R s M 1))
    (hd : IsLocallyConstant (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 1))) :
    Module.Projective R (cohomologyModuleCat R s M 1) := by
  let : Module.Finite R (cohomologyModuleCat R s M 1) := hfiniteOne
  have : Module.FinitePresentation R (cohomologyModuleCat R s M 1) :=
    Module.finitePresentation_of_finite R _
  apply GromovWitten.Algebra.reduced_fibre_projective
  convert hd using 1
  funext q
  exact (familyAffineBaseFibreCohomologyOneIso s M hflat hfinite q).toLinearEquiv.finrank_eq

end GromovWitten.AlgebraicGeometry.Curves

end
