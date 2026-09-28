/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineBaseFibreCohomology
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineTensorCechKernel
import GromovWitten.AlgebraicGeometry.TwoTermSemicontinuity

/-!
# Upper semicontinuity of degree-zero affine-base fibre cohomology

For a flat Čech two-open cover with finite actual degree-zero and degree-one cohomology,
the degree-zero fibre dimension is upper semicontinuous.  The fibre comparison uses the
kernel of the scalar-extended Čech differential and therefore requires no separate base-change
or fibre-finiteness hypothesis.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Upper semicontinuity of degree-zero cohomology fibre dimensions for an affine two-open cover. -/
theorem upperSemicontinuous_affineBaseFibreCohomology_zero
    [IsNoetherianRing R] [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (h0 : Module.Finite R (cohomologyModuleCat (R : Type u) s M 0))
    (h1 : Module.Finite R (cohomologyModuleCat (R : Type u) s M 1)) :
    UpperSemicontinuous (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 0)) := by
  let d := (baseCechPairMap s M U V).hom
  have hUflat : Module.Flat R (baseSectionModule s U M) :=
    baseSections_flat_of_relative_stalks s M U hU hflat
  have hVflat : Module.Flat R (baseSectionModule s V M) :=
    baseSections_flat_of_relative_stalks s M V hV hflat
  have hIflat : Module.Flat R (baseSectionModule s (U ⊓ V) M) :=
    baseSections_flat_of_relative_stalks s M (U ⊓ V) hI hflat
  let _ : Module.Flat R (baseSectionModule s U M) := hUflat
  let _ : Module.Flat R (baseSectionModule s V M) := hVflat
  let _ : Module.Flat R (baseSectionModule s (U ⊓ V) M) := hIflat
  have hprod : Module.Flat R
      (baseSectionModule s U M × baseSectionModule s V M) :=
    LinearMap.flat_prod_of_flat
  let _ : Module.Flat R
      (baseSectionModule s U M × baseSectionModule s V M) := hprod
  let ePair : ModuleCat.of R (baseSectionModule s U M × baseSectionModule s V M) ≅
      (ModuleCat.restrictScalars (baseRingHom (R : Type u) s)).obj
        (sectionsPairModule M U V) := Iso.refl _
  let eOverlap : baseSectionModule s (U ⊓ V) M ≅
      (ModuleCat.restrictScalars (baseRingHom (R : Type u) s)).obj
        (sectionModuleCat M (U ⊓ V)) := Iso.refl _
  let _ : Module.Flat R
      (((ModuleCat.restrictScalars (baseRingHom (R : Type u) s)).obj
        (sectionsPairModule M U V))) :=
    Module.Flat.of_linearEquiv ePair.toLinearEquiv.symm
  let _ : Module.Flat R
      (((ModuleCat.restrictScalars (baseRingHom (R : Type u) s)).obj
        (sectionModuleCat M (U ⊓ V)))) :=
    Module.Flat.of_linearEquiv eOverlap.toLinearEquiv.symm
  have hker : Module.Finite R d.ker := by
    let _ : Module.Finite R (cohomologyModuleCat (R : Type u) s M 0) := h0
    exact Module.Finite.equiv
      ((cohomologyZeroIsoBaseCechKernel s M U V hcover ≪≫
        ModuleCat.kernelIsoKer (baseCechPairMap s M U V)).toLinearEquiv)
  have hcoker : Module.Finite R
      (baseSectionModule s (U ⊓ V) M ⧸ d.range) := by
    let _ : Module.Finite R (cohomologyModuleCat (R : Type u) s M 1) := h1
    exact Module.Finite.equiv
      ((ModuleCat.cokernelIsoRangeQuotient (baseCechPairMap s M U V)).symm ≪≫
        baseCechCokernelIsoCohomology s M U V hU hV hcover).toLinearEquiv.symm
  have h := upperSemicontinuous_fibreKernelFinrank_of_flat_finite_cohomology
    (baseCechPairMap s M U V)
  convert h using 1
  funext q
  let φ := CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField)
  exact (twoAffineTensorCechKernelIso s φ (pullback.fst s (Spec.map φ))
    (pullback.snd s (Spec.map φ)) (IsPullback.of_hasPullback _ _)
    M U V hU hV hI hcover).toLinearEquiv.finrank_eq.symm

end GromovWitten.AlgebraicGeometry.Curves
