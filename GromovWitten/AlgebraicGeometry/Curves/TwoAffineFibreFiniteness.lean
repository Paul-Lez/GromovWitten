/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineBaseFibreCohomology
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineTensorCechKernel
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineFibreCohomologyOne
import GromovWitten.Algebra.FiniteTensorKernel

/-!
# Finiteness of two-affine fibre cohomology

The two-affine Čech kernel comparison gives finiteness of actual fibre H⁰
under flatness and finite base cohomology. The degree-one scalar-extension
comparison gives the corresponding H¹ finiteness directly.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The actual degree-zero cohomology of a fibre is finite under the two-affine flatness and
finite-cohomology hypotheses. -/
theorem finite_affineBaseFibreCohomology_zero
    [IsNoetherianRing R] [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (h0 : Module.Finite R (cohomologyModuleCat (R : Type u) s M 0))
    (h1 : Module.Finite R (cohomologyModuleCat (R : Type u) s M 1))
    (q : PrimeSpectrum R) :
    Module.Finite q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 0) := by
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
  have := ModuleCat.finite_kernel_extendScalars_of_flat_finite_cohomology
    (baseCechPairMap s M U V) (algebraMap R q.asIdeal.ResidueField)
  let φ := CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField)
  exact Module.Finite.equiv (twoAffineTensorCechKernelIso s φ
    (pullback.fst s (Spec.map φ)) (pullback.snd s (Spec.map φ))
    (IsPullback.of_hasPullback _ _) M U V hU hV hI hcover).toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The actual degree-one cohomology of a fibre is finite whenever base degree-one cohomology is
finite and the scalar-extension comparison is available on the two-affine cover. -/
theorem finite_affineBaseFibreCohomology_one
    [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) [LocallyOfFiniteType s]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤)
    [Module.Finite R (cohomologyModuleCat (R : Type u) s M 1)]
    (q : PrimeSpectrum R) :
    Module.Finite q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 1) := by
  let _ : Module.Finite R (cohomologyModuleCat (R : Type u) s M 1) := inferInstance
  have h := affineBaseFibreCohomologyOneIso s M U V hU hV hI hcover q
  exact Module.Finite.equiv h.toLinearEquiv

end GromovWitten.AlgebraicGeometry.Curves
