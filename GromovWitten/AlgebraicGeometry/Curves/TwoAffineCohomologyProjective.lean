/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.TensorKernel
import GromovWitten.Algebra.FiniteFlatTwoTerm
import GromovWitten.AlgebraicGeometry.Curves.OpenAffineSectionsFlat
import GromovWitten.AlgebraicGeometry.SheafCohomology.CechPairBaseModule
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Projectivity of degree-zero cohomology for an affine two-open cover

The scalar-linear Čech differential has flat source and target when the relative stalks are flat.
Flatness of degree-one cohomology makes its cokernel flat, so the Čech kernel is flat.  Noetherian
finite-presentation of the degree-zero cohomology then upgrades this kernel to a projective module.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- Degree-zero cohomology is projective when the two-affine Čech terms are flat and degree-one
cohomology is flat.  Finiteness of degree zero is the only finiteness input. -/
theorem projective_cohomology_zero_of_twoAffine
    [IsNoetherianRing R] [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (h0 : Module.Finite R (cohomologyModuleCat (R : Type u) s M 0))
    (h1flat : Module.Flat R (cohomologyModuleCat (R : Type u) s M 1)) :
    Module.Projective R (cohomologyModuleCat (R : Type u) s M 0) := by
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
  have hquotientflat : Module.Flat R
      (baseSectionModule s (U ⊓ V) M ⧸ d.range) := by
    let _ : Module.Flat R (cohomologyModuleCat (R : Type u) s M 1) := h1flat
    exact Module.Flat.of_linearEquiv
      ((ModuleCat.cokernelIsoRangeQuotient (baseCechPairMap s M U V)).symm ≪≫
        baseCechCokernelIsoCohomology s M U V hU hV hcover).toLinearEquiv
  let _ : Module.Flat R (baseSectionModule s (U ⊓ V) M ⧸ d.range) := hquotientflat
  have hkerflat : Module.Flat R d.ker :=
    d.kernel_flat_of_flat_source_of_flat_target_of_flat_cokernel
  let _ : Module.Flat R d.ker := hkerflat
  let eK : ModuleCat.of R (cohomologyModuleCat (R : Type u) s M 0) ≅
      ModuleCat.of R d.ker :=
    cohomologyZeroIsoBaseCechKernel s M U V hcover ≪≫
      ModuleCat.kernelIsoKer (baseCechPairMap s M U V)
  have hkerfinite : Module.Finite R d.ker := by
    let _ : Module.Finite R (cohomologyModuleCat (R : Type u) s M 0) := h0
    exact Module.Finite.equiv eK.toLinearEquiv
  let _ : Module.Finite R d.ker := hkerfinite
  let _ : Module.FinitePresentation R d.ker :=
    Module.finitePresentation_of_finite R d.ker
  have hkerprojective : Module.Projective R d.ker :=
    Module.Flat.projective_of_finitePresentation
  let _ : Module.Projective R d.ker := hkerprojective
  exact Module.Projective.of_equiv eK.toLinearEquiv.symm

end GromovWitten.AlgebraicGeometry.Curves
