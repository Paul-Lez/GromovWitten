/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.FiniteFlatTwoTerm
import GromovWitten.AlgebraicGeometry.Curves.OpenAffineSectionsFlat
import GromovWitten.AlgebraicGeometry.SheafCohomology.CechPairBaseModule

/-!
# A finite flat replacement for a two-affine Čech complex

For an affine two-open cover, flatness of the relative stalks makes the
base-linear Čech terms flat.  If the actual degree-zero and degree-one
cohomology modules are finite, the finite flat two-term replacement theorem
applies to the resulting restriction-difference map.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- A finite flat two-term replacement for the base-linear Čech differential of an affine
two-open cover, assuming finite actual degree-zero and degree-one cohomology. -/
theorem exists_finiteFlatTwoTerm_of_twoAffine
    [IsNoetherianRing R] [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (h0 : Module.Finite R (cohomologyModuleCat (R : Type u) s M 0))
    (h1 : Module.Finite R (cohomologyModuleCat (R : Type u) s M 1)) :
    ∃ (n : ℕ) (q : (Fin n → R) →ₗ[R] baseSectionModule s (U ⊓ V) M),
      Function.Surjective
          ((LinearMap.range (baseCechPairMap s M U V).hom).mkQ.comp q) ∧
        Module.Flat R
          (LinearMap.ker (LinearMap.finiteFlatTwoTermMap
            (baseCechPairMap s M U V).hom q)) ∧
        Module.Finite R
          (LinearMap.ker (LinearMap.finiteFlatTwoTermMap
            (baseCechPairMap s M U V).hom q)) ∧
        Module.Projective R
          (LinearMap.ker (LinearMap.finiteFlatTwoTermMap
            (baseCechPairMap s M U V).hom q)) := by
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
  exact LinearMap.exists_finiteFlatTwoTerm d

end GromovWitten.AlgebraicGeometry.Curves
