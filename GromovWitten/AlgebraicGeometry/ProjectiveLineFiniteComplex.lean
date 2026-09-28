/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.FiniteFlatTwoTerm
import GromovWitten.AlgebraicGeometry.ProjectiveLineCechComparison
import GromovWitten.AlgebraicGeometry.ProjectiveLineCechFiniteness
import GromovWitten.AlgebraicGeometry.Curves.OpenAffineSectionsFlat

/-!
# A finite flat replacement for the projective-line Čech complex

For a quasi-coherent finitely presented module on the standard projective line, this file
constructs a finite flat two-term replacement of the Čech differential when the section modules
on the two charts and their overlap are flat over the base.  The stalk-flatness assumptions are
kept explicit; deriving them from a global relative flatness hypothesis is a separate step.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.ProjectiveLine
open GromovWitten.AlgebraicGeometry.Curves

universe u
noncomputable section

namespace GromovWitten.AlgebraicGeometry.ProjectiveLine

variable (R : Type u) [CommRing R]

local instance (b : Bool) : IsOpenImmersion (chartMap R b) := by
  cases b <;> infer_instance

local instance (P : ModuleCat (Polynomial R)) : Module R P :=
  Module.compHom P (algebraMap R (Polynomial R))

local instance (Q : ModuleCat (overlapRing R)) : Module R Q :=
  Module.compHom Q (algebraMap R (overlapRing R))

/-- The Čech differential has a finite flat two-term replacement under stalk-flatness on the
two standard charts and their Laurent overlap. -/
theorem exists_finiteFlatTwoTerm_of_chartStalkFlat
    {M : (scheme R).Modules} [M.IsQuasicoherent] [M.IsFinitePresentation]
    [IsNoetherianRing R]
    (hchart : ∀ b : Bool, ∀ x : PrimeSpectrum.Top (Polynomial R),
      Module.Flat R (affineStalkBase (CommRingCat.of R)
        ((Scheme.Modules.pullback (chartMap R b)).obj M) x))
    (hoverlap : ∀ x : PrimeSpectrum.Top (overlapRing R),
      Module.Flat R (affineStalkBase (CommRingCat.of R)
        ((Scheme.Modules.pullback (overlapι R)).obj M) x)) :
    ∃ (n : ℕ) (q : (Fin n → R) →ₗ[R] overlapSections R M),
      Function.Surjective
          ((LinearMap.range (projectiveLineCechDifferential R M)).mkQ.comp q) ∧
        Module.Flat R
          (LinearMap.ker (LinearMap.finiteFlatTwoTermMap
            (projectiveLineCechDifferential R M) q)) ∧
        Module.Finite R
          (LinearMap.ker (LinearMap.finiteFlatTwoTermMap
            (projectiveLineCechDifferential R M) q)) ∧
        Module.Projective R
          (LinearMap.ker (LinearMap.finiteFlatTwoTermMap
            (projectiveLineCechDifferential R M) q)) := by
  have hchartFlat (b : Bool) : Module.Flat R (chartSectionsBase R M b) := by
    exact affineSections_flat_of_stalks (CommRingCat.of R)
      ((Scheme.Modules.pullback (chartMap R b)).obj M) (hchart b)
  have hoverlapFlat : Module.Flat R (overlapSectionsBase R M) := by
    exact affineSections_flat_of_stalks (CommRingCat.of R)
      ((Scheme.Modules.pullback (overlapι R)).obj M) hoverlap
  let _ : Module.Flat R (chartSections R M false) := hchartFlat false
  let _ : Module.Flat R (chartSections R M true) := hchartFlat true
  let _ : Module.Flat R (overlapSections R M) := hoverlapFlat
  have hprod : Module.Flat R (chartSections R M false × chartSections R M true) :=
    LinearMap.flat_prod_of_flat
  have hker : Module.Finite R (projectiveLineCechDifferential R M).ker :=
    projectiveLineCechDifferential_ker_finite R
  have hcoker : Module.Finite R
      ((overlapSections R M) ⧸ (projectiveLineCechDifferential R M).range) :=
    projectiveLineCechDifferential_range_quotient_finite R
  exact @LinearMap.exists_finiteFlatTwoTerm R _ _ _ _ _ _ _
    (projectiveLineCechDifferential R M) hprod hoverlapFlat hker hcoker inferInstance

/-- The finite flat replacement follows from flatness of all relative stalks over the base. -/
theorem exists_finiteFlatTwoTerm_of_relativeStalkFlat
    {M : (scheme R).Modules} [M.IsQuasicoherent] [M.IsFinitePresentation]
    [IsNoetherianRing R]
    (h : ∀ x : scheme R,
      Module.Flat R (relativeStalkBase (structureMap R) M x)) :
    ∃ (n : ℕ) (q : (Fin n → R) →ₗ[R] overlapSections R M),
      Function.Surjective
          ((LinearMap.range (projectiveLineCechDifferential R M)).mkQ.comp q) ∧
        Module.Flat R
          (LinearMap.ker (LinearMap.finiteFlatTwoTermMap
            (projectiveLineCechDifferential R M) q)) ∧
        Module.Finite R
          (LinearMap.ker (LinearMap.finiteFlatTwoTermMap
            (projectiveLineCechDifferential R M) q)) ∧
      Module.Projective R
          (LinearMap.ker (LinearMap.finiteFlatTwoTermMap
            (projectiveLineCechDifferential R M) q)) := by
  have hchartFlat (b : Bool) : Module.Flat R (chartSectionsBase R M b) := by
    exact affineOpenSections_flat_of_relative_stalks
      (CommRingCat.of R) (CommRingCat.of (Polynomial R)) (scheme R)
      (structureMap R) (chartMap R b) (chartMap_comp_structureMap R b) M h
  have hoverlapFlat : Module.Flat R (overlapSectionsBase R M) := by
    exact affineOpenSections_flat_of_relative_stalks
      (CommRingCat.of R) (CommRingCat.of (overlapRing R)) (scheme R)
      (structureMap R) (overlapι R) (overlap_comp_structureMap R) M h
  let _ : Module.Flat R (chartSections R M false) := hchartFlat false
  let _ : Module.Flat R (chartSections R M true) := hchartFlat true
  let _ : Module.Flat R (overlapSections R M) := hoverlapFlat
  have hprod : Module.Flat R (chartSections R M false × chartSections R M true) :=
    LinearMap.flat_prod_of_flat
  have hker : Module.Finite R (projectiveLineCechDifferential R M).ker :=
    projectiveLineCechDifferential_ker_finite R
  have hcoker : Module.Finite R
      ((overlapSections R M) ⧸ (projectiveLineCechDifferential R M).range) :=
    projectiveLineCechDifferential_range_quotient_finite R
  exact @LinearMap.exists_finiteFlatTwoTerm R _ _ _ _ _ _ _
    (projectiveLineCechDifferential R M) hprod hoverlapFlat hker hcoker inferInstance

/-- The kernel of a finite replacement of the projective-line Čech differential is canonically
isomorphic to the actual degree-zero cohomology module. -/
def finiteComplexKernelIso (M : (scheme R).Modules) {n : ℕ}
    (q : (Fin n → R) →ₗ[R] overlapSectionsBase R M) :
    ModuleCat.of R (LinearMap.finiteFlatTwoTermDifferential
      (projectiveLineCechDifferential R M) q).ker ≅
      cohomologyModuleCat R (structureMap R) M 0 := by
  let d := projectiveLineCechDifferential R M
  let d' := LinearMap.finiteFlatTwoTermDifferential d q
  let α := kernel.map (ModuleCat.ofHom d') (ModuleCat.ofHom d)
    (ModuleCat.ofHom (LinearMap.finiteFlatTwoTermLeft d q))
    (ModuleCat.ofHom q) (LinearMap.finiteFlatTwoTerm_isPullback d q).w
  have : IsIso α := LinearMap.finiteFlatTwoTerm_kernel_map_isIso d q
  exact (ModuleCat.kernelIsoKer (ModuleCat.ofHom d')).symm ≪≫ asIso α ≪≫
    ModuleCat.kernelIsoKer (ModuleCat.ofHom d) ≪≫ (projectiveLineCechKernelIso R M).symm

/-- The cokernel of a finite replacement of the projective-line Čech differential is canonically
isomorphic to the actual degree-one cohomology module when the replacement covers the range. -/
def finiteComplexCokernelIso [IsNoetherianRing R]
    (M : (scheme R).Modules) [M.IsQuasicoherent] {n : ℕ}
    (q : (Fin n → R) →ₗ[R] overlapSectionsBase R M)
    (hq : Function.Surjective ((projectiveLineCechDifferential R M).range.mkQ.comp q)) :
    ModuleCat.of R ((Fin n → R) ⧸ (LinearMap.finiteFlatTwoTermDifferential
      (projectiveLineCechDifferential R M) q).range) ≅
      cohomologyModuleCat R (structureMap R) M 1 := by
  let d := projectiveLineCechDifferential R M
  let d' := LinearMap.finiteFlatTwoTermDifferential d q
  let α := cokernel.map (ModuleCat.ofHom d') (ModuleCat.ofHom d)
    (ModuleCat.ofHom (LinearMap.finiteFlatTwoTermLeft d q))
    (ModuleCat.ofHom q) (LinearMap.finiteFlatTwoTerm_isPullback d q).w
  have : IsIso α := LinearMap.finiteFlatTwoTerm_cokernel_map_isIso d q hq
  exact (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom d')).symm ≪≫ asIso α ≪≫
    ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom d) ≪≫ projectiveLineCechCokernelIso R M

end GromovWitten.AlgebraicGeometry.ProjectiveLine
