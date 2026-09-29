/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.OpenPullbackSectionsNaturality
import GromovWitten.AlgebraicGeometry.Curves.OpenPullbackSectionsLinear
import GromovWitten.AlgebraicGeometry.ProjectiveLineCechFiniteness
import GromovWitten.AlgebraicGeometry.ProjectiveLineSections
import GromovWitten.AlgebraicGeometry.ProjectiveLineCohomology
import GromovWitten.AlgebraicGeometry.SheafCohomology.CechPairBaseModule

/-!
# Restriction squares for the projective-line Čech cover

The actual section maps from the two standard affine charts to their Laurent
overlap agree with restriction of the original sheaf sections.  These are the
underlying additive identities used by the later base-ring linear comparison.
-/

open CategoryTheory AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.ProjectiveLine
open GromovWitten.AlgebraicGeometry.Curves
open GromovWitten.AlgebraicGeometry.SheafCohomology
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

/-- The first chart restriction agrees with restriction of sections to the overlap. -/
lemma chartZeroRestrictionMap_openPullbackSectionsIso
    (M : (scheme R).Modules)
    (x : chartSections R M false) :
    (openPullbackSectionsIso (overlapι R) M).hom
        ((chartZeroRestrictionMap R M).hom x) =
      M.presheaf.map (homOfLE (show (overlapι R).opensRange ≤ (chartZero R).opensRange from
        by simpa only [← overlapToChartZero_comp R] using
          (range_comp_le (CommRingCat.ofHom (algebraMap (Polynomial R) (overlapRing R)))
            (chartZero R)))).op
        ((openPullbackSectionsIso (chartZero R) M).hom x) := by
  change (openPullbackSectionsIso (overlapι R) M).hom
      (((moduleSpecΓFunctor (R := CommRingCat.of (overlapRing R))).map
        (((Scheme.Modules.pullbackComp (overlapToChartZero R) (chartZero R)).hom.app M) ≫
          ((Scheme.Modules.pullbackCongr (overlapToChartZero_comp R)).hom.app M)))
        ((affinePullbackGammaUnit
          (CommRingCat.ofHom (algebraMap (Polynomial R) (overlapRing R)))
          ((Scheme.Modules.pullback (chartZero R)).obj M)).hom x)) = _
  exact openPullbackSectionsIso_unit_comp_congr
    (φ := CommRingCat.ofHom (algebraMap (Polynomial R) (overlapRing R)))
    (j := chartZero R) (k := overlapι R)
    (h := overlapToChartZero_comp R) M x

/-- The second chart restriction agrees with restriction of sections to the overlap. -/
lemma chartOneRestrictionMap_openPullbackSectionsIso
    (M : (scheme R).Modules)
    (x : chartSections R M true) :
    (openPullbackSectionsIso (overlapι R) M).hom
        ((chartOneRestrictionMap R M).hom x) =
      M.presheaf.map (homOfLE (show (overlapι R).opensRange ≤ (chartOne R).opensRange from
        by simpa only [← overlapToChartOne_comp R] using
          (range_comp_le (CommRingCat.ofHom (flipHom R)) (chartOne R)))).op
        ((openPullbackSectionsIso (chartOne R) M).hom x) := by
  change (openPullbackSectionsIso (overlapι R) M).hom
      (((moduleSpecΓFunctor (R := CommRingCat.of (overlapRing R))).map
        (((Scheme.Modules.pullbackComp (overlapToChartOne R) (chartOne R)).hom.app M) ≫
          ((Scheme.Modules.pullbackCongr (overlapToChartOne_comp R)).hom.app M)))
        ((affinePullbackGammaUnit (CommRingCat.ofHom (flipHom R))
          ((Scheme.Modules.pullback (chartOne R)).obj M)).hom x)) = _
  exact openPullbackSectionsIso_unit_comp_congr
    (φ := CommRingCat.ofHom (flipHom R))
    (j := chartOne R) (k := overlapι R)
    (h := overlapToChartOne_comp R) M x

/-- The overlap inclusion is compatible with the structure morphism over `R`. -/
lemma overlap_comp_structureMap :
    overlapι R ≫ structureMap R =
      Spec.map (CommRingCat.ofHom (algebraMap R (overlapRing R))) := by
  rw [← overlapToChartZero_comp R, Category.assoc, chartZero_comp_structureMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- Sections on either standard chart, identified with sections on its image,
as an equivalence of base-ring modules. -/
def chartSectionsOpenLinearEquiv (M : (scheme R).Modules) (b : Bool) :
    chartSectionsBase R M b ≃ₗ[R]
      baseSectionModule (structureMap R) (chartMap R b).opensRange M := by
  cases b
  · exact openPullbackSectionsLinearEquiv (structureMap R) (chartZero R)
      (CommRingCat.ofHom (algebraMap R (Polynomial R)))
      (chartZero_comp_structureMap R) M
  · exact openPullbackSectionsLinearEquiv (structureMap R) (chartOne R)
      (CommRingCat.ofHom (algebraMap R (Polynomial R)))
      (chartOne_comp_structureMap R) M

/-- Sections on the Laurent overlap, identified with sections on its image,
as an equivalence of base-ring modules. -/
def overlapSectionsOpenLinearEquiv (M : (scheme R).Modules) :
    overlapSectionsBase R M ≃ₗ[R]
      baseSectionModule (structureMap R) (overlapι R).opensRange M :=
  openPullbackSectionsLinearEquiv (structureMap R) (overlapι R)
    (CommRingCat.ofHom (algebraMap R (overlapRing R)))
    (overlap_comp_structureMap R) M

@[simp]
lemma chartSectionsOpenLinearEquiv_apply
    (M : (scheme R).Modules) (b : Bool) (x : chartSectionsBase R M b) :
    chartSectionsOpenLinearEquiv R M b x =
      (openPullbackSectionsIso (chartMap R b) M).hom x := by
  cases b <;> rfl

@[simp]
lemma overlapSectionsOpenLinearEquiv_apply
    (M : (scheme R).Modules) (x : overlapSectionsBase R M) :
    overlapSectionsOpenLinearEquiv R M x =
      (openPullbackSectionsIso (overlapι R) M).hom x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The first chart restriction commutes with the open-section identifications. -/
lemma chartZeroRestrictionMap_openLinearEquiv
    (M : (scheme R).Modules) (x : chartSectionsBase R M false) :
    overlapSectionsOpenLinearEquiv R M ((chartZeroRestrictionMap R M).hom x) =
      M.presheaf.map (homOfLE (show (overlapι R).opensRange ≤ (chartZero R).opensRange from
        by simpa only [← overlapToChartZero_comp R] using
          (range_comp_le (CommRingCat.ofHom (algebraMap (Polynomial R) (overlapRing R)))
            (chartZero R)))).op
        (chartSectionsOpenLinearEquiv R M false x) := by
  change (openPullbackSectionsIso (overlapι R) M).hom
      ((chartZeroRestrictionMap R M).hom x) = _
  exact chartZeroRestrictionMap_openPullbackSectionsIso R M x

set_option backward.isDefEq.respectTransparency false in
/-- The second chart restriction commutes with the open-section identifications. -/
lemma chartOneRestrictionMap_openLinearEquiv
    (M : (scheme R).Modules) (x : chartSectionsBase R M true) :
    overlapSectionsOpenLinearEquiv R M ((chartOneRestrictionMap R M).hom x) =
      M.presheaf.map (homOfLE (show (overlapι R).opensRange ≤ (chartOne R).opensRange from
        by simpa only [← overlapToChartOne_comp R] using
          (range_comp_le (CommRingCat.ofHom (flipHom R)) (chartOne R)))).op
        (chartSectionsOpenLinearEquiv R M true x) := by
  change (openPullbackSectionsIso (overlapι R) M).hom
      ((chartOneRestrictionMap R M).hom x) = _
  exact chartOneRestrictionMap_openPullbackSectionsIso R M x

/-- The pair of chart section modules, transported to base-ring modules. -/
def projectiveLineCechPairIso (M : (scheme R).Modules) :
    ModuleCat.of R (chartSectionsBase R M false × chartSectionsBase R M true) ≅
      (ModuleCat.restrictScalars (baseRingHom R (structureMap R))).obj
        (sectionsPairModule M (chartZero R).opensRange (chartOne R).opensRange) :=
  ((chartSectionsOpenLinearEquiv R M false).prodCongr
    (chartSectionsOpenLinearEquiv R M true)).toModuleIso

/-- The overlap section module, transported to the base-ring module on the
intersection of the two chart images. -/
def projectiveLineCechOverlapIso (M : (scheme R).Modules) :
    ModuleCat.of R (overlapSectionsBase R M) ≅
      (ModuleCat.restrictScalars (baseRingHom R (structureMap R))).obj
        (sectionModuleCat M
          ((chartZero R).opensRange ⊓ (chartOne R).opensRange) :
            ModuleCat Γ(scheme R, ⊤)) :=
  ((overlapSectionsOpenLinearEquiv R M).trans
    (baseSectionCongr (structureMap R) M
      (opensRange_chartZero_inf_chartOne R).symm)).toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- The projective-line Čech differential commutes with the two section
identifications over the base ring. -/
lemma projectiveLineCechDifferential_square (M : (scheme R).Modules) :
    ModuleCat.ofHom (projectiveLineCechDifferential R M) ≫
        (projectiveLineCechOverlapIso R M).hom =
      (projectiveLineCechPairIso R M).hom ≫ baseCechPairMap (structureMap R) M
        (chartZero R).opensRange (chartOne R).opensRange := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change M.presheaf.map (eqToHom (opensRange_chartZero_inf_chartOne R)).op
      ((openPullbackSectionsIso (overlapι R) M).hom
        ((show overlapSectionsBase R M from (chartZeroRestrictionMap R M).hom x) -
          (show overlapSectionsBase R M from (chartOneRestrictionMap R M).hom y))) =
    M.presheaf.map (homOfLE inf_le_left).op
        ((openPullbackSectionsIso (chartZero R) M).hom x) -
      M.presheaf.map (homOfLE inf_le_right).op
        ((openPullbackSectionsIso (chartOne R) M).hom y)
  rw [map_sub, chartZeroRestrictionMap_openPullbackSectionsIso,
    chartOneRestrictionMap_openPullbackSectionsIso, map_sub]
  congr 1 <;>
    rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp] <;>
      rfl

open CategoryTheory.Limits

/-- The degree-zero cohomology of the projective line is the kernel of the
base-linear Čech differential. -/
def projectiveLineCechKernelIso (M : (scheme R).Modules) :
    ModuleCat.of R (cohomologyModuleCat R (structureMap R) M 0) ≅
      ModuleCat.of R (projectiveLineCechDifferential R M).ker :=
  cohomologyZeroIsoBaseCechKernel (structureMap R) M
      (chartZero R).opensRange (chartOne R).opensRange
      (opensRange_chartZero_sup_chartOne R) ≪≫
    (kernel.mapIso (ModuleCat.ofHom (projectiveLineCechDifferential R M))
      (baseCechPairMap (structureMap R) M
        (chartZero R).opensRange (chartOne R).opensRange)
      (projectiveLineCechPairIso R M) (projectiveLineCechOverlapIso R M)
      (projectiveLineCechDifferential_square R M)).symm ≪≫
    ModuleCat.kernelIsoKer (ModuleCat.ofHom (projectiveLineCechDifferential R M))

/-- The degree-one projective-line Čech quotient is the base-linear first
cohomology module. -/
def projectiveLineCechCokernelIso [IsNoetherianRing R]
    (M : (scheme R).Modules) [M.IsQuasicoherent] :
    ModuleCat.of R ((overlapSectionsBase R M) ⧸
      (projectiveLineCechDifferential R M).range) ≅
      ModuleCat.of R (cohomologyModuleCat R (structureMap R) M 1) :=
  (ModuleCat.cokernelIsoRangeQuotient
      (ModuleCat.ofHom (projectiveLineCechDifferential R M))).symm ≪≫
    cokernel.mapIso (ModuleCat.ofHom (projectiveLineCechDifferential R M))
      (baseCechPairMap (structureMap R) M
        (chartZero R).opensRange (chartOne R).opensRange)
      (projectiveLineCechPairIso R M) (projectiveLineCechOverlapIso R M)
      (projectiveLineCechDifferential_square R M) ≪≫
    baseCechCokernelIsoCohomology (structureMap R) M
      (chartZero R).opensRange (chartOne R).opensRange
      (isAffineOpen_opensRange_chartZero R) (isAffineOpen_opensRange_chartOne R)
      (opensRange_chartZero_sup_chartOne R)

/-- Degree-zero projective-line cohomology is finite under finite-presentation
and Noetherian hypotheses. -/
lemma finite_cohomology_zero [IsNoetherianRing R]
    {M : (scheme R).Modules} [M.IsQuasicoherent] [M.IsFinitePresentation] :
    Module.Finite R (cohomologyModuleCat R (structureMap R) M 0) := by
  have : Module.Finite R (projectiveLineCechDifferential R M).ker :=
    projectiveLineCechDifferential_ker_finite R
  exact Module.Finite.equiv (projectiveLineCechKernelIso R M).toLinearEquiv.symm

/-- Degree-one projective-line cohomology is finite under finite-presentation
and Noetherian hypotheses. -/
lemma finite_cohomology_one [IsNoetherianRing R]
    {M : (scheme R).Modules} [M.IsQuasicoherent] [M.IsFinitePresentation] :
    Module.Finite R (cohomologyModuleCat R (structureMap R) M 1) := by
  have : Module.Finite R
      ((overlapSectionsBase R M) ⧸ (projectiveLineCechDifferential R M).range) :=
    projectiveLineCechDifferential_range_quotient_finite R
  exact Module.Finite.equiv (projectiveLineCechCokernelIso R M).toLinearEquiv

/-- All cohomology modules of a finitely presented quasicoherent module on the
projective line are finite over a Noetherian base ring. -/
theorem finite_cohomology_all [IsNoetherianRing R]
    {M : (scheme R).Modules} [M.IsQuasicoherent] [M.IsFinitePresentation] (n : ℕ) :
    Module.Finite R (cohomologyModuleCat R (structureMap R) M n) := by
  cases n with
  | zero =>
      exact finite_cohomology_zero R
  | succ n =>
      cases n with
      | zero =>
          exact finite_cohomology_one R
      | succ n =>
          exact finite_cohomology_succ_succ R M n

end GromovWitten.AlgebraicGeometry.ProjectiveLine
