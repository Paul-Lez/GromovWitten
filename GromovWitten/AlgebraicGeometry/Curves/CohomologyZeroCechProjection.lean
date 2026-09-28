/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.CechPairBaseModule
import GromovWitten.CategoryTheory.ScalarHomologyBaseChange

/-!
# The canonical degree-zero Cech projection

The base-linear Cech kernel comparison sends a degree-zero cohomology class to the pair of
its canonical restrictions on the two opens.  This is the pointwise identification used to
compare canonical degree-zero base-change maps with the Cech construction.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The Cech kernel comparison has the canonical pair of restrictions as its projection. -/
lemma cohomologyZeroIsoBaseCechKernel_projection (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (x : cohomologyModuleCat (R : Type u) s M 0) :
    kernel.ι (baseCechPairMap s M U V)
        ((cohomologyZeroIsoBaseCechKernel s M U V hcover).hom x) =
      (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          ((cohomologyZeroBaseLinearEquiv (R : Type u) s M) x),
        M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
          ((cohomologyZeroBaseLinearEquiv (R : Type u) s M) x)) := by
  let _ : Module Γ(X, ⊤) Γ(M, U ⊔ V) := sectionModule M (U ⊔ V)
  let _ : Module Γ(X, ⊤) (Γ(M, U) × Γ(M, V)) :=
    sectionsPairModuleStructure M U V
  let F := ModuleCat.restrictScalars (baseRingHom (R : Type u) s)
  let eTop : F.obj (sectionModuleCat M ⊤) ≅
      ModuleCat.of R (sectionsModuleCat (R : Type u) s M) :=
    (baseTopSectionsEquiv s M).toModuleIso
  let eCover : sectionModuleCat M (U ⊔ V) ≅ sectionModuleCat M ⊤ :=
    eqToIso (congrArg (sectionModuleCat M) hcover)
  let eK : sectionModuleCat M (U ⊔ V) ≅
      kernel (sectionsFromPairModuleHom M U V) :=
    (sectionsToPairKernelLinearEquiv M U V).toModuleIso ≪≫
      (ModuleCat.kernelIsoKer (sectionsFromPairModuleHom M U V)).symm
  change (((cohomologyZeroBaseLinearEquiv (R : Type u) s M).toModuleIso ≪≫
      eTop.symm ≪≫ F.mapIso eCover.symm ≪≫ F.mapIso eK ≪≫
      PreservesKernel.iso F (sectionsFromPairModuleHom M U V)).hom ≫
      kernel.ι (F.map (sectionsFromPairModuleHom M U V))).hom x = _
  have hcat :
      ((cohomologyZeroBaseLinearEquiv (R : Type u) s M).toModuleIso ≪≫
          eTop.symm ≪≫ F.mapIso eCover.symm ≪≫ F.mapIso eK ≪≫
          PreservesKernel.iso F (sectionsFromPairModuleHom M U V)).hom ≫
        kernel.ι (F.map (sectionsFromPairModuleHom M U V)) =
      ((cohomologyZeroBaseLinearEquiv (R : Type u) s M).toModuleIso ≪≫
          eTop.symm ≪≫ F.mapIso eCover.symm).hom ≫
        F.map eK.hom ≫ F.map (kernel.ι (sectionsFromPairModuleHom M U V)) := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, PreservesKernel.iso_hom,
      kernelComparison_comp_ι, Category.assoc]
  rw [hcat]
  have hK :
    eK.hom ≫ kernel.ι (sectionsFromPairModuleHom M U V) =
        ModuleCat.ofHom (sectionsToPairLinear M U V) := by
    dsimp only [eK]
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      ModuleCat.kernelIsoKer_inv_kernel_ι]
    rfl
  have hafter :
      ((cohomologyZeroBaseLinearEquiv (R : Type u) s M).toModuleIso ≪≫
          eTop.symm ≪≫ F.mapIso eCover.symm).hom ≫
        F.map eK.hom ≫ F.map (kernel.ι (sectionsFromPairModuleHom M U V)) =
      ((cohomologyZeroBaseLinearEquiv (R : Type u) s M).toModuleIso ≪≫
          eTop.symm ≪≫ F.mapIso eCover.symm).hom ≫
        F.map (ModuleCat.ofHom (sectionsToPairLinear M U V)) := by
    rw [← F.map_comp, hK]
  rw [hafter]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    ConcreteCategory.comp_apply]
  change sectionsToPairLinear M U V
    (eCover.inv ((cohomologyZeroBaseLinearEquiv (R : Type u) s M) x)) = _
  rw [sectionsToPairLinear_apply]
  have ht (W : X.Opens) (hw : W = ⊤) (Z : X.Opens) (hz : Z ≤ W)
      (z : sectionModuleCat M ⊤) :
      M.presheaf.map (homOfLE hz).op
        ((eqToIso (congrArg (sectionModuleCat M) hw)).inv z) =
      M.presheaf.map (homOfLE (le_top : Z ≤ ⊤)).op z := by
    subst W
    rfl
  exact Prod.ext (ht _ hcover U le_sup_left _) (ht _ hcover V le_sup_right _)

end GromovWitten.AlgebraicGeometry.Curves
