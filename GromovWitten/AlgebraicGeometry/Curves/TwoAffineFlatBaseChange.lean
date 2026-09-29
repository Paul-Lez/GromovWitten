/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TwoAffineCohomologyZeroBaseChangeCanonical
import GromovWitten.AlgebraicGeometry.Curves.ModulePullbackExact

/-!
# Flat base change for degree-zero cohomology on a two-affine cover

For a Cartesian base change with flat ring map, the degree-zero Cech comparison needs only a
quasi-coherent module, affine cover pieces and overlap, and the two pieces covering the source.
No Noetherian or stalk-flatness assumptions are needed.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero cohomology base change for a flat ring map and a two-affine cover. -/
def twoAffineCohomologyZeroBaseChangeIso_of_flat_base
    (s : X ⟶ Spec R) (φ : R ⟶ T) (hφ : φ.hom.Flat)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤) :
    (ModuleCat.extendScalars φ.hom).obj (cohomologyModuleCat R s M 0) ≅
      cohomologyModuleCat T g ((Scheme.Modules.pullback p).obj M) 0 := by
  have hc : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤ := by
    change p ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  let _ := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  have := cechPairBaseChangeMap_isIso s φ p g h M U V hU hV
  have := cechOverlapBaseChangeMap_isIso s φ p g h M U V hI
  exact (ModuleCat.extendScalars φ.hom).mapIso
      (cohomologyZeroIsoBaseCechKernel s M U V hcover) ≪≫
    PreservesKernel.iso (ModuleCat.extendScalars φ.hom) (baseCechPairMap s M U V) ≪≫
    kernel.mapIso ((ModuleCat.extendScalars φ.hom).map (baseCechPairMap s M U V))
      (baseCechPairMap g ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U) (p ⁻¹ᵁ V))
      (asIso (cechPairBaseChangeMap s φ p g h M U V))
      (asIso (cechOverlapBaseChangeMap s φ p g h M U V))
      (cechBaseChange_square s φ p g h M U V) ≪≫
    (cohomologyZeroIsoBaseCechKernel g ((Scheme.Modules.pullback p).obj M)
      (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hc).symm

set_option backward.isDefEq.respectTransparency false in
/-- The flat two-affine comparison has the canonical degree-zero projection formula. -/
lemma twoAffineCohomologyZeroBaseChangeIso_of_flat_base_projection
    (s : X ⟶ Spec R) (φ : R ⟶ T) (hφ : φ.hom.Flat)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤)
    (hc : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤) :
    (twoAffineCohomologyZeroBaseChangeIso_of_flat_base s φ hφ p g h M U V hU hV hI hcover).hom ≫
      (cohomologyZeroIsoBaseCechKernel g ((Scheme.Modules.pullback p).obj M)
        (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hc).hom ≫
      kernel.ι (baseCechPairMap g ((Scheme.Modules.pullback p).obj M)
        (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)) =
    (ModuleCat.extendScalars φ.hom).map
      ((cohomologyZeroIsoBaseCechKernel s M U V hcover).hom ≫
        kernel.ι (baseCechPairMap s M U V)) ≫ cechPairBaseChangeMap s φ p g h M U V := by
  simp only [twoAffineCohomologyZeroBaseChangeIso_of_flat_base, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc,
    kernel.mapIso_hom, asIso_hom, kernel.map, kernel.lift_ι,
    PreservesKernel.iso_hom, kernelComparison_comp_ι_assoc, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The flat two-affine comparison agrees with the canonical degree-zero base-change map. -/
lemma twoAffineCohomologyZeroBaseChangeIso_of_flat_base_hom_eq_canonical
    (s : X ⟶ Spec R) (φ : R ⟶ T) (hφ : φ.hom.Flat)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤) :
    (twoAffineCohomologyZeroBaseChangeIso_of_flat_base s φ hφ p g h M U V hU hV hI hcover).hom =
      canonicalCohomologyZeroBaseChangeMap s φ p g h M := by
  have hc : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤ := by
    change p ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  apply (cancel_mono ((cohomologyZeroIsoBaseCechKernel g ((Scheme.Modules.pullback p).obj M)
    (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hc).hom ≫
    kernel.ι (baseCechPairMap g ((Scheme.Modules.pullback p).obj M)
      (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)))).1
  rw [twoAffineCohomologyZeroBaseChangeIso_of_flat_base_projection]
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  simp only [ConcreteCategory.comp_apply, ModuleCat.ExtendScalars.map_tmul]
  rw [cechPairBaseChangeMap_one_tmul,
    cohomologyZeroIsoBaseCechKernel_projection,
    cohomologyZeroIsoBaseCechKernel_projection,
    canonicalCohomologyZeroBaseChangeMap_one_tmul]
  let η := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  apply Prod.ext
  · exact ConcreteCategory.congr_hom
      (η.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op)
      (cohomologyZeroBaseLinearEquiv (R : Type u) s M x)
  · exact ConcreteCategory.congr_hom
      (η.mapPresheaf.naturality (homOfLE (le_top : V ≤ ⊤)).op)
      (cohomologyZeroBaseLinearEquiv (R : Type u) s M x)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical degree-zero base-change map is invertible for a flat two-affine base change. -/
lemma canonicalCohomologyZeroBaseChangeMap_isIso_of_twoAffine_flat_base
    (s : X ⟶ Spec R) (φ : R ⟶ T) (hφ : φ.hom.Flat)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤) :
    IsIso (canonicalCohomologyZeroBaseChangeMap s φ p g h M) := by
  rw [← twoAffineCohomologyZeroBaseChangeIso_of_flat_base_hom_eq_canonical s φ hφ p g h M
    U V hU hV hI hcover]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The affine sections base-change map is invertible for a flat two-affine base change. -/
lemma sectionsBaseChangeMap_isIso_of_twoAffine_flat_base
    (s : X ⟶ Spec R) (φ : R ⟶ T) (hφ : φ.hom.Flat)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤) :
    IsIso (sectionsBaseChangeMap s φ p g h M) := by
  have : IsIso (canonicalCohomologyZeroBaseChangeMap s φ p g h M) :=
    canonicalCohomologyZeroBaseChangeMap_isIso_of_twoAffine_flat_base s φ hφ p g h M U V
      hU hV hI hcover
  have hsections :
      sectionsBaseChangeMap s φ p g h M =
        (ModuleCat.extendScalars φ.hom).map
            (cohomologyZeroPushforwardSectionsIso s M).inv ≫
          canonicalCohomologyZeroBaseChangeMap s φ p g h M ≫
            (cohomologyZeroPushforwardSectionsIso g ((Scheme.Modules.pullback p).obj M)).hom := by
    simp only [canonicalCohomologyZeroBaseChangeMap, Category.assoc]
    rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    simp
  rw [hsections]
  infer_instance

end GromovWitten.AlgebraicGeometry.Curves
