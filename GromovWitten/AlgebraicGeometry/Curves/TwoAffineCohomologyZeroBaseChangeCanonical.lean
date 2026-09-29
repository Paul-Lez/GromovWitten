/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.CohomologyZeroBaseChangeMap
import GromovWitten.AlgebraicGeometry.Curves.CohomologyZeroCechProjection
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineCohomologyZeroBaseChangeProjection

/-!
# Canonical degree-zero base change for a two-affine cover

The flat two-affine Cech comparison agrees with the canonical global-sections base-change map.
Consequently the canonical degree-zero cohomology map, and the corresponding affine sections
map, are isomorphisms under the stated two-affine hypotheses.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The flat two-affine Cech comparison is the canonical degree-zero base-change map. -/
lemma twoAffineCohomologyZeroBaseChangeIso_hom_eq_canonical [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    [Module.Flat R (cohomologyModuleCat R s M 1)] :
    (twoAffineCohomologyZeroBaseChangeIso_of_flat s φ p g h M U V hU hV hI hcover hflat).hom =
      canonicalCohomologyZeroBaseChangeMap s φ p g h M := by
  have hc : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤ := by
    change p ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  apply (cancel_mono ((cohomologyZeroIsoBaseCechKernel g ((Scheme.Modules.pullback p).obj M)
    (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hc).hom ≫
    kernel.ι (baseCechPairMap g ((Scheme.Modules.pullback p).obj M)
      (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)))).1
  rw [twoAffineCohomologyZeroBaseChangeIso_projection]
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

/-- The canonical degree-zero cohomology base-change map is invertible for a two-affine cover. -/
lemma canonicalCohomologyZeroBaseChangeMap_isIso_of_twoAffine [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    [Module.Flat R (cohomologyModuleCat R s M 1)] :
    IsIso (canonicalCohomologyZeroBaseChangeMap s φ p g h M) := by
  rw [← twoAffineCohomologyZeroBaseChangeIso_hom_eq_canonical s φ p g h M U V hU hV hI
    hcover hflat]
  infer_instance

/-- The affine sections base-change map is invertible for a two-affine cover
under relative flatness. -/
lemma sectionsBaseChangeMap_isIso_of_twoAffine [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    [Module.Flat R (cohomologyModuleCat R s M 1)] :
    IsIso (sectionsBaseChangeMap s φ p g h M) := by
  have : IsIso (canonicalCohomologyZeroBaseChangeMap s φ p g h M) :=
    canonicalCohomologyZeroBaseChangeMap_isIso_of_twoAffine s φ p g h M U V hU hV hI
      hcover hflat
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
