/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Curves.Prestable
import GromovWitten.AlgebraicGeometry.Curves.CartierDivisors
import GromovWitten.AlgebraicGeometry.Curves.SmoothLocusDimension

/-!
# Marking divisors of pointed prestable families

A closed section `σ : S ⟶ X` of a morphism `f : X ⟶ S` which is smooth of relative dimension
one is an effective Cartier divisor (`section_ker_isEffectiveCartierIdealSheaf`).  The proof is
local on `X`: away from the image of `σ` its kernel ideal is the unit ideal, and around each point
of the image an affine standard-smooth chart of relative dimension one contains the restricted
section, where `affineSchemeSection_ker_isEffectiveCartierIdealSheaf` applies.  The chart is
shrunk to a basic open of the base so that its source is the corresponding basic open of the
chart, which keeps both sides affine and the ring map standard smooth of relative dimension one.

Applied to a pointed prestable family, whose markings factor through the relative smooth locus
and whose smooth locus has relative dimension one by
`smoothLocus_smoothOfRelativeDimension_one`, this gives the effective Cartier divisor of every
marking (`PointedPrestableFamily.markingDivisor`), its canonical identification with the base,
and the sum of all marking divisors (`PointedPrestableFamily.markingsDivisor`).
-/

open CategoryTheory Limits Topology TopologicalSpace
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u v

noncomputable section

variable {X S : Scheme.{u}}

/-! ### Sections of morphisms smooth of relative dimension one -/

/-- Around every point of the base, a closed section of a morphism smooth of relative dimension
one has effective Cartier kernel on an open neighbourhood of the corresponding point of the
source. -/
theorem exists_open_section_ker_comap_isEffectiveCartier (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] (σ : S ⟶ X) [IsClosedImmersion σ] (hσ : σ ≫ f = 𝟙 S)
    (s : S) : ∃ W : X.Opens, σ s ∈ W ∧ IsEffectiveCartierIdealSheaf (σ.ker.comap W.ι) := by
  obtain ⟨U, hU, V, hV, hxV, e, hsm⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) (σ s)
  have hfσ : ∀ t : S, f (σ t) = t := fun t ↦ by
    rw [← Scheme.Hom.comp_apply, hσ]
    rfl
  have hsU : s ∈ U := by
    have h := e hxV
    change f (σ s) ∈ U at h
    rwa [hfσ] at h
  obtain ⟨a, haV, hsa⟩ := hU.exists_basicOpen_le (V := σ ⁻¹ᵁ V) ⟨s, hxV⟩ hsU
  -- Shrink the chart to the basic opens `U' ⊆ S` and `V' = V ∩ f⁻¹ U' ⊆ X`.
  have hU'aff : IsAffineOpen (S.basicOpen a) := hU.basicOpen a
  have hV'aff : IsAffineOpen (X.basicOpen (f.appLE U V e a)) := hV.basicOpen _
  have hV'eq : X.basicOpen (f.appLE U V e a) = V ⊓ f ⁻¹ᵁ S.basicOpen a := by
    simp [Scheme.Hom.appLE, Scheme.basicOpen_res, Scheme.preimage_basicOpen]
  have he' : X.basicOpen (f.appLE U V e a) ≤ f ⁻¹ᵁ S.basicOpen a := by
    rw [hV'eq]
    exact inf_le_right
  have hU'V' : S.basicOpen a = σ ⁻¹ᵁ X.basicOpen (f.appLE U V e a) := by
    apply le_antisymm
    · intro t ht
      change σ t ∈ X.basicOpen (f.appLE U V e a)
      rw [hV'eq]
      refine TopologicalSpace.Opens.mem_inf.mpr ⟨haV ht, ?_⟩
      change f (σ t) ∈ S.basicOpen a
      rwa [hfσ]
    · intro t ht
      change σ t ∈ X.basicOpen (f.appLE U V e a) at ht
      rw [hV'eq] at ht
      have h := (TopologicalSpace.Opens.mem_inf.mp ht).2
      change f (σ t) ∈ S.basicOpen a at h
      rwa [hfσ] at h
  -- The restricted section is an affine closed section of a standard-smooth chart.
  have hUaff : IsAffineOpen (σ ⁻¹ᵁ X.basicOpen (f.appLE U V e a)) := hU'V' ▸ hU'aff
  have : IsAffine (σ ⁻¹ᵁ X.basicOpen (f.appLE U V e a)).toScheme := hUaff
  have : IsAffine (X.basicOpen (f.appLE U V e a)).toScheme := hV'aff
  have he'' : X.basicOpen (f.appLE U V e a) ≤
      f ⁻¹ᵁ (σ ⁻¹ᵁ X.basicOpen (f.appLE U V e a)) := hU'V' ▸ he'
  let f' := f.resLE (σ ⁻¹ᵁ X.basicOpen (f.appLE U V e a)) (X.basicOpen (f.appLE U V e a)) he''
  let σ' := σ ∣_ X.basicOpen (f.appLE U V e a)
  have hσ'cl : IsClosedImmersion σ' :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance _
  have hσ'f' : σ' ≫ f' = 𝟙 _ := by
    rw [← cancel_mono (σ ⁻¹ᵁ X.basicOpen (f.appLE U V e a)).ι]
    dsimp only [σ', f']
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, morphismRestrict_ι_assoc, hσ,
      Category.comp_id, Category.id_comp]
  have hloc : (f.appLE (S.basicOpen a) (X.basicOpen (f.appLE U V e a))
      he').hom.IsStandardSmoothOfRelativeDimension 1 := by
    let _ := hU.isLocalization_basicOpen a
    let _ := hV.isLocalization_basicOpen (f.appLE U V e a)
    rw [hU.appLE_eq_away_map f hV e a]
    exact (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves 1).away _ a _ _ hsm
  have hf' : f'.appTop.hom.IsStandardSmoothOfRelativeDimension 1 := by
    change (f'.app ⊤).hom.IsStandardSmoothOfRelativeDimension 1
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
    exact (Scheme.Hom.appLE_congr f he'
      (by rw [Scheme.Opens.ι_image_top]; exact hU'V') (by simp)
      (fun g ↦ g.hom.IsStandardSmoothOfRelativeDimension 1)).mp hloc
  have hker :=
    EffectiveCartierDivisor.affineSchemeSection_ker_isEffectiveCartierIdealSheaf f' σ' hσ'f' hf'
  refine ⟨X.basicOpen (f.appLE U V e a), ?_, ?_⟩
  · rw [hV'eq]
    refine TopologicalSpace.Opens.mem_inf.mpr ⟨hxV, ?_⟩
    change f (σ s) ∈ S.basicOpen a
    rwa [hfσ]
  · rwa [ker_morphismRestrict σ] at hker

/-- A closed section of a morphism smooth of relative dimension one is an effective Cartier
divisor: its kernel ideal sheaf is locally generated by a single non-zero-divisor. -/
theorem section_ker_isEffectiveCartierIdealSheaf (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (σ : S ⟶ X) [IsClosedImmersion σ] (hσ : σ ≫ f = 𝟙 S) :
    IsEffectiveCartierIdealSheaf σ.ker := by
  choose W hW hcart using exists_open_section_ker_comap_isEffectiveCartier f σ hσ
  let U : Option S → X.Opens := fun o ↦ o.elim (complementOfClosedImmersion σ) W
  refine isEffectiveCartierIdealSheaf_of_openCover σ.ker U ?_ ?_
  · rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hx : x ∈ Set.range σ
    · obtain ⟨s, rfl⟩ := hx
      exact ⟨some s, hW s⟩
    · exact ⟨none, hx⟩
  · rintro (_ | s)
    · change IsEffectiveCartierIdealSheaf (σ.ker.comap (complementOfClosedImmersion σ).ι)
      rw [ker_comap_complementOfClosedImmersion_eq_top]
      exact top_isEffectiveCartierIdealSheaf
    · exact hcart s

/-- The effective Cartier divisor of a closed section of a morphism smooth of relative dimension
one. -/
def EffectiveCartierDivisor.ofSection (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (σ : S ⟶ X) [IsClosedImmersion σ] (hσ : σ ≫ f = 𝟙 S) : EffectiveCartierDivisor X where
  idealSheaf := σ.ker
  isEffectiveCartier := section_ker_isEffectiveCartierIdealSheaf f σ hσ

/-! ### Finite sums of effective Cartier divisors -/

namespace EffectiveCartierDivisor

/-- The ideal sheaf of a finite sum of effective Cartier divisors is the product of their ideal
sheaves. -/
theorem sum_finset_idealSheaf {ι : Type*} (s : Finset ι) (D : ι → EffectiveCartierDivisor X) :
    (∑ i ∈ s, D i).idealSheaf = ∏ i ∈ s, (D i).idealSheaf := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ← ih]
    exact sum_idealSheaf _ _

/-- The support of a finite sum of effective Cartier divisors is the union of their supports. -/
theorem sum_finset_support {ι : Type*} (s : Finset ι) (D : ι → EffectiveCartierDivisor X) :
    ((∑ i ∈ s, D i).support : Set X) = ⋃ i ∈ s, ((D i).support : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    change ((⊤ : X.IdealSheafData).support : Set X) = _
    rw [Scheme.IdealSheafData.support_top]
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    change ((sum (D a) (∑ i ∈ s, D i)).support : Set X) = _
    rw [sum_support, Closeds.coe_sup, ih, Finset.set_biUnion_insert]

end EffectiveCartierDivisor

/-! ### Marking divisors -/

namespace PointedPrestableFamily

variable {I : Type v} (C : PointedPrestableFamily S I)

/-- The relative smooth locus of a pointed prestable family is smooth of relative dimension one
over the base. -/
instance smoothPartToBase_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 C.smoothPartToBase :=
  smoothLocus_smoothOfRelativeDimension_one C.toBase
    (PrestableFamily.geometricPureRelativeDimension C.toBase)

/-- The kernel of a marking, viewed inside the relative smooth locus, is effective Cartier. -/
theorem markingToSmoothPart_ker_isEffectiveCartier (i : I) :
    IsEffectiveCartierIdealSheaf (C.markingToSmoothPart i).ker :=
  section_ker_isEffectiveCartierIdealSheaf C.smoothPartToBase (C.markingToSmoothPart i)
    (C.markingToSmoothPart_toBase i)

/-- The canonical ideal sheaf of every marking is effective Cartier: it is the unit ideal away
from the marking, and effective Cartier on the relative smooth locus. -/
theorem markingIdealSheaf_isEffectiveCartier (i : I) :
    IsEffectiveCartierIdealSheaf (C.markingIdealSheaf i) := by
  let U : Bool → C.total.Opens := fun b ↦
    Bool.rec (complementOfClosedImmersion (C.marking i)) C.toBase.smoothLocus b
  refine isEffectiveCartierIdealSheaf_of_openCover (C.markingIdealSheaf i) U ?_ ?_
  · rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hx : x ∈ Set.range (C.marking i)
    · obtain ⟨s, rfl⟩ := hx
      exact ⟨true, C.marking_mem_smoothLocus i s⟩
    · exact ⟨false, hx⟩
  · intro b
    cases b
    · change IsEffectiveCartierIdealSheaf
        ((C.marking i).ker.comap (complementOfClosedImmersion (C.marking i)).ι)
      rw [ker_comap_complementOfClosedImmersion_eq_top]
      exact top_isEffectiveCartierIdealSheaf
    · change IsEffectiveCartierIdealSheaf ((C.marking i).ker.comap C.toBase.smoothLocus.ι)
      rw [← ker_factorThrough_open (C.marking i) C.toBase.smoothLocus (C.markingToSmoothPart i)
        (C.markingToSmoothPart_toTotal i)]
      exact C.markingToSmoothPart_ker_isEffectiveCartier i

/-- The effective Cartier divisor cut out by a marking. -/
def markingDivisor (i : I) : EffectiveCartierDivisor C.total where
  idealSheaf := C.markingIdealSheaf i
  isEffectiveCartier := C.markingIdealSheaf_isEffectiveCartier i

@[simp]
theorem markingDivisor_idealSheaf (i : I) :
    (C.markingDivisor i).idealSheaf = C.markingIdealSheaf i := rfl

/-- The support of a marking divisor is the image of the marking. -/
theorem markingDivisor_support (i : I) :
    ((C.markingDivisor i).support : Set C.total) = Set.range (C.marking i) :=
  C.markingIdealSheaf_support i

/-- Distinct marking divisors have disjoint supports. -/
theorem markingDivisor_support_disjoint {i j : I} (hij : i ≠ j) :
    Disjoint ((C.markingDivisor i).support : Set C.total)
      ((C.markingDivisor j).support : Set C.total) :=
  C.markingIdealSheaf_support_disjoint hij

/-- The subscheme of a marking divisor is canonically the base. -/
def markingDivisorSubschemeIso (i : I) : S ≅ (C.markingDivisor i).subscheme :=
  EffectiveCartierDivisor.closedImmersionSubschemeIsoOfKerEq (C.marking i)
    (C.markingDivisor i).idealSheaf rfl

@[reassoc (attr := simp)]
theorem markingDivisorSubschemeIso_hom_ι (i : I) :
    (C.markingDivisorSubschemeIso i).hom ≫ (C.markingDivisor i).ι = C.marking i :=
  EffectiveCartierDivisor.closedImmersionSubschemeIsoOfKerEq_hom_subschemeι
    (C.marking i) (C.markingDivisor i).idealSheaf rfl

section Finite

variable [Fintype I]

/-- The sum of all marking divisors of a pointed prestable family with finitely many markings. -/
def markingsDivisor : EffectiveCartierDivisor C.total :=
  ∑ i, C.markingDivisor i

/-- The ideal sheaf of the sum of the marking divisors is the product of the marking ideals. -/
theorem markingsDivisor_idealSheaf :
    C.markingsDivisor.idealSheaf = ∏ i, C.markingIdealSheaf i :=
  EffectiveCartierDivisor.sum_finset_idealSheaf _ _

/-- The support of the sum of the marking divisors is the union of the markings. -/
theorem markingsDivisor_support :
    (C.markingsDivisor.support : Set C.total) = ⋃ i, Set.range (C.marking i) := by
  rw [markingsDivisor, EffectiveCartierDivisor.sum_finset_support]
  simp [markingDivisor_support]

end Finite

end PointedPrestableFamily

end

end GromovWitten.AlgebraicGeometry.Curves
