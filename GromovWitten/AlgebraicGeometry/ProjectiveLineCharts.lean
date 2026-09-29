/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import GromovWitten.AlgebraicGeometry.ProjectiveLine

/-!
# The standard chart cover of the projective line

This file contains the chart cover, overlap, and affine-open geometry of the projective line.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.ProjectiveLine

noncomputable section

variable (k : Type u) [CommRing k]

/-! The chart cover and its overlap geometry, isolated from proper-curve topology. -/

/-- The two standard charts of `ℙ¹_k`, indexed by `Bool`. -/
abbrev chartMap : Bool → (chart k ⟶ scheme k)
  | false => chartZero k
  | true => chartOne k

/-- The open cover of `ℙ¹_k` by its two standard charts. -/
def chartCover : (scheme k).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun _ => chart k) (chartMap k)
    (fun x => by
      rcases mem_range_chart k x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨false, y, hy⟩
      · exact ⟨true, y, hy⟩)
    (fun b => by cases b <;> infer_instance)

/-- Both charts are morphisms of `k`-schemes. -/
lemma chartMap_comp_structureMap (b : Bool) :
    chartMap k b ≫ structureMap k =
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) := by
  cases b
  · exact chartZero_comp_structureMap k
  · exact chartOne_comp_structureMap k

/-- A point of the first chart whose image lies in the second chart lies in the overlap. -/
lemma mem_range_overlapToChartZero_of_mem_range_chartOne {y : chart k}
    (hy : (chartZero k).base y ∈ Set.range (chartOne k).base) :
    y ∈ Set.range (overlapToChartZero k).base := by
  obtain ⟨y', hy'⟩ := hy
  obtain ⟨l, fi, fj, z, _, hzj⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := diagram k)).mp hy'
  cases fj with
  | id X => cases fi
  | init b =>
    cases fi with
    | init a =>
      rw [← hzj, map_init_zero]
      exact ⟨z, rfl⟩

/-- A point of the second chart whose image lies in the first chart lies in the overlap. -/
lemma mem_range_overlapToChartOne_of_mem_range_chartZero {y : chart k}
    (hy : (chartOne k).base y ∈ Set.range (chartZero k).base) :
    y ∈ Set.range (overlapToChartOne k).base := by
  obtain ⟨y', hy'⟩ := hy
  obtain ⟨l, fi, fj, z, _, hzj⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := diagram k)).mp hy'
  cases fj with
  | id X => cases fi
  | init b =>
    cases fi with
    | init a =>
      rw [← hzj, map_init_one]
      exact ⟨z, rfl⟩

/-- The preimage of the second chart in the first one is the overlap. -/
lemma preimage_opensRange_chartOne :
    (chartZero k) ⁻¹ᵁ (chartOne k).opensRange = (overlapToChartZero k).opensRange := by
  ext y
  constructor
  · exact fun h => mem_range_overlapToChartZero_of_mem_range_chartOne k h
  · rintro ⟨z, rfl⟩
    refine ⟨(overlapToChartOne k).base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, overlapToChartOne_comp,
      overlapToChartZero_comp]

/-- The preimage of the first chart in the second one is the overlap. -/
lemma preimage_opensRange_chartZero :
    (chartOne k) ⁻¹ᵁ (chartZero k).opensRange = (overlapToChartOne k).opensRange := by
  ext y
  constructor
  · exact fun h => mem_range_overlapToChartOne_of_mem_range_chartZero k h
  · rintro ⟨z, rfl⟩
    refine ⟨(overlapToChartZero k).base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, overlapToChartZero_comp,
      overlapToChartOne_comp]

/-- The fibre product of the two charts over `ℙ¹_k` is the overlap. -/
lemma isPullback_chartZero_chartOne :
    IsPullback (overlapToChartZero k) (overlapToChartOne k) (chartZero k) (chartOne k) :=
  AlgebraicGeometry.IsOpenImmersion.isPullback (overlapToChartZero k) (overlapToChartOne k)
    (chartZero k) (chartOne k)
    (by rw [overlapToChartOne_comp, overlapToChartZero_comp])
    (preimage_opensRange_chartZero k)

/-- The mirror image of `isPullback_chartZero_chartOne`. -/
lemma isPullback_chartOne_chartZero :
    IsPullback (overlapToChartOne k) (overlapToChartZero k) (chartOne k) (chartZero k) :=
  AlgebraicGeometry.IsOpenImmersion.isPullback (overlapToChartOne k) (overlapToChartZero k)
    (chartOne k) (chartZero k)
    (by rw [overlapToChartZero_comp, overlapToChartOne_comp])
    (preimage_opensRange_chartOne k)

/-- The identity map on the chart ring induces the identity scheme map. -/
lemma spec_map_ofHom_id : Spec.map (CommRingCat.ofHom (RingHom.id (Polynomial k))) =
    𝟙 (chart k) := by
  rw [CommRingCat.ofHom_id, Spec.map_id]

/-- The fibre product of a chart with itself over `ℙ¹_k` is that chart. -/
lemma isPullback_chart_self (b : Bool) :
    IsPullback (Spec.map (CommRingCat.ofHom (RingHom.id (Polynomial k))))
      (Spec.map (CommRingCat.ofHom (RingHom.id (Polynomial k)))) (chartMap k b)
      (chartMap k b) := by
  rw [spec_map_ofHom_id]
  cases b
  · exact IsKernelPair.id_of_mono (chartZero k)
  · exact IsKernelPair.id_of_mono (chartOne k)

/-- Each standard chart has affine open image. -/
lemma isAffineOpen_opensRange_chartZero :
    IsAffineOpen (chartZero k).opensRange :=
  isAffineOpen_opensRange _

lemma isAffineOpen_opensRange_chartOne :
    IsAffineOpen (chartOne k).opensRange :=
  isAffineOpen_opensRange _

/-- The two standard chart images cover the projective line. -/
lemma opensRange_chartZero_sup_chartOne :
    (chartZero k).opensRange ⊔ (chartOne k).opensRange = ⊤ := by
  ext x
  change x ∈ (chartZero k).opensRange ⊔ (chartOne k).opensRange ↔
    x ∈ (⊤ : (scheme k).Opens)
  simp only [TopologicalSpace.Opens.mem_sup, TopologicalSpace.Opens.mem_top, iff_true,
    Scheme.Hom.mem_opensRange]
  exact mem_range_chart k x

/-- The intersection of the two standard chart images is the overlap image. -/
lemma opensRange_chartZero_inf_chartOne :
    (chartZero k).opensRange ⊓ (chartOne k).opensRange = (overlapι k).opensRange := by
  calc
    (chartZero k).opensRange ⊓ (chartOne k).opensRange =
        (chartZero k) ''ᵁ (chartZero k) ⁻¹ᵁ (chartOne k).opensRange := by
      symm
      exact (chartZero k).image_preimage_eq_opensRange_inf _
    _ = (chartZero k) ''ᵁ (overlapToChartZero k).opensRange := by
      rw [preimage_opensRange_chartOne k]
    _ = (overlapToChartZero k ≫ chartZero k).opensRange := by
      exact (Scheme.Hom.opensRange_comp (overlapToChartZero k) (chartZero k)).symm
    _ = (overlapι k).opensRange := by
      simp only [overlapToChartZero_comp]

end
end GromovWitten.AlgebraicGeometry.ProjectiveLine
