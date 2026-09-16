/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNodeCentralChart
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.Data.Countable.Small

/-!
# Resolution of the standard node of arbitrary thickness

Blowing up the local node `xy = π^(k+2)` at its closed origin gives a scheme covered by two
regular side charts and a central chart which is again a node, of thickness `k`.  Replacing the
central chart by a resolution of that lower-thickness node, and gluing the result back to the
side charts, resolves the node of thickness `k + 2`.  Since the nodes of thickness `0` and `1`
are already regular, induction on the thickness produces, for every thickness `n`, a regular
scheme with a proper morphism to the node which is an isomorphism away from the origin
(`NodeResolution`, `nodeResolution`).

The gluing step uses Mathlib's relative gluing along a locally directed open cover of the
blowup: the cover consists of the central chart, the union of the two side charts, and their
intersection, and the schemes glued over them are the lower-thickness resolution, the side
charts themselves, and the open part of the lower-thickness resolution over which it is an
isomorphism.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

universe u

noncomputable section

/-! ### Restriction of isomorphisms and regularity along open immersions -/

/-- If a morphism is an isomorphism over an open `U`, it is an isomorphism over every open
contained in `U`. -/
theorem isIso_morphismRestrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens}
    (hVU : V ≤ U) (hU : IsIso (f ∣_ U)) : IsIso (f ∣_ V) := by
  have h1 : MorphismProperty.isomorphisms Scheme (f ∣_ U) := hU
  have h2 : MorphismProperty.isomorphisms Scheme ((f ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) :=
    IsZariskiLocalAtTarget.restrict h1 _
  have h3 : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVU
  have h4 := (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mp h2
  rw [h3] at h4
  exact h4

/-- The restriction of an isomorphism to any open is an isomorphism. -/
theorem isIso_morphismRestrict_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (U : Y.Opens) : IsIso (f ∣_ U) := by
  have h : MorphismProperty.isomorphisms Scheme f := inferInstance
  exact IsZariskiLocalAtTarget.restrict h U

/-- The source of an open immersion into a regular scheme is regular. -/
theorem schemeIsRegular_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (hY : SchemeIsRegular Y) : SchemeIsRegular X := by
  intro x
  let _ : IsRegularLocalRing (Y.presheaf.stalk (f x)) := hY (f x)
  let _ : IsIso (f.stalkMap x) := inferInstance
  exact IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

/-- The stalks of a scheme at the points of the image of an open immersion from a regular
scheme are regular. -/
theorem isRegularLocalRing_stalk_of_mem_opensRange {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (hX : SchemeIsRegular X) {y : Y} (hy : y ∈ f.opensRange) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  obtain ⟨x, rfl⟩ := hy
  let _ : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  let _ : IsIso (f.stalkMap x) := inferInstance
  exact IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm

/-! ### Properties of relative gluings -/

/-- A property of morphisms which respects isomorphisms holds for the structure map of a
relative gluing over a cover piece if and only if it holds for the glued piece over it. -/
theorem gluingData_property_restrict_iff {S : Scheme.{u}} {𝒰 : S.OpenCover}
    [Category 𝒰.I₀] [𝒰.LocallyDirected] (d : 𝒰.RelativeGluingData) [Small.{u} 𝒰.I₀]
    [Quiver.IsThin 𝒰.I₀] (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (i : 𝒰.I₀) :
    P (d.toBase ∣_ (𝒰.f i).opensRange) ↔ P (d.natTrans.app i) := by
  rw [P.arrow_mk_iso_iff (morphismRestrictOpensRange d.toBase (𝒰.f i))]
  exact (P.arrow_mk_iso_iff (Arrow.isoMk (d.isPullback_natTrans_ι_toBase i).flip.isoPullback
    (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id]
      exact (d.isPullback_natTrans_ι_toBase i).flip.isoPullback_hom_snd))).symm

/-! ### The origin complement and the side charts -/

variable (R : Type u) [CommRing R] (π : R)

/-- The open complement of the closed origin of the local node. -/
abbrev originComplement (n : ℕ) : (Spec (.of (Ring R π n))).Opens :=
  ReesBlowup.baseComplement (totalSpaceOriginIdeal R π n)

/-- The complement of the origin is the union of the three coordinate principal opens. -/
theorem originComplement_eq (n : ℕ) :
    originComplement R π n =
      (PrimeSpectrum.basicOpen (x R π n) : (Spec (.of (Ring R π n))).Opens) ⊔
        (PrimeSpectrum.basicOpen (y R π n) : (Spec (.of (Ring R π n))).Opens) ⊔
        (PrimeSpectrum.basicOpen (algebraMap R (Ring R π n) π) :
          (Spec (.of (Ring R π n))).Opens) := by
  apply le_antisymm
  · refine iSup_le fun r ↦ ?_
    intro p hp
    by_contra hcontra
    have hx : x R π n ∈ p.asIdeal := by
      by_contra hxp
      exact hcontra (Opens.mem_sup.mpr (Or.inl (Opens.mem_sup.mpr (Or.inl hxp))))
    have hy : y R π n ∈ p.asIdeal := by
      by_contra hyp
      exact hcontra (Opens.mem_sup.mpr (Or.inl (Opens.mem_sup.mpr (Or.inr hyp))))
    have hπ : algebraMap R (Ring R π n) π ∈ p.asIdeal := by
      by_contra hπp
      exact hcontra (Opens.mem_sup.mpr (Or.inr hπp))
    have hI : totalSpaceOriginIdeal R π n ≤ p.asIdeal := by
      rw [totalSpaceOriginIdeal, Ideal.span_le]
      rintro z (rfl | rfl | rfl)
      · exact hx
      · exact hy
      · exact hπ
    exact hp (hI r.2)
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact le_iSup (fun r : totalSpaceOriginIdeal R π n ↦
        (PrimeSpectrum.basicOpen r.1 : (Spec (.of (Ring R π n))).Opens)) (originCenterX R π n)
    · exact le_iSup (fun r : totalSpaceOriginIdeal R π n ↦
        (PrimeSpectrum.basicOpen r.1 : (Spec (.of (Ring R π n))).Opens)) (originCenterY R π n)
    · exact le_iSup (fun r : totalSpaceOriginIdeal R π n ↦
        (PrimeSpectrum.basicOpen r.1 : (Spec (.of (Ring R π n))).Opens))
        (originCenterParameter R π n)

/-- On a node, the parameter is invertible only where `x` is. -/
theorem basicOpen_parameter_le_basicOpen_x (n : ℕ) :
    (PrimeSpectrum.basicOpen (algebraMap R (Ring R π n) π) : (Spec (.of (Ring R π n))).Opens) ≤
      PrimeSpectrum.basicOpen (x R π n) := by
  intro p hp
  rw [PrimeSpectrum.mem_basicOpen] at hp ⊢
  intro hx
  apply hp
  have hmem : x R π n * y R π n ∈ p.asIdeal := p.asIdeal.mul_mem_right _ hx
  rw [x_mul_y, map_pow] at hmem
  exact p.isPrime.mem_of_pow_mem n hmem

/-- The union of the two regular side charts of the origin blowup. -/
abbrev sideCharts (n : ℕ) : (originBlowup R π n).Opens :=
  (originBlowupXChartMap R π n).opensRange ⊔ (originBlowupYChartMap R π n).opensRange

/-- Away from the origin, the blowup lies in the two side charts. -/
theorem projection_preimage_originComplement_le_sideCharts (n : ℕ) :
    originBlowupProjection R π n ⁻¹ᵁ originComplement R π n ≤ sideCharts R π n := by
  refine ((originBlowupProjection R π n).preimage_mono (originComplement_eq R π n).le).trans ?_
  have hx : originBlowupProjection R π n ⁻¹ᵁ PrimeSpectrum.basicOpen (x R π n) ≤
      (originBlowupXChartMap R π n).opensRange :=
    ReesBlowup.projection_preimage_basicOpen_le_chartMap_opensRange
      (totalSpaceOriginIdeal R π n) (originCenterX R π n)
  have hy : originBlowupProjection R π n ⁻¹ᵁ PrimeSpectrum.basicOpen (y R π n) ≤
      (originBlowupYChartMap R π n).opensRange :=
    ReesBlowup.projection_preimage_basicOpen_le_chartMap_opensRange
      (totalSpaceOriginIdeal R π n) (originCenterY R π n)
  change originBlowupProjection R π n ⁻¹ᵁ PrimeSpectrum.basicOpen (x R π n) ⊔
      originBlowupProjection R π n ⁻¹ᵁ PrimeSpectrum.basicOpen (y R π n) ⊔
      originBlowupProjection R π n ⁻¹ᵁ PrimeSpectrum.basicOpen (algebraMap R (Ring R π n) π) ≤
      sideCharts R π n
  refine sup_le (sup_le (hx.trans le_sup_left) (hy.trans le_sup_right)) ?_
  refine le_trans ?_ (hx.trans le_sup_left)
  exact (originBlowupProjection R π n).preimage_mono (basicOpen_parameter_le_basicOpen_x R π n)

/-- The parameter chart and the two side charts cover the origin blowup. -/
theorem parameterChart_opensRange_sup_sideCharts_eq_top (n : ℕ) :
    (originBlowupParameterChartMap R π n).opensRange ⊔ sideCharts R π n = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top (ReesBlowup.grade (totalSpaceOriginIdeal R π n))
    (ReesBlowup.generatorOfFamily (totalSpaceOriginIdeal R π n) (originCenterFamily R π n)
      (totalSpaceOriginIdeal_eq_span_range_originCenterFamily R π n))
    (ReesBlowup.irrelevant_le_span_generatorOfFamily (totalSpaceOriginIdeal R π n) _ _)
  rw [eq_top_iff, ← h]
  refine iSup_le fun i ↦ ?_
  fin_cases i
  · simp only
    rw [originCenterFamily_generator_eq R π n _ (originCenterX R π n)
      (by simp [originCenterFamily, originCenterX]), ← ReesBlowup.chartMap_opensRange]
    exact le_sup_of_le_right le_sup_left
  · simp only
    rw [originCenterFamily_generator_eq R π n _ (originCenterY R π n)
      (by simp [originCenterFamily, originCenterY]), ← ReesBlowup.chartMap_opensRange]
    exact le_sup_of_le_right le_sup_right
  · simp only
    rw [originCenterFamily_generator_eq R π n _ (originCenterParameter R π n)
      (by simp [originCenterFamily, originCenterParameter]), ← ReesBlowup.chartMap_opensRange]
    exact le_sup_left

/-! ### The central chart meets the side charts away from the origin -/

/-- Under the central-chart identification, the ratio `x/π` becomes the coordinate `x`. -/
theorem parameterReesChartToCentral_ratioElement_x [IsDomain R] (hπ : Irreducible π) (k : ℕ) :
    parameterReesChartToCentralAlgHom R π hπ k
      (ReesBlowup.ratioElement (totalSpaceOriginIdeal R π (k + 2))
        (originCenterParameter R π (k + 2)) (originCenterX R π (k + 2))) = x R π k := by
  change parameterReesChartToCentralRingHom R π hπ k _ = _
  rw [parameterReesChartToCentralRingHom,
    ReesBlowup.chartLift_ratioElement _ _ _ _ _ _ (x R π k)]
  change x R π k * centralChartMap R π k (algebraMap R (Ring R π (k + 2)) π) =
    centralChartMap R π k (x R π (k + 2))
  rw [centralChartMap_x, (centralChartMap R π k).commutes, mul_comm]

/-- Under the central-chart identification, the ratio `y/π` becomes the coordinate `y`. -/
theorem parameterReesChartToCentral_ratioElement_y [IsDomain R] (hπ : Irreducible π) (k : ℕ) :
    parameterReesChartToCentralAlgHom R π hπ k
      (ReesBlowup.ratioElement (totalSpaceOriginIdeal R π (k + 2))
        (originCenterParameter R π (k + 2)) (originCenterY R π (k + 2))) = y R π k := by
  change parameterReesChartToCentralRingHom R π hπ k _ = _
  rw [parameterReesChartToCentralRingHom,
    ReesBlowup.chartLift_ratioElement _ _ _ _ _ _ (y R π k)]
  change y R π k * centralChartMap R π k (algebraMap R (Ring R π (k + 2)) π) =
    centralChartMap R π k (y R π (k + 2))
  rw [centralChartMap_y, (centralChartMap R π k).commutes, mul_comm]

/-- The inverse of the central-chart identification is the spectrum of the chart map. -/
theorem parameterReesChartIso_inv [IsDomain R] (hπ : Irreducible π) (k : ℕ) :
    (parameterReesChartIso R π hπ k).inv =
      Spec.map (CommRingCat.ofHom (parameterReesChartToCentralAlgHom R π hπ k).toRingHom) := by
  simp only [parameterReesChartIso, Functor.mapIso_inv, Iso.symm_inv, Iso.op_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op]
  rfl

/-- Pulling a principal open of the parameter chart back along the central-chart
identification gives the principal open of the image element. -/
theorem parameterReesChartIso_inv_preimage_basicOpen [IsDomain R] (hπ : Irreducible π) (k : ℕ)
    (r : ParameterChartRing R π k) :
    (parameterReesChartIso R π hπ k).inv ⁻¹ᵁ
        (PrimeSpectrum.basicOpen r : (Spec (.of (ParameterChartRing R π k))).Opens) =
      PrimeSpectrum.basicOpen (parameterReesChartToCentralAlgHom R π hπ k r) := by
  rw [parameterReesChartIso_inv, SpecMap_preimage_basicOpen]
  rfl

/-- The part of the parameter chart lying in the side charts. -/
abbrev overlap (n : ℕ) : (originBlowupParameterChart R π n).Opens :=
  originBlowupParameterChartMap R π n ⁻¹ᵁ sideCharts R π n

/-- The overlap of the central chart with the side charts avoids the origin of the
lower-thickness node. -/
theorem parameterReesChartIso_inv_preimage_overlap_le [IsDomain R] (hπ : Irreducible π)
    (k : ℕ) :
    (parameterReesChartIso R π hπ k).inv ⁻¹ᵁ overlap R π (k + 2) ≤ originComplement R π k := by
  have hx : originBlowupParameterChartMap R π (k + 2) ⁻¹ᵁ
      (originBlowupXChartMap R π (k + 2)).opensRange =
      PrimeSpectrum.basicOpen (ReesBlowup.ratioElement (totalSpaceOriginIdeal R π (k + 2))
        (originCenterParameter R π (k + 2)) (originCenterX R π (k + 2))) :=
    ReesBlowup.chartMap_preimage_chartMap_opensRange _ _ _
  have hy : originBlowupParameterChartMap R π (k + 2) ⁻¹ᵁ
      (originBlowupYChartMap R π (k + 2)).opensRange =
      PrimeSpectrum.basicOpen (ReesBlowup.ratioElement (totalSpaceOriginIdeal R π (k + 2))
        (originCenterParameter R π (k + 2)) (originCenterY R π (k + 2))) :=
    ReesBlowup.chartMap_preimage_chartMap_opensRange _ _ _
  change (parameterReesChartIso R π hπ k).inv ⁻¹ᵁ
      (originBlowupParameterChartMap R π (k + 2) ⁻¹ᵁ
        (originBlowupXChartMap R π (k + 2)).opensRange) ⊔
      (parameterReesChartIso R π hπ k).inv ⁻¹ᵁ
      (originBlowupParameterChartMap R π (k + 2) ⁻¹ᵁ
        (originBlowupYChartMap R π (k + 2)).opensRange) ≤ originComplement R π k
  rw [hx, hy, parameterReesChartIso_inv_preimage_basicOpen,
    parameterReesChartIso_inv_preimage_basicOpen, parameterReesChartToCentral_ratioElement_x,
    parameterReesChartToCentral_ratioElement_y]
  exact sup_le
    (le_iSup (fun r : totalSpaceOriginIdeal R π k ↦
      (PrimeSpectrum.basicOpen r.1 : (Spec (.of (Ring R π k))).Opens)) (originCenterX R π k))
    (le_iSup (fun r : totalSpaceOriginIdeal R π k ↦
      (PrimeSpectrum.basicOpen r.1 : (Spec (.of (Ring R π k))).Opens)) (originCenterY R π k))

/-- The union of the two side charts is a regular scheme. -/
theorem sideCharts_isRegular [IsDomain R] [IsDiscreteValuationRing R] (hπ : Irreducible π)
    (k : ℕ) : SchemeIsRegular (sideCharts R π (k + 2)).toScheme := by
  intro z
  have hz : (sideCharts R π (k + 2)).ι z ∈ sideCharts R π (k + 2) := z.2
  have hreg : IsRegularLocalRing
      ((originBlowup R π (k + 2)).presheaf.stalk ((sideCharts R π (k + 2)).ι z)) := by
    rcases Opens.mem_sup.mp hz with h | h
    · exact isRegularLocalRing_stalk_of_mem_opensRange _ (xBlowupChart_isRegular R π hπ k) h
    · exact isRegularLocalRing_stalk_of_mem_opensRange _ (yBlowupChart_isRegular R π hπ k) h
  let _ : IsIso ((sideCharts R π (k + 2)).ι.stalkMap z) := inferInstance
  exact IsRegularLocalRing.of_ringEquiv
    (asIso ((sideCharts R π (k + 2)).ι.stalkMap z)).commRingCatIsoToRingEquiv

/-! ### Resolutions -/

/-- A resolution of the node of thickness `n`: a regular scheme with a proper morphism to the
node which is an isomorphism away from the origin. -/
structure NodeResolution (n : ℕ) where
  /-- The resolving scheme. -/
  total : Scheme.{u}
  /-- The resolution morphism. -/
  toNode : total ⟶ Spec (.of (Ring R π n))
  isProper : IsProper toNode
  isRegular : SchemeIsRegular total
  isIso_restrict : IsIso (toNode ∣_ originComplement R π n)

/-- A node whose coordinate ring is regular is its own resolution. -/
def NodeResolution.ofRegular (n : ℕ) (h : IsRegularRing (Ring R π n)) :
    NodeResolution R π n where
  total := Spec (.of (Ring R π n))
  toNode := 𝟙 _
  isProper := inferInstance
  isRegular := by
    let _ : IsRegularRing (Ring R π n) := h
    exact SchemeIsRegular.spec (Ring R π n)
  isIso_restrict := isIso_morphismRestrict_of_isIso _ _

/-! ### The three-piece locally directed cover of the blowup -/

/-- Indices for the gluing cover: the overlap, the central chart, and the side charts. -/
inductive ResolutionIndex
  | overlap
  | central
  | side
  deriving DecidableEq

instance : Preorder ResolutionIndex where
  le a b := a = b ∨ a = ResolutionIndex.overlap
  le_refl _ := Or.inl rfl
  le_trans _ _ _ hab hbc := by
    rcases hab with rfl | rfl
    · exact hbc
    · exact Or.inr rfl

instance : DecidableRel (α := ResolutionIndex) (· ≤ ·) := fun a b ↦
  inferInstanceAs (Decidable (a = b ∨ a = ResolutionIndex.overlap))

/-- The overlap index lies below every index. -/
theorem ResolutionIndex.overlap_le (i : ResolutionIndex) : ResolutionIndex.overlap ≤ i :=
  Or.inr rfl

/-- The pieces of the gluing cover of the origin blowup. -/
abbrev coverObj (n : ℕ) : ResolutionIndex → Scheme.{u}
  | .overlap => (overlap R π n).toScheme
  | .central => originBlowupParameterChart R π n
  | .side => (sideCharts R π n).toScheme

/-- The open immersions of the gluing cover pieces into the origin blowup. -/
def coverMap (n : ℕ) : ∀ i, coverObj R π n i ⟶ originBlowup R π n
  | .overlap => (overlap R π n).ι ≫ originBlowupParameterChartMap R π n
  | .central => originBlowupParameterChartMap R π n
  | .side => (sideCharts R π n).ι

instance coverMap_isOpenImmersion (n : ℕ) (i : ResolutionIndex) :
    IsOpenImmersion (coverMap R π n i) := by
  cases i
  · exact IsOpenImmersion.comp (overlap R π n).ι (originBlowupParameterChartMap R π n)
  · exact inferInstanceAs (IsOpenImmersion (originBlowupParameterChartMap R π n))
  · exact inferInstanceAs (IsOpenImmersion (sideCharts R π n).ι)

/-- A point lies in the overlap piece if and only if it lies in the parameter chart and in the
side charts. -/
theorem mem_range_coverMap_overlap_iff (n : ℕ) (z : originBlowup R π n) :
    z ∈ Set.range (coverMap R π n .overlap) ↔
      z ∈ Set.range (originBlowupParameterChartMap R π n) ∧ z ∈ sideCharts R π n := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨⟨(overlap R π n).ι w, (Scheme.Hom.comp_apply _ _ _).symm⟩, ?_⟩
    change (originBlowupParameterChartMap R π n) ((overlap R π n).ι w) ∈ sideCharts R π n
    exact w.2
  · rintro ⟨⟨w, rfl⟩, hS⟩
    exact ⟨⟨w, hS⟩, Scheme.Hom.comp_apply _ _ _⟩

/-- The ranges of the cover pieces are ordered by the index preorder. -/
theorem range_coverMap_le (n : ℕ) {i j : ResolutionIndex} (hij : i ⟶ j) :
    Set.range (coverMap R π n i) ⊆ Set.range (coverMap R π n j) := by
  rcases leOfHom hij with rfl | rfl
  · exact subset_rfl
  · intro z hz
    rw [mem_range_coverMap_overlap_iff] at hz
    cases j
    · rw [mem_range_coverMap_overlap_iff]
      exact hz
    · exact hz.1
    · change z ∈ Set.range (sideCharts R π n).ι
      rw [Scheme.Opens.range_ι]
      exact hz.2

/-- A point in the ranges of two distinct cover pieces lies in the overlap piece. -/
theorem mem_range_coverMap_overlap_of_ne (n : ℕ) {i j : ResolutionIndex} (hij : i ≠ j)
    {z : originBlowup R π n} (hi : z ∈ Set.range (coverMap R π n i))
    (hj : z ∈ Set.range (coverMap R π n j)) : z ∈ Set.range (coverMap R π n .overlap) := by
  cases i <;> cases j
  · exact hi
  · exact hi
  · exact hi
  · exact hj
  · exact absurd rfl hij
  · change z ∈ Set.range (sideCharts R π n).ι at hj
    rw [Scheme.Opens.range_ι] at hj
    exact (mem_range_coverMap_overlap_iff R π n z).mpr ⟨hi, hj⟩
  · exact hj
  · change z ∈ Set.range (sideCharts R π n).ι at hi
    rw [Scheme.Opens.range_ι] at hi
    exact (mem_range_coverMap_overlap_iff R π n z).mpr ⟨hj, hi⟩
  · exact absurd rfl hij

/-- The three-piece open cover of the origin blowup. -/
abbrev nodeCover (n : ℕ) : (originBlowup R π n).OpenCover where
  I₀ := ResolutionIndex
  X := coverObj R π n
  f := coverMap R π n
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun z ↦ ?_, fun i ↦ inferInstance⟩
    have hz : z ∈ (originBlowupParameterChartMap R π n).opensRange ⊔ sideCharts R π n := by
      rw [parameterChart_opensRange_sup_sideCharts_eq_top]
      trivial
    rcases Opens.mem_sup.mp hz with h | h
    · exact ⟨.central, h⟩
    · exact ⟨.side, ⟨⟨z, h⟩, rfl⟩⟩

instance nodeCover_locallyDirected (n : ℕ) : (nodeCover R π n).LocallyDirected where
  trans {i j} hij :=
    IsOpenImmersion.lift ((nodeCover R π n).f j) ((nodeCover R π n).f i)
      (range_coverMap_le R π n hij)
  trans_id i := by
    rw [← cancel_mono ((nodeCover R π n).f i)]
    simp
  trans_comp hij hjk := by
    rw [← cancel_mono ((nodeCover R π n).f _)]
    simp
  w hij := IsOpenImmersion.lift_fac _ _ _
  directed {i j} x := by
    by_cases hij : i = j
    · subst hij
      refine ⟨i, 𝟙 i, 𝟙 i, pullback.fst ((nodeCover R π n).f i) ((nodeCover R π n).f i) x, ?_⟩
      apply (pullback.fst ((nodeCover R π n).f i) ((nodeCover R π n).f i) ≫
        (nodeCover R π n).f i).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc, IsOpenImmersion.lift_fac,
        Scheme.Hom.comp_apply]
    · refine ⟨.overlap, homOfLE (ResolutionIndex.overlap_le i),
        homOfLE (ResolutionIndex.overlap_le j), ?_⟩
      have hx : (pullback.fst ((nodeCover R π n).f i) ((nodeCover R π n).f j) ≫
          (nodeCover R π n).f i) x ∈ Set.range ((nodeCover R π n).f .overlap) := by
        apply mem_range_coverMap_overlap_of_ne R π n hij
        · exact ⟨pullback.fst ((nodeCover R π n).f i) ((nodeCover R π n).f j) x,
            (Scheme.Hom.comp_apply _ _ _).symm⟩
        · refine ⟨pullback.snd ((nodeCover R π n).f i) ((nodeCover R π n).f j) x, ?_⟩
          rw [← Scheme.Hom.comp_apply, ← pullback.condition]
      obtain ⟨y, hy⟩ := hx
      refine ⟨y, ?_⟩
      apply (pullback.fst ((nodeCover R π n).f i) ((nodeCover R π n).f j) ≫
        (nodeCover R π n).f i).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc, IsOpenImmersion.lift_fac, hy]

/-- The transition map from the overlap to the central chart is the inclusion. -/
theorem nodeCover_trans_overlap_central (n : ℕ)
    (h : (ResolutionIndex.overlap : ResolutionIndex) ⟶ ResolutionIndex.central) :
    (nodeCover R π n).trans h = (overlap R π n).ι :=
  (IsOpenImmersion.lift_uniq ((nodeCover R π n).f .central) ((nodeCover R π n).f .overlap)
    (range_coverMap_le R π n h) (overlap R π n).ι rfl).symm

/-! ### The relative gluing datum -/

section Step

variable [IsDomain R] (hπ : Irreducible π) (k : ℕ) (res : NodeResolution R π k)

/-- The comparison map from a resolution of the thickness-`k` node to the parameter chart of
the blowup of the thickness-`k+2` node. -/
def toParameterChart : res.total ⟶ originBlowupParameterChart R π (k + 2) :=
  res.toNode ≫ (parameterReesChartIso R π hπ k).inv

/-- Over the overlap with the side charts the comparison map is an isomorphism. -/
theorem isIso_toParameterChart_restrict :
    IsIso (toParameterChart R π hπ k res ∣_ overlap R π (k + 2)) := by
  rw [toParameterChart, morphismRestrict_comp]
  have h1 : IsIso (res.toNode ∣_
      ((parameterReesChartIso R π hπ k).inv ⁻¹ᵁ overlap R π (k + 2))) :=
    isIso_morphismRestrict_of_le _ (parameterReesChartIso_inv_preimage_overlap_le R π hπ k)
      res.isIso_restrict
  have h2 : IsIso ((parameterReesChartIso R π hπ k).inv ∣_ overlap R π (k + 2)) :=
    isIso_morphismRestrict_of_isIso _ _
  exact IsIso.comp_isIso' h1 h2

/-- The schemes glued over the three cover pieces. -/
abbrev resObj : ResolutionIndex → Scheme.{u}
  | .overlap => (toParameterChart R π hπ k res ⁻¹ᵁ overlap R π (k + 2)).toScheme
  | .central => res.total
  | .side => (sideCharts R π (k + 2)).toScheme

/-- The transition maps between the glued schemes. -/
def resMap : ∀ {i j : ResolutionIndex}, (i ⟶ j) →
    (resObj R π hπ k res i ⟶ resObj R π hπ k res j)
  | .overlap, .overlap, _ => 𝟙 _
  | .central, .central, _ => 𝟙 _
  | .side, .side, _ => 𝟙 _
  | .overlap, .central, _ => (toParameterChart R π hπ k res ⁻¹ᵁ overlap R π (k + 2)).ι
  | .overlap, .side, h =>
    (toParameterChart R π hπ k res ∣_ overlap R π (k + 2)) ≫ (nodeCover R π (k + 2)).trans h
  | .central, .overlap, h => absurd (leOfHom h) (by decide)
  | .central, .side, h => absurd (leOfHom h) (by decide)
  | .side, .overlap, h => absurd (leOfHom h) (by decide)
  | .side, .central, h => absurd (leOfHom h) (by decide)

/-- The transition maps send identities to identities. -/
theorem resMap_id (i : ResolutionIndex) : resMap R π hπ k res (𝟙 i) = 𝟙 _ := by
  cases i <;> rfl

/-- The glued schemes as a functor on the cover indices. -/
def resFunctor : ResolutionIndex ⥤ Scheme.{u} where
  obj := resObj R π hπ k res
  map := resMap R π hπ k res
  map_id := resMap_id R π hπ k res
  map_comp {i j l} hij hjl := by
    rcases leOfHom hij with rfl | rfl
    · obtain rfl : hij = 𝟙 _ := Subsingleton.elim _ _
      rw [Category.id_comp, resMap_id, Category.id_comp]
    · rcases leOfHom hjl with rfl | rfl
      · obtain rfl : hjl = 𝟙 _ := Subsingleton.elim _ _
        rw [Category.comp_id, resMap_id, Category.comp_id]
      · obtain rfl : hij = 𝟙 _ := Subsingleton.elim _ _
        rw [Category.id_comp, resMap_id, Category.id_comp]

/-- The structure maps from the glued schemes to the cover pieces. -/
def resApp : ∀ i, (resFunctor R π hπ k res).obj i ⟶
    (nodeCover R π (k + 2)).functorOfLocallyDirected.obj i
  | .overlap => toParameterChart R π hπ k res ∣_ overlap R π (k + 2)
  | .central => toParameterChart R π hπ k res
  | .side => 𝟙 _

/-- The structure maps as a natural transformation. -/
def resNatTrans : resFunctor R π hπ k res ⟶ (nodeCover R π (k + 2)).functorOfLocallyDirected where
  app := resApp R π hπ k res
  naturality {i j} hij := by
    rcases leOfHom hij with rfl | rfl
    · obtain rfl : hij = 𝟙 _ := Subsingleton.elim _ _
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
        Category.comp_id]
    cases j
    · obtain rfl : hij = 𝟙 _ := Subsingleton.elim _ _
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
        Category.comp_id]
    · change (toParameterChart R π hπ k res ⁻¹ᵁ overlap R π (k + 2)).ι ≫
          toParameterChart R π hπ k res =
        (toParameterChart R π hπ k res ∣_ overlap R π (k + 2)) ≫
          (nodeCover R π (k + 2)).trans hij
      rw [nodeCover_trans_overlap_central, morphismRestrict_ι]
    · change ((toParameterChart R π hπ k res ∣_ overlap R π (k + 2)) ≫
          (nodeCover R π (k + 2)).trans hij) ≫ 𝟙 _ =
        (toParameterChart R π hπ k res ∣_ overlap R π (k + 2)) ≫
          (nodeCover R π (k + 2)).trans hij
      rw [Category.comp_id]

/-- The structure maps form cartesian squares over the transition maps. -/
theorem resNatTrans_equifibered : (resNatTrans R π hπ k res).Equifibered := by
  intro i j hij
  rcases leOfHom hij with rfl | rfl
  · obtain rfl : hij = 𝟙 _ := Subsingleton.elim _ _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  cases j
  · obtain rfl : hij = 𝟙 _ := Subsingleton.elim _ _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  · change IsPullback (toParameterChart R π hπ k res ⁻¹ᵁ overlap R π (k + 2)).ι
      (toParameterChart R π hπ k res ∣_ overlap R π (k + 2)) (toParameterChart R π hπ k res)
      ((nodeCover R π (k + 2)).trans hij)
    rw [nodeCover_trans_overlap_central]
    exact (isPullback_morphismRestrict _ _).flip
  · change IsPullback ((toParameterChart R π hπ k res ∣_ overlap R π (k + 2)) ≫
      (nodeCover R π (k + 2)).trans hij)
      (toParameterChart R π hπ k res ∣_ overlap R π (k + 2)) (𝟙 _)
      ((nodeCover R π (k + 2)).trans hij)
    have := isIso_toParameterChart_restrict R π hπ k res
    exact IsPullback.of_vert_isIso ⟨by simp⟩

/-- The relative gluing datum: the lower-thickness resolution over the central chart, the
side charts over themselves, and their common open part over the overlap. -/
def gluingData : (nodeCover R π (k + 2)).RelativeGluingData where
  functor := resFunctor R π hπ k res
  natTrans := resNatTrans R π hπ k res
  equifibered := resNatTrans_equifibered R π hπ k res

/-- The glued scheme maps properly to the blowup. -/
theorem gluingData_toBase_isProper : IsProper (gluingData R π hπ k res).toBase := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsProper)
    (fun i ↦ ((nodeCover R π (k + 2)).f i).opensRange)
    (nodeCover R π (k + 2)).iSup_opensRange).mpr fun i ↦ ?_
  refine (gluingData_property_restrict_iff (gluingData R π hπ k res) @IsProper i).mpr ?_
  cases i
  · change IsProper (toParameterChart R π hπ k res ∣_ overlap R π (k + 2))
    have := isIso_toParameterChart_restrict R π hπ k res
    infer_instance
  · change IsProper (res.toNode ≫ (parameterReesChartIso R π hπ k).inv)
    have := res.isProper
    infer_instance
  · change IsProper (𝟙 (sideCharts R π (k + 2)).toScheme)
    infer_instance

/-- The glued scheme is regular. -/
theorem gluingData_glued_isRegular [IsDiscreteValuationRing R] :
    SchemeIsRegular (gluingData R π hπ k res).glued := by
  apply SchemeIsRegular.of_openCover (gluingData R π hπ k res).cover
  intro i
  change SchemeIsRegular (resObj R π hπ k res i)
  cases i
  · change SchemeIsRegular (toParameterChart R π hπ k res ⁻¹ᵁ overlap R π (k + 2)).toScheme
    exact schemeIsRegular_of_isOpenImmersion
      (toParameterChart R π hπ k res ⁻¹ᵁ overlap R π (k + 2)).ι res.isRegular
  · exact res.isRegular
  · exact sideCharts_isRegular R π hπ k

/-- The glued scheme is isomorphic to the blowup over the side charts. -/
theorem gluingData_toBase_restrict_sideCharts_isIso :
    IsIso ((gluingData R π hπ k res).toBase ∣_ sideCharts R π (k + 2)) := by
  have h := (gluingData_property_restrict_iff (gluingData R π hπ k res)
    (MorphismProperty.isomorphisms Scheme) .side).mpr
    ((MorphismProperty.isomorphisms.iff _).mpr
      (inferInstance : IsIso (𝟙 (sideCharts R π (k + 2)).toScheme)))
  change MorphismProperty.isomorphisms Scheme
    ((gluingData R π hπ k res).toBase ∣_ (sideCharts R π (k + 2)).ι.opensRange) at h
  rw [Scheme.Opens.opensRange_ι] at h
  exact h

/-- The composite of the glued map with the blowup projection is an isomorphism away from
the origin. -/
theorem gluingData_toBase_projection_restrict_isIso :
    IsIso (((gluingData R π hπ k res).toBase ≫ originBlowupProjection R π (k + 2)) ∣_
      originComplement R π (k + 2)) := by
  rw [morphismRestrict_comp]
  have h1 : IsIso ((gluingData R π hπ k res).toBase ∣_
      (originBlowupProjection R π (k + 2) ⁻¹ᵁ originComplement R π (k + 2))) :=
    isIso_morphismRestrict_of_le _
      (projection_preimage_originComplement_le_sideCharts R π (k + 2))
      (gluingData_toBase_restrict_sideCharts_isIso R π hπ k res)
  have h2 : IsIso (originBlowupProjection R π (k + 2) ∣_ originComplement R π (k + 2)) :=
    ReesBlowup.projection_restrict_baseComplement_isIso _
  exact IsIso.comp_isIso' h1 h2

/-- Gluing a resolution of the thickness-`k` node into the blowup of the thickness-`k+2`
node resolves the latter. -/
def NodeResolution.step [IsDiscreteValuationRing R] : NodeResolution R π (k + 2) where
  total := (gluingData R π hπ k res).glued
  toNode := (gluingData R π hπ k res).toBase ≫ originBlowupProjection R π (k + 2)
  isProper := by
    have h1 := gluingData_toBase_isProper R π hπ k res
    have h2 : IsProper (originBlowupProjection R π (k + 2)) :=
      ReesBlowup.projection_isProper (totalSpaceOriginIdeal R π (k + 2))
    infer_instance
  isRegular := gluingData_glued_isRegular R π hπ k res
  isIso_restrict := gluingData_toBase_projection_restrict_isIso R π hπ k res

end Step

/-- Every standard node over a discrete valuation ring admits a resolution: a regular scheme
with a proper morphism to the node which is an isomorphism away from the origin, constructed
by repeatedly blowing up the origin. -/
def nodeResolution [IsDomain R] [IsDiscreteValuationRing R] (hπ : Irreducible π) :
    ∀ n : ℕ, NodeResolution R π n
  | 0 => NodeResolution.ofRegular R π 0 (ring_zero_isRegularRing R π)
  | 1 => NodeResolution.ofRegular R π 1 (ring_one_isRegularRing R π hπ)
  | k + 2 => NodeResolution.step R π hπ k (nodeResolution hπ k)

/-- The resolution of the thickness-`n` node is regular. -/
theorem nodeResolution_isRegular [IsDomain R] [IsDiscreteValuationRing R] (hπ : Irreducible π)
    (n : ℕ) : SchemeIsRegular (nodeResolution R π hπ n).total :=
  (nodeResolution R π hπ n).isRegular

/-- The resolution morphism of the thickness-`n` node is proper. -/
theorem nodeResolution_isProper [IsDomain R] [IsDiscreteValuationRing R] (hπ : Irreducible π)
    (n : ℕ) : IsProper (nodeResolution R π hπ n).toNode :=
  (nodeResolution R π hπ n).isProper

/-- The resolution morphism of the thickness-`n` node is an isomorphism away from the
origin. -/
theorem nodeResolution_isIso_restrict [IsDomain R] [IsDiscreteValuationRing R]
    (hπ : Irreducible π) (n : ℕ) :
    IsIso ((nodeResolution R π hπ n).toNode ∣_ originComplement R π n) :=
  (nodeResolution R π hπ n).isIso_restrict

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
