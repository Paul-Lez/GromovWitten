/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProjectiveBundleSegre
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyGlobal
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalizationExact

/-!
# The class of a coordinate point of `P(E ⊕ 1)` and the supports of the induction

Let `𝓔` be a graded vector bundle of rank `r = |ι|` over a scheme `X`, `q : P := P(E ⊕ 1) ⟶ X`
its projective completion with the charts `completionChart (j, s)`, `s : Option ι`, over the
trivialising opens `U_j`.  This file provides the supports used in the Noetherian induction of
the surjectivity half of the projective bundle formula, the bookkeeping of the restriction of
cycles to a chart `(j, s)`, and the key computation of the class of a coordinate point: for a
point `x ∈ U_j`, a finite set `S₀ ⊆ ι` of coordinates and a chart `s ∉ S₀`, the class of the
coordinate point `coordPoint j 𝔭_x (some '' S₀) s` (the generic point of `{x_t = 0 : t ∈ S₀}` in
the fibre over `x`) is `c₁(O(1))^{|S₀|} ∩ q^* [x]` plus the class of a cycle supported over
`closure {x} \ U_j`.  The proof restricts to the integral closed subscheme `P ×_X closure {x}`,
where the chain lemma of `ProjectiveBundleSegre.lean` identifies the two classes on the trivial
piece over `closure {x} ∩ U_j`, and uses the localisation sequence for the closed complement of
the piece.

## Main results

* `coordSupport`, `isClosed_coordSupport`, `coordSupport_empty`, `coordSupport_univ_subset`,
  `coordSupport_mono`, `coordSupport_anti`, `preimage_completionChart_coordSupport`,
  `coordSupport_diff_range_subset`, `coordSupport_univ_diff_range_subset`: the closed subset
  `coordSupport j Z S₀` of `P(E ⊕ 1)` (the points over `Z \ U_j` together with the points over
  `Z ∩ U_j` lying in none of the charts `(j, some t)`, `t ∈ S₀`) and its properties; its trace
  on the chart `(j, s)`, `s ∉ S₀`, is the zero locus of `chartIdeal j Z · R[x] + (x_t : t ∈ S₀)`.
* `supportedIn_compl_range_of_pullbackOpen_eq_zero`, `pullbackOpen_supportedIn_preimage`,
  `flatPullbackOpen_completionChart_point_coordPoint`,
  `flatPullbackOpen_completionChart_supportedIn_coordSupport`, `coordPoint_mem_coordSupport`,
  `dimensionFunction_coordPoint_chartBaseι`: restriction of cycles along the open immersion
  `completionChart (j, s)`: a cycle restricting to zero is supported off the chart, the
  coordinate point restricts to the coordinate prime `coordIdealPoint 𝔭 S₀`, and the dimension
  of a coordinate point over a prime `𝔭` of the chart ring.
* `ker_openImmersionPullback_le_range_of_homogeneous_of_isOpenImmersion`: the localisation
  sequence (exactness in the middle) for an arbitrary open immersion.
* `exists_coordPoint_class`: **the class of a coordinate point**: for `x ∈ U_j`, `S₀ ⊆ ι`
  finite and `s ∉ some '' S₀`, in `A_{dim x + r - |S₀|}(P(E ⊕ 1))`,
  `[coordPoint j 𝔭_x (some '' S₀) s] = c₁(O(1))^{|S₀|} ∩ q^* [x] + [ε]` for a cycle `ε`
  supported in `q⁻¹(closure {x} \ U_j)`.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open GradedBundleData ChartedOverSubscheme RationalEquivalenceSystem.DescendingMap
  FiniteTypeDimension BundlePullbackGlobal

/-! ## The supports of the induction -/

section Support

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : GradedBundleData X ι)

/-- The support used in the double induction of the projective bundle formula: the points of
`P(E ⊕ 1)` over `Z \ U_j`, together with the points over `Z ∩ U_j` lying in none of the charts
`(j, some t)`, `t ∈ S₀` (i.e. in the coordinate subspace `{x_t = 0 : t ∈ S₀}` of the fibre). -/
def coordSupport (j : 𝓔.bundle.J) (Z : Set X) (S₀ : Finset ι) : Set 𝓔.projectiveCompletion :=
  𝓔.completionToBase.base ⁻¹' (Z \ (𝓔.bundle.chart j).1) ∪
    {p | 𝓔.completionToBase.base p ∈ Z ∩ (𝓔.bundle.chart j).1 ∧
      ∀ t ∈ S₀, p ∉ Set.range (𝓔.completionChart (j, some t)).base}

/-- A point of the chart `(j, s)` of `P(E ⊕ 1)` lies over `U_j`. -/
theorem completionToBase_mem_chart_of_mem_range (j : 𝓔.bundle.J) (s : Option ι)
    {p : 𝓔.projectiveCompletion} (hp : p ∈ Set.range (𝓔.completionChart (j, s)).base) :
    𝓔.completionToBase.base p ∈ (𝓔.bundle.chart j).1 := by
  obtain ⟨y, rfl⟩ := hp
  have h : (𝓔.completionChart (j, s)).base y ∈ Set.range (𝓔.chartProjι j).base :=
    ⟨(projOptionChart _ ι s).base y, rfl⟩
  rw [range_chartProjι] at h
  exact h

/-- **(S-closed)** `coordSupport j Z S₀` is closed for closed `Z`: its complement is the union of
`q⁻¹(Zᶜ)` and the charts `(j, some t)`, `t ∈ S₀`. -/
theorem isClosed_coordSupport (j : 𝓔.bundle.J) {Z : Set X} (hZ : IsClosed Z) (S₀ : Finset ι) :
    IsClosed (coordSupport 𝓔 j Z S₀) := by
  have hcompl : (coordSupport 𝓔 j Z S₀)ᶜ = 𝓔.completionToBase.base ⁻¹' Zᶜ ∪
      ⋃ t ∈ S₀, Set.range (𝓔.completionChart (j, some t)).base := by
    ext p
    rw [Set.mem_compl_iff, Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, Set.mem_iUnion₂]
    constructor
    · intro h
      by_cases hZp : 𝓔.completionToBase.base p ∈ Z
      · right
        by_contra hcon
        push Not at hcon
        by_cases hU : 𝓔.completionToBase.base p ∈ (𝓔.bundle.chart j).1
        · exact h (Or.inr ⟨⟨hZp, hU⟩, hcon⟩)
        · exact h (Or.inl ⟨hZp, hU⟩)
      · exact Or.inl hZp
    · rintro (h | ⟨t, ht, hp⟩) hmem
      · rcases hmem with h' | h'
        · exact h h'.1
        · exact h h'.1.1
      · have hU := completionToBase_mem_chart_of_mem_range 𝓔 j (some t) hp
        rcases hmem with h' | h'
        · exact h'.2 hU
        · exact h'.2 t ht hp
  rw [← isOpen_compl_iff, hcompl]
  refine (hZ.isOpen_compl.preimage 𝓔.completionToBase.continuous).union ?_
  exact isOpen_biUnion fun t _ ↦ (𝓔.completionChart (j, some t)).isOpenEmbedding.isOpen_range

/-- **(S-empty)** `coordSupport j Z ∅ = q⁻¹(Z)`. -/
theorem coordSupport_empty (j : 𝓔.bundle.J) (Z : Set X) :
    coordSupport 𝓔 j Z ∅ = 𝓔.completionToBase.base ⁻¹' Z := by
  ext p
  simp only [coordSupport, Set.mem_union, Set.mem_preimage, Set.mem_sdiff, Set.mem_ofPred_eq,
    Set.mem_inter_iff, Finset.notMem_empty, false_imp_iff, implies_true, and_true]
  constructor
  · rintro (h | h)
    · exact h.1
    · exact h.1
  · intro h
    by_cases hU : 𝓔.completionToBase.base p ∈ (𝓔.bundle.chart j).1
    · exact Or.inr ⟨h, hU⟩
    · exact Or.inl ⟨h, hU⟩

/-- **(S-univ)** a point of `coordSupport j Z univ` is over `Z \ U_j` or in the chart
`(j, none)`. -/
theorem coordSupport_univ_subset [Fintype ι] (j : 𝓔.bundle.J) (Z : Set X) :
    coordSupport 𝓔 j Z Finset.univ ⊆
      𝓔.completionToBase.base ⁻¹' (Z \ (𝓔.bundle.chart j).1) ∪
        Set.range (𝓔.completionChart (j, none)).base := by
  rintro p (h | ⟨h1, h2⟩)
  · exact Or.inl h
  · obtain ⟨i, hi⟩ := exists_mem_range_completionChart_of_mem 𝓔 j h1.2
    cases i with
    | none => exact Or.inr hi
    | some t => exact absurd hi (h2 t (Finset.mem_univ t))

/-- **(S-mono in `Z`)** `coordSupport` is monotone in `Z`. -/
theorem coordSupport_mono (j : 𝓔.bundle.J) {Z Z' : Set X} (h : Z' ⊆ Z) (S₀ : Finset ι) :
    coordSupport 𝓔 j Z' S₀ ⊆ coordSupport 𝓔 j Z S₀ := by
  rintro p (hp | ⟨h1, h2⟩)
  · exact Or.inl ⟨h hp.1, hp.2⟩
  · exact Or.inr ⟨⟨h h1.1, h1.2⟩, h2⟩

/-- **(S-mono in `S₀`)** `coordSupport` is antitone in `S₀`. -/
theorem coordSupport_anti (j : 𝓔.bundle.J) (Z : Set X) {S₀ S₀' : Finset ι} (h : S₀ ⊆ S₀') :
    coordSupport 𝓔 j Z S₀' ⊆ coordSupport 𝓔 j Z S₀ := by
  rintro p (hp | ⟨h1, h2⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨h1, fun t ht ↦ h2 t (h ht)⟩

/-- **(S-rest)** a point of `coordSupport j Z S₀` outside the chart `(j, some t)` lies in
`coordSupport j Z (insert t S₀)`. -/
theorem coordSupport_diff_range_subset [DecidableEq ι] (j : 𝓔.bundle.J) (Z : Set X)
    (S₀ : Finset ι) (t : ι) :
    coordSupport 𝓔 j Z S₀ \ Set.range (𝓔.completionChart (j, some t)).base ⊆
      coordSupport 𝓔 j Z (insert t S₀) := by
  rintro p ⟨hp | ⟨h1, h2⟩, ht⟩
  · exact Or.inl hp
  · refine Or.inr ⟨h1, fun u hu ↦ ?_⟩
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact ht
    · exact h2 u hu

/-- **(S-rest, the case `S₀ = univ`)** a point of `coordSupport j Z univ` outside the chart
`(j, none)` lies over `Z \ U_j`. -/
theorem coordSupport_univ_diff_range_subset [Fintype ι] (j : 𝓔.bundle.J) (Z : Set X) :
    coordSupport 𝓔 j Z Finset.univ \ Set.range (𝓔.completionChart (j, none)).base ⊆
      𝓔.completionToBase.base ⁻¹' (Z \ (𝓔.bundle.chart j).1) := by
  rintro p ⟨hp, hn⟩
  rcases coordSupport_univ_subset 𝓔 j Z hp with h | h
  · exact h
  · exact absurd h hn

/-- The structure map of `P(E ⊕ 1)` on points of the chart `(j, s)`: contraction of primes to
`Γ(U_j)`, followed by the identification of `Spec Γ(U_j)` with `U_j`. -/
theorem completionToBase_completionChart_apply (j : 𝓔.bundle.J) (s : Option ι)
    (𝔮 : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))))) :
    𝓔.completionToBase.base ((𝓔.completionChart (j, s)).base 𝔮) =
      (𝓔.chartBaseι j).base (PrimeSpectrum.comap
        (MvPolynomial.C : Γ(X, (𝓔.bundle.chart j).1) →+* MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))
        𝔮) := by
  rw [completionChart_eq_projOptionChart_comp]
  change 𝓔.completionToBase.base ((𝓔.chartProjι j).base ((projOptionChart _ ι s).base 𝔮)) = _
  rw [completionToBase_chartProjι_apply, projection_projOptionChart, MvPolynomial.algebraMap_eq]

/-- A point of the chart `(j, s)` lies in the chart `(j, some u)`, for `s ≠ some u`, iff the
variable `X u` does not lie in its prime. -/
theorem completionChart_mem_range_completionChart_some_iff (j : 𝓔.bundle.J) {s : Option ι}
    {u : ι} (hsu : s ≠ some u)
    (𝔮 : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))))) :
    (𝓔.completionChart (j, s)).base 𝔮 ∈ Set.range (𝓔.completionChart (j, some u)).base ↔
      MvPolynomial.X u ∉ 𝔮.asIdeal := by
  rw [completionChart_eq_projOptionChart_comp (𝓔 := 𝓔) (j, s)]
  change (𝓔.chartProjι j).base ((projOptionChart _ ι s).base 𝔮) ∈ _ ↔ _
  rw [chartProjι_mem_range_completionChart_iff, projOptionChart_mem_basicOpen_iff,
    optionCoordVar_some_of_ne hsu]

/-- The trace of `coordSupport j Z S₀` on the chart `(j, s)`, `s ∉ S₀`, as a set of primes:
the primes `𝔮` lying over `Z` with `X u ∈ 𝔮` for all `u ∈ S₀`. -/
theorem preimage_completionChart_coordSupport' (j : 𝓔.bundle.J) (Z : Set X) (S₀ : Finset ι)
    {s : Option ι} (hs : s ∉ some '' (S₀ : Set ι)) :
    (𝓔.completionChart (j, s)).base ⁻¹' coordSupport 𝓔 j Z S₀ =
      {𝔮 | (𝓔.chartBaseι j).base (PrimeSpectrum.comap
          (MvPolynomial.C : Γ(X, (𝓔.bundle.chart j).1) →+*
            MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1)) 𝔮) ∈ Z ∧
        ∀ u ∈ S₀, MvPolynomial.X u ∈ 𝔮.asIdeal} := by
  ext 𝔮
  have hU : 𝓔.completionToBase.base ((𝓔.completionChart (j, s)).base 𝔮) ∈
      (𝓔.bundle.chart j).1 :=
    completionToBase_mem_chart_of_mem_range 𝓔 j s ⟨𝔮, rfl⟩
  have hsu : ∀ u ∈ S₀, s ≠ some u := fun u hu h ↦ hs ⟨u, hu, h.symm⟩
  simp only [Set.mem_preimage, coordSupport, Set.mem_union, Set.mem_sdiff, Set.mem_ofPred_eq,
    Set.mem_inter_iff]
  rw [completionToBase_completionChart_apply] at hU ⊢
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact absurd hU h.2
    · refine ⟨h1.1, fun u hu ↦ ?_⟩
      have := h2 u hu
      rwa [completionChart_mem_range_completionChart_some_iff 𝓔 j (hsu u hu), not_not] at this
  · rintro ⟨h1, h2⟩
    refine Or.inr ⟨⟨h1, hU⟩, fun u hu ↦ ?_⟩
    rw [completionChart_mem_range_completionChart_some_iff 𝓔 j (hsu u hu), not_not]
    exact h2 u hu

/-- **(S-chart)** the trace of `coordSupport j Z S₀` on the chart `(j, s)`, `s ∉ S₀`, for closed
`Z`, is the zero locus of the ideal `chartIdeal j Z · R[x] + (X u : u ∈ S₀)`. -/
theorem preimage_completionChart_coordSupport (j : 𝓔.bundle.J) {Z : Set X} (hZ : IsClosed Z)
    (S₀ : Finset ι) {s : Option ι} (hs : s ∉ some '' (S₀ : Set ι)) :
    (𝓔.completionChart (j, s)).base ⁻¹' coordSupport 𝓔 j Z S₀ =
      PrimeSpectrum.zeroLocus (((chartIdeal 𝓔.bundle j Z).map
        (MvPolynomial.C : Γ(X, (𝓔.bundle.chart j).1) →+*
          MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1)) ⊔
        Ideal.span (MvPolynomial.X '' (S₀ : Set ι)) :
          Ideal (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))) :
          Set (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))) := by
  rw [preimage_completionChart_coordSupport' 𝓔 j Z S₀ hs, PrimeSpectrum.zeroLocus_sup]
  ext 𝔮
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  have h1 : (𝓔.chartBaseι j).base (PrimeSpectrum.comap
      (MvPolynomial.C : Γ(X, (𝓔.bundle.chart j).1) →+*
        MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1)) 𝔮) ∈ Z ↔
      𝔮 ∈ PrimeSpectrum.zeroLocus ((chartIdeal 𝓔.bundle j Z).map
        (MvPolynomial.C : Γ(X, (𝓔.bundle.chart j).1) →+*
          MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1)) :
            Set (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))) := by
    rw [Ideal.map, PrimeSpectrum.zeroLocus_span, ← PrimeSpectrum.preimage_comap_zeroLocus,
      Set.mem_preimage, zeroLocus_chartIdeal 𝓔.bundle j hZ]
    exact Iff.rfl
  have h2 : (∀ u ∈ S₀, MvPolynomial.X u ∈ 𝔮.asIdeal) ↔
      𝔮 ∈ PrimeSpectrum.zeroLocus ((Ideal.span (MvPolynomial.X '' (S₀ : Set ι)) :
        Ideal (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))) :
          Set (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))) := by
    rw [PrimeSpectrum.zeroLocus_span, PrimeSpectrum.mem_zeroLocus, Set.image_subset_iff]
    exact ⟨fun h u hu ↦ h u hu, fun h u hu ↦ h hu⟩
  rw [h1, h2]

end Support

/-! ## Restriction of cycles to a chart `(j, s)` -/

section Chart

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : GradedBundleData X ι)

/-- The variables of the chart `s ∉ some '' S₀` indexed by the coordinates `some '' S₀` are
exactly the variables `X u`, `u ∈ S₀`. -/
theorem chartSet_option_image (S₀ : Set ι) {s : Option ι} (hs : s ∉ some '' S₀) :
    chartSet s (some '' S₀) = S₀ := by
  cases s with
  | none => exact chartSet_none_image S₀
  | some t => exact chartSet_some_image S₀ fun ht ↦ hs ⟨t, ht, rfl⟩

/-- The coordinate point `coordPoint j 𝔭 (some '' S₀) s`, `s ∉ some '' S₀`, is the image under
the chart `(j, s)` of the coordinate prime `coordIdealPoint 𝔭 S₀`. -/
theorem coordPoint_eq_completionChart_coordIdealPoint (j : 𝓔.bundle.J)
    (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1)))) (S₀ : Set ι) {s : Option ι}
    (hs : s ∉ some '' S₀) :
    𝓔.coordPoint j 𝔭 (some '' S₀) s =
      (𝓔.completionChart (j, s)).base (coordIdealPoint 𝔭.asIdeal S₀) := by
  rw [coordPoint_eq_completionChart, chartSet_option_image S₀ hs]

/-- The restriction to the chart `(j, s)`, `s ∉ some '' S₀`, of the point cycle of the coordinate
point `coordPoint j 𝔭 (some '' S₀) s` is the point cycle of the coordinate prime
`coordIdealPoint 𝔭 S₀`. -/
theorem flatPullbackOpen_completionChart_point_coordPoint
    {dimP : DimensionFunction 𝓔.projectiveCompletion} (j : 𝓔.bundle.J) {s : Option ι}
    {dimA : DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))))}
    (hdim : ∀ 𝔮, dimA 𝔮 = dimP ((𝓔.completionChart (j, s)).base 𝔮))
    (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1)))) (S₀ : Set ι)
    (hs : s ∉ some '' S₀) {i : ℤ} (h : dimP (𝓔.coordPoint j 𝔭 (some '' S₀) s) = i) :
    cyclesOfDimension.flatPullbackOpen (i := i) (𝓔.completionChart (j, s)) hdim
        (cyclesOfDimension.point (𝓔.coordPoint j 𝔭 (some '' S₀) s) h) =
      cyclesOfDimension.point (coordIdealPoint 𝔭.asIdeal S₀)
        ((hdim _).trans ((coordPoint_eq_completionChart_coordIdealPoint 𝓔 j 𝔭 S₀ hs) ▸ h)) := by
  rw [cyclesOfDimension.point_congr (coordPoint_eq_completionChart_coordIdealPoint 𝓔 j 𝔭 S₀ hs),
    flatPullbackOpen_point]

/-- The restriction to the chart `(j, s)`, `s ∉ some '' S₀`, of `pointProj` at the coordinate
point `coordPoint j 𝔭 (some '' S₀) s` is `pointProj` at the coordinate prime
`coordIdealPoint 𝔭 S₀`. -/
theorem pullbackOpen_completionChart_pointProj_coordPoint
    {dimP : DimensionFunction 𝓔.projectiveCompletion} (j : 𝓔.bundle.J) {s : Option ι}
    {dimA : DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))))}
    (hdim : ∀ 𝔮, dimA 𝔮 = dimP ((𝓔.completionChart (j, s)).base 𝔮))
    (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1)))) (S₀ : Set ι)
    (hs : s ∉ some '' S₀) (i : ℤ) :
    AlgebraicCycle.pullbackOpen (𝓔.completionChart (j, s))
        (cyclesOfDimension.pointProj dimP i (𝓔.coordPoint j 𝔭 (some '' S₀) s) :
          AlgebraicCycle 𝓔.projectiveCompletion ℚ) =
      (cyclesOfDimension.pointProj dimA i (coordIdealPoint 𝔭.asIdeal S₀) :
        AlgebraicCycle _ ℚ) := by
  rw [coordPoint_eq_completionChart_coordIdealPoint 𝓔 j 𝔭 S₀ hs]
  apply Function.locallyFinsuppWithin.ext
  intro b
  rw [AlgebraicCycle.pullbackOpen_apply, cyclesOfDimension.pointProj_apply,
    cyclesOfDimension.pointProj_apply, hdim b]
  by_cases hab : coordIdealPoint 𝔭.asIdeal S₀ = b
  · subst hab
    by_cases hd : dimP ((𝓔.completionChart (j, s)).base (coordIdealPoint 𝔭.asIdeal S₀)) = i
    · rw [if_pos ⟨rfl, hd⟩, if_pos ⟨rfl, hd⟩]
    · rw [if_neg (fun h ↦ hd h.2), if_neg (fun h ↦ hd h.2)]
  · rw [if_neg (fun h ↦ hab ((𝓔.completionChart (j, s)).isOpenEmbedding.injective h.1)),
      if_neg (fun h ↦ hab h.1)]

/-- The restriction to the chart `(j, s)`, `s ∉ some '' S₀`, of a cycle supported in
`coordSupport j Z S₀` (`Z` closed) is supported in the zero locus of
`chartIdeal j Z · R[x] + (X u : u ∈ S₀)`. -/
theorem pullbackOpen_completionChart_supportedIn_coordSupport (j : 𝓔.bundle.J) {Z : Set X}
    (hZ : IsClosed Z) (S₀ : Finset ι) {s : Option ι} (hs : s ∉ some '' (S₀ : Set ι))
    (z : AlgebraicCycle 𝓔.projectiveCompletion ℚ) (hz : z.SupportedIn (coordSupport 𝓔 j Z S₀)) :
    (AlgebraicCycle.pullbackOpen (𝓔.completionChart (j, s)) z).SupportedIn
      (PrimeSpectrum.zeroLocus (((chartIdeal 𝓔.bundle j Z).map
        (MvPolynomial.C : Γ(X, (𝓔.bundle.chart j).1) →+*
          MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1)) ⊔
        Ideal.span (MvPolynomial.X '' (S₀ : Set ι)) :
          Ideal (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))) :
          Set (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1)))) := by
  rw [← preimage_completionChart_coordSupport 𝓔 j hZ S₀ hs]
  exact fun a ha ↦ hz _ ha

/-- A coordinate point over a prime `𝔭` lying over `Z` lies in `coordSupport j Z S₀`. -/
theorem coordPoint_mem_coordSupport (j : 𝓔.bundle.J)
    (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1)))) {Z : Set X}
    (h𝔭 : (𝓔.chartBaseι j).base 𝔭 ∈ Z) (S₀ : Finset ι) {s : Option ι}
    (hs : s ∉ some '' (S₀ : Set ι)) :
    𝓔.coordPoint j 𝔭 (some '' (S₀ : Set ι)) s ∈ coordSupport 𝓔 j Z S₀ := by
  have hU : (𝓔.chartBaseι j).base 𝔭 ∈ (𝓔.bundle.chart j).1 := by
    have h : (𝓔.chartBaseι j).base 𝔭 ∈ Set.range (chartε 𝓔.bundle j).base := ⟨𝔭, rfl⟩
    rwa [range_chartε] at h
  refine Or.inr ⟨?_, fun u hu ↦ ?_⟩
  · rw [completionToBase_coordPoint]
    exact ⟨h𝔭, hU⟩
  · rw [coordPoint_mem_range_completionChart_iff 𝓔 j 𝔭 _ hs, not_not]
    exact ⟨u, hu, rfl⟩

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]

/-- The canonical dimension function of a chart `(j, s)` of `P(E ⊕ 1)` is the restriction of the
canonical dimension function of `P(E ⊕ 1)`. -/
theorem dimensionFunction_completionChart (a : 𝓔.bundle.J × Option ι)
    (𝔮 : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.bundle.chart a.1).1))))) :
    dimensionFunction (𝓔.completionChart a ≫ (𝓔.completionToBase ≫ f)) 𝔮 =
      dimensionFunction (𝓔.completionToBase ≫ f) ((𝓔.completionChart a).base 𝔮) :=
  dimensionFunction_comp _ _ 𝔮

/-- The dimension of the coordinate point of `S₀` over a prime `𝔭` of the chart ring `Γ(U_j)`:
`dim 𝔭 + rank - |S₀|`. -/
theorem dimensionFunction_coordPoint_chartBaseι [Finite ι] (j : 𝓔.bundle.J)
    (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1)))) (S₀ : Finset ι) {s : Option ι}
    (hs : s ∉ some '' (S₀ : Set ι)) :
    dimensionFunction (𝓔.completionToBase ≫ f) (𝓔.coordPoint j 𝔭 (some '' (S₀ : Set ι)) s) =
      dimensionFunction (𝓔.chartBaseι j ≫ f) 𝔭 + (Nat.card ι : ℤ) - S₀.card := by
  have hU : (𝓔.chartBaseι j).base 𝔭 ∈ (𝓔.bundle.chart j).1 := by
    have h : (𝓔.chartBaseι j).base 𝔭 ∈ Set.range (chartε 𝓔.bundle j).base := ⟨𝔭, rfl⟩
    rwa [range_chartε] at h
  have h𝔭 : 𝔭 = 𝓔.bundle.chartBasePoint j ⟨(𝓔.chartBaseι j).base 𝔭, hU⟩ := by
    apply (𝓔.chartBaseι j).isOpenEmbedding.injective
    rw [chartBaseι_chartBasePoint']
  rw [dimensionFunction_comp f (𝓔.chartBaseι j) 𝔭]
  conv_lhs => rw [h𝔭]
  exact 𝓔.dimensionFunction_coordPoint f j hU S₀ hs

end Chart

/-! ## The localisation sequence for an arbitrary open immersion -/

section Localisation

/-- `openImmersionPullback` only depends on the open immersion. -/
theorem openImmersionPullback_congr_hom {Y U : Scheme.{u}} {dimY : DimensionFunction Y}
    {dimU : DimensionFunction U} {i : ℤ} (R : RationalEquivalenceSystem Y dimY i)
    {ψ ψ' : U ⟶ Y} [IsOpenImmersion ψ] [IsOpenImmersion ψ'] (h : ψ = ψ')
    (hdim : ∀ u, dimU u = dimY (ψ.base u)) (S : RationalEquivalenceSystem U dimU i) :
    openImmersionPullback R ψ hdim S = openImmersionPullback R ψ' (h ▸ hdim) S := by
  subst h
  rfl

/-- **Exactness in the middle of the localisation sequence**, for an arbitrary open immersion
`ψ : U ⟶ Y` (not necessarily the inclusion of an `Opens`) and a closed immersion `g : W ⟶ Y`
whose image contains the complement of the image of `ψ`, over a Noetherian scheme all of whose
principal divisors are homogeneous: a class restricting to zero on `U` is pushed forward from
`W`. -/
theorem ker_openImmersionPullback_le_range_of_homogeneous_of_isOpenImmersion
    {Y U W : Scheme.{u}} [NoetherianSpace Y] [IsLocallyNoetherian Y]
    {dimY : DimensionFunction Y} {dimU : DimensionFunction U} {dimW : DimensionFunction W}
    {i : ℤ} (R : RationalEquivalenceSystem Y dimY i) (ψ : U ⟶ Y) [IsOpenImmersion ψ]
    (hdim : ∀ u, dimU u = dimY (ψ.base u)) (S : RationalEquivalenceSystem U dimU i)
    (Q : RationalEquivalenceSystem W dimW i) (g : W ⟶ Y) [IsClosedImmersion g]
    (hrange : ∀ y : Y, y ∉ Set.range ψ.base → y ∈ Set.range g.base)
    (hhom : PrincipalDivisorsHomogeneous Y dimY) :
    LinearMap.ker (openImmersionPullback R ψ hdim S) ≤
      LinearMap.range (closedImmersionPushforward Q g R) := by
  intro c hc
  rw [LinearMap.mem_ker] at hc
  let V : Y.Opens := ψ.opensRange
  let e : U ≅ V.toScheme := ψ.isoOpensRange
  have hfac : e.hom ≫ V.ι = ψ := ψ.isoOpensRange_hom_ι
  let dimV : DimensionFunction V.toScheme := DimensionFunction.comapClosedImmersion e.inv dimU
  have h₂ : ∀ v, dimV v = dimU (e.inv.base v) := fun _ ↦ rfl
  have hdimV : ∀ v, dimV v = dimY (V.ι.base v) := by
    intro v
    rw [h₂, hdim]
    change dimY ((e.inv ≫ ψ).base v) = _
    rw [← hfac, Iso.inv_hom_id_assoc]
  have h₁ : ∀ u, dimU u = dimV (e.hom.base u) := by
    intro u
    rw [h₂]
    change dimU u = dimU ((e.hom ≫ e.inv).base u)
    rw [Iso.hom_inv_id]
    rfl
  let S' : RationalEquivalenceSystem V.toScheme dimV i := .canonical
  have hcomp : openImmersionPullback R ψ hdim S =
      (openImmersionPullback S' e.hom h₁ S).comp (openImmersionPullback R V.ι hdimV S') := by
    rw [openImmersionPullback_congr_hom R hfac.symm hdim S]
    exact openImmersionPullback_comp R S' S e.hom V.ι h₁ hdimV _
  have hinj : Function.Injective (openImmersionPullback S' e.hom h₁ S) := by
    intro a b hab
    have hid : (openImmersionPullback S e.inv h₂ S').comp (openImmersionPullback S' e.hom h₁ S) =
        LinearMap.id := by
      rw [← openImmersionPullback_comp S' S S' e.inv e.hom h₂ h₁
        (fun v ↦ (h₂ v).trans (h₁ (e.inv.base v))),
        openImmersionPullback_congr_hom S' (Iso.inv_hom_id e)]
      exact openImmersionPullback_id S' _
    have := congrArg (openImmersionPullback S e.inv h₂ S') hab
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hid, LinearMap.id_apply,
      LinearMap.id_apply] at this
  have hc' : openImmersionPullback R V.ι hdimV S' c = 0 := by
    apply hinj
    rw [← LinearMap.comp_apply, ← hcomp, hc, map_zero]
  have hrange' : ∀ y : Y, y ∉ V → y ∈ Set.range g.base := fun y hy ↦ hrange y hy
  exact ker_openImmersionPullback_le_range_of_homogeneous R V S' hdimV Q g hrange' hhom hc'

end Localisation

/-! ## The class of a coordinate point -/

section CoordClass

open LineBundleInjective

/-- The image of the inclusion of `pointSubscheme x` is the closure of `{x}`. -/
theorem range_inclusion_pointSubscheme {X : Scheme.{u}} [IsLocallyNoetherian X]
    [NoetherianSpace X] (x : X) :
    Set.range (pointSubscheme x).inclusion.base = closure {x} := by
  have h := (pointSubscheme x).coe_support_ker
  rw [Scheme.Hom.support_ker, genericPointImage_pointSubscheme] at h
  rw [← h]
  exact (pointSubscheme x).inclusion.isClosedEmbedding.isClosed_range.closure_eq.symm

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [IsLocallyNoetherian X] [NoetherianSpace X] {ι : Type u} [Finite ι]
  (𝓔 : GradedBundleData X ι) [NoetherianSpace 𝓔.projectiveCompletion]
  (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))
  (x : X) (j : 𝓔.bundle.J) (hx : x ∈ (𝓔.bundle.chart j).1)

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- A point of `P(E ⊕ 1) ×_X closure {x}` outside the trivial piece over `closure {x} ∩ U_j`
maps to a point of `P(E ⊕ 1)` over `closure {x} \ U_j`. -/
theorem completionToBase_restrictι_mem_of_notMem_range_restrictOpenι
    (b : restrictScheme 𝓔.completionCharts (pointSubscheme x))
    (hb : b ∉ Set.range
      (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base) :
    𝓔.completionToBase.base ((restrictι 𝓔.completionCharts (pointSubscheme x)).base b) ∈
      closure {x} \ (𝓔.bundle.chart j).1 := by
  have h1 : 𝓔.completionToBase.base ((restrictι 𝓔.completionCharts (pointSubscheme x)).base b) ∈
      Set.range (pointSubscheme x).inclusion.base :=
    (mem_range_restrictι_iff 𝓔.completionCharts (pointSubscheme x) _).1 ⟨b, rfl⟩
  refine ⟨range_inclusion_pointSubscheme x ▸ h1, fun hU ↦ hb ?_⟩
  obtain ⟨a, ha⟩ := (mem_range_pieceι_iff 𝓔 x j _).2 ⟨h1, hU⟩
  refine ⟨a, (restrictι 𝓔.completionCharts (pointSubscheme x)).isClosedEmbedding.injective ?_⟩
  exact ha

/-- **The class of a coordinate point** (Fulton 3.3, the inductive step of the surjectivity of
the projective bundle map): for `x ∈ U_j`, a finite set `S₀ ⊆ ι` of coordinates and a chart
`s ∉ some '' S₀`, the class in `A_{dim x + r - |S₀|}(P(E ⊕ 1))` of the coordinate point
`coordPoint j 𝔭_x (some '' S₀) s` is `c₁(O(1))^{|S₀|} ∩ q^* [x]` plus the class of a cycle
`ε` supported in `q⁻¹(closure {x} \ U_j)`. -/
theorem exists_coordPoint_class (S₀ : Finset ι) {s : Option ι}
    (hs : s ∉ some '' (S₀ : Set ι)) :
    ∃ ε : cyclesOfDimension 𝓔.projectiveCompletion
      (dimensionFunction (𝓔.completionToBase ≫ f))
      (dimensionFunction f x + (Nat.card ι : ℤ) - S₀.card),
      (ε : AlgebraicCycle 𝓔.projectiveCompletion ℚ).SupportedIn
        (𝓔.completionToBase.base ⁻¹' (closure {x} \ (𝓔.bundle.chart j).1)) ∧
      (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f))
          (dimensionFunction f x + (Nat.card ι : ℤ) - S₀.card)).quotientMap
          (cyclesOfDimension.point
            (𝓔.coordPoint j (𝓔.bundle.chartBasePoint j ⟨x, hx⟩) (some '' (S₀ : Set ι)) s)
            (𝓔.dimensionFunction_coordPoint f j hx S₀ hs)) =
        c1Iter (𝓔.completionToBase ≫ f) (𝓔.tautological hX) S₀.card
          (dimensionFunction f x + (Nat.card ι : ℤ) - S₀.card) (chowCast (by ring)
            (chowPullbackCharted 𝓔.completionCharts (dimensionFunction f)
              (dimensionFunction (𝓔.completionToBase ≫ f))
              (𝓔.dimensionFunction_fibrePoint_completionCharts f) (dimensionFunction f x)
              (chowSystem _ _) (chowSystem _ _)
              ((chowSystem (dimensionFunction f) (dimensionFunction f x)).quotientMap
                (cyclesOfDimension.point x rfl)))) +
        (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f))
          (dimensionFunction f x + (Nat.card ι : ℤ) - S₀.card)).quotientMap ε := by
  classical
  have hNV := noetherianSpace_of_isClosedImmersion'
    (restrictι 𝓔.completionCharts (pointSubscheme x))
  have hLNV : IsLocallyNoetherian (restrictScheme 𝓔.completionCharts (pointSubscheme x)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (restrictι 𝓔.completionCharts (pointSubscheme x) ≫ (𝓔.completionToBase ≫ f))
  have hNpiece := noetherianSpace_of_isOpenImmersion
    (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j))
  have hcast : dimensionFunction f x + (Nat.card ι : ℤ) =
      dimensionFunction f x + (Nat.card ι : ℤ) - S₀.card + S₀.card := by ring
  have hgen : dimensionFunction f (pointSubscheme x).genericPointImage + (Nat.card ι : ℤ) =
      dimensionFunction f x + (Nat.card ι : ℤ) := by
    rw [genericPointImage_pointSubscheme]
  -- Step 1: `q^* [x]` is the pushforward of the generic class of `P ×_X closure {x}`.
  have h1 := chowPullbackCharted_point 𝓔.completionCharts f
    (𝓔.dimensionFunction_fibrePoint_completionCharts f) x rfl
  -- The point `π_V` of `P ×_X closure {x}` and its dimension.
  have hπ : dimensionFunction (restrictι 𝓔.completionCharts (pointSubscheme x) ≫
      (𝓔.completionToBase ≫ f))
      ((restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base
        (piecePoint 𝓔 x j hx S₀)) =
      dimensionFunction f x + (Nat.card ι : ℤ) - S₀.card :=
    (dim_restrictOpenι 𝓔.completionCharts f (pointSubscheme x) (pieceBaseι 𝓔 x j) _).symm.trans
      (dim_piecePoint f 𝓔 x j hx S₀)
  -- Step 4: the class `γ` on `P ×_X closure {x}` restricting to zero on the trivial piece.
  set γ := c1Iter (restrictι 𝓔.completionCharts (pointSubscheme x) ≫ (𝓔.completionToBase ≫ f))
      ((𝓔.tautological hX).restrict (restrictι 𝓔.completionCharts (pointSubscheme x))) S₀.card
      (dimensionFunction f x + (Nat.card ι : ℤ) - S₀.card)
      (chowCast hcast (chowCast hgen (genericRestrictClass 𝓔.completionCharts f
        (𝓔.dimensionFunction_fibrePoint_completionCharts f) (pointSubscheme x)))) -
    (chowSystem _ _).quotientMap (cyclesOfDimension.point
      ((restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base
        (piecePoint 𝓔 x j hx S₀)) hπ) with hγ
  have hγ0 : openImmersionPullback (chowSystem _ _)
      (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j))
      (dim_restrictOpenι 𝓔.completionCharts f (pointSubscheme x) (pieceBaseι 𝓔 x j))
      (chowSystem _ _) γ = 0 := by
    have hG : openImmersionPullback (chowSystem _ (dimensionFunction f x + (Nat.card ι : ℤ)))
        (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j))
        (dim_restrictOpenι 𝓔.completionCharts f (pointSubscheme x) (pieceBaseι 𝓔 x j))
        (chowSystem _ (dimensionFunction f x + (Nat.card ι : ℤ)))
        (chowCast hgen (genericRestrictClass 𝓔.completionCharts f
          (𝓔.dimensionFunction_fibrePoint_completionCharts f) (pointSubscheme x))) =
        (chowSystem _ _).quotientMap (cyclesOfDimension.point (piecePoint 𝓔 x j hx ∅)
          (by rw [dim_piecePoint]; simp)) := by
      rw [genericRestrictClass, chowCast_point, openImmersionPullback_quotientMap,
        cyclesOfDimension.point_congr (restrictOpenι_piecePoint_empty 𝓔 x j hx).symm,
        flatPullbackOpen_point]
    have hchain := c1Iter_piecePoint f 𝓔 hX x j hx S₀
    rw [chowCast_point] at hchain
    rw [hγ, map_sub, openImmersionPullback_c1Iter, openImmersionPullback_chowCast, hG,
      chowCast_point, openImmersionPullback_quotientMap, flatPullbackOpen_point]
    change c1Iter (pieceStructure f 𝓔 x j) (pieceBundle 𝓔 hX x j) S₀.card _ _ - _ = 0
    rw [hchain, sub_self]
  -- Step 5: localisation on `P ×_X closure {x}` along the closed complement `W` of the piece.
  set W : (restrictScheme 𝓔.completionCharts (pointSubscheme x)).IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨(Set.range (restrictOpenι 𝓔.completionCharts
      (pointSubscheme x) (pieceBaseι 𝓔 x j)).base)ᶜ,
      (restrictOpenι 𝓔.completionCharts (pointSubscheme x)
        (pieceBaseι 𝓔 x j)).isOpenEmbedding.isOpen_range.isClosed_compl⟩ with hW
  have hrangeW : Set.range W.subschemeι.base = (Set.range (restrictOpenι 𝓔.completionCharts
      (pointSubscheme x) (pieceBaseι 𝓔 x j)).base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, hW, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨ε', hε'⟩ := LinearMap.mem_range.mp
    (ker_openImmersionPullback_le_range_of_homogeneous_of_isOpenImmersion (chowSystem _ _)
      (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j))
      (dim_restrictOpenι 𝓔.completionCharts f (pointSubscheme x) (pieceBaseι 𝓔 x j))
      (chowSystem _ _)
      (chowSystem (dimensionFunction (W.subschemeι ≫
        (restrictι 𝓔.completionCharts (pointSubscheme x) ≫ (𝓔.completionToBase ≫ f))))
        (dimensionFunction f x + (Nat.card ι : ℤ) - S₀.card))
      W.subschemeι (fun b hb ↦ hrangeW ▸ hb)
      (FiniteTypeDimension.principalDivisorsHomogeneous _) (LinearMap.mem_ker.mpr hγ0))
  induction ε' using Submodule.Quotient.induction_on with
  | H e =>
  change closedImmersionPushforward _ W.subschemeι _ ((chowSystem _ _).quotientMap e) = γ at hε'
  rw [closedImmersionPushforward_quotientMap] at hε'
  -- Step 6: the cycle `ε` on `P(E ⊕ 1)` and its support.
  refine ⟨-cyclesOfDimension.properPushforward (restrictι 𝓔.completionCharts (pointSubscheme x))
    (cyclesOfDimension.properPushforward (dimensionY := dimensionFunction
      (restrictι 𝓔.completionCharts (pointSubscheme x) ≫ (𝓔.completionToBase ≫ f)))
      W.subschemeι e), ?_, ?_⟩
  · rw [Submodule.coe_neg]
    refine AlgebraicCycle.SupportedIn.neg fun p hp ↦ ?_
    have hp' : p ∈ Set.range (restrictι 𝓔.completionCharts (pointSubscheme x)).base := by
      by_contra hcon
      exact hp (closedImmersion_map_apply_of_not_mem_range
        (restrictι 𝓔.completionCharts (pointSubscheme x)) _ _ _ hcon)
    obtain ⟨b, rfl⟩ := hp'
    change _root_.AlgebraicGeometry.AlgebraicCycle.map
      (restrictι 𝓔.completionCharts (pointSubscheme x)) _ _ _
      ((restrictι 𝓔.completionCharts (pointSubscheme x)).base b) ≠ 0 at hp
    rw [closedImmersion_map_apply_base] at hp
    have hb : b ∈ Set.range W.subschemeι.base := by
      by_contra hcon
      exact hp (closedImmersion_map_apply_of_not_mem_range W.subschemeι _ _ _ hcon)
    rw [hrangeW] at hb
    exact completionToBase_restrictι_mem_of_notMem_range_restrictOpenι 𝓔 x j b hb
  · -- Step 7: assembly.
    have hpt : 𝓔.coordPoint j (𝓔.bundle.chartBasePoint j ⟨x, hx⟩) (some '' (S₀ : Set ι)) s =
        (restrictι 𝓔.completionCharts (pointSubscheme x)).base
          ((restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base
            (piecePoint 𝓔 x j hx S₀)) := by
      rw [coordPoint_congr 𝓔 j _ _ hs (i' := none) (by simp)]
      exact (pieceι_piecePoint 𝓔 x j hx S₀).symm
    have hpush : closedImmersionPushforward (chowSystem _ _)
        (restrictι 𝓔.completionCharts (pointSubscheme x)) (chowSystem _ _) γ =
        c1Iter (𝓔.completionToBase ≫ f) (𝓔.tautological hX) S₀.card
          (dimensionFunction f x + (Nat.card ι : ℤ) - S₀.card) (chowCast hcast
            (chowPullbackCharted 𝓔.completionCharts (dimensionFunction f)
              (dimensionFunction (𝓔.completionToBase ≫ f))
              (𝓔.dimensionFunction_fibrePoint_completionCharts f) (dimensionFunction f x)
              (chowSystem _ _) (chowSystem _ _)
              ((chowSystem (dimensionFunction f) (dimensionFunction f x)).quotientMap
                (cyclesOfDimension.point x rfl)))) -
          (chowSystem _ _).quotientMap (cyclesOfDimension.point
            (𝓔.coordPoint j (𝓔.bundle.chartBasePoint j ⟨x, hx⟩) (some '' (S₀ : Set ι)) s)
            (𝓔.dimensionFunction_coordPoint f j hx S₀ hs)) := by
      rw [hγ, map_sub, closedImmersionPushforward_c1Iter, closedImmersionPushforward_chowCast,
        ← h1, closedImmersionPushforward_quotientMap, properPushforward_point_of_isClosedImmersion,
        cyclesOfDimension.point_congr hpt]
    have hε'' : closedImmersionPushforward (chowSystem _ _)
        (restrictι 𝓔.completionCharts (pointSubscheme x))
        (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) _) γ =
        (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) _).quotientMap
          (cyclesOfDimension.properPushforward
          (dimensionY := dimensionFunction (𝓔.completionToBase ≫ f))
          (restrictι 𝓔.completionCharts (pointSubscheme x))
          (cyclesOfDimension.properPushforward (dimensionY := dimensionFunction
            (restrictι 𝓔.completionCharts (pointSubscheme x) ≫ (𝓔.completionToBase ≫ f)))
            W.subschemeι e)) := by
      rw [← hε', closedImmersionPushforward_quotientMap]
    rw [map_neg, ← hε'', hpush]
    abel

end CoordClass

end GromovWitten.AlgebraicGeometry.IntersectionTheory
