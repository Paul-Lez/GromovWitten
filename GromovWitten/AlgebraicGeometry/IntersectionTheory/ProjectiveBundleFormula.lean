/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProjectiveBundleSegre
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyGlobal

/-!
# The projective bundle formula for `P(E ⊕ 1)`: surjectivity and bijectivity

Let `𝓔` be a graded vector bundle of rank `r = |ι|` over a scheme `X` locally of finite type over
an infinite field `k` with Noetherian underlying space, `q : P := P(E ⊕ 1) ⟶ X` its projective
completion and `L = O(1)` the tautological line bundle.  Round 27 proved that the projective
bundle map
`θ_i : ⨁_{m = 0}^{r} A_{i + m - r}(X) → A_i(P)`, `(α_m)_m ↦ ∑_m c₁(O(1))^m ∩ q^* α_m`
is injective.  This file proves that it is **surjective**, hence bijective (Fulton,
*Intersection Theory*, Theorem 3.3(b) for `P(E ⊕ 1)`).

The proof is a double induction on supports: a Noetherian induction on the closed subset
`Z ⊆ X` over which a cycle is supported, and inside it a descending induction on a finite set
`S₀ ⊆ ι` of coordinates of a trivialising chart `U_j`; the cycles considered are supported in the
closed subsets `coordSupport j Z S₀` of `P` (the points over `Z \ U_j`, together with the points
over `Z ∩ U_j` lying in none of the charts `(j, some s)`, `s ∈ S₀`).  On the chart `(j, s)` the
affine statement with supports of `CoordinateSubspacePullback.lean` writes the restricted cycle
as a combination of coordinate points modulo a relation supported in the trace of the support;
the relation is extended by closure, the coordinate points are the classes
`c₁(O(1))^{|S₀|} ∩ q^* [x]` up to classes supported over `Z \ U_j`
(`ProjectiveBundleCoordClass.lean`), and the remainder is supported in a strictly smaller support.

## Main results

* `coordSupport_classes_mem_range`: the master statement of the double induction: every cycle
  of dimension `i` on `P(E ⊕ 1)` supported in `coordSupport j Z S₀` has class in the range of
  `θ_i`.
* `projectiveBundleMap_surjective`, `projectiveBundleMap_bijective`: the projective bundle map
  for `P(E ⊕ 1)` and `O(1)` is surjective, hence bijective.
* `projectiveBundleEquiv`: the resulting linear equivalence
  `⨁_{m = 0}^{r} A_{i + m - r}(X) ≃ₗ[ℚ] A_i(P(E ⊕ 1))`.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open GradedBundleData ChartedOverSubscheme RationalEquivalenceSystem.DescendingMap
  FiniteTypeDimension BundlePullbackGlobal
open GlobalBlowup (isAffineOpen)

/-! ## Generic bookkeeping for graded cycles -/

section Bookkeeping

variable {Y : Scheme.{u}} {dim : DimensionFunction Y} {i : ℤ}

/-- A finite combination of `pointProj`s at points of a subset is supported in that subset. -/
theorem sum_smul_pointProj_supportedIn {σ : Type*} (s : Finset σ) (c : σ → ℚ) (g : σ → Y)
    {C : Set Y} (hg : ∀ a ∈ s, g a ∈ C) :
    ((∑ a ∈ s, c a • cyclesOfDimension.pointProj dim i (g a) : cyclesOfDimension Y dim i) :
      AlgebraicCycle Y ℚ).SupportedIn C := by
  rw [Submodule.coe_sum]
  change _ ∈ AlgebraicCycle.supportedIn C
  refine Submodule.sum_mem _ fun a ha ↦ ?_
  rw [Submodule.coe_smul]
  refine Submodule.smul_mem _ _ ?_
  intro y hy
  rw [cyclesOfDimension.pointProj_apply] at hy
  by_cases h : g a = y ∧ dim y = i
  · rw [← h.1]
    exact hg a ha
  · exact absurd (if_neg h) hy

/-- The class of a graded cycle lying in `supportedRelations` vanishes. -/
theorem quotientMap_eq_zero_of_mem_supportedRelations [IsLocallyNoetherian Y]
    [NoetherianSpace Y] (C : Set Y) (ρ : cyclesOfDimension Y dim i)
    (hρ : (ρ : AlgebraicCycle Y ℚ) ∈ supportedRelations Y dim C) :
    (chowSystem dim i).quotientMap ρ = 0 := by
  change (Submodule.Quotient.mk ρ : (chowSystem dim i).ChowGroup) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change (ρ : AlgebraicCycle Y ℚ) ∈ totalRationalRelations Y dim
  exact supportedRelations_le_totalRationalRelations dim C hρ

/-- The open restriction of `pointProj` at a point of the image is `pointProj` at the preimage. -/
theorem pullbackOpen_pointProj {U : Scheme.{u}} (ψ : U ⟶ Y) [IsOpenImmersion ψ]
    {dimU : DimensionFunction U} (hdim : ∀ u, dimU u = dim (ψ.base u)) (a : U) :
    AlgebraicCycle.pullbackOpen ψ (cyclesOfDimension.pointProj dim i (ψ.base a) :
        AlgebraicCycle Y ℚ) =
      (cyclesOfDimension.pointProj dimU i a : AlgebraicCycle U ℚ) := by
  apply Function.locallyFinsuppWithin.ext
  intro b
  rw [AlgebraicCycle.pullbackOpen_apply, cyclesOfDimension.pointProj_apply,
    cyclesOfDimension.pointProj_apply, hdim b]
  by_cases hab : a = b
  · subst hab
    by_cases hd : dim (ψ.base a) = i
    · rw [if_pos ⟨rfl, hd⟩, if_pos ⟨rfl, hd⟩]
    · rw [if_neg (fun h ↦ hd h.2), if_neg (fun h ↦ hd h.2)]
  · rw [if_neg (fun h ↦ hab (ψ.isOpenEmbedding.injective h.1)), if_neg (fun h ↦ hab h.1)]

/-- A cycle whose restriction to an open immersion vanishes is supported in the complement of
the image. -/
theorem supportedIn_compl_range_of_pullbackOpen_eq_zero {U : Scheme.{u}} (ψ : U ⟶ Y)
    [IsOpenImmersion ψ] (z : AlgebraicCycle Y ℚ) (hz : AlgebraicCycle.pullbackOpen ψ z = 0) :
    z.SupportedIn (Set.range ψ.base)ᶜ := by
  rintro y hy ⟨a, rfl⟩
  refine hy ?_
  have := congrArg (fun c : AlgebraicCycle U ℚ ↦ (c : U → ℚ) a) hz
  exact this

/-- The open restriction of a cycle supported in `T` is supported in the preimage of `T`. -/
theorem pullbackOpen_supportedIn {U : Scheme.{u}} (ψ : U ⟶ Y) [IsOpenImmersion ψ]
    (z : AlgebraicCycle Y ℚ) {T : Set Y} (hz : z.SupportedIn T) :
    (AlgebraicCycle.pullbackOpen ψ z).SupportedIn (ψ.base ⁻¹' T) :=
  fun a ha ↦ hz (ψ.base a) ha

end Bookkeeping

/-! ## Standing assumptions -/

section Main

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] {ι : Type u} [Finite ι]
  (𝓔 : GradedBundleData X ι) [NoetherianSpace 𝓔.projectiveCompletion]
  (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))

/-! ### Placeholders for the concurrently proved inputs (to be replaced by imports) -/

section Placeholders

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] in
/-- PLACEHOLDER (COORD). The support used in the induction. -/
def coordSupport (j : 𝓔.bundle.J) (Z : Set X) (S₀ : Finset ι) : Set 𝓔.projectiveCompletion :=
  𝓔.completionToBase.base ⁻¹' (Z \ (𝓔.bundle.chart j).1) ∪
    {p | 𝓔.completionToBase.base p ∈ Z ∩ (𝓔.bundle.chart j).1 ∧
      ∀ s ∈ S₀, p ∉ Set.range (𝓔.completionChart (j, some s)).base}

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] in
/-- PLACEHOLDER (COORD, S-closed). -/
theorem isClosed_coordSupport (j : 𝓔.bundle.J) {Z : Set X} (hZ : IsClosed Z) (S₀ : Finset ι) :
    IsClosed (coordSupport 𝓔 j Z S₀) := by
  sorry

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] in
/-- PLACEHOLDER (COORD, S-empty). -/
theorem coordSupport_empty (j : 𝓔.bundle.J) (Z : Set X) :
    coordSupport 𝓔 j Z ∅ = 𝓔.completionToBase.base ⁻¹' Z := by
  sorry

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] in
/-- PLACEHOLDER (COORD, S-univ). -/
theorem coordSupport_subset_of_forall_mem (j : 𝓔.bundle.J) (Z : Set X) {S₀ : Finset ι}
    (hS : ∀ t, t ∈ S₀) :
    coordSupport 𝓔 j Z S₀ ⊆
      𝓔.completionToBase.base ⁻¹' (Z \ (𝓔.bundle.chart j).1) ∪
        Set.range (𝓔.completionChart (j, none)).base := by
  sorry

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] in
/-- PLACEHOLDER (COORD, S-mono in `Z`). -/
theorem coordSupport_mono (j : 𝓔.bundle.J) {Z Z' : Set X} (h : Z' ⊆ Z) (S₀ : Finset ι) :
    coordSupport 𝓔 j Z' S₀ ⊆ coordSupport 𝓔 j Z S₀ := by
  sorry

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] in
/-- PLACEHOLDER (COORD, S-mono in `S₀`). -/
theorem coordSupport_anti (j : 𝓔.bundle.J) (Z : Set X) {S₀ S₀' : Finset ι} (h : S₀ ⊆ S₀') :
    coordSupport 𝓔 j Z S₀' ⊆ coordSupport 𝓔 j Z S₀ := by
  sorry

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] in
/-- PLACEHOLDER (COORD, S-chart). -/
theorem preimage_completionChart_coordSupport (j : 𝓔.bundle.J) {Z : Set X} (hZ : IsClosed Z)
    (S₀ : Finset ι) {s : Option ι} (hs : s ∉ some '' (S₀ : Set ι)) :
    (𝓔.completionChart (j, s)).base ⁻¹' coordSupport 𝓔 j Z S₀ =
      PrimeSpectrum.zeroLocus (((chartIdeal 𝓔.bundle j Z).map
        (MvPolynomial.C : Γ(X, (𝓔.bundle.chart j).1) →+*
          MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1)) ⊔
        Ideal.span (MvPolynomial.X '' (S₀ : Set ι)) :
          Ideal (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))) :
            Set (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))) := by
  sorry

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] in
open Classical in
/-- PLACEHOLDER (COORD, S-rest). -/
theorem coordSupport_diff_range_subset (j : 𝓔.bundle.J) (Z : Set X) (S₀ : Finset ι) {t : ι}
    (ht : t ∉ S₀) :
    coordSupport 𝓔 j Z S₀ \ Set.range (𝓔.completionChart (j, some t)).base ⊆
      coordSupport 𝓔 j Z (insert t S₀) := by
  sorry

/-- PLACEHOLDER (COORD, A1.4): the class of a coordinate point. -/
theorem exists_coordPoint_class (j : 𝓔.bundle.J) {x : X} (hx : x ∈ (𝓔.bundle.chart j).1)
    (S₀ : Finset ι) {s : Option ι} (hs : s ∉ some '' (S₀ : Set ι)) :
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
  sorry

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] in
/-- PLACEHOLDER (AFF, A1.3): Fulton 1.9 on a coordinate subspace of a chart, with supports. -/
theorem exists_coordPullback_supported [NoetherianSpace X] (j : 𝓔.bundle.J) (s : Option ι)
    (I : Ideal Γ(X, (𝓔.bundle.chart j).1)) (S' : Finset ι) (i : ℤ)
    (z : cyclesOfDimension (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))))
      (dimensionFunction (𝓔.completionChart (j, s) ≫ (𝓔.completionToBase ≫ f))) i)
    (hz : (z : AlgebraicCycle
        (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1)))) ℚ).SupportedIn
      (PrimeSpectrum.zeroLocus ((I.map (MvPolynomial.C : Γ(X, (𝓔.bundle.chart j).1) →+*
          MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1)) ⊔
        Ideal.span (MvPolynomial.X '' (S' : Set ι)) :
          Ideal (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))) :
            Set (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))))) :
    haveI := noetherianSpace_of_isOpenImmersion (𝓔.chartBaseι j)
    ∃ w : AlgebraicCycle (Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1))) ℚ,
      (∀ 𝔭, dimensionFunction (𝓔.chartBaseι j ≫ f) 𝔭 ≠ i - ((Nat.card ι : ℤ) - S'.card) →
        (w : _ → ℚ) 𝔭 = 0) ∧
      w.SupportedIn (PrimeSpectrum.zeroLocus (I : Set Γ(X, (𝓔.bundle.chart j).1))) ∧
      (z : AlgebraicCycle _ ℚ) -
          ((∑ 𝔭 ∈ (finite_support_univ (X := Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1)))
              w).toFinset,
            (w : _ → ℚ) 𝔭 • cyclesOfDimension.pointProj
              (dimensionFunction (𝓔.completionChart (j, s) ≫ (𝓔.completionToBase ≫ f))) i
              (coordIdealPoint 𝔭.asIdeal (S' : Set ι)) : cyclesOfDimension _ _ i) :
            AlgebraicCycle _ ℚ) ∈
        supportedRelations _
          (dimensionFunction (𝓔.completionChart (j, s) ≫ (𝓔.completionToBase ≫ f)))
          (PrimeSpectrum.zeroLocus ((I.map (MvPolynomial.C : Γ(X, (𝓔.bundle.chart j).1) →+*
              MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1)) ⊔
            Ideal.span (MvPolynomial.X '' (S' : Set ι)) :
              Ideal (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))) :
                Set (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1)))) := by
  sorry

end Placeholders

/-! ### The range of the projective bundle map -/

section Range

/-- `ClassesInRange f 𝓔 hX C`: every graded cycle on `P(E ⊕ 1)` supported in the subset `C`
has class in the range of the projective bundle map (in its dimension). -/
def ClassesInRange (C : Set 𝓔.projectiveCompletion) : Prop :=
  ∀ (i : ℤ) (z : cyclesOfDimension 𝓔.projectiveCompletion
      (dimensionFunction (𝓔.completionToBase ≫ f)) i),
    (z : AlgebraicCycle 𝓔.projectiveCompletion ℚ).SupportedIn C →
      (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) i).quotientMap z ∈
        LinearMap.range (projectiveBundleMap 𝓔.completionCharts f
          (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i)

/-- `ClassesInRange` is monotone in the subset. -/
theorem ClassesInRange.mono {C C' : Set 𝓔.projectiveCompletion} (h : ClassesInRange f 𝓔 hX C)
    (hC : C' ⊆ C) : ClassesInRange f 𝓔 hX C' :=
  fun i z hz ↦ h i z (hz.mono hC)

/-- `chowCast` preserves membership in the range of the projective bundle map. -/
theorem chowCast_mem_range_projectiveBundleMap {d i : ℤ} (h : d = i)
    (x : (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) d).ChowGroup)
    (hx : x ∈ LinearMap.range (projectiveBundleMap 𝓔.completionCharts f
      (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) d)) :
    chowCast h x ∈ LinearMap.range (projectiveBundleMap 𝓔.completionCharts f
      (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i) := by
  subst h
  exact hx

/-- The summand `c₁(O(1))^m ∩ q^* α` of the projective bundle map lies in its range. -/
theorem c1Iter_chowPullbackCharted_mem_range (i : ℤ) (m : Fin (Nat.card ι + 1))
    (α : (chowSystem (dimensionFunction f) (i + ((m : ℕ) : ℤ) - Nat.card ι)).ChowGroup) :
    c1Iter (𝓔.completionToBase ≫ f) (𝓔.tautological hX) m i (chowCast (by ring)
      (chowPullbackCharted 𝓔.completionCharts (dimensionFunction f)
        (dimensionFunction (𝓔.completionToBase ≫ f))
        (𝓔.dimensionFunction_fibrePoint_completionCharts f) (i + ((m : ℕ) : ℤ) - Nat.card ι)
        (chowSystem _ _) (chowSystem _ _) α)) ∈
      LinearMap.range (projectiveBundleMap 𝓔.completionCharts f
        (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i) := by
  classical
  refine ⟨Pi.single m α, ?_⟩
  rw [projectiveBundleMap_apply, Finset.sum_eq_single m]
  · rw [Pi.single_eq_same]
  · intro m' _ hm'
    rw [Pi.single_eq_of_ne hm', map_zero, map_zero, map_zero]
  · intro h
    exact absurd (Finset.mem_univ m) h

/-- The summand `c₁(O(1))^m ∩ q^* α`, `m ≤ r`, `α ∈ A_{i + m - r}(X)`, lies in the range of the
projective bundle map, for an arbitrary spelling of the degree. -/
theorem c1Iter_chowPullbackCharted_mem_range' (i : ℤ) (m : ℕ) (hm : m ≤ Nat.card ι) {l : ℤ}
    (hl : l = i + m - Nat.card ι) (h : l + Nat.card ι = i + m)
    (α : (chowSystem (dimensionFunction f) l).ChowGroup) :
    c1Iter (𝓔.completionToBase ≫ f) (𝓔.tautological hX) m i (chowCast h
      (chowPullbackCharted 𝓔.completionCharts (dimensionFunction f)
        (dimensionFunction (𝓔.completionToBase ≫ f))
        (𝓔.dimensionFunction_fibrePoint_completionCharts f) l
        (chowSystem _ _) (chowSystem _ _) α)) ∈
      LinearMap.range (projectiveBundleMap 𝓔.completionCharts f
        (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i) := by
  subst hl
  exact c1Iter_chowPullbackCharted_mem_range f 𝓔 hX i ⟨m, by omega⟩ α

end Range

/-! ### Coordinate points over a chart -/

section CoordPoints

omit [Infinite k] [Finite ι] [NoetherianSpace 𝓔.projectiveCompletion] in
/-- Every point of `Spec Γ(U_j)` is the prime of its image in `U_j`. -/
theorem exists_chartBasePoint_eq (j : 𝓔.bundle.J)
    (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1)))) :
    ∃ hx : (𝓔.chartBaseι j).base 𝔭 ∈ (𝓔.bundle.chart j).1,
      𝓔.bundle.chartBasePoint j ⟨(𝓔.chartBaseι j).base 𝔭, hx⟩ = 𝔭 := by
  have hmem : (𝓔.chartBaseι j).base 𝔭 ∈ (𝓔.bundle.chart j).1 := by
    change _ ∈ ((𝓔.bundle.chart j).1 : Set X)
    rw [← range_chartε 𝓔.bundle j]
    exact ⟨𝔭, rfl⟩
  refine ⟨hmem, ?_⟩
  have h : (⟨(𝓔.chartBaseι j).base 𝔭, hmem⟩ : (𝓔.bundle.chart j).1.toScheme) =
      (isAffineOpen X (𝓔.bundle.chart j)).isoSpec.inv.base 𝔭 := Subtype.ext rfl
  change (isAffineOpen X (𝓔.bundle.chart j)).isoSpec.hom.base _ = 𝔭
  rw [h]
  change ((isAffineOpen X (𝓔.bundle.chart j)).isoSpec.inv ≫
    (isAffineOpen X (𝓔.bundle.chart j)).isoSpec.hom).base 𝔭 = 𝔭
  rw [Iso.inv_hom_id]
  rfl

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] in
/-- The dimension of the coordinate point over an arbitrary point `𝔭` of the chart `Spec Γ(U_j)`:
`dim (chartBaseι 𝔭) + r - |S₀|`. -/
theorem dimensionFunction_coordPoint_chartBaseι (j : 𝓔.bundle.J)
    (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1)))) (S₀ : Finset ι) {s : Option ι}
    (hs : s ∉ some '' (S₀ : Set ι)) :
    dimensionFunction (𝓔.completionToBase ≫ f) (𝓔.coordPoint j 𝔭 (some '' (S₀ : Set ι)) s) =
      dimensionFunction f ((𝓔.chartBaseι j).base 𝔭) + (Nat.card ι : ℤ) - S₀.card := by
  obtain ⟨hx, h𝔭⟩ := exists_chartBasePoint_eq 𝓔 j 𝔭
  have := 𝓔.dimensionFunction_coordPoint f j hx S₀ hs
  rw [h𝔭] at this
  exact this

omit [Infinite k] [Finite ι] [NoetherianSpace 𝓔.projectiveCompletion] in
/-- The coordinate point is the image under the chart `(j, s)`, `s ∉ some '' S₀`, of the
coordinate prime `coordIdealPoint 𝔭 S₀`. -/
theorem coordPoint_eq_completionChart_coordIdealPoint (j : 𝓔.bundle.J)
    (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1)))) (S₀ : Finset ι) {s : Option ι}
    (hs : s ∉ some '' (S₀ : Set ι)) :
    𝓔.coordPoint j 𝔭 (some '' (S₀ : Set ι)) s =
      (𝓔.completionChart (j, s)).base (coordIdealPoint 𝔭.asIdeal (S₀ : Set ι)) := by
  rw [coordPoint_eq_completionChart]
  congr 2
  cases s with
  | none => exact chartSet_none_image _
  | some t => exact chartSet_some_image _ (fun ht ↦ hs ⟨t, ht, rfl⟩)

/-- **The class of a coordinate point lies in the range of the projective bundle map**, modulo
classes supported over `Z \ U_j`: for `𝔭` a point of the chart `Spec Γ(U_j)` over a point of
the closed subset `Z`, the class of `coordPoint j 𝔭 (some '' S₀) s` is in the range as soon as
all classes supported in `q⁻¹(Z \ U_j)` are. -/
theorem quotientMap_point_coordPoint_mem_range (j : 𝓔.bundle.J) {Z : Set X} (hZ : IsClosed Z)
    (S₀ : Finset ι) {s : Option ι} (hs : s ∉ some '' (S₀ : Set ι)) {x : X}
    (hx : x ∈ (𝓔.bundle.chart j).1) (hxZ : x ∈ Z)
    (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1))))
    (h𝔭 : 𝔭 = 𝓔.bundle.chartBasePoint j ⟨x, hx⟩) {i : ℤ}
    (hd : dimensionFunction (𝓔.completionToBase ≫ f)
      (𝓔.coordPoint j 𝔭 (some '' (S₀ : Set ι)) s) = i)
    (hZ' : ClassesInRange f 𝓔 hX
      (𝓔.completionToBase.base ⁻¹' (Z \ (𝓔.bundle.chart j).1))) :
    (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) i).quotientMap
        (cyclesOfDimension.point (𝓔.coordPoint j 𝔭 (some '' (S₀ : Set ι)) s) hd) ∈
      LinearMap.range (projectiveBundleMap 𝓔.completionCharts f
        (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i) := by
  subst h𝔭
  have hd' : dimensionFunction f x + (Nat.card ι : ℤ) - S₀.card = i :=
    (𝓔.dimensionFunction_coordPoint f j hx S₀ hs).symm.trans hd
  obtain ⟨ε, hεsupp, hε⟩ := exists_coordPoint_class f 𝓔 hX j hx S₀ hs
  have hcast := congrArg (chowCast hd') hε
  rw [chowCast_quotientMap, cyclesCast_point, map_add, chowCast_quotientMap] at hcast
  rw [hcast]
  refine Submodule.add_mem _ ?_ ?_
  · refine chowCast_mem_range_projectiveBundleMap f 𝓔 hX hd' _ ?_
    have := Fintype.ofFinite ι
    exact c1Iter_chowPullbackCharted_mem_range' f 𝓔 hX _ S₀.card
      (by rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ S₀) (by ring) _ _
  · refine hZ' _ _ ?_
    rw [cyclesCast_coe]
    refine hεsupp.mono (Set.preimage_mono (Set.sdiff_subset_sdiff_left ?_))
    exact closure_minimal (Set.singleton_subset_iff.2 hxZ) hZ

end CoordPoints

/-! ### The chart step of the induction -/

section Step

variable [NoetherianSpace X]

/-- **The chart step of the double induction.** Let `Z ⊆ X` be closed, `j` a chart index,
`S₀ ⊆ ι` a finite set of coordinates and `s ∉ some '' S₀` the index of a chart `(j, s)` of
`P(E ⊕ 1)`.  If every class supported in `coordSupport j Z S₀` minus the chart `(j, s)` lies in
the range of the projective bundle map, and so does every class supported over `Z \ U_j`, then
every class supported in `coordSupport j Z S₀` lies in the range.

Proof: restrict to the chart, apply Fulton 1.9 on the coordinate subspace (`AFF`), extend the
relation by closure, write the coordinate points as `c₁(O(1))^{|S₀|} ∩ q^* [x]` up to classes
over `Z \ U_j` (`COORD`), and note that the remainder restricts to zero on the chart. -/
theorem classesInRange_coordSupport_step (Z : Closeds X) (j : 𝓔.bundle.J) (S₀ : Finset ι)
    {s : Option ι} (hs : s ∉ some '' (S₀ : Set ι))
    (hrest : ClassesInRange f 𝓔 hX
      (coordSupport 𝓔 j Z S₀ \ Set.range (𝓔.completionChart (j, s)).base))
    (hZ' : ClassesInRange f 𝓔 hX
      (𝓔.completionToBase.base ⁻¹' ((Z : Set X) \ (𝓔.bundle.chart j).1))) :
    ClassesInRange f 𝓔 hX (coordSupport 𝓔 j Z S₀) := by
  have _ := LocallyOfFiniteType.isLocallyNoetherian f
  have _ := 𝓔.isLocallyNoetherian_projectiveCompletion f
  have _ := noetherianSpace_of_isOpenImmersion (𝓔.chartBaseι j)
  intro i z hz
  -- dimension functions
  have hdimA : ∀ a, dimensionFunction (𝓔.completionChart (j, s) ≫ (𝓔.completionToBase ≫ f)) a =
      dimensionFunction (𝓔.completionToBase ≫ f) ((𝓔.completionChart (j, s)).base a) :=
    fun a ↦ dimensionFunction_comp (𝓔.completionToBase ≫ f) (𝓔.completionChart (j, s)) a
  have hdimR : ∀ 𝔭, dimensionFunction (𝓔.chartBaseι j ≫ f) 𝔭 =
      dimensionFunction f ((𝓔.chartBaseι j).base 𝔭) :=
    fun 𝔭 ↦ dimensionFunction_comp f (𝓔.chartBaseι j) 𝔭
  -- the restriction of `z` to the chart `(j, s)`
  set zs := cyclesOfDimension.flatPullbackOpen (i := i) (𝓔.completionChart (j, s)) hdimA z
    with hzs_def
  have hzs := pullbackOpen_supportedIn (𝓔.completionChart (j, s)) _ hz
  rw [preimage_completionChart_coordSupport 𝓔 j Z.isClosed S₀ hs] at hzs
  obtain ⟨w, hwdim, hwsupp, hwrel⟩ :=
    exists_coordPullback_supported f 𝓔 j s (chartIdeal 𝓔.bundle j Z) S₀ i zs hzs
  set sw := (finite_support_univ w).toFinset with hsw_def
  have hmem_sw : ∀ 𝔭, 𝔭 ∈ sw ↔ (w : _ → ℚ) 𝔭 ≠ 0 := fun 𝔭 ↦ by
    rw [hsw_def, Set.Finite.mem_toFinset, Function.mem_support]
  -- the coordinate points over the support of `w`
  have hgdim : ∀ 𝔭 ∈ sw, dimensionFunction (𝓔.completionToBase ≫ f)
      (𝓔.coordPoint j 𝔭 (some '' (S₀ : Set ι)) s) = i := by
    intro 𝔭 h𝔭
    rw [dimensionFunction_coordPoint_chartBaseι f 𝓔 j 𝔭 S₀ hs, ← hdimR]
    have hw : dimensionFunction (𝓔.chartBaseι j ≫ f) 𝔭 = i - ((Nat.card ι : ℤ) - S₀.card) := by
      by_contra h'
      exact (hmem_sw 𝔭).1 h𝔭 (hwdim 𝔭 h')
    omega
  have hgZ : ∀ 𝔭 ∈ sw, (𝓔.chartBaseι j).base 𝔭 ∈ (Z : Set X) := by
    intro 𝔭 h𝔭
    have := hwsupp 𝔭 ((hmem_sw 𝔭).1 h𝔭)
    rw [zeroLocus_chartIdeal 𝓔.bundle j Z.isClosed] at this
    exact this
  have hgU : ∀ 𝔭, (𝓔.chartBaseι j).base 𝔭 ∈ (𝓔.bundle.chart j).1 :=
    fun 𝔭 ↦ (exists_chartBasePoint_eq 𝓔 j 𝔭).1
  have hgC : ∀ 𝔭 ∈ sw, 𝓔.coordPoint j 𝔭 (some '' (S₀ : Set ι)) s ∈ coordSupport 𝓔 j Z S₀ := by
    intro 𝔭 h𝔭
    refine Or.inr ⟨?_, ?_⟩
    · rw [completionToBase_coordPoint]
      exact ⟨hgZ 𝔭 h𝔭, hgU 𝔭⟩
    · intro u hu
      rw [coordPoint_mem_range_completionChart_iff 𝓔 j 𝔭 _ hs (some u)]
      exact fun h ↦ h ⟨u, hu, rfl⟩
  set ζ : cyclesOfDimension 𝓔.projectiveCompletion (dimensionFunction (𝓔.completionToBase ≫ f))
      i := ∑ 𝔭 ∈ sw, (w : _ → ℚ) 𝔭 • cyclesOfDimension.pointProj
        (dimensionFunction (𝓔.completionToBase ≫ f)) i (𝓔.coordPoint j 𝔭 (some '' (S₀ : Set ι)) s)
    with hζ_def
  have hζsupp : (ζ : AlgebraicCycle 𝓔.projectiveCompletion ℚ).SupportedIn
      (coordSupport 𝓔 j Z S₀) :=
    sum_smul_pointProj_supportedIn sw _ _ hgC
  set ζA : cyclesOfDimension (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1))))
      (dimensionFunction (𝓔.completionChart (j, s) ≫ (𝓔.completionToBase ≫ f))) i :=
    ∑ 𝔭 ∈ sw, (w : _ → ℚ) 𝔭 • cyclesOfDimension.pointProj
      (dimensionFunction (𝓔.completionChart (j, s) ≫ (𝓔.completionToBase ≫ f))) i
      (coordIdealPoint 𝔭.asIdeal (S₀ : Set ι)) with hζA_def
  have hζres : AlgebraicCycle.pullbackOpen (𝓔.completionChart (j, s))
      (ζ : AlgebraicCycle 𝓔.projectiveCompletion ℚ) = (ζA : AlgebraicCycle _ ℚ) := by
    rw [hζ_def, hζA_def, Submodule.coe_sum, Submodule.coe_sum,
      ← AlgebraicCycle.pullbackOpenLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun 𝔭 _ ↦ ?_
    rw [Submodule.coe_smul, Submodule.coe_smul, map_smul, AlgebraicCycle.pullbackOpenLinear_apply,
      coordPoint_eq_completionChart_coordIdealPoint 𝓔 j 𝔭 S₀ hs, pullbackOpen_pointProj _ hdimA]
  -- the relation, extended by closure and projected to dimension `i`
  have hρrel : ((zs - ζA : cyclesOfDimension _ _ i) : AlgebraicCycle _ ℚ) ∈
      supportedRelations _ (dimensionFunction (𝓔.completionChart (j, s) ≫
        (𝓔.completionToBase ≫ f)))
        ((𝓔.completionChart (j, s)).base ⁻¹' coordSupport 𝓔 j Z S₀) := by
    rw [preimage_completionChart_coordSupport 𝓔 j Z.isClosed S₀ hs, Submodule.coe_sub]
    exact hwrel
  obtain ⟨ρ', hρ'mem, hρ'res⟩ := exists_supportedRelations_pullbackOpen
    (𝓔.completionChart (j, s)) (dimensionFunction (𝓔.completionToBase ≫ f))
    (dimensionFunction (𝓔.completionChart (j, s) ≫ (𝓔.completionToBase ≫ f)))
    (isClosed_coordSupport 𝓔 j Z.isClosed S₀) (Set.image_preimage_subset _ _) _ hρrel
  set ρi : cyclesOfDimension 𝓔.projectiveCompletion (dimensionFunction (𝓔.completionToBase ≫ f))
    i := cyclesOfDimension.project ρ' with hρi_def
  have hρimem : (ρi : AlgebraicCycle 𝓔.projectiveCompletion ℚ) ∈
      supportedRelations _ (dimensionFunction (𝓔.completionToBase ≫ f))
        (coordSupport 𝓔 j Z S₀) :=
    project_mem_supportedRelations_of_homogeneous
      (principalDivisorsHomogeneous (𝓔.completionToBase ≫ f)) _ ρ' hρ'mem
  have hρires : AlgebraicCycle.pullbackOpen (𝓔.completionChart (j, s))
      (ρi : AlgebraicCycle 𝓔.projectiveCompletion ℚ) =
      ((zs - ζA : cyclesOfDimension _ _ i) : AlgebraicCycle _ ℚ) := by
    rw [hρi_def, pullbackOpen_project (𝓔.completionChart (j, s))
      (dimensionFunction (𝓔.completionToBase ≫ f))
      (dimensionFunction (𝓔.completionChart (j, s) ≫ (𝓔.completionToBase ≫ f))) hdimA i ρ',
      hρ'res]
    exact congrArg Subtype.val (cyclesOfDimension.project_coe _)
  -- the remainder, supported in `coordSupport j Z S₀` minus the chart
  set δ : cyclesOfDimension 𝓔.projectiveCompletion (dimensionFunction (𝓔.completionToBase ≫ f))
    i := z - ζ - ρi with hδ_def
  have hδres : AlgebraicCycle.pullbackOpen (𝓔.completionChart (j, s))
      (δ : AlgebraicCycle 𝓔.projectiveCompletion ℚ) = 0 := by
    have hz' : AlgebraicCycle.pullbackOpen (𝓔.completionChart (j, s))
        (z : AlgebraicCycle 𝓔.projectiveCompletion ℚ) = (zs : AlgebraicCycle _ ℚ) := rfl
    rw [hδ_def, Submodule.coe_sub, Submodule.coe_sub, ← AlgebraicCycle.pullbackOpenLinear_apply,
      map_sub, map_sub, AlgebraicCycle.pullbackOpenLinear_apply,
      AlgebraicCycle.pullbackOpenLinear_apply, AlgebraicCycle.pullbackOpenLinear_apply, hz',
      hζres, hρires, Submodule.coe_sub]
    abel
  have hδsupp : (δ : AlgebraicCycle 𝓔.projectiveCompletion ℚ).SupportedIn
      (coordSupport 𝓔 j Z S₀ \ Set.range (𝓔.completionChart (j, s)).base) := by
    intro p hp
    refine ⟨?_, ?_⟩
    · have hsupp : (δ : AlgebraicCycle 𝓔.projectiveCompletion ℚ).SupportedIn
          (coordSupport 𝓔 j Z S₀) := by
        rw [hδ_def, Submodule.coe_sub, Submodule.coe_sub]
        exact (hz.sub hζsupp).sub (supportedRelations_le_supportedIn _ _ hρimem)
      exact hsupp p hp
    · exact supportedIn_compl_range_of_pullbackOpen_eq_zero (𝓔.completionChart (j, s)) _ hδres
        p hp
  have hδ := hrest i δ hδsupp
  -- the class of the coordinate points
  have hζ : (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) i).quotientMap ζ ∈
      LinearMap.range (projectiveBundleMap 𝓔.completionCharts f
        (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i) := by
    rw [hζ_def, map_sum]
    refine Submodule.sum_mem _ fun 𝔭 h𝔭 ↦ ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    rw [cyclesOfDimension.pointProj_eq_point (hgdim 𝔭 h𝔭)]
    obtain ⟨hx, h𝔭x⟩ := exists_chartBasePoint_eq 𝓔 j 𝔭
    exact quotientMap_point_coordPoint_mem_range f 𝓔 hX j Z.isClosed S₀ hs hx (hgZ 𝔭 h𝔭) 𝔭
      h𝔭x.symm (hgdim 𝔭 h𝔭) hZ'
  -- assembling
  have hsum : (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) i).quotientMap z =
      (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) i).quotientMap ζ +
        (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) i).quotientMap δ +
        (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) i).quotientMap ρi := by
    rw [hδ_def, map_sub, map_sub]
    abel
  rw [hsum, quotientMap_eq_zero_of_mem_supportedRelations _ ρi hρimem, add_zero]
  exact Submodule.add_mem _ hζ hδ

end Step

/-! ### The double induction -/

section Induction

variable [NoetherianSpace X]

omit [Infinite k] [NoetherianSpace X] [NoetherianSpace 𝓔.projectiveCompletion] in
/-- `coordSupport j Z S₀` lies over `Z`. -/
theorem coordSupport_subset_preimage (j : 𝓔.bundle.J) (Z : Set X) (S₀ : Finset ι) :
    coordSupport 𝓔 j Z S₀ ⊆ 𝓔.completionToBase.base ⁻¹' Z := by
  rw [← coordSupport_empty 𝓔 j Z]
  exact coordSupport_anti 𝓔 j Z (Finset.empty_subset S₀)

/-- **The inner induction** (descending on `S₀`): for a closed `Z ⊆ X` and a chart `j`, if every
class supported over `Z \ U_j` lies in the range of the projective bundle map, then so does every
class supported in `coordSupport j Z S₀`, for every `S₀`. -/
theorem classesInRange_coordSupport_of_diff (Z : Closeds X) (j : 𝓔.bundle.J)
    (hZ' : ClassesInRange f 𝓔 hX
      (𝓔.completionToBase.base ⁻¹' ((Z : Set X) \ (𝓔.bundle.chart j).1)))
    (S₀ : Finset ι) : ClassesInRange f 𝓔 hX (coordSupport 𝓔 j Z S₀) := by
  classical
  have _ := Fintype.ofFinite ι
  -- the case of a set of coordinates containing everything: the chart `(j, none)`
  have hfull : ∀ S₀ : Finset ι, (∀ t, t ∈ S₀) →
      ClassesInRange f 𝓔 hX (coordSupport 𝓔 j Z S₀) := by
    intro S₀ hall
    have hnone : (none : Option ι) ∉ some '' (S₀ : Set ι) :=
      fun ⟨_, _, h⟩ ↦ Option.some_ne_none _ h
    have hrest : ClassesInRange f 𝓔 hX
        (coordSupport 𝓔 j Z S₀ \ Set.range (𝓔.completionChart (j, none)).base) := by
      refine ClassesInRange.mono f 𝓔 hX hZ' ?_
      intro p hp
      rcases coordSupport_subset_of_forall_mem 𝓔 j Z hall hp.1 with h | h
      · exact h
      · exact absurd h hp.2
    exact classesInRange_coordSupport_step f 𝓔 hX Z j S₀ hnone hrest hZ'
  suffices h : ∀ n : ℕ, ∀ S₀ : Finset ι, Fintype.card ι ≤ S₀.card + n →
      ClassesInRange f 𝓔 hX (coordSupport 𝓔 j Z S₀) from
    h (Fintype.card ι) S₀ (by omega)
  intro n
  induction n with
  | zero =>
    intro S₀ hS₀
    refine hfull S₀ fun t ↦ ?_
    have : S₀ = Finset.univ :=
      Finset.eq_univ_of_card S₀ (le_antisymm (Finset.card_le_univ S₀) (by simpa using hS₀))
    rw [this]
    exact Finset.mem_univ t
  | succ n ih =>
    intro S₀ hS₀
    by_cases hall : ∀ t, t ∈ S₀
    · exact hfull S₀ hall
    · obtain ⟨t, ht⟩ := not_forall.mp hall
      refine classesInRange_coordSupport_step f 𝓔 hX Z j S₀ (s := some t)
        (fun ⟨u, hu, h⟩ ↦ ht (Option.some_injective _ h ▸ hu)) ?_ hZ'
      refine ClassesInRange.mono f 𝓔 hX (ih (insert t S₀) ?_)
        (coordSupport_diff_range_subset 𝓔 j Z S₀ ht)
      rw [Finset.card_insert_of_notMem ht]
      omega

/-- **The master statement of the double induction** (Noetherian induction on the closed subset
`Z ⊆ X`, descending induction on `S₀`): every graded cycle on `P(E ⊕ 1)` supported in
`coordSupport j Z S₀` has class in the range of the projective bundle map. -/
theorem coordSupport_classes_mem_range (Z : Closeds X) (j : 𝓔.bundle.J) (S₀ : Finset ι) :
    ClassesInRange f 𝓔 hX (coordSupport 𝓔 j Z S₀) := by
  induction Z using WellFoundedLT.induction generalizing j S₀ with
  | _ Z ih =>
  by_cases hZ : (Z : Set X) = ∅
  · intro i z hz
    have hz0 : z = 0 := by
      apply Subtype.ext
      apply Function.locallyFinsuppWithin.ext
      intro p
      by_contra hne
      have hmem := coordSupport_subset_preimage 𝓔 j Z S₀ (hz p hne)
      rw [hZ] at hmem
      exact hmem
    rw [hz0, map_zero]
    exact Submodule.zero_mem _
  · obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.2 hZ
    set j₀ := chartIndex 𝓔.bundle x₀ with hj₀_def
    have hx₀U : x₀ ∈ (𝓔.bundle.chart j₀).1 := mem_chart_chartIndex 𝓔.bundle x₀
    let Z' : Closeds X :=
      ⟨(Z : Set X) \ (𝓔.bundle.chart j₀).1, Z.isClosed.sdiff (𝓔.bundle.chart j₀).1.isOpen⟩
    have hle : Z' ≤ Z := fun x hx ↦ hx.1
    have hne : Z' ≠ Z := by
      intro hcon
      have hx₀' : x₀ ∈ (Z' : Set X) := by
        rw [hcon]
        exact hx₀
      exact hx₀'.2 hx₀U
    have hZ' : ClassesInRange f 𝓔 hX
        (𝓔.completionToBase.base ⁻¹' ((Z : Set X) \ (𝓔.bundle.chart j₀).1)) := by
      have := ih Z' (lt_of_le_of_ne hle hne) j₀ ∅
      rwa [coordSupport_empty] at this
    refine ClassesInRange.mono f 𝓔 hX (classesInRange_coordSupport_of_diff f 𝓔 hX Z j₀ hZ' ∅) ?_
    rw [coordSupport_empty]
    exact coordSupport_subset_preimage 𝓔 j Z S₀

end Induction

end Main

/-! ## Surjectivity and bijectivity of the projective bundle map -/

section Final

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [NoetherianSpace X] {ι : Type u} [Finite ι]
  (𝓔 : GradedBundleData X ι) (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))

/-- **The surjectivity half of the projective bundle formula** (Fulton, Theorem 3.3(b),
surjectivity) for `P(E ⊕ 1)`: the map `⨁_{m = 0}^{r} A_{i + m - r}(X) → A_i(P(E ⊕ 1))`,
`(α_m)_m ↦ ∑_m c₁(O(1))^m ∩ q^* α_m`, is surjective. -/
theorem projectiveBundleMap_surjective (i : ℤ) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    Function.Surjective (projectiveBundleMap 𝓔.completionCharts f
      (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i) := by
  have := 𝓔.noetherianSpace_projectiveCompletion f
  intro β
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ β
  change (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) i).quotientMap z ∈
    LinearMap.range (projectiveBundleMap 𝓔.completionCharts f
      (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i)
  rcases isEmpty_or_nonempty X with hX0 | ⟨⟨x₀⟩⟩
  · -- `X` is empty, hence so is `P(E ⊕ 1)` and every cycle vanishes
    have hz0 : z = 0 := by
      apply Subtype.ext
      apply Function.locallyFinsuppWithin.ext
      intro p
      exact (hX0.false (𝓔.completionToBase.base p)).elim
    rw [hz0, map_zero]
    exact Submodule.zero_mem _
  · refine coordSupport_classes_mem_range f 𝓔 hX ⊤ (chartIndex 𝓔.bundle x₀) ∅ i z ?_
    intro p _
    rw [coordSupport_empty]
    exact Set.mem_univ _

/-- **The projective bundle formula** (Fulton, Theorem 3.3(b)) for `P(E ⊕ 1)`: the map
`⨁_{m = 0}^{r} A_{i + m - r}(X) → A_i(P(E ⊕ 1))`, `(α_m)_m ↦ ∑_m c₁(O(1))^m ∩ q^* α_m`, is
bijective. -/
theorem projectiveBundleMap_bijective (i : ℤ) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    Function.Bijective (projectiveBundleMap 𝓔.completionCharts f
      (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i) :=
  have := 𝓔.noetherianSpace_projectiveCompletion f
  ⟨projectiveBundleMap_injective f 𝓔 hX i, projectiveBundleMap_surjective f 𝓔 hX i⟩

/-- **The projective bundle formula as a linear equivalence**
`⨁_{m = 0}^{r} A_{i + m - r}(X) ≃ₗ[ℚ] A_i(P(E ⊕ 1))`, induced by the projective bundle map. -/
noncomputable def projectiveBundleEquiv (i : ℤ) :
    (∀ m : Fin (Nat.card ι + 1),
      (chowSystem (dimensionFunction f) (i + ((m : ℕ) : ℤ) - Nat.card ι)).ChowGroup) ≃ₗ[ℚ]
      (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) i).ChowGroup :=
  haveI := 𝓔.noetherianSpace_projectiveCompletion f
  LinearEquiv.ofBijective (projectiveBundleMap 𝓔.completionCharts f
    (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i)
    (projectiveBundleMap_bijective f 𝓔 hX i)

/-- The projective bundle equivalence is the projective bundle map. -/
theorem projectiveBundleEquiv_apply (i : ℤ) (α : ∀ m : Fin (Nat.card ι + 1),
    (chowSystem (dimensionFunction f) (i + ((m : ℕ) : ℤ) - Nat.card ι)).ChowGroup) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    projectiveBundleEquiv f 𝓔 hX i α = projectiveBundleMap 𝓔.completionCharts f
      (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i α :=
  rfl

end Final

end GromovWitten.AlgebraicGeometry.IntersectionTheory
