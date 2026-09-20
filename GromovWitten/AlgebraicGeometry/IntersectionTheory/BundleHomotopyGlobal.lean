/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyClosed
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackGlobalChow
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackFundamental
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FiniteTypeDimension
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalizationExact
import GromovWitten.AlgebraicGeometry.IntersectionTheory.SupportedCycles

/-!
# Global surjectivity of the flat pullback along a vector bundle

This file globalises **Fulton, *Intersection Theory*, Proposition 1.9** (surjectivity of `π^*`)
from an affine base to an arbitrary Noetherian base, by Noetherian induction on the closed subset
of the base over which a cycle of the total space is supported.

## Contents

* `AlgebraicCycle.pullbackOpen_map_comp_iso`, `IntegralClosedSubscheme.transportIso`,
  `RationalFunctionGenerator.transportIso`, `pullbackOpen_divisor_transportIso`: transport of
  integral closed subschemes, of principal-divisor generators and of their divisors along an
  isomorphism.
* `exists_supportedRelations_pullbackOpen`: every rational relation supported in a subset of an
  open subscheme is the restriction of a rational relation supported in a closed subset of the
  ambient scheme containing the image (the closure step, through
  `RationalFunctionGenerator.closureIn`).
* `divisor_supportedIn`, `supportedRelations_le_supportedIn`,
  `project_mem_supportedRelations_of_homogeneous`: supports and grading of the relations
  supported in a subset.
* `chartε`, `chartπ`: the chart of the base read as `Spec Γ(X, U_j)` and the projection of the
  trivialised chart `Spec (MvPolynomial ι Γ(X, U_j))` of the total space onto it.
* `extendChart`: extension by zero of a cycle from a chart of the base to `X`; `chartIdeal` and
  `pullbackOpen_chartι_supportedIn`: the trace on a chart of a closed subset of the base.
* `BundlePullbackGlobal.exists_pullback_supported`: **Fulton, Proposition 1.9 with supports**, by
  Noetherian induction on the closed subset of the base over which the cycle lives, with the
  affine statement `VectorBundle.exists_pullback_supported` as the input on each chart.
* `BundlePullbackGlobal.exists_pullback_eq`, `chowPullbackBundleGlobal_surjective`,
  `exists_chowPullbackBundleGlobal_eq`: the cycle-level and Chow-group-level surjectivity of the
  global flat pullback.
* `BundlePullbackGlobal.chowPullbackBundleFiniteType_surjective` and
  `mem_range_chowPullbackBundleFiniteType`: the same for a bundle over a compact scheme locally
  of finite type over a field, where all the hypotheses are automatic.  This is the map
  `bundlePullbackFT` of `VirtualFundamentalClass/GlobalVirtualClass.lean`, so the second theorem
  is exactly the hypothesis `hmem` of `virtualClassFT`.

## Hypotheses

The general theorems carry the dimension functions of the charts (`dimChart`, `dimChartE`) and
their compatibilities with the dimension functions of the base and the total space as explicit
hypotheses, because a `DimensionFunction` does not restrict to an open subscheme in general;
they also carry the universal dimension formula of the chart rings and homogeneity of the
principal divisors on the total space.  In the finite-type case over a field all of these are
discharged.  Compactness of `X` is assumed throughout (Noetherian induction needs a Noetherian
space).
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Order

open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace

open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

/-- A locally Noetherian scheme with compact underlying space has a Noetherian underlying
space. -/
instance (priority := 100) noetherianSpace_of_isLocallyNoetherian (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] : NoetherianSpace X :=
  have : _root_.AlgebraicGeometry.IsNoetherian X := ⟨⟩
  inferInstance

/-- The residue-degree pushforward along a closed immersion composed with an isomorphism, read
back through the isomorphism, is the pushforward along the closed immersion. -/
theorem AlgebraicCycle.pullbackOpen_map_comp_iso {S W W' : Scheme.{u}} (incl : S ⟶ W)
    [_root_.AlgebraicGeometry.IsClosedImmersion incl] (e : W ≅ W') (wW : W → ℤ) (wW' : W' → ℤ)
    (c : AlgebraicCycle S ℚ) :
    AlgebraicCycle.pullbackOpen e.hom (_root_.AlgebraicGeometry.AlgebraicCycle.map (incl ≫ e.hom)
        (fun z ↦ wW' ((incl ≫ e.hom).base z)) wW' c) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map incl (fun z ↦ wW (incl.base z)) wW c := by
  apply Function.locallyFinsuppWithin.ext
  intro w
  rw [AlgebraicCycle.pullbackOpen_apply]
  by_cases hw : w ∈ Set.range incl.base
  · obtain ⟨z, rfl⟩ := hw
    have hz : e.hom.base (incl.base z) = (incl ≫ e.hom).base z := rfl
    rw [hz, AlgebraicCycle.map_closedImmersion_apply_image (incl ≫ e.hom),
      AlgebraicCycle.map_closedImmersion_apply_image incl]
  · have hnot : e.hom.base w ∉ Set.range (incl ≫ e.hom).base := by
      rintro ⟨z, hz⟩
      exact hw ⟨z, e.hom.isOpenEmbedding.injective hz⟩
    rw [AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range _ _ _ _ hnot,
      AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range _ _ _ _ hw]

/-! ## Transport of integral closed subschemes along an isomorphism -/

namespace IntegralClosedSubscheme

/-- An integral closed subscheme transported along an isomorphism of the ambient scheme. -/
noncomputable def transportIso {W W' : Scheme.{u}} (e : W ≅ W') (Z : IntegralClosedSubscheme W) :
    IntegralClosedSubscheme W' :=
  have _ := Z.isClosedImmersion
  have _ := Z.isIntegral
  have _ := Z.isLocallyNoetherian
  { scheme := Z.scheme
    inclusion := Z.inclusion ≫ e.hom }

@[simp]
theorem transportIso_scheme {W W' : Scheme.{u}} (e : W ≅ W') (Z : IntegralClosedSubscheme W) :
    (Z.transportIso e).scheme = Z.scheme :=
  rfl

@[simp]
theorem transportIso_inclusion {W W' : Scheme.{u}} (e : W ≅ W') (Z : IntegralClosedSubscheme W) :
    (Z.transportIso e).inclusion = Z.inclusion ≫ e.hom :=
  rfl

end IntegralClosedSubscheme

namespace RationalFunctionGenerator

/-- A principal-divisor generator transported along an isomorphism of the ambient scheme. -/
noncomputable def transportIso {W W' : Scheme.{u}} (e : W ≅ W')
    (g : RationalFunctionGenerator W) : RationalFunctionGenerator W' where
  subspace := g.subspace.transportIso e
  function := g.function

@[simp]
theorem transportIso_subspace {W W' : Scheme.{u}} (e : W ≅ W')
    (g : RationalFunctionGenerator W) :
    (g.transportIso e).subspace = g.subspace.transportIso e :=
  rfl

/-- The principal divisor of a transported generator pulls back to the principal divisor of the
generator: the two are the same cycle read through the isomorphism. -/
theorem pullbackOpen_divisor_transportIso {W W' : Scheme.{u}} (e : W ≅ W')
    (g : RationalFunctionGenerator W) (dimW : DimensionFunction W)
    (dimW' : DimensionFunction W') :
    AlgebraicCycle.pullbackOpen e.hom ((g.transportIso e).divisor dimW') = g.divisor dimW := by
  have _ := g.subspace.isClosedImmersion
  have _ := g.subspace.isIntegral
  have _ := g.subspace.isLocallyNoetherian
  unfold divisor IntegralClosedSubscheme.pushforward
  exact AlgebraicCycle.pullbackOpen_map_comp_iso g.subspace.inclusion e
    (fun x ↦ (dimW : W → ℤ) x) (fun x ↦ (dimW' : W' → ℤ) x) _

end RationalFunctionGenerator

/-- Flat pullback along an open immersion only depends on the morphism. -/
theorem AlgebraicCycle.pullbackOpen_congr {W E : Scheme.{u}} (f₁ f₂ : W ⟶ E)
    [_root_.AlgebraicGeometry.IsOpenImmersion f₁] [_root_.AlgebraicGeometry.IsOpenImmersion f₂]
    (h : f₁ = f₂) (c : AlgebraicCycle E ℚ) :
    AlgebraicCycle.pullbackOpen f₁ c = AlgebraicCycle.pullbackOpen f₂ c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  change (c : E → ℚ) (f₁.base x) = (c : E → ℚ) (f₂.base x)
  rw [h]

/-! ## Supports of rational relations -/

/-- The principal divisor of a generator supported in a subset is supported in that subset. -/
theorem divisor_supportedIn {X : Scheme.{u}} (dimension : DimensionFunction X) {Z : Set X}
    {g : RationalFunctionGenerator X} (hg : g.SupportedIn Z) :
    (g.divisor dimension).SupportedIn Z := by
  have _ := g.subspace.isClosedImmersion
  have _ := g.subspace.isIntegral
  have _ := g.subspace.isLocallyNoetherian
  intro x hx
  refine hg ?_
  by_contra hnot
  refine hx ?_
  unfold RationalFunctionGenerator.divisor IntegralClosedSubscheme.pushforward
  exact AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range _ _ _ _ hnot

/-- Every rational relation supported in a subset is a cycle supported in that subset. -/
theorem supportedRelations_le_supportedIn {X : Scheme.{u}} (dimension : DimensionFunction X)
    (Z : Set X) : supportedRelations X dimension Z ≤ AlgebraicCycle.supportedIn Z := by
  refine Submodule.span_le.2 ?_
  rintro d ⟨g, hg, rfl⟩
  exact divisor_supportedIn dimension hg

/-- The flat pullback of a cycle along a trivial affine bundle of rank `#ι` is concentrated in
dimension `d` as soon as the cycle is concentrated in dimension `d - #ι`. -/
theorem pullbackBundleRefl_eq_zero_of_dimension_ne {R : Type u} [CommRing R] [IsNoetherianRing R]
    {ι : Type u} [Finite ι] (dimB : DimensionFunction (Spec (CommRingCat.of R)))
    (dimT : DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι R)))) (d : ℤ)
    (a : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ)
    (ha : ∀ y, dimB y ≠ d - (Nat.card ι : ℤ) → (a : ↥(Spec (CommRingCat.of R)) → ℚ) y = 0)
    (q : ↥(Spec (CommRingCat.of (MvPolynomial ι R)))) (hq : dimT q ≠ d) :
    (AlgebraicCycle.pullbackBundle (AlgEquiv.refl : MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R) a :
      ↥(Spec (CommRingCat.of (MvPolynomial ι R))) → ℚ) q = 0 := by
  by_cases h : q ∈ Set.range (VectorBundle.bundlePoint
      (AlgEquiv.refl : MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R))
  · obtain ⟨y, rfl⟩ := h
    rw [AlgebraicCycle.pullbackBundle_apply_bundlePoint]
    refine ha y fun hy ↦ hq ?_
    rw [VectorBundle.dimension_bundlePoint _ dimB dimT y, hy]
    omega
  · exact AlgebraicCycle.pullbackBundle_eq_zero_of_notMem _ _ h

/-! ## The dimension projection of supported relations -/

/-- Flat pullback along an open immersion commutes with the dimension projection. -/
theorem pullbackOpen_project {W E : Scheme.{u}} (f : W ⟶ E)
    [_root_.AlgebraicGeometry.IsOpenImmersion f] (dimE : DimensionFunction E)
    (dimW : DimensionFunction W) (hdim : ∀ w, dimW w = dimE (f.base w)) (i : ℤ)
    (c : AlgebraicCycle E ℚ) :
    AlgebraicCycle.pullbackOpen f
        (cyclesOfDimension.project (dimension := dimE) (i := i) c : AlgebraicCycle E ℚ) =
      (cyclesOfDimension.project (dimension := dimW) (i := i)
        (AlgebraicCycle.pullbackOpen f c) : AlgebraicCycle W ℚ) := by
  apply Function.locallyFinsuppWithin.ext
  intro w
  rw [AlgebraicCycle.pullbackOpen_apply, cyclesOfDimension.project_apply,
    cyclesOfDimension.project_apply, hdim w]
  by_cases hw : dimE (f.base w) = i <;> simp [hw]

/-- A cycle concentrated in dimension `i` is its own dimension-`i` projection. -/
theorem project_eq_of_concentrated {X : Scheme.{u}} {dimension : DimensionFunction X} {i : ℤ}
    (c : AlgebraicCycle X ℚ) (hc : ∀ x, dimension x ≠ i → (c : X → ℚ) x = 0) :
    (cyclesOfDimension.project (dimension := dimension) (i := i) c : AlgebraicCycle X ℚ) = c := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [cyclesOfDimension.project_apply]
  by_cases hx : dimension x = i
  · rw [if_pos hx]
  · rw [if_neg hx, hc x hx]

/-- If all principal divisors are homogeneous then the relations supported in a subset are graded:
the dimension-`i` part of a relation supported in `Z` is again a relation supported in `Z`. -/
theorem project_mem_supportedRelations_of_homogeneous {X : Scheme.{u}}
    {dimension : DimensionFunction X} {i : ℤ}
    (hhom : PrincipalDivisorsHomogeneous X dimension) (Z : Set X) (c : AlgebraicCycle X ℚ)
    (hc : c ∈ supportedRelations X dimension Z) :
    (cyclesOfDimension.project (dimension := dimension) (i := i) c : AlgebraicCycle X ℚ) ∈
      supportedRelations X dimension Z := by
  induction hc using Submodule.span_induction with
  | mem d hd =>
      obtain ⟨g, hg, rfl⟩ := hd
      obtain ⟨e, he⟩ := hhom g
      by_cases hei : e = i
      · have hproj : (cyclesOfDimension.project (dimension := dimension) (i := i)
            (g.divisor dimension) : AlgebraicCycle X ℚ) = g.divisor dimension := by
          refine project_eq_of_concentrated _ fun x hx ↦ ?_
          by_contra hne
          exact hx ((he x hne).trans hei)
        rw [hproj]
        exact divisor_mem_supportedRelations dimension hg
      · have hproj : (cyclesOfDimension.project (dimension := dimension) (i := i)
            (g.divisor dimension) : AlgebraicCycle X ℚ) = 0 := by
          apply Function.locallyFinsuppWithin.ext
          intro x
          rw [cyclesOfDimension.project_apply]
          by_cases hx : dimension x = i
          · rw [if_pos hx]
            by_contra hne
            exact hei ((he x hne).symm.trans hx)
          · rw [if_neg hx]
            rfl
        rw [hproj]
        exact Submodule.zero_mem _
  | zero =>
      rw [cyclesOfDimension.project_zero]
      exact Submodule.zero_mem _
  | add c d _ _ hc hd =>
      rw [cyclesOfDimension.project_add]
      exact Submodule.add_mem _ hc hd
  | smul q c _ hc =>
      rw [cyclesOfDimension.project_smul]
      exact Submodule.smul_mem _ q hc

/-! ## Extension of rational relations along an open immersion -/

section RelationsAlongOpenImmersion

/-- The underlying closed set of the closure of an integral closed subscheme of an open subscheme
is the closure of its image. -/
theorem range_closureIn_inclusion {E : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsLocallyNoetherian E] (V : E.Opens)
    (Z : IntegralClosedSubscheme V.toScheme)
    [_root_.AlgebraicGeometry.QuasiCompact (Z.inclusion ≫ V.ι)] :
    Set.range (Z.closureIn V).inclusion.base = closure (Set.range (Z.inclusion ≫ V.ι).base) := by
  rw [IntegralClosedSubscheme.closureIn_inclusion]
  change Set.range ((Z.inclusion ≫ V.ι).ker.subschemeι).base = _
  rw [_root_.AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι,
    _root_.AlgebraicGeometry.Scheme.Hom.support_ker]

variable {W E : Scheme.{u}} (f : W ⟶ E) [_root_.AlgebraicGeometry.IsOpenImmersion f]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian E] [NoetherianSpace E]

/-- Every rational relation supported in a subset of an open subscheme is the restriction of a
rational relation supported in any closed subset of the ambient scheme containing the image. -/
theorem exists_supportedRelations_pullbackOpen (dimE : DimensionFunction E)
    (dimW : DimensionFunction W) {T : Set E} (hT : IsClosed T) {S : Set W}
    (hS : f.base '' S ⊆ T) (ρ : AlgebraicCycle W ℚ)
    (hρ : ρ ∈ supportedRelations W dimW S) :
    ∃ ρ' ∈ supportedRelations E dimE T, AlgebraicCycle.pullbackOpen f ρ' = ρ := by
  induction hρ using Submodule.span_induction with
  | mem d hd =>
      obtain ⟨g, hg, rfl⟩ := hd
      let V : E.Opens := f.opensRange
      let e : W ≅ V.toScheme := f.isoOpensRange
      have hfac : e.hom ≫ V.ι = f := f.isoOpensRange_hom_ι
      let g' : RationalFunctionGenerator V.toScheme := g.transportIso e
      have hincl : g'.subspace.inclusion ≫ V.ι = g.subspace.inclusion ≫ f := by
        change (g.subspace.inclusion ≫ e.hom) ≫ V.ι = _
        rw [Category.assoc, hfac]
      have _ := g.subspace.isClosedImmersion
      have _ : _root_.AlgebraicGeometry.QuasiCompact (g'.subspace.inclusion ≫ V.ι) := by
        infer_instance
      refine ⟨(g'.closureIn V).divisor dimE, ?_, ?_⟩
      · refine divisor_mem_supportedRelations dimE ?_
        change Set.range (g'.subspace.closureIn V).inclusion.base ⊆ T
        rw [range_closureIn_inclusion V g'.subspace, hincl]
        refine (closure_mono ?_).trans hT.closure_subset
        rintro _ ⟨z, rfl⟩
        exact hS ⟨g.subspace.inclusion.base z, hg ⟨z, rfl⟩, rfl⟩
      · have key : AlgebraicCycle.pullbackOpen (e.hom ≫ V.ι) ((g'.closureIn V).divisor dimE) =
            g.divisor dimW := by
          rw [← AlgebraicCycle.pullbackOpen_comp,
            g'.pullbackOpen_divisor_closureIn V dimE
              (DimensionFunction.comapClosedImmersion e.inv dimW),
            RationalFunctionGenerator.pullbackOpen_divisor_transportIso]
        exact (AlgebraicCycle.pullbackOpen_congr f (e.hom ≫ V.ι) hfac.symm _).trans key
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero (AlgebraicCycle.pullbackOpenLinear f)⟩
  | add c d _ _ hc hd =>
      obtain ⟨c', hc', rfl⟩ := hc
      obtain ⟨d', hd', rfl⟩ := hd
      exact ⟨c' + d', Submodule.add_mem _ hc' hd',
        map_add (AlgebraicCycle.pullbackOpenLinear f) c' d'⟩
  | smul q c _ hc =>
      obtain ⟨c', hc', rfl⟩ := hc
      exact ⟨q • c', Submodule.smul_mem _ q hc',
        map_smul (AlgebraicCycle.pullbackOpenLinear f) q c'⟩

end RelationsAlongOpenImmersion

namespace BundlePullbackGlobal

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : BundleData X ι)

/-! ## Noetherianity of the total space -/

/-- The total space of a bundle over a compact base is compact: the projection is an affine, hence
quasi-compact, morphism. -/
instance compactSpace_totalSpace [CompactSpace X] : CompactSpace 𝓔.totalSpace :=
  _root_.AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace 𝓔.proj

/-! ## The charts of the base -/

/-- A trivialising chart of the base, read as the spectrum of its ring of sections. -/
noncomputable abbrev chartε (j : 𝓔.J) : Spec (CommRingCat.of Γ(X, (𝓔.chart j).1)) ⟶ X :=
  (isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι

/-- The projection of a trivialising chart of the total space onto the corresponding chart of the
base. -/
noncomputable abbrev chartπ (j : 𝓔.J) :
    Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1))) ⟶
      Spec (CommRingCat.of Γ(X, (𝓔.chart j).1)) :=
  GradedCone.projection Γ(X, (𝓔.chart j).1) (MvPolynomial ι Γ(X, (𝓔.chart j).1))

/-- The image of a chart of the base is the chart. -/
theorem range_chartε (j : 𝓔.J) :
    Set.range (chartε 𝓔 j).base = ((𝓔.chart j).1 : Set X) := by
  have h : Set.range (chartε 𝓔 j).base =
      (𝓔.chart j).1.ι.base '' Set.range (isAffineOpen X (𝓔.chart j)).isoSpec.inv.base := by
    rw [← Set.range_comp]
    rfl
  have hsurj : Function.Surjective (isAffineOpen X (𝓔.chart j)).isoSpec.inv.base := by
    intro x
    refine ⟨(isAffineOpen X (𝓔.chart j)).isoSpec.hom.base x, ?_⟩
    change ((isAffineOpen X (𝓔.chart j)).isoSpec.hom ≫
      (isAffineOpen X (𝓔.chart j)).isoSpec.inv).base x = x
    rw [Iso.hom_inv_id]
    rfl
  rw [h, Set.range_eq_univ.2 hsurj, Set.image_univ,
    _root_.AlgebraicGeometry.Scheme.Opens.range_ι]

/-- The projection of the total space read in a chart is the projection of the trivialised affine
space over the chart. -/
theorem proj_chartι_chartε (j : 𝓔.J)
    (q : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1))))) :
    𝓔.proj.base ((𝓔.chartι j).base q) = (chartε 𝓔 j).base ((chartπ 𝓔 j).base q) :=
  proj_chartι_base 𝓔 j q

/-! ## The trace of a closed subset of the base on a chart -/

/-- The radical ideal of the trace on a chart of the base of a subset of the base. -/
noncomputable def chartIdeal (j : 𝓔.J) (Z : Set X) : Ideal Γ(X, (𝓔.chart j).1) :=
  PrimeSpectrum.vanishingIdeal ((chartε 𝓔 j).base ⁻¹' Z)

/-- The zero locus of the ideal of the trace of a closed subset on a chart is that trace. -/
theorem zeroLocus_chartIdeal (j : 𝓔.J) {Z : Set X} (hZ : IsClosed Z) :
    PrimeSpectrum.zeroLocus (chartIdeal 𝓔 j Z : Set Γ(X, (𝓔.chart j).1)) =
      (chartε 𝓔 j).base ⁻¹' Z := by
  rw [chartIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact (hZ.preimage (chartε 𝓔 j).continuous).closure_eq

/-- The preimage under the projection of a chart of the total space of the zero locus of an ideal
of the chart of the base is the zero locus of the extended ideal. -/
theorem preimage_chartπ_zeroLocus (j : 𝓔.J) (I : Ideal Γ(X, (𝓔.chart j).1)) :
    (chartπ 𝓔 j).base ⁻¹' (PrimeSpectrum.zeroLocus (I : Set Γ(X, (𝓔.chart j).1))) =
      PrimeSpectrum.zeroLocus
        (I.map (MvPolynomial.C : Γ(X, (𝓔.chart j).1) →+* MvPolynomial ι Γ(X, (𝓔.chart j).1)) :
          Set (MvPolynomial ι Γ(X, (𝓔.chart j).1))) := by
  have hmap : (I.map (MvPolynomial.C : Γ(X, (𝓔.chart j).1) →+*
        MvPolynomial ι Γ(X, (𝓔.chart j).1)) : Set (MvPolynomial ι Γ(X, (𝓔.chart j).1))) =
      (Ideal.span ((MvPolynomial.C : Γ(X, (𝓔.chart j).1) →+*
        MvPolynomial ι Γ(X, (𝓔.chart j).1)) '' (I : Set Γ(X, (𝓔.chart j).1))) :
          Set (MvPolynomial ι Γ(X, (𝓔.chart j).1))) := rfl
  rw [hmap, PrimeSpectrum.zeroLocus_span]
  change PrimeSpectrum.comap
    (algebraMap Γ(X, (𝓔.chart j).1) (MvPolynomial ι Γ(X, (𝓔.chart j).1))) ⁻¹'
      PrimeSpectrum.zeroLocus (I : Set Γ(X, (𝓔.chart j).1)) = _
  rw [PrimeSpectrum.preimage_comap_zeroLocus, MvPolynomial.algebraMap_eq]

/-- The restriction to a chart of a cycle supported over a closed subset `Z` of the base is
supported in the zero locus of the extension of the ideal of the trace of `Z` on the chart. -/
theorem pullbackOpen_chartι_supportedIn (j : 𝓔.J) {Z : Set X} (hZ : IsClosed Z)
    (z : AlgebraicCycle 𝓔.totalSpace ℚ) (hz : z.SupportedIn (𝓔.proj.base ⁻¹' Z)) :
    (AlgebraicCycle.pullbackOpen (𝓔.chartι j) z).SupportedIn
      (PrimeSpectrum.zeroLocus ((chartIdeal 𝓔 j Z).map
        (MvPolynomial.C : Γ(X, (𝓔.chart j).1) →+* MvPolynomial ι Γ(X, (𝓔.chart j).1)) :
          Set (MvPolynomial ι Γ(X, (𝓔.chart j).1)))) := by
  intro q hq
  rw [← preimage_chartπ_zeroLocus, zeroLocus_chartIdeal 𝓔 j hZ]
  have hval : (z : 𝓔.totalSpace → ℚ) ((𝓔.chartι j).base q) ≠ 0 := hq
  have hmem := hz _ hval
  change 𝓔.proj.base ((𝓔.chartι j).base q) ∈ Z at hmem
  rw [proj_chartι_chartε] at hmem
  exact hmem

/-! ## Extension of cycles from a chart of the base -/

section Extend

variable [IsLocallyNoetherian X] [CompactSpace X]

/-- Extension by zero of a cycle from a chart of the base, read as `Spec Γ(X, U_j)`, to the whole
base. -/
noncomputable def extendChart (j : 𝓔.J)
    (a : AlgebraicCycle (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))) ℚ) : AlgebraicCycle X ℚ :=
  AlgebraicCycle.extendByZero (𝓔.chart j).1
    (AlgebraicCycle.pullbackOpen (isAffineOpen X (𝓔.chart j)).isoSpec.hom a)

/-- The coefficients of an extended cycle at the points of the chart are the original ones. -/
theorem extendChart_apply_chartε (j : 𝓔.J)
    (a : AlgebraicCycle (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))) ℚ)
    (y : ↥(Spec (CommRingCat.of Γ(X, (𝓔.chart j).1)))) :
    (extendChart 𝓔 j a : X → ℚ) ((chartε 𝓔 j).base y) = (a : _ → ℚ) y := by
  have h : (isAffineOpen X (𝓔.chart j)).isoSpec.hom.base
      ((isAffineOpen X (𝓔.chart j)).isoSpec.inv.base y) = y := by
    change ((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫
      (isAffineOpen X (𝓔.chart j)).isoSpec.hom).base y = y
    rw [Iso.inv_hom_id]
    rfl
  change (AlgebraicCycle.extendByZero (𝓔.chart j).1
    (AlgebraicCycle.pullbackOpen (isAffineOpen X (𝓔.chart j)).isoSpec.hom a) : X → ℚ)
      ((𝓔.chart j).1.ι.base ((isAffineOpen X (𝓔.chart j)).isoSpec.inv.base y)) = _
  rw [AlgebraicCycle.extendByZero_apply_coe]
  change (a : _ → ℚ) ((isAffineOpen X (𝓔.chart j)).isoSpec.hom.base
    ((isAffineOpen X (𝓔.chart j)).isoSpec.inv.base y)) = _
  rw [h]

/-- Extension by zero from a chart is a section of restriction to that chart. -/
@[simp]
theorem pullbackOpen_chartε_extendChart (j : 𝓔.J)
    (a : AlgebraicCycle (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))) ℚ) :
    AlgebraicCycle.pullbackOpen (chartε 𝓔 j) (extendChart 𝓔 j a) = a := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  exact extendChart_apply_chartε 𝓔 j a y

/-- An extended cycle vanishes outside the chart. -/
theorem extendChart_eq_zero_of_notMem (j : 𝓔.J)
    (a : AlgebraicCycle (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))) ℚ) {x : X}
    (hx : x ∉ (𝓔.chart j).1) : (extendChart 𝓔 j a : X → ℚ) x = 0 :=
  AlgebraicCycle.extendByZero_apply_of_notMem _ _ x hx

/-- The support of an extended cycle is the image of the support of the original cycle. -/
theorem extendChart_supportedIn (j : 𝓔.J)
    (a : AlgebraicCycle (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))) ℚ)
    {S : Set ↥(Spec (CommRingCat.of Γ(X, (𝓔.chart j).1)))} (ha : a.SupportedIn S) :
    (extendChart 𝓔 j a).SupportedIn ((chartε 𝓔 j).base '' S) := by
  intro x hx
  by_cases hxU : x ∈ (𝓔.chart j).1
  · have hmem : x ∈ Set.range (chartε 𝓔 j).base := by
      rw [range_chartε]
      exact hxU
    obtain ⟨y, rfl⟩ := hmem
    exact ⟨y, ha y (by rwa [← extendChart_apply_chartε 𝓔 j a y]), rfl⟩
  · exact absurd (extendChart_eq_zero_of_notMem 𝓔 j a hxU) hx

/-- An extended cycle is concentrated in the same dimension as the original one. -/
theorem extendChart_concentrated (j : 𝓔.J)
    (a : AlgebraicCycle (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))) ℚ)
    (dimX : DimensionFunction X)
    (dimU : DimensionFunction (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))))
    (hdimU : ∀ y, dimU y = dimX ((chartε 𝓔 j).base y)) (d : ℤ)
    (ha : ∀ y, dimU y ≠ d → (a : _ → ℚ) y = 0) (x : X) (hx : dimX x ≠ d) :
    (extendChart 𝓔 j a : X → ℚ) x = 0 := by
  by_cases hxU : x ∈ (𝓔.chart j).1
  · have hmem : x ∈ Set.range (chartε 𝓔 j).base := by
      rw [range_chartε]
      exact hxU
    obtain ⟨y, rfl⟩ := hmem
    rw [extendChart_apply_chartε]
    exact ha y (by rw [hdimU y]; exact hx)
  · exact extendChart_eq_zero_of_notMem 𝓔 j a hxU

end Extend

/-! ## The Noetherian induction -/

section Induction

variable [Finite ι] [IsLocallyNoetherian X] [CompactSpace X]

omit [Finite ι] [IsLocallyNoetherian X] [CompactSpace ↥X] in
/-- The flat pullback of a cycle supported in a subset of the base is supported over that
subset. -/
theorem pullbackBundle_supportedIn (w : AlgebraicCycle X ℚ) {Z : Set X} (hw : w.SupportedIn Z) :
    (pullbackBundle 𝓔 w).SupportedIn (𝓔.proj.base ⁻¹' Z) := by
  intro q hq
  by_cases h : q ∈ Set.range (bundlePoint 𝓔)
  · obtain ⟨x, rfl⟩ := h
    change 𝓔.proj.base (bundlePoint 𝓔 x) ∈ Z
    rw [proj_bundlePoint]
    refine hw x ?_
    rwa [pullbackBundle_apply_bundlePoint] at hq
  · exact absurd (pullbackBundle_eq_zero_of_notMem 𝓔 w h) hq

omit [Finite ι] [IsLocallyNoetherian X] [CompactSpace ↥X] in
/-- The flat pullback of a cycle concentrated in dimension `d - rank` is concentrated in
dimension `d`. -/
theorem pullbackBundle_concentrated (dimX : DimensionFunction X)
    (dimE : DimensionFunction 𝓔.totalSpace)
    (hshift : ∀ x, dimE (bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ)) (d : ℤ)
    (w : AlgebraicCycle X ℚ) (hw : ∀ x, dimX x ≠ d - (Nat.card ι : ℤ) → (w : X → ℚ) x = 0)
    (q : 𝓔.totalSpace) (hq : dimE q ≠ d) : (pullbackBundle 𝓔 w : 𝓔.totalSpace → ℚ) q = 0 := by
  by_cases h : q ∈ Set.range (bundlePoint 𝓔)
  · obtain ⟨x, rfl⟩ := h
    rw [pullbackBundle_apply_bundlePoint]
    refine hw x fun hx ↦ hq ?_
    rw [hshift x, hx]
    omega
  · exact pullbackBundle_eq_zero_of_notMem 𝓔 w h

/-- **Fulton, *Intersection Theory*, Proposition 1.9, global form with supports.**  Let `𝓔` be a
vector bundle of finite rank over a Noetherian scheme `X` whose charts have the universal
dimension formula, and let `z` be a cycle on the total space concentrated in dimension `j` and
supported over a closed subset `Z` of the base.  Then `z` is the flat pullback of a cycle `w`
concentrated in dimension `j - rank` and supported in `Z`, modulo a rational relation supported
over `Z`.

The proof is Noetherian induction on `Z`: on a chart meeting `Z` the affine statement with
supports (`VectorBundle.exists_pullback_supported`) applies, the resulting cycle is extended by
zero and the resulting relation is extended by closure, and the difference is supported over the
strictly smaller closed subset `Z \ U`. -/
theorem exists_pullback_supported
    (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)
    (hshift : ∀ x, dimE (bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ))
    (dimChart : ∀ j : 𝓔.J, DimensionFunction (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))))
    (dimChartE : ∀ j : 𝓔.J,
      DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
    (hdimChart : ∀ (j : 𝓔.J) (y), dimChart j y = dimX ((chartε 𝓔 j).base y))
    (hdimChartE : ∀ (j : 𝓔.J) (q), dimChartE j q = dimE ((𝓔.chartι j).base q))
    (hdim : ∀ j : 𝓔.J, VectorBundle.HasUniversalDimensionFormula Γ(X, (𝓔.chart j).1))
    (hhom : PrincipalDivisorsHomogeneous 𝓔.totalSpace dimE)
    (Z : Closeds X) (j : ℤ) (z : AlgebraicCycle 𝓔.totalSpace ℚ)
    (hz : ∀ q, dimE q ≠ j → (z : 𝓔.totalSpace → ℚ) q = 0)
    (hsupp : z.SupportedIn (𝓔.proj.base ⁻¹' (Z : Set X))) :
    ∃ w : AlgebraicCycle X ℚ, (∀ x, dimX x ≠ j - (Nat.card ι : ℤ) → (w : X → ℚ) x = 0) ∧
      w.SupportedIn (Z : Set X) ∧
      z - pullbackBundle 𝓔 w ∈
        supportedRelations 𝓔.totalSpace dimE (𝓔.proj.base ⁻¹' (Z : Set X)) := by
  induction Z using WellFoundedLT.induction generalizing z with
  | _ Z ih =>
  by_cases hZ : (Z : Set X) = ∅
  · refine ⟨0, fun x _ ↦ rfl, AlgebraicCycle.supportedIn_zero _, ?_⟩
    have hz0 : z = 0 := by
      apply Function.locallyFinsuppWithin.ext
      intro q
      have hzero : ((0 : AlgebraicCycle 𝓔.totalSpace ℚ) : 𝓔.totalSpace → ℚ) q = 0 := rfl
      rw [hzero]
      by_contra hne
      have hmem := hsupp q hne
      rw [hZ] at hmem
      simp at hmem
    have h0 : pullbackBundle 𝓔 (0 : AlgebraicCycle X ℚ) = 0 :=
      map_zero (pullbackBundleLinear 𝓔)
    rw [hz0, h0, sub_zero]
    exact Submodule.zero_mem _
  · obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.2 hZ
    set j₀ := chartIndex 𝓔 x₀ with hj₀def
    have hx₀U : x₀ ∈ (𝓔.chart j₀).1 := mem_chart_chartIndex 𝓔 x₀
    -- restriction of `z` to the chart `j₀`
    have hzres : ∀ q, dimChartE j₀ q ≠ j →
        (AlgebraicCycle.pullbackOpen (𝓔.chartι j₀) z :
          ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j₀).1)))) → ℚ) q = 0 :=
      fun q hq ↦ hz _ fun hcon ↦ hq (by rw [hdimChartE j₀ q]; exact hcon)
    have hsuppres := pullbackOpen_chartι_supportedIn 𝓔 j₀ Z.isClosed z hsupp
    obtain ⟨a, hadim, hasupp, harel⟩ :=
      VectorBundle.exists_pullback_supported (hdim j₀) (dimChart j₀) (dimChartE j₀)
        (chartIdeal 𝓔 j₀ (Z : Set X)) j _ hzres hsuppres
    -- the extension by zero of `a`
    have hw₁supp : (extendChart 𝓔 j₀ a).SupportedIn (Z : Set X) := by
      refine (extendChart_supportedIn 𝓔 j₀ a hasupp).mono ?_
      rintro _ ⟨y, hy, rfl⟩
      have hy' : y ∈ (chartε 𝓔 j₀).base ⁻¹' (Z : Set X) := by
        rw [← zeroLocus_chartIdeal 𝓔 j₀ Z.isClosed]
        exact hy
      exact hy'
    have hw₁dim : ∀ x, dimX x ≠ j - (Nat.card ι : ℤ) →
        (extendChart 𝓔 j₀ a : X → ℚ) x = 0 :=
      fun x hx ↦ extendChart_concentrated 𝓔 j₀ a dimX (dimChart j₀) (hdimChart j₀)
        (j - (Nat.card ι : ℤ)) hadim x hx
    -- the extension by closure of the relation
    have hTclosed : IsClosed (𝓔.proj.base ⁻¹' (Z : Set X)) := Z.isClosed.preimage 𝓔.proj.continuous
    have hSsub : (𝓔.chartι j₀).base ''
        (PrimeSpectrum.zeroLocus ((chartIdeal 𝓔 j₀ (Z : Set X)).map
          (MvPolynomial.C : Γ(X, (𝓔.chart j₀).1) →+*
            MvPolynomial ι Γ(X, (𝓔.chart j₀).1)) :
              Set (MvPolynomial ι Γ(X, (𝓔.chart j₀).1)))) ⊆
        𝓔.proj.base ⁻¹' (Z : Set X) := by
      rintro _ ⟨q, hq, rfl⟩
      have hq' : q ∈ (chartπ 𝓔 j₀).base ⁻¹'
          (PrimeSpectrum.zeroLocus (chartIdeal 𝓔 j₀ (Z : Set X) : Set Γ(X, (𝓔.chart j₀).1))) := by
        rw [preimage_chartπ_zeroLocus]
        exact hq
      rw [zeroLocus_chartIdeal 𝓔 j₀ Z.isClosed] at hq'
      change 𝓔.proj.base ((𝓔.chartι j₀).base q) ∈ (Z : Set X)
      rw [proj_chartι_chartε]
      exact hq'
    obtain ⟨ρ, hρmem, hρres⟩ :=
      exists_supportedRelations_pullbackOpen (𝓔.chartι j₀) dimE (dimChartE j₀) hTclosed hSsub _
        harel
    -- its dimension-`j` part
    have hconc : ∀ q, dimChartE j₀ q ≠ j →
        ((AlgebraicCycle.pullbackOpen (𝓔.chartι j₀) z -
          AlgebraicCycle.pullbackBundle
            (AlgEquiv.refl : MvPolynomial ι Γ(X, (𝓔.chart j₀).1) ≃ₐ[Γ(X, (𝓔.chart j₀).1)]
              MvPolynomial ι Γ(X, (𝓔.chart j₀).1)) a) :
          ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j₀).1)))) → ℚ) q = 0 := by
      intro q hq
      have h1 := hzres q hq
      have h2 := pullbackBundleRefl_eq_zero_of_dimension_ne (dimChart j₀) (dimChartE j₀) j a
        hadim q hq
      simp only [Pi.sub_apply]
      rw [h1, h2, sub_zero]
    set ρ' : AlgebraicCycle 𝓔.totalSpace ℚ :=
      (cyclesOfDimension.project (dimension := dimE) (i := j) ρ : AlgebraicCycle 𝓔.totalSpace ℚ)
      with hρ'def
    have hρ'mem : ρ' ∈ supportedRelations 𝓔.totalSpace dimE (𝓔.proj.base ⁻¹' (Z : Set X)) :=
      project_mem_supportedRelations_of_homogeneous hhom _ ρ hρmem
    have hρ'dim : ∀ q, dimE q ≠ j → (ρ' : 𝓔.totalSpace → ℚ) q = 0 := by
      intro q hq
      rw [hρ'def, cyclesOfDimension.project_apply, if_neg hq]
    have hρ'res : AlgebraicCycle.pullbackOpen (𝓔.chartι j₀) ρ' =
        AlgebraicCycle.pullbackOpen (𝓔.chartι j₀) ρ := by
      rw [hρ'def, pullbackOpen_project (𝓔.chartι j₀) dimE (dimChartE j₀) (hdimChartE j₀) j ρ,
        hρres]
      exact project_eq_of_concentrated _ hconc
    -- the remainder, which lives over the strictly smaller closed subset `Z \ U`
    set z₂ : AlgebraicCycle 𝓔.totalSpace ℚ :=
      z - pullbackBundle 𝓔 (extendChart 𝓔 j₀ a) - ρ' with hz₂def
    have hz₂res : AlgebraicCycle.pullbackOpen (𝓔.chartι j₀) z₂ = 0 := by
      have hlin : AlgebraicCycle.pullbackOpen (𝓔.chartι j₀) z₂ =
          AlgebraicCycle.pullbackOpen (𝓔.chartι j₀) z -
            AlgebraicCycle.pullbackOpen (𝓔.chartι j₀)
              (pullbackBundle 𝓔 (extendChart 𝓔 j₀ a)) -
            AlgebraicCycle.pullbackOpen (𝓔.chartι j₀) ρ' := by
        rw [hz₂def]
        simp only [← AlgebraicCycle.pullbackOpenLinear_apply, map_sub]
      rw [hlin, hρ'res, hρres, pullbackOpen_chartι_pullbackBundle,
        pullbackOpen_chartε_extendChart]
      abel
    have hz₂dim : ∀ q, dimE q ≠ j → (z₂ : 𝓔.totalSpace → ℚ) q = 0 := by
      intro q hq
      have h1 := hz q hq
      have h2 := hρ'dim q hq
      have h3 := pullbackBundle_concentrated 𝓔 dimX dimE hshift j _ hw₁dim q hq
      rw [hz₂def]
      simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply]
      rw [h1, h2, h3]
      ring
    have hrange : Set.range (𝓔.chartι j₀).base =
        𝓔.proj.base ⁻¹' ((𝓔.chart j₀).1 : Set X) :=
      congrArg (fun V : 𝓔.totalSpace.Opens ↦ (V : Set 𝓔.totalSpace)) (𝓔.opensRange_chartι j₀)
    have hz₂supp : z₂.SupportedIn (𝓔.proj.base ⁻¹' ((Z : Set X) \ ((𝓔.chart j₀).1 : Set X))) := by
      intro q hq
      refine ⟨?_, ?_⟩
      · exact ((hsupp.sub (pullbackBundle_supportedIn 𝓔 _ hw₁supp)).sub
          (supportedRelations_le_supportedIn dimE _ hρ'mem)) q hq
      · intro hmem
        have hq' : q ∈ Set.range (𝓔.chartι j₀).base := by
          rw [hrange]
          exact hmem
        obtain ⟨q', rfl⟩ := hq'
        refine hq ?_
        have := congrArg (fun c : AlgebraicCycle
            (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j₀).1)))) ℚ ↦
          (c : _ → ℚ) q') hz₂res
        exact this
    -- the induction hypothesis applied to `Z \ U`
    let Z' : Closeds X :=
      ⟨(Z : Set X) \ ((𝓔.chart j₀).1 : Set X), Z.isClosed.sdiff (𝓔.chart j₀).1.isOpen⟩
    have hle : Z' ≤ Z := fun x hx ↦ hx.1
    have hne : Z' ≠ Z := by
      intro hcon
      have hx₀' : x₀ ∈ (Z' : Set X) := by
        rw [hcon]
        exact hx₀
      exact hx₀'.2 hx₀U
    obtain ⟨w₂, hw₂dim, hw₂supp, hw₂rel⟩ :=
      ih Z' (lt_of_le_of_ne hle hne) z₂ hz₂dim hz₂supp
    refine ⟨extendChart 𝓔 j₀ a + w₂, ?_, ?_, ?_⟩
    · intro x hx
      have h1 := hw₁dim x hx
      have h2 := hw₂dim x hx
      simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
      rw [h1, h2, add_zero]
    · exact hw₁supp.add (hw₂supp.mono fun y hy ↦ hy.1)
    · have hpb : pullbackBundle 𝓔 (extendChart 𝓔 j₀ a + w₂) =
          pullbackBundle 𝓔 (extendChart 𝓔 j₀ a) + pullbackBundle 𝓔 w₂ :=
        pullbackBundle_add 𝓔 _ _
      have hsum : z - pullbackBundle 𝓔 (extendChart 𝓔 j₀ a + w₂) =
          (z₂ - pullbackBundle 𝓔 w₂) + ρ' := by
        rw [hpb, hz₂def]
        abel
      rw [hsum]
      exact Submodule.add_mem _
        (supportedRelations_mono dimE (fun q hq ↦ hq.1) hw₂rel) hρ'mem

end Induction

/-! ## Surjectivity of the global flat pullback -/

section Surjectivity

variable [Finite ι] [IsLocallyNoetherian X] [CompactSpace X]
  (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)
  (hshift : ∀ x, dimE (bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ))
  (dimChart : ∀ j : 𝓔.J, DimensionFunction (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))))
  (dimChartE : ∀ j : 𝓔.J,
    DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
  (hdimChart : ∀ (j : 𝓔.J) (y), dimChart j y = dimX ((chartε 𝓔 j).base y))
  (hdimChartE : ∀ (j : 𝓔.J) (q), dimChartE j q = dimE ((𝓔.chartι j).base q))
  (hdim : ∀ j : 𝓔.J, VectorBundle.HasUniversalDimensionFormula Γ(X, (𝓔.chart j).1))
  (hhom : PrincipalDivisorsHomogeneous 𝓔.totalSpace dimE)

include hshift dimChart dimChartE hdimChart hdimChartE hdim hhom in
/-- **Fulton, *Intersection Theory*, Proposition 1.9, global form.**  Every cycle on the total
space of a vector bundle of finite rank over a Noetherian scheme which is concentrated in
dimension `j` is, modulo rational equivalence, the flat pullback of a cycle on the base
concentrated in dimension `j - rank`. -/
theorem exists_pullback_eq (j : ℤ) (z : AlgebraicCycle 𝓔.totalSpace ℚ)
    (hz : ∀ q, dimE q ≠ j → (z : 𝓔.totalSpace → ℚ) q = 0) :
    ∃ w : AlgebraicCycle X ℚ, (∀ x, dimX x ≠ j - (Nat.card ι : ℤ) → (w : X → ℚ) x = 0) ∧
      z - pullbackBundle 𝓔 w ∈ totalRationalRelations 𝓔.totalSpace dimE := by
  obtain ⟨w, hwdim, -, hwrel⟩ :=
    exists_pullback_supported 𝓔 dimX dimE hshift dimChart dimChartE hdimChart hdimChartE hdim
      hhom ⊤ j z hz (fun q _ ↦ by
        change 𝓔.proj.base q ∈ ((⊤ : Closeds X) : Set X)
        rw [Closeds.coe_top]
        exact Set.mem_univ _)
  refine ⟨w, hwdim, ?_⟩
  have hle : supportedRelations 𝓔.totalSpace dimE (𝓔.proj.base ⁻¹' ((⊤ : Closeds X) : Set X)) ≤
      totalRationalRelations 𝓔.totalSpace dimE :=
    supportedRelations_le_totalRationalRelations dimE _
  exact hle hwrel

include hshift dimChart dimChartE hdimChart hdimChartE hdim hhom in
/-- **The global flat pullback is surjective on rational Chow groups.** -/
theorem chowPullbackBundleGlobal_surjective (i : ℤ)
    (RX : RationalEquivalenceSystem X dimX i)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ))) :
    Function.Surjective (BundleOverSubscheme.chowPullbackBundleGlobal 𝓔 dimX dimE hshift i
      RX RE) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective RE.relations y
  have hz2 : ∀ q, dimE q ≠ i + (Nat.card ι : ℤ) →
      ((z : cyclesOfDimension 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ))) :
        AlgebraicCycle 𝓔.totalSpace ℚ) q = 0 := z.2
  obtain ⟨w, hw, hrel⟩ :=
    exists_pullback_eq 𝓔 dimX dimE hshift dimChart dimChartE hdimChart hdimChartE hdim hhom
      (i + (Nat.card ι : ℤ)) (z : AlgebraicCycle 𝓔.totalSpace ℚ) hz2
  have hw' : ∀ x, dimX x ≠ i → (w : X → ℚ) x = 0 := fun x hx ↦ hw x (by omega)
  refine ⟨RX.quotientMap ⟨w, hw'⟩, ?_⟩
  have hmem : flatPullbackBundleGlobal 𝓔 dimX dimE hshift i ⟨w, hw'⟩ - z ∈ RE.relations := by
    cases RE
    have hneg : pullbackBundle 𝓔 w - (z : AlgebraicCycle 𝓔.totalSpace ℚ) =
        -((z : AlgebraicCycle 𝓔.totalSpace ℚ) - pullbackBundle 𝓔 w) := by abel
    change pullbackBundle 𝓔 w - (z : AlgebraicCycle 𝓔.totalSpace ℚ) ∈
      totalRationalRelations 𝓔.totalSpace dimE
    rw [hneg]
    exact Submodule.neg_mem _ hrel
  rw [BundleOverSubscheme.chowPullbackBundleGlobal_quotientMap]
  exact (Submodule.Quotient.eq _).2 hmem

include hshift dimChart dimChartE hdimChart hdimChartE hdim hhom in
/-- Every rational Chow class on the total space of a vector bundle is a flat pullback. -/
theorem exists_chowPullbackBundleGlobal_eq (i : ℤ)
    (RX : RationalEquivalenceSystem X dimX i)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ)))
    (β : RE.ChowGroup) :
    ∃ α : RX.ChowGroup,
      BundleOverSubscheme.chowPullbackBundleGlobal 𝓔 dimX dimE hshift i RX RE α = β :=
  chowPullbackBundleGlobal_surjective 𝓔 dimX dimE hshift dimChart dimChartE hdimChart hdimChartE
    hdim hhom i RX RE β

end Surjectivity

end BundlePullbackGlobal

namespace BundlePullbackGlobal

/-! ## The finite-type case over a field -/

section FiniteType

open FiniteTypeDimension

variable {F : Type u} [Field F] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of F))
  [_root_.AlgebraicGeometry.LocallyOfFiniteType f] [CompactSpace X] {ι : Type u} [Finite ι]
  (𝓔 : BundleData X ι)

omit [CompactSpace ↥X] [Finite ι] in
include f 𝓔 in
/-- A scheme carrying a vector bundle and locally of finite type over a field is locally
Noetherian: the charts of the bundle are affine opens with Noetherian rings of sections. -/
theorem isLocallyNoetherian_of_locallyOfFiniteType : IsLocallyNoetherian X :=
  isLocallyNoetherian_of_affine_cover 𝓔.iSup_chart
    fun j ↦ isNoetherianRing_sections f (𝓔.chart j).1 (𝓔.chart j).2

/-- **Global surjectivity of the flat pullback along a vector bundle over a compact scheme of
finite type over a field.**  All the hypotheses of `chowPullbackBundleGlobal_surjective` are
automatic here: the canonical dimension functions of `IntersectionTheory/FiniteTypeDimension.lean`
restrict to the charts (`dimensionFunction_comp`), satisfy the dimension shift
(`dimensionFunction_bundlePoint`), the sections over the charts have the universal dimension
formula (`hasUniversalDimensionFormula_sections`) and principal divisors on the total space are
homogeneous (`principalDivisorsHomogeneous_totalSpace`).

The pullback map is the one used by `VirtualFundamentalClass/GlobalVirtualClass.lean` as
`bundlePullbackFT f i RX RE`. -/
theorem chowPullbackBundleFiniteType_surjective (i : ℤ)
    (RX : RationalEquivalenceSystem X (dimensionFunction f) i)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))
      (i + (Nat.card ι : ℤ))) :
    Function.Surjective (BundleOverSubscheme.chowPullbackBundleGlobal 𝓔 (dimensionFunction f)
      (dimensionFunction (𝓔.proj ≫ f)) (dimensionFunction_bundlePoint f 𝓔) i RX RE) := by
  have _ := isLocallyNoetherian_of_locallyOfFiniteType f 𝓔
  exact chowPullbackBundleGlobal_surjective 𝓔 (dimensionFunction f)
    (dimensionFunction (𝓔.proj ≫ f)) (dimensionFunction_bundlePoint f 𝓔)
    (fun j ↦ dimensionFunction (chartε 𝓔 j ≫ f))
    (fun j ↦ dimensionFunction (𝓔.chartι j ≫ 𝓔.proj ≫ f))
    (fun j y ↦ dimensionFunction_comp f (chartε 𝓔 j) y)
    (fun j q ↦ dimensionFunction_comp (𝓔.proj ≫ f) (𝓔.chartι j) q)
    (fun j ↦ hasUniversalDimensionFormula_sections f (𝓔.chart j).1 (𝓔.chart j).2)
    (principalDivisorsHomogeneous_totalSpace f 𝓔) i RX RE

/-- Every rational Chow class on the total space of a vector bundle over a compact scheme of
finite type over a field lies in the range of the flat pullback.  This is exactly the hypothesis
`hmem` of `VirtualFundamentalClass.GlobalVirtualClass.virtualClassFT`. -/
theorem mem_range_chowPullbackBundleFiniteType (i : ℤ)
    (RX : RationalEquivalenceSystem X (dimensionFunction f) i)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))
      (i + (Nat.card ι : ℤ)))
    (β : RE.ChowGroup) :
    β ∈ LinearMap.range (BundleOverSubscheme.chowPullbackBundleGlobal 𝓔 (dimensionFunction f)
      (dimensionFunction (𝓔.proj ≫ f)) (dimensionFunction_bundlePoint f 𝓔) i RX RE) :=
  LinearMap.mem_range.2 (chowPullbackBundleFiniteType_surjective f 𝓔 i RX RE β)

end FiniteType

end BundlePullbackGlobal

end GromovWitten.AlgebraicGeometry.IntersectionTheory
