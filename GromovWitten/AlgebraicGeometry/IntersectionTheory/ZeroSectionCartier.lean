/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
import GromovWitten.AlgebraicGeometry.Curves.MarkingDivisors
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackGlobal
import GromovWitten.AlgebraicGeometry.IntersectionTheory.CartierLineBundle
import GromovWitten.AlgebraicGeometry.IntersectionTheory.PointOrder
import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# The zero section of a rank-one bundle is an effective Cartier divisor

Let `𝓔 : BundleData X ι` be a bundle of rank one (`[Unique ι]`), with total space `E`,
projection `p` and zero section `o`.  The projection is smooth of relative dimension one, so
`o(X)` is an effective Cartier divisor of `E` (via `EffectiveCartierDivisor.ofSection`).  We then
compute the divisor of the canonical section of its line bundle `O(o(X))` along the closure of
the generic point `ξ` of a fibre closure `p⁻¹(closure x)`: it is the point `o x` with
multiplicity one.

## Main results
* `ZeroSectionCartier.smoothOfRelativeDimension_one_proj`: for a bundle of rank one
  (`[Unique ι]`), the projection of the total space is smooth of relative dimension one.
* `zeroSectionDivisor`: the zero section of a rank-one bundle as an effective Cartier divisor
  on the total space, with `zeroSectionDivisor_idealSheaf : _ = 𝓔.zeroSection.ker` and
  `coe_support_zeroSectionDivisor : _ = Set.range 𝓔.zeroSection`.
* `ZeroSectionCartier.maximalIdeal_pointStalk_eq_span`: for a retraction `p` of `o`, a local
  generator of the kernel ideal of `o` generates the maximal ideal of the point stalk of
  `q ⤳ o x` whenever `q` lies over `x`.
* `ZeroSectionCartier.zeroSection_ne_bundlePoint`,
  `bundlePoint_not_mem_support_zeroSectionDivisor`: the generic point of a fibre closure is not
  on the zero section.
* `canonicalSection_zeroSectionDivisor_divisor`,
  `canonicalSection_pointSubscheme_zeroSectionDivisor_divisor`: for a dimension function with
  `dimE ξ = dimE (o x) + 1`, the divisor of the canonical section along the closure of `ξ` is
  the cycle with coefficient `1` at `o x` and `0` elsewhere.
-/

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

open VectorBundleTotalSpace
open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)

namespace ZeroSectionCartier

/-- A polynomial ring in one variable, presented with one generator and no relations. -/
private noncomputable def mvPolynomialSubmersivePresentation (ι : Type u) [Unique ι]
    (F : Type u) [CommRing F] :
    Algebra.SubmersivePresentation F (MvPolynomial ι F) ι Empty := by
  let v : Empty → MvPolynomial ι F := Empty.elim
  let P : Algebra.PreSubmersivePresentation F
      (MvPolynomial ι F ⧸ Ideal.span (Set.range v)) ι Empty :=
    Algebra.PreSubmersivePresentation.naive Empty.elim (fun x => x.elim)
  let Q : Algebra.SubmersivePresentation F
      (MvPolynomial ι F ⧸ Ideal.span (Set.range v)) ι Empty :=
    { toPreSubmersivePresentation := P
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  let e : (MvPolynomial ι F ⧸ Ideal.span (Set.range v)) ≃ₐ[F] MvPolynomial ι F :=
    (Ideal.quotientEquivAlgOfEq F (by simp [v])).trans
      (AlgEquiv.quotientBot F (MvPolynomial ι F))
  exact Q.ofAlgEquiv e

/-- A polynomial ring in a single variable is standard smooth of relative dimension one. -/
theorem mvPolynomial_isStandardSmoothOfRelativeDimension_one (ι : Type u) [Unique ι]
    (F : Type u) [CommRing F] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 F (MvPolynomial ι F) := by
  apply (mvPolynomialSubmersivePresentation ι F).isStandardSmoothOfRelativeDimension
  simp [Algebra.Presentation.dimension]

/-- Composing a morphism smooth of relative dimension `n` with an open immersion keeps it
smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_comp_openImmersion {X Y Z : Scheme.{u}} (n : ℕ) (f : X ⟶ Y)
    (g : Y ⟶ Z) [SmoothOfRelativeDimension n f] [IsOpenImmersion g] :
    SmoothOfRelativeDimension n (f ≫ g) := by
  simpa using smoothOfRelativeDimension_comp (n := n) (m := 0) f g

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : BundleData X ι)

/-- The projection of a rank-one bundle is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one_proj [Unique ι] : SmoothOfRelativeDimension 1 𝓔.proj := by
  let _ : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  let _ : MorphismProperty.RespectsIso
      (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}) :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @SmoothOfRelativeDimension 1)
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (fun j ↦ (𝓔.chartι j).opensRange) 𝓔.iSup_opensRange_chartι
  intro j
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (𝓔.chartι j) (Scheme.Opens.ι _)
    (congr_arg TopologicalSpace.Opens.carrier
      (𝓔.chartι j).opensRange.opensRange_ι.symm), Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)]
  rw [← (𝓔.isPullback_chart j).w]
  let _ : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, (𝓔.chart j).1) (MvPolynomial ι Γ(X, (𝓔.chart j).1))))) := by
    apply HasRingHomProperty.Spec_iff.mpr
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    apply (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr
    exact ZeroSectionCartier.mvPolynomial_isStandardSmoothOfRelativeDimension_one ι _
  have := ZeroSectionCartier.smoothOfRelativeDimension_comp_openImmersion 1
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, (𝓔.chart j).1) (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
    (isAffineOpen X (𝓔.chart j)).isoSpec.inv
  exact ZeroSectionCartier.smoothOfRelativeDimension_comp_openImmersion 1 _ _


/-! ### Order one of a generator of the maximal ideal -/

/-- In a local ring whose maximal ideal is generated by `t`, the order of vanishing `Ring.ord`
of `t` (the length of `R ⧸ (t)`) is one. -/
theorem ord_eq_one_of_maximalIdeal_eq_span {R : Type*} [CommRing R] [IsLocalRing R]
    {t : R} (ht : maximalIdeal R = Ideal.span {t}) : Ring.ord R t = 1 := by
  rw [Ring.ord, Module.length_eq_one_iff, ← ht]
  rw [isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective (S := R ⧸ maximalIdeal R)
    Ideal.Quotient.mk_surjective]
  let := Ideal.Quotient.field (maximalIdeal R)
  exact instIsSimpleModule _

/-- If the point stalk of `w ⤳ v` is one-dimensional and its maximal ideal is generated by the
class of `t ∈ 𝒪_{X,v}`, then `pointOrd` of the image of `t` in `κ(w)` is one. -/
theorem pointOrd_eq_one_of_maximalIdeal_eq_span {X : Scheme.{u}} [IsLocallyNoetherian X]
    {w v : X} (h : w ⤳ v) (hd : ringKrullDim (pointStalk h) = 1) (t : X.presheaf.stalk v)
    (ht : maximalIdeal (pointStalk h) = Ideal.span {Ideal.Quotient.mk _ t})
    (u : (X.residueField w)ˣ) (hu : (u : X.residueField w) = pointStalkMap h t) :
    pointOrd h u = 1 := by
  have := krullDimLE_one_pointStalk_of_eq_one hd
  have h1 := pointOrd_of_eq_one hd u
  have hne : (Ideal.Quotient.mk (RingHom.ker (pointStalkMap h)) t) ≠ 0 := by
    intro h0
    apply u.ne_zero
    rw [hu, ← pointStalk_algebraMap_mk, h0, map_zero]
  rw [hu, ← pointStalk_algebraMap_mk, Ring.ordFrac_eq_ord _ hne,
    Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hne)
      (n := 1) (ord_eq_one_of_maximalIdeal_eq_span ht)] at h1
  simpa using WithZero.coe_injective h1

/-! ### The maximal ideal of a point stalk at a point of a section -/

/-- `appLE` of a morphism equal to the identity is a restriction map. -/
private theorem appLE_eq_map_of_eq_id {Y : Scheme.{u}} (g : Y ⟶ Y) (hg : g = 𝟙 Y)
    (U V : Y.Opens) (e : V ≤ g ⁻¹ᵁ U) (hVU : V ≤ U) (a : Γ(Y, U)) :
    g.appLE U V e a = Y.presheaf.map (homOfLE hVU).op a := by
  subst hg
  rfl

/-- Let `p : E ⟶ X` be a retraction of a quasi-compact morphism `o : X ⟶ E`, let `r` generate
the kernel ideal of `o` on an affine open `U ∋ o x`, and let `q` be a point over `x` with
`q ⤳ o x`.  Then the maximal ideal of the point stalk `pointStalk (q ⤳ o x)` is generated by
the class of the germ of `r`. -/
theorem maximalIdeal_pointStalk_eq_span {X E : Scheme.{u}} (o : X ⟶ E) [QuasiCompact o]
    (p : E ⟶ X) (hop : o ≫ p = 𝟙 X) (x : X) (U : E.affineOpens) (r : Γ(E, U.1))
    (hU : o.ker.ideal U = Ideal.span {r}) (hx : o x ∈ U.1) {q : E} (hq : p q = x)
    (h : q ⤳ o x) :
    maximalIdeal (pointStalk h) =
      Ideal.span {Ideal.Quotient.mk _ (E.presheaf.germ U.1 (o x) hx r)} := by
  have hpo : p (o x) = x := by
    rw [← Scheme.Hom.comp_apply, hop]; rfl
  have hr0 : o.app U.1 r = 0 := by
    have : r ∈ o.ker.ideal U := hU ▸ Ideal.subset_span rfl
    rwa [Scheme.Hom.ker_apply] at this
  have hspan : ∀ (W : E.affineOpens) (hW : W.1 ≤ U.1),
      o.ker.ideal W = Ideal.span {E.presheaf.map (homOfLE hW).op r} := by
    intro W hW
    rw [← o.ker.map_ideal (U := W) (V := U) hW, hU, Ideal.map_span, Set.image_singleton]
    rfl
  apply le_antisymm
  · intro sbar hs
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective sbar
    have hs' : s ∈ maximalIdeal (E.presheaf.stalk (o x)) := fun hu ↦ hs (hu.map _)
    obtain ⟨W, hxW, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ s
    have hmem : o x ∈ W ⊓ U.1 ⊓ p ⁻¹ᵁ (o ⁻¹ᵁ W) := by
      refine ⟨⟨hxW, hx⟩, ?_⟩
      change o (p (o x)) ∈ W
      rw [hpo]; exact hxW
    obtain ⟨W', hW'aff, hxW', hW'le⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp E.isBasis_affineOpens) hmem
    let W'' : E.affineOpens := ⟨W', hW'aff⟩
    have hW'W : W' ≤ W := fun y hy ↦ (hW'le hy).1.1
    have hW'U : W' ≤ U.1 := fun y hy ↦ (hW'le hy).1.2
    have hW'p : W' ≤ p ⁻¹ᵁ (o ⁻¹ᵁ W) := fun y hy ↦ (hW'le hy).2
    set b := o.app W a with hb
    set b' := p.appLE (o ⁻¹ᵁ W) W' hW'p b with hb'
    set c := E.presheaf.map (homOfLE hW'W).op a - b' with hc
    -- `c` restricts to zero along `o`
    have hc0 : o.app W' c = 0 := by
      rw [Scheme.Hom.app_eq_appLE, map_sub, sub_eq_zero, hb', hb]
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← CommRingCat.comp_apply,
        Scheme.Hom.appLE_comp_appLE, appLE_eq_map_of_eq_id _ hop _ _ _
          (fun y hy ↦ hW'W hy)]
      rfl
    have hcmem : c ∈ Ideal.span {E.presheaf.map (homOfLE hW'U).op r} := by
      rw [← hspan W'' hW'U, Scheme.Hom.ker_apply]
      exact hc0
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hcmem
    have hgerm : E.presheaf.germ W (o x) hxW a = E.presheaf.germ W' (o x) hxW' d *
        E.presheaf.germ U.1 (o x) hx r + E.presheaf.germ W' (o x) hxW' b' := by
      rw [← E.presheaf.germ_res_apply (homOfLE hW'W) (o x) hxW' a,
        ← E.presheaf.germ_res_apply (homOfLE hW'U) _ hxW' r, ← map_mul, ← map_add, hd, hc,
        sub_add_cancel]
    -- the pullback of `o^* a` along `p` vanishes at `q`
    have hb'0 : pointStalkMap h (E.presheaf.germ W' (o x) hxW' b') = 0 := by
      rw [pointStalkMap_eq_zero_iff, TopCat.Presheaf.germ_stalkSpecializes_apply]
      intro hu
      have hq' : q ∈ E.basicOpen b' := (E.mem_basicOpen b' q _).2 hu
      rw [hb', Scheme.basicOpen_appLE] at hq'
      have h1 : p q ∈ X.basicOpen b := hq'.2
      rw [hq, hb, ← Scheme.preimage_basicOpen] at h1
      exact hs' ((E.mem_basicOpen a (o x) hxW).1 h1)
    have hz : Ideal.Quotient.mk (RingHom.ker (pointStalkMap h))
        (E.presheaf.germ W' (o x) hxW' b') = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hb'0
    rw [hgerm, map_add, hz, add_zero, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    intro hu
    have hu' : IsUnit (E.presheaf.germ U.1 (o x) hx r) := (isUnit_map_iff _ _).1 hu
    have : x ∈ o ⁻¹ᵁ E.basicOpen r := (E.mem_basicOpen r (o x) hx).2 hu'
    rw [Scheme.preimage_basicOpen, hr0, Scheme.basicOpen_zero] at this
    exact this

/-! ### The generic point of a fibre and the zero section -/

/-- The zero section is a section of the projection, pointwise. -/
@[simp]
theorem proj_zeroSection_apply (x : X) : 𝓔.proj (𝓔.zeroSection x) = x := by
  rw [← Scheme.Hom.comp_apply, 𝓔.zeroSection_proj]
  rfl

/-- The generic point of the fibre over `x` specialises to a point `q` of the total space exactly
when `x` specialises to the image of `q` in the base. -/
theorem bundlePoint_specializes_iff_proj (x : X) (q : 𝓔.totalSpace) :
    BundlePullbackGlobal.bundlePoint 𝓔 x ⤳ q ↔ x ⤳ 𝓔.proj q := by
  constructor
  · intro h
    have := h.map 𝓔.proj.base.hom.continuous
    rwa [BundlePullbackGlobal.proj_bundlePoint] at this
  · intro h
    let j := BundlePullbackGlobal.chartIndex 𝓔 (𝓔.proj q)
    have hq : 𝓔.proj q ∈ (𝓔.chart j).1 := BundlePullbackGlobal.mem_chart_chartIndex 𝓔 _
    have hx : x ∈ (𝓔.chart j).1 := h.mem_open (𝓔.chart j).1.isOpen hq
    have e := BundlePullbackGlobal.bundlePoint_chart 𝓔 j ⟨x, hx⟩
    change BundlePullbackGlobal.bundlePoint 𝓔 x = _ at e
    rw [e]
    exact (BundlePullbackGlobal.chartBundlePoint_specializes_iff 𝓔 j _ q hq).2 h

/-- For a rank-one bundle, the zero section at `x` and the generic point of the fibre over `x`
are distinct points: in a chart `Spec Γ(U)[T]` the second is the prime `p_x Γ(U)[T]`, which does
not contain `T`, while the first contains `T`. -/
theorem zeroSection_ne_bundlePoint [Unique ι] (x : X) :
    𝓔.zeroSection x ≠ BundlePullbackGlobal.bundlePoint 𝓔 x := by
  let j := BundlePullbackGlobal.chartIndex 𝓔 x
  have hx : x ∈ (𝓔.chart j).1 := BundlePullbackGlobal.mem_chart_chartIndex 𝓔 x
  let x' : (𝓔.chart j).1.toScheme := ⟨x, hx⟩
  let y := 𝓔.chartBasePoint j x'
  have hξ : BundlePullbackGlobal.bundlePoint 𝓔 x = (𝓔.chartι j).base
      (VectorBundle.bundlePoint
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1))) y) :=
    BundlePullbackGlobal.bundlePoint_chart 𝓔 j x'
  have hinv : (isAffineOpen X (𝓔.chart j)).isoSpec.inv.base y = x' := by
    change ((isAffineOpen X (𝓔.chart j)).isoSpec.hom ≫
      (isAffineOpen X (𝓔.chart j)).isoSpec.inv).base x' = x'
    rw [Iso.hom_inv_id]
    rfl
  have ho : 𝓔.zeroSection x = (𝓔.chartι j).base
      ((GradedCone.vertexSection (𝓔.chartAugmentation j)).base y) := by
    have := congrArg (fun f ↦ f.base y) (𝓔.zeroSection_chart j)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rw [← this, hinv]
    rfl
  rw [hξ, ho]
  intro h
  have h' := congrArg (fun z : PrimeSpectrum (MvPolynomial ι Γ(X, (𝓔.chart j).1)) ↦ z.asIdeal)
    ((𝓔.chartι j).isOpenEmbedding.injective h)
  have hmem : (MvPolynomial.X default : MvPolynomial ι Γ(X, (𝓔.chart j).1)) ∈
      Ideal.map (algebraMap Γ(X, (𝓔.chart j).1) (MvPolynomial ι Γ(X, (𝓔.chart j).1)))
        (y : PrimeSpectrum Γ(X, (𝓔.chart j).1)).asIdeal := by
    have h1 : (MvPolynomial.X default : MvPolynomial ι Γ(X, (𝓔.chart j).1)) ∈
        ((GradedCone.vertexSection (𝓔.chartAugmentation j)).base y).asIdeal := by
      change 𝓔.chartAugmentation j (MvPolynomial.X default) ∈
        (y : PrimeSpectrum Γ(X, (𝓔.chart j).1)).asIdeal
      simp
    simp only at h'
    rw [h'] at h1
    exact h1
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.mem_map_C_iff] at hmem
  have := hmem (Finsupp.single default 1)
  rw [MvPolynomial.coeff_X, if_pos rfl] at this
  exact (y : PrimeSpectrum Γ(X, (𝓔.chart j).1)).isPrime.ne_top
    ((Ideal.eq_top_iff_one _).2 this)

/-- The divisor of a rational section along `W` vanishes at points that are not
specialisations of the generic point of `W`. -/
private theorem divisor_apply_eq_zero_of_not_specializes {Y : Scheme.{u}} {L : LineBundleData Y}
    {W : IntegralClosedSubscheme Y} (s : L.RationalSection W) (dim : DimensionFunction Y)
    {v : Y} (h : ¬ W.genericPointImage ⤳ v) : (s.divisor dim : Y → ℚ) v = 0 := by
  unfold LineBundleData.RationalSection.divisor IntegralClosedSubscheme.pushforward
  by_cases hmem : v ∈ Set.range W.inclusion.base
  · obtain ⟨q, rfl⟩ := hmem
    exact absurd (W.genericPointImage_specializes q) h
  · exact AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range W.inclusion
      (dim : Y → ℤ) _ v hmem

end ZeroSectionCartier

variable {X : Scheme.{u}} {ι : Type u} [Unique ι] (𝓔 : BundleData X ι)

/-- The zero section of a rank-one bundle, as an effective Cartier divisor on the total space:
its ideal sheaf is the kernel of the zero section. -/
noncomputable def zeroSectionDivisor : Curves.EffectiveCartierDivisor 𝓔.totalSpace :=
  have := ZeroSectionCartier.smoothOfRelativeDimension_one_proj 𝓔
  Curves.EffectiveCartierDivisor.ofSection 𝓔.proj 𝓔.zeroSection 𝓔.zeroSection_proj

/-- The ideal sheaf of `zeroSectionDivisor 𝓔` is the kernel of the zero section. -/
theorem zeroSectionDivisor_idealSheaf :
    (zeroSectionDivisor 𝓔).idealSheaf = 𝓔.zeroSection.ker := rfl

/-- The support of `zeroSectionDivisor 𝓔` is the image of the zero section. -/
theorem coe_support_zeroSectionDivisor :
    ((zeroSectionDivisor 𝓔).support : Set 𝓔.totalSpace) = Set.range 𝓔.zeroSection := by
  change (𝓔.zeroSection.ker.support : Set 𝓔.totalSpace) = _
  rw [Scheme.Hom.support_ker, 𝓔.zeroSection.isClosedEmbedding.isClosed_range.closure_eq]

/-- The zero section at `x` lies in the support of `zeroSectionDivisor 𝓔`. -/
theorem zeroSection_mem_support_zeroSectionDivisor (x : X) :
    𝓔.zeroSection x ∈ (zeroSectionDivisor 𝓔).support := by
  rw [← SetLike.mem_coe, coe_support_zeroSectionDivisor]
  exact ⟨x, rfl⟩

/-- The generic point of the fibre over any `x` is not in the support of the zero-section
divisor. -/
theorem bundlePoint_not_mem_support_zeroSectionDivisor (x : X) :
    BundlePullbackGlobal.bundlePoint 𝓔 x ∉ (zeroSectionDivisor 𝓔).support := by
  intro h
  rw [← SetLike.mem_coe, coe_support_zeroSectionDivisor] at h
  obtain ⟨y, hy⟩ := h
  have hyx : y = x := by
    have := congrArg 𝓔.proj hy
    rwa [ZeroSectionCartier.proj_zeroSection_apply,
      BundlePullbackGlobal.proj_bundlePoint] at this
  subst hyx
  exact ZeroSectionCartier.zeroSection_ne_bundlePoint 𝓔 y hy

open scoped Classical in
/-- **The divisor of the canonical section of `O(o(X))` along a fibre closure.**  Let `W` be an
integral closed subscheme of the total space whose generic point is the generic point
`ξ = bundlePoint 𝓔 x` of `p⁻¹(closure x)`.  For a dimension function with
`dimE ξ = dimE (o x) + 1`, the divisor of the canonical section of the line bundle of the
zero-section divisor along `W` is the cycle with coefficient `1` at `o x` and `0` elsewhere. -/
theorem canonicalSection_zeroSectionDivisor_divisor [IsLocallyNoetherian 𝓔.totalSpace] (x : X)
    (W : IntegralClosedSubscheme 𝓔.totalSpace)
    (hWξ : W.genericPointImage = BundlePullbackGlobal.bundlePoint 𝓔 x)
    (hW : W.genericPointImage ∉ (zeroSectionDivisor 𝓔).support)
    (dimE : DimensionFunction 𝓔.totalSpace)
    (hdim : dimE (BundlePullbackGlobal.bundlePoint 𝓔 x) = dimE (𝓔.zeroSection x) + 1) :
    ((zeroSectionDivisor 𝓔).canonicalSection W hW).divisor dimE =
      Function.locallyFinsuppWithin.single (𝓔.zeroSection x) (1 : ℚ) := by
  have hξo : W.genericPointImage ⤳ 𝓔.zeroSection x := by
    rw [hWξ, ZeroSectionCartier.bundlePoint_specializes_iff_proj,
      ZeroSectionCartier.proj_zeroSection_apply]
  apply Function.locallyFinsuppWithin.coe_injective
  funext v
  beta_reduce
  rw [Function.locallyFinsuppWithin.single_apply]
  by_cases hvs : v ∈ (zeroSectionDivisor 𝓔).support
  swap
  · rw [(zeroSectionDivisor 𝓔).canonicalSection_divisor_apply_eq_zero W hW dimE hvs, if_neg]
    rintro rfl
    exact hvs (zeroSection_mem_support_zeroSectionDivisor 𝓔 x)
  by_cases h : W.genericPointImage ⤳ v
  swap
  · rw [ZeroSectionCartier.divisor_apply_eq_zero_of_not_specializes _ dimE h, if_neg]
    rintro rfl
    exact h hξo
  rw [(zeroSectionDivisor 𝓔).canonicalSection_divisor_apply W hW dimE h v
    ((zeroSectionDivisor 𝓔).mem_localEquationOpen v)]
  by_cases hvo : v = 𝓔.zeroSection x
  · subst hvo
    rw [if_pos rfl]
    have hd : ringKrullDim (pointStalk h) = 1 :=
      (W.ringKrullDim_pointStalk_eq_one_iff_covBy rfl h).2
        (covBy_of_dim_eq_add_one dimE h (by rw [hWξ]; exact hdim))
    have hq : 𝓔.proj W.genericPointImage = x := by
      rw [hWξ, BundlePullbackGlobal.proj_bundlePoint]
    have := ZeroSectionCartier.pointOrd_eq_one_of_maximalIdeal_eq_span h hd
      (𝓔.totalSpace.presheaf.germ _ (𝓔.zeroSection x)
        ((zeroSectionDivisor 𝓔).mem_localEquationOpen _)
        ((zeroSectionDivisor 𝓔).localEquation (𝓔.zeroSection x)))
      (ZeroSectionCartier.maximalIdeal_pointStalk_eq_span 𝓔.zeroSection 𝓔.proj
        𝓔.zeroSection_proj x ((zeroSectionDivisor 𝓔).localEquationOpen (𝓔.zeroSection x))
        ((zeroSectionDivisor 𝓔).localEquation (𝓔.zeroSection x))
        ((zeroSectionDivisor 𝓔).ideal_localEquationOpen _)
        ((zeroSectionDivisor 𝓔).mem_localEquationOpen _) hq h)
      ((zeroSectionDivisor 𝓔).equationResidueUnit _
        (h.mem_open (TopologicalSpace.Opens.isOpen _)
          ((zeroSectionDivisor 𝓔).mem_localEquationOpen _)) hW) (by
          rw [Curves.EffectiveCartierDivisor.equationResidueUnit_val, pointStalkMap_apply,
            TopCat.Presheaf.germ_stalkSpecializes_apply])
    exact_mod_cast this
  · rw [if_neg hvo]
    rw [pointOrd_of_ne_one]
    · rfl
    intro hd
    have hcov := (W.ringKrullDim_pointStalk_eq_one_iff_covBy rfl h).1 hd
    rw [← SetLike.mem_coe, coe_support_zeroSectionDivisor] at hvs
    obtain ⟨y, rfl⟩ := hvs
    have hxy : x ⤳ y := by
      have := (ZeroSectionCartier.bundlePoint_specializes_iff_proj 𝓔 x _).1 (hWξ ▸ h)
      rwa [ZeroSectionCartier.proj_zeroSection_apply] at this
    have h1 : 𝓔.zeroSection x ⤳ 𝓔.zeroSection y := hxy.map 𝓔.zeroSection.base.hom.continuous
    have hlt1 : 𝓔.zeroSection y < 𝓔.zeroSection x :=
      lt_iff_le_not_ge.2 ⟨h1, fun h2 ↦ hvo (Specializes.antisymm h2 h1).eq⟩
    have hlt2 : 𝓔.zeroSection x < W.genericPointImage := by
      refine lt_iff_le_not_ge.2 ⟨hξo, fun h2 ↦ hW ?_⟩
      rw [(Specializes.antisymm hξo h2).eq]
      exact zeroSection_mem_support_zeroSectionDivisor 𝓔 x
    exact hcov.2 hlt1 hlt2

open scoped Classical in
/-- `canonicalSection_zeroSectionDivisor_divisor` for `W = pointSubscheme ξ`, where
`ξ = bundlePoint 𝓔 x` is the generic point of `p⁻¹(closure x)`: for a dimension function with
`dimE ξ = dimE (o x) + 1`, the divisor of the canonical section is the cycle with coefficient `1`
at `o x` and `0` elsewhere. -/
theorem canonicalSection_pointSubscheme_zeroSectionDivisor_divisor
    [IsLocallyNoetherian 𝓔.totalSpace] [TopologicalSpace.NoetherianSpace 𝓔.totalSpace] (x : X)
    (dimE : DimensionFunction 𝓔.totalSpace)
    (hdim : dimE (BundlePullbackGlobal.bundlePoint 𝓔 x) = dimE (𝓔.zeroSection x) + 1) :
    ((zeroSectionDivisor 𝓔).canonicalSection
        (LineBundleInjective.pointSubscheme (BundlePullbackGlobal.bundlePoint 𝓔 x))
        ((zeroSectionDivisor 𝓔).genericPointImage_pointSubscheme_not_mem
          (bundlePoint_not_mem_support_zeroSectionDivisor 𝓔 x))).divisor dimE =
      Function.locallyFinsuppWithin.single (𝓔.zeroSection x) (1 : ℚ) :=
  canonicalSection_zeroSectionDivisor_divisor 𝓔 x _
    (LineBundleInjective.genericPointImage_pointSubscheme _) _ dimE hdim

end GromovWitten.AlgebraicGeometry.IntersectionTheory
