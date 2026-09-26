/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperCurveDegreeFinal

/-!
# The transcendental case of `deg (div r) = 0` on a regular proper curve

Let `W` be an integral scheme over a field `k` all of whose local rings are valuation rings, let
`r` be a nonzero rational function on `W` and let `p : W ⟶ ℙ¹_k` be the morphism defined by `r`
(`RationalFunction.toProjectiveLine`).  This file identifies the preimages of the two standard
charts of `ℙ¹_k` under `p` with the two domains of definition of `r` and of `r⁻¹`:

* `preimage_chartZero_eq_regularLocus` : `p ⁻¹ᵁ (chartZero k).opensRange = regularLocus r`;
* `preimage_chartOne_eq_regularLocus_inv` : `p ⁻¹ᵁ (chartOne k).opensRange = regularLocus r⁻¹`.

Together with `isAffineOpen_preimage_chart` (the preimage of a standard chart under a finite
morphism is an affine open) this shows that both domains of definition are affine opens as soon as
`p` is finite, which is the remaining geometric input of
`degreeCycle_principalCycle_eq_zero_of_isAffineOpen`.  The file also shows that the coordinate ring
of the first domain of definition is a finite `k[t]`-module (`finite_toChartHom`) and assembles
everything into `RegularProperCurve.degreeCycle_principalCycle_eq_zero`, whose only remaining
hypothesis is a `ChartPresentation`, i.e. the comparison of the two chart fibre dimensions.

The proof of the chart identification is a computation with basic opens.  Over the open set `U` on
which a regular function `σ` represents `r`, the morphism `p` factors as `toChart f U σ ≫ chartZero`
(dually for `r⁻¹` and `chartOne`); the intersection of the two charts of `ℙ¹_k` is the basic open
set `D(t)` of either chart (`ProjectiveLine.preimage_opensRange_chartZero`), and `toChart f U σ`
pulls `D(t)` back to the locus where `σ` is invertible (`toChart_preimage_basicOpen_coord`, via
`Scheme.Opens.ι_image_basicOpen_topIso_inv`).  So `p x` lies in the other chart exactly when `σ` is
a unit at `x`, i.e. exactly when `r⁻¹` is regular at `x`.

## Main declarations

* `toChart_preimage_basicOpen_coord`, `mem_basicOpen_coord_toChart_iff` — the morphism to the
  standard chart pulls `D(t)` back to the locus where the defining section is invertible.
* `mem_regularLocus_inv_of_isUnit_germ` — if a section representing `r` is a unit at `x` then
  `r⁻¹` is regular at `x`.
* `preimage_chartZero_eq_regularLocus`, `preimage_chartOne_eq_regularLocus_inv` — the two chart
  preimages.
* `isAffineOpen_regularLocus_of_isFinite`, `isAffineOpen_regularLocus_inv_of_isFinite`,
  `RegularProperCurve.isAffineOpen_regularLocus`,
  `RegularProperCurve.isAffineOpen_regularLocus_inv` — both domains of definition are affine when
  the morphism to `ℙ¹_k` is finite, which on a regular proper curve happens as soon as `r` is
  transcendental over `k` (`RegularProperCurve.isFinite_toProjectiveLine`).
* `isFinite_toChart`, `finite_toChartHom` — the first chart ring is a finite `k[t]`-module, `t`
  acting as the regular function representing `r`.
* `inf_regularLocus_eq_basicOpen`, `basicOpen_regularSection_inv` — the intersection of the two
  domains of definition is the basic open set cut out by either of the two representing sections.
* `finrank_quotient_span_eq_finrank_of_injective`, `finrank_eq_of_localizationAway_equiv`,
  `overlapLift`, `finrank_eq_of_isLocalizationAway` — the algebra of the comparison of the two chart
  dimensions: the fibre dimension over the origin is the rank over `k[t]`, and two module-finite
  `k[t]`-algebras with isomorphic localisations away from `t` have the same rank, either over the
  transition automorphism `t ↦ t⁻¹` of `k[t, t⁻¹]` or, in the directly applicable form
  `finrank_eq_of_isLocalizationAway`, given an isomorphism of the two localisations carrying the
  image of `t` to the inverse of the image of `t`.
* `ChartPresentation` — the bundled remaining input: presentations of the two chart rings with
  equal fibre dimensions.
* `RegularProperCurve.degreeCycle_principalCycle_eq_zero_of_chartPresentation`,
  `RegularProperCurve.degreeCycle_principalCycle_eq_zero` — the degree of a principal divisor on a
  regular proper curve vanishes, the algebraic case unconditionally and the transcendental case
  given a `ChartPresentation`.

-/

universe u

open CategoryTheory AlgebraicGeometry Topology

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperCurveDegree

open ProjectiveLine

variable {k : Type u} [Field k]

/-! ## Pulling back the basic open set `D(t)` of the standard chart -/

/-- **The morphism to the standard chart `𝔸¹_k = Spec k[t]` defined by a regular function `σ` on
`U` pulls the basic open set `D(t)` back to the locus where `σ` is invertible.** -/
theorem toChart_preimage_basicOpen_coord {W : Scheme.{u}} (f : W ⟶ Spec (CommRingCat.of k))
    (U : W.Opens) (σ : Γ(W, U)) :
    RationalFunction.toChart f U σ ⁻¹ᵁ
        (chart k).basicOpen (RationalFunction.coord (k := k)) =
      U.ι ⁻¹ᵁ W.basicOpen σ := by
  rw [Scheme.preimage_basicOpen_top, RationalFunction.toChart_appTop_coord f U σ,
    ← U.ι.preimage_image_eq (U.toScheme.basicOpen (U.topIso.inv σ)),
    Scheme.Opens.ι_image_basicOpen_topIso_inv]

/-- The image of the overlap `Spec k[t, t⁻¹]` in the standard chart is the basic open set
`D(t)`. -/
theorem opensRange_overlapToChartZero :
    (overlapToChartZero k).opensRange =
      (chart k).basicOpen (RationalFunction.coord (k := k)) :=
  (Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (Polynomial k))
      (Polynomial.X : Polynomial k)).trans
    (AlgebraicGeometry.basicOpen_eq_of_affine (R := CommRingCat.of (Polynomial k))
      (Polynomial.X : Polynomial k)).symm

/-- The image of the overlap in the second standard chart is also the basic open set `D(t)`. -/
theorem opensRange_overlapToChartOne :
    (overlapToChartOne k).opensRange =
      (chart k).basicOpen (RationalFunction.coord (k := k)) :=
  (TopologicalSpace.Opens.ext (range_overlapToChartOne k)).trans
    (opensRange_overlapToChartZero (k := k))

/-- **A point of `U` is mapped into `D(t)` by `toChart f U σ` exactly when `σ` is invertible at
that point.** -/
theorem mem_basicOpen_coord_toChart_iff {W : Scheme.{u}} (f : W ⟶ Spec (CommRingCat.of k))
    (U : W.Opens) (σ : Γ(W, U)) (x : W) (hx : x ∈ U) :
    (RationalFunction.toChart f U σ).base ⟨x, hx⟩ ∈
        (chart k).basicOpen (RationalFunction.coord (k := k)) ↔
      IsUnit (W.presheaf.germ U x hx σ) := by
  have h1 : (⟨x, hx⟩ : U) ∈ RationalFunction.toChart f U σ ⁻¹ᵁ
      (chart k).basicOpen (RationalFunction.coord (k := k)) ↔
      (⟨x, hx⟩ : U) ∈ U.ι ⁻¹ᵁ W.basicOpen σ := by
    rw [toChart_preimage_basicOpen_coord]
  exact h1.trans (W.mem_basicOpen σ x hx)

/-! ## Invertibility of a representing section and regularity of the inverse -/

/-- **If a regular function `σ` on `U` represents the rational function `r` and is invertible at a
point `x` of `U`, then `r⁻¹` is regular at `x`.** -/
theorem mem_regularLocus_inv_of_isUnit_germ {X : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral X] {r : X.functionField} {U : X.Opens} [Nonempty U]
    (hgen : genericPoint X ∈ U) (σ : Γ(X, U))
    (hσ : X.presheaf.germ U (genericPoint X) hgen σ = r) {x : X} (hx : x ∈ U)
    (hu : IsUnit (X.presheaf.germ U x hx σ)) : x ∈ Scheme.regularLocus r⁻¹ := by
  obtain ⟨v, hv⟩ := hu
  refine Scheme.mem_regularLocus_iff.mpr ⟨(↑v⁻¹ : X.presheaf.stalk x), ?_⟩
  have hmap : algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ U x hx σ) = r := by
    rw [X.algebraMap_germ_eq_germToFunctionField hx σ]
    exact hσ
  have hmul : X.presheaf.germ U x hx σ * (↑v⁻¹ : X.presheaf.stalk x) = 1 := by
    rw [← hv]
    exact v.mul_inv
  have key : r * algebraMap (X.presheaf.stalk x) X.functionField
      (↑v⁻¹ : X.presheaf.stalk x) = 1 := by
    rw [← hmap, ← map_mul, hmul, map_one]
  exact (inv_eq_of_mul_eq_one_right key).symm

/-! ## The two chart preimages -/

variable {W : Scheme.{u}} [_root_.AlgebraicGeometry.IsIntegral W]
  (f : W ⟶ Spec (CommRingCat.of k))
  (hv : ∀ x : W, ValuationRing (W.presheaf.stalk x)) (r : W.functionField)

/-- On the domain of definition of `r⁻¹` the morphism to `ℙ¹_k` is the morphism to the second
standard chart defined by the regular function `r⁻¹`.  This is the mirror image of
`RationalFunction.ι_toProjectiveLine`. -/
theorem ι_toProjectiveLine_one (hr : r ≠ 0) :
    (Scheme.regularLocus r⁻¹).ι ≫ RationalFunction.toProjectiveLine f hv r hr =
      RationalFunction.toChart f (Scheme.regularLocus r⁻¹) (Scheme.regularSection r⁻¹) ≫
        chartOne k :=
  (RationalFunction.chartPairOfValuationRing hv r).ι_toProjectiveLine₁ f hr

include hv in
/-- Every point of `W` lies in the domain of definition of `r` or in that of `r⁻¹`. -/
theorem mem_regularLocus_sup (x : W) :
    x ∈ Scheme.regularLocus r ⊔ Scheme.regularLocus r⁻¹ := by
  rw [Scheme.regularLocus_sup_regularLocus_inv_eq_top hv r]
  trivial

/-- **The preimage of the first standard chart of `ℙ¹_k` under the morphism defined by `r` is the
domain of definition of `r`.** -/
theorem preimage_chartZero_eq_regularLocus (hr : r ≠ 0) :
    RationalFunction.toProjectiveLine f hv r hr ⁻¹ᵁ (chartZero k).opensRange =
      Scheme.regularLocus r := by
  refine le_antisymm (fun x hx => ?_) (regularLocus_le_preimage_chartZero f hv r hr)
  rcases TopologicalSpace.Opens.mem_sup.mp (mem_regularLocus_sup hv r x) with h | h₁
  · exact h
  have hbase := congrArg (fun g : (Scheme.regularLocus r⁻¹).toScheme ⟶ ProjectiveLine.scheme k =>
    g.base ⟨x, h₁⟩) (ι_toProjectiveLine_one f hv r hr)
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp] at hbase
  have hmem : (RationalFunction.toChart f (Scheme.regularLocus r⁻¹)
      (Scheme.regularSection r⁻¹)).base ⟨x, h₁⟩ ∈
      (chart k).basicOpen (RationalFunction.coord (k := k)) := by
    rw [← opensRange_overlapToChartOne, ← preimage_opensRange_chartZero k]
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy.trans hbase⟩
  have hinv := mem_regularLocus_inv_of_isUnit_germ
    (Scheme.genericPoint_mem_regularLocus r⁻¹) (Scheme.regularSection r⁻¹)
    (Scheme.germ_regularSection r⁻¹) h₁
    ((mem_basicOpen_coord_toChart_iff f _ _ x h₁).mp hmem)
  rwa [inv_inv] at hinv

/-- The domain of definition of `r⁻¹` is contained in the preimage of the second standard
chart. -/
theorem regularLocus_inv_le_preimage_chartOne (hr : r ≠ 0) :
    Scheme.regularLocus r⁻¹ ≤
      RationalFunction.toProjectiveLine f hv r hr ⁻¹ᵁ (chartOne k).opensRange := by
  intro x hx
  have h := congrArg (fun g : (Scheme.regularLocus r⁻¹).toScheme ⟶ ProjectiveLine.scheme k =>
    g.base ⟨x, hx⟩) (ι_toProjectiveLine_one f hv r hr)
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp] at h
  exact ⟨_, h.symm⟩

/-- **The preimage of the second standard chart of `ℙ¹_k` under the morphism defined by `r` is the
domain of definition of `r⁻¹`.** -/
theorem preimage_chartOne_eq_regularLocus_inv (hr : r ≠ 0) :
    RationalFunction.toProjectiveLine f hv r hr ⁻¹ᵁ (chartOne k).opensRange =
      Scheme.regularLocus r⁻¹ := by
  refine le_antisymm (fun x hx => ?_) (regularLocus_inv_le_preimage_chartOne f hv r hr)
  rcases TopologicalSpace.Opens.mem_sup.mp (mem_regularLocus_sup hv r x) with h₀ | h
  swap
  · exact h
  have hbase := congrArg (fun g : (Scheme.regularLocus r).toScheme ⟶ ProjectiveLine.scheme k =>
    g.base ⟨x, h₀⟩) (RationalFunction.ι_toProjectiveLine f hv r hr)
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp] at hbase
  have hmem : (RationalFunction.toChart f (Scheme.regularLocus r)
      (Scheme.regularSection r)).base ⟨x, h₀⟩ ∈
      (chart k).basicOpen (RationalFunction.coord (k := k)) := by
    rw [← opensRange_overlapToChartZero, ← preimage_opensRange_chartOne k]
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy.trans hbase⟩
  exact mem_regularLocus_inv_of_isUnit_germ
    (Scheme.genericPoint_mem_regularLocus r) (Scheme.regularSection r)
    (Scheme.germ_regularSection r) h₀
    ((mem_basicOpen_coord_toChart_iff f _ _ x h₀).mp hmem)

/-! ## Affineness of the two domains of definition -/

include hv in
/-- **The domain of definition of `r` is an affine open** as soon as the morphism to `ℙ¹_k`
defined by `r` is finite: it is the preimage of the first standard chart. -/
theorem isAffineOpen_regularLocus_of_isFinite (hr : r ≠ 0)
    (hfin : IsFinite (RationalFunction.toProjectiveLine f hv r hr)) :
    IsAffineOpen (Scheme.regularLocus r) := by
  have _ := hfin
  rw [← preimage_chartZero_eq_regularLocus f hv r hr]
  exact isAffineOpen_preimage_chart _ (chartZero k)

include hv in
/-- **The domain of definition of `r⁻¹` is an affine open** as soon as the morphism to `ℙ¹_k`
defined by `r` is finite: it is the preimage of the second standard chart. -/
theorem isAffineOpen_regularLocus_inv_of_isFinite (hr : r ≠ 0)
    (hfin : IsFinite (RationalFunction.toProjectiveLine f hv r hr)) :
    IsAffineOpen (Scheme.regularLocus r⁻¹) := by
  have _ := hfin
  rw [← preimage_chartOne_eq_regularLocus_inv f hv r hr]
  exact isAffineOpen_preimage_chart _ (chartOne k)

namespace RegularProperCurve

variable (X : _root_.GromovWitten.AlgebraicGeometry.RegularProperCurve k)

/-- **The morphism to `ℙ¹_k` defined by a rational function transcendental over `k` on a regular
proper curve is finite.** -/
theorem isFinite_toProjectiveLine (r : X.W.functionField) (hr : r ≠ 0)
    (htr : Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField X.f).hom r)) :
    IsFinite (RationalFunction.toProjectiveLine X.f X.valuationRing_stalk r hr) :=
  RationalFunction.isFinite_toProjectiveLine X.f X.valuationRing_stalk r hr
    X.finite_of_isClosed X.isClosed_singleton htr

/-- **On a regular proper curve the domain of definition of a rational function transcendental
over `k` is an affine open.** -/
theorem isAffineOpen_regularLocus (r : X.W.functionField) (hr : r ≠ 0)
    (htr : Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField X.f).hom r)) :
    IsAffineOpen (Scheme.regularLocus r) :=
  ProperCurveDegree.isAffineOpen_regularLocus_of_isFinite X.f X.valuationRing_stalk r hr
    (isFinite_toProjectiveLine X r hr htr)

/-- **On a regular proper curve the domain of definition of the inverse of a rational function
transcendental over `k` is an affine open.** -/
theorem isAffineOpen_regularLocus_inv (r : X.W.functionField) (hr : r ≠ 0)
    (htr : Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField X.f).hom r)) :
    IsAffineOpen (Scheme.regularLocus r⁻¹) :=
  ProperCurveDegree.isAffineOpen_regularLocus_inv_of_isFinite X.f X.valuationRing_stalk r hr
    (isFinite_toProjectiveLine X r hr htr)

end RegularProperCurve

/-! ## Module-finiteness of the first chart ring over `k[t]` -/

include hv in
/-- **The restriction of the morphism to `ℙ¹_k` over the first standard chart is the morphism to
that chart defined by `r`.**  Both sides are morphisms `regularLocus r ⟶ 𝔸¹_k`; they agree because
the chart `chartZero k` is a monomorphism and both become `(regularLocus r).ι ≫ p` after composing
with it. -/
theorem isoOfEq_morphismRestrict_isoOpensRange_inv (hr : r ≠ 0) :
    (W.isoOfEq (preimage_chartZero_eq_regularLocus f hv r hr).symm).hom ≫
        (RationalFunction.toProjectiveLine f hv r hr ∣_ (chartZero k).opensRange) ≫
          (chartZero k).isoOpensRange.inv =
      RationalFunction.toChart f (Scheme.regularLocus r) (Scheme.regularSection r) := by
  rw [← cancel_mono (chartZero k), Category.assoc, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι, ← Category.assoc,
    Scheme.isoOfEq_hom_ι, RationalFunction.ι_toProjectiveLine]

include hv in
/-- **The morphism to the first standard chart defined by `r` is finite** when the morphism to
`ℙ¹_k` is finite: it is the restriction of the latter over an open subset. -/
theorem isFinite_toChart (hr : r ≠ 0)
    (hfin : IsFinite (RationalFunction.toProjectiveLine f hv r hr)) :
    IsFinite (RationalFunction.toChart f (Scheme.regularLocus r) (Scheme.regularSection r)) := by
  have _ := hfin
  rw [← isoOfEq_morphismRestrict_isoOpensRange_inv f hv r hr]
  infer_instance

include hv in
/-- **The first chart ring is a finite `k[t]`-module**, where `t` acts as the regular function
representing `r`.  This is the module-finiteness input of the comparison of the two chart
dimensions. -/
theorem finite_toChartHom (hr : r ≠ 0)
    (hfin : IsFinite (RationalFunction.toProjectiveLine f hv r hr))
    (hU₀ : IsAffineOpen (Scheme.regularLocus r)) :
    RingHom.Finite (RationalFunction.toChartHom f (Scheme.regularLocus r)
      (Scheme.regularSection r)).hom := by
  have hfc := isFinite_toChart f hv r hr hfin
  rw [RationalFunction.toChart] at hfc
  refine (IsFinite.SpecMap_iff _).mp ?_
  have heq : Spec.map (RationalFunction.toChartHom f (Scheme.regularLocus r)
      (Scheme.regularSection r)) = hU₀.isoSpec.inv ≫
      ((Scheme.regularLocus r).toSpecΓ ≫ Spec.map (RationalFunction.toChartHom f
        (Scheme.regularLocus r) (Scheme.regularSection r))) := by
    rw [← Category.assoc, hU₀.isoSpec_inv_toSpecΓ, Category.id_comp]
  rw [heq]
  infer_instance

/-! ## The intersection of the two domains of definition -/

include hv in
/-- **The intersection of the two domains of definition of `r` and `r⁻¹` is the locus where the
regular function representing `r` is invertible.**  Hence it is the basic open subset cut out by
that function, and `Γ` of it is the localisation of the first chart ring away from it. -/
theorem inf_regularLocus_eq_basicOpen (hr : r ≠ 0) :
    Scheme.regularLocus r ⊓ Scheme.regularLocus r⁻¹ =
      W.basicOpen (Scheme.regularSection r) := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨h₀, h₁⟩ := hx
    have hZ : genericPoint W ∈ Scheme.regularLocus r ⊓ Scheme.regularLocus r⁻¹ :=
      ⟨Scheme.genericPoint_mem_regularLocus r, Scheme.genericPoint_mem_regularLocus r⁻¹⟩
    have hle₀ : Scheme.regularLocus r ⊓ Scheme.regularLocus r⁻¹ ≤ Scheme.regularLocus r :=
      inf_le_left
    have hle₁ : Scheme.regularLocus r ⊓ Scheme.regularLocus r⁻¹ ≤ Scheme.regularLocus r⁻¹ :=
      inf_le_right
    have hmul : W.presheaf.map (homOfLE hle₀).op (Scheme.regularSection r) *
        W.presheaf.map (homOfLE hle₁).op (Scheme.regularSection r⁻¹) = 1 :=
      (RationalFunction.chartPairOfValuationRing hv r).res_mul_res hr hle₀ hle₁ hZ
    have hg := congrArg (fun σ => W.presheaf.germ
      (Scheme.regularLocus r ⊓ Scheme.regularLocus r⁻¹) x ⟨h₀, h₁⟩ σ) hmul
    simp only [map_mul, map_one] at hg
    rw [W.presheaf.germ_res_apply (homOfLE hle₀) x ⟨h₀, h₁⟩,
      W.presheaf.germ_res_apply (homOfLE hle₁) x ⟨h₀, h₁⟩] at hg
    exact (W.mem_basicOpen _ x h₀).mpr (isUnit_iff_exists_inv.mpr ⟨_, hg⟩)
  · have h₀ : x ∈ Scheme.regularLocus r := W.basicOpen_le (Scheme.regularSection r) hx
    refine ⟨h₀, mem_regularLocus_inv_of_isUnit_germ
      (Scheme.genericPoint_mem_regularLocus r) (Scheme.regularSection r)
      (Scheme.germ_regularSection r) h₀ ((W.mem_basicOpen _ x h₀).mp hx)⟩

/-- **The regular function representing a nonzero rational function is nonzero.** -/
theorem regularSection_ne_zero (hr : r ≠ 0) : Scheme.regularSection r ≠ 0 := by
  intro h
  refine hr ?_
  rw [← Scheme.germ_regularSection r, h, map_zero]

include hv in
/-- **The two basic open subsets cut out by the regular functions representing `r` and `r⁻¹`
coincide**, both being the intersection of the two domains of definition. -/
theorem basicOpen_regularSection_inv (hr : r ≠ 0) :
    W.basicOpen (Scheme.regularSection r⁻¹) = W.basicOpen (Scheme.regularSection r) := by
  have h := inf_regularLocus_eq_basicOpen hv r⁻¹ (inv_ne_zero hr)
  rw [inv_inv] at h
  rw [← h, inf_comm, inf_regularLocus_eq_basicOpen hv r hr]

/-- **The `k[t]`-algebra structure of the first chart ring is injective** when `r` is
transcendental over `k`; together with module-finiteness this makes the chart ring a free
`k[t]`-module. -/
theorem injective_toChartHom_regularSection
    (htr : Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField f).hom r)) :
    Function.Injective (RationalFunction.toChartHom f (Scheme.regularLocus r)
      (Scheme.regularSection r)).hom :=
  RationalFunction.injective_toChartHom f (Scheme.regularLocus r)
    (Scheme.genericPoint_mem_regularLocus r) (Scheme.regularSection r)
    (by rw [Scheme.germ_regularSection]; exact htr)

/-! ## Comparison of the two chart dimensions -/

section Ranks

/-- **The `k`-dimension of the fibre of a module-finite `k[t]`-algebra over the origin is its rank
over `k[t]`.**  Such an algebra is automatically free: `k[t]` is a principal ideal domain and a
domain over which the structure map is injective is torsion-free. -/
theorem finrank_quotient_span_eq_finrank_of_injective (B : Type u) [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra (Polynomial k) B] [IsScalarTower k (Polynomial k) B]
    [Module.Finite (Polynomial k) B]
    (hinj : Function.Injective (algebraMap (Polynomial k) B)) :
    Module.finrank k (B ⧸ Ideal.span {algebraMap (Polynomial k) B Polynomial.X}) =
      Module.finrank (Polynomial k) B := by
  have _ : Module.Free (Polynomial k) B := free_of_finite_of_injective hinj
  exact finrank_quotient_span_X_eq_finrank B

/-- **Two module-finite `k[t]`-algebras whose localisations away from `t` are isomorphic over the
transition automorphism `t ↦ t⁻¹` of `k[t, t⁻¹]` have the same rank.**  This is the comparison of
the two chart dimensions of the morphism `W ⟶ ℙ¹_k` determined by a rational function `r`: the two
localisations are both the ring of functions on the intersection of the two domains of definition
of `r` and `r⁻¹`, and the two `k[t, t⁻¹]`-structures on it differ by `t ↦ t⁻¹`. -/
theorem finrank_eq_of_localizationAway_equiv (B₀ B₁ C₀ C₁ : Type u)
    [CommRing B₀] [IsDomain B₀] [Algebra (Polynomial k) B₀] [Module.Finite (Polynomial k) B₀]
    [CommRing B₁] [IsDomain B₁] [Algebra (Polynomial k) B₁] [Module.Finite (Polynomial k) B₁]
    [CommRing C₀] [Algebra B₀ C₀] [Algebra (Polynomial k) C₀] [Algebra (overlapRing k) C₀]
    [IsScalarTower (Polynomial k) (overlapRing k) C₀] [IsScalarTower (Polynomial k) B₀ C₀]
    [IsLocalization (Algebra.algebraMapSubmonoid B₀
      (Submonoid.powers (Polynomial.X : Polynomial k))) C₀]
    [CommRing C₁] [Algebra B₁ C₁] [Algebra (Polynomial k) C₁] [Algebra (overlapRing k) C₁]
    [IsScalarTower (Polynomial k) (overlapRing k) C₁] [IsScalarTower (Polynomial k) B₁ C₁]
    [IsLocalization (Algebra.algebraMapSubmonoid B₁
      (Submonoid.powers (Polynomial.X : Polynomial k))) C₁]
    (hinj₀ : Function.Injective (algebraMap (Polynomial k) B₀))
    (hinj₁ : Function.Injective (algebraMap (Polynomial k) B₁))
    (Φ : C₀ ≃+* C₁)
    (hΦ : (algebraMap (overlapRing k) C₁).comp (flipRingEquiv k).toRingHom =
      Φ.toRingHom.comp (algebraMap (overlapRing k) C₀)) :
    Module.finrank (Polynomial k) B₀ = Module.finrank (Polynomial k) B₁ := by
  have _ : Module.Free (Polynomial k) B₀ := free_of_finite_of_injective hinj₀
  have _ : Module.Free (Polynomial k) B₁ := free_of_finite_of_injective hinj₁
  have h₀ : Module.finrank (overlapRing k) C₀ = Module.finrank (Polynomial k) B₀ :=
    finrank_localization_eq_finrank (Submonoid.powers (Polynomial.X : Polynomial k))
      (overlapRing k) B₀ C₀
  have h₁ : Module.finrank (overlapRing k) C₁ = Module.finrank (Polynomial k) B₁ :=
    finrank_localization_eq_finrank (Submonoid.powers (Polynomial.X : Polynomial k))
      (overlapRing k) B₁ C₁
  rw [← h₀, ← h₁]
  exact Algebra.finrank_eq_of_equiv_equiv (flipRingEquiv k) Φ hΦ

/-- **The `k[t, t⁻¹]`-algebra structure on a `k[t]`-algebra in which `t` becomes a unit.** -/
noncomputable def overlapLift {C : Type u} [CommRing C] (g : Polynomial k →+* C)
    (hg : IsUnit (g Polynomial.X)) : overlapRing k →+* C :=
  IsLocalization.Away.lift (S := overlapRing k) (Polynomial.X : Polynomial k) hg

@[simp] lemma overlapLift_algebraMap {C : Type u} [CommRing C] (g : Polynomial k →+* C)
    (hg : IsUnit (g Polynomial.X)) (q : Polynomial k) :
    overlapLift g hg (algebraMap (Polynomial k) (overlapRing k) q) = g q :=
  IsLocalization.Away.lift_eq _ _ _

/-- `overlapLift` sends `t⁻¹` to the inverse of the image of `t`. -/
lemma overlapLift_tInv_mul {C : Type u} [CommRing C] (g : Polynomial k →+* C)
    (hg : IsUnit (g Polynomial.X)) :
    g Polynomial.X * overlapLift g hg (tInv k) = 1 := by
  rw [← overlapLift_algebraMap g hg Polynomial.X, ← map_mul, algebraMap_X_mul_tInv, map_one]

/-- **Two module-finite `k[t]`-algebras whose localisations away from `t` are isomorphic by an
isomorphism sending the image of `t` to the inverse of the image of `t` have the same rank.**  This
is the form in which the comparison of the two chart dimensions of the morphism `W ⟶ ℙ¹_k`
determined by a rational function `r` is used: both localisations are the ring of functions on the
intersection of the two domains of definition of `r` and `r⁻¹`, and the two coordinates restrict
there to mutually inverse units. -/
theorem finrank_eq_of_isLocalizationAway (B₀ B₁ C₀ C₁ : Type u)
    [CommRing B₀] [IsDomain B₀] [Algebra (Polynomial k) B₀] [Module.Finite (Polynomial k) B₀]
    [CommRing B₁] [IsDomain B₁] [Algebra (Polynomial k) B₁] [Module.Finite (Polynomial k) B₁]
    [CommRing C₀] [Algebra B₀ C₀]
    [IsLocalization.Away (algebraMap (Polynomial k) B₀ Polynomial.X) C₀]
    [CommRing C₁] [Algebra B₁ C₁]
    [IsLocalization.Away (algebraMap (Polynomial k) B₁ Polynomial.X) C₁]
    (hinj₀ : Function.Injective (algebraMap (Polynomial k) B₀))
    (hinj₁ : Function.Injective (algebraMap (Polynomial k) B₁))
    (Φ : C₀ ≃+* C₁)
    (hΦX : Φ (algebraMap B₀ C₀ (algebraMap (Polynomial k) B₀ Polynomial.X)) *
      algebraMap B₁ C₁ (algebraMap (Polynomial k) B₁ Polynomial.X) = 1)
    (hΦC : ∀ a : k, Φ (algebraMap B₀ C₀ (algebraMap (Polynomial k) B₀ (Polynomial.C a))) =
      algebraMap B₁ C₁ (algebraMap (Polynomial k) B₁ (Polynomial.C a))) :
    Module.finrank (Polynomial k) B₀ = Module.finrank (Polynomial k) B₁ := by
  have _ : Module.Free (Polynomial k) B₀ := free_of_finite_of_injective hinj₀
  have _ : Module.Free (Polynomial k) B₁ := free_of_finite_of_injective hinj₁
  set g₀ : Polynomial k →+* C₀ := (algebraMap B₀ C₀).comp (algebraMap (Polynomial k) B₀) with hg₀
  set g₁ : Polynomial k →+* C₁ := (algebraMap B₁ C₁).comp (algebraMap (Polynomial k) B₁) with hg₁
  have hu₁ : IsUnit (g₁ Polynomial.X) := isUnit_iff_exists_inv'.mpr ⟨_, hΦX⟩
  have hu₀ : IsUnit (g₀ Polynomial.X) := by
    refine isUnit_iff_exists_inv.mpr ⟨Φ.symm (g₁ Polynomial.X), ?_⟩
    have h := congrArg Φ.symm hΦX
    rwa [map_mul, map_one, Φ.symm_apply_apply] at h
  let _ : Algebra (Polynomial k) C₀ := g₀.toAlgebra
  let _ : Algebra (Polynomial k) C₁ := g₁.toAlgebra
  have _ : IsScalarTower (Polynomial k) B₀ C₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower (Polynomial k) B₁ C₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra (overlapRing k) C₀ := (overlapLift g₀ hu₀).toAlgebra
  let _ : Algebra (overlapRing k) C₁ := (overlapLift g₁ hu₁).toAlgebra
  have ht₀ : IsScalarTower (Polynomial k) (overlapRing k) C₀ :=
    IsScalarTower.of_algebraMap_eq fun q => (overlapLift_algebraMap g₀ hu₀ q).symm
  have ht₁ : IsScalarTower (Polynomial k) (overlapRing k) C₁ :=
    IsScalarTower.of_algebraMap_eq fun q => (overlapLift_algebraMap g₁ hu₁ q).symm
  have hsub₀ : Algebra.algebraMapSubmonoid B₀
      (Submonoid.powers (Polynomial.X : Polynomial k)) =
      Submonoid.powers (algebraMap (Polynomial k) B₀ Polynomial.X) := Submonoid.map_powers _ _
  have hsub₁ : Algebra.algebraMapSubmonoid B₁
      (Submonoid.powers (Polynomial.X : Polynomial k)) =
      Submonoid.powers (algebraMap (Polynomial k) B₁ Polynomial.X) := Submonoid.map_powers _ _
  have hloc₀ : IsLocalization (Algebra.algebraMapSubmonoid B₀
      (Submonoid.powers (Polynomial.X : Polynomial k))) C₀ := by rw [hsub₀]; infer_instance
  have hloc₁ : IsLocalization (Algebra.algebraMapSubmonoid B₁
      (Submonoid.powers (Polynomial.X : Polynomial k))) C₁ := by rw [hsub₁]; infer_instance
  have h₀ : Module.finrank (overlapRing k) C₀ = Module.finrank (Polynomial k) B₀ :=
    finrank_localization_eq_finrank (Submonoid.powers (Polynomial.X : Polynomial k))
      (overlapRing k) B₀ C₀
  have h₁ : Module.finrank (overlapRing k) C₁ = Module.finrank (Polynomial k) B₁ :=
    finrank_localization_eq_finrank (Submonoid.powers (Polynomial.X : Polynomial k))
      (overlapRing k) B₁ C₁
  rw [← h₀, ← h₁]
  refine Algebra.finrank_eq_of_equiv_equiv (flipRingEquiv k) Φ ?_
  refine IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial k)) ?_
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · change overlapLift g₁ hu₁ (flipRingHom k
      (algebraMap (Polynomial k) (overlapRing k) (Polynomial.C a))) =
      Φ (overlapLift g₀ hu₀ (algebraMap (Polynomial k) (overlapRing k) (Polynomial.C a)))
    rw [flipRingHom_algebraMap, flipHom_C, overlapLift_algebraMap, overlapLift_algebraMap]
    exact (hΦC a).symm
  · change overlapLift g₁ hu₁ (flipRingHom k
      (algebraMap (Polynomial k) (overlapRing k) (Polynomial.X : Polynomial k))) =
      Φ (overlapLift g₀ hu₀
        (algebraMap (Polynomial k) (overlapRing k) (Polynomial.X : Polynomial k)))
    rw [flipRingHom_algebraMap, flipHom_X, overlapLift_algebraMap]
    have hi := overlapLift_tInv_mul g₁ hu₁
    have hΦ' : Φ (g₀ Polynomial.X) * g₁ Polynomial.X = 1 := hΦX
    calc overlapLift g₁ hu₁ (tInv k)
        = (Φ (g₀ Polynomial.X) * g₁ Polynomial.X) * overlapLift g₁ hu₁ (tInv k) := by
          rw [hΦ', one_mul]
      _ = Φ (g₀ Polynomial.X) * (g₁ Polynomial.X * overlapLift g₁ hu₁ (tInv k)) := by ring
      _ = Φ (g₀ Polynomial.X) := by rw [hi, mul_one]

end Ranks

/-! ## Chart presentations and the assembled theorem -/

/-- **A chart presentation of the two domains of definition of a rational function `r`**: two
finite-type `k`-algebra presentations `B₀ ≅ Γ(W, regularLocus r)` and
`B₁ ≅ Γ(W, regularLocus r⁻¹)` of the two chart rings, together with the elements `b₀`, `b₁`
corresponding to the regular functions representing `r` and `r⁻¹`, and the comparison of the two
fibre dimensions `dim_k (B₀ ⧸ (b₀)) = dim_k (B₁ ⧸ (b₁))`.

This is exactly the data required by
`ProperCurveDegree.degreeCycle_principalCycle_eq_zero_of_isAffineOpen`, minus the affineness of
the two domains of definition, which is supplied by `isAffineOpen_regularLocus_of_isFinite` and
`isAffineOpen_regularLocus_inv_of_isFinite`.  The two chart rings are the coordinate rings of the
two affine charts of the finite morphism `W ⟶ ℙ¹_k` determined by `r`, the fibre dimensions are
both equal to the degree `[K(W) : k(t)]` of that morphism, and the comparison `hrank` is the only
remaining gap in the proof that the degree of a principal divisor on a regular proper curve
vanishes. -/
structure ChartPresentation {W : Scheme.{u}} [_root_.AlgebraicGeometry.IsIntegral W]
    (f : W ⟶ Spec (CommRingCat.of k)) (r : W.functionField) where
  /-- A presentation of the chart ring of the domain of definition of `r`. -/
  B₀ : Type u
  /-- A presentation of the chart ring of the domain of definition of `r⁻¹`. -/
  B₁ : Type u
  /-- `B₀` is a commutative ring. -/
  [commRing₀ : CommRing B₀]
  /-- `B₁` is a commutative ring. -/
  [commRing₁ : CommRing B₁]
  /-- `B₀` is a `k`-algebra. -/
  [algebra₀ : Algebra k B₀]
  /-- `B₁` is a `k`-algebra. -/
  [algebra₁ : Algebra k B₁]
  /-- `B₀` is a domain. -/
  [isDomain₀ : IsDomain B₀]
  /-- `B₁` is a domain. -/
  [isDomain₁ : IsDomain B₁]
  /-- `B₀` has Krull dimension at most one. -/
  [krullDimLE₀ : Ring.KrullDimLE 1 B₀]
  /-- `B₁` has Krull dimension at most one. -/
  [krullDimLE₁ : Ring.KrullDimLE 1 B₁]
  /-- `B₀` is a `k`-algebra of finite type. -/
  [finiteType₀ : Algebra.FiniteType k B₀]
  /-- `B₁` is a `k`-algebra of finite type. -/
  [finiteType₁ : Algebra.FiniteType k B₁]
  /-- `B₀` is Noetherian. -/
  [isNoetherian₀ : IsNoetherianRing B₀]
  /-- `B₁` is Noetherian. -/
  [isNoetherian₁ : IsNoetherianRing B₁]
  /-- The presentation of the first chart ring. -/
  e₀ : CommRingCat.of B₀ ≅ Γ(W, Scheme.regularLocus r)
  /-- The presentation of the second chart ring. -/
  e₁ : CommRingCat.of B₁ ≅ Γ(W, Scheme.regularLocus r⁻¹)
  /-- The first presentation is a presentation of `k`-algebras. -/
  he₀ : CommRingCat.ofHom (algebraMap k B₀) ≫ e₀.hom =
    RationalFunction.kSection f (Scheme.regularLocus r)
  /-- The second presentation is a presentation of `k`-algebras. -/
  he₁ : CommRingCat.ofHom (algebraMap k B₁) ≫ e₁.hom =
    RationalFunction.kSection f (Scheme.regularLocus r⁻¹)
  /-- The element of `B₀` corresponding to `r`. -/
  b₀ : B₀
  /-- The element of `B₁` corresponding to `r⁻¹`. -/
  b₁ : B₁
  /-- `b₀` is nonzero. -/
  hb₀ : b₀ ≠ 0
  /-- `b₁` is nonzero. -/
  hb₁ : b₁ ≠ 0
  /-- `b₀` corresponds to the regular function representing `r`. -/
  hbe₀ : e₀.hom.hom b₀ = Scheme.regularSection r
  /-- `b₁` corresponds to the regular function representing `r⁻¹`. -/
  hbe₁ : e₁.hom.hom b₁ = Scheme.regularSection r⁻¹
  /-- **The two chart fibres have the same `k`-dimension.** -/
  hrank : Module.finrank k (B₀ ⧸ Ideal.span {b₀}) = Module.finrank k (B₁ ⧸ Ideal.span {b₁})

attribute [instance] ChartPresentation.commRing₀ ChartPresentation.commRing₁
  ChartPresentation.algebra₀ ChartPresentation.algebra₁ ChartPresentation.isDomain₀
  ChartPresentation.isDomain₁ ChartPresentation.krullDimLE₀ ChartPresentation.krullDimLE₁
  ChartPresentation.finiteType₀ ChartPresentation.finiteType₁ ChartPresentation.isNoetherian₀
  ChartPresentation.isNoetherian₁

namespace RegularProperCurve

variable (X : _root_.GromovWitten.AlgebraicGeometry.RegularProperCurve k)

/-- **The transcendental case: the degree of the principal divisor of a rational function
transcendental over `k` on a regular proper curve vanishes**, given a chart presentation of its
two domains of definition. -/
theorem degreeCycle_principalCycle_eq_zero_of_chartPresentation (r : X.W.functionField)
    (hr : r ≠ 0)
    (htr : Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField X.f).hom r))
    (d : ChartPresentation X.f r) :
    have _ := X.isNoetherian
    ZeroCycleDegree.degreeCycle X.f (X.W.principalCycle r) = 0 := by
  intro _
  exact ProperCurveDegree.RegularProperCurve.degreeCycle_principalCycle_eq_zero_of_isAffineOpen
    X r (isAffineOpen_regularLocus X r hr htr) (isAffineOpen_regularLocus_inv X r hr htr)
    d.e₀ d.e₁ d.he₀ d.he₁ d.b₀ d.hb₀ d.b₁ d.hb₁ d.hbe₀ d.hbe₁ d.hrank

/-- **The degree of a principal divisor on a regular proper curve vanishes**, modulo the single
remaining input: a chart presentation of the two domains of definition of `r` in the case where
`r` is transcendental over `k` (the hypothesis `hd`).  If `r` is algebraic over `k` no input at
all is needed: `r` is then a unit at every point of `W` and its principal cycle vanishes
identically. -/
theorem degreeCycle_principalCycle_eq_zero (r : X.W.functionField) (hr : r ≠ 0)
    (hd : Function.Injective
        (Polynomial.eval₂RingHom (RationalFunction.kFunctionField X.f).hom r) →
      ChartPresentation X.f r) :
    have _ := X.isNoetherian
    ZeroCycleDegree.degreeCycle X.f (X.W.principalCycle r) = 0 := by
  intro _
  by_cases htr : Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField X.f).hom r)
  · exact degreeCycle_principalCycle_eq_zero_of_chartPresentation X r hr htr (hd htr)
  · exact ProperCurveDegree.RegularProperCurve.degreeCycle_principalCycle_eq_zero_of_not_injective
      X r htr

end RegularProperCurve

end GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperCurveDegree
