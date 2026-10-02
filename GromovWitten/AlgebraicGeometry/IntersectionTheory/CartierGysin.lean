/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleRestrict
import GromovWitten.AlgebraicGeometry.IntersectionTheory.CartierLineBundle

/-!
# The Gysin map of an effective Cartier divisor

Stacks, Sections 42.29–42.30 (`section-intersecting-effective-Cartier`, `section-gysin`).

Let `X` be a locally Noetherian scheme with Noetherian underlying space, `D` an effective Cartier
divisor on `X` (`Curves.EffectiveCartierDivisor`), and `i : Z ⟶ X` a closed immersion whose kernel
is the ideal sheaf of `D` (`hker : i.ker = D.idealSheaf`), so that the image of `i` is the support
of `D`.  Write `L := D.lineBundleData` for the Čech line bundle `O(D)` and `N := L.restrict i` for
its restriction to `Z`.  For dimension functions `dimX` on `X` and `dimZ` on `Z` (any two agree
along `i`) and an integer `k`, the Gysin map `i^* : Z_{k+1}(X) → A_k(Z)` is defined on the class
of a point `x` with `dimX x = k + 1` by
* `[x] ↦ [D ∩ closure x]`, the restriction to `Z` of the divisor of the canonical section of `O(D)`
  along `pointSubscheme x`, if `x ∉ D.support`;
* `[x] ↦ c₁(N) ∩ [closure z]` if `x = i z`,

and extended linearly (`gysinCycle`).  The key formula shows that it kills rational
equivalence, giving `gysin : A_{k+1}(X) →ₗ[ℚ] A_k(Z)`, and `i_* ∘ i^* = c₁(O(D)) ∩ -`.

## Main results

* `gysinSummand`, `gysinCycle`: the Gysin map on cycles, `gysinCycle_point` and
  `gysinSummand_of_not_mem_support`/`gysinSummand_base` for its values on point classes.
* `gysinCycle_properPushforward`: `i^* i_* β = c₁(N) ∩ β` on cycles (Stacks 42.30.3).
* `closedImmersionPushforward_gysinCycle`: `i_* i^* α = c₁(O(D)) ∩ α` on cycles
  (Stacks 42.29.4).
* `gysinCycle_divisor_eq_zero`: the Gysin map kills the divisor of every rational-function
  generator of dimension `k + 2` (Stacks 42.30.1–2), via the key formula with the tame symbol.
* `gysin`: the Gysin map `A_{k+1}(X) →ₗ[ℚ] A_k(Z)`, with `gysin_quotientMap`,
  `gysin_point_of_not_mem_support` and `gysin_point_base` (its values on point classes),
  `closedImmersionPushforward_gysin` (`i_* i^* = c₁(O(D)) ∩ -` on Chow groups) and
  `gysin_closedImmersionPushforward` (`i^* i_* = c₁(N) ∩ -` on Chow groups).

The hypotheses are those of `firstChernClass`: `hU` (unit differences in the stalks of `X`) and
`hcov : CovByDimension dimX`; the corresponding hypotheses on `Z` are derived.  The instances
`[IsLocallyNoetherian Z] [NoetherianSpace Z]` are taken as arguments
(`noetherianSpace_of_isClosedImmersion` supplies the second).
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace IsLocalRing

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open LineBundleInjective
open VectorBundle (UnitDifferences)
open RationalEquivalenceSystem.DescendingMap

/-! ## The support of `D` and the image of `i` -/

section Support

variable {X Z : Scheme.{u}} (D : Curves.EffectiveCartierDivisor X) (i : Z ⟶ X)
  [IsClosedImmersion i]

/-- If the kernel of the closed immersion `i` is the ideal sheaf of `D`, the support of `D` is
the image of `i`. -/
theorem coe_support_eq_range_of_ker_eq (hker : i.ker = D.idealSheaf) :
    (D.support : Set X) = Set.range i.base := by
  change (D.idealSheaf.support : Set X) = _
  rw [← hker, Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]

/-- Membership in the support of `D` is membership in the image of `i`. -/
theorem mem_support_iff_of_ker_eq (hker : i.ker = D.idealSheaf) (x : X) :
    x ∈ D.support ↔ x ∈ Set.range i.base := by
  rw [← SetLike.mem_coe, coe_support_eq_range_of_ker_eq D i hker]

/-- Points of `Z` map into the support of `D`. -/
theorem base_mem_support_of_ker_eq (hker : i.ker = D.idealSheaf) (z : Z) :
    i.base z ∈ D.support :=
  (mem_support_iff_of_ker_eq D i hker _).2 ⟨z, rfl⟩

/-- A point outside the image of `i` is outside the support of `D`. -/
theorem not_mem_support_of_not_mem_range (hker : i.ker = D.idealSheaf) {x : X}
    (hx : x ∉ Set.range i.base) : x ∉ D.support :=
  fun h ↦ hx ((mem_support_iff_of_ker_eq D i hker x).1 h)

include i in
/-- The source of a closed immersion into a scheme with Noetherian underlying space has
Noetherian underlying space (supplies the `[NoetherianSpace Z]` hypothesis below). -/
theorem noetherianSpace_of_isClosedImmersion [NoetherianSpace X] : NoetherianSpace Z :=
  noetherianSpace_iff_isCompact.2 fun _ ↦
    i.isClosedEmbedding.isInducing.isCompact_iff.2 (NoetherianSpace.isCompact _)

end Support

/-! ## Restriction of cycles to `Z` followed by the class map -/

section Proj

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- `AlgebraicCycle.pullbackClosed` as a `ℚ`-linear map. -/
noncomputable def pullbackClosedLinear : AlgebraicCycle X ℚ →ₗ[ℚ] AlgebraicCycle Z ℚ where
  toFun := AlgebraicCycle.pullbackClosed i
  map_add' c d := by
    apply Function.locallyFinsuppWithin.coe_injective
    funext z
    rfl
  map_smul' q c := by
    apply Function.locallyFinsuppWithin.coe_injective
    funext z
    rfl

/-- `pullbackClosedLinear` is `pullbackClosed`. -/
theorem pullbackClosedLinear_apply (c : AlgebraicCycle X ℚ) :
    pullbackClosedLinear i c = AlgebraicCycle.pullbackClosed i c := rfl

/-- Restriction of a cycle on `X` to `Z` along `i`, followed by projection to dimension `k` and
the class map: the linear map `AlgebraicCycle X ℚ →ₗ[ℚ] A_k(Z)`. -/
noncomputable def gysinProj (dimZ : DimensionFunction Z) (k : ℤ) :
    AlgebraicCycle X ℚ →ₗ[ℚ] (chowSystem dimZ k).ChowGroup :=
  (qProj dimZ k).comp (pullbackClosedLinear i)

/-- `gysinProj` on a cycle known to be graded in dimension `k` is the class of its graded
restriction. -/
theorem gysinProj_eq_quotientMap {dimX : DimensionFunction X} (dimZ : DimensionFunction Z)
    (k : ℤ) (c : AlgebraicCycle X ℚ) (hmem : c ∈ cyclesOfDimension X dimX k) :
    gysinProj i dimZ k c = (chowSystem dimZ k).quotientMap
      (cyclesOfDimension.pullbackClosed (dimensionW := dimZ) i ⟨c, hmem⟩) :=
  qProj_eq_quotientMap _ (cyclesOfDimension.pullbackClosed (dimensionW := dimZ) i ⟨c, hmem⟩).2

/-- The pushforward of `gysinProj c` is the class of `c`, for `c` graded in dimension `k` and
supported in the image of `i`. -/
theorem closedImmersionPushforward_gysinProj [IsLocallyNoetherian X] [NoetherianSpace X]
    {dimX : DimensionFunction X} (dimZ : DimensionFunction Z) (k : ℤ)
    (c : AlgebraicCycle X ℚ) (hmem : c ∈ cyclesOfDimension X dimX k)
    (hc : ∀ x, x ∉ Set.range i.base → c x = 0) :
    closedImmersionPushforward (chowSystem dimZ k) i (chowSystem dimX k)
      (gysinProj i dimZ k c) = (chowSystem dimX k).quotientMap ⟨c, hmem⟩ := by
  rw [gysinProj_eq_quotientMap i dimZ k c hmem, closedImmersionPushforward_quotientMap,
    cyclesOfDimension.properPushforward_pullbackClosed i ⟨c, hmem⟩ hc]

end Proj

/-! ## The Gysin map on cycles -/

section GysinCycle

variable {X Z : Scheme.{u}} [IsLocallyNoetherian X] [NoetherianSpace X]
  [IsLocallyNoetherian Z] [NoetherianSpace Z]
  (D : Curves.EffectiveCartierDivisor X) (i : Z ⟶ X) [IsClosedImmersion i]
  (hker : i.ker = D.idealSheaf) (dimX : DimensionFunction X) (dimZ : DimensionFunction Z)
  (k : ℤ)

open Classical in
/-- **The Gysin summand at a point `x`.**  If `x = i z` it is `c₁(O(D)|_Z) ∩ [closure z]`
(`chernSummand`); otherwise it is the class in `A_k(Z)` of the restriction to `Z` of the divisor
of the canonical section of `O(D)` along `pointSubscheme x`. -/
noncomputable def gysinSummand (x : X) : (chowSystem dimZ k).ChowGroup :=
  if hx : x ∈ Set.range i.base then
    chernSummand (D.lineBundleData.restrict i) dimZ k hx.choose
  else
    gysinProj i dimZ k ((D.canonicalSection (pointSubscheme x)
      (D.genericPointImage_pointSubscheme_not_mem
        (not_mem_support_of_not_mem_range D i hker hx))).divisor dimX)

/-- The Gysin summand at a point of the image of `i`. -/
theorem gysinSummand_base (z : Z) :
    gysinSummand D i hker dimX dimZ k (i.base z) =
      chernSummand (D.lineBundleData.restrict i) dimZ k z := by
  have hx : i.base z ∈ Set.range i.base := ⟨z, rfl⟩
  rw [gysinSummand, dif_pos hx]
  congr 1
  exact i.isClosedEmbedding.injective hx.choose_spec

/-- The Gysin summand at a point outside the support of `D`. -/
theorem gysinSummand_of_not_mem_support {x : X} (hx : x ∉ D.support) :
    gysinSummand D i hker dimX dimZ k x =
      gysinProj i dimZ k ((D.canonicalSection (pointSubscheme x)
        (D.genericPointImage_pointSubscheme_not_mem hx)).divisor dimX) := by
  have hx' : x ∉ Set.range i.base := fun h ↦ hx ((mem_support_iff_of_ker_eq D i hker x).2 h)
  rw [gysinSummand, dif_neg hx']

/-- **The Gysin map on cycles**, `i^* : Z_{k+1}(X) →ₗ[ℚ] A_k(Z)`: sends a graded cycle `α` to
`∑ᶠ x, α x • gysinSummand x`. -/
noncomputable def gysinCycle :
    cyclesOfDimension X dimX (k + 1) →ₗ[ℚ] (chowSystem dimZ k).ChowGroup where
  toFun α := ∑ᶠ x : X, (α : AlgebraicCycle X ℚ) x • gysinSummand D i hker dimX dimZ k x
  map_add' α β := by
    have hα' := finite_support_smul (α : AlgebraicCycle X ℚ) (gysinSummand D i hker dimX dimZ k)
      (finite_support_univ (α : AlgebraicCycle X ℚ))
    have hβ' := finite_support_smul (β : AlgebraicCycle X ℚ) (gysinSummand D i hker dimX dimZ k)
      (finite_support_univ (β : AlgebraicCycle X ℚ))
    simp_rw [Submodule.coe_add, Function.locallyFinsuppWithin.coe_add, Pi.add_apply, add_smul]
    exact finsum_add_distrib hα' hβ'
  map_smul' c α := by
    have hα' := finite_support_smul (α : AlgebraicCycle X ℚ) (gysinSummand D i hker dimX dimZ k)
      (finite_support_univ (α : AlgebraicCycle X ℚ))
    simp_rw [Submodule.coe_smul, Function.locallyFinsuppWithin.coe_rational_smul, Pi.smul_apply,
      smul_eq_mul, mul_smul]
    exact (smul_finsum' c hα').symm

/-- `gysinCycle` on a graded cycle, unfolded. -/
theorem gysinCycle_apply (α : cyclesOfDimension X dimX (k + 1)) :
    gysinCycle D i hker dimX dimZ k α =
      ∑ᶠ x : X, (α : AlgebraicCycle X ℚ) x • gysinSummand D i hker dimX dimZ k x := rfl

/-- `gysinCycle` on the class of a point `x` of dimension `k + 1` is `gysinSummand x`. -/
theorem gysinCycle_point {x : X} (hx : dimX x = k + 1) :
    gysinCycle D i hker dimX dimZ k (cyclesOfDimension.point x hx) =
      gysinSummand D i hker dimX dimZ k x := by
  rw [gysinCycle_apply, finsum_eq_single _ x]
  · rw [cyclesOfDimension.point_apply_self, one_smul]
  · intro y hy
    rw [cyclesOfDimension.point_apply_of_ne x y hx hy, zero_smul]

/-- `c1Cycle` on the class of a point `z` of dimension `k + 1` is `chernSummand z` (no
homogeneity hypothesis is needed for this unfolding). -/
theorem c1Cycle_point_eq_chernSummand (N : LineBundleData Z) {z : Z} (hz : dimZ z = k + 1) :
    c1Cycle N dimZ k (cyclesOfDimension.point z hz) = chernSummand N dimZ k z := by
  change (∑ᶠ y : Z, (cyclesOfDimension.point z hz : AlgebraicCycle Z ℚ) y • chernSummand N dimZ k y)
    = chernSummand N dimZ k z
  rw [finsum_eq_single _ z]
  · rw [cyclesOfDimension.point_apply_self, one_smul]
  · intro y hy
    rw [cyclesOfDimension.point_apply_of_ne z y hz hy, zero_smul]

/-- **`i^* i_* = c₁(N) ∩ -` on cycles** (Stacks, Lemma 42.30.3, `lemma-gysin-back`): for a
`(k+1)`-cycle `β` on `Z`, `gysinCycle (i_* β) = c₁(O(D)|_Z) ∩ β`. -/
theorem gysinCycle_properPushforward (β : cyclesOfDimension Z dimZ (k + 1)) :
    gysinCycle D i hker dimX dimZ k (cyclesOfDimension.properPushforward i β) =
      c1Cycle (D.lineBundleData.restrict i) dimZ k β := by
  refine LinearMap.congr_fun (c1Cycle_ext
    (f := (gysinCycle D i hker dimX dimZ k).comp (cyclesOfDimension.properPushforward i))
    (g := c1Cycle (D.lineBundleData.restrict i) dimZ k) fun z ↦ ?_) β
  by_cases hz : dimZ z = k + 1
  · rw [LinearMap.comp_apply, cyclesOfDimension.pointProj_eq_point hz,
      properPushforward_point_of_isClosedImmersion, gysinCycle_point, gysinSummand_base,
      c1Cycle_point_eq_chernSummand]
  · rw [cyclesOfDimension.pointProj_eq_zero_of_ne hz, map_zero, map_zero]

/-- **`i_* i^* = c₁(O(D)) ∩ -` on cycles** (Stacks, Lemma 42.29.4,
`lemma-support-cap-effective-Cartier`): for a `(k+1)`-cycle `α` on `X`, the pushforward to `X`
of `gysinCycle α` is `c₁(O(D)) ∩ α`. -/
theorem closedImmersionPushforward_gysinCycle (hcov : HomogeneityLocal.CovByDimension dimX)
    (α : cyclesOfDimension X dimX (k + 1)) :
    closedImmersionPushforward (chowSystem dimZ k) i (chowSystem dimX k)
        (gysinCycle D i hker dimX dimZ k α) =
      c1Cycle D.lineBundleData dimX k α := by
  refine LinearMap.congr_fun (c1Cycle_ext
    (f := (closedImmersionPushforward (chowSystem dimZ k) i (chowSystem dimX k)).comp
      (gysinCycle D i hker dimX dimZ k))
    (g := c1Cycle D.lineBundleData dimX k) fun x ↦ ?_) α
  by_cases hx : dimX x = k + 1
  · rw [LinearMap.comp_apply, cyclesOfDimension.pointProj_eq_point hx, gysinCycle_point]
    by_cases hxD : x ∈ D.support
    · obtain ⟨z, rfl⟩ := (mem_support_iff_of_ker_eq D i hker x).1 hxD
      have hz : dimZ z = k + 1 :=
        (DimensionFunction.apply_eq_of_isClosedImmersion dimZ dimX i z).trans hx
      rw [gysinSummand_base, ← c1Cycle_point_eq_chernSummand dimZ k _ hz,
        closedImmersionPushforward_c1Cycle_restrict i D.lineBundleData hcov dimZ k,
        properPushforward_point_of_isClosedImmersion]
    · set s := D.canonicalSection (pointSubscheme x)
        (D.genericPointImage_pointSubscheme_not_mem hxD)
      have hmem : s.divisor dimX ∈ cyclesOfDimension X dimX k :=
        s.divisor_mem_cyclesOfDimension dimX hcov
          (by rw [genericPointImage_pointSubscheme]; exact hx)
      rw [gysinSummand_of_not_mem_support D i hker dimX dimZ k hxD,
        closedImmersionPushforward_gysinProj i dimZ k _ hmem (fun y hy ↦
          D.canonicalSection_divisor_apply_eq_zero _ _ dimX
            (not_mem_support_of_not_mem_range D i hker hy)),
        c1Cycle_single hcov hx s]
  · rw [cyclesOfDimension.pointProj_eq_zero_of_ne hx, map_zero, map_zero]

end GysinCycle

/-! ## Restriction of frame and point-generator divisors to `Z` -/

section Restrict

variable {X Z : Scheme.{u}} [IsLocallyNoetherian X] [NoetherianSpace X]
  [IsLocallyNoetherian Z] [NoetherianSpace Z] (i : Z ⟶ X) [IsClosedImmersion i]
  (dimX : DimensionFunction X) (dimZ : DimensionFunction Z)

/-- The restriction to `Z` of the divisor of the frame of `L` at `i z` is the divisor of the
frame of `L.restrict i` at `z`. -/
theorem pullbackClosed_divisor_pointFrame (L : LineBundleData X) (z : Z) :
    AlgebraicCycle.pullbackClosed i ((L.pointFrame (i.base z)).divisor dimX) =
      ((L.restrict i).pointFrame z).divisor dimZ := by
  apply Function.locallyFinsuppWithin.ext
  intro q
  change ((L.pointFrame (i.base z)).divisor dimX : X → ℚ) (i.base q) =
    (((L.restrict i).pointFrame z).divisor dimZ : Z → ℚ) q
  by_cases h : z ⤳ q
  · exact (divisor_restrict_pointFrame_apply_of_specializes i L dimX dimZ h).symm
  · rw [LineBundleData.RationalSection.divisor_apply_eq_zero_of_not_specializes _ _ h,
      LineBundleData.RationalSection.divisor_apply_eq_zero_of_not_specializes _ _
        (fun h' => h ((i.isClosedEmbedding.isInducing.specializes_iff).1 h'))]

/-- `gysinProj` of the divisor of the frame of `L` at `i z` is `c₁(L|_Z) ∩ [closure z]`. -/
theorem gysinProj_divisor_pointFrame (hcovZ : HomogeneityLocal.CovByDimension dimZ)
    (L : LineBundleData X) (k : ℤ) {z : Z} (hz : dimZ z = k + 1) :
    gysinProj i dimZ k ((L.pointFrame (i.base z)).divisor dimX) =
      chernSummand (L.restrict i) dimZ k z := by
  change qProj dimZ k (AlgebraicCycle.pullbackClosed i _) = _
  rw [pullbackClosed_divisor_pointFrame i dimX dimZ L z,
    qProj_eq_quotientMap _ (((L.restrict i).pointFrame z).divisor_mem_cyclesOfDimension dimZ
      hcovZ (by rw [genericPointImage_pointSubscheme]; exact hz)),
    chernSummand_eq hcovZ hz]

/-- The restriction to `Z` of the divisor of the point generator of `u ∈ κ(i z)ˣ` is the divisor
of the point generator of the image of `u` in `κ(z)ˣ`. -/
theorem pullbackClosed_divisor_pointGenerator (z : Z) (u : (X.residueField (i.base z))ˣ) :
    AlgebraicCycle.pullbackClosed i ((pointGenerator (i.base z) u).divisor dimX) =
      (pointGenerator z (Units.map (closedResidueFieldEquiv i z).toMonoidHom u)).divisor dimZ := by
  apply Function.locallyFinsuppWithin.ext
  intro q
  change ((pointGenerator (i.base z) u).divisor dimX : X → ℚ) (i.base q) =
    ((pointGenerator z (Units.map (closedResidueFieldEquiv i z).toMonoidHom u)).divisor dimZ :
      Z → ℚ) q
  by_cases h : z ⤳ q
  · rw [divisor_pointGenerator_apply dimX _ u (specializes_hom_base (i := i) h),
      divisor_pointGenerator_apply dimZ z _ h, pointOrd_closedResidueFieldEquiv]
  · rw [divisor_pointGenerator_apply_eq_zero dimX _ u _
        (fun h' => h ((i.isClosedEmbedding.isInducing.specializes_iff).1 h')),
      divisor_pointGenerator_apply_eq_zero dimZ z _ q h]

/-- `gysinProj` kills the divisor of a point generator at a point `i z` of dimension `k + 1`:
its restriction to `Z` is a principal divisor on `Z`. -/
theorem gysinProj_divisor_pointGenerator (hcovZ : HomogeneityLocal.CovByDimension dimZ) (k : ℤ)
    {z : Z} (hz : dimZ z = k + 1) (u : (X.residueField (i.base z))ˣ) :
    gysinProj i dimZ k ((pointGenerator (i.base z) u).divisor dimX) = 0 := by
  change qProj dimZ k (AlgebraicCycle.pullbackClosed i _) = _
  rw [pullbackClosed_divisor_pointGenerator i dimX dimZ z u]
  exact qProj_divisor _ (RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimZ hcovZ _
    (by rw [genericPointImage_pointGenerator]; exact hz))

omit [IsLocallyNoetherian Z] [NoetherianSpace Z] in
/-- The divisor of a point generator at a point of the image of `i` vanishes off the image. -/
theorem divisor_pointGenerator_base_apply_eq_zero (z : Z) (u : (X.residueField (i.base z))ˣ)
    {x : X} (hx : x ∉ Set.range i.base) :
    ((pointGenerator (i.base z) u).divisor dimX : X → ℚ) x = 0 :=
  divisor_pointGenerator_apply_eq_zero dimX _ u x
    (fun h => hx (h.mem_closed i.isClosedEmbedding.isClosed_range ⟨z, rfl⟩))

/-- The pushforward along `i` of the divisor of the point generator of the image of `u` in
`κ(z)ˣ` is the divisor of the point generator of `u ∈ κ(i z)ˣ`. -/
theorem map_divisor_pointGenerator_base (z : Z) (u : (X.residueField (i.base z))ˣ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map i dimZ dimX
        ((pointGenerator z (Units.map (closedResidueFieldEquiv i z).toMonoidHom u)).divisor
          dimZ) =
      (pointGenerator (i.base z) u).divisor dimX := by
  rw [← pullbackClosed_divisor_pointGenerator i dimX dimZ z u,
    dimensionFunction_eq_comp_closedImmersion i dimX dimZ]
  exact AlgebraicCycle.map_pullbackClosed i dimX _
    (fun x hx => divisor_pointGenerator_base_apply_eq_zero i dimX z u hx)

omit [IsLocallyNoetherian Z] [NoetherianSpace Z] in
/-- The divisor of the point generator of `u ^ n` is `n` times the divisor of the point
generator of `u`. -/
theorem divisor_pointGenerator_zpow (v : X) (u : (X.residueField v)ˣ) (n : ℤ) :
    (pointGenerator v (u ^ n)).divisor dimX = (n : ℚ) • (pointGenerator v u).divisor dimX := by
  apply Function.locallyFinsuppWithin.ext
  intro Q
  change ((pointGenerator v (u ^ n)).divisor dimX : X → ℚ) Q =
    (((n : ℚ) • (pointGenerator v u).divisor dimX : AlgebraicCycle X ℚ) : X → ℚ) Q
  rw [Function.locallyFinsuppWithin.coe_rational_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : v ⤳ Q
  · rw [divisor_pointGenerator_apply dimX v _ h, divisor_pointGenerator_apply dimX v u h,
      pointOrd_zpow]
    push_cast
    rfl
  · rw [divisor_pointGenerator_apply_eq_zero dimX v _ Q h,
      divisor_pointGenerator_apply_eq_zero dimX v u Q h, mul_zero]

end Restrict

/-! ## The Gysin map kills rational equivalence -/

section Descent

variable {X Z : Scheme.{u}} [IsLocallyNoetherian X] [NoetherianSpace X]
  [IsLocallyNoetherian Z] [NoetherianSpace Z]
  (D : Curves.EffectiveCartierDivisor X) (i : Z ⟶ X) [IsClosedImmersion i]
  (hker : i.ker = D.idealSheaf) (dimX : DimensionFunction X) (dimZ : DimensionFunction Z)
  (k : ℤ)

/-- **`gysinCycle` of the divisor of a rational section along `pointSubscheme w`.**  If
`dimX w = k + 1 + 1` and `s` is a rational section of a line bundle `L'` along
`pointSubscheme w`, then `gysinCycle` of the divisor of `s` is `∑ ord_v(s) • gysinSummand v`,
the sum running over the codimension-one specialisations `v` of `w`, where `ord_v(s)` is the
order of the coordinate of `s` in the canonical chart of `L'` at `v`. -/
theorem gysinCycle_divisor_pointSubscheme {L' : LineBundleData X} {w : X}
    (hw : dimX w = k + 1 + 1) (s : L'.RationalSection (pointSubscheme w))
    (hmem : s.divisor dimX ∈ cyclesOfDimension X dimX (k + 1)) :
    gysinCycle D i hker dimX dimZ k ⟨s.divisor dimX, hmem⟩ =
      ∑ᶠ v : {v : X // w ⤳ v ∧ dimX w = dimX v + 1},
        (pointOrd v.2.1 (s.pointCoordAt v.2.1) : ℚ) • gysinSummand D i hker dimX dimZ k v.1 := by
  have hsupp : Function.support
      (fun x : X ↦ (s.divisor dimX : X → ℚ) x • gysinSummand D i hker dimX dimZ k x) ⊆
      Set.range (Subtype.val : {v : X // w ⤳ v ∧ dimX w = dimX v + 1} → X) := by
    intro x hx
    rw [Function.mem_support] at hx
    have hx0 : (s.divisor dimX : X → ℚ) x ≠ 0 := fun h0 ↦ hx (by rw [h0, zero_smul])
    by_cases hwx : w ⤳ x
    · by_cases hd : dimX x = k + 1
      · exact ⟨⟨x, hwx, by omega⟩, rfl⟩
      · exact absurd (hmem x hd) hx0
    · exact absurd (s.divisor_apply_eq_zero_of_not_specializes dimX hwx) hx0
  rw [gysinCycle_apply,
    finsum_comp_of_injective_of_support_subset_range Subtype.val_injective _ hsupp]
  refine finsum_congr fun v ↦ ?_
  rw [s.divisor_apply_eq_pointOrd dimX v.2.1 (L'.keyChart v.1) _ (L'.mem_keyChart v.1)]
  rfl

/-- **The per-point identity of the Gysin descent** (Stacks, proof of Lemma 42.30.1).  Let
`w ∉ D.support` with `dimX w = k + 1 + 1`, let `s` be the canonical section of `O(D)` along
`pointSubscheme w`, `t` a rational section of the trivial bundle along `pointSubscheme w`, and
`symb` a normalised symbol family.  For every codimension-one specialisation `v` of `w`, with
`n_v := ord_v(t)`,
`n_v • gysinSummand v = gysinProj (n_v • div(frame_{O(D)} v) + div(symb(s_v, t_v)))`.
If `v ∈ D.support` this is the restriction of the frame divisor, and the symbol term is a
principal divisor on `Z`; if `v ∉ D.support`, `s_v` is a point-stalk unit with residue `r̄_v`, so
the symbol is `r̄_v ^ n_v`, and `div(frame v) + div(r̄_v) = div(canonical section at v)`. -/
theorem smul_gysinSummand_eq (hcov : HomogeneityLocal.CovByDimension dimX)
    {symb : PointSymbolFamily X} (hnorm : symb.IsNormalized) {w : X} (hw : w ∉ D.support)
    (hk : dimX w = k + 1 + 1) (t : (LineBundleData.trivial X).RationalSection (pointSubscheme w))
    (v : {v : X // w ⤳ v ∧ dimX w = dimX v + 1}) :
    (pointOrd v.2.1 (t.pointCoordAt v.2.1) : ℚ) • gysinSummand D i hker dimX dimZ k v.1 =
      gysinProj i dimZ k
        ((pointOrd v.2.1 (t.pointCoordAt v.2.1) : ℚ) •
            (D.lineBundleData.pointFrame v.1).divisor dimX +
          (pointGenerator v.1 (symb v.2.1 ((D.canonicalSection (pointSubscheme w)
            (D.genericPointImage_pointSubscheme_not_mem hw)).pointCoordAt v.2.1)
            (t.pointCoordAt v.2.1))).divisor dimX) := by
  obtain ⟨v, hwv, hdv⟩ := v
  have hcovZ := covByDimension_of_isClosedImmersion i hcov dimZ
  have hv : dimX v = k + 1 := by omega
  set L := D.lineBundleData
  set n := pointOrd hwv (t.pointCoordAt hwv)
  rw [map_add, map_smul]
  by_cases hvD : v ∈ D.support
  · obtain ⟨z, rfl⟩ := (mem_support_iff_of_ker_eq D i hker v).1 hvD
    have hz : dimZ z = k + 1 :=
      (DimensionFunction.apply_eq_of_isClosedImmersion dimZ dimX i z).trans hv
    rw [gysinSummand_base, gysinProj_divisor_pointFrame i dimX dimZ hcovZ L k hz,
      gysinProj_divisor_pointGenerator i dimX dimZ hcovZ k hz, add_zero]
  · have hd1 : ringKrullDim (pointStalk hwv) = 1 :=
      ringKrullDim_pointStalk_eq_one_of_dim_eq dimX hwv hdv
    obtain ⟨a, ha1, ha2⟩ :=
      D.exists_pointStalk_unit_equationResidueUnit hwv (L.keyChart v) (L.mem_keyChart v) hvD
    have hs : (D.canonicalSection (pointSubscheme w)
        (D.genericPointImage_pointSubscheme_not_mem hw)).pointCoordAt hwv =
        pointStalkUnitIncl hwv a :=
      (D.pointCoord_canonicalSection _ (L.keyChart v) _
        (hwv.mem_open (Opens.isOpen _) (L.mem_keyChart v)) hw).trans ha1.symm
    rw [hs, (hnorm hwv hd1 a _).1, ha2, divisor_pointGenerator_zpow,
      gysinSummand_of_not_mem_support D i hker dimX dimZ k hvD,
      ← D.pointFrame_divisor_add_pointGenerator_divisor dimX hvD, map_add, map_smul, smul_add]

/-- **The Gysin map kills the divisor of a point generator at a point outside `D`** (Stacks,
Lemma 42.30.1, `lemma-gysin-factors-general`, for the trivial bundle): for `w ∉ D.support` with
`dimX w = k + 1 + 1` and `r ∈ κ(w)ˣ`, `gysinCycle (div (pointGenerator w r)) = 0`, by the key
formula with the tame symbol. -/
theorem gysinCycle_divisor_pointGenerator_eq_zero_of_not_mem
    (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x))
    (hcov : HomogeneityLocal.CovByDimension dimX) {w : X} (hw : w ∉ D.support)
    (hk : dimX w = k + 1 + 1) (r : (X.residueField w)ˣ)
    (hmem : (pointGenerator w r).divisor dimX ∈ cyclesOfDimension X dimX (k + 1)) :
    gysinCycle D i hker dimX dimZ k ⟨(pointGenerator w r).divisor dimX, hmem⟩ = 0 := by
  set T := LineBundleData.trivial X
  let t : T.RationalSection (pointSubscheme w) :=
    ⟨T.keyChart w, eta_pointSubscheme_mem (specializes_refl w) (T.mem_keyChart w),
      Units.map (pointFieldEquiv w).symm.toMonoidHom r⟩
  have hdiv : (pointGenerator w r).divisor dimX = t.divisor dimX :=
    divisor_pointGenerator_eq_trivial dimX w r _ _
  have hmem' : t.divisor dimX ∈ cyclesOfDimension X dimX (k + 1) := hdiv ▸ hmem
  have heq : (⟨(pointGenerator w r).divisor dimX, hmem⟩ : cyclesOfDimension X dimX (k + 1)) =
      ⟨t.divisor dimX, hmem'⟩ := Subtype.ext hdiv
  rw [heq, gysinCycle_divisor_pointSubscheme D i hker dimX dimZ k hk t hmem']
  set s := D.canonicalSection (pointSubscheme w) (D.genericPointImage_pointSubscheme_not_mem hw)
  have hnorm : PointSymbolFamily.IsNormalized (tamePointSymbol hU) :=
    tamePointSymbol_isNormalized hU
  have hK := keyFormula (tamePointSymbol hU) (tamePointSymbol_isBimultiplicative hU) hnorm
    (tamePointSymbol_satisfiesKeyLemma hU hcov) hcov D.lineBundleData T s t
  have h0 : ∀ v : X, (T.pointFrame v).divisor dimX = 0 := fun v ↦ trivial_divisor_eq_zero dimX _ _
  simp only [h0, smul_zero, zero_sub] at hK
  rw [finsum_neg_distrib] at hK
  have hfin1 := t.finite_support_pointOrd_smul dimX
    fun v : {v : X // w ⤳ v ∧ dimX w = dimX v + 1} ↦ (D.lineBundleData.pointFrame v.1).divisor dimX
  have hfin2 := finite_support_keyFormula_rhs dimX hnorm s t
  calc ∑ᶠ v : {v : X // w ⤳ v ∧ dimX w = dimX v + 1},
        (pointOrd v.2.1 (t.pointCoordAt v.2.1) : ℚ) • gysinSummand D i hker dimX dimZ k v.1
      = ∑ᶠ v : {v : X // w ⤳ v ∧ dimX w = dimX v + 1}, gysinProj i dimZ k
          ((pointOrd v.2.1 (t.pointCoordAt v.2.1) : ℚ) •
              (D.lineBundleData.pointFrame v.1).divisor dimX +
            (pointGenerator v.1 (tamePointSymbol hU v.2.1 (s.pointCoordAt v.2.1)
              (t.pointCoordAt v.2.1))).divisor dimX) :=
        finsum_congr fun v ↦ smul_gysinSummand_eq D i hker dimX dimZ k hcov hnorm hw hk t v
    _ = gysinProj i dimZ k (∑ᶠ v : {v : X // w ⤳ v ∧ dimX w = dimX v + 1},
          ((pointOrd v.2.1 (t.pointCoordAt v.2.1) : ℚ) •
              (D.lineBundleData.pointFrame v.1).divisor dimX +
            (pointGenerator v.1 (tamePointSymbol hU v.2.1 (s.pointCoordAt v.2.1)
              (t.pointCoordAt v.2.1))).divisor dimX)) :=
        (map_finsum _ ((hfin1.union hfin2).subset (Function.support_add _ _))).symm
    _ = 0 := by
        rw [finsum_add_distrib hfin1 hfin2, ← hK, add_neg_cancel, map_zero]

/-- **The Gysin map kills the divisor of a point generator at a point of `D`**: for `z : Z` with
`dimX (i z) = k + 1 + 1` and `r ∈ κ(i z)ˣ`, the divisor of `pointGenerator (i z) r` is the
pushforward of a principal divisor on `Z`, so `gysinCycle` of it is `c₁(O(D)|_Z)` of that
principal divisor, which vanishes by `killsRelations_of_unitDifferences` on `Z`. -/
theorem gysinCycle_divisor_pointGenerator_base_eq_zero
    (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x))
    (hcov : HomogeneityLocal.CovByDimension dimX) (z : Z) (hk : dimX (i.base z) = k + 1 + 1)
    (r : (X.residueField (i.base z))ˣ)
    (hmem : (pointGenerator (i.base z) r).divisor dimX ∈ cyclesOfDimension X dimX (k + 1)) :
    gysinCycle D i hker dimX dimZ k ⟨(pointGenerator (i.base z) r).divisor dimX, hmem⟩ = 0 := by
  have hcovZ := covByDimension_of_isClosedImmersion i hcov dimZ
  have hUZ := unitDifferences_stalk_of_hom i hU
  set r' := Units.map (closedResidueFieldEquiv i z).toMonoidHom r
  have hz : dimZ z = k + 1 + 1 :=
    (DimensionFunction.apply_eq_of_isClosedImmersion dimZ dimX i z).trans hk
  have hmemZ : (pointGenerator z r').divisor dimZ ∈ cyclesOfDimension Z dimZ (k + 1) :=
    RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimZ hcovZ _
      (by rw [genericPointImage_pointGenerator]; exact hz)
  have heq : (⟨(pointGenerator (i.base z) r).divisor dimX, hmem⟩ :
      cyclesOfDimension X dimX (k + 1)) =
      cyclesOfDimension.properPushforward i ⟨(pointGenerator z r').divisor dimZ, hmemZ⟩ := by
    apply Subtype.ext
    exact (map_divisor_pointGenerator_base i dimX dimZ z r).symm
  rw [heq, gysinCycle_properPushforward]
  exact killsRelations_of_unitDifferences hUZ hcovZ (D.lineBundleData.restrict i) k
    (pointGenerator z r') (by rw [genericPointImage_pointGenerator]; omega)

/-- The Gysin map kills the divisor of every point generator of dimension `k + 2`. -/
theorem gysinCycle_divisor_pointGenerator_eq_zero
    (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x))
    (hcov : HomogeneityLocal.CovByDimension dimX) (w : X) (hk : dimX w = k + 1 + 1)
    (r : (X.residueField w)ˣ)
    (hmem : (pointGenerator w r).divisor dimX ∈ cyclesOfDimension X dimX (k + 1)) :
    gysinCycle D i hker dimX dimZ k ⟨(pointGenerator w r).divisor dimX, hmem⟩ = 0 := by
  by_cases hw : w ∈ D.support
  · obtain ⟨z, rfl⟩ := (mem_support_iff_of_ker_eq D i hker w).1 hw
    exact gysinCycle_divisor_pointGenerator_base_eq_zero D i hker dimX dimZ k hU hcov z hk r hmem
  · exact gysinCycle_divisor_pointGenerator_eq_zero_of_not_mem D i hker dimX dimZ k hU hcov hw
      hk r hmem

/-- **The Gysin map kills rational equivalence** (Stacks, Lemma 42.30.2, `lemma-gysin-factors`):
`gysinCycle` kills the divisor of every rational-function generator of dimension `k + 2`. -/
theorem gysinCycle_divisor_eq_zero (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x))
    (hcov : HomogeneityLocal.CovByDimension dimX) (g : RationalFunctionGenerator X)
    (hg : dimX g.subspace.genericPointImage = k + 2) :
    gysinCycle D i hker dimX dimZ k ⟨g.divisor dimX,
      RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX hcov g
        (show dimX g.subspace.genericPointImage = (k + 1) + 1 by omega)⟩ = 0 := by
  have hk : dimX g.subspace.genericPointImage = k + 1 + 1 := by omega
  have hmem : (pointGenerator g.subspace.genericPointImage g.residueFunction).divisor dimX ∈
      cyclesOfDimension X dimX (k + 1) := by
    rw [divisor_pointGenerator]
    exact RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX hcov g hk
  have heq : (⟨g.divisor dimX, RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX hcov
      g (show dimX g.subspace.genericPointImage = (k + 1) + 1 by omega)⟩ :
        cyclesOfDimension X dimX (k + 1)) =
      ⟨(pointGenerator g.subspace.genericPointImage g.residueFunction).divisor dimX, hmem⟩ :=
    Subtype.ext (divisor_pointGenerator dimX g).symm
  rw [heq]
  exact gysinCycle_divisor_pointGenerator_eq_zero D i hker dimX dimZ k hU hcov _ hk _ hmem

/-- The relations submodule of `Z_{k+1}(X)` lies in the kernel of `gysinCycle`. -/
theorem gysinCycle_relations_le_ker (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x))
    (hcov : HomogeneityLocal.CovByDimension dimX) :
    (chowSystem dimX (k + 1)).relations ≤ LinearMap.ker (gysinCycle D i hker dimX dimZ k) := by
  intro z hz
  have hz' : (z : AlgebraicCycle X ℚ) ∈ totalRationalRelations X dimX := hz
  rw [totalRationalRelations, Submodule.mem_span_set'] at hz'
  obtain ⟨n, f, gg, hsum⟩ := hz'
  choose G hG using fun j ↦ (gg j).2
  have hzproj : z = cyclesOfDimension.projectLinear dimX (k + 1) (z : AlgebraicCycle X ℚ) :=
    (cyclesOfDimension.project_coe z).symm
  have hsum' : (z : AlgebraicCycle X ℚ) = ∑ j : Fin n, f j • (G j).divisor dimX := by
    rw [← hsum]
    exact Finset.sum_congr rfl (fun j _ ↦ by rw [← hG j])
  have hz_eq : z = ∑ j : Fin n,
      f j • cyclesOfDimension.projectLinear dimX (k + 1) ((G j).divisor dimX) := by
    rw [hzproj, hsum', map_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ LinearMap.map_smul _ _ _)
  rw [LinearMap.mem_ker, hz_eq, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [LinearMap.map_smul]
  by_cases hj : dimX (G j).subspace.genericPointImage = k + 2
  · have hmem := RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX hcov (G j)
      (show dimX (G j).subspace.genericPointImage = (k + 1) + 1 by omega)
    have hproj : cyclesOfDimension.projectLinear dimX (k + 1) ((G j).divisor dimX) =
        ⟨(G j).divisor dimX, hmem⟩ :=
      cyclesOfDimension.project_coe ⟨(G j).divisor dimX, hmem⟩
    rw [hproj, gysinCycle_divisor_eq_zero D i hker dimX dimZ k hU hcov (G j) hj, smul_zero]
  · have hmem : (G j).divisor dimX ∈
        cyclesOfDimension X dimX (dimX (G j).subspace.genericPointImage - 1) :=
      RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX hcov (G j) (by omega)
    have hproj : cyclesOfDimension.projectLinear dimX (k + 1) ((G j).divisor dimX) = 0 :=
      cyclesOfDimension.project_eq_zero_of_mem_ne hmem (by omega)
    rw [hproj, map_zero, smul_zero]

end Descent

/-! ## The Gysin map on Chow groups -/

section Gysin

variable {X Z : Scheme.{u}} [IsLocallyNoetherian X] [NoetherianSpace X]
  [IsLocallyNoetherian Z] [NoetherianSpace Z]
  (D : Curves.EffectiveCartierDivisor X) (i : Z ⟶ X) [IsClosedImmersion i]
  (hker : i.ker = D.idealSheaf) (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x))
  {dimX : DimensionFunction X} (hcov : HomogeneityLocal.CovByDimension dimX)
  (dimZ : DimensionFunction Z) (k : ℤ)

/-- **The Gysin map of an effective Cartier divisor on Chow groups**,
`i^* : A_{k+1}(X) →ₗ[ℚ] A_k(Z)` (Stacks, Definition 42.29.1 and Lemma 42.30.2): the descent of
`gysinCycle` through rational equivalence. -/
noncomputable def gysin :
    (chowSystem dimX (k + 1)).ChowGroup →ₗ[ℚ] (chowSystem dimZ k).ChowGroup :=
  Submodule.liftQ (chowSystem dimX (k + 1)).relations (gysinCycle D i hker dimX dimZ k)
    (gysinCycle_relations_le_ker D i hker dimX dimZ k hU hcov)

/-- `gysin` on the class of a cycle is `gysinCycle`. -/
theorem gysin_quotientMap (α : cyclesOfDimension X dimX (k + 1)) :
    gysin D i hker hU hcov dimZ k ((chowSystem dimX (k + 1)).quotientMap α) =
      gysinCycle D i hker dimX dimZ k α :=
  Submodule.liftQ_apply (chowSystem dimX (k + 1)).relations (gysinCycle D i hker dimX dimZ k) α

/-- **`i_* i^* = c₁(O(D)) ∩ -` on Chow groups** (Stacks, Lemma 42.29.4): for
`α ∈ A_{k+1}(X)`, the pushforward to `X` of `i^* α` is `c₁(O(D)) ∩ α`. -/
theorem closedImmersionPushforward_gysin (α : (chowSystem dimX (k + 1)).ChowGroup) :
    closedImmersionPushforward (chowSystem dimZ k) i (chowSystem dimX k)
        (gysin D i hker hU hcov dimZ k α) =
      firstChernClass hU hcov D.lineBundleData k α := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  change closedImmersionPushforward (chowSystem dimZ k) i (chowSystem dimX k)
      (gysin D i hker hU hcov dimZ k ((chowSystem dimX (k + 1)).quotientMap a)) =
    firstChernClass hU hcov D.lineBundleData k ((chowSystem dimX (k + 1)).quotientMap a)
  rw [gysin_quotientMap, firstChernClass_quotientMap,
    closedImmersionPushforward_gysinCycle D i hker dimX dimZ k hcov a]

/-- **`i^* i_* = c₁(O(D)|_Z) ∩ -` on Chow groups** (Stacks, Lemma 42.30.3): for
`β ∈ A_{k+1}(Z)`, `i^* (i_* β) = c₁(O(D)|_Z) ∩ β`, where `c₁` on `Z` is `firstChernClass` for
any admissible `hUZ`, `hcovZ`. -/
theorem gysin_closedImmersionPushforward
    (hUZ : ∀ z : Z, UnitDifferences (Z.presheaf.stalk z))
    (hcovZ : HomogeneityLocal.CovByDimension dimZ) (β : (chowSystem dimZ (k + 1)).ChowGroup) :
    gysin D i hker hU hcov dimZ k
        (closedImmersionPushforward (chowSystem dimZ (k + 1)) i (chowSystem dimX (k + 1)) β) =
      firstChernClass hUZ hcovZ (D.lineBundleData.restrict i) k β := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ β
  change gysin D i hker hU hcov dimZ k
      (closedImmersionPushforward (chowSystem dimZ (k + 1)) i (chowSystem dimX (k + 1))
        ((chowSystem dimZ (k + 1)).quotientMap b)) =
    firstChernClass hUZ hcovZ (D.lineBundleData.restrict i) k
      ((chowSystem dimZ (k + 1)).quotientMap b)
  rw [closedImmersionPushforward_quotientMap, gysin_quotientMap, firstChernClass_quotientMap,
    gysinCycle_properPushforward]

/-- **The Gysin map on a point class outside `D`**: for `x ∉ D.support` with `dimX x = k + 1`,
`i^* [x]` is the class of the restriction to `Z` of the divisor of the canonical section of
`O(D)` along `pointSubscheme x` (which is supported in `D.support`, the image of `i`). -/
theorem gysin_point_of_not_mem_support {x : X} (hx : x ∉ D.support) (hk : dimX x = k + 1) :
    gysin D i hker hU hcov dimZ k
        ((chowSystem dimX (k + 1)).quotientMap (cyclesOfDimension.point x hk)) =
      (chowSystem dimZ k).quotientMap (cyclesOfDimension.pullbackClosed (dimensionW := dimZ) i
        ⟨(D.canonicalSection (pointSubscheme x)
            (D.genericPointImage_pointSubscheme_not_mem hx)).divisor dimX,
          (D.canonicalSection (pointSubscheme x)
            (D.genericPointImage_pointSubscheme_not_mem hx)).divisor_mem_cyclesOfDimension dimX
              hcov (by rw [genericPointImage_pointSubscheme]; exact hk)⟩) := by
  rw [gysin_quotientMap, gysinCycle_point, gysinSummand_of_not_mem_support D i hker dimX dimZ k hx,
    gysinProj_eq_quotientMap]

/-- **The Gysin map on a point class of `D`**: for `z : Z` with `dimZ z = k + 1`,
`i^* [i z] = c₁(O(D)|_Z) ∩ [closure z]` (`chernSummand`). -/
theorem gysin_point_base (z : Z) (hk : dimZ z = k + 1) :
    gysin D i hker hU hcov dimZ k ((chowSystem dimX (k + 1)).quotientMap
        (cyclesOfDimension.point (i.base z)
          ((DimensionFunction.apply_eq_of_isClosedImmersion dimZ dimX i z).symm.trans hk))) =
      chernSummand (D.lineBundleData.restrict i) dimZ k z := by
  rw [gysin_quotientMap, gysinCycle_point, gysinSummand_base]

end Gysin

end GromovWitten.AlgebraicGeometry.IntersectionTheory
