/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ClassifyingStackChow
import GromovWitten.AlgebraicGeometry.IntersectionTheory.AtlasIndependence
import GromovWitten.AlgebraicGeometry.Stacks.ConstantGroup
import GromovWitten.AlgebraicGeometry.Stacks.TorsorRepresentable
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProjectiveLineDegree
import GromovWitten.AlgebraicGeometry.Stacks.ClassifyingStackSelfOverlap
import GromovWitten.AlgebraicGeometry.Stacks.TrivialActionDiagonal

/-!
# Chow groups and degree of the stack `[Spec k / Γ]`

Let `k` be a field and `Γ` a finite group.  The classifying stack `BΓ_k` is the quotient stack
`[Spec k / Γ]` of the trivial action of the constant group scheme `Γ` on `Spec k`
(`ActionTorsor.quotientStack (constantGroup Γ) (constantTrivialAction k Γ)`).  Its atlas chart
`constantAtlasChart k Γ : Spec k → [Spec k / Γ]` (equal by `rfl` to
`ActionTorsor.atlasChart _ _ (Spec k) rfl`) is étale, surjective and representably quasi-compact,
so it has a chart groupoid `constantChartGroupoid k Γ = Spec k ×_{[Spec k/Γ]} Spec k ⇉ Spec k`
and a Vistoli Chow group `StackChart.vistoliChow` (structure morphism the identity of `Spec k`).

We compute it.  Since the atlas `Spec k` has a single point, of dimension zero, every cycle is
invariant and there is no nontrivial invariant system of dimension one; hence `A_0 ≃ ℚ` and
`A_i = 0` for `i ≠ 0` (this part does not use the explicit description of the self-overlap).
The fundamental class `[Spec k]` has Vistoli degree `1 / d` for every normalisation `d` with
`IsOfDegree d`; with the degree `|Γ|` of the atlas (`constantChartGroupoid_isOfDegree`, from
`ClassifyingStackSelfOverlap.lean`) this gives `deg [BΓ_k] = 1 / |Γ|`.  By atlas independence
(`StackChart.vistoliChowEquivOfEtaleCharts`) the computation of the Chow groups holds for every
étale surjective, representably quasi-compact chart with compact scheme locally of finite type
over `k`.

We also record two generic transport lemmas for the Vistoli degree.

## Main results

* `EtalePresentationGroupoid.vistoliDegree_apply_of_degree_eq`: a linear map of Vistoli Chow
  groups induced by a degree-preserving map of cycles preserves the Vistoli degree.
* `EtalePresentationGroupoid.vistoliDegree_moritaVistoliChowEquiv`: a Morita map whose map of
  atlases is an isomorphism over `Spec k` preserves the Vistoli degree.
* `ClassifyingStackChowStack.constantAtlasChart_quasiCompact`: the atlas is representably
  quasi-compact.
* `ClassifyingStackChowStack.classifyingChowZeroEquiv`: `A_0([Spec k / Γ]) ≃ₗ[ℚ] ℚ`.
* `ClassifyingStackChowStack.subsingleton_classifyingChow_of_ne_zero`: `A_i([Spec k / Γ]) = 0`
  for `i ≠ 0`.
* `ClassifyingStackChowStack.classifyingFundamentalClass`, with
  `classifyingChowZeroEquiv_fundamentalClass` (it corresponds to `1`),
  `classifyingDegree_fundamentalClass_of_isOfDegree` (its Vistoli degree is `1 / d`) and
  `classifyingDegree_fundamentalClass` (its Vistoli degree is `1 / |Γ|`).
* `ClassifyingStackChowStack.vistoliChowZeroEquivOfEtaleChart`,
  `subsingleton_vistoliChow_of_etaleChart_of_ne_zero`: the same Chow groups for any étale atlas.
* `ClassifyingStackChowStack.constantQuotient_vistoliChowZeroEquiv`: `A_0 ≃ ℚ` for the chosen
  atlas of the Deligne–Mumford stack `constantQuotientDeligneMumfordStack k Γ` (under the
  hypotheses of `DeligneMumfordStack.vistoliChowEquivOfChart`).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open FiniteTypeDimension

/-! ## Transport of the Vistoli degree -/

namespace EtalePresentationGroupoid

variable {k : Type u} [Field k] {H G : EtalePresentationGroupoid.{u}}

/-- **Transport of the Vistoli degree along a linear isomorphism of Vistoli Chow groups.**
If a linear map `Φ : A_0(G) → A_0(H)` sends the class of each Vistoli cycle `z` of `G` to the
class of a Vistoli cycle `f z` of `H` of the same degree, and `G`, `H` have the same degree `d`,
then `Φ` preserves the Vistoli degree. -/
theorem vistoliDegree_apply_of_degree_eq (hH : H.Good) (hG : G.Good)
    (sH : H.base ⟶ Spec (CommRingCat.of k)) (sG : G.base ⟶ Spec (CommRingCat.of k))
    [IsProper sH] [CompactSpace H.base] [Nonempty H.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian H.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian H.arrows]
    [_root_.AlgebraicGeometry.QuasiCompact H.src]
    [IsProper sG] [CompactSpace G.base] [Nonempty G.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian G.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian G.arrows]
    [_root_.AlgebraicGeometry.QuasiCompact G.src] {d : ℚ} (hdH : H.IsOfDegree d)
    (hdG : G.IsOfDegree d) (Φ : G.vistoliChow 0 →ₗ[ℚ] H.vistoliChow 0)
    (f : G.cycles 0 → H.cycles 0)
    (hΦ : ∀ z, Φ (G.vistoliQuotientMap 0 z) = H.vistoliQuotientMap 0 (f z))
    (hf : ∀ z, ZeroCycleDegree.degree sH H.baseDim (f z) =
      ZeroCycleDegree.degree sG G.baseDim z) (x : G.vistoliChow 0) :
    vistoliDegree hH sH hdH (Φ x) = vistoliDegree hG sG hdG x := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  change vistoliDegree hH sH hdH (Φ (G.vistoliQuotientMap 0 z)) = _
  rw [hΦ, vistoliDegree_mk, vistoliDegree_mk, hf]

/-- **Pullback along an isomorphism preserves the degree of zero-cycles.** -/
theorem degree_flatPullbackEtale_of_isIso {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (e : X ⟶ Y) [IsIso e] (sY : Y ⟶ Spec (CommRingCat.of k)) (dX : DimensionFunction X)
    (dY : DimensionFunction Y) (hd : ∀ x, dX x = dY (e.base x))
    (z : cyclesOfDimension Y dY 0) :
    ZeroCycleDegree.degree (e ≫ sY) dX (cyclesOfDimension.flatPullbackEtale e hd z) =
      ZeroCycleDegree.degree sY dY z := by
  rw [ZeroCycleDegree.degree_apply, ZeroCycleDegree.degree_apply]
  let eq : X ≃ Y := Equiv.ofBijective e.base
    (ConcreteCategory.bijective_of_isIso ((Scheme.forgetToTop).map e))
  rw [← finsum_comp_equiv eq]
  refine finsum_congr fun x ↦ ?_
  rw [cyclesOfDimension.flatPullbackEtale_apply,
    ProjectiveLineDegree.residueDegree_openImmersion]
  rfl

/-- **A Morita map whose map of atlases is an isomorphism preserves the Vistoli degree**: if
`φ : H → G` has `φ.onBase` an isomorphism compatible with the structure morphisms to `Spec k`,
and `H`, `G` both have degree `d`, then the Morita isomorphism `A_0(G) ≃ A_0(H)` preserves the
Vistoli degree. -/
theorem vistoliDegree_moritaVistoliChowEquiv (φ : MoritaMap H G) [IsIso φ.onBase]
    (hH : H.Good) (hG : G.Good)
    (sH : H.base ⟶ Spec (CommRingCat.of k)) (sG : G.base ⟶ Spec (CommRingCat.of k))
    (hs : φ.onBase ≫ sG = sH)
    [IsProper sH] [CompactSpace H.base] [Nonempty H.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian H.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian H.arrows]
    [_root_.AlgebraicGeometry.QuasiCompact H.src]
    [IsProper sG] [CompactSpace G.base] [Nonempty G.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian G.base]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian G.arrows]
    [_root_.AlgebraicGeometry.QuasiCompact G.src] {d : ℚ} (hdH : H.IsOfDegree d)
    (hdG : G.IsOfDegree d) (x : G.vistoliChow 0) :
    vistoliDegree hH sH hdH (φ.vistoliChowEquiv 0 hH hG x) = vistoliDegree hG sG hdG x := by
  subst hs
  exact vistoliDegree_apply_of_degree_eq hH hG _ sG hdH hdG
    (φ.vistoliChowEquiv 0 hH hG).toLinearMap (φ.onCycles 0) (fun _ ↦ rfl)
    (fun z ↦ degree_flatPullbackEtale_of_isIso φ.onBase sG H.baseDim G.baseDim φ.onBase_dim
      (z : cyclesOfDimension G.base G.baseDim 0)) x

end EtalePresentationGroupoid

/-! ## The atlas `Spec k → [Spec k / Γ]` and its chart groupoid -/

namespace ClassifyingStackChowStack

variable (k : Type u) [Field k] (Γ : Type u) [Group Γ] [Finite Γ] [DecidableEq Γ]

/-- The atlas `Spec k → [Spec k / Γ]` is representably quasi-compact (torsors under the finite
constant group are represented by finite schemes over the base). -/
theorem constantAtlasChart_quasiCompact :
    (constantAtlasChart k Γ).HasRepresentableProperty @_root_.AlgebraicGeometry.QuasiCompact :=
  have := ActionTorsor.isIso_atlasChart_eqToHom
    (rfl : (constantTrivialAction k Γ).space =
      AlgebraicSpace.ofScheme.obj (Spec (CommRingCat.of k)))
  have : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  ActionTorsor.schemeAtlasChart_hasRepresentableProperty_of_representation _ _ _ fun _ P ↦ by
    obtain ⟨R, -, hR, -⟩ := exists_torsorRepresentation_constantGroup Γ P
    exact ⟨R, inferInstance⟩

/-- Every point of the atlas `Spec k` has dimension zero. -/
theorem constantChartGroupoid_baseDim_apply (x : (constantChartGroupoid k Γ).base) :
    (constantChartGroupoid k Γ).baseDim x = 0 := by
  rw [ProperPushforwardDivisor.dimensionFunction_eq (constantChartGroupoid k Γ).baseDim
    (DimensionFunction.specField k)]
  rfl

/-! ## The Vistoli Chow groups of `[Spec k / Γ]` -/

/-- The dimension-zero Vistoli relations of the chart groupoid of `[Spec k / Γ]` vanish: an
invariant system of dimension `1` has empty support, every point of `Spec k` having dimension
`0`. -/
theorem constantChartGroupoid_vistoliRelations_eq_bot :
    (constantChartGroupoid k Γ).vistoliRelations 0 = ⊥ := by
  refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
  rintro z ⟨F, hF⟩
  have hs : F.support = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun w hw ↦ ?_
    have := F.dim_support w hw
    rw [constantChartGroupoid_baseDim_apply] at this
    norm_num at this
  have h0 : F.divisor = 0 := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.coe_injective
    funext x
    simp [InvariantSystem.divisor, InvariantSystem.divisorCycle, hs]
  change z = 0
  apply Subtype.ext
  rw [hF, h0]
  rfl

/-- On the chart groupoid of `[Spec k / Γ]` the dimension-zero cycles for the certified dimension
function are the dimension-zero cycles of `Spec k` for `DimensionFunction.specField k`. -/
theorem constantChartGroupoid_cyclesOfDimension_eq :
    cyclesOfDimension (constantChartGroupoid k Γ).base (constantChartGroupoid k Γ).baseDim 0 =
      cyclesOfDimension (Spec (CommRingCat.of k)) (DimensionFunction.specField k) 0 := by
  rw [ProperPushforwardDivisor.dimensionFunction_eq (constantChartGroupoid k Γ).baseDim
    (DimensionFunction.specField k)]

/-- **`A_0([Spec k / Γ]) ≃ ℚ`**: the dimension-zero Vistoli Chow group of the stack `[Spec k / Γ]`,
computed from its atlas `Spec k → [Spec k / Γ]` (structure morphism the identity of `Spec k`), is
identified with `ℚ` by evaluating a cycle at the unique point of `Spec k`. -/
noncomputable def classifyingChowZeroEquiv :
    (constantAtlasChart k Γ).vistoliChow (constantAtlasChart_isEtaleSurjective k Γ)
      (𝟙 (Spec (CommRingCat.of k))) 0
      ≃ₗ[ℚ] ℚ :=
  (((constantChartGroupoid k Γ).vistoliRelations 0).quotEquivOfEqBot
    (constantChartGroupoid_vistoliRelations_eq_bot k Γ)).trans
    ((LinearEquiv.ofTop _
      (EtalePresentationGroupoid.cycles_eq_top_of_subsingleton (constantChartGroupoid k Γ) 0)).trans
      ((LinearEquiv.ofEq _ _ (constantChartGroupoid_cyclesOfDimension_eq k Γ)).trans
        (PointChow.cyclesEquivRat k)))

/-- `classifyingChowZeroEquiv` evaluates (a representative cycle of) a class at the unique point
of `Spec k`. -/
theorem classifyingChowZeroEquiv_mk (z : (constantChartGroupoid k Γ).cycles 0) :
    classifyingChowZeroEquiv k Γ ((constantChartGroupoid k Γ).vistoliQuotientMap 0 z) =
      ((z : cyclesOfDimension (constantChartGroupoid k Γ).base
          (constantChartGroupoid k Γ).baseDim 0) :
        AlgebraicCycle (Spec (CommRingCat.of k)) ℚ) default :=
  rfl

/-- **`A_i([Spec k / Γ]) = 0` for `i ≠ 0`**: the Vistoli Chow group of the stack `[Spec k / Γ]` in
dimension `i ≠ 0`, computed from its atlas `Spec k`, is trivial. -/
theorem subsingleton_classifyingChow_of_ne_zero {i : ℤ} (hi : i ≠ 0) :
    Subsingleton ((constantAtlasChart k Γ).vistoliChow (constantAtlasChart_isEtaleSurjective k Γ)
      (𝟙 (Spec (CommRingCat.of k))) i) := by
  have hc : Subsingleton (cyclesOfDimension (constantChartGroupoid k Γ).base
      (constantChartGroupoid k Γ).baseDim i) := by
    refine ⟨fun a b ↦ Subtype.ext
      (Function.locallyFinsuppWithin.coe_injective (funext fun x ↦ ?_))⟩
    have hx : (constantChartGroupoid k Γ).baseDim x ≠ i := by
      rw [constantChartGroupoid_baseDim_apply]; exact hi.symm
    change (a : AlgebraicCycle _ ℚ) x = (b : AlgebraicCycle _ ℚ) x
    rw [a.2 x hx, b.2 x hx]
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ b
  rw [Subsingleton.elim a b]

/-- **The fundamental class `[BΓ_k] ∈ A_0([Spec k / Γ])`**: the Vistoli class of the fundamental
cycle `[Spec k]` of the atlas (coefficient one at its unique point). -/
noncomputable def classifyingFundamentalClass :
    (constantAtlasChart k Γ).vistoliChow (constantAtlasChart_isEtaleSurjective k Γ)
      (𝟙 (Spec (CommRingCat.of k))) 0 :=
  (constantChartGroupoid k Γ).vistoliQuotientMap 0
    ⟨cyclesOfDimension.fundamental (fun x _ ↦ constantChartGroupoid_baseDim_apply k Γ x), by
      rw [EtalePresentationGroupoid.cycles_eq_top_of_subsingleton]; trivial⟩

/-- Under `classifyingChowZeroEquiv` the fundamental class corresponds to `1`. -/
theorem classifyingChowZeroEquiv_fundamentalClass :
    classifyingChowZeroEquiv k Γ (classifyingFundamentalClass k Γ) = 1 :=
  (Spec (CommRingCat.of k)).fundamentalCycle_apply_of_isMax_of_isReduced default
    fun x _ ↦ (Subsingleton.elim x default).le

/-- **The Vistoli degree of the fundamental class is `1 / d`** for any normalisation `d` with
`(constantChartGroupoid k Γ).IsOfDegree d` (structure morphism the identity of `Spec k`). -/
theorem classifyingDegree_fundamentalClass_of_isOfDegree {d : ℚ}
    (hd : (constantChartGroupoid k Γ).IsOfDegree d) :
    EtalePresentationGroupoid.vistoliDegree (constantChartGroupoid_good k Γ)
        (𝟙 (Spec (CommRingCat.of k))) hd (classifyingFundamentalClass k Γ) = 1 / d := by
  rw [classifyingFundamentalClass, EtalePresentationGroupoid.vistoliDegree_mk,
    ZeroCycleDegree.degree_apply,
    finsum_eq_single _ default (fun x hx ↦ absurd (Subsingleton.elim x default) hx)]
  change 1 / d * ((Spec (CommRingCat.of k)).fundamentalCycle default * _) = _
  rw [(Spec (CommRingCat.of k)).fundamentalCycle_apply_of_isMax_of_isReduced default
    fun x _ ↦ (Subsingleton.elim x default).le, ClassifyingStackChow.residueDegree_id_specField]
  simp

/-- **`deg [BΓ_k] = 1 / |Γ|`**: the Vistoli degree of the fundamental class of `[Spec k / Γ]`,
computed from the atlas `Spec k` (structure morphism the identity of `Spec k`, normalisation
`constantChartGroupoid_isOfDegree`: the atlas has degree `|Γ|`), is `1 / |Γ|`.  `Γ` is a group,
hence nonempty. -/
theorem classifyingDegree_fundamentalClass :
    EtalePresentationGroupoid.vistoliDegree (constantChartGroupoid_good k Γ)
        (𝟙 (Spec (CommRingCat.of k))) (constantChartGroupoid_isOfDegree k Γ)
        (classifyingFundamentalClass k Γ) = 1 / Nat.card Γ :=
  classifyingDegree_fundamentalClass_of_isOfDegree k Γ _

/-- **`|Γ| · deg [BΓ_k] = 1`.** -/
theorem natCard_mul_classifyingDegree_fundamentalClass :
    (Nat.card Γ : ℚ) * EtalePresentationGroupoid.vistoliDegree (constantChartGroupoid_good k Γ)
        (𝟙 (Spec (CommRingCat.of k))) (constantChartGroupoid_isOfDegree k Γ)
        (classifyingFundamentalClass k Γ) = 1 := by
  rw [classifyingDegree_fundamentalClass]
  have : (Nat.card Γ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  field_simp

/-! ## Atlas independence -/

/-- **`A_0([Spec k / Γ]) ≃ ℚ` for any étale atlas.** For every étale surjective, representably
quasi-compact chart `B` of `[Spec k / Γ]` whose scheme is quasi-compact and locally of finite type
over `k` (structure morphism `sB`), the dimension-zero Vistoli Chow group computed from `B` is
`ℚ`: compose the atlas-independence isomorphism `StackChart.vistoliChowEquivOfEtaleCharts` (from
`B` to the atlas `Spec k`) with `classifyingChowZeroEquiv`. -/
noncomputable def vistoliChowZeroEquivOfEtaleChart
    (B : StackChart (ActionTorsor.quotientStack (constantGroup Γ) (constantTrivialAction k Γ)))
    (hB : B.IsEtaleSurjective)
    (hBq : B.HasRepresentableProperty @_root_.AlgebraicGeometry.QuasiCompact)
    [CompactSpace B.scheme] (sB : B.scheme ⟶ Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType sB] :
    B.vistoliChow hB sB 0 ≃ₗ[ℚ] ℚ :=
  (StackChart.vistoliChowEquivOfEtaleCharts (constantAtlasChart k Γ) B
    (constantAtlasChart_isEtaleSurjective k Γ) hB
    (constantAtlasChart_quasiCompact k Γ) hBq (𝟙 _) sB 0).symm.trans (classifyingChowZeroEquiv k Γ)

/-- **`A_i([Spec k / Γ]) = 0` for `i ≠ 0`, for any étale atlas** `B` as in
`vistoliChowZeroEquivOfEtaleChart`. -/
theorem subsingleton_vistoliChow_of_etaleChart_of_ne_zero
    (B : StackChart (ActionTorsor.quotientStack (constantGroup Γ) (constantTrivialAction k Γ)))
    (hB : B.IsEtaleSurjective)
    (hBq : B.HasRepresentableProperty @_root_.AlgebraicGeometry.QuasiCompact)
    [CompactSpace B.scheme] (sB : B.scheme ⟶ Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType sB] {i : ℤ} (hi : i ≠ 0) :
    Subsingleton (B.vistoliChow hB sB i) :=
  have := subsingleton_classifyingChow_of_ne_zero k Γ hi
  (StackChart.vistoliChowEquivOfEtaleCharts (constantAtlasChart k Γ) B
    (constantAtlasChart_isEtaleSurjective k Γ) hB
    (constantAtlasChart_quasiCompact k Γ) hBq (𝟙 _) sB i).symm.toEquiv.subsingleton

/-- **`A_0` of the Deligne–Mumford stack `[Spec k / Γ]` from its chosen atlas.** For the
Deligne–Mumford stack `constantQuotientDeligneMumfordStack k Γ`, the dimension-zero Vistoli Chow
group computed from the internally chosen étale atlas `chosenEtaleAtlas` is `ℚ`, provided that
atlas is representably quasi-compact with compact scheme locally of finite type over `k`
(hypotheses `hXq`, `sX`; nothing is known about the chosen atlas, which is
`Classical.choose`).  This is `DeligneMumfordStack.vistoliChowEquivOfChart` (comparison with the
explicit atlas `constantAtlasChart k Γ`) followed by `classifyingChowZeroEquiv`. -/
noncomputable def constantQuotient_vistoliChowZeroEquiv
    (hXq : (constantQuotientDeligneMumfordStack k Γ).chosenEtaleAtlas.HasRepresentableProperty
      @_root_.AlgebraicGeometry.QuasiCompact)
    [CompactSpace (constantQuotientDeligneMumfordStack k Γ).chosenEtaleAtlas.scheme]
    (sX : (constantQuotientDeligneMumfordStack k Γ).chosenEtaleAtlas.scheme ⟶
      Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType sX] :
    (constantQuotientDeligneMumfordStack k Γ).chosenEtaleAtlas.vistoliChow
      (constantQuotientDeligneMumfordStack k Γ).chosenEtaleAtlas_isEtaleSurjective sX 0
      ≃ₗ[ℚ] ℚ :=
  (DeligneMumfordStack.vistoliChowEquivOfChart (constantQuotientDeligneMumfordStack k Γ) hXq sX
    (constantAtlasChart k Γ) (constantAtlasChart_isEtaleSurjective k Γ)
    (constantAtlasChart_quasiCompact k Γ) (𝟙 _) 0).trans (classifyingChowZeroEquiv k Γ)

end ClassifyingStackChowStack

end GromovWitten.AlgebraicGeometry.IntersectionTheory
