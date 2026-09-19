/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.CycleGluing
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyInjective
import GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace

/-!
# A Zariski-local criterion for homogeneity of principal divisors

`PrincipalDivisorsHomogeneous X dimension` (`IntersectionTheory/LocalizationExact.lean`) says that
the divisor of every rational function on every integral closed subscheme of `X` is concentrated
in a single dimension.  `IntersectionTheory/CycleGluing.lean` shows that this property restricts
to open subschemes, but its local-to-global converse there needs the auxiliary hypothesis
`hcommon` because homogeneity of a single generator gives one dimension per member of the cover
and nothing compares them.

This file removes that hypothesis by strengthening the local input to a genuinely pointwise
condition on the dimension grading, namely that it drops by exactly one along the covering
relation of the specialisation order:

`CovByDimension dimension : Prop := ∀ x η, x ⋖ η → dimension x + 1 = dimension η`.

Since `x ⋖ η` is a relation between two points of `X`, this condition is stable under both
restriction to and gluing along an open cover, and it implies homogeneity outright: the divisor
of a rational function on an integral closed subscheme `V` is supported at the points of coheight
one of `V`, and these are exactly the points covered by the generic point of `V`.

## Main results

* `HomogeneityLocal.coheight_eq_one_iff_covBy`: in a preorder with a top element `t`, a point has
  coheight one exactly when it is covered by `t`.
* `HomogeneityLocal.covBy_map_of_isOpenImmersion`, `HomogeneityLocal.covBy_map_of_isClosedImmersion`
  and `HomogeneityLocal.covBy_of_covBy_map`: the covering relation of the specialisation order is
  preserved and reflected by open and closed immersions of schemes.
* `HomogeneityLocal.CovByDimension` and
  `HomogeneityLocal.principalDivisorsHomogeneous_of_covByDimension`: the local criterion and the
  fact that it implies `PrincipalDivisorsHomogeneous`.
* `HomogeneityLocal.covByDimension_of_cover` and `HomogeneityLocal.covByDimension_restrict`: the
  criterion is Zariski-local, in both directions.
* `HomogeneityLocal.covByDimension_of_dimensionFormula`: on an affine scheme the criterion follows
  from the dimension formula for all prime quotients of the coordinate ring.
* `HomogeneityLocal.principalDivisorsHomogeneous_of_affineCover` and
  `HomogeneityLocal.principalDivisorsHomogeneous_of_charts`: homogeneity of principal divisors for
  a scheme with an affine cover whose coordinate rings satisfy the dimension formula.
* `HomogeneityLocal.principalDivisorsHomogeneous_totalSpace`: the corollary for the total space of
  a global vector bundle `VectorBundleTotalSpace.BundleData X ι`.

All statements are unconditional apart from the dimension-formula hypotheses, which the repository
carries everywhere because Mathlib has no catenarity statement for finite type algebras.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

universe u v

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace HomogeneityLocal

/-! ## The specialisation order -/

/-- Being below another point in the specialisation order of a scheme means being a
specialisation of it. -/
theorem le_iff_specializes {X : Scheme.{u}} {x y : X} : x ≤ y ↔ y ⤳ x := Iff.rfl

/-- The generic point of an irreducible scheme is the greatest point for the specialisation
order. -/
theorem isTop_genericPoint (V : Scheme.{u}) [IrreducibleSpace V] :
    IsTop (genericPoint V) := fun y ↦ (genericPoint_spec V).specializes (Set.mem_univ y)

/-! ## Coheight one and the covering relation -/

/-- In a preorder with a greatest element `t`, a point has coheight one exactly when it is covered
by `t`.  This is the order-theoretic form of "codimension one inside an irreducible space". -/
theorem coheight_eq_one_iff_covBy {α : Type*} [Preorder α] {t y : α} (ht : IsTop t) :
    Order.coheight y = 1 ↔ y ⋖ t := by
  have hmaxt : IsMax t := ht.isMax
  have htop : Order.coheight t = 0 := Order.coheight_eq_zero.2 hmaxt
  have hmax_of : ∀ z : α, t ≤ z → IsMax z := fun z hz b hb ↦ le_trans (ht b) hz
  constructor
  · intro h
    have hnotmax : ¬ IsMax y := by
      intro hcon
      rw [Order.coheight_eq_zero.2 hcon] at h
      exact zero_ne_one h
    have hlt : y < t := lt_of_le_not_ge (ht y) fun hcon ↦ hnotmax (hmax_of y hcon)
    refine ⟨hlt, fun z hz1 hz2 ↦ ?_⟩
    have h' : Order.coheight y = ((1 : ℕ) : ℕ∞) := by rw [h]; norm_num
    have hmaximal := Order.coheight_eq_coe_iff_maximal_le_coheight.mp h'
    have h1 : ((1 : ℕ) : ℕ∞) ≤ Order.coheight z := by
      rw [Nat.cast_one, Order.one_le_iff_ne_zero]
      exact Order.coheight_ne_zero.2 fun hcon ↦ not_le_of_gt hz2 (hcon (ht z))
    exact not_le_of_gt hz1 (hmaximal.2 h1 hz1.le)
  · intro h
    have hnotmax : ¬ IsMax y := fun hcon ↦ not_le_of_gt h.1 (hcon (ht y))
    refine le_antisymm ?_ ?_
    · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by norm_num]
      refine Order.coheight_le_coe_iff.2 fun z hz ↦ ?_
      have hz' : IsMax z := hmax_of z (by
        by_contra hcon
        exact h.2 hz (lt_of_le_not_ge (ht z) hcon))
      rw [Order.coheight_eq_zero.2 hz']
      norm_num
    · rw [Order.one_le_iff_ne_zero]
      exact Order.coheight_ne_zero.2 hnotmax

/-! ## Transfer of the covering relation along immersions -/

section Transfer

variable {X Y : Scheme.{u}}

/-- A morphism of schemes which is a topological inducing map is strictly monotone for the
specialisation order. -/
theorem map_lt (f : Y ⟶ X) (hind : IsInducing f.base) {a b : Y} (hab : a < b) :
    f.base a < f.base b :=
  lt_of_le_not_ge (le_iff_specializes.2 ((le_iff_specializes.1 hab.le).map f.continuous))
    fun hcon ↦ not_le_of_gt hab (le_iff_specializes.2
      (hind.specializes_iff.1 (le_iff_specializes.1 hcon)))

/-- A morphism of schemes which is a topological inducing map reflects the strict specialisation
order. -/
theorem lt_of_map_lt (f : Y ⟶ X) (hind : IsInducing f.base) {a b : Y}
    (hab : f.base a < f.base b) : a < b :=
  lt_of_le_not_ge (le_iff_specializes.2 (hind.specializes_iff.1 (le_iff_specializes.1 hab.le)))
    fun hcon ↦ not_le_of_gt hab (le_iff_specializes.2
      ((le_iff_specializes.1 hcon).map f.continuous))

/-- A morphism of schemes which is a topological inducing map and whose image contains every point
lying strictly between the images of `y` and `η` preserves the covering relation. -/
theorem covBy_map_base (f : Y ⟶ X) (hind : IsInducing f.base) {y η : Y} (h : y ⋖ η)
    (hmem : ∀ z : X, z ⤳ f.base y → f.base η ⤳ z → z ∈ Set.range f.base) :
    f.base y ⋖ f.base η := by
  refine ⟨map_lt f hind h.1, fun z hz1 hz2 ↦ ?_⟩
  obtain ⟨w, rfl⟩ := hmem z (le_iff_specializes.1 hz1.le) (le_iff_specializes.1 hz2.le)
  exact h.2 (lt_of_map_lt f hind hz1) (lt_of_map_lt f hind hz2)

/-- An open immersion preserves the covering relation of the specialisation order: every
generalisation of a point of an open subset lies in that open subset. -/
theorem covBy_map_of_isOpenImmersion (f : Y ⟶ X) [_root_.AlgebraicGeometry.IsOpenImmersion f]
    {y η : Y} (h : y ⋖ η) : f.base y ⋖ f.base η :=
  covBy_map_base f f.isOpenEmbedding.isInducing h
    fun _ hz _ ↦ hz.mem_open f.isOpenEmbedding.isOpen_range ⟨y, rfl⟩

/-- A closed immersion preserves the covering relation of the specialisation order: every
specialisation of a point of a closed subset lies in that closed subset. -/
theorem covBy_map_of_isClosedImmersion (f : Y ⟶ X) [_root_.AlgebraicGeometry.IsClosedImmersion f]
    {y η : Y} (h : y ⋖ η) : f.base y ⋖ f.base η := by
  refine covBy_map_base f f.isClosedEmbedding.isInducing h fun z _ hz ↦ ?_
  have hsub : closure ({f.base η} : Set X) ⊆ Set.range f.base := by
    rw [← f.isClosedEmbedding.isClosed_range.closure_eq]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨η, rfl⟩)
  exact hsub hz.mem_closure

/-- A morphism of schemes which is a topological inducing map reflects the covering relation of
the specialisation order. -/
theorem covBy_of_covBy_map (f : Y ⟶ X) (hind : IsInducing f.base) {y η : Y}
    (h : f.base y ⋖ f.base η) : y ⋖ η :=
  ⟨lt_of_map_lt f hind h.1, fun _ hw1 hw2 ↦ h.2 (map_lt f hind hw1) (map_lt f hind hw2)⟩

end Transfer

/-! ## The local criterion -/

/-- The dimension grading drops by exactly one along the covering relation of the specialisation
order.  This is the pointwise form of catenarity that homogeneity of principal divisors needs, and
unlike `PrincipalDivisorsHomogeneous` it is visibly a Zariski-local condition. -/
def CovByDimension {X : Scheme.{u}} (dimension : DimensionFunction X) : Prop :=
  ∀ x η : X, x ⋖ η → dimension x + 1 = dimension η

/-- **The local criterion implies homogeneity of principal divisors.**  The divisor of a rational
function on an integral closed subscheme `V ⊆ X` is supported at the points of coheight one of
`V`, which are exactly the points covered by the generic point of `V`; their images in `X` are
therefore all covered by the image of the generic point, so they all have the same dimension. -/
theorem principalDivisorsHomogeneous_of_covByDimension {X : Scheme.{u}}
    (dimension : DimensionFunction X) (hcov : CovByDimension dimension) :
    PrincipalDivisorsHomogeneous X dimension := by
  intro g
  refine ⟨dimension (g.subspace.inclusion.base (genericPoint g.subspace.scheme)) - 1, ?_⟩
  intro x hx
  unfold RationalFunctionGenerator.divisor IntegralClosedSubscheme.pushforward at hx
  by_cases hmem : x ∈ Set.range g.subspace.inclusion.base
  · obtain ⟨y, rfl⟩ := hmem
    rw [AlgebraicCycle.map_closedImmersion_apply_image g.subspace.inclusion
      (dimension : X → ℤ), _root_.AlgebraicGeometry.Scheme.principalCycle_apply] at hx
    have hord : g.subspace.scheme.ord
        (g.function : g.subspace.scheme.functionField) y ≠ 0 := by
      intro hcon
      rw [hcon] at hx
      exact hx (by norm_num)
    have hco : Order.coheight y = 1 := by
      by_contra hcon
      exact hord (_root_.AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hcon _)
    have hcovy : y ⋖ genericPoint g.subspace.scheme :=
      (coheight_eq_one_iff_covBy (isTop_genericPoint g.subspace.scheme)).1 hco
    have hkey := hcov _ _ (covBy_map_of_isClosedImmersion g.subspace.inclusion hcovy)
    omega
  · exact absurd (AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range
      g.subspace.inclusion (dimension : X → ℤ) _ x hmem) hx

/-! ## Zariski locality of the criterion -/

/-- The local criterion restricts to an open subscheme. -/
theorem covByDimension_restrict {X Y : Scheme.{u}} (f : Y ⟶ X)
    [_root_.AlgebraicGeometry.IsOpenImmersion f] (dimensionX : DimensionFunction X)
    (dimensionY : DimensionFunction Y) (hdim : ∀ y, dimensionY y = dimensionX (f.base y))
    (h : CovByDimension dimensionX) : CovByDimension dimensionY := by
  intro y η hc
  rw [hdim y, hdim η]
  exact h _ _ (covBy_map_of_isOpenImmersion f hc)

/-- **The local criterion is Zariski-local.**  If it holds on the members of an open cover, with
dimension functions compatible with the one on `X`, then it holds on `X`: both points of a
covering pair lie in a common member of the cover, because the larger one is a generalisation of
the smaller one. -/
theorem covByDimension_of_cover {X : Scheme.{u}} {J : Type v} {Y : J → Scheme.{u}}
    (f : ∀ j, Y j ⟶ X) [hopen : ∀ j, _root_.AlgebraicGeometry.IsOpenImmersion (f j)]
    (hcov : ⨆ j, (f j).opensRange = ⊤) (dimensionX : DimensionFunction X)
    (dimensionY : ∀ j, DimensionFunction (Y j))
    (hdim : ∀ (j : J) (y : Y j), dimensionY j y = dimensionX ((f j).base y))
    (hloc : ∀ j, CovByDimension (dimensionY j)) : CovByDimension dimensionX := by
  intro x η hc
  obtain ⟨j, hj⟩ := CycleGluing.exists_mem_of_iSup_eq_top hcov x
  have hη : η ∈ (f j).opensRange :=
    (le_iff_specializes.1 hc.1.le).mem_open (f j).opensRange.isOpen hj
  obtain ⟨x', hx'⟩ := hj
  obtain ⟨η', hη'⟩ := hη
  have hc' : x' ⋖ η' := by
    refine covBy_of_covBy_map (f j) (f j).isOpenEmbedding.isInducing ?_
    rw [hx', hη']
    exact hc
  have hkey := hloc j x' η' hc'
  rw [hdim j x', hdim j η', hx', hη'] at hkey
  exact hkey

/-! ## The affine case -/

section Affine

variable {A : Type u} [CommRing A]

/-- The specialisation order on the points of an affine scheme is the reverse of the inclusion
order on prime ideals. -/
theorem specLE_iff (x y : ↥(Spec (CommRingCat.of A))) :
    x ≤ y ↔ (y : PrimeSpectrum A).asIdeal ≤ (x : PrimeSpectrum A).asIdeal := by
  constructor
  · intro h
    exact ((VectorBundle.specOrderIso A).le_iff_le).2 h
  · intro h
    exact ((VectorBundle.specOrderIso A).le_iff_le).1 h

/-- A point of an affine scheme whose prime is the zero ideal is the greatest point for the
specialisation order. -/
theorem isTop_of_asIdeal_eq_bot (t : ↥(Spec (CommRingCat.of A)))
    (ht : (t : PrimeSpectrum A).asIdeal = ⊥) : IsTop t := fun s ↦
  (specLE_iff s t).2 (by rw [ht]; exact bot_le)

/-- **The affine case of the local criterion.**  If every prime quotient of `A` satisfies the
dimension formula then the certified dimension grading of `Spec A` drops by exactly one along the
covering relation: a covering pair `x ⋖ η` exhibits the image of `x` as a height-one prime of
`A ⧸ η`, and the dimension formula for `A ⧸ η` converts this into the dimension statement. -/
theorem covByDimension_of_dimensionFormula
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (hdf : ∀ P : Ideal A, P.IsPrime → HasDimensionFormula (A ⧸ P)) :
    CovByDimension dimA := by
  intro x η hc
  obtain ⟨P, hPdef⟩ : ∃ P : Ideal A, P = (η : PrimeSpectrum A).asIdeal := ⟨_, rfl⟩
  have hPprime : P.IsPrime := hPdef ▸ (η : PrimeSpectrum A).isPrime
  have hxprime : ((x : PrimeSpectrum A).asIdeal).IsPrime := (x : PrimeSpectrum A).isPrime
  have hPle : P ≤ (x : PrimeSpectrum A).asIdeal := by
    rw [hPdef]
    exact (specLE_iff x η).1 hc.1.le
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have hqprime : (((x : PrimeSpectrum A).asIdeal).map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [hker]; exact hPle)
  obtain ⟨q, hq⟩ : ∃ q : ↥(Spec (CommRingCat.of (A ⧸ P))),
      (q : PrimeSpectrum (A ⧸ P)).asIdeal =
        ((x : PrimeSpectrum A).asIdeal).map (Ideal.Quotient.mk P) :=
    ⟨show ↥(Spec (CommRingCat.of (A ⧸ P))) from ⟨_, hqprime⟩, rfl⟩
  have hxq : (x : PrimeSpectrum A).asIdeal =
      (q : PrimeSpectrum (A ⧸ P)).asIdeal.comap (Ideal.Quotient.mk P) := by
    rw [hq, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, hker]
    exact (sup_eq_left.2 hPle).symm
  have hdom : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  obtain ⟨t, ht⟩ : ∃ t : ↥(Spec (CommRingCat.of (A ⧸ P))),
      (t : PrimeSpectrum (A ⧸ P)).asIdeal = ⊥ :=
    ⟨show ↥(Spec (CommRingCat.of (A ⧸ P))) from ⟨⊥, Ideal.isPrime_bot⟩, rfl⟩
  -- the image of `x` is covered by the generic point of `Spec (A ⧸ P)`
  have hqlt : q < t := by
    refine lt_of_le_not_ge ((specLE_iff q t).2 (by rw [ht]; exact bot_le)) fun hcon ↦ ?_
    have hbot : (q : PrimeSpectrum (A ⧸ P)).asIdeal ≤ ⊥ := by
      have hle := (specLE_iff t q).1 hcon
      rwa [ht] at hle
    have hxP : (x : PrimeSpectrum A).asIdeal = P := by
      rw [hxq, le_bot_iff.1 hbot, ← RingHom.ker_eq_comap_bot, hker]
    exact not_le_of_gt hc.1 ((specLE_iff η x).2 (le_of_eq (by rw [hxP, hPdef])))
  have hcovq : q ⋖ t := by
    refine ⟨hqlt, fun w hw1 hw2 ↦ ?_⟩
    have hwprime : ((w : PrimeSpectrum (A ⧸ P)).asIdeal).IsPrime :=
      (w : PrimeSpectrum (A ⧸ P)).isPrime
    have hw1' : (w : PrimeSpectrum (A ⧸ P)).asIdeal ≤ (q : PrimeSpectrum (A ⧸ P)).asIdeal :=
      (specLE_iff q w).1 hw1.le
    have hw1'' : ¬ (q : PrimeSpectrum (A ⧸ P)).asIdeal ≤ (w : PrimeSpectrum (A ⧸ P)).asIdeal :=
      fun hcon ↦ not_le_of_gt hw1 ((specLE_iff w q).2 hcon)
    have hw2' : ¬ (w : PrimeSpectrum (A ⧸ P)).asIdeal ≤ ⊥ := by
      intro hcon
      refine not_le_of_gt hw2 ((specLE_iff t w).2 ?_)
      rw [ht]
      exact hcon
    obtain ⟨W, hW⟩ : ∃ W : ↥(Spec (CommRingCat.of A)),
        (W : PrimeSpectrum A).asIdeal =
          (w : PrimeSpectrum (A ⧸ P)).asIdeal.comap (Ideal.Quotient.mk P) :=
      ⟨show ↥(Spec (CommRingCat.of A)) from ⟨_, Ideal.comap_isPrime _ _⟩, rfl⟩
    have hlt1 : x < W := by
      refine lt_of_le_not_ge ((specLE_iff x W).2 ?_) fun hcon ↦ hw1'' ?_
      · rw [hW, hxq]
        exact Ideal.comap_mono hw1'
      · have hxW := (specLE_iff W x).1 hcon
        rw [hxq, hW] at hxW
        exact (Ideal.comap_le_comap_iff_of_surjective (f := Ideal.Quotient.mk P)
          Ideal.Quotient.mk_surjective _ _).1 hxW
    have hPcomap : P = (⊥ : Ideal (A ⧸ P)).comap (Ideal.Quotient.mk P) := by
      rw [← RingHom.ker_eq_comap_bot]
      exact hker.symm
    have hlt2 : W < η := by
      refine lt_of_le_not_ge ((specLE_iff W η).2 ?_) fun hcon ↦ hw2' ?_
      · exact le_trans (le_of_eq hPdef.symm) (le_trans (le_of_eq hPcomap)
          (le_trans (Ideal.comap_mono bot_le) (le_of_eq hW.symm)))
      · have hWη := (specLE_iff η W).1 hcon
        have hchain : (w : PrimeSpectrum (A ⧸ P)).asIdeal.comap (Ideal.Quotient.mk P) ≤
            (⊥ : Ideal (A ⧸ P)).comap (Ideal.Quotient.mk P) :=
          le_trans (le_of_eq hW.symm)
            (le_trans hWη (le_trans (le_of_eq hPdef.symm) (le_of_eq hPcomap)))
        exact (Ideal.comap_le_comap_iff_of_surjective (f := Ideal.Quotient.mk P)
          Ideal.Quotient.mk_surjective _ _).1 hchain
    exact hc.2 hlt1 hlt2
  have hheight : (q : PrimeSpectrum (A ⧸ P)).asIdeal.height = 1 := by
    rw [← VectorBundle.coheight_eq_ideal_height (A ⧸ P) (q : PrimeSpectrum (A ⧸ P))]
    exact (coheight_eq_one_iff_covBy (isTop_of_asIdeal_eq_bot t ht)).2 hcovq
  -- and the dimension formula for `A ⧸ P` finishes the computation
  have h1 := VectorBundle.dimension_add_one_eq_ringKrullDim P dimA (hdf P hPprime) x
    (q : PrimeSpectrum (A ⧸ P)) hheight hxq
  have h2 := GromovWitten.Algebra.PrimeSpectrum.coheight_eq_ringKrullDim_quotient
    (η : PrimeSpectrum A)
  rw [VectorBundle.coheight_eq_dimension A dimA (η : PrimeSpectrum A), ← hPdef] at h2
  rw [← h2, WithBot.coe_inj] at h1
  have h3 : Int.toNat (dimA x) + 1 = Int.toNat (dimA η) := by exact_mod_cast h1
  have h4 := dimA.nonnegative x
  have h5 := dimA.nonnegative η
  omega

end Affine

/-! ## Homogeneity from an affine cover -/

/-- Homogeneity of principal divisors from the local criterion on the members of an open cover. -/
theorem principalDivisorsHomogeneous_of_openCover {X : Scheme.{u}} {J : Type v}
    {Y : J → Scheme.{u}} (f : ∀ j, Y j ⟶ X)
    [hopen : ∀ j, _root_.AlgebraicGeometry.IsOpenImmersion (f j)]
    (hcov : ⨆ j, (f j).opensRange = ⊤) (dimensionX : DimensionFunction X)
    (dimensionY : ∀ j, DimensionFunction (Y j))
    (hdim : ∀ (j : J) (y : Y j), dimensionY j y = dimensionX ((f j).base y))
    (hloc : ∀ j, CovByDimension (dimensionY j)) :
    PrincipalDivisorsHomogeneous X dimensionX :=
  principalDivisorsHomogeneous_of_covByDimension dimensionX
    (covByDimension_of_cover f hcov dimensionX dimensionY hdim hloc)

/-- **Homogeneity of principal divisors from an affine cover.**  A scheme covered by affine opens
whose coordinate rings satisfy the dimension formula for all prime quotients has homogeneous
principal divisors. -/
theorem principalDivisorsHomogeneous_of_affineCover {X : Scheme.{u}} {J : Type v}
    (R : J → CommRingCat.{u}) (f : ∀ j, Spec (R j) ⟶ X)
    [hopen : ∀ j, _root_.AlgebraicGeometry.IsOpenImmersion (f j)]
    (hcov : ⨆ j, (f j).opensRange = ⊤) (dimensionX : DimensionFunction X)
    (dimensionR : ∀ j, DimensionFunction (Spec (R j)))
    (hdim : ∀ (j : J) (y : ↥(Spec (R j))), dimensionR j y = dimensionX ((f j).base y))
    (hdf : ∀ (j : J) (P : Ideal ↥(R j)), P.IsPrime → HasDimensionFormula (↥(R j) ⧸ P)) :
    PrincipalDivisorsHomogeneous X dimensionX :=
  principalDivisorsHomogeneous_of_openCover f hcov dimensionX dimensionR hdim fun j ↦
    covByDimension_of_dimensionFormula (A := ↥(R j)) (dimensionR j) (hdf j)

/-- The universal dimension formula over `R` gives the dimension formula for every prime quotient
of `R` itself, through the polynomial ring in an empty family of variables. -/
theorem hasDimensionFormula_of_universal {R : Type u} [CommRing R]
    (h : VectorBundle.HasUniversalDimensionFormula R) (P : Ideal R) (hP : P.IsPrime) :
    HasDimensionFormula (R ⧸ P) := by
  have _ : P.IsPrime := hP
  refine VectorBundle.hasDimensionFormula_quotient_of_ringEquiv
    ((MvPolynomial.isEmptyAlgEquiv R PEmpty.{u + 1}).toRingEquiv) P ?_
  exact h PEmpty.{u + 1} _ inferInstance

/-- **Homogeneity of principal divisors for a scheme with affine charts.**  If the sections over
every chart satisfy the universal dimension formula — which holds for a finitely generated algebra
over a field — then all principal divisors on `X` are homogeneous. -/
theorem principalDivisorsHomogeneous_of_charts {X : Scheme.{u}} {J : Type v}
    (chart : J → X.affineOpens) (hchart : ⨆ j, ((chart j).1 : X.Opens) = ⊤)
    (dimensionX : DimensionFunction X)
    (dimensionChart : ∀ j, DimensionFunction (Spec Γ(X, (chart j).1)))
    (hdim : ∀ (j : J) (y : ↥(Spec Γ(X, (chart j).1))),
      dimensionChart j y = dimensionX ((chart j).2.fromSpec.base y))
    (huniv : ∀ j, VectorBundle.HasUniversalDimensionFormula Γ(X, (chart j).1)) :
    PrincipalDivisorsHomogeneous X dimensionX := by
  refine principalDivisorsHomogeneous_of_affineCover (fun j ↦ Γ(X, (chart j).1))
    (fun j ↦ (chart j).2.fromSpec)
    (hopen := fun j ↦ (chart j).2.isOpenImmersion_fromSpec) ?_ dimensionX
    dimensionChart hdim fun j P hP ↦ ?_
  · rw [← hchart]
    exact iSup_congr fun j ↦ (chart j).2.opensRange_fromSpec
  · exact hasDimensionFormula_of_universal (huniv j) P hP

/-- **Homogeneity of principal divisors on the total space of a global vector bundle.**  The
charts of the total space are the affine spaces `𝔸^ι_U` over the charts `U` of the base, and the
universal dimension formula over `Γ(X, U)` supplies the dimension formula for every prime quotient
of `MvPolynomial ι Γ(X, U)`. -/
theorem principalDivisorsHomogeneous_totalSpace {X : Scheme.{u}} {ι : Type u} [Finite ι]
    (𝓔 : VectorBundleTotalSpace.BundleData X ι)
    (dimensionE : DimensionFunction 𝓔.totalSpace)
    (dimensionChart : ∀ j : 𝓔.J,
      DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
    (hdim : ∀ (j : 𝓔.J)
      (y : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1))))),
      dimensionChart j y = dimensionE ((𝓔.chartι j).base y))
    (huniv : ∀ j, VectorBundle.HasUniversalDimensionFormula Γ(X, (𝓔.chart j).1)) :
    PrincipalDivisorsHomogeneous 𝓔.totalSpace dimensionE :=
  principalDivisorsHomogeneous_of_affineCover
    (fun j ↦ CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1))) (fun j ↦ 𝓔.chartι j)
    𝓔.iSup_opensRange_chartι dimensionE dimensionChart hdim
    fun j P hP ↦ hasDimensionFormula_of_universal ((huniv j).mvPolynomial ι) P hP

end HomogeneityLocal

end GromovWitten.AlgebraicGeometry.IntersectionTheory
