/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.CartierGysin
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ZeroSectionCartier
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.GlobalVirtualClassSurjective

/-!
# Injectivity of the flat pullback along a rank-one bundle

Let `𝓔 : BundleData X ι` be a vector bundle of rank one (`[Unique ι]`) over a locally Noetherian
scheme `X` with Noetherian underlying space, with total space `E := 𝓔.totalSpace`, projection
`p := 𝓔.proj` and zero section `o := 𝓔.zeroSection`.  By `ZeroSectionCartier.lean` the zero
section is an effective Cartier divisor `D := zeroSectionDivisor 𝓔` on `E` whose ideal sheaf is
the kernel of `o`, so `CartierGysin.lean` provides the Gysin map
`o^* = gysin D o rfl hUE hcovE dimX k : A_{k+1}(E) →ₗ[ℚ] A_k(X)` (under the `firstChernClass`
hypotheses `hUE`, `hcovE` on `E`).  This file proves `o^* ∘ p^* = id` on Chow groups and deduces
that the flat pullback `p^* : A_k(X) →ₗ[ℚ] A_{k+1}(E)` (`chowPullbackBundleGlobal`) is injective
for **every** rank-one bundle, with no global trivialisation.

The computation is on point classes: for `x : X` with `dimX x = k` the pullback of `[x]` is the
class of the generic point `ξ := bundlePoint 𝓔 x` of `p⁻¹(closure x)`; it lies off `D`, and the
divisor of the canonical section of `O(D)` along `closure ξ` is `[o x]`
(`canonicalSection_pointSubscheme_zeroSectionDivisor_divisor`), whose restriction along `o` is
`[x]`.

## Main results

* `pullbackBundle_mem_cyclesOfDimension`: for a rank-one bundle the pullback of a cycle of
  dimension `k` is a cycle of dimension `k + 1`.
* `gysinSummand_bundlePoint`: the Gysin summand of `D` at `bundlePoint 𝓔 x` is the class of
  `pointProj dimX k x`.
* `gysinCycle_pullbackBundle`, `gysin_pullbackBundle`: `o^* (p^* a) = [a]` on cycles and on
  Chow groups.
* `gysin_chowPullbackBundleGlobal`: `o^* ∘ p^* = id` with `p^* = chowPullbackBundleGlobal`
  (through the index cast `chowCastDim` identifying `k + Nat.card ι` with `k + 1`).
* `mem_totalRationalRelations_of_pullbackBundle`: a graded cycle whose pullback is rationally
  equivalent to zero is itself rationally equivalent to zero.
* `chowPullbackBundleGlobal_injective_rankOne`: injectivity of `chowPullbackBundleGlobal` for
  every rank-one bundle, under the `firstChernClass` hypotheses on `E`.
* `bundlePullbackFT_injective_rankOne`, `virtualClassFT'_unique_rankOne`,
  `existsUnique_virtualClassFT'_rankOne`: over an infinite field, for `X` compact and locally of
  finite type, all hypotheses are discharged; the virtual class of a rank-one obstruction bundle
  is the unique class with `p^* [X]^vir = [C(E)]`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace RankOneBundleInjective

open LineBundleInjective BundlePullbackGlobal BundleOverSubscheme
open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
open _root_.GromovWitten.AlgebraicGeometry.IntersectionTheory.VectorBundle (UnitDifferences)

/-! ## Transport of Chow groups along an equality of dimension indices -/

section Cast

variable {X : Scheme.{u}} {dim : DimensionFunction X}

/-- Transport of the dimension-graded Chow group along an equality `m = n` of dimension
indices (the identity after substitution). -/
noncomputable def chowCastDim {m n : ℤ} (h : m = n) :
    (chowSystem dim m).ChowGroup ≃ₗ[ℚ] (chowSystem dim n).ChowGroup := by
  subst h
  exact LinearEquiv.refl ℚ _

/-- `chowCastDim` on the class of a cycle is the class of the same cycle. -/
theorem chowCastDim_quotientMap {m n : ℤ} (h : m = n) (a : cyclesOfDimension X dim m) :
    chowCastDim (dim := dim) h ((chowSystem dim m).quotientMap a) =
      (chowSystem dim n).quotientMap ⟨a, by rw [← h]; exact a.2⟩ := by
  subst h
  rfl

end Cast

/-! ## The dimension shift and the pullback of graded cycles for a rank-one bundle -/

section Shift

variable {X : Scheme.{u}} {ι : Type u} [Unique ι] (𝓔 : BundleData X ι)
  {dimX : DimensionFunction X} {dimE : DimensionFunction 𝓔.totalSpace}
  (hshift : ∀ x, dimE (bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ))

include hshift in
/-- For a rank-one bundle the dimension shift is `1`. -/
theorem dimE_bundlePoint_eq_add_one (x : X) : dimE (bundlePoint 𝓔 x) = dimX x + 1 := by
  rw [hshift x, Nat.card_unique, Nat.cast_one]

include hshift in
/-- The generic point of the fibre over `x` has dimension one more than the zero-section point
`o x` (the certified dimensions of `X` and `E` agree along the closed immersion `o`). -/
theorem dimE_bundlePoint_eq_zeroSection_add_one (x : X) :
    dimE (bundlePoint 𝓔 x) = dimE (𝓔.zeroSection x) + 1 := by
  rw [dimE_bundlePoint_eq_add_one 𝓔 hshift x,
    DimensionFunction.apply_eq_of_isClosedImmersion dimX dimE 𝓔.zeroSection x]

include hshift in
/-- The flat pullback of a cycle of dimension `k` along a rank-one bundle is a cycle of
dimension `k + 1`. -/
theorem pullbackBundle_mem_cyclesOfDimension (k : ℤ) (a : cyclesOfDimension X dimX k) :
    pullbackBundle 𝓔 (a : AlgebraicCycle X ℚ) ∈ cyclesOfDimension 𝓔.totalSpace dimE (k + 1) := by
  intro q hq
  by_contra hne
  have hsupp : q ∈ Function.support (pullbackBundleFun 𝓔 a.1) := hne
  obtain ⟨x, rfl⟩ := support_pullbackBundleFun_subset 𝓔 a.1 hsupp
  have hval : (a : AlgebraicCycle X ℚ) x ≠ 0 := by
    rw [← pullbackBundle_apply_bundlePoint 𝓔 a.1 x]
    exact hne
  have hdx : dimX x = k := by
    by_contra hcon
    exact hval (a.2 x hcon)
  exact hq (by rw [dimE_bundlePoint_eq_add_one 𝓔 hshift x, hdx])

/-- The kernel of the zero section is the ideal sheaf of the zero-section divisor (the
hypothesis `hker` of the Gysin map, here definitional). -/
theorem zeroSection_ker_eq_idealSheaf :
    𝓔.zeroSection.ker = (zeroSectionDivisor 𝓔).idealSheaf :=
  (zeroSectionDivisor_idealSheaf 𝓔).symm

end Shift

/-! ## The Gysin map of the zero section on pulled-back cycles -/

section Points

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : BundleData X ι)

/-- The restriction along the zero section of the point cycle at `o x` is the point cycle at
`x`. -/
theorem pullbackClosed_zeroSection_single [DecidableEq X] [DecidableEq 𝓔.totalSpace] (x : X) :
    AlgebraicCycle.pullbackClosed 𝓔.zeroSection
        (Function.locallyFinsuppWithin.single (𝓔.zeroSection x) (1 : ℚ)) =
      Function.locallyFinsuppWithin.single x (1 : ℚ) := by
  ext z
  rw [AlgebraicCycle.pullbackClosed_apply, Function.locallyFinsuppWithin.single_apply,
    Function.locallyFinsuppWithin.single_apply]
  by_cases hzx : z = x
  · subst hzx
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hzx, if_neg (fun h ↦ hzx (𝓔.zeroSection.isClosedEmbedding.injective h))]

/-- `qProj` of the point cycle at `x` is the class of `pointProj dim k x`. -/
theorem qProj_single [DecidableEq X] (dim : DimensionFunction X) (k : ℤ) (x : X) :
    qProj dim k (Function.locallyFinsuppWithin.single x (1 : ℚ)) =
      (chowSystem dim k).quotientMap (cyclesOfDimension.pointProj dim k x) := by
  change (chowSystem dim k).quotientMap (cyclesOfDimension.projectLinear dim k _) = _
  congr 1
  apply Subtype.ext
  ext y
  change (cyclesOfDimension.project (dimension := dim) (i := k)
    (Function.locallyFinsuppWithin.single x (1 : ℚ)) : AlgebraicCycle X ℚ) y =
    (cyclesOfDimension.pointProj dim k x : AlgebraicCycle X ℚ) y
  rw [cyclesOfDimension.pointProj_apply, cyclesOfDimension.project_apply,
    Function.locallyFinsuppWithin.single_apply]
  by_cases hyk : dim y = k
  · by_cases hxy : y = x
    · rw [if_pos hyk, if_pos hxy, if_pos ⟨hxy.symm, hyk⟩]
    · rw [if_pos hyk, if_neg hxy, if_neg (fun h ↦ hxy h.1.symm)]
  · rw [if_neg hyk, if_neg (fun h ↦ hyk h.2)]

end Points

section Gysin

variable {X : Scheme.{u}} {ι : Type u} [Unique ι] (𝓔 : BundleData X ι)
  [IsLocallyNoetherian X] [NoetherianSpace X] [NoetherianSpace 𝓔.totalSpace]
  {dimX : DimensionFunction X} {dimE : DimensionFunction 𝓔.totalSpace}
  (hshift : ∀ x, dimE (bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ))

include hshift in
/-- **The Gysin summand of the zero-section divisor at a generic fibre point.**  For
`ξ := bundlePoint 𝓔 x`, which lies off the zero section, the Gysin summand is the class of the
restriction along `o` of the divisor `[o x]` of the canonical section, that is, the class of
`pointProj dimX k x`. -/
theorem gysinSummand_bundlePoint (k : ℤ) (x : X) :
    gysinSummand (zeroSectionDivisor 𝓔) 𝓔.zeroSection
        (zeroSection_ker_eq_idealSheaf 𝓔) dimE dimX k (bundlePoint 𝓔 x) =
      (chowSystem dimX k).quotientMap (cyclesOfDimension.pointProj dimX k x) := by
  classical
  rw [gysinSummand_of_not_mem_support _ _ _ _ _ _
      (bundlePoint_not_mem_support_zeroSectionDivisor 𝓔 x),
    canonicalSection_pointSubscheme_zeroSectionDivisor_divisor 𝓔 x dimE
      (dimE_bundlePoint_eq_zeroSection_add_one 𝓔 hshift x)]
  change qProj dimX k (AlgebraicCycle.pullbackClosed 𝓔.zeroSection _) = _
  rw [pullbackClosed_zeroSection_single, qProj_single]

include hshift in
/-- **`o^* p^* = id` on cycles**: the Gysin map of the zero-section divisor sends the flat
pullback of a graded cycle `a` to the class of `a`. -/
theorem gysinCycle_pullbackBundle (k : ℤ) (a : cyclesOfDimension X dimX k) :
    gysinCycle (zeroSectionDivisor 𝓔) 𝓔.zeroSection
        (zeroSection_ker_eq_idealSheaf 𝓔) dimE dimX k
        ⟨pullbackBundle 𝓔 a, pullbackBundle_mem_cyclesOfDimension 𝓔 hshift k a⟩ =
      (chowSystem dimX k).quotientMap a := by
  rw [gysinCycle_apply]
  change ∑ᶠ q, pullbackBundle 𝓔 a q •
    gysinSummand (zeroSectionDivisor 𝓔) 𝓔.zeroSection
        (zeroSection_ker_eq_idealSheaf 𝓔) dimE dimX k q = _
  have hsupp : Function.support (fun q : 𝓔.totalSpace => pullbackBundle 𝓔 a q •
      gysinSummand (zeroSectionDivisor 𝓔) 𝓔.zeroSection
        (zeroSection_ker_eq_idealSheaf 𝓔) dimE dimX k q) ⊆
      Set.range (bundlePoint 𝓔) :=
    (Function.support_smul_subset_left (fun q : 𝓔.totalSpace => pullbackBundle 𝓔 a q)
      (gysinSummand (zeroSectionDivisor 𝓔) 𝓔.zeroSection
        (zeroSection_ker_eq_idealSheaf 𝓔) dimE dimX k)).trans
      (support_pullbackBundleFun_subset 𝓔 a)
  rw [finsum_comp_of_injective_of_support_subset_range (bundlePoint_injective 𝓔) _ hsupp]
  simp_rw [pullbackBundle_apply_bundlePoint, gysinSummand_bundlePoint 𝓔 hshift k,
    ← map_smul (chowSystem dimX k).quotientMap]
  have hfin : Function.HasFiniteSupport fun x : X =>
      (a : AlgebraicCycle X ℚ) x • cyclesOfDimension.pointProj dimX k x :=
    (finite_support_univ (a : AlgebraicCycle X ℚ)).subset
      (Function.support_smul_subset_left (fun x : X => (a : AlgebraicCycle X ℚ) x)
        (cyclesOfDimension.pointProj dimX k))
  rw [← map_finsum (chowSystem dimX k).quotientMap hfin]
  congr 1
  rw [finsum_eq_sum_of_support_subset _
    (s := (finite_support_univ (a : AlgebraicCycle X ℚ)).toFinset)
    (by
      rw [Set.Finite.coe_toFinset]
      exact Function.support_smul_subset_left (fun x : X => (a : AlgebraicCycle X ℚ) x)
        (cyclesOfDimension.pointProj dimX k))]
  exact (cyclesOfDimension.eq_sum_pointProj a).symm

variable (hUE : ∀ q : 𝓔.totalSpace, UnitDifferences (𝓔.totalSpace.presheaf.stalk q))
  (hcovE : HomogeneityLocal.CovByDimension dimE)

include hshift in
/-- **`o^* p^* = id` on Chow groups**, for the class of a pulled-back graded cycle. -/
theorem gysin_pullbackBundle (k : ℤ) (a : cyclesOfDimension X dimX k) :
    gysin (zeroSectionDivisor 𝓔) 𝓔.zeroSection
        (zeroSection_ker_eq_idealSheaf 𝓔) hUE hcovE dimX k
        ((chowSystem dimE (k + 1)).quotientMap
          ⟨pullbackBundle 𝓔 a, pullbackBundle_mem_cyclesOfDimension 𝓔 hshift k a⟩) =
      (chowSystem dimX k).quotientMap a := by
  rw [gysin_quotientMap, gysinCycle_pullbackBundle 𝓔 hshift]

/-- The index identity `k + Nat.card ι = k + 1` for a rank-one bundle. -/
theorem add_natCard_eq_add_one (k : ℤ) : k + (Nat.card ι : ℤ) = k + 1 := by
  rw [Nat.card_unique, Nat.cast_one]

/-- **`o^* ∘ p^* = id` on Chow groups** (Fulton, *Intersection Theory*, Thm. 3.3(a) in rank
one): for every rank-one bundle, the Gysin map of the zero section composed with the flat
pullback `chowPullbackBundleGlobal` is the identity of `A_k(X)`, after identifying the index
`k + Nat.card ι` with `k + 1` by `chowCastDim`. -/
theorem gysin_chowPullbackBundleGlobal (k : ℤ) (α : (chowSystem dimX k).ChowGroup) :
    gysin (zeroSectionDivisor 𝓔) 𝓔.zeroSection
        (zeroSection_ker_eq_idealSheaf 𝓔) hUE hcovE dimX k
        (chowCastDim (dim := dimE) (add_natCard_eq_add_one (ι := ι) k)
          (chowPullbackBundleGlobal 𝓔 dimX dimE hshift k (chowSystem dimX k)
            (chowSystem dimE (k + (Nat.card ι : ℤ))) α)) = α := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  change gysin (zeroSectionDivisor 𝓔) 𝓔.zeroSection
        (zeroSection_ker_eq_idealSheaf 𝓔) hUE hcovE dimX k
      (chowCastDim (dim := dimE) (add_natCard_eq_add_one (ι := ι) k)
        (chowPullbackBundleGlobal 𝓔 dimX dimE hshift k (chowSystem dimX k)
          (chowSystem dimE (k + (Nat.card ι : ℤ))) ((chowSystem dimX k).quotientMap a))) =
    (chowSystem dimX k).quotientMap a
  rw [chowPullbackBundleGlobal_quotientMap, chowCastDim_quotientMap]
  exact gysin_pullbackBundle 𝓔 hshift hUE hcovE k a

include hshift hUE hcovE in
/-- **Injectivity on cycles modulo rational equivalence.**  If the flat pullback of a graded
cycle `a` of dimension `k` is rationally equivalent to zero on `E`, then `a` is rationally
equivalent to zero on `X`: apply `o^*`, which kills the relations of `E` and sends `p^* a` to
`[a]`. -/
theorem mem_totalRationalRelations_of_pullbackBundle (k : ℤ) (a : cyclesOfDimension X dimX k)
    (h : pullbackBundle 𝓔 (a : AlgebraicCycle X ℚ) ∈
      totalRationalRelations 𝓔.totalSpace dimE) :
    (a : AlgebraicCycle X ℚ) ∈ totalRationalRelations X dimX := by
  have hrel : (⟨pullbackBundle 𝓔 a, pullbackBundle_mem_cyclesOfDimension 𝓔 hshift k a⟩ :
      cyclesOfDimension 𝓔.totalSpace dimE (k + 1)) ∈ (chowSystem dimE (k + 1)).relations := h
  have h0 := gysinCycle_relations_le_ker (zeroSectionDivisor 𝓔) 𝓔.zeroSection
        (zeroSection_ker_eq_idealSheaf 𝓔) dimE dimX k
    hUE hcovE hrel
  rw [LinearMap.mem_ker, gysinCycle_pullbackBundle 𝓔 hshift k a] at h0
  have h1 : a ∈ (chowSystem dimX k).relations := (Submodule.Quotient.mk_eq_zero _).1 h0
  exact h1

include hUE hcovE in
/-- **Injectivity of the flat pullback along every rank-one bundle** (Fulton, *Intersection
Theory*, Thm. 3.3(a) in rank one): for a rank-one `BundleData 𝓔` over a locally Noetherian
scheme `X` with Noetherian underlying space, with Noetherian total space, unit differences in
the stalks of the total space (`hUE`) and a dimension function with `CovByDimension` (`hcovE`),
the flat pullback `chowPullbackBundleGlobal : A_i(X) →ₗ[ℚ] A_{i+1}(E)` is injective.  No global
trivialisation is needed. -/
theorem chowPullbackBundleGlobal_injective_rankOne (i : ℤ)
    (RX : RationalEquivalenceSystem X dimX i)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ))) :
    Function.Injective (chowPullbackBundleGlobal 𝓔 dimX dimE hshift i RX RE) := by
  intro α β hαβ
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ β
  change chowPullbackBundleGlobal 𝓔 dimX dimE hshift i RX RE (RX.quotientMap a) =
    chowPullbackBundleGlobal 𝓔 dimX dimE hshift i RX RE (RX.quotientMap b) at hαβ
  change RX.quotientMap a = RX.quotientMap b
  rw [chowPullbackBundleGlobal_quotientMap, chowPullbackBundleGlobal_quotientMap, ← sub_eq_zero,
    ← map_sub, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hαβ
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  cases RX
  cases RE
  exact mem_totalRationalRelations_of_pullbackBundle 𝓔 hshift hUE hcovE i (a - b) hαβ

end Gysin

/-! ## Compact schemes locally of finite type over an infinite field -/

section FiniteType

open FiniteTypeDimension VirtualClass.GlobalVirtualClass
open GromovWitten.AlgebraicGeometry.VirtualFundamentalClass
open GromovWitten.AlgebraicGeometry.NormalSheafPicard.AffineIntrinsicNormalSheaf

variable {F : Type u} [Field F] [Infinite F] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] [CompactSpace X] {ι : Type u}
  [Unique ι] (𝓔 : BundleData X ι) (i : ℤ)
  (RX : RationalEquivalenceSystem X (dimensionFunction f) i)
  (RE : RationalEquivalenceSystem 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))
    (i + (Nat.card ι : ℤ)))

/-- **Injectivity of the flat pullback along a rank-one bundle over a compact scheme locally of
finite type over an infinite field**, at the canonical dimension functions: all hypotheses of
`chowPullbackBundleGlobal_injective_rankOne` are discharged (`X` is locally Noetherian by
`LocallyOfFiniteType.isLocallyNoetherian`, `X` and `E` have Noetherian underlying spaces since
they are compact, the stalks of `E` have unit differences since `F` is infinite, and
`CovByDimension` holds for `dimensionFunction (𝓔.proj ≫ f)`). -/
theorem chowPullbackBundleGlobal_injective_finiteType :
    Function.Injective (chowPullbackBundleGlobal 𝓔 (dimensionFunction f)
      (dimensionFunction (𝓔.proj ≫ f)) (dimensionFunction_bundlePoint f 𝓔) i RX RE) :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  chowPullbackBundleGlobal_injective_rankOne 𝓔 (dimensionFunction_bundlePoint f 𝓔)
    (unitDifferences_stalk_of_infinite (𝓔.proj ≫ f))
    (covByDimension_finiteTypeDimension (𝓔.proj ≫ f)) i RX RE

variable {k : Type u} [CommRing k] {𝓔} {R : 𝓔.J → Type u} [∀ j, CommRing (R j)]
  [∀ j, Algebra k (R j)] {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
  {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
  (𝒞 : VirtualClass.GlobalCone.GlobalConeData 𝓔 φ) [IsLocallyNoetherian 𝒞.coneScheme]

/-- **The injectivity hypothesis `hinj` of `virtualClassFT'_unique` holds for every rank-one
obstruction bundle** over a compact scheme locally of finite type over an infinite field. -/
theorem bundlePullbackFT_injective_rankOne :
    Function.Injective (bundlePullbackFT f i RX RE) :=
  chowPullbackBundleGlobal_injective_finiteType f 𝓔 i RX RE

/-- **Uniqueness of the virtual class for a rank-one obstruction bundle**: over an infinite field,
for `X` compact and locally of finite type, every class `α ∈ A_i(X)` with `p^* α = [C(E)]` is
`virtualClassFT'`.  The remaining hypotheses are the instances `[Infinite F]`,
`[LocallyOfFiniteType f]`, `[CompactSpace X]`, `[Unique ι]` and
`[IsLocallyNoetherian 𝒞.coneScheme]`. -/
theorem virtualClassFT'_unique_rankOne (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    α = virtualClassFT' f 𝒞 i RX RE :=
  virtualClassFT'_unique f 𝒞 i RX RE (bundlePullbackFT_injective_rankOne f i RX RE) α hα

/-- The symmetric form of `virtualClassFT'_unique_rankOne`. -/
theorem eq_virtualClassFT'_of_pullback_eq_rankOne (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    virtualClassFT' f 𝒞 i RX RE = α :=
  (virtualClassFT'_unique_rankOne f i RX RE 𝒞 α hα).symm

/-- **Existence and uniqueness of the virtual fundamental class for a rank-one obstruction
bundle** over a compact scheme locally of finite type over an infinite field: there is exactly
one class `α ∈ A_i(X)` with `p^* α = [C(E)]`.  Both halves of the homotopy property of Chow
groups are theorems here; no global trivialisation of the bundle is assumed.  The remaining
hypotheses are the instances `[Infinite F]`, `[LocallyOfFiniteType f]`, `[CompactSpace X]`,
`[Unique ι]` and `[IsLocallyNoetherian 𝒞.coneScheme]`. -/
theorem existsUnique_virtualClassFT'_rankOne :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE :=
  existsUnique_virtualClassFT' f 𝒞 i RX RE (bundlePullbackFT_injective_rankOne f i RX RE)

end FiniteType

end RankOneBundleInjective

end GromovWitten.AlgebraicGeometry.IntersectionTheory
