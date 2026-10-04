/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.FirstChernClassGeneral
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperPushforwardDivisor
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Proper pushforward on Chow groups: plumbing, dimension drop, and finite morphisms

This file assembles `cyclesOfDimension.properPushforward` (`ChowGroup.lean`) into a linear map
on rational Chow groups, under the hypothesis that it carries principal-divisor generators of
the relevant degree into the target's relations (`properPushforwardChow`).  It proves this
hypothesis automatically in the dimension-drop case (`properPushforward_divisor_eq_zero_of_dim_le`,
Stacks 42.20.3 case (iii)) and for finite morphisms (`dim_eq_of_isFinite`, feeding the
equidimensional case proved elsewhere), giving the finite-morphism pushforward
`finitePushforwardChow`.

Throughout, `X` and `Y` are schemes locally of finite type over a fixed field `k`, via structure
morphisms `sX : X ⟶ Spec k` and `sY : Y ⟶ Spec k`, and `dimX`, `dimY` are *arbitrary* certified
dimension functions: over a field every `DimensionFunction` is forced to agree with the canonical
transcendence-degree one (`FiniteTypeDimension.dimensionFunction`,
`FiniteTypeDimension.height_eq_resTrdeg`), which is recorded here as
`dimensionFunction_eq_of_locallyOfFiniteType` and used to transport the
`HomogeneityLocal.CovByDimension` hypothesis needed for homogeneity of principal divisors
(`covByDimension_of_locallyOfFiniteType`).  No compatibility hypothesis between `sX`, `sY` and `f`
is needed anywhere in this file (matching `ProperPushforwardDivisor`'s own finding that it is
unnecessary): dimension functions are intrinsic, and the dimension-preservation theorem for finite
morphisms (`dim_eq_of_isFinite`) is proved directly from Cohen–Seidenberg incomparability, not
from a residue-field or transcendence-degree computation.

## Main results

* `dimensionFunction_eq_of_locallyOfFiniteType`, `covByDimension_of_locallyOfFiniteType`: over a
  field, every certified dimension function agrees pointwise with the canonical one, hence
  satisfies `HomogeneityLocal.CovByDimension`.
* `properPushforward_divisor_eq_zero_of_dim_le` (Stacks 42.20.3, case (iii)): a proper pushforward
  kills the divisor of a generator whose image drops dimension by at least two.
* `properPushforwardDescending`, `properPushforwardChow`, `properPushforwardChow_quotientMap`:
  given a proof that the pushforward of every relevant generator's divisor lands in the target's
  relations, the dimension-graded proper pushforward descends to a linear map on Chow groups.
* `properPushforwardChow_hrel_comp`, `properPushforwardChow_comp`: functoriality.
* `properPushforwardChow_eq_closedImmersionPushforward`: agreement with
  `RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward` for closed immersions.
* `dim_eq_of_isFinite`: a finite morphism (over `k`) preserves the dimension of every point.
* `finitePushforwardChow`, `finitePushforwardChow_quotientMap`: the induced Chow-group pushforward
  for a finite morphism, built from `properPushforwardChow` using `dim_eq_of_isFinite` and
  `ProperPushforwardDivisor.properPushforward_divisor_mem_relations_of_dim_eq`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

attribute [local instance] specializationOrder

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## Dimension functions over a field are unique -/

section Setting

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- Over a field, every certified dimension function of a scheme locally of finite type agrees
pointwise with the canonical transcendence-degree dimension function: both are determined by the
order-theoretic height, which is a shared, uncontested invariant of the point. -/
theorem dimensionFunction_eq_of_locallyOfFiniteType
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX] (dimX : DimensionFunction X)
    (x : X) : dimX x = FiniteTypeDimension.dimensionFunction sX x := by
  have hcast : (Int.toNat (dimX x) : ℕ∞) =
      (Int.toNat (FiniteTypeDimension.dimensionFunction sX x) : ℕ∞) := by
    rw [← dimX.height_eq, ← (FiniteTypeDimension.dimensionFunction sX).height_eq]
  have hnat : Int.toNat (dimX x) = Int.toNat (FiniteTypeDimension.dimensionFunction sX x) :=
    ENat.natCast_inj.mp hcast
  rw [← Int.toNat_of_nonneg (dimX.nonnegative x),
    ← Int.toNat_of_nonneg ((FiniteTypeDimension.dimensionFunction sX).nonnegative x)]
  exact congrArg Int.ofNat hnat

/-- Over a field, every certified dimension function of a scheme locally of finite type satisfies
`HomogeneityLocal.CovByDimension`: this is forced from the canonical one
(`FirstChernClassGeneral.covByDimension_finiteTypeDimension`) by
`dimensionFunction_eq_of_locallyOfFiniteType`. -/
theorem covByDimension_of_locallyOfFiniteType
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX] (dimX : DimensionFunction X) :
    HomogeneityLocal.CovByDimension dimX := by
  intro x η hxη
  rw [dimensionFunction_eq_of_locallyOfFiniteType sX dimX x,
    dimensionFunction_eq_of_locallyOfFiniteType sX dimX η]
  exact covByDimension_finiteTypeDimension sX x η hxη

end Setting

/-! ## Monotonicity of a certified dimension function along specialisation -/

/-- A certified dimension function cannot increase along a specialisation: if `a ⤳ b` then
`dimZ b ≤ dimZ a`.  This is the order-theoretic monotonicity of `Order.height`, transported
through `DimensionFunction.height_eq`; no properness is needed. -/
theorem dimension_le_of_specializes {Z : Scheme.{u}} (dimZ : DimensionFunction Z)
    {a b : Z} (hab : a ⤳ b) : dimZ b ≤ dimZ a := by
  have hle : b ≤ a := hab
  have hh : Order.height b ≤ Order.height a := Order.height_mono hle
  rw [dimZ.height_eq, dimZ.height_eq] at hh
  have hnat : Int.toNat (dimZ b) ≤ Int.toNat (dimZ a) := by exact_mod_cast hh
  calc dimZ b = (Int.toNat (dimZ b) : ℤ) := (Int.toNat_of_nonneg (dimZ.nonnegative b)).symm
    _ ≤ (Int.toNat (dimZ a) : ℤ) := by exact_mod_cast hnat
    _ = dimZ a := Int.toNat_of_nonneg (dimZ.nonnegative a)

/-! ## Case (iii): the dimension-drop case -/

section DimLe

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  {dimX : DimensionFunction X} {dimY : DimensionFunction Y}
  (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsProper f]

/-- **Stacks 42.20.3, case (iii).** If `f` is proper and `g` is a principal-divisor generator of
`X` whose image drops the dimension by at least two (`w := g.subspace.genericPointImage`), the
pushforward of `g`'s divisor vanishes outright: the divisor is supported exactly in dimension
`dimX w - 1` (homogeneity of principal divisors, via `covByDimension_of_locallyOfFiniteType`),
every such point specialises from `w`, and the image of a specialisation of `w` cannot exceed
`dimY (f.base w)` in dimension — too small to match the source dimension. -/
theorem properPushforward_divisor_eq_zero_of_dim_le
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX]
    (g : RationalFunctionGenerator X)
    (hle : dimY (f.base g.subspace.genericPointImage) ≤
      dimX g.subspace.genericPointImage - 2) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY (g.divisor dimX) = 0 := by
  classical
  have hcovX : HomogeneityLocal.CovByDimension dimX := covByDimension_of_locallyOfFiniteType sX dimX
  set w := g.subspace.genericPointImage with hw
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  change (∑ᶠ x ∈ f.base ⁻¹' {y}, (g.divisor dimX) x *
      (_root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff f dimX dimY x : ℚ)) = (0 : ℚ)
  apply finsum_mem_of_eqOn_zero
  intro x _
  by_cases hcx : g.divisor dimX x = 0
  · simp [hcx]
  have hdx : dimX x = dimX w - 1 := by
    by_contra hne
    exact hcx (RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX hcovX g
      (show dimX w = (dimX w - 1) + 1 by ring) x hne)
  have hmem : x ∈ Set.range g.subspace.inclusion.base := by
    by_contra hmem
    exact hcx (AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range
      g.subspace.inclusion (dimX : X → ℤ) _ x hmem)
  obtain ⟨z, rfl⟩ := hmem
  have hwx : w ⤳ g.subspace.inclusion.base z := g.subspace.genericPointImage_specializes z
  have hfwx : f.base w ⤳ f.base (g.subspace.inclusion.base z) :=
    f.base.hom.map_specializes hwx
  have hspecY : dimY (f.base (g.subspace.inclusion.base z)) ≤ dimY (f.base w) :=
    dimension_le_of_specializes dimY hfwx
  have hlt : dimY (f.base (g.subspace.inclusion.base z)) < dimX (g.subspace.inclusion.base z) := by
    omega
  have hne : dimX (g.subspace.inclusion.base z) ≠ dimY (f.base (g.subspace.inclusion.base z)) := by
    omega
  simp [_root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff, hne]

end DimLe

/-! ## Descending the proper pushforward to Chow groups -/

section Descending

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  {dimX : DimensionFunction X} {dimY : DimensionFunction Y}
  (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsProper f] (i : ℤ)

/-- The hypothesis needed to descend `cyclesOfDimension.properPushforward f` to a `DescendingMap`
in degree `i`: every principal-divisor generator of `X` whose own dimension is `i + 1` is pushed
to a cycle lying in the target's canonical relations. -/
def ProperPushforwardHRel (dimX : DimensionFunction X) (dimY : DimensionFunction Y)
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX] : Prop :=
  ∀ (g : RationalFunctionGenerator X) (hg : dimX g.subspace.genericPointImage = i + 1),
    (cyclesOfDimension.properPushforward (dimensionY := dimY) (i := i) f
        ⟨g.divisor dimX, RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX
          (covByDimension_of_locallyOfFiniteType sX dimX) g hg⟩ :
        cyclesOfDimension Y dimY i) ∈
      (RationalEquivalenceSystem.canonical (X := Y) (dimension := dimY) (i := i)).relations

variable (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX]

/-- **The `DescendingMap` for proper pushforward in a fixed degree.**  Given
`ProperPushforwardHRel`, the dimension-graded proper pushforward along `f` preserves the
canonical rational-equivalence relations in degree `i`.  The proof expands an arbitrary relation
as a finite sum of generator divisors (`Submodule.mem_span_set'`) and treats the generators of
degree `i + 1` with the hypothesis, the others by homogeneity
(`cyclesOfDimension.project_eq_zero_of_mem_ne`), exactly mirroring
`FirstChernClass.c1Cycle_relations_le_ker`. -/
noncomputable def properPushforwardDescending (hrel : ProperPushforwardHRel
      (dimX := dimX) (dimY := dimY) (f := f) (i := i) (sX := sX)) :
    (RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := i)).DescendingMap
      (RationalEquivalenceSystem.canonical (X := Y) (dimension := dimY) (i := i)) where
  onCycles := cyclesOfDimension.properPushforward f
  maps_relations := by
    intro z hz
    change cyclesOfDimension.properPushforward f z ∈
      (RationalEquivalenceSystem.canonical (X := Y) (dimension := dimY) (i := i)).relations
    have hz' : (z : AlgebraicCycle X ℚ) ∈ totalRationalRelations X dimX := hz
    rw [totalRationalRelations, Submodule.mem_span_set'] at hz'
    obtain ⟨n, cf, gg, hsum⟩ := hz'
    choose G hG using fun k ↦ (gg k).2
    have hzproj : z = cyclesOfDimension.projectLinear dimX i (z : AlgebraicCycle X ℚ) :=
      (cyclesOfDimension.project_coe z).symm
    have hsum' : (z : AlgebraicCycle X ℚ) = ∑ k : Fin n, cf k • (G k).divisor dimX := by
      rw [← hsum]
      exact Finset.sum_congr rfl (fun k _ ↦ by rw [← hG k])
    have hz_eq : z = ∑ k : Fin n,
        cf k • cyclesOfDimension.projectLinear dimX i ((G k).divisor dimX) := by
      rw [hzproj, hsum', map_sum]
      exact Finset.sum_congr rfl (fun k _ ↦ LinearMap.map_smul _ _ _)
    rw [hz_eq, map_sum]
    apply Submodule.sum_mem
    intro k _
    rw [LinearMap.map_smul]
    by_cases hk : dimX (G k).subspace.genericPointImage = i + 1
    · have hmem := RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX
        (covByDimension_of_locallyOfFiniteType sX dimX) (G k) hk
      have hproj : cyclesOfDimension.projectLinear dimX i ((G k).divisor dimX) =
          ⟨(G k).divisor dimX, hmem⟩ :=
        cyclesOfDimension.project_coe ⟨(G k).divisor dimX, hmem⟩
      rw [hproj]
      exact Submodule.smul_mem _ _ (hrel (G k) hk)
    · have hmem : (G k).divisor dimX ∈
          cyclesOfDimension X dimX (dimX (G k).subspace.genericPointImage - 1) :=
        RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX
          (covByDimension_of_locallyOfFiniteType sX dimX) (G k) (by ring)
      have hproj : cyclesOfDimension.projectLinear dimX i ((G k).divisor dimX) = 0 :=
        cyclesOfDimension.project_eq_zero_of_mem_ne hmem (by omega)
      rw [hproj, map_zero, smul_zero]
      exact Submodule.zero_mem _

/-- **Proper pushforward on rational Chow groups, in a fixed degree.** -/
noncomputable def properPushforwardChow (hrel : ProperPushforwardHRel
      (dimX := dimX) (dimY := dimY) (f := f) (i := i) (sX := sX)) :
    (RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := i)).ChowGroup →ₗ[ℚ]
      (RationalEquivalenceSystem.canonical (X := Y) (dimension := dimY) (i := i)).ChowGroup :=
  RationalEquivalenceSystem.DescendingMap.inducedMap
    (RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := i))
    (properPushforwardDescending f i sX hrel)

/-- `properPushforwardChow` is induced by the actual residue-degree pushforward on dimension-
graded cycles. -/
@[simp]
theorem properPushforwardChow_quotientMap (hrel : ProperPushforwardHRel
      (dimX := dimX) (dimY := dimY) (f := f) (i := i) (sX := sX))
    (z : cyclesOfDimension X dimX i) :
    properPushforwardChow f i sX hrel
        ((RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := i)).quotientMap
          z) =
      (RationalEquivalenceSystem.canonical (X := Y) (dimension := dimY) (i := i)).quotientMap
        (cyclesOfDimension.properPushforward f z) :=
  rfl

/-- **Compatibility with closed-immersion pushforward.**  When `f` is additionally a closed
immersion, `properPushforwardChow` agrees with
`RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward`, for any valid `hrel`: both
are induced by the same cycle-level map `cyclesOfDimension.properPushforward f`. -/
theorem properPushforwardChow_eq_closedImmersionPushforward
    [_root_.AlgebraicGeometry.IsClosedImmersion f] (hrel : ProperPushforwardHRel
      (dimX := dimX) (dimY := dimY) (f := f) (i := i) (sX := sX)) :
    properPushforwardChow f i sX hrel =
      RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward
        (RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := i)) f
        (RationalEquivalenceSystem.canonical (X := Y) (dimension := dimY) (i := i)) := by
  apply LinearMap.ext
  rintro ⟨z⟩
  rfl

end Descending

/-! ## Functoriality -/

section Comp

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  {dimX : DimensionFunction X} {dimY : DimensionFunction Y} {dimZ : DimensionFunction Z}
  (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsProper f]
  (g : Y ⟶ Z) [_root_.AlgebraicGeometry.IsProper g] (i : ℤ)
  (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX]
  (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY]

/-- The composite `ProperPushforwardHRel` for `f ≫ g`, derived from the hypotheses for `f` and
for `g` separately: a generator of `X` of degree `i + 1` is pushed by `f`'s hypothesis into `Y`'s
relations in degree `i`, and `g`'s `DescendingMap` then carries that into `Z`'s relations. -/
theorem properPushforwardChow_hrel_comp
    (hrelf : ProperPushforwardHRel (dimX := dimX) (dimY := dimY) (f := f) (i := i) (sX := sX))
    (hrelg : ProperPushforwardHRel (dimX := dimY) (dimY := dimZ) (f := g) (i := i) (sX := sY)) :
    ProperPushforwardHRel (dimX := dimX) (dimY := dimZ) (f := f ≫ g) (i := i) (sX := sX) := by
  intro h hg
  have hpt := LinearMap.congr_fun
    (cyclesOfDimension.properPushforward_comp (dimensionY := dimY) (dimensionZ := dimZ) f g)
    ⟨h.divisor dimX, RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX
      (covByDimension_of_locallyOfFiniteType sX dimX) h hg⟩
  rw [hpt]
  exact (properPushforwardDescending g i sY hrelg).maps_relations (hrelf h hg)

/-- **Functoriality of `properPushforwardChow`.** -/
theorem properPushforwardChow_comp
    (hrelf : ProperPushforwardHRel (dimX := dimX) (dimY := dimY) (f := f) (i := i) (sX := sX))
    (hrelg : ProperPushforwardHRel (dimX := dimY) (dimY := dimZ) (f := g) (i := i) (sX := sY)) :
    properPushforwardChow (f ≫ g) i sX (properPushforwardChow_hrel_comp f g i sX sY hrelf hrelg) =
      (properPushforwardChow g i sY hrelg).comp (properPushforwardChow f i sX hrelf) := by
  apply LinearMap.ext
  rintro ⟨z⟩
  change (RationalEquivalenceSystem.canonical (X := Z) (dimension := dimZ) (i := i)).quotientMap
      (cyclesOfDimension.properPushforward (f ≫ g) z) =
    (RationalEquivalenceSystem.canonical (X := Z) (dimension := dimZ) (i := i)).quotientMap
      (cyclesOfDimension.properPushforward g (cyclesOfDimension.properPushforward f z))
  rw [cyclesOfDimension.properPushforward_comp]
  rfl

end Comp

/-! ## Finite morphisms preserve the dimension of every point -/

section FiniteMorphism

/-- **The affine case.**  For an integral ring homomorphism `φ`, the induced map
`Spec.map φ` cannot increase the height of a point: an integral extension has no comparable
pair of distinct primes with the same contraction (Cohen–Seidenberg incomparability,
`Ideal.IsIntegral.comap_lt_comap`), so `PrimeSpectrum.comap φ.hom` is strictly monotone for the
specialisation order, and strictly monotone maps cannot decrease height. -/
theorem height_le_height_apply_of_isFinite_affine {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : φ.hom.IsIntegral) (x : (Spec B : Scheme.{u})) :
    Order.height x ≤ Order.height ((Spec.map φ).base x) := by
  let _ : Algebra A B := φ.hom.toAlgebra
  have hint : Algebra.IsIntegral A B := ⟨hφ⟩
  apply Order.height_le_height_apply_of_strictMono (Spec.map φ).base
  intro a b hab
  rw [lt_iff_le_not_ge, HomogeneityLocal.specLE_iff, HomogeneityLocal.specLE_iff,
    ← lt_iff_le_not_ge] at hab
  have hcomap : ((b : PrimeSpectrum B).asIdeal.comap φ.hom) <
      ((a : PrimeSpectrum B).asIdeal.comap φ.hom) :=
    Ideal.IsIntegral.comap_lt_comap (R := A) (A := B) hab
  have hcomap2 : (PrimeSpectrum.comap φ.hom (b : PrimeSpectrum B)).asIdeal <
      (PrimeSpectrum.comap φ.hom (a : PrimeSpectrum B)).asIdeal := hcomap
  have hcomap' : (PrimeSpectrum.comap φ.hom (b : PrimeSpectrum B) : PrimeSpectrum A) <
      PrimeSpectrum.comap φ.hom (a : PrimeSpectrum B) :=
    (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp hcomap2
  change (Spec.map φ).base a < (Spec.map φ).base b
  rw [lt_iff_le_not_ge, HomogeneityLocal.specLE_iff, HomogeneityLocal.specLE_iff,
    ← lt_iff_le_not_ge]
  simpa [Spec.map_apply] using hcomap'

/-- **The general case.**  Every strict specialisation chain ending at `x` is confined to any
affine open neighbourhood of `x` (`specializes_iff_forall_open`), so the height of `x` can be
computed inside an affine open `W` with `f ⁻¹ᵁ V = W` for an affine open `V ∋ f.base x` of `Y`;
there the affine case above, transported along the two `isoSpec` identifications and the
commuting square `W.toSpecΓ ≫ Spec.map (f.appLE V W _) = f.resLE V W _ ≫ V.toSpecΓ`, gives the
height inequality. -/
theorem height_le_height_apply_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsFinite f] (x : X) :
    Order.height x ≤ Order.height (f.base x) := by
  apply Order.height_le
  intro s hs
  obtain ⟨V, hV, hfxV, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (X := Y) (x := f.base s.head) (U := ⊤) trivial
  set W : X.Opens := f ⁻¹ᵁ V with hWdef
  have hW : IsAffineOpen W := hV.preimage f
  have hmem : ∀ i, s i ∈ W := fun i ↦ by
    change f.base (s i) ∈ V
    exact (f.base.hom.map_specializes
      (HomogeneityLocal.le_iff_specializes.1 (s.head_le i))).mem_open V.2 hfxV
  let s' : LTSeries W.toScheme :=
    { length := s.length
      toFun := fun i ↦ ⟨s i, hmem i⟩
      step := fun i ↦ HomogeneityLocal.lt_of_map_lt W.ι
        W.ι.isOpenEmbedding.isInducing (s.step i) }
  have hlast : W.ι.base s'.last = s.last := rfl
  have hWV : W ≤ f ⁻¹ᵁ V := le_refl _
  have hfin : (f.appLE V W hWV).hom.Finite := by
    rw [f.appLE_eq_app]
    exact f.finite_app V hV
  have hφ : (f.appLE V W hWV).hom.IsIntegral :=
    (RingHom.finite_iff_isIntegral_and_finiteType.mp hfin).1
  have hheight := height_le_height_apply_of_isFinite_affine
    (f.appLE V W hWV) hφ (hW.isoSpec.hom.base s'.last)
  have heq1 : Order.height (hW.isoSpec.hom.base s'.last) = Order.height s'.last :=
    FiniteTypeDimension.height_iso hW.isoSpec s'.last
  have hsquare := AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE f V W hWV
  have hsquare_pt : (Spec.map (f.appLE V W hWV)).base (W.toSpecΓ.base s'.last) =
      V.toSpecΓ.base ((f.resLE V W hWV).base s'.last) :=
    congrArg (fun g : W.toScheme ⟶ Spec Γ(Y, V) ↦ g.base s'.last) hsquare
  have hVstep : Order.height (V.toSpecΓ.base ((f.resLE V W hWV).base s'.last)) =
      Order.height ((f.resLE V W hWV).base s'.last) := by
    rw [← hV.isoSpec_hom]
    exact FiniteTypeDimension.height_iso hV.isoSpec _
  have hopen : Order.height ((f.resLE V W hWV).base s'.last) ≤
      Order.height (V.ι.base ((f.resLE V W hWV).base s'.last)) :=
    Order.height_le_height_apply_of_strictMono V.ι.base
      (FiniteTypeDimension.strictMono_base V.ι) _
  have hcomp : V.ι.base ((f.resLE V W hWV).base s'.last) = f.base (W.ι.base s'.last) :=
    congrArg (fun g : W.toScheme ⟶ Y ↦ g.base s'.last)
      (AlgebraicGeometry.Scheme.Hom.resLE_comp_ι f hWV)
  calc (s.length : ℕ∞) = (s'.length : ℕ∞) := rfl
    _ ≤ Order.height s'.last := Order.length_le_height_last
    _ = Order.height (hW.isoSpec.hom.base s'.last) := heq1.symm
    _ = Order.height (W.toSpecΓ.base s'.last) := by rw [hW.isoSpec_hom]
    _ ≤ Order.height ((Spec.map (f.appLE V W hWV)).base (W.toSpecΓ.base s'.last)) := by
        rw [hW.isoSpec_hom] at hheight; exact hheight
    _ = Order.height (V.toSpecΓ.base ((f.resLE V W hWV).base s'.last)) := by
        rw [hsquare_pt]
    _ = Order.height ((f.resLE V W hWV).base s'.last) := hVstep
    _ ≤ Order.height (V.ι.base ((f.resLE V W hWV).base s'.last)) := hopen
    _ = Order.height (f.base (W.ι.base s'.last)) := by rw [hcomp]
    _ = Order.height (f.base s.last) := by rw [hlast]
    _ = Order.height (f.base x) := by rw [hs]

/-- **A finite morphism preserves the dimension of every point.**  Combined with
`DimensionFunction.apply_le_of_isProper` (which gives the reverse inequality from properness
alone), the height inequality above gives equality. -/
theorem dim_eq_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsFinite f]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (x : X) :
    dimY (f.base x) = dimX x := by
  have h1 : dimY (f.base x) ≤ dimX x := dimX.apply_le_of_isProper dimY f x
  have h2 : Order.height x ≤ Order.height (f.base x) := height_le_height_apply_of_isFinite f x
  rw [dimX.height_eq, dimY.height_eq] at h2
  have h2' : Int.toNat (dimX x) ≤ Int.toNat (dimY (f.base x)) := by exact_mod_cast h2
  have hnx := dimX.nonnegative x
  have hny := dimY.nonnegative (f.base x)
  omega

end FiniteMorphism

/-! ## The finite-morphism Chow pushforward -/

section FinitePushforwardChow

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- **For a finite morphism, every generator satisfies case (i).**  `dim_eq_of_isFinite` shows
every point keeps its dimension, so
`ProperPushforwardDivisor.properPushforward_divisor_mem_relations_of_dim_eq` (the equidimensional
theorem, P2) applies to every generator. -/
theorem properPushforwardHRel_of_isFinite (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsFinite f]
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (i : ℤ) :
    ProperPushforwardHRel (dimX := dimX) (dimY := dimY) (f := f) (i := i) (sX := sX) := by
  intro g hg
  have hmem := RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX
    (covByDimension_of_locallyOfFiniteType sX dimX) g hg
  refine ProperPushforwardDivisor.properPushforward_divisor_mem_relations_of_dim_eq
    sX sY f dimX dimY g ?_ hmem
  exact dim_eq_of_isFinite f dimX dimY g.subspace.genericPointImage

/-- **The proper pushforward along a finite morphism, on rational Chow groups.** -/
noncomputable def finitePushforwardChow (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsFinite f]
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (i : ℤ) :
    (RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := i)).ChowGroup →ₗ[ℚ]
      (RationalEquivalenceSystem.canonical (X := Y) (dimension := dimY) (i := i)).ChowGroup :=
  properPushforwardChow f i sX
    (properPushforwardHRel_of_isFinite f sX sY dimX dimY i)

/-- `finitePushforwardChow` is induced by the actual residue-degree pushforward on dimension-
graded cycles. -/
@[simp]
theorem finitePushforwardChow_quotientMap (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsFinite f]
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (i : ℤ)
    (z : cyclesOfDimension X dimX i) :
    finitePushforwardChow f sX sY dimX dimY i
        ((RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := i)).quotientMap
          z) =
      (RationalEquivalenceSystem.canonical (X := Y) (dimension := dimY) (i := i)).quotientMap
        (cyclesOfDimension.properPushforward f z) :=
  properPushforwardChow_quotientMap f i sX _ z

end FinitePushforwardChow

end GromovWitten.AlgebraicGeometry.IntersectionTheory
