/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ConeGluingIndependence

/-!
# Resolution independence under a rank-preserving quasi-isomorphism, for a fixed bundle

This file proves the quasi-isomorphism analogue of resolution independence for the global
virtual class attached to a fixed obstruction bundle `𝓔`: chart-wise quasi-isomorphisms
`f j : E j ⟶ E' j` which are already bijective in degree one give the same glued cone class and
(for a globally trivialised `𝓔`) the same finite-type virtual class. It builds directly on the
isomorphism-level comparison of
`GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ConeGluingIndependence`
(`ChartIso`, `coneClassAt_eq`, `virtualClassFT'_eq`), which is imported rather than reproduced.

## The key new algebraic fact

A quasi-isomorphism `f : Hom E F` of two-term complexes is, by definition, a chain map inducing
bijections on `H⁻¹ = ker(differential)` and `H⁰ = coker(differential)`; this does *not* force
`f` to be bijective in either raw degree unless the ranks of `E` and `F` already agree (the
general comparison, in `QuasiIsoInvariance.lean`, goes through padding both sides with acyclic
summands to equalise the ranks, which changes the ambient bundle and so cannot be used to
compare cone data for one and the same `𝓔`). However, if `f` happens to already be bijective in
degree one, a direct diagram chase
(`bijective_degreeZero_of_isQuasiIsomorphism_of_bijective_degreeOne` below) shows `f` is
automatically bijective in degree zero too, i.e. an isomorphism of two-term complexes in the
sense of `ConeGluingIndependence.ChartIso`. This is exactly option (a) of the round's task: the
chart quasi-isomorphisms of a `ChartQuasiIso` are, under the `bijective_degreeOne` hypothesis,
isomorphisms after all, so the whole comparison reduces to the isomorphism case.

## Main definitions and results

* `LinearTwoTermComplex.Hom.bijective_degreeZero_of_isQuasiIsomorphism_of_bijective_degreeOne` —
  the algebraic fact above, for an arbitrary chain map of two-term complexes over a commutative
  ring.
* `ChartQuasiIso 𝒞 𝒞'` — chart-wise quasi-isomorphisms `hom j : E j ⟶ E' j` (bijective in degree
  one, `bijective_degreeOne`) compatible with the affine obstruction data (`comp_degreeZero`) and
  with the bundle-chart embeddings (`bundleChart_comm`), stated exactly like
  `ConeGluingIndependence.ChartIso` but with the bijectivity of `hom j` in degree zero replaced by
  the pair (`isQuasiIso`, `bijective_degreeOne`) from which it is derived.
* `ChartQuasiIso.toChartIso` — the induced `ConeGluingIndependence.ChartIso 𝒞 𝒞'`.
* `coneClassAt_eq_of_quasiIso`, `virtualClassFT'_eq_of_quasiIso` — the quasi-isomorphism
  analogues of `ConeGluingIndependence.coneClassAt_eq`, `.virtualClassFT'_eq`, obtained by
  passing to `ChartQuasiIso.toChartIso`.

## What is not proved here

The general case of a chart-wise quasi-isomorphism which is *not* assumed bijective in degree
one is genuinely different: the ranks of `E j` and `E' j` may differ (only their alternating sum,
the virtual rank, is preserved, by `QuasiIsoInvariance.lean`'s `finrank_add_finrank_of_quasiIso`),
so there is in general no common ambient bundle `𝓔` for the two resolutions, and the comparison
of §5.3-style classes has to go through padding by acyclic summands on a *different*, larger
bundle (a direct-sum construction on `BundleData` that is not available in this file, per the
round survey already recorded in `ConeGluingIndependence.lean`'s module docstring). Proving that
finer statement is out of scope here.
-/

universe u

-- As in `ConeGluingIndependence.lean`: the coordinate ring of the affine product `C ×_X E₀` is a
-- tensor product whose left factor is a quotient of a Rees algebra, needing one more level of
-- pending instance problems than the default.
set_option maxSynthPendingDepth 5

-- As in `ConeGluingIndependence.lean`: the index type of Mathlib's directed affine cover is
-- definitionally, but not reducibly, the type of affine opens.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

open IntersectionTheory hiding Scheme AlgebraicCycle
open VectorBundleTotalSpace RelativeSpec
open NormalSheafPicard.AffineIntrinsicNormalSheaf
open VirtualFundamentalClass
open VirtualClass.GlobalCone
open VirtualClass.ConeGluingIndependence

noncomputable section

/-! ## The algebraic fact: a quasi-isomorphism bijective in degree one is an isomorphism -/

namespace LinearTwoTermComplex.Hom

variable {S : Type u} [CommRing S] {A B : LinearTwoTermComplex S}

/-- **A quasi-isomorphism of two-term complexes that is already bijective in degree one is
bijective in degree zero too.**

Injectivity: if `f.degreeZero x = f.degreeZero y` then, applying `f.comm` and the hypothesis,
`f.degreeOne (A.differential x) = f.degreeOne (A.differential y)`; since `f.degreeOne` is
injective, `A.differential x = A.differential y`, so `x - y` lies in `ker A.differential` and
`f.kernelMap` sends it to `0`; injectivity of `f.kernelMap` (from the quasi-isomorphism
hypothesis) forces `x = y`.

Surjectivity: given `y : B.degreeZero`, lift `B.differential y` along the bijection
`f.degreeOne` to some `z`; since `B.differential y` trivially lies in the range of
`B.differential`, `f.cokernelMap` sends the class of `z` to `0`; injectivity of `f.cokernelMap`
then gives `z = A.differential w` for some `w`, so `y - f.degreeZero w ∈ ker B.differential`;
surjectivity of `f.kernelMap` lifts this to some `u`, and `f.degreeZero (w + u.1) = y`. -/
theorem bijective_degreeZero_of_isQuasiIsomorphism_of_bijective_degreeOne (f : Hom A B)
    (hf : f.IsQuasiIsomorphism) (h1 : Function.Bijective f.degreeOne) :
    Function.Bijective f.degreeZero := by
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · have hcomm : f.degreeOne (A.differential x) = f.degreeOne (A.differential y) := by
      rw [f.comm x, f.comm y, hxy]
    have hd : A.differential x = A.differential y := h1.1 hcomm
    have hker : x - y ∈ LinearMap.ker A.differential := by
      rw [LinearMap.mem_ker, map_sub, hd, sub_self]
    have hval : (⟨x - y, hker⟩ : LinearMap.ker A.differential) = 0 := by
      refine hf.1.1 ?_
      rw [map_zero]
      apply Subtype.ext
      change f.degreeZero (x - y) = 0
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (congrArg Subtype.val hval)
  · obtain ⟨z, hz⟩ := h1.2 (B.differential y)
    have hzc : f.cokernelMap (Submodule.Quotient.mk z) = 0 := by
      change (Submodule.Quotient.mk (f.degreeOne z) :
        B.degreeOne ⧸ (LinearMap.range B.differential)) = 0
      rw [hz]
      exact (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range.2 ⟨y, rfl⟩)
    have hz0 : (Submodule.Quotient.mk z :
        A.degreeOne ⧸ (LinearMap.range A.differential)) = 0 := by
      refine hf.2.1 ?_
      rw [hzc, map_zero]
    obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).1 hz0
    have hdz : B.differential (f.degreeZero w) = B.differential y := by
      rw [← f.comm, hw, hz]
    have hker2 : y - f.degreeZero w ∈ LinearMap.ker B.differential := by
      rw [LinearMap.mem_ker, map_sub, hdz, sub_self]
    obtain ⟨u, hu⟩ := hf.1.2 ⟨y - f.degreeZero w, hker2⟩
    have hu2 : f.degreeZero u.1 = y - f.degreeZero w := congrArg Subtype.val hu
    exact ⟨w + u.1, by rw [map_add, hu2]; abel⟩

end LinearTwoTermComplex.Hom

namespace VirtualClass.ConeGluingQuasiIso

open LinearTwoTermComplex.Hom (bijective_degreeZero_of_isQuasiIsomorphism_of_bijective_degreeOne)

/-! ## Chart-wise quasi-isomorphisms of cone data for a fixed bundle -/

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u} {𝓔 : BundleData X ι}
variable {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)] {I : ∀ j, Ideal (R j)}
variable {E E' : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
variable {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
variable {φ' : ∀ j, LinearTwoTermComplex.Hom (E' j) (conormalComplex k (R j) (I j))}
variable {𝒞 : GlobalConeData 𝓔 φ} {𝒞' : GlobalConeData 𝓔 φ'}

/-- **Chart-wise quasi-isomorphism data between two cone data `𝒞`, `𝒞'` for the same bundle
`𝓔`, under the extra hypothesis that the quasi-isomorphism is already bijective in degree
one.**

The data is, at every chart `j`, a chain map `hom j` of the two-term complexes `E j` and `E' j`
which is a quasi-isomorphism (`isQuasiIso`) and bijective in degree one (`bijective_degreeOne`) —
by `LinearTwoTermComplex.Hom.bijective_degreeZero_of_isQuasiIsomorphism_of_bijective_degreeOne`
this forces `hom j` to be bijective in degree zero as well, so `hom j` is in fact an isomorphism
of two-term complexes — compatible with the affine obstruction data `φ j`, `φ' j`
(`comp_degreeZero`, exactly `ConeGluingIndependence.ChartIso`'s hypothesis) and with the two
embeddings of the chart into the total space of `𝓔` (`bundleChart_comm`, stated using the derived
degree-zero bijectivity). No conclusion is carried by this structure. -/
structure ChartQuasiIso (𝒞 : GlobalConeData 𝓔 φ) (𝒞' : GlobalConeData 𝓔 φ') where
  /-- The chart-wise quasi-isomorphism of two-term complexes over `R j ⧸ I j`. -/
  hom : ∀ j, LinearTwoTermComplex.Hom (E j) (E' j)
  /-- `hom j` is a quasi-isomorphism. -/
  isQuasiIso : ∀ j, (hom j).IsQuasiIsomorphism
  /-- `hom j` is bijective in degree one. -/
  bijective_degreeOne : ∀ j, Function.Bijective (hom j).degreeOne
  /-- `hom j` intertwines the two affine obstruction data `φ j`, `φ' j` in degree zero. -/
  comp_degreeZero : ∀ j, (φ' j).degreeZero.comp (hom j).degreeZero = (φ j).degreeZero
  /-- The isomorphism of affine bundle charts induced by `hom j` (via the degree-zero
  bijectivity derived from `isQuasiIso j` and `bijective_degreeOne j`) is compatible with the two
  embeddings of the chart into the total space of `𝓔`. -/
  bundleChart_comm : ∀ j,
    (VirtualClass.bundleSpaceIso (φ j) (φ' j) (hom j)
        (bijective_degreeZero_of_isQuasiIsomorphism_of_bijective_degreeOne
          (hom j) (isQuasiIso j) (bijective_degreeOne j))).hom ≫ 𝒞.bundleChartι j =
      𝒞'.bundleChartι j

/-- **A `ChartQuasiIso` is a `ConeGluingIndependence.ChartIso`.** The degree-zero bijectivity
required by `ChartIso` is supplied by
`LinearTwoTermComplex.Hom.bijective_degreeZero_of_isQuasiIsomorphism_of_bijective_degreeOne`,
and all remaining fields transport verbatim (the compatibility fields are `Prop`-valued, so the
particular proof of degree-zero bijectivity used to state them does not matter). -/
def ChartQuasiIso.toChartIso (H : ChartQuasiIso 𝒞 𝒞') : ChartIso 𝒞 𝒞' where
  hom := H.hom
  bijective_degreeZero := fun j ↦
    bijective_degreeZero_of_isQuasiIsomorphism_of_bijective_degreeOne
      (H.hom j) (H.isQuasiIso j) (H.bijective_degreeOne j)
  bijective_degreeOne := H.bijective_degreeOne
  comp_degreeZero := H.comp_degreeZero
  bundleChart_comm := H.bundleChart_comm

variable [∀ j, IsNoetherianRing (R j)]
variable [∀ j, Module.Free (R j ⧸ I j) (E j).degreeZero]
variable [∀ j, Module.Finite (R j ⧸ I j) (E j).degreeZero]
variable [∀ j, Module.Free (R j ⧸ I j) (E' j).degreeZero]
variable [∀ j, Module.Finite (R j ⧸ I j) (E' j).degreeZero]
variable [IsLocallyNoetherian 𝒞.coneScheme] [IsLocallyNoetherian 𝒞'.coneScheme]

/-- **Chart-wise quasi-isomorphic (bijective in degree one) cone data for the same bundle `𝓔`
give the same global cone class**, in every grading and every Chow group of the total space.
The quasi-isomorphism analogue of `ConeGluingIndependence.coneClassAt_eq`, obtained by passing to
the induced `ChartIso`. -/
theorem coneClassAt_eq_of_quasiIso (H : ChartQuasiIso 𝒞 𝒞')
    (dimAff : ∀ j, DimensionFunction (ResolvedCone.bundleSpace (φ j)))
    (dimE : DimensionFunction 𝓔.totalSpace) (d : ℤ)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE d) :
    𝒞.coneClassAt dimE d RE = 𝒞'.coneClassAt dimE d RE :=
  coneClassAt_eq H.toChartIso dimAff dimE d RE

/-! ## Corollary: the finite-type virtual class of a compact scheme over an infinite field -/

section FiniteType

open FiniteTypeDimension

variable {F : Type u} [Field F] [Infinite F]
  (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] [CompactSpace X] [Finite ι]
  (i : ℤ) (RX : RationalEquivalenceSystem X (dimensionFunction f) i)
  (RE : RationalEquivalenceSystem 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))
    (i + (Nat.card ι : ℤ)))

/-- **Resolution independence of the finite-type virtual class under a chart-wise
quasi-isomorphism bijective in degree one, for a fixed globally trivialised obstruction
bundle.**

For `X` compact and locally of finite type over an infinite field `F`, with a
`GlobalTrivialisation t` of `𝓔`, the unconditional virtual class `virtualClassFT'` of
`GlobalVirtualClassUnconditional.lean` agrees for the two chart-wise quasi-isomorphic cone data
`𝒞`, `𝒞'`: the hypothesis is exactly `ChartQuasiIso H`, with no extra assumption beyond those of
`existsUnique_virtualClassFT'_of_globalTrivialisation'`. The quasi-isomorphism analogue of
`ConeGluingIndependence.virtualClassFT'_eq`, obtained by passing to the induced `ChartIso`. -/
theorem virtualClassFT'_eq_of_quasiIso (H : ChartQuasiIso 𝒞 𝒞') (t : GlobalTrivialisation 𝓔) :
    VirtualClass.GlobalVirtualClass.virtualClassFT' f 𝒞 i RX RE =
      VirtualClass.GlobalVirtualClass.virtualClassFT' f 𝒞' i RX RE :=
  virtualClassFT'_eq f i RX RE H.toChartIso t

end FiniteType

end VirtualClass.ConeGluingQuasiIso

end

end GromovWitten.AlgebraicGeometry
