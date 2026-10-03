/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Stacks.ChartBaseChange
import GromovWitten.AlgebraicGeometry.IntersectionTheory.VistoliPushforward
import GromovWitten.AlgebraicGeometry.IntersectionTheory.AtlasIndependence

/-!
# Proper pushforward on the Vistoli Chow groups of Deligne–Mumford stacks

Let `f : X ⟶ Y` be a representable proper morphism of fppf stacks and `B` an étale surjective
chart of `Y`.  The base-change chart `A := f.baseChangeChart _ B` of `X`
(`Stacks/ChartBaseChange.lean`) is étale surjective, its projection `A.scheme ⟶ B.scheme` is
proper, and the self-overlap of `A` is the base change of the self-overlap of `B` through both
projections.  Hence the chart groupoids of `A` and `B` are related by a cartesian morphism of
étale presentation groupoids with proper map of atlases, and the Vistoli proper pushforward of
`IntersectionTheory/VistoliPushforward.lean` applies.  Composing with atlas independence
(`DeligneMumfordStack.vistoliChowEquivOfChart`) gives the proper pushforward between the Vistoli
Chow groups of Deligne–Mumford stacks computed from their chosen étale atlases.

The constructions live in the namespaces `GromovWitten.AlgebraicGeometry.StackHom`,
`GromovWitten.AlgebraicGeometry.StackChart` and `GromovWitten.AlgebraicGeometry.DeligneMumfordStack`
so that dot notation applies.

## Main results

* `StackChart.etaleGroupoid_good`: the chart groupoid of an étale surjective, representably
  quasi-compact chart with compact scheme locally of finite type over a field satisfies the
  standing hypotheses `Good`.
* `StackHom.cartesianGroupoidMap`: the cartesian morphism from the chart groupoid of the
  base-change chart to the chart groupoid of `B`; `StackHom.isProper_cartesianGroupoidMap_onBase`:
  its map of atlases is proper when `f` is representably proper.
* `StackHom.vistoliPushforward`: the Vistoli pushforward `A_i(A) → A_i(B)` of chart groups.
* `DeligneMumfordStack.properPushforward`: the proper pushforward
  `A_i(𝒳) → A_i(𝒴)` of Vistoli Chow groups (computed from the chosen étale atlases) along a
  representable proper morphism of Deligne–Mumford stacks.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry

open IntersectionTheory FiniteTypeDimension

namespace StackChart

variable {X : FppfStack.{u}} {k : Type u} [Field k]

/-- **The chart groupoid of a good chart is good.**  For an étale surjective, representably
quasi-compact chart `C` with compact scheme locally of finite type over `k`, the chart groupoid
`C.etaleGroupoid hC sC` satisfies the standing hypotheses `Good`. -/
theorem etaleGroupoid_good (C : StackChart X) (hC : C.IsEtaleSurjective)
    (hCq : C.HasRepresentableProperty @QuasiCompact) [CompactSpace C.scheme]
    (sC : C.scheme ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sC] :
    (C.etaleGroupoid hC sC).Good := by
  have hC' := C.isRepresentable_of_isEtaleSurjective hC
  have h1 : Etale (C.selfOverlapScheme hC').fst := C.selfOverlapScheme_fst_etale hC' hC
  have h2 : QuasiCompact (C.selfOverlapScheme hC').fst :=
    C.selfOverlapScheme_fst_quasiCompact hC' hCq
  have h3 : CompactSpace (C.selfOverlapScheme hC').space :=
    QuasiCompact.compactSpace_of_compactSpace (C.selfOverlapScheme hC').fst
  exact EtalePresentationGroupoid.good_of_locallyOfFiniteType sC
    ((C.selfOverlapScheme hC').fst ≫ sC)

end StackChart

namespace StackHom

variable {X Y : FppfStack.{u}} (f : StackHom X Y) (hf : f.IsRepresentable) (B : StackChart Y)
  (hB : B.IsEtaleSurjective) {k : Type u} [Field k]

/-- **The cartesian morphism of chart groupoids attached to a base-change chart.**  For a
representable `f : X ⟶ Y` and an étale surjective chart `B` of `Y`, the chart groupoid of the
base-change chart `f.baseChangeChart hf B` maps to the chart groupoid of `B`: on atlases by the
projection `f.baseChangeChartToBase hf B`, on arrows by the induced map of self-overlaps; both
the source and the target squares are cartesian. -/
noncomputable def cartesianGroupoidMap
    (sA : (f.baseChangeChart hf B).scheme ⟶ Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType sA]
    (sB : B.scheme ⟶ Spec (CommRingCat.of k)) [_root_.AlgebraicGeometry.LocallyOfFiniteType sB] :
    CartesianGroupoidMap
      ((f.baseChangeChart hf B).etaleGroupoid (f.baseChangeChart_isEtaleSurjective hf B hB) sA)
      (B.etaleGroupoid hB sB) where
  onBase := f.baseChangeChartToBase hf B
  onArrows := selfOverlapMap (baseChangePresentation f hf B) _ _
  src_comm := selfOverlapMap_fst _ _ _
  tgt_comm := selfOverlapMap_snd _ _ _
  isPullback_src := isPullback_selfOverlapMap_fst _ _ _
  isPullback_tgt := isPullback_selfOverlapMap_snd _ _ _

/-- The map of atlases of `cartesianGroupoidMap` is the projection of the base-change chart. -/
@[simp]
theorem cartesianGroupoidMap_onBase
    (sA : (f.baseChangeChart hf B).scheme ⟶ Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType sA]
    (sB : B.scheme ⟶ Spec (CommRingCat.of k)) [_root_.AlgebraicGeometry.LocallyOfFiniteType sB] :
    (f.cartesianGroupoidMap hf B hB sA sB).onBase = f.baseChangeChartToBase hf B := rfl

/-- For a representably proper `f`, the map of atlases of `cartesianGroupoidMap` is proper. -/
theorem isProper_cartesianGroupoidMap_onBase
    (hP : f.HasRepresentableProperty @_root_.AlgebraicGeometry.IsProper)
    (sA : (f.baseChangeChart hf B).scheme ⟶ Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType sA]
    (sB : B.scheme ⟶ Spec (CommRingCat.of k)) [_root_.AlgebraicGeometry.LocallyOfFiniteType sB] :
    _root_.AlgebraicGeometry.IsProper (f.cartesianGroupoidMap hf B hB sA sB).onBase :=
  f.baseChangeChartToBase_isProper hf B hP

/-- The base-change chart of a representably proper `f` has compact scheme when `B` does. -/
theorem compactSpace_baseChangeChart
    (hP : f.HasRepresentableProperty @_root_.AlgebraicGeometry.IsProper)
    [CompactSpace B.scheme] : CompactSpace (f.baseChangeChart hf B).scheme := by
  have := f.baseChangeChartToBase_isProper hf B hP
  exact QuasiCompact.compactSpace_of_compactSpace (f.baseChangeChartToBase hf B)

/-- **The Vistoli pushforward along the base-change chart.**  For a representably proper
`f : X ⟶ Y` and an étale surjective, representably quasi-compact chart `B` of `Y` with compact
scheme locally of finite type over `k`, the Vistoli proper pushforward
`A_i(f.baseChangeChart _ B) → A_i(B)` of the cartesian morphism `cartesianGroupoidMap`. -/
noncomputable def vistoliPushforward
    (hP : f.HasRepresentableProperty @_root_.AlgebraicGeometry.IsProper)
    (hBq : B.HasRepresentableProperty @_root_.AlgebraicGeometry.QuasiCompact)
    [CompactSpace B.scheme]
    (sA : (f.baseChangeChart (f.isRepresentable_of_hasRepresentableProperty _ hP) B).scheme ⟶
      Spec (CommRingCat.of k)) [_root_.AlgebraicGeometry.LocallyOfFiniteType sA]
    (sB : B.scheme ⟶ Spec (CommRingCat.of k)) [_root_.AlgebraicGeometry.LocallyOfFiniteType sB]
    (i : ℤ) :
    (f.baseChangeChart (f.isRepresentable_of_hasRepresentableProperty _ hP) B).vistoliChow
        (f.baseChangeChart_isEtaleSurjective _ B hB) sA i →ₗ[ℚ]
      B.vistoliChow hB sB i :=
  let hf := f.isRepresentable_of_hasRepresentableProperty _ hP
  let Φ := f.cartesianGroupoidMap hf B hB sA sB
  haveI := f.isProper_cartesianGroupoidMap_onBase hf B hB hP sA sB
  haveI := f.compactSpace_baseChangeChart hf B hP
  haveI : CompactSpace
      ((f.baseChangeChart hf B).etaleGroupoid (f.baseChangeChart_isEtaleSurjective hf B hB)
        sA).arrows := by
    have hG := B.etaleGroupoid_good hB hBq sB
    have := hG.compactSpace_arrows
    have := Φ.isProper_onArrows
    exact QuasiCompact.compactSpace_of_compactSpace Φ.onArrows
  have hH : ((f.baseChangeChart hf B).etaleGroupoid (f.baseChangeChart_isEtaleSurjective hf B hB)
      sA).Good := by
    have hA' := (f.baseChangeChart hf B).isRepresentable_of_isEtaleSurjective
      (f.baseChangeChart_isEtaleSurjective hf B hB)
    have : _root_.AlgebraicGeometry.Etale ((f.baseChangeChart hf B).selfOverlapScheme hA').fst :=
      (f.baseChangeChart hf B).selfOverlapScheme_fst_etale hA'
        (f.baseChangeChart_isEtaleSurjective hf B hB)
    exact EtalePresentationGroupoid.good_of_locallyOfFiniteType sA
      (((f.baseChangeChart hf B).selfOverlapScheme hA').fst ≫ sA)
  Φ.vistoliPushforward i sB hH (B.etaleGroupoid_good hB hBq sB)

end StackHom

namespace DeligneMumfordStack

variable {k : Type u} [Field k]

/-- **Proper pushforward on the Vistoli Chow groups of Deligne–Mumford stacks.**  Let
`f : 𝒳 ⟶ 𝒴` be a representable proper morphism of Deligne–Mumford stacks whose chosen étale
atlases are representably quasi-compact, with compact schemes locally of finite type over a
field `k`.  The proper pushforward `A_i(𝒳) → A_i(𝒴)` of Vistoli rational Chow groups (each
computed from the chosen étale atlas) is the composite of the atlas-independence isomorphism
`A_i(𝒳) ≅ A_i(f.baseChangeChart _ 𝒴.chosenEtaleAtlas)` with the Vistoli pushforward of the
cartesian morphism of chart groupoids `StackHom.cartesianGroupoidMap`. -/
noncomputable def properPushforward {𝒳 𝒴 : DeligneMumfordStack.{u}}
    (f : StackHom 𝒳.toStack 𝒴.toStack)
    (hP : f.HasRepresentableProperty @_root_.AlgebraicGeometry.IsProper)
    (hXq : 𝒳.chosenEtaleAtlas.HasRepresentableProperty @_root_.AlgebraicGeometry.QuasiCompact)
    [CompactSpace 𝒳.chosenEtaleAtlas.scheme]
    (sX : 𝒳.chosenEtaleAtlas.scheme ⟶ Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType sX]
    (hYq : 𝒴.chosenEtaleAtlas.HasRepresentableProperty @_root_.AlgebraicGeometry.QuasiCompact)
    [CompactSpace 𝒴.chosenEtaleAtlas.scheme]
    (sY : 𝒴.chosenEtaleAtlas.scheme ⟶ Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType sY]
    (i : ℤ) :
    𝒳.chosenEtaleAtlas.vistoliChow 𝒳.chosenEtaleAtlas_isEtaleSurjective sX i →ₗ[ℚ]
      𝒴.chosenEtaleAtlas.vistoliChow 𝒴.chosenEtaleAtlas_isEtaleSurjective sY i :=
  let hf := f.isRepresentable_of_hasRepresentableProperty _ hP
  let A := f.baseChangeChart hf 𝒴.chosenEtaleAtlas
  haveI := f.compactSpace_baseChangeChart hf 𝒴.chosenEtaleAtlas hP
  haveI := f.baseChangeChartToBase_isProper hf 𝒴.chosenEtaleAtlas hP
  let sA : A.scheme ⟶ Spec (CommRingCat.of k) := f.baseChangeChartToBase hf _ ≫ sY
  have hA := f.baseChangeChart_isEtaleSurjective hf _ 𝒴.chosenEtaleAtlas_isEtaleSurjective
  have hAq : A.HasRepresentableProperty @_root_.AlgebraicGeometry.QuasiCompact :=
    f.baseChangeChart_hasRepresentableProperty hf _ _ hYq
  (f.vistoliPushforward 𝒴.chosenEtaleAtlas 𝒴.chosenEtaleAtlas_isEtaleSurjective hP hYq sA sY
    i).comp (𝒳.vistoliChowEquivOfChart hXq sX A hA hAq sA i).toLinearMap

end DeligneMumfordStack

end GromovWitten.AlgebraicGeometry
