/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.SchemeAtlasRefinementChart
import GromovWitten.AlgebraicGeometry.Stacks.OverlapSwap
import GromovWitten.AlgebraicGeometry.Stacks.PropertiesDescent

/-!
# Scheme-valued common atlas refinements

Presentations of a chart and of its stack morphism are interchangeable. This
lets us prove that the scheme overlap of two smooth surjective charts is again
a smooth surjective chart, with both projections smooth and surjective. The
overlap and its universal comparison are obtained from chart representability.
-/

open CategoryTheory CategoryTheory.Limits
open GromovWitten.AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackChart

variable {X : FppfStack.{u}} {A : StackChart X}

/-! ## Recovering a chart pullback from a morphism presentation -/

set_option backward.isDefEq.respectTransparency false in
/-- Recover a chart presentation by normalizing the represented source object. -/
noncomputable def ofStackMorphismPresentation {T : Scheme.{u}} {y : StackFiber X T}
    (p : StackMorphismPresentation A.map T y) :
    A.PullbackPresentation T y := by
  cases p with
  | mk space map object comparison lift lift_map liftObjectIso lift_compatible
      liftObjectIso_unique lift_unique =>
    cases object with
    | mk as =>
      exact
        { space := space
          fst := map
          snd := as
          comparison := by simpa only [StackChart.obj] using comparison
          lift := fun toBase toChart c ↦
            lift toBase (Discrete.mk toChart) (by
              simpa only [StackChart.obj] using c)
          lift_fst := fun toBase toChart c ↦
            lift_map toBase (Discrete.mk toChart) (by
              simpa only [StackChart.obj] using c)
          lift_snd := fun toBase toChart c ↦ by
            have e := liftObjectIso toBase (Discrete.mk toChart) (by
              simpa only [StackChart.obj] using c)
            change Discrete.mk toChart ≅
              Discrete.mk (lift toBase (Discrete.mk toChart) _ ≫ as) at e
            exact (Discrete.eq_of_hom e.hom).symm
          lift_compatible := fun toBase toChart c ↦ by
            let c' : (A.map.appFunctor _).obj (Discrete.mk toChart) ≅
                (stackPullback X toBase).obj y := by
              simpa only [StackChart.obj] using c
            let g := lift toBase (Discrete.mk toChart) c'
            have e := liftObjectIso toBase (Discrete.mk toChart) c'
            change Discrete.mk toChart ≅ Discrete.mk (g ≫ as) at e
            have hobj : toChart = g ≫ as := Discrete.eq_of_hom e.hom
            have hc := lift_compatible toBase (Discrete.mk toChart) c'
            have hraw := stackMorphismInducedComparison_chart_raw'
              (A := A) map as comparison g (Discrete.mk toChart)
                (liftObjectIso toBase (Discrete.mk toChart) c')
            refine ⟨lift_map toBase (Discrete.mk toChart) c', hobj.symm, ?_⟩
            dsimp only [g] at hraw
            obtain ⟨map_eq, hcomp⟩ := hc
            rw [hraw] at hcomp
            simpa only [StackChart.obj, c', id_eq, Iso.trans_assoc] using hcomp
          lift_unique := fun toBase toChart c m compatible ↦ by
            obtain ⟨map_eq, hs, hcomp⟩ := compatible
            let c' : (A.map.appFunctor _).obj (Discrete.mk toChart) ≅
                (stackPullback X toBase).obj y := by
              simpa only [StackChart.obj] using c
            let objectIso := Discrete.eqToIso hs.symm
            apply lift_unique toBase (Discrete.mk toChart) c' m objectIso
            refine ⟨map_eq, ?_⟩
            have hraw := stackMorphismInducedComparison_chart_raw'
              (A := A) map as comparison m (Discrete.mk toChart)
                objectIso
            rw [hraw]
            simpa only [StackChart.obj, c', id_eq, Iso.trans_assoc] using hcomp }

/-- Chart and stack-morphism formulations agree for properties invariant under isomorphism. -/
theorem hasRepresentableProperty_iff_map
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    A.HasRepresentableProperty P ↔ A.map.HasRepresentableProperty P := by
  constructor
  · exact StackHom.hasRepresentableProperty_of_chart P
  · intro hmap
    have hraw := (StackHom.hasRepresentableProperty_iff_raw P).mp hmap
    refine ⟨?_, ?_⟩
    · intro T y
      obtain ⟨⟨q, _⟩⟩ := hraw T y
      exact ⟨StackChart.ofStackMorphismPresentation q⟩
    · intro T y q
      exact StackHom.property_of_hasRepresentablePropertyRaw P hraw
        (StackChart.toStackMorphismPresentation q)

end StackChart

/-! ## A common scheme atlas -/

variable {X : FppfStack.{u}}

/-- The chart on the overlap, composed through the first projection. -/
noncomputable def commonSchemeAtlasChart {A B : StackChart X}
    (p : B.PullbackPresentation A.scheme
      (A.obj A.scheme (𝟙 A.scheme))) : StackChart X where
  scheme := p.space
  map := Pseudofunctor.StrongTrans.vcomp
    (FppfStack.mapOfSchemeHom p.fst) A.map

/-- The universal overlap isomorphism pulled back along an arbitrary test-scheme map. -/
noncomputable def commonSchemeAtlasComparison {A B : StackChart X}
    (p : B.PullbackPresentation A.scheme
      (A.obj A.scheme (𝟙 A.scheme)))
    {S : Scheme.{u}} (g : S ⟶ p.space) :
    A.obj S (g ≫ p.fst) ≅ B.obj S (g ≫ p.snd) :=
  (A.objPullbackIso g p.fst).trans
    (((stackPullback X g).mapIso
      ((A.identityObjectPullbackComparison p.fst).trans p.comparison.symm)).trans
      (B.objPullbackIso g p.snd).symm)

/- The coherent comparison `StackIso2` is constructed from this fibrewise
   comparison in `SchemeAtlasRefinementCoherence.lean`. -/

/-- Two smooth surjective charts admit a scheme overlap which is itself an atlas,
with smooth surjective projections to both original chart schemes. -/
theorem exists_commonSchemeAtlas
    {X : FppfStack.{u}} (A B : StackChart X)
    (hA : A.IsSmoothSurjective) (hB : B.IsSmoothSurjective) :
    ∃ (p : B.PullbackPresentation A.scheme
        (A.obj A.scheme (𝟙 A.scheme))),
      (commonSchemeAtlasChart p).IsSmoothSurjective ∧
        (@_root_.AlgebraicGeometry.Smooth ⊓ @_root_.AlgebraicGeometry.Surjective)
          p.fst ∧
        (@_root_.AlgebraicGeometry.Smooth ⊓ @_root_.AlgebraicGeometry.Surjective)
          p.snd := by
  let P : MorphismProperty Scheme.{u} :=
    (@_root_.AlgebraicGeometry.Smooth ⊓ @_root_.AlgebraicGeometry.Surjective)
  have hbase : P.IsStableUnderBaseChange := by
    change ((@_root_.AlgebraicGeometry.Smooth ⊓
      @_root_.AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})).IsStableUnderBaseChange
    exact MorphismProperty.IsStableUnderBaseChange.inf
  have hcomp : P.IsStableUnderComposition := by
    have hsurj : MorphismProperty.IsStableUnderComposition
        (@_root_.AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u}) :=
      ⟨fun f g hf hg ↦ ⟨hg.1.comp hf.1⟩⟩
    change ((@_root_.AlgebraicGeometry.Smooth ⊓
      @_root_.AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})).IsStableUnderComposition
    exact MorphismProperty.IsStableUnderComposition.inf
  obtain ⟨p⟩ := hB.1 A.scheme (A.obj A.scheme (𝟙 A.scheme))
  have hpfst : P p.fst := by
    exact hB.2 A.scheme (A.obj A.scheme (𝟙 A.scheme)) p
  have hpsnd : P p.snd := by
    have hs := hA.2 B.scheme (B.obj B.scheme (𝟙 B.scheme))
      (StackChart.PullbackPresentation.swap B A p)
    exact hs
  have hscheme : (FppfStack.mapOfSchemeHom p.fst).HasRepresentableProperty P :=
    FppfStack.mapOfSchemeHom_hasRepresentableProperty P p.fst hpfst
  have hchart : A.map.HasRepresentableProperty P :=
    StackHom.hasRepresentableProperty_of_chart P hA
  have hmap : (commonSchemeAtlasChart p).map.HasRepresentableProperty P := by
    exact StackHom.comp_hasRepresentableProperty P hscheme hchart
  have hcommon : (commonSchemeAtlasChart p).HasRepresentableProperty P :=
    (StackChart.hasRepresentableProperty_iff_map
      (A := commonSchemeAtlasChart p) P).mpr hmap
  refine ⟨p, hcommon, hpfst, hpsnd⟩

end GromovWitten.AlgebraicGeometry
