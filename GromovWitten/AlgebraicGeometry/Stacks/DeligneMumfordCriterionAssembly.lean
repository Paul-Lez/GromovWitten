/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Sites.StackSiteContinuity
import GromovWitten.AlgebraicGeometry.Stacks.SchemeAtlasRefinementChart
import GromovWitten.AlgebraicGeometry.Stacks.PropertiesDescent
import GromovWitten.AlgebraicGeometry.Stacks.EtaleSliceScheme
import GromovWitten.AlgebraicGeometry.Stacks.StackProducts

/-!
# Testing etaleness of a sliced chart on the self-overlap

This file assembles the geometric step of the converse Deligne--Mumford criterion
(Stacks 06N3) that turns a *scheme-level* statement about the self-overlap of a smooth atlas
into a *stack-level* statement about a chart.

Let `A` be a smooth surjective chart of a stack `X`, write `U := A.scheme`, and let
`pR : A.PullbackPresentation U (A.obj U (𝟙 U))` be the self-overlap of `A`, i.e. a scheme
`R = U ×_X U` with the two projections `t := pR.fst` and `s := pR.snd`.  For a morphism of
schemes `g : W ⟶ U` the sliced chart `SiteChart.restrict A g : StackChart X` is the composite
`W → U → X`.  The main theorem `StackChart.restrict_hasRepresentableProperty_of_slice` says that
a base-change stable, fppf-descending property `P` (such as `Etale`) holds for the sliced chart
as soon as it holds for the single morphism of schemes

`pullback.snd g pR.snd ≫ pR.fst : s⁻¹(W) ⟶ U`,

that is, as soon as `s⁻¹(W) → U` has `P` through `t`.  No presentation has to be constructed by
hand: `StackChart.isPullback_presentationBaseChangeHom` (a repackaging of
`StackMorphismPresentation.isPullback_baseChangeHom` through
`StackChart.toStackMorphismPresentation`) identifies *one* auxiliary presentation
`q : A.PullbackPresentation p.space (A.obj p.space p.snd)` simultaneously with
`p.space ×_T p.space` and with `p.space ×_U R`; the theorem is then pure pasting of pullback
squares followed by fppf descent along the smooth surjective `p.fst`.

## Main results

* `StackChart.isPullback_presentationBaseChangeHom`, `StackChart.presentationBaseChangeHom_snd`:
  the comparison of two chart presentations over different bases is a pullback square of schemes
  and is compatible with the chart legs.
* `StackChart.restrict_hasRepresentableProperty_of_slice`: the criterion above, and
  `StackChart.restrict_hasRepresentableProperty_iff_slice`: it is an equivalence, the converse
  being `StackChart.slice_of_restrict_hasRepresentableProperty`.
* `StackChart.restrict_isEtaleSurjective_of_slice`: with `g` surjective and `s⁻¹(W) → U` etale,
  the sliced chart is an etale surjective atlas.
* `AlgebraicStack.exists_etaleChart_of_exists_slice`,
  `AlgebraicStack.toDeligneMumfordStack_of_exists_slice`: the resulting Deligne--Mumford stack.
* `AlgebraicStack.exists_etaleChart_of_sliceFamily`: the same, from a *family* of slices whose
  images cover `U`, via the gluing of `Stacks/EtaleSliceScheme.lean`.  This is the form in which
  the criterion will be applied, since slicing only works locally on `U`.
* `StackChart.hasUnramifiedIsom_of_stackDiagonal_unramified`: the hypothesis
  `(stackDiagonal X).Unramified` of the converse criterion, unpacked into unramifiedness of the
  isomorphism schemes of pairs of chart objects.

## Remaining gap

The input `Etale (pullback.snd (g i) pR.snd ≫ pR.fst)` for a family covering `U` has to be
produced from the unramifiedness of the stack diagonal by cutting an affine chart of `U` by `d`
functions whose differentials generate the relative cotangent module of `t`
(`Stacks/EtaleSlice.lean` has the commutative-algebra core,
`EtaleSlice.etale_of_span_eq_top_of_isStandardSmooth`).  That step is not formalised, so the
headline theorem `AlgebraicStack.exists_etaleChart_of_unramified_diagonal_of_saturated` is not
available here;
the exact missing statement is the hypothesis `hEt` of
`AlgebraicStack.exists_etaleChart_of_sliceFamily`.
-/

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Sites

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackChart

variable {X : FppfStack.{u}} {A : StackChart X}

/-! ## Comparing chart presentations over different bases -/

/-- The canonical comparison morphism from a chart presentation over `S` to a chart
presentation over `T`, along a morphism `base : S ⟶ T` identifying the presented objects. -/
noncomputable def presentationBaseChangeHom {T S : Scheme.{u}} {x : StackFiber X T}
    {y : StackFiber X S} (p : A.PullbackPresentation T x) (q : A.PullbackPresentation S y)
    (base : S ⟶ T) (kappa : y ≅ (stackPullback X base).obj x) : q.space ⟶ p.space :=
  (toStackMorphismPresentation p).baseChangeHom (toStackMorphismPresentation q) base kappa

/-- **The representing scheme of a chart presentation over `S` is the fibre product of the
representing scheme over `T` with `S`.** -/
theorem isPullback_presentationBaseChangeHom {T S : Scheme.{u}} {x : StackFiber X T}
    {y : StackFiber X S} (p : A.PullbackPresentation T x) (q : A.PullbackPresentation S y)
    (base : S ⟶ T) (kappa : y ≅ (stackPullback X base).obj x) :
    IsPullback q.fst (presentationBaseChangeHom p q base kappa) base p.fst :=
  (toStackMorphismPresentation p).isPullback_baseChangeHom
    (toStackMorphismPresentation q) base kappa

set_option backward.isDefEq.respectTransparency false in
/-- The comparison morphism of two chart presentations is compatible with the chart legs. -/
theorem presentationBaseChangeHom_snd {T S : Scheme.{u}} {x : StackFiber X T}
    {y : StackFiber X S} (p : A.PullbackPresentation T x) (q : A.PullbackPresentation S y)
    (base : S ⟶ T) (kappa : y ≅ (stackPullback X base).obj x) :
    presentationBaseChangeHom p q base kappa ≫ p.snd = q.snd :=
  p.lift_snd _ _ _

/-! ## Testing a representable property of a sliced chart on the self-overlap -/

variable (A) in
/-- **A representable property of a chart precomposed with `g : W ⟶ A.scheme` is tested on the
self-overlap slice.**  If `P` is stable under base change and descends along fppf covers, and if
the second leg `s⁻¹(W) ⟶ A.scheme` of the slice of the self-overlap `pR` has `P`, then the
sliced chart `SiteChart.restrict A g` has the representable property `P`.

The proof identifies the auxiliary presentation `q` of the chart over its own presentation space
both with `p.space ×_T p.space` and with `p.space ×_{A.scheme} R`, so that the base change of
`(SiteChart.restrictPresentation A g p).fst` along the smooth surjective cover `p.fst` becomes
the base change of `s⁻¹(W) ⟶ A.scheme` along `p.snd`. -/
theorem restrict_hasRepresentableProperty_of_slice
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong FppfCover.{u}] (hA : A.IsSmoothSurjective)
    (pR : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)))
    {W : Scheme.{u}} (g : W ⟶ A.scheme)
    (hslice : P (pullback.snd g pR.snd ≫ pR.fst)) :
    (SiteChart.restrict A g).HasRepresentableProperty P := by
  refine SiteChart.hasRepresentableProperty_of_exists (SiteChart.restrict A g) P
    MorphismProperty.IsStableUnderBaseChange.respectsIso ?_
  intro T x
  obtain ⟨p⟩ := hA.1 T x
  refine ⟨SiteChart.restrictPresentation A g p, ?_⟩
  change P (pullback.snd g p.snd ≫ p.fst)
  obtain ⟨q⟩ := hA.1 p.space (A.obj p.space p.snd)
  set h₁ := presentationBaseChangeHom p q p.fst p.comparison with hh₁
  set h₂ := presentationBaseChangeHom pR q p.snd
    (A.identityObjectPullbackComparison p.snd) with hh₂
  have sq₁ : IsPullback q.fst h₁ p.fst p.fst := by
    rw [hh₁]; exact isPullback_presentationBaseChangeHom p q p.fst p.comparison
  have sq₂ : IsPullback q.fst h₂ p.snd pR.fst := by
    rw [hh₂]
    exact isPullback_presentationBaseChangeHom pR q p.snd
      (A.identityObjectPullbackComparison p.snd)
  have e₁ : h₁ ≫ p.snd = q.snd := by
    rw [hh₁]; exact presentationBaseChangeHom_snd p q p.fst p.comparison
  have e₂ : h₂ ≫ pR.snd = q.snd := by
    rw [hh₂]
    exact presentationBaseChangeHom_snd pR q p.snd (A.identityObjectPullbackComparison p.snd)
  have sqZ : IsPullback (pullback.fst g p.snd) (pullback.snd g p.snd) g p.snd :=
    IsPullback.of_hasPullback _ _
  have sqA : IsPullback (pullback.fst h₁ (pullback.snd g p.snd))
      (pullback.snd h₁ (pullback.snd g p.snd)) h₁ (pullback.snd g p.snd) :=
    IsPullback.of_hasPullback _ _
  have sqB := sqA.paste_vert sqZ.flip
  rw [e₁, ← e₂] at sqB
  have sqAlpha := IsPullback.of_bot' sqB (IsPullback.of_hasPullback g pR.snd).flip
  have sqII := sqAlpha.paste_horiz sq₂
  have hII : P (pullback.fst h₁ (pullback.snd g p.snd) ≫ q.fst) :=
    MorphismProperty.of_isPullback sqII.flip hslice
  have hcov : FppfCover.{u} p.fst := by
    have hsm := hA.2 T x p
    exact smoothCover_le_fppfCover _ ⟨hsm.2, hsm.1⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (sqA.paste_horiz sq₁) hcov hII

variable (A) in
/-- The slice condition is also necessary: the self-overlap presentation `pR` of `A` presents
the base change of the sliced chart along `A` itself. -/
theorem slice_of_restrict_hasRepresentableProperty (P : MorphismProperty Scheme.{u})
    (pR : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)))
    {W : Scheme.{u}} (g : W ⟶ A.scheme)
    (h : (SiteChart.restrict A g).HasRepresentableProperty P) :
    P (pullback.snd g pR.snd ≫ pR.fst) :=
  h.2 A.scheme _ (SiteChart.restrictPresentation A g pR)

variable (A) in
/-- **A representable property of a sliced chart is equivalent to the corresponding property of
the slice of the self-overlap.** -/
theorem restrict_hasRepresentableProperty_iff_slice
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong FppfCover.{u}] (hA : A.IsSmoothSurjective)
    (pR : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)))
    {W : Scheme.{u}} (g : W ⟶ A.scheme) :
    (SiteChart.restrict A g).HasRepresentableProperty P ↔
      P (pullback.snd g pR.snd ≫ pR.fst) :=
  ⟨slice_of_restrict_hasRepresentableProperty A P pR g,
    restrict_hasRepresentableProperty_of_slice A P hA pR g⟩

variable (A) in
/-- **An etale surjective slice of a smooth surjective chart is an etale surjective chart.**
If `g : W ⟶ A.scheme` is surjective and the slice `s⁻¹(W) ⟶ A.scheme` of the self-overlap is
etale, then the sliced chart `SiteChart.restrict A g` is an etale surjective atlas. -/
theorem restrict_isEtaleSurjective_of_slice (hA : A.IsSmoothSurjective)
    (pR : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)))
    {W : Scheme.{u}} (g : W ⟶ A.scheme) (hg : Surjective g)
    (hslice : Etale (pullback.snd g pR.snd ≫ pR.fst)) :
    (SiteChart.restrict A g).IsEtaleSurjective := by
  have hsurjfst : Surjective (pullback.snd g pR.snd) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback g pR.snd) hg
  have hsurjR : Surjective pR.fst := (hA.2 A.scheme _ pR).2
  have _inst : MorphismProperty.IsStableUnderBaseChange
      ((@Etale ⊓ @Surjective) : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have _inst2 : MorphismProperty.DescendsAlong
      ((@Etale ⊓ @Surjective) : MorphismProperty Scheme.{u}) FppfCover.{u} :=
    MorphismProperty.DescendsAlong.inf
  have _inst3 : MorphismProperty.IsStableUnderComposition
      ((@Surjective) : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      ((@Surjective) : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  refine restrict_hasRepresentableProperty_of_slice A _ hA pR g ⟨hslice, ?_⟩
  exact MorphismProperty.comp_mem _ _ _ hsurjfst hsurjR

/-! ## The unramified diagonal as an input -/

variable (A) in
/-- **An unramified stack diagonal gives unramified isomorphism schemes for every chart.**  This
is the converse of `stackDiagonal_unramified_of_etaleAtlas`'s hypothesis and is the form in which
the hypothesis `(stackDiagonal X).Unramified` of the converse Deligne--Mumford criterion is used.

The identification of the self-overlap presentation `pR` with the isomorphism scheme of the
pair `(prod.fst, prod.snd)` over `A.scheme ⨯ A.scheme`, which turns this statement into
`Unramified (prod.lift pR.fst pR.snd)` for every representable chart, is
`StackChart.selfOverlapPair_unramified_of_stackDiagonal_unramified` in
`Stacks/EtaleAtlasDiagonal.lean`; it is used in `Stacks/DeligneMumfordCriterionFinal.lean`. -/
theorem hasUnramifiedIsom_of_stackDiagonal_unramified
    (h : (stackDiagonal X).Unramified) : A.HasUnramifiedIsom := by
  intro S a b
  obtain ⟨⟨p, hp⟩⟩ := (StackHom.hasRepresentableProperty_iff_raw
    (@GromovWitten.AlgebraicGeometry.Unramified : MorphismProperty Scheme.{u})).1 h S
    (stackProdObj (A.obj S a) (A.obj S b))
  exact ⟨p, hp⟩

end StackChart

/-- **Existence of an etale surjective chart from a slice of the self-overlap.**  Given a smooth
surjective chart `A` of an algebraic stack and a presentation `pR` of its self-overlap
`R = A.scheme ×_X A.scheme` (with projections `t = pR.fst`, `s = pR.snd`), a surjective
`g : W ⟶ A.scheme` whose slice `s⁻¹(W) ⟶ A.scheme` is etale through `t` produces an etale
surjective atlas.

The still-missing geometric input for the converse Deligne--Mumford criterion is exactly the
hypothesis `h` below, derived from `(stackDiagonal X.toStack).Unramified`. -/
theorem AlgebraicStack.exists_etaleChart_of_exists_slice (X : AlgebraicStack.{u})
    (A : StackChart X.toStack) (hA : A.IsSmoothSurjective)
    (pR : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)))
    (h : ∃ (W : Scheme.{u}) (g : W ⟶ A.scheme), Surjective g ∧
      Etale (pullback.snd g pR.snd ≫ pR.fst)) :
    ∃ B : StackChart X.toStack, B.IsEtaleSurjective := by
  obtain ⟨W, g, hg, hslice⟩ := h
  exact ⟨SiteChart.restrict A g, StackChart.restrict_isEtaleSurjective_of_slice A hA pR g hg hslice⟩

/-- **The converse Deligne--Mumford criterion, reduced to a purely local slicing statement.**
A family of slices `g i : W i ⟶ A.scheme` whose images cover `A.scheme` and each of whose
self-overlap slices `s⁻¹(W i) ⟶ A.scheme` is etale through `t` produces an etale surjective
atlas.  Only the *local* existence of such slices (from an unramified diagonal) is missing. -/
theorem AlgebraicStack.exists_etaleChart_of_sliceFamily (X : AlgebraicStack.{u})
    (A : StackChart X.toStack) (hA : A.IsSmoothSurjective)
    (pR : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)))
    {σ : Type u} (W : σ → Scheme.{u}) (g : ∀ i, W i ⟶ A.scheme)
    (hEt : ∀ i, Etale (pullback.snd (g i) pR.snd ≫ pR.fst))
    (hcov : ∀ u : A.scheme, ∃ (i : σ) (w : W i), (g i) w = u) :
    ∃ B : StackChart X.toStack, B.IsEtaleSurjective :=
  X.exists_etaleChart_of_exists_slice A hA pR
    (exists_surjective_etale_slice_of_family pR.fst pR.snd W g hEt hcov)

/-- The Deligne--Mumford stack attached to an algebraic stack admitting an etale slice of
smooth atlas, cf. `AlgebraicStack.exists_etaleChart_of_exists_slice`. -/
def AlgebraicStack.toDeligneMumfordStack_of_exists_slice (X : AlgebraicStack.{u})
    (A : StackChart X.toStack) (hA : A.IsSmoothSurjective)
    (pR : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)))
    (h : ∃ (W : Scheme.{u}) (g : W ⟶ A.scheme), Surjective g ∧
      Etale (pullback.snd g pR.snd ≫ pR.fst)) :
    DeligneMumfordStack.{u} where
  toAlgebraicStack := X
  etaleAtlas := X.exists_etaleChart_of_exists_slice A hA pR h

end GromovWitten.AlgebraicGeometry
