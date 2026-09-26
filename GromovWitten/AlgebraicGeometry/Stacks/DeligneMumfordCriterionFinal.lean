/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.DeligneMumfordCriterionAssembly
import GromovWitten.AlgebraicGeometry.Stacks.EtaleAtlasDiagonal
import GromovWitten.AlgebraicGeometry.Stacks.EtaleSliceLocal

/-!
# The converse Deligne--Mumford criterion: the scheme-level slicing hypothesis

`Stacks.DeligneMumfordCriterionAssembly` reduces the converse Deligne--Mumford criterion
(an algebraic stack with representably unramified diagonal has an étale surjective chart) to
two statements.  This file proves the first of them and isolates the second as a single
scheme-theoretic proposition, which contains no stack theory at all.

Let `A` be a smooth surjective chart of `X`, `U := A.scheme`, and let
`pR : A.PullbackPresentation U (A.obj U (𝟙 U))` present the self-overlap `R = U ×_X U`, with
projections `t := pR.fst` and `s := pR.snd`.

## Main results

* `StackChart.selfOverlapPair_unramified_of_diagonal`: if `(stackDiagonal X).Unramified` then
  `Unramified (prod.lift pR.fst pR.snd)`, i.e. `R ⟶ U ⨯ U` is unramified, for *any* presentation
  `pR` of the self-overlap of *any* representable chart.  This transfers
  `StackChart.selfOverlapPair_unramified_of_stackDiagonal_unramified`
  (`Stacks.EtaleAtlasDiagonal`, proved there for the presentation chosen by representability) to
  an arbitrary presentation.  It is the only place where the unramifiedness of the diagonal is
  used, and it replaces `StackChart.selfOverlapPair_unramified`, which needed an *étale* chart.
* `EtaleSliceExists t s`: existence of a family of slices `g i : W i ⟶ U` with each
  `pullback.snd (g i) s ≫ t` étale and with the `g i` covering `U`;
  `etaleSliceExists_of_etale` shows it holds trivially when `t` is already étale.
  **Its covering condition is too strong**, see below.
* `LocalSlicing`: `EtaleSliceExists t s` for every smooth surjective `t` with `(t, s)`
  unramified (Stacks 06N3, scheme level, with the wrong covering condition).
  **This proposition is false**, see below.

## `LocalSlicing` is false; the criterion is proved from `SaturatedLocalSlicing`

`Stacks.EtaleSliceLocalSlicing` shows that the covering condition of `EtaleSliceExists` --
joint surjectivity of the `g i` themselves -- is too strong: applied to `R = U`, `s = 𝟙 U`
(whose pairing `prod.lift t (𝟙 U)` is an immersion, hence unramified, for every `t`),
`LocalSlicing` would give, for every smooth surjective self-map `t : U ⟶ U` and *every* point
`u` of `U`, a morphism `g : W ⟶ U` hitting `u` with `g ≫ t` étale; this fails for
`U = Spec ℤ[x₁, x₂, …]`, `t = Spec.map (xᵢ ↦ xᵢ₊₁)` and `u` the generic point
(`not_localSlicing_of_forall_not_etale`, `exists_etale_over_terminal_of_localSlicing`).
`EtaleSliceExists` and `LocalSlicing` are kept here only as the inputs of that refutation and of
the comparison with the corrected condition `SaturatedEtaleSliceExists`; no theorem is deduced
from them.

The converse criterion itself is proved in `Stacks.EtaleSliceLocalSlicing` from the corrected
hypothesis `SaturatedLocalSlicing`, which asks only that the *slice morphisms*
`pullback.snd (g i) s ≫ t` be jointly surjective, by
`AlgebraicStack.exists_etaleChart_of_unramified_diagonal_of_saturated` and
`AlgebraicStack.toDeligneMumfordStack_of_saturated`.

## The remaining gap

`SaturatedLocalSlicing` (Stacks 06N3 at the scheme level) is **not proved**, here or elsewhere in
the library; it is the one missing ingredient of the converse criterion.
`Stacks.EtaleSliceLocal` proves its affine core (`EtaleSliceLocal.etale_slice_specMap`: a slice of
an affine standard smooth `t` cut out by `n` functions whose differentials generate the relative
cotangent module has étale slice morphism); what is missing is the choice of those functions near
a point (Nakayama plus the two localisation facts recorded in that file) and, more seriously, the
fact that generating the relative cotangent module at one point of `R` forces it along the whole
slice `s⁻¹(W)`, which in Stacks 06N3 uses the groupoid composition law of `R = U ×_X U`.
-/

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackChart

variable {X : FppfStack.{u}} (A : StackChart X)

/-- **The self-overlap pairing of any presentation of `R = U ×_X U` is unramified when the
stack diagonal is.**  `EtaleAtlasDiagonal`'s
`selfOverlapPair_unramified_of_stackDiagonal_unramified` proves this for the presentation
`A.selfOverlapScheme hA` chosen by representability; any other presentation of the same object
differs from it by an isomorphism compatible with both projections
(`StackMorphismPresentation.isIso_baseChangeHom_id`, `baseChangeHom_id_map` and
`presentationBaseChangeHom_snd`), so the statement transfers. -/
theorem selfOverlapPair_unramified_of_diagonal (hA : A.IsRepresentable)
    (pR : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)))
    (h : (stackDiagonal X).Unramified) :
    Unramified (prod.lift pR.fst pR.snd) := by
  set P := A.selfOverlapScheme hA with hP
  set c : pR.space ⟶ P.space :=
    presentationBaseChangeHom P pR (𝟙 A.scheme)
      (stackPullbackIdIso X A.scheme (A.obj A.scheme (𝟙 A.scheme))) with hc
  have hiso : IsIso c :=
    StackMorphismPresentation.isIso_baseChangeHom_id (toStackMorphismPresentation P)
      (toStackMorphismPresentation pR)
  have hfst : c ≫ P.fst = pR.fst :=
    StackMorphismPresentation.baseChangeHom_id_map (toStackMorphismPresentation P)
      (toStackMorphismPresentation pR)
  have hsnd : c ≫ P.snd = pR.snd :=
    presentationBaseChangeHom_snd P pR (𝟙 A.scheme) _
  have hcomp : c ≫ A.selfOverlapPair hA = prod.lift pR.fst pR.snd := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prod.lift_fst, prod.lift_fst, hfst]
    · rw [Category.assoc, prod.lift_snd, prod.lift_snd, hsnd]
  rw [← hcomp]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@Unramified : MorphismProperty Scheme.{u}) _ _).2
    (A.selfOverlapPair_unramified_of_stackDiagonal_unramified hA h)

end StackChart

/-- **The local slicing statement** for a pair of morphisms `t s : R ⟶ U`: a family of
morphisms `g i : W i ⟶ U` whose images cover `U` such that each slice `s⁻¹(W i) ⟶ U` is
étale through `t`.

**The covering condition -- joint surjectivity of the `g i` themselves -- is too strong**: it is
what makes `LocalSlicing` below false (see the module docstring).  The condition the converse
criterion actually needs is that the *slice morphisms* be jointly surjective, i.e.
`GromovWitten.AlgebraicGeometry.SaturatedEtaleSliceExists` of `Stacks.EtaleSliceLocalSlicing`.
This definition is kept only as the input of the refutation of `LocalSlicing` there and of the
comparison `saturatedEtaleSliceExists_of_etaleSliceExists`. -/
def EtaleSliceExists {R U : Scheme.{u}} (t s : R ⟶ U) : Prop :=
  ∃ (σ : Type u) (W : σ → Scheme.{u}) (g : ∀ i, W i ⟶ U),
    (∀ i, Etale (pullback.snd (g i) s ≫ t)) ∧ ∀ u : U, ∃ (i : σ) (w : W i), (g i) w = u

/-- **Local slicing of a smooth morphism with unramified pairing** (Stacks 06N3, the scheme-level
step, with the covering condition of `EtaleSliceExists`): for `t : R ⟶ U` smooth and surjective
and `s : R ⟶ U` such that `(t, s) : R ⟶ U ⨯ U` is unramified, slices as in `EtaleSliceExists`
exist.  This statement involves no stacks.

**This proposition is false**, the covering condition of `EtaleSliceExists` being too strong: see
`GromovWitten.AlgebraicGeometry.not_localSlicing_of_forall_not_etale` and
`GromovWitten.AlgebraicGeometry.exists_etale_over_terminal_of_localSlicing` in
`Stacks.EtaleSliceLocalSlicing`.  Nothing is deduced from it; the corrected proposition
`SaturatedLocalSlicing` of that file replaces it and yields the converse Deligne--Mumford
criterion (`AlgebraicStack.exists_etaleChart_of_unramified_diagonal_of_saturated`). -/
def LocalSlicing : Prop :=
  ∀ (R U : Scheme.{u}) (t s : R ⟶ U), _root_.AlgebraicGeometry.Smooth t →
    _root_.AlgebraicGeometry.Surjective t → Unramified (prod.lift t s) → EtaleSliceExists t s

/-- **Nonvacuity of `EtaleSliceExists`:** if `t` is already étale, the trivial family
`g = 𝟙 U` is a slicing.  (So `LocalSlicing` is exactly the statement that one can always reduce
to this case -- which is why it is false: reducing to it needs a slice through a *prescribed*
point.) -/
theorem etaleSliceExists_of_etale {R U : Scheme.{u}} (t s : R ⟶ U) (ht : Etale t) :
    EtaleSliceExists t s := by
  have _hres : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine ⟨PUnit.{u + 1}, fun _ ↦ U, fun _ ↦ 𝟙 U, fun _ ↦ ?_, fun u ↦ ⟨PUnit.unit, u, ?_⟩⟩
  · have hiso : IsIso (pullback.snd (𝟙 U) s) :=
      (IsPullback.of_hasPullback (𝟙 U) s).isIso_snd_of_isIso
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@Etale : MorphismProperty Scheme.{u}) (pullback.snd (𝟙 U) s) t).2 ht
  · rfl

end GromovWitten.AlgebraicGeometry
