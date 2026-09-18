/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.Dimension

/-!
# Exchanging the two legs of the overlap of two charts

`Stacks.Dimension` computes the dimension of an algebraic stack from an atlas and reduces its
atlas independence to the geometry of the overlap `U ×_X V` of two atlases.  Only the *first*
projection `U ×_X V ⟶ V` was known to be smooth, surjective and of the relative dimension of
the first atlas; the second projection `U ×_X V ⟶ U` was left as three hypotheses of
`StackDimensionPresentation.CommonRefinement.ofOverlap`.

This file removes those hypotheses.  The missing ingredient was the symmetry of a chart
pullback presentation in the two charts, which is constructed here:

* `StackChart.swapComparison A B` reverses a comparison 2-cell
  `A.obj S f ≅ (stackPullback X g).obj (B.obj B.scheme (𝟙 B.scheme))` into
  `B.obj S g ≅ (stackPullback X f).obj (A.obj A.scheme (𝟙 A.scheme))`, using the canonical
  identification `identityObjectPullbackComparison` of a chart object with a pullback of the
  tautological object of that chart.  It is an involution
  (`StackChart.swapComparison_swapComparison`) and it commutes with pulling back along a test
  map (`StackChart.inducedComparison_swap`), which is the only coherence needed.
* `StackChart.classifies_swap_iff` transports the classification predicate, and
  `StackChart.PullbackPresentation.swap` is the resulting presentation
  `B.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme))` on the *same* scheme with the
  two legs exchanged: `swap.space = P.space`, `swap.fst = P.snd`, `swap.snd = P.fst`, all by
  `rfl` (`StackChart.PullbackPresentation.swap_space/_fst/_snd`).  Every classification and
  uniqueness field is derived from the corresponding field of `P` by conjugating with
  `swapComparison`; nothing is assumed.

  This generalises `StackChart.PullbackPresentation.selfSwap` of `Stacks.Algebraic`, which is
  the case `A = B`, to two distinct charts, at the (necessary) cost of restricting the base
  object to the tautological object of a second chart — which is exactly the situation of the
  overlap of two atlases.

## Consequences for stack dimension

* `StackDimensionPresentation.overlap_snd_smooth`, `overlap_snd_surjective` and
  `overlap_snd_relativeDimension`: the second projection of the overlap is smooth, surjective
  and of the relative dimension of the *second* atlas, obtained by applying the representability
  hypotheses of the second atlas to `StackDimensionPresentation.overlapSwap`.
* `StackDimensionPresentation.CommonRefinement.overlap`: two atlas dimension presentations
  always admit a common refinement — unconditionally, with no hypothesis at all.
* `stackDimensionIndependent_of_smoothPureDimensionFormula` and
  `AlgebraicStack.dim_eq_of_smoothPureDimensionFormula`: atlas independence and the computation
  of `AlgebraicStack.dim` now depend only on the scheme-level dimension formula for smooth
  surjections (plus non-emptiness of the atlas schemes, which is genuinely needed: over an empty
  atlas scheme every pure dimension holds vacuously).
* Because a proof of the scheme-level formula is expected only in a restricted setting (schemes
  locally of finite type over a field), the same conclusion is also derived from the *local*
  hypothesis `OverlapDimensionFormula X`, which asks for the formula only for the two
  projections of the overlaps of atlases of `X` (`SmoothPureDimensionFormulaAt` is the formula
  for a single morphism):
  `stackDimensionIndependent_of_overlapDimensionFormula`.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackChart

variable {X : FppfStack.{u}}

/-! ## Reversing a comparison cell between two charts -/

/-- Reverse a comparison 2-cell between two charts.  A cell exhibiting the chart object of
`f : S ⟶ A.scheme` as the pullback along `g : S ⟶ B.scheme` of the tautological object of `B`
is turned into a cell exhibiting the chart object of `g` as the pullback along `f` of the
tautological object of `A`.  This is the groupoid symmetry exchanging the two legs of an
overlap, with the pseudonaturality comparisons inserted explicitly. -/
noncomputable def swapComparison (A B : StackChart X) {S : Scheme.{u}}
    {f : S ⟶ A.scheme} {g : S ⟶ B.scheme}
    (c : A.obj S f ≅ (stackPullback X g).obj (B.obj B.scheme (𝟙 B.scheme))) :
    B.obj S g ≅ (stackPullback X f).obj (A.obj A.scheme (𝟙 A.scheme)) :=
  (B.identityObjectPullbackComparison g).trans
    (c.symm.trans (A.identityObjectPullbackComparison f))

/-- Reversing a comparison cell twice, with the roles of the two charts exchanged back,
recovers the original cell. -/
@[simp]
theorem swapComparison_swapComparison (A B : StackChart X) {S : Scheme.{u}}
    {f : S ⟶ A.scheme} {g : S ⟶ B.scheme}
    (c : A.obj S f ≅ (stackPullback X g).obj (B.obj B.scheme (𝟙 B.scheme))) :
    B.swapComparison A (A.swapComparison B c) = c := by
  simp [swapComparison]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back a reversed comparison cell is the reversal of the pulled-back cell.  This is
the coherence that lets the two legs of a chart pullback presentation be exchanged. -/
theorem inducedComparison_swap (A B : StackChart X)
    (P : A.PullbackPresentation B.scheme (B.obj B.scheme (𝟙 B.scheme)))
    {S : Scheme.{u}} (m : S ⟶ P.space) :
    B.inducedComparison P.snd P.fst (A.swapComparison B P.comparison) m =
      A.swapComparison B (A.inducedComparison P.fst P.snd P.comparison m) := by
  unfold swapComparison
  rw [← A.inducedComparison_identityObjectPullbackComparison P.snd m,
    ← B.inducedComparison_identityObjectPullbackComparison P.fst m]
  apply Iso.ext
  dsimp only [inducedComparison, Iso.trans, Iso.symm,
    CategoryTheory.Functor.mapIso]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]

/-- Classifying a scheme map by the leg-exchanged presentation is the same as classifying it by
the original presentation with the two legs and the comparison cell exchanged. -/
theorem classifies_swap_iff (A B : StackChart X)
    (P : A.PullbackPresentation B.scheme (B.obj B.scheme (𝟙 B.scheme)))
    {S : Scheme.{u}} (toBase : S ⟶ A.scheme) (toChart : S ⟶ B.scheme)
    (c : B.obj S toChart ≅
      (stackPullback X toBase).obj (A.obj A.scheme (𝟙 A.scheme)))
    (m : S ⟶ P.space) :
    B.Classifies P.snd P.fst (A.swapComparison B P.comparison) toBase toChart c m ↔
      A.Classifies P.fst P.snd P.comparison toChart toBase
        (B.swapComparison A c) m := by
  constructor
  · rintro ⟨fst_eq, snd_eq, h⟩
    refine ⟨snd_eq, fst_eq, ?_⟩
    subst toBase
    subst toChart
    simp only [objIsoOfEq, stackPullbackObjIsoOfEq, Iso.refl_symm,
      Iso.refl_trans, Iso.trans_refl] at h ⊢
    rw [A.inducedComparison_swap B P m] at h
    have h' := congrArg (fun z ↦ B.swapComparison A z) h
    simpa using h'
  · rintro ⟨fst_eq, snd_eq, h⟩
    refine ⟨snd_eq, fst_eq, ?_⟩
    subst toBase
    subst toChart
    simp only [objIsoOfEq, stackPullbackObjIsoOfEq, Iso.refl_symm,
      Iso.refl_trans, Iso.trans_refl] at h ⊢
    rw [A.inducedComparison_swap B P m]
    simpa using congrArg (fun z ↦ A.swapComparison B z) h

/-! ## The leg-exchanged pullback presentation -/

/-- **The overlap of two charts, with its two legs exchanged.**  A presentation of the base
change of the chart `A` by the tautological object of the chart `B` is also a presentation of
the base change of `B` by the tautological object of `A`, on the *same* scheme, with the two
projections swapped.  The comparison cell is the reversed one and every classification and
uniqueness law is obtained from the original one by conjugation. -/
noncomputable def PullbackPresentation.swap (A B : StackChart X)
    (P : A.PullbackPresentation B.scheme (B.obj B.scheme (𝟙 B.scheme))) :
    B.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)) where
  space := P.space
  fst := P.snd
  snd := P.fst
  comparison := A.swapComparison B P.comparison
  lift toBase toChart c := P.lift toChart toBase (B.swapComparison A c)
  lift_fst toBase toChart c := P.lift_snd toChart toBase (B.swapComparison A c)
  lift_snd toBase toChart c := P.lift_fst toChart toBase (B.swapComparison A c)
  lift_compatible toBase toChart c :=
    (A.classifies_swap_iff B P toBase toChart c
      (P.lift toChart toBase (B.swapComparison A c))).2
        (P.lift_compatible toChart toBase (B.swapComparison A c))
  lift_unique toBase toChart c m compatible :=
    P.lift_unique toChart toBase (B.swapComparison A c) m
      ((A.classifies_swap_iff B P toBase toChart c m).1 compatible)

/-- The leg-exchanged presentation lives on the same scheme. -/
@[simp]
theorem PullbackPresentation.swap_space (A B : StackChart X)
    (P : A.PullbackPresentation B.scheme (B.obj B.scheme (𝟙 B.scheme))) :
    (PullbackPresentation.swap A B P).space = P.space := rfl

/-- The first projection of the leg-exchanged presentation is the second projection of the
original one. -/
@[simp]
theorem PullbackPresentation.swap_fst (A B : StackChart X)
    (P : A.PullbackPresentation B.scheme (B.obj B.scheme (𝟙 B.scheme))) :
    (PullbackPresentation.swap A B P).fst = P.snd := rfl

/-- The second projection of the leg-exchanged presentation is the first projection of the
original one. -/
@[simp]
theorem PullbackPresentation.swap_snd (A B : StackChart X)
    (P : A.PullbackPresentation B.scheme (B.obj B.scheme (𝟙 B.scheme))) :
    (PullbackPresentation.swap A B P).snd = P.fst := rfl

end StackChart

/-! ## The second projection of the overlap of two atlases -/

namespace StackDimensionPresentation

variable {X : AlgebraicStack.{u}}

/-- The overlap `U ×_X V` of the atlases of two dimension presentations, regarded as a pullback
presentation of the *second* chart against the tautological object of the first.  It is the
same scheme with the two projections exchanged. -/
noncomputable def overlapSwap (A B : StackDimensionPresentation X) :
    B.atlas.PullbackPresentation A.atlas.scheme A.atlas.tautologicalObject :=
  StackChart.PullbackPresentation.swap A.atlas B.atlas (A.overlap B)

/-- The first projection of the exchanged overlap is the second projection of the overlap. -/
theorem overlapSwap_fst (A B : StackDimensionPresentation X) :
    (A.overlapSwap B).fst = (A.overlap B).snd := rfl

/-- The second projection of the exchanged overlap is the first projection of the overlap. -/
theorem overlapSwap_snd (A B : StackDimensionPresentation X) :
    (A.overlapSwap B).snd = (A.overlap B).fst := rfl

/-- **The projection `U ×_X V ⟶ U` is smooth**, because the second atlas is. -/
theorem overlap_snd_smooth (A B : StackDimensionPresentation X) :
    _root_.AlgebraicGeometry.Smooth (A.overlap B).snd :=
  (B.isSmoothSurjective.2 A.atlas.scheme A.atlas.tautologicalObject
    (A.overlapSwap B)).1

/-- **The projection `U ×_X V ⟶ U` is surjective**, because the second atlas is. -/
theorem overlap_snd_surjective (A B : StackDimensionPresentation X) :
    _root_.AlgebraicGeometry.Surjective (A.overlap B).snd :=
  (B.isSmoothSurjective.2 A.atlas.scheme A.atlas.tautologicalObject
    (A.overlapSwap B)).2

/-- **The projection `U ×_X V ⟶ U` has the relative dimension of the second atlas**, because it
is a base change of it. -/
theorem overlap_snd_relativeDimension (A B : StackDimensionPresentation X) :
    SchemeMorphismPureRelativeDimension (A.overlap B).snd B.relativeDimension :=
  B.atlasPureRelativeDimension.2 A.atlas.scheme A.atlas.tautologicalObject
    (A.overlapSwap B)

/-- **The overlap is a common refinement, unconditionally.**  All six geometric facts about the
two projections of `U ×_X V` are now available, so any two atlas dimension presentations of an
algebraic stack admit a common refinement with no hypothesis whatsoever. -/
noncomputable def CommonRefinement.overlap (A B : StackDimensionPresentation X) :
    CommonRefinement A B :=
  CommonRefinement.ofOverlap A B (A.overlap_snd_smooth B) (A.overlap_snd_surjective B)
    (A.overlap_snd_relativeDimension B)

/-- Any two atlas dimension presentations admit a common refinement. -/
theorem nonempty_commonRefinement (A B : StackDimensionPresentation X) :
    Nonempty (CommonRefinement A B) :=
  ⟨CommonRefinement.overlap A B⟩

end StackDimensionPresentation

/-! ## Atlas independence from the scheme-level dimension formula alone -/

/-- **Atlas independence of the corrected dimension.**  The only remaining input is the
scheme-level dimension formula for smooth surjections, together with non-emptiness of the atlas
schemes (which cannot be dropped: over an empty scheme every pure dimension holds vacuously, so
the corrected dimension is not determined). -/
theorem stackDimensionIndependent_of_smoothPureDimensionFormula
    (hF : SmoothPureDimensionFormula.{u}) (X : AlgebraicStack.{u})
    (hne : ∀ A : StackDimensionPresentation X, Nonempty A.atlas.scheme) :
    StackDimensionIndependent X :=
  stackDimensionIndependent_of_commonRefinement hF hne
    StackDimensionPresentation.nonempty_commonRefinement

/-- **The dimension of a stack is computed by any single atlas**, given the scheme-level
dimension formula for smooth surjections and non-emptiness of the atlas schemes. -/
theorem AlgebraicStack.dim_eq_of_smoothPureDimensionFormula
    (hF : SmoothPureDimensionFormula.{u}) {X : AlgebraicStack.{u}}
    (hne : ∀ A : StackDimensionPresentation X, Nonempty A.atlas.scheme)
    (A : StackDimensionPresentation X) :
    X.dim = StackDim.ofInt A.correctedDimension :=
  AlgebraicStack.dim_eq_of_independent
    (stackDimensionIndependent_of_smoothPureDimensionFormula hF X hne) A

/-! ## A local form of the dimension formula

A proof of `SmoothPureDimensionFormula` in full generality is not expected; the realistic
statement is restricted (for instance to schemes locally of finite type over a field).  The
atlas-independence argument only ever applies the formula to the two projections of an overlap,
so it is recorded here with exactly that hypothesis. -/

/-- The scheme-level dimension formula for smooth surjections, for one fixed morphism.  The
global formula `SmoothPureDimensionFormula` is the statement that this holds for every
morphism. -/
def SmoothPureDimensionFormulaAt {W U : Scheme.{u}} (q : W ⟶ U) : Prop :=
  ∀ r a : ℕ, _root_.AlgebraicGeometry.Smooth q → _root_.AlgebraicGeometry.Surjective q →
    SchemeMorphismPureRelativeDimension q r → SchemePureDimension U a →
      SchemePureDimension W (a + r)

/-- The global dimension formula specialises to every single morphism. -/
theorem smoothPureDimensionFormulaAt_of_formula (hF : SmoothPureDimensionFormula.{u})
    {W U : Scheme.{u}} (q : W ⟶ U) : SmoothPureDimensionFormulaAt q :=
  fun r a ↦ hF q r a

/-- The *local* dimension formula for a stack: the scheme-level formula for smooth surjections
is required only for the two projections of the overlap of two atlas dimension presentations of
`X`.  This is what the atlas-independence argument actually consumes. -/
def OverlapDimensionFormula (X : AlgebraicStack.{u}) : Prop :=
  ∀ A B : StackDimensionPresentation X,
    SmoothPureDimensionFormulaAt (A.overlap B).fst ∧
      SmoothPureDimensionFormulaAt (A.overlap B).snd

/-- The global dimension formula implies its local form for every stack. -/
theorem overlapDimensionFormula_of_smoothPureDimensionFormula
    (hF : SmoothPureDimensionFormula.{u}) (X : AlgebraicStack.{u}) :
    OverlapDimensionFormula X :=
  fun A B ↦ ⟨smoothPureDimensionFormulaAt_of_formula hF (A.overlap B).fst,
    smoothPureDimensionFormulaAt_of_formula hF (A.overlap B).snd⟩

/-- **Atlas independence from the local dimension formula.**  Computing the dimension of the
overlap `U ×_X V` through each of its two smooth projections gives
`dim U + r_V = dim V + r_U`, hence `dim U - r_U = dim V - r_V`.  Only the formula for those two
projections is used, so a dimension formula proved in a restricted setting suffices. -/
theorem stackDimensionIndependent_of_overlapDimensionFormula
    {X : AlgebraicStack.{u}} (hF : OverlapDimensionFormula X)
    (hne : ∀ A : StackDimensionPresentation X, Nonempty A.atlas.scheme) :
    StackDimensionIndependent X := by
  intro A B
  obtain ⟨x⟩ := hne A
  obtain ⟨w, -⟩ := (A.overlap_snd_surjective B).surj x
  have hspace : Nonempty (A.overlap B).space := ⟨w⟩
  have h1 : SchemePureDimension (A.overlap B).space
      (A.atlasDimension + B.relativeDimension) :=
    (hF A B).2 B.relativeDimension A.atlasDimension (A.overlap_snd_smooth B)
      (A.overlap_snd_surjective B) (A.overlap_snd_relativeDimension B)
      A.atlasPureDimension
  have h2 : SchemePureDimension (A.overlap B).space
      (B.atlasDimension + A.relativeDimension) :=
    (hF A B).1 A.relativeDimension B.atlasDimension (A.overlap_fst_smooth B)
      (A.overlap_fst_surjective B) (A.overlap_fst_relativeDimension B)
      B.atlasPureDimension
  have hkey := SchemePureDimension.unique hspace h1 h2
  simp only [StackDimensionPresentation.correctedDimension]
  omega

/-- The dimension of a stack is computed by any single atlas, given only the local dimension
formula for the overlaps of its atlases. -/
theorem AlgebraicStack.dim_eq_of_overlapDimensionFormula
    {X : AlgebraicStack.{u}} (hF : OverlapDimensionFormula X)
    (hne : ∀ A : StackDimensionPresentation X, Nonempty A.atlas.scheme)
    (A : StackDimensionPresentation X) :
    X.dim = StackDim.ofInt A.correctedDimension :=
  AlgebraicStack.dim_eq_of_independent
    (stackDimensionIndependent_of_overlapDimensionFormula hF hne) A

end GromovWitten.AlgebraicGeometry
