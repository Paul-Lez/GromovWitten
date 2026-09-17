/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.AtlasRefinement
import GromovWitten.AlgebraicGeometry.Curves.RelativeDimension
import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# The dimension of an algebraic stack

`Stacks.Algebraic` already carries the geometric data of an atlas dimension presentation: a
smooth surjective chart `U ⟶ X` whose scheme is pure of dimension `dim U` and whose base
changes are pure of relative dimension `r`, together with the corrected value
`dim U - r : ℤ`.  This file turns that into a *public* dimension of the stack and studies its
independence of the chosen atlas.

## The public value

`AlgebraicStack.dim X` is the supremum, in `WithBot (WithTop ℤ)`, of the corrected dimensions
of **all** atlas dimension presentations of `X`.  No atlas occurs in the value, and no chart is
chosen; every presentation contributes and `AlgebraicStack.ofInt_correctedDimension_le_dim`
records that contribution.  If the presentations of two atlases agree — the atlas independence
statement `StackDimensionIndependent` of `Stacks.Algebraic` — then
`AlgebraicStack.dim_eq_of_independent` computes the supremum by any single presentation, and
`AlgebraicStack.pureStackDimension_iff_dim_eq` identifies it with `PureStackDimension`.

## Atlas independence

The geometric mechanism is the overlap `U ×_X V` of two atlases.  It maps smoothly and
surjectively to `V` with the relative dimension of `U ⟶ X` and to `U` with the relative
dimension of `V ⟶ X`, so the scheme-level formula

  `dim (source) = dim (target) + (relative dimension)`

for a smooth surjection computes `dim U ×_X V` in two ways and forces
`dim U - r_U = dim V - r_V`.  `StackDimensionPresentation.CommonRefinement` is that overlap as
a witness type (only geometric data, no dimension of `X` is stored), and
`StackDimensionPresentation.correctedDimension_eq_of_commonRefinement` and
`stackDimensionIndependent_of_commonRefinement` carry out the two computations.

## What is still missing

Two inputs are not available in the pinned Mathlib or in this repository, and both are isolated
here rather than assumed silently.

* `SmoothPureDimensionFormula` is the scheme-level dimension formula for a smooth surjection of
  pure relative dimension `r`.  Mathlib has `topologicalKrullDim` and `SmoothOfRelativeDimension`
  but no dimension formula for flat, smooth or syntomic morphisms: the required input is the
  local statement `dim 𝒪_{W,w} = dim 𝒪_{U,q w} + dim 𝒪_{W_{q w},w}` for a flat local
  homomorphism (Stacks 02JS / `Ideal.height` additivity in a flat local extension), which the
  pinned Mathlib does not contain in any form.  Only the two degenerate cases are proved here:
  `schemePureDimension_of_isIso` (`r = 0`, isomorphism) and
  `schemePureDimension_of_surjective_etale` (`r = 0`, étale, in the descent direction), the
  latter from `Curves.pureTopologicalDimension_of_surjective_etale`.
* The *second* projection of the overlap presentation, `U ×_X V ⟶ U`, is not yet known to be
  smooth, surjective and of relative dimension `r_V`.  The first projection `U ×_X V ⟶ V` is
  proved to be smooth, surjective and of relative dimension `r_U` in
  `StackDimensionPresentation.overlap_fst_smooth`, `..._surjective` and
  `..._relativeDimension`.  The 2-categorical form of the missing half *is* proved here:
  `StackHom.twoPullbackFst_hasPureRelativeDimension` says that the first projection of a genuine
  two-pullback of stacks carries the pure relative dimension of the second morphism, and
  `StackTwoPullback.Genuine.fst_hasRepresentableProperty` of `Stacks.AtlasRefinement` says the
  same for smoothness and surjectivity.  What is missing is the *scheme-level* translation: the
  symmetry `A.PullbackPresentation V x_V ≃ B.PullbackPresentation U x_U` exchanging the two legs
  of a chart pullback presentation, which for two *distinct* charts is not in the repository
  (`StackChart.PullbackPresentation.selfSwap` covers only a chart against itself), or
  equivalently a comparison between `StackChart.PullbackPresentation` and
  `StackMorphismPresentation` of the chart morphism.
  `StackDimensionPresentation.CommonRefinement.ofOverlap` takes exactly the three missing facts
  as arguments, so the gap is a single named construction.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

/-! ## Scheme-level pure dimension -/

/-- `SchemePureDimension` is the object property `Curves.PureTopologicalDimension`, so the
whole relative-dimension API of `Curves.RelativeDimension` applies to it. -/
theorem schemePureDimension_iff_pureTopologicalDimension (Z : Scheme.{u}) (d : ℕ) :
    SchemePureDimension Z d ↔ Curves.PureTopologicalDimension d Z :=
  Iff.rfl

/-- `SchemeMorphismPureRelativeDimension` is `Curves.PureRelativeDimension`, so the whole
relative-dimension API of `Curves.RelativeDimension` applies to it. -/
theorem schemeMorphismPureRelativeDimension_iff_pureRelativeDimension
    {W U : Scheme.{u}} (q : W ⟶ U) (d : ℕ) :
    SchemeMorphismPureRelativeDimension q d ↔ Curves.PureRelativeDimension d q :=
  Iff.rfl

/-- Pure dimension of a scheme is transported along an isomorphism. -/
theorem SchemePureDimension.of_iso {Z Z' : Scheme.{u}} (e : Z ≅ Z') {d : ℕ}
    (h : SchemePureDimension Z d) : SchemePureDimension Z' d :=
  Curves.pureTopologicalDimensionOfHomeomorph e.symm.schemeIsoToHomeo h

/-- A nonempty scheme has at most one pure dimension: any point lies in an irreducible
component, whose Krull dimension is both prescribed values. -/
theorem SchemePureDimension.unique {Z : Scheme.{u}} (hZ : Nonempty Z) {d e : ℕ}
    (hd : SchemePureDimension Z d) (he : SchemePureDimension Z e) : d = e := by
  obtain ⟨z⟩ := hZ
  obtain ⟨C, hC, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({z} : Set Z)) isIrreducible_singleton.closure
  have h := (hd C hC).symm.trans (he C hC)
  exact_mod_cast h

/-- An isomorphism is the degenerate `r = 0` case of the smooth dimension formula. -/
theorem schemePureDimension_of_isIso {W U : Scheme.{u}} (q : W ⟶ U) [IsIso q] {a : ℕ}
    (h : SchemePureDimension U a) : SchemePureDimension W a :=
  SchemePureDimension.of_iso (asIso q).symm h

/-- Pure dimension descends along a surjective étale morphism.  This is the `r = 0` case of the
smooth dimension formula, in the direction available from
`Curves.pureTopologicalDimension_of_surjective_etale`. -/
theorem schemePureDimension_of_surjective_etale {W U : Scheme.{u}} (q : W ⟶ U)
    [_root_.AlgebraicGeometry.Etale q] [_root_.AlgebraicGeometry.Surjective q] {a : ℕ}
    (h : SchemePureDimension W a) : SchemePureDimension U a :=
  Curves.pureTopologicalDimension_of_surjective_etale q h

/-- **The scheme-level dimension formula for smooth surjections**, isolated as a proposition
rather than assumed.  A smooth surjection of pure relative dimension `r` onto a scheme pure of
dimension `a` has source pure of dimension `a + r`.  See the module docstring for the precise
commutative-algebra input that the pinned Mathlib is missing. -/
def SmoothPureDimensionFormula : Prop :=
  ∀ {W U : Scheme.{u}} (q : W ⟶ U) (r a : ℕ),
    _root_.AlgebraicGeometry.Smooth q → _root_.AlgebraicGeometry.Surjective q →
      SchemeMorphismPureRelativeDimension q r → SchemePureDimension U a →
        SchemePureDimension W (a + r)

/-! ## Stack dimensions as extended integers -/

/-- Dimensions of algebraic stacks are integers, extended by `⊥` (no atlas at all) and `⊤` (an
unbounded family of atlas dimensions), so that a supremum over all atlases always exists. -/
abbrev StackDim : Type := WithBot (WithTop ℤ)

/-- An integer regarded as a finite stack dimension. -/
def StackDim.ofInt (n : ℤ) : StackDim := ((n : WithTop ℤ) : StackDim)

/-- Distinct integers give distinct stack dimensions. -/
theorem StackDim.ofInt_injective : Function.Injective StackDim.ofInt := by
  intro a b h
  have h' : ((a : WithTop ℤ) : StackDim) = ((b : WithTop ℤ) : StackDim) := h
  exact_mod_cast h'

/-- Two integers give the same stack dimension exactly when they are equal. -/
@[simp]
theorem StackDim.ofInt_inj {a b : ℤ} : StackDim.ofInt a = StackDim.ofInt b ↔ a = b :=
  ⟨fun h ↦ StackDim.ofInt_injective h, fun h ↦ by rw [h]⟩

/-- A finite stack dimension is not `⊥`. -/
@[simp]
theorem StackDim.ofInt_ne_bot (n : ℤ) : StackDim.ofInt n ≠ ⊥ := by
  simp [StackDim.ofInt]

/-- **The dimension of an algebraic stack.**  It is the supremum of the corrected dimensions
`dim U - r` of *all* atlas dimension presentations of `X`; no atlas and no chart occurs in the
value. -/
noncomputable def AlgebraicStack.dim (X : AlgebraicStack.{u}) : StackDim :=
  ⨆ A : StackDimensionPresentation X, StackDim.ofInt A.correctedDimension

/-- Every atlas dimension presentation contributes to the dimension of the stack. -/
theorem AlgebraicStack.ofInt_correctedDimension_le_dim {X : AlgebraicStack.{u}}
    (A : StackDimensionPresentation X) :
    StackDim.ofInt A.correctedDimension ≤ X.dim :=
  le_iSup (fun B : StackDimensionPresentation X ↦ StackDim.ofInt B.correctedDimension) A

/-- A bound valid for every atlas dimension presentation bounds the dimension of the stack. -/
theorem AlgebraicStack.dim_le {X : AlgebraicStack.{u}} {c : StackDim}
    (h : ∀ A : StackDimensionPresentation X, StackDim.ofInt A.correctedDimension ≤ c) :
    X.dim ≤ c :=
  iSup_le h

/-- **Atlas independence computes the dimension.**  If all atlas dimension presentations of `X`
give the same corrected dimension, then that common value *is* the dimension of `X`. -/
theorem AlgebraicStack.dim_eq_of_independent {X : AlgebraicStack.{u}}
    (h : StackDimensionIndependent X) (A : StackDimensionPresentation X) :
    X.dim = StackDim.ofInt A.correctedDimension :=
  le_antisymm (AlgebraicStack.dim_le fun B ↦ le_of_eq (congrArg StackDim.ofInt (h B A)))
    (AlgebraicStack.ofInt_correctedDimension_le_dim A)

/-- Under atlas independence, a certified pure stack dimension is the dimension of the stack. -/
theorem AlgebraicStack.dim_eq_of_pureStackDimension {X : AlgebraicStack.{u}} {d : ℤ}
    (h : StackDimensionIndependent X) (hd : PureStackDimension X d) :
    X.dim = StackDim.ofInt d := by
  obtain ⟨A, hA⟩ := hd
  rw [AlgebraicStack.dim_eq_of_independent h A, hA]

/-- Under atlas independence, pure stack dimension and the public dimension agree. -/
theorem AlgebraicStack.pureStackDimension_iff_dim_eq {X : AlgebraicStack.{u}} {d : ℤ}
    (h : StackDimensionIndependent X) (hne : Nonempty (StackDimensionPresentation X)) :
    PureStackDimension X d ↔ X.dim = StackDim.ofInt d := by
  refine ⟨AlgebraicStack.dim_eq_of_pureStackDimension h, fun hdim ↦ ?_⟩
  obtain ⟨A⟩ := hne
  refine ⟨A, ?_⟩
  have := (AlgebraicStack.dim_eq_of_independent h A).symm.trans hdim
  exact StackDim.ofInt_injective this

/-- The dimension of a stack is `⊥` exactly when it has no atlas dimension presentation at
all. -/
theorem AlgebraicStack.dim_eq_bot_iff {X : AlgebraicStack.{u}} :
    X.dim = ⊥ ↔ IsEmpty (StackDimensionPresentation X) := by
  rw [AlgebraicStack.dim, iSup_eq_bot]
  refine ⟨fun h ↦ ⟨fun A ↦ StackDim.ofInt_ne_bot _ (h A)⟩, fun h A ↦ (h.false A).elim⟩

/-! ## Common refinements of two atlas dimension presentations -/

namespace StackDimensionPresentation

variable {X : AlgebraicStack.{u}}

/-- A common refinement of two atlas dimension presentations: a scheme smoothly and
surjectively covering both atlas schemes, with the two relative dimensions exchanged.
Geometrically it is the overlap `U ×_X V`.  Every field is geometric data about schemes; no
field records a dimension of the stack. -/
structure CommonRefinement (A B : StackDimensionPresentation X) where
  /-- The refining scheme, geometrically `U ×_X V`. -/
  space : Scheme.{u}
  /-- Projection to the scheme of the first atlas. -/
  toFirst : space ⟶ A.atlas.scheme
  /-- Projection to the scheme of the second atlas. -/
  toSecond : space ⟶ B.atlas.scheme
  /-- The first projection is smooth. -/
  toFirst_smooth : _root_.AlgebraicGeometry.Smooth toFirst
  /-- The first projection is surjective. -/
  toFirst_surjective : _root_.AlgebraicGeometry.Surjective toFirst
  /-- Being a base change of the second atlas, the first projection has the relative dimension
  of the second atlas. -/
  toFirst_relativeDimension :
    SchemeMorphismPureRelativeDimension toFirst B.relativeDimension
  /-- The second projection is smooth. -/
  toSecond_smooth : _root_.AlgebraicGeometry.Smooth toSecond
  /-- The second projection is surjective. -/
  toSecond_surjective : _root_.AlgebraicGeometry.Surjective toSecond
  /-- Being a base change of the first atlas, the second projection has the relative dimension
  of the first atlas. -/
  toSecond_relativeDimension :
    SchemeMorphismPureRelativeDimension toSecond A.relativeDimension

namespace CommonRefinement

variable {A B : StackDimensionPresentation X}

/-- A common refinement of two atlases of a nonempty atlas scheme is itself nonempty. -/
theorem nonempty_space (R : CommonRefinement A B) (hA : Nonempty A.atlas.scheme) :
    Nonempty R.space := by
  obtain ⟨x⟩ := hA
  obtain ⟨w, -⟩ := R.toFirst_surjective.surj x
  exact ⟨w⟩

end CommonRefinement

/-- **Atlas independence from a common refinement.**  Computing the dimension of the overlap
`U ×_X V` through each of its two smooth projections gives
`dim U + r_V = dim V + r_U`, hence `dim U - r_U = dim V - r_V`. -/
theorem correctedDimension_eq_of_commonRefinement (hF : SmoothPureDimensionFormula.{u})
    {A B : StackDimensionPresentation X} (R : CommonRefinement A B)
    (hA : Nonempty A.atlas.scheme) :
    A.correctedDimension = B.correctedDimension := by
  have hne : Nonempty R.space := R.nonempty_space hA
  have h1 : SchemePureDimension R.space (A.atlasDimension + B.relativeDimension) :=
    hF R.toFirst B.relativeDimension A.atlasDimension R.toFirst_smooth R.toFirst_surjective
      R.toFirst_relativeDimension A.atlasPureDimension
  have h2 : SchemePureDimension R.space (B.atlasDimension + A.relativeDimension) :=
    hF R.toSecond A.relativeDimension B.atlasDimension R.toSecond_smooth R.toSecond_surjective
      R.toSecond_relativeDimension B.atlasPureDimension
  have hkey := SchemePureDimension.unique hne h1 h2
  simp only [correctedDimension]
  omega

end StackDimensionPresentation

/-- **Atlas independence.**  Given the scheme-level smooth dimension formula and a common
refinement of any two atlas dimension presentations of `X` (whose atlas schemes are nonempty),
the corrected dimension does not depend on the atlas. -/
theorem stackDimensionIndependent_of_commonRefinement {X : AlgebraicStack.{u}}
    (hF : SmoothPureDimensionFormula.{u})
    (hne : ∀ A : StackDimensionPresentation X, Nonempty A.atlas.scheme)
    (hR : ∀ A B : StackDimensionPresentation X,
      Nonempty (StackDimensionPresentation.CommonRefinement A B)) :
    StackDimensionIndependent X := by
  intro A B
  obtain ⟨R⟩ := hR A B
  exact StackDimensionPresentation.correctedDimension_eq_of_commonRefinement hF R (hne A)

/-- Under the hypotheses of `stackDimensionIndependent_of_commonRefinement`, the dimension of
the stack is computed by any single atlas. -/
theorem AlgebraicStack.dim_eq_of_commonRefinement {X : AlgebraicStack.{u}}
    (hF : SmoothPureDimensionFormula.{u})
    (hne : ∀ A : StackDimensionPresentation X, Nonempty A.atlas.scheme)
    (hR : ∀ A B : StackDimensionPresentation X,
      Nonempty (StackDimensionPresentation.CommonRefinement A B))
    (A : StackDimensionPresentation X) :
    X.dim = StackDim.ofInt A.correctedDimension :=
  AlgebraicStack.dim_eq_of_independent
    (stackDimensionIndependent_of_commonRefinement hF hne hR) A

/-! ## The overlap of two atlases -/

/-- The tautological object of a stack over the scheme of one of its charts. -/
noncomputable def StackChart.tautologicalObject {X : FppfStack.{u}} (A : StackChart X) :
    StackFiber X A.scheme :=
  A.obj A.scheme (𝟙 A.scheme)

namespace StackDimensionPresentation

variable {X : AlgebraicStack.{u}}

/-- The overlap `U ×_X V` of the atlases of two dimension presentations, as an actual pullback
presentation of the first chart against the tautological object of the second.  Its existence
is part of representability of the first atlas, not an assumption. -/
noncomputable def overlap (A B : StackDimensionPresentation X) :
    A.atlas.PullbackPresentation B.atlas.scheme B.atlas.tautologicalObject :=
  Classical.choice (A.isSmoothSurjective.1 B.atlas.scheme B.atlas.tautologicalObject)

/-- The projection `U ×_X V ⟶ V` is smooth, because the first atlas is. -/
theorem overlap_fst_smooth (A B : StackDimensionPresentation X) :
    _root_.AlgebraicGeometry.Smooth (A.overlap B).fst :=
  (A.isSmoothSurjective.2 B.atlas.scheme B.atlas.tautologicalObject (A.overlap B)).1

/-- The projection `U ×_X V ⟶ V` is surjective, because the first atlas is. -/
theorem overlap_fst_surjective (A B : StackDimensionPresentation X) :
    _root_.AlgebraicGeometry.Surjective (A.overlap B).fst :=
  (A.isSmoothSurjective.2 B.atlas.scheme B.atlas.tautologicalObject (A.overlap B)).2

/-- The projection `U ×_X V ⟶ V` has the relative dimension of the first atlas, because it is
a base change of it. -/
theorem overlap_fst_relativeDimension (A B : StackDimensionPresentation X) :
    SchemeMorphismPureRelativeDimension (A.overlap B).fst A.relativeDimension :=
  A.atlasPureRelativeDimension.2 B.atlas.scheme B.atlas.tautologicalObject (A.overlap B)

/-- **Assembling a common refinement from the overlap.**  The three hypotheses are exactly the
facts about the second projection `U ×_X V ⟶ U` that the repository does not yet prove; see the
module docstring. -/
noncomputable def CommonRefinement.ofOverlap (A B : StackDimensionPresentation X)
    (hsmooth : _root_.AlgebraicGeometry.Smooth (A.overlap B).snd)
    (hsurj : _root_.AlgebraicGeometry.Surjective (A.overlap B).snd)
    (hdim : SchemeMorphismPureRelativeDimension (A.overlap B).snd B.relativeDimension) :
    CommonRefinement A B where
  space := (A.overlap B).space
  toFirst := (A.overlap B).snd
  toSecond := (A.overlap B).fst
  toFirst_smooth := hsmooth
  toFirst_surjective := hsurj
  toFirst_relativeDimension := hdim
  toSecond_smooth := A.overlap_fst_smooth B
  toSecond_surjective := A.overlap_fst_surjective B
  toSecond_relativeDimension := A.overlap_fst_relativeDimension B

end StackDimensionPresentation

/-! ## The dimension of a scheme, viewed as a stack -/

namespace FppfStack

/-- **The formula for schemes.**  A scheme pure of dimension `d`, regarded as an algebraic
stack, has pure stack dimension `d`: its identity chart is a smooth surjective atlas of
relative dimension zero. -/
theorem pureStackDimension_ofSchemeAlgebraicStack {Z : Scheme.{u}} {d : ℕ}
    (h : SchemePureDimension Z d) :
    PureStackDimension (FppfStack.ofSchemeAlgebraicStack Z) (d : ℤ) := by
  refine ⟨{ atlas := FppfStack.schemeChart Z
            isSmoothSurjective := FppfStack.schemeChart_isSmoothSurjective Z
            atlasDimension := d
            atlasPureDimension := h
            relativeDimension := 0
            atlasPureRelativeDimension :=
              FppfStack.schemeChart_hasPureRelativeDimension_zero Z }, ?_⟩
  simp [StackDimensionPresentation.correctedDimension]

/-- The dimension of a scheme is a lower bound for the dimension of the stack it represents. -/
theorem ofInt_le_dim_ofSchemeAlgebraicStack {Z : Scheme.{u}} {d : ℕ}
    (h : SchemePureDimension Z d) :
    StackDim.ofInt (d : ℤ) ≤ (FppfStack.ofSchemeAlgebraicStack Z).dim := by
  obtain ⟨A, hA⟩ := pureStackDimension_ofSchemeAlgebraicStack h
  rw [← hA]
  exact AlgebraicStack.ofInt_correctedDimension_le_dim A

/-- Under atlas independence, the stack dimension of a scheme is its scheme dimension. -/
theorem dim_ofSchemeAlgebraicStack {Z : Scheme.{u}} {d : ℕ}
    (hind : StackDimensionIndependent (FppfStack.ofSchemeAlgebraicStack Z))
    (h : SchemePureDimension Z d) :
    (FppfStack.ofSchemeAlgebraicStack Z).dim = StackDim.ofInt (d : ℤ) :=
  AlgebraicStack.dim_eq_of_pureStackDimension hind
    (pureStackDimension_ofSchemeAlgebraicStack h)

end FppfStack

/-! ## Smooth-morphism, product and quotient formulas -/

namespace StackDimensionPresentation

/-- **The smooth-morphism formula.**  If an atlas of `X` is a smooth surjective cover of
relative dimension `r` of an atlas of `Y`, and the two atlases have the same relative dimension
over their stacks, then `dim X = dim Y + r`. -/
theorem correctedDimension_of_smoothCover {X Y : AlgebraicStack.{u}}
    (hF : SmoothPureDimensionFormula.{u})
    (A : StackDimensionPresentation X) (B : StackDimensionPresentation Y) (r : ℕ)
    (q : A.atlas.scheme ⟶ B.atlas.scheme)
    (hsmooth : _root_.AlgebraicGeometry.Smooth q)
    (hsurj : _root_.AlgebraicGeometry.Surjective q)
    (hq : SchemeMorphismPureRelativeDimension q r)
    (hrel : A.relativeDimension = B.relativeDimension)
    (hne : Nonempty A.atlas.scheme) :
    A.correctedDimension = B.correctedDimension + r := by
  have h1 : SchemePureDimension A.atlas.scheme (B.atlasDimension + r) :=
    hF q r B.atlasDimension hsmooth hsurj hq B.atlasPureDimension
  have hkey := SchemePureDimension.unique hne A.atlasPureDimension h1
  simp only [correctedDimension, hrel]
  omega

/-- **The product formula.**  A presentation whose atlas is the product of two atlases — its
scheme has the sum of the two dimensions and its relative dimension is the sum of the two
relative dimensions — has the sum of the two corrected dimensions.  This is the sign convention
`dim (X × Y) = dim X + dim Y` in the form available before products of algebraic stacks have
been constructed. -/
theorem correctedDimension_add {X Y Z : AlgebraicStack.{u}}
    (A : StackDimensionPresentation X) (B : StackDimensionPresentation Y)
    (C : StackDimensionPresentation Z)
    (hdim : C.atlasDimension = A.atlasDimension + B.atlasDimension)
    (hrel : C.relativeDimension = A.relativeDimension + B.relativeDimension) :
    C.correctedDimension = A.correctedDimension + B.correctedDimension := by
  simp only [correctedDimension, hdim, hrel]
  push_cast
  ring

/-- **The quotient formula `dim [U/G] = dim U - dim G`.**  For a stack presented by an atlas
whose scheme is pure of dimension `dim U` and whose relative dimension is `dim G` — the case of
the canonical atlas `U ⟶ [U/G]` of a quotient by a smooth group, whose base changes are
`G`-torsors — the corrected dimension is `dim U - dim G`.

The quotient prestack `[U/G]` of `Stacks.QuotientStack` is *not* yet an algebraic stack in this
repository: the block constructing `AlgebraicQuotientPresentation.algebraicStack` is retired
because its algebraicity was supplied as a field.  So the formula is stated for an abstract
atlas of the prescribed relative dimension; once `[U/G]` is constructed as an algebraic stack
with its canonical atlas, this theorem applies to it verbatim. -/
theorem correctedDimension_quotient {X : AlgebraicStack.{u}}
    (A : StackDimensionPresentation X) {u g : ℕ}
    (hU : A.atlasDimension = u) (hG : A.relativeDimension = g) :
    A.correctedDimension = (u : ℤ) - (g : ℤ) := by
  simp [correctedDimension, hU, hG]

end StackDimensionPresentation

/-! ## Pure relative dimension under genuine two-pullbacks

This is the 2-categorical half of the common-refinement argument: both projections of the
two-pullback `U ×_X V` of two atlases carry the relative dimension of the opposite atlas.
Pure relative dimension is not multiplicative — relative dimensions *add* under composition — so
the existing base-change theorem `StackHom.twoPullbackSnd_hasRepresentableProperty`, which
assumes `MorphismProperty.IsMultiplicative`, does not apply.  The composition law below is
therefore stated for three separate properties, which is enough because the only composition
that occurs is with the comparison equivalence, whose presentations are isomorphisms. -/

namespace StackHom

/-- Pure relative dimension of a stack morphism is exactly the representable property attached
to `SchemeMorphismPureRelativeDimension`. -/
theorem hasPureRelativeDimension_iff_hasRepresentableProperty
    {X Y : FppfStack.{u}} (f : StackHom X Y) (d : ℕ) :
    f.HasPureRelativeDimension d ↔
      f.HasRepresentableProperty
        (fun {_ _} q ↦ SchemeMorphismPureRelativeDimension q d) :=
  Iff.rfl

/-- Raw representable properties compose for three possibly different scheme-morphism
properties, as soon as the scheme-level composition law holds. -/
theorem comp_hasRepresentablePropertyRaw_of_comp {X Y Z : FppfStack.{u}}
    {f : StackHom X Y} {g : StackHom Y Z}
    (P Q R : MorphismProperty Scheme.{u})
    (hPQR : ∀ {W V T : Scheme.{u}} (a : W ⟶ V) (b : V ⟶ T), P a → Q b → R (a ≫ b))
    (hf : f.HasRepresentablePropertyRaw P) (hg : g.HasRepresentablePropertyRaw Q) :
    HasRepresentablePropertyRaw (Pseudofunctor.StrongTrans.vcomp f g) R := by
  intro T z
  obtain ⟨⟨p, hp⟩⟩ := hg T z
  obtain ⟨⟨q, hq⟩⟩ := hf p.space p.object
  exact ⟨⟨p.comp q, hPQR q.map p.map hq hp⟩⟩

/-- Representable properties compose for three possibly different scheme-morphism properties;
the two displayed 2-cells are whiskered and composed exactly as in the multiplicative case. -/
theorem comp_hasRepresentableProperty_of_comp {X Y Z : FppfStack.{u}}
    {f : StackHom X Y} {g : StackHom Y Z}
    (P Q R : MorphismProperty Scheme.{u})
    (hPQR : ∀ {W V T : Scheme.{u}} (a : W ⟶ V) (b : V ⟶ T), P a → Q b → R (a ≫ b))
    (hf : f.HasRepresentableProperty P) (hg : g.HasRepresentableProperty Q) :
    HasRepresentableProperty (Pseudofunctor.StrongTrans.vcomp f g) R := by
  obtain ⟨f', ⟨ef⟩, hf'⟩ := hf
  obtain ⟨g', ⟨eg⟩, hg'⟩ := hg
  refine ⟨Pseudofunctor.StrongTrans.vcomp f' g',
    ⟨(ef.whiskerRight g).trans (StackIso2.whiskerLeft f' eg)⟩, ?_⟩
  exact comp_hasRepresentablePropertyRaw_of_comp P Q R hPQR hf' hg'

/-- Precomposing a morphism of pure relative dimension `d` with an isomorphism does not change
the relative dimension, because the scheme-theoretic fibres are homeomorphic. -/
theorem schemeMorphismPureRelativeDimension_comp_isomorphism
    {W V T : Scheme.{u}} (a : W ⟶ V) (b : V ⟶ T) {d : ℕ}
    (ha : MorphismProperty.isomorphisms Scheme.{u} a)
    (hb : SchemeMorphismPureRelativeDimension b d) :
    SchemeMorphismPureRelativeDimension (a ≫ b) d := by
  have : IsIso a := ha
  exact Curves.PureRelativeDimension.precomp_iso (asIso a) b hb

/-- **Base change of pure relative dimension.**  The second projection of every genuine
bicategorical two-pullback inherits the pure relative dimension of the first morphism. -/
theorem twoPullbackSnd_hasPureRelativeDimension {X Y Z : FppfStack.{u}}
    (f : StackHom X Z) (g : StackHom Y Z) (P : StackTwoPullback.Genuine f g) (d : ℕ)
    (hf : f.HasPureRelativeDimension d) : P.snd.HasPureRelativeDimension d := by
  let E := StackTwoPullback.canonicalComparisonEquivalence P
  have hE : E.hom.HasRepresentableProperty (MorphismProperty.isomorphisms Scheme.{u}) :=
    E.hom_hasRepresentableProperty _
  have hcanonical :
      (StackTwoPullback.canonicalGenuine f g).snd.HasRepresentableProperty
        (fun {_ _} q ↦ SchemeMorphismPureRelativeDimension q d) :=
    fiberTwoPullbackSnd_hasRepresentableProperty f g _ hf
  have hcomp := comp_hasRepresentableProperty_of_comp
    (MorphismProperty.isomorphisms Scheme.{u})
    (fun {_ _} q ↦ SchemeMorphismPureRelativeDimension q d)
    (fun {_ _} q ↦ SchemeMorphismPureRelativeDimension q d)
    (fun a b ha hb ↦ schemeMorphismPureRelativeDimension_comp_isomorphism a b ha hb)
    hE hcanonical
  exact (hasRepresentableProperty_congr _
    (StackTwoPullback.canonicalComparisonSndIso P)).mp hcomp

/-- **Base change of pure relative dimension, first projection.**  The first projection of a
genuine two-pullback inherits the pure relative dimension of the second morphism. -/
theorem twoPullbackFst_hasPureRelativeDimension {X Y Z : FppfStack.{u}}
    (f : StackHom X Z) (g : StackHom Y Z) (P : StackTwoPullback.Genuine f g) (d : ℕ)
    (hg : g.HasPureRelativeDimension d) : P.fst.HasPureRelativeDimension d :=
  twoPullbackSnd_hasPureRelativeDimension g f (StackTwoPullback.swap P) d hg

end StackHom

/-- The quotient formula for the public dimension: under atlas independence, a stack with an
atlas of dimension `u` and relative dimension `g` has dimension `u - g`. -/
theorem AlgebraicStack.dim_quotient {X : AlgebraicStack.{u}}
    (hind : StackDimensionIndependent X) (A : StackDimensionPresentation X) {u g : ℕ}
    (hU : A.atlasDimension = u) (hG : A.relativeDimension = g) :
    X.dim = StackDim.ofInt ((u : ℤ) - (g : ℤ)) := by
  rw [AlgebraicStack.dim_eq_of_independent hind A,
    A.correctedDimension_quotient hU hG]

end GromovWitten.AlgebraicGeometry
