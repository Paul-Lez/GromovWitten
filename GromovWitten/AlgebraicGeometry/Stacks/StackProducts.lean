/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.AtlasRefinement
import GromovWitten.AlgebraicGeometry.Stacks.Inertia

/-!
# Binary products of stacks, pasting of two-pullbacks, and the diagonal of a chart

`Stacks.Inertia` constructs the terminal fppf stack, the absolute self product `X × X` as the
canonical genuine two-pullback of `X ⟶ *` with itself, and the diagonal
`stackDiagonal X : X ⟶ X × X`.  Its module docstring records two obstructions to the
Deligne--Mumford diagonal criterion: there are no *products of stack morphisms* and no *pasting
calculus* for genuine two-pullbacks.  This file supplies the first, supplies the second in the
form needed for representable properties, constructs the diagonal square of a chart, and reduces
one direction of the criterion to a single explicitly stated hypothesis.

## Binary products

`stackProduct X Y` is the canonical genuine two-pullback of the two structural morphisms to
`terminalStack`; `stackProduct X X` is *definitionally* the `stackSelfProduct X` used by
`stackDiagonal` (`stackProduct_self`).  Because every fibre of the terminal stack is a one-point
discrete groupoid, the comparison face of the bicategorical universal property is automatic
(`stackProduct_coneLiftClassifies`), so the product has a purely one-dimensional universal
property:

* `stackPair p q : T ⟶ X × Y` with `stackPair_fst`, `stackPair_snd`;
* `stackPair_unique`: *any* morphism whose two projections are 2-isomorphic to `p` and `q` is
  2-isomorphic to `stackPair p q` -- no compatibility has to be supplied;
* `stackProd_ext`, `stackPair_fst_snd`, `stackPair_comp`;
* `stackProdMap f g : X × Y ⟶ X' × Y'` with `stackProdMap_fst`, `stackProdMap_snd` and
  `stackPair_comp_prodMap`;
* `stackDiagonal_iso_pair`, `stackDiagonal_fst`, `stackDiagonal_snd`: the already-constructed
  diagonal is the pairing of the identity with itself;
* `stackProdObj`, `stackProdObjIso`, `stackProdObj_self`, `stackPullback_stackProdObj`: the
  objectwise description of the fibres of a product stack.

## Pasting

`StackTwoPullback.Genuine.pastedSnd_hasRepresentableProperty` and
`pastedFst_hasRepresentableProperty` are the pasting lemma **for representable properties**: two
genuine squares pasted along a common edge transfer every multiplicative representable
scheme-morphism property from the far edge to the near one, by two applications of the
base-change theorem of `Stacks.GenuineBaseChange`.  What is *not* proved is that the pasted
rectangle is itself a genuine two-pullback of the composite cospan: that needs the fibrewise
pasting equivalence of `CategoricalPullback`s together with its compatibility with the composed
comparison 2-cell, which is a substantial separate construction.

## The diagonal square of a chart

For `u : U ⟶ X`, `selfOverlap u` is the canonical genuine two-pullback `U ×_X U`, and
`selfOverlapSquare u` proves that the square

  `U ×_X U ⟶ X`, `U ×_X U ⟶ U × U`, `X ⟶ X × X`, `U × U ⟶ X × X`

2-commutes: this is `stackProd_ext` applied to the two projections, with the comparison 2-cell of
the self-overlap entering exactly once.  Both comparison morphisms between `U ×_X U` and the
canonical base change `X ×_{X × X} (U × U)` are constructed
(`selfOverlapToDiagonalBaseChange`, with its two projection 2-cells, and
`diagonalBaseChangeToSelfOverlap`).  **They are not proved to be mutually inverse**, so the
square is not established to be 2-cartesian; that would need the two `ConeLiftClassifies`
round-trip computations.

## The Deligne--Mumford diagonal criterion

`StackChart.exists_etaleCover_pair` is unconditional: over an etale surjective chart, any pair of
objects of `X(T)` becomes a pair of chart objects after an etale surjective base change
`S ⟶ T` (the composite of the two chart base changes).
`StackHom.hasRepresentablePropertyRaw_of_coverIso` refines the descent theorem of
`Stacks.PropertiesDescent` so that the presentation over the cover may be given at any object
isomorphic to the pulled-back one.  Together they give
`stackDiagonal_unramified_of_etaleAtlas`, which derives `(stackDiagonal X).Unramified` from two
hypotheses:

* `hrep : (stackDiagonal X).IsRepresentable`.  This is *not* available from
  `AlgebraicStack.diagonal_representable`, which uses the other encoding
  (`HasRepresentableDiagonal`, isomorphism sheaves); comparing the two encodings is the first
  obstruction listed in `Stacks.Inertia` and is still open.
* `hIsom : A.HasUnramifiedIsom`, the isomorphism-scheme hypothesis: for all `a b : S ⟶ U` the
  base change of the diagonal by the pair of chart objects `(u a, u b)` is representable by a
  scheme unramified over `S`.  Geometrically this is 2-cartesianness of `selfOverlapSquare`
  together with the scheme-level cancellation for unramified morphisms.

`DeligneMumfordStack.stackDiagonal_unramified` and
`DeligneMumfordStack.inertiaProjection_unramified` package the conclusion for a
Deligne--Mumford stack.  The converse direction of the criterion (an unramified diagonal
produces an etale atlas) is untouched: it needs etale slices, for which there is no input.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

/-! ## The binary product of two stacks -/

/-- **The binary product `X × Y` of two fppf stacks**, constructed as the canonical genuine
bicategorical two-pullback of the two structural morphisms to the terminal stack.  Nothing is
assumed: the terminal stack, the canonical two-pullback and its bilimit property are all already
constructed in `Stacks.Inertia` and `Stacks.TwoPullbackBilimit`. -/
noncomputable def stackProduct (X Y : FppfStack.{u}) :
    StackTwoPullback.Genuine X.toTerminal Y.toTerminal :=
  StackTwoPullback.canonicalGenuine X.toTerminal Y.toTerminal

/-- The self product used by `stackDiagonal` is the binary product of a stack with itself. -/
theorem stackProduct_self (X : FppfStack.{u}) :
    stackProduct X X = stackSelfProduct X := rfl

/-- The first projection `X × Y ⟶ X`. -/
noncomputable abbrev stackProdFst (X Y : FppfStack.{u}) :
    StackHom (stackProduct X Y).pullback X :=
  (stackProduct X Y).fst

/-- The second projection `X × Y ⟶ Y`. -/
noncomputable abbrev stackProdSnd (X Y : FppfStack.{u}) :
    StackHom (stackProduct X Y).pullback Y :=
  (stackProduct X Y).snd

/-- **Every comparison face over the terminal stack holds automatically.**  The fibres of the
terminal stack are one-point discrete groupoids, so the equation of 2-cells required by
`StackTwoPullback.ConeLiftClassifies` is an equation between arrows of a discrete one-point
groupoid.  This is what makes the universal property of the product purely one-dimensional. -/
theorem stackProduct_coneLiftClassifies {T X Y : FppfStack.{u}}
    (c : StackTwoPullback.Cone (f := X.toTerminal) (g := Y.toTerminal) T)
    (h : StackHom T (stackProduct X Y).pullback)
    (hfst : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (stackProdFst X Y)) c.fst)
    (hsnd : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (stackProdSnd X Y)) c.snd) :
    StackTwoPullback.ConeLiftClassifies (stackProduct X Y).toStackTwoPullback c h
      hfst hsnd := by
  intro U x
  apply Iso.ext
  exact (terminalStack_hom_subsingleton _ _).elim _ _

/-- The cone attached to a pair of stack morphisms out of a common source.  Its comparison
2-cell is the canonical one between the two induced morphisms to the terminal stack. -/
noncomputable def stackPairCone {T X Y : FppfStack.{u}}
    (p : StackHom T X) (q : StackHom T Y) :
    StackTwoPullback.Cone (f := X.toTerminal) (g := Y.toTerminal) T where
  fst := p
  snd := q
  comparison := FppfStack.terminalIso2 _ _

/-- **The pairing `⟨p, q⟩ : T ⟶ X × Y` of two stack morphisms.** -/
noncomputable def stackPair {T X Y : FppfStack.{u}}
    (p : StackHom T X) (q : StackHom T Y) :
    StackHom T (stackProduct X Y).pullback :=
  (stackProduct X Y).bilimit.lift (stackPairCone p q)

/-- The first projection of a pairing is the first component. -/
noncomputable def stackPair_fst {T X Y : FppfStack.{u}}
    (p : StackHom T X) (q : StackHom T Y) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp (stackPair p q) (stackProdFst X Y)) p :=
  (stackProduct X Y).bilimit.lift_fst (stackPairCone p q)

/-- The second projection of a pairing is the second component. -/
noncomputable def stackPair_snd {T X Y : FppfStack.{u}}
    (p : StackHom T X) (q : StackHom T Y) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp (stackPair p q) (stackProdSnd X Y)) q :=
  (stackProduct X Y).bilimit.lift_snd (stackPairCone p q)

/-- **The universal property of the product, in its one-dimensional form.**  Any morphism into
`X × Y` whose two projections are 2-isomorphic to `p` and `q` is itself 2-isomorphic to the
pairing `⟨p, q⟩`.  No compatibility between the two 2-cells has to be supplied, because the
comparison face over the terminal stack is automatic. -/
noncomputable def stackPair_unique {T X Y : FppfStack.{u}}
    {p : StackHom T X} {q : StackHom T Y} (h : StackHom T (stackProduct X Y).pullback)
    (hfst : StackIso2 (Pseudofunctor.StrongTrans.vcomp h (stackProdFst X Y)) p)
    (hsnd : StackIso2 (Pseudofunctor.StrongTrans.vcomp h (stackProdSnd X Y)) q) :
    StackIso2 h (stackPair p q) :=
  (stackProduct X Y).bilimit.lift_unique (stackPairCone p q) h hfst hsnd
    (stackProduct_coneLiftClassifies _ h hfst hsnd)

/-- **Two morphisms into a product with 2-isomorphic projections are 2-isomorphic.** -/
noncomputable def stackProd_ext {T X Y : FppfStack.{u}}
    (h k : StackHom T (stackProduct X Y).pullback)
    (hfst : StackIso2 (Pseudofunctor.StrongTrans.vcomp h (stackProdFst X Y))
      (Pseudofunctor.StrongTrans.vcomp k (stackProdFst X Y)))
    (hsnd : StackIso2 (Pseudofunctor.StrongTrans.vcomp h (stackProdSnd X Y))
      (Pseudofunctor.StrongTrans.vcomp k (stackProdSnd X Y))) :
    StackIso2 h k :=
  (stackPair_unique h hfst hsnd).trans
    (stackPair_unique k (StackIso2.refl _) (StackIso2.refl _)).symm

/-- The identity of a product is the pairing of its two projections. -/
noncomputable def stackPair_fst_snd (X Y : FppfStack.{u}) :
    StackIso2 (Pseudofunctor.StrongTrans.id (stackProduct X Y).pullback.toPseudofunctor)
      (stackPair (stackProdFst X Y) (stackProdSnd X Y)) :=
  stackPair_unique _ (StackIso2.leftUnitor _) (StackIso2.leftUnitor _)

/-- **Precomposition of a pairing.**  Pairing commutes with composition on the source. -/
noncomputable def stackPair_comp {S T X Y : FppfStack.{u}}
    (r : StackHom S T) (p : StackHom T X) (q : StackHom T Y) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp r (stackPair p q))
      (stackPair (Pseudofunctor.StrongTrans.vcomp r p)
        (Pseudofunctor.StrongTrans.vcomp r q)) :=
  stackPair_unique _
    ((StackIso2.associator r (stackPair p q) (stackProdFst X Y)).trans
      (StackIso2.whiskerLeft r (stackPair_fst p q)))
    ((StackIso2.associator r (stackPair p q) (stackProdSnd X Y)).trans
      (StackIso2.whiskerLeft r (stackPair_snd p q)))

/-! ## Products of stack morphisms -/

/-- **The product `f × g : X × Y ⟶ X' × Y'` of two stack morphisms.** -/
noncomputable def stackProdMap {X Y X' Y' : FppfStack.{u}}
    (f : StackHom X X') (g : StackHom Y Y') :
    StackHom (stackProduct X Y).pullback (stackProduct X' Y').pullback :=
  stackPair (Pseudofunctor.StrongTrans.vcomp (stackProdFst X Y) f)
    (Pseudofunctor.StrongTrans.vcomp (stackProdSnd X Y) g)

/-- The first projection of a product morphism. -/
noncomputable def stackProdMap_fst {X Y X' Y' : FppfStack.{u}}
    (f : StackHom X X') (g : StackHom Y Y') :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (stackProdMap f g) (stackProdFst X' Y'))
      (Pseudofunctor.StrongTrans.vcomp (stackProdFst X Y) f) :=
  stackPair_fst _ _

/-- The second projection of a product morphism. -/
noncomputable def stackProdMap_snd {X Y X' Y' : FppfStack.{u}}
    (f : StackHom X X') (g : StackHom Y Y') :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (stackProdMap f g) (stackProdSnd X' Y'))
      (Pseudofunctor.StrongTrans.vcomp (stackProdSnd X Y) g) :=
  stackPair_snd _ _

/-- **Compatibility of pairing with products of morphisms**: `⟨p, q⟩ ≫ (f × g) ≅ ⟨p ≫ f,
q ≫ g⟩`.  This is the calculation that expresses a base change along `f × g` in terms of the
two components. -/
noncomputable def stackPair_comp_prodMap {T X Y X' Y' : FppfStack.{u}}
    (p : StackHom T X) (q : StackHom T Y)
    (f : StackHom X X') (g : StackHom Y Y') :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp (stackPair p q) (stackProdMap f g))
      (stackPair (Pseudofunctor.StrongTrans.vcomp p f)
        (Pseudofunctor.StrongTrans.vcomp q g)) :=
  stackPair_unique _
    (((StackIso2.associator (stackPair p q) (stackProdMap f g)
        (stackProdFst X' Y')).trans
      (StackIso2.whiskerLeft (stackPair p q) (stackProdMap_fst f g))).trans
      (((StackIso2.associator (stackPair p q) (stackProdFst X Y) f).symm.trans
        (StackIso2.whiskerRight (stackPair_fst p q) f))))
    (((StackIso2.associator (stackPair p q) (stackProdMap f g)
        (stackProdSnd X' Y')).trans
      (StackIso2.whiskerLeft (stackPair p q) (stackProdMap_snd f g))).trans
      (((StackIso2.associator (stackPair p q) (stackProdSnd X Y) g).symm.trans
        (StackIso2.whiskerRight (stackPair_snd p q) g))))

/-! ## The diagonal as a pairing -/

/-- **The diagonal is the pairing of the identity with itself.**  This identifies the
already-constructed `stackDiagonal` with the product-theoretic diagonal. -/
noncomputable def stackDiagonal_iso_pair (X : FppfStack.{u}) :
    StackIso2 (stackDiagonal X)
      (stackPair (Pseudofunctor.StrongTrans.id X.toPseudofunctor)
        (Pseudofunctor.StrongTrans.id X.toPseudofunctor)) :=
  stackPair_unique _ (stackSelfProduct X).relativeDiagonalFstComparison
    (stackSelfProduct X).relativeDiagonalSndComparison

/-- The first projection of the diagonal is the identity. -/
noncomputable def stackDiagonal_fst (X : FppfStack.{u}) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp (stackDiagonal X) (stackProdFst X X))
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor) :=
  (stackSelfProduct X).relativeDiagonalFstComparison

/-- The second projection of the diagonal is the identity. -/
noncomputable def stackDiagonal_snd (X : FppfStack.{u}) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp (stackDiagonal X) (stackProdSnd X X))
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor) :=
  (stackSelfProduct X).relativeDiagonalSndComparison

/-! ## Objects of a product stack -/

/-- The object of the product stack `X × Y` attached to a pair of objects in the fibres of `X`
and of `Y` over the same test scheme.  Its comparison isomorphism lives in a fibre of the
terminal stack and is therefore forced. -/
noncomputable def stackProdObj {X Y : FppfStack.{u}} {T : Scheme.{u}}
    (x : StackFiber X T) (y : StackFiber Y T) :
    StackFiber (stackProduct X Y).pullback T :=
  { fst := x, snd := y, iso := Iso.refl _ }

/-- An isomorphism of product objects built from isomorphisms of the two components. -/
noncomputable def stackProdObjIso {X Y : FppfStack.{u}} {T : Scheme.{u}}
    {x x' : StackFiber X T} {y y' : StackFiber Y T}
    (α : x ≅ x') (β : y ≅ y') :
    stackProdObj x y ≅ stackProdObj x' y' :=
  CategoricalPullback.mkIso α β ((terminalStack_hom_subsingleton _ _).elim _ _)

/-- Every object of a product stack is canonically isomorphic to the product object of its two
components: the third component of a product object is determined. -/
noncomputable def stackProdObj_self {X Y : FppfStack.{u}} {T : Scheme.{u}}
    (p : StackFiber (stackProduct X Y).pullback T) :
    stackProdObj (CategoricalPullback.fst p) (CategoricalPullback.snd p) ≅ p :=
  CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _)
    ((terminalStack_hom_subsingleton _ _).elim _ _)

/-- Pulling back a product object along a scheme morphism is the product of the pulled-back
components. -/
noncomputable def stackPullback_stackProdObj {X Y : FppfStack.{u}} {S T : Scheme.{u}}
    (l : S ⟶ T) (x : StackFiber X T) (y : StackFiber Y T) :
    stackProdObj ((stackPullback X l).obj x) ((stackPullback Y l).obj y) ≅
      (stackPullback (stackProduct X Y).pullback l).obj (stackProdObj x y) :=
  CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _)
    ((terminalStack_hom_subsingleton _ _).elim _ _)

/-! ## Pasting of genuine two-pullbacks, for representable properties -/

namespace StackTwoPullback.Genuine

/-- **Pasting of two genuine two-pullback squares, second projection.**  If `P` is a genuine
two-pullback of `f` along `g`, and `Q` is a genuine two-pullback of the resulting projection
`P.snd` along `h`, then the second projection of `Q` — which is the second projection of the
pasted rectangle over `f` and `h ≫ g` — inherits every multiplicative representable
scheme-morphism property of `f`.

Only the transfer of properties is proved; the pasted rectangle is *not* identified here with a
genuine two-pullback of the composite `h ≫ g`, which would require the fibrewise pasting
equivalence of categorical pullbacks together with its compatibility with the composed
comparison 2-cell. -/
theorem pastedSnd_hasRepresentableProperty {X Y Z W : FppfStack.{u}}
    {f : StackHom X Z} {g : StackHom Y Z} (P : Genuine f g)
    {h : StackHom W Y} (Q : Genuine P.snd h)
    (R : MorphismProperty Scheme.{u}) [R.IsMultiplicative]
    (hf : f.HasRepresentableProperty R) :
    Q.snd.HasRepresentableProperty R :=
  Q.snd_hasRepresentableProperty R (P.snd_hasRepresentableProperty R hf)

/-- **Pasting of two genuine two-pullback squares, first projection.** -/
theorem pastedFst_hasRepresentableProperty {X Y Z W : FppfStack.{u}}
    {f : StackHom X Z} {g : StackHom Y Z} (P : Genuine f g)
    {h : StackHom W X} (Q : Genuine h P.fst)
    (R : MorphismProperty Scheme.{u}) [R.IsMultiplicative]
    (hg : g.HasRepresentableProperty R) :
    Q.fst.HasRepresentableProperty R :=
  Q.fst_hasRepresentableProperty R (P.fst_hasRepresentableProperty R hg)

/-- **Cancellation.**  If the outer projection of a pasted rectangle has a multiplicative
representable property and the intermediate square is genuine, then the inner projection has it
too: this is the form of cancellation used when a base change is computed in two steps. -/
theorem pastedSnd_hasRepresentableProperty_of_middle {X Y Z W : FppfStack.{u}}
    {f : StackHom X Z} {g : StackHom Y Z} (P : Genuine f g)
    {h : StackHom W Y} (Q : Genuine P.snd h)
    (R : MorphismProperty Scheme.{u}) [R.IsMultiplicative]
    (hP : P.snd.HasRepresentableProperty R) :
    Q.snd.HasRepresentableProperty R :=
  Q.snd_hasRepresentableProperty R hP

end StackTwoPullback.Genuine

/-! ## The self-overlap of a chart over the diagonal square -/

/-- The self-overlap `U ×_X U` of a stack morphism, as the canonical genuine two-pullback. -/
noncomputable abbrev selfOverlap {X U : FppfStack.{u}} (u : StackHom U X) :
    StackTwoPullback.Genuine u u :=
  StackTwoPullback.canonicalGenuine u u

/-- The structural morphism `U ×_X U ⟶ X`. -/
noncomputable abbrev selfOverlapToBase {X U : FppfStack.{u}} (u : StackHom U X) :
    StackHom (selfOverlap u).pullback X :=
  Pseudofunctor.StrongTrans.vcomp (selfOverlap u).fst u

/-- The morphism `U ×_X U ⟶ U × U` given by the two projections of the self-overlap. -/
noncomputable abbrev selfOverlapToProduct {X U : FppfStack.{u}} (u : StackHom U X) :
    StackHom (selfOverlap u).pullback (stackProduct U U).pullback :=
  stackPair (selfOverlap u).fst (selfOverlap u).snd

/-- The first projection of the left-hand composite of the diagonal square. -/
noncomputable def selfOverlapSquareLeftFst {X U : FppfStack.{u}} (u : StackHom U X) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (selfOverlapToBase u) (stackDiagonal X))
        (stackProdFst X X))
      (selfOverlapToBase u) :=
  ((StackIso2.associator (selfOverlapToBase u) (stackDiagonal X)
      (stackProdFst X X)).trans
    (StackIso2.whiskerLeft (selfOverlapToBase u) (stackDiagonal_fst X))).trans
    (StackIso2.rightUnitor (selfOverlapToBase u))

/-- The second projection of the left-hand composite of the diagonal square. -/
noncomputable def selfOverlapSquareLeftSnd {X U : FppfStack.{u}} (u : StackHom U X) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (selfOverlapToBase u) (stackDiagonal X))
        (stackProdSnd X X))
      (selfOverlapToBase u) :=
  ((StackIso2.associator (selfOverlapToBase u) (stackDiagonal X)
      (stackProdSnd X X)).trans
    (StackIso2.whiskerLeft (selfOverlapToBase u) (stackDiagonal_snd X))).trans
    (StackIso2.rightUnitor (selfOverlapToBase u))

/-- The first projection of the right-hand composite of the diagonal square. -/
noncomputable def selfOverlapSquareRightFst {X U : FppfStack.{u}} (u : StackHom U X) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (selfOverlapToProduct u) (stackProdMap u u))
        (stackProdFst X X))
      (selfOverlapToBase u) :=
  (((StackIso2.associator (selfOverlapToProduct u) (stackProdMap u u)
      (stackProdFst X X)).trans
    (StackIso2.whiskerLeft (selfOverlapToProduct u) (stackProdMap_fst u u))).trans
    (StackIso2.associator (selfOverlapToProduct u) (stackProdFst U U) u).symm).trans
    (StackIso2.whiskerRight (stackPair_fst (selfOverlap u).fst (selfOverlap u).snd) u)

/-- The second projection of the right-hand composite of the diagonal square. -/
noncomputable def selfOverlapSquareRightSnd {X U : FppfStack.{u}} (u : StackHom U X) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (selfOverlapToProduct u) (stackProdMap u u))
        (stackProdSnd X X))
      (Pseudofunctor.StrongTrans.vcomp (selfOverlap u).snd u) :=
  (((StackIso2.associator (selfOverlapToProduct u) (stackProdMap u u)
      (stackProdSnd X X)).trans
    (StackIso2.whiskerLeft (selfOverlapToProduct u) (stackProdMap_snd u u))).trans
    (StackIso2.associator (selfOverlapToProduct u) (stackProdSnd U U) u).symm).trans
    (StackIso2.whiskerRight (stackPair_snd (selfOverlap u).fst (selfOverlap u).snd) u)

/-- **The self-overlap square over the diagonal 2-commutes.**  The composite
`U ×_X U ⟶ X ⟶ X × X` is 2-isomorphic to `U ×_X U ⟶ U × U ⟶ X × X`; the only input beyond the
product calculus is the comparison 2-cell of the self-overlap. -/
noncomputable def selfOverlapSquare {X U : FppfStack.{u}} (u : StackHom U X) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (selfOverlapToBase u) (stackDiagonal X))
      (Pseudofunctor.StrongTrans.vcomp (selfOverlapToProduct u) (stackProdMap u u)) :=
  stackProd_ext _ _
    ((selfOverlapSquareLeftFst u).trans (selfOverlapSquareRightFst u).symm)
    (((selfOverlapSquareLeftSnd u).trans (selfOverlap u).comparison).trans
      (selfOverlapSquareRightSnd u).symm)

/-- The self-overlap square, regarded as a cone over the cospan defining the base change of the
diagonal along `u × u`. -/
noncomputable def selfOverlapDiagonalCone {X U : FppfStack.{u}} (u : StackHom U X) :
    StackTwoPullback.Cone (f := stackDiagonal X) (g := stackProdMap u u)
      (selfOverlap u).pullback where
  fst := selfOverlapToBase u
  snd := selfOverlapToProduct u
  comparison := selfOverlapSquare u

/-- **The canonical comparison `U ×_X U ⟶ X ×_{X × X} (U × U)`.**  It is the lift of the
self-overlap square through the bicategorical universal property of the canonical base change of
the diagonal along `u × u`.  Whether it is an equivalence — that is, whether the self-overlap
square is 2-cartesian — is exactly the statement that the repository still lacks. -/
noncomputable def selfOverlapToDiagonalBaseChange {X U : FppfStack.{u}} (u : StackHom U X) :
    StackHom (selfOverlap u).pullback
      (StackTwoPullback.canonicalGenuine (stackDiagonal X)
        (stackProdMap u u)).pullback :=
  (StackTwoPullback.canonicalGenuine (stackDiagonal X)
    (stackProdMap u u)).bilimit.lift (selfOverlapDiagonalCone u)

/-- The comparison morphism is compatible with the projections to `X`. -/
noncomputable def selfOverlapToDiagonalBaseChange_fst {X U : FppfStack.{u}}
    (u : StackHom U X) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (selfOverlapToDiagonalBaseChange u)
        (StackTwoPullback.canonicalGenuine (stackDiagonal X) (stackProdMap u u)).fst)
      (selfOverlapToBase u) :=
  (StackTwoPullback.canonicalGenuine (stackDiagonal X)
    (stackProdMap u u)).bilimit.lift_fst (selfOverlapDiagonalCone u)

/-- The comparison morphism is compatible with the projections to `U × U`. -/
noncomputable def selfOverlapToDiagonalBaseChange_snd {X U : FppfStack.{u}}
    (u : StackHom U X) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (selfOverlapToDiagonalBaseChange u)
        (StackTwoPullback.canonicalGenuine (stackDiagonal X) (stackProdMap u u)).snd)
      (selfOverlapToProduct u) :=
  (StackTwoPullback.canonicalGenuine (stackDiagonal X)
    (stackProdMap u u)).bilimit.lift_snd (selfOverlapDiagonalCone u)

/-- The first leg of the comparison cell available on the base change of the diagonal. -/
noncomputable def diagonalBaseChangeFstIso {X U : FppfStack.{u}} (u : StackHom U X)
    (P : StackTwoPullback.Genuine (stackDiagonal X) (stackProdMap u u)) :
    StackIso2 P.fst
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp P.snd (stackProdFst U U)) u) :=
  ((((StackIso2.associator P.fst (stackDiagonal X) (stackProdFst X X)).trans
      (StackIso2.whiskerLeft P.fst (stackDiagonal_fst X))).trans
    (StackIso2.rightUnitor P.fst)).symm.trans
      (StackIso2.whiskerRight P.comparison (stackProdFst X X))).trans
    ((((StackIso2.associator P.snd (stackProdMap u u) (stackProdFst X X)).trans
        (StackIso2.whiskerLeft P.snd (stackProdMap_fst u u))).trans
      (StackIso2.associator P.snd (stackProdFst U U) u).symm))

/-- The second leg of the comparison cell available on the base change of the diagonal. -/
noncomputable def diagonalBaseChangeSndIso {X U : FppfStack.{u}} (u : StackHom U X)
    (P : StackTwoPullback.Genuine (stackDiagonal X) (stackProdMap u u)) :
    StackIso2 P.fst
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp P.snd (stackProdSnd U U)) u) :=
  ((((StackIso2.associator P.fst (stackDiagonal X) (stackProdSnd X X)).trans
      (StackIso2.whiskerLeft P.fst (stackDiagonal_snd X))).trans
    (StackIso2.rightUnitor P.fst)).symm.trans
      (StackIso2.whiskerRight P.comparison (stackProdSnd X X))).trans
    ((((StackIso2.associator P.snd (stackProdMap u u) (stackProdSnd X X)).trans
        (StackIso2.whiskerLeft P.snd (stackProdMap_snd u u))).trans
      (StackIso2.associator P.snd (stackProdSnd U U) u).symm))

/-- **The comparison morphism in the opposite direction**, `X ×_{X × X} (U × U) ⟶ U ×_X U`.
The two projections of the base change into `U` are identified after composition with `u`, so
they form a cone over the self-overlap cospan. -/
noncomputable def diagonalBaseChangeToSelfOverlap {X U : FppfStack.{u}} (u : StackHom U X)
    (P : StackTwoPullback.Genuine (stackDiagonal X) (stackProdMap u u)) :
    StackHom P.pullback (selfOverlap u).pullback :=
  (selfOverlap u).bilimit.lift
    { fst := Pseudofunctor.StrongTrans.vcomp P.snd (stackProdFst U U)
      snd := Pseudofunctor.StrongTrans.vcomp P.snd (stackProdSnd U U)
      comparison := (diagonalBaseChangeFstIso u P).symm.trans
        (diagonalBaseChangeSndIso u P) }

/-- **Base change of the diagonal along `u × u`.**  The second projection of any genuine
two-pullback of the diagonal along `u × u` inherits every multiplicative representable property
of the diagonal.  Combined with 2-cartesianness of `selfOverlapSquare` this is the statement that
`U ×_X U ⟶ U × U` is unramified whenever the diagonal is. -/
theorem diagonalBaseChange_hasRepresentableProperty {X U : FppfStack.{u}} (u : StackHom U X)
    (P : StackTwoPullback.Genuine (stackDiagonal X) (stackProdMap u u))
    (R : MorphismProperty Scheme.{u}) [R.IsMultiplicative]
    (h : (stackDiagonal X).HasRepresentableProperty R) :
    P.snd.HasRepresentableProperty R :=
  P.snd_hasRepresentableProperty R h

/-! ## Charts: lifting a pair of objects through an etale atlas -/

/-- **Every pair of objects over a test scheme is induced by a chart after an etale surjective
base change.**  The cover is the composite of two chart base changes, one for each object. -/
theorem StackChart.exists_etaleCover_pair {X : FppfStack.{u}} (A : StackChart X)
    (hA : A.IsEtaleSurjective) (T : Scheme.{u}) (x y : StackFiber X T) :
    ∃ (S : Scheme.{u}) (base : S ⟶ T) (a b : S ⟶ A.scheme),
      _root_.AlgebraicGeometry.Etale base ∧
        _root_.AlgebraicGeometry.Surjective base ∧
        Nonempty (A.obj S a ≅ (stackPullback X base).obj x) ∧
        Nonempty (A.obj S b ≅ (stackPullback X base).obj y) := by
  obtain ⟨P₁⟩ := hA.1 T x
  have h₁ := hA.2 T x P₁
  obtain ⟨P₂⟩ := hA.1 P₁.space ((stackPullback X P₁.fst).obj y)
  have h₂ := hA.2 P₁.space ((stackPullback X P₁.fst).obj y) P₂
  refine ⟨P₂.space, P₂.fst ≫ P₁.fst, P₂.fst ≫ P₁.snd, P₂.snd, ?_, ?_, ⟨?_⟩, ⟨?_⟩⟩
  · have e2 : _root_.AlgebraicGeometry.Etale P₂.fst := h₂.1
    have e1 : _root_.AlgebraicGeometry.Etale P₁.fst := h₁.1
    infer_instance
  · have s2 : _root_.AlgebraicGeometry.Surjective P₂.fst := h₂.2
    have s1 : _root_.AlgebraicGeometry.Surjective P₁.fst := h₁.2
    infer_instance
  · exact ((A.objPullbackIso P₂.fst P₁.snd).trans
      ((stackPullback X P₂.fst).mapIso P₁.comparison)).trans
      (stackPullbackCompIso X P₂.fst P₁.fst x)
  · exact P₂.comparison.trans (stackPullbackCompIso X P₂.fst P₁.fst y)

/-! ## The Deligne--Mumford diagonal criterion -/

/-- **Descent for representable properties along a cover, up to an isomorphism of the test
object.**  This refines `StackHom.hasRepresentablePropertyRaw_of_cover` by allowing the
presentation over the cover to be given at any object isomorphic to the pulled-back one, which
is what a chart-induced object provides. -/
theorem StackHom.hasRepresentablePropertyRaw_of_coverIso {X Y : FppfStack.{u}}
    {f : StackHom X Y} (P Q : MorphismProperty Scheme.{u})
    [MorphismProperty.DescendsAlong P Q]
    (hrep : f.HasRepresentablePropertyRaw ⊤)
    (hcover : ∀ (T : Scheme.{u}) (y : StackFiber Y T),
      ∃ (S : Scheme.{u}) (base : S ⟶ T) (y' : StackFiber Y S), Q base ∧
        Nonempty (y' ≅ (stackPullback Y base).obj y) ∧
        ∃ q : StackMorphismPresentation f S y', P q.map) :
    f.HasRepresentablePropertyRaw P := by
  intro T y
  obtain ⟨⟨p, -⟩⟩ := hrep T y
  obtain ⟨S, base, y', hQ, ⟨kappa⟩, q, hq⟩ := hcover T y
  exact ⟨⟨p, p.property_of_descendsAlong P Q q base kappa hQ hq⟩⟩

/-- **The isomorphism-scheme hypothesis for a chart.**  For any two maps `a b : S ⟶ U` into the
chart scheme, the base change of the diagonal by the pair of chart objects they define is
representable by a scheme unramified over `S`.

Geometrically this is the statement that the self-overlap square of the chart is 2-cartesian
over the diagonal together with the scheme-level cancellation
`U ×_X U ⟶ U × U` unramified, whose two halves are `selfOverlapSquare` (proved above, but only
as a commuting square) and Mathlib's cancellation for unramified morphisms.  It is the single
hypothesis of `stackDiagonal_unramified_of_etaleAtlas`. -/
def StackChart.HasUnramifiedIsom {X : FppfStack.{u}} (A : StackChart X) : Prop :=
  ∀ (S : Scheme.{u}) (a b : S ⟶ A.scheme),
    ∃ q : StackMorphismPresentation (stackDiagonal X) S
      (stackProdObj (A.obj S a) (A.obj S b)), Unramified q.map

/-- **One direction of the Deligne--Mumford diagonal criterion.**  A stack with an etale
surjective chart whose isomorphism schemes are unramified has representably unramified
diagonal.

The proof is genuine descent: `StackChart.exists_etaleCover_pair` produces, for any pair of
objects over a test scheme, an etale surjective cover over which both objects come from the
chart; the hypothesis `A.HasUnramifiedIsom` supplies an unramified presentation there; and
`StackHom.hasRepresentablePropertyRaw_of_coverIso` descends the property back to the test
scheme.  Representability of the diagonal is assumed separately, because the repository does
not yet compare the two encodings `HasRepresentableDiagonal` (isomorphism sheaves) and
`StackHom.IsRepresentable` applied to `stackDiagonal`. -/
theorem stackDiagonal_unramified_of_etaleAtlas {X : FppfStack.{u}} (A : StackChart X)
    (hA : A.IsEtaleSurjective) (hrep : (stackDiagonal X).IsRepresentable)
    (hIsom : A.HasUnramifiedIsom) : (stackDiagonal X).Unramified := by
  refine (StackHom.hasRepresentableProperty_iff_raw _).2
    (StackHom.hasRepresentablePropertyRaw_of_coverIso (@Unramified) FppfCover.{u}
      ((StackHom.hasRepresentableProperty_iff_raw _).1 hrep) ?_)
  intro T p
  obtain ⟨S, base, a, b, he, hs, ⟨α⟩, ⟨β⟩⟩ := A.exists_etaleCover_pair hA T
    (CategoricalPullback.fst p) (CategoricalPullback.snd p)
  obtain ⟨q, hq⟩ := hIsom S a b
  refine ⟨S, base, stackProdObj (A.obj S a) (A.obj S b),
    smoothCover_le_fppfCover base (etaleCover_le_smoothCover base ⟨hs, he⟩), ⟨?_⟩, q, hq⟩
  exact ((stackProdObjIso α β).trans
    (stackPullback_stackProdObj base (CategoricalPullback.fst p)
      (CategoricalPullback.snd p))).trans
    ((stackPullback (stackProduct X X).pullback base).mapIso (stackProdObj_self p))

/-- The Deligne--Mumford diagonal criterion applied to a Deligne--Mumford stack: its etale
atlas gives an unramified diagonal as soon as the isomorphism-scheme hypothesis holds for that
atlas. -/
theorem DeligneMumfordStack.stackDiagonal_unramified (Z : DeligneMumfordStack.{u})
    (hrep : (stackDiagonal Z.toStack).IsRepresentable)
    (hIsom : ∀ A : StackChart Z.toStack, A.IsEtaleSurjective → A.HasUnramifiedIsom) :
    (stackDiagonal Z.toStack).Unramified := by
  obtain ⟨A, hA⟩ := Z.etaleAtlas
  exact stackDiagonal_unramified_of_etaleAtlas A hA hrep (hIsom A hA)

/-- **Unramified inertia for a Deligne--Mumford stack**, under the same two hypotheses: the
inertia projection is a genuine base change of the diagonal. -/
theorem DeligneMumfordStack.inertiaProjection_unramified (Z : DeligneMumfordStack.{u})
    (hrep : (stackDiagonal Z.toStack).IsRepresentable)
    (hIsom : ∀ A : StackChart Z.toStack, A.IsEtaleSurjective → A.HasUnramifiedIsom) :
    (inertiaProjection Z.toStack).Unramified :=
  _root_.GromovWitten.AlgebraicGeometry.inertiaProjection_unramified _
    (Z.stackDiagonal_unramified hrep hIsom)

end GromovWitten.AlgebraicGeometry
