/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.Geometry
import GromovWitten.AlgebraicGeometry.Stacks.GenuineBaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Common atlas refinements and presentation groupoids

Two atlases `U → X` and `V → X` of a stack are refined by the genuine two-pullback
`U ×_X V → X`.  The refinement is *constructed*: the refining stack is the two-pullback, the
two comparison morphisms are its projections, and the two comparison 2-cells are its
specified invertible comparison modification.  That the refinement is again an atlas is a
theorem, proved from the base-change theorem for representable properties in
`Stacks.GenuineBaseChange` and the composition theorem in `Stacks.Properties`; nothing is
supplied by the caller.

From a genuine self two-pullback `R = U ×_X U` the groupoid `R ⇉ U` is constructed.  Its
source and target are the two projections, its unit is the relative diagonal built in
`Stacks.Geometry`, its inverse is the lift of the flipped cone, and its composition is the
lift of the cone over the two-pullback of the target against the source.  Every structure map
is accompanied by the invertible 2-cells describing its projections, all obtained from the
bicategorical universal property; none of them is a field.

Fibrewise the same groupoid is completely explicit: over a test scheme `T` its objects are the
objects of `U(T)` and its arrows `a ⟶ b` are the isomorphisms `f(a) ≅ f(b)` in `X(T)`.  This
is an honest `Groupoid`, its arrows are in bijection with the objects of the fibre of the
two-pullback (so no arrow, in particular no stabilizer arrow, is discarded), and the functor
induced by a refinement is proved fully faithful, which is refinement compatibility in its
strongest form.

Finally the point relation used to build the topological space of an algebraic stack in
`Stacks.Geometry` is proved reflexive and symmetric, using the unit and the inversion of the
chosen atlas self-overlap.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

/-! ## Multiplicativity of the atlas properties -/

/-- Smooth scheme morphisms contain all identities, because identities are open immersions. -/
theorem smooth_containsIdentities :
    MorphismProperty.ContainsIdentities
      (@_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) :=
  ⟨fun _ ↦ inferInstance⟩

/-- Smooth scheme morphisms form a multiplicative morphism property. -/
theorem smooth_isMultiplicative :
    MorphismProperty.IsMultiplicative
      (@_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) :=
  have := smooth_containsIdentities.{u}
  ⟨⟩

/-- Smooth surjective scheme morphisms, the atlas property of an algebraic stack, form a
multiplicative morphism property. -/
theorem smoothSurjective_isMultiplicative :
    MorphismProperty.IsMultiplicative
      ((@_root_.AlgebraicGeometry.Smooth ⊓ @_root_.AlgebraicGeometry.Surjective :
        MorphismProperty Scheme.{u})) :=
  have := smooth_isMultiplicative.{u}
  MorphismProperty.IsMultiplicative.inf

namespace StackTwoPullback

namespace Genuine

variable {X U V : FppfStack.{u}} {f : StackHom U X} {g : StackHom V X}

/-! ## Common refinements of two atlases -/

/-- The refining morphism to the base attached to a genuine two-pullback of two morphisms to a
common target: the composite of the first projection with the first morphism. -/
noncomputable def refinementHom (P : Genuine f g) : StackHom P.pullback X :=
  Pseudofunctor.StrongTrans.vcomp P.fst f

/-- The first comparison 2-cell of a common refinement: the refining morphism *is* the first
projection followed by the first atlas. -/
noncomputable def refinementFstComparison (P : Genuine f g) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.fst f) P.refinementHom :=
  StackIso2.refl _

/-- The second comparison 2-cell of a common refinement: the second projection followed by the
second atlas is invertibly 2-isomorphic to the refining morphism.  This is the specified
comparison modification of the two-pullback, so no coherence is lost. -/
noncomputable def refinementSndComparison (P : Genuine f g) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.snd g) P.refinementHom :=
  P.comparison.symm

/-- The first projection of a genuine two-pullback is a base change of the second morphism, so
it inherits every multiplicative representable property of that morphism. -/
theorem fst_hasRepresentableProperty (P : Genuine f g)
    (Q : MorphismProperty Scheme.{u}) [Q.IsMultiplicative]
    (hg : g.HasRepresentableProperty Q) :
    P.fst.HasRepresentableProperty Q :=
  StackHom.twoPullbackSnd_hasRepresentableProperty g f (StackTwoPullback.swap P) Q hg

/-- The second projection of a genuine two-pullback is a base change of the first morphism, so
it inherits every multiplicative representable property of that morphism. -/
theorem snd_hasRepresentableProperty (P : Genuine f g)
    (Q : MorphismProperty Scheme.{u}) [Q.IsMultiplicative]
    (hf : f.HasRepresentableProperty Q) :
    P.snd.HasRepresentableProperty Q :=
  StackHom.twoPullbackSnd_hasRepresentableProperty f g P Q hf

/-- **The common refinement of two atlases is again an atlas.**  If both morphisms to the base
have a multiplicative representable property, then so does the refining morphism from their
genuine two-pullback. -/
theorem refinementHom_hasRepresentableProperty (P : Genuine f g)
    (Q : MorphismProperty Scheme.{u}) [Q.IsMultiplicative]
    (hf : f.HasRepresentableProperty Q) (hg : g.HasRepresentableProperty Q) :
    StackHom.HasRepresentableProperty P.refinementHom Q :=
  StackHom.comp_hasRepresentableProperty Q (P.fst_hasRepresentableProperty Q hg) hf

/-- The refining morphism computed through the second leg has the same representable
properties, since the two composites are identified by the comparison 2-cell. -/
theorem sndComp_hasRepresentableProperty (P : Genuine f g)
    (Q : MorphismProperty Scheme.{u}) [Q.IsMultiplicative]
    (hf : f.HasRepresentableProperty Q) (hg : g.HasRepresentableProperty Q) :
    StackHom.HasRepresentableProperty
      (Pseudofunctor.StrongTrans.vcomp P.snd g) Q :=
  (StackHom.hasRepresentableProperty_congr Q P.comparison).mp
    (P.refinementHom_hasRepresentableProperty Q hf hg)

/-- The common refinement of two smooth surjective atlases is a smooth surjective atlas. -/
theorem refinementHom_smoothSurjective (P : Genuine f g)
    (hf : StackHom.HasRepresentableProperty f
      ((@_root_.AlgebraicGeometry.Smooth ⊓ @_root_.AlgebraicGeometry.Surjective :
        MorphismProperty Scheme.{u})))
    (hg : StackHom.HasRepresentableProperty g
      ((@_root_.AlgebraicGeometry.Smooth ⊓ @_root_.AlgebraicGeometry.Surjective :
        MorphismProperty Scheme.{u}))) :
    StackHom.HasRepresentableProperty P.refinementHom
      ((@_root_.AlgebraicGeometry.Smooth ⊓ @_root_.AlgebraicGeometry.Surjective :
        MorphismProperty Scheme.{u})) :=
  have := smoothSurjective_isMultiplicative.{u}
  P.refinementHom_hasRepresentableProperty _ hf hg

end Genuine

/-- **Existence of a common refinement.**  Any two morphisms to a common base with a
multiplicative representable property admit a refining stack with a morphism to the base having
the same property and two comparison morphisms whose composites with the given morphisms are
invertibly 2-isomorphic to it.  The refinement is constructed as the canonical genuine
two-pullback; it is not supplied. -/
theorem exists_commonRefinement {X U V : FppfStack.{u}}
    (f : StackHom U X) (g : StackHom V X)
    (Q : MorphismProperty Scheme.{u}) [Q.IsMultiplicative]
    (hf : f.HasRepresentableProperty Q) (hg : g.HasRepresentableProperty Q) :
    ∃ (W : FppfStack.{u}) (w : StackHom W X) (a : StackHom W U) (b : StackHom W V),
      Nonempty (StackIso2 (Pseudofunctor.StrongTrans.vcomp a f) w) ∧
        Nonempty (StackIso2 (Pseudofunctor.StrongTrans.vcomp b g) w) ∧
        StackHom.HasRepresentableProperty w Q := by
  refine ⟨(canonicalGenuine f g).pullback, (canonicalGenuine f g).refinementHom,
    (canonicalGenuine f g).fst, (canonicalGenuine f g).snd,
    ⟨(canonicalGenuine f g).refinementFstComparison⟩,
    ⟨(canonicalGenuine f g).refinementSndComparison⟩, ?_⟩
  exact (canonicalGenuine f g).refinementHom_hasRepresentableProperty Q hf hg

/-! ## The presentation groupoid of an atlas -/

namespace Genuine

variable {X U : FppfStack.{u}} {f : StackHom U X}

/-- The source map of the presentation groupoid `U ×_X U ⇉ U`. -/
noncomputable def source (R : Genuine f f) : StackHom R.pullback U := R.fst

/-- The target map of the presentation groupoid `U ×_X U ⇉ U`. -/
noncomputable def target (R : Genuine f f) : StackHom R.pullback U := R.snd

/-- The tautological 2-cell of the presentation groupoid: the images under the atlas of the
source and the target of an arrow are identified. -/
noncomputable def sourceTargetComparison (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.source f)
      (Pseudofunctor.StrongTrans.vcomp R.target f) :=
  R.comparison

/-- The unit of the presentation groupoid, constructed as the relative diagonal through the
bicategorical universal property of the self two-pullback. -/
noncomputable def unit (R : Genuine f f) : StackHom U R.pullback :=
  R.relativeDiagonal

/-- The source of the unit arrow is the identity. -/
noncomputable def unit_source (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.unit R.source)
      (Pseudofunctor.StrongTrans.id U.toPseudofunctor) :=
  R.relativeDiagonalFstComparison

/-- The target of the unit arrow is the identity. -/
noncomputable def unit_target (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.unit R.target)
      (Pseudofunctor.StrongTrans.id U.toPseudofunctor) :=
  R.relativeDiagonalSndComparison

/-- The cone classifying the inversion of arrows: the two legs of the self two-pullback are
interchanged and the comparison 2-cell is reversed. -/
noncomputable def inverseCone (R : Genuine f f) :
    Cone (f := f) (g := f) R.pullback where
  fst := R.snd
  snd := R.fst
  comparison := R.comparison.symm

/-- The inversion map of the presentation groupoid, constructed by the universal property. -/
noncomputable def inverse (R : Genuine f f) : StackHom R.pullback R.pullback :=
  R.bilimit.lift R.inverseCone

/-- Inversion exchanges source and target: the source of an inverted arrow is the original
target. -/
noncomputable def inverse_source (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.inverse R.source) R.target :=
  R.bilimit.lift_fst R.inverseCone

/-- Inversion exchanges source and target: the target of an inverted arrow is the original
source. -/
noncomputable def inverse_target (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.inverse R.target) R.source :=
  R.bilimit.lift_snd R.inverseCone

/-- The stack of composable pairs of arrows: the genuine two-pullback of the target against the
source. -/
noncomputable def composable (R : Genuine f f) : Genuine R.snd R.fst :=
  canonicalGenuine R.snd R.fst

/-- The first arrow of a composable pair. -/
noncomputable def firstArrow (R : Genuine f f) :
    StackHom R.composable.pullback R.pullback :=
  R.composable.fst

/-- The second arrow of a composable pair. -/
noncomputable def secondArrow (R : Genuine f f) :
    StackHom R.composable.pullback R.pullback :=
  R.composable.snd

/-- Composability: the target of the first arrow agrees with the source of the second. -/
noncomputable def composableComparison (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.firstArrow R.target)
      (Pseudofunctor.StrongTrans.vcomp R.secondArrow R.source) :=
  R.composable.comparison

/-- The comparison 2-cell of the composition cone, assembled from the tautological 2-cells of
the two arrows and the composability 2-cell by whiskering and reassociation. -/
noncomputable def composeConeComparison (R : Genuine f f) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.firstArrow R.fst) f)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.secondArrow R.snd) f) :=
  ((((StackIso2.associator R.firstArrow R.fst f).trans
    (StackIso2.whiskerLeft R.firstArrow R.comparison)).trans
      (StackIso2.associator R.firstArrow R.snd f).symm).trans
        (StackIso2.whiskerRight R.composableComparison f)).trans
          (((StackIso2.associator R.secondArrow R.fst f).trans
            (StackIso2.whiskerLeft R.secondArrow R.comparison)).trans
              (StackIso2.associator R.secondArrow R.snd f).symm)

/-- The cone classifying the composition of a composable pair: its source is the source of the
first arrow, its target is the target of the second. -/
noncomputable def composeCone (R : Genuine f f) :
    Cone (f := f) (g := f) R.composable.pullback where
  fst := Pseudofunctor.StrongTrans.vcomp R.firstArrow R.fst
  snd := Pseudofunctor.StrongTrans.vcomp R.secondArrow R.snd
  comparison := R.composeConeComparison

/-- The composition map of the presentation groupoid, constructed by the universal property. -/
noncomputable def compose (R : Genuine f f) :
    StackHom R.composable.pullback R.pullback :=
  R.bilimit.lift R.composeCone

/-- The source of a composite is the source of its first arrow. -/
noncomputable def compose_source (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.compose R.source)
      (Pseudofunctor.StrongTrans.vcomp R.firstArrow R.source) :=
  R.bilimit.lift_fst R.composeCone

/-- The target of a composite is the target of its second arrow. -/
noncomputable def compose_target (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.compose R.target)
      (Pseudofunctor.StrongTrans.vcomp R.secondArrow R.target) :=
  R.bilimit.lift_snd R.composeCone

/-- The composition map classifies its cone completely, including the comparison face. -/
theorem compose_classifies (R : Genuine f f) :
    ConeLiftClassifies R.toStackTwoPullback R.composeCone R.compose
      R.compose_source R.compose_target :=
  R.bilimit.lift_compatible R.composeCone

/-- The inversion map classifies its cone completely, including the comparison face. -/
theorem inverse_classifies (R : Genuine f f) :
    ConeLiftClassifies R.toStackTwoPullback R.inverseCone R.inverse
      R.inverse_source R.inverse_target :=
  R.bilimit.lift_compatible R.inverseCone

/-- The arrow stack of the presentation groupoid is representable with any multiplicative
representable property of the atlas, both as a stack over the atlas and over the base. -/
theorem source_hasRepresentableProperty (R : Genuine f f)
    (Q : MorphismProperty Scheme.{u}) [Q.IsMultiplicative]
    (hf : f.HasRepresentableProperty Q) :
    R.source.HasRepresentableProperty Q :=
  R.fst_hasRepresentableProperty Q hf

/-- The target map of the presentation groupoid inherits the representable properties of the
atlas. -/
theorem target_hasRepresentableProperty (R : Genuine f f)
    (Q : MorphismProperty Scheme.{u}) [Q.IsMultiplicative]
    (hf : f.HasRepresentableProperty Q) :
    R.target.HasRepresentableProperty Q :=
  R.snd_hasRepresentableProperty Q hf

end Genuine

/-! ## Refinement compatibility for presentation groupoids -/

section RefinementGroupoid

variable {X U W : FppfStack.{u}} {f : StackHom U X} {w : StackHom W X}

/-- The comparison 2-cell of the cone used to map the groupoid of a refinement to the groupoid
of the refined atlas.  It is assembled from the tautological 2-cell of the refinement groupoid
and the refinement 2-cell, by whiskering and reassociation. -/
noncomputable def refinementGroupoidConeComparison (S : Genuine w w)
    (q : StackHom W U) (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp S.fst q) f)
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp S.snd q) f) :=
  ((((StackIso2.associator S.fst q f).trans
    (StackIso2.whiskerLeft S.fst e)).trans S.comparison).trans
      (StackIso2.whiskerLeft S.snd e).symm).trans
        (StackIso2.associator S.snd q f).symm

/-- The cone, over the refined atlas, determined by an arrow of the refinement groupoid. -/
noncomputable def refinementGroupoidCone (S : Genuine w w)
    (q : StackHom W U) (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w) :
    Cone (f := f) (g := f) S.pullback where
  fst := Pseudofunctor.StrongTrans.vcomp S.fst q
  snd := Pseudofunctor.StrongTrans.vcomp S.snd q
  comparison := refinementGroupoidConeComparison S q e

/-- **Refinement compatibility.**  A refinement of atlases induces a morphism from the
presentation groupoid of the refinement to the presentation groupoid of the refined atlas,
constructed by the bicategorical universal property. -/
noncomputable def refinementGroupoidMap (S : Genuine w w) (R : Genuine f f)
    (q : StackHom W U) (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w) :
    StackHom S.pullback R.pullback :=
  R.bilimit.lift (refinementGroupoidCone S q e)

/-- The induced groupoid morphism commutes with the source maps, up to the displayed
2-cell. -/
noncomputable def refinementGroupoidMap_source (S : Genuine w w) (R : Genuine f f)
    (q : StackHom W U) (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (refinementGroupoidMap S R q e) R.source)
      (Pseudofunctor.StrongTrans.vcomp S.source q) :=
  R.bilimit.lift_fst (refinementGroupoidCone S q e)

/-- The induced groupoid morphism commutes with the target maps, up to the displayed
2-cell. -/
noncomputable def refinementGroupoidMap_target (S : Genuine w w) (R : Genuine f f)
    (q : StackHom W U) (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (refinementGroupoidMap S R q e) R.target)
      (Pseudofunctor.StrongTrans.vcomp S.target q) :=
  R.bilimit.lift_snd (refinementGroupoidCone S q e)

/-- The induced groupoid morphism classifies its cone completely, including the comparison
face: the 2-cells of the refinement are respected, not merely the two projections. -/
theorem refinementGroupoidMap_classifies (S : Genuine w w) (R : Genuine f f)
    (q : StackHom W U) (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w) :
    ConeLiftClassifies R.toStackTwoPullback (refinementGroupoidCone S q e)
      (refinementGroupoidMap S R q e)
      (refinementGroupoidMap_source S R q e)
      (refinementGroupoidMap_target S R q e) :=
  R.bilimit.lift_compatible (refinementGroupoidCone S q e)

end RefinementGroupoid

end StackTwoPullback

/-! ## The fibrewise presentation groupoid -/

/-- The objects of the presentation groupoid of an atlas over a test scheme: the objects of the
atlas fibre.  Arrows are recorded separately so that no arrow of the base stack is lost. -/
def PresentationGroupoid {X U : FppfStack.{u}} (_f : StackHom U X) (T : Scheme.{u}) : Type u :=
  StackFiber U T

namespace PresentationGroupoid

variable {X U : FppfStack.{u}} {f : StackHom U X} {T : Scheme.{u}}

/-- The underlying object of the atlas fibre. -/
abbrev back (a : PresentationGroupoid f T) : StackFiber U T := a

/-- An arrow of the presentation groupoid: an actual isomorphism in the fibre of the base stack
between the images of the two endpoints.  Retaining the isomorphism, rather than only the
statement that one exists, is what keeps every stabilizer arrow. -/
@[ext]
structure Arrow (f : StackHom U X) {T : Scheme.{u}} (a b : PresentationGroupoid f T) where
  /-- The isomorphism in the base-stack fibre relating the images of the endpoints. -/
  iso : (f.appFunctor T).obj (back a) ≅ (f.appFunctor T).obj (back b)

/-- The presentation groupoid is a category: composition of arrows is composition of the
underlying isomorphisms. -/
instance : Category (PresentationGroupoid f T) where
  Hom a b := Arrow f a b
  id _ := ⟨Iso.refl _⟩
  comp p q := ⟨p.iso ≪≫ q.iso⟩
  id_comp _ := by apply Arrow.ext; apply Iso.ext; simp
  comp_id _ := by apply Arrow.ext; apply Iso.ext; simp
  assoc _ _ _ := by apply Arrow.ext; apply Iso.ext; simp

@[simp]
theorem id_iso (a : PresentationGroupoid f T) : (𝟙 a : Arrow f a a).iso = Iso.refl _ :=
  rfl

@[simp]
theorem comp_iso {a b c : PresentationGroupoid f T} (p : a ⟶ b) (q : b ⟶ c) :
    (p ≫ q).iso = p.iso ≪≫ q.iso :=
  rfl

/-- The presentation groupoid is a groupoid: every arrow is invertible because it is an
isomorphism of the base stack. -/
instance : Groupoid (PresentationGroupoid f T) where
  inv p := ⟨p.iso.symm⟩
  inv_comp _ := by apply Arrow.ext; apply Iso.ext; simp
  comp_inv _ := by apply Arrow.ext; apply Iso.ext; simp

@[simp]
theorem inv_iso {a b : PresentationGroupoid f T} (p : a ⟶ b) :
    (Groupoid.inv p).iso = p.iso.symm :=
  rfl

/-- **The arrows of the presentation groupoid are exactly the objects of the fibre of the
self two-pullback.**  No arrow is discarded by passing to the groupoid presentation. -/
def arrowEquiv (f : StackHom U X) (T : Scheme.{u}) :
    StackInGroupoids.FiberTwoPullback f f T ≃
      Σ a b : PresentationGroupoid f T, (a ⟶ b) where
  toFun p := ⟨p.1, p.2, ⟨p.3⟩⟩
  invFun p := ⟨p.1, p.2.1, p.2.2.iso⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Stabilizers are retained.**  The automorphisms of an object of the presentation groupoid
are exactly the automorphisms in the base stack of its image under the atlas. -/
def autEquiv (f : StackHom U X) {T : Scheme.{u}} (a : PresentationGroupoid f T) :
    (a ⟶ a) ≃ Aut ((f.appFunctor T).obj (back a)) where
  toFun p := p.iso
  invFun p := ⟨p⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Refinement

variable {W : FppfStack.{u}} {w : StackHom W X}

/-- The image in the refined presentation groupoid of an object of the refinement presentation
groupoid: its image under the comparison morphism of the refinement. -/
abbrev refinementObj (f : StackHom U X) {W : FppfStack.{u}} {w : StackHom W X}
    (q : StackHom W U) {T : Scheme.{u}} (a : PresentationGroupoid w T) :
    PresentationGroupoid f T :=
  (q.appFunctor T).obj (back a)

/-- The component at one object of the 2-cell of a refinement of atlases: it identifies the
image of the object under the refined atlas with its image under the refining morphism. -/
noncomputable def refinementIso (q : StackHom W U)
    (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w) (T : Scheme.{u})
    (a : PresentationGroupoid w T) :
    (f.appFunctor T).obj (back (refinementObj f q a)) ≅ (w.appFunctor T).obj (back a) :=
  (e.appIso T).app (back a)

/-- **Refinement compatibility on arrows.**  Conjugation by the 2-cell of a refinement is a
bijection between the arrows of the refinement presentation groupoid and *all* arrows between
the corresponding objects of the refined presentation groupoid.  In particular no stabilizer
arrow is created or destroyed by refining an atlas. -/
noncomputable def refinementArrowEquiv (q : StackHom W U)
    (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w) (T : Scheme.{u})
    (a b : PresentationGroupoid w T) :
    (a ⟶ b) ≃ (refinementObj f q a ⟶ refinementObj f q b) where
  toFun p := ⟨(refinementIso q e T a ≪≫ p.iso) ≪≫ (refinementIso q e T b).symm⟩
  invFun p := ⟨((refinementIso q e T a).symm ≪≫ p.iso) ≪≫ refinementIso q e T b⟩
  left_inv _ := by apply Arrow.ext; apply Iso.ext; simp
  right_inv _ := by apply Arrow.ext; apply Iso.ext; simp

/-- The functor of presentation groupoids induced by a refinement of atlases.  On objects it is
the comparison morphism of the refinement; on arrows it is conjugation by the refinement 2-cell,
so the 2-cell is used rather than discarded. -/
noncomputable def refinementFunctor (q : StackHom W U)
    (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w) (T : Scheme.{u}) :
    PresentationGroupoid w T ⥤ PresentationGroupoid f T where
  obj a := refinementObj f q a
  map {a b} p := refinementArrowEquiv q e T a b p
  map_id a := by
    apply Arrow.ext
    change (refinementIso q e T a ≪≫ Iso.refl _) ≪≫ (refinementIso q e T a).symm =
      Iso.refl _
    rw [Iso.trans_refl, Iso.self_symm_id]
  map_comp {a b c} p r := by
    apply Arrow.ext
    change (refinementIso q e T a ≪≫ (p.iso ≪≫ r.iso)) ≪≫ (refinementIso q e T c).symm =
      ((refinementIso q e T a ≪≫ p.iso) ≪≫ (refinementIso q e T b).symm) ≪≫
        ((refinementIso q e T b ≪≫ r.iso) ≪≫ (refinementIso q e T c).symm)
    apply Iso.ext
    simp

@[simp]
theorem refinementFunctor_obj (q : StackHom W U)
    (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w) (T : Scheme.{u})
    (a : PresentationGroupoid w T) :
    (refinementFunctor q e T).obj a = refinementObj f q a :=
  rfl

@[simp]
theorem refinementFunctor_map (q : StackHom W U)
    (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w) (T : Scheme.{u})
    {a b : PresentationGroupoid w T} (p : a ⟶ b) :
    (refinementFunctor q e T).map p = refinementArrowEquiv q e T a b p :=
  rfl

/-- A refinement of atlases induces a faithful functor of presentation groupoids. -/
theorem refinementFunctor_faithful (q : StackHom W U)
    (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w) (T : Scheme.{u}) :
    (refinementFunctor (f := f) q e T).Faithful where
  map_injective {a b} := (refinementArrowEquiv q e T a b).injective

/-- A refinement of atlases induces a full functor of presentation groupoids. -/
theorem refinementFunctor_full (q : StackHom W U)
    (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w) (T : Scheme.{u}) :
    (refinementFunctor (f := f) q e T).Full where
  map_surjective {a b} := (refinementArrowEquiv q e T a b).surjective

end Refinement

section CommonRefinement

variable {V : FppfStack.{u}} {g : StackHom V X}

/-- The fibrewise groupoid functor from the common refinement of two atlases to the first
atlas. -/
noncomputable def commonRefinementLeftFunctor
    (P : StackTwoPullback.Genuine f g) (T : Scheme.{u}) :
    PresentationGroupoid P.refinementHom T ⥤ PresentationGroupoid f T :=
  refinementFunctor P.fst P.refinementFstComparison T

/-- The fibrewise groupoid functor from the common refinement of two atlases to the second
atlas. -/
noncomputable def commonRefinementRightFunctor
    (P : StackTwoPullback.Genuine f g) (T : Scheme.{u}) :
    PresentationGroupoid P.refinementHom T ⥤ PresentationGroupoid g T :=
  refinementFunctor P.snd P.refinementSndComparison T

/-- The comparison functor to the first atlas is faithful. -/
theorem commonRefinementLeftFaithful
    (P : StackTwoPullback.Genuine f g) (T : Scheme.{u}) :
    (commonRefinementLeftFunctor P T).Faithful :=
  refinementFunctor_faithful P.fst P.refinementFstComparison T

/-- The comparison functor to the first atlas is full. -/
theorem commonRefinementLeftFull
    (P : StackTwoPullback.Genuine f g) (T : Scheme.{u}) :
    (commonRefinementLeftFunctor P T).Full :=
  refinementFunctor_full P.fst P.refinementFstComparison T

/-- The comparison functor to the second atlas is faithful. -/
theorem commonRefinementRightFaithful
    (P : StackTwoPullback.Genuine f g) (T : Scheme.{u}) :
    (commonRefinementRightFunctor P T).Faithful :=
  refinementFunctor_faithful P.snd P.refinementSndComparison T

/-- The comparison functor to the second atlas is full. -/
theorem commonRefinementRightFull
    (P : StackTwoPullback.Genuine f g) (T : Scheme.{u}) :
    (commonRefinementRightFunctor P T).Full :=
  refinementFunctor_full P.snd P.refinementSndComparison T

end CommonRefinement

end PresentationGroupoid

/-! ## The atlas point relation -/

namespace StackChart

variable {X : FppfStack.{u}} (A : StackChart X)

/-- The point relation of a chart determined by a self-overlap presentation: two points of the
chart scheme are related when an actual point of the self-overlap maps to them under its two
projections. -/
def pointRelation
    (p : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)))
    (x y : A.scheme) : Prop :=
  ∃ r : p.space, p.fst.base r = x ∧ p.snd.base r = y

/-- The comparison morphism between two self-overlap presentations of one chart, constructed by
the universal property of the target presentation. -/
noncomputable def overlapComparison
    (p q : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme))) :
    q.space ⟶ p.space :=
  p.lift q.fst q.snd q.comparison

/-- The comparison morphism of self-overlap presentations respects the first projection. -/
theorem overlapComparison_fst
    (p q : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme))) :
    A.overlapComparison p q ≫ p.fst = q.fst :=
  p.lift_fst _ _ _

/-- The comparison morphism of self-overlap presentations respects the second projection. -/
theorem overlapComparison_snd
    (p q : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme))) :
    A.overlapComparison p q ≫ p.snd = q.snd :=
  p.lift_snd _ _ _

/-- Every point relation is contained in every other one, by the comparison morphism. -/
theorem pointRelation_mono
    (p q : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)))
    {x y : A.scheme} (h : A.pointRelation q x y) : A.pointRelation p x y := by
  obtain ⟨r, hr₁, hr₂⟩ := h
  refine ⟨(A.overlapComparison p q).base r, ?_, ?_⟩
  · rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, A.overlapComparison_fst]
    exact hr₁
  · rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, A.overlapComparison_snd]
    exact hr₂

/-- **The point relation of a chart does not depend on the chosen self-overlap
presentation.**  Consequently neither does the quotient point set nor its quotient topology. -/
theorem pointRelation_eq
    (p q : A.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme))) :
    A.pointRelation p = A.pointRelation q := by
  funext x y
  exact propext ⟨fun h ↦ A.pointRelation_mono q p h, fun h ↦ A.pointRelation_mono p q h⟩

end StackChart

namespace AlgebraicStack

variable (Y : AlgebraicStack.{u})

/-- The point relation used to build the underlying space of an algebraic stack is the point
relation of the chosen atlas for the chosen self-overlap presentation. -/
theorem atlasPointRelation_eq_pointRelation :
    Y.atlasPointRelation =
      Y.chosenSmoothAtlas.pointRelation Y.chosenAtlasSelfOverlap :=
  rfl

/-- The point relation of an algebraic stack is unchanged if the chosen self-overlap
presentation is replaced by any other one. -/
theorem atlasPointRelation_eq_of_presentation
    (p : Y.chosenSmoothAtlas.PullbackPresentation Y.chosenSmoothAtlas.scheme
      (Y.chosenSmoothAtlas.obj Y.chosenSmoothAtlas.scheme
        (𝟙 Y.chosenSmoothAtlas.scheme))) :
    Y.atlasPointRelation = Y.chosenSmoothAtlas.pointRelation p :=
  Y.chosenSmoothAtlas.pointRelation_eq Y.chosenAtlasSelfOverlap p

/-- The unit section of the chosen atlas self-overlap, constructed from its universal
property. -/
noncomputable def atlasSelfOverlapUnit :
    Y.chosenSmoothAtlas.scheme ⟶ Y.chosenAtlasSelfOverlap.space :=
  Y.chosenAtlasSelfOverlap.lift (𝟙 _) (𝟙 _)
    (Y.chosenSmoothAtlas.identityObjectPullbackComparison (𝟙 _))

@[simp]
theorem atlasSelfOverlapUnit_fst :
    Y.atlasSelfOverlapUnit ≫ Y.chosenAtlasSelfOverlap.fst = 𝟙 _ :=
  Y.chosenAtlasSelfOverlap.lift_fst _ _ _

@[simp]
theorem atlasSelfOverlapUnit_snd :
    Y.atlasSelfOverlapUnit ≫ Y.chosenAtlasSelfOverlap.snd = 𝟙 _ :=
  Y.chosenAtlasSelfOverlap.lift_snd _ _ _

/-- The inversion of the chosen atlas self-overlap, constructed from its universal property by
reversing the comparison isomorphism. -/
noncomputable def atlasSelfOverlapInv :
    Y.chosenAtlasSelfOverlap.space ⟶ Y.chosenAtlasSelfOverlap.space :=
  Y.chosenAtlasSelfOverlap.lift Y.chosenAtlasSelfOverlap.snd
    Y.chosenAtlasSelfOverlap.fst Y.chosenAtlasSelfOverlap.selfSwapComparison

@[simp]
theorem atlasSelfOverlapInv_fst :
    Y.atlasSelfOverlapInv ≫ Y.chosenAtlasSelfOverlap.fst =
      Y.chosenAtlasSelfOverlap.snd :=
  Y.chosenAtlasSelfOverlap.lift_fst _ _ _

@[simp]
theorem atlasSelfOverlapInv_snd :
    Y.atlasSelfOverlapInv ≫ Y.chosenAtlasSelfOverlap.snd =
      Y.chosenAtlasSelfOverlap.fst :=
  Y.chosenAtlasSelfOverlap.lift_snd _ _ _

/-- The atlas point relation is reflexive, witnessed by the constructed unit section. -/
theorem atlasPointRelation_refl (x : Y.chosenSmoothAtlas.scheme) :
    Y.atlasPointRelation x x := by
  refine ⟨Y.atlasSelfOverlapUnit.base x, ?_, ?_⟩
  · rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, Y.atlasSelfOverlapUnit_fst]
    simp
  · rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, Y.atlasSelfOverlapUnit_snd]
    simp

/-- The atlas point relation is symmetric, witnessed by the constructed inversion. -/
theorem atlasPointRelation_symm {x y : Y.chosenSmoothAtlas.scheme}
    (h : Y.atlasPointRelation x y) : Y.atlasPointRelation y x := by
  obtain ⟨r, hr₁, hr₂⟩ := h
  refine ⟨Y.atlasSelfOverlapInv.base r, ?_, ?_⟩
  · rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, Y.atlasSelfOverlapInv_fst]
    exact hr₂
  · rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, Y.atlasSelfOverlapInv_snd]
    exact hr₁

/-- The scheme of composable pairs of points of the chosen atlas self-overlap: the fibre product
of the target against the source. -/
noncomputable abbrev overlapComposable : Scheme.{u} :=
  Limits.pullback Y.chosenAtlasSelfOverlap.snd Y.chosenAtlasSelfOverlap.fst

/-- The comparison isomorphism classifying the composite of a composable pair of overlap points.
It is assembled from the two pulled-back universal comparisons of the self-overlap and the
identity-object comparison of the chart. -/
noncomputable def overlapComposeComparison :
    Y.chosenSmoothAtlas.obj Y.overlapComposable
        (Limits.pullback.snd Y.chosenAtlasSelfOverlap.snd Y.chosenAtlasSelfOverlap.fst ≫
          Y.chosenAtlasSelfOverlap.snd) ≅
      (stackPullback Y.toStack
        (Limits.pullback.fst Y.chosenAtlasSelfOverlap.snd Y.chosenAtlasSelfOverlap.fst ≫
          Y.chosenAtlasSelfOverlap.fst)).obj
        (Y.chosenSmoothAtlas.obj Y.chosenSmoothAtlas.scheme
          (𝟙 Y.chosenSmoothAtlas.scheme)) :=
  ((Y.chosenSmoothAtlas.inducedComparison Y.chosenAtlasSelfOverlap.fst
        Y.chosenAtlasSelfOverlap.snd Y.chosenAtlasSelfOverlap.comparison
        (Limits.pullback.snd Y.chosenAtlasSelfOverlap.snd
          Y.chosenAtlasSelfOverlap.fst)).trans
      ((stackPullbackObjIsoOfEq Y.toStack Limits.pullback.condition.symm _).trans
        (Y.chosenSmoothAtlas.identityObjectPullbackComparison _).symm)).trans
    (Y.chosenSmoothAtlas.inducedComparison Y.chosenAtlasSelfOverlap.fst
      Y.chosenAtlasSelfOverlap.snd Y.chosenAtlasSelfOverlap.comparison
      (Limits.pullback.fst Y.chosenAtlasSelfOverlap.snd Y.chosenAtlasSelfOverlap.fst))

/-- The composition of the chosen atlas self-overlap, constructed from its universal
property. -/
noncomputable def overlapCompose :
    Y.overlapComposable ⟶ Y.chosenAtlasSelfOverlap.space :=
  Y.chosenAtlasSelfOverlap.lift _ _ Y.overlapComposeComparison

/-- The source of a composite overlap point is the source of the first factor. -/
theorem overlapCompose_fst :
    Y.overlapCompose ≫ Y.chosenAtlasSelfOverlap.fst =
      Limits.pullback.fst Y.chosenAtlasSelfOverlap.snd Y.chosenAtlasSelfOverlap.fst ≫
        Y.chosenAtlasSelfOverlap.fst :=
  Y.chosenAtlasSelfOverlap.lift_fst _ _ _

/-- The target of a composite overlap point is the target of the second factor. -/
theorem overlapCompose_snd :
    Y.overlapCompose ≫ Y.chosenAtlasSelfOverlap.snd =
      Limits.pullback.snd Y.chosenAtlasSelfOverlap.snd Y.chosenAtlasSelfOverlap.fst ≫
        Y.chosenAtlasSelfOverlap.snd :=
  Y.chosenAtlasSelfOverlap.lift_snd _ _ _

/-- The atlas point relation is transitive, witnessed by the constructed composition on the
scheme of composable pairs. -/
theorem atlasPointRelation_trans {x y z : Y.chosenSmoothAtlas.scheme}
    (h₁ : Y.atlasPointRelation x y) (h₂ : Y.atlasPointRelation y z) :
    Y.atlasPointRelation x z := by
  obtain ⟨r, hr₁, hr₂⟩ := h₁
  obtain ⟨s, hs₁, hs₂⟩ := h₂
  obtain ⟨t, ht₁, ht₂⟩ :=
    _root_.AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (f := Y.chosenAtlasSelfOverlap.snd) (g := Y.chosenAtlasSelfOverlap.fst) r s
      (by rw [hr₂, hs₁])
  refine ⟨Y.overlapCompose.base t, ?_, ?_⟩
  · rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, Y.overlapCompose_fst,
      _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, ht₁]
    exact hr₁
  · rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, Y.overlapCompose_snd,
      _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, ht₂]
    exact hs₂

/-- **The atlas point relation is already an equivalence relation.**  Reflexivity, symmetry and
transitivity are the unit, the inversion and the composition of the atlas self-overlap. -/
theorem atlasPointRelation_equivalence : Equivalence Y.atlasPointRelation where
  refl := Y.atlasPointRelation_refl
  symm := Y.atlasPointRelation_symm
  trans := Y.atlasPointRelation_trans

/-- The equivalence relation generated by the atlas point relation is the atlas point relation
itself; no genuinely new identification is created by taking the generated closure. -/
theorem eqvGen_atlasPointRelation_iff {x y : Y.chosenSmoothAtlas.scheme} :
    Relation.EqvGen Y.atlasPointRelation x y ↔ Y.atlasPointRelation x y := by
  constructor
  · intro h
    induction h with
    | rel a b hab => exact hab
    | refl a => exact Y.atlasPointRelation_refl a
    | symm a b _ ih => exact Y.atlasPointRelation_symm ih
    | trans a b c _ _ hab hbc => exact Y.atlasPointRelation_trans hab hbc
  · exact Relation.EqvGen.rel _ _

/-- **The underlying point space of an algebraic stack is the honest orbit set of the
presentation groupoid.**  Two atlas points have the same image exactly when an actual point of
the self-overlap joins them. -/
theorem atlasPointMap_eq_iff {x y : Y.chosenSmoothAtlas.scheme} :
    Y.atlasPointMap x = Y.atlasPointMap y ↔ Y.atlasPointRelation x y := by
  constructor
  · intro h
    have h' : Quotient.mk (Relation.EqvGen.setoid Y.atlasPointRelation) x =
        Quotient.mk (Relation.EqvGen.setoid Y.atlasPointRelation) y := h
    exact Y.eqvGen_atlasPointRelation_iff.mp (Quotient.exact h')
  · intro h
    exact Quotient.sound (Relation.EqvGen.rel _ _ h)

/-- The topology on the underlying point space is the quotient topology of the chosen atlas:
a subset is open exactly when its preimage in the atlas is open. -/
theorem isOpen_underlyingStackPoint_iff (S : Set (UnderlyingStackPoint Y)) :
    IsOpen S ↔ IsOpen (Y.atlasPointMap ⁻¹' S) :=
  Iff.rfl

end AlgebraicStack

end GromovWitten.AlgebraicGeometry
