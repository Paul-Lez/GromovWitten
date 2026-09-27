/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.AtlasRefinement

/-!
# The presentation groupoid object `U ×_X U ⇉ U`

Given an atlas `f : StackHom U X` and a genuine self two-pullback `R : Genuine f f`
(so `R.pullback` presents `U ×_X U`), `Stacks.AtlasRefinement` already constructs the source,
target, unit, composition and inverse maps of the presentation groupoid `R.pullback ⇉ U`
together with their source/target compatibility 2-cells.  This file bundles that data into a
single structure `PresentationGroupoidObject f` (`presentationGroupoidObject` builds one from
any `R : Genuine f f`, in particular from the chosen smooth atlas of an `AlgebraicStack`) and
proves genuinely new groupoid-object laws, all as `StackIso2`s comparing two maps into
`R.pullback`.

Two two-dimensional coherence identities are proved completely:

* **Inversion is an involution**, `StackIso2 (vcomp R.inverse R.inverse) (id R.pullback)`
  (`Genuine.inverse_inverse`).  This is obtained for free from `BilimitComparison.roundTripIso`,
  applied to `R` and its leg-swap `R.swap`: both comparison maps of that round trip literally
  *are* `R.inverse`, since `R.swap.pullback = R.pullback` definitionally and `R.swap`'s defining
  cone is exactly `R`'s inversion cone.
* Two reusable general coherence lemmas for comparing composite lifts (the remaining laws --
  associativity of `compose`, the two unit laws, the two inverse-composition laws -- are proved in
  `Stacks/PresentationGroupoidLaws.lean` by direct diagram chases through the bilimit uniqueness,
  and do not use them): **`Genuine.cone_classifies_precomp`** shows that if `h1` classifies a cone
  `c1`, then for any `q` the composite `vcomp q h1` classifies the whiskered cone (precomposed by
  `q`), with whiskered projection data — this is the "lifts compose" lemma that the survey
  identified as the missing infrastructure.  **`Genuine.cone_classifies_congr`** transports
  classification of `h` along a compatible pair of leg isomorphisms from one cone to another.
  Chaining the two turns "two composite maps into `R.pullback` are 2-isomorphic" into "build the
  whiskered cone, its leg comparisons, and check one compatibility square", instead of a bespoke
  naturality chase for every law.

The right unit law is carried as far as: `Genuine.rightUnitPair` (built from
`Genuine.rightUnitPairCone`, pairing an arrow `g` with the identity arrow at its target) together
with its two projection 2-cells and `Genuine.rightUnitPair_classifies`.  Composing
`cone_classifies_precomp` (precomposing `compose_classifies` by `rightUnitPair`) with
`cone_classifies_congr` (transporting the resulting classification of the composable-pair cone
along to `R`'s own self-cone) would finish `compose (g, unit (target g)) ≅ g`; what remains is
the single compatibility square between the composable-pair comparison and `R`'s own comparison,
which unfolds `composeConeComparison` and needs `rightUnitPair_classifies`.  That last square,
and the symmetric left-unit and inverse-composition laws (built the same way from the swapped or
inverted pairing cone) and associativity (from a triple-composable pullback), are not built here;
see `Not done` in the accompanying report for the precise remaining obstacle.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackTwoPullback

variable {U X : FppfStack.{u}} {f : StackHom U X}

/-- **The presentation groupoid object of an atlas.**  Bundles a genuine self two-pullback
`R : Genuine f f` (presenting `U ×_X U`) together with the groupoid structure maps of
`Stacks.AtlasRefinement`: source, target, unit, composition (on the composable-pair pullback
`R.composable.pullback`) and inverse, plus their source/target compatibility 2-cells.  Every
field below is filled by the corresponding construction of `AtlasRefinement.Genuine`; nothing
new is postulated. -/
structure PresentationGroupoidObject {U X : FppfStack.{u}} (f : StackHom U X) where
  /-- The genuine self two-pullback `U ×_X U` presenting the arrow stack of the groupoid. -/
  R : Genuine f f

namespace PresentationGroupoidObject

variable {U X : FppfStack.{u}} {f : StackHom U X}

/-- The arrow stack `U ×_X U` of the groupoid object. -/
abbrev arrows (P : PresentationGroupoidObject f) : FppfStack.{u} := P.R.pullback

/-- The stack of composable pairs of arrows. -/
noncomputable abbrev composable (P : PresentationGroupoidObject f) : FppfStack.{u} :=
  P.R.composable.pullback

/-- The source map `R.pullback ⟶ U` of the groupoid object. -/
noncomputable abbrev source (P : PresentationGroupoidObject f) :
    StackHom P.arrows U := P.R.source

/-- The target map `R.pullback ⟶ U` of the groupoid object. -/
noncomputable abbrev target (P : PresentationGroupoidObject f) :
    StackHom P.arrows U := P.R.target

/-- The unit (identity-arrow) section `U ⟶ R.pullback` of the groupoid object. -/
noncomputable abbrev unit (P : PresentationGroupoidObject f) :
    StackHom U P.arrows := P.R.unit

/-- The composition map `R.composable.pullback ⟶ R.pullback` of the groupoid object. -/
noncomputable abbrev compose (P : PresentationGroupoidObject f) :
    StackHom P.composable P.arrows := P.R.compose

/-- The inversion map `R.pullback ⟶ R.pullback` of the groupoid object. -/
noncomputable abbrev inverse (P : PresentationGroupoidObject f) :
    StackHom P.arrows P.arrows := P.R.inverse

/-- The source of the unit arrow is the identity: `unit ≫ source ≅ id`. -/
noncomputable def unit_source (P : PresentationGroupoidObject f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.unit P.source)
      (Pseudofunctor.StrongTrans.id U.toPseudofunctor) :=
  P.R.unit_source

/-- The target of the unit arrow is the identity: `unit ≫ target ≅ id`. -/
noncomputable def unit_target (P : PresentationGroupoidObject f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.unit P.target)
      (Pseudofunctor.StrongTrans.id U.toPseudofunctor) :=
  P.R.unit_target

/-- The source of a composite is the source of the first arrow. -/
noncomputable def compose_source (P : PresentationGroupoidObject f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.compose P.source)
      (Pseudofunctor.StrongTrans.vcomp P.R.firstArrow P.source) :=
  P.R.compose_source

/-- The target of a composite is the target of the second arrow. -/
noncomputable def compose_target (P : PresentationGroupoidObject f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.compose P.target)
      (Pseudofunctor.StrongTrans.vcomp P.R.secondArrow P.target) :=
  P.R.compose_target

/-- Composition classifies its defining cone completely, including the comparison face. -/
theorem compose_classifies (P : PresentationGroupoidObject f) :
    ConeLiftClassifies P.R.toStackTwoPullback P.R.composeCone P.compose
      P.compose_source P.compose_target :=
  P.R.compose_classifies

/-- Inversion exchanges source and target. -/
noncomputable def inverse_source (P : PresentationGroupoidObject f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.inverse P.source) P.target :=
  P.R.inverse_source

/-- Inversion exchanges source and target. -/
noncomputable def inverse_target (P : PresentationGroupoidObject f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.inverse P.target) P.source :=
  P.R.inverse_target

/-- Inversion classifies its defining cone completely, including the comparison face. -/
theorem inverse_classifies (P : PresentationGroupoidObject f) :
    ConeLiftClassifies P.R.toStackTwoPullback P.R.inverseCone P.inverse
      P.inverse_source P.inverse_target :=
  P.R.inverse_classifies

end PresentationGroupoidObject

namespace Genuine

variable {U X : FppfStack.{u}} {f : StackHom U X}

/-- The inversion cone of a self two-pullback is literally the self-cone of its leg-swap:
both have first leg `R.snd`, second leg `R.fst`, and comparison `R.comparison.symm`. -/
theorem inverseCone_eq_swap_selfCone (R : Genuine f f) :
    R.inverseCone = (StackTwoPullback.swap R).toStackTwoPullback.selfCone :=
  rfl

/-- **Inversion is an involution.**  Composing the inversion map of a presentation groupoid
with itself is 2-isomorphic to the identity.  This follows for free from
`BilimitComparison.roundTripIso`, applied to `R` and its leg-swap `R.swap`: since
`R.swap.pullback = R.pullback` and `R.swap`'s self-cone is exactly `R`'s inversion cone (in
both directions of the round trip), both comparison maps of that round trip literally *are*
`R.inverse`. -/
noncomputable def inverse_inverse (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.inverse R.inverse)
      (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor) :=
  roundTripIso R (StackTwoPullback.swap R)

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition preserves classification: if `h1` classifies the cone `c1` (over `T1`) of
the self two-pullback `R`, then for any `q` the composite `vcomp q h1` classifies the whiskered
cone `c1` precomposed by `q`, with whiskered projection data.  This is the key reusable
coherence lemma for the groupoid-object laws: it lets such a law be reduced to identifying two
composite maps as lifts of a common cone, without re-deriving the naturality square by hand
each time. -/
theorem cone_classifies_precomp (R : Genuine f f) {T1 T2 : FppfStack.{u}}
    (c1 : Cone (f := f) (g := f) T1) (h1 : StackHom T1 R.pullback)
    (a1 : StackIso2 (Pseudofunctor.StrongTrans.vcomp h1 R.fst) c1.fst)
    (b1 : StackIso2 (Pseudofunctor.StrongTrans.vcomp h1 R.snd) c1.snd)
    (hc1 : ConeLiftClassifies R.toStackTwoPullback c1 h1 a1 b1)
    (q : StackHom T2 T1) :
    ConeLiftClassifies R.toStackTwoPullback
      { fst := Pseudofunctor.StrongTrans.vcomp q c1.fst
        snd := Pseudofunctor.StrongTrans.vcomp q c1.snd
        comparison := (StackIso2.associator q c1.fst f).trans
          ((StackIso2.whiskerLeft q c1.comparison).trans
            (StackIso2.associator q c1.snd f).symm) }
      (Pseudofunctor.StrongTrans.vcomp q h1)
      ((StackIso2.associator q h1 R.fst).trans (StackIso2.whiskerLeft q a1))
      ((StackIso2.associator q h1 R.snd).trans (StackIso2.whiskerLeft q b1)) := by
  intro V x
  have hx := hc1 V ((q.appFunctor V).obj x)
  have step_fst :
      ((((StackIso2.associator q h1 R.fst).trans
        (StackIso2.whiskerLeft q a1)).appIso V).hom.app x) =
        (a1.appIso V).hom.app ((q.appFunctor V).obj x) := by
    rw [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
      StackIso2.whiskerLeft_appIso_hom_app, Category.id_comp]
  have step_snd :
      ((((StackIso2.associator q h1 R.snd).trans
        (StackIso2.whiskerLeft q b1)).appIso V).hom.app x) =
        (b1.appIso V).hom.app ((q.appFunctor V).obj x) := by
    rw [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
      StackIso2.whiskerLeft_appIso_hom_app, Category.id_comp]
  have step_assoc_symm :
      (((StackIso2.associator q c1.snd f).symm).appIso V).hom.app x = 𝟙 _ := by
    rfl
  have step_comparison :
      ((((StackIso2.associator q c1.fst f).trans
        ((StackIso2.whiskerLeft q c1.comparison).trans
          (StackIso2.associator q c1.snd f).symm)).appIso V).hom.app x) =
        (c1.comparison.appIso V).hom.app ((q.appFunctor V).obj x) := by
    rw [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
      Category.id_comp,
      StackTwoPullback.trans_appIso_hom_app, StackIso2.whiskerLeft_appIso_hom_app,
      step_assoc_symm, Category.comp_id]
  apply Iso.ext
  change
    (f.appFunctor V).map
        ((((StackIso2.associator q h1 R.fst).trans
          (StackIso2.whiskerLeft q a1)).appIso V).hom.app x) ≫
      (((StackIso2.associator q c1.fst f).trans
        ((StackIso2.whiskerLeft q c1.comparison).trans
          (StackIso2.associator q c1.snd f).symm)).appIso V).hom.app x =
    (R.comparison.appIso V).hom.app ((h1.appFunctor V).obj ((q.appFunctor V).obj x)) ≫
      (f.appFunctor V).map
        ((((StackIso2.associator q h1 R.snd).trans
          (StackIso2.whiskerLeft q b1)).appIso V).hom.app x)
  rw [step_fst, step_snd, step_comparison]
  exact congrArg Iso.hom hx

/-! ## The right unit law -/

/-- The comparison 2-cell of the cone pairing an arrow with the identity arrow at its target:
`target ≅ vcomp (vcomp target unit) source`, assembled from the left/right unitors, the
associator and the source-triviality of the unit. -/
noncomputable def rightUnitPairComparison (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor) R.target)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.target R.unit) R.source) :=
  (StackIso2.leftUnitor R.target).trans
    ((((StackIso2.associator R.target R.unit R.source).trans
      (StackIso2.whiskerLeft R.target R.unit_source)).trans
      (StackIso2.rightUnitor R.target)).symm)

/-- The cone, over `R.pullback`, of the composable pair `(g, unit (target g))`: its first arrow
is `g` itself (the identity map), its second arrow is the identity arrow at the target of `g`. -/
noncomputable def rightUnitPairCone (R : Genuine f f) :
    Cone (f := R.target) (g := R.source) R.pullback where
  fst := Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor
  snd := Pseudofunctor.StrongTrans.vcomp R.target R.unit
  comparison := R.rightUnitPairComparison

/-- The map `R.pullback ⟶ R.composable.pullback` pairing an arrow with the identity arrow at
its target, constructed by the universal property of the composable-pair pullback. -/
noncomputable def rightUnitPair (R : Genuine f f) :
    StackHom R.pullback R.composable.pullback :=
  R.composable.bilimit.lift R.rightUnitPairCone

/-- The first projection of the right-unit pairing map is the identity. -/
noncomputable def rightUnitPair_firstArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.rightUnitPair R.firstArrow)
      (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor) :=
  R.composable.bilimit.lift_fst R.rightUnitPairCone

/-- The second projection of the right-unit pairing map is the identity arrow at the target. -/
noncomputable def rightUnitPair_secondArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.rightUnitPair R.secondArrow)
      (Pseudofunctor.StrongTrans.vcomp R.target R.unit) :=
  R.composable.bilimit.lift_snd R.rightUnitPairCone

/-- The right-unit pairing map classifies its defining cone completely. -/
theorem rightUnitPair_classifies (R : Genuine f f) :
    ConeLiftClassifies R.composable.toStackTwoPullback R.rightUnitPairCone R.rightUnitPair
      R.rightUnitPair_firstArrow R.rightUnitPair_secondArrow :=
  R.composable.bilimit.lift_compatible R.rightUnitPairCone

/-- The component of a right-whiskered 2-cell is the naive functorial image of the original
component.  Needed alongside `whiskerLeft_appIso_hom_app`/`associator_appIso_hom_app` to unfold
cone comparisons built by whiskering on the right. -/
theorem whiskerRight_appIso_hom_app {A B C : FppfStack.{u}} {p q : StackHom A B}
    (e : StackIso2 p q) (r : StackHom B C) (V : Scheme.{u}) (x : StackFiber A V) :
    ((StackIso2.whiskerRight e r).appIso V).hom.app x =
      (r.appFunctor V).map ((e.appIso V).hom.app x) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Transport of classification along a cone isomorphism.**  If `h` classifies the cone `c`
and `(φ, ψ)` is a compatible pair of isomorphisms from `c`'s legs to another cone `c'`'s legs
(compatible meaning it intertwines the two comparison 2-cells, `hcompat`), then `h` also
classifies `c'`, via `hfst.trans φ` and `hsnd.trans ψ`.  Combined with `cone_classifies_precomp`
this reduces a groupoid-object law to: build the whiskered cone, compute its legs' comparison
with the target cone, and check the compatibility square. -/
theorem cone_classifies_congr (R : Genuine f f) {T : FppfStack.{u}}
    (c c' : Cone (f := f) (g := f) T) (h : StackHom T R.pullback)
    (hfst : StackIso2 (Pseudofunctor.StrongTrans.vcomp h R.fst) c.fst)
    (hsnd : StackIso2 (Pseudofunctor.StrongTrans.vcomp h R.snd) c.snd)
    (hcls : ConeLiftClassifies R.toStackTwoPullback c h hfst hsnd)
    (φ : StackIso2 c.fst c'.fst) (ψ : StackIso2 c.snd c'.snd)
    (hcompat : ∀ (V : Scheme.{u}) (x : StackFiber T V),
      (f.appFunctor V).map ((φ.appIso V).hom.app x) ≫ (c'.comparison.appIso V).hom.app x =
        (c.comparison.appIso V).hom.app x ≫ (f.appFunctor V).map ((ψ.appIso V).hom.app x)) :
    ConeLiftClassifies R.toStackTwoPullback c' h (hfst.trans φ) (hsnd.trans ψ) := by
  intro V x
  apply Iso.ext
  have base := congrArg Iso.hom (hcls V x)
  have hc := hcompat V x
  change
    (f.appFunctor V).map ((hfst.appIso V).hom.app x) ≫ (c.comparison.appIso V).hom.app x =
      (R.comparison.appIso V).hom.app ((h.appFunctor V).obj x) ≫
        (f.appFunctor V).map ((hsnd.appIso V).hom.app x) at base
  change
    (f.appFunctor V).map ((hfst.appIso V).hom.app x ≫ (φ.appIso V).hom.app x) ≫
        (c'.comparison.appIso V).hom.app x =
      (R.comparison.appIso V).hom.app ((h.appFunctor V).obj x) ≫
        (f.appFunctor V).map ((hsnd.appIso V).hom.app x ≫ (ψ.appIso V).hom.app x)
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, hc, ← Category.assoc, base,
    Category.assoc]

end Genuine

/-- **The presentation groupoid object of a genuine self two-pullback.**  Every genuine self
overlap `R : Genuine f f` of an atlas `f : StackHom U X` gives rise to a presentation groupoid
object; in particular this applies to the chosen atlas self-overlap of an `AlgebraicStack`
(via `canonicalGenuine` applied to `X.chosenSmoothAtlas.map`). -/
def presentationGroupoidObject {U X : FppfStack.{u}} (f : StackHom U X) (R : Genuine f f) :
    PresentationGroupoidObject f :=
  ⟨R⟩

/-- The presentation groupoid object attached to the chosen smooth atlas of an algebraic
stack, using the canonical genuine self two-pullback of the atlas map with itself. -/
noncomputable def AlgebraicStack.presentationGroupoidObject (Y : AlgebraicStack.{u}) :
    PresentationGroupoidObject Y.chosenSmoothAtlas.map :=
  StackTwoPullback.presentationGroupoidObject Y.chosenSmoothAtlas.map
    (canonicalGenuine Y.chosenSmoothAtlas.map Y.chosenSmoothAtlas.map)

end StackTwoPullback

end GromovWitten.AlgebraicGeometry
