/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.RelativeProj
import GromovWitten.AlgebraicGeometry.Stacks.SchemeAtlasRefinement

/-!
# Relative `Proj` as a morphism of stacks

The relative `Proj` `relativeProj X 𝒜` of a quasi-coherent graded algebra `𝒜` on a scheme `X`
(`RelativeProj.GradedAlgebraData`) is promoted here to a morphism of represented fppf stacks
`stackProj X 𝒜 : StackHom (representedStack (relativeProj X 𝒜)) (representedStack X)`, the
image of the structure morphism `toBase X 𝒜` under the functoriality of `representedStack`. When
`𝒜` is affine-locally of finite type over its degree-zero part with degree-zero part the section
ring, `toBase X 𝒜` is proper (`RelativeProj.toBase_isProper`), and since properness of scheme
morphisms is stable under base change this promotes to a representable property of the stack
morphism, exhibiting `relativeProj X 𝒜` as a "proper morphism of stacks" over `X` in the sense of
`Stacks.Algebraic`.

* `stackProj X 𝒜` is the morphism of represented stacks induced by `toBase X 𝒜`.
* `stackProj_hasRepresentableProperty_isProper` shows it is representable by proper morphisms of
  schemes, using `FppfStack.mapOfSchemeHom_hasRepresentableProperty` (which represents every base
  change of `stackProj X 𝒜` by the actual scheme-theoretic pullback of `toBase X 𝒜`, with no
  reference to `𝒜` beyond the properness of its structure morphism) together with
  `RelativeProj.toBase_isProper`.
* `stackProj_isRepresentable` records the weaker fact that `stackProj X 𝒜` is representable by
  schemes at all, regardless of any finiteness hypothesis on `𝒜`.

## A general pullback of `GradedAlgebraData` is not constructed here

Unlike the affine case (`RelativeSpecStack.AlgebraData.pullback`), no general pullback
`GradedAlgebraData.pullback (𝒜 : GradedAlgebraData X) (f : T ⟶ X) : GradedAlgebraData T` is
constructed in this file, and consequently no analogue of `RelativeSpecStack`'s
`isPullback_relativeSpecPullback`, `relativeSpecPullbackCompIso` or the stack-language universal
property is proved here either. The reason is specific to `Proj` versus `Spec`: an *affine*
morphism `g : C ⟶ X` is *equivalent* data to a quasi-coherent algebra on `X` (its own pushforward
of sections, `RelativeSpec.AlgebraData.ofAffineHom g`), so pulling back the structure morphism of
`relativeSpec X 𝒜` along any `f : T ⟶ X` and reading off the algebra of sections of the resulting
affine morphism recovers a `GradedAlgebraData`-free, purely categorical, construction of the
pullback algebra. A *proper* morphism carries no such canonical grading: exhibiting it as a
relative `Proj` requires an auxiliary choice (a relatively ample graded algebra of sections), which
`toBase X 𝒜` alone, after an arbitrary base change, does not automatically supply again. Concretely,
`ProjBaseChange.lean` records the compatibility of `Proj` with base change only as a *hypothesis*
on an already-given graded ring map (`GradedHomOver.IsBaseChange`, `IsGradedBaseChangeAlong`), not
as a construction producing the base-changed graded algebra from `𝒜` and `f` alone; assembling such
a construction into a full `GradedAlgebraData T` (compatible on every affine open of an arbitrary
test scheme `T`, with the transition/base-change fields of the structure) would essentially replay
the gluing argument that builds `relativeProj` itself, relative to the covering system induced by
`f`, and is out of scope for this file. The representability statement below does not need this: it
uses only the actual categorical scheme pullback of `toBase X 𝒜` (via
`FppfStack.schemeHomPresentation`), exactly as
`RelativeSpecStack.stackSpec_hasRepresentableProperty_isAffineHom` does for the affine case.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

open RelativeProj

universe u

noncomputable section

/-- The morphism of represented stacks induced by the structure map of a relative `Proj`: the
image of `toBase X 𝒜` under the functoriality of `representedStack`. -/
def stackProj (X : Scheme.{u}) (𝒜 : GradedAlgebraData X) :
    StackHom (representedStack (relativeProj X 𝒜)) (representedStack X) :=
  FppfStack.mapOfSchemeHom (toBase X 𝒜)

/-- The structure morphism of a relative `Proj` of a graded algebra which is affine-locally of
finite type over its degree-zero part, with degree-zero part the section ring, viewed as a
morphism of represented stacks, is representable by proper morphisms: every base change by a test
object over a scheme `T` is represented by the scheme-theoretic pullback of `toBase X 𝒜`, whose
structure map to `T` is proper (`RelativeProj.toBase_isProper`), using that properness of scheme
morphisms is stable under base change. -/
theorem stackProj_hasRepresentableProperty_isProper (X : Scheme.{u}) (𝒜 : GradedAlgebraData X)
    [∀ U, Algebra.FiniteType (𝒜.grading U 0) (𝒜.ring U)]
    (h0 : ∀ U, Function.Bijective (algebraMap Γ(X, U.1) (𝒜.grading U 0))) :
    (stackProj X 𝒜).HasRepresentableProperty
      (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) :=
  FppfStack.mapOfSchemeHom_hasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u})
    (toBase X 𝒜) (toBase_isProper X 𝒜 h0)

/-- The structure morphism of a relative `Proj`, viewed as a morphism of represented stacks, is
representable by schemes, with no finiteness hypothesis on `𝒜` (the property `⊤` is stable under
base change). -/
theorem stackProj_isRepresentable (X : Scheme.{u}) (𝒜 : GradedAlgebraData X) :
    (stackProj X 𝒜).IsRepresentable :=
  StackHom.isRepresentable_of_hasRepresentableProperty _ _
    (FppfStack.mapOfSchemeHom_hasRepresentableProperty (⊤ : MorphismProperty Scheme.{u})
      (toBase X 𝒜) trivial)

end

end GromovWitten.AlgebraicGeometry
