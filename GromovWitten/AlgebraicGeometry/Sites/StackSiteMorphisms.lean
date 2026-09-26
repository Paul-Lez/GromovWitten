/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Sites.Stack
import GromovWitten.AlgebraicGeometry.Sites.StackComparison
import GromovWitten.AlgebraicGeometry.Sites.StackTopology
import GromovWitten.AlgebraicGeometry.Sites.StackCoverTopology

/-!
# The small-étale to lisse-étale inclusion, as a functor of sites

This file records what can currently be proved, in this development, about the inclusion
`smallEtaleToLisse X : SmallEtaleStackSite X ⥤ LisseEtaleStackSite X.toStack` as a comparison
of sites in the sense of `RingedSiteMorphism`.

The inclusion is fully faithful: it identifies each small-étale object with the same underlying
object of the Grothendieck total category, retagged with a weaker (lisse) presentation
predicate, and it acts as the identity on the (unchanged) underlying arrows. This is
`smallEtaleToLisse_fullyFaithful` below, together with the compatibility of the two forgetful
functors to the total category, `smallEtaleForget_eq_smallEtaleToLisse_comp_lisseEtaleForget`.

The continuity of `smallEtaleToLisse` for the pair of topologies `smallEtaleStackTopology X`
and `lisseEtaleStackTopology X.toStack`, and the resulting morphism of ringed sites, are
proved in `Sites/StackSiteContinuity.lean`; both topologies are `Functor.inducedTopology`s,
and that file first describes their covering sieves concretely (they are the sieves whose
pushforward to schemes is an étale covering sieve) and then verifies
`CompatiblePreserving`/`CoverPreserving` for the inclusion.
-/

open CategoryTheory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Sites

universe u

/-- The small-to-lisse inclusion is fully faithful: a morphism of lisse-étale objects between
(images of) small-étale objects is literally a morphism of the underlying total category
between the two underlying objects, and this is exactly the datum of a morphism of small-étale
objects. -/
def smallEtaleToLisse_fullyFaithful (X : DeligneMumfordStack.{u}) :
    (smallEtaleToLisse X).FullyFaithful where
  preimage g := InducedCategory.homMk g.hom

/-- The small-to-lisse inclusion is full. -/
instance smallEtaleToLisse_full (X : DeligneMumfordStack.{u}) :
    (smallEtaleToLisse X).Full :=
  (smallEtaleToLisse_fullyFaithful X).full

/-- The small-to-lisse inclusion is faithful. -/
instance smallEtaleToLisse_faithful (X : DeligneMumfordStack.{u}) :
    (smallEtaleToLisse X).Faithful :=
  (smallEtaleToLisse_fullyFaithful X).faithful

/-- Forgetting a small-étale object to the total category factors, strictly, through the
small-to-lisse inclusion followed by forgetting a lisse-étale object to the total category:
both composites send an object to its underlying total-category object and a morphism to its
underlying total-category morphism. -/
def smallEtaleForget_eq_smallEtaleToLisse_comp_lisseEtaleForget (X : DeligneMumfordStack.{u}) :
    smallEtaleToLisse X ⋙ lisseEtaleForget X.toStack ≅ smallEtaleForget X :=
  Iso.refl _

end GromovWitten.AlgebraicGeometry.Sites
