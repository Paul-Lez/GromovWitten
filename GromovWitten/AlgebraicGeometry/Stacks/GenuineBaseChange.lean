/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.BaseChange
import GromovWitten.AlgebraicGeometry.Stacks.BilimitComparison

/-!
# Representable properties under arbitrary genuine stack base change

The canonical fibrewise pullback projection is representable whenever the original stack
morphism is.  Here that result is transported to every other genuine bicategorical pullback
presentation, using the equivalence constructed solely from the two bilimit universal
properties.  No comparison equivalence or projection 2-cell is accepted from the caller.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackTwoPullback

variable {X Y Z : FppfStack.{u}} {f : StackHom X Z} {g : StackHom Y Z}

/-- Canonical equivalence from an arbitrary genuine pullback to the constructed fibrewise
categorical pullback. -/
noncomputable def canonicalComparisonEquivalence (P : Genuine f g) :
    StackEquivalenceData P.pullback (canonicalGenuine f g).pullback :=
  presentationEquivalence P (canonicalGenuine f g)

/-- Under the canonical comparison equivalence, the second projection is identified with the
second projection of the supplied pullback presentation. -/
noncomputable def canonicalComparisonSndIso (P : Genuine f g) : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (canonicalComparisonEquivalence P).hom (canonicalGenuine f g).snd)
    P.snd :=
  (canonicalGenuine f g).bilimit.lift_snd P.toStackTwoPullback.selfCone

end StackTwoPullback

namespace StackHom

variable {X Y Z : FppfStack.{u}} (f : StackHom X Z) (g : StackHom Y Z)

/-- A multiplicative representable scheme-morphism property is preserved by the second
projection of every genuine bicategorical pullback presentation. -/
theorem twoPullbackSnd_hasRepresentableProperty
    (Q : StackTwoPullback.Genuine f g)
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    (hf : f.HasRepresentableProperty P) :
    Q.snd.HasRepresentableProperty P := by
  let E := StackTwoPullback.canonicalComparisonEquivalence Q
  have hE : E.hom.HasRepresentableProperty P :=
    E.hom_hasRepresentableProperty P
  have hcanonical :
      (StackTwoPullback.canonicalGenuine f g).snd.HasRepresentableProperty P :=
    fiberTwoPullbackSnd_hasRepresentableProperty f g P hf
  have hcomp := comp_hasRepresentableProperty P hE hcanonical
  exact (hasRepresentableProperty_congr P
    (StackTwoPullback.canonicalComparisonSndIso Q)).mp hcomp

end StackHom

end GromovWitten.AlgebraicGeometry
