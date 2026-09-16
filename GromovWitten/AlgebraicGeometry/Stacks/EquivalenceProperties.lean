/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.EquivalencePresentation

/-!
# Representable properties under equivalences of source and target stacks

Representable properties were already invariant under an invertible 2-cell between morphisms
with fixed source and target.  This file proves the stronger geometric invariance under changing
either stack by an equivalence.  The cancellation 2-cells are built from the displayed inverse
laws, associators, and unitors; the proof does not accept a property-comparison theorem as data.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackEquivalenceData

variable {A B C : FppfStack.{u}}

/-- Precomposing by an equivalence and then its inverse cancels up to the constructed coherence
2-cell. -/
noncomputable def cancelPrecompositionIso
    (E : StackEquivalenceData A B) (f : StackHom B C) : StackIso2
    (Pseudofunctor.StrongTrans.vcomp E.inv
      (Pseudofunctor.StrongTrans.vcomp E.hom f)) f :=
  ((StackIso2.associator E.inv E.hom f).symm.trans
    (E.invHom.whiskerRight f)).trans
    (StackIso2.leftUnitor f)

/-- Postcomposing by an equivalence and then its inverse cancels up to the constructed coherence
2-cell. -/
noncomputable def cancelPostcompositionIso
    (E : StackEquivalenceData B C) (f : StackHom A B) : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp f E.hom) E.inv) f :=
  ((StackIso2.associator f E.hom E.inv).trans
    (StackIso2.whiskerLeft f E.homInv)).trans
    (StackIso2.rightUnitor f)

/-- A multiplicative representable property is unchanged by precomposition with an equivalence
of source stacks. -/
theorem precompose_hasRepresentableProperty_iff
    (E : StackEquivalenceData A B) (f : StackHom B C)
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] :
    StackHom.HasRepresentableProperty
      (Pseudofunctor.StrongTrans.vcomp E.hom f : StackHom A C) P ↔
      f.HasRepresentableProperty P := by
  constructor
  · intro h
    have hinv := E.inv_hasRepresentableProperty P
    have hround := StackHom.comp_hasRepresentableProperty P hinv h
    exact (StackHom.hasRepresentableProperty_congr P
      (E.cancelPrecompositionIso f)).mp hround
  · intro h
    exact StackHom.comp_hasRepresentableProperty P
      (E.hom_hasRepresentableProperty P) h

/-- A multiplicative representable property is unchanged by postcomposition with an equivalence
of target stacks. -/
theorem postcompose_hasRepresentableProperty_iff
    (E : StackEquivalenceData B C) (f : StackHom A B)
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] :
    StackHom.HasRepresentableProperty
      (Pseudofunctor.StrongTrans.vcomp f E.hom : StackHom A C) P ↔
      f.HasRepresentableProperty P := by
  constructor
  · intro h
    have hinv := E.inv_hasRepresentableProperty P
    have hround := StackHom.comp_hasRepresentableProperty P h hinv
    exact (StackHom.hasRepresentableProperty_congr P
      (E.cancelPostcompositionIso f)).mp hround
  · intro h
    exact StackHom.comp_hasRepresentableProperty P h
      (E.hom_hasRepresentableProperty P)

end StackEquivalenceData

namespace StackHom

variable {X Y X' Y' : FppfStack.{u}}

/-- Multiplicative representable properties are invariant under simultaneous equivalences of
source and target, provided the square commutes up to the displayed invertible 2-cell. -/
theorem hasRepresentableProperty_equivalence_iff
    (f : StackHom X Y) (f' : StackHom X' Y')
    (source : StackEquivalenceData X X')
    (target : StackEquivalenceData Y Y')
    (compatible : StackIso2
      (Pseudofunctor.StrongTrans.vcomp source.hom f')
      (Pseudofunctor.StrongTrans.vcomp f target.hom))
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] :
    f.HasRepresentableProperty P ↔ f'.HasRepresentableProperty P := by
  constructor
  · intro hf
    have htarget :
        StackHom.HasRepresentableProperty
          (Pseudofunctor.StrongTrans.vcomp f target.hom : StackHom X Y') P :=
      (target.postcompose_hasRepresentableProperty_iff f P).mpr hf
    have hsource :
        StackHom.HasRepresentableProperty
          (Pseudofunctor.StrongTrans.vcomp source.hom f' : StackHom X Y') P :=
      (hasRepresentableProperty_congr P compatible).mpr htarget
    exact (source.precompose_hasRepresentableProperty_iff f' P).mp hsource
  · intro hf'
    have hsource :
        StackHom.HasRepresentableProperty
          (Pseudofunctor.StrongTrans.vcomp source.hom f' : StackHom X Y') P :=
      (source.precompose_hasRepresentableProperty_iff f' P).mpr hf'
    have htarget :
        StackHom.HasRepresentableProperty
          (Pseudofunctor.StrongTrans.vcomp f target.hom : StackHom X Y') P :=
      (hasRepresentableProperty_congr P compatible).mp hsource
    exact (target.postcompose_hasRepresentableProperty_iff f P).mp htarget

end StackHom

end GromovWitten.AlgebraicGeometry
