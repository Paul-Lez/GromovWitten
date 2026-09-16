/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RingHomProperties
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Finite complete-intersection presentations

This file records the commutative-algebra input used by local complete-intersection morphisms.
A finite presentation is a complete-intersection presentation when its displayed relations form
a regular sequence in the ambient polynomial ring.  An algebra is globally a complete
intersection when it admits such a presentation.

The definition is deliberately algebraic and global.  Its Zariski-local closure, and the
corresponding scheme-morphism property, belong in the subsequent syntomic layer.
-/

namespace Algebra

universe u v

noncomputable section

namespace Presentation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A finite presentation is a complete-intersection presentation when its ordered family of
relations is a regular sequence in the ambient polynomial ring. -/
def IsCompleteIntersection {n m : ℕ} (P : Presentation R S (Fin n) (Fin m)) : Prop :=
  RingTheory.Sequence.IsRegular P.Ring (List.ofFn P.relation)

/-- Transporting the target algebra through an algebra equivalence preserves a displayed
complete-intersection presentation. -/
theorem IsCompleteIntersection.ofAlgEquiv {n m : ℕ}
    {P : Presentation R S (Fin n) (Fin m)} (hP : P.IsCompleteIntersection)
    {T : Type v} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    (P.ofAlgEquiv e).IsCompleteIntersection :=
  hP

end Presentation

/-- An algebra is a global complete intersection if it admits a finite polynomial presentation
whose displayed relations form a regular sequence. -/
class IsCompleteIntersection (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_presentation : ∃ (n m : ℕ) (P : Presentation R S (Fin n) (Fin m)),
    P.IsCompleteIntersection

namespace IsCompleteIntersection

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The identity algebra is a complete intersection, presented with no generators and no
relations.  This is the algebraic input for the identity locally complete-intersection
morphism; in particular, it is constructed rather than postulated as a closure axiom. -/
instance self (R : Type u) [CommRing R] [Nontrivial R] : IsCompleteIntersection R R := by
  let P : Presentation R R (Fin 0) (Fin 0) := {
    toGenerators := Generators.ofSurjective (fun i : Fin 0 ↦ Fin.elim0 i) (by
      intro r
      exact ⟨MvPolynomial.C r, by simp⟩)
    relation := Fin.elim0
    span_range_relation_eq_ker := by
      simp only [Set.range_eq_empty, Ideal.span_empty]
      symm
      rw [Generators.ker_eq_ker_aeval_val]
      rw [← RingHom.injective_iff_ker_eq_bot]
      change Function.Injective (MvPolynomial.aeval Fin.elim0)
      rw [MvPolynomial.aeval_injective_iff_of_isEmpty]
      exact Function.injective_id }
  refine ⟨0, 0, P, ?_⟩
  change RingTheory.Sequence.IsRegular P.Ring (List.ofFn P.relation)
  simpa only [List.ofFn_zero] using
    (RingTheory.Sequence.IsRegular.nil P.Ring P.Ring)

/-- A global complete-intersection algebra is finitely presented. -/
theorem finitePresentation [IsCompleteIntersection R S] : FinitePresentation R S := by
  obtain ⟨n, m, P, -⟩ := exists_presentation (R := R) (S := S)
  exact P.finitePresentation_of_isFinite

/-- Global complete-intersection presentations transport across algebra equivalences. -/
theorem of_algEquiv [IsCompleteIntersection R S]
    {T : Type v} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    IsCompleteIntersection R T := by
  obtain ⟨n, m, P, hP⟩ := exists_presentation (R := R) (S := S)
  exact ⟨⟨n, m, P.ofAlgEquiv e, hP.ofAlgEquiv e⟩⟩

end IsCompleteIntersection

/-- A globally syntomic algebra is flat and admits a finite global complete-intersection
presentation.  This is an affine certificate for the Zariski-local scheme-theoretic notion of
a syntomic morphism. -/
class IsGloballySyntomic (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : Prop extends
    Module.Flat R S, IsCompleteIntersection R S

namespace IsGloballySyntomic

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A globally syntomic algebra is finitely presented. -/
theorem finitePresentation [IsGloballySyntomic R S] : FinitePresentation R S :=
  IsCompleteIntersection.finitePresentation

end IsGloballySyntomic

end

end Algebra

namespace RingHom

universe u

noncomputable section

open CategoryTheory

/-- A ring map has a displayed complete-intersection presentation when its induced algebra
structure admits a finite polynomial presentation by a regular sequence. -/
def HasCompleteIntersectionPresentation {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IsCompleteIntersection R S

/-- A ring map is a global complete intersection when it is isomorphic, as an arrow of
commutative rings, to a map with a displayed complete-intersection presentation.

The isomorphism closure is part of the definition so that affine scheme charts do not depend on
the chosen identifications of their section rings. -/
def IsCompleteIntersection {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  ∃ (R' S' : CommRingCat.{u}) (g : R' ⟶ S'),
    HasCompleteIntersectionPresentation g.hom ∧
      Nonempty (Arrow.mk (CommRingCat.ofHom f) ≅ Arrow.mk g)

namespace IsCompleteIntersection

/-- A displayed complete-intersection algebra gives a complete-intersection ring map. -/
theorem of_algebraMap {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsCompleteIntersection R S] :
    IsCompleteIntersection (algebraMap R S) := by
  have h : HasCompleteIntersectionPresentation (algebraMap R S) := by
    rw [HasCompleteIntersectionPresentation, toAlgebra_algebraMap]
    infer_instance
  exact ⟨CommRingCat.of R, CommRingCat.of S,
    CommRingCat.ofHom (algebraMap R S), h, ⟨Iso.refl _⟩⟩

/-- Global complete-intersection ring maps are invariant under isomorphisms of their source and
target rings. -/
theorem respectsIso : RingHom.RespectsIso (@IsCompleteIntersection) := by
  constructor
  · intro R S T _ _ _ f e hf
    obtain ⟨R', S', g, hg, hi⟩ := hf
    refine ⟨R', S', g, hg, ?_⟩
    exact hi.map fun i ↦
      (Arrow.isoMk' (CommRingCat.ofHom (e.toRingHom.comp f))
        (CommRingCat.ofHom f) (Iso.refl _) e.symm.toCommRingCatIso (by ext; simp)).trans i
  · intro R S T _ _ _ f e hf
    obtain ⟨R', S', g, hg, hi⟩ := hf
    refine ⟨R', S', g, hg, ?_⟩
    exact hi.map fun i ↦
      (Arrow.isoMk' (CommRingCat.ofHom (f.comp e.toRingHom))
        (CommRingCat.ofHom f) e.toCommRingCatIso (Iso.refl _) (by ext; simp)).trans i

end IsCompleteIntersection

end


end RingHom
