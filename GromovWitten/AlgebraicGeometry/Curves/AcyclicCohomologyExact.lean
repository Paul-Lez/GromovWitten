/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.CohomologyExactSequence

/-!
# Cohomology vanishing through short exact sequences

These bounded lemmas record the exactness consequences needed for affine
global-sections arguments.
-/

open CategoryTheory Limits Abelian
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X : Scheme.{u}} {S : ShortComplex X.Modules}

/-- Positive cohomology vanishing for the two outer terms implies positive
cohomology vanishing for the middle term of a short exact sequence. -/
lemma subsingleton_cohomology_X₂_of_subsingleton_cohomology_X₁_X₃
    (hS : S.ShortExact)
    (h₁ : ∀ n : ℕ, Subsingleton (cohomology X S.X₁ (n + 1)))
    (h₃ : ∀ n : ℕ, Subsingleton (cohomology X S.X₃ (n + 1))) :
    ∀ n : ℕ, Subsingleton (cohomology X S.X₂ (n + 1)) := by
  change ∀ n : ℕ, Subsingleton ((cohomologyFunctor X (n + 1)).obj S.X₂)
  intro n
  let h₁' : Subsingleton ((cohomologyFunctor X (n + 1)).obj S.X₁) := h₁ n
  let h₃' : Subsingleton ((cohomologyFunctor X (n + 1)).obj S.X₃) := h₃ n
  constructor
  intro x y
  have hxy : ((cohomologyFunctor X (n + 1)).map S.g).hom x =
      ((cohomologyFunctor X (n + 1)).map S.g).hom y :=
    h₃'.elim _ _
  have hdiff : ((cohomologyFunctor X (n + 1)).map S.g).hom (x - y) = 0 := by
    simp only [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := (cohomology_exact_at_X₂ hS (n + 1) (x - y)).1 hdiff
  have hfzero : ((cohomologyFunctor X (n + 1)).map S.f).hom z = 0 := by
    simpa using congrArg ((cohomologyFunctor X (n + 1)).map S.f).hom
      (h₁'.elim z 0)
  have hzero : x - y = 0 := by
    rw [← hz, hfzero]
  exact sub_eq_zero.mp hzero

/-- Positive cohomology vanishing for the first two terms implies positive
cohomology vanishing for the third term of a short exact sequence. -/
lemma subsingleton_cohomology_X₃_of_subsingleton_cohomology_X₁_X₂
    (hS : S.ShortExact)
    (h₁ : ∀ n : ℕ, Subsingleton (cohomology X S.X₁ (n + 1)))
    (h₂ : ∀ n : ℕ, Subsingleton (cohomology X S.X₂ (n + 1))) :
    ∀ n : ℕ, Subsingleton (cohomology X S.X₃ (n + 1)) := by
  change ∀ n : ℕ, Subsingleton ((cohomologyFunctor X (n + 1)).obj S.X₃)
  intro n
  let h₁' : Subsingleton ((cohomologyFunctor X (n + 2)).obj S.X₁) := h₁ (n + 1)
  let h₂' : Subsingleton ((cohomologyFunctor X (n + 1)).obj S.X₂) := h₂ n
  have hz : ∀ x : (cohomologyFunctor X (n + 1)).obj S.X₃, x = 0 := by
    intro x
    have hδ : cohomologyConnectingHom hS (n + 1) x = 0 :=
      h₁'.elim _ _
    obtain ⟨y, hy⟩ := (cohomology_exact_at_X₃ hS (n + 1) x).1 hδ
    have hyzero : y = 0 := h₂'.elim _ _
    rw [← hy, hyzero]
    exact map_zero _
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end GromovWitten.AlgebraicGeometry.Curves
