/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.FittingIdealsSheaf
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNodeIntrinsicThickness

/-!
# Intrinsic invariance of local-node thickness

The differential Fitting ideal used by the node chart is the presentation-free Fitting ideal of
the relative Kähler differentials.  This file transports that intrinsic ideal through arbitrary
algebra equivalences and then compares the resulting quotient algebras.  The displayed
`xy = a` presentations are used only to compute the intrinsic ideal, never as an input to its
invariance.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct Polynomial

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

universe u v

noncomputable section

/-! ## Presentation-free differential Fitting ideals -/

/-- Differential Fitting ideals are transported by an arbitrary algebra equivalence.  The
intermediate algebra structure is induced by the equivalence itself, so the ideal map below is
proved by the formally étale base-change theorem rather than assumed as a presentation fact. -/
theorem differentialFittingIdeal_map_algEquiv {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B]
    [_root_.Algebra.FinitePresentation R A]
    (e : A ≃ₐ[R] B) (i : ℕ) :
    Algebra.differentialFittingIdeal R B i =
      (Algebra.differentialFittingIdeal R A i).map e.toRingHom := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq
    (fun r => (e.commutes r).symm)
  let _ : Algebra.FormallyEtale A B := by
    exact Algebra.FormallyEtale.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId A B) e.bijective)
  exact Algebra.differentialFittingIdeal_of_formallyEtale R A B i

/-- The first intrinsic differential Fitting ideal is transported by an arbitrary algebra
equivalence. -/
theorem intrinsicDifferentialFittingIdeal_map_algEquiv {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B]
    [_root_.Algebra.FinitePresentation R A] (e : A ≃ₐ[R] B) :
    Algebra.differentialFittingIdeal R B 1 =
      (Algebra.differentialFittingIdeal R A 1).map e.toRingHom :=
  differentialFittingIdeal_map_algEquiv e 1

/-- The intrinsic differential-Fitting quotients are carried to one another by the actual
algebra equivalence induced by an algebra equivalence of the node algebras.  The ideal equality
used here is the formally-etale transport theorem above; it is not an assumed invariance axiom. -/
noncomputable def intrinsicDifferentialFittingQuotientAlgEquiv
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [_root_.Algebra.FinitePresentation R A]
    (e : A ≃ₐ[R] B) :
    (A ⧸ Algebra.differentialFittingIdeal R A 1) ≃ₐ[R]
      (B ⧸ Algebra.differentialFittingIdeal R B 1) := by
  apply Ideal.quotientEquivAlg
    (Algebra.differentialFittingIdeal R A 1)
    (Algebra.differentialFittingIdeal R B 1) e
  exact intrinsicDifferentialFittingIdeal_map_algEquiv e

/-- In particular, the module lengths that define node exponents agree for arbitrary isomorphic
node algebras over the same coefficient ring. -/
theorem intrinsicDifferentialFittingQuotientLength_eq
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [_root_.Algebra.FinitePresentation R A]
    (e : A ≃ₐ[R] B) :
    Module.length R (A ⧸ Algebra.differentialFittingIdeal R A 1) =
      Module.length R (B ⧸ Algebra.differentialFittingIdeal R B 1) :=
  (intrinsicDifferentialFittingQuotientAlgEquiv e).toLinearEquiv.length_eq

/-! ## The bridge for the concrete node presentation -/

/-- The computed presentation Fitting ideal of a node is its intrinsic differential Fitting ideal.
This is the direct presentation bridge from `FittingIdealsSheaf`. -/
theorem nodeDifferentialFittingIdeal_eq_intrinsic (R : Type u) [CommRing R]
    (π : R) (n : ℕ) :
    Algebra.differentialFittingIdeal R (Ring R π n) 1 =
      AlgebraPresentation.differentialFittingIdeal
        (completeIntersectionPresentation R π n) 1 := by
  exact Algebra.differentialFittingIdeal_eq_of_presentation
    (completeIntersectionPresentation R π n) 1

/-- The actual intrinsic quotient and the quotient used by the node thickness definition are
canonically equivalent as `R`-algebras. -/
noncomputable def nodeIntrinsicFittingQuotientEquiv (R : Type u) [CommRing R]
    (π : R) (n : ℕ) :
    (Ring R π n ⧸ Algebra.differentialFittingIdeal R (Ring R π n) 1) ≃ₐ[R]
      differentialFittingQuotient R π n := by
  apply Ideal.quotientEquivAlgOfEq R
  exact nodeDifferentialFittingIdeal_eq_intrinsic R π n

/-- The presentation quotient has the same `R`-module length as the intrinsic one. -/
theorem nodeIntrinsicThickness_eq_intrinsicQuotientLength (R : Type u) [CommRing R]
    (π : R) (n : ℕ) :
    nodeThickness R π n = Module.length R
      (Ring R π n ⧸ Algebra.differentialFittingIdeal R (Ring R π n) 1) := by
  rw [nodeThickness]
  exact (nodeIntrinsicFittingQuotientEquiv R π n).symm.toLinearEquiv.length_eq

/-- Node thickness is invariant under any algebra isomorphism between node charts over the same
coefficient ring.  Thus exponent uniqueness uses the intrinsic quotient and does not depend on
having two factorizations of one chosen smoothing parameter. -/
theorem nodeThickness_eq_of_algEquiv {R : Type u} [CommRing R]
    (π₁ π₂ : R) (n₁ n₂ : ℕ)
    (e : Ring R π₁ n₁ ≃ₐ[R] Ring R π₂ n₂) :
    nodeThickness R π₁ n₁ = nodeThickness R π₂ n₂ := by
  rw [nodeIntrinsicThickness_eq_intrinsicQuotientLength,
    nodeIntrinsicThickness_eq_intrinsicQuotientLength]
  exact intrinsicDifferentialFittingQuotientLength_eq e

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
