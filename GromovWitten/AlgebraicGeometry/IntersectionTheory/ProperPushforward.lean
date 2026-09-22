/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroup
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.LocalRing.Length

/-!
# Norms and codimension-one orders

The proper pushforward in `ChowGroup.lean` already has the residue-degree coefficient formula.
This file proves a local algebraic input to the missing norm/divisor theorem. For a finite free
domain algebra over a one-dimensional Noetherian principal ideal domain, Smith normal form
identifies the order of the determinant norm with the length of the principal quotient. For a
local algebra map, restriction of scalars then gives the residue-field length factor.

The final two lemmas separately evaluate Galois norms for an order map whose restriction and
Galois invariance are hypotheses. They do not establish those hypotheses for geometric valuations.
No scheme-level norm/divisor identity or proper pushforward on Chow quotients is constructed here;
these still need the comparison with orders at all points above a codimension-one point and the
global principal-divisor argument, including dimension-drop cancellation.
-/

open CategoryTheory WithZero

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open Ideal Module

/-! ## Smith normal form and the norm/cokernel length identity -/

/-- For a finite free algebra over a one-dimensional Noetherian principal ideal domain, the order
of the actual determinant norm of a nonzero element is the module length of its actual principal
quotient.  The proof uses Smith normal form: `FreeModule.Norm` identifies the determinant norm with
the product of Smith coefficients, and `Ideal.quotientEquivPiSpan` identifies the quotient with the
product of the corresponding cyclic quotients. -/
theorem ord_norm_eq_length_quotient
    {R S : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {ι : Type*} [Finite ι] (b : Basis ι R S)
    {f : S} (hf : f ≠ 0) :
    Ring.ord R (Algebra.norm R f) =
      Module.length R (S ⧸ Ideal.span ({f} : Set S)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let I : Ideal S := Ideal.span ({f} : Set S)
  have hI : I ≠ (⊥ : Ideal S) := Ideal.span_singleton_eq_bot.not.2 hf
  let a : ι → R := fun i ↦ Ideal.smithCoeffs b I hI i
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    exact Ideal.smithCoeffs_ne_zero b I hI i
  have hsnf : Associated (Algebra.norm R f) (∏ i, a i) := by
    exact associated_norm_prod_smith b hf
  have hprod : Ring.ord R (Algebra.norm R f) = Ring.ord R (∏ i, a i) :=
    Ring.ord_eq_of_associated hsnf
  rw [hprod]
  have hprodord : Ring.ord R (∏ i, a i) = ∑ i, Ring.ord R (a i) := by
    have haux : ∀ s : Finset ι, Ring.ord R (s.prod a) =
        s.sum (fun i ↦ Ring.ord R (a i)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s his ih =>
        rw [Finset.prod_insert his, Finset.sum_insert his]
        rw [Ring.ord_mul R]
        · rw [ih]
        · exact mem_nonZeroDivisors_of_ne_zero
            (Finset.prod_ne_zero_iff.mpr (fun j hj ↦ ha j))
    exact haux Finset.univ
  rw [hprodord]
  change _ = Module.length R (S ⧸ I)
  rw [(Ideal.quotientEquivPiSpan I b hI).length_eq,
    Module.length_pi_of_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- In the local case, the same identity is residue-degree weighted.  The factor is obtained from
Mathlib's actual restriction-of-scalars length theorem, so it is the residue-field multiplicity
used by proper cycle pushforward. -/
theorem ord_norm_eq_ord_mul_residueLength
    {R S : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    {ι : Type*} [Finite ι] (b : Basis ι R S)
    {f : S} (hf : f ≠ 0) :
    Ring.ord R (Algebra.norm R f) =
      Ring.ord S f * Module.length (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) := by
  rw [ord_norm_eq_length_quotient b hf]
  let I : Ideal S := Ideal.span ({f} : Set S)
  change Module.length R (S ⧸ I) = _
  rw [IsLocalRing.length_restrictScalars R S (S ⧸ I)]
  rfl

/-! ## The finite Galois norm formula for an order hom -/

/-- For a finite Galois field extension, a multiplicative order on the upper field which restricts
to the base order and is invariant under every base automorphism evaluates the actual field norm
as the extension degree times the upper order.  No divisor-preservation statement is assumed or
encoded: the conclusion is obtained from `Algebra.norm_eq_prod_automorphisms`. -/
theorem order_norm_eq_pow_finrank_of_isGalois
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (orderK : K →*₀ ℤᵐ⁰) (orderL : L →*₀ ℤᵐ⁰)
    (hrestriction : ∀ a : K,
      orderL (algebraMap K L a) = orderK a)
    (hinvariant : ∀ (σ : Gal(L / K)) (x : L), orderL (σ x) = orderL x)
    (x : L) :
    orderK (Algebra.norm K x) = orderL x ^ Module.finrank K L := by
  calc
    orderK (Algebra.norm K x) =
        orderL (algebraMap K L (Algebra.norm K x)) := (hrestriction _).symm
    _ = orderL (∏ σ : Gal(L / K), σ x) := by
      rw [Algebra.norm_eq_prod_automorphisms (K := K) (L := L) x]
    _ = ∏ σ : Gal(L / K), orderL (σ x) := by
      exact map_prod orderL (fun σ : Gal(L / K) ↦ σ x) Finset.univ
    _ = ∏ σ : Gal(L / K), orderL x := by
      apply Finset.prod_congr rfl
      intro σ hσ
      exact hinvariant σ x
    _ = orderL x ^ Fintype.card (Gal(L / K)) := by
      rw [Finset.prod_const]
      rfl
    _ = orderL x ^ Module.finrank K L := by
      rw [← IsGalois.card_aut_eq_finrank K L]
      rw [Nat.card_eq_fintype_card]

/-! ## The order-of-vanishing specialization -/

/-- The preceding formula specialized to the order maps of one-dimensional Noetherian domains and
their fraction fields.  The hypotheses are exactly local valuation statements: `hrestriction`
identifies the order on the base fraction field with the order after scalar extension, while
`hinvariant` states that the chosen codimension-one order is unchanged by a Galois conjugation.
The equality itself is proved from the norm product formula, rather than supplied as a field of a
structure. -/
theorem ordFrac_norm_eq_pow_finrank_of_isGalois
    {R S K L : Type u} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]
    [Field K] [Field L] [Algebra R K] [Algebra S L]
    [IsFractionRing R K] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hrestriction : ∀ a : K,
      Ring.ordFrac S (algebraMap K L a) = Ring.ordFrac R a)
    (hinvariant : ∀ (σ : Gal(L / K)) (x : L),
      Ring.ordFrac S (σ x) = Ring.ordFrac S x)
    (x : L) :
    Ring.ordFrac R (Algebra.norm K x) =
      Ring.ordFrac S x ^ Module.finrank K L := by
  exact order_norm_eq_pow_finrank_of_isGalois
    (Ring.ordFrac R) (Ring.ordFrac S) hrestriction hinvariant x

end GromovWitten.AlgebraicGeometry.IntersectionTheory
