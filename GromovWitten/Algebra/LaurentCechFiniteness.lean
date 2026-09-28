/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Data.Int.Interval
import GromovWitten.Algebra.SubmoduleIntersection

/-!
# Finiteness for a Laurent Čech quotient

This is the algebra behind the standard two-chart Čech computation: a finitely
generated Laurent module has finite quotient by two stable submodules whose
elements clear denominators in the positive and negative directions.  It is a
module-theoretic statement and does not assert finiteness for general proper
objects.
-/

open scoped LaurentPolynomial
open LaurentPolynomial
noncomputable section

namespace GromovWitten.Algebra

universe u v w

variable {R : Type u} {N : Type v} [CommRing R] [AddCommGroup N]
variable [Module R[T;T⁻¹] N] [Module R N] [IsScalarTower R R[T;T⁻¹] N]

omit [IsScalarTower R R[T;T⁻¹] N] in
private lemma pos_smul_mem (A : Submodule R N)
    (hA : ∀ x ∈ A, (T 1 : R[T;T⁻¹]) • x ∈ A) {x : N} (hx : x ∈ A) (n : ℕ) :
    (T (n : ℤ) : R[T;T⁻¹]) • x ∈ A := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have h := hA _ ih
    simpa only [smul_smul, ← T_add, Nat.cast_add, Nat.cast_one, add_comm] using h

omit [IsScalarTower R R[T;T⁻¹] N] in
private lemma neg_smul_mem (B : Submodule R N)
    (hB : ∀ x ∈ B, (T (-1) : R[T;T⁻¹]) • x ∈ B) {x : N} (hx : x ∈ B) (n : ℕ) :
    (T (-(n : ℤ)) : R[T;T⁻¹]) • x ∈ B := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have h := hB _ ih
    convert h using 1
    rw [smul_smul, ← T_add]
    congr 2
    omega

/--
If positive and negative Laurent powers of finitely many generators enter two
stable submodules, their quotient is finite over the coefficient ring.  This
is the algebraic finiteness input for the usual two-chart Čech `H¹` module.
-/
theorem finiteLaurentCechQuotient [Module.Finite R[T;T⁻¹] N] (A B : Submodule R N)
    (hA : ∀ x ∈ A, (T 1 : R[T;T⁻¹]) • x ∈ A)
    (hB : ∀ x ∈ B, (T (-1) : R[T;T⁻¹]) • x ∈ B)
    (hpos : ∀ x : N, ∃ n : ℕ, (T (n : ℤ) : R[T;T⁻¹]) • x ∈ A)
    (hneg : ∀ x : N, ∃ n : ℕ, (T (-(n : ℤ)) : R[T;T⁻¹]) • x ∈ B) :
    Module.Finite R (N ⧸ (A ⊔ B)) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R[T;T⁻¹]) (M := N)
  choose a ha using hpos
  choose b hb using hneg
  let q := (A ⊔ B).mkQ
  let G : Set (N ⧸ (A ⊔ B)) :=
    ⋃ x ∈ (s : Set N), (fun k : ℤ => q ((T k : R[T;T⁻¹]) • x)) ''
      Set.Icc (-(b x : ℤ)) (a x : ℤ)
  have hG : G.Finite := s.finite_toSet.biUnion fun x _ => (Set.finite_Icc _ _).image _
  let K := Submodule.span R G
  have hbound (x : N) (hx : x ∈ s) (k : ℤ) : q ((T k : R[T;T⁻¹]) • x) ∈ K := by
    by_cases hhi : (a x : ℤ) ≤ k
    · have hxA := pos_smul_mem A hA (ha x) (k - a x).toNat
      have hk : ((k - a x).toNat : ℤ) + a x = k := by omega
      rw [smul_smul, ← T_add, hk] at hxA
      have hz : q ((T k : R[T;T⁻¹]) • x) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ((show A ≤ A ⊔ B from le_sup_left) hxA)
      rw [hz]
      exact K.zero_mem
    by_cases hlo : k ≤ -(b x : ℤ)
    · have hxB := neg_smul_mem B hB (hb x) (-b x - k).toNat
      have hk : -((-(b x : ℤ) - k).toNat : ℤ) + -(b x : ℤ) = k := by omega
      rw [smul_smul, ← T_add, hk] at hxB
      have hz : q ((T k : R[T;T⁻¹]) • x) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ((show B ≤ A ⊔ B from le_sup_right) hxB)
      rw [hz]
      exact K.zero_mem
    apply Submodule.subset_span
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx,
      ⟨k, ⟨by omega, by omega⟩, rfl⟩⟩⟩
  have hspan (x : N) (hx : x ∈ Submodule.span R[T;T⁻¹] (s : Set N)) :
      ∀ k : ℤ, q ((T k : R[T;T⁻¹]) • x) ∈ K := by
    induction hx using Submodule.span_induction with
    | mem y hy => exact hbound y hy
    | zero => intro k; simp only [smul_zero, map_zero]; exact K.zero_mem
    | add x y _ _ hx hy =>
      intro k
      simpa only [smul_add, map_add] using K.add_mem (hx k) (hy k)
    | smul c x _ hx =>
      intro k
      induction c using LaurentPolynomial.induction_on' with
      | add c d hc hd =>
        simpa only [add_smul, smul_add, map_add] using K.add_mem hc hd
      | C_mul_T j r =>
        have h := K.smul_mem r (hx (k + j))
        have heq : (T k : R[T;T⁻¹]) • ((C r * T j) • x) =
            r • ((T (k + j) : R[T;T⁻¹]) • x) := by
          rw [smul_smul, ← mul_assoc, mul_comm (T k) (C r), mul_assoc, ← T_add,
            mul_smul, C_eq_algebraMap, algebraMap_smul]
        rw [heq, map_smul]
        exact h
  have htop : K = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨x, rfl⟩ := (A ⊔ B).mkQ_surjective z
    have hx := hspan x (by rw [hs]; trivial) 0
    simpa only [T_zero, one_smul] using hx
  rw [Module.finite_def, ← htop]
  exact Submodule.fg_span hG

/-!
The next result is the image-intersection step used when a Laurent module maps
to a larger module: the finite Laurent quotient controls the kernel part of
the connecting difference map, while `Submodule.finite_inf_map_of...` lifts
this to the intersection of the two image lattices.
-/

theorem finiteLaurentCechIntersectionImage
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {S : Type v} [AddCommGroup S] [Module R[T;T⁻¹] S] [Module R S]
    [IsScalarTower R R[T;T⁻¹] S] [Module.Finite R[T;T⁻¹] S]
    {N' : Type w} [AddCommGroup N'] [Module R[T;T⁻¹] N'] [Module R N']
    [IsScalarTower R R[T;T⁻¹] N']
    (q : S →ₗ[R[T;T⁻¹]] N') (A B : Submodule R S)
    [Module.Finite R (A ⊓ B : Submodule R S)]
    (hA : ∀ x ∈ A, (T 1 : R[T;T⁻¹]) • x ∈ A)
    (hB : ∀ x ∈ B, (T (-1) : R[T;T⁻¹]) • x ∈ B)
    (hpos : ∀ x : S, ∃ n : ℕ, (T (n : ℤ) : R[T;T⁻¹]) • x ∈ A)
    (hneg : ∀ x : S, ∃ n : ℕ, (T (-(n : ℤ)) : R[T;T⁻¹]) • x ∈ B) :
    Module.Finite R
      (A.map (q.restrictScalars R) ⊓ B.map (q.restrictScalars R) : Submodule R N') := by
  let K := q.ker
  let i : K →ₗ[R] S := K.subtype.restrictScalars R
  let AK := A.comap i
  let BK := B.comap i
  have : IsNoetherianRing R[T;T⁻¹] :=
    IsLocalization.isNoetherianRing (.powers (Polynomial.X : Polynomial R)) _ inferInstance
  have : Module.Finite R[T;T⁻¹] K := inferInstance
  have hfin : Module.Finite R (K ⧸ (AK ⊔ BK)) :=
    finiteLaurentCechQuotient AK BK
      (fun x hx => hA x hx) (fun x hx => hB x hx)
      (fun x => hpos x) (fun x => hneg x)
  have : Module.Finite R ((q.restrictScalars R).ker ⧸
      (A.comap (q.restrictScalars R).ker.subtype ⊔
        B.comap (q.restrictScalars R).ker.subtype)) := by
    change Module.Finite R (K ⧸ (AK ⊔ BK))
    exact hfin
  exact Submodule.finite_inf_map_of_finite_inf_of_finite_ker_quotient
    (q.restrictScalars R) A B

end GromovWitten.Algebra
