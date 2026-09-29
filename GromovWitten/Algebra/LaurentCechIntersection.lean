/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.LaurentLattices
import GromovWitten.Algebra.LaurentCechFiniteness
import GromovWitten.Algebra.PolynomialLocalizationKernel
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite Laurent Čech intersections

Finite positive and negative Laurent lattices with mutually clearing generators have finite image
intersection. The same orbit calculation records finite Laurent-module images under compatible
polynomial and Laurent actions.
-/

open Polynomial
open scoped LaurentPolynomial
open LaurentPolynomial
noncomputable section
namespace GromovWitten.Algebra
universe u v w z
variable {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N]
  [Module R[T;T⁻¹] N] [Module R N] [IsScalarTower R R[T;T⁻¹] N]
  {I : Type w} {J : Type z}

omit [IsScalarTower R R[T;T⁻¹] N] in
private lemma pos_mem (A : Submodule R N)
    (hA : ∀ x ∈ A, (T (R := R) 1 : R[T;T⁻¹]) • x ∈ A) {x : N} (hx : x ∈ A) (n : ℕ) :
    (T (R := R) (n : ℤ) : R[T;T⁻¹]) • x ∈ A := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have h := hA _ ih
    simpa only [smul_smul, ← T_add, Nat.cast_add, Nat.cast_one, add_comm] using h

omit [IsScalarTower R R[T;T⁻¹] N] in
private lemma neg_mem (B : Submodule R N)
    (hB : ∀ x ∈ B, (T (R := R) (-1) : R[T;T⁻¹]) • x ∈ B) {x : N} (hx : x ∈ B) (n : ℕ) :
    (T (R := R) (-(n : ℤ)) : R[T;T⁻¹]) • x ∈ B := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have h := hB _ ih
    convert h using 1
    rw [smul_smul, ← T_add]
    congr 2
    omega

omit [IsScalarTower R R[T;T⁻¹] N] in
private theorem latticeImageSpans (A B : Submodule R N) (a : I → N) (b : J → N)
    (ha : A = Submodule.span R (Set.range fun p : I × ℕ => (T (R := R) (p.2 : ℤ)) • a p.1))
    (hb : B = Submodule.span R (Set.range fun p : J × ℕ => (T (R := R) (-(p.2 : ℤ))) • b p.1))
    (hA : ∀ x ∈ A, (T (R := R) 1 : R[T;T⁻¹]) • x ∈ A)
    (hB : ∀ x ∈ B, (T (R := R) (-1) : R[T;T⁻¹]) • x ∈ B)
    (m : J → ℕ) (n : I → ℕ)
    (hm : ∀ j, (T (R := R) (m j : ℤ)) • b j ∈ A)
    (hn : ∀ i, (T (R := R) (-(n i : ℤ))) • a i ∈ B) :
    let v : I ⊕ J → N := Sum.elim a (fun j => (T (R := R) (m j : ℤ)) • b j)
    let d : I ⊕ J → ℤ := Sum.elim (fun i => -(n i : ℤ)) (fun j => -(m j : ℤ))
    Submodule.span R (Set.range fun p : (I ⊕ J) × ℕ => (T (R := R) (p.2 : ℤ)) • v p.1) = A ∧
    Submodule.span R (Set.range fun p : (I ⊕ J) × ℕ => (T (R := R) (d p.1 - p.2)) • v p.1) = B := by
  dsimp only
  have hai (i : I) : a i ∈ A := by
    rw [ha]
    simpa using (Submodule.subset_span (R := R)
      (Set.mem_range_self (i, 0) : (T (R := R) (0 : ℤ)) • a i ∈ Set.range
        (fun p : I × ℕ => (T (R := R) (p.2 : ℤ)) • a p.1)))
  constructor
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨i | j, k⟩, rfl⟩
      · exact pos_mem A hA (hai i) k
      · exact pos_mem A hA (hm j) k
    · rw [ha]
      apply Submodule.span_mono
      rintro _ ⟨⟨i, k⟩, rfl⟩
      exact ⟨(Sum.inl i, k), rfl⟩
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨i | j, k⟩, rfl⟩
      · have h := neg_mem B hB (hn i) k
        change (T (R := R) (-(n i : ℤ) - k)) • a i ∈ B
        rw [smul_smul, ← T_add] at h
        convert h using 1
        congr 2
        omega
      · have hbj : b j ∈ B := by
          rw [hb]
          simpa using (Submodule.subset_span (R := R)
            (Set.mem_range_self (j, 0) : (T (R := R) (-(0 : ℤ))) • b j ∈ Set.range
              (fun p : J × ℕ => (T (R := R) (-(p.2 : ℤ))) • b p.1)))
        have h := neg_mem B hB hbj k
        change (T (R := R) (-(m j : ℤ) - k)) • ((T (R := R) (m j : ℤ)) • b j) ∈ B
        rw [smul_smul, ← T_add]
        convert h using 1
        congr 2
        omega
    · rw [hb]
      apply Submodule.span_mono
      rintro _ ⟨⟨j, k⟩, rfl⟩
      refine ⟨(Sum.inr j, k), ?_⟩
      simp only [Sum.elim_inr, smul_smul, ← T_add]
      congr 2
      omega


/-- A finitely generated Laurent image has finite intersection of the two orbit lattices. -/
theorem finiteLaurentCechIntersection [IsNoetherianRing R] [Finite I] [Finite J]
    (A B : Submodule R N) (a : I → N) (b : J → N)
    (ha : A = Submodule.span R (Set.range fun p : I × ℕ => (T (R := R) (p.2 : ℤ)) • a p.1))
    (hb : B = Submodule.span R (Set.range fun p : J × ℕ => (T (R := R) (-(p.2 : ℤ))) • b p.1))
    (hA : ∀ x ∈ A, (T 1 : R[T;T⁻¹]) • x ∈ A)
    (hB : ∀ x ∈ B, (T (-1) : R[T;T⁻¹]) • x ∈ B)
    (hpos : ∀ j, ∃ m : ℕ, (T (R := R) (m : ℤ)) • b j ∈ A)
    (hneg : ∀ i, ∃ n : ℕ, (T (R := R) (-(n : ℤ))) • a i ∈ B) :
    Module.Finite R (A ⊓ B : Submodule R N) := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  choose m hm using hpos
  choose n hn using hneg
  let v : I ⊕ J → N := Sum.elim a (fun j => (T (R := R) (m j : ℤ)) • b j)
  let d : I ⊕ J → ℤ := Sum.elim (fun i => -(n i : ℤ)) (fun j => -(m j : ℤ))
  let q := Fintype.linearCombination R[T;T⁻¹] v
  have hsp := latticeImageSpans A B a b ha hb hA hB m n hm hn
  have hqa : (positiveLattice (R := R) (I ⊕ J)).map (q.restrictScalars R) = A := by
    rw [positiveLattice_eq_span_nat, Submodule.map_span, ← Set.range_comp]
    convert hsp.1 using 2
    congr 1
    funext p
    exact Fintype.linearCombination_apply_single R[T;T⁻¹] v p.1 _
  have hqb : (negativeLattice (R := R) d).map (q.restrictScalars R) = B := by
    rw [negativeLattice_eq_span_nat, Submodule.map_span, ← Set.range_comp]
    convert hsp.2 using 2
    congr 1
    funext p
    exact Fintype.linearCombination_apply_single R[T;T⁻¹] v p.1 _
  have := finite_positiveLattice_inf_negativeLattice (R := R) d
  have hf := finiteLaurentCechIntersectionImage q (positiveLattice (R := R) (I ⊕ J))
    (negativeLattice (R := R) d)
    (fun x hx => positiveLattice_smul_T _ hx)
    (fun x hx => negativeLattice_smul_T_neg d hx)
    (positiveLattice_clears (R := R)) (negativeLattice_clears (R := R) d)
  rw [hqa, hqb] at hf
  exact hf
end GromovWitten.Algebra

universe u₁ v₁ w₁

variable {R₁ : Type u₁} [CommRing R₁]
  {P₁ : Type v₁} [AddCommGroup P₁] [Module R₁[X] P₁] [Module R₁ P₁]
  [IsScalarTower R₁ R₁[X] P₁]
  {N₁ : Type w₁} [AddCommGroup N₁] [Module R₁ N₁]

/-- A polynomial image compatible with a Laurent shift is generated by finitely many Laurent
orbits. -/
theorem LinearMap.range_eq_span_laurent_orbits [Module.Finite R₁[X] P₁]
    [Module R₁[T;T⁻¹] N₁] [IsScalarTower R₁ R₁[T;T⁻¹] N₁]
    (f : P₁ →ₗ[R₁] N₁) (ε : ℤ)
    (hf : ∀ x, f ((X : R₁[X]) • x) = (T ε : R₁[T;T⁻¹]) • f x) :
    ∃ s : Finset N₁, f.range = Submodule.span R₁
      (Set.range fun p : s × ℕ =>
        (T (R := R₁) ((p.2 : ℤ) * ε)) • (p.1 : N₁)) := by
  classical
  have hpow (x : P₁) (n : ℕ) :
      f ((X ^ n : R₁[X]) • x) = (T (R := R₁) ((n : ℤ) * ε)) • f x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_smul, hf, ih, smul_smul, ← T_add]
      congr 2
      push_cast
      ring
  obtain ⟨s, hs⟩ := LinearMap.range_eq_span_polynomial_orbits f
  refine ⟨s.image f, ?_⟩
  rw [hs]
  congr 1
  ext y
  constructor
  · intro hy
    rcases Set.mem_iUnion.mp hy with ⟨x, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hxs, n, rfl⟩
    refine ⟨(⟨f x, Finset.mem_image.mpr ⟨x, hxs, rfl⟩⟩, n), ?_⟩
    exact (hpow x n).symm
  · rintro ⟨⟨x, n⟩, rfl⟩
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp x.property
    refine Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, n, ?_⟩⟩
    dsimp only
    rw [hpow, he]

universe u₂ v₂ w₂ z₂

variable {R₂ : Type u₂} [CommRing R₂] [IsNoetherianRing R₂]
  {P₂ : Type v₂} [AddCommGroup P₂] [Module R₂[X] P₂] [Module R₂ P₂]
  [IsScalarTower R₂ R₂[X] P₂] [Module.Finite R₂[X] P₂]
  {Q₂ : Type w₂} [AddCommGroup Q₂] [Module R₂[X] Q₂] [Module R₂ Q₂]
  [IsScalarTower R₂ R₂[X] Q₂] [Module.Finite R₂[X] Q₂]
  {N₂ : Type z₂} [AddCommGroup N₂] [Module R₂[T;T⁻¹] N₂] [Module R₂ N₂]
  [IsScalarTower R₂ R₂[T;T⁻¹] N₂]

/-- A finite intersection of polynomial images remains finite after Laurent localization
when the two images intertwine `X` with opposite Laurent shifts and all Laurent powers
can be cleared into the respective ranges. -/
theorem LinearMap.finite_range_inf_of_laurent_localization
    (f : P₂ →ₗ[R₂] N₂) (g : Q₂ →ₗ[R₂] N₂)
    (hf : ∀ x, f ((X : R₂[X]) • x) = (T 1 : R₂[T;T⁻¹]) • f x)
    (hg : ∀ x, g ((X : R₂[X]) • x) = (T (-1 : ℤ) : R₂[T;T⁻¹]) • g x)
    (hpos : ∀ x : N₂, ∃ n : ℕ, (T (n : ℤ) : R₂[T;T⁻¹]) • x ∈ f.range)
    (hneg : ∀ x : N₂, ∃ n : ℕ, (T (-(n : ℤ)) : R₂[T;T⁻¹]) • x ∈ g.range) :
    Module.Finite R₂ (f.range ⊓ g.range : Submodule R₂ N₂) := by
  obtain ⟨s, hs⟩ := f.range_eq_span_laurent_orbits 1 hf
  obtain ⟨t, ht⟩ := g.range_eq_span_laurent_orbits (-1) hg
  apply GromovWitten.Algebra.finiteLaurentCechIntersection f.range g.range
    (fun x : s => (x : N₂)) (fun x : t => (x : N₂))
  · simpa only [mul_one] using hs
  · simpa only [mul_neg_one] using ht
  · rintro _ ⟨x, rfl⟩
    exact ⟨(X : R₂[X]) • x, hf x⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨(X : R₂[X]) • x, hg x⟩
  · intro x
    exact hpos x
  · intro x
    exact hneg x
