/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Polynomial localization kernels

Finite polynomial modules with locally nilpotent `X` action are finite over the
coefficient ring.  Over a Noetherian coefficient ring this applies to kernels
of `X`-localization maps.
-/

open Polynomial
noncomputable section

universe u v w

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M]
  [Module R[X] M] [Module R M] [IsScalarTower R R[X] M]

/-- A finite polynomial module on which the variable acts locally nilpotently is finite over
the coefficient ring. -/
theorem Module.Finite.of_polynomial_X_torsion [Module.Finite R[X] M]
    (h : ∀ x : M, ∃ n : ℕ, (X ^ n : R[X]) • x = 0) :
    Module.Finite R M := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R[X]) (M := M)
  choose n hn using h
  let G : Set M := ⋃ x ∈ (s : Set M),
    (fun i : ℕ => (X ^ i : R[X]) • x) '' Set.Iio (n x)
  have hG : G.Finite := s.finite_toSet.biUnion fun x _ => (Set.finite_Iio _).image _
  let K := Submodule.span R G
  have hpow (x : M) (hx : x ∈ s) (i : ℕ) : (X ^ i : R[X]) • x ∈ K := by
    by_cases hi : i < n x
    · exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨x,
        Set.mem_iUnion.mpr ⟨hx, ⟨i, hi, rfl⟩⟩⟩)
    · have he : i = (i - n x) + n x := by omega
      rw [he, pow_add, mul_smul, hn, smul_zero]
      exact K.zero_mem
  have hspan (x : M) (hx : x ∈ Submodule.span R[X] (s : Set M)) :
      ∀ i : ℕ, (X ^ i : R[X]) • x ∈ K := by
    induction hx using Submodule.span_induction with
    | mem x hx => exact hpow x hx
    | zero => intro i; simp only [smul_zero]; exact K.zero_mem
    | add x y _ _ hx hy => intro i; simpa only [smul_add] using K.add_mem (hx i) (hy i)
    | smul p x _ hx =>
      intro i
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simpa only [add_smul, smul_add] using K.add_mem hp hq
      | monomial j a =>
        have hh := K.smul_mem a (hx (i + j))
        have he : (X ^ i : R[X]) • ((monomial j a) • x) =
            a • ((X ^ (i + j) : R[X]) • x) := by
          rw [← C_mul_X_pow_eq_monomial, smul_smul, ← mul_assoc,
            mul_comm (X ^ i) (C a), mul_assoc, ← pow_add,
            mul_smul, ← Polynomial.algebraMap_eq, algebraMap_smul]
        rw [he]
        exact hh
  have htop : K = ⊤ := by
    apply top_unique
    intro x _
    have hx := hspan x (by rw [hs]; trivial) 0
    simpa only [pow_zero, one_smul] using hx
  rw [Module.finite_def, ← htop]
  exact Submodule.fg_span hG

/-- The image of a finite polynomial module map is generated over the coefficient ring by
finitely many `X`-orbits of polynomial generators. -/
theorem LinearMap.range_eq_span_polynomial_orbits
    {P : Type v} [AddCommGroup P] [Module R[X] P] [Module R P]
    [IsScalarTower R R[X] P]
    {N : Type w} [AddCommGroup N] [Module R N]
    [Module.Finite R[X] P] (f : P →ₗ[R] N) :
    ∃ s : Finset P, f.range = Submodule.span R
      (⋃ x ∈ (s : Set P), Set.range fun n : ℕ => f ((X ^ n : R[X]) • x)) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R[X]) (M := P)
  refine ⟨s, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    let K := Submodule.span R
      (⋃ y ∈ (s : Set P), Set.range fun n : ℕ => f ((X ^ n : R[X]) • y))
    have hspan (y : P) (hy : y ∈ Submodule.span R[X] (s : Set P)) :
        ∀ n : ℕ, f ((X ^ n : R[X]) • y) ∈ K := by
      induction hy using Submodule.span_induction with
      | mem y hy =>
        intro n
        exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨y,
          Set.mem_iUnion.mpr ⟨hy, ⟨n, rfl⟩⟩⟩)
      | zero => intro n; simp only [smul_zero, map_zero]; exact K.zero_mem
      | add y z _ _ hy hz =>
        intro n
        simpa only [smul_add, map_add] using K.add_mem (hy n) (hz n)
      | smul p y _ hy =>
        intro n
        induction p using Polynomial.induction_on' with
        | add p q hp hq =>
          simpa only [add_smul, smul_add, map_add] using K.add_mem hp hq
        | monomial j a =>
          have he : (X ^ n : R[X]) • ((monomial j a) • y) =
              a • ((X ^ (n + j) : R[X]) • y) := by
            rw [← C_mul_X_pow_eq_monomial, smul_smul, ← mul_assoc,
              mul_comm (X ^ n) (C a), mul_assoc, ← pow_add,
              mul_smul, ← Polynomial.algebraMap_eq, algebraMap_smul]
          rw [he, map_smul]
          exact K.smul_mem a (hy (n + j))
    simpa only [pow_zero, one_smul] using hspan x (by rw [hs]; trivial) 0
  · apply Submodule.span_le.mpr
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨x, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨_, n, rfl⟩
    exact ⟨_, rfl⟩

/-- The kernel of an `X`-localization map on a finite polynomial module is finite over the
coefficient ring. -/
theorem LinearMap.finite_ker_of_polynomial_localization
    [IsNoetherianRing R] [Module.Finite R[X] M]
    {N : Type v} [AddCommGroup N] [Module R[X] N]
    (f : M →ₗ[R[X]] N) [IsLocalizedModule (.powers (X : R[X])) f] :
    Module.Finite R (LinearMap.ker f) := by
  have : Module.Finite R[X] (LinearMap.ker f) := inferInstance
  apply Module.Finite.of_polynomial_X_torsion
  intro x
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalizedModule.eq_zero_iff (.powers (X : R[X])) f).mp x.property
  exact ⟨n, Subtype.ext hn⟩
