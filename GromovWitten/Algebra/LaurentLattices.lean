/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Data.Int.Interval

/-!
# Finite Laurent lattices

The standard positive and bounded Laurent lattices in a finite free module are stable under the
appropriate Laurent shifts. Their intersection is supported in finite integer intervals, while
every element enters each lattice after a sufficiently large shift.
-/

open scoped LaurentPolynomial
open LaurentPolynomial
noncomputable section

namespace GromovWitten.Algebra

universe u v

variable {R : Type u} [CommRing R]

/-- The free coordinate module of Laurent polynomials indexed by `ι`. -/
abbrev LaurentFree (R : Type u) (ι : Type v) [CommRing R] := ι → R[T;T⁻¹]

/-- The Laurent vectors whose coordinates are supported in nonnegative degrees. -/
def positiveLattice (ι : Type v) : Submodule R (LaurentFree R ι) :=
  Submodule.pi Set.univ (fun _ : ι =>
    AddMonoidAlgebra.supported R R (Set.Ici (0 : ℤ)))

/-- The Laurent vectors whose `i`-th coordinate is supported in degrees at most `d i`. -/
def negativeLattice (d : ι → ℤ) : Submodule R (LaurentFree R ι) :=
  Submodule.pi Set.univ (fun i =>
    AddMonoidAlgebra.supported R R (Set.Iic (d i)))

private def intervalLattice (d : ι → ℤ) : Submodule R (LaurentFree R ι) :=
  Submodule.pi Set.univ (fun i =>
    AddMonoidAlgebra.supported R R (Set.Icc (0 : ℤ) (d i)))

private lemma positiveLattice_inf_negativeLattice (d : ι → ℤ) :
    positiveLattice (R := R) ι ⊓ negativeLattice d = intervalLattice d := by
  ext x
  simp only [positiveLattice, negativeLattice, intervalLattice]
  rw [Submodule.mem_inf, Submodule.mem_pi, Submodule.mem_pi, Submodule.mem_pi]
  simp only [Set.mem_univ, AddMonoidAlgebra.mem_supported, true_implies]
  constructor
  · rintro ⟨hpos, hneg⟩ i
    intro a ha
    exact ⟨hpos i ha, hneg i ha⟩
  · intro h
    exact ⟨fun i a ha => (h i ha).1, fun i a ha => (h i ha).2⟩

private def piSubtypeEquiv {R : Type u} [CommRing R] {ι : Type v} {M : ι → Type*}
    [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (p : ∀ i, Submodule R (M i)) :
    (∀ i, p i) ≃ₗ[R] (Submodule.pi Set.univ p) where
  toFun f := ⟨fun i => f i, by
    rw [Submodule.mem_pi]
    intro i _
    exact (f i).property⟩
  invFun x i := ⟨x.1 i, (Submodule.mem_pi.mp x.property) i (Set.mem_univ i)⟩
  left_inv f := by rfl
  right_inv x := by apply Subtype.ext; rfl
  map_add' f g := by rfl
  map_smul' a f := by rfl

private lemma finite_intervalLattice [Finite ι] (d : ι → ℤ) :
    Module.Finite R (intervalLattice (R := R) d) := by
  let p : ∀ i : ι, Submodule R (R[T;T⁻¹]) := fun i =>
    AddMonoidAlgebra.supported R R (Set.Icc (0 : ℤ) (d i))
  let : ∀ i, Module.Finite R (p i) := fun i => by
    dsimp [p]
    have hfin := Module.Finite.span_of_finite R
      ((Set.finite_Icc (0 : ℤ) (d i)).image
        (fun m : ℤ => (AddMonoidAlgebra.single m 1 : R[T;T⁻¹])))
    let e := LinearEquiv.ofEq
      (Submodule.span R ((fun m : ℤ => (AddMonoidAlgebra.single m 1 : R[T;T⁻¹])) ''
        Set.Icc (0 : ℤ) (d i)))
      (AddMonoidAlgebra.supported R R (Set.Icc (0 : ℤ) (d i)))
      (AddMonoidAlgebra.supported_eq_span_single R _).symm
    exact Module.Finite.equiv e
  let e := piSubtypeEquiv (R := R) p
  change Module.Finite R (Submodule.pi Set.univ p)
  exact Module.Finite.equiv e

private lemma shift_mem_supported (s : Set ℤ) (n : ℤ)
    (hs : ∀ ⦃m : ℤ⦄, m ∈ s → n + m ∈ s)
    {x : R[T;T⁻¹]} (hx : x ∈ AddMonoidAlgebra.supported R R s) :
    (T n : R[T;T⁻¹]) • x ∈ AddMonoidAlgebra.supported R R s := by
  change T n * x ∈ AddMonoidAlgebra.supported R R s
  rw [AddMonoidAlgebra.mem_supported] at hx ⊢
  intro m hm
  have hm0 : (T n * x).coeff m ≠ 0 := Finsupp.mem_support_iff.mp hm
  change (AddMonoidAlgebra.single n 1 * x).coeff m ≠ 0 at hm0
  rw [AddMonoidAlgebra.coeff_single_mul_apply] at hm0
  have hxm : -n + m ∈ (x.coeff.support : Set ℤ) := by
    exact Finsupp.mem_support_iff.mpr (by simpa using hm0)
  have hsm : -n + m ∈ s := hx hxm
  simpa [add_assoc] using hs hsm

/-- Multiplication by `T` preserves the positive Laurent lattice. -/
lemma positiveLattice_smul_T (ι : Type v) {x : LaurentFree R ι}
    (hx : x ∈ positiveLattice ι) :
    (T 1 : R[T;T⁻¹]) • x ∈ positiveLattice ι := by
  rw [positiveLattice, Submodule.mem_pi] at hx ⊢
  intro i _
  exact shift_mem_supported (Set.Ici (0 : ℤ)) 1 (by
    intro m hm
    have hm' := Set.mem_Ici.mp hm
    exact Set.mem_Ici.mpr (by omega)) (hx i (Set.mem_univ i))

/-- Multiplication by `T⁻¹` preserves the bounded negative Laurent lattice. -/
lemma negativeLattice_smul_T_neg (d : ι → ℤ) {x : LaurentFree R ι}
    (hx : x ∈ negativeLattice d) :
    (T (-1) : R[T;T⁻¹]) • x ∈ negativeLattice d := by
  rw [negativeLattice, Submodule.mem_pi] at hx ⊢
  intro i _
  exact shift_mem_supported (Set.Iic (d i)) (-1) (by
    intro m hm
    have hm' := Set.mem_Iic.mp hm
    exact Set.mem_Iic.mpr (by omega)) (hx i (Set.mem_univ i))

private lemma exists_positive_shift [Finite ι] (x : LaurentFree R ι) :
    ∃ n : ℕ, (T (n : ℤ) : R[T;T⁻¹]) • x ∈ positiveLattice ι := by
  classical
  let := Fintype.ofFinite ι
  let U : Finset ℤ := Finset.biUnion Finset.univ (fun i => (x i).coeff.support)
  by_cases hU : U.Nonempty
  · let m := U.min' hU
    let n := (-m).toNat
    refine ⟨n, ?_⟩
    rw [positiveLattice, Submodule.mem_pi]
    intro i _
    rw [AddMonoidAlgebra.mem_supported]
    intro a ha
    have ha0 : (T (n : ℤ) * x i).coeff a ≠ 0 := Finsupp.mem_support_iff.mp ha
    change (AddMonoidAlgebra.single (n : ℤ) 1 * x i).coeff a ≠ 0 at ha0
    rw [AddMonoidAlgebra.coeff_single_mul_apply] at ha0
    have hxa : -((n : ℤ)) + a ∈ (x i).coeff.support :=
      Finsupp.mem_support_iff.mpr (by simpa using ha0)
    have hUa : -((n : ℤ)) + a ∈ U := by
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hxa⟩
    have hmle : m ≤ -((n : ℤ)) + a := Finset.min'_le U _ hUa
    by_cases hm : m ≤ 0
    · have hn : ((n : ℤ)) = -m := by
        dsimp [n]
        exact Int.toNat_of_nonneg (by omega)
      rw [hn] at hmle
      change 0 ≤ a
      omega
    · have hm' : 0 < m := lt_of_not_ge hm
      have hn : ((n : ℤ)) = 0 := by
        dsimp [n]
        have hnonpos : -m ≤ 0 := by omega
        rw [Int.toNat_of_nonpos hnonpos]
        norm_num
      rw [hn] at hmle
      change 0 ≤ a
      omega
  · refine ⟨0, ?_⟩
    rw [positiveLattice, Submodule.mem_pi]
    intro i _
    rw [AddMonoidAlgebra.mem_supported]
    intro a ha
    have ha0 : (T (0 : ℤ) * x i).coeff a ≠ 0 := Finsupp.mem_support_iff.mp ha
    change (AddMonoidAlgebra.single (0 : ℤ) 1 * x i).coeff a ≠ 0 at ha0
    rw [AddMonoidAlgebra.coeff_single_mul_apply] at ha0
    have hxa : a ∈ (x i).coeff.support :=
      Finsupp.mem_support_iff.mpr (by simpa using ha0)
    have hUa : a ∈ U := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hxa⟩
    exact (hU ⟨a, hUa⟩).elim

private lemma exists_negative_shift [Finite ι] (d : ι → ℤ) (x : LaurentFree R ι) :
    ∃ n : ℕ, (T (-(n : ℤ)) : R[T;T⁻¹]) • x ∈ negativeLattice d := by
  classical
  let := Fintype.ofFinite ι
  let V : Finset ℤ := Finset.biUnion Finset.univ (fun i =>
    (x i).coeff.support.image (fun a => a - d i))
  by_cases hV : V.Nonempty
  · let m := V.max' hV
    let n := m.toNat
    refine ⟨n, ?_⟩
    rw [negativeLattice, Submodule.mem_pi]
    intro i _
    rw [AddMonoidAlgebra.mem_supported]
    intro a ha
    have ha0 : (T (-(n : ℤ)) * x i).coeff a ≠ 0 := Finsupp.mem_support_iff.mp ha
    change (AddMonoidAlgebra.single (-(n : ℤ)) 1 * x i).coeff a ≠ 0 at ha0
    rw [AddMonoidAlgebra.coeff_single_mul_apply] at ha0
    have hxa : (n : ℤ) + a ∈ (x i).coeff.support := by
      apply Finsupp.mem_support_iff.mpr
      simpa only [neg_neg, neg_neg, one_mul] using ha0
    have hVa : ((n : ℤ) + a) - d i ∈ V := by
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Finset.mem_image.mpr ⟨(n : ℤ) + a, hxa, rfl⟩⟩
    have hmle : ((n : ℤ) + a) - d i ≤ m := Finset.le_max' V _ hVa
    by_cases hm : m ≤ 0
    · have hn : ((n : ℤ)) = 0 := by
        dsimp [n]
        have hnonpos : m ≤ 0 := hm
        rw [Int.toNat_of_nonpos hnonpos]
        norm_num
      rw [hn] at hmle
      change a ≤ d i
      omega
    · have hm' : 0 ≤ m := by omega
      have hn : ((n : ℤ)) = m := by
        dsimp [n]
        exact Int.toNat_of_nonneg hm'
      rw [hn] at hmle
      change a ≤ d i
      omega
  · refine ⟨0, ?_⟩
    rw [negativeLattice, Submodule.mem_pi]
    intro i _
    rw [AddMonoidAlgebra.mem_supported]
    intro a ha
    have ha0 : (T (-(0 : ℤ)) * x i).coeff a ≠ 0 := Finsupp.mem_support_iff.mp ha
    change (AddMonoidAlgebra.single (-(0 : ℤ)) 1 * x i).coeff a ≠ 0 at ha0
    rw [AddMonoidAlgebra.coeff_single_mul_apply] at ha0
    have hxa : a ∈ (x i).coeff.support := by
      apply Finsupp.mem_support_iff.mpr
      simpa only [neg_zero, neg_neg, zero_add, one_mul] using ha0
    have hVa : a - d i ∈ V := by
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Finset.mem_image.mpr ⟨a, hxa, rfl⟩⟩
    exact (hV ⟨a - d i, hVa⟩).elim

/-- A sufficiently large positive shift sends every finite Laurent vector into the positive
lattice. -/
lemma positiveLattice_clears [Finite ι] (x : LaurentFree R ι) :
    ∃ n : ℕ, (T (n : ℤ) : R[T;T⁻¹]) • x ∈ positiveLattice ι :=
  exists_positive_shift x

/-- A sufficiently large negative shift sends every finite Laurent vector into the bounded
lattice. -/
lemma negativeLattice_clears [Finite ι] (d : ι → ℤ) (x : LaurentFree R ι) :
    ∃ n : ℕ, (T (-(n : ℤ)) : R[T;T⁻¹]) • x ∈ negativeLattice d :=
  exists_negative_shift d x

private lemma supported_Ici_eq_span_nat :
    AddMonoidAlgebra.supported R R (Set.Ici (0 : ℤ)) =
      Submodule.span R (Set.range fun n : ℕ => (T (n : ℤ) : R[T;T⁻¹])) := by
  rw [AddMonoidAlgebra.supported_eq_span_single]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    refine Submodule.subset_span ⟨m.toNat, ?_⟩
    have hm' : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (Set.mem_Ici.mp hm)
    simp [hm']
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    refine Submodule.subset_span ⟨(n : ℤ), Set.mem_Ici.mpr (by omega), ?_⟩
    rfl

private lemma supported_Iic_eq_span_nat (b : ℤ) :
    AddMonoidAlgebra.supported R R (Set.Iic b) =
      Submodule.span R (Set.range fun n : ℕ =>
        (T (b - (n : ℤ)) : R[T;T⁻¹])) := by
  rw [AddMonoidAlgebra.supported_eq_span_single]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    let n := (b - m).toNat
    refine Submodule.subset_span ⟨n, ?_⟩
    have hm' : m ≤ b := Set.mem_Iic.mp hm
    have hnonneg : 0 ≤ b - m := by omega
    have hn : ((n : ℤ)) = b - m := by
      dsimp [n]
      exact Int.toNat_of_nonneg hnonneg
    change T (b - (n : ℤ)) = T m
    rw [hn, sub_sub_cancel]
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    refine Submodule.subset_span ⟨b - (n : ℤ), ?_, ?_⟩
    · exact Set.mem_Iic.mpr (by omega)
    · rfl

/-- The positive lattice is spanned by its coordinate Laurent monomials. -/
lemma positiveLattice_eq_span_nat [Finite ι] [DecidableEq ι] :
    positiveLattice (R := R) ι =
      Submodule.span R (Set.range fun p : ι × ℕ =>
        Pi.single p.1 (T (p.2 : ℤ) : R[T;T⁻¹])) := by
  classical
  let p : ∀ i : ι, Submodule R (R[T;T⁻¹]) := fun _ =>
    AddMonoidAlgebra.supported R R (Set.Ici (0 : ℤ))
  let G : Set (LaurentFree R ι) := Set.range fun q : ι × ℕ =>
    Pi.single q.1 (T (q.2 : ℤ) : R[T;T⁻¹])
  change Submodule.pi Set.univ p = Submodule.span R G
  apply le_antisymm
  · rw [← Submodule.iSup_map_single (R := R) (p := p)]
    refine iSup_le fun i => ?_
    apply Submodule.map_le_iff_le_comap.mpr
    dsimp [p]
    rw [supported_Ici_eq_span_nat]
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact Submodule.subset_span ⟨(i, n), rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, n⟩, rfl⟩
    dsimp [G]
    change Pi.single i (T (n : ℤ) : R[T;T⁻¹]) ∈ Submodule.pi Set.univ p
    rw [Submodule.mem_pi]
    intro j _
    by_cases h : j = i
    · subst h
      dsimp [p]
      simp only [Pi.single_eq_same]
      change AddMonoidAlgebra.single (n : ℤ) 1 ∈
        AddMonoidAlgebra.supported R R (Set.Ici (0 : ℤ))
      exact Finsupp.single_mem_supported R 1 (Set.mem_Ici.mpr (by omega))
    · simp [h]

/-- The bounded negative lattice is spanned by its coordinate Laurent monomials. -/
lemma negativeLattice_eq_span_nat [Finite ι] [DecidableEq ι] (d : ι → ℤ) :
    negativeLattice d =
      Submodule.span R (Set.range fun p : ι × ℕ =>
        Pi.single p.1 (T (d p.1 - (p.2 : ℤ)) : R[T;T⁻¹])) := by
  classical
  let p : ∀ i : ι, Submodule R (R[T;T⁻¹]) := fun i =>
    AddMonoidAlgebra.supported R R (Set.Iic (d i))
  let G : Set (LaurentFree R ι) := Set.range fun q : ι × ℕ =>
    Pi.single q.1 (T (d q.1 - (q.2 : ℤ)) : R[T;T⁻¹])
  change Submodule.pi Set.univ p = Submodule.span R G
  apply le_antisymm
  · rw [← Submodule.iSup_map_single (R := R) (p := p)]
    refine iSup_le fun i => ?_
    apply Submodule.map_le_iff_le_comap.mpr
    dsimp [p]
    rw [supported_Iic_eq_span_nat]
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact Submodule.subset_span ⟨(i, n), rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, n⟩, rfl⟩
    dsimp [G]
    change Pi.single i (T (d i - (n : ℤ)) : R[T;T⁻¹]) ∈ Submodule.pi Set.univ p
    rw [Submodule.mem_pi]
    intro j _
    by_cases h : j = i
    · subst h
      dsimp [p]
      simp only [Pi.single_eq_same]
      change AddMonoidAlgebra.single (d j - (n : ℤ)) 1 ∈
        AddMonoidAlgebra.supported R R (Set.Iic (d j))
      exact Finsupp.single_mem_supported R 1 (Set.mem_Iic.mpr (by omega))
    · simp [h]

/-- The intersection of the positive and bounded negative lattices is finite. -/
lemma finite_positiveLattice_inf_negativeLattice [Finite ι] (d : ι → ℤ) :
    Module.Finite R ((positiveLattice (R := R) ι ⊓ negativeLattice (R := R) d) :
      Submodule R (LaurentFree R ι)) := by
  have hfin : Module.Finite R (intervalLattice (R := R) d) :=
    finite_intervalLattice (R := R) d
  let e := LinearEquiv.ofEq (intervalLattice (R := R) d)
    (positiveLattice (R := R) ι ⊓ negativeLattice (R := R) d)
    (positiveLattice_inf_negativeLattice (R := R) d).symm
  exact Module.Finite.equiv e

end GromovWitten.Algebra
