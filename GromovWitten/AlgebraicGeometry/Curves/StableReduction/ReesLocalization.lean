/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ReesBlowup
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Ideal

/-!
# Rees algebras commute with localization

If `B` is the localization of `A` at `S`, this file proves that the Rees algebra of the
extended ideal `I B` is the localization of `Rees(I)` at the degree-zero constants coming from
`S`.  The proof clears one common denominator from a polynomial and then one further common
denominator from the finitely many ideal-membership witnesses.

This is the algebraic base-change theorem needed to identify affine blowups after restriction to
a principal open.  Passing from the graded localization equivalence to the corresponding
cartesian square of `Proj` schemes is a separate geometric comparison.
-/

open Polynomial

universe u v

namespace AlgebraicGeometry.ReesBlowup

noncomputable section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  (S : Submonoid A) [Algebra A B] [IsLocalization S B]

/-- A denominator clearing the assertion that one polynomial coefficient belongs to the
extended ideal power. -/
def coefficientDenominator (I : Ideal A) (q : A[X])
    (hq : ∀ n, algebraMap A B (q.coeff n) ∈ I.map (algebraMap A B) ^ n)
    (n : ℕ) : S :=
  ⟨Classical.choose ((IsLocalization.algebraMap_mem_map_algebraMap_iff S B
      (I ^ n) (q.coeff n)).mp (by simpa only [Ideal.map_pow] using hq n)),
    (Classical.choose_spec ((IsLocalization.algebraMap_mem_map_algebraMap_iff S B
      (I ^ n) (q.coeff n)).mp (by simpa only [Ideal.map_pow] using hq n))).1⟩

theorem coefficientDenominator_spec (I : Ideal A) (q : A[X])
    (hq : ∀ n, algebraMap A B (q.coeff n) ∈ I.map (algebraMap A B) ^ n)
    (n : ℕ) :
    (coefficientDenominator S I q hq n : A) * q.coeff n ∈ I ^ n := by
  exact (Classical.choose_spec ((IsLocalization.algebraMap_mem_map_algebraMap_iff S B
    (I ^ n) (q.coeff n)).mp (by simpa only [Ideal.map_pow] using hq n))).2

/-- The product of coefficient denominators over the finite support of a polynomial. -/
def commonDenominator (I : Ideal A) (q : A[X])
    (hq : ∀ n, algebraMap A B (q.coeff n) ∈ I.map (algebraMap A B) ^ n) : S :=
  ∏ n ∈ q.support, coefficientDenominator S I q hq n

theorem commonDenominator_mul_coeff_mem (I : Ideal A) (q : A[X])
    (hq : ∀ n, algebraMap A B (q.coeff n) ∈ I.map (algebraMap A B) ^ n)
    (n : ℕ) :
    (commonDenominator S I q hq : A) * q.coeff n ∈ I ^ n := by
  classical
  by_cases hn : n ∈ q.support
  · have hprod := Finset.prod_erase_mul q.support
      (fun m ↦ coefficientDenominator S I q hq m) hn
    have hmem := (I ^ n).mul_mem_left
      (∏ m ∈ q.support.erase n, (coefficientDenominator S I q hq m : A))
      (coefficientDenominator_spec S I q hq n)
    change ((∏ m ∈ q.support, coefficientDenominator S I q hq m : S) : A) *
      q.coeff n ∈ I ^ n
    rw [← hprod]
    simpa only [Submonoid.coe_mul, Submonoid.coe_finsetProd, mul_assoc] using hmem
  · have hzero : q.coeff n = 0 := by
      simpa [mem_support_iff] using hn
    rw [hzero, mul_zero]
    exact Ideal.zero_mem _

/-- Clearing the common denominator turns a polynomial whose localized coefficients lie in
the extended ideal powers into an element of the original Rees algebra. -/
def clearedReesElement (I : Ideal A) (q : A[X])
    (hq : ∀ n, algebraMap A B (q.coeff n) ∈ I.map (algebraMap A B) ^ n) :
    reesAlgebra I :=
  ⟨C (commonDenominator S I q hq : A) * q, by
    rw [mem_reesAlgebra_iff]
    intro n
    rw [coeff_C_mul]
    exact commonDenominator_mul_coeff_mem S I q hq n⟩

@[simp]
theorem clearedReesElement_coe (I : Ideal A) (q : A[X])
    (hq : ∀ n, algebraMap A B (q.coeff n) ∈ I.map (algebraMap A B) ^ n) :
    (clearedReesElement S I q hq : A[X]) =
      C (commonDenominator S I q hq : A) * q :=
  rfl

/-- Every element of the localized Rees algebra is a fraction of an element of the original
Rees algebra with a degree-zero denominator. -/
theorem exists_reesMap_clearDenominator (I : Ideal A)
    (p : reesAlgebra (I.map (algebraMap A B))) :
    ∃ q : reesAlgebra I, ∃ s : S,
      (p : B[X]) * C (algebraMap A B (s : A)) =
        (q : A[X]).map (algebraMap A B) := by
  let _ : Algebra A[X] B[X] := Polynomial.algebra A B
  let _ : IsLocalization (S.map C) B[X] := Polynomial.isLocalization S B
  obtain ⟨q, t, hqt⟩ := IsLocalization.exists_mk'_eq (S.map C) (p : B[X])
  have hmul := IsLocalization.mk'_spec B[X] q t
  rw [hqt] at hmul
  obtain ⟨s, hs, hst⟩ := t.property
  let s' : S := ⟨s, hs⟩
  have hmul' : (p : B[X]) * C (algebraMap A B s) =
      q.map (algebraMap A B) := by
    change (p : B[X]) * (t : A[X]).map (algebraMap A B) =
      q.map (algebraMap A B) at hmul
    rw [← hst, map_C] at hmul
    exact hmul
  have hq : ∀ n, algebraMap A B (q.coeff n) ∈
      I.map (algebraMap A B) ^ n := by
    intro n
    have hcoeff := congrArg (fun z : B[X] ↦ z.coeff n) hmul'
    have hp := ((mem_reesAlgebra_iff (I.map (algebraMap A B)) (p : B[X])).mp
      p.property) n
    simp only [coeff_mul_C, coeff_map] at hcoeff
    rw [← hcoeff]
    exact (I.map (algebraMap A B) ^ n).mul_mem_right _ hp
  let d := commonDenominator S I q hq
  let q' := clearedReesElement S I q hq
  refine ⟨q', s' * d, ?_⟩
  rw [show (q' : A[X]) = C (d : A) * q by rfl]
  change (p : B[X]) * C (algebraMap A B ((s' : A) * (d : A))) =
    (C (d : A) * q).map (algebraMap A B)
  rw [Polynomial.map_mul, map_C, map_mul, C_mul]
  calc
    (p : B[X]) * (C (algebraMap A B (s' : A)) * C (algebraMap A B (d : A))) =
        ((p : B[X]) * C (algebraMap A B (s' : A))) *
          C (algebraMap A B (d : A)) := by rw [mul_assoc]
    _ = q.map (algebraMap A B) * C (algebraMap A B (d : A)) := by rw [hmul']
    _ = C (algebraMap A B (d : A)) * q.map (algebraMap A B) := by rw [mul_comm]

/-- The degree-zero copy of the localization submonoid inside the Rees algebra. -/
def reesLocalizationSubmonoid (I : Ideal A) : Submonoid (reesAlgebra I) :=
  S.map (algebraMap A (reesAlgebra I))

theorem reesMap_algebraMap_apply (I : Ideal A) (x : reesAlgebra I) :
    @algebraMap (reesAlgebra I) (reesAlgebra (I.map (algebraMap A B))) _ _
      (reesMap I (algebraMap A B)).toAlgebra x =
        reesMap I (algebraMap A B) x :=
  rfl

theorem reesMap_base_apply (I : Ideal A) (a : A) :
    reesMap I (algebraMap A B) (algebraMap A (reesAlgebra I) a) =
      algebraMap B (reesAlgebra (I.map (algebraMap A B))) (algebraMap A B a) := by
  apply Subtype.ext
  simp [reesMap]

theorem reesMap_map_units (I : Ideal A) (y : reesLocalizationSubmonoid S I) :
    IsUnit (reesMap I (algebraMap A B) y.1) := by
  obtain ⟨s, hsS, hs⟩ := y.2
  let s' : S := ⟨s, hsS⟩
  rw [← hs, reesMap_base_apply]
  exact (IsLocalization.map_units B s').map (algebraMap B _)

theorem reesMap_surj (I : Ideal A)
    (z : reesAlgebra (I.map (algebraMap A B))) :
    ∃ x : reesAlgebra I × reesLocalizationSubmonoid S I,
      z * reesMap I (algebraMap A B) x.2.1 =
        reesMap I (algebraMap A B) x.1 := by
  obtain ⟨q, s, h⟩ := exists_reesMap_clearDenominator S I z
  let t : reesLocalizationSubmonoid S I :=
    ⟨algebraMap A (reesAlgebra I) s.1, ⟨s.1, s.2, rfl⟩⟩
  refine ⟨⟨q, t⟩, ?_⟩
  apply Subtype.ext
  simpa [t, reesMap_base_apply] using h

theorem reesMap_exists_of_eq (I : Ideal A) {x y : reesAlgebra I}
    (h : reesMap I (algebraMap A B) x = reesMap I (algebraMap A B) y) :
    ∃ c : reesLocalizationSubmonoid S I, c.1 * x = c.1 * y := by
  let _ : Algebra A[X] B[X] := Polynomial.algebra A B
  let _ : IsLocalization (S.map C) B[X] := Polynomial.isLocalization S B
  have hpoly : (x : A[X]).map (algebraMap A B) =
      (y : A[X]).map (algebraMap A B) := congrArg Subtype.val h
  have halg : algebraMap A[X] B[X] (x : A[X]) =
      algebraMap A[X] B[X] (y : A[X]) := hpoly
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (S.map C) B[X]).mp halg
  obtain ⟨s, hsS, hsc⟩ := c.property
  let d : reesLocalizationSubmonoid S I :=
    ⟨algebraMap A (reesAlgebra I) s, ⟨s, hsS, rfl⟩⟩
  refine ⟨d, ?_⟩
  apply Subtype.ext
  change C s * (x : A[X]) = C s * (y : A[X])
  simpa [hsc] using hc

/-- The extended Rees algebra satisfies the universal characterization of localization at the
degree-zero image of `S`. -/
theorem reesMap_isLocalization (I : Ideal A) :
    @IsLocalization (reesAlgebra I) _ (reesLocalizationSubmonoid S I)
      (reesAlgebra (I.map (algebraMap A B))) _
      (reesMap I (algebraMap A B)).toAlgebra := by
  let _ : Algebra (reesAlgebra I) (reesAlgebra (I.map (algebraMap A B))) :=
    (reesMap I (algebraMap A B)).toAlgebra
  exact ⟨
    { map_units := by
        intro y
        exact reesMap_map_units S I y
      surj := by
        intro z
        exact reesMap_surj S I z
      exists_of_eq := by
        intro x y h
        exact reesMap_exists_of_eq S I h }⟩

/-- The canonical localization of `Rees(I)` is explicitly equivalent to the Rees algebra of
the localized ideal. -/
def reesLocalizationEquiv (I : Ideal A) :
    Localization (reesLocalizationSubmonoid S I) ≃+*
      reesAlgebra (I.map (algebraMap A B)) := by
  let _ : Algebra (reesAlgebra I) (reesAlgebra (I.map (algebraMap A B))) :=
    (reesMap I (algebraMap A B)).toAlgebra
  let _ : IsLocalization (reesLocalizationSubmonoid S I)
      (reesAlgebra (I.map (algebraMap A B))) := reesMap_isLocalization S I
  have hM : (reesLocalizationSubmonoid S I).map (RingEquiv.refl _).toMonoidHom =
      reesLocalizationSubmonoid S I := by
    ext x
    simp
  exact IsLocalization.ringEquivOfRingEquiv
    (Localization (reesLocalizationSubmonoid S I))
    (reesAlgebra (I.map (algebraMap A B))) (RingEquiv.refl _) hM

@[simp]
theorem reesLocalizationEquiv_algebraMap (I : Ideal A) (x : reesAlgebra I) :
    reesLocalizationEquiv S I
      (algebraMap (reesAlgebra I) (Localization (reesLocalizationSubmonoid S I)) x) =
      reesMap I (algebraMap A B) x := by
  let _ : Algebra (reesAlgebra I) (reesAlgebra (I.map (algebraMap A B))) :=
    (reesMap I (algebraMap A B)).toAlgebra
  let _ : IsLocalization (reesLocalizationSubmonoid S I)
      (reesAlgebra (I.map (algebraMap A B))) := reesMap_isLocalization S I
  change reesLocalizationEquiv S I
      (algebraMap (reesAlgebra I) (Localization (reesLocalizationSubmonoid S I)) x) =
    algebraMap (reesAlgebra I) (reesAlgebra (I.map (algebraMap A B))) x
  apply IsLocalization.ringEquivOfRingEquiv_eq
  ext z
  simp

end


end AlgebraicGeometry.ReesBlowup
