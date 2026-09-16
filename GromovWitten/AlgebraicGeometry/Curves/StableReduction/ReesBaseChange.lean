/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ReesBlowup
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.Localization

/-!
# Flat base change for the affine Rees blowup

`ReesBlowup.lean` constructs the affine blowup `Bl_I(Spec A) = Proj (⨁ Iⁿ tⁿ)` together with
its standard affine charts.  This file proves that the construction commutes with flat base
change, chart by chart, and deduces the cartesian comparison square of affine schemes on every
standard chart.
-/

open Polynomial CategoryTheory Limits
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry.ReesBlowup

noncomputable section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-! ## Explicit elements of a standard Rees chart -/

/-- The coordinate ring of the standard Rees chart indexed by `r ∈ I`. -/
abbrev chartRing (I : Ideal A) (r : I) : Type u :=
  HomogeneousLocalization.Away (grade I) (generator I r)

theorem homogeneousMonomial_mem_grade (I : Ideal A) (n : ℕ) (c : A) :
    homogeneousMonomial I n c ∈ grade I n := by
  classical
  by_cases hc : c ∈ I ^ n
  · change ((homogeneousMonomial I n c : reesAlgebra I) : A[X]) =
      monomial n (((homogeneousMonomial I n c : reesAlgebra I) : A[X]).coeff n)
    rw [homogeneousMonomial_coe I n c hc]
    simp
  · have hzero : homogeneousMonomial I n c = 0 := by simp [homogeneousMonomial, hc]
    rw [hzero]
    exact zero_mem _

theorem mul_mem_pow_add (I : Ideal A) {n m : ℕ} {c d : A}
    (hc : c ∈ I ^ n) (hd : d ∈ I ^ m) : c * d ∈ I ^ (n + m) := by
  rw [pow_add]
  exact Ideal.mul_mem_mul hc hd

theorem homogeneousMonomial_mul (I : Ideal A) (n m : ℕ) (c d : A)
    (hc : c ∈ I ^ n) (hd : d ∈ I ^ m) :
    homogeneousMonomial I n c * homogeneousMonomial I m d =
      homogeneousMonomial I (n + m) (c * d) := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, homogeneousMonomial_coe I n c hc,
    homogeneousMonomial_coe I m d hd,
    homogeneousMonomial_coe I (n + m) (c * d) (mul_mem_pow_add I hc hd)]
  exact monomial_mul_monomial n m c d

/-- The degree-`n` chart element `c / rⁿ` on the standard chart indexed by `r`. -/
def chartElem (I : Ideal A) (r : I) (n : ℕ) (c : A) : chartRing I r :=
  HomogeneousLocalization.Away.mk (grade I) (generator_mem_grade_one I r) n
    (homogeneousMonomial I n c) (by simpa using homogeneousMonomial_mem_grade I n c)

@[simp]
theorem chartElem_val (I : Ideal A) (r : I) (n : ℕ) (c : A) :
    (chartElem I r n c).val =
      Localization.mk (homogeneousMonomial I n c)
        (⟨generator I r ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (generator I r)) :=
  rfl

theorem generator_pow (I : Ideal A) (r : I) (k : ℕ) :
    generator I r ^ k = homogeneousMonomial I k (r.1 ^ k) := by
  apply Subtype.ext
  rw [homogeneousMonomial_coe I k _ (Ideal.pow_mem_pow r.2 k)]
  change ((generator I r : reesAlgebra I) : A[X]) ^ k = _
  rw [show ((generator I r : reesAlgebra I) : A[X]) = monomial 1 r.1 from rfl]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, monomial_mul_monomial, pow_succ]

theorem chartElem_add (I : Ideal A) (r : I) (n : ℕ) {c d : A}
    (hc : c ∈ I ^ n) (hd : d ∈ I ^ n) :
    chartElem I r n c + chartElem I r n d = chartElem I r n (c + d) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_add, chartElem_val, chartElem_val, chartElem_val,
    Localization.add_mk_self]
  congr 1
  apply Subtype.ext
  rw [Subalgebra.coe_add, homogeneousMonomial_coe I n c hc,
    homogeneousMonomial_coe I n d hd,
    homogeneousMonomial_coe I n (c + d) (Ideal.add_mem _ hc hd)]
  simp

theorem chartElem_mul (I : Ideal A) (r : I) (n m : ℕ) {c d : A}
    (hc : c ∈ I ^ n) (hd : d ∈ I ^ m) :
    chartElem I r n c * chartElem I r m d = chartElem I r (n + m) (c * d) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, chartElem_val, chartElem_val, chartElem_val,
    Localization.mk_mul, homogeneousMonomial_mul I n m c d hc hd]
  congr 1
  apply Subtype.ext
  simp [pow_add]

theorem chartElem_shift (I : Ideal A) (r : I) (n k : ℕ) {c : A} (hc : c ∈ I ^ n) :
    chartElem I r n c = chartElem I r (n + k) (r.1 ^ k * c) := by
  apply HomogeneousLocalization.val_injective
  rw [chartElem_val, chartElem_val]
  rw [show homogeneousMonomial I (n + k) (r.1 ^ k * c) =
      generator I r ^ k * homogeneousMonomial I n c by
    rw [generator_pow, homogeneousMonomial_mul I k n _ _ (Ideal.pow_mem_pow r.2 k) hc,
      Nat.add_comm k n]]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  change (1 : reesAlgebra I) * (generator I r ^ (n + k) * homogeneousMonomial I n c) =
    1 * (generator I r ^ n * (generator I r ^ k * homogeneousMonomial I n c))
  rw [pow_add]
  ring

theorem chartElem_eq_zero_iff (I : Ideal A) (r : I) (n : ℕ) {c : A} (hc : c ∈ I ^ n) :
    chartElem I r n c = 0 ↔ ∃ k : ℕ, r.1 ^ k * c = 0 := by
  constructor
  · intro h
    have hval : (chartElem I r n c).val = 0 := by rw [h, HomogeneousLocalization.val_zero]
    rw [chartElem_val, Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff] at hval
    obtain ⟨⟨m, k, hk⟩, hm⟩ := hval
    refine ⟨k, ?_⟩
    have hm' : generator I r ^ k * homogeneousMonomial I n c = 0 := by
      rw [show generator I r ^ k = m from hk]
      exact hm
    have hpoly := congrArg (fun x : reesAlgebra I ↦ (x : A[X])) hm'
    rw [Subalgebra.coe_mul, generator_pow] at hpoly
    rw [homogeneousMonomial_coe I k _ (Ideal.pow_mem_pow r.2 k),
      homogeneousMonomial_coe I n c hc, monomial_mul_monomial] at hpoly
    have hcoeff := congrArg (fun p : A[X] ↦ p.coeff (k + n)) hpoly
    simpa using hcoeff
  · rintro ⟨k, hk⟩
    apply HomogeneousLocalization.val_injective
    rw [chartElem_val, HomogeneousLocalization.val_zero, Localization.mk_eq_mk'_apply,
      IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨generator I r ^ k, ⟨k, rfl⟩⟩, ?_⟩
    change generator I r ^ k * homogeneousMonomial I n c = 0
    rw [generator_pow, homogeneousMonomial_mul I k n _ _ (Ideal.pow_mem_pow r.2 k) hc, hk]
    apply Subtype.ext
    simp [homogeneousMonomial]

theorem baseElement_eq_chartElem (I : Ideal A) (r : I) (a : A) :
    baseElement I r a = chartElem I r 0 a := by
  apply HomogeneousLocalization.val_injective
  rw [chartElem_val]
  change Localization.mk (algebraMap A (reesAlgebra I) a) _ = _
  congr 1
  apply Subtype.ext
  rw [homogeneousMonomial_coe I 0 a (by simp)]
  simp [Polynomial.monomial_zero_left]

theorem baseRingHom_eq_chartElem (I : Ideal A) (r : I) (a : A) :
    baseRingHom I r a = chartElem I r 0 a := by
  rw [baseRingHom_apply, baseElement_eq_chartElem]

theorem chartElem_surjective (I : Ideal A) (r : I) (z : chartRing I r) :
    ∃ (n : ℕ) (c : A), c ∈ I ^ n ∧ chartElem I r n c = z := by
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grade I) (generator_mem_grade_one I r) z
  have ha' : a ∈ grade I n := by
    convert ha using 2
    simp
  refine ⟨n, (a : A[X]).coeff n,
    ((mem_reesAlgebra_iff I (a : A[X])).mp a.property) n, ?_⟩
  apply HomogeneousLocalization.val_injective
  rw [chartElem_val, HomogeneousLocalization.Away.val_mk]
  congr 1
  apply Subtype.ext
  rw [homogeneousMonomial_coe I n _ (((mem_reesAlgebra_iff I (a : A[X])).mp a.property) n)]
  exact ha'.symm

/-! ## Functoriality of the standard charts -/

/-- The image of a chosen centre generator in the extended ideal. -/
def mapGenerator (I : Ideal A) (f : A →+* B) (r : I) : (I.map f) :=
  ⟨f r.1, Ideal.mem_map_of_mem f r.2⟩

theorem reesMap_homogeneousMonomial (I : Ideal A) (f : A →+* B) (n : ℕ) {c : A}
    (hc : c ∈ I ^ n) :
    reesMap I f (homogeneousMonomial I n c) =
      homogeneousMonomial (I.map f) n (f c) := by
  apply Subtype.ext
  have hfc : f c ∈ (I.map f) ^ n := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f hc
  rw [reesMap_coe, homogeneousMonomial_coe I n c hc,
    homogeneousMonomial_coe (I.map f) n (f c) hfc]
  exact map_monomial f

theorem reesMap_generator' (I : Ideal A) (f : A →+* B) (r : I) :
    reesMap I f (generator I r) = generator (I.map f) (mapGenerator I f r) := by
  apply Subtype.ext
  simp [generator, mapGenerator]

theorem reesMap_generator_pow (I : Ideal A) (f : A →+* B) (r : I) (n : ℕ) :
    reesMap I f (generator I r ^ n) = generator (I.map f) (mapGenerator I f r) ^ n := by
  rw [map_pow, reesMap_generator']

/-- Coefficientwise extension of a standard Rees chart along a ring map of base rings. -/
def chartBaseChangeHom (I : Ideal A) (f : A →+* B) (r : I) :
    chartRing I r →+* chartRing (I.map f) (mapGenerator I f r) :=
  HomogeneousLocalization.map (gradedMap I f) (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, (reesMap_generator_pow I f r n).symm⟩)

@[simp]
theorem chartBaseChangeHom_chartElem (I : Ideal A) (f : A →+* B) (r : I) (n : ℕ) {c : A}
    (hc : c ∈ I ^ n) :
    chartBaseChangeHom I f r (chartElem I r n c) =
      chartElem (I.map f) (mapGenerator I f r) n (f c) := by
  apply HomogeneousLocalization.val_injective
  rw [chartBaseChangeHom, chartElem, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk, chartElem_val]
  change Localization.mk (reesMap I f (homogeneousMonomial I n c))
      ⟨reesMap I f (generator I r ^ n), _⟩ = _
  rw [reesMap_homogeneousMonomial I f n hc]
  congr 1
  apply Subtype.ext
  exact reesMap_generator_pow I f r n

theorem chartBaseChangeHom_baseRingHom (I : Ideal A) (f : A →+* B) (r : I) (a : A) :
    chartBaseChangeHom I f r (baseRingHom I r a) =
      baseRingHom (I.map f) (mapGenerator I f r) (f a) := by
  rw [baseRingHom_eq_chartElem, baseRingHom_eq_chartElem,
    chartBaseChangeHom_chartElem I f r 0 (by simp)]

theorem chartElem_zero (I : Ideal A) (r : I) (n : ℕ) : chartElem I r n 0 = 0 := by
  apply HomogeneousLocalization.val_injective
  rw [chartElem_val, HomogeneousLocalization.val_zero,
    show homogeneousMonomial I n (0 : A) = 0 by
      apply Subtype.ext
      simp [homogeneousMonomial]]
  exact Localization.mk_zero _

/-! ## The chart-level base change map -/

section FlatChart

variable [Algebra A B]

/-- The base ring acts on each of its standard Rees charts through the chart structure map. -/
@[instance_reducible]
def chartAlgebra (I : Ideal A) (r : I) : Algebra A (chartRing I r) :=
  (baseRingHom I r).toAlgebra

attribute [local instance] chartAlgebra

theorem chartAlgebraMap_eq (I : Ideal A) (r : I) :
    algebraMap A (chartRing I r) = baseRingHom I r := rfl

theorem chartAlgebraMap_apply (I : Ideal A) (r : I) (a : A) :
    algebraMap A (chartRing I r) a = chartElem I r 0 a :=
  baseRingHom_eq_chartElem I r a

/-- The extended chart of a base-changed ideal, as an algebra over the original base ring. -/
@[instance_reducible]
def chartBaseAlgebra (I : Ideal A) (r : I) :
    Algebra A (chartRing (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r)) :=
  ((baseRingHom (I.map (algebraMap A B))
    (mapGenerator I (algebraMap A B) r)).comp (algebraMap A B)).toAlgebra

attribute [local instance] chartBaseAlgebra

/-- The chart base-change map as an algebra morphism over the original base ring. -/
def chartBaseChangeAlgHom (I : Ideal A) (r : I) :
    chartRing I r →ₐ[A]
      chartRing (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) where
  toFun := chartBaseChangeHom I (algebraMap A B) r
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' a := chartBaseChangeHom_baseRingHom I (algebraMap A B) r a

/-- The structure map of the extended chart, as an algebra morphism over the original base. -/
def chartTargetAlgHom (I : Ideal A) (r : I) :
    B →ₐ[A] chartRing (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) where
  toFun := baseRingHom (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r)
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' _ := rfl

/-- The canonical comparison map from the scalar extension of a standard Rees chart to the
corresponding standard chart of the base-changed ideal. -/
def chartTensorMap (I : Ideal A) (r : I) :
    chartRing I r ⊗[A] B →ₐ[A]
      chartRing (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) :=
  Algebra.TensorProduct.lift (chartBaseChangeAlgHom I r) (chartTargetAlgHom I r)
    (fun _ _ ↦ Commute.all _ _)

@[simp]
theorem chartTensorMap_tmul (I : Ideal A) (r : I) (z : chartRing I r) (b : B) :
    chartTensorMap I r (z ⊗ₜ[A] b) =
      chartBaseChangeHom I (algebraMap A B) r z *
        baseRingHom (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) b := by
  simp [chartTensorMap, chartBaseChangeAlgHom, chartTargetAlgHom]

theorem chartElem_mem_range (I : Ideal A) (r : I) (n : ℕ) {b : B}
    (hb : b ∈ Ideal.map (algebraMap A B) (I ^ n)) :
    b ∈ (I.map (algebraMap A B)) ^ n ∧
      ∃ w : chartRing I r ⊗[A] B,
        chartTensorMap I r w =
          chartElem (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) n b := by
  refine Submodule.span_induction
    (p := fun b _ ↦ b ∈ (I.map (algebraMap A B)) ^ n ∧
      ∃ w : chartRing I r ⊗[A] B, chartTensorMap I r w =
        chartElem (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) n b)
    ?_ ?_ ?_ ?_ hb
  · rintro _ ⟨c, hc, rfl⟩
    refine ⟨by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hc,
      chartElem I r n c ⊗ₜ[A] (1 : B), ?_⟩
    rw [chartTensorMap_tmul, map_one, mul_one,
      chartBaseChangeHom_chartElem I (algebraMap A B) r n hc]
  · exact ⟨Ideal.zero_mem _, (0 : chartRing I r ⊗[A] B), by rw [map_zero, chartElem_zero]⟩
  · rintro x y _ _ ⟨hx, wx, hwx⟩ ⟨hy, wy, hwy⟩
    exact ⟨Ideal.add_mem _ hx hy, wx + wy, by
      rw [map_add, hwx, hwy, chartElem_add _ _ n hx hy]⟩
  · rintro c x _ ⟨hx, wx, hwx⟩
    refine ⟨Ideal.mul_mem_left _ c hx, (1 ⊗ₜ[A] c) * wx, ?_⟩
    rw [map_mul, hwx, chartTensorMap_tmul, map_one, one_mul, baseRingHom_eq_chartElem,
      chartElem_mul _ _ 0 n (by simp) hx, zero_add, smul_eq_mul]

theorem chartTensorMap_surjective (I : Ideal A) (r : I) :
    Function.Surjective (chartTensorMap (B := B) I r) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ :=
    chartElem_surjective (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) z
  exact (chartElem_mem_range I r n (by rwa [Ideal.map_pow])).2

/-- The `A`-linear map sending `c ∈ Iⁿ` to the chart element `c / rⁿ`. -/
def chartElemLinear (I : Ideal A) (r : I) (n : ℕ) :
    (I ^ n : Ideal A) →ₗ[A] chartRing I r where
  toFun c := chartElem I r n c.1
  map_add' c d := (chartElem_add I r n c.2 d.2).symm
  map_smul' a c := by
    change chartElem I r n (a * c.1) = a • chartElem I r n c.1
    rw [Algebra.smul_def, chartAlgebraMap_apply, chartElem_mul I r 0 n (by simp) c.2, zero_add]

@[simp]
theorem chartElemLinear_apply (I : Ideal A) (r : I) (n : ℕ) (c : (I ^ n : Ideal A)) :
    chartElemLinear I r n c = chartElem I r n c.1 := rfl

/-- Multiplication by `rᵏ`, viewed as an `A`-linear map from `Iⁿ` to `I^(n+k)`. -/
def idealPowShift (I : Ideal A) (r : I) (n k : ℕ) :
    (I ^ n : Ideal A) →ₗ[A] (I ^ (n + k) : Ideal A) where
  toFun c := ⟨r.1 ^ k * c.1, by
    rw [Nat.add_comm n k]
    exact mul_mem_pow_add I (Ideal.pow_mem_pow r.2 k) c.2⟩
  map_add' c d := by
    apply Subtype.ext
    simp [mul_add]
  map_smul' a c := by
    apply Subtype.ext
    simp [smul_eq_mul]
    ring

@[simp]
theorem idealPowShift_apply (I : Ideal A) (r : I) (n k : ℕ) (c : (I ^ n : Ideal A)) :
    ((idealPowShift I r n k c : (I ^ (n + k) : Ideal A)) : A) = r.1 ^ k * c.1 := rfl

theorem chartElemLinear_comp_shift (I : Ideal A) (r : I) (n k : ℕ) :
    (chartElemLinear I r (n + k)).comp (idealPowShift I r n k) = chartElemLinear I r n := by
  apply LinearMap.ext
  intro c
  exact (chartElem_shift I r n k c.2).symm

/-- Evaluation of a scalar extension of an ideal power inside the extended base ring. -/
def idealPowTensorEval (I : Ideal A) (n : ℕ) :
    (I ^ n : Ideal A) ⊗[A] B →ₗ[A] B :=
  (TensorProduct.lid A B).toLinearMap.comp
    (LinearMap.rTensor B ((I ^ n : Ideal A).subtype))

@[simp]
theorem idealPowTensorEval_tmul (I : Ideal A) (n : ℕ) (c : (I ^ n : Ideal A)) (b : B) :
    idealPowTensorEval I n (c ⊗ₜ[A] b) = algebraMap A B c.1 * b := by
  simp [idealPowTensorEval, Algebra.smul_def]

theorem idealPowTensorEval_injective (I : Ideal A) (n : ℕ) [Module.Flat A B] :
    Function.Injective (idealPowTensorEval (B := B) I n) :=
  (TensorProduct.lid A B).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _))

theorem idealPowTensorEval_mem (I : Ideal A) (n : ℕ) (w : (I ^ n : Ideal A) ⊗[A] B) :
    idealPowTensorEval I n w ∈ (I.map (algebraMap A B)) ^ n := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
      rw [idealPowTensorEval_tmul]
      refine Ideal.mul_mem_right _ _ ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ c.2
  | add x y hx hy =>
      rw [map_add]
      exact Ideal.add_mem _ hx hy

theorem idealPowTensorEval_shift (I : Ideal A) (r : I) (n k : ℕ)
    (w : (I ^ n : Ideal A) ⊗[A] B) :
    idealPowTensorEval I (n + k) (LinearMap.rTensor B (idealPowShift I r n k) w) =
      algebraMap A B r.1 ^ k * idealPowTensorEval I n w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
      rw [LinearMap.rTensor_tmul, idealPowTensorEval_tmul, idealPowTensorEval_tmul,
        idealPowShift_apply, map_mul, map_pow, mul_assoc]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, mul_add]

theorem chartTensorMap_rTensor (I : Ideal A) (r : I) (n : ℕ)
    (w : (I ^ n : Ideal A) ⊗[A] B) :
    chartTensorMap I r (LinearMap.rTensor B (chartElemLinear I r n) w) =
      chartElem (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) n
        (idealPowTensorEval I n w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [chartElem_zero]
  | tmul c b =>
      rw [LinearMap.rTensor_tmul, chartElemLinear_apply, chartTensorMap_tmul,
        chartBaseChangeHom_chartElem I (algebraMap A B) r n c.2, baseRingHom_eq_chartElem,
        chartElem_mul _ _ n 0 (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ c.2)
          (by simp), add_zero, idealPowTensorEval_tmul]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add,
        chartElem_add _ _ n (idealPowTensorEval_mem I n x) (idealPowTensorEval_mem I n y)]

theorem exists_rTensor_chartElemLinear_eq (I : Ideal A) (r : I)
    (z : chartRing I r ⊗[A] B) :
    ∃ (n : ℕ) (w : (I ^ n : Ideal A) ⊗[A] B),
      LinearMap.rTensor B (chartElemLinear I r n) w = z := by
  have hshift : ∀ (n k : ℕ) (w : (I ^ n : Ideal A) ⊗[A] B),
      LinearMap.rTensor B (chartElemLinear I r (n + k))
        (LinearMap.rTensor B (idealPowShift I r n k) w) =
        LinearMap.rTensor B (chartElemLinear I r n) w := by
    intro n k w
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, chartElemLinear_comp_shift]
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, map_zero _⟩
  | tmul z b =>
      obtain ⟨n, c, hc, rfl⟩ := chartElem_surjective I r z
      exact ⟨n, (⟨c, hc⟩ : (I ^ n : Ideal A)) ⊗ₜ[A] b, by simp⟩
  | add x y hx hy =>
      obtain ⟨n, w, rfl⟩ := hx
      obtain ⟨m, v, rfl⟩ := hy
      rcases Nat.le_total n m with hnm | hmn
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
        exact ⟨n + k, LinearMap.rTensor B (idealPowShift I r n k) w + v, by
          rw [map_add, hshift]⟩
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        exact ⟨m + k, w + LinearMap.rTensor B (idealPowShift I r m k) v, by
          rw [map_add, hshift]⟩

theorem chartTensorMap_injective (I : Ideal A) (r : I) [Module.Flat A B] :
    Function.Injective (chartTensorMap (B := B) I r) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, w, rfl⟩ := exists_rTensor_chartElemLinear_eq I r z
  rw [chartTensorMap_rTensor] at hz
  obtain ⟨k, hk⟩ :=
    (chartElem_eq_zero_iff _ _ n (idealPowTensorEval_mem I n w)).mp hz
  have hzero : LinearMap.rTensor B (idealPowShift I r n k) w = 0 := by
    apply idealPowTensorEval_injective (B := B) I (n + k)
    rw [idealPowTensorEval_shift, map_zero]
    exact hk
  rw [← chartElemLinear_comp_shift I r n k, LinearMap.rTensor_comp, LinearMap.comp_apply,
    hzero, map_zero]

theorem chartTensorMap_bijective (I : Ideal A) (r : I) [Module.Flat A B] :
    Function.Bijective (chartTensorMap (B := B) I r) :=
  ⟨chartTensorMap_injective I r, chartTensorMap_surjective I r⟩

/-- Rees charts commute with flat base change: the scalar extension of a standard chart is the
corresponding standard chart of the base-changed ideal. -/
def chartTensorEquiv (I : Ideal A) (r : I) [Module.Flat A B] :
    chartRing I r ⊗[A] B ≃ₐ[A]
      chartRing (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) :=
  AlgEquiv.ofBijective (chartTensorMap I r) (chartTensorMap_bijective I r)

theorem chartTensorMap_includeLeft (I : Ideal A) (r : I) :
    (chartTensorMap (B := B) I r).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom) =
      chartBaseChangeHom I (algebraMap A B) r := by
  apply RingHom.ext
  intro z
  change chartTensorMap I r (z ⊗ₜ[A] (1 : B)) = _
  rw [chartTensorMap_tmul, map_one, mul_one]

theorem chartTensorMap_includeRight (I : Ideal A) (r : I) :
    (chartTensorMap (B := B) I r).toRingHom.comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] _).toRingHom =
      baseRingHom (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) := by
  apply RingHom.ext
  intro b
  change chartTensorMap I r ((1 : chartRing I r) ⊗ₜ[A] b) = _
  rw [chartTensorMap_tmul, map_one, one_mul]

end FlatChart

/-! ## The cartesian chart square -/

section ChartPullback

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

attribute [local instance] chartAlgebra chartBaseAlgebra

/-- The structure morphism of a standard Rees chart down to its affine base. -/
def chartProjection (I : Ideal A) (r : I) : chart I r ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (baseRingHom I r))

theorem chartMap_comp_projection (I : Ideal A) (r : I) :
    chartMap I r ≫ projection I = chartProjection I r :=
  chartMap_projection I r

/-- The comparison morphism from a standard chart of the base-changed blowup to the
corresponding standard chart of the original blowup. -/
def chartSchemeBaseChange (I : Ideal A) (r : I) :
    chart (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) ⟶ chart I r :=
  Spec.map (CommRingCat.ofHom (chartBaseChangeHom I (algebraMap A B) r))

theorem chartSchemeBaseChange_comm (I : Ideal A) (r : I) :
    chartSchemeBaseChange I r ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (chartRing I r))) =
      Spec.map (CommRingCat.ofHom (algebraMap B
          (chartRing (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
  rw [chartSchemeBaseChange, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro a
  exact chartBaseChangeHom_baseRingHom I (algebraMap A B) r a

/-- On every standard chart, the affine Rees blowup of a flat base change is the base change of
the affine Rees blowup. -/
theorem chart_isPullback (I : Ideal A) (r : I) [Module.Flat A B] :
    IsPullback (chartSchemeBaseChange I r)
      (Spec.map (CommRingCat.ofHom (algebraMap B
        (chartRing (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r)))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (chartRing I r))))
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  have hiso : IsIso (Spec.map (CommRingCat.ofHom (chartTensorMap (B := B) I r).toRingHom)) := by
    rw [isIso_SpecMap_iff]
    exact chartTensorMap_bijective I r
  refine IsPullback.of_iso_pullback ⟨chartSchemeBaseChange_comm I r⟩
    (asIso (Spec.map (CommRingCat.ofHom (chartTensorMap (B := B) I r).toRingHom)) ≪≫
      (pullbackSpecIso A (chartRing I r) B).symm) ?_ ?_
  · rw [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc, pullbackSpecIso_inv_fst,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, chartSchemeBaseChange]
    congr 2
    apply RingHom.ext
    intro z
    change chartTensorMap I r (z ⊗ₜ[A] (1 : B)) = chartBaseChangeHom I (algebraMap A B) r z
    rw [chartTensorMap_tmul, map_one, mul_one]
  · rw [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc, pullbackSpecIso_inv_snd,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro b
    change chartTensorMap I r ((1 : chartRing I r) ⊗ₜ[A] b) =
      baseRingHom (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) b
    rw [chartTensorMap_tmul, map_one, one_mul]

/-- The cartesian chart square, phrased through the chart structure morphisms. -/
theorem chartProjection_isPullback (I : Ideal A) (r : I) [Module.Flat A B] :
    IsPullback (chartSchemeBaseChange I r)
      (chartProjection (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r))
      (chartProjection I r) (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  chart_isPullback I r

end ChartPullback

/-! ## The global cartesian square -/

section GlobalPullback

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The structure map from the base ring to the homogeneous localization of the Rees algebra at
a homogeneous element. -/
def awayBaseHom (I : Ideal A) (s : reesAlgebra I) :
    A →+* HomogeneousLocalization.Away (grade I) s :=
  (HomogeneousLocalization.fromZeroRingHom (grade I) (Submonoid.powers s)).comp
    (zeroEquiv I).symm.toRingHom

theorem baseRingHom_eq_awayBaseHom (I : Ideal A) (r : I) :
    baseRingHom I r = awayBaseHom I (generator I r) := rfl

theorem awayι_comp_projection (I : Ideal A) {d : ℕ} (s : reesAlgebra I) (hs : s ∈ grade I d)
    (hd : 0 < d) :
    Proj.awayι (grade I) s hs hd ≫ projection I =
      Spec.map (CommRingCat.ofHom (awayBaseHom I s)) := by
  rw [projection, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem awayMap_awayBaseHom (I : Ideal A) (f : A →+* B) (s : reesAlgebra I) (a : A) :
    HomogeneousLocalization.Away.map (gradedMap I f) s (awayBaseHom I s a) =
      awayBaseHom (I.map f) ((gradedMap I f) s) (f a) := by
  have h1 : ∀ y : grade I 0,
      HomogeneousLocalization.fromZeroRingHom (grade I) (Submonoid.powers s) y =
        HomogeneousLocalization.mk ⟨0, y, 1, one_mem _⟩ := fun _ ↦ rfl
  have h2 : ∀ y : grade (I.map f) 0,
      HomogeneousLocalization.fromZeroRingHom (grade (I.map f))
          (Submonoid.powers ((gradedMap I f) s)) y =
        HomogeneousLocalization.mk ⟨0, y, 1, one_mem _⟩ := fun _ ↦ rfl
  apply HomogeneousLocalization.val_injective
  rw [awayBaseHom, awayBaseHom, RingHom.comp_apply, RingHom.comp_apply, h1, h2,
    HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  congr 1
  · apply Subtype.ext
    simp [zeroEquiv, component, gradedMap]
  · apply Subtype.ext
    exact map_one (reesMap I f)

theorem awayι_comp_schemeMap_comp_projection (I : Ideal A) (f : A →+* B) {d : ℕ} (hd : 0 < d)
    (s : reesAlgebra I) (hs : s ∈ grade I d) :
    Proj.awayι (grade (I.map f)) ((gradedMap I f) s) ((gradedMap I f).2 hs) hd ≫
        schemeMap I f ≫ projection I =
      Proj.awayι (grade (I.map f)) ((gradedMap I f) s) ((gradedMap I f).2 hs) hd ≫
        projection (I.map f) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Category.assoc, ← Category.assoc, schemeMap,
    Proj.awayι_comp_map (gradedMap I f) (irrelevant_le_map_gradedMap I f) hd s hs,
    Category.assoc, awayι_comp_projection I s hs hd,
    awayι_comp_projection (I.map f) ((gradedMap I f) s) ((gradedMap I f).2 hs) hd,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro a
  exact awayMap_awayBaseHom I f s a

/-- The affine Rees blowup projection is natural in the base ring. -/
theorem schemeMap_comp_projection (I : Ideal A) (f : A →+* B) :
    schemeMap I f ≫ projection I = projection (I.map f) ≫ Spec.map (CommRingCat.ofHom f) := by
  refine (Proj.mapAffineOpenCover (gradedMap I f)
      (irrelevant_le_map_gradedMap I f)).openCover.hom_ext _ _ fun s ↦ ?_
  exact awayι_comp_schemeMap_comp_projection I f s.1.2 s.2.1 s.2.2

theorem awayι_comp_schemeMap (I : Ideal A) (f : A →+* B) (r : I)
    (q : reesAlgebra (I.map f)) (hq : q ∈ grade (I.map f) 1)
    (h : (gradedMap I f) (generator I r) = q)
    (hle : Submonoid.powers (generator I r) ≤ (Submonoid.powers q).comap (gradedMap I f)) :
    Proj.awayι (grade (I.map f)) q hq Nat.one_pos ≫ schemeMap I f =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map (gradedMap I f) hle)) ≫
        chartMap I r := by
  subst h
  exact Proj.awayι_comp_map (gradedMap I f) (irrelevant_le_map_gradedMap I f) Nat.one_pos _
    (generator_mem_grade_one I r)

/-- On standard charts, the blowup base-change morphism is the chart base-change map. -/
theorem chartMap_comp_schemeMap (I : Ideal A) (f : A →+* B) (r : I) :
    chartMap (I.map f) (mapGenerator I f r) ≫ schemeMap I f =
      Spec.map (CommRingCat.ofHom (chartBaseChangeHom I f r)) ≫ chartMap I r :=
  awayι_comp_schemeMap I f r _ (generator_mem_grade_one _ _) (reesMap_generator' I f r) _

/-- The standard chart of the base-changed blowup is the full preimage of the corresponding
standard chart. -/
theorem schemeMap_preimage_chartMap_opensRange (I : Ideal A) (f : A →+* B) (r : I) :
    schemeMap I f ⁻¹ᵁ (chartMap I r).opensRange =
      (chartMap (I.map f) (mapGenerator I f r)).opensRange := by
  rw [chartMap_opensRange, chartMap_opensRange, schemeMap_preimage_basicOpen,
    reesMap_generator']

/-- On standard charts, the comparison square for the blowup base change is cartesian. -/
theorem chartMap_isPullback_schemeMap (I : Ideal A) (f : A →+* B) (r : I) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartBaseChangeHom I f r)))
      (chartMap (I.map f) (mapGenerator I f r)) (chartMap I r) (schemeMap I f) :=
  IsOpenImmersion.isPullback _ _ _ _ (chartMap_comp_schemeMap I f r)
    (schemeMap_preimage_chartMap_opensRange I f r)

end GlobalPullback

/-! ## Flat base change for the whole affine blowup -/

section GlobalFlat

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

attribute [local instance] chartAlgebra chartBaseAlgebra

/-- The canonical comparison morphism from the blowup of the extended ideal to the base change
of the blowup. -/
def blowupComparison (I : Ideal A) :
    scheme (I.map (algebraMap A B)) ⟶
      pullback (projection I) (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  pullback.lift (schemeMap I (algebraMap A B)) (projection (I.map (algebraMap A B)))
    (schemeMap_comp_projection I (algebraMap A B))

theorem chartMap_isPullback (I : Ideal A) (r : I) [Module.Flat A B] :
    IsPullback (chartSchemeBaseChange I r)
      (chartMap (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) ≫
        projection (I.map (algebraMap A B)))
      (chartMap I r ≫ projection I) (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  rw [chartMap_projection, chartMap_projection]
  exact chart_isPullback I r

/-- The member of the base-changed affine cover of the pullback attached to a standard chart. -/
def chartPullbackMap (I : Ideal A) (r : I) :
    pullback (chartMap I r ≫ projection I)
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⟶
      pullback (projection I) (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  pullback.map (chartMap I r ≫ projection I) _ (projection I) _ (chartMap I r) (𝟙 _) (𝟙 _)
    (by simp) (by simp)

theorem isIso_snd_blowupComparison (I : Ideal A) (r : I) [Module.Flat A B] :
    IsIso (pullback.snd (blowupComparison (B := B) I) (chartPullbackMap I r)) := by
  have hfst : blowupComparison (B := B) I ≫
      pullback.fst (projection I) (Spec.map (CommRingCat.ofHom (algebraMap A B))) =
      schemeMap I (algebraMap A B) := pullback.lift_fst _ _ _
  have hsnd : blowupComparison (B := B) I ≫
      pullback.snd (projection I) (Spec.map (CommRingCat.ofHom (algebraMap A B))) =
      projection (I.map (algebraMap A B)) := pullback.lift_snd _ _ _
  have hmfst : chartPullbackMap (B := B) I r ≫
      pullback.fst (projection I) (Spec.map (CommRingCat.ofHom (algebraMap A B))) =
      pullback.fst (chartMap I r ≫ projection I)
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫ chartMap I r :=
    pullback.lift_fst _ _ _
  have hmsnd : chartPullbackMap (B := B) I r ≫
      pullback.snd (projection I) (Spec.map (CommRingCat.ofHom (algebraMap A B))) =
      pullback.snd (chartMap I r ≫ projection I)
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    rw [chartPullbackMap, pullback.lift_snd, Category.comp_id]
  have hδfst := (chartMap_isPullback (B := B) I r).isoPullback_hom_fst
  have hδsnd := (chartMap_isPullback (B := B) I r).isoPullback_hom_snd
  have hS3 : IsPullback (pullback.fst (chartMap I r ≫ projection I)
        (Spec.map (CommRingCat.ofHom (algebraMap A B))))
      (chartPullbackMap (B := B) I r) (chartMap I r)
      (pullback.fst (projection I) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) := by
    refine IsPullback.of_bot ?_ hmfst.symm (IsPullback.of_hasPullback _ _)
    rw [hmsnd]
    exact IsPullback.of_hasPullback _ _
  have hp : (chartMap_isPullback (B := B) I r).isoPullback.hom ≫ chartPullbackMap I r =
      chartMap (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r) ≫
        blowupComparison (B := B) I := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmfst, ← Category.assoc, hδfst, Category.assoc, hfst]
      exact (chartMap_comp_schemeMap I (algebraMap A B) r).symm
    · rw [Category.assoc, hmsnd, hδsnd, Category.assoc, hsnd]
  have hS4 : IsPullback (chartMap_isPullback (B := B) I r).isoPullback.hom
      (chartMap (I.map (algebraMap A B)) (mapGenerator I (algebraMap A B) r))
      (chartPullbackMap (B := B) I r) (blowupComparison (B := B) I) := by
    refine IsPullback.of_right ?_ hp hS3
    rw [hδfst, hfst]
    exact chartMap_isPullback_schemeMap I (algebraMap A B) r
  have hres : pullback.snd (blowupComparison (B := B) I) (chartPullbackMap I r) =
      hS4.flip.isoPullback.inv ≫ (chartMap_isPullback (B := B) I r).isoPullback.hom := by
    rw [Iso.eq_inv_comp]
    exact hS4.flip.isoPullback_hom_snd
  rw [hres]
  infer_instance

theorem isIso_blowupComparison (I : Ideal A) [Module.Flat A B] :
    IsIso (blowupComparison (B := B) I) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_openCover
    (Scheme.Pullback.openCoverOfLeft (generatorAffineOpenCover I).openCover
      (projection I) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) fun r ↦ ?_
  rw [MorphismProperty.isomorphisms.iff]
  exact isIso_snd_blowupComparison I r

/-- Flat base change for the affine Rees blowup: the blowup of the extended ideal is the base
change of the blowup. -/
theorem isPullback_schemeMap (I : Ideal A) [Module.Flat A B] :
    IsPullback (schemeMap I (algebraMap A B)) (projection (I.map (algebraMap A B)))
      (projection I) (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  have := isIso_blowupComparison (B := B) I
  exact IsPullback.of_iso_pullback ⟨schemeMap_comp_projection I (algebraMap A B)⟩
    (asIso (blowupComparison (B := B) I)) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- If the base change of affine bases is an open immersion, so is the induced morphism of
blowups. -/
instance isOpenImmersion_schemeMap (I : Ideal A) [Module.Flat A B]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B)))] :
    IsOpenImmersion (schemeMap I (algebraMap A B)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_schemeMap (B := B) I).flip inferInstance

/-- The image of the base-changed blowup is the full inverse image of the image of the base. -/
theorem opensRange_schemeMap (I : Ideal A) [Module.Flat A B]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B)))] :
    (schemeMap I (algebraMap A B)).opensRange =
      projection I ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap A B))).opensRange := by
  have h : (isPullback_schemeMap (B := B) I).isoPullback.hom ≫
      pullback.fst (projection I) (Spec.map (CommRingCat.ofHom (algebraMap A B))) =
      schemeMap I (algebraMap A B) := (isPullback_schemeMap (B := B) I).isoPullback_hom_fst
  refine TopologicalSpace.Opens.ext ?_
  have hset : Set.range (schemeMap I (algebraMap A B)) =
      Set.range (pullback.fst (projection I)
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))) := by
    have hsurj : Function.Surjective (isPullback_schemeMap (B := B) I).isoPullback.hom := by
      exact (isPullback_schemeMap (B := B) I).isoPullback.hom.homeomorph.surjective
    rw [← h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr hsurj, Set.image_univ]
  rw [Scheme.Hom.coe_opensRange, hset]
  exact IsOpenImmersion.range_pullbackFst _ _

end GlobalFlat

/-! ## Compatibility with localization of the base -/

section LocalizationBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Blowing up commutes with localization of the affine base. -/
theorem isPullback_schemeMap_isLocalization (I : Ideal A) (S : Submonoid A)
    [IsLocalization S B] :
    IsPullback (schemeMap I (algebraMap A B)) (projection (I.map (algebraMap A B)))
      (projection I) (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  have : Module.Flat A B := IsLocalization.flat B S
  exact isPullback_schemeMap I

/-- The blowup of a centre localized at a base element is the part of the blowup lying over the
corresponding principal open of the base.  This is the gluing datum for a global blowup. -/
theorem opensRange_schemeMap_localizationAway (I : Ideal A) (a : A) :
    (schemeMap I (algebraMap A (Localization.Away a))).opensRange =
      projection I ⁻¹ᵁ PrimeSpectrum.basicOpen a := by
  rw [opensRange_schemeMap I, Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A) a]

end LocalizationBaseChange

end

end AlgebraicGeometry.ReesBlowup
