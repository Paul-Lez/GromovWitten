/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.Int.Cast.Lemmas

/-!
# The projective line over `ℤ`: the graded ring and its charts

Let `ℤ' := ULift.{u} ℤ` (Mathlib's standard representative of `ℤ` in the working universe `u`,
as used by `AlgebraicGeometry.AffineSpace`), `A := MvPolynomial (Fin 2) ℤ'` and
`𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) ℤ'` the grading by total degree. This file
proves the commutative-algebra facts behind the projective line `Proj 𝒜`: the degree-zero part
of `𝒜` is `ℤ'`, each of the two standard charts `Away 𝒜 (Xᵢ)` (the homogeneous localisation away
from a coordinate) is a polynomial ring in one variable over `ℤ'` via the coordinate
`t i := X (other i) / X i`, and the irrelevant ideal is contained in the span of the two
coordinates (so the two charts cover `Proj 𝒜`).

## Main results

* `grading`, `instance : GradedAlgebra grading`: the grading of `A` by total degree.
* `algebraMap_gradeZero_bijective`, `instGradeZeroAlgebra`, `gradeZeroEquiv`: the degree-zero
  part of `𝒜` is canonically `ℤ'`.
* `instFiniteTypeGradeZero`: `A` is of finite type over `grading 0`.
* `X`, `X_mem`, `other`, `t`: the two coordinates and the coordinate `t i = X (other i) / X i`
  of the `i`-th standard chart `Away grading (X i)`.
* `ev`, `ev_t`: evaluation of the chart ring at a point, characterised by its value on `t i`.
* `adjoin_t_eq_top`, `ringHom_ext_t`: `t i` generates `Away grading (X i)` as a `ℤ'`-algebra, so
  ring homomorphisms out of it are determined by their value on `t i`.
* `awayEquivPoly`, `awayEquivPoly_t`, `awayEquivPoly_symm_X`: the `i`-th standard chart is
  isomorphic, as a ring, to the polynomial ring `MvPolynomial PUnit ℤ'` in one variable, via
  `t i ↦ X ()`.
* `irrelevant_le_span_X`, `instIsDomain`, `X_ne_zero`: the irrelevant ideal is contained in the
  span of the two coordinates, and `A` is a domain.
-/

universe u

noncomputable section

namespace GromovWitten.AlgebraicGeometry.P1

/-- The base ring: `ℤ` lifted to the working universe `u`, as used throughout this development
(matching `AlgebraicGeometry.AffineSpace`'s use of `ULift ℤ`). -/
abbrev Zu : Type u := ULift.{u} ℤ

/-- The homogeneous coordinate ring of the projective line, `ℤ'[X₀, X₁]`. -/
abbrev A : Type u := MvPolynomial (Fin 2) Zu.{u}

/-- The grading of `A` by total degree. -/
abbrev grading : ℕ → Submodule Zu.{u} A.{u} :=
  MvPolynomial.homogeneousSubmodule (Fin 2) Zu.{u}

instance : GradedAlgebra grading.{u} := MvPolynomial.gradedAlgebra

/-- The `i`-th coordinate of `ℙ¹`. -/
abbrev X (i : Fin 2) : A.{u} := MvPolynomial.X i

/-- Any two ring homomorphisms `ℤ' → R` agree (`ℤ'` is isomorphic to `ℤ`, and ring homomorphisms
out of `ℤ` are unique). -/
theorem ringHom_ext_Zu {R : Type*} [NonAssocSemiring R] (f g : Zu.{u} →+* R) : f = g := by
  have e : Zu.{u} ≃+* ℤ := ULift.ringEquiv
  have h1 : f.comp e.symm.toRingHom = g.comp e.symm.toRingHom := RingHom.ext_int _ _
  ext x
  have hx : x = e.symm (e x) := (e.symm_apply_apply x).symm
  rw [hx]
  exact RingHom.congr_fun h1 (e x)

/-- The canonical ring homomorphism `ℤ' → R` for an arbitrary commutative ring `R` (via
`ℤ' ≃+* ℤ` and the integer cast). -/
def ZuRingHom (R : Type*) [CommRing R] : Zu.{u} →+* R :=
  (Int.castRingHom R).comp (ULift.ringEquiv : Zu.{u} ≃+* ℤ).toRingHom

/-- `ZuRingHom` agrees with `algebraMap` whenever the latter is available, by uniqueness of ring
homomorphisms out of `ℤ'`. -/
theorem ZuRingHom_eq_algebraMap {R : Type*} [CommRing R] [Algebra Zu.{u} R] :
    ZuRingHom.{u} R = algebraMap Zu.{u} R := ringHom_ext_Zu.{u} _ _

/-! ### The degree-zero part -/

/-- The ring homomorphism `ℤ' → 𝒜 0` sending `c` to the constant polynomial `C c`. -/
def toGradeZeroHom : Zu.{u} →+* grading.{u} 0 where
  toFun c := ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C (Fin 2) c⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

instance instGradeZeroAlgebra : Algebra Zu.{u} (grading.{u} 0) := toGradeZeroHom.toAlgebra

@[simp] lemma algebraMap_gradeZero_apply (c : Zu.{u}) :
    (algebraMap Zu.{u} (grading.{u} 0) c : A.{u}) = MvPolynomial.C c := rfl

/-- The degree-zero part of `𝒜` is canonically `ℤ'`, via the constant polynomials. -/
theorem algebraMap_gradeZero_bijective :
    Function.Bijective (algebraMap Zu.{u} (grading.{u} 0)) := by
  constructor
  · intro a b h
    exact MvPolynomial.C_injective _ _ (congrArg Subtype.val h)
  · intro p
    have hp := p.property
    obtain ⟨c, hc⟩ := (show ∃ c : Zu.{u}, algebraMap Zu.{u} A.{u} c = p.val by
      simpa only [MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] using hp)
    exact ⟨c, Subtype.ext hc⟩

/-- `A` is of finite type over `𝒜 0`: it is generated by the two coordinates together with the
image of `algebraMap (𝒜 0) A`. -/
instance instFiniteTypeGradeZero : Algebra.FiniteType (grading.{u} 0) A.{u} := by
  refine ⟨{X 0, X 1}, ?_⟩
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hCa : MvPolynomial.C a =
        algebraMap (grading.{u} 0) A.{u} (algebraMap Zu.{u} (grading.{u} 0) a) := rfl
    rw [hCa]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X p j hp =>
    refine Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ?_)
    fin_cases j <;> simp

/-- The canonical isomorphism `ℤ' ≃+* 𝒜 0`. -/
def gradeZeroEquiv : Zu.{u} ≃+* grading.{u} 0 :=
  RingEquiv.ofBijective _ algebraMap_gradeZero_bijective

@[simp] lemma gradeZeroEquiv_apply_coe (c : Zu.{u}) :
    (gradeZeroEquiv.{u} c : A.{u}) = MvPolynomial.C c := rfl

/-! ### The two coordinates -/

theorem X_mem (i : Fin 2) : X.{u} i ∈ grading.{u} 1 := MvPolynomial.isHomogeneous_X Zu.{u} i

theorem X_ne_zero (i : Fin 2) : X.{u} i ≠ 0 := MvPolynomial.X_ne_zero i

/-- The other index in `Fin 2`. -/
def other (i : Fin 2) : Fin 2 := i + 1

theorem other_ne (i : Fin 2) : other i ≠ i := by fin_cases i <;> decide

theorem other_other (i : Fin 2) : other (other i) = i := by fin_cases i <;> decide

/-- `Fin 2` is exactly `{i, other i}`. -/
theorem univ_eq_pair (i : Fin 2) : (Finset.univ : Finset (Fin 2)) = {i, other i} := by
  fin_cases i <;> decide

/-- The explicit witness that `Xᵢⁿ` is a power of `Xᵢ`. -/
abbrev powMem (i : Fin 2) (n : ℕ) : Submonoid.powers (X.{u} i) := ⟨X.{u} i ^ n, ⟨n, rfl⟩⟩

@[simp] theorem powMem_coe (i : Fin 2) (n : ℕ) : (powMem.{u} i n : A.{u}) = X.{u} i ^ n := rfl

/-- The coordinate `t i = X (other i) / X i` of the `i`-th standard chart. -/
def t (i : Fin 2) : HomogeneousLocalization.Away grading.{u} (X.{u} i) :=
  HomogeneousLocalization.Away.mk grading.{u} (X_mem i) 1 (X (other i))
    (by simpa using X_mem (other i))

theorem t_val (i : Fin 2) :
    (t.{u} i).val = Localization.mk (X.{u} (other i)) (powMem i 1) := by
  change (HomogeneousLocalization.Away.mk grading.{u} (X_mem i) 1 (X (other i)) _).val = _
  rw [HomogeneousLocalization.Away.val_mk]

/-! ### The `ℤ'`-algebra structure on a chart, and evaluation -/

/-- The ring homomorphism `ℤ' → Away grading (X i)` through the degree-zero part. -/
def toAwayZeroHom (i : Fin 2) : Zu.{u} →+* HomogeneousLocalization.Away grading.{u} (X.{u} i) :=
  (algebraMap (grading.{u} 0) (HomogeneousLocalization.Away grading.{u} (X.{u} i))).comp
    gradeZeroEquiv.{u}.toRingHom

instance instAwayAlgebra (i : Fin 2) :
    Algebra Zu.{u} (HomogeneousLocalization.Away grading.{u} (X.{u} i)) :=
  (toAwayZeroHom i).toAlgebra

@[simp] lemma algebraMap_away_val (i : Fin 2) (c : Zu.{u}) :
    (algebraMap Zu.{u} (HomogeneousLocalization.Away grading.{u} (X.{u} i)) c).val =
      Localization.mk (MvPolynomial.C c) 1 := by
  change ((algebraMap (grading.{u} 0) (HomogeneousLocalization.Away grading.{u} (X.{u} i)))
    (gradeZeroEquiv.{u} c)).val = _
  rw [HomogeneousLocalization.algebraMap_eq]
  rfl

/-- The ring hom underlying `HomogeneousLocalization.val`. -/
def valRingHom (i : Fin 2) :
    HomogeneousLocalization.Away grading.{u} (X.{u} i) →+* Localization.Away (X.{u} i) where
  toFun := HomogeneousLocalization.val
  map_one' := HomogeneousLocalization.val_one
  map_mul' := HomogeneousLocalization.val_mul
  map_zero' := HomogeneousLocalization.val_zero
  map_add' := HomogeneousLocalization.val_add

@[simp] lemma valRingHom_apply (i : Fin 2)
    (y : HomogeneousLocalization.Away grading.{u} (X.{u} i)) :
    valRingHom i y = y.val := rfl

private theorem ev_isUnit_aux (i : Fin 2) {R : Type*} [CommRing R] (r : R) :
    (MvPolynomial.eval₂Hom (ZuRingHom.{u} R) (Function.update (fun _ : Fin 2 => r) i 1))
        (X.{u} i) * 1 = 1 := by
  rw [MvPolynomial.eval₂Hom_X', Function.update_self, mul_one]

/-- Evaluation of the `i`-th chart ring at a point `r : R`, sending `t i ↦ r`. -/
def ev (i : Fin 2) {R : Type*} [CommRing R] (r : R) :
    HomogeneousLocalization.Away grading.{u} (X.{u} i) →+* R :=
  (Localization.awayLift
      (MvPolynomial.eval₂Hom (ZuRingHom.{u} R) (Function.update (fun _ : Fin 2 => r) i 1))
      (X.{u} i)
      (isUnit_iff_exists_inv.mpr ⟨1, ev_isUnit_aux i r⟩)).comp (valRingHom i)

@[simp] theorem ev_t (i : Fin 2) {R : Type*} [CommRing R] (r : R) : ev.{u} i r (t.{u} i) = r := by
  unfold ev
  rw [RingHom.comp_apply, valRingHom_apply, t_val,
    Localization.awayLift_mk _ (X.{u} i) _ 1 (ev_isUnit_aux i r) 1]
  rw [MvPolynomial.eval₂Hom_X', Function.update_of_ne (other_ne i)]
  simp

/-! ### `t i` generates the `i`-th chart as a `ℤ'`-algebra -/

private theorem monomial_eq_pow_mul (i : Fin 2) (d : Fin 2 →₀ ℕ) (c : Zu.{u}) :
    MvPolynomial.monomial d c = MvPolynomial.C c * (X.{u} i ^ d i * X (other i) ^ d (other i)) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun j => pow_zero _),
    univ_eq_pair i, Finset.prod_pair (other_ne i).symm]

private theorem isHomogeneous_degree_of_mem_support {n : ℕ} {a : A.{u}} (ha : a ∈ grading.{u} n)
    {d : Fin 2 →₀ ℕ} (hd : d ∈ a.support) : d.degree = n := by
  by_contra hne
  exact (MvPolynomial.mem_support_iff.mp hd) (ha.coeff_eq_zero hne)

/-- Every element of the `i`-th chart ring is a `ℤ'`-polynomial expression in `t i`. -/
theorem adjoin_t_eq_top (i : Fin 2) :
    Algebra.adjoin Zu.{u} ({t.{u} i} : Set (HomogeneousLocalization.Away grading.{u} (X.{u} i)))
      = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective grading.{u} (X_mem i) x
  have ha' : a ∈ grading.{u} n := by simpa using ha
  have key : HomogeneousLocalization.Away.mk grading.{u} (X_mem i) n a ha =
      ∑ d ∈ a.support,
        algebraMap Zu.{u} _ (MvPolynomial.coeff d a) * (t.{u} i) ^ (d (other i)) := by
    apply HomogeneousLocalization.val_injective
    have hsum := map_sum (valRingHom i)
      (fun d => algebraMap Zu.{u} (HomogeneousLocalization.Away grading.{u} (X.{u} i))
        (MvPolynomial.coeff d a) * (t.{u} i) ^ (d (other i))) a.support
    simp only [valRingHom_apply] at hsum
    rw [HomogeneousLocalization.Away.val_mk, hsum]
    have hterm : ∀ d ∈ a.support,
        (algebraMap Zu.{u} _ (MvPolynomial.coeff d a) * (t.{u} i) ^ (d (other i))).val =
          Localization.mk (MvPolynomial.monomial d (MvPolynomial.coeff d a)) (powMem i n) := by
      intro d hd
      have hdeg : d i + d (other i) = n := by
        rw [← isHomogeneous_degree_of_mem_support ha' hd, Finsupp.degree_eq_sum,
          univ_eq_pair i, Finset.sum_pair (other_ne i).symm]
      simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
        algebraMap_away_val, t_val, Localization.mk_pow]
      rw [Localization.mk_mul, one_mul, monomial_eq_pow_mul i d (MvPolynomial.coeff d a),
        Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [OneMemClass.coe_one, SubmonoidClass.coe_pow, one_mul]
      rw [← hdeg, pow_add]
      ring
    rw [Finset.sum_congr rfl hterm, ← Localization.mk_sum, ← MvPolynomial.as_sum]
  rw [key]
  have hmem : t.{u} i ∈ Algebra.adjoin Zu.{u} ({t.{u} i} : Set _) := Algebra.subset_adjoin rfl
  refine Subalgebra.sum_mem (Algebra.adjoin Zu.{u} ({t.{u} i} : Set _)) fun d _ =>
    Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.pow_mem _ hmem _)

/-- Ring homomorphisms out of the `i`-th chart ring are determined by their value on `t i`. -/
theorem ringHom_ext_t {i : Fin 2} {R : Type*} [CommRing R]
    {f g : HomogeneousLocalization.Away grading.{u} (X.{u} i) →+* R} (h : f (t i) = g (t i)) :
    f = g := by
  ext x
  have hx : x ∈ Algebra.adjoin Zu.{u}
      ({t.{u} i} : Set (HomogeneousLocalization.Away grading.{u} (X.{u} i))) := by
    rw [adjoin_t_eq_top]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy => rwa [Set.mem_singleton_iff.mp hy]
  | algebraMap c =>
    exact RingHom.congr_fun (ringHom_ext_Zu.{u} (f.comp (algebraMap Zu.{u} _))
      (g.comp (algebraMap Zu.{u} _))) c
  | add y z _ _ ihy ihz => simp only [map_add, ihy, ihz]
  | mul y z _ _ ihy ihz => simp only [map_mul, ihy, ihz]

/-! ### The `i`-th chart is a polynomial ring in one variable -/

private theorem awayEquivPoly_hom_comp_inv (i : Fin 2) :
    (ev.{u} i (MvPolynomial.X PUnit.unit)).comp
        (MvPolynomial.eval₂Hom (algebraMap Zu.{u} _) (fun _ : PUnit.{u + 1} => t.{u} i))
      = RingHom.id (MvPolynomial PUnit.{u + 1} Zu.{u}) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, RingHom.id_apply, MvPolynomial.eval₂Hom_C]
    unfold ev
    rw [RingHom.comp_apply, valRingHom_apply, algebraMap_away_val]
    have heq : Localization.mk (MvPolynomial.C r) (1 : Submonoid.powers (X.{u} i)) =
        algebraMap A.{u} (Localization.Away (X.{u} i)) (MvPolynomial.C r) := by
      rw [Localization.mk_eq_mk'_apply]; exact IsLocalization.mk'_one _ _
    rw [heq, IsLocalization.Away.lift_eq, MvPolynomial.eval₂Hom_C, ZuRingHom_eq_algebraMap,
      MvPolynomial.algebraMap_eq]
  · intro r
    rw [RingHom.comp_apply, RingHom.id_apply, MvPolynomial.eval₂Hom_X', ev_t]

private theorem awayEquivPoly_inv_comp_hom (i : Fin 2) :
    (MvPolynomial.eval₂Hom (algebraMap Zu.{u} _) (fun _ : PUnit.{u + 1} => t.{u} i)).comp
        (ev.{u} i (MvPolynomial.X PUnit.unit))
      = RingHom.id (HomogeneousLocalization.Away grading.{u} (X.{u} i)) := by
  apply ringHom_ext_t
  rw [RingHom.comp_apply, RingHom.id_apply, ev_t, MvPolynomial.eval₂Hom_X']

/-- The isomorphism between the `i`-th standard chart and the polynomial ring `ℤ'[T]`. -/
def awayEquivPoly (i : Fin 2) :
    HomogeneousLocalization.Away grading.{u} (X.{u} i) ≃+* MvPolynomial PUnit.{u + 1} Zu.{u} :=
  RingEquiv.ofRingHom (ev i (MvPolynomial.X PUnit.unit))
    (MvPolynomial.eval₂Hom (algebraMap Zu.{u} _) (fun _ => t i))
    (awayEquivPoly_hom_comp_inv i) (awayEquivPoly_inv_comp_hom i)

@[simp] theorem awayEquivPoly_t (i : Fin 2) :
    awayEquivPoly.{u} i (t.{u} i) = MvPolynomial.X PUnit.unit := ev_t i _

@[simp] theorem awayEquivPoly_symm_X (i : Fin 2) :
    (awayEquivPoly.{u} i).symm (MvPolynomial.X PUnit.unit) = t.{u} i := by
  rw [← awayEquivPoly_t i, RingEquiv.symm_apply_apply]

/-! ### The irrelevant ideal is spanned by the two coordinates -/

private theorem mem_span_X_of_isHomogeneous_pos {n : ℕ} (hn : n ≠ 0) {p : A.{u}}
    (hp : p.IsHomogeneous n) : p ∈ Ideal.span (Set.range X.{u}) := by
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hdeg : m.degree = n := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hm) (hp.coeff_eq_zero hne)
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, map_zero] at hdeg
    exact hn hdeg.symm
  obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp hm0
  exact ⟨i, Set.mem_univ i, by simpa using hi⟩

/-- The irrelevant ideal is contained in the ideal spanned by the two coordinates, in the exact
shape needed by `Proj.iSup_basicOpen_eq_top`/`Proj.affineOpenCoverOfIrrelevantLESpan`. -/
theorem irrelevant_le_span_X :
    (HomogeneousIdeal.irrelevant grading.{u}).toIdeal ≤ Ideal.span (Set.range X.{u}) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi x hx
  exact mem_span_X_of_isHomogeneous_pos hi.ne' hx

instance instIsDomainZu : IsDomain Zu.{u} :=
  MulEquiv.isDomain ℤ (ULift.ringEquiv : Zu.{u} ≃+* ℤ).toMulEquiv

instance instIsDomain : IsDomain A.{u} := inferInstance

end GromovWitten.AlgebraicGeometry.P1
