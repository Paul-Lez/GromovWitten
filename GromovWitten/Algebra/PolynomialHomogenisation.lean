/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.GradedBaseChangeAlong
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.FiniteType

/-!
# The homogenisation `𝒜[t]` of a graded algebra

Let `𝒜 : ℕ → Submodule R S` be a grading of an `R`-algebra `S`.  We grade the polynomial ring
`S[t]` by total degree, `deg t = 1`: the degree-`n` piece `homog 𝒜 n` consists of the polynomials
`∑ⱼ sⱼ tʲ` with `sⱼ ∈ 𝒜 (n - j)` for `j ≤ n` and `sⱼ = 0` for `j > n`.

## Main results

* `homog`, `homog.gradedAlgebra`: the grading `homog 𝒜` of `S[t]` and its `GradedAlgebra`
  instance (Theorem G2.a).
* `homog_zero`, `homogZeroEquiv`, `bijective_algebraMap_homog_zero`, `finiteType_homog_zero`,
  `finiteType_homog_zero_of_finiteType`: the degree-zero part of `𝒜[t]` is `𝒜 0`, and the
  hypotheses of properness of `Proj` transfer from `𝒜` to `𝒜[t]` (Theorem G2.b).
* `homogMap`, `homogMap_id`, `homogMap_comp`: functoriality in graded ring maps.
* `dehomogeniseAt`, `dehomogenise`, `dehomogeniseAlgEquiv`: `Away (𝒜[t]) t ≃ S`,
  `p / tⁿ ↦ p(1)`, natural in graded ring maps (`dehomogeniseAt_awayMap`) (Theorem G2.d).
* `evalZeroGraded`, `evalZeroGraded_surjective`, `irrelevant_le_map_evalZeroGraded`: the
  surjective graded map `𝒜[t] → 𝒜`, `t ↦ 0`, with the irrelevant-ideal condition needed by
  `Proj.map` (Theorem G2.e).
* `homogOver`, `homogOver_isBaseChange`, `isGradedBaseChangeAlong_homog`: homogenisation
  commutes with base change of graded algebras (no flatness needed) (Theorem G2.c).
* `homogEquivOption`, `map_homog_homogEquivOption`, `homogToOptionGraded`,
  `optionToHomogGraded`: for the standard grading of `R[x_i : i ∈ ι]`, the homogenisation is the
  standard grading of `R[x_i : i ∈ Option ι]` (with `t = x_none`), for any index type `ι`.

## Implementation notes

`dehomogeniseAt 𝒜 f hf` is stated for any `f` with `hf : f = X`, since for a graded ring map `g`
the target of `HomogeneousLocalization.Away.map (homogMap g) X` is `Away (ℬ[t]) (map g X)`, which
is not syntactically `Away (ℬ[t]) X`.
-/

open Polynomial DirectSum

namespace GromovWitten.Algebra

noncomputable section

section Homog

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S)

/-- The degree-`n` piece of the homogenisation `𝒜[t]`: polynomials `∑ⱼ sⱼ tʲ` with
`sⱼ ∈ 𝒜 (n - j)`, and `sⱼ = 0` for `j > n`. -/
def homog (n : ℕ) : Submodule R S[X] where
  carrier := {p | ∀ j, p.coeff j ∈ 𝒜 (n - j) ∧ (n < j → p.coeff j = 0)}
  add_mem' {p q} hp hq j := ⟨by rw [coeff_add]; exact add_mem (hp j).1 (hq j).1,
    fun h => by rw [coeff_add, (hp j).2 h, (hq j).2 h, add_zero]⟩
  zero_mem' j := ⟨by rw [coeff_zero]; exact zero_mem _, fun _ => coeff_zero j⟩
  smul_mem' r p hp j := ⟨by rw [coeff_smul]; exact Submodule.smul_mem _ r (hp j).1,
    fun h => by rw [coeff_smul, (hp j).2 h, smul_zero]⟩

variable {𝒜}

/-- Membership in `homog 𝒜 n`, coefficientwise. -/
@[simp]
theorem mem_homog_iff {n : ℕ} {p : S[X]} :
    p ∈ homog 𝒜 n ↔ ∀ j, p.coeff j ∈ 𝒜 (n - j) ∧ (n < j → p.coeff j = 0) :=
  Iff.rfl

/-- The coefficients of an element of `homog 𝒜 n` lie in the expected graded pieces. -/
theorem coeff_mem_of_mem_homog {n : ℕ} {p : S[X]} (hp : p ∈ homog 𝒜 n) (j : ℕ) :
    p.coeff j ∈ 𝒜 (n - j) :=
  (hp j).1

/-- The coefficients of an element of `homog 𝒜 n` vanish above degree `n`. -/
theorem coeff_eq_zero_of_mem_homog {n : ℕ} {p : S[X]} (hp : p ∈ homog 𝒜 n) {j : ℕ}
    (hj : n < j) : p.coeff j = 0 :=
  (hp j).2 hj

/-- An element of `homog 𝒜 n` has `t`-degree at most `n`. -/
theorem natDegree_le_of_mem_homog {n : ℕ} {p : S[X]} (hp : p ∈ homog 𝒜 n) : p.natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ h => coeff_eq_zero_of_mem_homog hp h

/-- An element of `homog 𝒜 n` is the sum of its monomials of degree `≤ n`. -/
theorem eq_sum_monomial_of_mem_homog {n : ℕ} {p : S[X]} (hp : p ∈ homog 𝒜 n) :
    p = ∑ j ∈ Finset.range (n + 1), monomial j (p.coeff j) :=
  as_sum_range' p (n + 1) (Nat.lt_succ_of_le (natDegree_le_of_mem_homog hp))

/-- The monomial `s tʲ` with `s ∈ 𝒜 i` is homogeneous of degree `i + j`. -/
theorem monomial_mem_homog {i : ℕ} {s : S} (hs : s ∈ 𝒜 i) (j : ℕ) :
    monomial j s ∈ homog 𝒜 (i + j) := by
  intro k
  rw [coeff_monomial]
  split_ifs with h
  · subst h
    exact ⟨by rwa [Nat.add_sub_cancel], fun h => by omega⟩
  · exact ⟨zero_mem _, fun _ => rfl⟩

/-- A constant `s ∈ 𝒜 n` is homogeneous of degree `n` in `𝒜[t]`. -/
theorem C_mem_homog {n : ℕ} {s : S} (hs : s ∈ 𝒜 n) : C s ∈ homog 𝒜 n := by
  rw [← monomial_zero_left]
  exact monomial_mem_homog hs 0

/-- The variable `t` is homogeneous of degree `1`. -/
@[simp]
theorem X_mem_homog [SetLike.GradedOne 𝒜] : (X : S[X]) ∈ homog 𝒜 1 := by
  rw [← monomial_one_one_eq_X]
  exact monomial_mem_homog SetLike.GradedOne.one_mem 1

/-- The pieces `homog 𝒜 n` are multiplicative. -/
instance homog.gradedMonoid [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (homog 𝒜) where
  one_mem := by
    rw [← C_1]
    exact C_mem_homog SetLike.GradedOne.one_mem
  mul_mem {i j p q} hp hq k := by
    rw [coeff_mul]
    constructor
    · refine Submodule.sum_mem _ fun x hx => ?_
      rw [Finset.mem_antidiagonal] at hx
      by_cases ha : x.1 ≤ i
      · by_cases hb : x.2 ≤ j
        · have := SetLike.mul_mem_graded (coeff_mem_of_mem_homog hp x.1)
            (coeff_mem_of_mem_homog hq x.2)
          convert this using 2
          omega
        · rw [coeff_eq_zero_of_mem_homog hq (by omega), mul_zero]
          exact zero_mem _
      · rw [coeff_eq_zero_of_mem_homog hp (by omega), zero_mul]
        exact zero_mem _
    · intro hk
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [Finset.mem_antidiagonal] at hx
      by_cases ha : x.1 ≤ i
      · rw [coeff_eq_zero_of_mem_homog hq (by omega), mul_zero]
      · rw [coeff_eq_zero_of_mem_homog hp (by omega), zero_mul]

/-! ### The decomposition -/

section Decomposition

variable (𝒜) [GradedAlgebra 𝒜]

/-- Multiplication by `tʲ`, as a map `𝒜 i → homog 𝒜 (i + j)`. -/
def monomialHomog (i j : ℕ) : 𝒜 i →ₗ[R] homog 𝒜 (i + j) :=
  LinearMap.codRestrict _ ((monomial j : S →ₗ[S] S[X]).restrictScalars R ∘ₗ (𝒜 i).subtype)
    fun x => monomial_mem_homog x.2 j

/-- The decomposition of `s tʲ` into homogeneous pieces. -/
def homogDecomposeAux (j : ℕ) : S →ₗ[R] ⨁ n, homog 𝒜 n :=
  (DirectSum.toModule R ℕ _ fun i =>
    DirectSum.lof R ℕ (fun n => homog 𝒜 n) (i + j) ∘ₗ monomialHomog 𝒜 i j) ∘ₗ
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

/-- The decomposition of `S[t]` into the pieces `homog 𝒜 n`. -/
def homogDecompose : S[X] →ₗ[R] ⨁ n, homog 𝒜 n :=
  Polynomial.lsum fun j => homogDecomposeAux 𝒜 j

variable {𝒜}

/-- `homogDecompose` on a monomial. -/
theorem homogDecompose_monomial (j : ℕ) (s : S) :
    homogDecompose 𝒜 (monomial j s) = homogDecomposeAux 𝒜 j s := by
  simp [homogDecompose]

/-- The decomposition of `s tʲ` for homogeneous `s ∈ 𝒜 i` is concentrated in degree
`i + j`. -/
theorem homogDecomposeAux_of_mem {i : ℕ} {s : S} (hs : s ∈ 𝒜 i) (j : ℕ) :
    homogDecomposeAux 𝒜 j s =
      DirectSum.of (fun n => homog 𝒜 n) (i + j) ⟨monomial j s, monomial_mem_homog hs j⟩ := by
  simp only [homogDecomposeAux, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    DirectSum.decomposeLinearEquiv_apply]
  rw [DirectSum.decompose_of_mem 𝒜 hs, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
  rfl

omit [GradedAlgebra 𝒜] in
private theorem of_homog_congr {a b : ℕ} (h : a = b) (p : S[X]) (ha : p ∈ homog 𝒜 a)
    (hb : p ∈ homog 𝒜 b) :
    DirectSum.of (fun n => homog 𝒜 n) a ⟨p, ha⟩ = DirectSum.of (fun n => homog 𝒜 n) b ⟨p, hb⟩ := by
  subst h
  rfl

/-- Summing the components of `homogDecompose 𝒜 p` gives back `p`. -/
theorem coe_homogDecompose (p : S[X]) :
    DirectSum.coeLinearMap (homog 𝒜) (homogDecompose 𝒜 p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial j s =>
    rw [homogDecompose_monomial]
    induction s using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | homogeneous x =>
      rw [homogDecomposeAux_of_mem x.2, DirectSum.coeLinearMap_of]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The decomposition of an element of `homog 𝒜 n` is concentrated in degree `n`. -/
theorem homogDecompose_of_mem {n : ℕ} {p : S[X]} (hp : p ∈ homog 𝒜 n) :
    homogDecompose 𝒜 p = DirectSum.of (fun n => homog 𝒜 n) n ⟨p, hp⟩ := by
  have hmem : ∀ j, monomial j (p.coeff j) ∈ homog 𝒜 n := by
    intro j
    by_cases hj : j ≤ n
    · have := monomial_mem_homog (coeff_mem_of_mem_homog hp j) j
      rwa [Nat.sub_add_cancel hj] at this
    · rw [coeff_eq_zero_of_mem_homog hp (by omega), map_zero]
      exact zero_mem _
  have key : ∀ j ∈ Finset.range (n + 1), homogDecompose 𝒜 (monomial j (p.coeff j)) =
      DirectSum.of (fun n => homog 𝒜 n) n ⟨monomial j (p.coeff j), hmem j⟩ := by
    intro j hj
    rw [homogDecompose_monomial, homogDecomposeAux_of_mem (coeff_mem_of_mem_homog hp j)]
    exact of_homog_congr (Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) _ _ _
  conv_lhs => rw [eq_sum_monomial_of_mem_homog hp]
  rw [map_sum, Finset.sum_congr rfl key, ← map_sum]
  congr 1
  apply Subtype.ext
  simp only [AddSubmonoidClass.coe_finsetSum]
  exact (eq_sum_monomial_of_mem_homog hp).symm

/-- The homogenisation `homog 𝒜` is a graded algebra. -/
instance homog.gradedAlgebra : GradedAlgebra (homog 𝒜) :=
  { homog.gradedMonoid,
    DirectSum.Decomposition.ofLinearMap _ (homogDecompose 𝒜)
      (LinearMap.ext coe_homogDecompose)
      (DirectSum.linearMap_ext _ fun n => LinearMap.ext fun x => by
        simp only [LinearMap.coe_comp, Function.comp_apply, DirectSum.lof_eq_of,
          DirectSum.coeLinearMap_of, LinearMap.id_coe, id_eq]
        exact homogDecompose_of_mem x.2) with }

end Decomposition

/-! ### The degree-zero part -/

section DegreeZero

/-- Theorem G2.b: the degree-zero part of `𝒜[t]` is the image of `𝒜 0` under `C`. -/
theorem homog_zero :
    homog 𝒜 0 = (𝒜 0).map ((monomial 0 : S →ₗ[S] S[X]).restrictScalars R) := by
  ext p
  constructor
  · intro hp
    refine ⟨p.coeff 0, coeff_mem_of_mem_homog hp 0, ?_⟩
    change monomial 0 (p.coeff 0) = p
    rw [monomial_zero_left]
    exact (eq_C_of_natDegree_eq_zero (Nat.le_zero.mp (natDegree_le_of_mem_homog hp))).symm
  · rintro ⟨s, hs, rfl⟩
    exact monomial_mem_homog hs 0

variable (𝒜) [SetLike.GradedMonoid 𝒜]

/-- The degree-zero part of `𝒜[t]` is the degree-zero part of `𝒜`, through `C`. -/
def homogZeroEquiv : 𝒜 0 ≃+* homog 𝒜 0 where
  toFun x := ⟨C (x : S), C_mem_homog x.2⟩
  invFun p := ⟨(p : S[X]).coeff 0, coeff_mem_of_mem_homog p.2 0⟩
  left_inv _ := Subtype.ext coeff_C_zero
  right_inv p := Subtype.ext
    (eq_C_of_natDegree_eq_zero (Nat.le_zero.mp (natDegree_le_of_mem_homog p.2))).symm
  map_mul' x y := Subtype.ext (C_mul (a := (x : S)) (b := (y : S)))
  map_add' x y := Subtype.ext (C_add (a := (x : S)) (b := (y : S)))

variable {𝒜}

/-- The value of `homogZeroEquiv`. -/
@[simp]
theorem coe_homogZeroEquiv_apply (x : 𝒜 0) : (homogZeroEquiv 𝒜 x : S[X]) = C (x : S) := rfl

/-- The value of the inverse of `homogZeroEquiv`. -/
@[simp]
theorem coe_homogZeroEquiv_symm_apply (p : homog 𝒜 0) :
    ((homogZeroEquiv 𝒜).symm p : S) = (p : S[X]).coeff 0 := rfl

/-- `homogZeroEquiv` is compatible with the structure maps from `R`. -/
theorem homogZeroEquiv_algebraMap (r : R) :
    homogZeroEquiv 𝒜 (algebraMap R (𝒜 0) r) = algebraMap R (homog 𝒜 0) r :=
  Subtype.ext (Polynomial.algebraMap_apply r).symm

/-- If the structure map `R → 𝒜 0` is bijective, so is `R → (𝒜[t])₀`. -/
theorem bijective_algebraMap_homog_zero (h : Function.Bijective (algebraMap R (𝒜 0))) :
    Function.Bijective (algebraMap R (homog 𝒜 0)) := by
  have : ⇑(algebraMap R (homog 𝒜 0)) = homogZeroEquiv 𝒜 ∘ algebraMap R (𝒜 0) :=
    funext fun r => (homogZeroEquiv_algebraMap r).symm
  rw [this]
  exact (homogZeroEquiv 𝒜).bijective.comp h

/-- If `S` is of finite type over `𝒜 0`, then `S[t]` is of finite type over `(𝒜[t])₀`. -/
theorem finiteType_homog_zero [Algebra.FiniteType (𝒜 0) S] :
    Algebra.FiniteType (homog 𝒜 0) S[X] := by
  let _ : Algebra (𝒜 0) (homog 𝒜 0) := (homogZeroEquiv 𝒜).toRingHom.toAlgebra
  have : IsScalarTower (𝒜 0) (homog 𝒜 0) S[X] :=
    IsScalarTower.of_algebraMap_eq fun x => (Polynomial.algebraMap_apply x).trans rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType (𝒜 0) (homog 𝒜 0) S[X]

/-- If `S` is of finite type over `R`, then `S[t]` is of finite type over `(𝒜[t])₀`. -/
theorem finiteType_homog_zero_of_finiteType [Algebra.FiniteType R S] :
    Algebra.FiniteType (homog 𝒜 0) S[X] := by
  have : IsScalarTower R (homog 𝒜 0) S[X] :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (homog 𝒜 0) S[X]

end DegreeZero

/-! ### Functoriality -/

section Functoriality

variable {R' T : Type*} [CommRing R'] [CommRing T] [Algebra R' T] {ℬ : ℕ → Submodule R' T}
variable {R'' U : Type*} [CommRing R''] [CommRing U] [Algebra R'' U] {𝒞 : ℕ → Submodule R'' U}

/-- A graded ring map `𝒜 → ℬ` induces the graded ring map `𝒜[t] → ℬ[t]` on coefficients. -/
def homogMap (g : 𝒜 →+*ᵍ ℬ) : homog 𝒜 →+*ᵍ homog ℬ where
  toRingHom := Polynomial.mapRingHom g.toRingHom
  map_mem {n p} hp j := by
    simp only [coe_mapRingHom, coeff_map, GradedRingHom.coe_toRingHom]
    exact ⟨g.map_mem (coeff_mem_of_mem_homog hp j),
      fun h => by rw [coeff_eq_zero_of_mem_homog hp h, map_zero]⟩

/-- The value of `homogMap`. -/
@[simp]
theorem homogMap_apply (g : 𝒜 →+*ᵍ ℬ) (p : S[X]) :
    homogMap g p = p.map (g : S →+* T) := rfl

/-- `homogMap` preserves identities. -/
@[simp]
theorem homogMap_id : homogMap (GradedRingHom.id 𝒜) = GradedRingHom.id (homog 𝒜) := by
  refine GradedRingHom.ext fun p => ?_
  change p.map (RingHom.id S) = p
  exact Polynomial.map_id

/-- `homogMap` preserves composition. -/
theorem homogMap_comp (g : 𝒜 →+*ᵍ ℬ) (g' : ℬ →+*ᵍ 𝒞) :
    homogMap (g'.comp g) = (homogMap g').comp (homogMap g) := by
  refine GradedRingHom.ext fun p => ?_
  change p.map ((g' : T →+* U).comp (g : S →+* T)) = (p.map (g : S →+* T)).map (g' : T →+* U)
  exact (Polynomial.map_map _ _ p).symm

end Functoriality

/-! ### The closed piece `t = 0` -/

section EvalZero

variable {R' T : Type*} [CommRing R'] [CommRing T] [Algebra R' T] {ℬ : ℕ → Submodule R' T}

variable (𝒜) in
/-- Setting `t = 0`: the graded ring map `𝒜[t] → 𝒜`, `p ↦ p(0)`, the constant coefficient. -/
def evalZeroGraded : homog 𝒜 →+*ᵍ 𝒜 where
  toRingHom := Polynomial.constantCoeff
  map_mem {_ _} hp := coeff_mem_of_mem_homog hp 0

/-- The value of `evalZeroGraded`. -/
@[simp]
theorem evalZeroGraded_apply (p : S[X]) : evalZeroGraded 𝒜 p = p.coeff 0 := rfl

/-- `evalZeroGraded` is surjective (a constant `s` is the image of `C s`). -/
theorem evalZeroGraded_surjective : Function.Surjective (evalZeroGraded 𝒜) :=
  fun s => ⟨C s, coeff_C_zero⟩

/-- Naturality of `evalZeroGraded`. -/
theorem evalZeroGraded_comp_homogMap (g : 𝒜 →+*ᵍ ℬ) :
    (evalZeroGraded ℬ).comp (homogMap g) = g.comp (evalZeroGraded 𝒜) := by
  ext p
  exact coeff_map _ 0

/-- The irrelevant ideal of `𝒜` is the image of the irrelevant ideal of `𝒜[t]`, as needed for
`Proj.map (evalZeroGraded 𝒜)`. -/
theorem irrelevant_le_map_evalZeroGraded [GradedAlgebra 𝒜] :
    HomogeneousIdeal.irrelevant 𝒜 ≤
      (HomogeneousIdeal.irrelevant (homog 𝒜)).map (evalZeroGraded 𝒜) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi y hy
  rw [HomogeneousIdeal.toIdeal_map]
  have hC : C y ∈ (HomogeneousIdeal.irrelevant (homog 𝒜)).toIdeal := by
    change C y ∈ HomogeneousIdeal.irrelevant (homog 𝒜)
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_ne (homog 𝒜) (C_mem_homog hy) hi.ne']
  have := Ideal.mem_map_of_mem (evalZeroGraded 𝒜) hC
  rwa [evalZeroGraded_apply, coeff_C_zero] at this

end EvalZero

/-! ### The open piece `t ≠ 0` -/

section Dehomogenise

variable [GradedAlgebra 𝒜]

/-- An element of `homog 𝒜 n` whose value at `t = 1` vanishes is zero. -/
theorem eq_zero_of_mem_homog_of_eval_one_eq_zero {n : ℕ} {p : S[X]} (hp : p ∈ homog 𝒜 n)
    (h : p.eval 1 = 0) : p = 0 := by
  ext j
  rw [coeff_zero]
  by_cases hj : j ≤ n
  · rw [eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_le_of_mem_homog hp))] at h
    simp only [one_pow, mul_one] at h
    have h' := congrArg (GradedAlgebra.proj 𝒜 (n - j)) h
    rw [map_sum, map_zero, Finset.sum_eq_single j] at h'
    · rwa [GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_same 𝒜 (coeff_mem_of_mem_homog hp j)] at h'
    · intro i hi hij
      rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜
        (coeff_mem_of_mem_homog hp i)]
      have := Finset.mem_range.mp hi
      omega
    · intro hj'
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) hj'
  · exact coeff_eq_zero_of_mem_homog hp (by omega)

variable (𝒜)

/-- Evaluation at `t = 1` on the localisation `S[t]_f`, for `f = t`. -/
def evalOneLocalization (f : S[X]) (hf : f = X) : Localization.Away f →+* S :=
  IsLocalization.Away.lift f (g := evalRingHom 1) (by rw [hf, coe_evalRingHom, eval_X]; simp)

/-- The ring map `Away (𝒜[t]) f → S`, `p / fⁿ ↦ p(1)`, for `f = t`. -/
def dehomogeniseHom (f : S[X]) (hf : f = X) : HomogeneousLocalization.Away (homog 𝒜) f →+* S :=
  (evalOneLocalization f hf).comp (algebraMap _ (Localization.Away f))

variable {𝒜}

/-- The value of `dehomogeniseHom` on `p / fⁿ` is `p(1)`. -/
theorem dehomogeniseHom_mk (f : S[X]) (hf : f = X) {d : ℕ} (hX : f ∈ homog 𝒜 d) (n : ℕ)
    (p : S[X]) (hp : p ∈ homog 𝒜 (n • d)) :
    dehomogeniseHom 𝒜 f hf (HomogeneousLocalization.Away.mk (homog 𝒜) hX n p hp) = p.eval 1 := by
  simp only [dehomogeniseHom, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk', evalOneLocalization, IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec]
  simp [hf]

/-- Theorem G2.d: `dehomogeniseHom` is bijective. -/
theorem dehomogeniseHom_bijective (f : S[X]) (hf : f = X) :
    Function.Bijective (dehomogeniseHom 𝒜 f hf) := by
  have hX : f ∈ homog 𝒜 1 := hf ▸ X_mem_homog
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (homog 𝒜) hX x
    rw [dehomogeniseHom_mk] at hx
    obtain rfl := eq_zero_of_mem_homog_of_eval_one_eq_zero hp hx
    apply HomogeneousLocalization.val_injective
    simp [Localization.mk_zero]
  · intro s
    induction s using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => exact ⟨0, map_zero _⟩
    | @homogeneous i x =>
      have hC : C (x : S) ∈ homog 𝒜 (i • 1) := by
        rw [smul_eq_mul, mul_one]
        exact C_mem_homog x.2
      exact ⟨HomogeneousLocalization.Away.mk (homog 𝒜) hX i _ hC,
        by rw [dehomogeniseHom_mk, eval_C]⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]⟩

variable (𝒜)

/-- The ring isomorphism `Away (𝒜[t]) f ≃+* S`, `p / fⁿ ↦ p(1)`, for an element `f = t`
(stated for a general `f` with `f = t`, so that it applies to `Away (𝒜[t]) (g t)` for a ring map
`g` with `g t = t`). -/
def dehomogeniseAt (f : S[X]) (hf : f = X) : HomogeneousLocalization.Away (homog 𝒜) f ≃+* S :=
  RingEquiv.ofBijective (dehomogeniseHom 𝒜 f hf) (dehomogeniseHom_bijective f hf)

/-- The ring isomorphism `Away (𝒜[t]) t ≃+* S`, `p / tⁿ ↦ p(1)` (dehomogenisation). -/
def dehomogenise : HomogeneousLocalization.Away (homog 𝒜) (X : S[X]) ≃+* S :=
  dehomogeniseAt 𝒜 X rfl

variable {𝒜}

/-- The value of `dehomogeniseAt` on `p / fⁿ` is `p(1)`. -/
@[simp]
theorem dehomogeniseAt_mk (f : S[X]) (hf : f = X) {d : ℕ} (hX : f ∈ homog 𝒜 d) (n : ℕ)
    (p : S[X]) (hp : p ∈ homog 𝒜 (n • d)) :
    dehomogeniseAt 𝒜 f hf (HomogeneousLocalization.Away.mk (homog 𝒜) hX n p hp) = p.eval 1 :=
  dehomogeniseHom_mk f hf hX n p hp

/-- The value of `dehomogenise` on `p / tⁿ` is `p(1)`. -/
@[simp]
theorem dehomogenise_mk {d : ℕ} (hX : (X : S[X]) ∈ homog 𝒜 d) (n : ℕ) (p : S[X])
    (hp : p ∈ homog 𝒜 (n • d)) :
    dehomogenise 𝒜 (HomogeneousLocalization.Away.mk (homog 𝒜) hX n p hp) = p.eval 1 :=
  dehomogeniseHom_mk X rfl hX n p hp

/-- The inverse of `dehomogeniseAt` on a homogeneous element `s ∈ 𝒜 n` is `C s / fⁿ`. -/
theorem dehomogeniseAt_symm_of_mem (f : S[X]) (hf : f = X) {n : ℕ} {s : S} (hs : s ∈ 𝒜 n) :
    (dehomogeniseAt 𝒜 f hf).symm s =
      HomogeneousLocalization.Away.mk (homog 𝒜) (hf ▸ X_mem_homog : f ∈ homog 𝒜 1) n (C s)
        (by rw [smul_eq_mul, mul_one]; exact C_mem_homog hs) := by
  rw [RingEquiv.symm_apply_eq, dehomogeniseAt_mk, eval_C]

/-- Compatibility of `dehomogeniseAt` with the structure maps from `R`. -/
theorem dehomogeniseAt_algebraMap (f : S[X]) (hf : f = X) (r : R) :
    dehomogeniseAt 𝒜 f hf (algebraMap (homog 𝒜 0) (HomogeneousLocalization.Away (homog 𝒜) f)
      (algebraMap R (homog 𝒜 0) r)) = algebraMap R S r := by
  have hX : f ∈ homog 𝒜 1 := hf ▸ X_mem_homog
  have : algebraMap (homog 𝒜 0) (HomogeneousLocalization.Away (homog 𝒜) f)
      (algebraMap R (homog 𝒜 0) r) =
      HomogeneousLocalization.Away.mk (homog 𝒜) hX 0 (algebraMap R S[X] r)
        (by rw [zero_smul]; exact (algebraMap R (homog 𝒜 0) r).2) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk]
    change Localization.mk ((algebraMap R (homog 𝒜 0) r : S[X])) 1 = _
    congr 1
  rw [this, dehomogeniseAt_mk, Polynomial.algebraMap_apply, eval_C]

variable {R' T : Type*} [CommRing R'] [CommRing T] [Algebra R' T] {ℬ : ℕ → Submodule R' T}
  [GradedAlgebra ℬ]

/-- Naturality of dehomogenisation in a graded ring map `g : 𝒜 → ℬ`. -/
theorem dehomogeniseAt_awayMap (g : 𝒜 →+*ᵍ ℬ) (f : S[X]) (hf : f = X)
    (x : HomogeneousLocalization.Away (homog 𝒜) f) :
    dehomogeniseAt ℬ (homogMap g f) (by rw [hf, homogMap_apply, map_X])
      (HomogeneousLocalization.Away.map (homogMap g) f x) = g (dehomogeniseAt 𝒜 f hf x) := by
  have hX : f ∈ homog 𝒜 1 := hf ▸ X_mem_homog
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (homog 𝒜) hX x
  rw [HomogeneousLocalization.Away.map_mk, dehomogeniseAt_mk, dehomogeniseAt_mk, homogMap_apply,
    eval_one_map]
  rfl

/-- Naturality of `dehomogenise` in a graded ring map `g : 𝒜 → ℬ`. -/
theorem dehomogenise_awayMap (g : 𝒜 →+*ᵍ ℬ) (x : HomogeneousLocalization.Away (homog 𝒜) X) :
    dehomogeniseAt ℬ (homogMap g X) (by rw [homogMap_apply, map_X])
      (HomogeneousLocalization.Away.map (homogMap g) X x) = g (dehomogenise 𝒜 x) :=
  dehomogeniseAt_awayMap g X rfl x

end Dehomogenise

end Homog

/-! ### Dehomogenisation as an algebra isomorphism -/

section AlgEquiv

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]

attribute [local instance] AlgebraicGeometry.ProjBaseChange.awayAlgebra

/-- Dehomogenisation as an `R`-algebra isomorphism `Away (𝒜[t]) t ≃ₐ[R] S`, for the `R`-algebra
structure `AlgebraicGeometry.ProjBaseChange.awayAlgebra` on the homogeneous localisation (through
its degree-zero part; this structure is not a global instance, activate it with
`attribute [local instance] AlgebraicGeometry.ProjBaseChange.awayAlgebra`). -/
def dehomogeniseAlgEquiv : HomogeneousLocalization.Away (homog 𝒜) (X : S[X]) ≃ₐ[R] S :=
  AlgEquiv.ofRingEquiv (f := dehomogenise 𝒜) fun r => dehomogeniseAt_algebraMap X rfl r

/-- The underlying ring isomorphism of `dehomogeniseAlgEquiv` is `dehomogenise`. -/
@[simp]
theorem dehomogeniseAlgEquiv_apply (x : HomogeneousLocalization.Away (homog 𝒜) (X : S[X])) :
    dehomogeniseAlgEquiv 𝒜 x = dehomogenise 𝒜 x := rfl

end AlgEquiv

/-! ### Base change -/

section BaseChange

universe u

open AlgebraicGeometry.ProjBaseChange TensorProduct

section Over

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {S T : Type u} [CommRing S] [CommRing T] [Algebra A S] [Algebra B T] [Algebra A T]
  [IsScalarTower A B T]
variable {𝒜 : ℕ → Submodule A S} [GradedAlgebra 𝒜] {ℬ : ℕ → Submodule B T} [GradedAlgebra ℬ]

omit [GradedAlgebra 𝒜] in
variable (𝒜) in
/-- The `j`-th coefficient, as a linear map `homog 𝒜 n → 𝒜 (n - j)`. -/
def coeffHomog (n j : ℕ) : homog 𝒜 n →ₗ[A] 𝒜 (n - j) :=
  LinearMap.codRestrict _ ((lcoeff S j).restrictScalars A ∘ₗ (homog 𝒜 n).subtype)
    fun p => coeff_mem_of_mem_homog p.2 j

omit [GradedAlgebra 𝒜] in
variable (𝒜) in
/-- Multiplication by `tʲ`, as a linear map `𝒜 (n - j) → homog 𝒜 n` for `j ≤ n`. -/
def monomialHomogLE (n j : ℕ) (hj : j ≤ n) : 𝒜 (n - j) →ₗ[A] homog 𝒜 n :=
  LinearMap.codRestrict _ ((monomial j : S →ₗ[S] S[X]).restrictScalars A ∘ₗ (𝒜 (n - j)).subtype)
    fun x => by
      have := monomial_mem_homog x.2 j
      rwa [Nat.sub_add_cancel hj] at this

omit [GradedAlgebra 𝒜] in
/-- An element of `homog 𝒜 n` is the sum of its monomials `coeff j · tʲ`, `j ≤ n`. -/
theorem sum_monomialHomogLE_coeffHomog {n : ℕ} (p : homog 𝒜 n) :
    ∑ j : Fin (n + 1), monomialHomogLE 𝒜 n j (Nat.lt_succ_iff.mp j.isLt)
      (coeffHomog 𝒜 n j p) = p := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  change ∑ j : Fin (n + 1), monomial (j : ℕ) ((p : S[X]).coeff j) = p
  rw [Fin.sum_univ_eq_sum_range (fun j => monomial j ((p : S[X]).coeff j)) (n + 1)]
  exact (eq_sum_monomial_of_mem_homog p.2).symm

/-- A graded map `ψ : 𝒜 → ℬ` over `A → B` induces the graded map `𝒜[t] → ℬ[t]` over `A → B`. -/
def homogOver (ψ : GradedHomOver 𝒜 ℬ) : GradedHomOver (homog 𝒜) (homog ℬ) where
  __ := homogMap ψ.toGradedRingHom
  commutes' a := by
    change (C (algebraMap A S a)).map (ψ.toRingHom) = _
    rw [map_C, Polynomial.algebraMap_apply]
    exact congrArg C (ψ.commutes a)

omit [Algebra A B] [IsScalarTower A B T] [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- The underlying graded ring map of `homogOver ψ` is `homogMap ψ`. -/
@[simp]
theorem homogOver_toGradedRingHom (ψ : GradedHomOver 𝒜 ℬ) :
    (homogOver ψ).toGradedRingHom = homogMap ψ.toGradedRingHom := rfl

variable (ψ : GradedHomOver 𝒜 ℬ)

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- The `j`-th coefficient of the degree-`n` comparison map of `homogOver ψ` is the
degree-`(n - j)` comparison map of `ψ`. -/
theorem coeff_homogOver_degreeMap (n j : ℕ) (z : homog 𝒜 n ⊗[A] B) :
    ((homogOver ψ).degreeMap n z).coeff j =
      ψ.degreeMap (n - j) ((coeffHomog 𝒜 n j).rTensor B z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul p b =>
    rw [GradedHomOver.degreeMap_tmul, LinearMap.rTensor_tmul, GradedHomOver.degreeMap_tmul,
      Polynomial.algebraMap_apply, coeff_mul_C]
    change ((p : S[X]).map ψ.toRingHom).coeff j * _ = _
    rw [coeff_map]
    rfl
  | add x y hx hy => rw [map_add, coeff_add, hx, hy, map_add, map_add]

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- The comparison map of `homogOver ψ` on `x tʲ ⊗ b` is `tʲ` times that of `ψ`. -/
theorem homogOver_degreeMap_monomial (n j : ℕ) (hj : j ≤ n) (w : 𝒜 (n - j) ⊗[A] B) :
    (homogOver ψ).degreeMap n ((monomialHomogLE 𝒜 n j hj).rTensor B w) =
      monomial j (ψ.degreeMap (n - j) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    rw [LinearMap.rTensor_tmul, GradedHomOver.degreeMap_tmul, GradedHomOver.degreeMap_tmul,
      Polynomial.algebraMap_apply, ← monomial_mul_C]
    change (monomial j (x : S)).map ψ.toRingHom * _ = _
    rw [map_monomial]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

omit [GradedAlgebra 𝒜] in
/-- The degree-`n` comparison map of `homogOver ψ` lands in `homog ℬ n`. -/
theorem homogOver_degreeMap_mem (n : ℕ) (z : homog 𝒜 n ⊗[A] B) :
    (homogOver ψ).degreeMap n z ∈ homog ℬ n := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul p b =>
    rw [GradedHomOver.degreeMap_tmul]
    have hb : algebraMap B T[X] b ∈ homog ℬ 0 := by
      rw [Polynomial.algebraMap_apply]
      exact C_mem_homog (SetLike.algebraMap_mem_graded ℬ b)
    exact SetLike.mul_mem_graded ((homogMap ψ.toGradedRingHom).map_mem p.2) hb
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

omit [GradedAlgebra 𝒜] in
/-- Theorem G2.c: if `ψ` exhibits `ℬ` as the base change of `𝒜` along `A → B`, then
`homogOver ψ` exhibits `ℬ[t]` as the base change of `𝒜[t]`. -/
theorem homogOver_isBaseChange {ψ : GradedHomOver 𝒜 ℬ} (h : ψ.IsBaseChange) :
    (homogOver ψ).IsBaseChange where
  injective n := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hc : ∀ j : Fin (n + 1), (coeffHomog 𝒜 n j).rTensor B z = 0 := by
      intro j
      apply h.injective (n - j)
      rw [← coeff_homogOver_degreeMap, hz, coeff_zero, map_zero]
    have hz' : z = ∑ j : Fin (n + 1),
        (monomialHomogLE 𝒜 n j (Nat.lt_succ_iff.mp j.isLt)).rTensor B
          ((coeffHomog 𝒜 n j).rTensor B z) := by
      clear hz hc
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul p b =>
        simp only [LinearMap.rTensor_tmul]
        rw [← TensorProduct.sum_tmul, sum_monomialHomogLE_coeffHomog]
      | add x y hx hy =>
        simp only [map_add, Finset.sum_add_distrib]
        rw [← hx, ← hy]
    rw [hz']
    exact Finset.sum_eq_zero fun j _ => by rw [hc j, map_zero]
  range_eq n := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      exact homogOver_degreeMap_mem ψ n z
    · intro q hq
      have hw : ∀ j : Fin (n + 1), ∃ w, ψ.degreeMap (n - j) w = q.coeff j :=
        fun j => h.mem_range (coeff_mem_of_mem_homog hq j)
      choose w hw using hw
      refine ⟨∑ j : Fin (n + 1),
        (monomialHomogLE 𝒜 n j (Nat.lt_succ_iff.mp j.isLt)).rTensor B (w j), ?_⟩
      rw [map_sum]
      simp only [homogOver_degreeMap_monomial, hw]
      rw [Fin.sum_univ_eq_sum_range (fun j => monomial j (q.coeff j)) (n + 1)]
      exact (eq_sum_monomial_of_mem_homog hq).symm

end Over

variable {A B S T : Type u} [CommRing A] [CommRing B] [CommRing S] [CommRing T] [Algebra A S]
  [Algebra B T] {f : A →+* B} {𝒜 : ℕ → Submodule A S}
  {ℬ : ℕ → Submodule B T} [GradedAlgebra ℬ] {φ : 𝒜 →+*ᵍ ℬ}

/-- Theorem G2.c along an explicit ring map: if `φ` exhibits `ℬ` as the base change of `𝒜` along
`f`, then `homogMap φ` exhibits `ℬ[t]` as the base change of `𝒜[t]` along `f`. -/
theorem isGradedBaseChangeAlong_homog (h : IsGradedBaseChangeAlong f 𝒜 ℬ φ) :
    IsGradedBaseChangeAlong f (homog 𝒜) (homog ℬ) (homogMap φ) := by
  let _ := f.toAlgebra
  let _ : Algebra A T := ((algebraMap B T).comp f).toAlgebra
  have : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨ψ, rfl, hψ⟩ := h
  exact IsGradedBaseChangeAlong.of_isBaseChange (homogOver ψ) (homogOver_isBaseChange hψ)

end BaseChange

/-! ### Charts: the homogenisation of a polynomial ring -/

section Charts

open MvPolynomial (homogeneousSubmodule)

private theorem degree_option_eq {ι : Type*} (d : Option ι →₀ ℕ) :
    d.degree = d none + d.some.degree := by
  rw [Finsupp.degree_apply, Finsupp.degree_apply]
  exact Finsupp.sum_option_index d (fun _ x => x) (fun _ => rfl) (fun _ _ _ => rfl)

private theorem isHomogeneous_iff_degree {σ R : Type*} [CommRing R] (φ : MvPolynomial σ R)
    (n : ℕ) : φ.IsHomogeneous n ↔ ∀ d, φ.coeff d ≠ 0 → d.degree = n := by
  simp only [MvPolynomial.IsHomogeneous, MvPolynomial.IsWeightedHomogeneous,
    Finsupp.degree_eq_weight_one]
  rfl

variable (R : Type*) [CommRing R] (ι : Type*)

/-- The polynomial ring `R[x_i : i ∈ ι][t]` is `R[x_i : i ∈ Option ι]`, with `t = x_none`. -/
def homogEquivOption : Polynomial (MvPolynomial ι R) ≃ₐ[R] MvPolynomial (Option ι) R :=
  (MvPolynomial.optionEquivLeft R ι).symm

variable {R ι}

/-- Under `optionEquivLeft`, homogeneous polynomials of degree `n` in the variables `Option ι`
correspond to elements of the degree-`n` part of the homogenisation of `R[x_i : i ∈ ι]`. -/
theorem optionEquivLeft_mem_homog_iff (q : MvPolynomial (Option ι) R) (n : ℕ) :
    MvPolynomial.optionEquivLeft R ι q ∈ homog (homogeneousSubmodule ι R) n ↔
      q.IsHomogeneous n := by
  have key : ∀ (j : ℕ) (m : ι →₀ ℕ),
      ((MvPolynomial.optionEquivLeft R ι q).coeff j).coeff m ≠ 0 ↔
        q.coeff (m.optionElim j) ≠ 0 := by
    intro j m
    rw [← MvPolynomial.mem_support_iff, ← MvPolynomial.mem_support_iff]
    exact MvPolynomial.mem_support_coeff_optionEquivLeft R
  have hdeg : ∀ (j : ℕ) (m : ι →₀ ℕ), (m.optionElim j).degree = j + m.degree := by
    intro j m
    rw [degree_option_eq, Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
  constructor
  · intro hP
    rw [isHomogeneous_iff_degree]
    intro d hd
    rw [← Finsupp.optionElim_some d, ← key] at hd
    rw [degree_option_eq]
    by_cases hj : d none ≤ n
    · have h1 := coeff_mem_of_mem_homog hP (d none)
      rw [MvPolynomial.mem_homogeneousSubmodule, isHomogeneous_iff_degree] at h1
      rw [h1 _ hd]
      omega
    · exact absurd (by rw [coeff_eq_zero_of_mem_homog hP (by omega)]; rfl) hd
  · intro hq j
    rw [isHomogeneous_iff_degree] at hq
    constructor
    · rw [MvPolynomial.mem_homogeneousSubmodule, isHomogeneous_iff_degree]
      intro m hm
      have := hq _ ((key j m).mp hm)
      rw [hdeg] at this
      omega
    · intro hj
      ext m
      rw [MvPolynomial.coeff_zero]
      by_contra hm
      have := hq _ ((key j m).mp hm)
      rw [hdeg] at this
      omega

/-- Theorem G2.7: `homogEquivOption` identifies the homogenisation of the standard grading of
`R[x_i : i ∈ ι]` with the standard grading of `R[x_i : i ∈ Option ι]`. -/
theorem map_homog_homogEquivOption (n : ℕ) :
    (homog (homogeneousSubmodule ι R) n).map (homogEquivOption R ι).toLinearMap =
      homogeneousSubmodule (Option ι) R n := by
  ext q
  rw [Submodule.mem_map, MvPolynomial.mem_homogeneousSubmodule]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [← optionEquivLeft_mem_homog_iff]
    change MvPolynomial.optionEquivLeft R ι ((MvPolynomial.optionEquivLeft R ι).symm p) ∈ _
    rwa [AlgEquiv.apply_symm_apply]
  · intro hq
    refine ⟨MvPolynomial.optionEquivLeft R ι q, (optionEquivLeft_mem_homog_iff q n).mpr hq, ?_⟩
    change (MvPolynomial.optionEquivLeft R ι).symm (MvPolynomial.optionEquivLeft R ι q) = q
    exact AlgEquiv.symm_apply_apply _ q

variable (R ι)

/-- `homogEquivOption` as a graded ring map. -/
def homogToOptionGraded :
    homog (homogeneousSubmodule ι R) →+*ᵍ homogeneousSubmodule (Option ι) R where
  toRingHom := (homogEquivOption R ι).toRingEquiv.toRingHom
  map_mem {n p} hp := by
    rw [← map_homog_homogEquivOption]
    exact Submodule.mem_map_of_mem hp

/-- The inverse of `homogEquivOption` as a graded ring map. -/
def optionToHomogGraded :
    homogeneousSubmodule (Option ι) R →+*ᵍ homog (homogeneousSubmodule ι R) where
  toRingHom := (homogEquivOption R ι).symm.toRingEquiv.toRingHom
  map_mem {_ q} hq := (optionEquivLeft_mem_homog_iff q _).mpr hq

/-- `optionToHomogGraded` is a left inverse of `homogToOptionGraded`. -/
theorem optionToHomogGraded_comp_homogToOptionGraded :
    (optionToHomogGraded R ι).comp (homogToOptionGraded R ι) = GradedRingHom.id _ :=
  GradedRingHom.ext fun p => (homogEquivOption R ι).symm_apply_apply p

/-- `optionToHomogGraded` is a right inverse of `homogToOptionGraded`. -/
theorem homogToOptionGraded_comp_optionToHomogGraded :
    (homogToOptionGraded R ι).comp (optionToHomogGraded R ι) = GradedRingHom.id _ :=
  GradedRingHom.ext fun q => (homogEquivOption R ι).apply_symm_apply q

end Charts

end

end GromovWitten.Algebra
