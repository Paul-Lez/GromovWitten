/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/

import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Localization.Integer
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Norm.Defs
import GromovWitten.Algebra.OrderSemilocal

/-!
# Length of a cokernel versus the order of a determinant (Fulton A.2.6)

Let `A` be a Noetherian domain of Krull dimension `≤ 1`. This file proves Fulton's Lemma A.2.6
(*Intersection Theory*, Appendix A.2): for a square matrix `M` over `A` with `det M ≠ 0`,

`Module.length A ((ι → A) ⧸ range M.mulVecLin) = Ring.ord A M.det`

(`OrderDeterminant.cokerLength_eq_ord_det`), and its consequence for a finite free `A`-algebra `B`
and a non-zero-divisor `b : B`, the **norm formula** (Fulton, Prop. 1.4, local form)

`Module.length A (B ⧸ b B) = Ring.ord A (Algebra.norm A b)`

(`OrderDeterminant.length_quotient_span_eq_ord_norm`), which combined with
`OrderSemilocal.length_eq_finsum` says that a finite morphism of curves pushes the divisor of `b`
forward to the divisor of its norm (`OrderDeterminant.finsum_summand_eq_ord_norm`).

## Strategy

Following Fulton, the proof compares the two sides after passing to the fraction field `K`, where
Gaussian elimination is available. Rather than Fulton's *index of a pair of lattices*, we use the
predicate

`CokerOrdProp A Ψ : ∀ c ≠ 0, ∀ P, P.map (algebraMap A K) = algebraMap A K c • Ψ →
  cokerLength P = Ring.ord A P.det`

for a matrix `Ψ` over `K`: "the conclusion holds for every integral multiple of `Ψ`". This carries
the same information as Fulton's index but never requires subtraction, and it is visibly invariant
under rescaling. The proof then has four steps:

* `cokerLength_mul`: `cokerLength` is additive under matrix multiplication (the three-term exact
  sequence `(ι → A) ⧸ ran N → (ι → A) ⧸ ran (M * N) → (ι → A) ⧸ ran M`), and
  `cokerLength_diagonal`: `cokerLength (diagonal d) = ∑ i, Ring.ord A (d i)`
  (`Submodule.quotientPi`);
* `cokerOrdProp_of_witness`: a single integral multiple witnessing the conclusion suffices
  (clearing denominators, `Ring.ord_ne_top` and cancellation in `ℕ∞`);
* `cokerOrdProp_diagonal`, `cokerOrdProp_transvection`, `cokerOrdProp_mul`: the predicate holds for
  diagonal matrices and for transvections and is stable under products. A transvection
  `1 + c • single i j` with `c = a / b` is handled by the factorisation
  `b • transvection i j c = diagonal d' * transvection i j a * diagonal d` over `A`
  (`diagonal_mul_transvection_mul_diagonal`), where `d` is `b` at `i` and `1` elsewhere and `d'`
  is `1` at `i` and `b` elsewhere;
* `Matrix.diagonal_transvection_induction_of_det_ne_zero` assembles these into `CokerOrdProp A Ψ`
  for every invertible `Ψ` over `K`, which applied to `Ψ = M.map (algebraMap A K)` with `c = 1`
  gives the theorem.

## Main declarations

* `OrderDeterminant.cokerLength`: `Module.length A ((ι → A) ⧸ range M.mulVecLin)`.
* `OrderDeterminant.cokerLength_mul`, `OrderDeterminant.cokerLength_diagonal`: the lattice-index
  calculus.
* `OrderDeterminant.cokerLength_eq_ord_det`, `..._of_injective`: Fulton's Lemma A.2.6 for matrices.
* `OrderDeterminant.length_quotient_range_eq_ord_det`, `..._of_injective`: the same statement for
  an endomorphism of a finite free module,
  `Module.length A (M ⧸ range φ) = Ring.ord A (LinearMap.det φ)`.
* `OrderDeterminant.length_quotient_span_eq_ord_norm`: **the norm formula** (Fulton, Prop. 1.4,
  local form; Example A.3.1 in rank `n`): for `B` finite and free over `A` and `b : B` a
  non-zero-divisor, `Module.length A (B ⧸ b B) = Ring.ord A (Algebra.norm A b)`.
* `OrderDeterminant.finsum_summand_eq_ord_norm`: the same statement decomposed over the maximal
  ideals of `B` via `OrderSemilocal.length_eq_finsum` (for `A` local):
  `∑ᶠ q : MaximalSpectrum B, [κ(q):κ_A] · length (B_q) ((B ⧸ bB)_q) = Ring.ord A (Algebra.norm A b)`
  — a finite morphism of curves pushes the divisor of `b` forward to the divisor of its norm.

Note that `A` is *not* assumed local for anything except `finsum_summand_eq_ord_norm`.
-/

open Matrix

namespace OrderDeterminant

section CokerLength

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The length, as an `A`-module, of the cokernel of the endomorphism of `ι → A` given by a square
matrix `M` over `A`. For `M` injective this is the local intersection multiplicity of Fulton's
Lemma A.2.6. -/
noncomputable def cokerLength (M : Matrix ι ι A) : ℕ∞ :=
  Module.length A ((ι → A) ⧸ LinearMap.range M.mulVecLin)

/-- A square matrix over a domain with nonzero determinant acts injectively on vectors. -/
theorem mulVecLin_injective_of_det_ne_zero [IsDomain A] {M : Matrix ι ι A} (hM : M.det ≠ 0) :
    Function.Injective M.mulVecLin := by
  rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro v hv
  exact Matrix.eq_zero_of_mulVec_eq_zero hM hv

/-- An invertible matrix acts surjectively on vectors. -/
theorem range_mulVecLin_eq_top_of_isUnit_det {M : Matrix ι ι A} (hM : IsUnit M.det) :
    LinearMap.range M.mulVecLin = ⊤ := by
  rw [eq_top_iff]
  intro v _
  refine ⟨M⁻¹ *ᵥ v, ?_⟩
  simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM]

/-- An invertible matrix has cokernel of length `0`. -/
theorem cokerLength_eq_zero_of_isUnit_det {M : Matrix ι ι A} (hM : IsUnit M.det) :
    cokerLength M = 0 := by
  rw [cokerLength, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff]
  exact range_mulVecLin_eq_top_of_isUnit_det hM

/-- The identity matrix has cokernel of length `0`. -/
@[simp]
theorem cokerLength_one : cokerLength (1 : Matrix ι ι A) = 0 :=
  cokerLength_eq_zero_of_isUnit_det (by simp)

omit [DecidableEq ι] in
/-- The range of `M * N` is contained in the range of `M`. -/
theorem range_mulVecLin_mul_le (M N : Matrix ι ι A) :
    LinearMap.range (M * N).mulVecLin ≤ LinearMap.range M.mulVecLin := by
  rintro _ ⟨v, rfl⟩
  exact ⟨N.mulVecLin v, by simp⟩

omit [DecidableEq ι] in
/-- **Additivity of the cokernel length under matrix multiplication.** If `M` acts injectively
then `cokerLength (M * N) = cokerLength M + cokerLength N`; this is the additivity of the relative
length of lattices along a chain `ran (M * N) ⊆ ran M ⊆ (ι → A)`. -/
theorem cokerLength_mul {M N : Matrix ι ι A} (hM : Function.Injective M.mulVecLin) :
    cokerLength (M * N) = cokerLength M + cokerLength N := by
  set p : Submodule A (ι → A) := LinearMap.range (M * N).mulVecLin with hp
  set q : Submodule A (ι → A) := LinearMap.range M.mulVecLin with hq
  set r : Submodule A (ι → A) := LinearMap.range N.mulVecLin with hr
  have hpq : p ≤ q := range_mulVecLin_mul_le M N
  have hle : r ≤ Submodule.comap M.mulVecLin p := by
    rintro _ ⟨v, rfl⟩
    exact ⟨v, by simp⟩
  set f : ((ι → A) ⧸ r) →ₗ[A] ((ι → A) ⧸ p) := Submodule.mapQ r p M.mulVecLin hle with hf
  set g : ((ι → A) ⧸ p) →ₗ[A] ((ι → A) ⧸ q) := Submodule.factor hpq with hg
  have hfapp : ∀ v : ι → A, f (Submodule.Quotient.mk v) = Submodule.Quotient.mk (M *ᵥ v) := by
    intro v; rfl
  have hgapp : ∀ v : ι → A, g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
    intro v; rfl
  have hfinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ v =>
      rw [LinearMap.mem_ker, hfapp, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨w, hw⟩ := hx
      have : v = N *ᵥ w := hM (by simpa using hw.symm)
      rw [this, Submodule.Quotient.mk_eq_zero]
      exact ⟨w, rfl⟩
  have hgsurj : Function.Surjective g := Submodule.factor_surjective hpq
  have hex : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro x hx
      induction x using Submodule.Quotient.induction_on with
      | _ v =>
        rw [LinearMap.mem_ker, hgapp, Submodule.Quotient.mk_eq_zero] at hx
        obtain ⟨w, hw⟩ := hx
        exact ⟨Submodule.Quotient.mk w, by rw [hfapp]; exact congrArg _ hw⟩
    · rintro x ⟨y, rfl⟩
      induction y using Submodule.Quotient.induction_on with
      | _ w =>
        rw [LinearMap.mem_ker, hfapp, hgapp, Submodule.Quotient.mk_eq_zero]
        exact ⟨w, rfl⟩
  rw [cokerLength, cokerLength, cokerLength, ← hp, ← hq, ← hr,
    Module.length_eq_add_of_exact f g hfinj hgsurj hex, add_comm]

/-- The range of a diagonal matrix is the product of the principal ideals generated by its
entries. -/
theorem range_mulVecLin_diagonal (d : ι → A) :
    LinearMap.range (Matrix.diagonal d).mulVecLin
      = Submodule.pi Set.univ fun i => (Ideal.span {d i} : Submodule A A) := by
  ext v
  simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, forall_const,
    Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨w, rfl⟩ i
    exact Ideal.mem_span_singleton'.2 ⟨w i, by rw [Matrix.mulVec_diagonal]; ring⟩
  · intro hv
    choose c hc using fun i => Ideal.mem_span_singleton'.1 (hv i)
    refine ⟨c, funext fun i => ?_⟩
    rw [Matrix.mulVec_diagonal, ← hc i]
    ring

/-- **The cokernel length of a diagonal matrix** is the sum of the orders of its entries. -/
theorem cokerLength_diagonal (d : ι → A) :
    cokerLength (Matrix.diagonal d) = ∑ i, Ring.ord A (d i) := by
  rw [cokerLength, range_mulVecLin_diagonal,
    (Submodule.quotientPi fun i => (Ideal.span {d i} : Submodule A A)).length_eq,
    Module.length_pi_of_fintype]
  rfl

/-- Scalar multiplication of a matrix is multiplication by a diagonal matrix. -/
theorem smul_eq_diagonal_mul (c : A) (P : Matrix ι ι A) :
    c • P = Matrix.diagonal (fun _ => c) * P := by
  ext i j
  simp [Matrix.diagonal_mul]

/-- The key factorisation used for transvections with fractional coefficient: a transvection with
coefficient `c` scaled by `b` is a product of a diagonal matrix, an *integral* transvection with
coefficient `b * c`, and another diagonal matrix. Over the fraction field, with `c = a / b`, this
expresses `b • transvection i j c` as a product of matrices defined over `A`. -/
theorem diagonal_mul_transvection_mul_diagonal {i j : ι} (hij : i ≠ j) (b c : A) :
    Matrix.diagonal (fun k => if k = i then 1 else b) * Matrix.transvection i j (b * c) *
        Matrix.diagonal (fun k => if k = i then b else 1)
      = b • Matrix.transvection i j c := by
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.smul_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, smul_eq_mul]
  have hji : j ≠ i := Ne.symm hij
  by_cases hk : k = i
  · subst hk
    by_cases hl : k = l
    · subst hl; simp [hji]
    · by_cases hlj : j = l
      · subst hlj; simp [hl, hji]
      · simp [hl, hlj]
  · have hik : i ≠ k := fun h => hk h.symm
    by_cases hl : k = l
    · subst hl; simp [hk, hik]
    · simp [hk, hl, hik]

variable [IsDomain A]

omit [DecidableEq ι] in
/-- Rescaling a matrix by `c ≠ 0` adds `card ι * Ring.ord A c` to its cokernel length. -/
theorem cokerLength_smul {c : A} (hc : c ≠ 0) (P : Matrix ι ι A) :
    cokerLength (c • P) = (Fintype.card ι : ℕ∞) * Ring.ord A c + cokerLength P := by
  classical
  have hdet : (Matrix.diagonal (fun _ : ι => c)).det ≠ 0 := by
    simpa using pow_ne_zero _ hc
  rw [smul_eq_diagonal_mul, cokerLength_mul (mulVecLin_injective_of_det_ne_zero hdet),
    cokerLength_diagonal]
  simp [Finset.card_univ, nsmul_eq_mul]

/-- Rescaling a matrix by `c ≠ 0` adds `card ι * Ring.ord A c` to the order of its
determinant. -/
theorem ord_det_smul {c : A} (hc : c ≠ 0) (P : Matrix ι ι A) :
    Ring.ord A (c • P).det = (Fintype.card ι : ℕ∞) * Ring.ord A c + Ring.ord A P.det := by
  have hmem : c ^ Fintype.card ι ∈ nonZeroDivisors A :=
    mem_nonZeroDivisors_iff_ne_zero.2 (pow_ne_zero _ hc)
  rw [Matrix.det_smul, Ring.ord_mul' A hmem,
    Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.2 hc), nsmul_eq_mul]

/-- The order of a product of nonzero elements is the sum of their orders. -/
theorem ord_prod {κ : Type*} (s : Finset κ) (f : κ → A) (hf : ∀ i ∈ s, f i ≠ 0) :
    Ring.ord A (∏ i ∈ s, f i) = ∑ i ∈ s, Ring.ord A (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      Ring.ord_mul' A (mem_nonZeroDivisors_iff_ne_zero.2 (hf a (Finset.mem_cons_self a s))),
      ih fun i hi => hf i (Finset.mem_cons_of_mem hi)]

end CokerLength

section Map

/-- Applying a ring homomorphism entrywise to a transvection gives a transvection. -/
theorem transvection_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {ι : Type*}
    [DecidableEq ι] (i j : ι) (c : R) :
    (Matrix.transvection i j c).map f = Matrix.transvection i j (f c) := by
  ext k l
  simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply, apply_ite f]

/-- Entrywise application of a ring homomorphism commutes with the determinant. -/
theorem det_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R) : (M.map f).det = f M.det := by
  rw [RingHom.map_det f M, RingHom.mapMatrix_apply]

end Map

section Predicate

variable {A : Type*} [CommRing A] {K : Type*} [CommRing K] [Algebra A K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (A) in
/-- The auxiliary predicate carrying Fulton's index of a pair of lattices without subtraction:
`CokerOrdProp A Ψ` says that *every* integral multiple `P` of the matrix `Ψ` over `K` satisfies the
conclusion of Lemma A.2.6, `cokerLength P = Ring.ord A P.det`. It is stable under products
(`cokerOrdProp_mul`) and can be checked on a single integral multiple
(`cokerOrdProp_of_witness`). -/
def CokerOrdProp (Ψ : Matrix ι ι K) : Prop :=
  ∀ (c : A) (P : Matrix ι ι A), c ≠ 0 →
    P.map (algebraMap A K) = algebraMap A K c • Ψ → cokerLength P = Ring.ord A P.det

end Predicate

section Scaling

variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K] {ι : Type*} [Finite ι]

/-- Every matrix over the fraction field becomes integral after clearing denominators. -/
theorem exists_integral_scaling (Ψ : Matrix ι ι K) :
    ∃ (c : A) (P : Matrix ι ι A), c ≠ 0 ∧
      P.map (algebraMap A K) = algebraMap A K c • Ψ := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (M := nonZeroDivisors A)
    (S := K) fun p : ι × ι => Ψ p.1 p.2
  choose P hP using fun p : ι × ι => RingHom.mem_range.1 (hb p)
  refine ⟨(b : A), Matrix.of fun i j => P (i, j), nonZeroDivisors.coe_ne_zero b, ?_⟩
  ext i j
  simpa [Algebra.smul_def] using hP (i, j)

end Scaling

section Fraction

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A single integral multiple suffices.** If some integral multiple `P₀ = c₀ • Ψ` of `Ψ`
satisfies `cokerLength P₀ = Ring.ord A P₀.det`, then every integral multiple does: any two integral
multiples `c₀ • P = c • P₀` agree after cross-scaling, and both sides of the desired identity
change by the same amount `card ι * Ring.ord A c` under rescaling by `c`
(`cokerLength_smul`, `ord_det_smul`). -/
theorem cokerOrdProp_of_witness {Ψ : Matrix ι ι K} {c₀ : A} {P₀ : Matrix ι ι A} (hc₀ : c₀ ≠ 0)
    (hP₀ : P₀.map (algebraMap A K) = algebraMap A K c₀ • Ψ)
    (hlen : cokerLength P₀ = Ring.ord A P₀.det) : CokerOrdProp A Ψ := by
  intro c P hc hP
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hkey : c₀ • P = c • P₀ := by
    ext i j
    apply hinj
    have h1 : algebraMap A K (P i j) = algebraMap A K c * Ψ i j := by
      have := congrFun (congrFun hP i) j
      simpa using this
    have h2 : algebraMap A K (P₀ i j) = algebraMap A K c₀ * Ψ i j := by
      have := congrFun (congrFun hP₀ i) j
      simpa using this
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, h1, h2]
    ring
  have hcard : ((Fintype.card ι : ℕ) : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top _
  have hord : Ring.ord A c₀ ≠ ⊤ := Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.2 hc₀)
  have hne : ((Fintype.card ι : ℕ∞) * Ring.ord A c₀) ≠ ⊤ := WithTop.mul_ne_top hcard hord
  refine WithTop.add_left_cancel hne ?_
  calc (Fintype.card ι : ℕ∞) * Ring.ord A c₀ + cokerLength P
      = cokerLength (c₀ • P) := (cokerLength_smul hc₀ P).symm
    _ = cokerLength (c • P₀) := by rw [hkey]
    _ = (Fintype.card ι : ℕ∞) * Ring.ord A c + cokerLength P₀ := cokerLength_smul hc P₀
    _ = (Fintype.card ι : ℕ∞) * Ring.ord A c + Ring.ord A P₀.det := by rw [hlen]
    _ = Ring.ord A (c • P₀).det := (ord_det_smul hc P₀).symm
    _ = Ring.ord A (c₀ • P).det := by rw [hkey]
    _ = (Fintype.card ι : ℕ∞) * Ring.ord A c₀ + Ring.ord A P.det := ord_det_smul hc₀ P

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
/-- The determinant of an integral multiple of an invertible matrix over `K` is nonzero. -/
theorem det_ne_zero_of_map_eq_smul {Ψ : Matrix ι ι K} (hΨ : Ψ.det ≠ 0) {c : A}
    {P : Matrix ι ι A} (hc : c ≠ 0) (hP : P.map (algebraMap A K) = algebraMap A K c • Ψ) :
    P.det ≠ 0 := by
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hc' : algebraMap A K c ≠ 0 := fun h => hc (hinj (h.trans (map_zero _).symm))
  intro h
  have h0 : (P.map (algebraMap A K)).det = 0 := by rw [det_map, h, map_zero]
  rw [hP, Matrix.det_smul] at h0
  exact mul_ne_zero (pow_ne_zero _ hc') hΨ h0

/-- **The predicate is stable under products.** -/
theorem cokerOrdProp_mul {Ψ₁ Ψ₂ : Matrix ι ι K} (h1 : Ψ₁.det ≠ 0)
    (H1 : CokerOrdProp A Ψ₁) (H2 : CokerOrdProp A Ψ₂) : CokerOrdProp A (Ψ₁ * Ψ₂) := by
  obtain ⟨c₁, P₁, hc₁, hP₁⟩ := exists_integral_scaling (A := A) Ψ₁
  obtain ⟨c₂, P₂, hc₂, hP₂⟩ := exists_integral_scaling (A := A) Ψ₂
  have hd₁ : P₁.det ≠ 0 := det_ne_zero_of_map_eq_smul h1 hc₁ hP₁
  refine cokerOrdProp_of_witness (c₀ := c₁ * c₂) (P₀ := P₁ * P₂) (mul_ne_zero hc₁ hc₂) ?_ ?_
  · rw [Matrix.map_mul, hP₁, hP₂, map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  · rw [cokerLength_mul (mulVecLin_injective_of_det_ne_zero hd₁), H1 c₁ P₁ hc₁ hP₁,
      H2 c₂ P₂ hc₂ hP₂, ← Ring.ord_mul' A (mem_nonZeroDivisors_iff_ne_zero.2 hd₁),
      Matrix.det_mul]

/-- **The predicate holds for invertible diagonal matrices**: clearing a common denominator `b`
turns `diagonal D` into the integral diagonal matrix `diagonal d`, for which both sides equal
`∑ i, Ring.ord A (d i)` (`cokerLength_diagonal`, `ord_prod`). -/
theorem cokerOrdProp_diagonal (D : ι → K) (hD : (Matrix.diagonal D).det ≠ 0) :
    CokerOrdProp A (Matrix.diagonal D) := by
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (M := nonZeroDivisors A)
    (S := K) D
  choose d hd using fun i => RingHom.mem_range.1 (hb i)
  have hb0 : (b : A) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hb0' : algebraMap A K (b : A) ≠ 0 := fun h => hb0 (hinj (h.trans (map_zero _).symm))
  have hDi : ∀ i, D i ≠ 0 := by
    intro i hi
    rw [Matrix.det_diagonal] at hD
    exact hD (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have hdi : ∀ i, d i ≠ 0 := by
    intro i hi
    have h := hd i
    rw [hi, map_zero, Algebra.smul_def] at h
    exact mul_ne_zero hb0' (hDi i) h.symm
  refine cokerOrdProp_of_witness (c₀ := (b : A)) (P₀ := Matrix.diagonal d) hb0 ?_ ?_
  · rw [Matrix.diagonal_map (map_zero (algebraMap A K)), ← Matrix.diagonal_smul]
    exact congrArg Matrix.diagonal (funext fun i => by simp [hd i, Algebra.smul_def])
  · rw [cokerLength_diagonal, Matrix.det_diagonal, ord_prod _ _ fun i _ => hdi i]

/-- **The predicate holds for transvections.** Writing the coefficient as `a / b` with `a b : A`,
`b • transvection i j (a/b) = diagonal d' * transvection i j a * diagonal d` over `A`
(`diagonal_mul_transvection_mul_diagonal`); the two diagonal factors contribute
`∑ k, (Ring.ord A (d' k) + Ring.ord A (d k)) = card ι * Ring.ord A b` to the cokernel length, the
transvection contributes `0`, and the determinant of the product is `b ^ card ι`. -/
theorem cokerOrdProp_transvection (t : Matrix.TransvectionStruct ι K) :
    CokerOrdProp A t.toMatrix := by
  obtain ⟨i, j, hij, γ⟩ := t
  rw [Matrix.TransvectionStruct.toMatrix_mk]
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  obtain ⟨b, hb⟩ := IsLocalization.exists_integer_multiple (M := nonZeroDivisors A) (S := K) γ
  obtain ⟨a, ha⟩ := RingHom.mem_range.1 hb
  have hb0 : (b : A) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  set d' : ι → A := fun k => if k = i then 1 else (b : A) with hd'
  set d : ι → A := fun k => if k = i then (b : A) else 1 with hd
  have hprod : ∀ k : ι, d' k * d k = (b : A) := by
    intro k
    simp only [hd', hd]
    split_ifs <;> ring
  have hne1 : ∀ k : ι, d' k ≠ 0 := by
    intro k
    simp only [hd']
    split_ifs
    · exact one_ne_zero
    · exact hb0
  have hne2 : ∀ k : ι, d k ≠ 0 := by
    intro k
    simp only [hd]
    split_ifs
    · exact hb0
    · exact one_ne_zero
  have hdet1 : (Matrix.diagonal d').det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hne1 k
  have hdetE : (Matrix.transvection i j a).det ≠ 0 := by
    rw [Matrix.det_transvection_of_ne _ _ hij]
    exact one_ne_zero
  have hE0 : cokerLength (Matrix.transvection i j a) = 0 := by
    refine cokerLength_eq_zero_of_isUnit_det ?_
    rw [Matrix.det_transvection_of_ne _ _ hij]
    exact isUnit_one
  refine cokerOrdProp_of_witness (c₀ := (b : A))
    (P₀ := Matrix.diagonal d' * (Matrix.transvection i j a * Matrix.diagonal d)) hb0 ?_ ?_
  · have hab : algebraMap A K a = algebraMap A K (b : A) * γ := by
      rw [ha, Algebra.smul_def]
    rw [← Matrix.mul_assoc, Matrix.map_mul, Matrix.map_mul, transvection_map,
      Matrix.diagonal_map (map_zero (algebraMap A K)),
      Matrix.diagonal_map (map_zero (algebraMap A K)), hab]
    have h1 : (fun k => algebraMap A K (d' k)) = fun k : ι => if k = i then (1 : K)
        else algebraMap A K (b : A) := by
      funext k
      simp only [hd']
      split_ifs <;> simp
    have h2 : (fun k => algebraMap A K (d k)) = fun k : ι =>
        if k = i then algebraMap A K (b : A) else (1 : K) := by
      funext k
      simp only [hd]
      split_ifs <;> simp
    rw [h1, h2]
    exact diagonal_mul_transvection_mul_diagonal hij _ γ
  · have hlen : cokerLength (Matrix.diagonal d' *
        (Matrix.transvection i j a * Matrix.diagonal d))
        = (Fintype.card ι : ℕ∞) * Ring.ord A (b : A) := by
      rw [cokerLength_mul (mulVecLin_injective_of_det_ne_zero hdet1),
        cokerLength_mul (mulVecLin_injective_of_det_ne_zero hdetE), hE0, zero_add,
        cokerLength_diagonal, cokerLength_diagonal, Finset.sum_add_distrib.symm]
      calc ∑ k : ι, (Ring.ord A (d' k) + Ring.ord A (d k))
          = ∑ _k : ι, Ring.ord A (b : A) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Ring.ord_mul' A (mem_nonZeroDivisors_iff_ne_zero.2 (hne1 k)), hprod k]
        _ = (Fintype.card ι : ℕ∞) * Ring.ord A (b : A) := by
            simp [Finset.card_univ, nsmul_eq_mul]
    have hdetP : (Matrix.diagonal d' * (Matrix.transvection i j a * Matrix.diagonal d)).det
        = (b : A) ^ Fintype.card ι := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transvection_of_ne _ _ hij,
        Matrix.det_diagonal, Matrix.det_diagonal, one_mul, ← Finset.prod_mul_distrib,
        Finset.prod_congr rfl fun k _ => hprod k, Finset.prod_const, Finset.card_univ]
    rw [hlen, hdetP, Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.2 hb0), nsmul_eq_mul]

end Fraction


section Main

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Fulton's Lemma A.2.6** (*Intersection Theory*, Appendix A.2) for matrices: over a Noetherian
domain `A` of Krull dimension `≤ 1`, the length of the cokernel of a square matrix `M` with nonzero
determinant equals the order of vanishing of that determinant,
`Module.length A ((ι → A) ⧸ range M.mulVecLin) = Ring.ord A M.det`.

The proof runs the Gaussian-elimination induction
`Matrix.diagonal_transvection_induction_of_det_ne_zero` over the fraction field, using
`cokerOrdProp_diagonal`, `cokerOrdProp_transvection` and `cokerOrdProp_mul`, and then specialises
the resulting predicate to the integral multiple `1 • M` of `M`. -/
theorem cokerLength_eq_ord_det {M : Matrix ι ι A} (hM : M.det ≠ 0) :
    cokerLength M = Ring.ord A M.det := by
  have hinj : Function.Injective (algebraMap A (FractionRing A)) :=
    IsFractionRing.injective A (FractionRing A)
  have hdet : (M.map (algebraMap A (FractionRing A))).det ≠ 0 := by
    rw [det_map]
    exact fun h => hM (hinj (h.trans (map_zero _).symm))
  have H : CokerOrdProp A (M.map (algebraMap A (FractionRing A))) :=
    Matrix.diagonal_transvection_induction_of_det_ne_zero _ _ hdet
      (fun D hD => cokerOrdProp_diagonal D hD) (fun t => cokerOrdProp_transvection t)
      (fun _ _ h1 _ H1 H2 => cokerOrdProp_mul h1 H1 H2)
  exact H 1 M one_ne_zero (by simp)

/-- **Fulton's Lemma A.2.6**, stated for an injective matrix: over a Noetherian domain `A` of
Krull dimension `≤ 1`, `Module.length A ((ι → A) ⧸ range M.mulVecLin) = Ring.ord A M.det` whenever
`M` acts injectively on `ι → A`. -/
theorem cokerLength_eq_ord_det_of_injective {M : Matrix ι ι A}
    (hM : Function.Injective M.mulVecLin) : cokerLength M = Ring.ord A M.det := by
  refine cokerLength_eq_ord_det fun h => ?_
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  exact hv0 (hM (by simpa using hv))

end Main

section FreeModule

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]

/-- **Fulton's Lemma A.2.6** for an endomorphism `φ` of a finite free module `M` over a Noetherian
domain `A` of Krull dimension `≤ 1`: `Module.length A (M ⧸ range φ) = Ring.ord A (det φ)`.
Obtained from `cokerLength_eq_ord_det` by transporting along `Basis.equivFun` for an arbitrary
basis, using `LinearMap.det_toMatrix`. -/
theorem length_quotient_range_eq_ord_det {φ : M →ₗ[A] M} (hφ : LinearMap.det φ ≠ 0) :
    Module.length A (M ⧸ LinearMap.range φ) = Ring.ord A (LinearMap.det φ) := by
  classical
  set b : Module.Basis (Module.Free.ChooseBasisIndex A M) A M := Module.Free.chooseBasis A M with hb
  set N : Matrix (Module.Free.ChooseBasisIndex A M) (Module.Free.ChooseBasisIndex A M) A :=
    LinearMap.toMatrix b b φ with hN
  have hNdet : N.det = LinearMap.det φ := LinearMap.det_toMatrix b φ
  have hcomp : (b.equivFun : M →ₗ[A] _) ∘ₗ φ = N.mulVecLin ∘ₗ (b.equivFun : M →ₗ[A] _) := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe,
      Module.Basis.equivFun_apply, hN]
    exact (LinearMap.toMatrix_mulVec_repr b b φ x).symm
  have hmap : Submodule.map (b.equivFun : M →ₗ[A] _) (LinearMap.range φ)
      = LinearMap.range N.mulVecLin := by
    rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp,
      LinearMap.range_eq_top.2 b.equivFun.surjective, Submodule.map_top]
  calc Module.length A (M ⧸ LinearMap.range φ)
      = Module.length A (_ ⧸ LinearMap.range N.mulVecLin) :=
        (Submodule.Quotient.equiv _ _ b.equivFun hmap).length_eq
    _ = Ring.ord A N.det := cokerLength_eq_ord_det (hNdet ▸ hφ)
    _ = Ring.ord A (LinearMap.det φ) := by rw [hNdet]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
/-- Over a domain, an injective endomorphism of a finite free module has nonzero determinant. -/
theorem det_ne_zero_of_injective {φ : M →ₗ[A] M} (hφ : Function.Injective φ) :
    LinearMap.det φ ≠ 0 := fun h =>
  LinearMap.det_eq_zero_iff_ker_ne_bot.1 h (LinearMap.ker_eq_bot.2 hφ)

/-- **Fulton's Lemma A.2.6** for an injective endomorphism of a finite free module. -/
theorem length_quotient_range_eq_ord_det_of_injective {φ : M →ₗ[A] M}
    (hφ : Function.Injective φ) :
    Module.length A (M ⧸ LinearMap.range φ) = Ring.ord A (LinearMap.det φ) :=
  length_quotient_range_eq_ord_det (det_ne_zero_of_injective hφ)

/-- **Fulton's Lemma A.2.6** in the shape stated in *Intersection Theory*, Appendix A.2: for an
injective `A`-linear map `φ : (Fin n → A) →ₗ[A] (Fin n → A)` over a Noetherian domain `A` of Krull
dimension `≤ 1`, the length of the cokernel of `φ` is the order of vanishing of `det φ`. -/
theorem length_quotient_range_eq_ord_det_pi {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] {n : ℕ} {φ : (Fin n → A) →ₗ[A] (Fin n → A)}
    (hφ : Function.Injective φ) :
    Module.length A ((Fin n → A) ⧸ LinearMap.range φ) = Ring.ord A (LinearMap.det φ) :=
  length_quotient_range_eq_ord_det_of_injective hφ

end FreeModule

section Norm

variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B]

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Free A B]
  [Module.Finite A B] in
/-- Multiplication by a non-zero-divisor of `B` is an injective `A`-linear endomorphism. -/
theorem injective_lmul {b : B} (hb : b ∈ nonZeroDivisors B) :
    Function.Injective (Algebra.lmul A B b) := by
  intro x y hxy
  simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] at hxy
  have h : (x - y) * b = 0 := by
    rw [sub_mul, mul_comm x b, mul_comm y b, hxy, sub_self]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hb).2 (x - y) h)

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Free A B]
  [Module.Finite A B] in
/-- The range of multiplication by `b : B`, as an `A`-submodule of `B`, is the principal ideal
generated by `b`. -/
theorem range_lmul (b : B) :
    LinearMap.range (Algebra.lmul A B b) = (Ideal.span {b} : Ideal B).restrictScalars A := by
  ext y
  simp only [LinearMap.mem_range, Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [← hx, mul_comm]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [mul_comm, hc]⟩

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
/-- The norm of a non-zero-divisor is nonzero. -/
theorem norm_ne_zero {b : B} (hb : b ∈ nonZeroDivisors B) : Algebra.norm A b ≠ 0 := by
  rw [Algebra.norm_apply]
  exact det_ne_zero_of_injective (injective_lmul hb)

/-- **The norm formula** (Fulton, *Intersection Theory*, Prop. 1.4, local form; Example A.3.1 in
rank `n`). Let `A` be a Noetherian domain of Krull dimension `≤ 1` and `B` a commutative
`A`-algebra that is finite and free as an `A`-module. For `b : B` a non-zero-divisor,

`Module.length A (B ⧸ b B) = Ring.ord A (Algebra.norm A b)`.

This is the statement that a finite morphism of curves pushes the divisor of `b` forward to the
divisor of its norm. It is `length_quotient_range_eq_ord_det_of_injective` applied to the
multiplication endomorphism `Algebra.lmul A B b`, whose determinant is `Algebra.norm A b` by
definition and whose range is `b B` (`range_lmul`). -/
theorem length_quotient_span_eq_ord_norm {b : B} (hb : b ∈ nonZeroDivisors B) :
    Module.length A (B ⧸ (Ideal.span {b} : Ideal B)) = Ring.ord A (Algebra.norm A b) := by
  rw [Algebra.norm_apply,
    ← length_quotient_range_eq_ord_det_of_injective (injective_lmul (A := A) hb), range_lmul]
  exact (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {b} : Ideal B)).length_eq.symm

/-- **The norm formula** for `B` a domain and `b ≠ 0`: `Module.length A (B ⧸ b B) =
Ring.ord A (Algebra.norm A b)`. -/
theorem length_quotient_span_eq_ord_norm_of_ne_zero [IsDomain B] {b : B} (hb : b ≠ 0) :
    Module.length A (B ⧸ (Ideal.span {b} : Ideal B)) = Ring.ord A (Algebra.norm A b) :=
  length_quotient_span_eq_ord_norm (mem_nonZeroDivisors_iff_ne_zero.2 hb)

end Norm

section NormFinsum

variable {A B : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B]

/-- **The norm formula in semilocal form.** Combining `length_quotient_span_eq_ord_norm` with the
semilocal length formula `OrderSemilocal.length_eq_finsum` (Fulton A.2.3, Part 2) gives, for `A` a
Noetherian local domain of Krull dimension `≤ 1`, `B` finite and free over `A` and `b : B` a
non-zero-divisor,

`∑ᶠ q : MaximalSpectrum B, [κ(q) : κ_A] · Module.length (B_q) ((B ⧸ bB)_q)
  = Ring.ord A (Algebra.norm A b)`,

i.e. the divisor of `b` on `Spec B` pushes forward to the divisor of `Algebra.norm A b`. -/
theorem finsum_summand_eq_ord_norm {b : B} (hb : b ∈ nonZeroDivisors B) :
    ∑ᶠ q : MaximalSpectrum B,
        OrderSemilocal.summand (A := A) (B ⧸ (Ideal.span {b} : Ideal B)) q
      = Ring.ord A (Algebra.norm A b) := by
  have hA : IsFiniteLength A (B ⧸ (Ideal.span {b} : Ideal B)) := by
    rw [← Module.length_ne_top_iff, length_quotient_span_eq_ord_norm hb]
    exact Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr (norm_ne_zero hb))
  obtain ⟨hNoeth, hArt⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hA
  have hB : IsFiniteLength B (B ⧸ (Ideal.span {b} : Ideal B)) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_of_tower A inferInstance, isArtinian_of_tower A inferInstance⟩
  rw [← length_quotient_span_eq_ord_norm (A := A) hb]
  exact (OrderSemilocal.length_eq_finsum (A := A) hB).symm

/-- The semilocal norm formula for `B` a domain and `b ≠ 0`. -/
theorem finsum_summand_eq_ord_norm_of_ne_zero [IsDomain B] {b : B} (hb : b ≠ 0) :
    ∑ᶠ q : MaximalSpectrum B,
        OrderSemilocal.summand (A := A) (B ⧸ (Ideal.span {b} : Ideal B)) q
      = Ring.ord A (Algebra.norm A b) :=
  finsum_summand_eq_ord_norm (mem_nonZeroDivisors_iff_ne_zero.2 hb)

end NormFinsum

end OrderDeterminant
