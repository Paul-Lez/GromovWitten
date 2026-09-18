/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.NormalConeProductInj2
import GromovWitten.AlgebraicGeometry.Cones.NormalConeProductInj

/-!
# The product formula for the affine normal cone over a field

Let `k` be a **field**, let `R`, `R'` be `k`-algebras with ideals `I ⊆ R`, `I' ⊆ R'`, and let
`J = productIdeal k R R' I I' = I ⊗ R' + R ⊗ I'` be the ideal of `U × U'` in `M × M'`.
`Cones/NormalConeProduct.lean` constructs the comparison map

`grTensorToGr : gr_I(R) ⊗[k] gr_{I'}(R') →ₐ[k] gr_J(R ⊗[k] R')`

and proves it surjective; its injectivity was left as an explicit hypothesis of `grTensorEquiv`
and of `ringKrullDim_associatedGradedRing_productIdeal`.  This file proves that injectivity
**unconditionally over a field** (`grTensorToGr_injective`) and restates the two consequences
without hypotheses (`grTensorEquivOfField`,
`ringKrullDim_associatedGradedRing_productIdeal_of_field`).

## The linear algebra input

Over a field, the kernel of a tensor product of two linear maps is what it should be:

`ker (f ⊗ g) ≤ (ker f) ⊗' ⊤ ⊔ ⊤ ⊗' (ker g)`   (`GromovWitten.Algebra.ker_tensorMap_le`),

proved by choosing an idempotent `e` with range `ker f` (`exists_isIdempotentElem_range_eq`) and
splitting `x = (e ⊗ 1) x + y`: the element `z = (1 ⊗ g) y` lies both in `ker (f ⊗ 1) = ker f ⊗' ⊤`
(`ker_rTensor_eq`) and in `range (1 - e) ⊗' ⊤`, and these meet in `⊥` by `inf_tensorSub_top`, so
`y ∈ ker (1 ⊗ g) = ⊤ ⊗' ker g` (`ker_lTensor_eq`).  The consequence actually used is
`ker_tensorMap_le_ker_tensorMap`: if `u` kills `ker f` and `v` kills `ker g`, then `u ⊗ v` kills
`ker (f ⊗ g)`.

## The geometric input

`gr_I(R)` carries the degree projections `AffineNormalCone.grProj` of
`Cones/AssociatedGradedGrading.lean`.  The degree-`n` part is described by the monomial map
`grMonomial k R I n : I^n →ₗ[k] gr_I(R)`, `u ↦ [u X^n]`, which is onto the image of `grProj n`
(`range_grProj_le_range_grMonomial`) and vanishes exactly on `I^(n+1)`
(`grMonomial_eq_zero_iff`).  On the tensor product, the bidegree projections
`biProj a b = grProj a ⊗ grProj b` decompose every element into finitely many bidegree pieces
(`exists_sum_biProj`), each of which is a combination of bidegree monomials
(`biProj_mem_range_biMonomial`), and `grTensorToGr` sends a bidegree-`(a,b)` monomial with
coefficient `T ∈ I^a ⊗ I'^b` to the degree-`(a+b)` monomial with coefficient `T ∈ J^(a+b)`
(`grTensorToGr_biMonomial`).

Bidegrees inside a fixed total degree `n = a + b` are separated by the functional
`grQuotCoeff a b : gr_J(R ⊗ R') →ₗ[k] (R ⧸ I^(a+1)) ⊗[k] (R' ⧸ I'^(b+1))`, the degree-`n`
coefficient read modulo `I^(a+1)` and `I'^(b+1)`.  It is well defined because `J^(n+1)` is killed
by that reduction (`productIdeal_pow_le_ker`, which uses `productIdeal_pow_eq` of
`Cones/NormalConeProductInj.lean`: every summand `I^c · I'^d` of `J^(n+1)` has `c > a` or
`d > b`), and it kills all bidegrees other than `(a,b)` for the same reason.  Applying it to the
bidegree decomposition of an element of the kernel leaves a single term, whence the coefficient
`T` of the bidegree-`(a,b)` piece lies in the kernel of
`I^a ⊗ I'^b → (R ⧸ I^(a+1)) ⊗ (R' ⧸ I'^(b+1))`; by `ker_tensorMap_le_ker_tensorMap` it is
therefore killed by `grMonomial a ⊗ grMonomial b`, i.e. that piece vanishes.  Since all bidegree
pieces vanish, so does the element.

## Main results

* `GromovWitten.Algebra.ker_tensorMap_le`, `ker_tensorMap`, `ker_tensorMap_le_ker_tensorMap`:
  the kernel of a tensor product of linear maps over a field.
* `AffineNormalCone.grMonomial`, `grMonomial_eq_zero_iff`, `ker_grMonomial`, `grCoeff`:
  homogeneous elements of `gr_I(R)`, the identification of the degree-`n` part with
  `I^n / I^(n+1)`, and the degree-`n` coefficient functional.
* `AffineNormalConeProduct.grTensorToGr_injective`: the comparison map is injective.
* `AffineNormalConeProduct.grTensorEquivOfField`: `gr_J(R ⊗ R') ≃ₐ[k] gr_I(R) ⊗ gr_{I'}(R')`.
* `AffineNormalConeProduct.ringKrullDim_associatedGradedRing_productIdeal_of_field`: the
  resulting equality of Krull dimensions.

Everything in this file is unconditional; `k` is a field throughout (the linear algebra input is
false over a general base ring).  Not done here: the corresponding statement for normal
*sheaves*, `N_{U×U'/M×M'} ≅ N_{U/M} × N_{U'/M'}`, which needs the degree-one case
`J/J² ≅ (I/I²) ⊗ (R'/I') ⊕ (R/I) ⊗ (I'/I'²)` together with base change for symmetric algebras on
top of `NormalSheafPicard.symProdEquiv`.
-/

open scoped TensorProduct

namespace GromovWitten.Algebra

universe u v

variable {k : Type u} [Field k] {M M' N N' P Q : Type v} [AddCommGroup M] [Module k M]
  [AddCommGroup M'] [Module k M'] [AddCommGroup N] [Module k N] [AddCommGroup N'] [Module k N']
  [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]

/-! ### The kernel of a tensor product of linear maps -/

/-- The tensor product of the zero subspace with anything is zero. -/
theorem tensorSub_bot_left (B : Submodule k N) : tensorSub (⊥ : Submodule k M) B = ⊥ := by
  rw [tensorSub, LinearMap.range_eq_bot]
  refine TensorProduct.ext' fun u v ↦ ?_
  have hu : (u : M) = 0 := (Submodule.mem_bot k).mp u.2
  simp [hu]

/-- The ranges of an idempotent endomorphism and of its complementary idempotent meet in zero. -/
theorem range_inf_range_one_sub {e : M →ₗ[k] M} (he : IsIdempotentElem e) :
    LinearMap.range e ⊓ LinearMap.range (LinearMap.id - e) = ⊥ := by
  have he' : e ∘ₗ e = e := he
  rw [eq_bot_iff]
  rintro w ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have h1 : e w = w := by
    rw [← ha, ← LinearMap.comp_apply, he']
  have h2 : e w = 0 := by
    rw [← hb]
    have : (LinearMap.id - e : M →ₗ[k] M) b = b - e b := rfl
    rw [this, map_sub, ← LinearMap.comp_apply, he', sub_self]
  rw [Submodule.mem_bot, ← h1, h2]

/-- A tensor product of linear maps kills `(ker f) ⊗ ⊤`. -/
theorem tensorSub_ker_left_le_ker (u : M →ₗ[k] P) (v : N →ₗ[k] Q) :
    tensorSub (LinearMap.ker u) (⊤ : Submodule k N) ≤
      LinearMap.ker (TensorProduct.map u v) := by
  rintro x ⟨t, rfl⟩
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  have h : u ∘ₗ (LinearMap.ker u).subtype = 0 := by
    refine LinearMap.ext fun w ↦ ?_
    exact w.2
  have hz : TensorProduct.map (u ∘ₗ (LinearMap.ker u).subtype)
      (v ∘ₗ (⊤ : Submodule k N).subtype) = 0 := by
    rw [h]
    exact TensorProduct.ext' fun _ _ ↦ by simp
  simpa using LinearMap.congr_fun hz t

/-- A tensor product of linear maps kills `⊤ ⊗ (ker g)`. -/
theorem tensorSub_ker_right_le_ker (u : M →ₗ[k] P) (v : N →ₗ[k] Q) :
    tensorSub (⊤ : Submodule k M) (LinearMap.ker v) ≤
      LinearMap.ker (TensorProduct.map u v) := by
  rintro x ⟨t, rfl⟩
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  have h : v ∘ₗ (LinearMap.ker v).subtype = 0 := by
    refine LinearMap.ext fun w ↦ ?_
    exact w.2
  have hz : TensorProduct.map (u ∘ₗ (⊤ : Submodule k M).subtype)
      (v ∘ₗ (LinearMap.ker v).subtype) = 0 := by
    rw [h]
    exact TensorProduct.ext' fun _ _ ↦ by simp
  simpa using LinearMap.congr_fun hz t

/-- **The kernel of a tensor product of two linear maps over a field.**  It is contained in
`(ker f) ⊗ N + M ⊗ (ker g)` (and clearly contains it, see `tensorSub_ker_left_le_ker`).  The
proof splits off `ker f` by an idempotent `e` with range `ker f`: the complementary part `y` of
`x` satisfies `(1 ⊗ g) y ∈ (ker f ⊗ ⊤) ⊓ (range (1 - e) ⊗ ⊤) = 0`, hence lies in
`ker (1 ⊗ g) = ⊤ ⊗ ker g`. -/
theorem ker_tensorMap_le (f : M →ₗ[k] M') (g : N →ₗ[k] N') :
    LinearMap.ker (TensorProduct.map f g) ≤
      tensorSub (LinearMap.ker f) (⊤ : Submodule k N) ⊔
        tensorSub (⊤ : Submodule k M) (LinearMap.ker g) := by
  obtain ⟨e, he, hek⟩ := exists_isIdempotentElem_range_eq (LinearMap.ker f)
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hfe : ∀ m : M, f (e m) = 0 := fun m ↦ hek.le (LinearMap.mem_range_self e m)
  -- the complementary idempotent
  have hsplit : x = LinearMap.rTensor N e x + LinearMap.rTensor N (LinearMap.id - e) x := by
    rw [← LinearMap.add_apply, ← LinearMap.rTensor_add]
    simp
  -- the first summand is visibly in `(ker f) ⊗ ⊤`
  have h1 : LinearMap.rTensor N e x ∈ tensorSub (LinearMap.ker f) (⊤ : Submodule k N) := by
    have hr : LinearMap.range (LinearMap.rTensor N e)
        = tensorSub (LinearMap.range e) (⊤ : Submodule k N) :=
      range_tensorMap' rfl (LinearMap.range_id (M := N))
    rw [← hek, ← hr]
    exact LinearMap.mem_range_self _ _
  -- the second summand lies in `⊤ ⊗ (ker g)`
  set y := LinearMap.rTensor N (LinearMap.id - e) x with hy
  have hmapy : TensorProduct.map f g y = 0 := by
    have hcomp : TensorProduct.map f g ∘ₗ LinearMap.rTensor N (LinearMap.id - e)
        = TensorProduct.map f g := by
      refine TensorProduct.ext' fun m n ↦ ?_
      have hm : (LinearMap.id - e : M →ₗ[k] M) m = m - e m := rfl
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, hm, map_sub, hfe,
        TensorProduct.map_tmul, sub_zero]
    rw [hy, ← LinearMap.comp_apply, hcomp]
    exact hx
  have h2 : y ∈ tensorSub (⊤ : Submodule k M) (LinearMap.ker g) := by
    set z := LinearMap.lTensor M g y with hz
    have hz1 : z ∈ tensorSub (LinearMap.ker f) (⊤ : Submodule k N') := by
      rw [← ker_rTensor_eq f, LinearMap.mem_ker, hz, ← LinearMap.comp_apply]
      have hrl : LinearMap.rTensor N' f ∘ₗ LinearMap.lTensor M g = TensorProduct.map f g :=
        TensorProduct.ext' fun _ _ ↦ rfl
      rw [hrl]
      exact hmapy
    have hz2 : z ∈ tensorSub (LinearMap.range (LinearMap.id - e)) (⊤ : Submodule k N') := by
      have hcomm : LinearMap.lTensor M g ∘ₗ LinearMap.rTensor N (LinearMap.id - e)
          = LinearMap.rTensor N' (LinearMap.id - e) ∘ₗ LinearMap.lTensor M g :=
        TensorProduct.ext' fun _ _ ↦ rfl
      have hzz : z = LinearMap.rTensor N' (LinearMap.id - e) (LinearMap.lTensor M g x) := by
        rw [hz, hy, ← LinearMap.comp_apply, hcomm, LinearMap.comp_apply]
      have hr : LinearMap.range (LinearMap.rTensor N' (LinearMap.id - e))
          = tensorSub (LinearMap.range (LinearMap.id - e)) (⊤ : Submodule k N') :=
        range_tensorMap' rfl (LinearMap.range_id (M := N'))
      rw [hzz, ← hr]
      exact LinearMap.mem_range_self _ _
    have hzero : z = 0 := by
      have hmem : z ∈ tensorSub (LinearMap.ker f) (⊤ : Submodule k N') ⊓
          tensorSub (LinearMap.range (LinearMap.id - e)) (⊤ : Submodule k N') :=
        Submodule.mem_inf.mpr ⟨hz1, hz2⟩
      rw [inf_tensorSub_top, ← hek, range_inf_range_one_sub he, tensorSub_bot_left] at hmem
      exact (Submodule.mem_bot k).mp hmem
    rw [← ker_lTensor_eq g, LinearMap.mem_ker]
    exact hzero
  rw [hsplit]
  exact Submodule.add_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)

/-- **The kernel of a tensor product of two linear maps over a field**, as an equality. -/
theorem ker_tensorMap (f : M →ₗ[k] M') (g : N →ₗ[k] N') :
    LinearMap.ker (TensorProduct.map f g) =
      tensorSub (LinearMap.ker f) (⊤ : Submodule k N) ⊔
        tensorSub (⊤ : Submodule k M) (LinearMap.ker g) :=
  le_antisymm (ker_tensorMap_le f g)
    (sup_le (tensorSub_ker_left_le_ker f g) (tensorSub_ker_right_le_ker f g))

/-- **Comparison of kernels of tensor products.**  Over a field, if `u` kills the kernel of `f`
and `v` kills the kernel of `g`, then `u ⊗ v` kills the kernel of `f ⊗ g`. -/
theorem ker_tensorMap_le_ker_tensorMap (f : M →ₗ[k] M') (g : N →ₗ[k] N') (u : M →ₗ[k] P)
    (v : N →ₗ[k] Q) (hu : LinearMap.ker f ≤ LinearMap.ker u)
    (hv : LinearMap.ker g ≤ LinearMap.ker v) :
    LinearMap.ker (TensorProduct.map f g) ≤ LinearMap.ker (TensorProduct.map u v) :=
  le_trans (ker_tensorMap_le f g)
    (sup_le
      (le_trans (tensorSub_mono hu le_rfl) (tensorSub_ker_left_le_ker u v))
      (le_trans (tensorSub_mono le_rfl hv) (tensorSub_ker_right_le_ker u v)))

end GromovWitten.Algebra

namespace GromovWitten.AlgebraicGeometry

namespace AffineNormalCone

universe u

variable (k : Type u) [CommRing k] (R : Type u) [CommRing R] [Algebra k R] (I : Ideal R)

/-! ### Homogeneous elements of the associated graded ring -/

/-- The degree-`n` monomial `u ↦ u X^n`, as a `k`-linear map from `I^n` to the Rees algebra. -/
noncomputable def grMonomialRees (n : ℕ) :
    Submodule.restrictScalars k (I ^ n) →ₗ[k] reesAlgebra I where
  toFun u := ⟨Polynomial.monomial n (u : R), reesAlgebra.monomial_mem.mpr u.2⟩
  map_add' u v := by
    apply Subtype.ext
    simp
  map_smul' c u := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_grMonomialRees (n : ℕ) (u : Submodule.restrictScalars k (I ^ n)) :
    (grMonomialRees k R I n u : Polynomial R) = Polynomial.monomial n (u : R) := rfl

/-- The degree-`n` homogeneous elements of `gr_I(R)`: the class of `u X^n` for `u ∈ I^n`. -/
noncomputable def grMonomial (n : ℕ) :
    Submodule.restrictScalars k (I ^ n) →ₗ[k] associatedGradedRing R I :=
  (Ideal.Quotient.mkₐ k (Ideal.map (algebraMap R (reesAlgebra I)) I)).toLinearMap.comp
    (grMonomialRees k R I n)

theorem grMonomial_apply (n : ℕ) (u : Submodule.restrictScalars k (I ^ n)) :
    grMonomial k R I n u =
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
        (grMonomialRees k R I n u) := rfl

/-- **A homogeneous monomial vanishes exactly when its coefficient is one power deeper.**  This
is the concrete description of the degree-`n` part of `gr_I(R)` as `I^n / I^(n+1)`. -/
theorem grMonomial_eq_zero_iff (n : ℕ) (u : Submodule.restrictScalars k (I ^ n)) :
    grMonomial k R I n u = 0 ↔ (u : R) ∈ I ^ (n + 1) := by
  rw [grMonomial_apply, Ideal.Quotient.eq_zero_iff_mem, mem_reesIdeal_iff]
  constructor
  · intro h
    have hn := h n
    rwa [coe_grMonomialRees, Polynomial.coeff_monomial, if_pos rfl] at hn
  · intro h m
    rw [coe_grMonomialRees, Polynomial.coeff_monomial]
    split_ifs with hm
    · subst hm
      exact h
    · exact Ideal.zero_mem _

/-- Every homogeneous part of an element of `gr_I(R)` is a monomial class. -/
theorem range_grProj_le_range_grMonomial (n : ℕ) :
    LinearMap.range (LinearMap.restrictScalars k (grProj R I n)) ≤
      LinearMap.range (grMonomial k R I n) := by
  rintro x ⟨y, rfl⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨⟨(p : Polynomial R).coeff n, (mem_reesAlgebra_iff I _).mp p.2 n⟩, rfl⟩

/-- The homogeneous decomposition of an element of `gr_I(R)`, in the form used for tensor
products: all sufficiently long partial sums of the homogeneous parts recover the element. -/
theorem exists_sum_grProj_ge (x : associatedGradedRing R I) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M → ∑ n ∈ Finset.range M, grProj R I n x = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨(p : Polynomial R).natDegree + 1, fun M hM ↦ ?_⟩
  rw [Finset.sum_congr rfl fun n _ ↦ grProj_mk R I n p, ← map_sum,
    sum_reesProj R I p (by omega)]

/-- The reduction `I^n → R ⧸ I^(n+1)`. -/
noncomputable def idealQuotMap (n : ℕ) :
    Submodule.restrictScalars k (I ^ n) →ₗ[k] R ⧸ I ^ (n + 1) :=
  (Ideal.Quotient.mkₐ k (I ^ (n + 1))).toLinearMap.comp
    (Submodule.restrictScalars k (I ^ n)).subtype

/-- **The degree-`n` part of `gr_I(R)` is `I^n / I^(n+1)`**: the monomial map and the reduction
`I^n → R ⧸ I^(n+1)` have the same kernel. -/
theorem ker_grMonomial (n : ℕ) :
    LinearMap.ker (grMonomial k R I n) = LinearMap.ker (idealQuotMap k R I n) := by
  refine le_antisymm (fun u hu ↦ ?_) (fun u hu ↦ ?_)
  · rw [LinearMap.mem_ker] at hu ⊢
    rw [grMonomial_eq_zero_iff] at hu
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hu
  · rw [LinearMap.mem_ker] at hu ⊢
    rw [grMonomial_eq_zero_iff]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hu

/-- The degree-`n` monomial map kills the kernel of the reduction `I^n → R ⧸ I^(n+1)`. -/
theorem ker_idealQuotMap_le (n : ℕ) :
    LinearMap.ker (idealQuotMap k R I n) ≤ LinearMap.ker (grMonomial k R I n) :=
  le_of_eq (ker_grMonomial k R I n).symm

/-! ### The degree-`n` coefficient functional -/

/-- The degree-`n` coefficient of a Rees element, as a `k`-linear map. -/
noncomputable def reesCoeff (n : ℕ) : reesAlgebra I →ₗ[k] R :=
  LinearMap.restrictScalars k
    ((Polynomial.lcoeff R n).comp (Subalgebra.val (reesAlgebra I)).toLinearMap)

/-- **The degree-`n` coefficient functional on `gr_I(R)`.**  Any `k`-linear map `ψ` out of `R`
which kills `I^(n+1)` descends to the associated graded ring through the degree-`n` coefficient:
this is well defined precisely because the defining ideal of `gr_I(R)` is homogeneous with
degree-`m` part `I^(m+1) X^m` (`mem_reesIdeal_iff`). -/
noncomputable def grCoeff (n : ℕ) {W : Type u} [AddCommGroup W] [Module k W] (ψ : R →ₗ[k] W)
    (hψ : ∀ c ∈ I ^ (n + 1), ψ c = 0) : associatedGradedRing R I →ₗ[k] W :=
  Submodule.liftQ ((Ideal.map (algebraMap R (reesAlgebra I)) I).restrictScalars k)
    (ψ.comp (reesCoeff k R I n))
    (fun q hq ↦ by
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact hψ _ ((mem_reesIdeal_iff R I q).mp hq n))

@[simp]
theorem grCoeff_mk (n : ℕ) {W : Type u} [AddCommGroup W] [Module k W] (ψ : R →ₗ[k] W)
    (hψ : ∀ c ∈ I ^ (n + 1), ψ c = 0) (p : reesAlgebra I) :
    grCoeff k R I n ψ hψ (Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I) p) =
      ψ ((p : Polynomial R).coeff n) := rfl

/-- The coefficient functional on a monomial class. -/
theorem grCoeff_grMonomial (n m : ℕ) {W : Type u} [AddCommGroup W] [Module k W] (ψ : R →ₗ[k] W)
    (hψ : ∀ c ∈ I ^ (n + 1), ψ c = 0) (u : Submodule.restrictScalars k (I ^ m)) :
    grCoeff k R I n ψ hψ (grMonomial k R I m u) = if m = n then ψ (u : R) else 0 := by
  rw [grMonomial_apply, grCoeff_mk, coe_grMonomialRees, Polynomial.coeff_monomial]
  split_ifs with h
  · subst h
    rfl
  · exact map_zero ψ

end AffineNormalCone

namespace AffineNormalConeProduct

universe u

variable (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R]
  (R' : Type u) [CommRing R'] [Algebra k R'] (I : Ideal R) (I' : Ideal R')

open AffineNormalCone GromovWitten.Algebra

/-! ### Bidegree decomposition of the source -/

/-- The bidegree-`(a,b)` projection of `gr_I(R) ⊗[k] gr_{I'}(R')`. -/
noncomputable def biProj (a b : ℕ) :
    associatedGradedRing R I ⊗[k] associatedGradedRing R' I' →ₗ[k]
      associatedGradedRing R I ⊗[k] associatedGradedRing R' I' :=
  TensorProduct.map (LinearMap.restrictScalars k (grProj R I a))
    (LinearMap.restrictScalars k (grProj R' I' b))

/-- The bidegree-`(a,b)` monomials of `gr_I(R) ⊗[k] gr_{I'}(R')`. -/
noncomputable def biMonomial (a b : ℕ) :
    Submodule.restrictScalars k (I ^ a) ⊗[k] Submodule.restrictScalars k (I' ^ b) →ₗ[k]
      associatedGradedRing R I ⊗[k] associatedGradedRing R' I' :=
  TensorProduct.map (grMonomial k R I a) (grMonomial k R' I' b)

/-- Each bidegree component of an element of `gr_I(R) ⊗[k] gr_{I'}(R')` is a combination of
bidegree-`(a,b)` monomials. -/
theorem biProj_mem_range_biMonomial (a b : ℕ)
    (x : associatedGradedRing R I ⊗[k] associatedGradedRing R' I') :
    biProj k R R' I I' a b x ∈ LinearMap.range (biMonomial k R R' I I' a b) := by
  have h1 : LinearMap.range (biProj k R R' I I' a b) =
      tensorSub (LinearMap.range (LinearMap.restrictScalars k (grProj R I a)))
        (LinearMap.range (LinearMap.restrictScalars k (grProj R' I' b))) :=
    range_tensorMap' rfl rfl
  have h2 : LinearMap.range (biMonomial k R R' I I' a b) =
      tensorSub (LinearMap.range (grMonomial k R I a)) (LinearMap.range (grMonomial k R' I' b)) :=
    range_tensorMap' rfl rfl
  rw [h2]
  refine tensorSub_mono (range_grProj_le_range_grMonomial k R I a)
    (range_grProj_le_range_grMonomial k R' I' b) ?_
  rw [← h1]
  exact LinearMap.mem_range_self _ _

/-- **The bidegree decomposition.**  Every element of `gr_I(R) ⊗[k] gr_{I'}(R')` is the sum of
its bidegree components, all sufficiently large square partial sums agreeing with it. -/
theorem exists_sum_biProj (x : associatedGradedRing R I ⊗[k] associatedGradedRing R' I') :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M, biProj k R R' I I' a b x = x := by
  induction x using TensorProduct.induction_on with
  | zero =>
    refine ⟨0, fun M _ ↦ ?_⟩
    refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
    exact LinearMap.map_zero (biProj k R R' I I' a b)
  | tmul u v =>
    obtain ⟨N₁, h₁⟩ := exists_sum_grProj_ge R I u
    obtain ⟨N₂, h₂⟩ := exists_sum_grProj_ge R' I' v
    refine ⟨max N₁ N₂, fun M hM ↦ ?_⟩
    have e1 := h₁ M (le_trans (le_max_left _ _) hM)
    have e2 := h₂ M (le_trans (le_max_right _ _) hM)
    have hb : ∀ a b : ℕ, biProj k R R' I I' a b (u ⊗ₜ[k] v)
        = (grProj R I a u) ⊗ₜ[k] (grProj R' I' b v) := fun _ _ ↦ rfl
    calc ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M, biProj k R R' I I' a b (u ⊗ₜ[k] v)
        = ∑ a ∈ Finset.range M, (grProj R I a u) ⊗ₜ[k]
            (∑ b ∈ Finset.range M, grProj R' I' b v) := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [TensorProduct.tmul_sum]
          exact Finset.sum_congr rfl fun b _ ↦ hb a b
      _ = (∑ a ∈ Finset.range M, grProj R I a u) ⊗ₜ[k]
            (∑ b ∈ Finset.range M, grProj R' I' b v) := (TensorProduct.sum_tmul _ _ _).symm
      _ = u ⊗ₜ[k] v := by rw [e1, e2]
  | add x y hx hy =>
    obtain ⟨N₁, h₁⟩ := hx
    obtain ⟨N₂, h₂⟩ := hy
    refine ⟨max N₁ N₂, fun M hM ↦ ?_⟩
    have e1 := h₁ M (le_trans (le_max_left _ _) hM)
    have e2 := h₂ M (le_trans (le_max_right _ _) hM)
    have hstep : ∀ a : ℕ, ∑ b ∈ Finset.range M, biProj k R R' I I' a b (x + y)
        = (∑ b ∈ Finset.range M, biProj k R R' I I' a b x)
          + ∑ b ∈ Finset.range M, biProj k R R' I I' a b y := by
      intro a
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ ↦ LinearMap.map_add (biProj k R R' I I' a b) x y
    rw [Finset.sum_congr rfl fun a _ ↦ hstep a, Finset.sum_add_distrib, e1, e2]

/-! ### The image of a bidegree monomial -/

/-- The inclusion `I^a ⊗_k I'^b → R ⊗[k] R'`. -/
noncomputable def idealTensorIncl (a b : ℕ) :
    Submodule.restrictScalars k (I ^ a) ⊗[k] Submodule.restrictScalars k (I' ^ b) →ₗ[k]
      R ⊗[k] R' :=
  TensorProduct.map (Submodule.restrictScalars k (I ^ a)).subtype
    (Submodule.restrictScalars k (I' ^ b)).subtype

/-- Elementary tensors of `I^a` and `I'^b` are products of an element of the extended ideal of
`I^a` with one of the extended ideal of `I'^b`. -/
theorem tmul_eq_inl_mul_inr (x : R) (y : R') :
    x ⊗ₜ[k] y = inl k R R' x * inr k R R' y := by
  rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The image of `I^a ⊗ I'^b` lies in `J^(a+b)`. -/
theorem idealTensorIncl_mem (a b : ℕ)
    (t : Submodule.restrictScalars k (I ^ a) ⊗[k] Submodule.restrictScalars k (I' ^ b)) :
    idealTensorIncl k R R' I I' a b t ∈
      Submodule.restrictScalars k (productIdeal k R R' I I' ^ (a + b)) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [LinearMap.map_zero (idealTensorIncl k R R' I I' a b)]
    exact Submodule.zero_mem _
  | tmul u v =>
    have hmem : inl k R R' (u : R) * inr k R R' (v : R') ∈
        Ideal.map (inl k R R') (I ^ a) * Ideal.map (inr k R R') (I' ^ b) :=
      Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ u.2) (Ideal.mem_map_of_mem _ v.2)
    have : idealTensorIncl k R R' I I' a b (u ⊗ₜ[k] v) = (u : R) ⊗ₜ[k] (v : R') := rfl
    rw [this, tmul_eq_inl_mul_inr]
    exact le_productIdeal_pow k R R' I I' a b hmem
  | add s t hs ht =>
    rw [LinearMap.map_add (idealTensorIncl k R R' I I' a b) s t]
    exact Submodule.add_mem _ hs ht

/-- The inclusion `I^a ⊗_k I'^b → J^(a+b)`. -/
noncomputable def idealTensorInclJ (a b : ℕ) :
    Submodule.restrictScalars k (I ^ a) ⊗[k] Submodule.restrictScalars k (I' ^ b) →ₗ[k]
      Submodule.restrictScalars k (productIdeal k R R' I I' ^ (a + b)) :=
  LinearMap.codRestrict _ (idealTensorIncl k R R' I I' a b) (idealTensorIncl_mem k R R' I I' a b)

@[simp]
theorem coe_idealTensorInclJ (a b : ℕ)
    (t : Submodule.restrictScalars k (I ^ a) ⊗[k] Submodule.restrictScalars k (I' ^ b)) :
    (idealTensorInclJ k R R' I I' a b t : R ⊗[k] R') = idealTensorIncl k R R' I I' a b t := rfl

/-- **The comparison map on bidegree monomials.**  A bidegree-`(a,b)` monomial of
`gr_I(R) ⊗ gr_{I'}(R')` goes to the degree-`(a+b)` monomial of `gr_J(R ⊗[k] R')` attached to the
image of its coefficient in `J^(a+b)`. -/
theorem grTensorToGr_biMonomial (a b : ℕ)
    (t : Submodule.restrictScalars k (I ^ a) ⊗[k] Submodule.restrictScalars k (I' ^ b)) :
    grTensorToGr k R R' I I' (biMonomial k R R' I I' a b t) =
      grMonomial k (R ⊗[k] R') (productIdeal k R R' I I') (a + b)
        (idealTensorInclJ k R R' I I' a b t) := by
  have key : (grTensorToGr k R R' I I').toLinearMap.comp (biMonomial k R R' I I' a b)
      = (grMonomial k (R ⊗[k] R') (productIdeal k R R' I I') (a + b)).comp
          (idealTensorInclJ k R R' I I' a b) := by
    refine TensorProduct.ext' fun u v ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [biMonomial, TensorProduct.map_tmul, grTensorToGr_tmul, grMonomial_apply, grMonomial_apply,
      grMonomial_apply, grLeft_mk, grRight_mk, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subalgebra.coe_mul, coe_reesLeftAlg, coe_reesRightAlg, coe_grMonomialRees,
      coe_grMonomialRees, coe_grMonomialRees, Polynomial.map_monomial, Polynomial.map_monomial,
      Polynomial.monomial_mul_monomial, coe_idealTensorInclJ]
    have huv : idealTensorIncl k R R' I I' a b (u ⊗ₜ[k] v) = (u : R) ⊗ₜ[k] (v : R') := rfl
    rw [huv, tmul_eq_inl_mul_inr]
    rfl
  exact LinearMap.congr_fun key t

/-! ### The reduction maps used to separate bidegrees -/

/-- A finite sum of ideals is contained in an ideal as soon as each summand is. -/
theorem sum_ideal_le {S : Type u} [CommRing S] {f : ℕ → Ideal S} {K : Ideal S} :
    ∀ s : Finset ℕ, (∀ i ∈ s, f i ≤ K) → ∑ i ∈ s, f i ≤ K := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp
  | @insert i s hi ih =>
    intro h
    rw [Finset.sum_insert hi, Ideal.add_eq_sup]
    exact sup_le (h i (Finset.mem_insert_self i s))
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-- The reduction `R ⊗[k] R' → (R ⧸ I^(a+1)) ⊗[k] (R' ⧸ I'^(b+1))`. -/
noncomputable def quotTensorMap (a b : ℕ) :
    R ⊗[k] R' →ₐ[k] (R ⧸ I ^ (a + 1)) ⊗[k] (R' ⧸ I' ^ (b + 1)) :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (I ^ (a + 1)))
    (Ideal.Quotient.mkₐ k (I' ^ (b + 1)))

/-- The extended ideal of `I^c` is killed by the reduction as soon as `c > a`. -/
theorem map_inl_pow_le_ker (a b c : ℕ) (hc : a + 1 ≤ c) :
    Ideal.map (inl k R R') (I ^ c) ≤
      RingHom.ker (quotTensorMap k R R' I I' a b).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro u hu
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have h1 : (quotTensorMap k R R' I I' a b).toRingHom (inl k R R' u)
      = Ideal.Quotient.mk (I ^ (a + 1)) u ⊗ₜ[k] (1 : R' ⧸ I' ^ (b + 1)) := rfl
  rw [h1, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_le_pow_right hc hu),
    TensorProduct.zero_tmul]

/-- The extended ideal of `I'^d` is killed by the reduction as soon as `d > b`. -/
theorem map_inr_pow_le_ker (a b d : ℕ) (hd : b + 1 ≤ d) :
    Ideal.map (inr k R R') (I' ^ d) ≤
      RingHom.ker (quotTensorMap k R R' I I' a b).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro v hv
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have h1 : (quotTensorMap k R R' I I' a b).toRingHom (inr k R R' v)
      = (1 : R ⧸ I ^ (a + 1)) ⊗ₜ[k] Ideal.Quotient.mk (I' ^ (b + 1)) v := rfl
  rw [h1, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_le_pow_right hd hv),
    TensorProduct.tmul_zero]

/-- **The reduction kills `J^(a+b+1)`.**  Every summand `I^c · I'^d` of `J^(a+b+1)` has `c > a`
or `d > b`, hence is killed. -/
theorem productIdeal_pow_le_ker (a b : ℕ) :
    productIdeal k R R' I I' ^ (a + b + 1) ≤
      RingHom.ker (quotTensorMap k R R' I I' a b).toRingHom := by
  rw [productIdeal_pow_eq]
  refine sum_ideal_le _ fun c hc ↦ ?_
  rw [Finset.mem_range] at hc
  rcases Nat.lt_or_ge c (a + 1) with h | h
  · refine le_trans Ideal.mul_le_right (map_inr_pow_le_ker k R R' I I' a b _ ?_)
    omega
  · exact le_trans Ideal.mul_le_left (map_inl_pow_le_ker k R R' I I' a b c h)

/-- The reduction kills `J^(a+b+1)`, stated exactly in the form required by `grCoeff`. -/
theorem quotTensorMap_eq_zero_of_mem (a b : ℕ) :
    ∀ c ∈ productIdeal k R R' I I' ^ (a + b + 1),
      (quotTensorMap k R R' I I' a b).toLinearMap c = 0 := by
  intro c hc
  have h := productIdeal_pow_le_ker k R R' I I' a b hc
  rw [RingHom.mem_ker] at h
  exact h

/-- **The bidegree separating functional.**  The degree-`(a+b)` coefficient of `gr_J(R ⊗ R')`,
read modulo `I^(a+1)` and `I'^(b+1)`.  It is well defined because `J^(a+b+1)` is killed by the
reduction (`productIdeal_pow_le_ker`), and it kills every bidegree monomial except the ones of
bidegree `(a,b)`. -/
noncomputable def grQuotCoeff (a b : ℕ) :
    associatedGradedRing (R ⊗[k] R') (productIdeal k R R' I I') →ₗ[k]
      (R ⧸ I ^ (a + 1)) ⊗[k] (R' ⧸ I' ^ (b + 1)) :=
  grCoeff k (R ⊗[k] R') (productIdeal k R R' I I') (a + b)
    (quotTensorMap k R R' I I' a b).toLinearMap
    (quotTensorMap_eq_zero_of_mem k R R' I I' a b)

/-- The separating functional on the image of a bidegree monomial. -/
theorem grQuotCoeff_grTensorToGr_biMonomial (a b c d : ℕ)
    (t : Submodule.restrictScalars k (I ^ c) ⊗[k] Submodule.restrictScalars k (I' ^ d)) :
    grQuotCoeff k R R' I I' a b
        (grTensorToGr k R R' I I' (biMonomial k R R' I I' c d t)) =
      if c + d = a + b then
        quotTensorMap k R R' I I' a b (idealTensorIncl k R R' I I' c d t) else 0 := by
  rw [grTensorToGr_biMonomial, grQuotCoeff,
    grCoeff_grMonomial k (R ⊗[k] R') (productIdeal k R R' I I') (a + b) (c + d)]
  split_ifs with h
  · rfl
  · rfl

/-- The reduction kills the image of `I^c ⊗ I'^d` whenever `c > a` or `d > b`. -/
theorem quotTensorMap_idealTensorIncl_eq_zero (a b c d : ℕ) (h : a + 1 ≤ c ∨ b + 1 ≤ d)
    (t : Submodule.restrictScalars k (I ^ c) ⊗[k] Submodule.restrictScalars k (I' ^ d)) :
    quotTensorMap k R R' I I' a b (idealTensorIncl k R R' I I' c d t) = 0 := by
  have hkey : (quotTensorMap k R R' I I' a b).toLinearMap.comp
      (idealTensorIncl k R R' I I' c d) = 0 := by
    refine TensorProduct.ext' fun u v ↦ ?_
    have hval : ((quotTensorMap k R R' I I' a b).toLinearMap.comp
        (idealTensorIncl k R R' I I' c d)) (u ⊗ₜ[k] v)
        = Ideal.Quotient.mk (I ^ (a + 1)) (u : R) ⊗ₜ[k]
          Ideal.Quotient.mk (I' ^ (b + 1)) (v : R') := rfl
    rw [hval, LinearMap.zero_apply]
    rcases h with h | h
    · rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_le_pow_right h u.2),
        TensorProduct.zero_tmul]
    · rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_le_pow_right h v.2),
        TensorProduct.tmul_zero]
  simpa using LinearMap.congr_fun hkey t

/-! ### Injectivity of the comparison map -/

/-- **The comparison map for the affine normal cone of a product is injective over a field.**
An element `x` of the kernel has all its bidegree components zero: applying the separating
functional `grQuotCoeff a b` to the (finite) bidegree decomposition of `x` kills every component
except the one of bidegree `(a,b)`, so that the coefficient `T` of the latter lies in the kernel
of `I^a ⊗ I'^b → (R/I^(a+1)) ⊗ (R'/I'^(b+1))`; by `ker_tensorMap_le_ker_tensorMap` (which is
where the field hypothesis enters) `T` is then killed by the pair of monomial maps, that is, the
bidegree-`(a,b)` component of `x` itself vanishes. -/
theorem grTensorToGr_injective : Function.Injective (grTensorToGr k R R' I I') := by
  have hzero : ∀ x, grTensorToGr k R R' I I' x = 0 → x = 0 := by
    intro x hx
    have hrep : ∀ a b : ℕ, ∃ t, biMonomial k R R' I I' a b t = biProj k R R' I I' a b x :=
      fun a b ↦ biProj_mem_range_biMonomial k R R' I I' a b x
    choose t ht using hrep
    obtain ⟨N₀, hN₀⟩ := exists_sum_biProj k R R' I I' x
    have hvanish : ∀ a₀ b₀ : ℕ, biProj k R R' I I' a₀ b₀ x = 0 := by
      intro a₀ b₀
      obtain ⟨N, hNle, ha₀, hb₀⟩ : ∃ N : ℕ, N₀ ≤ N ∧ a₀ < N ∧ b₀ < N :=
        ⟨max N₀ (max (a₀ + 1) (b₀ + 1)), le_max_left _ _, by omega, by omega⟩
      have hbox := hN₀ N hNle
      -- the separating functional on a bidegree component
      have hterm : ∀ c d : ℕ, grQuotCoeff k R R' I I' a₀ b₀
          (grTensorToGr k R R' I I' (biProj k R R' I I' c d x)) =
            if c + d = a₀ + b₀ then
              quotTensorMap k R R' I I' a₀ b₀ (idealTensorIncl k R R' I I' c d (t c d))
            else 0 := by
        intro c d
        rw [← ht c d, grQuotCoeff_grTensorToGr_biMonomial]
      -- all bidegrees other than `(a₀, b₀)` are killed
      have hvan : ∀ c d : ℕ, c + d = a₀ + b₀ → c ≠ a₀ →
          quotTensorMap k R R' I I' a₀ b₀ (idealTensorIncl k R R' I I' c d (t c d)) = 0 := by
        intro c d hcd hc
        refine quotTensorMap_idealTensorIncl_eq_zero k R R' I I' a₀ b₀ c d ?_ (t c d)
        rcases Nat.lt_or_ge c a₀ with h | h
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
      -- apply the separating functional to the bidegree decomposition
      have hcomp : ∀ z, grQuotCoeff k R R' I I' a₀ b₀ (grTensorToGr k R R' I I' z)
          = ((grQuotCoeff k R R' I I' a₀ b₀).comp
              (grTensorToGr k R R' I I').toLinearMap) z := fun _ ↦ rfl
      have hsum : grQuotCoeff k R R' I I' a₀ b₀ (grTensorToGr k R R' I I' x)
          = ∑ c ∈ Finset.range N, ∑ d ∈ Finset.range N,
              grQuotCoeff k R R' I I' a₀ b₀
                (grTensorToGr k R R' I I' (biProj k R R' I I' c d x)) := by
        simp only [hcomp]
        conv_lhs => rw [← hbox]
        rw [map_sum]
        exact Finset.sum_congr rfl fun c _ ↦ map_sum _ _ _
      have hstart : ∑ c ∈ Finset.range N, ∑ d ∈ Finset.range N,
          (if c + d = a₀ + b₀ then
              quotTensorMap k R R' I I' a₀ b₀ (idealTensorIncl k R R' I I' c d (t c d))
            else 0) = 0 := by
        rw [← Finset.sum_congr rfl fun c (_ : c ∈ Finset.range N) ↦
          Finset.sum_congr rfl fun d (_ : d ∈ Finset.range N) ↦ hterm c d, ← hsum, hx,
          LinearMap.map_zero]
      -- the sum collapses to the single term of bidegree `(a₀, b₀)`
      have hcollapse : quotTensorMap k R R' I I' a₀ b₀
          (idealTensorIncl k R R' I I' a₀ b₀ (t a₀ b₀)) = 0 := by
        rw [← hstart, Finset.sum_eq_single_of_mem a₀ (Finset.mem_range.mpr ha₀)]
        · rw [Finset.sum_eq_single_of_mem b₀ (Finset.mem_range.mpr hb₀)]
          · rw [if_pos rfl]
          · intro d _ hd
            rw [if_neg (by omega)]
        · intro c _ hc
          refine Finset.sum_eq_zero fun d _ ↦ ?_
          split_ifs with hcd
          · exact hvan c d hcd hc
          · rfl
      -- conclude by the kernel comparison for tensor products
      have hfactor : (quotTensorMap k R R' I I' a₀ b₀).toLinearMap.comp
          (idealTensorIncl k R R' I I' a₀ b₀)
          = TensorProduct.map (idealQuotMap k R I a₀) (idealQuotMap k R' I' b₀) :=
        TensorProduct.ext' fun _ _ ↦ rfl
      have hker : t a₀ b₀ ∈
          LinearMap.ker (TensorProduct.map (idealQuotMap k R I a₀) (idealQuotMap k R' I' b₀)) := by
        rw [LinearMap.mem_ker, ← hfactor]
        exact hcollapse
      have hfin := GromovWitten.Algebra.ker_tensorMap_le_ker_tensorMap
        (idealQuotMap k R I a₀) (idealQuotMap k R' I' b₀) (grMonomial k R I a₀)
        (grMonomial k R' I' b₀) (ker_idealQuotMap_le k R I a₀) (ker_idealQuotMap_le k R' I' b₀)
        hker
      rw [← ht a₀ b₀]
      exact hfin
    rw [← hN₀ N₀ le_rfl]
    exact Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ hvanish a b
  exact LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hzero)

/-! ### The unconditional product formula -/

/-- **The product formula for the affine normal cone, over a field.**  Unconditionally,
`gr_J(R ⊗[k] R') ≃ₐ[k] gr_I(R) ⊗[k] gr_{I'}(R')`; on cones, `C_{U×U'/M×M'} ≅ C_{U/M} × C_{U'/M'}`.
This is `grTensorEquiv` with its injectivity hypothesis discharged by
`grTensorToGr_injective`. -/
noncomputable def grTensorEquivOfField :
    associatedGradedRing R I ⊗[k] associatedGradedRing R' I' ≃ₐ[k]
      associatedGradedRing (R ⊗[k] R') (productIdeal k R R' I I') :=
  grTensorEquiv k R R' I I' (grTensorToGr_injective k R R' I I')

@[simp]
theorem grTensorEquivOfField_apply (s : associatedGradedRing R I ⊗[k]
    associatedGradedRing R' I') :
    grTensorEquivOfField k R R' I I' s = grTensorToGr k R R' I I' s := rfl

-- The `CommRing` instance of `gr_I(R) ⊗[k] gr_{I'}(R')` is found only after unfolding the
-- Rees-algebra subalgebra structure, which needs a larger pending-synthesis depth here.
set_option maxSynthPendingDepth 5 in
/-- **The Krull dimension of the affine normal cone of a product, over a field.**  This is
`ringKrullDim_associatedGradedRing_productIdeal` with its injectivity hypothesis discharged. -/
theorem ringKrullDim_associatedGradedRing_productIdeal_of_field :
    ringKrullDim (associatedGradedRing (R ⊗[k] R') (productIdeal k R R' I I'))
      = ringKrullDim (associatedGradedRing R I ⊗[k] associatedGradedRing R' I') :=
  ringKrullDim_associatedGradedRing_productIdeal k R R' I I'
    (grTensorToGr_injective k R R' I I')

end AffineNormalConeProduct

end GromovWitten.AlgebraicGeometry
