/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.ConeTranslation
import GromovWitten.AlgebraicGeometry.Cones.Products

/-!
# The refinement lemma for local embeddings (polynomial model)

Behrend–Fantechi's intrinsic normal cone is glued from the local presentations
`[C_{U/M} / T_M|_U]` attached to closed embeddings of `U` into smooth schemes `M`.  The
compatibility which makes that gluing possible is the *refinement lemma*: for a refinement
`(U, M') → (U, M)` of local embeddings with `M' → M` smooth, the pair `C_{U/M} ⊆ N_{U/M}` is the
quotient of `C_{U/M'} ⊆ N_{U/M'}` by the relative tangent bundle `T_{M'/M}|_U`.

This file proves that statement in the polynomial model of `Cones/ConeTranslation.lean`, for the
basic refinement `M' = 𝔸^{σ⊕τ}_A → M = 𝔸^σ_A` (the projection) together with a graph embedding
`U = Spec (R/I) ↪ M'`, `x ↦ (x, g(x))`, whose ideal `graphIdeal A σ τ I g = I·R' + (y_t - g_t)`
is presented as the preimage of `I` under the retraction `graphProj g : x_i ↦ x_i, y_t ↦ g_t`.

## The coefficient filtration and the product formula

Over an arbitrary base ring `R` with an ideal `I`, the ideal of the zero-section embedding
`U ↪ Spec R[y_τ]` is `polyExt τ I = I·R[y_τ] + (y_τ)`, the polynomials whose constant term in
the `y`-variables lies in `I`.  Its powers are computed coefficientwise
(`pow_eq_coeffFiltration`): `f ∈ (I')^N` if and only if every coefficient `coeff m f` lies in
`I^(N - |m|)`.  This is the combinatorial heart of the file, and it gives

* `prodEquiv : gr_I(R)[z_τ] ≃+* gr_{I'}(R[y_τ])`, that is `C_{U/M'} = C_{U/M} × 𝔸^τ`
  (`prodMap_surjective` and `prodMap_injective`), the extra variables being the degree-one
  classes `zVar t` of the new coordinates;
* `nsProdMap : N_{U/M}[z_τ] → N_{U/M'}`, a surjection (`nsProdMap_surjective`) of normal-sheaf
  rings, and the commuting square `nsToGr_comp_nsProdMap` expressing that the closed immersion
  `C ⊆ N` is compatible with the two product decompositions.

## The polynomial model

`refinementEquiv` transports `prodEquiv` along `sumRingEquiv : A[x_σ,y_τ] ≃+* (A[x_σ])[y_τ]`,
giving `MvPolynomial τ (Gr I) ≃+* Gr (graphIdeal A σ τ I 0)`.  The change of variables
`map_shear_graphIdeal` reduces an arbitrary graph embedding to the zero section, and
`graphQuotientEquiv` identifies the two presentations `R'/I' ≃ₐ[A] R/I` of `U`.
`translatePoint_comp_refinementEquiv` proves that the isomorphism is equivariant on `B`-points:
the tangent translation of `T_{M'} = 𝔸^{σ⊕τ}` is the product of the translation action of `𝔸^σ`
on `C_{U/M}` and of the translation action of `𝔸^τ` on itself.

## The gate statement

`ConeGroupoid I B` is the action groupoid `[C_{U/M}/T_M|_U](B)` of the translation action
(`ConeTranslation.translatePoint`) on `B`-points, and `refinementFunctor` is the functor induced
by the projection `M' → M`.  `refinementQuotientEquivalence` proves that it is an equivalence of
groupoids for every test algebra `B`: the quotient presentation of the intrinsic normal cone is
unchanged by the refinement.

The analogous statement for the normal sheaves is only partially proved here: `nsProdMap` is
constructed, shown to be surjective and shown to be compatible with `nsToGr`, but its
injectivity (equivalently `N_{U/M'} = N_{U/M} × 𝔸^τ`) is not established, and neither is the
corresponding equivalence of quotient groupoids.
-/

namespace GromovWitten.AlgebraicGeometry

namespace ConeRefinement

universe u

noncomputable section

open AffineNormalCone MvPolynomial

variable {R : Type u} [CommRing R] (τ : Type u) (I : Ideal R)

/-! ### The ideal `I' = I·R[y] + (y)` and its coefficient filtration -/

/-- The ideal `I' = I·R[y_τ] + (y_t : t ∈ τ)` of `R[y_τ]`: the polynomials whose constant term
in the `y`-variables lies in `I`.  It is the ideal of the graph embedding `U ↪ M × 𝔸^τ`
of a refinement, after the change of variables which makes the graph the zero section. -/
def polyExt : Ideal (MvPolynomial τ R) :=
  Ideal.comap (MvPolynomial.constantCoeff : MvPolynomial τ R →+* R) I

variable {τ I}

theorem mem_polyExt_iff {f : MvPolynomial τ R} : f ∈ polyExt τ I ↔ constantCoeff f ∈ I :=
  Iff.rfl

theorem X_mem_polyExt (t : τ) : (X t : MvPolynomial τ R) ∈ polyExt τ I := by
  rw [mem_polyExt_iff, constantCoeff_X]
  exact Ideal.zero_mem _

theorem C_mem_polyExt {r : R} (hr : r ∈ I) : (C r : MvPolynomial τ R) ∈ polyExt τ I := by
  rwa [mem_polyExt_iff, constantCoeff_C]

theorem map_C_le_polyExt : Ideal.map (C : R →+* MvPolynomial τ R) I ≤ polyExt τ I := by
  rw [Ideal.map_le_iff_le_comap]
  exact fun r hr ↦ C_mem_polyExt hr

variable (τ I)

/-- The coefficientwise filtration of `R[y_τ]` attached to `I`: the `N`-th step consists of the
polynomials all of whose coefficients of multidegree `m` lie in `I ^ (N - |m|)`.  It is proved
below to be exactly the `N`-th power of `polyExt τ I`. -/
def coeffFiltration (N : ℕ) : Ideal (MvPolynomial τ R) where
  carrier := {f | ∀ m : τ →₀ ℕ, coeff m f ∈ I ^ (N - m.degree)}
  add_mem' hf hg m := by
    rw [coeff_add]; exact Ideal.add_mem _ (hf m) (hg m)
  zero_mem' m := by
    rw [coeff_zero]; exact Ideal.zero_mem _
  smul_mem' c f hf m := by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ fun x hx ↦ ?_
    have hxm : x.1 + x.2 = m := Finset.mem_antidiagonal.mp hx
    have hdeg : x.1.degree + x.2.degree = m.degree := by rw [← hxm, map_add]
    have hmul := Ideal.mul_mem_mul (Submodule.mem_top (x := coeff x.1 c)) (hf x.2)
    rw [Ideal.top_mul] at hmul
    exact Ideal.pow_le_pow_right (by omega) hmul

variable {τ I}

theorem mem_coeffFiltration_iff {N : ℕ} {f : MvPolynomial τ R} :
    f ∈ coeffFiltration τ I N ↔ ∀ m : τ →₀ ℕ, coeff m f ∈ I ^ (N - m.degree) :=
  Iff.rfl

/-- The coefficient filtration is multiplicative. -/
theorem coeffFiltration_mul {a b : ℕ} :
    coeffFiltration τ I a * coeffFiltration τ I b ≤ coeffFiltration τ I (a + b) := by
  classical
  refine Ideal.mul_le.mpr fun f hf g hg ↦ ?_
  intro m
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun x hx ↦ ?_
  have hxm : x.1 + x.2 = m := Finset.mem_antidiagonal.mp hx
  have hdeg : x.1.degree + x.2.degree = m.degree := by rw [← hxm, map_add]
  have hmul := Ideal.mul_mem_mul (hf x.1) (hg x.2)
  rw [← pow_add] at hmul
  exact Ideal.pow_le_pow_right (by omega) hmul

theorem polyExt_le_coeffFiltration_one : polyExt τ I ≤ coeffFiltration τ I 1 := by
  intro f hf m
  rcases eq_or_ne m 0 with rfl | hm
  · have h0 : (0 : τ →₀ ℕ).degree = 0 := map_zero _
    rw [h0, Nat.sub_zero, pow_one]
    exact hf
  · have : 1 - m.degree = 0 := by
      have : m.degree ≠ 0 := fun h ↦ hm ((Finsupp.degree_eq_zero_iff m).mp h)
      omega
    rw [this, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

/-- Powers of `I'` are contained in the coefficient filtration. -/
theorem pow_le_coeffFiltration (N : ℕ) : polyExt τ I ^ N ≤ coeffFiltration τ I N := by
  induction N with
  | zero => rw [pow_zero]; exact le_top.trans (by intro f _ m; simp)
  | succ n ih =>
    rw [pow_succ]
    refine le_trans (Ideal.mul_mono ih polyExt_le_coeffFiltration_one) ?_
    exact coeffFiltration_mul

/-- The monomial `y^m` lies in the `|m|`-th power of `I'`. -/
theorem monomial_one_mem_pow (m : τ →₀ ℕ) :
    (monomial m 1 : MvPolynomial τ R) ∈ polyExt τ I ^ m.degree := by
  classical
  rw [monic_monomial_eq, Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun t _ ↦ Ideal.pow_mem_pow (X_mem_polyExt t) _

/-- A coefficientwise-filtered polynomial lies in the corresponding power of `I'`. -/
theorem coeffFiltration_le_pow (N : ℕ) : coeffFiltration τ I N ≤ polyExt τ I ^ N := by
  intro f hf
  classical
  rw [f.as_sum]
  refine Ideal.sum_mem _ fun m _ ↦ ?_
  have hC : (C (coeff m f) : MvPolynomial τ R) ∈ polyExt τ I ^ (N - m.degree) := by
    have h1 : (C (coeff m f) : MvPolynomial τ R) ∈
        Ideal.map (C : R →+* MvPolynomial τ R) (I ^ (N - m.degree)) :=
      Ideal.mem_map_of_mem _ (hf m)
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono map_C_le_polyExt _ h1
  have hmul := Ideal.mul_mem_mul hC (monomial_one_mem_pow (I := I) m)
  rw [← pow_add] at hmul
  have hmm : (monomial m (coeff m f) : MvPolynomial τ R) = C (coeff m f) * monomial m 1 := by
    rw [C_mul_monomial, mul_one]
  rw [hmm]
  exact Ideal.pow_le_pow_right (by omega) hmul

/-- The powers of `I'` are exactly the steps of the coefficient filtration. -/
theorem pow_eq_coeffFiltration (N : ℕ) : polyExt τ I ^ N = coeffFiltration τ I N :=
  le_antisymm (pow_le_coeffFiltration N) (coeffFiltration_le_pow N)

theorem coeff_mem_of_mem_pow {N : ℕ} {f : MvPolynomial τ R} (hf : f ∈ polyExt τ I ^ N)
    (m : τ →₀ ℕ) : coeff m f ∈ I ^ (N - m.degree) :=
  pow_le_coeffFiltration N hf m

/-! ### Auxiliary lemmas on associated graded rings -/

section Gr

variable {A B : Type u} [CommRing A] [CommRing B] (J : Ideal A) (K : Ideal B)

/-- Functoriality of the Rees algebra for a ring map which only *carries* `J` into `K`
(as opposed to `AffineNormalCone.reesMapOfEq`, which needs `J·B = K`). -/
def reesMapOfLe (f : A →+* B) (h : J.map f ≤ K) : reesAlgebra J →+* reesAlgebra K :=
  ((Polynomial.mapRingHom f).comp (reesAlgebra J).val.toRingHom).codRestrict (reesAlgebra K) (by
    intro p
    rw [mem_reesAlgebra_iff]
    intro n
    change ((p : Polynomial A).map f).coeff n ∈ K ^ n
    rw [Polynomial.coeff_map]
    refine Ideal.pow_right_mono h n ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f ((mem_reesAlgebra_iff J _).mp p.property n))

@[simp]
theorem reesMapOfLe_coe (f : A →+* B) (h : J.map f ≤ K) (p : reesAlgebra J) :
    (reesMapOfLe J K f h p : Polynomial B) = (p : Polynomial A).map f :=
  rfl

theorem reesMapOfLe_algebraMap (f : A →+* B) (h : J.map f ≤ K) (a : A) :
    reesMapOfLe J K f h (algebraMap A (reesAlgebra J) a) = algebraMap B (reesAlgebra K) (f a) := by
  apply Subtype.ext
  change (Polynomial.C a).map f = Polynomial.C (f a)
  rw [Polynomial.map_C]

theorem reesMapOfLe_degreeOneRees (f : A →+* B) (h : J.map f ≤ K) (x : J) :
    reesMapOfLe J K f h (degreeOneRees A J x) =
      degreeOneRees B K ⟨f x, h (Ideal.mem_map_of_mem f x.2)⟩ := by
  apply Subtype.ext
  change (Polynomial.monomial 1 (x : A)).map f = Polynomial.monomial 1 (f x)
  rw [Polynomial.map_monomial]

theorem map_le_comap_reesMapOfLe (f : A →+* B) (h : J.map f ≤ K) :
    Ideal.map (algebraMap A (reesAlgebra J)) J ≤
      (Ideal.map (algebraMap B (reesAlgebra K)) K).comap (reesMapOfLe J K f h) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, reesMapOfLe_algebraMap]
  exact Ideal.mem_map_of_mem _ (h (Ideal.mem_map_of_mem f ha))

/-- The map of associated graded rings induced by a ring map carrying `J` into `K`. -/
def grMapOfLe (f : A →+* B) (h : J.map f ≤ K) :
    associatedGradedRing A J →+* associatedGradedRing B K :=
  Ideal.quotientMap _ (reesMapOfLe J K f h) (map_le_comap_reesMapOfLe J K f h)

@[simp]
theorem grMapOfLe_mk (f : A →+* B) (h : J.map f ≤ K) (p : reesAlgebra J) :
    grMapOfLe J K f h (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (reesMapOfLe J K f h p) :=
  rfl

theorem grMapOfLe_algebraMap (f : A →+* B) (h : J.map f ≤ K) (a : A) :
    grMapOfLe J K f h (algebraMap A (associatedGradedRing A J) a) =
      algebraMap B (associatedGradedRing B K) (f a) := by
  change grMapOfLe J K f h (Ideal.Quotient.mk _ (algebraMap A (reesAlgebra J) a)) =
    Ideal.Quotient.mk _ (algebraMap B (reesAlgebra K) (f a))
  rw [grMapOfLe_mk, reesMapOfLe_algebraMap]

theorem grMapOfLe_degreeOneRees (f : A →+* B) (h : J.map f ≤ K) (x : J) :
    grMapOfLe J K f h (Ideal.Quotient.mk _ (degreeOneRees A J x)) =
      Ideal.Quotient.mk _ (degreeOneRees B K ⟨f x, h (Ideal.mem_map_of_mem f x.2)⟩) := by
  rw [grMapOfLe_mk, reesMapOfLe_degreeOneRees]

variable {J K}

/-- The coefficientwise description of `J · Rees_J(A)`, whose quotient is `gr_J(A)`. -/
theorem mem_map_rees_of_coe_monomial {n : ℕ} {c : A} (hc : c ∈ J ^ (n + 1))
    (x : reesAlgebra J) (hx : (x : Polynomial A) = Polynomial.monomial n c) :
    x ∈ Ideal.map (algebraMap A (reesAlgebra J)) J := by
  rw [pow_succ] at hc
  refine Submodule.mul_induction_on'
    (C := fun c _ ↦ ∀ x : reesAlgebra J, (x : Polynomial A) = Polynomial.monomial n c →
      x ∈ Ideal.map (algebraMap A (reesAlgebra J)) J) ?_ ?_ hc x hx
  · intro a ha b hb x hx
    have hmem : Polynomial.monomial n a ∈ reesAlgebra J := reesAlgebra.monomial_mem.mpr ha
    have hxeq : x = algebraMap A (reesAlgebra J) b * ⟨Polynomial.monomial n a, hmem⟩ := by
      apply Subtype.ext
      rw [hx]
      change Polynomial.monomial n (a * b) = Polynomial.C b * Polynomial.monomial n a
      rw [Polynomial.C_mul_monomial, mul_comm]
    rw [hxeq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb)
  · intro c₁ hc₁ c₂ hc₂ ih₁ ih₂ x hx
    have hle : J ^ n * J ≤ J ^ n := by
      rw [← pow_succ]
      exact Ideal.pow_le_pow_right (Nat.le_succ n)
    have hm₁ : Polynomial.monomial n c₁ ∈ reesAlgebra J :=
      reesAlgebra.monomial_mem.mpr (hle hc₁)
    have hm₂ : Polynomial.monomial n c₂ ∈ reesAlgebra J :=
      reesAlgebra.monomial_mem.mpr (hle hc₂)
    have hxeq : x = (⟨_, hm₁⟩ : reesAlgebra J) + ⟨_, hm₂⟩ := by
      apply Subtype.ext
      rw [hx]
      change Polynomial.monomial n (c₁ + c₂) = Polynomial.monomial n c₁ + Polynomial.monomial n c₂
      exact map_add (Polynomial.monomial n) c₁ c₂
    rw [hxeq]
    exact Ideal.add_mem _ (ih₁ _ rfl) (ih₂ _ rfl)

/-- Membership in `J · Rees_J(A)` is detected coefficientwise. -/
theorem mem_map_rees_iff (q : reesAlgebra J) :
    q ∈ Ideal.map (algebraMap A (reesAlgebra J)) J ↔
      ∀ n, (q : Polynomial A).coeff n ∈ J ^ (n + 1) := by
  refine ⟨fun h n ↦ coeff_mem_pow_succ_of_mem_map_rees A J h n, fun h ↦ ?_⟩
  classical
  have hcoe : ∀ n, Polynomial.monomial n ((q : Polynomial A).coeff n) ∈ reesAlgebra J :=
    fun n ↦ reesAlgebra.monomial_mem.mpr ((mem_reesAlgebra_iff J _).mp q.2 n)
  have hsum : q = ∑ n ∈ (q : Polynomial A).support, (⟨_, hcoe n⟩ : reesAlgebra J) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (Polynomial.as_sum_support (q : Polynomial A)).trans rfl
  rw [hsum]
  exact Ideal.sum_mem _ fun n _ ↦ mem_map_rees_of_coe_monomial (h n) _ rfl

variable (J)

theorem degreeOneRaw_eq_mk (x : J) :
    degreeOneRaw A J x = Ideal.Quotient.mk _ (degreeOneRees A J x) :=
  rfl

theorem degreeOneRaw_smul (a : A) (x : J) :
    degreeOneRaw A J (a • x) =
      algebraMap A (associatedGradedRing A J) a * degreeOneRaw A J x := by
  rw [map_smul]
  change Ideal.Quotient.mk _ (a • degreeOneRees A J x) = _
  rw [Algebra.smul_def, map_mul]
  rfl

theorem degreeOneRaw_eq_zero_of_mem_sq (x : J) (hx : (x : A) ∈ J ^ 2) :
    degreeOneRaw A J x = 0 := by
  rw [degreeOneRaw_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  refine mem_map_rees_of_coe_monomial (n := 1) ?_ _ rfl
  rwa [show (1 : ℕ) + 1 = 2 from rfl]

theorem algebraMap_gr_eq_zero {a : A} (ha : a ∈ J) :
    algebraMap A (associatedGradedRing A J) a = 0 := by
  change Ideal.Quotient.mk _ (algebraMap A (reesAlgebra J) a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ ha

/-- Two ring maps out of `gr_J(A)` agreeing on degree zero and on the degree-one classes are
equal. -/
theorem gr_ringHom_ext {T : Type u} [CommSemiring T] {f g : associatedGradedRing A J →+* T}
    (h0 : ∀ a : A, f (algebraMap _ _ a) = g (algebraMap _ _ a))
    (h1 : ∀ x : J, f (degreeOneRaw A J x) = g (degreeOneRaw A J x)) : f = g := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p ↦ ?_)
  obtain ⟨s, rfl⟩ := symToRees_surjective A J p
  induction s using SymmetricAlgebra.induction with
  | algebraMap a =>
    have e : (symToRees A J) (algebraMap _ _ a) = algebraMap _ _ a := AlgHom.commutes _ a
    simpa [e] using h0 a
  | ι x =>
    simp only [RingHom.comp_apply, symToRees_ι]
    exact h1 x
  | mul a b ha hb => simp only [RingHom.comp_apply, map_mul] at ha hb ⊢; rw [ha, hb]
  | add a b ha hb => simp only [RingHom.comp_apply, map_add] at ha hb ⊢; rw [ha, hb]

/-- A ring map into `gr_J(A)` whose range contains the degree-zero and the degree-one classes is
surjective. -/
theorem gr_surjective {T : Type u} [CommRing T] (f : T →+* associatedGradedRing A J)
    (h0 : ∀ a : A, algebraMap A (associatedGradedRing A J) a ∈ f.range)
    (h1 : ∀ x : J, degreeOneRaw A J x ∈ f.range) : Function.Surjective f := by
  have hrange : ∀ z : associatedGradedRing A J, z ∈ f.range := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨s, rfl⟩ := symToRees_surjective A J p
    induction s using SymmetricAlgebra.induction with
    | algebraMap a =>
      have e : (symToRees A J) (algebraMap _ _ a) = algebraMap _ _ a := AlgHom.commutes _ a
      rw [e]
      exact h0 a
    | ι x =>
      rw [symToRees_ι]
      exact h1 x
    | mul a b ha hb =>
      rw [map_mul, map_mul]
      exact Subring.mul_mem _ ha hb
    | add a b ha hb =>
      rw [map_add, map_add]
      exact Subring.add_mem _ ha hb
  exact fun z ↦ hrange z

variable (K)

theorem map_symm_of_map (f : A ≃+* B) (h : J.map (f : A →+* B) = K) :
    K.map (f.symm : B →+* A) = J := by
  rw [← h, Ideal.map_map, show ((f.symm : B →+* A).comp (f : A →+* B)) = RingHom.id A from
    RingHom.ext fun a ↦ f.symm_apply_apply a, Ideal.map_id]

theorem grMapOfEq_degreeOneRaw (f : A →+* B) (h : J.map f = K) (x : J) :
    grMapOfEq J f K h (degreeOneRaw A J x) =
      degreeOneRaw B K ⟨f x, h ▸ Ideal.mem_map_of_mem f x.2⟩ := by
  rw [degreeOneRaw_eq_mk, grMapOfEq_mk, reesMapOfEq_degreeOneRees, degreeOneRaw_eq_mk]

theorem grMapOfEq_symm_comp (f : A ≃+* B) (h : J.map (f : A →+* B) = K)
    (h' : K.map (f.symm : B →+* A) = J) :
    (grMapOfEq K (f.symm : B →+* A) J h').comp (grMapOfEq J (f : A →+* B) K h) =
      RingHom.id (associatedGradedRing A J) := by
  have hcomp := grMapOfEq_comp J (f : A →+* B) K h (f.symm : B →+* A) J h'
  have he : ((f.symm : B →+* A).comp (f : A →+* B)) = RingHom.id A :=
    RingHom.ext fun a ↦ f.symm_apply_apply a
  rw [← hcomp, grMapOfEq_congr J _ J _ he]
  exact grMapOfEq_id J

/-- The associated graded ring only depends on the pair `(ring, ideal)` up to isomorphism. -/
def grEquivOfEquiv (f : A ≃+* B) (h : J.map (f : A →+* B) = K) :
    associatedGradedRing A J ≃+* associatedGradedRing B K where
  toFun := grMapOfEq J (f : A →+* B) K h
  invFun := grMapOfEq K (f.symm : B →+* A) J (map_symm_of_map J K f h)
  left_inv z := DFunLike.congr_fun (grMapOfEq_symm_comp J K f h (map_symm_of_map J K f h)) z
  right_inv z := DFunLike.congr_fun
    (grMapOfEq_symm_comp K J f.symm (map_symm_of_map J K f h) h) z
  map_mul' := map_mul _
  map_add' := map_add _

@[simp]
theorem grEquivOfEquiv_apply (f : A ≃+* B) (h : J.map (f : A →+* B) = K)
    (z : associatedGradedRing A J) :
    grEquivOfEquiv J K f h z = grMapOfEq J (f : A →+* B) K h z :=
  rfl

@[simp]
theorem grEquivOfEquiv_symm_apply (f : A ≃+* B) (h : J.map (f : A →+* B) = K)
    (z : associatedGradedRing B K) :
    (grEquivOfEquiv J K f h).symm z =
      grMapOfEq K (f.symm : B →+* A) J (map_symm_of_map J K f h) z :=
  rfl

/-! #### The normal sheaf -/

variable (J' : Ideal A)

/-- Functoriality of the symmetric algebra for an inclusion of ideals of the same ring. -/
def symMapOfLe (h : J ≤ J') : SymmetricAlgebra A J →ₐ[A] SymmetricAlgebra A J' :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι A J').comp (Submodule.inclusion h))

@[simp]
theorem symMapOfLe_ι (h : J ≤ J') (x : J) :
    symMapOfLe J J' h (SymmetricAlgebra.ι A J x) =
      SymmetricAlgebra.ι A J' ⟨(x : A), h x.2⟩ :=
  SymmetricAlgebra.lift_ι_apply _ _

theorem symMapOfLe_map_le (h : J ≤ J') :
    Ideal.map (algebraMap A (SymmetricAlgebra A J)) J ≤
      (Ideal.map (algebraMap A (SymmetricAlgebra A J')) J').comap (symMapOfLe J J' h) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
  exact Ideal.mem_map_of_mem _ (h ha)

/-- Functoriality of the normal-sheaf ring for an inclusion of ideals of the same ring. -/
def nsMapOfLe (h : J ≤ J') : normalSheafRing A J →+* normalSheafRing A J' :=
  Ideal.quotientMap _ (symMapOfLe J J' h).toRingHom (symMapOfLe_map_le J J' h)

@[simp]
theorem nsMapOfLe_mk (h : J ≤ J') (s : SymmetricAlgebra A J) :
    nsMapOfLe J J' h (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ (symMapOfLe J J' h s) :=
  rfl

/-- The degree-one class of `x ∈ J` in the normal-sheaf ring `Sym_A(J)/J·Sym_A(J)`. -/
def nsClass : J →ₗ[A] normalSheafRing A J :=
  (Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A (SymmetricAlgebra A J)) J)).toLinearMap.comp
    (SymmetricAlgebra.ι A J)

theorem nsClass_eq_mk (x : J) :
    nsClass J x = Ideal.Quotient.mk _ (SymmetricAlgebra.ι A J x) :=
  rfl

theorem nsClass_smul (a : A) (x : J) :
    nsClass J (a • x) = algebraMap A (normalSheafRing A J) a * nsClass J x := by
  rw [map_smul, Algebra.smul_def]

theorem nsClass_eq_zero_of_mem_sq (x : J) (hx : (x : A) ∈ J ^ 2) : nsClass J x = 0 := by
  rw [nsClass_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  rw [pow_two] at hx
  refine Submodule.mul_induction_on'
    (C := fun c _ ↦ ∀ hc : c ∈ J, SymmetricAlgebra.ι A J ⟨c, hc⟩ ∈
      Ideal.map (algebraMap A (SymmetricAlgebra A J)) J) ?_ ?_ hx x.2
  · intro a ha b hb hab
    have hsm : (⟨a * b, hab⟩ : J) = a • (⟨b, hb⟩ : J) := Subtype.ext rfl
    rw [hsm, map_smul, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
  · intro c₁ hc₁ c₂ hc₂ ih₁ ih₂ hc
    have hsum : (⟨c₁ + c₂, hc⟩ : J) =
        (⟨c₁, Ideal.mul_le_left hc₁⟩ : J) + ⟨c₂, Ideal.mul_le_left hc₂⟩ := Subtype.ext rfl
    rw [hsum, map_add]
    exact Ideal.add_mem _ (ih₁ _) (ih₂ _)

theorem algebraMap_ns_eq_zero {a : A} (ha : a ∈ J) :
    algebraMap A (normalSheafRing A J) a = 0 := by
  change Ideal.Quotient.mk _ (algebraMap A (SymmetricAlgebra A J) a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ ha

theorem nsToGr_nsClass (x : J) : nsToGr A J (nsClass J x) = degreeOneRaw A J x := by
  rw [nsClass_eq_mk, nsToGr_mk, symToRees_ι, degreeOneRaw_eq_mk]

/-- Two ring maps out of the normal-sheaf ring agreeing on degree zero and on the degree-one
classes are equal. -/
theorem ns_ringHom_ext {T : Type u} [CommSemiring T] {f g : normalSheafRing A J →+* T}
    (h0 : ∀ a : A, f (algebraMap _ _ a) = g (algebraMap _ _ a))
    (h1 : ∀ x : J, f (nsClass J x) = g (nsClass J x)) : f = g := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun s ↦ ?_)
  induction s using SymmetricAlgebra.induction with
  | algebraMap a =>
    change f (algebraMap A (normalSheafRing A J) a) = g (algebraMap A (normalSheafRing A J) a)
    exact h0 a
  | ι x =>
    change f (nsClass J x) = g (nsClass J x)
    exact h1 x
  | mul a b ha hb => simp only [RingHom.comp_apply, map_mul] at ha hb ⊢; rw [ha, hb]
  | add a b ha hb => simp only [RingHom.comp_apply, map_add] at ha hb ⊢; rw [ha, hb]

/-- A ring map into the normal-sheaf ring whose range contains the degree-zero and the
degree-one classes is surjective. -/
theorem ns_surjective {T : Type u} [CommRing T] (f : T →+* normalSheafRing A J)
    (h0 : ∀ a : A, algebraMap A (normalSheafRing A J) a ∈ f.range)
    (h1 : ∀ x : J, nsClass J x ∈ f.range) : Function.Surjective f := by
  have hrange : ∀ z : normalSheafRing A J, z ∈ f.range := by
    intro z
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction s using SymmetricAlgebra.induction with
    | algebraMap a => exact h0 a
    | ι x => exact h1 x
    | mul a b ha hb =>
      rw [map_mul]
      exact Subring.mul_mem _ ha hb
    | add a b ha hb =>
      rw [map_add]
      exact Subring.add_mem _ ha hb
  exact fun z ↦ hrange z

end Gr

/-! ### The product formula `gr_{I'}(R[y]) = gr_I(R)[z]` -/

section ProductFormula

variable (τ I)

/-- The inclusion `Rees_I(R) → Rees_{I'}(R[y_τ])` of Rees algebras. -/
def reesIncl : reesAlgebra I →+* reesAlgebra (polyExt τ I) :=
  reesMapOfLe I (polyExt τ I) (C : R →+* MvPolynomial τ R) map_C_le_polyExt

/-- The inclusion `gr_I(R) → gr_{I'}(R[y_τ])`, dual to the projection `C_{U/M'} → C_{U/M}`. -/
def grIncl : associatedGradedRing R I →+* associatedGradedRing (MvPolynomial τ R) (polyExt τ I) :=
  grMapOfLe I (polyExt τ I) (C : R →+* MvPolynomial τ R) map_C_le_polyExt

theorem grIncl_mk (p : reesAlgebra I) :
    grIncl τ I (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (reesIncl τ I p) :=
  rfl

theorem grIncl_algebraMap (r : R) :
    grIncl τ I (algebraMap R (associatedGradedRing R I) r) =
      algebraMap (MvPolynomial τ R) (associatedGradedRing (MvPolynomial τ R) (polyExt τ I))
        (C r) :=
  grMapOfLe_algebraMap I (polyExt τ I) _ _ r

theorem grIncl_degreeOneRaw (x : I) :
    grIncl τ I (degreeOneRaw R I x) =
      degreeOneRaw (MvPolynomial τ R) (polyExt τ I) ⟨C (x : R), C_mem_polyExt x.2⟩ :=
  grMapOfLe_degreeOneRees I (polyExt τ I) _ _ x

/-- The degree-one class of the extra variable `y_t`: the `t`-th coordinate on the factor
`𝔸^τ` of `C_{U/M'} = C_{U/M} × 𝔸^τ`. -/
def zVar (t : τ) : associatedGradedRing (MvPolynomial τ R) (polyExt τ I) :=
  degreeOneRaw (MvPolynomial τ R) (polyExt τ I) ⟨X t, X_mem_polyExt t⟩

/-- The comparison map `gr_I(R)[z_τ] → gr_{I'}(R[y_τ])`.  It is proved to be an isomorphism
in `prodEquiv`: the normal cone of the refined embedding is `C_{U/M} × 𝔸^τ`. -/
def prodMap : MvPolynomial τ (associatedGradedRing R I) →+*
    associatedGradedRing (MvPolynomial τ R) (polyExt τ I) :=
  eval₂Hom (grIncl τ I) (zVar τ I)

variable {τ I}

@[simp]
theorem prodMap_C (w : associatedGradedRing R I) : prodMap τ I (C w) = grIncl τ I w :=
  eval₂Hom_C _ _ _

@[simp]
theorem prodMap_X (t : τ) : prodMap τ I (X t) = zVar τ I t :=
  eval₂Hom_X' _ _ _

theorem prodMap_monomial (m : τ →₀ ℕ) (w : associatedGradedRing R I) :
    prodMap τ I (monomial m w) = grIncl τ I w * m.prod fun t e ↦ zVar τ I t ^ e := by
  rw [prodMap, coe_eval₂Hom, eval₂_monomial]

/-! #### Surjectivity -/

theorem algebraMap_gr_polyExt_eq (v : MvPolynomial τ R) :
    algebraMap (MvPolynomial τ R) (associatedGradedRing (MvPolynomial τ R) (polyExt τ I)) v =
      algebraMap (MvPolynomial τ R) (associatedGradedRing (MvPolynomial τ R) (polyExt τ I))
        (C (constantCoeff v)) := by
  have hmem : v - C (constantCoeff v) ∈ polyExt τ I := by
    rw [mem_polyExt_iff, map_sub, constantCoeff_C, sub_self]
    exact Ideal.zero_mem _
  have h0 := algebraMap_gr_eq_zero (polyExt τ I) hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0

/-- The degree-one class of a monomial of `y`-degree at least two vanishes. -/
theorem degreeOneRaw_monomial_eq_zero {m : τ →₀ ℕ} (hm : 2 ≤ m.degree) (c : R)
    (hc : (monomial m c : MvPolynomial τ R) ∈ polyExt τ I) :
    degreeOneRaw (MvPolynomial τ R) (polyExt τ I) ⟨monomial m c, hc⟩ = 0 := by
  refine degreeOneRaw_eq_zero_of_mem_sq _ _ ?_
  change (monomial m c : MvPolynomial τ R) ∈ polyExt τ I ^ 2
  rw [show (monomial m c : MvPolynomial τ R) = C c * monomial m 1 by
    rw [C_mul_monomial, mul_one]]
  exact Ideal.mul_mem_left _ _
    (Ideal.pow_le_pow_right hm (monomial_one_mem_pow (I := I) m))

theorem prodMap_surjective : Function.Surjective (prodMap τ I) := by
  classical
  refine gr_surjective _ _ ?_ ?_
  · intro v
    refine ⟨C (algebraMap R (associatedGradedRing R I) (constantCoeff v)), ?_⟩
    rw [prodMap_C, grIncl_algebraMap, ← algebraMap_gr_polyExt_eq]
  · intro x
    have hx : ∀ m : τ →₀ ℕ, (monomial m (coeff m (x : MvPolynomial τ R)) :
        MvPolynomial τ R) ∈ polyExt τ I := by
      intro m
      rcases eq_or_ne m 0 with rfl | hm
      · rw [monomial_zero']
        exact C_mem_polyExt x.2
      · rw [mem_polyExt_iff, constantCoeff_monomial, if_neg hm]
        exact Ideal.zero_mem _
    have hsum : x = ∑ m ∈ (x : MvPolynomial τ R).support,
        (⟨_, hx m⟩ : polyExt τ I) := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact (support_sum_monomial_coeff (x : MvPolynomial τ R)).symm
    rw [hsum, map_sum]
    refine Subring.sum_mem _ fun m _ ↦ ?_
    rcases Nat.lt_or_ge m.degree 2 with hm | hm
    · interval_cases hmd : m.degree
      · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp hmd
        subst hm0
        have hc0 : coeff (0 : τ →₀ ℕ) (x : MvPolynomial τ R) ∈ I := x.2
        refine ⟨C (degreeOneRaw R I ⟨coeff (0 : τ →₀ ℕ) (x : MvPolynomial τ R), hc0⟩), ?_⟩
        rw [prodMap_C, grIncl_degreeOneRaw]
        exact congrArg _ (Subtype.ext (congrFun monomial_zero' _).symm)
      · obtain ⟨t, ht⟩ := (Finsupp.range_single_one (σ := τ)).ge hmd
        subst ht
        refine ⟨C (algebraMap R (associatedGradedRing R I)
          (coeff (Finsupp.single t 1) (x : MvPolynomial τ R))) * X t, ?_⟩
        rw [map_mul, prodMap_C, prodMap_X, grIncl_algebraMap, zVar]
        rw [← degreeOneRaw_smul]
        congr 1
        apply Subtype.ext
        rw [SetLike.val_smul, smul_eq_mul, C_mul_X_eq_monomial]
    · exact ⟨0, by rw [map_zero, degreeOneRaw_monomial_eq_zero hm]⟩

/-! #### Injectivity -/

theorem prod_monomial_eq {S : Type u} [CommRing S] (s : Finset τ) (k : τ → ℕ) (c : τ → S) :
    ∏ t ∈ s, Polynomial.monomial (k t) (c t) =
      Polynomial.monomial (∑ t ∈ s, k t) (∏ t ∈ s, c t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, ih,
      Polynomial.monomial_mul_monomial]

variable (τ I)

@[simp]
theorem coe_reesIncl (p : reesAlgebra I) :
    (reesIncl τ I p : Polynomial (MvPolynomial τ R)) = (p : Polynomial R).map C :=
  rfl

/-- The Rees element `y^m t^{|m|}` of `Rees_{I'}(R[y_τ])`, whose class in `gr_{I'}` is the
monomial `z^m` in the extra coordinates. -/
def reesMonomial (m : τ →₀ ℕ) : reesAlgebra (polyExt τ I) :=
  ⟨Polynomial.C (monomial m 1) * Polynomial.X ^ m.degree, by
    rw [mem_reesAlgebra_iff]
    intro n
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs with h
    · rw [h]
      exact monomial_one_mem_pow m
    · exact Ideal.zero_mem _⟩

@[simp]
theorem coe_reesMonomial (m : τ →₀ ℕ) :
    (reesMonomial τ I m : Polynomial (MvPolynomial τ R)) =
      Polynomial.C (monomial m 1) * Polynomial.X ^ m.degree :=
  rfl

theorem mk_reesMonomial (m : τ →₀ ℕ) :
    Ideal.Quotient.mk _ (reesMonomial τ I m) = m.prod fun t e ↦ zVar τ I t ^ e := by
  classical
  have hprod : (m.prod fun t e ↦ (degreeOneRees (MvPolynomial τ R) (polyExt τ I)
      ⟨X t, X_mem_polyExt t⟩) ^ e) = reesMonomial τ I m := by
    apply Subtype.ext
    rw [Finsupp.prod, SubmonoidClass.coe_finsetProd, coe_reesMonomial]
    have hcoe : ∀ t : τ, ((degreeOneRees (MvPolynomial τ R) (polyExt τ I)
        ⟨X t, X_mem_polyExt t⟩ ^ m t : reesAlgebra (polyExt τ I)) :
          Polynomial (MvPolynomial τ R)) =
          Polynomial.monomial (m t) ((X t : MvPolynomial τ R) ^ m t) := by
      intro t
      rw [SubmonoidClass.coe_pow,
        show ((degreeOneRees (MvPolynomial τ R) (polyExt τ I) ⟨X t, X_mem_polyExt t⟩ :
          reesAlgebra (polyExt τ I)) : Polynomial (MvPolynomial τ R)) =
          Polynomial.monomial 1 (X t) from rfl, Polynomial.monomial_pow, one_mul]
    rw [Finset.prod_congr rfl fun t _ ↦ hcoe t, prod_monomial_eq,
      ← Polynomial.C_mul_X_pow_eq_monomial, ← Finsupp.degree_apply]
    congr 1
    rw [monic_monomial_eq, Finsupp.prod]
  rw [← hprod, Finsupp.prod, Finsupp.prod, map_prod]
  exact Finset.prod_congr rfl fun t _ ↦ map_pow _ _ _

variable {τ I}

theorem prodMap_injective : Function.Injective (prodMap τ I) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨q, hq⟩ : ∃ q : (τ →₀ ℕ) → reesAlgebra I,
      ∀ m, Ideal.Quotient.mk _ (q m) = coeff m u :=
    ⟨fun m ↦ Function.surjInv Ideal.Quotient.mk_surjective (coeff m u),
      fun m ↦ Function.surjInv_eq _ _⟩
  have hmk : prodMap τ I u =
      Ideal.Quotient.mk _ (∑ m ∈ u.support, reesIncl τ I (q m) * reesMonomial τ I m) := by
    conv_lhs => rw [u.as_sum]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [prodMap_monomial, map_mul, ← mk_reesMonomial, ← hq m, grIncl_mk]
  have hzero : (∑ m ∈ u.support, reesIncl τ I (q m) * reesMonomial τ I m) ∈
      Ideal.map (algebraMap (MvPolynomial τ R) (reesAlgebra (polyExt τ I))) (polyExt τ I) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hmk, hu]
  have hcoe : ∀ N : ℕ,
      ((∑ m ∈ u.support, reesIncl τ I (q m) * reesMonomial τ I m :
          reesAlgebra (polyExt τ I)) : Polynomial (MvPolynomial τ R)).coeff N =
        ∑ m ∈ u.support, if m.degree ≤ N then
          monomial m ((q m : Polynomial R).coeff (N - m.degree)) else 0 := by
    intro N
    rw [AddSubmonoidClass.coe_finsetSum, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    have hcoemul : ((reesIncl τ I (q m) * reesMonomial τ I m : reesAlgebra (polyExt τ I)) :
        Polynomial (MvPolynomial τ R)) =
        ((q m : Polynomial R).map C * Polynomial.C (monomial m 1)) * Polynomial.X ^ m.degree := by
      change (reesIncl τ I (q m) : Polynomial (MvPolynomial τ R)) *
        (reesMonomial τ I m : Polynomial (MvPolynomial τ R)) = _
      rw [coe_reesIncl, coe_reesMonomial, ← mul_assoc]
    rw [hcoemul, Polynomial.coeff_mul_X_pow']
    split_ifs with h
    · rw [Polynomial.coeff_mul_C, Polynomial.coeff_map, C_mul_monomial, mul_one]
    · rfl
  refine MvPolynomial.ext _ _ fun m' ↦ ?_
  rw [coeff_zero]
  by_cases hm' : m' ∈ u.support
  · rw [← hq m', Ideal.Quotient.eq_zero_iff_mem, mem_map_rees_iff]
    intro n
    have hN := coeff_mem_of_mem_pow ((mem_map_rees_iff _).mp hzero (n + m'.degree)) m'
    rw [hcoe, coeff_sum] at hN
    have hsingle : ∑ m ∈ u.support, coeff m' (if m.degree ≤ n + m'.degree then
        monomial m ((q m : Polynomial R).coeff (n + m'.degree - m.degree)) else 0) =
        (q m' : Polynomial R).coeff n := by
      refine (Finset.sum_eq_single m' ?_ ?_).trans ?_
      · intro m _ hne
        split_ifs
        · rw [coeff_monomial, if_neg hne]
        · rw [coeff_zero]
      · intro h
        exact absurd hm' h
      · rw [if_pos (Nat.le_add_left _ _), coeff_monomial, if_pos rfl, Nat.add_sub_cancel]
    rw [hsingle] at hN
    have hexp : n + m'.degree + 1 - m'.degree = n + 1 := by omega
    rwa [hexp] at hN
  · simpa using hm'

/-- **The product formula for the normal cone of a refinement.**  The normal cone of the
graph embedding `U ↪ M × 𝔸^τ` is the product `C_{U/M} × 𝔸^τ`: the associated graded ring of
`I' = I·R[y_τ] + (y_τ)` is the polynomial ring `gr_I(R)[z_τ]`, the extra variables being the
degree-one classes of the new coordinates. -/
def prodEquiv : MvPolynomial τ (associatedGradedRing R I) ≃+*
    associatedGradedRing (MvPolynomial τ R) (polyExt τ I) :=
  RingEquiv.ofBijective (prodMap τ I) ⟨prodMap_injective, prodMap_surjective⟩

@[simp]
theorem prodEquiv_apply (w : MvPolynomial τ (associatedGradedRing R I)) :
    prodEquiv w = prodMap τ I w :=
  rfl

/-! #### The normal sheaf of the refinement -/

variable (τ I)

/-- The inclusion `N_{U/M} → N_{U/M'}` of normal-sheaf rings. -/
def nsIncl : normalSheafRing R I →+*
    normalSheafRing (MvPolynomial τ R) (polyExt τ I) :=
  (nsMapOfLe (Ideal.map (C : R →+* MvPolynomial τ R) I) (polyExt τ I) map_C_le_polyExt).comp
    (nsMapOfEq I (C : R →+* MvPolynomial τ R) (Ideal.map (C : R →+* MvPolynomial τ R) I) rfl)

theorem nsIncl_algebraMap (r : R) :
    nsIncl τ I (algebraMap R (normalSheafRing R I) r) =
      algebraMap (MvPolynomial τ R) (normalSheafRing (MvPolynomial τ R) (polyExt τ I)) (C r) := by
  rw [nsIncl, RingHom.comp_apply]
  change nsMapOfLe _ _ _ (nsMapOfEq I (C : R →+* MvPolynomial τ R) _ rfl
    (Ideal.Quotient.mk _ (algebraMap R (SymmetricAlgebra R I) r))) = _
  rw [nsMapOfEq_mk, symMapOfEq_algebraMap, nsMapOfLe_mk]
  change Ideal.Quotient.mk _ (symMapOfLe _ _ _ (algebraMap _ _ (C r))) = _
  rw [AlgHom.commutes]
  rfl

theorem nsIncl_nsClass (x : I) :
    nsIncl τ I (nsClass I x) =
      nsClass (polyExt τ I) ⟨C (x : R), C_mem_polyExt x.2⟩ := by
  rw [nsIncl, RingHom.comp_apply, nsClass_eq_mk, nsMapOfEq_mk, symMapOfEq_ι, nsMapOfLe_mk,
    symMapOfLe_ι, nsClass_eq_mk]

/-- The degree-one class of the extra variable `y_t` in the normal-sheaf ring. -/
def nsZVar (t : τ) : normalSheafRing (MvPolynomial τ R) (polyExt τ I) :=
  nsClass (polyExt τ I) ⟨X t, X_mem_polyExt t⟩

/-- The comparison map `N_{U/M}[z_τ] → N_{U/M'}` of normal sheaves of a refinement. -/
def nsProdMap : MvPolynomial τ (normalSheafRing R I) →+*
    normalSheafRing (MvPolynomial τ R) (polyExt τ I) :=
  eval₂Hom (nsIncl τ I) (nsZVar τ I)

variable {τ I}

@[simp]
theorem nsProdMap_C (w : normalSheafRing R I) : nsProdMap τ I (C w) = nsIncl τ I w :=
  eval₂Hom_C _ _ _

@[simp]
theorem nsProdMap_X (t : τ) : nsProdMap τ I (X t) = nsZVar τ I t :=
  eval₂Hom_X' _ _ _

theorem nsToGr_comp_nsIncl :
    (nsToGr (MvPolynomial τ R) (polyExt τ I)).toRingHom.comp (nsIncl τ I) =
      (grIncl τ I).comp (nsToGr R I).toRingHom := by
  refine ns_ringHom_ext I (fun r ↦ ?_) fun x ↦ ?_
  · change nsToGr (MvPolynomial τ R) (polyExt τ I) (nsIncl τ I
      (algebraMap R (normalSheafRing R I) r)) =
      grIncl τ I (nsToGr R I (algebraMap R (normalSheafRing R I) r))
    rw [nsIncl_algebraMap, AlgHom.commutes, AlgHom.commutes, grIncl_algebraMap]
  · change nsToGr (MvPolynomial τ R) (polyExt τ I) (nsIncl τ I (nsClass I x)) =
      grIncl τ I (nsToGr R I (nsClass I x))
    rw [nsIncl_nsClass, nsToGr_nsClass, nsToGr_nsClass, grIncl_degreeOneRaw]

/-- **The closed immersion `C ⊆ N` is compatible with the product decomposition.**  The
comparison maps of the normal cone and of the normal sheaf of a refinement fit in a commutative
square with the surjections `Sym(I/I²) ↠ gr_I`. -/
theorem nsToGr_comp_nsProdMap :
    (nsToGr (MvPolynomial τ R) (polyExt τ I)).toRingHom.comp (nsProdMap τ I) =
      (prodMap τ I).comp (MvPolynomial.map (nsToGr R I).toRingHom) := by
  refine MvPolynomial.ringHom_ext (fun w ↦ ?_) fun t ↦ ?_
  · rw [RingHom.comp_apply, RingHom.comp_apply, nsProdMap_C, MvPolynomial.map_C, prodMap_C]
    exact DFunLike.congr_fun nsToGr_comp_nsIncl w
  · rw [RingHom.comp_apply, RingHom.comp_apply, nsProdMap_X, MvPolynomial.map_X, prodMap_X,
      nsZVar, zVar]
    exact nsToGr_nsClass _ _

theorem algebraMap_ns_polyExt_eq (v : MvPolynomial τ R) :
    algebraMap (MvPolynomial τ R) (normalSheafRing (MvPolynomial τ R) (polyExt τ I)) v =
      algebraMap (MvPolynomial τ R) (normalSheafRing (MvPolynomial τ R) (polyExt τ I))
        (C (constantCoeff v)) := by
  have hmem : v - C (constantCoeff v) ∈ polyExt τ I := by
    rw [mem_polyExt_iff, map_sub, constantCoeff_C, sub_self]
    exact Ideal.zero_mem _
  have h0 := algebraMap_ns_eq_zero (polyExt τ I) hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0

theorem nsProdMap_surjective : Function.Surjective (nsProdMap τ I) := by
  classical
  refine ns_surjective _ _ ?_ ?_
  · intro v
    refine ⟨C (algebraMap R (normalSheafRing R I) (constantCoeff v)), ?_⟩
    rw [nsProdMap_C, nsIncl_algebraMap, ← algebraMap_ns_polyExt_eq]
  · intro x
    have hx : ∀ m : τ →₀ ℕ, (monomial m (coeff m (x : MvPolynomial τ R)) :
        MvPolynomial τ R) ∈ polyExt τ I := by
      intro m
      rcases eq_or_ne m 0 with rfl | hm
      · rw [monomial_zero']
        exact C_mem_polyExt x.2
      · rw [mem_polyExt_iff, constantCoeff_monomial, if_neg hm]
        exact Ideal.zero_mem _
    have hsum : x = ∑ m ∈ (x : MvPolynomial τ R).support, (⟨_, hx m⟩ : polyExt τ I) := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact (support_sum_monomial_coeff (x : MvPolynomial τ R)).symm
    rw [hsum, map_sum]
    refine Subring.sum_mem _ fun m _ ↦ ?_
    rcases Nat.lt_or_ge m.degree 2 with hm | hm
    · interval_cases hmd : m.degree
      · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp hmd
        subst hm0
        have hc0 : coeff (0 : τ →₀ ℕ) (x : MvPolynomial τ R) ∈ I := x.2
        refine ⟨C (nsClass I ⟨coeff (0 : τ →₀ ℕ) (x : MvPolynomial τ R), hc0⟩), ?_⟩
        rw [nsProdMap_C, nsIncl_nsClass]
        exact congrArg _ (Subtype.ext (congrFun monomial_zero' _).symm)
      · obtain ⟨t, ht⟩ := (Finsupp.range_single_one (σ := τ)).ge hmd
        subst ht
        refine ⟨C (algebraMap R (normalSheafRing R I)
          (coeff (Finsupp.single t 1) (x : MvPolynomial τ R))) * X t, ?_⟩
        rw [map_mul, nsProdMap_C, nsProdMap_X, nsIncl_algebraMap, nsZVar, ← nsClass_smul]
        exact congrArg _ (Subtype.ext (by
          rw [SetLike.val_smul, smul_eq_mul, C_mul_X_eq_monomial]))
    · refine ⟨0, ?_⟩
      rw [map_zero]
      refine (nsClass_eq_zero_of_mem_sq _ _ ?_).symm
      change (monomial m (coeff m (x : MvPolynomial τ R)) : MvPolynomial τ R) ∈ polyExt τ I ^ 2
      rw [show (monomial m (coeff m (x : MvPolynomial τ R)) : MvPolynomial τ R) =
        C (coeff m (x : MvPolynomial τ R)) * monomial m 1 by rw [C_mul_monomial, mul_one]]
      exact Ideal.mul_mem_left _ _
        (Ideal.pow_le_pow_right hm (monomial_one_mem_pow (I := I) m))


end ProductFormula

/-! ### The polynomial model: the graph embedding `U ↪ 𝔸^{σ ⊕ τ}` -/

section Graph

open ConeTranslation

variable (A : Type u) [CommRing A] (σ τ : Type u)

/-- The inclusion `𝔸^{σ⊕τ} → 𝔸^σ` of coordinate rings induced by the projection
`M' = 𝔸^{σ⊕τ} → 𝔸^σ = M`. -/
def incl : Amb A σ →ₐ[A] Amb A (σ ⊕ τ) :=
  rename Sum.inl

variable {A σ τ}

@[simp]
theorem incl_X (i : σ) : incl A σ τ (X i) = X (Sum.inl i) :=
  rename_X _ _

@[simp]
theorem incl_C (a : A) : incl A σ τ (C a) = C a :=
  rename_C _ _

/-- The retraction `𝔸^σ → 𝔸^{σ⊕τ}` of coordinate rings dual to the graph embedding
`x ↦ (x, g(x))`. -/
def graphProj (g : τ → Amb A σ) : Amb A (σ ⊕ τ) →ₐ[A] Amb A σ :=
  aeval (Sum.elim X g)

@[simp]
theorem graphProj_X_inl (g : τ → Amb A σ) (i : σ) : graphProj g (X (Sum.inl i)) = X i :=
  aeval_X _ _

@[simp]
theorem graphProj_X_inr (g : τ → Amb A σ) (t : τ) : graphProj g (X (Sum.inr t)) = g t :=
  aeval_X _ _

theorem graphProj_comp_incl (g : τ → Amb A σ) :
    (graphProj g).comp (incl A σ τ) = AlgHom.id A (Amb A σ) := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  rw [AlgHom.comp_apply, incl_X, graphProj_X_inl, AlgHom.id_apply]

theorem graphProj_incl (g : τ → Amb A σ) (f : Amb A σ) : graphProj g (incl A σ τ f) = f :=
  DFunLike.congr_fun (graphProj_comp_incl g) f

theorem graphProj_surjective (g : τ → Amb A σ) : Function.Surjective (graphProj g) :=
  fun f ↦ ⟨incl A σ τ f, graphProj_incl g f⟩

variable (A σ τ)

/-- The ideal of the graph embedding `U = Spec (R/I) ↪ M' = 𝔸^{σ⊕τ}`, `x ↦ (x, g(x))`:
it is `I·R' + (y_t - g_t)`, presented as the preimage of `I` under the retraction. -/
def graphIdeal (I : Ideal (Amb A σ)) (g : τ → Amb A σ) : Ideal (Amb A (σ ⊕ τ)) :=
  Ideal.comap (graphProj g : Amb A (σ ⊕ τ) →+* Amb A σ) I

variable {A σ τ}

theorem mem_graphIdeal_iff {I : Ideal (Amb A σ)} {g : τ → Amb A σ} {f : Amb A (σ ⊕ τ)} :
    f ∈ graphIdeal A σ τ I g ↔ graphProj g f ∈ I :=
  Iff.rfl

theorem ker_mk_comp_graphProj (I : Ideal (Amb A σ)) (g : τ → Amb A σ) :
    RingHom.ker ((Ideal.Quotient.mkₐ A I).comp (graphProj g)) = graphIdeal A σ τ I g := by
  ext f
  rw [RingHom.mem_ker, mem_graphIdeal_iff]
  change Ideal.Quotient.mk I (graphProj g f) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]

/-- The graph embedding presents the same closed subscheme as the original one:
`R'/I' ≃ R/I`. -/
def graphQuotientEquiv (I : Ideal (Amb A σ)) (g : τ → Amb A σ) :
    (Amb A (σ ⊕ τ) ⧸ graphIdeal A σ τ I g) ≃ₐ[A] (Amb A σ ⧸ I) :=
  (Ideal.quotientEquivAlgOfEq A (ker_mk_comp_graphProj I g).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := (Ideal.Quotient.mkₐ A I).comp (graphProj g))
      (Ideal.Quotient.mk_surjective.comp (graphProj_surjective g)))

@[simp]
theorem graphQuotientEquiv_mk (I : Ideal (Amb A σ)) (g : τ → Amb A σ) (f : Amb A (σ ⊕ τ)) :
    graphQuotientEquiv I g (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk I (graphProj g f) :=
  rfl

@[simp]
theorem graphQuotientEquiv_symm_mk (I : Ideal (Amb A σ)) (g : τ → Amb A σ) (f : Amb A σ) :
    (graphQuotientEquiv I g).symm (Ideal.Quotient.mk I f) =
      Ideal.Quotient.mk _ (incl A σ τ f) := by
  rw [AlgEquiv.symm_apply_eq, graphQuotientEquiv_mk, graphProj_incl]

/-! #### The change of variables making the graph the zero section -/

/-- The shear `y_t ↦ y_t + g_t(x)` of `𝔸^{σ⊕τ}` as an algebra map. -/
def shearHom (g : τ → Amb A σ) : Amb A (σ ⊕ τ) →ₐ[A] Amb A (σ ⊕ τ) :=
  aeval (Sum.elim (fun i ↦ X (Sum.inl i)) fun t ↦ X (Sum.inr t) + incl A σ τ (g t))

@[simp]
theorem shearHom_X_inl (g : τ → Amb A σ) (i : σ) :
    shearHom g (X (Sum.inl i)) = X (Sum.inl i) :=
  aeval_X _ _

@[simp]
theorem shearHom_X_inr (g : τ → Amb A σ) (t : τ) :
    shearHom g (X (Sum.inr t)) = X (Sum.inr t) + incl A σ τ (g t) :=
  aeval_X _ _

theorem shearHom_comp_incl (g : τ → Amb A σ) :
    (shearHom g).comp (incl A σ τ) = incl A σ τ := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  rw [AlgHom.comp_apply, incl_X, shearHom_X_inl]

theorem shearHom_incl (g : τ → Amb A σ) (f : Amb A σ) :
    shearHom g (incl A σ τ f) = incl A σ τ f :=
  DFunLike.congr_fun (shearHom_comp_incl g) f

theorem shearHom_comp_shearHom (g : τ → Amb A σ) :
    (shearHom (-g)).comp (shearHom g) = AlgHom.id A (Amb A (σ ⊕ τ)) := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  cases i with
  | inl i => rw [AlgHom.comp_apply, shearHom_X_inl, shearHom_X_inl, AlgHom.id_apply]
  | inr t =>
    rw [AlgHom.comp_apply, shearHom_X_inr, map_add, shearHom_X_inr, shearHom_incl,
      AlgHom.id_apply]
    change X (Sum.inr t) + incl A σ τ (-g t) + incl A σ τ (g t) = X (Sum.inr t)
    rw [map_neg]
    ring

/-- The change of variables `y_t ↦ y_t + g_t(x)`: an automorphism of `𝔸^{σ⊕τ}` over `𝔸^σ`. -/
def shear (g : τ → Amb A σ) : Amb A (σ ⊕ τ) ≃ₐ[A] Amb A (σ ⊕ τ) :=
  AlgEquiv.ofAlgHom (shearHom g) (shearHom (-g))
    (by simpa using shearHom_comp_shearHom (-g)) (shearHom_comp_shearHom g)

@[simp]
theorem shear_apply (g : τ → Amb A σ) (f : Amb A (σ ⊕ τ)) : shear g f = shearHom g f :=
  rfl

/-- The change of variables as a ring isomorphism. -/
def shearEquiv (g : τ → Amb A σ) : Amb A (σ ⊕ τ) ≃+* Amb A (σ ⊕ τ) :=
  (shear g).toRingEquiv

theorem graphProj_comp_shearHom (g : τ → Amb A σ) :
    (graphProj (0 : τ → Amb A σ)).comp (shearHom g) = graphProj g := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  cases i with
  | inl i => rw [AlgHom.comp_apply, shearHom_X_inl, graphProj_X_inl, graphProj_X_inl]
  | inr t =>
    rw [AlgHom.comp_apply, shearHom_X_inr, map_add, graphProj_X_inr, graphProj_incl,
      graphProj_X_inr]
    change (0 : Amb A σ) + g t = g t
    rw [zero_add]

/-- **Change of variables.**  The shear `y_t ↦ y_t + g_t(x)` carries the ideal of the graph
embedding to the ideal `I·R' + (y_τ)` of the zero-section embedding: one may assume `g = 0`. -/
theorem map_shear_graphIdeal (I : Ideal (Amb A σ)) (g : τ → Amb A σ) :
    Ideal.map (shearEquiv g) (graphIdeal A σ τ I g) = graphIdeal A σ τ I 0 := by
  have hshear : ∀ f, graphProj g ((shearEquiv g).symm f) = graphProj (0 : τ → Amb A σ) f := by
    intro f
    have hf := DFunLike.congr_fun (graphProj_comp_shearHom g) ((shearEquiv g).symm f)
    rw [AlgHom.comp_apply] at hf
    rw [← hf]
    congr 1
    change shearEquiv g ((shearEquiv g).symm f) = f
    rw [RingEquiv.apply_symm_apply]
  rw [← Ideal.comap_symm]
  refine Ideal.ext fun f ↦ ?_
  rw [Ideal.mem_comap, mem_graphIdeal_iff, mem_graphIdeal_iff, hshear]

/-- The ideal of the zero-section embedding is `I·R' + (y_τ)`, as in Behrend–Fantechi. -/
theorem graphIdeal_zero_eq (I : Ideal (Amb A σ)) :
    graphIdeal A σ τ I 0 = Ideal.map (incl A σ τ : Amb A σ →+* Amb A (σ ⊕ τ)) I ⊔
      Ideal.span (Set.range fun t : τ ↦ X (Sum.inr t)) := by
  refine le_antisymm (fun f hf ↦ ?_) (sup_le ?_ ?_)
  · have hker : f - incl A σ τ (graphProj 0 f) ∈
        RingHom.ker (graphProj (0 : τ → Amb A σ) : Amb A (σ ⊕ τ) →+* Amb A σ) := by
      rw [RingHom.mem_ker, map_sub]
      change graphProj 0 f - graphProj 0 (incl A σ τ (graphProj 0 f)) = 0
      rw [graphProj_incl, sub_self]
    have hspan : RingHom.ker (graphProj (0 : τ → Amb A σ)).toRingHom ≤
        Ideal.span (Set.range fun t : τ ↦ (X (Sum.inr t) : Amb A (σ ⊕ τ))) := by
      have hgen : Algebra.adjoin A (Set.range (X : σ ⊕ τ → Amb A (σ ⊕ τ))) = ⊤ :=
        MvPolynomial.adjoin_range_X
      have hker := AlgebraRetract.ker_eq_span (graphProj_comp_incl (0 : τ → Amb A σ))
        (Set.range (X : σ ⊕ τ → Amb A (σ ⊕ τ))) hgen
      rw [hker]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      cases i with
      | inl i =>
        change X (Sum.inl i) - incl A σ τ (graphProj 0 (X (Sum.inl i))) ∈ _
        rw [graphProj_X_inl, incl_X, sub_self]
        exact Ideal.zero_mem _
      | inr t =>
        change X (Sum.inr t) - incl A σ τ (graphProj 0 (X (Sum.inr t))) ∈ _
        rw [graphProj_X_inr]
        change X (Sum.inr t) - incl A σ τ 0 ∈ _
        rw [map_zero, sub_zero]
        exact Ideal.subset_span ⟨t, rfl⟩
    have : f = incl A σ τ (graphProj 0 f) + (f - incl A σ τ (graphProj 0 f)) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
      (Ideal.mem_sup_right (hspan hker))
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, mem_graphIdeal_iff]
    change graphProj 0 (incl A σ τ r) ∈ I
    rwa [graphProj_incl]
  · rw [Ideal.span_le]
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, mem_graphIdeal_iff, graphProj_X_inr]
    change (0 : Amb A σ) ∈ I
    exact Ideal.zero_mem _

/-! #### Transport of the product formula to the `σ ⊕ τ` coordinates -/

variable (A σ τ)

/-- The identification `A[x_σ, y_τ] ≅ (A[x_σ])[y_τ]`. -/
def sumEquiv : Amb A (σ ⊕ τ) ≃ₐ[A] MvPolynomial τ (Amb A σ) :=
  (renameEquiv A (Equiv.sumComm σ τ)).trans (sumAlgEquiv A τ σ)

variable {A σ τ}

@[simp]
theorem sumEquiv_C (a : A) : sumEquiv A σ τ (C a) = C (C a) := by
  rw [sumEquiv]
  change sumAlgEquiv A τ σ (rename (Equiv.sumComm σ τ) (C a)) = _
  rw [rename_C]
  exact sumAlgEquiv_C_inl _ _ _ a

@[simp]
theorem graphProj_C (g : τ → Amb A σ) (a : A) : graphProj g (C a) = C a := by
  rw [graphProj, aeval_C, algebraMap_eq]

@[simp]
theorem sumEquiv_X_inl (i : σ) : sumEquiv A σ τ (X (Sum.inl i)) = C (X i) := by
  rw [sumEquiv]
  change sumAlgEquiv A τ σ (rename (Equiv.sumComm σ τ) (X (Sum.inl i))) = _
  rw [rename_X]
  exact sumAlgEquiv_X_inr _ _ _ i

@[simp]
theorem sumEquiv_X_inr (t : τ) : sumEquiv A σ τ (X (Sum.inr t)) = X t := by
  rw [sumEquiv]
  change sumAlgEquiv A τ σ (rename (Equiv.sumComm σ τ) (X (Sum.inr t))) = _
  rw [rename_X]
  exact sumAlgEquiv_X_inl _ _ _ t

theorem sumEquiv_incl (f : Amb A σ) : sumEquiv A σ τ (incl A σ τ f) = C f := by
  have hcomp : (sumEquiv A σ τ).toAlgHom.comp (incl A σ τ) =
      IsScalarTower.toAlgHom A (Amb A σ) (MvPolynomial τ (Amb A σ)) := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rw [AlgHom.comp_apply, incl_X]
    change sumEquiv A σ τ (X (Sum.inl i)) = algebraMap (Amb A σ) (MvPolynomial τ (Amb A σ)) (X i)
    rw [sumEquiv_X_inl, algebraMap_eq]
  exact DFunLike.congr_fun hcomp f

theorem sumEquiv_symm_C (f : Amb A σ) : (sumEquiv A σ τ).symm (C f) = incl A σ τ f := by
  rw [AlgEquiv.symm_apply_eq, sumEquiv_incl]

theorem sumEquiv_symm_X (t : τ) : (sumEquiv A σ τ).symm (X t) = X (Sum.inr t) := by
  rw [AlgEquiv.symm_apply_eq, sumEquiv_X_inr]

theorem constantCoeff_sumEquiv (f : Amb A (σ ⊕ τ)) :
    constantCoeff (sumEquiv A σ τ f) = graphProj (0 : τ → Amb A σ) f := by
  have hcomp : (constantCoeff : MvPolynomial τ (Amb A σ) →+* Amb A σ).comp
      (sumEquiv A σ τ).toAlgHom.toRingHom = (graphProj (0 : τ → Amb A σ)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun v ↦ ?_)
    · change constantCoeff (sumEquiv A σ τ (C a)) = graphProj (0 : τ → Amb A σ) (C a)
      rw [sumEquiv_C, graphProj_C, constantCoeff_C]
    · cases v with
      | inl i =>
        change constantCoeff (sumEquiv A σ τ (X (Sum.inl i))) =
          graphProj (0 : τ → Amb A σ) (X (Sum.inl i))
        rw [sumEquiv_X_inl, constantCoeff_C, graphProj_X_inl]
      | inr t =>
        change constantCoeff (sumEquiv A σ τ (X (Sum.inr t))) =
          graphProj (0 : τ → Amb A σ) (X (Sum.inr t))
        rw [sumEquiv_X_inr, constantCoeff_X, graphProj_X_inr]
        rfl
  exact DFunLike.congr_fun hcomp f

variable (A σ τ)

/-- The identification `A[x_σ, y_τ] ≅ (A[x_σ])[y_τ]` as a ring isomorphism. -/
def sumRingEquiv : Amb A (σ ⊕ τ) ≃+* MvPolynomial τ (Amb A σ) :=
  (sumEquiv A σ τ).toRingEquiv

variable {A σ τ}

@[simp]
theorem sumRingEquiv_apply (f : Amb A (σ ⊕ τ)) : sumRingEquiv A σ τ f = sumEquiv A σ τ f :=
  rfl

@[simp]
theorem sumRingEquiv_symm_C (f : Amb A σ) :
    (sumRingEquiv A σ τ).symm (C f) = incl A σ τ f :=
  sumEquiv_symm_C f

@[simp]
theorem sumRingEquiv_symm_X (t : τ) :
    (sumRingEquiv A σ τ).symm (X t) = X (Sum.inr t) :=
  sumEquiv_symm_X t

theorem graphIdeal_zero_eq_comap (I : Ideal (Amb A σ)) :
    graphIdeal A σ τ I 0 =
      Ideal.comap ((sumRingEquiv A σ τ : Amb A (σ ⊕ τ) ≃+* MvPolynomial τ (Amb A σ)) :
        Amb A (σ ⊕ τ) →+* MvPolynomial τ (Amb A σ)) (polyExt τ I) := by
  refine Ideal.ext fun f ↦ ?_
  rw [Ideal.mem_comap, mem_polyExt_iff, mem_graphIdeal_iff]
  change graphProj 0 f ∈ I ↔ constantCoeff (sumEquiv A σ τ f) ∈ I
  rw [constantCoeff_sumEquiv]

theorem map_sumRingEquiv_graphIdeal (I : Ideal (Amb A σ)) :
    Ideal.map ((sumRingEquiv A σ τ : Amb A (σ ⊕ τ) ≃+* MvPolynomial τ (Amb A σ)) :
      Amb A (σ ⊕ τ) →+* MvPolynomial τ (Amb A σ)) (graphIdeal A σ τ I 0) = polyExt τ I := by
  rw [graphIdeal_zero_eq_comap]
  exact Ideal.map_comap_of_surjective _ (sumRingEquiv A σ τ).surjective _

theorem incl_mem_graphIdeal {I : Ideal (Amb A σ)} {x : Amb A σ} (hx : x ∈ I) :
    incl A σ τ x ∈ graphIdeal A σ τ I 0 := by
  rw [mem_graphIdeal_iff, graphProj_incl]
  exact hx

theorem X_inr_mem_graphIdeal {I : Ideal (Amb A σ)} (t : τ) :
    (X (Sum.inr t) : Amb A (σ ⊕ τ)) ∈ graphIdeal A σ τ I 0 := by
  rw [mem_graphIdeal_iff, graphProj_X_inr]
  change (0 : Amb A σ) ∈ I
  exact Ideal.zero_mem _

/-- **The normal cone of a refinement is a product.**  For the zero-section embedding
`U ↪ M' = 𝔸^{σ⊕τ}` refining `U ↪ M = 𝔸^σ`, the affine normal cone is
`C_{U/M'} = C_{U/M} × 𝔸^τ`: its coordinate ring `gr_{I'}` is the polynomial ring
`gr_I(R)[z_τ]` over the coordinate ring of `C_{U/M}`. -/
def refinementEquiv (I : Ideal (Amb A σ)) :
    MvPolynomial τ (Gr I) ≃+* Gr (graphIdeal A σ τ I 0) :=
  (prodEquiv (τ := τ) (I := I)).trans
    (grEquivOfEquiv (graphIdeal A σ τ I 0) (polyExt τ I) (sumRingEquiv A σ τ)
      (map_sumRingEquiv_graphIdeal I)).symm

theorem refinementEquiv_apply (I : Ideal (Amb A σ)) (w : MvPolynomial τ (Gr I)) :
    refinementEquiv I w =
      grMapOfEq (polyExt τ I) (((sumRingEquiv A σ τ).symm :
          MvPolynomial τ (Amb A σ) ≃+* Amb A (σ ⊕ τ)) :
          MvPolynomial τ (Amb A σ) →+* Amb A (σ ⊕ τ)) (graphIdeal A σ τ I 0)
        (map_symm_of_map _ _ _ (map_sumRingEquiv_graphIdeal I)) (prodMap τ I w) :=
  rfl

/-! #### The comparison map on generators -/

variable {I : Ideal (Amb A σ)}

@[simp]
theorem refinementEquiv_C_algebraMap (r : Amb A σ) :
    refinementEquiv I (C (algebraMap (Amb A σ) (Gr I) r)) =
      algebraMap (Amb A (σ ⊕ τ)) (Gr (graphIdeal A σ τ I 0)) (incl A σ τ r) := by
  rw [refinementEquiv_apply, prodMap_C, grIncl_algebraMap, grMapOfEq_algebraMap]
  change algebraMap _ _ ((sumRingEquiv A σ τ).symm (C r)) = _
  rw [sumRingEquiv_symm_C]

@[simp]
theorem refinementEquiv_C_degreeOneRaw (x : I) :
    refinementEquiv I (C (degreeOneRaw (Amb A σ) I x)) =
      degreeOneRaw (Amb A (σ ⊕ τ)) (graphIdeal A σ τ I 0)
        ⟨incl A σ τ (x : Amb A σ), incl_mem_graphIdeal x.2⟩ := by
  rw [refinementEquiv_apply, prodMap_C, grIncl_degreeOneRaw, grMapOfEq_degreeOneRaw]
  exact congrArg _ (Subtype.ext (sumRingEquiv_symm_C (x : Amb A σ)))

@[simp]
theorem refinementEquiv_X (t : τ) :
    refinementEquiv I (X t) =
      degreeOneRaw (Amb A (σ ⊕ τ)) (graphIdeal A σ τ I 0)
        ⟨X (Sum.inr t), X_inr_mem_graphIdeal t⟩ := by
  rw [refinementEquiv_apply, prodMap_X, zVar, grMapOfEq_degreeOneRaw]
  exact congrArg _ (Subtype.ext (sumRingEquiv_symm_X t))

@[simp]
theorem refinementEquiv_toRingHom_apply (w : MvPolynomial τ (Gr I)) :
    (refinementEquiv I).toRingHom w = refinementEquiv I w :=
  rfl

theorem refinementEquiv_C_degreeOne (x : I) :
    refinementEquiv I (C (Ideal.Quotient.mk _ (degreeOneRees (Amb A σ) I x))) =
      Ideal.Quotient.mk _ (degreeOneRees (Amb A (σ ⊕ τ)) (graphIdeal A σ τ I 0)
        ⟨incl A σ τ (x : Amb A σ), incl_mem_graphIdeal x.2⟩) :=
  refinementEquiv_C_degreeOneRaw x

theorem refinementEquiv_X_mk (t : τ) :
    refinementEquiv I (X t) =
      Ideal.Quotient.mk _ (degreeOneRees (Amb A (σ ⊕ τ)) (graphIdeal A σ τ I 0)
        ⟨X (Sum.inr t), X_inr_mem_graphIdeal t⟩) :=
  refinementEquiv_X t


/-! #### Compatibility of the Taylor derivation with the refinement -/

theorem taylor_incl (x : Amb A σ) :
    ConeTranslation.taylor A (σ ⊕ τ) (incl A σ τ x) =
      rename Sum.inl (MvPolynomial.map (incl A σ τ : Amb A σ →+* Amb A (σ ⊕ τ))
        (ConeTranslation.taylor A σ x)) := by
  induction x using MvPolynomial.induction_on with
  | C a =>
    rw [incl_C, ConeTranslation.taylor_C, ConeTranslation.taylor_C, map_zero, map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
    rw [map_mul, incl_X, ConeTranslation.taylor_mul, ConeTranslation.taylor_X,
      ConeTranslation.taylor_mul, ConeTranslation.taylor_X, map_add, map_add, map_mul, map_mul,
      map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, rename_C, rename_X, hf,
      MvPolynomial.map_C, rename_C]
    simp only [AlgHom.coe_toRingHom, incl_X]

theorem eval₂_taylor_incl {B : Type u} [CommSemiring B] (ψ : Amb A (σ ⊕ τ) →+* B)
    (v : σ ⊕ τ → B) (x : Amb A σ) :
    eval₂ ψ v (ConeTranslation.taylor A (σ ⊕ τ) (incl A σ τ x)) =
      eval₂ (ψ.comp (incl A σ τ : Amb A σ →+* Amb A (σ ⊕ τ))) (v ∘ Sum.inl)
        (ConeTranslation.taylor A σ x) := by
  rw [taylor_incl, eval₂_rename, eval₂_map]

theorem translatePoint_degreeOneRaw {A σ : Type u} [CommRing A] (J : Ideal (Amb A σ))
    {B : Type u} [CommRing B] (φ : Gr J →+* B) (v : σ → B) (y : Amb A σ) (hy : y ∈ J) :
    ConeTranslation.translatePoint J φ v (degreeOneRaw (Amb A σ) J ⟨y, hy⟩) =
      φ (degreeOneRaw (Amb A σ) J ⟨y, hy⟩) +
        eval₂ (φ.comp (algebraMap (Amb A σ) (Gr J))) v (ConeTranslation.taylor A σ y) :=
  ConeTranslation.translatePoint_degreeOne J φ v ⟨y, hy⟩

/-! #### Equivariance of the product decomposition -/

set_option maxHeartbeats 1600000 in
-- The unifier has to match the composite isomorphism `refinementEquiv` (a transport of the
-- polynomial-ring presentation along `sumRingEquiv`) against the quotient-of-a-subalgebra
-- presentation of `gr`, which is expensive; the same phenomenon occurs in `ConeTranslation`.
/-- **Equivariance.**  On `B`-points, the translation action of `T_{M'} = 𝔸^{σ⊕τ}` on
`C_{U/M'} = C_{U/M} × 𝔸^τ` is the product of the translation action of `𝔸^σ` on `C_{U/M}`
(through the first factor) and of the translation action of `𝔸^τ` on itself (through the
second factor: the coordinate `z_t` is translated by `v (inr t)`). -/
theorem translatePoint_comp_refinementEquiv {B : Type u} [CommRing B]
    (φ : Gr (graphIdeal A σ τ I 0) →+* B) (v : σ ⊕ τ → B) :
    (ConeTranslation.translatePoint (graphIdeal A σ τ I 0) φ v).comp
        (refinementEquiv I).toRingHom =
      eval₂Hom (ConeTranslation.translatePoint I
          (φ.comp ((refinementEquiv I).toRingHom.comp (C : Gr I →+* MvPolynomial τ (Gr I))))
          (v ∘ Sum.inl))
        fun t ↦ φ (refinementEquiv I (X t)) + v (Sum.inr t) := by
  have hbase : ∀ r : Amb A σ, φ (refinementEquiv I (C (algebraMap (Amb A σ) (Gr I) r))) =
      φ (algebraMap (Amb A (σ ⊕ τ)) (Gr (graphIdeal A σ τ I 0)) (incl A σ τ r)) := fun r ↦ by
    rw [refinementEquiv_C_algebraMap]
  have hcomp : (φ.comp (algebraMap (Amb A (σ ⊕ τ))
        (Gr (graphIdeal A σ τ I 0)))).comp (incl A σ τ : Amb A σ →+* Amb A (σ ⊕ τ)) =
      (φ.comp ((refinementEquiv I).toRingHom.comp
        (C : Gr I →+* MvPolynomial τ (Gr I)))).comp (algebraMap (Amb A σ) (Gr I)) :=
    RingHom.ext fun r ↦ (hbase r).symm
  have key : (ConeTranslation.translatePoint (graphIdeal A σ τ I 0) φ v).comp
      ((refinementEquiv I).toRingHom.comp (C : Gr I →+* MvPolynomial τ (Gr I))) =
      ConeTranslation.translatePoint I (φ.comp ((refinementEquiv I).toRingHom.comp
        (C : Gr I →+* MvPolynomial τ (Gr I)))) (v ∘ Sum.inl) := by
    refine ConeTranslation.gr_ringHom_ext I (fun r ↦ ?_) fun x ↦ ?_
    · simp only [RingHom.comp_apply, refinementEquiv_toRingHom_apply]
      rw [refinementEquiv_C_algebraMap, ConeTranslation.translatePoint_algebraMap,
        ConeTranslation.translatePoint_algebraMap]
      simp only [RingHom.comp_apply, refinementEquiv_toRingHom_apply,
        refinementEquiv_C_algebraMap]
    · simp only [RingHom.comp_apply, refinementEquiv_toRingHom_apply]
      rw [refinementEquiv_C_degreeOne, ConeTranslation.translatePoint_degreeOne,
        ConeTranslation.translatePoint_degreeOne]
      simp only [RingHom.comp_apply, refinementEquiv_toRingHom_apply, refinementEquiv_C_degreeOne]
      rw [eval₂_taylor_incl, hcomp]
  refine MvPolynomial.ringHom_ext (fun w ↦ ?_) fun t ↦ ?_
  · rw [RingHom.comp_apply, eval₂Hom_C]
    exact DFunLike.congr_fun key w
  · rw [RingHom.comp_apply, eval₂Hom_X']
    simp only [refinementEquiv_toRingHom_apply]
    rw [refinementEquiv_X_mk, ConeTranslation.translatePoint_degreeOne]
    simp only [ConeTranslation.taylor_X, eval₂_X]

theorem translatePoint_comp_refinementEquiv_comp_C {B : Type u} [CommRing B]
    (φ : Gr (graphIdeal A σ τ I 0) →+* B) (v : σ ⊕ τ → B) :
    ConeTranslation.translatePoint I
        (φ.comp ((refinementEquiv I).toRingHom.comp (C : Gr I →+* MvPolynomial τ (Gr I))))
        (v ∘ Sum.inl) =
      (ConeTranslation.translatePoint (graphIdeal A σ τ I 0) φ v).comp
        ((refinementEquiv I).toRingHom.comp (C : Gr I →+* MvPolynomial τ (Gr I))) := by
  refine RingHom.ext fun w ↦ ?_
  have h := DFunLike.congr_fun (translatePoint_comp_refinementEquiv (I := I) φ v) (C w)
  rw [RingHom.comp_apply, eval₂Hom_C] at h
  exact h.symm

theorem translatePoint_refinementEquiv_X {B : Type u} [CommRing B]
    (φ : Gr (graphIdeal A σ τ I 0) →+* B) (v : σ ⊕ τ → B) (t : τ) :
    ConeTranslation.translatePoint (graphIdeal A σ τ I 0) φ v (refinementEquiv I (X t)) =
      φ (refinementEquiv I (X t)) + v (Sum.inr t) := by
  have h := DFunLike.congr_fun (translatePoint_comp_refinementEquiv (I := I) φ v) (X t)
  rw [RingHom.comp_apply, eval₂Hom_X', refinementEquiv_toRingHom_apply] at h
  exact h


end Graph

/-! ### The quotient groupoids and the refinement equivalence -/

section QuotientGroupoid

open CategoryTheory ConeTranslation

variable {A : Type u} [CommRing A] {σ τ : Type u}

/-- The `B`-points of the quotient stack `[C_{U/M} / T_M|_U]` in the polynomial model: the
action groupoid of the translation action of the `B`-points `σ → B` of the tangent bundle on
the `B`-points of the affine normal cone. -/
@[ext]
structure ConeGroupoid (I : Ideal (Amb A σ)) (B : Type u) [CommRing B] where
  /-- The underlying `B`-point of the affine normal cone. -/
  point : Gr I →+* B

namespace ConeGroupoid

variable {I : Ideal (Amb A σ)} {B : Type u} [CommRing B]

/-- An arrow of the quotient groupoid: a `B`-point of the tangent bundle `T_M|_U = U × 𝔸^σ`
carrying the source to the target. -/
@[ext]
structure Hom (x y : ConeGroupoid I B) where
  /-- The translating tangent vector. -/
  val : σ → B
  /-- It carries the source point to the target point. -/
  translate_eq : translatePoint I x.point val = y.point

/-- The action groupoid structure on the `B`-points of `[C_{U/M}/T_M|_U]`. -/
instance instCategory : Category (ConeGroupoid I B) where
  Hom := Hom
  id x := ⟨0, translatePoint_zero I x.point⟩
  comp f g := ⟨f.val + g.val, by
    rw [← translatePoint_add, f.translate_eq, g.translate_eq]⟩
  id_comp f := Hom.ext (zero_add _)
  comp_id f := Hom.ext (add_zero _)
  assoc f g h := Hom.ext (add_assoc _ _ _)

@[simp]
theorem id_val (x : ConeGroupoid I B) : (𝟙 x : x ⟶ x).val = 0 :=
  rfl

@[simp]
theorem comp_val {x y z : ConeGroupoid I B} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = f.val + g.val :=
  rfl

/-- Every arrow of the action groupoid is invertible. -/
instance instGroupoid : Groupoid (ConeGroupoid I B) where
  inv f := ⟨-f.val, by
    rw [← f.translate_eq, translatePoint_add, add_neg_cancel, translatePoint_zero]⟩
  inv_comp f := Hom.ext (neg_add_cancel _)
  comp_inv f := Hom.ext (add_neg_cancel _)

end ConeGroupoid

/-- The functor `[C_{U/M'}/T_{M'}|_U](B) → [C_{U/M}/T_M|_U](B)` induced by the projection
`M' = 𝔸^{σ⊕τ} → M = 𝔸^σ`: on points it is the projection `C_{U/M} × 𝔸^τ → C_{U/M}` and on
arrows the projection `𝔸^{σ⊕τ} → 𝔸^σ` of tangent bundles. -/
def refinementFunctor (I : Ideal (Amb A σ)) (τ : Type u) (B : Type u) [CommRing B] :
    ConeGroupoid (graphIdeal A σ τ I 0) B ⥤ ConeGroupoid I B where
  obj x := ⟨x.point.comp ((refinementEquiv I).toRingHom.comp
    (C : Gr I →+* MvPolynomial τ (Gr I)))⟩
  map f := ⟨f.val ∘ Sum.inl, by
    rw [translatePoint_comp_refinementEquiv_comp_C, f.translate_eq]⟩
  map_id x := ConeGroupoid.Hom.ext rfl
  map_comp f g := ConeGroupoid.Hom.ext rfl

@[simp]
theorem refinementFunctor_obj_point (I : Ideal (Amb A σ)) (τ : Type u) (B : Type u) [CommRing B]
    (x : ConeGroupoid (graphIdeal A σ τ I 0) B) :
    ((refinementFunctor I τ B).obj x).point =
      x.point.comp ((refinementEquiv I).toRingHom.comp
        (C : Gr I →+* MvPolynomial τ (Gr I))) :=
  rfl

@[simp]
theorem refinementFunctor_map_val (I : Ideal (Amb A σ)) (τ : Type u) (B : Type u) [CommRing B]
    {x y : ConeGroupoid (graphIdeal A σ τ I 0) B} (f : x ⟶ y) :
    ((refinementFunctor I τ B).map f).val = f.val ∘ Sum.inl :=
  rfl

set_option maxHeartbeats 1600000 in
-- As for `translatePoint_comp_refinementEquiv`, the unifier has to see through the composite
-- isomorphism `refinementEquiv` and the quotient presentation of `gr`.
/-- **The refinement lemma in the polynomial model (the gate statement of Layer 5).**  For a
refinement `(U, M' = 𝔸^{σ⊕τ}) → (U, M = 𝔸^σ)` of local embeddings, given by the zero-section
(equivalently, after `map_shear_graphIdeal`, by any graph) embedding, the induced functor
`[C_{U/M'}/T_{M'}|_U](B) → [C_{U/M}/T_M|_U](B)` is an equivalence of groupoids for every test
algebra `B`: the pair `C_{U/M} ⊆ T_M|_U` is the quotient of `C_{U/M'} ⊆ T_{M'}|_U` by the
relative tangent bundle `T_{M'/M}|_U = 𝔸^τ`. -/
theorem refinementQuotientEquivalence (I : Ideal (Amb A σ)) (τ : Type u) (B : Type u)
    [CommRing B] : (refinementFunctor I τ B).IsEquivalence where
  faithful := ⟨fun {x y f g} hfg ↦ by
    have hval : f.val ∘ Sum.inl = g.val ∘ Sum.inl := congrArg ConeGroupoid.Hom.val hfg
    refine ConeGroupoid.Hom.ext (funext fun i ↦ ?_)
    cases i with
    | inl j => exact congrFun hval j
    | inr t =>
      have hf := congrArg (fun z ↦ z (refinementEquiv I (X t))) f.translate_eq
      have hg := congrArg (fun z ↦ z (refinementEquiv I (X t))) g.translate_eq
      simp only [translatePoint_refinementEquiv_X] at hf hg
      exact add_left_cancel (hf.trans hg.symm)⟩
  full := ⟨fun {x y} k ↦ by
    refine ⟨⟨Sum.elim k.val fun t ↦ y.point (refinementEquiv I (X t)) -
      x.point (refinementEquiv I (X t)), ?_⟩, ConeGroupoid.Hom.ext rfl⟩
    have hk := k.translate_eq
    refine RingHom.ext fun z ↦ ?_
    obtain ⟨w, rfl⟩ := (refinementEquiv I).surjective z
    have hring : (translatePoint (graphIdeal A σ τ I 0) x.point
        (Sum.elim k.val fun t ↦ y.point (refinementEquiv I (X t)) -
          x.point (refinementEquiv I (X t)))).comp (refinementEquiv I).toRingHom =
        y.point.comp (refinementEquiv I).toRingHom := by
      rw [translatePoint_comp_refinementEquiv]
      refine MvPolynomial.ringHom_ext (fun u ↦ ?_) fun t ↦ ?_
      · rw [eval₂Hom_C, RingHom.comp_apply, refinementEquiv_toRingHom_apply]
        exact congrArg (fun z ↦ z u) hk
      · rw [eval₂Hom_X', RingHom.comp_apply, refinementEquiv_toRingHom_apply, Sum.elim_inr]
        ring
    exact DFunLike.congr_fun hring w⟩
  essSurj := ⟨fun y ↦ by
    refine ⟨⟨(eval₂Hom y.point fun _ : τ ↦ (0 : B)).comp (refinementEquiv I).symm.toRingHom⟩,
      ⟨eqToIso (ConeGroupoid.ext ?_)⟩⟩
    rw [refinementFunctor_obj_point, RingHom.comp_assoc]
    have hid : ((refinementEquiv I).symm.toRingHom).comp
        ((refinementEquiv I).toRingHom.comp (C : Gr I →+* MvPolynomial τ (Gr I))) =
        (C : Gr I →+* MvPolynomial τ (Gr I)) :=
      RingHom.ext fun w ↦ (refinementEquiv I).symm_apply_apply (C w)
    rw [hid]
    exact RingHom.ext fun u ↦ eval₂Hom_C _ _ u⟩

end QuotientGroupoid

end

end ConeRefinement

end GromovWitten.AlgebraicGeometry
