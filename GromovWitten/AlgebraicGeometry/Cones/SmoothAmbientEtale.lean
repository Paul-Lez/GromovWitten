/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.SmoothAmbient

/-!
# Taylor expansion along a formally étale ambient chart

`Cones/ConeTranslation.lean` constructs the translation coaction of the tangent bundle
`T_M = 𝔸^σ × M` on the affine normal cone for the *polynomial* ambient scheme
`M = 𝔸^σ_A = Spec P`, `P = Amb A σ = A[x_i]`, and `Cones/SmoothAmbient.lean` transports it to
a flat `P`-algebra `R` for the *extended* ideals `I·R`.  A general closed subscheme of an étale
chart `Spec R → 𝔸^σ` is cut out by an ideal `J ⊆ R` which is not extended from `P`, so the
transport by base change does not apply.

This file provides the missing ingredient: the **Taylor expansion**

`taylor n : R →ₐ[P] Shift A σ R n`,  `Shift A σ R n = R[ε_σ]/(ε)^{n+1}`,

which exists and is unique whenever `R` is a formally étale `P`-algebra.

## The shifted polynomial extension

`Shift A σ R n` is a type synonym for `R[ε_σ]/(ε)^{n+1}` carrying the `P`-algebra structure

`x_i ↦ x_i + ε_i`  (`shiftHom`, `instAlgebraShift`),

which is *not* the one obtained from `P → R → R[ε]`; the type synonym exists precisely to keep
the two apart.  The ideal `(ε)` is nilpotent in `Shift A σ R n` and the reduction
`red : Shift A σ R n →ₐ[P] R`, `ε ↦ 0`, is a surjective `P`-algebra map with nilpotent kernel
(`redAlg`, `redAlg_surjective`, `isNilpotent_ker_redAlg`).  Formal étaleness therefore produces a
unique section `taylor n` of `red` (`Algebra.FormallySmooth.liftOfSurjective`,
`Algebra.FormallyUnramified.lift_unique'`):

* `redAlg_taylor : red (taylor n r) = r`, i.e. `taylor n r ≡ r mod (ε)`;
* `taylor_unique`: any `P`-algebra map `R →ₐ[P] Shift A σ R n` reducing to the identity is
  `taylor n`;
* `trunc_comp_taylor`: the `taylor n` are compatible with the truncations
  `Shift A σ R n → Shift A σ R m`, `m ≤ n`;
* `taylor_self` and `taylor_X`: for `R = P` the Taylor expansion is the substitution
  `x_i ↦ x_i + ε_i`, as it must be.

## The degree-`k` classes on the associated graded ring

For an arbitrary ideal `J ⊆ R` write `I' = polyExt σ J = J·R[ε] + (ε)` for the ideal of the
graph embedding of the refinement (`Cones/RefinementQuotient.lean`), so that
`gr_{I'}(R[ε]) ≅ gr_J(R)[z_σ]` by `ConeRefinement.prodEquiv`.  The key unconditional inclusion is

* `taylor_mem_map_polyExt_pow : x ∈ J^k → taylor n x ∈ (I'^k).map (shiftMk n)`,

which says that `taylor` respects the `J`-adic filtration, and it makes the degree-`k` class

* `taylorClass n k : J^k → gr_{I'}(R[ε])`

well defined (`taylorClass_spec`, independent of the chosen lift).  These classes are additive
(`taylorClass_add`), multiplicative across degrees (`taylorClass_mul`), kill `J^{k+1}`
(`taylorClass_eq_zero`), and in degree zero and one are computed by `taylorClass_zero` and
`taylorClass_one`.

## The tangent coaction

Summing the degree-`k` classes over the coefficients of a Rees element gives a ring map
`reesPhi : Rees_J(R) → gr_{I'}(R[ε])` (`phiPoly`, `phiPoly_add`, `phiPoly_monomial_mul`,
`phiPoly_mul`) which kills `J·Rees_J(R)` (`map_le_ker_reesPhi`) and therefore descends to

* `grPhi : gr_J(R) →+* gr_{I'}(R[ε])`, and, in the coordinates of `ConeRefinement.prodEquiv`,
* `coactionEtale : gr_J(R) →+* gr_J(R)[z_σ]`,

the tangent coaction of the ambient chart.  It is computed on the degree-`k` classes by
`grPhi_degRaw` and `coactionEtale_degRaw`, is the identity in degree zero
(`grPhi_algebraMap`, `coactionEtale_algebraMap`), is the derivative in degree one
(`grPhi_degreeOneRaw`), and satisfies the counit law `counitMap_comp_grPhi`: setting `ε = 0`
recovers the identity of `gr_J(R)`.  Coassociativity, the induced action on `B`-points and the
equivariance of `C_{U/M} ↪ N_{U/M}` are *not* proved here.
-/

namespace GromovWitten.AlgebraicGeometry

namespace EtaleAmbient

universe u

noncomputable section

open MvPolynomial ConeTranslation ConeRefinement AffineNormalCone

/-! ### The augmentation ideal of `R[ε_σ]` -/

section Eps

variable (σ : Type u) (R : Type u) [CommRing R]

/-- The augmentation ideal `(ε_i : i ∈ σ)` of `R[ε_σ]`, i.e. the kernel of `ε ↦ 0`.  It is the
ideal `polyExt σ ⊥` of `Cones/RefinementQuotient.lean` for the zero ideal of `R`. -/
def epsIdeal : Ideal (MvPolynomial σ R) := ConeRefinement.polyExt σ (⊥ : Ideal R)

variable {σ R}

theorem mem_epsIdeal_iff {f : MvPolynomial σ R} : f ∈ epsIdeal σ R ↔ constantCoeff f = 0 :=
  Iff.rfl

theorem X_mem_epsIdeal (i : σ) : (X i : MvPolynomial σ R) ∈ epsIdeal σ R :=
  ConeRefinement.X_mem_polyExt i

/-- The augmentation ideal is contained in every `polyExt σ J`. -/
theorem epsIdeal_le_polyExt (J : Ideal R) : epsIdeal σ R ≤ ConeRefinement.polyExt σ J :=
  fun _ hf ↦ by
    rw [ConeRefinement.mem_polyExt_iff, mem_epsIdeal_iff.mp hf]
    exact Ideal.zero_mem _

/-- Powers of the augmentation ideal are contained in the corresponding powers of
`polyExt σ J`. -/
theorem epsIdeal_pow_le_polyExt_pow (J : Ideal R) (k : ℕ) :
    epsIdeal σ R ^ k ≤ ConeRefinement.polyExt σ J ^ k :=
  Ideal.pow_right_mono (epsIdeal_le_polyExt J) k

variable (σ R)

/-- Elements of `(ε)^{n+1}` have vanishing constant term. -/
theorem constantCoeff_eq_zero_of_mem (n : ℕ) (a : MvPolynomial σ R)
    (ha : a ∈ epsIdeal σ R ^ (n + 1)) : constantCoeff a = 0 :=
  mem_epsIdeal_iff.mp (Ideal.pow_le_self (Nat.succ_ne_zero n) ha)

end Eps

/-! ### The shifted truncated polynomial extension -/

section Shift

variable (A : Type u) [CommRing A] (σ : Type u) (R : Type u) [CommRing R]
  [Algebra (Amb A σ) R]

/-- The *shifted* `P`-algebra structure on `R[ε_σ]`, `P = A[x_σ]`: the ring map sending the
ambient coordinate `x_i` to `x_i + ε_i`. -/
def shiftHom : Amb A σ →+* MvPolynomial σ R :=
  eval₂Hom (C.comp ((algebraMap (Amb A σ) R).comp C))
    fun i ↦ C (algebraMap (Amb A σ) R (X i)) + X i

@[simp]
theorem shiftHom_C (a : A) :
    shiftHom A σ R (C a) = C (algebraMap (Amb A σ) R (C a)) :=
  eval₂Hom_C _ _ a

@[simp]
theorem shiftHom_X (i : σ) :
    shiftHom A σ R (X i) = C (algebraMap (Amb A σ) R (X i)) + X i :=
  eval₂Hom_X' _ _ i

/-- Setting `ε = 0` in the shifted structure recovers the given `P`-algebra structure on `R`. -/
theorem constantCoeff_shiftHom (p : Amb A σ) :
    constantCoeff (shiftHom A σ R p) = algebraMap (Amb A σ) R p := by
  have h : (constantCoeff : MvPolynomial σ R →+* R).comp (shiftHom A σ R) =
      algebraMap (Amb A σ) R := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · simp
    · simp
  exact RingHom.congr_fun h p

/-- `R[ε_σ]` truncated at order `n`, i.e. `R[ε_σ]/(ε)^{n+1}`, as a type synonym carrying the
shifted `P`-algebra structure `x_i ↦ x_i + ε_i` of `shiftHom`. -/
def Shift (A : Type u) [CommRing A] (σ R : Type u) [CommRing R] [Algebra (Amb A σ) R]
    (n : ℕ) : Type u :=
  MvPolynomial σ R ⧸ epsIdeal σ R ^ (n + 1)

/-- The truncated polynomial extension is a commutative ring. -/
instance instCommRingShift (n : ℕ) : CommRing (Shift A σ R n) :=
  inferInstanceAs (CommRing (MvPolynomial σ R ⧸ epsIdeal σ R ^ (n + 1)))

/-- The quotient map `R[ε_σ] → R[ε_σ]/(ε)^{n+1}`. -/
def shiftMk (n : ℕ) : MvPolynomial σ R →+* Shift A σ R n :=
  Ideal.Quotient.mk (epsIdeal σ R ^ (n + 1))

theorem shiftMk_surjective (n : ℕ) : Function.Surjective (shiftMk A σ R n) :=
  Ideal.Quotient.mk_surjective

theorem shiftMk_eq_zero_iff (n : ℕ) {f : MvPolynomial σ R} :
    shiftMk A σ R n f = 0 ↔ f ∈ epsIdeal σ R ^ (n + 1) :=
  Ideal.Quotient.eq_zero_iff_mem

theorem shiftMk_eq_iff (n : ℕ) {f g : MvPolynomial σ R} :
    shiftMk A σ R n f = shiftMk A σ R n g ↔ f - g ∈ epsIdeal σ R ^ (n + 1) :=
  Ideal.Quotient.mk_eq_mk_iff_sub_mem f g

/-- The shifted `P`-algebra structure on the truncated extension. -/
instance instAlgebraShift (n : ℕ) : Algebra (Amb A σ) (Shift A σ R n) :=
  RingHom.toAlgebra ((shiftMk A σ R n).comp (shiftHom A σ R))

theorem algebraMap_shift_eq (n : ℕ) (p : Amb A σ) :
    algebraMap (Amb A σ) (Shift A σ R n) p = shiftMk A σ R n (shiftHom A σ R p) :=
  rfl

/-- The reduction `ε ↦ 0` from the truncated extension back to `R`. -/
def redHom (n : ℕ) : Shift A σ R n →+* R :=
  Ideal.Quotient.lift (epsIdeal σ R ^ (n + 1)) (constantCoeff : MvPolynomial σ R →+* R)
    (constantCoeff_eq_zero_of_mem σ R n)

@[simp]
theorem redHom_shiftMk (n : ℕ) (f : MvPolynomial σ R) :
    redHom A σ R n (shiftMk A σ R n f) = constantCoeff f :=
  rfl

theorem redHom_algebraMap (n : ℕ) (p : Amb A σ) :
    redHom A σ R n (algebraMap (Amb A σ) (Shift A σ R n) p) = algebraMap (Amb A σ) R p := by
  rw [algebraMap_shift_eq, redHom_shiftMk, constantCoeff_shiftHom]

/-- The reduction `ε ↦ 0` as a `P`-algebra map, for the shifted structure on the source. -/
def redAlg (n : ℕ) : Shift A σ R n →ₐ[Amb A σ] R :=
  { redHom A σ R n with commutes' := redHom_algebraMap A σ R n }

@[simp]
theorem redAlg_shiftMk (n : ℕ) (f : MvPolynomial σ R) :
    redAlg A σ R n (shiftMk A σ R n f) = constantCoeff f :=
  rfl

theorem redAlg_surjective (n : ℕ) : Function.Surjective (redAlg A σ R n) := fun r ↦
  ⟨shiftMk A σ R n (C r), by rw [redAlg_shiftMk, constantCoeff_C]⟩

theorem ker_redAlg_le (n : ℕ) :
    RingHom.ker (redAlg A σ R n : Shift A σ R n →+* R) ≤
      Ideal.map (shiftMk A σ R n) (epsIdeal σ R) := by
  intro x hx
  obtain ⟨f, rfl⟩ := shiftMk_surjective A σ R n x
  have hf : constantCoeff f = 0 := by
    have := RingHom.mem_ker.mp hx
    rwa [RingHom.coe_coe, redAlg_shiftMk] at this
  exact Ideal.mem_map_of_mem _ (mem_epsIdeal_iff.mpr hf)

/-- The kernel of the reduction is nilpotent: it is the image of `(ε)`, whose `(n+1)`-st power
vanishes in `R[ε_σ]/(ε)^{n+1}`. -/
theorem isNilpotent_ker_redAlg (n : ℕ) :
    IsNilpotent (RingHom.ker (redAlg A σ R n : Shift A σ R n →+* R)) := by
  refine ⟨n + 1, ?_⟩
  have h1 : RingHom.ker (redAlg A σ R n : Shift A σ R n →+* R) ^ (n + 1) ≤
      Ideal.map (shiftMk A σ R n) (epsIdeal σ R) ^ (n + 1) :=
    Ideal.pow_right_mono (ker_redAlg_le A σ R n) (n + 1)
  have h2 : Ideal.map (shiftMk A σ R n) (epsIdeal σ R) ^ (n + 1) = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    exact le_of_eq (Ideal.mk_ker (I := epsIdeal σ R ^ (n + 1))).symm
  rw [Ideal.zero_eq_bot]
  exact le_bot_iff.mp (h1.trans h2.le)

/-! #### Truncation -/

/-- The truncation `R[ε]/(ε)^{n+1} → R[ε]/(ε)^{m+1}` for `m ≤ n`, a map of shifted
`P`-algebras. -/
def trunc {m n : ℕ} (h : m ≤ n) : Shift A σ R n →ₐ[Amb A σ] Shift A σ R m :=
  { Ideal.Quotient.lift (epsIdeal σ R ^ (n + 1)) (shiftMk A σ R m)
      (fun _a ha ↦ (shiftMk_eq_zero_iff A σ R m).mpr
        (Ideal.pow_le_pow_right (Nat.succ_le_succ h) ha)) with
    commutes' := fun _p ↦ rfl }

@[simp]
theorem trunc_shiftMk {m n : ℕ} (h : m ≤ n) (f : MvPolynomial σ R) :
    trunc A σ R h (shiftMk A σ R n f) = shiftMk A σ R m f :=
  rfl

theorem redAlg_trunc {m n : ℕ} (h : m ≤ n) (x : Shift A σ R n) :
    redAlg A σ R m (trunc A σ R h x) = redAlg A σ R n x := by
  obtain ⟨f, rfl⟩ := shiftMk_surjective A σ R n x
  rw [trunc_shiftMk, redAlg_shiftMk, redAlg_shiftMk]

end Shift

/-! ### The Taylor expansion of a formally étale algebra -/

section Taylor

variable (A : Type u) [CommRing A] (σ : Type u) (R : Type u) [CommRing R]
  [Algebra (Amb A σ) R] [Algebra.FormallyEtale (Amb A σ) R]

/-- **The Taylor expansion of a formally étale ambient chart.**  For a formally étale
`P`-algebra `R`, `P = A[x_σ]`, this is the unique `P`-algebra map `R → R[ε_σ]/(ε)^{n+1}` which
reduces to the identity modulo `(ε)`, where the target carries the shifted structure
`x_i ↦ x_i + ε_i`.  For `R = P` it is the substitution `x_i ↦ x_i + ε_i` (`taylor_self`). -/
def taylor (n : ℕ) : R →ₐ[Amb A σ] Shift A σ R n :=
  Algebra.FormallySmooth.liftOfSurjective (AlgHom.id (Amb A σ) R) (redAlg A σ R n)
    (redAlg_surjective A σ R n) (isNilpotent_ker_redAlg A σ R n)

@[simp]
theorem redAlg_taylor (n : ℕ) (r : R) : redAlg A σ R n (taylor A σ R n r) = r :=
  Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ r

/-- `taylor n r ≡ r mod (ε)`: the constant term of any lift of `taylor n r` is `r`. -/
theorem constantCoeff_of_taylor (n : ℕ) (r : R) (f : MvPolynomial σ R)
    (hf : shiftMk A σ R n f = taylor A σ R n r) : constantCoeff f = r := by
  rw [← redAlg_shiftMk A σ R n f, hf, redAlg_taylor]

/-- **Uniqueness of the Taylor expansion.** -/
theorem taylor_unique (n : ℕ) (g : R →ₐ[Amb A σ] Shift A σ R n)
    (hg : ∀ r, redAlg A σ R n (g r) = r) : g = taylor A σ R n :=
  Algebra.FormallyUnramified.lift_unique' (redAlg A σ R n) (isNilpotent_ker_redAlg A σ R n)
    g (taylor A σ R n) (AlgHom.ext fun r ↦ by rw [AlgHom.comp_apply, AlgHom.comp_apply, hg,
      redAlg_taylor])

/-- The Taylor expansions at different orders are compatible with the truncation maps. -/
theorem trunc_comp_taylor {m n : ℕ} (h : m ≤ n) :
    (trunc A σ R h).comp (taylor A σ R n) = taylor A σ R m :=
  taylor_unique A σ R m _ fun r ↦ by
    rw [AlgHom.comp_apply, redAlg_trunc, redAlg_taylor]

theorem trunc_taylor {m n : ℕ} (h : m ≤ n) (r : R) :
    trunc A σ R h (taylor A σ R n r) = taylor A σ R m r :=
  AlgHom.congr_fun (trunc_comp_taylor A σ R h) r

end Taylor

/-! ### Sanity checks: the polynomial model and localisations -/

section Examples

variable (A : Type u) [CommRing A] (σ : Type u)

/-- For the polynomial model `R = P` the Taylor expansion is the structure map of the shifted
algebra structure, i.e. it is the substitution `x_i ↦ x_i + ε_i`. -/
theorem taylor_self (n : ℕ) :
    taylor A σ (Amb A σ) n = Algebra.ofId (Amb A σ) (Shift A σ (Amb A σ) n) :=
  (taylor_unique A σ (Amb A σ) n (Algebra.ofId (Amb A σ) (Shift A σ (Amb A σ) n))
    fun r ↦ (redAlg A σ (Amb A σ) n).commutes r).symm

/-- Explicitly, in the polynomial model the Taylor expansion sends `x_i` to `x_i + ε_i`. -/
theorem taylor_X (n : ℕ) (i : σ) :
    taylor A σ (Amb A σ) n (X i) =
      shiftMk A σ (Amb A σ) n (C (X i) + X i) := by
  rw [taylor_self]
  change algebraMap (Amb A σ) (Shift A σ (Amb A σ) n) (X i) = _
  rw [algebraMap_shift_eq, shiftHom_X]
  congr 1

end Examples

/-! ### Degree-`k` classes in an associated graded ring -/

section DegRaw

variable {S : Type u} [CommRing S] (K : Ideal S)

/-- The degree-`k` Rees element `y·t^k` attached to `y ∈ K^k`.  For `k = 1` this is
`AffineNormalCone.degreeOneRees`. -/
def degRees (k : ℕ) : (K ^ k : Ideal S) →ₗ[S] reesAlgebra K :=
  LinearMap.codRestrict (reesAlgebra K).toSubmodule
    ((Polynomial.monomial k : S →ₗ[S] Polynomial S).comp (K ^ k).subtype)
    (fun y ↦ reesAlgebra.monomial_mem.mpr y.2)

/-- The degree-`k` class of `y ∈ K^k` in `gr_K(S)`.  For `k = 1` this is
`AffineNormalCone.degreeOneRaw`. -/
def degRaw (k : ℕ) : (K ^ k : Ideal S) →ₗ[S] associatedGradedRing S K :=
  (Ideal.Quotient.mkₐ S
    (Ideal.map (algebraMap S (reesAlgebra K)) K)).toLinearMap.comp (degRees K k)

/-- An element of `K^{k+1}` has vanishing degree-`k` class. -/
theorem degRaw_eq_zero (k : ℕ) (y : (K ^ k : Ideal S)) (hy : (y : S) ∈ K ^ (k + 1)) :
    degRaw K k y = 0 := by
  change Ideal.Quotient.mk _ (degRees K k y) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact ConeRefinement.mem_map_rees_of_coe_monomial hy _ rfl

/-- The degree-`k` classes are additive. -/
theorem degRaw_add (k : ℕ) (y z w : (K ^ k : Ideal S)) (hw : (w : S) = (y : S) + (z : S)) :
    degRaw K k w = degRaw K k y + degRaw K k z := by
  have h : w = y + z := Subtype.ext hw
  rw [h, map_add]

/-- The degree-`k` classes are multiplicative: the class of a product of elements of `K^k` and
`K^l` in degree `k + l` is the product of the classes. -/
theorem degRaw_mul (k l : ℕ) (y : (K ^ k : Ideal S)) (z : (K ^ l : Ideal S))
    (w : (K ^ (k + l) : Ideal S)) (hw : (w : S) = (y : S) * (z : S)) :
    degRaw K (k + l) w = degRaw K k y * degRaw K l z := by
  have h : degRees K (k + l) w = degRees K k y * degRees K l z := by
    apply Subtype.ext
    change Polynomial.monomial (k + l) (w : S) =
      Polynomial.monomial k (y : S) * Polynomial.monomial l (z : S)
    rw [Polynomial.monomial_mul_monomial, hw]
  change Ideal.Quotient.mk _ (degRees K (k + l) w) = _
  rw [h, map_mul]
  rfl

/-- In degree zero the class of `y` is the image of `y` under the structure map of `gr_K(S)`. -/
theorem degRaw_zero_deg (y : (K ^ 0 : Ideal S)) :
    degRaw K 0 y = algebraMap S (associatedGradedRing S K) (y : S) := by
  change Ideal.Quotient.mk _ (degRees K 0 y) =
    Ideal.Quotient.mk _ (algebraMap S (reesAlgebra K) (y : S))
  congr 1

/-- In degree one the class is the one used to build the normal sheaf. -/
theorem degRaw_one_deg (y : (K ^ 1 : Ideal S)) (z : K) (hz : (z : S) = (y : S)) :
    degRaw K 1 y = degreeOneRaw S K z := by
  change Ideal.Quotient.mk _ (degRees K 1 y) = Ideal.Quotient.mk _ (degreeOneRees S K z)
  congr 1
  apply Subtype.ext
  change Polynomial.monomial 1 (y : S) = Polynomial.monomial 1 (z : S)
  rw [hz]

end DegRaw

/-! ### The Taylor expansion respects the adic filtration -/

section Graded

variable (A : Type u) [CommRing A] (σ : Type u) (R : Type u) [CommRing R]
  [Algebra (Amb A σ) R] [Algebra.FormallyEtale (Amb A σ) R] (J : Ideal R)

/-- The Taylor expansion of an element of `J` lands in `I' = J·R[ε] + (ε)`. -/
theorem taylor_mem_map_polyExt (n : ℕ) {x : R} (hx : x ∈ J) :
    taylor A σ R n x ∈ Ideal.map (shiftMk A σ R n) (ConeRefinement.polyExt σ J) := by
  obtain ⟨f, hf⟩ := shiftMk_surjective A σ R n (taylor A σ R n x)
  refine (Ideal.mem_map_iff_of_surjective _ (shiftMk_surjective A σ R n)).mpr ⟨f, ?_, hf⟩
  rw [ConeRefinement.mem_polyExt_iff, constantCoeff_of_taylor A σ R n x f hf]
  exact hx

/-- **The Taylor expansion respects the adic filtrations**: the expansion of an element of `J^k`
lies in the `k`-th power of `I' = J·R[ε] + (ε)`, modulo `(ε)^{n+1}`. -/
theorem taylor_mem_map_polyExt_pow (n : ℕ) :
    ∀ (k : ℕ) {x : R}, x ∈ J ^ k →
      taylor A σ R n x ∈ Ideal.map (shiftMk A σ R n) (ConeRefinement.polyExt σ J ^ k) := by
  intro k
  induction k with
  | zero =>
    intro x _
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
    exact Submodule.mem_top
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [map_mul, pow_succ, Ideal.map_mul]
      exact Ideal.mul_mem_mul (ih ha) (taylor_mem_map_polyExt A σ R J n hb)
    · intro y z hy hz
      rw [map_add]
      exact Ideal.add_mem _ hy hz

/-- Every element of `J^k` has a Taylor expansion of order `k` which lifts to `(I')^k`. -/
theorem exists_taylor_lift (k : ℕ) (x : R) (hx : x ∈ J ^ k) :
    ∃ y : MvPolynomial σ R, y ∈ ConeRefinement.polyExt σ J ^ k ∧
      shiftMk A σ R k y = taylor A σ R k x := by
  obtain ⟨y, hy, hmk⟩ := (Ideal.mem_map_iff_of_surjective _ (shiftMk_surjective A σ R k)).mp
    (taylor_mem_map_polyExt_pow A σ R J k k hx)
  exact ⟨y, hy, hmk⟩

/-- **The degree-`k` component of the tangent coaction.**  For `x ∈ J^k` this is the class in
`gr_{I'}(R[ε])`, `I' = polyExt σ J`, of any lift to `(I')^k` of the order-`k` Taylor expansion
of `x`; `taylorClass_spec` shows that it does not depend on the lift. -/
def taylorClass (k : ℕ) (x : R) (hx : x ∈ J ^ k) :
    associatedGradedRing (MvPolynomial σ R) (ConeRefinement.polyExt σ J) :=
  degRaw (ConeRefinement.polyExt σ J) k ⟨(exists_taylor_lift A σ R J k x hx).choose,
    (exists_taylor_lift A σ R J k x hx).choose_spec.1⟩

/-- **Independence of the lift.**  Any lift to `(I')^k` of the order-`n` Taylor expansion of
`x ∈ J^k`, `k ≤ n`, computes the degree-`k` class. -/
theorem taylorClass_spec (k n : ℕ) (hkn : k ≤ n) (x : R) (hx : x ∈ J ^ k)
    (y : MvPolynomial σ R) (hy : y ∈ ConeRefinement.polyExt σ J ^ k)
    (hmk : shiftMk A σ R n y = taylor A σ R n x) :
    taylorClass A σ R J k x hx = degRaw (ConeRefinement.polyExt σ J) k ⟨y, hy⟩ := by
  have hy₀ : (exists_taylor_lift A σ R J k x hx).choose ∈ ConeRefinement.polyExt σ J ^ k :=
    (exists_taylor_lift A σ R J k x hx).choose_spec.1
  have hmk₀ : shiftMk A σ R k (exists_taylor_lift A σ R J k x hx).choose = taylor A σ R k x :=
    (exists_taylor_lift A σ R J k x hx).choose_spec.2
  have h1 : shiftMk A σ R k y = shiftMk A σ R k (exists_taylor_lift A σ R J k x hx).choose := by
    rw [← trunc_shiftMk A σ R hkn y, hmk, trunc_taylor]
    exact hmk₀.symm
  have h2 : y - (exists_taylor_lift A σ R J k x hx).choose ∈ epsIdeal σ R ^ (k + 1) :=
    (shiftMk_eq_iff A σ R k).mp h1
  have h3 : y - (exists_taylor_lift A σ R J k x hx).choose ∈
      ConeRefinement.polyExt σ J ^ (k + 1) := epsIdeal_pow_le_polyExt_pow J (k + 1) h2
  have key : degRaw (ConeRefinement.polyExt σ J) k
      (⟨y, hy⟩ - ⟨(exists_taylor_lift A σ R J k x hx).choose, hy₀⟩) = 0 :=
    degRaw_eq_zero _ k _ h3
  rw [map_sub, sub_eq_zero] at key
  exact key.symm

/-- The degree-`k` classes are additive. -/
theorem taylorClass_add (k : ℕ) (x x' : R) (hx : x ∈ J ^ k) (hx' : x' ∈ J ^ k)
    (hs : x + x' ∈ J ^ k) :
    taylorClass A σ R J k (x + x') hs =
      taylorClass A σ R J k x hx + taylorClass A σ R J k x' hx' := by
  obtain ⟨y, hy, hmk⟩ := exists_taylor_lift A σ R J k x hx
  obtain ⟨y', hy', hmk'⟩ := exists_taylor_lift A σ R J k x' hx'
  rw [taylorClass_spec A σ R J k k le_rfl x hx y hy hmk,
    taylorClass_spec A σ R J k k le_rfl x' hx' y' hy' hmk',
    taylorClass_spec A σ R J k k le_rfl (x + x') hs (y + y') (Ideal.add_mem _ hy hy')
      (by rw [map_add, hmk, hmk', map_add (taylor A σ R k) x x'])]
  exact degRaw_add (ConeRefinement.polyExt σ J) k ⟨y, hy⟩ ⟨y', hy'⟩ _ rfl

/-- The degree-`k` classes are multiplicative across degrees: this is the multiplicativity of
the tangent coaction. -/
theorem taylorClass_mul (k l : ℕ) (x x' : R) (hx : x ∈ J ^ k) (hx' : x' ∈ J ^ l)
    (hp : x * x' ∈ J ^ (k + l)) :
    taylorClass A σ R J (k + l) (x * x') hp =
      taylorClass A σ R J k x hx * taylorClass A σ R J l x' hx' := by
  obtain ⟨y, hy, hmk⟩ := (Ideal.mem_map_iff_of_surjective _
    (shiftMk_surjective A σ R (k + l))).mp (taylor_mem_map_polyExt_pow A σ R J (k + l) k hx)
  obtain ⟨y', hy', hmk'⟩ := (Ideal.mem_map_iff_of_surjective _
    (shiftMk_surjective A σ R (k + l))).mp (taylor_mem_map_polyExt_pow A σ R J (k + l) l hx')
  have hprod : y * y' ∈ ConeRefinement.polyExt σ J ^ (k + l) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hy hy'
  rw [taylorClass_spec A σ R J k (k + l) (Nat.le_add_right k l) x hx y hy hmk,
    taylorClass_spec A σ R J l (k + l) (Nat.le_add_left l k) x' hx' y' hy' hmk',
    taylorClass_spec A σ R J (k + l) (k + l) le_rfl (x * x') hp (y * y') hprod
      (by rw [map_mul, hmk, hmk', map_mul (taylor A σ R (k + l)) x x'])]
  exact degRaw_mul _ k l ⟨y, hy⟩ ⟨y', hy'⟩ ⟨y * y', hprod⟩ rfl

/-- The degree-`k` class of an element of `J^{k+1}` vanishes: the classes descend to
`J^k/J^{k+1}`. -/
theorem taylorClass_eq_zero (k : ℕ) (x : R) (hx : x ∈ J ^ k) (hx' : x ∈ J ^ (k + 1)) :
    taylorClass A σ R J k x hx = 0 := by
  obtain ⟨y, hy, hmk⟩ := (Ideal.mem_map_iff_of_surjective _
    (shiftMk_surjective A σ R k)).mp (taylor_mem_map_polyExt_pow A σ R J k (k + 1) hx')
  have hyk : y ∈ ConeRefinement.polyExt σ J ^ k :=
    Ideal.pow_le_pow_right (Nat.le_succ k) hy
  rw [taylorClass_spec A σ R J k k le_rfl x hx y hyk hmk]
  exact degRaw_eq_zero _ k _ hy

/-! #### Degree zero and degree one -/

omit [Algebra.FormallyEtale (Amb A σ) R] in
/-- The order-zero truncation `R[ε]/(ε)` is `R`: the reduction map is injective. -/
theorem redAlg_zero_injective : Function.Injective (redAlg A σ R 0) := by
  intro a b hab
  obtain ⟨f, rfl⟩ := shiftMk_surjective A σ R 0 a
  obtain ⟨g, rfl⟩ := shiftMk_surjective A σ R 0 b
  rw [redAlg_shiftMk, redAlg_shiftMk] at hab
  refine (shiftMk_eq_iff A σ R 0).mpr ?_
  have h : epsIdeal σ R ^ (0 + 1) = epsIdeal σ R := pow_one _
  rw [h, mem_epsIdeal_iff, map_sub, hab, sub_self]

/-- The order-zero Taylor expansion is the identity. -/
theorem shiftMk_C_eq_taylor_zero (x : R) :
    shiftMk A σ R 0 (MvPolynomial.C x) = taylor A σ R 0 x := by
  apply redAlg_zero_injective A σ R
  rw [redAlg_shiftMk, redAlg_taylor, constantCoeff_C]

/-- In degree zero the tangent coaction is the structure map of `gr_{I'}(R[ε])`. -/
theorem taylorClass_zero (x : R) (hx : x ∈ J ^ 0) :
    taylorClass A σ R J 0 x hx =
      algebraMap (MvPolynomial σ R)
        (associatedGradedRing (MvPolynomial σ R) (ConeRefinement.polyExt σ J))
        (MvPolynomial.C x) := by
  have hC : (MvPolynomial.C x : MvPolynomial σ R) ∈ ConeRefinement.polyExt σ J ^ 0 := by
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  rw [taylorClass_spec A σ R J 0 0 le_rfl x hx (MvPolynomial.C x) hC
    (shiftMk_C_eq_taylor_zero A σ R x)]
  exact degRaw_zero_deg (ConeRefinement.polyExt σ J) ⟨MvPolynomial.C x, hC⟩

/-- **The degree-one tangent coaction is the derivative.**  For `x ∈ J` and any lift `y` of the
first-order Taylor expansion `taylor 1 x = x + Σ ∂ᵢx·εᵢ`, the degree-one class of `x` is the
degree-one class of `y` in `gr_{I'}(R[ε])`. -/
theorem taylorClass_one (x : R) (hx : x ∈ J ^ 1) (y : MvPolynomial σ R)
    (hy : y ∈ ConeRefinement.polyExt σ J) (hmk : shiftMk A σ R 1 y = taylor A σ R 1 x) :
    taylorClass A σ R J 1 x hx =
      degreeOneRaw (MvPolynomial σ R) (ConeRefinement.polyExt σ J) ⟨y, hy⟩ := by
  have hy1 : y ∈ ConeRefinement.polyExt σ J ^ 1 := by rwa [pow_one]
  rw [taylorClass_spec A σ R J 1 1 le_rfl x hx y hy1 hmk]
  exact degRaw_one_deg (ConeRefinement.polyExt σ J) ⟨y, hy1⟩ ⟨y, hy⟩ rfl

/-! #### Assembling the degreewise classes into a ring map -/

/-- Shorthand for the associated graded ring `gr_{I'}(R[ε_σ])` of the refined ideal
`I' = polyExt σ J`. -/
abbrev GrExt : Type u :=
  associatedGradedRing (MvPolynomial σ R) (ConeRefinement.polyExt σ J)

open Classical in
/-- The degree-`k` class as a total function of `x : R`, with junk value `0` outside `J^k`. -/
def taylorClassOf (k : ℕ) (x : R) : GrExt σ R J :=
  if h : x ∈ J ^ k then taylorClass A σ R J k x h else 0

theorem taylorClassOf_of_mem (k : ℕ) (x : R) (hx : x ∈ J ^ k) :
    taylorClassOf A σ R J k x = taylorClass A σ R J k x hx :=
  dif_pos hx

theorem taylorClassOf_zero_right (k : ℕ) : taylorClassOf A σ R J k 0 = 0 := by
  rw [taylorClassOf_of_mem A σ R J k 0 (Ideal.zero_mem _)]
  exact taylorClass_eq_zero A σ R J k 0 (Ideal.zero_mem _) (Ideal.zero_mem _)

theorem taylorClassOf_add (k : ℕ) (x y : R) (hx : x ∈ J ^ k) (hy : y ∈ J ^ k) :
    taylorClassOf A σ R J k (x + y) =
      taylorClassOf A σ R J k x + taylorClassOf A σ R J k y := by
  rw [taylorClassOf_of_mem A σ R J k x hx, taylorClassOf_of_mem A σ R J k y hy,
    taylorClassOf_of_mem A σ R J k (x + y) (Ideal.add_mem _ hx hy)]
  exact taylorClass_add A σ R J k x y hx hy _

theorem taylorClassOf_mul (k l : ℕ) (x y : R) (hx : x ∈ J ^ k) (hy : y ∈ J ^ l) :
    taylorClassOf A σ R J (k + l) (x * y) =
      taylorClassOf A σ R J k x * taylorClassOf A σ R J l y := by
  have hp : x * y ∈ J ^ (k + l) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hx hy
  rw [taylorClassOf_of_mem A σ R J k x hx, taylorClassOf_of_mem A σ R J l y hy,
    taylorClassOf_of_mem A σ R J (k + l) (x * y) hp]
  exact taylorClass_mul A σ R J k l x y hx hy hp

theorem taylorClassOf_sum {ι : Type u} (k : ℕ) (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, f i ∈ J ^ k) :
    taylorClassOf A σ R J k (∑ i ∈ s, f i) = ∑ i ∈ s, taylorClassOf A σ R J k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using taylorClassOf_zero_right A σ R J k
  | insert a s ha ih =>
    have hmem : ∑ i ∈ s, f i ∈ J ^ k :=
      Ideal.sum_mem _ fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      taylorClassOf_add A σ R J k _ _ (hf a (Finset.mem_insert_self a s)) hmem,
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

/-- The value of the tangent coaction on a polynomial `∑ p_n t^n` of the Rees algebra: the sum
over `n` of the degree-`n` classes of its coefficients. -/
def phiPoly (p : Polynomial R) : GrExt σ R J :=
  ∑ n ∈ p.support, taylorClassOf A σ R J n (p.coeff n)

theorem phiPoly_eq_sum (p : Polynomial R) (s : Finset ℕ) (hs : p.support ⊆ s) :
    phiPoly A σ R J p = ∑ n ∈ s, taylorClassOf A σ R J n (p.coeff n) := by
  refine Finset.sum_subset hs fun n _ hn ↦ ?_
  rw [Polynomial.notMem_support_iff.mp hn, taylorClassOf_zero_right]

theorem phiPoly_zero : phiPoly A σ R J 0 = 0 := by
  rw [phiPoly, Polynomial.support_zero, Finset.sum_empty]

theorem phiPoly_monomial (i : ℕ) (a : R) :
    phiPoly A σ R J (Polynomial.monomial i a) = taylorClassOf A σ R J i a := by
  have hs : (Polynomial.monomial i a).support ⊆ {i} := by
    intro n hn
    rw [Polynomial.mem_support_iff, Polynomial.coeff_monomial] at hn
    rw [Finset.mem_singleton]
    by_contra hne
    exact hn (if_neg fun h ↦ hne h.symm)
  rw [phiPoly_eq_sum A σ R J _ {i} hs, Finset.sum_singleton, Polynomial.coeff_monomial,
    if_pos rfl]

theorem phiPoly_add (p q : Polynomial R) (hp : p ∈ reesAlgebra J) (hq : q ∈ reesAlgebra J) :
    phiPoly A σ R J (p + q) = phiPoly A σ R J p + phiPoly A σ R J q := by
  classical
  rw [phiPoly_eq_sum A σ R J (p + q) (p.support ∪ q.support) Polynomial.support_add,
    phiPoly_eq_sum A σ R J p (p.support ∪ q.support) Finset.subset_union_left,
    phiPoly_eq_sum A σ R J q (p.support ∪ q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [Polynomial.coeff_add, taylorClassOf_add A σ R J n _ _
    ((mem_reesAlgebra_iff J p).mp hp n) ((mem_reesAlgebra_iff J q).mp hq n)]

/-- The coefficients of `t^i·a·q`. -/
theorem coeff_monomial_mul' (i : ℕ) (a : R) (q : Polynomial R) (k : ℕ) :
    (Polynomial.monomial i a * q).coeff k = if i ≤ k then a * q.coeff (k - i) else 0 := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc,
    mul_comm (Polynomial.X ^ i : Polynomial R) q, Polynomial.coeff_C_mul,
    Polynomial.coeff_mul_X_pow']
  split_ifs with h
  · rfl
  · rw [mul_zero]

theorem phiPoly_monomial_mul (i : ℕ) (a : R) (ha : a ∈ J ^ i) (q : Polynomial R)
    (hq : q ∈ reesAlgebra J) :
    phiPoly A σ R J (Polynomial.monomial i a * q) =
      taylorClassOf A σ R J i a * phiPoly A σ R J q := by
  classical
  have hsub : (Polynomial.monomial i a * q).support ⊆
      q.support.map ⟨fun d ↦ i + d, fun x y h ↦ Nat.add_left_cancel h⟩ := by
    intro k hk
    rw [Polynomial.mem_support_iff, coeff_monomial_mul'] at hk
    split_ifs at hk with hik
    · rw [Finset.mem_map]
      refine ⟨k - i, ?_, ?_⟩
      · rw [Polynomial.mem_support_iff]
        intro h0
        rw [h0, mul_zero] at hk
        exact hk rfl
      · change i + (k - i) = k
        omega
    · exact absurd rfl hk
  rw [phiPoly_eq_sum A σ R J _ _ hsub, Finset.sum_map, phiPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  change taylorClassOf A σ R J (i + d) ((Polynomial.monomial i a * q).coeff (i + d)) = _
  rw [coeff_monomial_mul', if_pos (Nat.le_add_right i d)]
  have hd : i + d - i = d := by omega
  rw [hd, taylorClassOf_mul A σ R J i d a (q.coeff d) ha
    ((mem_reesAlgebra_iff J q).mp hq d)]

/-- The truncations of a Rees element are Rees elements. -/
theorem sum_monomial_mem_rees (s : Finset ℕ) (p : Polynomial R) (hp : p ∈ reesAlgebra J) :
    (∑ n ∈ s, Polynomial.monomial n (p.coeff n)) ∈ reesAlgebra J :=
  Subalgebra.sum_mem _ fun n _ ↦
    reesAlgebra.monomial_mem.mpr ((mem_reesAlgebra_iff J p).mp hp n)

theorem phiPoly_mul (p q : Polynomial R) (hp : p ∈ reesAlgebra J) (hq : q ∈ reesAlgebra J) :
    phiPoly A σ R J (p * q) = phiPoly A σ R J p * phiPoly A σ R J q := by
  classical
  have key : ∀ s : Finset ℕ,
      phiPoly A σ R J ((∑ n ∈ s, Polynomial.monomial n (p.coeff n)) * q) =
        phiPoly A σ R J (∑ n ∈ s, Polynomial.monomial n (p.coeff n)) * phiPoly A σ R J q := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, zero_mul, phiPoly_zero, zero_mul]
    | insert a s ha ih =>
      have hmono : (Polynomial.monomial a (p.coeff a) : Polynomial R) ∈ reesAlgebra J :=
        reesAlgebra.monomial_mem.mpr ((mem_reesAlgebra_iff J p).mp hp a)
      have hsum : (∑ n ∈ s, Polynomial.monomial n (p.coeff n)) ∈ reesAlgebra J :=
        sum_monomial_mem_rees R J s p hp
      rw [Finset.sum_insert ha, add_mul,
        phiPoly_add A σ R J _ _ (mul_mem hmono hq) (mul_mem hsum hq),
        phiPoly_monomial_mul A σ R J a (p.coeff a) ((mem_reesAlgebra_iff J p).mp hp a) q hq, ih,
        phiPoly_add A σ R J _ _ hmono hsum, phiPoly_monomial, add_mul]
  have hps : p = ∑ n ∈ p.support, Polynomial.monomial n (p.coeff n) := Polynomial.as_sum_support p
  have h1 := key p.support
  rwa [← hps] at h1

theorem phiPoly_one : phiPoly A σ R J 1 = 1 := by
  have h1 : (1 : Polynomial R) = Polynomial.monomial 0 1 := by
    rw [Polynomial.monomial_zero_left, map_one]
  have h0 : (1 : R) ∈ J ^ 0 := by
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  rw [h1, phiPoly_monomial, taylorClassOf_of_mem A σ R J 0 1 h0,
    taylorClass_zero A σ R J 1 h0, map_one, map_one]

/-- **The tangent coaction on the Rees algebra.**  It sends `f·t^n` with `f ∈ J^n` to the
degree-`n` class of the Taylor expansion of `f`. -/
def reesPhi : reesAlgebra J →+* GrExt σ R J where
  toFun p := phiPoly A σ R J (p : Polynomial R)
  map_one' := phiPoly_one A σ R J
  map_zero' := phiPoly_zero A σ R J
  map_add' p q := phiPoly_add A σ R J _ _ p.2 q.2
  map_mul' p q := phiPoly_mul A σ R J _ _ p.2 q.2

theorem reesPhi_apply (p : reesAlgebra J) :
    reesPhi A σ R J p = phiPoly A σ R J (p : Polynomial R) :=
  rfl

theorem reesPhi_algebraMap (r : R) :
    reesPhi A σ R J (algebraMap R (reesAlgebra J) r) =
      algebraMap (MvPolynomial σ R) (GrExt σ R J) (MvPolynomial.C r) := by
  have h0 : r ∈ J ^ 0 := by
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  have hc : ((algebraMap R (reesAlgebra J) r : reesAlgebra J) : Polynomial R) =
      Polynomial.monomial 0 r := by
    rw [Polynomial.monomial_zero_left]
    rfl
  rw [reesPhi_apply, hc, phiPoly_monomial, taylorClassOf_of_mem A σ R J 0 r h0,
    taylorClass_zero A σ R J r h0]

/-- The coaction kills the ideal `J·Rees_J(R)`, hence descends to `gr_J(R)`. -/
theorem map_le_ker_reesPhi :
    Ideal.map (algebraMap R (reesAlgebra J)) J ≤
      RingHom.ker (reesPhi A σ R J) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, RingHom.mem_ker, reesPhi_algebraMap]
  refine ConeRefinement.algebraMap_gr_eq_zero (ConeRefinement.polyExt σ J) ?_
  rw [ConeRefinement.mem_polyExt_iff, MvPolynomial.constantCoeff_C]
  exact hr

/-- **The tangent coaction of a formally étale ambient chart**, in the form of a ring map
`gr_J(R) → gr_{I'}(R[ε_σ])`: the degree-`n` piece `J^n/J^{n+1}` is sent to the class of the
order-`n` Taylor expansion. -/
def grPhi : associatedGradedRing R J →+* GrExt σ R J :=
  Ideal.Quotient.lift _ (reesPhi A σ R J) (map_le_ker_reesPhi A σ R J)

theorem grPhi_mk (p : reesAlgebra J) :
    grPhi A σ R J (Ideal.Quotient.mk _ p) = phiPoly A σ R J (p : Polynomial R) :=
  rfl

theorem grPhi_algebraMap (r : R) :
    grPhi A σ R J (algebraMap R (associatedGradedRing R J) r) =
      algebraMap (MvPolynomial σ R) (GrExt σ R J) (MvPolynomial.C r) :=
  reesPhi_algebraMap A σ R J r

/-- The degree-one part of the coaction is the derivative: the class of `x ∈ J` goes to the
degree-one class of any lift of its first-order Taylor expansion. -/
theorem grPhi_degreeOneRaw (x : R) (hx : x ∈ J) (y : MvPolynomial σ R)
    (hy : y ∈ ConeRefinement.polyExt σ J) (hmk : shiftMk A σ R 1 y = taylor A σ R 1 x) :
    grPhi A σ R J (degreeOneRaw R J ⟨x, hx⟩) =
      degreeOneRaw (MvPolynomial σ R) (ConeRefinement.polyExt σ J) ⟨y, hy⟩ := by
  have hx1 : x ∈ J ^ 1 := by rwa [pow_one]
  have hc : ((degreeOneRees R J ⟨x, hx⟩ : reesAlgebra J) : Polynomial R) =
      Polynomial.monomial 1 x := rfl
  rw [show degreeOneRaw R J ⟨x, hx⟩ = Ideal.Quotient.mk _ (degreeOneRees R J ⟨x, hx⟩) from rfl,
    grPhi_mk, hc, phiPoly_monomial, taylorClassOf_of_mem A σ R J 1 x hx1,
    taylorClass_one A σ R J x hx1 y hy hmk]

/-! #### The counit law -/

/-- The constant term of an element of `I' = polyExt σ J` lies in `J`. -/
theorem map_constantCoeff_polyExt_le :
    Ideal.map (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R)
      (ConeRefinement.polyExt σ J) ≤ J := by
  rw [Ideal.map_le_iff_le_comap]
  exact fun f hf ↦ hf

/-- Setting `ε = 0`: the map `gr_{I'}(R[ε]) → gr_J(R)` induced by `R[ε] → R`. -/
def counitMap : GrExt σ R J →+* associatedGradedRing R J :=
  ConeRefinement.grMapOfLe (ConeRefinement.polyExt σ J) J
    (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R) (map_constantCoeff_polyExt_le σ R J)

/-- **The counit law**: setting `ε = 0` in the tangent coaction gives back the identity. -/
theorem counitMap_comp_grPhi :
    (counitMap σ R J).comp (grPhi A σ R J) = RingHom.id (associatedGradedRing R J) := by
  refine ConeRefinement.gr_ringHom_ext (J := J) (fun r ↦ ?_) (fun x ↦ ?_)
  · rw [RingHom.comp_apply, grPhi_algebraMap, counitMap,
      ConeRefinement.grMapOfLe_algebraMap, MvPolynomial.constantCoeff_C, RingHom.id_apply]
  · obtain ⟨y, hy, hmk⟩ := exists_taylor_lift A σ R J 1 x (by rw [pow_one]; exact x.2)
    have hy' : y ∈ ConeRefinement.polyExt σ J := by rwa [pow_one] at hy
    have hcc : MvPolynomial.constantCoeff y = (x : R) :=
      constantCoeff_of_taylor A σ R 1 (x : R) y hmk
    rw [RingHom.comp_apply, RingHom.id_apply,
      show degreeOneRaw R J x = degreeOneRaw R J ⟨(x : R), x.2⟩ from rfl,
      grPhi_degreeOneRaw A σ R J (x : R) x.2 y hy' hmk, counitMap,
      show degreeOneRaw (MvPolynomial σ R) (ConeRefinement.polyExt σ J) ⟨y, hy'⟩ =
        Ideal.Quotient.mk _ (degreeOneRees (MvPolynomial σ R) (ConeRefinement.polyExt σ J)
          ⟨y, hy'⟩) from rfl,
      ConeRefinement.grMapOfLe_degreeOneRees]
    have hxeq : ∀ h : MvPolynomial.constantCoeff y ∈ J,
        (⟨MvPolynomial.constantCoeff y, h⟩ : ↥J) = x := fun _ ↦ Subtype.ext hcc
    rw [hxeq]
    rfl

/-! #### The coaction as a ring map in the coordinates `gr_J(R)[z_σ]` -/

/-- **The tangent coaction of a formally étale ambient chart** in the coordinates
`gr_{I'}(R[ε]) ≅ gr_J(R)[z_σ]` of `ConeRefinement.prodEquiv`: a ring map
`gr_J(R) → gr_J(R)[z_σ]`. -/
def coactionEtale :
    associatedGradedRing R J →+* MvPolynomial σ (associatedGradedRing R J) :=
  RingHom.comp
    ((ConeRefinement.prodEquiv (τ := σ) (I := J)).symm : GrExt σ R J ≃+* _).toRingHom
    (grPhi A σ R J)

theorem coactionEtale_apply (z : associatedGradedRing R J) :
    coactionEtale A σ R J z =
      (ConeRefinement.prodEquiv (τ := σ) (I := J)).symm (grPhi A σ R J z) :=
  rfl

/-! #### The coaction in the coordinates `gr_J(R)[z_σ]` -/

/-- The degree-`k` component of the tangent coaction, read in the product decomposition
`gr_{I'}(R[ε]) ≅ gr_J(R)[z_σ]` of `ConeRefinement.prodEquiv`. -/
def taylorCoeff (k : ℕ) (x : R) (hx : x ∈ J ^ k) :
    MvPolynomial σ (associatedGradedRing R J) :=
  (ConeRefinement.prodEquiv (τ := σ) (I := J)).symm (taylorClass A σ R J k x hx)

/-- The degree-`k` components of the coaction are additive. -/
theorem taylorCoeff_add (k : ℕ) (x x' : R) (hx : x ∈ J ^ k) (hx' : x' ∈ J ^ k)
    (hs : x + x' ∈ J ^ k) :
    taylorCoeff A σ R J k (x + x') hs =
      taylorCoeff A σ R J k x hx + taylorCoeff A σ R J k x' hx' := by
  rw [taylorCoeff, taylorClass_add A σ R J k x x' hx hx' hs, map_add]
  rfl

/-- The degree-`k` components of the coaction are multiplicative across degrees. -/
theorem taylorCoeff_mul (k l : ℕ) (x x' : R) (hx : x ∈ J ^ k) (hx' : x' ∈ J ^ l)
    (hp : x * x' ∈ J ^ (k + l)) :
    taylorCoeff A σ R J (k + l) (x * x') hp =
      taylorCoeff A σ R J k x hx * taylorCoeff A σ R J l x' hx' := by
  rw [taylorCoeff, taylorClass_mul A σ R J k l x x' hx hx' hp, map_mul]
  rfl

/-- The degree-`k` components of the coaction kill `J^{k+1}`. -/
theorem taylorCoeff_eq_zero (k : ℕ) (x : R) (hx : x ∈ J ^ k) (hx' : x ∈ J ^ (k + 1)) :
    taylorCoeff A σ R J k x hx = 0 := by
  rw [taylorCoeff, taylorClass_eq_zero A σ R J k x hx hx', map_zero]

/-- The coaction computes the degree-`k` classes: the class of `x ∈ J^k` in `gr_J(R)` goes to
the degree-`k` class of its order-`k` Taylor expansion. -/
theorem grPhi_degRaw (k : ℕ) (x : R) (hx : x ∈ J ^ k) :
    grPhi A σ R J (degRaw J k ⟨x, hx⟩) = taylorClass A σ R J k x hx := by
  rw [show degRaw J k ⟨x, hx⟩ = Ideal.Quotient.mk _ (degRees J k ⟨x, hx⟩) from rfl, grPhi_mk,
    show ((degRees J k ⟨x, hx⟩ : reesAlgebra J) : Polynomial R) =
      Polynomial.monomial k x from rfl,
    phiPoly_monomial, taylorClassOf_of_mem A σ R J k x hx]

/-- The coaction is the identity in degree zero. -/
theorem coactionEtale_algebraMap (r : R) :
    coactionEtale A σ R J (algebraMap R (associatedGradedRing R J) r) =
      MvPolynomial.C (algebraMap R (associatedGradedRing R J) r) := by
  rw [coactionEtale_apply, grPhi_algebraMap]
  refine (ConeRefinement.prodEquiv (τ := σ) (I := J)).injective ?_
  rw [RingEquiv.apply_symm_apply, ConeRefinement.prodEquiv_apply, ConeRefinement.prodMap_C,
    ConeRefinement.grIncl_algebraMap]

/-- In the coordinates `gr_J(R)[z_σ]` the coaction is given by the degreewise classes
`taylorCoeff`. -/
theorem coactionEtale_degRaw (k : ℕ) (x : R) (hx : x ∈ J ^ k) :
    coactionEtale A σ R J (degRaw J k ⟨x, hx⟩) = taylorCoeff A σ R J k x hx := by
  rw [coactionEtale_apply, grPhi_degRaw, taylorCoeff]

end Graded

end

end EtaleAmbient

end GromovWitten.AlgebraicGeometry
