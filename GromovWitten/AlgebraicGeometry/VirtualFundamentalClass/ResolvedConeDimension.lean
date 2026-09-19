/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ResolvedCone
import GromovWitten.AlgebraicGeometry.Cones.NormalConeDimension
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChernClasses

/-!
# Purity of the resolved cone in the polynomial model

This file is the dimension theory of the resolved cone `C(E) ⊆ E₁` constructed in
`VirtualFundamentalClass/ResolvedCone.lean`, in the polynomial model `R = k[x_i]_{i ∈ σ}`
(`k` a field, `σ` finite) of the affine Behrend–Fantechi setting.

The geometric picture is that `C ×_X E₀ → C(E)` is a torsor under the trivial bundle
`T_M|_U = U × 𝔸^σ`, so that `C ×_X E₀` is, over `C(E)`, an affine space of relative dimension
`|σ|`.  Two ingredients are developed.

* The **invariant ideal lemma** (a general statement about polynomial rings): if an ideal `K` of
  `D[x_i]` is stable under the translation coaction `x_i ↦ x_i + t_i`, then `K` is extended from
  the base, `K = (K ∩ D) · D[x_i]`.  This is the algebraic form of the statement that a
  translation invariant closed subscheme of `𝔸^σ_D` is a cone over the base.

* **Purity**: granting the dimension formula for the extended Rees algebra of `I` (the single
  conditional input of `Cones/NormalConeDimension.lean`) and the trivialisation of the torsor,
  every irreducible component of `C(E)` has dimension `b = rank E⁰`.

## Main definitions

* `ResolvedCone.translationCoaction D σ`: the translation coaction
  `D[x_i] → D[x_i][t_i]`, `x_i ↦ x_i + t_i` (written with the inner variables as coefficients).
* `ResolvedCone.productRingEquiv φ`: the coordinate ring `gr_I(R) ⊗ Sym(E⁰)` of `C ×_X E₀` is a
  polynomial ring in `b = rank E⁰` variables over `gr_I(R)`.
* `ResolvedCone.IsPolynomialTrivialisation φ`: the hypothesis that `C ×_X E₀ → C(E)` is a
  trivial `𝔸^σ`-torsor, that is, that `gr_I(R) ⊗ Sym(E⁰)` is a polynomial ring in `σ` variables
  over the coordinate ring of `C(E)`, compatibly with `toProduct φ`.

## Main results

* `ResolvedCone.eq_map_comap_C_of_translationCoaction`: the invariant ideal lemma.
* `ResolvedCone.map_C_mem_minimalPrimes`, `ResolvedCone.comap_C_mem_minimalPrimes`,
  `ResolvedCone.map_comap_C_of_mem_minimalPrimes`: the minimal primes of `A[x_i]` are exactly the
  extensions of the minimal primes of `A`.
* `ResolvedCone.ringKrullDim_quotient_map_C`: `dim A[x_i]/qA[x_i] = dim A/q + |σ|`.
* `ResolvedCone.ringKrullDim_quotient_productRing`: every minimal prime of `gr_I(R) ⊗ Sym(E⁰)`
  has quotient of Krull dimension `|σ| + b`.
* `ResolvedCone.exists_rightInverse_coneBeta`: the mapping-cone surjection `L⁻¹ ⊕ E⁰ → L⁰` of an
  obstruction theory splits in the polynomial model, where `L⁰` is free on the differentials of
  the coordinates.
* `ResolvedCone.ringKrullDim_quotient_ring_eq`: **purity of `C(E)`** — every minimal prime `q` of
  the coordinate ring of `C(E)` has `dim (ring φ ⧸ q) = b`.
* `ResolvedCone.dimension_eq_of_isMax`, `ResolvedCone.dimension_toBundle_eq_of_isMax`: the same
  statement in the form `∀ x, IsMax x → dim x = b` used by the certified dimension functions of
  `IntersectionTheory/ChowGroup.lean`, on `C(E)` and on the ambient bundle `E₁`.

## The conditional inputs

Two hypotheses are carried explicitly and are never used as instances or fields:

* `HasDimensionFormula (extendedRees R I)`, exactly the hypothesis of
  `ringKrullDim_quotient_eq_of_mem_minimalPrimes` (`Cones/NormalConeDimension.lean`), which is
  the catenarity/equidimensionality of finite type algebras over a field;
* `IsPolynomialTrivialisation φ`, the trivialisation of the `T_M|_U`-torsor `C ×_X E₀ → C(E)`.
  It is the ring-theoretic form of the splitting of the surjection `L⁻¹ ⊕ E⁰ → L⁰` of an
  obstruction theory; it is stated here as an explicit hypothesis and is *not* proved in this
  file.  The invariant ideal lemma above is the tool with which it is meant to be established.
-/

universe u

-- The coordinate ring of `C ×_X E₀` is a tensor product whose left factor is itself a quotient
-- of a Rees algebra; synthesising `CommSemiring`/`CommRing` for it needs one more level of
-- pending instance problems than the default.
set_option maxSynthPendingDepth 5

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ResolvedCone

open CategoryTheory Order IntersectionTheory
open NormalSheafPicard.AffineIntrinsicNormalSheaf
open scoped TensorProduct

attribute [local instance] specializationOrder

/-! ## The invariant ideal lemma for the translation coaction -/

section InvariantIdeal

variable (D : Type u) [CommRing D] (σ : Type u)

/-- The **translation coaction** on the polynomial ring `D[x_i]`: the `D`-algebra map
`D[x_i] → D[x_i][t_i]` sending `x_i` to `x_i + t_i`.  The coefficient ring of the target is the
source, so that the coaction is a map of rings over `D`; the variables `t_i` of the target are
the translation parameters. -/
noncomputable def translationCoaction :
    MvPolynomial σ D →+* MvPolynomial σ (MvPolynomial σ D) :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : MvPolynomial σ D →+* MvPolynomial σ (MvPolynomial σ D)).comp
      (MvPolynomial.C : D →+* MvPolynomial σ D))
    fun i ↦ MvPolynomial.C (MvPolynomial.X i) + MvPolynomial.X i

@[simp]
theorem translationCoaction_C (d : D) :
    translationCoaction D σ (MvPolynomial.C d) =
      MvPolynomial.C (MvPolynomial.C d : MvPolynomial σ D) :=
  MvPolynomial.eval₂Hom_C _ _ d

@[simp]
theorem translationCoaction_X (i : σ) :
    translationCoaction D σ (MvPolynomial.X i) =
      MvPolynomial.C (MvPolynomial.X i : MvPolynomial σ D) + MvPolynomial.X i :=
  MvPolynomial.eval₂Hom_X' _ _ i

/-- Specialising the translation parameters to the variables and the variables to zero:
`t_i ↦ x_i`, `x_i ↦ 0`.  It is a retraction of the translation coaction. -/
noncomputable def collapseOuter : MvPolynomial σ (MvPolynomial σ D) →+* MvPolynomial σ D :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : D →+* MvPolynomial σ D).comp
      (MvPolynomial.constantCoeff : MvPolynomial σ D →+* D))
    MvPolynomial.X

/-- Specialising the translation parameters to minus the variables: `t_i ↦ -x_i`, `x_i ↦ x_i`.
Composed with the translation coaction it is evaluation at zero. -/
noncomputable def collapseInner : MvPolynomial σ (MvPolynomial σ D) →+* MvPolynomial σ D :=
  MvPolynomial.eval₂Hom (RingHom.id (MvPolynomial σ D)) fun i ↦ -MvPolynomial.X i

/-- `collapseOuter` is a retraction of the translation coaction. -/
theorem collapseOuter_comp_translationCoaction :
    (collapseOuter D σ).comp (translationCoaction D σ) = RingHom.id (MvPolynomial σ D) := by
  refine MvPolynomial.ringHom_ext (fun d ↦ ?_) (fun i ↦ ?_)
  · simp [collapseOuter]
  · simp [collapseOuter]

/-- The effect of `collapseOuter` on constants. -/
theorem collapseOuter_comp_C :
    (collapseOuter D σ).comp (MvPolynomial.C : MvPolynomial σ D →+* _) =
      (MvPolynomial.C : D →+* MvPolynomial σ D).comp MvPolynomial.constantCoeff :=
  MvPolynomial.eval₂Hom_comp_C _ _

/-- The effect of `collapseInner` on constants: it is a retraction of the inclusion of the
coefficient ring. -/
theorem collapseInner_comp_C :
    (collapseInner D σ).comp (MvPolynomial.C : MvPolynomial σ D →+* _) =
      RingHom.id (MvPolynomial σ D) :=
  MvPolynomial.eval₂Hom_comp_C _ _

/-- Translating by minus the variables is evaluation at zero. -/
theorem collapseInner_comp_translationCoaction :
    (collapseInner D σ).comp (translationCoaction D σ) =
      (MvPolynomial.C : D →+* MvPolynomial σ D).comp MvPolynomial.constantCoeff := by
  refine MvPolynomial.ringHom_ext (fun d ↦ ?_) (fun i ↦ ?_)
  · simp [collapseInner]
  · simp [collapseInner]

/-- **The invariant ideal lemma.**  An ideal of a polynomial ring which is stable under the
translation coaction, in the sense that it is carried into the ideal it generates in
`D[x_i][t_i]`, is extended from the coefficient ring.

Geometrically: a closed subscheme of `𝔸^σ_D` stable under all translations is the preimage of a
closed subscheme of `Spec D`. -/
theorem eq_map_comap_C_of_translationCoaction {K : Ideal (MvPolynomial σ D)}
    (hK : ∀ f ∈ K, translationCoaction D σ f ∈
      K.map (MvPolynomial.C : MvPolynomial σ D →+* MvPolynomial σ (MvPolynomial σ D))) :
    K = (K.comap (MvPolynomial.C : D →+* MvPolynomial σ D)).map MvPolynomial.C := by
  have hconst : ∀ f ∈ K, MvPolynomial.constantCoeff f ∈
      K.comap (MvPolynomial.C : D →+* MvPolynomial σ D) := by
    intro f hf
    have h1 : collapseInner D σ (translationCoaction D σ f) ∈
        Ideal.map (collapseInner D σ)
          (K.map (MvPolynomial.C : MvPolynomial σ D →+* MvPolynomial σ (MvPolynomial σ D))) :=
      Ideal.mem_map_of_mem _ (hK f hf)
    rw [Ideal.map_map, collapseInner_comp_C, Ideal.map_id] at h1
    have h2 : collapseInner D σ (translationCoaction D σ f) =
        MvPolynomial.C (MvPolynomial.constantCoeff f) := by
      have h3 := congrArg (fun g : MvPolynomial σ D →+* MvPolynomial σ D ↦ g f)
        (collapseInner_comp_translationCoaction D σ)
      simpa using h3
    rw [h2] at h1
    exact h1
  refine le_antisymm (fun f hf ↦ ?_) (Ideal.map_le_iff_le_comap.mpr le_rfl)
  have h1 : collapseOuter D σ (translationCoaction D σ f) ∈
      Ideal.map (collapseOuter D σ)
        (K.map (MvPolynomial.C : MvPolynomial σ D →+* MvPolynomial σ (MvPolynomial σ D))) :=
    Ideal.mem_map_of_mem _ (hK f hf)
  rw [Ideal.map_map, collapseOuter_comp_C, ← Ideal.map_map] at h1
  have h2 : collapseOuter D σ (translationCoaction D σ f) = f := by
    have h3 := congrArg (fun g : MvPolynomial σ D →+* MvPolynomial σ D ↦ g f)
      (collapseOuter_comp_translationCoaction D σ)
    simpa using h3
  rw [h2] at h1
  exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr hconst) h1

end InvariantIdeal

/-! ## Minimal primes and Krull dimension under a polynomial extension -/

section PolynomialPrimes

variable {A : Type u} [CommRing A] {τ : Type u}

/-- An ideal of the coefficient ring is recovered from the ideal it generates in a polynomial
ring. -/
theorem comap_map_C (p : Ideal A) :
    (p.map (MvPolynomial.C : A →+* MvPolynomial τ A)).comap MvPolynomial.C = p := by
  refine le_antisymm (fun r hr ↦ ?_) Ideal.le_comap_map
  have hle : p.map (MvPolynomial.C : A →+* MvPolynomial τ A) ≤
      RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk p) :
        MvPolynomial τ A →+* MvPolynomial τ (A ⧸ p)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  have h := hle (Ideal.mem_comap.mp hr)
  rw [RingHom.mem_ker, MvPolynomial.map_C] at h
  have h0 : (Ideal.Quotient.mk p) r = 0 :=
    MvPolynomial.C_injective τ (A ⧸ p) (by simpa using h)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

/-- The ideal generated by a prime ideal in a polynomial ring is prime. -/
theorem isPrime_map_C {p : Ideal A} (hp : p.IsPrime) :
    (p.map (MvPolynomial.C : A →+* MvPolynomial τ A)).IsPrime := by
  have hdom : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain_iff_prime p |>.mpr hp
  have hpoly : IsDomain (MvPolynomial τ (A ⧸ p)) := inferInstance
  have h : IsDomain (MvPolynomial τ A ⧸ p.map (MvPolynomial.C : A →+* MvPolynomial τ A)) :=
    MulEquiv.isDomain (MvPolynomial τ (A ⧸ p))
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) p).symm.toRingEquiv.toMulEquiv
  exact (Ideal.Quotient.isDomain_iff_prime _).mp h

/-- The extension of a minimal prime to a polynomial ring is a minimal prime. -/
theorem map_C_mem_minimalPrimes {q : Ideal A} (hq : q ∈ minimalPrimes A) :
    q.map (MvPolynomial.C : A →+* MvPolynomial τ A) ∈ minimalPrimes (MvPolynomial τ A) := by
  rw [minimalPrimes_eq_minimals] at hq ⊢
  refine ⟨isPrime_map_C hq.1, fun b hb hble ↦ ?_⟩
  have hbp : (b.comap (MvPolynomial.C : A →+* MvPolynomial τ A)).IsPrime := hb.comap _
  have hle : b.comap (MvPolynomial.C : A →+* MvPolynomial τ A) ≤ q := by
    rw [← comap_map_C (τ := τ) q]
    exact Ideal.comap_mono hble
  have hq' : q ≤ b.comap (MvPolynomial.C : A →+* MvPolynomial τ A) := hq.2 hbp hle
  exact le_trans (Ideal.map_mono hq') Ideal.map_comap_le

/-- A minimal prime of a polynomial ring is extended from its contraction. -/
theorem map_comap_C_of_mem_minimalPrimes {P : Ideal (MvPolynomial τ A)}
    (hP : P ∈ minimalPrimes (MvPolynomial τ A)) :
    (P.comap (MvPolynomial.C : A →+* MvPolynomial τ A)).map MvPolynomial.C = P := by
  rw [minimalPrimes_eq_minimals] at hP
  have hbp : (P.comap (MvPolynomial.C : A →+* MvPolynomial τ A)).IsPrime := hP.1.comap _
  exact le_antisymm Ideal.map_comap_le (hP.2 (isPrime_map_C hbp) Ideal.map_comap_le)

/-- The contraction of a minimal prime of a polynomial ring is a minimal prime. -/
theorem comap_C_mem_minimalPrimes {P : Ideal (MvPolynomial τ A)}
    (hP : P ∈ minimalPrimes (MvPolynomial τ A)) :
    P.comap (MvPolynomial.C : A →+* MvPolynomial τ A) ∈ minimalPrimes A := by
  have hmap := map_comap_C_of_mem_minimalPrimes hP
  rw [minimalPrimes_eq_minimals] at hP ⊢
  refine ⟨hP.1.comap _, fun b hb hble ↦ ?_⟩
  have h1 : b.map (MvPolynomial.C : A →+* MvPolynomial τ A) ≤ P :=
    Ideal.map_le_iff_le_comap.mpr hble
  have h2 : P ≤ b.map (MvPolynomial.C : A →+* MvPolynomial τ A) :=
    hP.2 (isPrime_map_C hb) h1
  calc P.comap (MvPolynomial.C : A →+* MvPolynomial τ A)
      ≤ (b.map (MvPolynomial.C : A →+* MvPolynomial τ A)).comap MvPolynomial.C :=
        Ideal.comap_mono h2
    _ = b := comap_map_C b

/-- The Krull dimension of the quotient of a polynomial ring by an extended ideal. -/
theorem ringKrullDim_quotient_map_C [Finite τ] (q : Ideal A) [IsNoetherianRing (A ⧸ q)] :
    ringKrullDim (MvPolynomial τ A ⧸ q.map (MvPolynomial.C : A →+* MvPolynomial τ A)) =
      ringKrullDim (A ⧸ q) + Nat.card τ := by
  rw [← ringKrullDim_eq_of_ringEquiv
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) q).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing]

/-- Transport of minimal primes along a ring isomorphism. -/
theorem comap_mem_minimalPrimes_of_ringEquiv {B : Type u} [CommRing B] (e : A ≃+* B)
    {P : Ideal B} (hP : P ∈ minimalPrimes B) :
    P.comap (e : A →+* B) ∈ minimalPrimes A := by
  have h := Ideal.minimalPrimes_comap_of_surjective (f := (e : A →+* B)) e.surjective
    (I := ⊥) hP
  have hbot : (⊥ : Ideal B).comap (e : A →+* B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot (e : A →+* B)).mp e.injective
  rwa [hbot] at h

/-- Transport of the Krull dimension of a quotient along a ring isomorphism. -/
theorem ringKrullDim_quotient_comap_ringEquiv {B : Type u} [CommRing B] (e : A ≃+* B)
    (P : Ideal B) :
    ringKrullDim (A ⧸ P.comap (e : A →+* B)) = ringKrullDim (B ⧸ P) :=
  ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientEquiv _ _ e (Ideal.map_comap_of_surjective (e : A →+* B) e.surjective P).symm)

end PolynomialPrimes

/-! ## Purity of the resolved cone in the polynomial model -/

section Purity

variable {k : Type u} [Field k] {σ : Type u} [Finite σ] {I : Ideal (MvPolynomial σ k)}
variable {E : LinearTwoTermComplex (MvPolynomial σ k ⧸ I)}
variable [Module.Free (MvPolynomial σ k ⧸ I) E.degreeZero]
variable [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero]
variable [Module.Free (MvPolynomial σ k ⧸ I) E.degreeOne]
variable [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeOne]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))

/-- The associated graded ring of an ideal of a Noetherian ring is Noetherian: it is the special
fibre of the deformation space, a quotient of the extended Rees algebra. -/
theorem isNoetherianRing_associatedGradedRing (R : Type u) [CommRing R] [IsNoetherianRing R]
    (J : Ideal R) : IsNoetherianRing (AffineNormalCone.associatedGradedRing R J) :=
  isNoetherianRing_of_ringEquiv (AffineDeformationSpace.specialFibreRing R J)
    (AffineDeformationSpace.specialFibreEquiv R J).symm.toRingEquiv

omit [Module.Free (MvPolynomial σ k ⧸ I) E.degreeOne]
  [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeOne] in
/-- The coordinate ring of the vector bundle `E₁` is Noetherian. -/
theorem isNoetherianRing_bundleRing : IsNoetherianRing (bundleRing φ) :=
  isNoetherianRing_of_ringEquiv
    (MvPolynomial (Module.Free.ChooseBasisIndex (MvPolynomial σ k ⧸ I) E.degreeZero)
      (MvPolynomial σ k ⧸ I))
    (VectorBundle.symTrivialization (MvPolynomial σ k ⧸ I) E.degreeZero).symm.toRingEquiv

omit [Module.Free (MvPolynomial σ k ⧸ I) E.degreeOne]
  [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeOne] in
/-- The coordinate ring of the resolved cone `C(E)` is Noetherian. -/
theorem isNoetherianRing_ring : IsNoetherianRing (ring φ) := by
  have hb := isNoetherianRing_bundleRing φ
  infer_instance

/-- The Krull dimension of the ambient polynomial ring of the model is the number of
variables. -/
theorem ringKrullDim_mvPolynomial_field :
    ringKrullDim (MvPolynomial σ k) = ((Nat.card σ : ℕ∞)) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  rfl

/-- **The product `C ×_X E₀` is a polynomial ring over the normal cone.**  Choosing a basis of
`E⁰` trivialises the bundle `E₀`, so that `gr_I(R) ⊗ Sym(E⁰)` becomes a polynomial ring in
`rank E⁰` variables over `gr_I(R)`. -/
noncomputable def productRingEquiv :
    productRing φ ≃+*
      MvPolynomial (Module.Free.ChooseBasisIndex (MvPolynomial σ k ⧸ I) E.degreeOne)
        (AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I) :=
  (Algebra.TensorProduct.congr
      (AlgEquiv.refl :
        AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I ≃ₐ[MvPolynomial σ k ⧸ I]
          AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I)
      (VectorBundle.symTrivialization (MvPolynomial σ k ⧸ I) E.degreeOne)).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv (MvPolynomial σ k ⧸ I)
      (AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I)).toRingEquiv

omit [Module.Free (MvPolynomial σ k ⧸ I) E.degreeZero]
  [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero] in
/-- **Purity of `C ×_X E₀`.**  Granting the dimension formula for the extended Rees algebra of
`I`, every irreducible component of the product `C ×_X E₀` has dimension `|σ| + rank E⁰`: the
normal cone is pure of dimension `|σ| = dim R` and the bundle `E₀` adds its rank. -/
theorem ringKrullDim_quotient_productRing (hI : I ≠ ⊤)
    (hdf : HasDimensionFormula (AffineDeformationSpace.extendedRees (MvPolynomial σ k) I))
    {P : Ideal (productRing φ)} (hP : P ∈ minimalPrimes (productRing φ)) :
    ringKrullDim (productRing φ ⧸ P) =
      ((Nat.card σ + Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℕ) : ℕ∞) := by
  have hnt : Nontrivial (MvPolynomial σ k ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hgr := isNoetherianRing_associatedGradedRing (MvPolynomial σ k) I
  have hQmin := comap_mem_minimalPrimes_of_ringEquiv (productRingEquiv φ).symm hP
  have hdimQ := ringKrullDim_quotient_comap_ringEquiv (productRingEquiv φ).symm P
  have hq' := comap_C_mem_minimalPrimes hQmin
  have hQeq := map_comap_C_of_mem_minimalPrimes hQmin
  have hbase := AffineDeformationSpace.ringKrullDim_quotient_eq_of_mem_minimalPrimes
    (MvPolynomial σ k) I k hI (Nat.card σ) ringKrullDim_mvPolynomial_field hdf hq'
  have hcard : Nat.card (Module.Free.ChooseBasisIndex (MvPolynomial σ k ⧸ I) E.degreeOne) =
      Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne :=
    VectorBundle.card_chooseBasisIndex (MvPolynomial σ k ⧸ I) E.degreeOne
  rw [← hdimQ, ← hQeq, ringKrullDim_quotient_map_C, hbase, hcard]
  push_cast
  rfl

/-! ### The splitting of the mapping-cone surjection -/

omit [Finite σ] [Module.Free (MvPolynomial σ k ⧸ I) E.degreeZero]
  [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero]
  [Module.Free (MvPolynomial σ k ⧸ I) E.degreeOne]
  [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeOne] in
/-- **The mapping-cone surjection of an obstruction theory splits in the polynomial model.**
The term `L⁰ = (R ⧸ I) ⊗ Ω[R⁄k]` of the conormal complex is free on the differentials of the
coordinates, hence projective, and `coneBeta φ : L⁻¹ ⊕ E⁰ → L⁰` is surjective for an obstruction
theory; so the surjection admits a linear section.

This is the first step towards `IsPolynomialTrivialisation` below: a section identifies
`L⁻¹ ⊕ E⁰` with `ker (coneBeta φ) ⊕ L⁰`, hence `Sym(L⁻¹ ⊕ E⁰)` with a polynomial ring in `|σ|`
variables over `Sym(ker (coneBeta φ))`, the variables being the coordinates of the acting
tangent bundle `T_M|_U`. -/
theorem exists_rightInverse_coneBeta (h : PicardCriteria.IsObstructionTheory φ) :
    ∃ s : (conormalComplex k (MvPolynomial σ k) I).degreeOne →ₗ[MvPolynomial σ k ⧸ I]
        (conormalComplex k (MvPolynomial σ k) I).degreeZero × E.degreeOne,
      (PicardCriteria.coneBeta φ) ∘ₗ s = LinearMap.id :=
  Module.projective_lifting_property _ LinearMap.id h.exact_cone.1

/-- **The trivialisation of the `T_M|_U`-torsor `C ×_X E₀ → C(E)`.**  This is the statement that
the coordinate ring `gr_I(R) ⊗ Sym(E⁰)` of `C ×_X E₀` is a polynomial ring in `|σ|` variables
over the coordinate ring `ring φ` of the resolved cone, compatibly with the inclusion
`toProduct φ`.

Geometrically, `C ×_X E₀ → C(E)` is a torsor under the tangent bundle `T_M|_U = U × 𝔸^σ` of the
ambient affine space, and the statement is that this torsor is trivial.  It is *not* proved
here: it is an explicit hypothesis of the purity statements below.  The intended proof splits
the surjection `L⁻¹ ⊕ E⁰ → L⁰` of an obstruction theory and identifies the ideal of `C(E)` with
an ideal invariant under the translation coaction, to which
`eq_map_comap_C_of_translationCoaction` applies. -/
def IsPolynomialTrivialisation : Prop :=
  ∃ e : productRing φ ≃+* MvPolynomial σ (ring φ),
    ∀ a : ring φ, e (toProduct φ a) = MvPolynomial.C a

/-- **Purity of the resolved cone.**  Granting the dimension formula for the extended Rees
algebra of `I` and the trivialisation of the torsor `C ×_X E₀ → C(E)`, every irreducible
component of `C(E)` has dimension `b = rank E⁰`: the components of `C ×_X E₀` have dimension
`|σ| + b` and the torsor has relative dimension `|σ|`. -/
theorem ringKrullDim_quotient_ring_eq (hI : I ≠ ⊤)
    (hdf : HasDimensionFormula (AffineDeformationSpace.extendedRees (MvPolynomial σ k) I))
    (htriv : IsPolynomialTrivialisation φ)
    {q : Ideal (ring φ)} (hq : q ∈ minimalPrimes (ring φ)) :
    ringKrullDim (ring φ ⧸ q) =
      ((Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℕ∞)) := by
  obtain ⟨e, -⟩ := htriv
  have hring := isNoetherianRing_ring φ
  have hQ : q.map (MvPolynomial.C : ring φ →+* MvPolynomial σ (ring φ)) ∈
      minimalPrimes (MvPolynomial σ (ring φ)) := map_C_mem_minimalPrimes hq
  have h1 := ringKrullDim_quotient_productRing φ hI hdf
    (comap_mem_minimalPrimes_of_ringEquiv e hQ)
  have h2 := ringKrullDim_quotient_comap_ringEquiv e
    (q.map (MvPolynomial.C : ring φ →+* MvPolynomial σ (ring φ)))
  have h3 : ringKrullDim (MvPolynomial σ (ring φ) ⧸
      q.map (MvPolynomial.C : ring φ →+* MvPolynomial σ (ring φ))) =
      ringKrullDim (ring φ ⧸ q) + Nat.card σ := ringKrullDim_quotient_map_C q
  rw [h2, h3] at h1
  have hprime : q.IsPrime := hq.1.1
  have hnontriv : Nontrivial (ring φ ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr hprime.ne_top
  have hbot : ringKrullDim (ring φ ⧸ q) ≠ ⊥ := by
    intro h
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := ring φ ⧸ q)
    rw [h] at h0
    simp at h0
  obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.mp hbot
  rw [← hy] at h1 ⊢
  have hfin : ((Nat.card σ : ℕ∞)) ≠ ⊤ := by simp
  have h4 : y + (Nat.card σ : ℕ∞) =
      (Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℕ∞) + (Nat.card σ : ℕ∞) := by
    have h5 : y + (Nat.card σ : ℕ∞) =
        ((Nat.card σ + Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℕ) : ℕ∞) := by
      exact_mod_cast h1
    rw [h5]
    push_cast
    exact add_comm _ _
  have hle1 : y ≤ (Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℕ∞) :=
    (ENat.add_le_add_iff_right hfin).mp h4.le
  have hle2 : (Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℕ∞) ≤ y :=
    (ENat.add_le_add_iff_right hfin).mp h4.ge
  rw [le_antisymm hle1 hle2]

/-! ### The certified dimension function -/

/-- A point of an affine scheme is maximal for the specialisation order (that is, it is the
generic point of an irreducible component) exactly when the corresponding prime ideal is a
minimal prime. -/
theorem mem_minimalPrimes_of_isMax {A : Type u} [CommRing A]
    (x : ↥(_root_.AlgebraicGeometry.Spec (CommRingCat.of A)))
    (hx : IsMax ((VectorBundle.specOrderIso A) x)) :
    (x : PrimeSpectrum A).asIdeal ∈ minimalPrimes A :=
  PrimeSpectrum.isMin_iff.mp hx

/-- **Purity in the form used by the Chow groups.**  Every generic point of an irreducible
component of `C(E)` has dimension `b = rank E⁰` for the certified dimension function of
`C(E)`; this is the hypothesis `pure` of `cyclesOfDimension.fundamental`. -/
theorem dimension_eq_of_isMax (dimC : DimensionFunction (scheme φ)) (hI : I ≠ ⊤)
    (hdf : HasDimensionFormula (AffineDeformationSpace.extendedRees (MvPolynomial σ k) I))
    (htriv : IsPolynomialTrivialisation φ) (x : ↥(scheme φ)) (hx : IsMax x) :
    dimC x = (Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℤ) := by
  have hmin := mem_minimalPrimes_of_isMax x
    ((VectorBundle.specOrderIso (ring φ)).isMax_apply.mpr hx)
  have hdim := ringKrullDim_quotient_ring_eq φ hI hdf htriv hmin
  have hco := GromovWitten.Algebra.PrimeSpectrum.coheight_eq_ringKrullDim_quotient
    (x : PrimeSpectrum (ring φ))
  have hdimf := VectorBundle.coheight_eq_dimension (ring φ) dimC x
  rw [hdim, hdimf] at hco
  have hnat : Int.toNat (dimC x) = Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne := by
    exact_mod_cast hco
  rw [← Int.toNat_of_nonneg (dimC.nonnegative x), hnat]

/-- The same purity statement on the ambient bundle `E₁`, along the closed immersion
`toBundle φ : C(E) ↪ E₁`: the image of a generic point of an irreducible component of `C(E)` has
dimension `b = rank E⁰` for the certified dimension function of `E₁`. -/
theorem dimension_toBundle_eq_of_isMax (dimC : DimensionFunction (scheme φ))
    (dimB : DimensionFunction (bundleSpace φ)) (hI : I ≠ ⊤)
    (hdf : HasDimensionFormula (AffineDeformationSpace.extendedRees (MvPolynomial σ k) I))
    (htriv : IsPolynomialTrivialisation φ) (x : ↥(scheme φ)) (hx : IsMax x) :
    dimB ((toBundle φ).base x) = (Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℤ) := by
  rw [← DimensionFunction.apply_eq_of_isClosedImmersion dimC dimB (toBundle φ) x]
  exact dimension_eq_of_isMax φ dimC hI hdf htriv x hx

end Purity

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ResolvedCone
