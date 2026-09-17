/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Cones.Affine
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Deformation to the normal cone: the affine Rees deformation space

For an ideal `I` of a commutative ring `R`, the extended Rees algebra
`R[It, t⁻¹] = ⨁_{n ∈ ℤ} Iⁿ tⁿ ⊆ R[t, t⁻¹]` (with `Iⁿ = R` for `n ≤ 0`) is the coordinate ring
of the deformation space `M° → 𝔸¹` of the closed subscheme `Spec (R/I) ⊆ Spec R`.  This file
constructs it as a subalgebra of the Laurent polynomial ring and proves the two fibre
identifications that make it a deformation to the normal cone:

* the parameter `u = t⁻¹` is a nonzerodivisor, and the special fibre `R[It, t⁻¹] / (u)` is the
  associated graded ring `gr_I(R) = Rees_I(R) / I·Rees_I(R)`, the coordinate ring of the affine
  normal cone `AffineNormalCone.scheme R I` (`specialFibreEquiv`);
* inverting `u` recovers the Laurent polynomial ring `R[t, t⁻¹]`, so the generic fibre over
  `𝔾_m ⊆ 𝔸¹` is the trivial family `Spec R × 𝔾_m` (`isLocalization_parameter`).

The constructions are packaged as schemes: the deformation space `space R I`, its structure
map `toLine R I` to the affine line, the closed immersion of the normal cone as the fibre over
the origin, and the open immersion of the trivial family over the complement of the origin.
-/

open CategoryTheory Limits AlgebraicGeometry LaurentPolynomial

namespace GromovWitten.AlgebraicGeometry

namespace AffineDeformationSpace

universe u

noncomputable section

variable (R : Type u) [CommRing R] (I : Ideal R)

/-! ### The extended Rees algebra -/

/-- Membership in the extended Rees algebra: the coefficient of `tⁿ` lies in `I ^ n` for
`n ≥ 0` and is unrestricted for `n ≤ 0`. -/
def IsExtendedRees (f : R[T;T⁻¹]) : Prop := ∀ n : ℤ, f.coeff n ∈ I ^ n.toNat

theorem isExtendedRees_C_mul_T {a : R} {n : ℤ} (ha : a ∈ I ^ n.toNat) :
    IsExtendedRees R I (LaurentPolynomial.C a * T n) := by
  intro m
  rw [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with h
  · subst h
    exact ha
  · exact zero_mem _

theorem isExtendedRees_of_nonpos {a : R} {n : ℤ} (hn : n ≤ 0) :
    IsExtendedRees R I (LaurentPolynomial.C a * T n) := by
  apply isExtendedRees_C_mul_T
  rw [Int.toNat_eq_zero.mpr hn, pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

theorem isExtendedRees_C (a : R) : IsExtendedRees R I (LaurentPolynomial.C a) := by
  simpa using isExtendedRees_of_nonpos R I (a := a) (n := 0) le_rfl

theorem isExtendedRees_toLaurent {p : Polynomial R} (hp : p ∈ reesAlgebra I) :
    IsExtendedRees R I p.toLaurent := by
  intro n
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have h : p.toLaurent.coeff m = p.coeff m := by
      rw [LaurentPolynomial.coeff_toLaurent]
      exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ m
    rw [h, Int.toNat_natCast]
    exact (mem_reesAlgebra_iff I p).mp hp m
  · have h : p.toLaurent.coeff n = 0 := by
      rw [LaurentPolynomial.coeff_toLaurent]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨m, hm⟩
      have : (0 : ℤ) ≤ m := Int.natCast_nonneg m
      change (m : ℤ) = n at hm
      omega
    rw [h]
    exact zero_mem _

/-- The extended Rees algebra `R[It, t⁻¹]` as a subalgebra of the Laurent polynomials. -/
def extendedRees : Subalgebra R R[T;T⁻¹] where
  carrier := {f | IsExtendedRees R I f}
  mul_mem' := by
    intro f g hf hg n
    classical
    rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
    refine Ideal.sum_mem _ fun m₁ _ ↦ ?_
    rw [Finsupp.sum]
    refine Ideal.sum_mem _ fun m₂ _ ↦ ?_
    split_ifs with h
    · have hprod := Ideal.mul_mem_mul (hf m₁) (hg m₂)
      rw [← pow_add] at hprod
      exact Ideal.pow_le_pow_right (by omega) hprod
    · exact zero_mem _
  one_mem' := by
    have : (1 : R[T;T⁻¹]) = LaurentPolynomial.C 1 := (map_one _).symm
    change IsExtendedRees R I 1
    rw [this]
    exact isExtendedRees_C R I 1
  add_mem' := by
    intro f g hf hg n
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact Ideal.add_mem _ (hf n) (hg n)
  algebraMap_mem' := fun r ↦ by
    change IsExtendedRees R I _
    rw [← C_eq_algebraMap]
    exact isExtendedRees_C R I r

theorem mem_extendedRees_iff (f : R[T;T⁻¹]) :
    f ∈ extendedRees R I ↔ ∀ n : ℤ, f.coeff n ∈ I ^ n.toNat := Iff.rfl

theorem coeff_mem_of_mem {f : R[T;T⁻¹]} (hf : f ∈ extendedRees R I) (n : ℤ) :
    f.coeff n ∈ I ^ n.toNat := hf n

/-- The deformation parameter `u = t⁻¹`. -/
def parameter : extendedRees R I :=
  ⟨T (-1), by
    have h := isExtendedRees_of_nonpos R I (a := (1 : R)) (n := -1) (by norm_num)
    rwa [map_one, one_mul] at h⟩

@[simp] theorem coe_parameter : (parameter R I : R[T;T⁻¹]) = T (-1) := rfl

/-- The degree-one element `a t` for `a ∈ I`. -/
def degreeOne (a : I) : extendedRees R I :=
  ⟨LaurentPolynomial.C (a : R) * T 1, isExtendedRees_C_mul_T R I (by simp [a.2])⟩

@[simp] theorem coe_degreeOne (a : I) :
    (degreeOne R I a : R[T;T⁻¹]) = LaurentPolynomial.C (a : R) * T 1 := rfl

/-- Multiplying `a t` by the parameter gives `a`. -/
theorem parameter_mul_degreeOne (a : I) :
    parameter R I * degreeOne R I a = algebraMap R (extendedRees R I) a := by
  apply Subtype.ext
  change T (-1) * (LaurentPolynomial.C (a : R) * T 1) = algebraMap R R[T;T⁻¹] (a : R)
  rw [T_mul, mul_T_assoc, ← C_eq_algebraMap]
  simp

/-- The parameter is a nonzerodivisor of the extended Rees algebra: the deformation space is
`u`-torsion-free over the affine line. -/
theorem parameter_isSMulRegular : IsSMulRegular (extendedRees R I) (parameter R I) := by
  intro f g h
  apply Subtype.ext
  have h' : (T (-1) : R[T;T⁻¹]) * (f : R[T;T⁻¹]) = T (-1) * (g : R[T;T⁻¹]) :=
    congrArg Subtype.val h
  exact (isUnit_T (-1)).mul_left_cancel h'

/-- The structure map from the polynomial ring `R[u]` of the affine line, sending `u` to the
deformation parameter. -/
def structureMap : Polynomial R →ₐ[R] extendedRees R I := Polynomial.aeval (parameter R I)

@[simp] theorem structureMap_X : structureMap R I Polynomial.X = parameter R I :=
  Polynomial.aeval_X _

/-! ### Coefficient calculus -/

/-- The coefficient of `f · tⁿ`. -/
theorem coeff_mul_T (f : R[T;T⁻¹]) (n m : ℤ) : (f * T n).coeff m = f.coeff (m - n) := by
  classical
  have h := AddMonoidAlgebra.coeff_mul_single_eq_coeff_mul (x := f) (m := n) (r := (1 : R))
    (m₁ := m) (m - n) (fun m' _ ↦ by constructor <;> intro h <;> omega)
  rw [mul_one] at h
  exact h

/-- Every Laurent polynomial is the sum of its monomials. -/
theorem eq_sum_support (f : R[T;T⁻¹]) :
    f = ∑ n ∈ f.coeff.support, LaurentPolynomial.C (f.coeff n) * T n := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  exact single_eq_C_mul_T _ _

/-! ### The special fibre is the associated graded ring -/

/-- The Rees algebra maps into the extended Rees algebra. -/
def reesToExtended : reesAlgebra I →ₐ[R] extendedRees R I :=
  AlgHom.codRestrict (Polynomial.toLaurentAlg.comp (reesAlgebra I).val) (extendedRees R I)
    fun p ↦ isExtendedRees_toLaurent R I p.2

@[simp] theorem coe_reesToExtended (p : reesAlgebra I) :
    (reesToExtended R I p : R[T;T⁻¹]) = Polynomial.toLaurent (p : Polynomial R) := rfl

/-- The ideal generated by the parameter: the fibre over the origin of the affine line. -/
abbrev parameterIdeal : Ideal (extendedRees R I) := Ideal.span {parameter R I}

/-- The coordinate ring of the special fibre. -/
abbrev specialFibreRing : Type u := extendedRees R I ⧸ parameterIdeal R I

/-- The Rees algebra maps onto the special fibre. -/
def reesToSpecialFibre : reesAlgebra I →ₐ[R] specialFibreRing R I :=
  (Ideal.Quotient.mkₐ R (parameterIdeal R I)).comp (reesToExtended R I)

theorem reesToSpecialFibre_apply (p : reesAlgebra I) :
    reesToSpecialFibre R I p = Ideal.Quotient.mk _ (reesToExtended R I p) := rfl

/-- An element of the extended Rees algebra of the form `u · h` is zero in the special
fibre. -/
theorem mk_eq_zero_of_eq_parameter_mul {f : extendedRees R I} {h : R[T;T⁻¹]}
    (hh : h ∈ extendedRees R I) (hf : (f : R[T;T⁻¹]) = h * T (-1)) :
    Ideal.Quotient.mk (parameterIdeal R I) f = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨⟨h, hh⟩, Subtype.ext hf.symm⟩

/-- Every element of the extended Rees algebra is, modulo the parameter, the image of a Rees
element: the positive-degree part. -/
theorem exists_reesToExtended_add_parameter_mul (f : R[T;T⁻¹]) (hf : f ∈ extendedRees R I) :
    ∃ (p : reesAlgebra I) (h : R[T;T⁻¹]), h ∈ extendedRees R I ∧
      f = Polynomial.toLaurent (p : Polynomial R) + h * T (-1) := by
  classical
  let s := f.coeff.support
  let p₀ : Polynomial R :=
    ∑ n ∈ s with 0 ≤ n, Polynomial.monomial n.toNat (f.coeff n)
  have hp₀ : p₀ ∈ reesAlgebra I := by
    refine Subalgebra.sum_mem _ fun n hn ↦ ?_
    exact reesAlgebra.monomial_mem.mpr (hf n)
  let h : R[T;T⁻¹] := ∑ n ∈ s with ¬ 0 ≤ n, LaurentPolynomial.C (f.coeff n) * T (n + 1)
  have hh : h ∈ extendedRees R I := by
    refine Subalgebra.sum_mem _ fun n hn ↦ ?_
    have hn' : ¬ 0 ≤ n := (Finset.mem_filter.mp hn).2
    exact isExtendedRees_of_nonpos R I (by omega)
  refine ⟨⟨p₀, hp₀⟩, h, hh, ?_⟩
  have e1 : Polynomial.toLaurent p₀ =
      ∑ n ∈ s with 0 ≤ n, LaurentPolynomial.C (f.coeff n) * T n := by
    simp only [p₀, map_sum]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn' : 0 ≤ n := (Finset.mem_filter.mp hn).2
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow,
      Int.toNat_of_nonneg hn']
  have e2 : h * T (-1) = ∑ n ∈ s with ¬ 0 ≤ n, LaurentPolynomial.C (f.coeff n) * T n := by
    simp only [h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [mul_T_assoc]
    congr 2
    omega
  rw [e1, e2, Finset.sum_filter_add_sum_filter_not]
  exact eq_sum_support R f

/-- The Rees algebra surjects onto the special fibre. -/
theorem reesToSpecialFibre_surjective : Function.Surjective (reesToSpecialFibre R I) := by
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨p, h, hh, hf⟩ := exists_reesToExtended_add_parameter_mul R I f f.2
  refine ⟨p, ?_⟩
  rw [reesToSpecialFibre_apply]
  have hmem : h * T (-1) ∈ extendedRees R I := (extendedRees R I).mul_mem hh (parameter R I).2
  have hsplit : f = reesToExtended R I p + ⟨h * T (-1), hmem⟩ := Subtype.ext hf
  rw [hsplit, map_add, mk_eq_zero_of_eq_parameter_mul R I (f := ⟨h * T (-1), hmem⟩) hh rfl,
    add_zero]

/-- A Rees element whose degree-`m` coefficient lies in `I ^ (m + 1)` for every `m` belongs
to `I · Rees_I(R)`.  This is the converse of
`AffineNormalCone.coeff_mem_pow_succ_of_mem_map_rees`. -/
theorem mem_map_of_forall_coeff_mem_pow_succ (q : reesAlgebra I)
    (hq : ∀ m : ℕ, (q : Polynomial R).coeff m ∈ I ^ (m + 1)) :
    q ∈ Ideal.map (algebraMap R (reesAlgebra I)) I := by
  classical
  have key : ∀ (i : ℕ) (c : R), c ∈ I ^ (i + 1) →
      ∃ hc : c ∈ I ^ i, (⟨Polynomial.monomial i c, reesAlgebra.monomial_mem.mpr hc⟩ :
        reesAlgebra I) ∈ Ideal.map (algebraMap R (reesAlgebra I)) I := by
    intro i c hc
    rw [pow_succ'] at hc
    refine Submodule.mul_induction_on hc ?_ ?_
    · intro a ha b hb
      refine ⟨Ideal.mul_mem_left _ a hb, ?_⟩
      have : (⟨Polynomial.monomial i (a * b),
            reesAlgebra.monomial_mem.mpr (Ideal.mul_mem_left _ a hb)⟩ : reesAlgebra I) =
          algebraMap R (reesAlgebra I) a * ⟨Polynomial.monomial i b,
            reesAlgebra.monomial_mem.mpr hb⟩ := by
        apply Subtype.ext
        change Polynomial.monomial i (a * b) = Polynomial.C a * Polynomial.monomial i b
        rw [Polynomial.C_mul_monomial]
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
      refine ⟨Ideal.add_mem _ hx hy, ?_⟩
      have : (⟨Polynomial.monomial i (x + y),
            reesAlgebra.monomial_mem.mpr (Ideal.add_mem _ hx hy)⟩ : reesAlgebra I) =
          ⟨Polynomial.monomial i x, reesAlgebra.monomial_mem.mpr hx⟩ +
            ⟨Polynomial.monomial i y, reesAlgebra.monomial_mem.mpr hy⟩ := by
        apply Subtype.ext
        change Polynomial.monomial i (x + y) =
          Polynomial.monomial i x + Polynomial.monomial i y
        rw [map_add]
      rw [this]
      exact Ideal.add_mem _ hx' hy'
  have hsum : q = ∑ i ∈ (q : Polynomial R).support,
      (⟨Polynomial.monomial i ((q : Polynomial R).coeff i),
        reesAlgebra.monomial_mem.mpr ((mem_reesAlgebra_iff I _).mp q.2 i)⟩ : reesAlgebra I) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Polynomial.as_sum_support (q : Polynomial R)
  rw [hsum]
  refine Ideal.sum_mem _ fun i _ ↦ ?_
  obtain ⟨_, h⟩ := key i _ (hq i)
  exact h

/-- The kernel of the map from the Rees algebra to the special fibre is `I · Rees_I(R)`. -/
theorem ker_reesToSpecialFibre :
    RingHom.ker (reesToSpecialFibre R I) = Ideal.map (algebraMap R (reesAlgebra I)) I := by
  ext q
  rw [RingHom.mem_ker, reesToSpecialFibre_apply]
  constructor
  · intro hq
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hq
    obtain ⟨a, ha⟩ := hq
    have ha' : (a : R[T;T⁻¹]) * T (-1) = Polynomial.toLaurent (q : Polynomial R) :=
      congrArg Subtype.val ha
    apply mem_map_of_forall_coeff_mem_pow_succ
    intro m
    have hm : (Polynomial.toLaurent (q : Polynomial R)).coeff m = (q : Polynomial R).coeff m := by
      rw [LaurentPolynomial.coeff_toLaurent]
      exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ m
    rw [← hm, ← ha', coeff_mul_T]
    have := a.2 (m - (-1))
    have hexp : (m - (-1) : ℤ).toNat = m + 1 := by omega
    rwa [hexp] at this
  · intro hq
    have hcoeff := AffineNormalCone.coeff_mem_pow_succ_of_mem_map_rees R I hq
    let h : R[T;T⁻¹] := Polynomial.toLaurent (q : Polynomial R) * T 1
    have hh : h ∈ extendedRees R I := by
      intro m
      rw [coeff_mul_T]
      rcases le_or_gt 1 m with hm | hm
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, m - 1 = k := ⟨(m - 1).toNat, by omega⟩
        rw [hk]
        have hcast : (Polynomial.toLaurent (q : Polynomial R)).coeff k =
            (q : Polynomial R).coeff k := by
          rw [LaurentPolynomial.coeff_toLaurent]
          exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ k
        rw [hcast]
        have hexp : m.toNat = k + 1 := by omega
        rw [hexp]
        exact hcoeff k
      · have : (Polynomial.toLaurent (q : Polynomial R)).coeff (m - 1) = 0 := by
          rw [LaurentPolynomial.coeff_toLaurent]
          apply Finsupp.mapDomain_of_notMem_range
          rintro ⟨k, hk⟩
          change (k : ℤ) = m - 1 at hk
          omega
        rw [this]
        exact zero_mem _
    apply mk_eq_zero_of_eq_parameter_mul R I hh
    change Polynomial.toLaurent (q : Polynomial R) = h * T (-1)
    simp only [h, mul_T_assoc]
    simp

/-- The special fibre of the deformation space is the associated graded ring, the coordinate
ring of the affine normal cone. -/
def specialFibreEquiv : AffineNormalCone.associatedGradedRing R I ≃ₐ[R] specialFibreRing R I :=
  (Ideal.quotientEquivAlgOfEq R (ker_reesToSpecialFibre R I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (reesToSpecialFibre_surjective R I))

theorem specialFibreEquiv_mk (p : reesAlgebra I) :
    specialFibreEquiv R I (Ideal.Quotient.mk _ p) = reesToSpecialFibre R I p := rfl

/-! ### The generic fibre is the trivial family -/

/-- Inverting the parameter recovers the Laurent polynomial ring: away from the origin of the
affine line, the deformation space is `Spec R × 𝔾ₘ`. -/
theorem isLocalization_parameter : IsLocalization.Away (parameter R I) R[T;T⁻¹] where
  map_units := by
    rintro ⟨t, ht⟩
    obtain ⟨n, rfl⟩ := ht
    change IsUnit ((parameter R I ^ n : extendedRees R I) : R[T;T⁻¹])
    rw [Subalgebra.coe_pow, coe_parameter, T_pow]
    exact isUnit_T _
  surj := by
    intro f
    obtain ⟨n, f', hf⟩ := f.exists_T_pow
    let N : ℕ := f'.natDegree
    let g : R[T;T⁻¹] := Polynomial.toLaurent f' * T (-((n + N : ℕ) : ℤ))
    have hg : g ∈ extendedRees R I := by
      intro m
      rw [coeff_mul_T]
      rcases le_or_gt m 0 with hm | hm
      · rw [Int.toNat_eq_zero.mpr hm, pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, m - -((n + N : ℕ) : ℤ) = k := ⟨(m + (n + N : ℕ)).toNat, by omega⟩
        rw [hk]
        have hcast : (Polynomial.toLaurent f').coeff k = f'.coeff k := by
          rw [LaurentPolynomial.coeff_toLaurent]
          exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ k
        rw [hcast, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        exact zero_mem _
    refine ⟨(⟨g, hg⟩, ⟨parameter R I ^ N, N, rfl⟩), ?_⟩
    change f * ((parameter R I ^ N : extendedRees R I) : R[T;T⁻¹]) = g
    rw [Subalgebra.coe_pow, coe_parameter, T_pow]
    simp only [g]
    rw [hf, mul_T_assoc]
    congr 2
    push_cast
    ring
  exists_of_eq := by
    intro x y h
    exact ⟨1, by rw [Subtype.ext (h : (x : R[T;T⁻¹]) = y)]⟩

/-- The generic fibre of the deformation space, identified with the Laurent polynomial ring. -/
def genericFibreEquiv :
    haveI := isLocalization_parameter R I
    Localization.Away (parameter R I) ≃ₐ[extendedRees R I] R[T;T⁻¹] :=
  haveI := isLocalization_parameter R I
  IsLocalization.algEquiv (Submonoid.powers (parameter R I)) _ _

/-! ### The deformation space as a scheme -/

/-- The affine deformation space `M° = Spec R[It, t⁻¹]`. -/
abbrev space : Scheme.{u} := Spec (.of (extendedRees R I))

/-- The structure morphism `M° → 𝔸¹` to the affine line. -/
def toLine : space R I ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (structureMap R I).toRingHom)

/-- The special fibre `Spec (R[It, t⁻¹] / (u))`. -/
abbrev specialFibre : Scheme.{u} := Spec (.of (specialFibreRing R I))

/-- The closed immersion of the special fibre into the deformation space. -/
def specialFibreι : specialFibre R I ⟶ space R I :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (parameterIdeal R I)))

instance specialFibreι_isClosedImmersion : IsClosedImmersion (specialFibreι R I) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The special fibre is the affine normal cone. -/
def normalConeIsoSpecialFibre : AffineNormalCone.scheme R I ≅ specialFibre R I :=
  Scheme.Spec.mapIso (specialFibreEquiv R I).toRingEquiv.toCommRingCatIso.symm.op

/-- The normal cone embeds as a closed subscheme of the deformation space. -/
def normalConeι : AffineNormalCone.scheme R I ⟶ space R I :=
  (normalConeIsoSpecialFibre R I).hom ≫ specialFibreι R I

instance normalConeι_isClosedImmersion : IsClosedImmersion (normalConeι R I) := by
  unfold normalConeι
  infer_instance

/-- The generic fibre `Spec R[t, t⁻¹] = Spec R × 𝔾ₘ` of the deformation space. -/
abbrev genericFibre : Scheme.{u} := Spec (.of R[T;T⁻¹])

/-- The open immersion of the generic fibre into the deformation space. -/
def genericFibreι : genericFibre R ⟶ space R I :=
  Spec.map (CommRingCat.ofHom (algebraMap (extendedRees R I) R[T;T⁻¹]))

instance genericFibreι_isOpenImmersion : IsOpenImmersion (genericFibreι R I) :=
  haveI := isLocalization_parameter R I
  IsOpenImmersion.of_isLocalization (S := R[T;T⁻¹]) (parameter R I)

/-- The image of the generic fibre is the locus where the parameter is invertible. -/
theorem range_genericFibreι :
    Set.range (genericFibreι R I) = (PrimeSpectrum.basicOpen (parameter R I)).1 :=
  haveI := isLocalization_parameter R I
  PrimeSpectrum.localization_away_comap_range R[T;T⁻¹] (parameter R I)


/-! ### The fibre over `u = 1` is the original scheme -/

/-- Evaluation of a Laurent polynomial at `t = 1`. -/
def evalOneLaurent : R[T;T⁻¹] →+* R := LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ)

theorem evalOneLaurent_C_mul_T (a : R) (n : ℤ) :
    evalOneLaurent R (LaurentPolynomial.C a * T n) = a := by
  rw [evalOneLaurent, eval₂_C_mul_T]
  simp

theorem evalOneLaurent_T (n : ℤ) : evalOneLaurent R (T n) = 1 := by
  rw [evalOneLaurent, eval₂_T]
  simp

/-- Evaluation at `t = 1` on the extended Rees algebra: the coordinate map of the fibre of the
deformation space over the point `u = 1` of the affine line. -/
def evalOne : extendedRees R I →ₐ[R] R where
  toRingHom := (evalOneLaurent R).comp (extendedRees R I).val.toRingHom
  commutes' r := by
    change evalOneLaurent R (algebraMap R R[T;T⁻¹] r) = r
    rw [← C_eq_algebraMap, evalOneLaurent, eval₂_C]
    rfl

theorem evalOne_apply (f : extendedRees R I) : evalOne R I f = evalOneLaurent R f := rfl

theorem evalOne_surjective : Function.Surjective (evalOne R I) :=
  fun r ↦ ⟨algebraMap R _ r, (evalOne R I).commutes r⟩

theorem evalOne_parameter : evalOne R I (parameter R I) = 1 := by
  rw [evalOne_apply, coe_parameter, evalOneLaurent_T]

/-- `tᵐ - 1` is divisible by `u - 1 = t⁻¹ - 1`, with a quotient whose products with elements
of `I ^ m` lie in the extended Rees algebra. -/
theorem exists_T_sub_one_eq (m : ℤ) : ∃ g : R[T;T⁻¹], T m - 1 = (T (-1) - 1) * g ∧
    ∀ a ∈ I ^ m.toNat, LaurentPolynomial.C a * g ∈ extendedRees R I := by
  induction m using Int.induction_on with
  | zero =>
    refine ⟨0, by simp, fun a _ ↦ ?_⟩
    rw [mul_zero]
    exact zero_mem _
  | succ i ih =>
    obtain ⟨g, hg, hmem⟩ := ih
    refine ⟨g - T ((i : ℤ) + 1), ?_, ?_⟩
    · have h1 : ((T (-1) - 1 : R[T;T⁻¹])) * T ((i : ℤ) + 1) = T (i : ℤ) - T ((i : ℤ) + 1) := by
        rw [sub_mul, one_mul, ← T_add]
        congr 2
        ring
      rw [mul_sub, ← hg, h1]
      ring
    · intro a ha
      rw [mul_sub]
      refine (extendedRees R I).sub_mem (hmem a ?_) (isExtendedRees_C_mul_T R I ha)
      exact Ideal.pow_le_pow_right (by omega) ha
  | pred i ih =>
    obtain ⟨g, hg, hmem⟩ := ih
    refine ⟨g + T (-(i : ℤ)), ?_, ?_⟩
    · have h1 : ((T (-1) - 1 : R[T;T⁻¹])) * T (-(i : ℤ)) = T (-(i : ℤ) - 1) - T (-(i : ℤ)) := by
        rw [sub_mul, one_mul, ← T_add]
        congr 2
        ring
      rw [mul_add, ← hg, h1]
      ring
    · intro a _
      rw [mul_add]
      refine (extendedRees R I).add_mem (hmem a ?_) (isExtendedRees_of_nonpos R I (by omega))
      have h0 : (-(i : ℤ)).toNat = 0 := by omega
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top

/-- An element of the extended Rees algebra vanishing at `t = 1` is a multiple of `u - 1`
inside the extended Rees algebra. -/
theorem exists_eq_parameter_sub_one_mul {f : R[T;T⁻¹]} (hf : f ∈ extendedRees R I)
    (h0 : evalOneLaurent R f = 0) :
    ∃ g ∈ extendedRees R I, f = (T (-1) - 1) * g := by
  classical
  choose g hg hmem using fun m ↦ exists_T_sub_one_eq R I m
  refine ⟨∑ n ∈ f.coeff.support, LaurentPolynomial.C (f.coeff n) * g n, ?_, ?_⟩
  · exact Subalgebra.sum_mem _ fun n _ ↦ hmem n _ (hf n)
  · have heval : evalOneLaurent R f = ∑ n ∈ f.coeff.support, f.coeff n := by
      conv_lhs => rw [eq_sum_support R f]
      rw [map_sum]
      exact Finset.sum_congr rfl fun n _ ↦ evalOneLaurent_C_mul_T R _ _
    have hsum : f = ∑ n ∈ f.coeff.support, LaurentPolynomial.C (f.coeff n) * (T n - 1) := by
      have : ∑ n ∈ f.coeff.support, LaurentPolynomial.C (f.coeff n) * (T n - 1) =
          ∑ n ∈ f.coeff.support, LaurentPolynomial.C (f.coeff n) * T n -
            LaurentPolynomial.C (∑ n ∈ f.coeff.support, f.coeff n) := by
        rw [map_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun n _ ↦ by rw [mul_sub, mul_one]
      rw [this, ← heval, h0, map_zero, sub_zero]
      exact eq_sum_support R f
    conv_lhs => rw [hsum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [hg n]
    ring

/-- The kernel of evaluation at `t = 1` is generated by `u - 1`. -/
theorem ker_evalOne : RingHom.ker (evalOne R I) = Ideal.span {parameter R I - 1} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton']
  constructor
  · intro h0
    obtain ⟨g, hg, hfg⟩ := exists_eq_parameter_sub_one_mul R I f.2 h0
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    change g * (T (-1) - 1) = (f : R[T;T⁻¹])
    rw [mul_comm]
    exact hfg.symm
  · rintro ⟨a, rfl⟩
    rw [map_mul, map_sub, evalOne_parameter, map_one, sub_self, mul_zero]

/-- The ideal of the fibre over `u = 1`. -/
abbrev fibreOneIdeal : Ideal (extendedRees R I) := Ideal.span {parameter R I - 1}

/-- The fibre of the deformation space over `u = 1` is the original ring. -/
def fibreOneEquiv : (extendedRees R I ⧸ fibreOneIdeal R I) ≃ₐ[R] R :=
  (Ideal.quotientEquivAlgOfEq R (ker_evalOne R I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (evalOne_surjective R I))

/-- The fibre of the deformation space over `u = 1`, as a scheme. -/
abbrev fibreOne : Scheme.{u} := Spec (.of (extendedRees R I ⧸ fibreOneIdeal R I))

/-- The closed immersion of the fibre over `u = 1` into the deformation space. -/
def fibreOneι : fibreOne R I ⟶ space R I :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (fibreOneIdeal R I)))

instance fibreOneι_isClosedImmersion : IsClosedImmersion (fibreOneι R I) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The fibre over `u = 1` is the original affine scheme. -/
def fibreOneIso : fibreOne R I ≅ Spec (.of R) :=
  Scheme.Spec.mapIso (fibreOneEquiv R I).toRingEquiv.toCommRingCatIso.symm.op

/-! ### Flatness over the affine line -/

section Flat

variable (k : Type u) [Field k] [Algebra k R]

/-- The structure map is the substitution `t ↦ t⁻¹` applied to a polynomial. -/
theorem coe_structureMap (q : Polynomial R) :
    (structureMap R I q : R[T;T⁻¹]) = invert (Polynomial.toLaurent q) := by
  have h : (extendedRees R I).val.comp (structureMap R I) =
      (invert (R := R)).toAlgHom.comp Polynomial.toLaurentAlg := by
    apply Polynomial.algHom_ext
    simp [structureMap]
  exact congrArg (fun φ : Polynomial R →ₐ[R] R[T;T⁻¹] ↦ φ q) h

/-- The `k[u]`-algebra structure of the deformation space over the affine line of a base
field `k`. -/
def lineRingHom : Polynomial k →+* extendedRees R I :=
  (structureMap R I).toRingHom.comp (Polynomial.mapRingHom (algebraMap k R))

theorem coe_lineRingHom (p : Polynomial k) :
    (lineRingHom R I k p : R[T;T⁻¹]) =
      invert (Polynomial.toLaurent (p.map (algebraMap k R))) := by
  change (structureMap R I (Polynomial.map (algebraMap k R) p) : R[T;T⁻¹]) = _
  exact coe_structureMap R I _

/-- A polynomial with unit leading coefficient is a nonzerodivisor. -/
theorem eq_zero_of_mul_eq_zero_of_isUnit_leadingCoeff {q r : Polynomial R}
    (hq : IsUnit q.leadingCoeff) (h : q * r = 0) : r = 0 := by
  by_contra hr
  have hne : q.leadingCoeff * r.leadingCoeff ≠ 0 :=
    fun h' ↦ hr (Polynomial.leadingCoeff_eq_zero.mp (hq.mul_right_eq_zero.mp h'))
  have := Polynomial.leadingCoeff_mul' hne
  rw [h, Polynomial.leadingCoeff_zero] at this
  exact hne this.symm

/-- Over a field, the deformation space is torsion-free over the affine line. -/
theorem isTorsionFree_line [Nontrivial R] :
    letI := (lineRingHom R I k).toAlgebra
    Module.IsTorsionFree (Polynomial k) (extendedRees R I) := by
  let _ := (lineRingHom R I k).toAlgebra
  refine ⟨fun p hp f g hfg ↦ ?_⟩
  have hp0 : p ≠ 0 := hp.left.ne_zero
  set q : Polynomial R := p.map (algebraMap k R) with hqdef
  have h1 : (lineRingHom R I k p : R[T;T⁻¹]) * f = (lineRingHom R I k p : R[T;T⁻¹]) * g := by
    have := congrArg Subtype.val hfg
    simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using this
  rw [coe_lineRingHom] at h1
  have h2 : Polynomial.toLaurent q * invert (f : R[T;T⁻¹]) =
      Polynomial.toLaurent q * invert (g : R[T;T⁻¹]) := by
    have := congrArg invert h1
    simpa only [map_mul, involutive_invert _] using this
  obtain ⟨a, f', hf'⟩ := (invert (f : R[T;T⁻¹])).exists_T_pow
  obtain ⟨b, g', hg'⟩ := (invert (g : R[T;T⁻¹])).exists_T_pow
  have h3 : Polynomial.toLaurent (q * f' * Polynomial.X ^ b) =
      Polynomial.toLaurent (q * g' * Polynomial.X ^ a) := by
    rw [map_mul, map_mul, map_mul, map_mul, Polynomial.toLaurent_X_pow,
      Polynomial.toLaurent_X_pow, hf', hg']
    calc Polynomial.toLaurent q * (invert (f : R[T;T⁻¹]) * T a) * T b
        = Polynomial.toLaurent q * invert (f : R[T;T⁻¹]) * (T a * T b) := by ring
      _ = Polynomial.toLaurent q * invert (g : R[T;T⁻¹]) * (T a * T b) := by rw [h2]
      _ = Polynomial.toLaurent q * (invert (g : R[T;T⁻¹]) * T b) * T a := by ring
  rw [Polynomial.toLaurent_inj] at h3
  have hq : IsUnit q.leadingCoeff := by
    rw [hqdef, Polynomial.leadingCoeff_map_of_injective (algebraMap k R).injective]
    exact (isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp0)).map _
  have hcancel : f' * Polynomial.X ^ b = g' * Polynomial.X ^ a := by
    have hzero : q * (f' * Polynomial.X ^ b - g' * Polynomial.X ^ a) = 0 := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, h3, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_mul_eq_zero_of_isUnit_leadingCoeff R hq hzero)
  have h4 : invert (f : R[T;T⁻¹]) * T a * T b = invert (g : R[T;T⁻¹]) * T b * T a := by
    have := congrArg Polynomial.toLaurent hcancel
    rwa [map_mul, map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_X_pow, hf',
      hg'] at this
  have h5 : invert (f : R[T;T⁻¹]) = invert (g : R[T;T⁻¹]) := by
    rw [mul_T_assoc, mul_T_assoc, add_comm] at h4
    exact (isUnit_T _).mul_right_cancel h4
  exact Subtype.ext (involutive_invert.injective h5)

/-- Over a field, the deformation space is flat over the affine line. -/
theorem flat_line [Nontrivial R] :
    letI := (lineRingHom R I k).toAlgebra
    Module.Flat (Polynomial k) (extendedRees R I) := by
  let _ := (lineRingHom R I k).toAlgebra
  have := isTorsionFree_line R I k
  infer_instance

theorem lineRingHom_flat [Nontrivial R] : (lineRingHom R I k).Flat := flat_line R I k

/-- The structure morphism of the deformation space to the affine line over the base field. -/
def toLineOver : space R I ⟶ Spec (.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (lineRingHom R I k))

/-- The deformation space is flat over the affine line of the base field. -/
theorem toLineOver_flat [Nontrivial R] : Flat (toLineOver R I k) := by
  rw [toLineOver, HasRingHomProperty.Spec_iff (P := @Flat)]
  exact lineRingHom_flat R I k

end Flat

end

end AffineDeformationSpace

end GromovWitten.AlgebraicGeometry
