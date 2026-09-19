/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleSectionGysinIdentity
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyKey

/-!
# Injectivity of the flat pullback along a trivialised affine vector bundle

This file completes the homotopy invariance of rational Chow groups for trivialised affine
vector bundles over a Noetherian ring.  Surjectivity of the flat pullback was proved in
`IntersectionTheory/BundleHomotopy.lean`; here we prove injectivity, following Fulton's
argument for the trivial line bundle (*Intersection Theory*, Theorem 3.3(a)) in the form which
avoids Chern classes: a relation on the total space is restricted along a *general* constant
section `σ_c` of the line bundle, using the cycle-level Gysin map of
`IntersectionTheory/BundleSectionGysin.lean`.

Two hypotheses on the base ring are used.

* `VectorBundle.UnitDifferences R`: `R` contains an infinite set whose pairwise differences are
  units (for instance an infinite field of which `R` is an algebra).  This is what makes "a
  general constant section" available: only finitely many values of `c` are excluded.
* `VectorBundle.HasUniversalDimensionFormula R`: every prime quotient of every finitely generated
  polynomial ring over `R` satisfies the dimension formula `dim (A ⧸ p) + ht p = dim A`.  This is
  the catenarity input of Fulton's local symmetry computation, and it also makes all principal
  divisors homogeneous, which discharges the hypothesis `hhom` of the surjectivity theorem.

## Contents

* `VectorBundle.UnitDifferences`, with `VectorBundle.unitDifferences_of_field` and the transport
  lemmas `VectorBundle.unitDifferences_polynomial`, `VectorBundle.unitDifferences_mvPolynomial`.
* `VectorBundle.HasUniversalDimensionFormula`, with the transport lemmas
  `VectorBundle.HasUniversalDimensionFormula.polynomial` and
  `VectorBundle.HasUniversalDimensionFormula.mvPolynomial`.
* `VectorBundle.principalDivisorsHomogeneous_of_dimensionFormula`: the dimension formula implies
  that principal divisors are homogeneous.
* `VectorBundle.exists_good_translate`: a constant `c` whose section avoids finitely many primes.
* `VectorBundle.BundleInjective` and its proof in rank one
  (`VectorBundle.bundleInjective_polynomial`) and in arbitrary rank
  (`VectorBundle.bundleInjective_of_card`).
* `VectorBundle.chowPullbackBundle_injective`, `VectorBundle.chowPullbackBundle_bijective`,
  `VectorBundle.chowPullbackBundle_equiv` and `VectorBundle.zeroSectionGysinEquiv''`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace VectorBundle

/-! ## Rings with infinitely many pairwise-unit differences -/

/-- A commutative ring has *unit differences* if it contains an infinite set whose pairwise
differences are units.  An infinite field has this property, and so does every algebra over an
infinite field which is nontrivial. -/
def UnitDifferences (R : Type u) [CommRing R] : Prop :=
  ∃ Λ : Set R, Λ.Infinite ∧ ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → IsUnit (x - y)

/-- Any nontrivial algebra over an infinite field has unit differences: take the image of the
field. -/
theorem unitDifferences_of_field (k : Type u) [Field k] [Infinite k] (R : Type u) [CommRing R]
    [Nontrivial R] [Algebra k R] : UnitDifferences R := by
  refine ⟨Set.range (algebraMap k R), Set.infinite_range_of_injective ?_, ?_⟩
  · exact (algebraMap k R).injective
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
    have hxy : x - y ≠ 0 := by
      intro hcon
      exact hne (by rw [sub_eq_zero] at hcon; rw [hcon])
    have hu : IsUnit (x - y) := isUnit_iff_ne_zero.2 hxy
    have h2 : algebraMap k R x - algebraMap k R y = algebraMap k R (x - y) := (map_sub _ _ _).symm
    rw [h2]
    exact hu.map (algebraMap k R)

/-- Unit differences transport along an injective ring homomorphism. -/
theorem unitDifferences_of_injective {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (h : UnitDifferences R) : UnitDifferences S := by
  obtain ⟨Λ, hinf, hunit⟩ := h
  refine ⟨f '' Λ, hinf.image hf.injOn, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
  have hxy : x ≠ y := fun hcon ↦ hne (by rw [hcon])
  rw [← map_sub]
  exact (hunit x hx y hy hxy).map f

/-- A polynomial ring over a ring with unit differences has unit differences. -/
theorem unitDifferences_polynomial {R : Type u} [CommRing R] (h : UnitDifferences R) :
    UnitDifferences (Polynomial R) :=
  unitDifferences_of_injective (Polynomial.C : R →+* Polynomial R) Polynomial.C_injective h

/-- A multivariate polynomial ring over a ring with unit differences has unit differences. -/
theorem unitDifferences_mvPolynomial {R : Type u} [CommRing R] (ι : Type u)
    (h : UnitDifferences R) : UnitDifferences (MvPolynomial ι R) :=
  unitDifferences_of_injective (MvPolynomial.C : R →+* MvPolynomial ι R)
    (MvPolynomial.C_injective ι R) h

/-! ## The dimension formula for all polynomial algebras -/

/-- The dimension formula holds *universally* over `R` if every prime quotient of every finitely
generated polynomial algebra over `R` satisfies it.  This is true when `R` is a finitely generated
algebra over a field; Mathlib has no such statement, so it is carried as a hypothesis. -/
def HasUniversalDimensionFormula (R : Type u) [CommRing R] : Prop :=
  ∀ (ι : Type u) [Finite ι] (P : Ideal (MvPolynomial ι R)), P.IsPrime →
    HasDimensionFormula (MvPolynomial ι R ⧸ P)

/-- The dimension formula for a quotient transports along a ring isomorphism of the ambient
rings. -/
theorem hasDimensionFormula_quotient_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (P : Ideal B)
    (h : HasDimensionFormula (A ⧸ P.comap (e : A →+* B))) : HasDimensionFormula (B ⧸ P) :=
  SectionGysinIdentity.hasDimensionFormula_of_ringEquiv
    (Ideal.quotientEquiv _ P e (Ideal.map_comap_of_surjective (e : A →+* B) e.surjective P).symm) h

/-- The universal dimension formula over `R` gives the dimension formula for every prime quotient
of the univariate polynomial ring `R[X]`. -/
theorem HasUniversalDimensionFormula.polynomial {R : Type u} [CommRing R]
    (h : HasUniversalDimensionFormula R) (P : Ideal (Polynomial R)) (hP : P.IsPrime) :
    HasDimensionFormula (Polynomial R ⧸ P) := by
  have _ : P.IsPrime := hP
  refine hasDimensionFormula_quotient_of_ringEquiv
    ((polyTrivialization R).symm.toRingEquiv) P ?_
  exact h PUnit.{u + 1} _ inferInstance

/-- The universal dimension formula is inherited by a finitely generated polynomial algebra. -/
theorem HasUniversalDimensionFormula.mvPolynomial {R : Type u} [CommRing R] (ι' : Type u)
    [Finite ι'] (h : HasUniversalDimensionFormula R) :
    HasUniversalDimensionFormula (MvPolynomial ι' R) := by
  intro ι _ P hP
  have _ : P.IsPrime := hP
  refine hasDimensionFormula_quotient_of_ringEquiv
    ((MvPolynomial.sumAlgEquiv R ι ι').toRingEquiv) P ?_
  exact h (ι ⊕ ι') _ inferInstance

/-! ## Homogeneity of principal divisors from the dimension formula -/

section Homogeneity

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Every principal-divisor generator on a Noetherian affine scheme is the pushforward, along the
closed immersion of `Spec (A ⧸ P)` for a prime `P`, of the principal cycle of a rational function
on `Spec (A ⧸ P)`. -/
theorem exists_quotient_divisor_form (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (g : RationalFunctionGenerator (Spec (CommRingCat.of A))) :
    ∃ (P : Ideal A) (_ : P.IsPrime) (f' : (Spec (CommRingCat.of (A ⧸ P))).functionField),
      g.divisor dimA =
        _root_.AlgebraicGeometry.AlgebraicCycle.map (quotImmersion P)
          (fun z ↦ (dimA : _ → ℤ) ((quotImmersion P).base z)) (dimA : _ → ℤ)
          ((Spec (CommRingCat.of (A ⧸ P))).principalCycle f') := by
  obtain ⟨P, ε, hfac⟩ :=
    _root_.AlgebraicGeometry.IsClosedImmersion.Spec_iff.1 g.subspace.isClosedImmersion
  have hint : _root_.AlgebraicGeometry.IsIntegral (Spec (CommRingCat.of (A ⧸ P))) :=
    _root_.AlgebraicGeometry.IsIntegral.of_isIso ε.hom
  have hdom : IsDomain (A ⧸ P) :=
    (_root_.AlgebraicGeometry.affine_isIntegral_iff (CommRingCat.of (A ⧸ P))).1 hint
  have hP : P.IsPrime := (Ideal.Quotient.isDomain_iff_prime P).1 hdom
  have hnoeth : IsNoetherianRing ↑(CommRingCat.of (A ⧸ P)) :=
    inferInstanceAs (IsNoetherianRing (A ⧸ P))
  have hloc : _root_.AlgebraicGeometry.IsLocallyNoetherian
      (Spec (CommRingCat.of (A ⧸ P))) := inferInstance
  set f' : (Spec (CommRingCat.of (A ⧸ P))).functionFieldˣ :=
    Units.map (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap ε.inv).toMonoidHom
      g.function with hf'
  have h1 : g.divisor dimA =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (ε.hom ≫ quotImmersion P)
        (fun x ↦ (dimA : _ → ℤ) ((ε.hom ≫ quotImmersion P).base x)) (dimA : _ → ℤ)
        (g.subspace.scheme.principalCycle (g.function : _)) :=
    AlgebraicCycle.map_congr_hom hfac (dimA : _ → ℤ) _
  have h2 := AlgebraicCycle.map_comp_of_isClosedImmersion ε.hom (quotImmersion P)
    ((DimensionFunction.comapClosedImmersion (quotImmersion P) dimA : _ → ℤ))
    (dimA : _ → ℤ) (g.subspace.scheme.principalCycle (g.function : _))
  have h3 := map_isIso_principalCycle ε
    (DimensionFunction.comapClosedImmersion (quotImmersion P) dimA)
    (g.function : g.subspace.scheme.functionField)
  rw [h3] at h2
  exact ⟨P, hP, (f' : (Spec (CommRingCat.of (A ⧸ P))).functionField), h1.trans h2.symm⟩

/-- A point at which the pushforward of a principal cycle from `Spec (A ⧸ P)` is nonzero is the
image of a prime of `A ⧸ P` of height one. -/
theorem exists_height_one_of_map_principalCycle (P : Ideal A) [P.IsPrime]
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (f' : (Spec (CommRingCat.of (A ⧸ P))).functionField) (x : ↥(Spec (CommRingCat.of A)))
    (hx : (_root_.AlgebraicGeometry.AlgebraicCycle.map (quotImmersion P)
        (fun z ↦ (dimA : _ → ℤ) ((quotImmersion P).base z)) (dimA : _ → ℤ)
        ((Spec (CommRingCat.of (A ⧸ P))).principalCycle f') :
        ↥(Spec (CommRingCat.of A)) → ℚ) x ≠ 0) :
    ∃ q : PrimeSpectrum (A ⧸ P), q.asIdeal.height = 1 ∧
      (x : PrimeSpectrum A).asIdeal = q.asIdeal.comap (Ideal.Quotient.mk P) := by
  by_cases hmem : x ∈ Set.range (quotImmersion P).base
  · obtain ⟨q, rfl⟩ := hmem
    rw [AlgebraicCycle.map_closedImmersion_apply_image (quotImmersion P) (dimA : _ → ℤ)] at hx
    rw [_root_.AlgebraicGeometry.Scheme.principalCycle_apply] at hx
    have hord : (Spec (CommRingCat.of (A ⧸ P))).ord f' q ≠ 0 := by
      intro hcon
      exact hx (by rw [hcon]; norm_num)
    have hco : Order.coheight q = 1 := by
      by_contra hcon
      exact hord (_root_.AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hcon f')
    refine ⟨(q : PrimeSpectrum (A ⧸ P)), ?_, rfl⟩
    rw [← coheight_eq_ideal_height (A ⧸ P) (q : PrimeSpectrum (A ⧸ P))]
    exact hco
  · exact absurd (AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range (quotImmersion P)
      (dimA : _ → ℤ) _ x hmem) hx

omit [IsNoetherianRing A] in
/-- The dimension formula pins down the dimension of a height-one point of `V(P)`: it is one less
than the dimension of `V(P)`. -/
theorem dimension_add_one_eq_ringKrullDim (P : Ideal A) [P.IsPrime]
    (dimA : DimensionFunction (Spec (CommRingCat.of A))) (hdf : HasDimensionFormula (A ⧸ P))
    (x : ↥(Spec (CommRingCat.of A))) (q : PrimeSpectrum (A ⧸ P)) (hq : q.asIdeal.height = 1)
    (hxq : (x : PrimeSpectrum A).asIdeal = q.asIdeal.comap (Ideal.Quotient.mk P)) :
    (((Int.toNat (dimA x) : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = ringKrullDim (A ⧸ P) := by
  have hsurj : Function.Surjective
      (((Ideal.Quotient.mk q.asIdeal).comp (Ideal.Quotient.mk P) : A →+* _)) :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker ((Ideal.Quotient.mk q.asIdeal).comp (Ideal.Quotient.mk P)) =
      q.asIdeal.comap (Ideal.Quotient.mk P) := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  have hequiv : (A ⧸ (x : PrimeSpectrum A).asIdeal) ≃+* ((A ⧸ P) ⧸ q.asIdeal) :=
    (Ideal.quotEquivOfEq (hxq.trans hker.symm)).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)
  have h3 : ringKrullDim (A ⧸ (x : PrimeSpectrum A).asIdeal) =
      ringKrullDim ((A ⧸ P) ⧸ q.asIdeal) := ringKrullDim_eq_of_ringEquiv hequiv
  have h4 := hdf q.asIdeal q.isPrime
  rw [hq] at h4
  have h1 := GromovWitten.Algebra.PrimeSpectrum.coheight_eq_ringKrullDim_quotient
    (x : PrimeSpectrum A)
  have h2 := coheight_eq_dimension A dimA (x : PrimeSpectrum A)
  rw [h2] at h1
  rw [WithBot.coe_add, h1, h3]
  simpa using h4

/-- **Principal divisors are homogeneous** as soon as every prime quotient of the coordinate ring
satisfies the dimension formula: the divisor of a rational function on `V(P)` is supported at the
height-one points of `V(P)`, and all of those have dimension `dim V(P) - 1`. -/
theorem principalDivisorsHomogeneous_of_dimensionFormula
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (hdf : ∀ P : Ideal A, P.IsPrime → HasDimensionFormula (A ⧸ P)) :
    PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimA := by
  intro g
  obtain ⟨P, hP, f', hdiv⟩ := exists_quotient_divisor_form dimA g
  have _ : P.IsPrime := hP
  have key : ∀ x : ↥(Spec (CommRingCat.of A)), (g.divisor dimA : _ → ℚ) x ≠ 0 →
      (((Int.toNat (dimA x) : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = ringKrullDim (A ⧸ P) := by
    intro x hx
    rw [hdiv] at hx
    obtain ⟨q, hq, hxq⟩ := exists_height_one_of_map_principalCycle P dimA f' x hx
    exact dimension_add_one_eq_ringKrullDim P dimA (hdf P hP) x q hq hxq
  by_cases hsupp : ∃ x : ↥(Spec (CommRingCat.of A)), (g.divisor dimA : _ → ℚ) x ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hsupp
    refine ⟨dimA x₀, fun x hx ↦ ?_⟩
    have heq := (key x hx).trans (key x₀ hx₀).symm
    rw [WithBot.coe_inj] at heq
    have heq2 : (Int.toNat (dimA x) : ℕ∞) = (Int.toNat (dimA x₀) : ℕ∞) :=
      LocalOrdSymmetry.enat_add_right_cancel (by simp) heq
    have heq3 : Int.toNat (dimA x) = Int.toNat (dimA x₀) := by exact_mod_cast heq2
    rw [← Int.toNat_of_nonneg (dimA.nonnegative x), ← Int.toNat_of_nonneg (dimA.nonnegative x₀),
      heq3]
  · refine ⟨0, fun x hx ↦ absurd ⟨x, hx⟩ hsupp⟩

end Homogeneity

/-! ## A general constant section -/

/-- Given finitely many proper ideals of `R[X]` and an infinite set of elements of `R` with unit
differences, some translate `X - c` lies in none of the ideals: each ideal excludes at most one
value of `c`, because the difference of two such translates is a unit constant. -/
theorem exists_good_translate {R : Type u} [CommRing R] (hunit : UnitDifferences R)
    (T : Set (Ideal (Polynomial R))) (hTfin : T.Finite) (hTne : ∀ Q ∈ T, Q ≠ ⊤) :
    ∃ c : R, ∀ Q ∈ T, sectionPoly c ∉ Q := by
  obtain ⟨Λ, hinf, hu⟩ := hunit
  have hbadfin : (⋃ Q ∈ T, {x ∈ Λ | sectionPoly x ∈ Q}).Finite := by
    refine hTfin.biUnion ?_
    intro Q hQ
    refine Set.Subsingleton.finite ?_
    intro x hx y hy
    by_contra hne
    have h1 : sectionPoly x - sectionPoly y ∈ Q := Q.sub_mem hx.2 hy.2
    have h2 : sectionPoly x - sectionPoly y = Polynomial.C (y - x) := by
      simp only [sectionPoly, map_sub]
      ring
    have h3 : IsUnit (y - x) := hu y hy.1 x hx.1 fun hcon ↦ hne hcon.symm
    rw [h2] at h1
    exact hTne Q hQ (Q.eq_top_of_isUnit_mem h1 (h3.map Polynomial.C))
  obtain ⟨c, hc⟩ := (hinf.sdiff hbadfin).nonempty
  refine ⟨c, fun Q hQ hmem ↦ hc.2 ?_⟩
  exact Set.mem_biUnion hQ ⟨hc.1, hmem⟩

/-! ## Good position of a general section -/

/-- Krull's principal ideal theorem in relative form: a prime minimal over `P + (x)`, for a prime
`P` not containing `x`, has height exactly one in `A ⧸ P`. -/
theorem height_map_eq_one_of_mem_minimalPrimes {A : Type u} [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsPrime] (x : A) (hx : x ∉ P) {Q : Ideal A}
    (hQ : Q ∈ (P ⊔ Ideal.span {x}).minimalPrimes) :
    (Q.map (Ideal.Quotient.mk P)).height = 1 := by
  have hQp : Q.IsPrime := hQ.isPrime
  have hPQ : P ≤ Q := le_sup_left.trans hQ.le
  have hxQ : x ∈ Q :=
    hQ.le ((le_sup_right : Ideal.span {x} ≤ P ⊔ Ideal.span {x})
      (Ideal.mem_span_singleton_self x))
  have hlt : P < Q := lt_of_le_of_ne hPQ (by rintro rfl; exact hx hxQ)
  have hprime : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    SectionGysinIdentity.map_quotient_isPrime P Q hPQ
  have hdom : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  have hne : (Q.map (Ideal.Quotient.mk P)).height ≠ 0 := by
    intro hcon
    exact map_ne_bot_of_lt P Q hlt (Ideal.height_eq_zero_iff_eq_bot.1 hcon)
  exact le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hQ)
    (Order.one_le_iff_ne_zero.2 hne)

/-- The "good position" hypothesis of theorem (B) holds for `(P, a)` as soon as the translate
`X - c` avoids `P` and every prime minimal over `P + (a)`.

Indeed, a prime `Q` minimal over `P + (X - c)` which contained `a` would contain a prime `Q'`
minimal over `P + (a)`; the translate avoids `Q'` but lies in `Q`, so `Q' < Q`, and both would
have height one in `R[X] ⧸ P`, which is impossible. -/
theorem hgood_of_avoid {R : Type u} [CommRing R] [IsNoetherianRing R] (c : R)
    (P : Ideal (Polynomial R)) [P.IsPrime] (hP : sectionPoly c ∉ P) (a : Polynomial R)
    (ha : a ∉ P) (havoid : ∀ Q ∈ (P ⊔ Ideal.span {a}).minimalPrimes, sectionPoly c ∉ Q) :
    ∀ Q : Ideal (Polynomial R), Q.IsPrime → P < Q → sectionPoly c ∈ Q →
      (∀ Q' : Ideal (Polynomial R), Q'.IsPrime → P ≤ Q' → Q' < Q → sectionPoly c ∉ Q') →
      a ∉ Q := by
  intro Q hQp hPQ hsQ hmin haQ
  have _ : Q.IsPrime := hQp
  -- `Q` is minimal over `P + (X - c)`
  have hIQ : P ⊔ Ideal.span {sectionPoly c} ≤ Q :=
    sup_le hPQ.le (Ideal.span_le.2 (by simpa using hsQ))
  obtain ⟨Q₀, hQ₀, hQ₀Q⟩ := Ideal.exists_minimalPrimes_le hIQ
  have hQ₀eq : Q₀ = Q := by
    by_contra hne
    refine hmin Q₀ hQ₀.isPrime (le_sup_left.trans hQ₀.le) (lt_of_le_of_ne hQ₀Q hne) ?_
    exact hQ₀.le ((le_sup_right : Ideal.span {sectionPoly c} ≤ _)
      (Ideal.mem_span_singleton_self _))
  have hQheight : (Q.map (Ideal.Quotient.mk P)).height = 1 := by
    rw [← hQ₀eq]
    exact height_map_eq_one_of_mem_minimalPrimes P (sectionPoly c) hP hQ₀
  -- a prime minimal over `P + (a)` inside `Q`
  have hJQ : P ⊔ Ideal.span {a} ≤ Q := sup_le hPQ.le (Ideal.span_le.2 (by simpa using haQ))
  obtain ⟨Q', hQ', hQ'Q⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hQ'ne : Q' ≠ Q := by
    intro hcon
    exact havoid Q' hQ' (by rw [hcon]; exact hsQ)
  have hQ'height : (Q'.map (Ideal.Quotient.mk P)).height = 1 :=
    height_map_eq_one_of_mem_minimalPrimes P a ha hQ'
  exact height_map_ne_one_of_lt P Q' Q hQ'.isPrime hQp (le_sup_left.trans hQ'.le) hPQ.le
    (lt_of_le_of_ne hQ'Q hQ'ne) hQ'height hQheight

/-! ## Injectivity of the flat pullback at the level of cycles -/

section Injective

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} (e : A ≃ₐ[R] MvPolynomial ι R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of A)))

/-- Injectivity of the flat pullback at the level of cycles: a cycle on the base whose pullback
is rationally equivalent to zero is itself rationally equivalent to zero. -/
def BundleInjective : Prop :=
  ∀ w : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ,
    AlgebraicCycle.pullbackBundle e w ∈ totalRationalRelations (Spec (CommRingCat.of A)) dimE →
      w ∈ totalRationalRelations (Spec (CommRingCat.of R)) dimX

end Injective

/-- The cycle-level injectivity statement is invariant under an isomorphism of the coordinate
algebras of two affine vector bundles over the same base. -/
theorem bundleInjective_of_algEquiv {R : Type u} [CommRing R] {A A' : Type u} [CommRing A]
    [Algebra R A] [CommRing A'] [Algebra R A'] {ι ι' : Type u} (φ : A ≃ₐ[R] A')
    (e : A ≃ₐ[R] MvPolynomial ι R) (e' : A' ≃ₐ[R] MvPolynomial ι' R)
    (dimX : DimensionFunction (Spec (CommRingCat.of R)))
    (dimE : DimensionFunction (Spec (CommRingCat.of A)))
    (dimE' : DimensionFunction (Spec (CommRingCat.of A')))
    (h : BundleInjective e dimX dimE) : BundleInjective e' dimX dimE' := by
  intro w hw
  refine h w ?_
  let ε : Spec (CommRingCat.of A') ≅ Spec (CommRingCat.of A) := specIsoOfAlgEquiv φ
  have hhom : IsIso ε.hom := ⟨ε.inv, ε.hom_inv_id, ε.inv_hom_id⟩
  have hinv : IsIso ε.inv := ⟨ε.hom, ε.inv_hom_id, ε.hom_inv_id⟩
  have hkey : AlgebraicCycle.pullbackBundle e' w =
      AlgebraicCycle.pullbackOpen ε.hom (AlgebraicCycle.pullbackBundle e w) := by
    apply Function.locallyFinsuppWithin.coe_injective
    funext q
    exact AlgebraicCycle.pullbackBundle_algEquiv φ e e' w q
  rw [hkey] at hw
  have hmem := totalRationalRelations_pullbackOpen_of_isIso ε.symm dimE dimE' ⟨_, hw, rfl⟩
  have hid : AlgebraicCycle.pullbackOpen ε.inv
      (AlgebraicCycle.pullbackOpen ε.hom (AlgebraicCycle.pullbackBundle e w)) =
      AlgebraicCycle.pullbackBundle e w := by
    apply Function.locallyFinsuppWithin.coe_injective
    funext x
    change (AlgebraicCycle.pullbackBundle e w : _ → ℚ) (ε.hom.base (ε.inv.base x)) = _
    have hx : ε.hom.base (ε.inv.base x) = x :=
      congrArg (fun f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) ↦ f.base x)
        ε.inv_hom_id
    rw [hx]
  rw [← hid]
  exact hmem

/-- A rank-zero affine vector bundle has injective flat pullback on cycles: its projection is an
isomorphism of schemes. -/
theorem bundleInjective_of_isEmpty {R : Type u} [CommRing R] {A : Type u} [CommRing A]
    [Algebra R A] {ι : Type u} [IsEmpty ι] (e : A ≃ₐ[R] MvPolynomial ι R)
    (dimX : DimensionFunction (Spec (CommRingCat.of R)))
    (dimE : DimensionFunction (Spec (CommRingCat.of A))) : BundleInjective e dimX dimE := by
  intro w hw
  set ε : A →ₐ[R] R := (e.trans (MvPolynomial.isEmptyAlgEquiv R ι)).toAlgHom with hε
  have hiso : IsIso (zeroSection ε) := isIso_zeroSection_of_isEmpty ε e
  have hmem := totalRationalRelations_pullbackOpen_of_isIso (asIso (zeroSection ε)) dimX dimE
    ⟨_, hw, rfl⟩
  have hinv : CategoryTheory.inv (zeroSection ε) = GradedCone.projection R A :=
    CategoryTheory.IsIso.inv_eq_of_inv_hom_id (projection_comp_zeroSection_of_isEmpty ε e)
  have hcomp2 : zeroSection ε ≫ GradedCone.projection R A = 𝟙 (Spec (CommRingCat.of R)) := by
    rw [← hinv]
    exact CategoryTheory.IsIso.hom_inv_id _
  have hval : AlgebraicCycle.pullbackOpen (zeroSection ε)
      (AlgebraicCycle.pullbackBundle e w) = w := by
    apply Function.locallyFinsuppWithin.coe_injective
    funext x
    change (AlgebraicCycle.pullbackBundle e w : _ → ℚ) ((zeroSection ε).base x) = _
    rw [AlgebraicCycle.pullbackBundle_apply_of_isEmpty e]
    have hx : (GradedCone.projection R A).base ((zeroSection ε).base x) = x :=
      congrArg (fun f : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R) ↦ f.base x) hcomp2
    rw [hx]
  rw [← hval]
  exact hmem

/-- **Fulton, *Intersection Theory*, Theorem 3.3(a)** for the trivial line bundle `Spec R[X]`
over a Noetherian ring, at the level of cycles: a cycle whose flat pullback is rationally
equivalent to zero is itself rationally equivalent to zero.

The proof restricts a relation `π^* w = ∑ nᵢ div(gᵢ)` along a *general* constant section.  Each
generator `gᵢ` is written as a difference of the divisors of two polynomials `aᵢ, bᵢ` on a
subvariety `V(Pᵢ)` (`exists_generator_eq_elementGenerator_sub`), and the constant `c` is chosen
(`exists_good_translate`) so that `X - c` avoids every `Pᵢ` and every prime minimal over
`Pᵢ + (aᵢ)` or `Pᵢ + (bᵢ)`; `hgood_of_avoid` turns this into the good-position hypothesis of
Fulton's local symmetry.  The section Gysin map then returns `w` on the left
(`sectionGysin_pullbackBundle`) and a sum of principal divisors on the right
(`sectionGysin_elementGenerator_mem'`). -/
theorem bundleInjective_polynomial {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hunit : UnitDifferences R)
    (hdim : ∀ P : Ideal (Polynomial R), P.IsPrime → HasDimensionFormula (Polynomial R ⧸ P))
    (dimX : DimensionFunction (Spec (CommRingCat.of R)))
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R)))) :
    BundleInjective (polyTrivialization R) dimX dimE := by
  classical
  intro w hw
  have hw' : AlgebraicCycle.pullbackBundle (polyTrivialization R) w ∈
      Submodule.span ℚ (Set.range
        (fun g : RationalFunctionGenerator (Spec (CommRingCat.of (Polynomial R))) ↦
          g.divisor dimE)) := hw
  obtain ⟨κ, hκ⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hw'
  choose P hP a b ha hb hdivsub using
    fun g : RationalFunctionGenerator (Spec (CommRingCat.of (Polynomial R))) ↦
      exists_generator_eq_elementGenerator_sub dimE g
  set T : Set (Ideal (Polynomial R)) :=
    ⋃ g ∈ (κ.support : Set (RationalFunctionGenerator (Spec (CommRingCat.of (Polynomial R))))),
      insert (P g) ((P g ⊔ Ideal.span {a g}).minimalPrimes ∪
        (P g ⊔ Ideal.span {b g}).minimalPrimes) with hTdef
  have hTfin : T.Finite := by
    refine Set.Finite.biUnion κ.support.finite_toSet fun g _ ↦ ?_
    exact Set.Finite.insert _
      ((Ideal.finite_minimalPrimes_of_isNoetherianRing (Polynomial R) _).union
        (Ideal.finite_minimalPrimes_of_isNoetherianRing (Polynomial R) _))
  have hTne : ∀ Q ∈ T, Q ≠ ⊤ := by
    intro Q hQ
    simp only [hTdef, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_union] at hQ
    obtain ⟨g, _, hQ⟩ := hQ
    rcases hQ with rfl | h | h
    · exact (hP g).ne_top
    · exact h.isPrime.ne_top
    · exact h.isPrime.ne_top
  obtain ⟨c, hc⟩ := exists_good_translate hunit T hTfin hTne
  have hmemT : ∀ g ∈ κ.support, ∀ Q ∈ insert (P g) ((P g ⊔ Ideal.span {a g}).minimalPrimes ∪
      (P g ⊔ Ideal.span {b g}).minimalPrimes), sectionPoly c ∉ Q := by
    intro g hg Q hQ
    refine hc Q ?_
    rw [hTdef]
    exact Set.mem_biUnion (Finset.mem_coe.2 hg) hQ
  have hsum : w = ∑ g ∈ κ.support, κ g • sectionGysin c dimE (g.divisor dimE) := by
    have h0 : sectionGysin c dimE
        (AlgebraicCycle.pullbackBundle (polyTrivialization R) w) = w :=
      sectionGysin_pullbackBundle c dimE w
    rw [← h0, ← hκ]
    simp only [Finsupp.sum, map_sum, map_smul]
  rw [hsum]
  refine Submodule.sum_mem _ fun g hg ↦ Submodule.smul_mem _ _ ?_
  have hpg : (P g).IsPrime := hP g
  have hsPg : sectionPoly c ∉ P g := hmemT g hg (P g) (Set.mem_insert _ _)
  have hgoodA := hgood_of_avoid c (P g) hsPg (a g) (ha g)
    (fun Q hQ ↦ hmemT g hg Q (Set.mem_insert_of_mem _ (Or.inl hQ)))
  have hgoodB := hgood_of_avoid c (P g) hsPg (b g) (hb g)
    (fun Q hQ ↦ hmemT g hg Q (Set.mem_insert_of_mem _ (Or.inr hQ)))
  rw [hdivsub g, map_sub]
  refine Submodule.sub_mem _ ?_ ?_
  · exact sectionGysin_elementGenerator_mem' localOrdSymmetry hdim c dimX dimE (P g) hsPg
      (a g) (ha g) hgoodA
  · exact sectionGysin_elementGenerator_mem' localOrdSymmetry hdim c dimX dimE (P g) hsPg
      (b g) (hb g) hgoodB

/-! ## Induction on the rank -/

/-- Injectivity of the flat pullback at the level of cycles, for a trivialised affine vector
bundle of any finite rank over a Noetherian base with unit differences and the universal
dimension formula.  The proof is an induction on the rank, factoring the bundle as a trivial line
bundle over a bundle of one rank less (`MvPolynomial.optionEquivLeft`), composing the two flat
pullbacks (`pullbackBundle_tower`) and transporting along the isomorphism of coordinate algebras
(`bundleInjective_of_algEquiv`).  Both hypotheses on the base ring are inherited by the
intermediate base `MvPolynomial ι' R`. -/
theorem bundleInjective_of_card (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R], UnitDifferences R →
      HasUniversalDimensionFormula R →
      ∀ (A : Type u) [CommRing A] [Algebra R A] (ι : Type u) [Finite ι]
        (e : A ≃ₐ[R] MvPolynomial ι R)
        (dimX : DimensionFunction (Spec (CommRingCat.of R)))
        (dimE : DimensionFunction (Spec (CommRingCat.of A))),
        Nat.card ι = n → BundleInjective e dimX dimE := by
  induction n with
  | zero =>
      intro R _ _ _ _ A _ _ ι _ e dimX dimE hcard
      have hempty : IsEmpty ι := by
        rcases Nat.card_eq_zero.1 hcard with h | h
        · exact h
        · exact absurd h (not_infinite_iff_finite.2 ‹Finite ι›)
      exact bundleInjective_of_isEmpty (ι := ι) e dimX dimE
  | succ n IH =>
      intro R _ _ hunit hdim A _ _ ι _ e dimX dimE hcard
      obtain ⟨ι', hfin', eqv, hcard'⟩ := exists_option_equiv ι n hcard
      have _ : Finite ι' := hfin'
      let R' : Type u := MvPolynomial ι' R
      let A₂ : Type u := Polynomial R'
      let φ : A₂ ≃ₐ[R] A :=
        (((MvPolynomial.optionEquivLeft R ι').symm.trans
          (MvPolynomial.renameEquiv R eqv.symm)).trans e.symm)
      let eA : A₂ ≃ₐ[R] MvPolynomial ι R := φ.trans e
      have hisoφ : IsIso (Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) :=
        isIso_specMap_algEquiv φ.symm
      let dimE₂ : DimensionFunction (Spec (CommRingCat.of A₂)) :=
        DimensionFunction.comapClosedImmersion
          (Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) dimE
      let e₁ : A₂ ≃ₐ[R'] MvPolynomial (PUnit.{u + 1}) R' := polyTrivialization R'
      let dimX' : DimensionFunction (Spec (CommRingCat.of R')) := baseDimension e₁ dimE₂
      have hunit' : UnitDifferences R' := unitDifferences_mvPolynomial ι' hunit
      have hdim' : HasUniversalDimensionFormula R' := hdim.mvPolynomial ι'
      have h1 : BundleInjective e₁ dimX' dimE₂ :=
        bundleInjective_polynomial hunit' (fun P hP ↦ hdim'.polynomial P hP) dimX' dimE₂
      have h2 : BundleInjective (AlgEquiv.refl : R' ≃ₐ[R] MvPolynomial ι' R) dimX dimX' :=
        IH R hunit hdim R' ι' AlgEquiv.refl dimX dimX' hcard'
      have hcomp : BundleInjective eA dimX dimE₂ := by
        intro w hwmem
        refine h2 w (h1 _ ?_)
        rw [← pullbackBundle_tower eA e₁ (AlgEquiv.refl : R' ≃ₐ[R] MvPolynomial ι' R) w]
        exact hwmem
      exact bundleInjective_of_algEquiv φ eA e dimX dimE₂ dimE hcomp

/-! ## Injectivity and bijectivity of the Chow pullback -/

section Injectivity

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} [Finite ι] (e : A ≃ₐ[R] MvPolynomial ι R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of A))) (i : ℤ)
  (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
  (RE : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimE (i + (Nat.card ι : ℤ)))

include e in
/-- The universal dimension formula over the base makes all principal divisors on the total space
of a trivialised affine vector bundle homogeneous.  This discharges the hypothesis `hhom` of the
surjectivity theorem `chowPullbackBundle_surjective'`. -/
theorem principalDivisorsHomogeneous_of_hasUniversalDimensionFormula
    (hdim : HasUniversalDimensionFormula R) :
    PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE := by
  have hnoeth : IsNoetherianRing A :=
    isNoetherianRing_of_ringEquiv (MvPolynomial ι R) e.symm.toRingEquiv
  refine principalDivisorsHomogeneous_of_dimensionFormula dimE fun P hP ↦ ?_
  have _ : P.IsPrime := hP
  exact hasDimensionFormula_quotient_of_ringEquiv e.symm.toRingEquiv P (hdim ι _ inferInstance)

include e in
/-- Injectivity of the flat pullback at the level of cycles, in arbitrary rank. -/
theorem bundleInjective_of_universal (hunit : UnitDifferences R)
    (hdim : HasUniversalDimensionFormula R) : BundleInjective e dimX dimE :=
  bundleInjective_of_card (Nat.card ι) R hunit hdim A ι e dimX dimE rfl

/-- **Fulton, *Intersection Theory*, Theorem 3.3(a)**: the flat pullback along a trivialised
affine vector bundle of finite rank is injective on dimension-graded rational Chow groups, over a
Noetherian base ring with unit differences and the universal dimension formula. -/
theorem chowPullbackBundle_injective (hdim : HasUniversalDimensionFormula R)
    (hunit : UnitDifferences R) :
    Function.Injective (chowPullbackBundle e dimX dimE i RX RE) := by
  have hinj : BundleInjective e dimX dimE := bundleInjective_of_universal e dimX dimE hunit hdim
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro α hα
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective RX.relations α
  have h0 : RE.quotientMap (cyclesOfDimension.flatPullbackBundle e dimX dimE i z) = 0 :=
    LinearMap.mem_ker.1 hα
  have h1 : cyclesOfDimension.flatPullbackBundle e dimX dimE i z ∈ RE.relations :=
    (Submodule.Quotient.mk_eq_zero _).1 h0
  have h2 : (z : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) ∈
      totalRationalRelations (Spec (CommRingCat.of R)) dimX := by
    refine hinj _ ?_
    cases RE
    exact h1
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  cases RX
  exact h2

/-- **Homotopy invariance of the rational Chow groups**: the flat pullback along a trivialised
affine vector bundle of finite rank is bijective. -/
theorem chowPullbackBundle_bijective (hdim : HasUniversalDimensionFormula R)
    (hunit : UnitDifferences R) :
    Function.Bijective (chowPullbackBundle e dimX dimE i RX RE) :=
  ⟨chowPullbackBundle_injective e dimX dimE i RX RE hdim hunit,
    chowPullbackBundle_surjective' e dimX dimE i RX RE
      (principalDivisorsHomogeneous_of_hasUniversalDimensionFormula e dimE hdim)⟩

/-- Homotopy invariance as an isomorphism of rational Chow groups
`A_i(Spec R) ≃ A_{i+r}(E)`. -/
noncomputable def chowPullbackBundle_equiv (hdim : HasUniversalDimensionFormula R)
    (hunit : UnitDifferences R) : RX.ChowGroup ≃ₗ[ℚ] RE.ChowGroup :=
  LinearEquiv.ofBijective _ (chowPullbackBundle_bijective e dimX dimE i RX RE hdim hunit)

@[simp]
theorem chowPullbackBundle_equiv_apply (hdim : HasUniversalDimensionFormula R)
    (hunit : UnitDifferences R) (α : RX.ChowGroup) :
    chowPullbackBundle_equiv e dimX dimE i RX RE hdim hunit α =
      chowPullbackBundle e dimX dimE i RX RE α :=
  rfl

/-- The zero-section Gysin isomorphism `0^! : A_{i+r}(E) ≃ A_i(Spec R)`, now unconditional apart
from the two hypotheses on the base ring. -/
noncomputable def zeroSectionGysinEquiv'' (hdim : HasUniversalDimensionFormula R)
    (hunit : UnitDifferences R) : RE.ChowGroup ≃ₗ[ℚ] RX.ChowGroup :=
  zeroSectionGysin' e dimX dimE i RX RE
    (principalDivisorsHomogeneous_of_hasUniversalDimensionFormula e dimE hdim)
    (chowPullbackBundle_injective e dimX dimE i RX RE hdim hunit)

/-- The zero-section Gysin map undoes the flat pullback. -/
@[simp]
theorem zeroSectionGysinEquiv''_pullback (hdim : HasUniversalDimensionFormula R)
    (hunit : UnitDifferences R) (α : RX.ChowGroup) :
    zeroSectionGysinEquiv'' e dimX dimE i RX RE hdim hunit
        (chowPullbackBundle e dimX dimE i RX RE α) = α :=
  zeroSectionGysin'_pullback e dimX dimE i RX RE _ _ α

/-- The flat pullback undoes the zero-section Gysin map. -/
@[simp]
theorem pullback_zeroSectionGysinEquiv'' (hdim : HasUniversalDimensionFormula R)
    (hunit : UnitDifferences R) (β : RE.ChowGroup) :
    chowPullbackBundle e dimX dimE i RX RE
        (zeroSectionGysinEquiv'' e dimX dimE i RX RE hdim hunit β) = β :=
  pullback_zeroSectionGysin' e dimX dimE i RX RE _ _ β

end Injectivity

end VectorBundle

end GromovWitten.AlgebraicGeometry.IntersectionTheory
