/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleSectionGysinIdentity

/-!
# Fulton's symmetric divisor identity in the affine model

This file proves the cycle-level identity behind Fulton's Theorem 2.4 (`Intersection Theory`,
2nd ed.) directly for two elements `a, b` of a Noetherian domain `A` with no common height-one
prime: the cycles `∑_{q height 1, b ∈ q} ord_q(b) · [div of ā on V(q)]` and
`∑_{q height 1, a ∈ q} ord_q(a) · [div of b̄ on V(q)]` on `Spec A` are equal.  This generalises
`VectorBundle.sectionGysin_elementGenerator_eq_finsum` of
`GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleSectionGysinIdentity`, which proves the
same statement for `A = Polynomial R` and one of the two elements equal to `T - c`, arising
inside the proof of the injectivity of the flat pullback along a trivial line bundle.  Unlike
that file, the present statement has no extra ambient "total space" layer, since `a` and `b`
already live in `A` itself; this makes the finiteness bookkeeping considerably simpler, because
every height-one prime containing a fixed nonzero element is automatically a *minimal* prime
over the ideal it generates, and a Noetherian ring has only finitely many minimal primes over
any given ideal.

## Contents

* `VectorBundle.Affine.elementGenerator`: the principal-divisor generator on `Spec A` attached to
  a prime `q` and an element `a ∉ q`, together with the translation of its divisor's coefficients
  into `Ring.ord` (`VectorBundle.Affine.elementGenerator_divisor_apply_of_le`,
  `VectorBundle.Affine.elementGenerator_divisor_apply_of_not_le`).
* `VectorBundle.Affine.heightOne_containing_finite`: for a nonzero `x : A`, the set of height-one
  primes containing `x` is finite (every such prime is minimal over `Ideal.span {x}`).
* `VectorBundle.Affine.divisorSymmetry`: the symmetric local identity, Fulton's Theorem 2.4 for
  `Spec A`.
* `VectorBundle.Affine.divisorSymmetry_sub`: the difference of the two cycles is `0`.

## Hypotheses taken as arguments

`hdim : ∀ P : Ideal A, P.IsPrime → HasDimensionFormula (A ⧸ P)` supplies the catenarity used to
identify the height of a point above a height-one prime.  No other hypothesis is assumed, and
there is no `sorry` and no new axiom.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace VectorBundle

namespace Affine

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/-! ## The principal-divisor generator on `Spec A` attached to a prime `q` -/

/-- The quotient of a Noetherian domain by a prime ideal is a domain, in the shape instance
search needs for the corresponding object of `CommRingCat`. -/
instance isDomain_quotient (q : Ideal A) [q.IsPrime] :
    IsDomain ↑(CommRingCat.of (A ⧸ q)) :=
  inferInstanceAs (IsDomain (A ⧸ q))

/-- The quotient of a Noetherian ring by an ideal is Noetherian, in the shape instance search
needs for the corresponding object of `CommRingCat`. -/
instance isNoetherianRing_quotient (q : Ideal A) :
    IsNoetherianRing ↑(CommRingCat.of (A ⧸ q)) :=
  inferInstanceAs (IsNoetherianRing (A ⧸ q))

/-- The integral closed subscheme `V(q) ⊆ Spec A` cut out by a prime ideal `q`. -/
noncomputable def quotientSubscheme (q : Ideal A) [q.IsPrime] :
    IntegralClosedSubscheme (Spec (CommRingCat.of A)) where
  scheme := Spec (CommRingCat.of (A ⧸ q))
  inclusion := quotImmersion q

omit [IsDomain A] [IsNoetherianRing A] in
/-- The class of an element outside a prime `q` is a nonzero element of the quotient. -/
theorem quotientMk_ne_zero (q : Ideal A) (x : A) (hx : x ∉ q) :
    (Ideal.Quotient.mk q x : A ⧸ q) ≠ 0 :=
  fun h ↦ hx (Ideal.Quotient.eq_zero_iff_mem.1 h)

/-- The rational function on the subvariety `V(q)` determined by an element outside `q`. -/
noncomputable def elementFunction (q : Ideal A) [q.IsPrime] (x : A) (hx : x ∉ q) :
    (Spec (CommRingCat.of (A ⧸ q))).functionFieldˣ :=
  functionFieldUnit (CommRingCat.of (A ⧸ q)) (Ideal.Quotient.mk q x) (quotientMk_ne_zero q x hx)

/-- The principal-divisor generator on the subvariety `V(q)` of `Spec A` attached to an element
`x` not lying in `q`. -/
noncomputable def elementGenerator (q : Ideal A) [q.IsPrime] (x : A) (hx : x ∉ q) :
    RationalFunctionGenerator (Spec (CommRingCat.of A)) where
  subspace := quotientSubscheme q
  function := elementFunction q x hx

/-- The point of `V(q)` corresponding to a prime of `A` containing `q`. -/
noncomputable def quotientPoint (q Q : Ideal A) (hQp : Q.IsPrime) (hqQ : q ≤ Q) :
    ↥(Spec (CommRingCat.of (A ⧸ q))) :=
  show PrimeSpectrum (A ⧸ q) from
    ⟨Q.map (Ideal.Quotient.mk q),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hqQ)⟩

omit [IsDomain A] [IsNoetherianRing A] in
/-- The prime attached to `quotientPoint` is the extension of `Q` along the quotient map. -/
theorem quotientPoint_asIdeal (q Q : Ideal A) (hQp : Q.IsPrime) (hqQ : q ≤ Q) :
    (quotientPoint q Q hQp hqQ : PrimeSpectrum (A ⧸ q)).asIdeal = Q.map (Ideal.Quotient.mk q) :=
  rfl

omit [IsDomain A] [IsNoetherianRing A] in
/-- The closed immersion of `V(q)` sends `quotientPoint` back to the prime it came from. -/
theorem quotImmersion_base_quotientPoint (q Q : Ideal A) (hQp : Q.IsPrime) (hqQ : q ≤ Q) :
    ((quotImmersion q).base (quotientPoint q Q hQp hqQ) : PrimeSpectrum A).asIdeal = Q := by
  change (Q.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = Q
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_eq_left.mpr hqQ

omit [IsDomain A] [IsNoetherianRing A] in
/-- The image of the closed immersion of `V(q)` consists of the primes containing `q`. -/
theorem mem_range_quotImmersion_iff (q : Ideal A) (Q : ↥(Spec (CommRingCat.of A))) :
    Q ∈ Set.range (quotImmersion q).base ↔ q ≤ (Q : PrimeSpectrum A).asIdeal := by
  constructor
  · rintro ⟨y, rfl⟩
    intro x hx
    change Ideal.Quotient.mk q x ∈ (y : PrimeSpectrum (A ⧸ q)).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact Ideal.zero_mem _
  · intro hqQ
    exact ⟨quotientPoint q _ (Q : PrimeSpectrum A).isPrime hqQ,
      PrimeSpectrum.ext (quotImmersion_base_quotientPoint q _ _ hqQ)⟩

omit [IsDomain A] in
/-- The coefficient of the divisor of `elementGenerator` at a point of `V(q)`. -/
theorem elementGenerator_divisor_apply_image (q : Ideal A) [q.IsPrime] (x : A) (hx : x ∉ q)
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (Q : ↥(Spec (CommRingCat.of (A ⧸ q)))) :
    (elementGenerator q x hx).divisor dimA ((quotImmersion q).base Q) =
      (((Spec (CommRingCat.of (A ⧸ q))).ord
        (elementFunction q x hx : (Spec (CommRingCat.of (A ⧸ q))).functionField) Q : ℤ) : ℚ) :=
  AlgebraicCycle.map_closedImmersion_apply_image (quotImmersion q) (dimA : _ → ℤ) _ Q

omit [IsDomain A] in
/-- The coefficient of the divisor of `elementGenerator` at a prime containing `q`, computed as
the order of vanishing at the corresponding point of `V(q)`. -/
theorem elementGenerator_divisor_apply_of_le (q : Ideal A) [q.IsPrime] (x : A) (hx : x ∉ q)
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (Q : ↥(Spec (CommRingCat.of A))) (hqQ : q ≤ (Q : PrimeSpectrum A).asIdeal) :
    (elementGenerator q x hx).divisor dimA Q =
      (((Spec (CommRingCat.of (A ⧸ q))).ord
        (elementFunction q x hx : (Spec (CommRingCat.of (A ⧸ q))).functionField)
        (quotientPoint q (Q : PrimeSpectrum A).asIdeal (Q : PrimeSpectrum A).isPrime hqQ) : ℤ) :
        ℚ) := by
  have himg : (quotImmersion q).base
      (quotientPoint q (Q : PrimeSpectrum A).asIdeal (Q : PrimeSpectrum A).isPrime hqQ) = Q :=
    PrimeSpectrum.ext (quotImmersion_base_quotientPoint q _ _ hqQ)
  have h := elementGenerator_divisor_apply_image q x hx dimA
    (quotientPoint q (Q : PrimeSpectrum A).asIdeal (Q : PrimeSpectrum A).isPrime hqQ)
  rwa [himg] at h

omit [IsDomain A] in
/-- The divisor of `elementGenerator` vanishes off the subvariety `V(q)`. -/
theorem elementGenerator_divisor_apply_of_not_le (q : Ideal A) [q.IsPrime] (x : A) (hx : x ∉ q)
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (Q : ↥(Spec (CommRingCat.of A))) (hQ : ¬ q ≤ (Q : PrimeSpectrum A).asIdeal) :
    (elementGenerator q x hx).divisor dimA Q = 0 :=
  AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range (quotImmersion q) (dimA : _ → ℤ) _ Q
    (fun h ↦ hQ ((mem_range_quotImmersion_iff q Q).1 h))

/-! ## Finiteness of the height-one primes containing a nonzero element -/

omit [IsNoetherianRing A] in
/-- A height-one prime containing a nonzero element `x` is a minimal prime over `Ideal.span {x}`:
any prime `≤ q` containing `x` and properly smaller than `q` would have height `0`, forcing it to
be `⊥`, contradicting `x ≠ 0`. -/
theorem isMinimalPrime_of_height_eq_one (x : A) (hx : x ≠ 0) (q : Ideal A) [q.IsPrime]
    (hq1 : q.height = 1) (hxq : x ∈ q) : (Ideal.span {x}).IsMinimalPrime q := by
  refine ⟨⟨‹q.IsPrime›, (Ideal.span_singleton_le_iff_mem q).mpr hxq⟩, ?_⟩
  intro y hy hyq
  rcases eq_or_lt_of_le hyq with h | h
  · exact h.ge
  · exfalso
    let _ : y.IsPrime := hy.1
    have hstep : y.height + 1 ≤ q.height := Ideal.height_add_one_le_of_lt_of_isPrime h
    rw [hq1] at hstep
    have hy0 : y.height = 0 := by
      have h2 : y.height + 1 ≤ (0 : ℕ∞) + 1 := by rwa [zero_add]
      exact le_antisymm ((ENat.add_le_add_iff_right (by norm_num)).mp h2) bot_le
    have hybot : y = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp hy0
    exact hx (by
      have hxy : x ∈ y := hy.2 (Ideal.mem_span_singleton_self x)
      rwa [hybot, Ideal.mem_bot] at hxy)

/-- For a nonzero element `x` of a Noetherian domain, the set of height-one primes containing
`x` is finite: every such prime is minimal over `Ideal.span {x}` by
`isMinimalPrime_of_height_eq_one`, and a Noetherian ring has only finitely many minimal primes
over any given ideal. -/
theorem heightOne_containing_finite (x : A) (hx : x ≠ 0) :
    {q : PrimeSpectrum A | q.asIdeal.height = 1 ∧ x ∈ q.asIdeal}.Finite := by
  have hinj : Set.InjOn (fun q : PrimeSpectrum A ↦ q.asIdeal)
      {q : PrimeSpectrum A | q.asIdeal.height = 1 ∧ x ∈ q.asIdeal} :=
    fun q _ q' _ h ↦ PrimeSpectrum.ext h
  have hmaps : Set.MapsTo (fun q : PrimeSpectrum A ↦ q.asIdeal)
      {q : PrimeSpectrum A | q.asIdeal.height = 1 ∧ x ∈ q.asIdeal}
      (Ideal.span {x}).minimalPrimes := by
    rintro q ⟨hq1, hxq⟩
    let _ : q.asIdeal.IsPrime := q.isPrime
    exact isMinimalPrime_of_height_eq_one x hx q.asIdeal hq1 hxq
  exact Set.Finite.of_finite_image
    (((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {x})).subset
      (hmaps.image_subset)))
    hinj

/-! ## Coefficients of the divisor in terms of `Ring.ord` -/

omit [IsDomain A] in
/-- The coefficient of the divisor of `x` on the subvariety `V(q)` at a point of `V(q)` of
height one is the length-theoretic order of vanishing of `x` in the localisation of `A ⧸ q` at
that point. -/
theorem divisor_apply_eq_ringOrd (q : Ideal A) [q.IsPrime] (x : A) (hx : x ∉ q)
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (Q : PrimeSpectrum (A ⧸ q)) (hht : Q.asIdeal.height = 1) :
    ((elementGenerator q x hx).divisor dimA :
        ↥(Spec (CommRingCat.of A)) → ℚ) ((quotImmersion q).base Q) =
      ((Ring.ord (Localization.AtPrime Q.asIdeal)
        (algebraMap (A ⧸ q) (Localization.AtPrime Q.asIdeal)
          (Ideal.Quotient.mk q x))).toNat : ℚ) := by
  have hco : Order.coheight (show ↥(Spec (CommRingCat.of (A ⧸ q))) from Q) = 1 := by
    rw [coheight_eq_ideal_height (A ⧸ q) Q]
    exact hht
  have hord :
      ((Spec (CommRingCat.of (A ⧸ q))).ord
          (elementFunction q x hx : (Spec (CommRingCat.of (A ⧸ q))).functionField)
          (show ↥(Spec (CommRingCat.of (A ⧸ q))) from Q) : ℤ) =
        ((Ring.ord (Localization.AtPrime Q.asIdeal)
          (algebraMap (A ⧸ q) (Localization.AtPrime Q.asIdeal)
            (Ideal.Quotient.mk q x))).toNat : ℤ) :=
    scheme_ord_eq_localization (CommRingCat.of (A ⧸ q))
      (show ↥(Spec (CommRingCat.of (A ⧸ q))) from Q) (Ideal.Quotient.mk q x)
      (quotientMk_ne_zero q x hx) hco
  rw [elementGenerator_divisor_apply_image q x hx dimA
    (show ↥(Spec (CommRingCat.of (A ⧸ q))) from Q), hord]
  norm_num

omit [IsDomain A] in
/-- The coefficient of the divisor of `x` on the subvariety `V(q)` vanishes at a point whose
height is not one, because `Scheme.ord` is junk zero away from codimension one. -/
theorem divisor_apply_eq_zero_of_height_ne (q : Ideal A) [q.IsPrime] (x : A) (hx : x ∉ q)
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (Q : PrimeSpectrum (A ⧸ q)) (hht : Q.asIdeal.height ≠ 1) :
    ((elementGenerator q x hx).divisor dimA :
        ↥(Spec (CommRingCat.of A)) → ℚ) ((quotImmersion q).base Q) = 0 := by
  have hco : Order.coheight (show ↥(Spec (CommRingCat.of (A ⧸ q))) from Q) ≠ 1 := by
    rw [coheight_eq_ideal_height (A ⧸ q) Q]
    exact hht
  rw [elementGenerator_divisor_apply_image q x hx dimA
    (show ↥(Spec (CommRingCat.of (A ⧸ q))) from Q),
    _root_.AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hco]
  norm_num

omit [IsDomain A] in
/-- The length-theoretic order of vanishing occurring in a divisor coefficient is finite. -/
theorem divisor_ringOrd_ne_top (q : Ideal A) [q.IsPrime] (x : A) (hx : x ∉ q)
    (Q : PrimeSpectrum (A ⧸ q)) (hht : Q.asIdeal.height = 1) :
    Ring.ord (Localization.AtPrime Q.asIdeal)
      (algebraMap (A ⧸ q) (Localization.AtPrime Q.asIdeal) (Ideal.Quotient.mk q x)) ≠ ⊤ := by
  have hco : Order.coheight (show ↥(Spec (CommRingCat.of (A ⧸ q))) from Q) = 1 := by
    rw [coheight_eq_ideal_height (A ⧸ q) Q]
    exact hht
  exact localization_ord_ne_top (CommRingCat.of (A ⧸ q))
    (show ↥(Spec (CommRingCat.of (A ⧸ q))) from Q) (Ideal.Quotient.mk q x)
    (quotientMk_ne_zero q x hx) hco

omit [IsDomain A] in
/-- The coefficient of the divisor of `x` on the subvariety `V(q)` vanishes at a prime `X ⊇ q`
whose image in `A ⧸ q` does not have height one. -/
theorem divisor_apply_eq_zero_of_le_of_height_ne (q : Ideal A) [q.IsPrime] (x : A) (hx : x ∉ q)
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (X : PrimeSpectrum A) (hqX : q ≤ X.asIdeal)
    (hht : (X.asIdeal.map (Ideal.Quotient.mk q)).height ≠ 1) :
    ((elementGenerator q x hx).divisor dimA : ↥(Spec (CommRingCat.of A)) → ℚ) X = 0 := by
  have himg : (quotImmersion q).base (quotientPoint q X.asIdeal X.isPrime hqX) = X :=
    PrimeSpectrum.ext (quotImmersion_base_quotientPoint q _ _ hqX)
  have hstep := divisor_apply_eq_zero_of_height_ne q x hx dimA
    (quotientPoint q X.asIdeal X.isPrime hqX)
    (by rw [quotientPoint_asIdeal]; exact hht)
  rwa [himg] at hstep

omit [IsDomain A] in
/-- The key comparison: the coefficient of the divisor of `x` on `V(q)` at a prime `X ⊇ q` whose
image in `A ⧸ q` has height one equals the second factor of `VectorBundle.symTerm` attached to
`q` and `X`. -/
theorem divisor_apply_eq_symTerm_snd (q : Ideal A) [q.IsPrime] (x : A) (hx : x ∉ q)
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (X : PrimeSpectrum A) (hqX : q ≤ X.asIdeal)
    (hht : (X.asIdeal.map (Ideal.Quotient.mk q)).height = 1) :
    ((elementGenerator q x hx).divisor dimA : ↥(Spec (CommRingCat.of A)) → ℚ) X =
      ((Ring.ord (Localization.AtPrime X.asIdeal ⧸
          q.map (algebraMap A (Localization.AtPrime X.asIdeal)))
        (Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime X.asIdeal) x))).toNat : ℚ) := by
  let _ : (X.asIdeal.map (Ideal.Quotient.mk q)).IsPrime :=
    SectionGysinIdentity.map_quotient_isPrime q X.asIdeal hqX
  let Q0 : PrimeSpectrum (A ⧸ q) := ⟨X.asIdeal.map (Ideal.Quotient.mk q), ‹_›⟩
  have hQ0eq : quotientPoint q X.asIdeal X.isPrime hqX = Q0 := rfl
  have himg : (quotImmersion q).base Q0 = X := by
    rw [← hQ0eq]
    exact PrimeSpectrum.ext (quotImmersion_base_quotientPoint q _ _ hqX)
  have hstep := divisor_apply_eq_ringOrd q x hx dimA Q0 hht
  rw [himg] at hstep
  rw [hstep, SectionGysinIdentity.ring_ord_quotient_atPrime q X.asIdeal hqX _ x]

/-- The natural-number order of vanishing of `x` at a prime `q`. -/
noncomputable def ordAt (q : Ideal A) [q.IsPrime] (x : A) : ℕ :=
  (Ring.ord (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) x)).toNat

/-! ## Consequences of a fixed point having height two -/

/-- Given the dimension formula, a height-one prime `q ≤ X` whose extension to `A ⧸ q` has
height one forces `X` to have height two. -/
theorem height_two_of_le (hdim : ∀ P : Ideal A, P.IsPrime → HasDimensionFormula (A ⧸ P))
    (hA : HasDimensionFormula A) (q : Ideal A) [q.IsPrime] (X : Ideal A) [X.IsPrime]
    (hq1 : q.height = 1) (hqX : q ≤ X) (hX1 : (X.map (Ideal.Quotient.mk q)).height = 1) :
    X.height = 2 :=
  SectionGysinIdentity.height_eq_two hA q X (hdim q ‹q.IsPrime›) hq1 hX1 hqX

omit [IsDomain A] [IsNoetherianRing A] in
/-- If `X` has height two and `q ≤ X` has height one, there is no prime strictly between `q` and
`X`: any such prime `W'` would satisfy `q.height + 1 ≤ W'.height` and `W'.height + 1 ≤ X.height`,
forcing `2 ≤ W'.height ≤ 1`.  Hence the extension of `X` to `A ⧸ q` automatically has height
one. -/
theorem height_map_eq_one_of_height_two (q : Ideal A) [q.IsPrime] (X : Ideal A) [X.IsPrime]
    (hq1 : q.height = 1) (hX2 : X.height = 2) (hqX : q ≤ X) :
    (X.map (Ideal.Quotient.mk q)).height = 1 := by
  have hqXlt : q < X := by
    refine lt_of_le_of_ne hqX (fun h ↦ ?_)
    rw [h, hX2] at hq1
    exact absurd hq1 (by norm_num)
  refine height_map_eq_one_of_no_middle q X hqXlt (fun W' hW' hqW' hW'X ↦ ?_)
  let _ : W'.IsPrime := hW'
  have h1 : q.height + 1 ≤ W'.height := Ideal.height_add_one_le_of_lt_of_isPrime hqW'
  rw [hq1] at h1
  have h2 : W'.height + 1 ≤ X.height := Ideal.height_add_one_le_of_lt_of_isPrime hW'X
  rw [hX2] at h2
  have h1' : (2 : ℕ∞) ≤ W'.height := by
    rw [show (2 : ℕ∞) = 1 + 1 from rfl]; exact h1
  have h2' : W'.height ≤ 1 :=
    (ENat.add_le_add_iff_right (by norm_num)).mp
      (show W'.height + 1 ≤ 1 + 1 by rw [show (1 : ℕ∞) + 1 = 2 from rfl]; exact h2)
  exact absurd (h1'.trans h2') (by norm_num)

omit [IsNoetherianRing A] in
/-- A nonzero prime strictly below a height-two prime automatically has height one: the upper
bound comes from `Ideal.height_add_one_le_of_lt_of_isPrime` applied to the given inequality, and
the lower bound from the same fact applied to `⊥ < q0`. -/
theorem height_eq_one_of_lt_height_two (q0 X : Ideal A) [q0.IsPrime] [X.IsPrime]
    (hX2 : X.height = 2) (hlt : q0 < X) (hne0 : q0 ≠ ⊥) : q0.height = 1 := by
  have hle : q0.height ≤ 1 := by
    have h2 : q0.height + 1 ≤ X.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [hX2] at h2
    exact (ENat.add_le_add_iff_right (by norm_num)).mp
      (show q0.height + 1 ≤ 1 + 1 by rw [show (1 : ℕ∞) + 1 = 2 from rfl]; exact h2)
  have hge : (1 : ℕ∞) ≤ q0.height := by
    let _ : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
    have hbot : (⊥ : Ideal A).height = 0 := Ideal.height_eq_zero_iff_eq_bot.mpr rfl
    have := Ideal.height_add_one_le_of_lt_of_isPrime
      (bot_lt_iff_ne_bot.mpr hne0 : (⊥ : Ideal A) < q0)
    simpa [hbot] using this
  exact le_antisymm hle hge

/-! ## Comparison with Fulton's symmetric local identity -/

omit [IsDomain A] in
/-- The term `ordAt q b • (divisor of a on V(q))` evaluated at `X` equals the value of
`VectorBundle.symTerm` (cast down through `Nat`), whenever `q` is a height-one prime containing
`b`, contained in `X`, and `X` has height two. -/
theorem coeff_eq_symTerm_toNat (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (a b : A) (X : PrimeSpectrum A) (hX2 : X.asIdeal.height = 2)
    (q : Ideal A) [q.IsPrime] (hq1 : q.height = 1) (hbq : b ∈ q) (haq : a ∉ q)
    (hqX : q ≤ X.asIdeal) :
    (ordAt q b : ℚ) *
        ((elementGenerator q a haq).divisor dimA : ↥(Spec (CommRingCat.of A)) → ℚ) X =
      ((symTerm A X.asIdeal b a ⟨q, ‹q.IsPrime›⟩).toNat : ℚ) := by
  have hqXlt : q < X.asIdeal := by
    refine lt_of_le_of_ne hqX (fun h ↦ ?_)
    rw [h, hX2] at hq1
    exact absurd hq1 (by norm_num)
  have hXq1 : (X.asIdeal.map (Ideal.Quotient.mk q)).height = 1 :=
    height_map_eq_one_of_height_two q X.asIdeal hq1 hX2 hqX
  let _ : X.asIdeal.IsPrime := X.isPrime
  rw [symTerm_of_lt X.asIdeal b a ⟨q, ‹q.IsPrime›⟩ ⟨hqXlt, hbq⟩,
    divisor_apply_eq_symTerm_snd q a haq dimA X hqX hXq1, ENat.toNat_mul, ordAt]
  push_cast
  ring

/-- The order of vanishing at a height-one prime of a nonzero element is finite. -/
theorem ordAt_ne_top (q : Ideal A) [q.IsPrime] (hq1 : q.height = 1) (x : A) (hx : x ≠ 0) :
    Ring.ord (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) x) ≠ ⊤ := by
  have hco : Order.coheight (show ↥(Spec (CommRingCat.of A)) from ⟨q, ‹q.IsPrime›⟩) = 1 := by
    rw [coheight_eq_ideal_height A ⟨q, ‹q.IsPrime›⟩]
    exact hq1
  exact localization_ord_ne_top (CommRingCat.of A)
    (show ↥(Spec (CommRingCat.of A)) from ⟨q, ‹q.IsPrime›⟩) x hx hco

omit [IsDomain A] in
/-- The second factor of `VectorBundle.symTerm` occurring in `coeff_eq_symTerm_toNat` is
finite. -/
theorem symTerm_snd_ne_top (q : Ideal A) [q.IsPrime] (x : A) (hx : x ∉ q) (X : PrimeSpectrum A)
    (hqX : q ≤ X.asIdeal) (hht : (X.asIdeal.map (Ideal.Quotient.mk q)).height = 1) :
    Ring.ord (Localization.AtPrime X.asIdeal ⧸
        q.map (algebraMap A (Localization.AtPrime X.asIdeal)))
      (Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime X.asIdeal) x)) ≠ ⊤ := by
  let _ : (X.asIdeal.map (Ideal.Quotient.mk q)).IsPrime :=
    SectionGysinIdentity.map_quotient_isPrime q X.asIdeal hqX
  let Q0 : PrimeSpectrum (A ⧸ q) := ⟨X.asIdeal.map (Ideal.Quotient.mk q), ‹_›⟩
  have hne := divisor_ringOrd_ne_top q x hx Q0 hht
  rwa [SectionGysinIdentity.ring_ord_quotient_atPrime q X.asIdeal hqX _ x] at hne

/-- The divisor of `x` on `V(q)` (for `q` a height-one prime not containing `x`) vanishes at
every point of `Spec A` which does not have height two. -/
theorem divisor_apply_eq_zero_of_height_ne_two
    (hdim : ∀ P : Ideal A, P.IsPrime → HasDimensionFormula (A ⧸ P))
    (hA : HasDimensionFormula A) (q : Ideal A) [q.IsPrime] (hq1 : q.height = 1) (x : A)
    (hx : x ∉ q) (dimA : DimensionFunction (Spec (CommRingCat.of A))) (X : PrimeSpectrum A)
    (hX2 : X.asIdeal.height ≠ 2) :
    ((elementGenerator q x hx).divisor dimA : ↥(Spec (CommRingCat.of A)) → ℚ) X = 0 := by
  by_cases hqX : q ≤ X.asIdeal
  · by_cases hht : (X.asIdeal.map (Ideal.Quotient.mk q)).height = 1
    · exact absurd (height_two_of_le hdim hA q X.asIdeal hq1 hqX hht) hX2
    · exact divisor_apply_eq_zero_of_le_of_height_ne q x hx dimA X hqX hht
  · exact elementGenerator_divisor_apply_of_not_le q x hx dimA X hqX

omit [IsNoetherianRing A] in
/-- The support of the natural-number cast of `VectorBundle.symTerm` at a height-two prime `Y'`
is contained in the (finite) set of height-one primes containing `b'`. -/
theorem support_symTerm_toNat_subset (b' a' : A) (hb' : b' ≠ 0) (Y' : Ideal A) [Y'.IsPrime]
    (hY2 : Y'.height = 2) :
    Function.support (fun q0 : PrimeSpectrum A ↦ (symTerm A Y' b' a' q0).toNat) ⊆
      {q0 : PrimeSpectrum A | q0.asIdeal.height = 1 ∧ b' ∈ q0.asIdeal} := by
  intro q0 hq0
  simp only [Set.mem_ofPred_eq]
  by_contra hcon
  apply hq0
  by_cases hcond : q0.asIdeal < Y' ∧ b' ∈ q0.asIdeal
  · exact absurd ⟨height_eq_one_of_lt_height_two q0.asIdeal Y' hY2 hcond.1
      (fun hbot ↦ hb' (by rw [hbot] at hcond; exact hcond.2)), hcond.2⟩ hcon
  · simp [symTerm_eq_zero Y' b' a' q0 hcond]

/-- `VectorBundle.symTerm` at a height-two prime `Y'` is finite, given the "no common component"
hypothesis relating `b'` and `a'`: the first factor is `VectorBundle.localization_ord_ne_top` and
the second is `symTerm_snd_ne_top`, with `a' ∉ q0` supplied by `hcommon'` since `q0` automatically
has height one whenever it contributes. -/
theorem symTerm_ne_top (b' a' : A) (hb' : b' ≠ 0)
    (hcommon' : ∀ q : Ideal A, q.IsPrime → q.height = 1 → b' ∈ q → a' ∈ q → False)
    (Y' : Ideal A) [Y'.IsPrime] (hY2 : Y'.height = 2) (q0 : PrimeSpectrum A) :
    symTerm A Y' b' a' q0 ≠ ⊤ := by
  by_cases hcond : q0.asIdeal < Y' ∧ b' ∈ q0.asIdeal
  · rw [symTerm_of_lt Y' b' a' q0 hcond]
    have hq0ne0 : q0.asIdeal ≠ ⊥ := fun hbot ↦ hb' (by rw [hbot] at hcond; exact hcond.2)
    have hq1 : q0.asIdeal.height = 1 :=
      height_eq_one_of_lt_height_two q0.asIdeal Y' hY2 hcond.1 hq0ne0
    have hXq1 : (Y'.map (Ideal.Quotient.mk q0.asIdeal)).height = 1 :=
      height_map_eq_one_of_height_two q0.asIdeal Y' hq1 hY2 hcond.1.le
    have haq0 : a' ∉ q0.asIdeal := fun hmem ↦
      hcommon' q0.asIdeal q0.isPrime hq1 hcond.2 hmem
    exact WithTop.mul_ne_top (ordAt_ne_top q0.asIdeal hq1 b' hb')
      (symTerm_snd_ne_top q0.asIdeal a' haq0 (⟨Y', ‹Y'.IsPrime›⟩ : PrimeSpectrum A)
        hcond.1.le hXq1)
  · rw [symTerm_eq_zero Y' b' a' q0 hcond]
    exact (by norm_num : (0 : ℕ∞) ≠ ⊤)

/-! ## Assembling the symmetric sum -/

variable (dimA : DimensionFunction (Spec (CommRingCat.of A))) (a b : A)
  (hcommon : ∀ q : Ideal A, q.IsPrime → q.height = 1 → a ∈ q → b ∈ q → False)

open Classical in
/-- The `dite`-packaged term of the symmetric identity: the divisor of `a` on `V(q)` scaled by
`ordAt q b`, defined for every prime `q` of `A` and vanishing unless `q` has height one and
contains `b`. -/
noncomputable def termCycle (q0 : PrimeSpectrum A) :
    AlgebraicCycle (Spec (CommRingCat.of A)) ℚ :=
  if h : q0.asIdeal.height = 1 ∧ b ∈ q0.asIdeal then
    (ordAt q0.asIdeal b : ℚ) • (elementGenerator q0.asIdeal a
      (fun hmem ↦ hcommon q0.asIdeal q0.isPrime h.1 hmem h.2)).divisor dimA
  else 0

omit [IsDomain A] in
open Classical in
/-- `termCycle` vanishes unless `q0` has height one and contains `b`. -/
theorem support_termCycle_subset :
    Function.support (termCycle dimA a b hcommon) ⊆
      {q0 : PrimeSpectrum A | q0.asIdeal.height = 1 ∧ b ∈ q0.asIdeal} := by
  intro q0 hq0
  simp only [Set.mem_ofPred_eq]
  by_contra hcon
  exact hq0 (by simp only [termCycle, dif_neg hcon])

omit [IsDomain A] in
open Classical in
/-- The coefficient of `termCycle q0` at a point `X`, unfolded from the scalar multiple. -/
theorem termCycle_apply (q0 : PrimeSpectrum A) (X : ↥(Spec (CommRingCat.of A))) :
    (termCycle dimA a b hcommon q0 : ↥(Spec (CommRingCat.of A)) → ℚ) X =
      if h : q0.asIdeal.height = 1 ∧ b ∈ q0.asIdeal then
        (ordAt q0.asIdeal b : ℚ) *
          ((elementGenerator q0.asIdeal a
            (fun hmem ↦ hcommon q0.asIdeal q0.isPrime h.1 hmem h.2)).divisor dimA :
              ↥(Spec (CommRingCat.of A)) → ℚ) X
      else 0 := by
  by_cases h : q0.asIdeal.height = 1 ∧ b ∈ q0.asIdeal
  · simp only [termCycle, dif_pos h]
    have hcoe := congrFun (Function.locallyFinsuppWithin.coe_rational_smul
      (ordAt q0.asIdeal b : ℚ) ((elementGenerator q0.asIdeal a
        (fun hmem ↦ hcommon q0.asIdeal q0.isPrime h.1 hmem h.2)).divisor dimA)) X
    rw [hcoe]
    simp only [Pi.smul_apply, smul_eq_mul]
  · simp only [termCycle, dif_neg h]
    rfl

open Classical in
/-- `termCycle` vanishes at every point of `Spec A` which does not have height two. -/
theorem termCycle_apply_eq_zero_of_height_ne_two
    (hdim : ∀ P : Ideal A, P.IsPrime → HasDimensionFormula (A ⧸ P))
    (hA : HasDimensionFormula A) (X : ↥(Spec (CommRingCat.of A)))
    (hX2 : (X : PrimeSpectrum A).asIdeal.height ≠ 2) (q0 : PrimeSpectrum A) :
    (termCycle dimA a b hcommon q0 : ↥(Spec (CommRingCat.of A)) → ℚ) X = 0 := by
  rw [termCycle_apply dimA a b hcommon q0 X]
  by_cases h : q0.asIdeal.height = 1 ∧ b ∈ q0.asIdeal
  · rw [dif_pos h,
      divisor_apply_eq_zero_of_height_ne_two hdim hA q0.asIdeal h.1 a
        (fun hmem ↦ hcommon q0.asIdeal q0.isPrime h.1 hmem h.2) dimA (X : PrimeSpectrum A) hX2]
    ring
  · rw [dif_neg h]

open Classical in
/-- At a point `X` of height two, `termCycle q0` evaluates to the value of `VectorBundle.symTerm`
attached to `X`'s prime, `b` and `a`, cast down through `Nat`. -/
theorem termCycle_apply_eq_symTerm_toNat (hb : b ≠ 0) (X : PrimeSpectrum A)
    (hX2 : X.asIdeal.height = 2) (q0 : PrimeSpectrum A) :
    (termCycle dimA a b hcommon q0 : ↑(Spec (CommRingCat.of A)) → ℚ)
        (show ↑(Spec (CommRingCat.of A)) from X) =
      ((symTerm A X.asIdeal b a q0).toNat : ℚ) := by
  rw [termCycle_apply dimA a b hcommon q0 (show ↑(Spec (CommRingCat.of A)) from X)]
  by_cases hcond : q0.asIdeal < X.asIdeal ∧ b ∈ q0.asIdeal
  · obtain ⟨hqXlt, hbq⟩ := hcond
    have hq0ne0 : q0.asIdeal ≠ ⊥ := by
      intro hbot
      apply hb
      rw [hbot] at hbq
      exact hbq
    have hq1 : q0.asIdeal.height = 1 :=
      height_eq_one_of_lt_height_two q0.asIdeal X.asIdeal hX2 hqXlt hq0ne0
    have haq : a ∉ q0.asIdeal := fun hmem ↦ hcommon q0.asIdeal q0.isPrime hq1 hmem hbq
    rw [dif_pos ⟨hq1, hbq⟩]
    exact coeff_eq_symTerm_toNat dimA a b X hX2 q0.asIdeal hq1 hbq haq hqXlt.le
  · rw [symTerm_eq_zero X.asIdeal b a q0 hcond]
    by_cases h : q0.asIdeal.height = 1 ∧ b ∈ q0.asIdeal
    · rw [dif_pos h]
      have hqXne : q0.asIdeal ≠ X.asIdeal := by
        intro heq
        rw [heq, hX2] at h
        exact absurd h.1 (by norm_num)
      have hnle : ¬ q0.asIdeal ≤ X.asIdeal := fun hle ↦
        hcond ⟨lt_of_le_of_ne hle hqXne, h.2⟩
      rw [elementGenerator_divisor_apply_of_not_le q0.asIdeal a
        (fun hmem ↦ hcommon q0.asIdeal q0.isPrime h.1 hmem h.2) dimA
        (show ↑(Spec (CommRingCat.of A)) from X) hnle]
      simp
    · rw [dif_neg h]
      simp


/-! ## The main theorem -/

/-- **Fulton's symmetric divisor identity in the affine model.**  For a Noetherian domain `A`
satisfying the dimension formula and two nonzero elements `a, b` with no common height-one
prime, the cycles obtained by taking the divisor of `a` on `V(q)` for every height-one prime `q`
containing `b`, weighted by `ord_q(b)`, and the same construction with `a, b` exchanged, agree on
`Spec A`. -/
theorem divisorSymmetry (hdim : ∀ P : Ideal A, P.IsPrime → HasDimensionFormula (A ⧸ P))
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcommon : ∀ q : Ideal A, q.IsPrime → q.height = 1 → a ∈ q → b ∈ q → False) :
    (∑ᶠ q : {q : PrimeSpectrum A // q.asIdeal.height = 1 ∧ b ∈ q.asIdeal},
        (ordAt q.1.asIdeal b : ℚ) •
          (elementGenerator q.1.asIdeal a
            (fun h ↦ hcommon q.1.asIdeal q.1.isPrime q.2.1 h q.2.2)).divisor dimA) =
      ∑ᶠ q : {q : PrimeSpectrum A // q.asIdeal.height = 1 ∧ a ∈ q.asIdeal},
        (ordAt q.1.asIdeal a : ℚ) •
          (elementGenerator q.1.asIdeal b
            (fun h ↦ hcommon q.1.asIdeal q.1.isPrime q.2.1 q.2.2 h)).divisor dimA := by
  classical
  have hA : HasDimensionFormula A :=
    SectionGysinIdentity.hasDimensionFormula_of_ringEquiv (RingEquiv.quotientBot A)
      (hdim ⊥ Ideal.isPrime_bot)
  have hcommon' : ∀ q : Ideal A, q.IsPrime → q.height = 1 → b ∈ q → a ∈ q → False :=
    fun q hq h1 hbm ham ↦ hcommon q hq h1 ham hbm
  have hLHS : (∑ᶠ q : {q : PrimeSpectrum A // q.asIdeal.height = 1 ∧ b ∈ q.asIdeal},
      (ordAt q.1.asIdeal b : ℚ) • (elementGenerator q.1.asIdeal a
        (fun h ↦ hcommon q.1.asIdeal q.1.isPrime q.2.1 h q.2.2)).divisor dimA) =
      ∑ᶠ X, termCycle dimA a b hcommon X := by
    have hpt : ∀ q : {q : PrimeSpectrum A // q.asIdeal.height = 1 ∧ b ∈ q.asIdeal},
        (ordAt q.1.asIdeal b : ℚ) • (elementGenerator q.1.asIdeal a
          (fun h ↦ hcommon q.1.asIdeal q.1.isPrime q.2.1 h q.2.2)).divisor dimA =
          termCycle dimA a b hcommon q.1 := fun q ↦ by
      simp only [termCycle, dif_pos q.2]
    have hstep : (∑ᶠ x : {q0 : PrimeSpectrum A // q0.asIdeal.height = 1 ∧ b ∈ q0.asIdeal},
        termCycle dimA a b hcommon (x : PrimeSpectrum A)) =
        ∑ᶠ X ∈ {q0 : PrimeSpectrum A | q0.asIdeal.height = 1 ∧ b ∈ q0.asIdeal},
          termCycle dimA a b hcommon X :=
      finsum_set_coe_eq_finsum_mem {q0 : PrimeSpectrum A | q0.asIdeal.height = 1 ∧ b ∈ q0.asIdeal}
    rw [finsum_congr hpt, hstep, finsum_mem_def,
      Set.indicator_eq_self.2 (support_termCycle_subset dimA a b hcommon)]
  have hRHS : (∑ᶠ q : {q : PrimeSpectrum A // q.asIdeal.height = 1 ∧ a ∈ q.asIdeal},
      (ordAt q.1.asIdeal a : ℚ) • (elementGenerator q.1.asIdeal b
        (fun h ↦ hcommon q.1.asIdeal q.1.isPrime q.2.1 q.2.2 h)).divisor dimA) =
      ∑ᶠ X, termCycle dimA b a hcommon' X := by
    have hpt : ∀ q : {q : PrimeSpectrum A // q.asIdeal.height = 1 ∧ a ∈ q.asIdeal},
        (ordAt q.1.asIdeal a : ℚ) • (elementGenerator q.1.asIdeal b
          (fun h ↦ hcommon q.1.asIdeal q.1.isPrime q.2.1 q.2.2 h)).divisor dimA =
          termCycle dimA b a hcommon' q.1 := fun q ↦ by
      simp only [termCycle, dif_pos q.2]
    have hstep : (∑ᶠ x : {q0 : PrimeSpectrum A // q0.asIdeal.height = 1 ∧ a ∈ q0.asIdeal},
        termCycle dimA b a hcommon' (x : PrimeSpectrum A)) =
        ∑ᶠ X ∈ {q0 : PrimeSpectrum A | q0.asIdeal.height = 1 ∧ a ∈ q0.asIdeal},
          termCycle dimA b a hcommon' X :=
      finsum_set_coe_eq_finsum_mem {q0 : PrimeSpectrum A | q0.asIdeal.height = 1 ∧ a ∈ q0.asIdeal}
    rw [finsum_congr hpt, hstep, finsum_mem_def,
      Set.indicator_eq_self.2 (support_termCycle_subset dimA b a hcommon')]
  rw [hLHS, hRHS]
  apply Function.locallyFinsuppWithin.coe_injective
  funext Y
  dsimp only
  have hfinL : (Function.support (termCycle dimA a b hcommon)).Finite :=
    (heightOne_containing_finite b hb).subset (support_termCycle_subset dimA a b hcommon)
  have hfinR : (Function.support (termCycle dimA b a hcommon')).Finite :=
    (heightOne_containing_finite a ha).subset (support_termCycle_subset dimA b a hcommon')
  rw [finsum_cycle_apply _ hfinL, finsum_cycle_apply _ hfinR]
  by_cases hY2 : (Y : PrimeSpectrum A).asIdeal.height = 2
  · have hYp : (Y : PrimeSpectrum A).asIdeal.IsPrime := (Y : PrimeSpectrum A).isPrime
    have hz1 : ∀ q0, (termCycle dimA a b hcommon q0 : ↥(Spec (CommRingCat.of A)) → ℚ) Y =
        ((symTerm A (Y : PrimeSpectrum A).asIdeal b a q0).toNat : ℚ) := fun q0 ↦
      termCycle_apply_eq_symTerm_toNat dimA a b hcommon hb (Y : PrimeSpectrum A) hY2 q0
    have hz2 : ∀ q0, (termCycle dimA b a hcommon' q0 : ↥(Spec (CommRingCat.of A)) → ℚ) Y =
        ((symTerm A (Y : PrimeSpectrum A).asIdeal a b q0).toNat : ℚ) := fun q0 ↦
      termCycle_apply_eq_symTerm_toNat dimA b a hcommon' ha (Y : PrimeSpectrum A) hY2 q0
    simp only [hz1, hz2]
    have hchain : ∀ q q' : Ideal A, q.IsPrime → q'.IsPrime → ⊥ < q' → q' < q →
        q < (Y : PrimeSpectrum A).asIdeal → False := by
      intro q q' hq hq' h0 h1 h2
      let _ := hq
      let _ := hq'
      exact absurd
        (SectionGysinIdentity.three_le_height_of_chain q' q (Y : PrimeSpectrum A).asIdeal h0 h1 h2)
        (by rw [hY2]; norm_num)
    have hmin : ∀ q : Ideal A, q.IsPrime → q ≤ (Y : PrimeSpectrum A).asIdeal → a ∈ q → b ∈ q →
        q = (Y : PrimeSpectrum A).asIdeal := by
      intro q hq hqY ham hbm
      rcases eq_or_lt_of_le hqY with h | h
      · exact h
      · exfalso
        have hqne0 : q ≠ ⊥ := fun hbot ↦ ha (by rw [hbot] at ham; exact ham)
        have hq1 : q.height = 1 :=
          height_eq_one_of_lt_height_two q (Y : PrimeSpectrum A).asIdeal hY2 h hqne0
        exact hcommon q hq hq1 ham hbm
    have hsymEq := VectorBundle.localOrdSymmetry_symTerm VectorBundle.localOrdSymmetry A
      (Y : PrimeSpectrum A).asIdeal a b ha hb hchain hmin
    have hfin1 : (Function.support
        fun q0 ↦ (symTerm A (Y : PrimeSpectrum A).asIdeal b a q0).toNat).Finite :=
      (heightOne_containing_finite b hb).subset
        (support_symTerm_toNat_subset b a hb (Y : PrimeSpectrum A).asIdeal hY2)
    have hfin2 : (Function.support
        fun q0 ↦ (symTerm A (Y : PrimeSpectrum A).asIdeal a b q0).toNat).Finite :=
      (heightOne_containing_finite a ha).subset
        (support_symTerm_toNat_subset a b ha (Y : PrimeSpectrum A).asIdeal hY2)
    have hnat : (∑ᶠ q0, (symTerm A (Y : PrimeSpectrum A).asIdeal b a q0).toNat) =
        ∑ᶠ q0, (symTerm A (Y : PrimeSpectrum A).asIdeal a b q0).toNat :=
      finsum_toNat_eq _ _ hfin1 hfin2
        (symTerm_ne_top b a hb hcommon' (Y : PrimeSpectrum A).asIdeal hY2)
        (symTerm_ne_top a b ha hcommon (Y : PrimeSpectrum A).asIdeal hY2) hsymEq
    have hcast1 : ((∑ᶠ q0, (symTerm A (Y : PrimeSpectrum A).asIdeal b a q0).toNat : ℕ) : ℚ) =
        ∑ᶠ q0, ((symTerm A (Y : PrimeSpectrum A).asIdeal b a q0).toNat : ℚ) :=
      (Nat.castAddMonoidHom ℚ).map_finsum hfin1
    have hcast2 : ((∑ᶠ q0, (symTerm A (Y : PrimeSpectrum A).asIdeal a b q0).toNat : ℕ) : ℚ) =
        ∑ᶠ q0, ((symTerm A (Y : PrimeSpectrum A).asIdeal a b q0).toNat : ℚ) :=
      (Nat.castAddMonoidHom ℚ).map_finsum hfin2
    rw [← hcast1, ← hcast2, hnat]
  · have hz1 : ∀ q0, (termCycle dimA a b hcommon q0 : ↥(Spec (CommRingCat.of A)) → ℚ) Y = 0 :=
      termCycle_apply_eq_zero_of_height_ne_two dimA a b hcommon hdim hA Y hY2
    have hz2 : ∀ q0, (termCycle dimA b a hcommon' q0 : ↥(Spec (CommRingCat.of A)) → ℚ) Y = 0 :=
      termCycle_apply_eq_zero_of_height_ne_two dimA b a hcommon' hdim hA Y hY2
    simp only [hz1, hz2, finsum_zero]

/-- The difference of the two cycles of `divisorSymmetry` vanishes; this is the form ready for
the descent argument of the companion file (agent C2's `FirstChernClass.lean`). -/
theorem divisorSymmetry_sub (hdim : ∀ P : Ideal A, P.IsPrime → HasDimensionFormula (A ⧸ P))
    (dimA : DimensionFunction (Spec (CommRingCat.of A)))
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcommon : ∀ q : Ideal A, q.IsPrime → q.height = 1 → a ∈ q → b ∈ q → False) :
    (∑ᶠ q : {q : PrimeSpectrum A // q.asIdeal.height = 1 ∧ b ∈ q.asIdeal},
        (ordAt q.1.asIdeal b : ℚ) •
          (elementGenerator q.1.asIdeal a
            (fun h ↦ hcommon q.1.asIdeal q.1.isPrime q.2.1 h q.2.2)).divisor dimA) -
      ∑ᶠ q : {q : PrimeSpectrum A // q.asIdeal.height = 1 ∧ a ∈ q.asIdeal},
        (ordAt q.1.asIdeal a : ℚ) •
          (elementGenerator q.1.asIdeal b
            (fun h ↦ hcommon q.1.asIdeal q.1.isPrime q.2.1 q.2.2 h)).divisor dimA = 0 :=
  sub_eq_zero.mpr (divisorSymmetry hdim dimA a b ha hb hcommon)


end Affine

end VectorBundle

end GromovWitten.AlgebraicGeometry.IntersectionTheory
