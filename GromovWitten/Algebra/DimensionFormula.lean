/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.Algebra.FiniteTypeKrullDimension
import GromovWitten.AlgebraicGeometry.Cones.NormalConeDimension
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The dimension formula for finite type domains over a field

For a field `k`, a finitely generated `k`-algebra `A` which is a domain, and a prime `p` of `A`,

`dim (A ⧸ p) + ht p = dim A`.

This is the algebraic form of the statement that finite type algebras over a field are catenary
and equidimensional (Stacks 02JX, Matsumura 5.6, Eisenbud 13.A).

## Strategy

The inequality `ht p + dim (A ⧸ p) ≤ dim A` is formal (concatenate a chain below `p` with a
chain above it).  The content is the reverse inequality, proved in three steps.

1. `le_ringKrullDim_quotient_span_singleton`: for a polynomial ring `C = k[x₀, …, x_{s-1}]` and a
   nonzero non-unit `f`, `dim (C ⧸ (f)) ≥ s - 1`.  Writing `C = D[X]` for the variable `X = x_a`
   actually occurring in `f` (`MvPolynomial.degreeOf_eq_natDegree`), the coefficient ring `D`
   injects into `C ⧸ (f)` because `f ∣ C g` forces `g = 0` by degree reasons
   (`eq_zero_of_C_mem_span_singleton`); hence `trdeg_k (C ⧸ (f)) ≥ trdeg_k D = s - 1`.

2. `ringKrullDim_quotient_succ_eq_of_height_eq_one`: for a finite type `k`-domain `B` and a prime
   `P` of height one, `dim (B ⧸ P) + 1 = dim B`.  Noether normalization presents `B` as a finite
   extension of a polynomial ring `C` of dimension `dim B`; the contraction `Q = P ∩ C` again has
   height one, by incomparability and by going down (available because `C` is a unique
   factorization domain, hence integrally closed).  Since `C` is a UFD, `Q` is principal, so
   step 1 applies, and `dim (B ⧸ P) = dim (C ⧸ Q)` because the extension of the quotients is
   again finite and injective.

3. `ringKrullDim_quotient_add_height`: the general case, by induction along a chain of primes
   realising `ht p`; each step of such a chain is saturated, so step 2 applies to the quotient by
   the previous prime.

## Main results

* `ringKrullDim_quotient_add_height` — the dimension formula, in the form
  `ringKrullDim (A ⧸ p) + p.height = ringKrullDim A`.
* `hasDimensionFormula` — the same statement packaged as
  `GromovWitten.AlgebraicGeometry.HasDimensionFormula A`.
* `hasDimensionFormula_extendedRees`, `ringKrullDim_quotient_eq_of_mem_minimalPrimes'`,
  `ringKrullDim_associatedGradedRing'`, `pureTopologicalDimension_normalCone'` — the purity
  statements of `Cones/NormalConeDimension.lean` with their `HasDimensionFormula` hypothesis
  discharged.

Everything in this file is unconditional.
-/

namespace GromovWitten.Algebra

universe u

/-! ### Step 1: cutting a polynomial ring by one equation -/

section PolynomialStep

/-- If `F` has positive degree over a domain `D`, then no nonzero constant is a multiple of `F`.
-/
theorem eq_zero_of_C_mem_span_singleton {D : Type*} [CommRing D] [IsDomain D]
    {F : Polynomial D} (hF : 0 < F.natDegree) {g : D}
    (hg : Polynomial.C g ∈ Ideal.span {F}) : g = 0 := by
  by_contra hg0
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hg
  have hCg : (Polynomial.C g : Polynomial D) ≠ 0 := by
    simpa [Polynomial.C_eq_zero] using hg0
  have hh0 : h ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hh
    exact hCg hh.symm
  have hF0 : F ≠ 0 := fun h0 ↦ by simp [h0] at hF
  have hdeg : (h * F).natDegree = h.natDegree + F.natDegree :=
    Polynomial.natDegree_mul hh0 hF0
  rw [hh, Polynomial.natDegree_C] at hdeg
  omega

variable (k : Type u) [Field k]

/-- Presenting a polynomial ring in finitely many variables as a polynomial ring in one
distinguished variable `a` over the polynomial ring in the remaining variables. -/
noncomputable def mvPolynomialEquivPolynomial {s : ℕ} (a : Fin s) :
    MvPolynomial (Fin s) k ≃ₐ[k] Polynomial (MvPolynomial {b : Fin s // b ≠ a} k) :=
  (MvPolynomial.renameEquiv k (Equiv.optionSubtypeNe a).symm).trans
    (MvPolynomial.optionEquivLeft k {b : Fin s // b ≠ a})

/-- Under `mvPolynomialEquivPolynomial`, the degree in the distinguished variable becomes the
degree of a one-variable polynomial. -/
theorem natDegree_mvPolynomialEquivPolynomial {s : ℕ} (a : Fin s)
    (p : MvPolynomial (Fin s) k) :
    (mvPolynomialEquivPolynomial k a p).natDegree = p.degreeOf a := by
  classical
  rw [MvPolynomial.degreeOf_eq_natDegree]
  rfl

/-- The number of variables other than a fixed one. -/
theorem natCard_subtype_ne {s : ℕ} (a : Fin s) : Nat.card {b : Fin s // b ≠ a} = s - 1 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp

/-- **Step 1.**  For a nonzero non-unit `f` of a polynomial ring `C` in `s` variables over a
field whose span is prime, `dim (C ⧸ (f)) ≥ s - 1`. -/
theorem le_ringKrullDim_quotient_span_singleton {s : ℕ} {f : MvPolynomial (Fin s) k}
    (hf0 : f ≠ 0) (hfu : ¬ IsUnit f) (hp : (Ideal.span {f}).IsPrime) :
    ((s - 1 : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {f}) := by
  classical
  -- Some variable occurs in `f`.
  obtain ⟨a, ha⟩ : ∃ a, f.degreeOf a ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ b, f.degreeOf b = 0 := by
      intro b
      by_contra hb
      exact hcon ⟨b, hb⟩
    have hvars : f.vars = ∅ := by
      ext b
      simp [MvPolynomial.mem_vars_iff_degreeOf_ne_zero, hcon' b]
    rw [MvPolynomial.vars_eq_empty_iff_eq_C] at hvars
    obtain ⟨c, hc⟩ : ∃ c, f = MvPolynomial.C c := ⟨f.coeff 0, hvars⟩
    have hc0 : c ≠ 0 := fun h ↦ hf0 (by rw [hc, h, map_zero])
    refine hfu ?_
    rw [hc]
    exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hc0)
  set Φ := mvPolynomialEquivPolynomial k a with hΦ
  have hdeg : 0 < (Φ f).natDegree := by
    rw [hΦ, natDegree_mvPolynomialEquivPolynomial]
    omega
  -- Membership in `(f)` transports along `Φ`.
  have hmem : ∀ x : MvPolynomial (Fin s) k,
      x ∈ Ideal.span {f} → Φ x ∈ Ideal.span {Φ f} := by
    intro x hx
    rw [Ideal.mem_span_singleton'] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨Φ c, by rw [map_mul]⟩
  -- The coefficient ring injects into the quotient.
  let ψ : MvPolynomial {b : Fin s // b ≠ a} k →ₐ[k]
      (MvPolynomial (Fin s) k ⧸ Ideal.span {f}) :=
    (Ideal.Quotient.mkₐ k (Ideal.span {f})).comp
      (Φ.symm.toAlgHom.comp (IsScalarTower.toAlgHom k (MvPolynomial {b : Fin s // b ≠ a} k)
        (Polynomial (MvPolynomial {b : Fin s // b ≠ a} k))))
  have hψ : Function.Injective ψ := by
    intro g₁ g₂ hg
    have hsub : Φ.symm (Polynomial.C (g₁ - g₂)) ∈ Ideal.span {f} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have h1 : ψ g₁ - ψ g₂ = 0 := by rw [hg, sub_self]
      simpa [ψ, map_sub, Polynomial.C_sub] using h1
    have h2 : Polynomial.C (g₁ - g₂) ∈ Ideal.span {Φ f} := by
      have := hmem _ hsub
      rwa [AlgEquiv.apply_symm_apply] at this
    have := eq_zero_of_C_mem_span_singleton hdeg h2
    exact sub_eq_zero.mp this
  -- Transcendence degrees.
  have hdomain : IsDomain (MvPolynomial (Fin s) k ⧸ Ideal.span {f}) :=
    Ideal.Quotient.isDomain_iff_prime _ |>.mpr hp
  have hft : Algebra.FiniteType k (MvPolynomial (Fin s) k ⧸ Ideal.span {f}) :=
    Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ k (Ideal.span {f})) Ideal.Quotient.mk_surjective
  have htr : Algebra.trdeg k (MvPolynomial {b : Fin s // b ≠ a} k) ≤
      Algebra.trdeg k (MvPolynomial (Fin s) k ⧸ Ideal.span {f}) :=
    _root_.trdeg_le_of_injective ψ hψ
  have hdimD : ringKrullDim (MvPolynomial {b : Fin s // b ≠ a} k) =
      ((s - 1 : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      natCard_subtype_ne]
    simp
  rw [ringKrullDim_eq_toENat_trdeg k (MvPolynomial (Fin s) k ⧸ Ideal.span {f}), ← hdimD,
    ringKrullDim_eq_toENat_trdeg k (MvPolynomial {b : Fin s // b ≠ a} k)]
  exact_mod_cast OrderHomClass.mono Cardinal.toENat htr

end PolynomialStep

/-! ### Step 2: primes of height one -/

section HeightOne

/-- The Krull dimension of `A ⧸ p` plus the height of `p` is at most the Krull dimension of `A`:
a chain below `p` concatenates with a chain above it. -/
theorem ringKrullDim_quotient_add_height_le {A : Type u} [CommRing A] (x : PrimeSpectrum A) :
    ringKrullDim (A ⧸ x.asIdeal) + ((x.asIdeal.height : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim A := by
  have hne : Nonempty (PrimeSpectrum A) := ⟨x⟩
  have hco := PrimeSpectrum.coheight_eq_ringKrullDim_quotient x
  have hht := PrimeSpectrum.height_eq_orderHeight x
  calc ringKrullDim (A ⧸ x.asIdeal) + ((x.asIdeal.height : ℕ∞) : WithBot ℕ∞)
      = ((Order.height x + Order.coheight x : ℕ∞) : WithBot ℕ∞) := by
        rw [← hco, hht, WithBot.coe_add]
        exact add_comm _ _
    _ ≤ ringKrullDim A := by
        rw [ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty,
          WithBot.coe_le_coe]
        exact le_iSup (fun a : PrimeSpectrum A ↦ Order.height a + Order.coheight a) x

variable (k : Type u) [Field k]

/-- **Step 2.**  For a finitely generated `k`-algebra `B` which is a domain and a prime `P` of
height one, `dim (B ⧸ P) + 1 = dim B`.

The proof presents `B` as a finite extension of a polynomial ring `C` by Noether normalization;
the contraction `Q` of `P` to `C` has height one (incomparability gives `≥`, going down, valid
because `C` is a UFD hence integrally closed, gives `≤`), it is principal because `C` is a UFD,
and `dim (B ⧸ P) = dim (C ⧸ Q) ≥ dim C - 1` by step 1. -/
theorem ringKrullDim_quotient_succ_eq_of_height_eq_one (B : Type u) [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (P : Ideal B) [hP : P.IsPrime] (hh : P.height = 1) :
    ringKrullDim (B ⧸ P) + 1 = ringKrullDim B := by
  classical
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  algebraize [g.toRingHom]
  have htower : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have hmf : Module.Finite (MvPolynomial (Fin s) k) B := hfin
  have hint : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := Algebra.IsIntegral.of_finite _ _
  have hfaith : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hdimB : ringKrullDim B = ((s : ℕ) : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) k) B,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  -- the contraction of `P`
  have hQprime : (P.under (MvPolynomial (Fin s) k)).IsPrime := Ideal.IsPrime.under _ _
  -- comap of primes is strictly monotone (incomparability)
  have hmono : StrictMono
      (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin s) k) B)) := fun x y hxy ↦ by
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hxy ⊢
    exact Ideal.IsIntegral.comap_lt_comap hxy
  have hge : (1 : ℕ∞) ≤ (P.under (MvPolynomial (Fin s) k)).height := by
    have h1 := Order.height_le_height_apply_of_strictMono _ hmono (⟨P, hP⟩ : PrimeSpectrum B)
    rw [← PrimeSpectrum.height_eq_orderHeight (⟨P, hP⟩ : PrimeSpectrum B), hh] at h1
    exact le_trans h1 (le_of_eq (PrimeSpectrum.height_eq_orderHeight
      (⟨P.under (MvPolynomial (Fin s) k), hQprime⟩ : PrimeSpectrum (MvPolynomial (Fin s) k))).symm)
  -- going down
  have hgd : Algebra.HasGoingDown (MvPolynomial (Fin s) k) B := inferInstance
  have hle : (P.under (MvPolynomial (Fin s) k)).height ≤ 1 := by
    rw [PrimeSpectrum.height_eq_orderHeight
      (⟨P.under (MvPolynomial (Fin s) k), hQprime⟩ : PrimeSpectrum _)]
    refine Order.height_le fun l hlast ↦ ?_
    have hlo : P.LiesOver l.last.asIdeal := by
      rw [hlast]
      exact ⟨rfl⟩
    obtain ⟨L, hLlen, hLlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
    have h3 := Order.length_le_height_last (p := L)
    rw [hLlast, hLlen] at h3
    rw [← PrimeSpectrum.height_eq_orderHeight (⟨P, hP⟩ : PrimeSpectrum B), hh] at h3
    exact h3
  have hQh : (P.under (MvPolynomial (Fin s) k)).height = 1 := le_antisymm hle hge
  -- `Q` is principal because the polynomial ring is a UFD
  have hPrinc : (P.under (MvPolynomial (Fin s) k)).IsPrincipal :=
    UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hQh
  obtain ⟨q, hq⟩ := Submodule.IsPrincipal.principal (P.under (MvPolynomial (Fin s) k))
  have hqspan : P.under (MvPolynomial (Fin s) k) = Ideal.span {q} := hq
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0] at hqspan
    simp only [Ideal.span_singleton_zero] at hqspan
    rw [hqspan] at hQh
    simp at hQh
  have hqu : ¬ IsUnit q := by
    intro hu
    rw [Ideal.span_singleton_eq_top.mpr hu] at hqspan
    exact hQprime.ne_top hqspan
  have hqp : (Ideal.span {q} : Ideal (MvPolynomial (Fin s) k)).IsPrime := hqspan ▸ hQprime
  have hstep1 := le_ringKrullDim_quotient_span_singleton k hq0 hqu hqp
  -- the quotients form an integral extension again
  have hfaith' : FaithfulSMul
      (MvPolynomial (Fin s) k ⧸ P.under (MvPolynomial (Fin s) k)) (B ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.quotientMap_injective
  have hdimq : ringKrullDim (B ⧸ P) =
      ringKrullDim (MvPolynomial (Fin s) k ⧸ P.under (MvPolynomial (Fin s) k)) :=
    ringKrullDim_eq_of_isIntegral _ _
  -- `1 ≤ s`
  have hs : 1 ≤ s := by
    by_contra hcon
    have hs0 : s = 0 := by omega
    have hle0 := Ideal.height_le_ringKrullDim_of_ne_top (I := P) hP.ne_top
    rw [hh, hdimB, hs0] at hle0
    have h10 : (1 : ℕ) ≤ (0 : ℕ) := by exact_mod_cast hle0
    omega
  -- assemble
  refine le_antisymm ?_ ?_
  · have hup := ringKrullDim_quotient_add_height_le (⟨P, hP⟩ : PrimeSpectrum B)
    change ringKrullDim (B ⧸ P) + ((P.height : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim B at hup
    rw [hh] at hup
    simpa using hup
  · rw [hdimB, hdimq, hqspan]
    have hcast : ((s - 1 : ℕ) : WithBot ℕ∞) + 1 = ((s : ℕ) : WithBot ℕ∞) := by
      have hss : (s - 1 : ℕ) + 1 = s := by omega
      rw [← hss]
      push_cast
      ring
    rw [← hcast]
    exact add_le_add hstep1 le_rfl

end HeightOne

/-! ### Step 3: the general dimension formula -/

section General

variable (k : Type u) [Field k]

/-- Auxiliary induction on the height: for a finitely generated `k`-algebra `A` which is a
domain and a prime `p` of height `n`, `dim (A ⧸ p) + n = dim A`.

The induction step uses a chain of primes of length `n + 1` ending at `p`.  Its next-to-last
term `q` has height exactly `n`, and no prime lies strictly between `q` and `p`, so the image of
`p` in the finitely generated `k`-domain `A ⧸ q` has height one and
`ringKrullDim_quotient_succ_eq_of_height_eq_one` applies. -/
theorem ringKrullDim_quotient_add_height_aux (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] : ∀ (n : ℕ) (p : Ideal A) (_ : p.IsPrime), p.height = (n : ℕ∞) →
      ringKrullDim (A ⧸ p) + ((n : ℕ) : WithBot ℕ∞) = ringKrullDim A := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    have hbot : p = ⊥ := by
      have hmin := Ideal.height_eq_zero_iff (I := p) |>.mp (by exact_mod_cast hn)
      rw [IsDomain.minimalPrimes_eq_singleton_bot] at hmin
      simpa using hmin
    subst hbot
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A)]
    simp
  | succ n ih =>
    intro p hp hn
    -- a chain of primes of length `n + 1` ending at `p`
    have hht : Order.height (⟨p, hp⟩ : PrimeSpectrum A) = ((n + 1 : ℕ) : ℕ∞) := by
      rw [← PrimeSpectrum.height_eq_orderHeight]
      exact_mod_cast hn
    obtain ⟨l, hlast, hlen⟩ := Order.exists_series_of_height_eq_coe _ hht
    have hlne : l.length ≠ 0 := by omega
    set x : PrimeSpectrum A := l.eraseLast.last with hxdef
    have hxlt : x < (⟨p, hp⟩ : PrimeSpectrum A) := by
      have hrel := l.eraseLast_last_rel_last hlne
      rwa [hlast] at hrel
    have hxlen : l.eraseLast.length = n := by
      rw [RelSeries.eraseLast_length, hlen]
      omega
    have hxge : ((n : ℕ) : ℕ∞) ≤ Order.height x := by
      have hle := Order.length_le_height_last (p := l.eraseLast)
      rwa [hxlen] at hle
    have hxle : Order.height x ≤ ((n : ℕ) : ℕ∞) := by
      have h0 : Order.height x + 1 ≤ ((n + 1 : ℕ) : ℕ∞) := by
        rw [← hht]
        exact Order.height_add_one_le hxlt
      have h1 : Order.height x + 1 ≤ ((n : ℕ) : ℕ∞) + 1 := by
        refine le_trans h0 (le_of_eq ?_)
        push_cast
        ring
      exact (ENat.add_le_add_iff_right (by simp)).mp h1
    have hxh : Order.height x = ((n : ℕ) : ℕ∞) := le_antisymm hxle hxge
    -- `q` is the ideal of `x`
    set q : Ideal A := x.asIdeal with hqdef
    have hqprime : q.IsPrime := x.isPrime
    have hqp : q < p := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hxlt
      exact hxlt
    -- no prime lies strictly between `q` and `p`
    have hsat : ∀ r : Ideal A, r.IsPrime → q ≤ r → r < p → r = q := by
      intro r hr hqr hrp
      by_contra hne
      have hqr' : (x : PrimeSpectrum A) < (⟨r, hr⟩ : PrimeSpectrum A) := by
        rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
        exact lt_of_le_of_ne hqr (Ne.symm hne)
      have hrp' : (⟨r, hr⟩ : PrimeSpectrum A) < (⟨p, hp⟩ : PrimeSpectrum A) := by
        rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
        exact hrp
      have h4 : ((n + 2 : ℕ) : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) := by
        calc ((n + 2 : ℕ) : ℕ∞) = ((n : ℕ) : ℕ∞) + 1 + 1 := by push_cast; ring
          _ ≤ Order.height (⟨r, hr⟩ : PrimeSpectrum A) + 1 := by
              refine add_le_add ?_ le_rfl
              rw [← hxh]
              exact Order.height_add_one_le hqr'
          _ ≤ ((n + 1 : ℕ) : ℕ∞) := by
              rw [← hht]
              exact Order.height_add_one_le hrp'
      have h5 : n + 2 ≤ n + 1 := by exact_mod_cast h4
      omega
    -- pass to the quotient by `q`
    have hqdomain : IsDomain (A ⧸ q) := Ideal.Quotient.isDomain_iff_prime q |>.mpr hqprime
    have hqft : Algebra.FiniteType k (A ⧸ q) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k q) Ideal.Quotient.mk_surjective
    have hmono : StrictMono (PrimeSpectrum.comap (Ideal.Quotient.mk q)) :=
      RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
    have hbotcomap : (⊥ : Ideal (A ⧸ q)).comap (Ideal.Quotient.mk q) = q := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    set P : Ideal (A ⧸ q) := p.map (Ideal.Quotient.mk q) with hPdef
    have hPprime : P.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp.le
    have hPcomap : P.comap (Ideal.Quotient.mk q) = p := by
      rw [hPdef, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hqp.le]
    have hcomapP : PrimeSpectrum.comap (Ideal.Quotient.mk q) (⟨P, hPprime⟩ : PrimeSpectrum (A ⧸ q))
        = (⟨p, hp⟩ : PrimeSpectrum A) := PrimeSpectrum.ext hPcomap
    -- every prime strictly below `P` is zero
    have hbelow : ∀ y : PrimeSpectrum (A ⧸ q),
        y < (⟨P, hPprime⟩ : PrimeSpectrum (A ⧸ q)) → y = ⊥ := by
      intro y hy
      have hylt : PrimeSpectrum.comap (Ideal.Quotient.mk q) y < (⟨p, hp⟩ : PrimeSpectrum A) := by
        rw [← hcomapP]
        exact hmono hy
      have hyq : q ≤ Ideal.comap (Ideal.Quotient.mk q) y.asIdeal := by
        intro z hz
        change Ideal.Quotient.mk q z ∈ y.asIdeal
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz]
        exact y.asIdeal.zero_mem
      have hyeq : Ideal.comap (Ideal.Quotient.mk q) y.asIdeal = q := by
        refine hsat _ (PrimeSpectrum.comap (Ideal.Quotient.mk q) y).isPrime hyq ?_
        rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hylt
        exact hylt
      apply PrimeSpectrum.ext
      refine Ideal.comap_injective_of_surjective (Ideal.Quotient.mk q)
        Ideal.Quotient.mk_surjective ?_
      rw [hyeq, show ((⊥ : PrimeSpectrum (A ⧸ q)).asIdeal) = ⊥ from rfl, hbotcomap]
    -- the image of `p` has height one
    have hPne : P ≠ ⊥ := by
      intro h0
      rw [h0, hbotcomap] at hPcomap
      exact hqp.ne hPcomap
    have hPge : (1 : ℕ∞) ≤ P.height := by
      by_cases h0 : P.height = 0
      · exfalso
        have hmin := Ideal.height_eq_zero_iff (I := P) |>.mp h0
        rw [IsDomain.minimalPrimes_eq_singleton_bot] at hmin
        exact hPne (by simpa using hmin)
      · exact Order.one_le_iff_ne_zero.mpr h0
    have hPle : P.height ≤ 1 := by
      rw [PrimeSpectrum.height_eq_orderHeight (⟨P, hPprime⟩ : PrimeSpectrum (A ⧸ q)),
        Order.height_eq_iSup_lt_height]
      refine iSup_le fun y ↦ iSup_le fun hy ↦ ?_
      rw [hbelow y hy]
      simp
    have hPh : P.height = 1 := le_antisymm hPle hPge
    -- the two quotients agree
    have hker : RingHom.ker ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk q)) = p := by
      ext z
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap,
        hPcomap]
    have hsurj : Function.Surjective ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk q)) :=
      Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
    have hequiv : ringKrullDim (A ⧸ p) = ringKrullDim ((A ⧸ q) ⧸ P) :=
      ringKrullDim_eq_of_ringEquiv
        ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj))
    -- assemble
    have hstep2 := ringKrullDim_quotient_succ_eq_of_height_eq_one k (A ⧸ q) P hPh
    have hqh : q.height = ((n : ℕ) : ℕ∞) := by
      rw [hqdef, PrimeSpectrum.height_eq_orderHeight]
      exact hxh
    have hIH := ih q hqprime hqh
    have hcast : (((n + 1 : ℕ)) : WithBot ℕ∞) = ((n : ℕ) : WithBot ℕ∞) + 1 := by
      push_cast
      ring
    rw [hequiv, hcast, add_comm (((n : ℕ)) : WithBot ℕ∞) 1, ← add_assoc, hstep2, hIH]

/-- **The dimension formula.**  For a field `k`, a finitely generated `k`-algebra `A` which is a
domain, and a prime `p` of `A`, `dim (A ⧸ p) + ht p = dim A`. -/
theorem ringKrullDim_quotient_add_height (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (p : Ideal A) [hp : p.IsPrime] :
    ringKrullDim (A ⧸ p) + ((p.height : ℕ∞) : WithBot ℕ∞) = ringKrullDim A := by
  have hnoeth : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨n, hn⟩ : ∃ n : ℕ, p.height = (n : ℕ∞) := by
    have hlt := Ideal.height_lt_top (I := p) hp.ne_top
    exact ⟨p.height.toNat, by rw [ENat.natCast_toNat hlt.ne]⟩
  rw [hn]
  exact_mod_cast ringKrullDim_quotient_add_height_aux k A n p hp hn

end General

/-! ### Consequences for the affine normal cone -/

section NormalCone

open GromovWitten.AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The dimension formula, packaged as the predicate `HasDimensionFormula` used as a hypothesis
in `GromovWitten/AlgebraicGeometry/Cones/NormalConeDimension.lean`. -/
theorem hasDimensionFormula (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] : HasDimensionFormula A :=
  fun p hp ↦ ringKrullDim_quotient_add_height (hp := hp) k A p

variable {R : Type u} [CommRing R] (I : Ideal R) [Algebra k R]

/-- The extended Rees algebra of an ideal of a finitely generated domain over a field satisfies
the dimension formula. -/
theorem hasDimensionFormula_extendedRees [IsDomain R] [IsNoetherianRing R]
    [Algebra.FiniteType k R] :
    HasDimensionFormula (AffineDeformationSpace.extendedRees R I) :=
  have : Algebra.FiniteType k (AffineDeformationSpace.extendedRees R I) :=
    Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  hasDimensionFormula k _

/-- **Purity of the affine normal cone, unconditional form.**  Every minimal prime `q` of
`gr_I(R)` satisfies `dim (gr_I(R) ⧸ q) = dim R`. -/
theorem ringKrullDim_quotient_eq_of_mem_minimalPrimes' [IsDomain R] [IsNoetherianRing R]
    [Algebra.FiniteType k R] (hI : I ≠ ⊤) (n : ℕ) (hn : ringKrullDim R = (n : ℕ∞))
    {q : Ideal (AffineNormalCone.associatedGradedRing R I)}
    (hq : q ∈ minimalPrimes (AffineNormalCone.associatedGradedRing R I)) :
    ringKrullDim (AffineNormalCone.associatedGradedRing R I ⧸ q) = (n : ℕ∞) :=
  AffineDeformationSpace.ringKrullDim_quotient_eq_of_mem_minimalPrimes R I k hI n hn
    (hasDimensionFormula_extendedRees k I) hq

/-- **Unconditional form.**  The affine normal cone of a proper ideal of an `n`-dimensional
finitely generated domain over a field has Krull dimension exactly `n`. -/
theorem ringKrullDim_associatedGradedRing' [IsDomain R] [IsNoetherianRing R]
    [Algebra.FiniteType k R] (hI : I ≠ ⊤) (n : ℕ) (hn : ringKrullDim R = (n : ℕ∞)) :
    ringKrullDim (AffineNormalCone.associatedGradedRing R I) = (n : ℕ∞) :=
  AffineDeformationSpace.ringKrullDim_associatedGradedRing R I k hI n hn
    (hasDimensionFormula_extendedRees k I)

/-- **Purity of the affine normal cone, scheme form, unconditional.**  Every irreducible
component of `Spec (gr_I R)` has dimension `dim R`.  This is the affine algebraic form of
Fulton, *Intersection Theory*, B.6.6. -/
theorem pureTopologicalDimension_normalCone' [IsDomain R] [IsNoetherianRing R]
    [Algebra.FiniteType k R] (hI : I ≠ ⊤) (n : ℕ) (hn : ringKrullDim R = (n : ℕ∞)) :
    Curves.PureTopologicalDimension n (AffineNormalCone.scheme R I) :=
  AffineDeformationSpace.pureTopologicalDimension_normalCone R I k hI n hn
    (hasDimensionFormula_extendedRees k I)

end NormalCone

end GromovWitten.Algebra
