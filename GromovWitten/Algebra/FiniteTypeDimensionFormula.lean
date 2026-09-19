/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.Algebra.FiniteTypeKrullDimension
import GromovWitten.Algebra.DimensionFormula
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyInjective
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# The dimension formula for finite type algebras over a field, given the height one case

For a field `k`, a finitely generated `k`-algebra `A` which is a domain and a prime `p` of `A`,
the *dimension formula* is

`ringKrullDim (A ⧸ p) + p.height = ringKrullDim A`.

This file proves the formula by induction on the height, taking the height one case as an
explicit hypothesis

`hG1 : ∀ (B : Type u) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
  (q : Ideal B) [q.IsPrime], q.height = 1 → ringKrullDim (B ⧸ q) + 1 = ringKrullDim B`

(the hypothesis is stated for *all* finitely generated `k`-domains, because the induction applies
it to the quotients `A ⧸ q` and not only to `A` itself).

## Main results

* `height_add_ringKrullDim_quotient_le` — the trivial inequality
  `ringKrullDim (A ⧸ p) + p.height ≤ ringKrullDim A`, valid in every commutative ring.
* `height_map_quotient_add_one_le` — for a Noetherian domain `A` and primes `⊥ ≠ p₁ ≤ p`, the
  image of `p` in `A ⧸ p₁` has height at most `p.height - 1`.
* `ringKrullDim_quotient_add_height_of_hG1`, `hasDimensionFormula_of_finiteType_of_hG1` — the
  dimension formula for a finitely generated `k`-domain, granted `hG1`.
* `hasUniversalDimensionFormula_of_finiteType_of_hG1` — the universal form used by the
  intersection theory files: every prime quotient of every finitely generated polynomial algebra
  over a finitely generated `k`-algebra `R` satisfies the dimension formula.

The hypothesis `hG1` is the only thing missing here; it is proved separately (Noether
normalisation together with the fact that a polynomial ring over a field is a unique
factorisation domain).

Note that an unconditional proof of the same statements is already available in
`GromovWitten/Algebra/DimensionFormula.lean` (`ringKrullDim_quotient_add_height`,
`hasDimensionFormula`); the present file is the conditional repackaging with `hG1` isolated.
-/

namespace GromovWitten.Algebra.FiniteTypeDimensionFormula

open GromovWitten.AlgebraicGeometry

universe u

/-! ### The trivial inequality -/

/-- The Krull dimension of `A ⧸ p` plus the height of `p` is at most the Krull dimension of `A`:
a chain of primes below `p` concatenates with a chain of primes above `p`. -/
theorem height_add_ringKrullDim_quotient_le (A : Type u) [CommRing A] (p : Ideal A)
    [hp : p.IsPrime] :
    ringKrullDim (A ⧸ p) + ((p.height : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim A := by
  have key : ∀ x : PrimeSpectrum A,
      ringKrullDim (A ⧸ x.asIdeal) + ((x.asIdeal.height : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim A := by
    intro x
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
  exact key ⟨p, hp⟩

/-! ### The key inequality for the quotient by a height one prime -/

/-- The image of a prime `p` under the quotient map by a prime `p₁ ≤ p` is prime.  This is
`Ideal.isPrime_map_quotientMk_of_isPrime`, restated for convenience. -/
theorem isPrime_map_quotient_mk {A : Type u} [CommRing A] {p₁ p : Ideal A} [p.IsPrime]
    (hle : p₁ ≤ p) : (p.map (Ideal.Quotient.mk p₁)).IsPrime :=
  Ideal.isPrime_map_quotientMk_of_isPrime hle

/-- Every prime of `A` contracted from `A ⧸ p₁` contains `p₁`. -/
theorem le_comap_asIdeal {A : Type u} [CommRing A] (p₁ : Ideal A)
    (y : PrimeSpectrum (A ⧸ p₁)) :
    p₁ ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk p₁) y).asIdeal := by
  intro z hz
  change Ideal.Quotient.mk p₁ z ∈ y.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz]
  exact y.asIdeal.zero_mem

/-- **The key inequality.**  If `A` is a Noetherian domain and `⊥ ≠ p₁ ≤ p` are primes, then the
height of the image of `p` in `A ⧸ p₁` is at least one less than the height of `p`: a chain
of primes of `A ⧸ p₁` ending at that image pulls back to a chain of primes of `A` ending at `p`
all of whose members contain `p₁`, and the zero ideal can be prepended to it. -/
theorem height_map_quotient_add_one_le (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    {p₁ p : Ideal A} [p₁.IsPrime] [hp : p.IsPrime] (h₁ : p₁ ≠ ⊥) (hle : p₁ ≤ p) :
    (p.map (Ideal.Quotient.mk p₁)).height + 1 ≤ p.height := by
  have hP : (p.map (Ideal.Quotient.mk p₁)).IsPrime := isPrime_map_quotient_mk hle
  have hPcomap : (p.map (Ideal.Quotient.mk p₁)).comap (Ideal.Quotient.mk p₁) = p := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hle]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (p.map (Ideal.Quotient.mk p₁)).height = (n : ℕ∞) :=
    ⟨(p.map (Ideal.Quotient.mk p₁)).height.toNat,
      by rw [ENat.natCast_toNat (Ideal.height_lt_top hP.ne_top).ne]⟩
  have hPh : Order.height (⟨p.map (Ideal.Quotient.mk p₁), hP⟩ : PrimeSpectrum (A ⧸ p₁))
      = (n : ℕ∞) := by
    rw [← PrimeSpectrum.height_eq_orderHeight]
    exact hn
  obtain ⟨l, hlast, hlen⟩ := Order.exists_series_of_height_eq_coe _ hPh
  have hmono : StrictMono (PrimeSpectrum.comap (Ideal.Quotient.mk p₁)) :=
    RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  have hbotlt : (⊥ : PrimeSpectrum A)
      < (l.map (PrimeSpectrum.comap (Ideal.Quotient.mk p₁)) hmono).head := by
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    have hb : ((⊥ : PrimeSpectrum A).asIdeal) = ⊥ := rfl
    rw [hb, LTSeries.head_map]
    exact lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr h₁) (le_comap_asIdeal p₁ l.head)
  have hlast' : ((l.map (PrimeSpectrum.comap (Ideal.Quotient.mk p₁)) hmono).cons ⊥ hbotlt).last
      = (⟨p, hp⟩ : PrimeSpectrum A) := by
    rw [RelSeries.last_cons, LTSeries.last_map, hlast]
    exact PrimeSpectrum.ext hPcomap
  have hlen' : ((l.map (PrimeSpectrum.comap (Ideal.Quotient.mk p₁)) hmono).cons ⊥ hbotlt).length
      = n + 1 := by
    rw [RelSeries.cons_length]
    change l.length + 1 = n + 1
    rw [hlen]
  have hchain := Order.length_le_height_last
    (p := (l.map (PrimeSpectrum.comap (Ideal.Quotient.mk p₁)) hmono).cons ⊥ hbotlt)
  rw [hlast', hlen'] at hchain
  have hgoal : Order.height (⟨p, hp⟩ : PrimeSpectrum A) = p.height := by
    rw [← PrimeSpectrum.height_eq_orderHeight]
  rw [hn, ← hgoal]
  exact_mod_cast hchain

/-! ### The induction on the height -/

variable (k : Type u) [Field k]

/-- Auxiliary induction on the height: for a finitely generated `k`-algebra `A` which is a domain
and a prime `p` of height `n`, `dim (A ⧸ p) + n = dim A`, granted the height one case `hG1`.

The induction step uses a chain of primes of length `n + 1` ending at `p`.  Its next-to-last term
`q` has height exactly `n`, and no prime lies strictly between `q` and `p`, so the image of `p` in
the finitely generated `k`-domain `A ⧸ q` has height one and `hG1` applies. -/
theorem ringKrullDim_quotient_add_height_aux_of_hG1 (A : Type u) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (hG1 : ∀ (B : Type u) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
      (q : Ideal B) [q.IsPrime], q.height = 1 → ringKrullDim (B ⧸ q) + 1 = ringKrullDim B) :
    ∀ (n : ℕ) (p : Ideal A) (_ : p.IsPrime), p.height = (n : ℕ∞) →
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
    have hPprime : P.IsPrime := isPrime_map_quotient_mk hqp.le
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
      have hyeq : Ideal.comap (Ideal.Quotient.mk q) y.asIdeal = q := by
        refine hsat _ (PrimeSpectrum.comap (Ideal.Quotient.mk q) y).isPrime
          (le_comap_asIdeal q y) ?_
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
    have hstep2 := hG1 (A ⧸ q) P hPh
    have hqh : q.height = ((n : ℕ) : ℕ∞) := by
      rw [hqdef, PrimeSpectrum.height_eq_orderHeight]
      exact hxh
    have hIH := ih q hqprime hqh
    have hcast : (((n + 1 : ℕ)) : WithBot ℕ∞) = ((n : ℕ) : WithBot ℕ∞) + 1 := by
      push_cast
      ring
    rw [hequiv, hcast, add_comm (((n : ℕ)) : WithBot ℕ∞) 1, ← add_assoc, hstep2, hIH]

/-- **The dimension formula**, granted the height one case `hG1`.  For a field `k`, a finitely
generated `k`-algebra `A` which is a domain and a prime `p` of `A`,
`dim (A ⧸ p) + ht p = dim A`. -/
theorem ringKrullDim_quotient_add_height_of_hG1 (A : Type u) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (hG1 : ∀ (B : Type u) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
      (q : Ideal B) [q.IsPrime], q.height = 1 → ringKrullDim (B ⧸ q) + 1 = ringKrullDim B)
    (p : Ideal A) [hp : p.IsPrime] :
    ringKrullDim (A ⧸ p) + ((p.height : ℕ∞) : WithBot ℕ∞) = ringKrullDim A := by
  have hnoeth : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨n, hn⟩ : ∃ n : ℕ, p.height = (n : ℕ∞) := by
    have hlt := Ideal.height_lt_top (I := p) hp.ne_top
    exact ⟨p.height.toNat, by rw [ENat.natCast_toNat hlt.ne]⟩
  rw [hn]
  exact_mod_cast ringKrullDim_quotient_add_height_aux_of_hG1 k A hG1 n p hp hn

/-- The dimension formula for a finitely generated `k`-domain, packaged as the predicate
`GromovWitten.AlgebraicGeometry.HasDimensionFormula`, granted the height one case `hG1`. -/
theorem hasDimensionFormula_of_finiteType_of_hG1 (A : Type u) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (hG1 : ∀ (B : Type u) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
      (q : Ideal B) [q.IsPrime], q.height = 1 → ringKrullDim (B ⧸ q) + 1 = ringKrullDim B) :
    HasDimensionFormula A :=
  fun p hp ↦ ringKrullDim_quotient_add_height_of_hG1 (hp := hp) k A hG1 p

/-- The **universal dimension formula** for a finitely generated `k`-algebra `R` (not necessarily
a domain), granted the height one case `hG1`: every prime quotient of every finitely generated
polynomial algebra over `R` is a finitely generated `k`-domain, so it satisfies the dimension
formula. -/
theorem hasUniversalDimensionFormula_of_finiteType_of_hG1 (R : Type u) [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R]
    (hG1 : ∀ (B : Type u) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
      (q : Ideal B) [q.IsPrime], q.height = 1 → ringKrullDim (B ⧸ q) + 1 = ringKrullDim B) :
    IntersectionTheory.VectorBundle.HasUniversalDimensionFormula R := by
  intro ι _ P hP
  have hPprime : P.IsPrime := hP
  have hdom : IsDomain (MvPolynomial ι R ⧸ P) :=
    Ideal.Quotient.isDomain_iff_prime P |>.mpr hPprime
  have hft : Algebra.FiniteType k (MvPolynomial ι R ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P) Ideal.Quotient.mk_surjective
  exact hasDimensionFormula_of_finiteType_of_hG1 k (MvPolynomial ι R ⧸ P) hG1

/-- The dimension formula holds universally over every finitely generated algebra `R` over a
field `k`: every prime quotient of every finitely generated polynomial algebra over `R` satisfies
`dim (A ⧸ p) + ht p = dim A`.  The height-one input is
`GromovWitten.Algebra.ringKrullDim_quotient_succ_eq_of_height_eq_one`. -/
theorem hasUniversalDimensionFormula_of_finiteType (R : Type u) [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] :
    IntersectionTheory.VectorBundle.HasUniversalDimensionFormula R :=
  hasUniversalDimensionFormula_of_finiteType_of_hG1 k R fun B _ _ _ _ q _ hq ↦
    GromovWitten.Algebra.ringKrullDim_quotient_succ_eq_of_height_eq_one k B q hq

end GromovWitten.Algebra.FiniteTypeDimensionFormula
