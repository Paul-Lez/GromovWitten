/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalOrdSymmetry
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.Data.ENat.BigOperators

/-!
# The order of a nonzerodivisor on a reduced one-dimensional local ring

Let `B` be a Noetherian reduced ring of Krull dimension at most `1` (formalised as
`[Ring.KrullDimLE 1 B]`; the blueprint's setting of a local ring of Krull dimension exactly `1`
is the main case of interest, but the argument below never uses locality), and let `g : B` avoid
every minimal prime of `B`. We show that the order of vanishing `Ring.ord B g` decomposes as the
sum, over the (finitely many) minimal primes `q` of `B`, of the order of vanishing of the image
of `g` in the quotient domain `B ⧸ q`. This is Stacks, Chow Homology, the algebraic input used to
compute how a point-generator divisor behaves on a reducible curve, and the key
commutative-algebra fact for Task S2 of the Vistoli-relations round.

The proof goes through dévissage (`LocalOrdSymmetry.devissage`): both sides of the desired
identity are special values of the Fulton-style identity for the pair of multiplicity functions
`chiCoker g`, `chiKer g`, evaluated at `B` itself. The weights `lengthAt q B` occurring in
dévissage are shown to be `1` because a reduced ring localised at a minimal prime is a field.

## Main results

* `GromovWitten.Algebra.reducedOrd_eq_sum_minimalPrimes`: the order-of-vanishing identity
  `Ring.ord B g = ∑ q ∈ (minimalPrimes B).toFinset, Ring.ord (B ⧸ q) (Ideal.Quotient.mk q g)`
  in `ℕ∞`.
* `GromovWitten.Algebra.reducedOrd_toNat_eq_sum_minimalPrimes`: the same identity with every
  term converted to `ℕ` via `ENat.toNat` (all the terms involved are finite).
-/

namespace GromovWitten.Algebra

open GromovWitten.AlgebraicGeometry.IntersectionTheory
open LocalOrdSymmetry

variable {B : Type*} [CommRing B] [IsNoetherianRing B] [IsReduced B] [Ring.KrullDimLE 1 B]

omit [IsNoetherianRing B] [Ring.KrullDimLE 1 B] in
/-- A reduced ring localised at a minimal prime is a field: the radical of the image of `⊥` is
the image of the minimal prime `q` (`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`),
which is the maximal ideal of the localisation; since the localisation is still reduced, this
radical is `⊥`, so the maximal ideal is `⊥` and the local ring is a field. -/
private theorem isField_localization_atPrime_of_mem_minimalPrimes {q : Ideal B}
    [hqp : q.IsPrime] (hq : q ∈ minimalPrimes B) : IsField (Localization.AtPrime q) := by
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (Localization.AtPrime q) q (⊥ : Ideal B) hq
  rw [Ideal.map_bot, Localization.AtPrime.map_eq_maximalIdeal] at hrad
  have hred : IsReduced (Localization.AtPrime q) := inferInstance
  have hradbot : (⊥ : Ideal (Localization.AtPrime q)).radical = ⊥ := by
    ext x
    simp only [Ideal.mem_radical_iff, Submodule.mem_bot]
    exact ⟨fun ⟨n, hn⟩ ↦ IsReduced.eq_zero x ⟨n, hn⟩, fun hx ↦ ⟨1, by simp [hx]⟩⟩
  have hbot : IsLocalRing.maximalIdeal (Localization.AtPrime q) = ⊥ := by
    rw [← hrad, hradbot]
  exact (IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot

omit [IsNoetherianRing B] [Ring.KrullDimLE 1 B] in
/-- The localisation of `B` itself at a minimal prime `q` has length `1` as a module over
itself: it is a field, hence a simple module over itself. -/
private theorem lengthAt_self_eq_one_of_mem_minimalPrimes {q : Ideal B}
    (hq : q ∈ minimalPrimes B) [hqp : q.IsPrime] :
    LocalOrdSymmetry.lengthAt q B = 1 := by
  have hfield := isField_localization_atPrime_of_mem_minimalPrimes hq
  set A := Localization.AtPrime q
  have hsimple : IsSimpleModule A A := isSimpleModule_self_iff_isUnit.2
    ⟨nontrivial_iff.mpr hfield.exists_pair_ne, fun x hx ↦ by
      obtain ⟨y, hy⟩ := hfield.mul_inv_cancel hx
      exact IsUnit.of_mul_eq_one y hy⟩
  have e : (B ⧸ (⊥ : Ideal B)) ≃ₗ[B] B := Submodule.quotEquivOfEqBot (⊥ : Ideal B) rfl
  calc LocalOrdSymmetry.lengthAt q B = LocalOrdSymmetry.lengthAt q (B ⧸ (⊥ : Ideal B)) :=
        (LocalOrdSymmetry.lengthAt_congr q e).symm
    _ = Module.length A (A ⧸ (⊥ : Ideal B).map (algebraMap B A)) :=
        LocalOrdSymmetry.lengthAt_quotient q (⊥ : Ideal B)
    _ = Module.length A (A ⧸ (⊥ : Ideal A)) := by rw [Ideal.map_bot]
    _ = Module.length A A :=
        LinearEquiv.length_eq (Submodule.quotEquivOfEqBot (⊥ : Ideal A) rfl)
    _ = 1 := Module.length_eq_one A A

omit [IsNoetherianRing B] [Ring.KrullDimLE 1 B] in
/-- A nonzerodivisor on `B` avoids every minimal prime of `B`: if `g` avoided no minimal prime
but `x * g = 0` for some `x ≠ 0`, then (since `B` is reduced) `x ∉ ⋂ q`, so `x` is nonzero modulo
some minimal prime `q`; cancelling in the domain `B ⧸ q` forces `g ∈ q`, a contradiction. -/
private theorem mem_nonZeroDivisors_of_forall_notMem_minimalPrimes {g : B}
    (hg : ∀ q ∈ minimalPrimes B, g ∉ q) : g ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  by_contra hx0
  have hmem : ∀ q ∈ minimalPrimes B, x ∈ q := by
    intro q hq
    by_contra hxq
    have hqp : q.IsPrime := hq.isPrime
    have hxne : Ideal.Quotient.mk q x ≠ 0 := fun h ↦ hxq (Ideal.Quotient.eq_zero_iff_mem.1 h)
    have hgq : Ideal.Quotient.mk q g = 0 := by
      have hxg : Ideal.Quotient.mk q x * Ideal.Quotient.mk q g = 0 := by
        rw [← map_mul, hx, map_zero]
      rcases mul_eq_zero.1 hxg with h | h
      · exact absurd h hxne
      · exact h
    exact hg q hq (Ideal.Quotient.eq_zero_iff_mem.1 hgq)
  have hxbot : x ∈ sInf (minimalPrimes B) := Submodule.mem_sInf.2 hmem
  rw [Ideal.sInf_minimalPrimes, Ideal.mem_radical_iff] at hxbot
  obtain ⟨n, hn⟩ := hxbot
  rw [Submodule.mem_bot] at hn
  exact hx0 (IsReduced.eq_zero x ⟨n, hn⟩)

/-- **Main theorem (Blueprint S1).** Let `B` be a Noetherian reduced ring with
`[Ring.KrullDimLE 1 B]` (in particular a Noetherian local reduced ring of Krull dimension `1`,
the setting of the blueprint) and let `g : B` avoid every minimal prime of `B` (equivalently,
since `B` is reduced, a nonzerodivisor). Then the order of vanishing of `g` on `B` is the sum,
over the (finitely many) minimal primes `q` of `B`, of the order of vanishing of the image of
`g` in the quotient domain `B ⧸ q`. -/
theorem reducedOrd_eq_sum_minimalPrimes (g : B) (hg : ∀ q ∈ minimalPrimes B, g ∉ q) :
    Ring.ord B g
      = ∑ q ∈ (minimalPrimes.finite_of_isNoetherianRing B).toFinset,
          Ring.ord (B ⧸ q) (Ideal.Quotient.mk q g) := by
  classical
  have hg' : g ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_forall_notMem_minimalPrimes hg
  have hfin : (minimalPrimes B).Finite := minimalPrimes.finite_of_isNoetherianRing B
  -- the finite set of primes of `B` that are minimal, as a `Finset (PrimeSpectrum B)`
  have hfinPS : {p : PrimeSpectrum B | p.asIdeal ∈ minimalPrimes B}.Finite :=
    hfin.preimage (Set.injOn_of_injective fun p q h ↦ PrimeSpectrum.ext h)
  set T := hfinPS.toFinset
  have hTmin : ∀ q : PrimeSpectrum B, q.asIdeal ∈ (⊥ : Ideal B).minimalPrimes → q ∈ T :=
    fun q hq ↦ hfinPS.mem_toFinset.2 hq
  have hTmem : ∀ q ∈ T, q.asIdeal ∈ (⊥ : Ideal B).minimalPrimes :=
    fun q hq ↦ hfinPS.mem_toFinset.1 hq
  have hdim : ∀ q : Ideal B, q.IsPrime → (⊥ : Ideal B) ≤ q →
      q ∈ (⊥ : Ideal B).minimalPrimes ∨ q.IsMaximal :=
    fun q hqp _ ↦ Ring.krullDimLE_one_iff.1 ‹Ring.KrullDimLE 1 B› q hqp
  have hartFL : IsFiniteLength B (B ⧸ Ideal.span {g}) :=
    isFiniteLength_quotient_span_singleton B hg'
  have hart : IsArtinian B (B ⧸ ((⊥ : Ideal B) ⊔ Ideal.span {g})) := by
    rw [bot_sup_eq]
    exact (isFiniteLength_iff_isNoetherian_isArtinian.1 hartFL).2
  have hdev := LocalOrdSymmetry.devissage g (⊥ : Ideal B) hart T hTmin hTmem hdim
    (⊥ : Ideal B) le_rfl
  -- simplify both sides of the dévissage identity
  have ebot : (B ⧸ (⊥ : Ideal B)) ≃ₗ[B] B := Submodule.quotEquivOfEqBot (⊥ : Ideal B) rfl
  have hcoker : LocalOrdSymmetry.chiCoker g (B ⧸ (⊥ : Ideal B)) = Ring.ord B g := by
    rw [LocalOrdSymmetry.chiCoker_congr g ebot, LocalOrdSymmetry.chiCoker_self B g]
  have hker : LocalOrdSymmetry.chiKer g (B ⧸ (⊥ : Ideal B)) = 0 := by
    rw [LocalOrdSymmetry.chiKer_congr g ebot]
    have hkerbot : LinearMap.ker (LinearMap.lsmul B B g) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro m hm
      rw [LinearMap.lsmul_apply] at hm
      exact (mem_nonZeroDivisors_iff_left.1 hg' m) hm
    change Module.length B (LinearMap.ker (LinearMap.lsmul B B g)) = 0
    rw [hkerbot, Module.length_bot]
  have hweight : ∀ q ∈ T, LocalOrdSymmetry.lengthAt q.asIdeal (B ⧸ (⊥ : Ideal B)) = 1 := by
    intro q hq
    have hqmin : q.asIdeal ∈ minimalPrimes B := hTmem q hq
    have : LocalOrdSymmetry.lengthAt q.asIdeal B = 1 :=
      lengthAt_self_eq_one_of_mem_minimalPrimes hqmin
    rwa [LocalOrdSymmetry.lengthAt_congr q.asIdeal ebot]
  have hkerq : ∀ q ∈ T, LocalOrdSymmetry.chiKer g (B ⧸ q.asIdeal) = 0 := by
    intro q hq
    exact LocalOrdSymmetry.chiKer_quotient_prime_eq_zero q.asIdeal (hg q.asIdeal (hTmem q hq))
  have hcokerq : ∀ q ∈ T, LocalOrdSymmetry.chiCoker g (B ⧸ q.asIdeal)
      = Ring.ord (B ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal g) :=
    fun q _ ↦ LocalOrdSymmetry.chiCoker_quotient_ord g q.asIdeal
  have hsum1 : ∑ q ∈ T, LocalOrdSymmetry.lengthAt q.asIdeal (B ⧸ (⊥ : Ideal B))
      * LocalOrdSymmetry.chiKer g (B ⧸ q.asIdeal) = 0 := by
    refine Finset.sum_eq_zero fun q hq ↦ ?_
    rw [hweight q hq, one_mul, hkerq q hq]
  have hsum2 : ∑ q ∈ T, LocalOrdSymmetry.lengthAt q.asIdeal (B ⧸ (⊥ : Ideal B))
      * LocalOrdSymmetry.chiCoker g (B ⧸ q.asIdeal)
      = ∑ q ∈ T, Ring.ord (B ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal g) := by
    refine Finset.sum_congr rfl fun q hq ↦ ?_
    rw [hweight q hq, one_mul, hcokerq q hq]
  rw [hcoker, hker, hsum1, hsum2] at hdev
  rw [add_zero, zero_add] at hdev
  -- reindex the sum over `T` as a sum over the minimal primes of `B` as ideals
  have hinj : Function.Injective (PrimeSpectrum.asIdeal (R := B)) := fun p q h ↦ PrimeSpectrum.ext h
  have himg : T.image PrimeSpectrum.asIdeal = hfin.toFinset := by
    ext q
    simp only [Finset.mem_image, hfin.mem_toFinset]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hTmem p hp
    · intro hq
      exact ⟨⟨q, hq.isPrime⟩, hTmin ⟨q, hq.isPrime⟩ hq, rfl⟩
  rw [hdev, ← himg, Finset.sum_image (Set.injOn_of_injective hinj)]

/-- The `ℕ`-valued (`ENat.toNat`) version of `reducedOrd_eq_sum_minimalPrimes`: all the orders of
vanishing involved are finite (`Ring.ord_ne_top`), so the identity transports to `ℕ`. -/
theorem reducedOrd_toNat_eq_sum_minimalPrimes (g : B) (hg : ∀ q ∈ minimalPrimes B, g ∉ q) :
    (Ring.ord B g).toNat
      = ∑ q ∈ (minimalPrimes.finite_of_isNoetherianRing B).toFinset,
          (Ring.ord (B ⧸ q) (Ideal.Quotient.mk q g)).toNat := by
  have heq := reducedOrd_eq_sum_minimalPrimes g hg
  have hterm : ∀ q ∈ (minimalPrimes.finite_of_isNoetherianRing B).toFinset,
      Ring.ord (B ⧸ q) (Ideal.Quotient.mk q g) ≠ ⊤ := by
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    have hqp : q.IsPrime := hq.isPrime
    have hgq : Ideal.Quotient.mk q g ≠ 0 := fun h ↦
      hg q hq (Ideal.Quotient.eq_zero_iff_mem.1 h)
    have hqd : Ring.KrullDimLE 1 (B ⧸ q) := by
      rw [Ring.krullDimLE_iff]
      exact (ringKrullDim_quotient_le q).trans (Ring.krullDimLE_iff.1 ‹Ring.KrullDimLE 1 B›)
    have hqNoeth : IsNoetherianRing (B ⧸ q) := inferInstance
    exact Ring.ord_ne_top ((mem_nonZeroDivisors_iff_ne_zero).2 hgq)
  rw [heq, ENat.toNat_sum hterm]

end GromovWitten.Algebra
