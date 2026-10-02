/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.Algebra.Herbrand
import GromovWitten.Algebra.TameFactorization
import GromovWitten.Algebra.TameGluing
import GromovWitten.Algebra.NormOrder
import GromovWitten.Algebra.TameSymbol

/-!
# The key lemma for tame symbols (Stacks 42.6)

Let `A` be a two-dimensional Noetherian local domain with fraction field `K` and unit
differences (`VectorBundle.UnitDifferences A`). For a height-one prime `q` of `A` and
`f, g ∈ Kˣ`, `tameOrd A K hU q f g ∈ ℤ` is the order, for the one-dimensional local domain
`A ⧸ q` on its fraction field `κ(q)`, of the tame symbol `∂_{A_q}(f, g) ∈ κ(q)ˣ` of
`A_q = Localization.AtPrime q` (see `GromovWitten/Algebra/TameSymbol.lean`). The key lemma
(Stacks, Lemma 42.6.3) says that `∑_q ord_{A/q}(∂_{A_q}(f, g)) = 0`.

The proof follows Stacks 42.6.2:
* bimultiplicativity (T3) reduces to `f = a`, `g = b` with `a, b ∈ A` nonzero;
* admissible overrings of the `A_q` for `q ∋ a b` (TameFactorization) are glued to a local
  subalgebra `B ⊆ K` finite over `A` with the same residue field (TameGluing);
* the norm-down formula (T5), invariance (T6) and the order of norms (NormOrder) give
  `ord_{A/q} ∂_{A_q} = ∑_{Q | q} ord_{B/Q} ∂_{B_Q}`, which replaces `A` by `B`;
* in `B` the pair factors at every height-one prime `Q ∋ a b`; there
  `ord_{B/Q} ∂_{B_Q}(a, b) = -e(M_Q, a, b)` for the Herbrand quotient of the image `M_Q` of
  `B ⧸ (a b)` in `B_Q ⧸ (a b)` (realised as `B ⧸ satIdeal Q (a b)`), computed with Stacks
  42.3.1, 42.3.3 and 42.3.4 (Herbrand), including the rescaling by elements outside `Q`;
* the map `B ⧸ (a b) → ∏_Q M_Q` has kernel and cokernel of finite length, so
  `∑_Q e(M_Q, a, b) = e(B ⧸ (a b), a, b) = 0`.

## Main results

* `GromovWitten.Algebra.Tame.tameOrd`: `ord_{A/q}(∂_{A_q}(f, g))`.
* `GromovWitten.Algebra.Tame.finsum_tameOrd_eq_zero`: **the key lemma** (Stacks 42.6.3).
* `GromovWitten.Algebra.Tame.finite_support_tameOrd`, `support_tameOrd_subset`: the sum is
  finite, supported on the height-one primes where `f` or `g` is not a unit of `A_q`
  (`IsUnitAtPrime`, `isUnitAtPrime_iff`).
* `GromovWitten.Algebra.Tame.tameOrd_mul_left`, `tameOrd_mul_right`, `tameOrd_inv_left`,
  `tameOrd_inv_right`: additivity in each argument.
* `GromovWitten.Algebra.Tame.finsum_tameOrd_eq_zero_of_ne_zero`: the case `f, g ∈ A`
  (Stacks 42.6.2).
* `GromovWitten.Algebra.Tame.herbrand_satComplex`: the Herbrand computation
  `e(M_q, a, b) = m · (e (ord v₀ - ord s₂) - f (ord u₀ - ord s₁))` from `s₁ a = u₀ π₀^e`,
  `s₂ b = v₀ π₀^f`.
* `GromovWitten.Algebra.Tame.finsum_herbrand_satComplex`: `∑_q e(M_q, a, b) = 0`.
* `GromovWitten.Algebra.Tame.tameOrd_eq_of_data`,
  `finsum_tameOrd_eq_zero_of_data`: the key lemma when the pair factors at all relevant primes.
* `GromovWitten.Algebra.Tame.tameOrd_eq_finsum_fiber`: the norm-down step `A → B`.
* `GromovWitten.Algebra.Tame.exists_glued_factorization`: construction of `B`.
-/

namespace GromovWitten.Algebra.Tame

open IsLocalRing GromovWitten.Algebra.PeriodicComplex
open GromovWitten.AlgebraicGeometry.IntersectionTheory LocalOrdSymmetry

section Saturation

variable {A : Type*} [CommRing A]

/-- The `q`-saturation of the principal ideal `(t)`: the elements `r` with `t ∣ s * r` for some
`s ∉ q`. It is the kernel of `A → A_q ⧸ (t)`. -/
def satIdeal (q : Ideal A) [hq : q.IsPrime] (t : A) : Ideal A where
  carrier := {r | ∃ s ∉ q, t ∣ s * r}
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨s', hs', hy⟩
    refine ⟨s * s', hq.mul_notMem hs hs', ?_⟩
    have : s * s' * (x + y) = s' * (s * x) + s * (s' * y) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right hy _)
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simp⟩
  smul_mem' := by
    rintro c x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_eq_mul, mul_left_comm]
    exact dvd_mul_of_dvd_right hx _

variable (q : Ideal A) [hq : q.IsPrime]

/-- Membership in the saturation. -/
theorem mem_satIdeal {t r : A} : r ∈ satIdeal q t ↔ ∃ s ∉ q, t ∣ s * r := Iff.rfl

/-- `t ∈ satIdeal q t`. -/
theorem self_mem_satIdeal (t : A) : t ∈ satIdeal q t :=
  ⟨1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simp⟩

/-- The saturation is `q`-saturated: `s r ∈ satIdeal q t` with `s ∉ q` implies
`r ∈ satIdeal q t`. -/
theorem mem_satIdeal_of_mul_mem {t r s : A} (hs : s ∉ q) (h : s * r ∈ satIdeal q t) :
    r ∈ satIdeal q t := by
  obtain ⟨s', hs', h⟩ := h
  exact ⟨s' * s, hq.mul_notMem hs' hs, by rwa [mul_assoc]⟩

/-- The saturation only depends on `t` up to factors outside `q`: `s t = w t'` with `s, w ∉ q`
implies `satIdeal q t = satIdeal q t'`. -/
theorem satIdeal_eq_of_mul {t t' s w : A} (hs : s ∉ q) (hw : w ∉ q) (h : s * t = w * t') :
    satIdeal q t = satIdeal q t' := by
  ext r
  constructor
  · rintro ⟨s', hs', hd⟩
    refine ⟨s * s', hq.mul_notMem hs hs', ?_⟩
    have : t' ∣ w * t' := dvd_mul_left _ _
    rw [← h] at this
    exact this.trans (by rw [mul_assoc]; exact mul_dvd_mul_left s hd)
  · rintro ⟨s', hs', hd⟩
    refine ⟨w * s', hq.mul_notMem hw hs', ?_⟩
    have : t ∣ s * t := dvd_mul_left _ _
    rw [h] at this
    exact this.trans (by rw [mul_assoc]; exact mul_dvd_mul_left w hd)

/-- In a domain, if `s₀ t = w₀ x y` with `s₀, w₀ ∉ q` and `x ≠ 0`, then `x r ∈ satIdeal q t` iff
`r ∈ satIdeal q y`. -/
theorem mul_mem_satIdeal_iff [IsDomain A] {t x y s₀ w₀ r : A} (hs₀ : s₀ ∉ q) (hw₀ : w₀ ∉ q)
    (hxy : s₀ * t = w₀ * (x * y)) (hx : x ≠ 0) :
    x * r ∈ satIdeal q t ↔ r ∈ satIdeal q y := by
  rw [satIdeal_eq_of_mul q hs₀ hw₀ hxy]
  constructor
  · rintro ⟨s, hs, hd⟩
    refine ⟨s, hs, ?_⟩
    rwa [mul_left_comm, mul_dvd_mul_iff_left hx] at hd
  · rintro ⟨s, hs, hd⟩
    refine ⟨s, hs, ?_⟩
    rw [mul_left_comm]
    exact mul_dvd_mul_left x hd

end Saturation

section Dim

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]

omit [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] in
/-- The localization at a height-one prime has dimension `≤ 1`. -/
theorem krullDimLE_one_localization_of_height_eq_one {q : Ideal A} [q.IsPrime] (hq : q.height = 1) :
    Ring.KrullDimLE 1 (Localization.AtPrime q) := by
  rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
  rfl

omit [IsDomain A] [IsNoetherianRing A] in
/-- A height-one prime of a two-dimensional local ring is not maximal. -/
private theorem not_isMaximal_of_height_eq_one (hdim : ringKrullDim A = 2) {q : Ideal A} [q.IsPrime]
    (hq : q.height = 1) : ¬ q.IsMaximal := by
  intro h
  have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [← IsLocalRing.eq_maximalIdeal h, hq, hdim] at this
  exact absurd (WithBot.coe_eq_coe.mp this) (by decide)

variable (hdim : ringKrullDim A = 2) {q : Ideal A} [hq : q.IsPrime] (hq1 : q.height = 1)
include hdim hq1

omit [IsNoetherianRing A] in
/-- Every prime containing the saturation `satIdeal q y` (`y ≠ 0`) is `q` or the maximal
ideal. -/
theorem eq_of_satIdeal_le {y : A} (hy : y ≠ 0) (P : Ideal A) [hP : P.IsPrime]
    (hle : satIdeal q y ≤ P) : P = q ∨ P = maximalIdeal A := by
  by_contra hne
  push Not at hne
  have hyP : y ∈ P := hle (self_mem_satIdeal q y)
  have hP0 : P ≠ ⊥ := fun h ↦ hy (by simpa [h] using hyP)
  have hP1 := height_eq_one_of_ne_bot_of_ne_maximalIdeal hdim hP0 hne.2
  have hqP : ¬ q ≤ P := fun h ↦ hne.1
    (eq_of_le_of_height_eq_one_of_ne_bot hP1 h (Ideal.ne_bot_of_height_eq_one hq1)).symm
  obtain ⟨z, hzq, hzP⟩ := SetLike.not_le_iff_exists.1 hqP
  have _ := krullDimLE_one_localization_of_height_eq_one hq1
  have hz : algebraMap A (Localization.AtPrime q) z ∈ maximalIdeal (Localization.AtPrime q) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ q]
    exact hzq
  have hy' : algebraMap A (Localization.AtPrime q) y ≠ 0 := by
    rwa [ne_eq, IsLocalization.to_map_eq_zero_iff (Localization.AtPrime q)
      q.primeCompl_le_nonZeroDivisors]
  obtain ⟨N, hN⟩ := exists_pow_mem_span_of_mem_maximalIdeal hz hy'
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hN
  obtain ⟨⟨c₀, s⟩, hcs⟩ := IsLocalization.surj q.primeCompl c
  have hmem : z ^ N ∈ satIdeal q y := by
    refine ⟨s, s.2, ⟨c₀, ?_⟩⟩
    apply IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors
    simp only [map_mul, map_pow] at hcs ⊢
    rw [← hc, ← hcs]
    ring
  exact hzP (hP.mem_of_pow_mem N (hle hmem))

omit [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] hdim hq1 in
/-- The saturation localizes to the principal ideal. -/
theorem map_satIdeal (y : A) :
    (satIdeal q y).map (algebraMap A (Localization.AtPrime q)) =
      Ideal.span {algebraMap A (Localization.AtPrime q) y} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro r ⟨s, hs, c, hc⟩
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    have hu : IsUnit (algebraMap A (Localization.AtPrime q) s) :=
      IsLocalization.map_units (Localization.AtPrime q) (⟨s, hs⟩ : q.primeCompl)
    refine ⟨hu.unit⁻¹ * algebraMap A _ c, ?_⟩
    have : algebraMap A (Localization.AtPrime q) s * algebraMap A _ r =
        algebraMap A (Localization.AtPrime q) y * algebraMap A _ c := by
      rw [← map_mul, ← map_mul, hc]
    calc _ = hu.unit⁻¹ * (algebraMap A (Localization.AtPrime q) y * algebraMap A _ c) := by ring
      _ = _ := by rw [← this, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ (self_mem_satIdeal q y)

omit [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] hdim hq1 in
/-- The `q`-local length of `A ⧸ satIdeal q y` is the order of `y` in `A_q`. -/
theorem lengthAt_satIdeal (y : A) :
    lengthAt q (A ⧸ satIdeal q y) =
      Ring.ord (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) y) := by
  rw [lengthAt_quotient, map_satIdeal]
  rfl

/-- A finite module killed by `satIdeal q y` (`y ≠ 0`) whose elements are each killed by some
element outside `q` has finite length. -/
theorem length_ne_top_of_satIdeal {y : A} (hy : y ≠ 0) {N : Type*} [AddCommGroup N]
    [Module A N] [Module.Finite A N] (hJ : ∀ r ∈ satIdeal q y, ∀ n : N, r • n = 0)
    (hN : ∀ n : N, ∃ s ∉ q, s • n = 0) : Module.length A N ≠ ⊤ := by
  apply length_ne_top_of_support
  intro p hp
  by_contra hpm
  by_cases hpq : p.asIdeal = q
  · exact (Module.notMem_support_iff'.2 (by rw [hpq]; exact hN)) hp
  · have hle : ¬ satIdeal q y ≤ p.asIdeal := fun h ↦
      (eq_of_satIdeal_le hdim hq1 hy p.asIdeal h).elim hpq hpm
    obtain ⟨r, hr, hrp⟩ := SetLike.not_le_iff_exists.1 hle
    exact (Module.notMem_support_iff'.2 fun n ↦ ⟨r, hrp, hJ r hr n⟩) hp

end Dim

section Complex

variable {A : Type*} [CommRing A]

/-- The periodic complex `(M, a, b)` (multiplication by `a` and by `b`) for scalars `a, b` with
`(a * b) • M = 0`. -/
def scalComplex (M : Type*) [AddCommGroup M] [Module A M] (a b : A)
    (h : ∀ m : M, (a * b) • m = 0) : PeriodicComplex A M where
  φ := LinearMap.lsmul A M a
  ψ := LinearMap.lsmul A M b
  φ_ψ m := by
    change a • b • m = 0
    rw [smul_smul, h]
  ψ_φ m := by
    change b • a • m = 0
    rw [smul_smul, mul_comm, h]

/-- An element of an ideal `J` kills the module `A ⧸ J`. -/
private theorem smul_quotient_eq_zero_of_mem {J : Ideal A} {c : A} (hc : c ∈ J) (x : A ⧸ J) :
    c • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H r =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact J.mul_mem_right r hc

/-- The range of multiplication by `x` on `A ⧸ J` is isomorphic to `A ⧸ I` for
`I = {r | x * r ∈ J}`. -/
noncomputable def rangeLsmulEquiv (J : Ideal A) (x : A) (I : Ideal A)
    (hI : ∀ r, r ∈ I ↔ x * r ∈ J) :
    (A ⧸ I) ≃ₗ[A] LinearMap.range (LinearMap.lsmul A (A ⧸ J) x) :=
  (Submodule.quotEquivOfEq I (LinearMap.ker ((LinearMap.lsmul A (A ⧸ J) x) ∘ₗ J.mkQ)) (by
      ext r
      rw [hI, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.lsmul_apply,
        Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        smul_eq_mul])).trans
    ((LinearMap.quotKerEquivRange _).trans (LinearEquiv.ofEq _ _
      (LinearMap.range_comp_of_range_eq_top _ (Submodule.range_mkQ J))))

end Complex

section Core

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  (hdim : ringKrullDim A = 2) {q : Ideal A} [hq : q.IsPrime] (hq1 : q.height = 1)
include hdim hq1

/-- On `A ⧸ satIdeal q t` with `s₀ t = w₀ x y` (`s₀, w₀ ∉ q`, `x ≠ 0`), the module
`ker x ⧸ (im y ∩ ker x)` has finite length. -/
theorem length_ker_quot_range_ne_top {t x y s₀ w₀ : A} (ht : t ≠ 0) (hs₀ : s₀ ∉ q)
    (hw₀ : w₀ ∉ q) (hxy : s₀ * t = w₀ * (x * y)) (hx : x ≠ 0) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ satIdeal q t) x) ⧸
      (LinearMap.range (LinearMap.lsmul A (A ⧸ satIdeal q t) y)).comap
        (LinearMap.ker (LinearMap.lsmul A (A ⧸ satIdeal q t) x)).subtype) ≠ ⊤ := by
  apply length_ne_top_of_satIdeal hdim hq1 ht
  · intro r hr n
    induction n using Submodule.Quotient.induction_on with
    | H m =>
      have h0 : r • m = 0 := Subtype.ext (by
        rw [Submodule.coe_smul, ZeroMemClass.coe_zero]
        exact smul_quotient_eq_zero_of_mem hr _)
      rw [← Submodule.Quotient.mk_smul, h0, Submodule.Quotient.mk_zero]
  · intro n
    induction n using Submodule.Quotient.induction_on with
    | H m =>
      obtain ⟨m, hm⟩ := m
      induction m using Submodule.Quotient.induction_on with
      | H z =>
        have hz : x * z ∈ satIdeal q t := by
          rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul,
            Submodule.Quotient.mk_eq_zero, smul_eq_mul] at hm
          exact hm
        obtain ⟨s, hs, c, hc⟩ := (mul_mem_satIdeal_iff q hs₀ hw₀ hxy hx).1 hz
        refine ⟨s, hs, ?_⟩
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
        refine ⟨Submodule.Quotient.mk c, ?_⟩
        rw [LinearMap.lsmul_apply, Submodule.subtype_apply, Submodule.coe_smul,
          ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, smul_eq_mul,
          hc]

/-- On `A ⧸ satIdeal q t` (`t ≠ 0`), multiplication by `c ∉ q` has a finite-length cokernel. -/
theorem chiCoker_satIdeal_ne_top {t c : A} (ht : t ≠ 0) (hc : c ∉ q) :
    chiCoker c (A ⧸ satIdeal q t) ≠ ⊤ := by
  apply length_ne_top_of_satIdeal hdim hq1 ht
  · intro r hr n
    induction n using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, smul_quotient_eq_zero_of_mem hr, Submodule.Quotient.mk_zero]
  · intro n
    induction n using Submodule.Quotient.induction_on with
    | H m =>
      exact ⟨c, hc, by
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact ⟨m, rfl⟩⟩

/-- Stacks 42.3.1 on the range of multiplication by `x` on `A ⧸ satIdeal q t`, where
`s₀ t = w₀ x y`: `e(x (A ⧸ satIdeal q t), 0, c) = ord_{A/q}(c) · ord_{A_q}(y)` for `c ∉ q`. -/
theorem herbrand_smulComplex_range {t x y s₀ w₀ c : A} (hs₀ : s₀ ∉ q)
    (hw₀ : w₀ ∉ q) (hxy : s₀ * t = w₀ * (x * y)) (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ∉ q) :
    (smulComplex (LinearMap.range (LinearMap.lsmul A (A ⧸ satIdeal q t) x)) c).FiniteCohomology ∧
    (smulComplex (LinearMap.range (LinearMap.lsmul A (A ⧸ satIdeal q t) x)) c).herbrand =
      ((Ring.ord (A ⧸ q) (Ideal.Quotient.mk q c)).toNat *
        (Ring.ord (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) y)).toNat :
          ℕ) := by
  have e := rangeLsmulEquiv (satIdeal q t) x (satIdeal q y)
    (fun r ↦ (mul_mem_satIdeal_iff q hs₀ hw₀ hxy hx).symm)
  obtain ⟨h1, h2⟩ := herbrand_smulComplex_quotient q (not_isMaximal_of_height_eq_one hdim hq1)
    (satIdeal q y)
    (fun P _ hP ↦ eq_of_satIdeal_le hdim hq1 hy P hP) c hc
  rw [lengthAt_satIdeal] at h2
  exact ⟨(finiteCohomology_smulComplex_congr e c).1 h1,
    by rw [← herbrand_smulComplex_congr e c, h2]⟩

omit [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] hdim hq1 in
/-- Orders in `A_q` of elements of `A` related by `s * x = u * y` with `s, u ∉ q`. -/
private theorem ord_localization_eq_of_mul {x y s u : A} (hs : s ∉ q) (hu : u ∉ q)
    (h : s * x = u * y) :
    Ring.ord (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) x) =
      Ring.ord (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) y) := by
  have hs' : IsUnit (algebraMap A (Localization.AtPrime q) s) :=
    IsLocalization.map_units _ (⟨s, hs⟩ : q.primeCompl)
  have hu' : IsUnit (algebraMap A (Localization.AtPrime q) u) :=
    IsLocalization.map_units _ (⟨u, hu⟩ : q.primeCompl)
  rw [← Ring.ord_mul_of_isUnit_left hs' (algebraMap A _ x),
    ← Ring.ord_mul_of_isUnit_left hu' (algebraMap A _ y), ← map_mul, ← map_mul, h]

omit [IsNoetherianRing A] [IsLocalRing A] hdim hq1 in
/-- The order in `A_q` of a power. -/
private theorem ord_localization_pow {x : A} (hx : x ≠ 0) (n : ℕ) :
    (Ring.ord (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) (x ^ n))).toNat =
      n * (Ring.ord (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) x)).toNat := by
  have hx' : algebraMap A (Localization.AtPrime q) x ∈ nonZeroDivisors (Localization.AtPrime q) :=
    mem_nonZeroDivisors_of_ne_zero (by
      rwa [ne_eq, IsLocalization.to_map_eq_zero_iff (Localization.AtPrime q)
        q.primeCompl_le_nonZeroDivisors])
  rw [map_pow, Ring.ord_pow hx', nsmul_eq_mul, ENat.toNat_mul, ENat.toNat_natCast]

omit [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] hdim hq1 in
/-- `(a * b) • (A ⧸ satIdeal q (a * b)) = 0`. -/
theorem smul_satIdeal_eq_zero (a b : A) (m : A ⧸ satIdeal q (a * b)) : (a * b) • m = 0 :=
  smul_quotient_eq_zero_of_mem (self_mem_satIdeal q _) m

omit [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] hdim hq1 in
variable (q) in
/-- The periodic complex `(M, a, b)` for `M` the image of `A` in `A_q ⧸ (a b)`, i.e.
`M = A ⧸ satIdeal q (a * b)` (Stacks 42.6.2). -/
def satComplex (a b : A) : PeriodicComplex A (A ⧸ satIdeal q (a * b)) :=
  scalComplex _ a b (smul_satIdeal_eq_zero a b)

/-- The complex `(A ⧸ satIdeal q (a b), a, b)` has finite cohomology (`a, b ≠ 0`). -/
theorem finiteCohomology_satComplex {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) :
    (satComplex q a b).FiniteCohomology := by
  have h1q : (1 : A) ∉ q := (Ideal.ne_top_iff_one q).1 hq.ne_top
  exact ⟨length_ker_quot_range_ne_top hdim hq1 (mul_ne_zero ha hb) h1q h1q
      (by ring : 1 * (a * b) = 1 * (a * b)) ha,
    length_ker_quot_range_ne_top hdim hq1 (mul_ne_zero ha hb) h1q h1q
      (by ring : 1 * (a * b) = 1 * (b * a)) hb⟩

/-- **Herbrand core of Stacks 42.6.2.** Let `A` be a two-dimensional Noetherian local domain,
`q` a height-one prime, `a, b ≠ 0`, and suppose `s₁ a = u₀ π₀^e`, `s₂ b = v₀ π₀^f` in `A` with
`s₁, s₂, u₀, v₀ ∉ q` and `π₀ ≠ 0`. Then the complex `(A ⧸ satIdeal q (a b), a, b)` has finite
cohomology and multiplicity
`m · (e (ord(v₀) - ord(s₂)) - f (ord(u₀) - ord(s₁)))`, where `m = ord_{A_q}(π₀)` and the other
orders are those of `A ⧸ q`. -/
theorem herbrand_satComplex {a b π₀ u₀ v₀ s₁ s₂ : A} {e f : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hπ₀ : π₀ ≠ 0) (hs₁ : s₁ ∉ q) (hs₂ : s₂ ∉ q) (hu₀ : u₀ ∉ q) (hv₀ : v₀ ∉ q)
    (h₁ : s₁ * a = u₀ * π₀ ^ e) (h₂ : s₂ * b = v₀ * π₀ ^ f) :
    (satComplex q a b).FiniteCohomology ∧
    (satComplex q a b).herbrand =
      ((Ring.ord (Localization.AtPrime q) (algebraMap A _ π₀)).toNat : ℤ) *
        (e * (((Ring.ord (A ⧸ q) (Ideal.Quotient.mk q v₀)).toNat : ℤ) -
            (Ring.ord (A ⧸ q) (Ideal.Quotient.mk q s₂)).toNat) -
          f * (((Ring.ord (A ⧸ q) (Ideal.Quotient.mk q u₀)).toNat : ℤ) -
            (Ring.ord (A ⧸ q) (Ideal.Quotient.mk q s₁)).toNat)) := by
  set M := A ⧸ satIdeal q (a * b)
  set X := satComplex q a b
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have h1q : (1 : A) ∉ q := (Ideal.ne_top_iff_one q).1 hq.ne_top
  have hsq : s₁ * s₂ ∉ q := hq.mul_notMem hs₁ hs₂
  have huv : u₀ * v₀ ∉ q := hq.mul_notMem hu₀ hv₀
  have hrel : (s₁ * s₂) * (a * b) = (u₀ * v₀) * (π₀ ^ e * π₀ ^ f) := by
    rw [show (s₁ * s₂) * (a * b) = (s₁ * a) * (s₂ * b) by ring, h₁, h₂]
    ring
  have hXf : X.FiniteCohomology := finiteCohomology_satComplex hdim hq1 ha hb
  -- rescaling by `s₁`, `s₂` (Stacks 42.3.4)
  obtain ⟨hX1f, -, hX1⟩ := herbrand_smulLeft X hXf s₁ (chiCoker_satIdeal_ne_top hdim hq1 hab hs₁)
  obtain ⟨-, -, hX2⟩ :=
    herbrand_smulRight (X.smulLeft s₁) hX1f s₂ (chiCoker_satIdeal_ne_top hdim hq1 hab hs₂)
  -- the nilpotent complex `(M, π₀^e, π₀^f)` (Stacks 42.3.3)
  have hmem : π₀ ^ (e + f) ∈ satIdeal q (a * b) :=
    ⟨u₀ * v₀, huv, ⟨s₁ * s₂, by rw [pow_add, ← hrel]; ring⟩⟩
  have hpow : (LinearMap.lsmul A M π₀) ^ (e + f) = 0 := by
    rw [lsmul_pow_eq]
    exact LinearMap.ext fun m ↦ smul_quotient_eq_zero_of_mem hmem m
  have hfin : Module.length A (LinearMap.ker (LinearMap.lsmul A M π₀) ⧸
      (LinearMap.range (LinearMap.lsmul A M π₀ ^ (e + f - 1))).comap
        (LinearMap.ker (LinearMap.lsmul A M π₀)).subtype) ≠ ⊤ := by
    rcases Nat.eq_zero_or_pos (e + f) with h0 | hpos
    · have htop : satIdeal q (a * b) = ⊤ := by
        rw [satIdeal_eq_of_mul q hsq huv (t' := 1) (by rw [hrel, ← pow_add, h0]; ring),
          Ideal.eq_top_iff_one]
        exact self_mem_satIdeal q 1
      have : Subsingleton M := Ideal.Quotient.subsingleton_iff.2 htop
      rw [Module.length_eq_zero]
      exact ENat.zero_ne_top
    · rw [lsmul_pow_eq]
      refine length_ker_quot_range_ne_top hdim hq1 hab hsq huv ?_ hπ₀
      rw [hrel, ← pow_add, ← pow_succ', Nat.sub_add_cancel hpos]
  set C0 := powComplex' (LinearMap.lsmul A M π₀) e f hpow
  obtain ⟨hC0f, hC0⟩ := herbrand_powComplex' (LinearMap.lsmul A M π₀) e f hpow hfin
  obtain ⟨hC1f, -, hC1⟩ :=
    herbrand_smulRight C0 hC0f v₀ (chiCoker_satIdeal_ne_top hdim hq1 hab hv₀)
  obtain ⟨-, -, hC2⟩ :=
    herbrand_smulLeft (C0.smulRight v₀) hC1f u₀ (chiCoker_satIdeal_ne_top hdim hq1 hab hu₀)
  -- the two rescaled complexes coincide
  have hEq : ((X.smulLeft s₁).smulRight s₂).herbrand =
      ((C0.smulRight v₀).smulLeft u₀).herbrand := by
    refine herbrand_congr (LinearEquiv.refl A M) (fun m ↦ ?_) (fun m ↦ ?_)
    · change s₁ • a • m = u₀ • ((LinearMap.lsmul A M π₀ ^ e) m)
      rw [lsmul_pow_eq, LinearMap.lsmul_apply, smul_smul, smul_smul, h₁]
    · change s₂ • b • m = v₀ • ((LinearMap.lsmul A M π₀ ^ f) m)
      rw [lsmul_pow_eq, LinearMap.lsmul_apply, smul_smul, smul_smul, h₂]
  -- the four correction terms (Stacks 42.3.1)
  rw [show LinearMap.range X.φ = LinearMap.range (LinearMap.lsmul A M a) from rfl,
    (herbrand_smulComplex_range hdim hq1 h1q h1q (by ring : 1 * (a * b) = 1 * (a * b)) ha hb
      hs₁).2] at hX1
  rw [show LinearMap.range (X.smulLeft s₁).ψ = LinearMap.range (LinearMap.lsmul A M b) from rfl,
    (herbrand_smulComplex_range hdim hq1 h1q h1q (by ring : 1 * (a * b) = 1 * (b * a)) hb ha
      hs₂).2] at hX2
  rw [herbrand_smulComplex_submodule_congr
      (show LinearMap.range C0.ψ = LinearMap.range (LinearMap.lsmul A M (π₀ ^ f)) by
        rw [← lsmul_pow_eq]; rfl) v₀,
    (herbrand_smulComplex_range hdim hq1 hsq huv (by rw [hrel]; ring :
      (s₁ * s₂) * (a * b) = (u₀ * v₀) * (π₀ ^ f * π₀ ^ e)) (pow_ne_zero _ hπ₀)
      (pow_ne_zero _ hπ₀) hv₀).2, hC0] at hC1
  rw [herbrand_smulComplex_submodule_congr
      (show LinearMap.range (C0.smulRight v₀).φ = LinearMap.range (LinearMap.lsmul A M (π₀ ^ e)) by
        rw [← lsmul_pow_eq]; rfl) u₀,
    (herbrand_smulComplex_range hdim hq1 hsq huv hrel (pow_ne_zero _ hπ₀)
      (pow_ne_zero _ hπ₀) hu₀).2] at hC2
  refine ⟨hXf, ?_⟩
  rw [ord_localization_eq_of_mul hs₁ hu₀ h₁, ord_localization_pow hπ₀] at hX2
  rw [ord_localization_eq_of_mul hs₂ hv₀ h₂, ord_localization_pow hπ₀] at hX1
  rw [ord_localization_pow hπ₀] at hC1 hC2
  push_cast at hX1 hX2 hC1 hC2
  linear_combination -hX1 - hX2 + hEq + hC2 + hC1

end Core

section Sum

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]

/-- The height-one primes of `A` containing `t`. -/
abbrev HeightOneOver (A : Type*) [CommRing A] (t : A) : Type _ :=
  {q : PrimeSpectrum A // q.asIdeal.height = 1 ∧ t ∈ q.asIdeal}

omit [IsLocalRing A] in
/-- `HeightOneOver A t` is finite for `t ≠ 0`. -/
theorem finite_heightOneOver {t : A} (ht : t ≠ 0) : Finite (HeightOneOver A t) :=
  (finite_setOf_height_eq_one_mem ht).to_subtype

variable (hdim : ringKrullDim A = 2)
include hdim

omit [IsNoetherianRing A] in
/-- A non-maximal prime containing `t ≠ 0` is a height-one prime containing `a * b`. -/
theorem height_eq_one_of_mem_of_ne_maximalIdeal {t : A} (ht : t ≠ 0) (p : Ideal A) [p.IsPrime]
    (htp : t ∈ p)
    (hpm : p ≠ maximalIdeal A) : p.height = 1 :=
  height_eq_one_of_ne_bot_of_ne_maximalIdeal hdim (fun h ↦ ht (by simpa [h] using htp)) hpm

/-- **Stacks 42.6.2, the sum.** For `a, b ≠ 0` in a two-dimensional Noetherian local domain,
`∑_q e(A ⧸ satIdeal q (a b), a, b) = 0`, the sum running over the (finitely many) height-one
primes `q` containing `a b`. -/
theorem finsum_herbrand_satComplex {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ᶠ q : HeightOneOver A (a * b), (satComplex q.1.asIdeal a b).herbrand = 0 := by
  classical
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have _ := finite_heightOneOver hab
  have _ : Fintype (HeightOneOver A (a * b)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  -- the exact complex `(A ⧸ (a b), a, b)`
  set Y := scalComplex (A ⧸ Ideal.span {a * b}) a b
    (fun m ↦ smul_quotient_eq_zero_of_mem (Ideal.mem_span_singleton_self _) m)
  have hexact : ∀ x y : A, x ≠ 0 → x * y = a * b →
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) x) ≤
        LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) y) := by
    intro x y hx hxy m hm
    induction m using Submodule.Quotient.induction_on with
    | H z =>
      rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, smul_eq_mul, ← hxy, Ideal.mem_span_singleton'] at hm
      obtain ⟨c, hc⟩ := hm
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      rw [LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul]
      congr 1
      apply mul_left_cancel₀ hx
      rw [← hc]
      ring
  obtain ⟨hYf, hY0⟩ := herbrand_eq_zero_of_exact Y (hexact a b ha rfl)
    (hexact b a hb (mul_comm b a))
  -- the comparison map `A ⧸ (a b) → Π_q A ⧸ satIdeal q (a b)`
  set Cs : ∀ i : HeightOneOver A (a * b), PeriodicComplex A (A ⧸ satIdeal i.1.asIdeal (a * b)) :=
    fun i ↦ satComplex i.1.asIdeal a b
  have hle : ∀ i : HeightOneOver A (a * b),
      Ideal.span {a * b} ≤ satIdeal i.1.asIdeal (a * b) := fun i ↦
    (Ideal.span_singleton_le_iff_mem _).2 (self_mem_satIdeal _ _)
  let F : Hom Y (pi Cs) :=
    { f := LinearMap.pi fun i ↦ Submodule.factor (hle i)
      comm_φ := fun m ↦ funext fun i ↦ (Submodule.factor (hle i)).map_smul a m
      comm_ψ := fun m ↦ funext fun i ↦ (Submodule.factor (hle i)).map_smul b m }
  have hker : Module.length A (LinearMap.ker F.f) ≠ ⊤ := by
    apply length_ne_top_of_support
    intro p hp
    by_contra hpm
    apply Module.notMem_support_iff'.2 _ hp
    rintro ⟨x, hx⟩
    by_cases habp : a * b ∈ p.asIdeal
    · have hp1 := height_eq_one_of_mem_of_ne_maximalIdeal hdim hab p.asIdeal habp hpm
      let i₀ : HeightOneOver A (a * b) := ⟨p, hp1, habp⟩
      induction x using Submodule.Quotient.induction_on with
      | H z =>
        have hz := congr_fun (LinearMap.mem_ker.1 hx) i₀
        change Submodule.Quotient.mk z = 0 at hz
        obtain ⟨s, hs, c, hc⟩ := (Submodule.Quotient.mk_eq_zero _).1 hz
        refine ⟨s, hs, Subtype.ext ?_⟩
        rw [Submodule.coe_smul, ZeroMemClass.coe_zero, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.mk_eq_zero, smul_eq_mul, hc]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · exact ⟨a * b, habp, Subtype.ext (by
        rw [Submodule.coe_smul, ZeroMemClass.coe_zero]
        exact smul_quotient_eq_zero_of_mem (Ideal.mem_span_singleton_self _) x)⟩
  have hcoker : Module.length A ((∀ i : HeightOneOver A (a * b), A ⧸ satIdeal i.1.asIdeal (a * b)) ⧸
      LinearMap.range F.f) ≠ ⊤ := by
    apply length_ne_top_of_support
    intro p hp
    by_contra hpm
    apply Module.notMem_support_iff'.2 _ hp
    -- for `j` with `q_j ≠ p`, an element of `satIdeal q_j (a b)` outside `p`
    have hsel : ∀ j : HeightOneOver A (a * b), j.1 ≠ p →
        ∃ r ∈ satIdeal j.1.asIdeal (a * b), r ∉ p.asIdeal := by
      intro j hj
      by_contra hcon
      push Not at hcon
      rcases eq_of_satIdeal_le hdim j.2.1 hab p.asIdeal hcon with h | h
      · exact hj (PrimeSpectrum.ext h.symm)
      · exact hpm h
    choose! r hrJ hrp using hsel
    set s := ∏ j ∈ Finset.univ.filter (fun j : HeightOneOver A (a * b) ↦ j.1 ≠ p), r j
    have hs : s ∉ p.asIdeal := by
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨j, hj, hjp⟩
      exact hrp j (Finset.mem_filter.1 hj).2 hjp
    have hsJ : ∀ j : HeightOneOver A (a * b), j.1 ≠ p →
        s ∈ satIdeal j.1.asIdeal (a * b) := fun j hj ↦
      Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩))
        (hrJ j hj)
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H z =>
      refine ⟨s, hs, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      by_cases hex : ∃ i₀ : HeightOneOver A (a * b), i₀.1 = p
      · obtain ⟨i₀, hi₀⟩ := hex
        obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (z i₀)
        refine ⟨Submodule.Quotient.mk (s * w), funext fun j ↦ ?_⟩
        change Submodule.Quotient.mk (s * w) = s • z j
        by_cases hj : j = i₀
        · subst hj
          rw [← hw, ← Submodule.Quotient.mk_smul, smul_eq_mul]
        · have hjp : j.1 ≠ p := fun h ↦ hj (Subtype.ext (h.trans hi₀.symm))
          rw [smul_quotient_eq_zero_of_mem (hsJ j hjp), (Submodule.Quotient.mk_eq_zero _).2
            (Ideal.mul_mem_right _ _ (hsJ j hjp))]
      · push Not at hex
        refine ⟨0, funext fun j ↦ ?_⟩
        rw [map_zero, Pi.zero_apply, Pi.smul_apply, smul_quotient_eq_zero_of_mem (hsJ j (hex j))]
  have h1 := herbrand_eq_of_hom F hker hcoker hYf
  obtain ⟨-, h2⟩ := herbrand_pi Cs (fun i ↦ finiteCohomology_satComplex hdim i.2.1 ha hb)
  exact h2.symm.trans (h1.symm.trans hY0)

end Sum



section Data

variable {D K : Type*} [CommRing D] [Field K] [Algebra D K] {B : Subalgebra D K}
  {Q : Ideal B} [hQ : Q.IsPrime]

/-- An element of `B` lying in `Q` is not a unit of the localization `B_Q ⊆ K`. -/
private theorem not_isUnit_localizationAt_of_mem {x : B} (hx : x ∈ Q) :
    ¬ IsUnit (⟨(x : K), le_localizationAt B Q x.2⟩ : localizationAt B Q) := by
  rintro ⟨w, hw⟩
  obtain ⟨d, hd, hdw⟩ := (mem_localizationAt B Q).1 (w⁻¹ : (localizationAt B Q)ˣ).1.2
  have hprod : x * ⟨_, hdw⟩ = d := by
    apply Subtype.ext
    have h1 : ((w : localizationAt B Q) : K) * ((w⁻¹ : (localizationAt B Q)ˣ) : K) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    have h2 : ((w : localizationAt B Q) : K) = x := by rw [hw]
    change (x : K) * ((d : K) * _) = d
    rw [← h2, mul_left_comm, h1, mul_one]
  exact hd (hprod ▸ Q.mul_mem_right _ hx)

/-- A numerator `c w ∈ B` (`c ∉ Q`) of a unit `w` of `B_Q ⊆ K` lies outside `Q`. -/
private theorem mul_unit_notMem {w : (localizationAt B Q)ˣ} {c : B} (hc : c ∉ Q)
    (hcw : (c : K) * ((w : localizationAt B Q) : K) ∈ B) : (⟨_, hcw⟩ : B) ∉ Q := by
  intro hmem
  obtain ⟨d, hd, hdw⟩ := (mem_localizationAt B Q).1 (w⁻¹ : (localizationAt B Q)ˣ).1.2
  have h1 : ((w : localizationAt B Q) : K) * ((w⁻¹ : (localizationAt B Q)ˣ) : K) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  have hprod : (⟨_, hcw⟩ : B) * ⟨_, hdw⟩ = c * d := by
    apply Subtype.ext
    change (c : K) * _ * ((d : K) * _) = (c : K) * d
    calc (c : K) * ((w : localizationAt B Q) : K) * ((d : K) * ((w⁻¹ : (localizationAt B Q)ˣ) : K))
        = (c : K) * d * (((w : localizationAt B Q) : K) *
          ((w⁻¹ : (localizationAt B Q)ˣ) : K)) := by ring
      _ = (c : K) * d := by rw [h1, mul_one]
  exact hQ.mul_notMem hc hd (hprod ▸ Q.mul_mem_right _ hmem)

omit hQ in
/-- Coercion to `K` of an integer power of a unit of a subalgebra. -/
private theorem coe_units_zpow_subalgebra {S : Subalgebra D K} (w : Sˣ) (n : ℤ) :
    (((w ^ n : Sˣ) : S) : K) = ((w : S) : K) ^ n := by
  have h := congrArg Units.val (map_zpow (Units.map (S.val : S →* K)) w n)
  rwa [Units.val_zpow_eq_zpow_val] at h

/-- A factorization `x = u π^e`, `y = v π^f` in `B_Q` of two elements of `B` can be taken with
natural-number exponents. -/
theorem exists_nat_factorization {x y : Kˣ} (a b : B) (ha : (a : K) = x) (hb : (b : K) = y)
    (hfac : Factors (localizationAt B Q) ![x, y]) :
    ∃ (π : localizationAt B Q) (e f : ℕ) (u v : (localizationAt B Q)ˣ), (π : K) ≠ 0 ∧
      (a : K) = ((u : localizationAt B Q) : K) * (π : K) ^ e ∧
      (b : K) = ((v : localizationAt B Q) : K) * (π : K) ^ f := by
  obtain ⟨π, n, u, hπ, hfu⟩ := hfac
  have h0 : (a : K) = ((u 0 : localizationAt B Q) : K) * (π : K) ^ n 0 := by
    rw [ha]; exact hfu 0
  have h1 : (b : K) = ((u 1 : localizationAt B Q) : K) * (π : K) ^ n 1 := by
    rw [hb]; exact hfu 1
  by_cases hπu : IsUnit π
  · refine ⟨1, 0, 0, u 0 * hπu.unit ^ n 0, u 1 * hπu.unit ^ n 1, one_ne_zero, ?_, ?_⟩
    · rw [pow_zero, mul_one, Units.val_mul, Subalgebra.coe_mul, coe_units_zpow_subalgebra,
        IsUnit.unit_spec, h0]
    · rw [pow_zero, mul_one, Units.val_mul, Subalgebra.coe_mul, coe_units_zpow_subalgebra,
        IsUnit.unit_spec, h1]
  · have hnonneg : ∀ (c : B) (i : Fin 2),
        (c : K) = ((u i : localizationAt B Q) : K) * (π : K) ^ n i → 0 ≤ n i := by
      intro c i hc
      by_contra hneg
      push Not at hneg
      obtain ⟨m, hm⟩ : ∃ m : ℕ, n i = -((m + 1 : ℕ) : ℤ) := ⟨(-n i - 1).toNat, by omega⟩
      have hK : (c : K) * (π : K) ^ (m + 1) = ((u i : localizationAt B Q) : K) := by
        rw [hc, hm, mul_assoc, ← zpow_natCast, ← zpow_add₀ hπ, neg_add_cancel, zpow_zero,
          mul_one]
      have hL : (⟨(c : K), le_localizationAt B Q c.2⟩ : localizationAt B Q) * π ^ (m + 1) =
          (u i : localizationAt B Q) := Subtype.ext (by
        rw [Subalgebra.coe_mul, Subalgebra.coe_pow]
        exact hK)
      have : IsUnit (π ^ (m + 1)) :=
        isUnit_of_mul_isUnit_right (hL ▸ (u i).isUnit)
      exact hπu ((isUnit_pow_iff (Nat.succ_ne_zero m)).1 this)
    have hn0 := hnonneg a 0 h0
    have hn1 := hnonneg b 1 h1
    refine ⟨π, (n 0).toNat, (n 1).toNat, u 0, u 1, hπ, ?_, ?_⟩
    · rw [h0, ← zpow_natCast, Int.toNat_of_nonneg hn0]
    · rw [h1, ← zpow_natCast, Int.toNat_of_nonneg hn1]

/-- **Clearing denominators.** If two elements `a, b` of `B` factor in `B_Q ⊆ K`, then there are
`π₀, u₀, v₀, s₁, s₂ ∈ B` and `e, f : ℕ` with `π₀ ≠ 0`, `s₁, s₂, u₀, v₀ ∉ Q`, `s₁ a = u₀ π₀^e` and
`s₂ b = v₀ π₀^f` (the input of `herbrand_satComplex`). -/
theorem exists_factor_data {x y : Kˣ} (a b : B) (ha : (a : K) = x) (hb : (b : K) = y)
    (hfac : Factors (localizationAt B Q) ![x, y]) :
    ∃ (π₀ u₀ v₀ s₁ s₂ : B) (e f : ℕ), π₀ ≠ 0 ∧ s₁ ∉ Q ∧ s₂ ∉ Q ∧ u₀ ∉ Q ∧ v₀ ∉ Q ∧
      s₁ * a = u₀ * π₀ ^ e ∧ s₂ * b = v₀ * π₀ ^ f := by
  obtain ⟨π, e, f, u, v, hπ, hau, hbv⟩ := exists_nat_factorization a b ha hb hfac
  obtain ⟨c, hc, hcπ⟩ := (mem_localizationAt B Q).1 π.2
  obtain ⟨c₁, hc₁, hcu⟩ := (mem_localizationAt B Q).1 (u : localizationAt B Q).2
  obtain ⟨c₂, hc₂, hcv⟩ := (mem_localizationAt B Q).1 (v : localizationAt B Q).2
  have hc0 : (c : K) ≠ 0 := fun h ↦ hc (by
    rw [show c = 0 from Subtype.ext h]
    exact Q.zero_mem)
  refine ⟨⟨_, hcπ⟩, ⟨_, hcu⟩, ⟨_, hcv⟩, c₁ * c ^ e, c₂ * c ^ f, e, f, ?_,
    hQ.mul_notMem hc₁ (fun h ↦ hc (hQ.mem_of_pow_mem _ h)),
    hQ.mul_notMem hc₂ (fun h ↦ hc (hQ.mem_of_pow_mem _ h)),
    mul_unit_notMem hc₁ hcu, mul_unit_notMem hc₂ hcv, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    exact mul_ne_zero hc0 hπ this
  · apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
    rw [hau]
    ring
  · apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
    rw [hbv]
    ring

end Data

section Glue

open GromovWitten.AlgebraicGeometry.IntersectionTheory

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

omit [IsLocalRing A] in
/-- The localization `A_q ⊆ K` at a height-one prime is a Noetherian local domain of dimension
`≤ 1` with unit differences (when `A` has them); packaged as the existence of an admissible
overring for any finite family. -/
theorem exists_admissible_locInK (hU : VectorBundle.UnitDifferences A) (q : Ideal A) [q.IsPrime]
    (hq : q.height = 1) {ι : Type*} [Finite ι] (f : ι → Kˣ) :
    ∃ C, Admissible (locInK q.primeCompl (⊥ : Subalgebra A K)) C f := by
  set E := locInK q.primeCompl (⊥ : Subalgebra A K)
  have _ : IsLocalization.AtPrime E q := isLocalization_locInK_bot _ q.primeCompl_le_nonZeroDivisors
  have _ : IsLocalRing E := IsLocalization.AtPrime.isLocalRing E q
  have _ : IsNoetherianRing E := IsLocalization.isNoetherianRing q.primeCompl E inferInstance
  have _ : Ring.KrullDimLE 1 E := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height q E, hq]
    rfl
  have hinj : Function.Injective (algebraMap A E) := fun x y h ↦
    IsFractionRing.injective A K (congrArg Subtype.val h)
  exact exists_admissible E (unitDifferences_of_injective_tame _ hinj hU) f

/-- **Reduction step of Stacks 42.6.2.** For `a, b ≠ 0` in a two-dimensional Noetherian local
domain `A` with unit differences, there is a local subalgebra `B` of `K`, finite over `A`, with
the same residue field, such that `(a, b)` factors in `B_Q` for every height-one prime `Q` of
`B` containing `a b`. -/
theorem exists_glued_factorization (hdim : ringKrullDim A = 2)
    (hU : VectorBundle.UnitDifferences A) {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ (B : Subalgebra A K) (_ : IsLocalRing B) (_ : IsLocalHom (algebraMap A B)),
      Module.Finite A B ∧
      Function.Bijective (ResidueField.map (algebraMap A B)) ∧
      (∀ q : PrimeSpectrum A, q.asIdeal.height = 1 →
        IsOverring (locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K))
          (locInK q.asIdeal.primeCompl B)) ∧
      ∀ (Q : Ideal B) [Q.IsPrime], Q.height = 1 → algebraMap A B (a * b) ∈ Q →
        Factors (localizationAt B Q) ![Units.mk0 (algebraMap A K a)
          ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ha),
          Units.mk0 (algebraMap A K b)
            ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hb)] := by
  set x := Units.mk0 (algebraMap A K a) ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ha)
  set y := Units.mk0 (algebraMap A K b) ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hb)
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hadm : ∀ q : PrimeSpectrum A, ∃ C : Subalgebra A K, q.asIdeal.height = 1 →
      Admissible (locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K)) C ![x, y] := by
    intro q
    by_cases hq1 : q.asIdeal.height = 1
    · obtain ⟨C, hC⟩ := exists_admissible_locInK hU q.asIdeal hq1 ![x, y]
      exact ⟨C, fun _ ↦ hC⟩
    · exact ⟨⊤, fun h ↦ absurd h hq1⟩
  choose C hC using hadm
  set T : Set (PrimeSpectrum A) := {q | q.asIdeal.height = 1 ∧ a * b ∈ q.asIdeal}
  obtain ⟨B, hBloc, hBhom, hBfin, hBres, hBC, hrest⟩ := exists_glued_subalgebra (C := C) hdim hab
    (finite_setOf_height_eq_one_mem hab) (fun q hq ↦ hq.1)
    (fun q hq ↦ (hC q hq.1).isOverring.le) (fun q hq ↦ by
      obtain ⟨G, hG⟩ := (hC q hq.1).isOverring.fg
      exact ⟨G, fun z hz ↦ hG ▸ Submodule.subset_span hz⟩)
  refine ⟨B, hBloc, hBhom, hBfin, hBres, fun q hq1 ↦ ?_, fun Q _ hQ habQ ↦ ?_⟩
  · by_cases hqT : q ∈ T
    · rw [hBC q hqT]
      exact (hC q hq1).isOverring
    · have habq : a * b ∉ q.asIdeal := fun h ↦ hqT ⟨hq1, h⟩
      rw [hrest q hq1 hqT habq]
      exact IsOverring.refl _
  have hq1 := height_comap_eq_one hdim B Q hQ
  set q : PrimeSpectrum A := ⟨Q.comap (algebraMap A B), Ideal.comap_isPrime _ _⟩
  have hqT : q ∈ T := ⟨hq1, habQ⟩
  obtain ⟨ε, hε⟩ := exists_equiv_maximalSpectrum_locInK B q.asIdeal hq1 (C q) (hBC q hqT)
  set P := ε ⟨⟨Q, ‹_›⟩, hQ, rfl⟩
  rw [hε ⟨⟨Q, ‹_›⟩, hQ, rfl⟩]
  exact (hC q hq1).factors P.asIdeal

end Glue

section QuotDim

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsDomain R] [IsNoetherianRing R] in
/-- A quotient of a local ring by a prime ideal is local. -/
private theorem isLocalRing_quotient_prime (P : Ideal R) [hP : P.IsPrime] : IsLocalRing (R ⧸ P) :=
  have := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  .of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective

omit [IsNoetherianRing R] in
/-- In a two-dimensional Noetherian local domain, the quotient by a height-one prime has
dimension `≤ 1`. -/
theorem krullDimLE_one_quotient_of_height_eq_one (hdim : ringKrullDim R = 2) (P : Ideal R)
    [hP : P.IsPrime] (h1 : P.height = 1) : Ring.KrullDimLE 1 (R ⧸ P) := by
  rw [Ring.krullDimLE_one_iff_of_noZeroDivisors]
  intro I hI0 hIp
  set J := I.comap (Ideal.Quotient.mk P)
  have hJp : J.IsPrime := Ideal.comap_isPrime _ _
  have hPJ : P ≤ J := fun x hx ↦ by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact I.zero_mem
  have hIJ : I = J.map (Ideal.Quotient.mk P) :=
    (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective I).symm
  have hPne : P ≠ J := by
    intro h
    apply hI0
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, h]
    exact hy
  have hJm : J = maximalIdeal R := by
    by_contra hne
    have hJ0 : J ≠ ⊥ := fun h ↦ (Ideal.ne_bot_of_height_eq_one h1) (le_bot_iff.1 (h ▸ hPJ))
    have := height_eq_one_of_ne_bot_of_ne_maximalIdeal hdim hJ0 hne
    exact hPne (eq_of_le_of_height_eq_one_of_ne_bot this hPJ (Ideal.ne_bot_of_height_eq_one h1))
  have : J.IsMaximal := hJm ▸ maximalIdeal.isMaximal R
  rw [hIJ]
  exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hPJ)

end QuotDim

section NormDown

variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B] [Algebra A B] [Module.Finite A B]

/-- A finite field extension with surjective structure map has degree one. -/
private theorem finrank_eq_one_of_surjective_algebraMap {F E : Type*} [Field F] [Field E]
    [Algebra F E]
    (h : Function.Surjective (algebraMap F E)) : Module.finrank F E = 1 := by
  have e := LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨(algebraMap F E).injective, h⟩
  rw [← e.finrank_eq, Module.finrank_self]

omit [IsDomain A] [IsDomain B] in
/-- **N1 for residue fields.** Let `A → B` be a finite map of Noetherian local domains inducing
a surjection on residue fields, `Q` a prime of `B` over `q`, with `A ⧸ q` and `B ⧸ Q` of dimension
`≤ 1`. Then for `z ∈ κ(Q)ˣ`, `ord_{A/q}(N_{κ(Q)/κ(q)} z) = ord_{B/Q}(z)`. -/
theorem ordFrac_norm_residueField (hres : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B)
    (Q : Ideal B) [Q.IsPrime] (q : Ideal A) [q.IsPrime] (hq : q = Q.comap (algebraMap A B))
    [Ring.KrullDimLE 1 (A ⧸ q)] [Ring.KrullDimLE 1 (B ⧸ Q)] {z : Q.ResidueField} (hz : z ≠ 0) :
    letI := (Ideal.ResidueField.map q Q (algebraMap A B) hq).toAlgebra
    Ring.ordFrac (A ⧸ q) (Algebra.norm q.ResidueField z) = Ring.ordFrac (B ⧸ Q) z := by
  subst hq
  let _ := (Ideal.ResidueField.map _ Q (algebraMap A B) rfl).toAlgebra
  have _ : IsLocalRing (A ⧸ Q.comap (algebraMap A B)) :=
    isLocalRing_quotient_prime (Q.comap (algebraMap A B))
  have _ : IsLocalRing (B ⧸ Q) := isLocalRing_quotient_prime Q
  have _ : FaithfulSMul (A ⧸ Q.comap (algebraMap A B)) (B ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Ideal.algebraMap_quotient_injective
  have _ : Module.Finite A (B ⧸ Q) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A Q).toLinearMap
      (Ideal.Quotient.mkₐ_surjective A Q)
  have _ : Module.Finite (A ⧸ Q.comap (algebraMap A B)) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ Q.comap (algebraMap A B)) (B ⧸ Q)
  let _ : Algebra (A ⧸ Q.comap (algebraMap A B)) Q.ResidueField :=
    ((algebraMap (B ⧸ Q) Q.ResidueField).comp
      (algebraMap (A ⧸ Q.comap (algebraMap A B)) (B ⧸ Q))).toAlgebra
  have _ : IsScalarTower (A ⧸ Q.comap (algebraMap A B)) (B ⧸ Q) Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have _ : IsScalarTower (A ⧸ Q.comap (algebraMap A B)) (Q.comap (algebraMap A B)).ResidueField
      Q.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change algebraMap (B ⧸ Q) Q.ResidueField (Ideal.Quotient.mk Q (algebraMap A B a)) =
      Ideal.ResidueField.map _ Q (algebraMap A B) rfl
        (algebraMap (A ⧸ Q.comap (algebraMap A B)) (Q.comap (algebraMap A B)).ResidueField
          (Ideal.Quotient.mk (Q.comap (algebraMap A B)) a))
    rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk,
      Ideal.ResidueField.map_algebraMap]
  have hdeg : Module.finrank (ResidueField (A ⧸ Q.comap (algebraMap A B)))
      (ResidueField (B ⧸ Q)) = 1 := by
    apply finrank_eq_one_of_surjective_algebraMap
    intro y
    obtain ⟨y, rfl⟩ := residue_surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hres b
    refine ⟨residue _ (Ideal.Quotient.mk (Q.comap (algebraMap A B)) a), ?_⟩
    rw [ResidueField.algebraMap_residue, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    change Ideal.Quotient.mk Q (algebraMap A B a) - Ideal.Quotient.mk Q b ∈ _
    rw [← map_sub, mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (u⁻¹ : (B ⧸ Q)ˣ).1
    have h1 : Ideal.Quotient.mk Q ((algebraMap A B a - b) * c) = 1 := by
      rw [map_mul, hc, ← hu, Units.mul_inv]
    rw [← map_one (Ideal.Quotient.mk Q), Ideal.Quotient.eq] at h1
    have hm : (algebraMap A B a - b) * c ∈ maximalIdeal B := by
      rw [← neg_sub]
      exact Ideal.mul_mem_right _ _ (neg_mem ha)
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).2 (by
      have := sub_mem hm (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) h1)
      simp at this))
  rw [ordFrac_norm_of_ne_zero (B := B ⧸ Q) hz, hdeg, pow_one]

end NormDown

section LocalFactor

variable {D K : Type*} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
  [Ring.KrullDimLE 1 D] [Field K] [Algebra D K] [IsFractionRing D K]

/-- If `(f, g)` factors in `D` itself, the tame symbol is the local symbol of that
factorization. -/
theorem tameSymbol_eq_symbol (hU : VectorBundle.UnitDifferences D) {f g : Kˣ}
    (F : PairFactorization D f g) : tameSymbol D K hU f g = F.symbol := by
  have hσ : ∀ d : D, (RingEquiv.refl K) (algebraMap D K d) =
      algebraMap (⊥ : Subalgebra D K) K (botRingEquiv D K d) := fun d ↦
    (coe_botRingEquiv d).symm
  let F' : PairFactorization (⊥ : Subalgebra D K) f g :=
    F.map (botRingEquiv D K) (RingEquiv.refl K) hσ
  have hsym : F'.symbol = Units.map (ResidueField.mapEquiv (botRingEquiv D K) :
      ResidueField D →* ResidueField (⊥ : Subalgebra D K)) F.symbol :=
    PairFactorization.symbol_map _ _ hσ F
  have hC : Admissible (⊥ : Subalgebra D K) ⊥ ![f, g] := admissible_self_of_factors F'.factors
  rw [tameSymbol_eq_tameOf hU hC, tameOf,
    finprod_normSym_localizationAt (IsOverring.refl (⊥ : Subalgebra D K)) F', normSym_eq,
    localSymbol_eq F', hsym]
  have hbij : Function.Surjective (algebraMap (ResidueField D)
      (ResidueField (⊥ : Subalgebra D K))) := by
    intro y
    obtain ⟨y, rfl⟩ := residue_surjective y
    obtain ⟨d, rfl⟩ := (botRingEquiv D K).surjective y
    refine ⟨residue D d, ?_⟩
    rw [ResidueField.algebraMap_residue, algebraMap_bot_eq]
    rfl
  have hdeg := finrank_eq_one_of_surjective_algebraMap hbij
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  have halg : (ResidueField.mapEquiv (botRingEquiv D K) (F.symbol : ResidueField D)) =
      algebraMap (ResidueField D) (ResidueField (⊥ : Subalgebra D K)) F.symbol := by
    obtain ⟨y, hy⟩ := residue_surjective (F.symbol : ResidueField D)
    rw [← hy, ResidueField.algebraMap_residue, ResidueField.mapEquiv_apply,
      ResidueField.map_residue, algebraMap_bot_eq]
  rw [halg, Algebra.norm_algebraMap, hdeg, pow_one]

end LocalFactor

section AtPrime

variable {A : Type*} [CommRing A] [IsDomain A] (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K] (q : Ideal A) [q.IsPrime]

/-- The `K`-algebra structure on `A_q = Localization.AtPrime q`, for a fraction field `K` of
`A` (the canonical map `A_q → K`). -/
noncomputable abbrev atPrimeAlgebra : Algebra (Localization.AtPrime q) K :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ K q.primeCompl (nonZeroDivisors A)
    q.primeCompl_le_nonZeroDivisors

/-- `A → A_q → K` is a scalar tower for `atPrimeAlgebra`. -/
theorem atPrime_isScalarTower :
    letI := atPrimeAlgebra K q
    IsScalarTower A (Localization.AtPrime q) K :=
  IsLocalization.localization_isScalarTower_of_submonoid_le _ K q.primeCompl (nonZeroDivisors A)
    q.primeCompl_le_nonZeroDivisors

/-- `K` is a fraction field of `A_q` via `atPrimeAlgebra`. -/
theorem atPrime_isFractionRing :
    letI := atPrimeAlgebra K q
    IsFractionRing (Localization.AtPrime q) K :=
  letI := atPrimeAlgebra K q
  haveI := atPrime_isScalarTower K q
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl _ K

variable {K q} in
/-- The map `A_q → K` extends `A → K`. -/
theorem algebraMap_atPrime_apply (x : A) :
    letI := atPrimeAlgebra K q
    algebraMap (Localization.AtPrime q) K (algebraMap A _ x) = algebraMap A K x :=
  letI := atPrimeAlgebra K q
  haveI := atPrime_isScalarTower K q
  (IsScalarTower.algebraMap_apply A _ K x).symm

variable {K} in
/-- `A_q` inherits unit differences from `A`. -/
theorem unitDifferences_atPrime (hU : VectorBundle.UnitDifferences A) :
    VectorBundle.UnitDifferences (Localization.AtPrime q) :=
  unitDifferences_of_injective_tame (algebraMap A _)
    (IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors) hU

end AtPrime

section TameOrd

variable (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] (K : Type*) [Field K]
  [Algebra A K] [IsFractionRing A K]

/-- **The order of the tame symbol at a height-one prime.** For a height-one prime `q` of `A`
and `f, g ∈ Kˣ`, the order `ord_{A/q}(∂_{A_q}(f, g)) ∈ ℤ` of the tame symbol of the local ring
`A_q = Localization.AtPrime q` (with fraction field `K`), an element of `κ(q)ˣ`, where `κ(q)` is
the fraction field of `A ⧸ q`. It is defined to be `0` if `A ⧸ q` has dimension `> 1` (this does
not happen when `A` is local of dimension two). -/
noncomputable def tameOrd (hU : VectorBundle.UnitDifferences A)
    (q : {q : PrimeSpectrum A // q.asIdeal.height = 1}) (f g : Kˣ) : ℤ :=
  letI := atPrimeAlgebra K q.1.asIdeal
  haveI := atPrime_isFractionRing K q.1.asIdeal
  haveI := krullDimLE_one_localization_of_height_eq_one q.2
  open Classical in
  if _ : Ring.KrullDimLE 1 (A ⧸ q.1.asIdeal) then
    ordZ (A ⧸ q.1.asIdeal) (tameSymbol (Localization.AtPrime q.1.asIdeal) K
      (unitDifferences_atPrime q.1.asIdeal hU) f g)
  else 0

end TameOrd

section TameOrdData

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] (P : Ideal R) [hP : P.IsPrime]
  [Ring.KrullDimLE 1 (R ⧸ P)]

omit [IsDomain R] in
/-- The order in `R ⧸ P` of the residue of `u / s ∈ R_P` (`u, s ∉ P`) is
`ord(u) - ord(s)`. -/
theorem ordZ_resUnits_mk' {u s : R} (hu : u ∉ P) (hs : s ∉ P) :
    ordZ (R ⧸ P) (resUnits (Localization.AtPrime P)
      ((IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime P) P u ⟨s, hs⟩).2 hu).unit) =
      ((Ring.ord (R ⧸ P) (Ideal.Quotient.mk P u)).toNat : ℤ) -
        (Ring.ord (R ⧸ P) (Ideal.Quotient.mk P s)).toNat := by
  have hres : ∀ x : R, algebraMap (R ⧸ P) P.ResidueField (Ideal.Quotient.mk P x) =
      residue (Localization.AtPrime P) (algebraMap R (Localization.AtPrime P) x) := by
    intro x
    rw [Ideal.algebraMap_quotient_residueField_mk,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime P) P.ResidueField,
      ResidueField.algebraMap_eq]
  have hne : ∀ x : R, x ∉ P → algebraMap (R ⧸ P) P.ResidueField (Ideal.Quotient.mk P x) ≠ 0 := by
    intro x hx
    rw [hres, ne_eq, residue_eq_zero_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P]
    exact hx
  have key : resUnits (Localization.AtPrime P)
      ((IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime P) P u ⟨s, hs⟩).2 hu).unit *
      Units.mk0 _ (hne s hs) = Units.mk0 _ (hne u hu) := by
    ext
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec,
      Units.val_mk0, hres]
    rw [← map_mul, IsLocalization.mk'_spec]
  have := congrArg (ordZ (R ⧸ P)) key
  rw [ordZ_mul, ordZ_mk0, ordZ_mk0] at this
  linarith

end TameOrdData

section TameOrdFormula

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- `ordZ (-1) = 0`. -/
private theorem ordZ_neg_one {S L : Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 S] [Field L] [Algebra S L] [IsFractionRing S L] :
    ordZ S (-1 : Lˣ) = 0 := by
  have h := ordZ_mul (R := S) (-1 : Lˣ) (-1)
  rw [neg_one_mul, neg_neg, ordZ_one] at h
  linarith

/-- **The tame order from a factorization.** Let `R` be a two-dimensional Noetherian local
domain, `Q` a height-one prime, and `s₁ a = u₀ π₀^e`, `s₂ b = v₀ π₀^f` in `R` with
`s₁, s₂, u₀, v₀ ∉ Q` and `π₀ ≠ 0`. Then for `x = a`, `y = b` in `Kˣ`,
`ord_{R/Q}(∂_{R_Q}(x, y)) = m · (f (ord(u₀) - ord(s₁)) - e (ord(v₀) - ord(s₂)))` with
`m = ord_{R_Q}(π₀)`. -/
theorem tameOrd_eq_of_data (hdim : ringKrullDim R = 2) (hU : VectorBundle.UnitDifferences R)
    (Q : {Q : PrimeSpectrum R // Q.asIdeal.height = 1}) {x y : Kˣ}
    {a b π₀ u₀ v₀ s₁ s₂ : R} {e f : ℕ} (hx : (x : K) = algebraMap R K a)
    (hy : (y : K) = algebraMap R K b) (hπ₀ : π₀ ≠ 0) (hs₁ : s₁ ∉ Q.1.asIdeal)
    (hs₂ : s₂ ∉ Q.1.asIdeal) (hu₀ : u₀ ∉ Q.1.asIdeal) (hv₀ : v₀ ∉ Q.1.asIdeal)
    (h₁ : s₁ * a = u₀ * π₀ ^ e) (h₂ : s₂ * b = v₀ * π₀ ^ f) :
    tameOrd R K hU Q x y =
      ((Ring.ord (Localization.AtPrime Q.1.asIdeal) (algebraMap R _ π₀)).toNat : ℤ) *
        (f * (((Ring.ord (R ⧸ Q.1.asIdeal) (Ideal.Quotient.mk _ u₀)).toNat : ℤ) -
            (Ring.ord (R ⧸ Q.1.asIdeal) (Ideal.Quotient.mk _ s₁)).toNat) -
          e * (((Ring.ord (R ⧸ Q.1.asIdeal) (Ideal.Quotient.mk _ v₀)).toNat : ℤ) -
            (Ring.ord (R ⧸ Q.1.asIdeal) (Ideal.Quotient.mk _ s₂)).toNat)) := by
  obtain ⟨⟨P, hP⟩, hP1⟩ := Q
  have hdimQ : Ring.KrullDimLE 1 (R ⧸ P) := krullDimLE_one_quotient_of_height_eq_one hdim P hP1
  let _ := atPrimeAlgebra K P
  have _ := atPrime_isFractionRing K P
  have _ := atPrime_isScalarTower K P
  have _ := krullDimLE_one_localization_of_height_eq_one hP1
  simp only [tameOrd]
  rw [dif_pos hdimQ]
  have hu₁ := (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime P) P u₀ ⟨s₁, hs₁⟩).2 hu₀
  have hv₁ := (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime P) P v₀ ⟨s₂, hs₂⟩).2 hv₀
  have hK : ∀ (c w : R) (hw : w ∉ P), algebraMap (Localization.AtPrime P) K
      (IsLocalization.mk' (Localization.AtPrime P) c (⟨w, hw⟩ : P.primeCompl)) *
        algebraMap R K w = algebraMap R K c := by
    intro c w hw
    rw [← algebraMap_atPrime_apply (q := P) w, ← algebraMap_atPrime_apply (q := P) c, ← map_mul,
      IsLocalization.mk'_spec]
  have hs0 : ∀ w : R, w ∉ P → algebraMap R K w ≠ 0 := fun w hw ↦
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 fun h ↦ hw (h ▸ P.zero_mem)
  let F : PairFactorization (Localization.AtPrime P) x y :=
    { π := algebraMap R _ π₀
      e₁ := e
      e₂ := f
      u₁ := hu₁.unit
      u₂ := hv₁.unit
      hπ := by
        rw [algebraMap_atPrime_apply]
        exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ₀
      hf := by
        rw [hx, IsUnit.unit_spec, algebraMap_atPrime_apply, zpow_natCast]
        apply mul_left_cancel₀ (hs0 s₁ hs₁)
        rw [← map_mul, h₁, map_mul, map_pow, ← hK u₀ s₁ hs₁]
        ring
      hg := by
        rw [hy, IsUnit.unit_spec, algebraMap_atPrime_apply, zpow_natCast]
        apply mul_left_cancel₀ (hs0 s₂ hs₂)
        rw [← map_mul, h₂, map_mul, map_pow, ← hK v₀ s₂ hs₂]
        ring }
  rw [tameSymbol_eq_symbol _ F, PairFactorization.symbol, ← zpow_natCast, ordZ_zpow, ordZ_mul,
    ordZ_mul, ordZ_zpow, ordZ_zpow, ordZ_zpow, ordZ_neg_one]
  change _ * (_ + _ * ordZ (R ⧸ P) (resUnits (Localization.AtPrime P) hu₁.unit) +
    _ * ordZ (R ⧸ P) (resUnits (Localization.AtPrime P) hv₁.unit)) = _
  rw [ordZ_resUnits_mk' P hu₀ hs₁, ordZ_resUnits_mk' P hv₀ hs₂]
  ring

/-- **Key lemma, factored case (Stacks 42.6.2, second part).** Let `R` be a two-dimensional
Noetherian local domain with fraction field `K`, `a, b ∈ R` nonzero with images `x, y ∈ Kˣ`, and
suppose that at every height-one prime `Q ∋ a b` there are `π₀, u₀, v₀, s₁, s₂ ∈ R`, `e, f : ℕ`
with `π₀ ≠ 0`, `s₁, s₂, u₀, v₀ ∉ Q`, `s₁ a = u₀ π₀^e`, `s₂ b = v₀ π₀^f`. Then
`∑_Q ord_{R/Q}(∂_{R_Q}(x, y)) = 0`. -/
theorem finsum_tameOrd_eq_zero_of_data (hdim : ringKrullDim R = 2)
    (hU : VectorBundle.UnitDifferences R) {x y : Kˣ} {a b : R}
    (hx : (x : K) = algebraMap R K a) (hy : (y : K) = algebraMap R K b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdata : ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → a * b ∈ Q →
      ∃ (π₀ u₀ v₀ s₁ s₂ : R) (e f : ℕ), π₀ ≠ 0 ∧ s₁ ∉ Q ∧ s₂ ∉ Q ∧ u₀ ∉ Q ∧ v₀ ∉ Q ∧
        s₁ * a = u₀ * π₀ ^ e ∧ s₂ * b = v₀ * π₀ ^ f) :
    ∑ᶠ Q : {Q : PrimeSpectrum R // Q.asIdeal.height = 1}, tameOrd R K hU Q x y = 0 := by
  classical
  have hQ : ∀ Q : {Q : PrimeSpectrum R // Q.asIdeal.height = 1}, tameOrd R K hU Q x y =
      if a * b ∈ Q.1.asIdeal then -(satComplex Q.1.asIdeal a b).herbrand else 0 := by
    intro Q
    split_ifs with hab
    · obtain ⟨π₀, u₀, v₀, s₁, s₂, e, f, hπ₀, hs₁, hs₂, hu₀, hv₀, h₁, h₂⟩ :=
        hdata Q.1.asIdeal Q.2 hab
      rw [tameOrd_eq_of_data hdim hU Q hx hy hπ₀ hs₁ hs₂ hu₀ hv₀ h₁ h₂,
        (herbrand_satComplex hdim Q.2 ha hb hπ₀ hs₁ hs₂ hu₀ hv₀ h₁ h₂).2]
      ring
    · have h1 : (1 : R) ∉ Q.1.asIdeal := (Ideal.ne_top_iff_one _).1 Q.1.isPrime.ne_top
      have haQ : a ∉ Q.1.asIdeal := fun h ↦ hab (Q.1.asIdeal.mul_mem_right b h)
      have hbQ : b ∉ Q.1.asIdeal := fun h ↦ hab (Q.1.asIdeal.mul_mem_left a h)
      rw [tameOrd_eq_of_data (e := 0) (f := 0) hdim hU Q hx hy one_ne_zero h1 h1 haQ hbQ
        (by ring) (by ring)]
      ring
  rw [finsum_congr hQ]
  have e1 : ∀ Q : {Q : PrimeSpectrum R // Q.asIdeal.height = 1},
      (if a * b ∈ Q.1.asIdeal then -(satComplex Q.1.asIdeal a b).herbrand else 0) =
        ∑ᶠ (_ : a * b ∈ Q.1.asIdeal), -(satComplex Q.1.asIdeal a b).herbrand :=
    fun Q ↦ finsum_eq_if.symm
  have e2 := finsum_subtype_eq_finsum_cond
    (f := fun Q : {Q : PrimeSpectrum R // Q.asIdeal.height = 1} ↦
      -(satComplex Q.1.asIdeal a b).herbrand) (fun Q ↦ a * b ∈ Q.1.asIdeal)
  beta_reduce at e2
  rw [finsum_congr e1, ← e2, ← finsum_comp_equiv (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun Q : PrimeSpectrum R ↦ Q.asIdeal.height = 1) (fun Q ↦ a * b ∈ Q.asIdeal)).symm]
  rw [finsum_neg_distrib]
  rw [show ∀ c : ℤ, -c = 0 ↔ c = 0 from fun c ↦ neg_eq_zero]
  exact finsum_herbrand_satComplex hdim ha hb

end TameOrdFormula

section Equivs

variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- `A_q ⊆ K` (as `locInK`) is a localization of `A` at `q`. -/
theorem isLocalization_locInK_atPrime (P : Ideal A) [P.IsPrime] :
    IsLocalization.AtPrime (locInK P.primeCompl (⊥ : Subalgebra A K)) P :=
  isLocalization_locInK_bot _ P.primeCompl_le_nonZeroDivisors

/-- The isomorphism `Localization.AtPrime P ≃ A_P ⊆ K`. -/
noncomputable def atPrimeEquivLocInK (P : Ideal A) [P.IsPrime] :
    Localization.AtPrime P ≃+* locInK P.primeCompl (⊥ : Subalgebra A K) :=
  haveI := isLocalization_locInK_atPrime (K := K) P
  (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
    (locInK P.primeCompl (⊥ : Subalgebra A K))).toRingEquiv

/-- `atPrimeEquivLocInK` is compatible with the maps to `K`. -/
theorem coe_atPrimeEquivLocInK (P : Ideal A) [P.IsPrime] (d : Localization.AtPrime P) :
    letI := atPrimeAlgebra K P
    ((atPrimeEquivLocInK P d : locInK P.primeCompl (⊥ : Subalgebra A K)) : K) =
      algebraMap (Localization.AtPrime P) K d := by
  let _ := atPrimeAlgebra K P
  have _ := isLocalization_locInK_atPrime (K := K) P
  have h := IsLocalization.ringHom_ext P.primeCompl
    (j := (locInK P.primeCompl (⊥ : Subalgebra A K)).val.toRingHom.comp
      (atPrimeEquivLocInK P).toRingHom)
    (k := algebraMap (Localization.AtPrime P) K) (RingHom.ext fun a ↦ by
      simp only [RingHom.comp_apply]
      rw [algebraMap_atPrime_apply]
      simp only [atPrimeEquivLocInK, RingEquiv.toRingHom_eq_coe,
        AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, AlgEquiv.commutes]
      rfl)
  exact congrArg (fun φ : Localization.AtPrime P →+* K ↦ φ d) h

variable (B : Subalgebra A K) (Q : Ideal B) [Q.IsPrime]

/-- The isomorphism `B_Q ⊆ K` (as `localizationAt`) `≃ Localization.AtPrime Q`. -/
noncomputable def localizationAtEquivAtPrime : localizationAt B Q ≃+* Localization.AtPrime Q :=
  (localizationAtEquiv B Q).symm.toRingEquiv

omit [IsDomain A] in
/-- `localizationAtEquivAtPrime` is compatible with the maps to `K`. -/
theorem algebraMap_localizationAtEquivAtPrime (t : localizationAt B Q) :
    letI := atPrimeAlgebra K Q
    algebraMap (Localization.AtPrime Q) K (localizationAtEquivAtPrime B Q t) = (t : K) := by
  let _ := atPrimeAlgebra K Q
  have h := IsLocalization.ringHom_ext Q.primeCompl
    (j := (localizationAt B Q).val.toRingHom.comp (localizationAtEquiv B Q).toRingEquiv.toRingHom)
    (k := algebraMap (Localization.AtPrime Q) K) (RingHom.ext fun c ↦ by
      simp only [RingHom.comp_apply]
      rw [algebraMap_atPrime_apply]
      simp only [RingEquiv.toRingHom_eq_coe,
        AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, AlgEquiv.commutes]
      rfl)
  have := congrArg (fun φ : Localization.AtPrime Q →+* K ↦ φ (localizationAtEquivAtPrime B Q t)) h
  simp only [RingHom.comp_apply] at this
  rw [← this]
  simp [localizationAtEquivAtPrime]

/-- The local homomorphism `A_P → B_Q` is compatible with the maps to `K`. -/
theorem algebraMap_localRingHom (P : Ideal A) [P.IsPrime] (hP : P = Q.comap (algebraMap A B))
    (d : Localization.AtPrime P) :
    letI := atPrimeAlgebra K Q
    letI := atPrimeAlgebra K P
    algebraMap (Localization.AtPrime Q) K (Localization.localRingHom P Q (algebraMap A B) hP d) =
      algebraMap (Localization.AtPrime P) K d := by
  let _ := atPrimeAlgebra K Q
  let _ := atPrimeAlgebra K P
  have h := IsLocalization.ringHom_ext P.primeCompl
    (j := (algebraMap (Localization.AtPrime Q) K).comp
      (Localization.localRingHom P Q (algebraMap A B) hP))
    (k := algebraMap (Localization.AtPrime P) K) (RingHom.ext fun c ↦ by
      simp only [RingHom.comp_apply]
      rw [Localization.localRingHom_to_map, algebraMap_atPrime_apply, algebraMap_atPrime_apply]
      rfl)
  exact congrArg (fun φ : Localization.AtPrime P →+* K ↦ φ d) h

end Equivs

section TameOrdEq

/-- Unfolding `tameOrd` when `A ⧸ q` has dimension `≤ 1`. -/
theorem tameOrd_eq (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] (K : Type*)
    [Field K] [Algebra A K] [IsFractionRing A K] (hU : VectorBundle.UnitDifferences A)
    (q : {q : PrimeSpectrum A // q.asIdeal.height = 1}) [h : Ring.KrullDimLE 1 (A ⧸ q.1.asIdeal)]
    (f g : Kˣ) :
    letI := atPrimeAlgebra K q.1.asIdeal
    haveI := atPrime_isFractionRing K q.1.asIdeal
    haveI := krullDimLE_one_localization_of_height_eq_one q.2
    tameOrd A K hU q f g = ordZ (A ⧸ q.1.asIdeal) (tameSymbol (Localization.AtPrime q.1.asIdeal) K
      (unitDifferences_atPrime q.1.asIdeal hU) f g) := by
  unfold tameOrd
  exact dif_pos h

end TameOrdEq

section NormStep

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {B : Subalgebra A K} [IsLocalRing B] [IsNoetherianRing B] [Module.Finite A B]

omit [IsNoetherianRing A] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing B]
  [Module.Finite A B] in
/-- Compatibility of the residue-field isomorphisms with the maps `κ(A_P) → κ(L)` and
`κ(P) → κ(Q)` (used for the norm comparison in `ordZ_normDown_eq`). -/
theorem residueField_compat_normStep (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (hP : P = Q.comap (algebraMap A B))
    [IsLocalRing (locInK P.primeCompl (⊥ : Subalgebra A K))]
    (L : Subalgebra (locInK P.primeCompl (⊥ : Subalgebra A K)) K) [IsLocalRing L]
    [IsLocalHom (algebraMap (locInK P.primeCompl (⊥ : Subalgebra A K)) L)]
    (hL : ∀ t, t ∈ L ↔ (RingEquiv.refl K) t ∈ localizationAt B Q)
    (t : ResidueField (locInK P.primeCompl (⊥ : Subalgebra A K))) :
    letI := (Ideal.ResidueField.map P Q (algebraMap A B) hP).toAlgebra
    ResidueField.mapEquiv ((subEquiv (RingEquiv.refl K) hL).trans (localizationAtEquivAtPrime B Q))
      (algebraMap (ResidueField (locInK P.primeCompl (⊥ : Subalgebra A K))) (ResidueField L) t) =
      algebraMap P.ResidueField Q.ResidueField
        (ResidueField.mapEquiv (atPrimeEquivLocInK (K := K) P).symm t) := by
  let _ := atPrimeAlgebra K Q
  let _ := atPrimeAlgebra K P
  have _ := atPrime_isFractionRing K Q
  let _ : Algebra P.ResidueField Q.ResidueField :=
    (Ideal.ResidueField.map P Q (algebraMap A B) hP).toAlgebra
  obtain ⟨w, rfl⟩ := residue_surjective t
  rw [ResidueField.algebraMap_residue, ResidueField.mapEquiv_apply, ResidueField.map_residue,
    ResidueField.mapEquiv_apply, ResidueField.map_residue]
  change _ = ResidueField.map _ _
  rw [ResidueField.map_residue]
  refine congrArg (residue _) ?_
  apply IsFractionRing.injective (Localization.AtPrime Q) K
  rw [algebraMap_localRingHom B Q P hP]
  change algebraMap (Localization.AtPrime Q) K (localizationAtEquivAtPrime B Q _) = _
  rw [algebraMap_localizationAtEquivAtPrime, ← coe_atPrimeEquivLocInK P]
  erw [RingEquiv.apply_symm_apply]
  rfl

/-- **One factor of the norm-down.** Let `B ⊆ K` be finite over `A` with the same residue field,
`Q` a prime of `B` over `P`, and `L` a local subalgebra of `K` over `A_P ⊆ K` with the same carrier
as `B_Q`. For `z ∈ κ(L)ˣ`, the order in `A ⧸ P` of `N_{κ(L)/κ(A_P)}(z)` (moved to `κ(P)`) is the
order in `B ⧸ Q` of `z` (moved to `κ(Q)`). -/
theorem ordZ_normDown_eq (hres : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B)
    (P : Ideal A) [P.IsPrime] [Ring.KrullDimLE 1 (A ⧸ P)] (Q : Ideal B) [Q.IsPrime]
    [Ring.KrullDimLE 1 (B ⧸ Q)] (hP : P = Q.comap (algebraMap A B))
    [IsLocalRing (locInK P.primeCompl (⊥ : Subalgebra A K))]
    (L : Subalgebra (locInK P.primeCompl (⊥ : Subalgebra A K)) K) [IsLocalRing L]
    [IsLocalHom (algebraMap (locInK P.primeCompl (⊥ : Subalgebra A K)) L)]
    (hL : ∀ t, t ∈ L ↔ (RingEquiv.refl K) t ∈ localizationAt B Q) (z : (ResidueField L)ˣ) :
    ordZ (A ⧸ P) (Units.map (ResidueField.mapEquiv (atPrimeEquivLocInK (K := K) P).symm :
        ResidueField (locInK P.primeCompl (⊥ : Subalgebra A K)) →*
          ResidueField (Localization.AtPrime P)) (normDown L z)) =
      ordZ (B ⧸ Q) (Units.map (ResidueField.mapEquiv
        ((subEquiv (RingEquiv.refl K) hL).trans (localizationAtEquivAtPrime B Q)) :
          ResidueField L →* ResidueField (Localization.AtPrime Q)) z) := by
  have h3 := fun (w : Q.ResidueField) (hw : w ≠ 0) ↦
    ordFrac_norm_residueField (A := A) (B := B) hres Q P hP hw
  let _ := atPrimeAlgebra K Q
  let _ := atPrimeAlgebra K P
  have _ := atPrime_isFractionRing K Q
  let _ : Algebra P.ResidueField Q.ResidueField :=
    (Ideal.ResidueField.map P Q (algebraMap A B) hP).toAlgebra
  have hc := residueField_compat_normStep P Q hP L hL
  have key := norm_ringEquiv_compat (ResidueField.mapEquiv (atPrimeEquivLocInK (K := K) P).symm)
    (ResidueField.mapEquiv ((subEquiv (RingEquiv.refl K) hL).trans
      (localizationAtEquivAtPrime B Q))) hc (z : ResidueField L)
  have hz : ResidueField.mapEquiv ((subEquiv (RingEquiv.refl K) hL).trans
      (localizationAtEquivAtPrime B Q)) (z : ResidueField L) ≠ 0 :=
    (map_ne_zero _).2 z.ne_zero
  rw [normDown_eq]
  unfold ordZ
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [← key, h3 _ hz]

end NormStep

section OrdZProd

/-- `ordZ` turns finite products into sums. -/
private theorem ordZ_finprod {R L ι : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Field L] [Algebra R L] [IsFractionRing R L] [Finite ι] (u : ι → Lˣ) :
    ordZ R (∏ᶠ i, u i) = ∑ᶠ i, ordZ R (u i) := by
  classical
  have _ : Fintype ι := Fintype.ofFinite ι
  rw [finprod_eq_prod_of_fintype, finsum_eq_sum_of_fintype]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [ordZ_one]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ordZ_mul, ih]

end OrdZProd

section PerPrime

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- One term of the norm-down sum: for a local subalgebra `L` of `K` over `A_P ⊆ K` with the
same carrier as `B_Q` (`Q` a height-one prime of `B` over `P`), the order in `A ⧸ P` of the
normed tame symbol of `L` is `ord_{B/Q} ∂_{B_Q}`. -/
theorem ordZ_normDown_tameSymbol_eq_tameOrd (hdim : ringKrullDim A = 2)
    (hU : VectorBundle.UnitDifferences A)
    (B : Subalgebra A K) [IsLocalRing B] [IsNoetherianRing B] [Module.Finite A B]
    (hres : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B)
    (P : Ideal A) [P.IsPrime] [Ring.KrullDimLE 1 (A ⧸ P)]
    [IsLocalRing (locInK P.primeCompl (⊥ : Subalgebra A K))]
    {hUE : VectorBundle.UnitDifferences (locInK P.primeCompl (⊥ : Subalgebra A K))}
    {L : Subalgebra (locInK P.primeCompl (⊥ : Subalgebra A K)) K} [IsLocalRing L]
    [IsNoetherianRing L] [Ring.KrullDimLE 1 L]
    [IsLocalHom (algebraMap (locInK P.primeCompl (⊥ : Subalgebra A K)) L)]
    (Q : {Q : PrimeSpectrum B // Q.asIdeal.height = 1 ∧ Q.asIdeal.comap (algebraMap A B) = P})
    (hL : ∀ t, t ∈ L ↔ (RingEquiv.refl K) t ∈ localizationAt B Q.1.asIdeal) (x y : Kˣ) :
    ordZ (A ⧸ P) (Units.map (ResidueField.mapEquiv (atPrimeEquivLocInK (K := K) P).symm :
        ResidueField (locInK P.primeCompl (⊥ : Subalgebra A K)) →*
          ResidueField (Localization.AtPrime P))
      (normDown L (tameSymbol L K (unitDifferences_subalgebra hUE L) x y))) =
      tameOrd B K (unitDifferences_subalgebra hU B) ⟨Q.1, Q.2.1⟩ x y := by
  have hdimQ : Ring.KrullDimLE 1 (B ⧸ Q.1.asIdeal) :=
    krullDimLE_one_quotient_of_height_eq_one (ringKrullDim_eq_two_of_finite hdim B) Q.1.asIdeal
      Q.2.1
  rw [ordZ_normDown_eq hres P Q.1.asIdeal Q.2.2.symm _ hL]
  let _ := atPrimeAlgebra K Q.1.asIdeal
  have _ := atPrime_isFractionRing K Q.1.asIdeal
  have _ := krullDimLE_one_localization_of_height_eq_one Q.2.1
  have h6' := tameSymbol_ringEquiv ((subEquiv (RingEquiv.refl K) hL).trans
      (localizationAtEquivAtPrime B Q.1.asIdeal)) (RingEquiv.refl K)
    (fun d ↦ (algebraMap_localizationAtEquivAtPrime B Q.1.asIdeal
      (subEquiv (RingEquiv.refl K) hL d)).symm) (unitDifferences_subalgebra hUE _)
    (unitDifferences_atPrime Q.1.asIdeal (unitDifferences_subalgebra hU B)) x y
  have e : ∀ z : Kˣ, Units.map ((RingEquiv.refl K : K ≃+* K) : K →* K) z = z :=
    fun z ↦ Units.ext rfl
  rw [e, e] at h6'
  rw [tameOrd_eq, h6']

/-- **Norm-down at one height-one prime (Stacks 42.6.2, first paragraph).** Let `B ⊆ K` be a
local subalgebra, finite over the two-dimensional local domain `A`, with the same residue field,
and `q` a height-one prime of `A` such that `B_q ⊆ K` is an overring of `A_q ⊆ K`. Then
`ord_{A/q} ∂_{A_q}(x, y) = ∑_{Q} ord_{B/Q} ∂_{B_Q}(x, y)`, the sum over the height-one primes `Q`
of `B` lying over `q`. -/
theorem tameOrd_eq_finsum_fiber (hdim : ringKrullDim A = 2) (hU : VectorBundle.UnitDifferences A)
    (B : Subalgebra A K) [IsLocalRing B] [IsNoetherianRing B] [Module.Finite A B]
    (hres : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B)
    (q : {q : PrimeSpectrum A // q.asIdeal.height = 1})
    (hS : IsOverring (locInK q.1.asIdeal.primeCompl (⊥ : Subalgebra A K))
      (locInK q.1.asIdeal.primeCompl B)) (x y : Kˣ) :
    tameOrd A K hU q x y =
      ∑ᶠ Q : {Q : PrimeSpectrum B // Q.asIdeal.height = 1 ∧
          Q.asIdeal.comap (algebraMap A B) = q.1.asIdeal},
        tameOrd B K (unitDifferences_subalgebra hU B) ⟨Q.1, Q.2.1⟩ x y := by
  classical
  obtain ⟨⟨P, hPp⟩, hq1⟩ := q
  -- the local ring `E = A_P ⊆ K`
  have _ : IsLocalization.AtPrime (locInK P.primeCompl (⊥ : Subalgebra A K)) P :=
    isLocalization_locInK_atPrime P
  have _ : IsLocalRing (locInK P.primeCompl (⊥ : Subalgebra A K)) :=
    IsLocalization.AtPrime.isLocalRing _ P
  have _ : IsNoetherianRing (locInK P.primeCompl (⊥ : Subalgebra A K)) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have _ : Ring.KrullDimLE 1 (locInK P.primeCompl (⊥ : Subalgebra A K)) := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height P, hq1]
    rfl
  have hUE := unitDifferences_subalgebra hU (locInK P.primeCompl (⊥ : Subalgebra A K))
  have hdimP : Ring.KrullDimLE 1 (A ⧸ P) := krullDimLE_one_quotient_of_height_eq_one hdim P hq1
  let _ := atPrimeAlgebra K P
  have _ := atPrime_isFractionRing K P
  have _ := krullDimLE_one_localization_of_height_eq_one hq1
  -- T6: from `Localization.AtPrime P` to `E`
  have h6 := tameSymbol_ringEquiv (atPrimeEquivLocInK (K := K) P).symm (RingEquiv.refl K)
    (fun d ↦ by
      rw [RingEquiv.refl_apply, ← coe_atPrimeEquivLocInK P, RingEquiv.apply_symm_apply]
      rfl) hUE (unitDifferences_atPrime P hU) x y
  have e : ∀ z : Kˣ, Units.map ((RingEquiv.refl K : K ≃+* K) : K →* K) z = z :=
    fun z ↦ Units.ext rfl
  rw [e, e] at h6
  -- T5 over `E` for the overring `S = B_P ⊆ K`
  have hB := isOverring_overSubalgebra hS
  have _ := hB.isNoetherianRing
  have _ := hB.krullDimLE
  have _ := hB.finite_maximalSpectrum
  have h5 := tameSymbol_eq_finprod_normDown hUE hB x y
  simp only [tameOrd]
  rw [dif_pos hdimP]
  change ordZ (A ⧸ P) (tameSymbol (Localization.AtPrime P) K _ x y) = _
  rw [h6, h5, map_finprod _ (Set.toFinite _), ordZ_finprod]
  -- reindex the maximal ideals of `S` by the height-one primes of `B` over `P`
  obtain ⟨ε, hε⟩ := exists_equiv_maximalSpectrum_locInK B P hq1 (locInK P.primeCompl B) rfl
  have h : ∀ t, t ∈ locInK P.primeCompl B ↔ (RingEquiv.refl K) t ∈ overSubalgebra hS.le :=
    fun _ ↦ Iff.rfl
  rw [← finsum_comp_equiv (ε.trans (maxSpecEquiv (RingEquiv.refl K) h))]
  refine finsum_congr fun Q ↦ ?_
  have hL : ∀ t, t ∈ localizationAt (overSubalgebra hS.le)
      ((ε.trans (maxSpecEquiv (RingEquiv.refl K) h)) Q).asIdeal ↔
        (RingEquiv.refl K) t ∈ localizationAt B Q.1.asIdeal := fun t ↦ by
    rw [hε Q]
    exact (mem_localizationAt_subEquiv_iff (RingEquiv.refl K) h (ε Q).asIdeal t).symm
  have _ := isLocalHom_algebraMap_localizationAt hB
    ((ε.trans (maxSpecEquiv (RingEquiv.refl K) h)) Q).asIdeal
  exact ordZ_normDown_tameSymbol_eq_tameOrd hdim hU B hres P (hUE := hUE) Q hL x y

end PerPrime

section Fiberwise

/-- Summing over the fibres of a map: `∑_y ∑_{φ x = y} G x = ∑_x G x` for `G` of finite
support. -/
private theorem finsum_fiberwise_keyLemma {X Y : Type*} (φ : X → Y) (G : X → ℤ)
    (hG : (Function.support G).Finite) :
    ∑ᶠ y, ∑ᶠ x : {x // φ x = y}, G x = ∑ᶠ x, G x := by
  classical
  have h1 : ∀ y, ∑ᶠ x : {x // φ x = y}, G x = ∑ x ∈ hG.toFinset, if φ x = y then G x else 0 := by
    intro y
    rw [finsum_subtype_eq_finsum_cond (fun x ↦ φ x = y)]
    simp_rw [finsum_eq_if]
    refine finsum_eq_sum_of_support_subset _ fun x hx ↦ ?_
    rw [Set.Finite.coe_toFinset]
    by_contra hxs
    apply hx
    simp only [Function.mem_support, not_not] at hxs
    simp [hxs]
  simp_rw [h1]
  rw [finsum_sum_comm]
  · rw [finsum_eq_sum_of_support_subset G (s := hG.toFinset) (by rw [Set.Finite.coe_toFinset])]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [finsum_eq_single _ (φ x) fun y hy ↦ by simp [Ne.symm hy]]
    simp
  · intro x _
    refine (Set.finite_singleton (φ x)).subset fun y hy ↦ ?_
    by_contra hne
    exact hy (by simp [Ne.symm hne])

end Fiberwise

section Final

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The tame order vanishes at height-one primes containing neither `a` nor `b`. -/
theorem tameOrd_eq_zero_of_notMem (hdim : ringKrullDim R = 2)
    (hU : VectorBundle.UnitDifferences R) (Q : {Q : PrimeSpectrum R // Q.asIdeal.height = 1})
    {x y : Kˣ} {a b : R} (hx : (x : K) = algebraMap R K a) (hy : (y : K) = algebraMap R K b)
    (ha : a ∉ Q.1.asIdeal) (hb : b ∉ Q.1.asIdeal) : tameOrd R K hU Q x y = 0 := by
  have h1 : (1 : R) ∉ Q.1.asIdeal := (Ideal.ne_top_iff_one _).1 Q.1.isPrime.ne_top
  rw [tameOrd_eq_of_data (e := 0) (f := 0) hdim hU Q hx hy one_ne_zero h1 h1 ha hb (by ring)
    (by ring)]
  ring

/-- **Key lemma for elements (Stacks 42.6.2).** For a two-dimensional Noetherian local domain
`A` with unit differences and `a, b ∈ A` nonzero, `∑_q ord_{A/q}(∂_{A_q}(a, b)) = 0` over the
height-one primes `q` of `A`. -/
theorem finsum_tameOrd_eq_zero_of_ne_zero (hdim : ringKrullDim R = 2)
    (hU : VectorBundle.UnitDifferences R) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ᶠ q : {q : PrimeSpectrum R // q.asIdeal.height = 1}, tameOrd R K hU q
      (Units.mk0 (algebraMap R K a) ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ha))
      (Units.mk0 (algebraMap R K b) ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hb))
      = 0 := by
  set x := Units.mk0 (algebraMap R K a) ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ha)
  set y := Units.mk0 (algebraMap R K b) ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hb)
  obtain ⟨B, _, _, _, hBres, hover, hfac⟩ := exists_glued_factorization (K := K) hdim hU ha hb
  have _ : IsNoetherianRing B :=
    isNoetherian_of_tower R (isNoetherian_of_isNoetherianRing_of_finite R B)
  have hres : ∀ c : B, ∃ r : R, c - algebraMap R B r ∈ maximalIdeal B := by
    intro c
    obtain ⟨t, ht⟩ := hBres.2 (residue B c)
    obtain ⟨r, rfl⟩ := residue_surjective t
    refine ⟨r, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, ← ResidueField.map_residue, ht, sub_self]
  have hdimB : ringKrullDim B = 2 := ringKrullDim_eq_two_of_finite hdim B
  have hUB := unitDifferences_subalgebra hU B
  have hinj : Function.Injective (algebraMap R B) := fun r s h ↦
    IsFractionRing.injective R K (congrArg Subtype.val h)
  have ha' : algebraMap R B a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha
  have hb' : algebraMap R B b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb
  -- the factored key lemma on `B`
  have hB0 := finsum_tameOrd_eq_zero_of_data hdimB hUB (x := x) (y := y)
    (a := algebraMap R B a) (b := algebraMap R B b) rfl rfl ha' hb' (fun Q _ hQ habQ ↦
      exists_factor_data _ _ rfl rfl (hfac Q hQ (by rwa [map_mul])))
  -- the norm-down at each height-one prime of `A`
  rw [finsum_congr fun q ↦ tameOrd_eq_finsum_fiber hdim hU B hres q (hover q.1 q.2) x y, ← hB0]
  -- sum over the fibres of `Q ↦ Q ∩ R`
  let φ : {Q : PrimeSpectrum B // Q.asIdeal.height = 1} →
      {q : PrimeSpectrum R // q.asIdeal.height = 1} := fun Q ↦
    ⟨⟨Q.1.asIdeal.comap (algebraMap R B), Ideal.comap_isPrime _ _⟩,
      height_comap_eq_one hdim B Q.1.asIdeal Q.2⟩
  have hG : (Function.support fun Q : {Q : PrimeSpectrum B // Q.asIdeal.height = 1} ↦
      tameOrd B K hUB Q x y).Finite := by
    refine ((finite_setOf_height_eq_one_mem (mul_ne_zero ha' hb')).preimage
      (Function.Injective.injOn (fun _ _ h ↦ Subtype.ext h))).subset fun Q hQ ↦ ?_
    refine ⟨Q.2, ?_⟩
    by_contra hab
    exact hQ (tameOrd_eq_zero_of_notMem hdimB hUB Q (a := algebraMap R B a)
      (b := algebraMap R B b) rfl rfl (fun h ↦ hab (Q.1.asIdeal.mul_mem_right _ h))
      (fun h ↦ hab (Q.1.asIdeal.mul_mem_left _ h)))
  rw [← finsum_fiberwise_keyLemma φ _ hG]
  refine finsum_congr fun q ↦ ?_
  let e : {Q : PrimeSpectrum B // Q.asIdeal.height = 1 ∧
      Q.asIdeal.comap (algebraMap R B) = q.1.asIdeal} ≃
      {Q : {Q : PrimeSpectrum B // Q.asIdeal.height = 1} // φ Q = q} :=
    { toFun := fun Q ↦ ⟨⟨Q.1, Q.2.1⟩, Subtype.ext (PrimeSpectrum.ext Q.2.2)⟩
      invFun := fun Q ↦ ⟨Q.1.1, Q.1.2, congrArg (fun q' ↦ q'.1.asIdeal) Q.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact finsum_comp_equiv e (f := fun Q ↦ tameOrd B K hUB Q.1 x y)

end Final

section Bilinear

variable (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] (K : Type*) [Field K]
  [Algebra A K] [IsFractionRing A K] (hU : VectorBundle.UnitDifferences A)
  (q : {q : PrimeSpectrum A // q.asIdeal.height = 1})

/-- `tameOrd` is additive in the first argument. -/
theorem tameOrd_mul_left (f f' g : Kˣ) :
    tameOrd A K hU q (f * f') g = tameOrd A K hU q f g + tameOrd A K hU q f' g := by
  by_cases h : Ring.KrullDimLE 1 (A ⧸ q.1.asIdeal)
  · let _ := atPrimeAlgebra K q.1.asIdeal
    have _ := atPrime_isFractionRing K q.1.asIdeal
    have _ := krullDimLE_one_localization_of_height_eq_one q.2
    rw [tameOrd_eq, tameOrd_eq, tameOrd_eq, tameSymbol_mul_left, ordZ_mul]
  · simp only [tameOrd, dif_neg h, add_zero]

/-- `tameOrd` is additive in the second argument. -/
theorem tameOrd_mul_right (f g g' : Kˣ) :
    tameOrd A K hU q f (g * g') = tameOrd A K hU q f g + tameOrd A K hU q f g' := by
  by_cases h : Ring.KrullDimLE 1 (A ⧸ q.1.asIdeal)
  · let _ := atPrimeAlgebra K q.1.asIdeal
    have _ := atPrime_isFractionRing K q.1.asIdeal
    have _ := krullDimLE_one_localization_of_height_eq_one q.2
    rw [tameOrd_eq, tameOrd_eq, tameOrd_eq, tameSymbol_mul_right, ordZ_mul]
  · simp only [tameOrd, dif_neg h, add_zero]

/-- `tameOrd` changes sign under inversion of the first argument. -/
theorem tameOrd_inv_left (f g : Kˣ) : tameOrd A K hU q f⁻¹ g = -tameOrd A K hU q f g := by
  have h := tameOrd_mul_left A K hU q f⁻¹ f g
  rw [inv_mul_cancel] at h
  have h1 : tameOrd A K hU q 1 g = 0 := by
    have h2 := tameOrd_mul_left A K hU q 1 1 g
    rw [one_mul] at h2
    linarith
  linarith

/-- `tameOrd` changes sign under inversion of the second argument. -/
theorem tameOrd_inv_right (f g : Kˣ) : tameOrd A K hU q f g⁻¹ = -tameOrd A K hU q f g := by
  have h := tameOrd_mul_right A K hU q f g⁻¹ g
  rw [inv_mul_cancel] at h
  have h1 : tameOrd A K hU q f 1 = 0 := by
    have h2 := tameOrd_mul_right A K hU q f 1 1
    rw [one_mul] at h2
    linarith
  linarith

/-- `f ∈ Kˣ` is a unit of `A_q`: `f = a / s` with `a, s ∉ q`. -/
def IsUnitAtPrime (f : Kˣ) : Prop :=
  ∃ a s : A, a ∉ q.1.asIdeal ∧ s ∉ q.1.asIdeal ∧ (f : K) * algebraMap A K s = algebraMap A K a

omit [IsNoetherianRing A] in
variable {A K q} in
/-- `IsUnitAtPrime A K q f` says exactly that `f` is (the image of) a unit of
`A_q = Localization.AtPrime q`. -/
theorem isUnitAtPrime_iff (f : Kˣ) :
    letI := atPrimeAlgebra K q.1.asIdeal
    IsUnitAtPrime A K q f ↔ ∃ u : (Localization.AtPrime q.1.asIdeal)ˣ,
      Units.map (algebraMap (Localization.AtPrime q.1.asIdeal) K :
        Localization.AtPrime q.1.asIdeal →* K) u = f := by
  let _ := atPrimeAlgebra K q.1.asIdeal
  constructor
  · rintro ⟨a, s, ha, hs, hfs⟩
    refine ⟨((IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime q.1.asIdeal)
      q.1.asIdeal a ⟨s, hs⟩).2 ha).unit, Units.ext ?_⟩
    have hs0 : algebraMap A K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2
      fun h0 ↦ hs (h0 ▸ q.1.asIdeal.zero_mem)
    rw [Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec]
    apply mul_right_cancel₀ hs0
    rw [hfs, ← algebraMap_atPrime_apply (q := q.1.asIdeal) s, ← map_mul,
      IsLocalization.mk'_spec, algebraMap_atPrime_apply]
  · rintro ⟨u, rfl⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.mk'_surjective q.1.asIdeal.primeCompl
      (u : Localization.AtPrime q.1.asIdeal)
    change IsLocalization.mk' (Localization.AtPrime q.1.asIdeal) a s = _ at h
    have hu : IsUnit (IsLocalization.mk' (Localization.AtPrime q.1.asIdeal) a s) := by
      rw [h]
      exact u.isUnit
    have ha : a ∈ q.1.asIdeal.primeCompl :=
      (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime q.1.asIdeal) q.1.asIdeal a s).1
        hu
    refine ⟨a, s, ha, s.2, ?_⟩
    rw [Units.coe_map, MonoidHom.coe_coe, ← h, ← algebraMap_atPrime_apply (q := q.1.asIdeal),
      ← algebraMap_atPrime_apply (q := q.1.asIdeal), ← map_mul, IsLocalization.mk'_spec]

variable {A K q} in
/-- T4 for `tameOrd`: if `f` and `g` are units of `A_q`, then `ord_{A/q} ∂_{A_q}(f, g) = 0`. -/
theorem tameOrd_eq_zero_of_isUnitAtPrime {f g : Kˣ} (hf : IsUnitAtPrime A K q f)
    (hg : IsUnitAtPrime A K q g) : tameOrd A K hU q f g = 0 := by
  by_cases h : Ring.KrullDimLE 1 (A ⧸ q.1.asIdeal)
  · let _ := atPrimeAlgebra K q.1.asIdeal
    have _ := atPrime_isFractionRing K q.1.asIdeal
    have _ := krullDimLE_one_localization_of_height_eq_one q.2
    obtain ⟨u, rfl⟩ := (isUnitAtPrime_iff f).1 hf
    obtain ⟨v, rfl⟩ := (isUnitAtPrime_iff g).1 hg
    rw [tameOrd_eq, tameSymbol_units_units, ordZ_one]
  · simp only [tameOrd, dif_neg h]

end Bilinear

section Support

variable (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] (K : Type*) [Field K]
  [Algebra A K] [IsFractionRing A K] (hU : VectorBundle.UnitDifferences A)

/-- The support of `q ↦ ord_{A/q} ∂_{A_q}(f, g)` consists of height-one primes at which `f` or `g`
is not a unit of `A_q`. -/
theorem support_tameOrd_subset (f g : Kˣ) :
    Function.support (fun q ↦ tameOrd A K hU q f g) ⊆
      {q | ¬ IsUnitAtPrime A K q f ∨ ¬ IsUnitAtPrime A K q g} := by
  intro q hq
  by_contra h
  simp only [Set.mem_ofPred_eq, not_or, not_not] at h
  exact hq (tameOrd_eq_zero_of_isUnitAtPrime hU h.1 h.2)

/-- `f ∈ Kˣ` is a unit of `A_q` for all but finitely many height-one primes `q`. -/
theorem finite_setOf_not_isUnitAtPrime (f : Kˣ) :
    {q : {q : PrimeSpectrum A // q.asIdeal.height = 1} | ¬ IsUnitAtPrime A K q f}.Finite := by
  obtain ⟨a, s, hs, hf⟩ := IsFractionRing.div_surjective (A := A) (f : K)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsK : algebraMap A K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hs0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hf
    exact f.ne_zero hf.symm
  refine ((finite_setOf_height_eq_one_mem (mul_ne_zero ha0 hs0)).preimage
    (Function.Injective.injOn (fun _ _ h ↦ Subtype.ext h))).subset fun q hq ↦ ?_
  refine ⟨q.2, ?_⟩
  by_contra has
  exact hq ⟨a, s, fun h ↦ has (q.1.asIdeal.mul_mem_right s h),
    fun h ↦ has (q.1.asIdeal.mul_mem_left a h), by rw [← hf, div_mul_cancel₀ _ hsK]⟩

/-- **Finiteness of the key-lemma sum:** `ord_{A/q} ∂_{A_q}(f, g) = 0` for all but finitely
many height-one primes `q`. -/
theorem finite_support_tameOrd (f g : Kˣ) :
    (Function.support (fun q ↦ tameOrd A K hU q f g)).Finite :=
  ((finite_setOf_not_isUnitAtPrime A K f).union (finite_setOf_not_isUnitAtPrime A K g)).subset
    (support_tameOrd_subset A K hU f g)

end Support

section KeyLemma

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- **The key lemma (Stacks 42.6.3).** Let `A` be a two-dimensional Noetherian local domain with
fraction field `K` and unit differences. For `f, g ∈ Kˣ`,
`∑_q ord_{A/q}(∂_{A_q}(f, g)) = 0`, the (finite, see `finite_support_tameOrd`) sum running over
the height-one primes `q` of `A`. -/
theorem finsum_tameOrd_eq_zero (hdim : ringKrullDim A = 2) (hU : VectorBundle.UnitDifferences A)
    (f g : Kˣ) :
    ∑ᶠ q : {q : PrimeSpectrum A // q.asIdeal.height = 1}, tameOrd A K hU q f g = 0 := by
  have hdec : ∀ f : Kˣ, ∃ (a s : A) (ha : a ≠ 0) (hs : s ≠ 0),
      f = Units.mk0 (algebraMap A K a) ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ha) *
        (Units.mk0 (algebraMap A K s)
          ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hs))⁻¹ := by
    intro f
    obtain ⟨a, s, hs, hf⟩ := IsFractionRing.div_surjective (A := A) (f : K)
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_div] at hf
      exact f.ne_zero hf.symm
    exact ⟨a, s, ha0, hs0, Units.ext (by simp [← hf, div_eq_mul_inv])⟩
  obtain ⟨a, s, ha, hs, rfl⟩ := hdec f
  obtain ⟨b, t, hb, ht, rfl⟩ := hdec g
  set x₁ := Units.mk0 (algebraMap A K a) ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ha)
  set x₂ := Units.mk0 (algebraMap A K s) ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hs)
  set y₁ := Units.mk0 (algebraMap A K b) ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hb)
  set y₂ := Units.mk0 (algebraMap A K t) ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ht)
  have hsplit : ∀ q, tameOrd A K hU q (x₁ * x₂⁻¹) (y₁ * y₂⁻¹) =
      tameOrd A K hU q x₁ y₁ - tameOrd A K hU q x₁ y₂ -
        (tameOrd A K hU q x₂ y₁ - tameOrd A K hU q x₂ y₂) := by
    intro q
    rw [tameOrd_mul_left, tameOrd_mul_right, tameOrd_mul_right, tameOrd_inv_left,
      tameOrd_inv_left, tameOrd_inv_right, tameOrd_inv_right]
    ring
  have h11 := finite_support_tameOrd A K hU x₁ y₁
  have h12 := finite_support_tameOrd A K hU x₁ y₂
  have h21 := finite_support_tameOrd A K hU x₂ y₁
  have h22 := finite_support_tameOrd A K hU x₂ y₂
  rw [finsum_congr hsplit, finsum_sub_distrib ((h11.union h12).subset (Function.support_sub _ _))
      ((h21.union h22).subset (Function.support_sub _ _)), finsum_sub_distrib h11 h12,
    finsum_sub_distrib h21 h22, finsum_tameOrd_eq_zero_of_ne_zero hdim hU ha hb,
    finsum_tameOrd_eq_zero_of_ne_zero hdim hU ha ht,
    finsum_tameOrd_eq_zero_of_ne_zero hdim hU hs hb,
    finsum_tameOrd_eq_zero_of_ne_zero hdim hU hs ht]
  ring

end KeyLemma

end GromovWitten.Algebra.Tame
