/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Finiteness.Ideal
import GromovWitten.Algebra.FiniteTypeKrullDimension
import GromovWitten.Algebra.TameFactorization

/-!
# Gluing finite extensions of a two-dimensional local domain

This file proves the preparation lemma for the key lemma on tame symbols (Stacks 42.6.1), in the
form where all rings are subalgebras of one fixed field. Let `(A, m)` be a Noetherian local
domain of Krull dimension two with fraction field `K`, let `t ∈ A` be nonzero, let `T` be a
finite set of height-one primes of `A` and, for `q ∈ T`, let `C q` be a subalgebra of `K`
containing `A_q` and contained in a finitely generated `A_q`-submodule of `K`. Then there is a
subalgebra `B` of `K`, finite over `A`, local, with residue field equal to that of `A`, such that
`(A \ q)⁻¹ B = C q` for `q ∈ T` and `(A \ q)⁻¹ B = A_q` for height-one `q ∉ T` with `t ∉ q`.

Localizations are taken inside `K`: `locInK S B = {x ∈ K | s * x ∈ B for some s ∈ S}` for a
submonoid `S` of `A`. Localizations of `B` at a prime ideal of `B` reuse
`GromovWitten.Algebra.Tame.localizationAt` from `TameFactorization`
(`localizationAt B P = {x ∈ K | s * x ∈ B for some s ∈ B \ P}`). In particular `A_q` is
`locInK q.primeCompl ⊥`, which is Mathlib's `Localization.subalgebra.ofField`
(`locInK_bot_eq_ofField`).

The construction (Stacks): first enlarge `T` so that it is the set of all height-one primes
containing a suitable nonzero `s ∈ A` (with `C q = A_q` on the new primes). Choose `n` with
`tⁿ C q ⊆ A_q`, put `M_k = {x ∈ K | tᵏ x ∈ A, x ∈ C q for all q ∈ T}` and choose `c` with
`mᶜ M_{2n} ⊆ M_n` (the quotient is supported at `m`). Then `B = A + m^(c+1) M_n`.

## Main results

* `GromovWitten.Algebra.Tame.exists_glued_subalgebra`: the gluing lemma above.
* `GromovWitten.Algebra.Tame.exists_glued_subalgebra_core`: the same when `T` is exactly the
  set of height-one primes containing `t`.
* `GromovWitten.Algebra.Tame.exists_equiv_maximalSpectrum_locInK`: for `B ⊆ K` finite over `A`
  and a height-one prime `q`, the primes of `B` of height one lying over `q` correspond to the
  maximal ideals of `(A \ q)⁻¹ B`, with equal localizations inside `K`.
* `GromovWitten.Algebra.Tame.localizationAt_maximalIdeal_eq_self`: the localization of a local
  subalgebra at its own maximal ideal is itself.
* `GromovWitten.Algebra.Tame.exists_unique_height_one_prime_localizationAt_eq_locInK_bot`: if
  `(A \ q)⁻¹ B = A_q`, the height-one prime of `B` over `q` is unique and its local ring
  (inside `K`) is `A_q`.
* `GromovWitten.Algebra.Tame.height_comap_eq_one`: for `B ⊆ K` local and finite over `A`, every
  height-one prime of `B` contracts to a height-one prime of `A`;
  `comap_mem_heightOneSet_iff` then identifies those over primes containing `t`.
* `GromovWitten.Algebra.Tame.ringKrullDim_eq_two_of_finite`: such a `B` has dimension two.
* `GromovWitten.Algebra.Tame.exists_finset_span_of_moduleFinite`: converts `Module.Finite`
  over `A_q` into the finiteness hypothesis used here.
-/

namespace GromovWitten.Algebra.Tame

open IsLocalRing

section Defs

variable {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]

/-- The localization of a subalgebra `B` of `K` at a submonoid `S` of `A`, taken inside `K`:
the elements `x : K` with `s * x ∈ B` for some `s ∈ S`. -/
def locInK (S : Submonoid A) (B : Subalgebra A K) : Subalgebra A K where
  carrier := {x | ∃ s ∈ S, algebraMap A K s * x ∈ B}
  mul_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨s', hs', hy⟩
    refine ⟨s * s', S.mul_mem hs hs', ?_⟩
    convert B.mul_mem hx hy using 1
    simp only [map_mul]; ring
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨s', hs', hy⟩
    refine ⟨s * s', S.mul_mem hs hs', ?_⟩
    convert B.add_mem (B.mul_mem (B.algebraMap_mem s') hx) (B.mul_mem (B.algebraMap_mem s) hy)
      using 1
    simp only [map_mul]; ring
  algebraMap_mem' a := ⟨1, S.one_mem, by simp⟩

/-- Membership in `locInK`. -/
theorem mem_locInK {S : Submonoid A} {B : Subalgebra A K} {x : K} :
    x ∈ locInK S B ↔ ∃ s ∈ S, algebraMap A K s * x ∈ B := Iff.rfl

/-- `B` is contained in each of its localizations inside `K`. -/
theorem le_locInK (S : Submonoid A) (B : Subalgebra A K) : B ≤ locInK S B :=
  fun x hx ↦ ⟨1, S.one_mem, by simpa using hx⟩

end Defs

section Basic

variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- `locInK S ⊥` is Mathlib's `Localization.subalgebra.ofField`. -/
theorem locInK_bot_eq_ofField (S : Submonoid A) (hS : S ≤ nonZeroDivisors A) :
    locInK S (⊥ : Subalgebra A K) = Localization.subalgebra.ofField K S hS := by
  ext x
  change _ ↔ ∃ (a s : A) (_ : s ∈ S), x = algebraMap A K a * (algebraMap A K s)⁻¹
  rw [mem_locInK]
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hx
    have hs0 : algebraMap A K s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
    refine ⟨a, s, hs, ?_⟩
    rw [ha]; field_simp
  · rintro ⟨a, s, hs, rfl⟩
    have hs0 : algebraMap A K s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
    refine ⟨s, hs, Algebra.mem_bot.mpr ⟨a, ?_⟩⟩
    field_simp

/-- `locInK S ⊥` is a localization of `A` at `S`. -/
theorem isLocalization_locInK_bot (S : Submonoid A) (hS : S ≤ nonZeroDivisors A) :
    IsLocalization S (locInK S (⊥ : Subalgebra A K)) := by
  rw [locInK_bot_eq_ofField S hS]
  infer_instance

omit [IsFractionRing A K] in
/-- A nonzero prime contained in a height-one prime is equal to it. -/
theorem eq_of_le_of_height_eq_one_of_ne_bot {p q : Ideal A} [p.IsPrime] [q.IsPrime]
    (hq : q.height = 1) (hle : p ≤ q) (hp : p ≠ ⊥) : p = q := by
  by_contra hne
  have h := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
  rw [hq] at h
  have h0 : p.height = 0 := by
    have := (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp
      (by simpa using h : p.height + 1 ≤ 0 + 1)
    simpa using this
  exact hp (Ideal.height_eq_zero_iff_eq_bot.mp h0)

omit [IsFractionRing A K] in
/-- Avoidance for a height-one prime `q`: if a submonoid `W` contains `A \ q` and meets `q`,
then every nonzero `d` divides some element of `W`. -/
private theorem exists_mem_dvd_of_height_eq_one {q : Ideal A} [q.IsPrime] (hq : q.height = 1)
    (W : Submonoid A) (hW : q.primeCompl ≤ W) {w : A} (hwW : w ∈ W) (hwq : w ∈ q) {d : A}
    (hd : d ≠ 0) : ∃ w' ∈ W, d ∣ w' := by
  by_contra h
  push Not at h
  have hdisj : Disjoint ((Ideal.span {d} : Ideal A) : Set A) (W : Set A) := by
    rw [Set.disjoint_left]
    intro x hx hxW
    exact h x hxW (Ideal.mem_span_singleton.mp hx)
  obtain ⟨p, hp, hdp, hpW⟩ := Ideal.exists_le_prime_disjoint _ W hdisj
  have hpq : p ≤ q := by
    intro x hx
    by_contra hxq
    exact Set.disjoint_left.mp hpW hx (hW hxq)
  have hp0 : p ≠ ⊥ := by
    intro h0
    exact hd (by simpa [h0] using hdp (Ideal.mem_span_singleton_self d))
  have := eq_of_le_of_height_eq_one_of_ne_bot hq hpq hp0
  subst this
  exact Set.disjoint_left.mp hpW hwq hwW

/-- If `q` is a height-one prime containing `t`, then every `g : K` becomes an element of
`A_q` after multiplication by a power of `t`. -/
theorem exists_pow_mul_mem_locInK {q : Ideal A} [q.IsPrime] (hq : q.height = 1) {t : A}
    (ht : t ∈ q) (g : K) :
    ∃ n : ℕ, algebraMap A K (t ^ n) * g ∈ locInK q.primeCompl (⊥ : Subalgebra A K) := by
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) g
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdK : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  obtain ⟨w, hw, e, he⟩ := exists_mem_dvd_of_height_eq_one hq (q.primeCompl ⊔ Submonoid.powers t)
    le_sup_left (Submonoid.mem_sup_right (Submonoid.mem_powers t)) ht hd0
  obtain ⟨s, hs, z, hz, rfl⟩ := Submonoid.mem_sup.mp hw
  obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp hz
  refine ⟨n, s, hs, Algebra.mem_bot.mpr ⟨e * a, ?_⟩⟩
  have : algebraMap A K s * algebraMap A K (t ^ n) = algebraMap A K d * algebraMap A K e := by
    rw [← map_mul, he, map_mul]
  simp only [map_mul]
  rw [← mul_assoc, this]
  field_simp

/-- For two distinct height-one primes `q ≠ q'` and `x : K`, some `s ∉ q` puts `s * x` in
`A_{q'}`. -/
theorem exists_primeCompl_mul_mem_locInK {q q' : Ideal A} [q.IsPrime] [q'.IsPrime]
    (hq : q.height = 1) (hq' : q'.height = 1) (hne : q ≠ q') (x : K) :
    ∃ s ∈ q.primeCompl, algebraMap A K s * x ∈ locInK q'.primeCompl (⊥ : Subalgebra A K) := by
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdK : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hnle : ¬ q ≤ q' := fun hle ↦ hne (eq_of_le_of_height_eq_one_of_ne_bot hq' hle
    (fun h ↦ by simp [h] at hq))
  obtain ⟨w, hwq, hwq'⟩ := Set.not_subset.mp hnle
  obtain ⟨w', hw', e, he⟩ := exists_mem_dvd_of_height_eq_one hq
    (q.primeCompl ⊔ q'.primeCompl) le_sup_left (Submonoid.mem_sup_right hwq') hwq hd0
  obtain ⟨s, hs, s', hs', rfl⟩ := Submonoid.mem_sup.mp hw'
  refine ⟨s, hs, s', hs', Algebra.mem_bot.mpr ⟨e * a, ?_⟩⟩
  have : algebraMap A K s * algebraMap A K s' = algebraMap A K d * algebraMap A K e := by
    rw [← map_mul, he, map_mul]
  simp only [map_mul]
  rw [← mul_assoc, mul_comm (algebraMap A K s'), this]
  field_simp

end Basic

section TwoDim

variable {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]

/-- In a local domain of dimension two, a prime other than `0` and the maximal ideal has
height one. -/
theorem height_eq_one_of_ne_bot_of_ne_maximalIdeal (hdim : ringKrullDim A = 2) {p : Ideal A}
    [p.IsPrime] (h0 : p ≠ ⊥) (hm : p ≠ maximalIdeal A) : p.height = 1 := by
  have hm2 : (maximalIdeal A).height = 2 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
    rw [hdim] at this
    exact WithBot.coe_eq_coe.mp (by rw [this]; rfl)
  have h := Ideal.height_add_one_le_of_lt_of_isPrime
    (lt_of_le_of_ne (le_maximalIdeal ‹p.IsPrime›.ne_top) hm)
  rw [hm2] at h
  have hle : p.height ≤ 1 := (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp
    (by simpa [one_add_one_eq_two] using h)
  refine le_antisymm hle (Order.one_le_iff_ne_zero.mpr fun h' ↦ h0 ?_)
  exact Ideal.height_eq_zero_iff_eq_bot.mp h'

end TwoDim

section Bound

variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]

omit [IsDomain A] [IsFractionRing A K] in
/-- If `t ^ k * x ∈ R` and `k ≤ l`, then `t ^ l * x ∈ R`. -/
private theorem pow_mul_mem_of_le {R : Subalgebra A K} {t : A} {k l : ℕ} (hkl : k ≤ l) {x : K}
    (hx : algebraMap A K (t ^ k) * x ∈ R) : algebraMap A K (t ^ l) * x ∈ R := by
  have : algebraMap A K (t ^ l) * x = algebraMap A K (t ^ (l - k)) * (algebraMap A K (t ^ k) * x)
  := by rw [← mul_assoc, ← map_mul, ← pow_add, Nat.sub_add_cancel hkl]
  rw [this]
  exact R.mul_mem (R.algebraMap_mem _) hx

/-- If `C` lies in a finitely generated `A_q`-submodule of `K` and `t ∈ q` with `q` of height
one, then a power of `t` multiplies `C` into `A_q`. -/
theorem exists_pow_mul_mem_of_span {q : Ideal A} [q.IsPrime] (hq : q.height = 1) {t : A}
    (ht : t ∈ q) (C : Set K) (G : Finset K)
    (hG : ∀ x ∈ C, x ∈ Submodule.span (locInK q.primeCompl (⊥ : Subalgebra A K)) (G : Set K)) :
    ∃ n : ℕ, ∀ x ∈ C,
      algebraMap A K (t ^ n) * x ∈ locInK q.primeCompl (⊥ : Subalgebra A K) := by
  choose N hN using fun g : K ↦ exists_pow_mul_mem_locInK (K := K) hq ht g
  refine ⟨G.sup N, fun x hx ↦ ?_⟩
  have hxG := hG x hx
  clear hx
  induction hxG using Submodule.span_induction with
  | mem g hg => exact pow_mul_mem_of_le (Finset.le_sup hg) (hN g)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx =>
    change algebraMap A K (t ^ G.sup N) * ((r : K) * x) ∈ _
    rw [mul_left_comm]
    exact Subalgebra.mul_mem _ r.2 hx

omit [IsDomain A] [IsFractionRing A K] in
/-- If `C` is a finitely generated module over a smaller subalgebra `R` of `K` (via the inclusion),
then `C` lies in the `R`-span of a finite subset of `K`. This converts the `Module.Finite`
formulation into the hypothesis used by `exists_glued_subalgebra`. -/
theorem exists_finset_span_of_moduleFinite {R C : Subalgebra A K} (h : R ≤ C) :
    letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
    Module.Finite R C → ∃ G : Finset K, ∀ x ∈ C, x ∈ Submodule.span R (G : Set K) := by
  classical
  let _ := (Subalgebra.inclusion h).toRingHom.toAlgebra
  intro hfin
  obtain ⟨s, hs⟩ := hfin.fg_top
  let f : C →ₗ[R] K :=
    { toFun := Subtype.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine ⟨s.image Subtype.val, fun x hx ↦ ?_⟩
  have hmem : (⟨x, hx⟩ : C) ∈ Submodule.span R (s : Set C) := hs ▸ Submodule.mem_top
  have h2 : f ⟨x, hx⟩ ∈ Submodule.span R (f '' (s : Set C)) := by
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem hmem
  rw [Finset.coe_image]
  exact h2

end Bound

section Construction

variable {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]

/-- The auxiliary module `M_k = {x ∈ K | t ^ k * x ∈ A, x ∈ C q for all q ∈ T}` of the
gluing construction. -/
private def glueModule (t : A) (k : ℕ) (T : Set (PrimeSpectrum A))
    (C : PrimeSpectrum A → Subalgebra A K) :
    Submodule A K where
  carrier := {x | algebraMap A K (t ^ k) * x ∈ (⊥ : Subalgebra A K) ∧ ∀ q ∈ T, x ∈ C q}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨by rw [mul_add]; exact add_mem hx hy, fun q hq ↦ add_mem (hx' q hq) (hy' q hq)⟩
  zero_mem' := ⟨by simp, fun q _ ↦ zero_mem _⟩
  smul_mem' := by
    rintro a x ⟨hx, hx'⟩
    refine ⟨?_, fun q hq ↦ Subalgebra.smul_mem _ (hx' q hq) a⟩
    change _ * (a • x) ∈ _
    rw [Algebra.smul_def, mul_left_comm]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) hx

variable {t : A} {T : Set (PrimeSpectrum A)} {C : PrimeSpectrum A → Subalgebra A K}

/-- Membership in `glueModule`. -/
private theorem mem_glueModule {k : ℕ} {x : K} : x ∈ glueModule t k T C ↔
    algebraMap A K (t ^ k) * x ∈ (⊥ : Subalgebra A K) ∧ ∀ q ∈ T, x ∈ C q := Iff.rfl

/-- `M_k * M_l ⊆ M_{k + l}`. -/
private theorem glueModule_mul_mem {k l : ℕ} {x y : K} (hx : x ∈ glueModule t k T C)
    (hy : y ∈ glueModule t l T C) : x * y ∈ glueModule t (k + l) T C := by
  refine ⟨?_, fun q hq ↦ Subalgebra.mul_mem _ (hx.2 q hq) (hy.2 q hq)⟩
  have : algebraMap A K (t ^ (k + l)) * (x * y) =
      (algebraMap A K (t ^ k) * x) * (algebraMap A K (t ^ l) * y) := by
    rw [pow_add, map_mul]; ring
  rw [this]
  exact Subalgebra.mul_mem _ hx.1 hy.1

/-- The modules `M_k` increase with `k`. -/
private theorem glueModule_mono {k l : ℕ} (hkl : k ≤ l) : glueModule t k T C ≤ glueModule t l T C :=
  fun _ hx ↦ ⟨pow_mul_mem_of_le hkl hx.1, hx.2⟩

variable [IsFractionRing A K]

omit [IsFractionRing A K] in
/-- `M_k ⊆ t⁻ᵏ A`. -/
private theorem glueModule_le_span (ht0 : algebraMap A K t ≠ 0) (k : ℕ) :
    glueModule t k T C ≤ Submodule.span A {(algebraMap A K (t ^ k))⁻¹} := by
  intro x hx
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hx.1
  rw [Submodule.mem_span_singleton]
  refine ⟨a, ?_⟩
  rw [Algebra.smul_def, ha]
  have : algebraMap A K (t ^ k) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ ht0
  field_simp

/-- The module `M_k` is a finitely generated `A`-module. -/
private theorem glueModule_fg [IsDomain A] [IsNoetherianRing A] (ht0 : t ≠ 0) (k : ℕ) :
    (glueModule t k T C).FG := by
  have ht0' : algebraMap A K t ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht0)
  have : IsNoetherian A (Submodule.span A {(algebraMap A K (t ^ k))⁻¹}) :=
    isNoetherian_span_of_finite A (Set.finite_singleton _)
  have : IsNoetherian A (glueModule t k T C) := isNoetherian_of_le (glueModule_le_span ht0' k)
  exact Module.Finite.iff_fg.mp inferInstance

omit [IsFractionRing A K] in
/-- `(I • M) * (J • N) ⊆ (I * J) • (M * N)` for submodules of the `A`-algebra `K`. -/
private theorem mul_mem_smul_mul {I J : Ideal A} {M N : Submodule A K} {x y : K} (hx : x ∈ I • M)
    (hy : y ∈ J • N) : x * y ∈ (I * J) • (M * N) := by
  refine Submodule.smul_induction_on hx (fun a ha m hm ↦ ?_) (fun x x' h h' ↦ ?_)
  · refine Submodule.smul_induction_on hy (fun b hb n hn ↦ ?_) (fun y y' h h' ↦ ?_)
    · have : a • m * b • n = (a * b) • (m * n) := by
        rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]; ring
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.mul_mem_mul ha hb) (Submodule.mul_mem_mul hm hn)
    · rw [mul_add]; exact add_mem h h'
  · rw [add_mul]; exact add_mem h h'

omit [IsFractionRing A K] in
/-- If `N * N ≤ N`, then `A + N` is a subalgebra of `K`. -/
private def subalgebraOfMulLe (N : Submodule A K) (hN : N * N ≤ N) : Subalgebra A K :=
  Submodule.toSubalgebra (1 ⊔ N) (Submodule.mem_sup_left (Submodule.mem_one.mpr ⟨1, map_one _⟩))
    fun x y hx hy ↦ by
      have h : (1 ⊔ N) * (1 ⊔ N) ≤ 1 ⊔ N := by
        simp only [Submodule.sup_mul, Submodule.mul_sup, one_mul, mul_one]
        exact sup_le (sup_le le_sup_left le_sup_right) (sup_le le_sup_right (hN.trans le_sup_right))
      exact h (Submodule.mul_mem_mul hx hy)

omit [IsFractionRing A K] in
/-- Elements of `subalgebraOfMulLe N hN` are the sums `a + z` with `a ∈ A` and `z ∈ N`. -/
private theorem mem_subalgebraOfMulLe {N : Submodule A K} {hN : N * N ≤ N} {x : K} :
    x ∈ subalgebraOfMulLe N hN ↔ ∃ a : A, ∃ z ∈ N, x = algebraMap A K a + z := by
  change x ∈ (1 : Submodule A K) ⊔ N ↔ _
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hy
    exact ⟨a, z, hz, rfl⟩
  · rintro ⟨a, z, hz, rfl⟩
    exact ⟨_, Submodule.mem_one.mpr ⟨a, rfl⟩, z, hz, rfl⟩

end Construction

section Core

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {t : A} {T : Set (PrimeSpectrum A)} {C : PrimeSpectrum A → Subalgebra A K}

omit [IsDomain A] [IsNoetherianRing A] [IsFractionRing A K] in
/-- The maximal ideal of a two-dimensional local ring has height two. -/
private theorem maximalIdeal_height_eq_two (hdim : ringKrullDim A = 2) :
    (maximalIdeal A).height = 2 := by
  have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [hdim] at this
  exact WithBot.coe_eq_coe.mp (by rw [this]; rfl)

omit [IsNoetherianRing A] [IsFractionRing A K] in
/-- Away from the maximal ideal, `M_{2n}` and `M_n` agree after localization. -/
private theorem exists_smul_mem_glueModule_of_ne_maximalIdeal (hdim : ringKrullDim A = 2)
    (ht0 : t ≠ 0)
    (hTall : ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 → t ∈ q.asIdeal → q ∈ T) {n : ℕ}
    (hn : ∀ q ∈ T, ∀ x ∈ C q,
      algebraMap A K (t ^ n) * x ∈ locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K))
    {x : K} (hx : x ∈ glueModule t (n + n) T C) (p : Ideal A) [p.IsPrime]
    (hpm : p ≠ maximalIdeal A) : ∃ s ∉ p, s • x ∈ glueModule t n T C := by
  by_cases htp : t ∈ p
  · have hp0 : p ≠ ⊥ := fun h ↦ ht0 (by simpa [h] using htp)
    have hp1 := height_eq_one_of_ne_bot_of_ne_maximalIdeal hdim hp0 hpm
    have hT : (⟨p, ‹_›⟩ : PrimeSpectrum A) ∈ T := hTall ⟨p, ‹_›⟩ hp1 htp
    obtain ⟨s, hs, hsx⟩ := hn _ hT x (hx.2 _ hT)
    refine ⟨s, hs, ?_, fun q hq ↦ Subalgebra.smul_mem _ (hx.2 q hq) s⟩
    rw [Algebra.smul_def, mul_left_comm]
    exact hsx
  · refine ⟨t ^ n, fun h ↦ htp (‹p.IsPrime›.mem_of_pow_mem _ h), ?_,
      fun q hq ↦ Subalgebra.smul_mem _ (hx.2 q hq) _⟩
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, ← pow_add]
    exact hx.1

/-- Some power of `m` multiplies `M_{2n}` into `M_n` (`M_{2n} / M_n` is supported at `m`). -/
private theorem exists_pow_smul_glueModule_le (hdim : ringKrullDim A = 2) (ht0 : t ≠ 0)
    (hTall : ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 → t ∈ q.asIdeal → q ∈ T) {n : ℕ}
    (hn : ∀ q ∈ T, ∀ x ∈ C q,
      algebraMap A K (t ^ n) * x ∈ locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K)) :
    ∃ c : ℕ, maximalIdeal A ^ c • glueModule t (n + n) T C ≤ glueModule t n T C := by
  classical
  obtain ⟨G, hG⟩ := glueModule_fg (T := T) (C := C) (K := K) ht0 (n + n)
  set M := glueModule t n T C
  set J : Ideal A := G.inf (fun g ↦ M.colon {g})
  have hJ : ∀ s ∈ J, ∀ y ∈ glueModule t (n + n) T C, s • y ∈ M := by
    intro s hs y hy
    rw [← hG] at hy
    have hsub : Submodule.span A (G : Set K) ≤ M.comap (s • LinearMap.id) := by
      rw [Submodule.span_le]
      intro g hg
      have := (Finset.inf_le hg : J ≤ M.colon {g}) hs
      simpa using this
    exact hsub hy
  have hrad : maximalIdeal A ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun p ⟨hJp, hp⟩ ↦ ?_
    by_contra hpm
    have hpm' : p ≠ maximalIdeal A := fun h ↦ hpm (h ▸ le_rfl)
    obtain ⟨g, hg, hgp⟩ := (hp.inf_le').mp hJp
    have hgM : g ∈ glueModule t (n + n) T C := hG ▸ Submodule.subset_span hg
    obtain ⟨s, hs, hsg⟩ :=
      exists_smul_mem_glueModule_of_ne_maximalIdeal hdim ht0 hTall hn hgM p hpm'
    exact hs (hgp (Submodule.mem_colon_singleton.mpr hsg))
  obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  exact ⟨c, Submodule.smul_le.mpr fun r hr y hy ↦ hJ r (hc hr) y hy⟩

/-- The gluing construction when `T` is exactly the set of height-one primes containing `t`
(the case treated in Stacks 42.6.1); see `exists_glued_subalgebra` for a general finite `T`. -/
theorem exists_glued_subalgebra_core (hdim : ringKrullDim A = 2)
    (ht0 : t ≠ 0) (hTfin : T.Finite) (hTht : ∀ q ∈ T, q.asIdeal.height = 1)
    (htT : ∀ q ∈ T, t ∈ q.asIdeal)
    (hTall : ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 → t ∈ q.asIdeal → q ∈ T)
    (hC : ∀ q ∈ T, locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K) ≤ C q)
    (hCfin : ∀ q ∈ T, ∃ G : Finset K, ∀ x ∈ C q,
      x ∈ Submodule.span (locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K)) (G : Set K)) :
    ∃ (B : Subalgebra A K) (_ : IsLocalRing B) (_ : IsLocalHom (algebraMap A B)),
      Module.Finite A B ∧ Function.Bijective (ResidueField.map (algebraMap A B)) ∧
      (∀ q ∈ T, locInK q.asIdeal.primeCompl B = C q) ∧
      ∀ q : PrimeSpectrum A, t ∉ q.asIdeal →
        locInK q.asIdeal.primeCompl B = locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K) := by
  classical
  have ht0' : algebraMap A K t ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht0)
  -- a uniform power of `t` multiplying every `C q` into `A_q`
  have hex : ∀ q : PrimeSpectrum A, ∃ k : ℕ, q ∈ T → ∀ x ∈ C q,
      algebraMap A K (t ^ k) * x ∈ locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K) := by
    intro q
    by_cases hq : q ∈ T
    · obtain ⟨G, hG⟩ := hCfin q hq
      obtain ⟨k, hk⟩ := exists_pow_mul_mem_of_span (hTht q hq) (htT q hq) (C q : Set K) G hG
      exact ⟨k, fun _ ↦ hk⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose Nq hNq using hex
  set n := hTfin.toFinset.sup Nq
  have hn : ∀ q ∈ T, ∀ x ∈ C q,
      algebraMap A K (t ^ n) * x ∈ locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K) :=
    fun q hq x hx ↦ pow_mul_mem_of_le (Finset.le_sup (hTfin.mem_toFinset.mpr hq)) (hNq q hq x hx)
  obtain ⟨c, hc⟩ := exists_pow_smul_glueModule_le hdim ht0 hTall hn
  set m := maximalIdeal A
  set M := glueModule t n T C
  set N : Submodule A K := m ^ (c + 1) • M
  have hNM : N ≤ M := Submodule.smul_le_right
  have hNN : N * N ≤ m • N := by
    rw [Submodule.mul_le]
    intro x hx y hy
    have h2 : M * M ≤ glueModule t (n + n) T C :=
      Submodule.mul_le.mpr fun _ ha _ hb ↦ glueModule_mul_mem ha hb
    have h3 : (m ^ (c + 1) * m ^ (c + 1)) • (M * M) ≤ m • N :=
      calc (m ^ (c + 1) * m ^ (c + 1)) • (M * M)
          ≤ (m ^ (c + 1) * m ^ (c + 1)) • glueModule t (n + n) T C :=
            Submodule.smul_mono le_rfl h2
        _ = (m * m ^ (c + 1)) • (m ^ c • glueModule t (n + n) T C) := by
            rw [← Submodule.mul_smul]; congr 1; ring
        _ ≤ (m * m ^ (c + 1)) • M := Submodule.smul_mono le_rfl hc
        _ = m • N := Submodule.mul_smul _ _ _
    exact h3 (mul_mem_smul_mul hx hy)
  have hNN' : N * N ≤ N := hNN.trans Submodule.smul_le_right
  set B := subalgebraOfMulLe N hNN'
  have hmemB : ∀ x : K, x ∈ B ↔ ∃ a : A, ∃ z ∈ N, x = algebraMap A K a + z :=
    fun _ ↦ mem_subalgebraOfMulLe
  have hNB : ∀ z ∈ N, z ∈ B := fun z hz ↦ (hmemB _).mpr ⟨0, z, hz, by simp⟩
  -- finiteness
  have hfin : Module.Finite A B := by
    have hle : Subalgebra.toSubmodule B ≤ Submodule.span A {(algebraMap A K (t ^ n))⁻¹} := by
      intro x hx
      obtain ⟨a, z, hz, rfl⟩ := (hmemB _).mp hx
      refine add_mem ?_ (glueModule_le_span ht0' n (hNM hz))
      rw [Submodule.mem_span_singleton]
      refine ⟨a * t ^ n, ?_⟩
      have : algebraMap A K (t ^ n) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ ht0'
      rw [Algebra.smul_def, map_mul]
      field_simp
    have : IsNoetherian A (Submodule.span A {(algebraMap A K (t ^ n))⁻¹}) :=
      isNoetherian_span_of_finite A (Set.finite_singleton _)
    have : IsNoetherian A (Subalgebra.toSubmodule B) := isNoetherian_of_le hle
    exact (inferInstance : Module.Finite A (Subalgebra.toSubmodule B))
  -- maximal ideals of `B` contain `m` and `N`
  have hPm : ∀ P : Ideal B, P.IsMaximal → ∀ a ∈ m, algebraMap A B a ∈ P := by
    intro P hP a ha
    have hmax : (P.comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    have h := IsLocalRing.eq_maximalIdeal hmax
    have : a ∈ P.comap (algebraMap A B) := by rw [h]; exact ha
    exact this
  have hPN : ∀ P : Ideal B, P.IsMaximal → ∀ z (hz : z ∈ N), (⟨z, hNB z hz⟩ : B) ∈ P := by
    intro P hP z hz
    have hmN : ∀ w ∈ m • N, ∃ hw : w ∈ B, (⟨w, hw⟩ : B) ∈ P := by
      intro w hw
      refine Submodule.smul_induction_on hw (fun a ha y hy ↦ ⟨Subalgebra.smul_mem _ (hNB y hy) a,
        ?_⟩) (fun w w' ⟨h, h'⟩ ⟨k, k'⟩ ↦ ⟨add_mem h k, ?_⟩)
      · have : (⟨a • y, Subalgebra.smul_mem _ (hNB y hy) a⟩ : B) =
            algebraMap A B a * ⟨y, hNB y hy⟩ := Subtype.ext (by simp [Algebra.smul_def])
        rw [this]
        exact P.mul_mem_right _ (hPm P hP a ha)
      · exact P.add_mem h' k'
    obtain ⟨_, hw⟩ := hmN _ (hNN (Submodule.mul_mem_mul hz hz))
    exact (hP.isPrime.mem_or_mem hw).elim id id
  have hdecomp : ∀ b : B, ∃ a : A, ∃ z, ∃ hz : z ∈ N, b = algebraMap A B a + ⟨z, hNB z hz⟩ := by
    intro b
    obtain ⟨a, z, hz, hb⟩ := (hmemB _).mp b.2
    exact ⟨a, z, hz, Subtype.ext (by simpa using hb)⟩
  have hle : ∀ P P' : Ideal B, P.IsMaximal → P'.IsMaximal → P ≤ P' := by
    intro P P' hP hP' b hb
    obtain ⟨a, z, hz, rfl⟩ := hdecomp b
    have haP : algebraMap A B a ∈ P := by
      have := P.sub_mem hb (hPN P hP z hz)
      simpa using this
    have ham : a ∈ m := le_maximalIdeal (Ideal.comap_ne_top _ hP.ne_top) haP
    exact P'.add_mem (hPm P' hP' a ham) (hPN P' hP' z hz)
  have hlocal : IsLocalRing B := by
    refine IsLocalRing.of_unique_max_ideal ?_
    obtain ⟨P, hP⟩ := Ideal.exists_maximal B
    exact ⟨P, hP, fun P' hP' ↦ hP'.eq_of_le hP.ne_top (hle P' P hP' hP)⟩
  have hlh : IsLocalHom (algebraMap A B) := by
    refine ⟨fun a ha ↦ ?_⟩
    by_contra hna
    exact (IsLocalRing.mem_maximalIdeal _).mp
      (hPm _ inferInstance a ((IsLocalRing.mem_maximalIdeal _).mpr hna)) ha
  refine ⟨B, hlocal, hlh, hfin, ⟨(ResidueField.map (algebraMap A B)).injective, ?_⟩, ?_, ?_⟩
  · -- residue fields
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, z, hz, rfl⟩ := hdecomp b
    refine ⟨residue A a, ?_⟩
    rw [ResidueField.map_residue]
    change residue B _ = residue B _
    rw [map_add, (residue_eq_zero_iff _).mpr (hPN _ inferInstance z hz), add_zero]
  · -- localization at `q ∈ T`
    intro q hq
    have hqm : q.asIdeal ≠ m := by
      intro h
      have := hTht q hq
      rw [h, maximalIdeal_height_eq_two hdim] at this
      exact absurd this (by decide)
    ext x
    constructor
    · rintro ⟨s, hs, hsx⟩
      obtain ⟨a, z, hz, hsxe⟩ := (hmemB _).mp hsx
      have hsC : algebraMap A K s * x ∈ C q := by
        rw [hsxe]
        exact add_mem (Subalgebra.algebraMap_mem _ a) ((hNM hz).2 q hq)
      have hs0 : algebraMap A K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero fun h ↦ hs (h ▸ q.asIdeal.zero_mem))
      have hinv : (algebraMap A K s)⁻¹ ∈ C q :=
        hC q hq ⟨s, hs, by rw [mul_inv_cancel₀ hs0]; exact Subalgebra.one_mem _⟩
      have := Subalgebra.mul_mem _ hinv hsC
      rwa [← mul_assoc, inv_mul_cancel₀ hs0, one_mul] at this
    · intro hx
      -- an element `s ∉ q` with `s • x ∈ M`
      let I0 : Ideal A := (Subalgebra.toSubmodule (⊥ : Subalgebra A K)).colon
        {algebraMap A K (t ^ n) * x}
      let Iq : PrimeSpectrum A → Ideal A := fun q' ↦ (Subalgebra.toSubmodule (C q')).colon {x}
      have hI0 : ¬ I0 ≤ q.asIdeal := by
        obtain ⟨s, hs, hsx⟩ := hn q hq x hx
        intro h
        exact hs (h (Submodule.mem_colon_singleton.mpr (by rwa [Algebra.smul_def])))
      have hIq : ∀ q' ∈ hTfin.toFinset, ¬ Iq q' ≤ q.asIdeal := by
        intro q' hq' h
        rw [Set.Finite.mem_toFinset] at hq'
        by_cases hqq : q = q'
        · subst hqq
          exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr
            (h (Submodule.mem_colon_singleton.mpr (by simpa using hx))))
        · have hne : q.asIdeal ≠ q'.asIdeal := fun h' ↦ hqq (PrimeSpectrum.ext h')
          obtain ⟨s, hs, hsx⟩ :=
            exists_primeCompl_mul_mem_locInK (K := K) (hTht q hq) (hTht q' hq') hne x
          exact hs (h (Submodule.mem_colon_singleton.mpr
            (by rw [Algebra.smul_def]; exact hC q' hq' hsx)))
      have hJ : ¬ I0 ⊓ hTfin.toFinset.inf Iq ≤ q.asIdeal := by
        rw [q.isPrime.inf_le, q.isPrime.inf_le']
        push Not
        exact ⟨hI0, hIq⟩
      obtain ⟨s, hsJ, hsq⟩ := SetLike.not_le_iff_exists.mp hJ
      have hsM : s • x ∈ M := by
        refine ⟨?_, fun q' hq' ↦ ?_⟩
        · have := Submodule.mem_colon_singleton.mp (Ideal.mem_inf.mp hsJ).1
          rw [Algebra.smul_def] at this ⊢
          rwa [mul_left_comm]
        · have := (Finset.inf_le (hTfin.mem_toFinset.mpr hq') : hTfin.toFinset.inf Iq ≤ Iq q')
            (Ideal.mem_inf.mp hsJ).2
          exact Submodule.mem_colon_singleton.mp this
      have hmq : ¬ m ^ (c + 1) ≤ q.asIdeal := fun h ↦
        hqm (le_antisymm (le_maximalIdeal q.isPrime.ne_top) (q.isPrime.le_of_pow_le h))
      obtain ⟨a, ham, haq⟩ := SetLike.not_le_iff_exists.mp hmq
      refine ⟨a * s, fun h ↦ (q.isPrime.mem_or_mem h).elim haq hsq, hNB _ ?_⟩
      have : algebraMap A K (a * s) * x = a • (s • x) := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
      rw [this]
      exact Submodule.smul_mem_smul ham hsM
  · -- localization away from `t`
    intro q htq
    ext x
    constructor
    · rintro ⟨s, hs, hsx⟩
      obtain ⟨a, z, hz, hsxe⟩ := (hmemB _).mp hsx
      refine ⟨t ^ n * s, fun h ↦ (q.isPrime.mem_or_mem h).elim
        (fun h' ↦ htq (q.isPrime.mem_of_pow_mem _ h')) hs, ?_⟩
      rw [map_mul, mul_assoc, hsxe, mul_add]
      exact add_mem (by rw [← map_mul]; exact Subalgebra.algebraMap_mem _ _) (hNM hz).1
    · rintro ⟨s, hs, hsx⟩
      exact ⟨s, hs, (bot_le : (⊥ : Subalgebra A K) ≤ B) hsx⟩

omit [IsLocalRing A] [IsFractionRing A K] in
/-- In a Noetherian domain, only finitely many height-one primes contain a nonzero element. -/
theorem finite_setOf_height_eq_one_mem {s : A} (hs : s ≠ 0) :
    {q : PrimeSpectrum A | q.asIdeal.height = 1 ∧ s ∈ q.asIdeal}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {s})).preimage
    (Function.Injective.injOn (fun _ _ h ↦ PrimeSpectrum.ext h))).subset ?_
  rintro q ⟨hq1, hsq⟩
  refine ⟨⟨q.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hsq⟩, fun P ⟨hP, hsP⟩ hPq ↦ ?_⟩
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hs (by simpa using hsP (Ideal.mem_span_singleton_self s))
  exact (eq_of_le_of_height_eq_one_of_ne_bot hq1 hPq hP0).ge

/-- **Gluing lemma (Stacks 42.6.1).** Let `(A, m)` be a two-dimensional Noetherian local domain
with fraction field `K`, `t ∈ A` nonzero, `T` a finite set of height-one primes and, for `q ∈ T`,
`C q` a subalgebra of `K` containing `A_q` and contained in a finitely generated `A_q`-submodule
of `K`. Then there is a subalgebra `B` of `K`, finite over `A`, local, with the residue field map
`κ(A) → κ(B)` bijective, whose localization at `A \ q` (inside `K`) is `C q` for `q ∈ T` and is
`A_q` for every height-one prime `q ∉ T` with `t ∉ q`. -/
theorem exists_glued_subalgebra (hdim : ringKrullDim A = 2) (ht0 : t ≠ 0) (hTfin : T.Finite)
    (hTht : ∀ q ∈ T, q.asIdeal.height = 1)
    (hC : ∀ q ∈ T, locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K) ≤ C q)
    (hCfin : ∀ q ∈ T, ∃ G : Finset K, ∀ x ∈ C q,
      x ∈ Submodule.span (locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K)) (G : Set K)) :
    ∃ (B : Subalgebra A K) (_ : IsLocalRing B) (_ : IsLocalHom (algebraMap A B)),
      Module.Finite A B ∧ Function.Bijective (ResidueField.map (algebraMap A B)) ∧
      (∀ q ∈ T, locInK q.asIdeal.primeCompl B = C q) ∧
      ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 → q ∉ T → t ∉ q.asIdeal →
        locInK q.asIdeal.primeCompl B = locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K) := by
  classical
  have hX : ∀ q : PrimeSpectrum A, ∃ x : A, q ∈ T → x ∈ q.asIdeal ∧ x ≠ 0 := by
    intro q
    by_cases hq : q ∈ T
    · obtain ⟨x, hx, hx0⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.ne_bot_of_height_eq_one (hTht q hq))
      exact ⟨x, fun _ ↦ ⟨hx, hx0⟩⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose X hX using hX
  set s := t * ∏ q ∈ hTfin.toFinset, X q
  have hs0 : s ≠ 0 := mul_ne_zero ht0 (Finset.prod_ne_zero_iff.mpr fun q hq ↦
    (hX q (hTfin.mem_toFinset.mp hq)).2)
  have hsT : ∀ q ∈ T, s ∈ q.asIdeal := fun q hq ↦ q.asIdeal.mul_mem_left _
    (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (hTfin.mem_toFinset.mpr hq)) (hX q hq).1)
  set T' := {q : PrimeSpectrum A | q.asIdeal.height = 1 ∧ s ∈ q.asIdeal}
  let C' : PrimeSpectrum A → Subalgebra A K := fun q ↦
    if q ∈ T then C q else locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K)
  obtain ⟨B, hBl, hBh, hBfin, hBres, hBT, hBt⟩ := exists_glued_subalgebra_core (C := C') hdim hs0
    (finite_setOf_height_eq_one_mem hs0) (fun q hq ↦ hq.1) (fun q hq ↦ hq.2)
    (fun q hq1 hsq ↦ ⟨hq1, hsq⟩)
    (fun q _ ↦ by
      by_cases hq : q ∈ T
      · simpa [C', hq] using hC q hq
      · simp [C', hq])
    (fun q _ ↦ by
      by_cases hq : q ∈ T
      · simpa [C', hq] using hCfin q hq
      · refine ⟨{1}, fun x hx ↦ ?_⟩
        simp only [C', hq, if_false] at hx
        have : x = (⟨x, hx⟩ : locInK q.asIdeal.primeCompl (⊥ : Subalgebra A K)) • (1 : K) := by
          simp [Subalgebra.smul_def]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  refine ⟨B, hBl, hBh, hBfin, hBres, fun q hq ↦ ?_, fun q hq1 hqT htq ↦ ?_⟩
  · simpa [C', hq] using hBT q ⟨hTht q hq, hsT q hq⟩
  · by_cases hsq : s ∈ q.asIdeal
    · simpa [C', hqT] using hBT q ⟨hq1, hsq⟩
    · exact hBt q hsq

end Core

section Correspondence

variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- The inclusion of `B` into its localization `locInK S B` inside `K`. -/
noncomputable instance algebraLocInK (S : Submonoid A) (B : Subalgebra A K) :
    Algebra B (locInK S B) :=
  (Subalgebra.inclusion (le_locInK S B)).toRingHom.toAlgebra

omit [IsDomain A] [IsFractionRing A K] in
/-- The inclusion `B → locInK S B` is the identity on underlying elements of `K`. -/
@[simp]
theorem coe_algebraMap_locInK (S : Submonoid A) (B : Subalgebra A K) (b : B) :
    ((algebraMap B (locInK S B) b : locInK S B) : K) = b := rfl

/-- An element of `S` maps outside every proper ideal of `locInK S B` (it is a unit there). -/
private theorem algebraMap_notMem_of_mem {S : Submonoid A} (hS : S ≤ nonZeroDivisors A)
    {B : Subalgebra A K} (P : Ideal (locInK S B)) (hP : P ≠ ⊤) {s : A} (hs : s ∈ S) :
    algebraMap A (locInK S B) s ∉ P := by
  intro h
  have hs0 : algebraMap A K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
  have hinv : (algebraMap A K s)⁻¹ ∈ locInK S B :=
    ⟨s, hs, by rw [mul_inv_cancel₀ hs0]; exact Subalgebra.one_mem _⟩
  refine hP ((Ideal.eq_top_iff_one _).mpr ?_)
  have := P.mul_mem_left ⟨_, hinv⟩ h
  convert this using 1
  exact Subtype.ext (by simp [inv_mul_cancel₀ hs0])

/-- `locInK S B` is the localization of `B` at the image of `S`, for the inclusion algebra. -/
theorem isLocalization_locInK (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)
    (B : Subalgebra A K) :
    IsLocalization (Algebra.algebraMapSubmonoid B S) (locInK S B) := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, s, hs, rfl⟩
    have hs0 : algebraMap A K s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
    have hinv : (algebraMap A K s)⁻¹ ∈ locInK S B :=
      ⟨s, hs, by rw [mul_inv_cancel₀ hs0]; exact Subalgebra.one_mem _⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    change algebraMap A K s * (algebraMap A K s)⁻¹ = 1
    exact mul_inv_cancel₀ hs0
  · rintro ⟨x, s, hs, hsx⟩
    refine ⟨(⟨_, hsx⟩, ⟨algebraMap A B s, s, hs, rfl⟩), Subtype.ext ?_⟩
    change x * algebraMap A K s = algebraMap A K s * x
    ring
  · intro x y h
    exact ⟨1, by simpa using Subalgebra.inclusion_injective _ h⟩

omit [IsFractionRing A K] in
/-- In an integral extension of domains, a prime lying over a height-one prime has height
one. -/
theorem height_eq_one_of_height_comap_eq_one {R : Type*} [CommRing R] [IsDomain R] [Algebra A R]
    [Algebra.IsIntegral A R] (hinj : Function.Injective (algebraMap A R)) (Q : Ideal R)
    [Q.IsPrime] (hQ : (Q.comap (algebraMap A R)).height = 1) : Q.height = 1 := by
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    rw [Ideal.comap_bot_of_injective _ hinj] at hQ
    simp at hQ
  refine le_antisymm ?_ (Order.one_le_iff_ne_zero.mpr fun h ↦
    hQ0 (Ideal.height_eq_zero_iff_eq_bot.mp h))
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
  intro P hP hPQ
  have hlt := Ideal.IsIntegral.comap_lt_comap (R := A) hPQ
  have hP0 : P.comap (algebraMap A R) = ⊥ := by
    by_contra h
    exact hlt.ne (eq_of_le_of_height_eq_one_of_ne_bot hQ hlt.le h)
  rw [Ideal.IsIntegral.eq_bot_of_comap_eq_bot A hP0, Ideal.height_bot]
  exact zero_lt_one

/-- Height-one primes of `B` over a height-one prime `q` of `A` correspond to the maximal ideals
of the localization `C = (A \ q)⁻¹ B` (inside `K`), with the same local rings inside `K`. -/
theorem exists_equiv_maximalSpectrum_locInK (B : Subalgebra A K) [Module.Finite A B]
    (q : Ideal A) [q.IsPrime] (hq : q.height = 1) (C : Subalgebra A K)
    (hBC : locInK q.primeCompl B = C) :
    ∃ e : {Q : PrimeSpectrum B // Q.asIdeal.height = 1 ∧
        Q.asIdeal.comap (algebraMap A B) = q} ≃ MaximalSpectrum C,
      ∀ Q, localizationAt B Q.1.asIdeal = localizationAt C (e Q).asIdeal := by
  subst hBC
  have hS : q.primeCompl ≤ nonZeroDivisors A := fun s hs ↦
    mem_nonZeroDivisors_of_ne_zero fun h ↦ hs (h ▸ q.zero_mem)
  have hinj : Function.Injective (algebraMap A B) := fun a b h ↦
    IsFractionRing.injective A K (by simpa using congrArg Subtype.val h)
  set C := locInK q.primeCompl B
  set M := Algebra.algebraMapSubmonoid B q.primeCompl
  have hloc : IsLocalization M C := isLocalization_locInK q.primeCompl hS B
  let φ := IsLocalization.orderIsoOfPrime M C
  have hφ : ∀ P, (φ P).1 = P.1.comap (algebraMap B C) := fun _ ↦ rfl
  have hdisj : ∀ Q : Ideal B, Q.comap (algebraMap A B) ≤ q → Disjoint (M : Set B) Q := by
    intro Q hQ
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsQ
    exact hs (hQ hsQ)
  have hdisj' : ∀ Q : Ideal B, Disjoint (M : Set B) Q → Q.comap (algebraMap A B) ≤ q := by
    intro Q hQ a ha
    by_contra hna
    exact Set.disjoint_left.mp hQ ⟨a, hna, rfl⟩ ha
  -- maximality of the ideal corresponding to a prime over `q`
  have hmax : ∀ Q : Ideal B, ∀ hQ : Q.IsPrime, ∀ hQq : Q.comap (algebraMap A B) = q,
      (φ.symm ⟨Q, hQ, hdisj Q hQq.le⟩).1.IsMaximal := by
    intro Q hQ hQq
    obtain ⟨P'', hP'', hle⟩ := Ideal.exists_le_maximal (φ.symm ⟨Q, hQ, hdisj Q hQq.le⟩).1
      (φ.symm ⟨Q, hQ, hdisj Q hQq.le⟩).2.ne_top
    have hle' : φ.symm ⟨Q, hQ, hdisj Q hQq.le⟩ ≤ ⟨P'', hP''.isPrime⟩ := hle
    rw [← φ.le_iff_le, φ.apply_symm_apply] at hle'
    have hQ2 := (φ ⟨P'', hP''.isPrime⟩).2
    have hcomap : (φ ⟨P'', hP''.isPrime⟩).1.comap (algebraMap A B) = q :=
      le_antisymm (hdisj' _ hQ2.2) (hQq ▸ Ideal.comap_mono hle')
    have heq : Q = (φ ⟨P'', hP''.isPrime⟩).1 := by
      by_contra hne
      have := Ideal.IsIntegral.comap_lt_comap (R := A) (lt_of_le_of_ne hle' hne)
      rw [hQq, hcomap] at this
      exact this.ne rfl
    have : φ.symm ⟨Q, hQ, hdisj Q hQq.le⟩ = ⟨P'', hP''.isPrime⟩ := by
      rw [OrderIso.symm_apply_eq]
      exact Subtype.ext heq
    rw [this]
    exact hP''
  -- the inverse direction
  have hinv : ∀ P : MaximalSpectrum C, (φ ⟨P.asIdeal, inferInstance⟩).1.height = 1 ∧
      (φ ⟨P.asIdeal, inferInstance⟩).1.comap (algebraMap A B) = q := by
    intro P
    set Q := (φ ⟨P.asIdeal, inferInstance⟩)
    obtain ⟨Q₀, -, hQ₀, hQ₀q⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) q ⊥
      (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
    have hQ0 : Q.1 ≠ ⊥ := by
      intro h0
      have hle : Q ≤ ⟨Q₀, hQ₀, hdisj Q₀ hQ₀q.le⟩ := by
        change Q.1 ≤ Q₀
        rw [h0]; exact bot_le
      rw [← φ.apply_symm_apply ⟨Q₀, hQ₀, hdisj Q₀ hQ₀q.le⟩, φ.le_iff_le] at hle
      have hPeq : P.asIdeal = (φ.symm ⟨Q₀, hQ₀, hdisj Q₀ hQ₀q.le⟩).1 :=
        P.isMaximal.eq_of_le (φ.symm _).2.ne_top hle
      have : Q₀ = ⊥ := by
        have h1 : φ ⟨P.asIdeal, inferInstance⟩ = ⟨Q₀, hQ₀, hdisj Q₀ hQ₀q.le⟩ := by
          rw [← φ.apply_symm_apply ⟨Q₀, hQ₀, hdisj Q₀ hQ₀q.le⟩]
          congr 1
          exact Subtype.ext hPeq
        rw [← h0]
        exact (congrArg Subtype.val h1).symm
      rw [this, Ideal.comap_bot_of_injective _ hinj] at hQ₀q
      exact Ideal.ne_bot_of_height_eq_one hq hQ₀q.symm
    have := Q.2.1
    have hcomap : Q.1.comap (algebraMap A B) = q :=
      eq_of_le_of_height_eq_one_of_ne_bot (hq := hq) (hdisj' _ Q.2.2)
        (Ideal.IsIntegral.comap_ne_bot A hQ0)
    exact ⟨height_eq_one_of_height_comap_eq_one hinj _ (by rw [hcomap]; exact hq), hcomap⟩
  refine ⟨{
    toFun := fun Q ↦ ⟨(φ.symm ⟨Q.1.asIdeal, Q.1.isPrime, hdisj _ Q.2.2.le⟩).1,
      hmax Q.1.asIdeal Q.1.isPrime Q.2.2⟩
    invFun := fun P ↦ ⟨⟨(φ ⟨P.asIdeal, inferInstance⟩).1, (φ ⟨P.asIdeal, inferInstance⟩).2.1⟩,
      hinv P⟩
    left_inv := fun Q ↦ by
      apply Subtype.ext
      apply PrimeSpectrum.ext
      change (φ (φ.symm _)).1 = _
      rw [φ.apply_symm_apply]
    right_inv := fun P ↦ by
      apply MaximalSpectrum.ext
      change (φ.symm (φ _)).1 = _
      rw [φ.symm_apply_apply] }, fun Q ↦ ?_⟩
  -- equality of the local rings
  set P := (φ.symm ⟨Q.1.asIdeal, Q.1.isPrime, hdisj _ Q.2.2.le⟩).1
  have hPQ : P.comap (algebraMap B C) = Q.1.asIdeal := by
    rw [← hφ, φ.apply_symm_apply]
  have hPtop : P ≠ ⊤ := (φ.symm ⟨Q.1.asIdeal, Q.1.isPrime, hdisj _ Q.2.2.le⟩).2.ne_top
  have : P.IsPrime := (φ.symm ⟨Q.1.asIdeal, Q.1.isPrime, hdisj _ Q.2.2.le⟩).2
  change localizationAt B Q.1.asIdeal = localizationAt C P
  ext x
  constructor
  · rintro ⟨s, hs, hsx⟩
    refine ⟨algebraMap B C s, fun h ↦ hs ?_, le_locInK _ B hsx⟩
    rw [← hPQ]
    exact h
  · rintro ⟨s', hs', hsx⟩
    obtain ⟨σ, hσ, hσs⟩ := s'.2
    obtain ⟨σ', hσ', hσx⟩ := hsx
    refine ⟨⟨_, hσs⟩ * algebraMap A B σ', ?_, ?_⟩
    · rw [← hPQ, Ideal.mem_comap, map_mul]
      have h1 : algebraMap B C ⟨_, hσs⟩ = algebraMap A C σ * s' := Subtype.ext rfl
      have h2 : algebraMap B C (algebraMap A B σ') = algebraMap A C σ' := Subtype.ext rfl
      rw [h1, h2]
      intro h
      rcases this.mem_or_mem h with h | h
      · rcases this.mem_or_mem h with h | h
        · exact algebraMap_notMem_of_mem hS P hPtop hσ h
        · exact hs' h
      · exact algebraMap_notMem_of_mem hS P hPtop hσ' h
    · have : ((⟨_, hσs⟩ * algebraMap A B σ' : B) : K) * x =
          algebraMap A K σ * (algebraMap A K σ' * ((s' : K) * x)) := by
        simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
        ring
      rw [this]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hσx

omit [IsDomain A] [IsFractionRing A K] in
/-- The localization of a local subalgebra `C` of `K` at its own maximal ideal is `C` itself. -/
theorem localizationAt_maximalIdeal_eq_self (C : Subalgebra A K) [IsLocalRing C] :
    localizationAt C (IsLocalRing.maximalIdeal C) = C := by
  refine le_antisymm ?_ (le_localizationAt C _)
  rintro x ⟨s, hs, hsx⟩
  obtain ⟨u, hu⟩ := IsLocalRing.notMem_maximalIdeal.mp hs
  have hinv : (u⁻¹.val : K) * (s : K) = 1 := by
    rw [← hu]
    exact congrArg (fun c : C ↦ (c : K)) u.inv_mul
  have hxeq : x = (u⁻¹.val : K) * ((s : K) * x) := by rw [← mul_assoc, hinv, one_mul]
  rw [hxeq]
  exact C.mul_mem u⁻¹.val.2 hsx

/-- If `(A \ q)⁻¹ B = A_q` for a height-one prime `q` of `A` (this is clause (d) of
`exists_glued_subalgebra`, applied to a height-one prime `q ∉ T` with `t ∉ q`), then the
height-one prime of `B` lying over `q` is unique, and its local ring inside `K` is `A_q`. -/
theorem exists_unique_height_one_prime_localizationAt_eq_locInK_bot
    (B : Subalgebra A K) [Module.Finite A B] (q : Ideal A) [q.IsPrime] (hq : q.height = 1)
    (hBq : locInK q.primeCompl B = locInK q.primeCompl (⊥ : Subalgebra A K)) :
    ∃! Q : {Q : PrimeSpectrum B // Q.asIdeal.height = 1 ∧
        Q.asIdeal.comap (algebraMap A B) = q},
      localizationAt B Q.1.asIdeal = locInK q.primeCompl (⊥ : Subalgebra A K) := by
  obtain ⟨e, he⟩ :=
    exists_equiv_maximalSpectrum_locInK B q hq (locInK q.primeCompl (⊥ : Subalgebra A K)) hBq
  have hS : q.primeCompl ≤ nonZeroDivisors A := fun s hs ↦
    mem_nonZeroDivisors_of_ne_zero fun h ↦ hs (h ▸ q.zero_mem)
  have hloc : locInK q.primeCompl (⊥ : Subalgebra A K) =
      Localization.subalgebra.ofField K q.primeCompl hS := locInK_bot_eq_ofField q.primeCompl hS
  have hAt : IsLocalization.AtPrime (locInK q.primeCompl (⊥ : Subalgebra A K)) q := by
    rw [hloc]; infer_instance
  have : IsLocalRing (locInK q.primeCompl (⊥ : Subalgebra A K)) :=
    IsLocalization.AtPrime.isLocalRing _ q
  refine ⟨e.symm default, ?_, fun Q _ ↦ ?_⟩
  · change localizationAt B (e.symm default).1.asIdeal = locInK q.primeCompl (⊥ : Subalgebra A K)
    rw [he, Equiv.apply_symm_apply]
    exact localizationAt_maximalIdeal_eq_self _
  · apply e.injective
    rw [Equiv.apply_symm_apply]
    exact Subsingleton.elim _ _

end Correspondence

section Consequences

variable {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] {K : Type*} [Field K]
  [Algebra A K] [IsFractionRing A K]

omit [IsLocalRing A] in
/-- The structure map `A → B` of a subalgebra `B` of `K` is injective. -/
theorem algebraMap_subalgebra_injective (B : Subalgebra A K) :
    Function.Injective (algebraMap A B) := fun a b h ↦
  IsFractionRing.injective A K (by simpa using congrArg Subtype.val h)

omit [IsLocalRing A] in
/-- A subalgebra of `K` finite over the two-dimensional domain `A` has dimension two. -/
theorem ringKrullDim_eq_two_of_finite (hdim : ringKrullDim A = 2) (B : Subalgebra A K)
    [Module.Finite A B] : ringKrullDim B = 2 := by
  have : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr (algebraMap_subalgebra_injective B)
  rw [ringKrullDim_eq_of_isIntegral A B, hdim]

/-- If `B ⊆ K` is local and finite over the two-dimensional local domain `A`, then every
height-one prime of `B` contracts to a height-one prime of `A`. -/
theorem height_comap_eq_one (hdim : ringKrullDim A = 2) (B : Subalgebra A K) [IsLocalRing B]
    [Module.Finite A B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height = 1) :
    (Q.comap (algebraMap A B)).height = 1 := by
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hQ
  refine height_eq_one_of_ne_bot_of_ne_maximalIdeal hdim (Ideal.IsIntegral.comap_ne_bot A hQ0) ?_
  intro hm
  have : Q.IsMaximal :=
    Ideal.IsIntegral.isMaximal_of_isMaximal_comap Q (by rw [hm]; infer_instance)
  have hQm := IsLocalRing.eq_maximalIdeal this
  have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B)
  rw [← hQm, hQ, ringKrullDim_eq_two_of_finite hdim B] at h2
  exact absurd h2 (by decide)

/-- With `T` the set of height-one primes of `A` containing `t`, a height-one prime `Q` of `B`
contracts into `T` exactly when `t ∈ Q`. -/
theorem comap_mem_heightOneSet_iff (hdim : ringKrullDim A = 2) (B : Subalgebra A K) [IsLocalRing B]
    [Module.Finite A B] {t : A} {T : Set (PrimeSpectrum A)}
    (hT : ∀ q : PrimeSpectrum A, q ∈ T ↔ q.asIdeal.height = 1 ∧ t ∈ q.asIdeal)
    (Q : PrimeSpectrum B) (hQ : Q.asIdeal.height = 1) :
    PrimeSpectrum.comap (algebraMap A B) Q ∈ T ↔ algebraMap A B t ∈ Q.asIdeal := by
  rw [hT]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨height_comap_eq_one hdim B Q.asIdeal hQ, h⟩⟩

end Consequences

end GromovWitten.Algebra.Tame
