/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The affine moving lemma for rational sections

This file proves the commutative-algebra input to Fulton's Theorem 2.4: given a line bundle on an
affine integral scheme and finitely many codimension-one points, one can find a rational section
whose local coordinate is a unit at each of the given points. Concretely, let `A` be a Noetherian
domain with fraction field `K`, let `q₁, …, qₘ` be finitely many distinct nonzero prime ideals of
`A` such that each localisation `A_{qᵢ}` has Krull dimension `1`, and let `u₁, …, uₘ` be units of
`K`. Then there is a unit `f` of `K` such that `f * uᵢ` is a unit of `A_{qᵢ}` for every `i`. This is
the moving lemma used to reduce the descent of the first Chern class to the case where a Cartier
divisor has no component in common with the finitely many subvarieties being avoided.

## Main results

* `GromovWitten.Algebra.exists_unit_mul_isUnit_atPrime`: the moving lemma above.

## Proof strategy

We write each `uᵢ = aᵢ / bᵢ` with `aᵢ, bᵢ ∈ A` nonzero. The key local input
(`exists_unit_of_sub_mem`) shows that in a Noetherian local domain of dimension at most `1` with
maximal ideal `𝔪`, for a nonzero element `a` there is `N` such that any `c` congruent to `a` modulo
`𝔪 ^ (N + 1)` is an associate of `a`. Since the `qᵢ` are pairwise distinct primes all of whose
localisations have dimension `1`, they are pairwise incomparable, so their images in the
semilocalisation `S` of `A` at the complement of `⋃ qᵢ` are pairwise distinct maximal ideals, hence
pairwise coprime. The Chinese remainder theorem in `S` produces elements approximating the `aᵢ`
and `bᵢ` simultaneously modulo high powers of the `qᵢ`, and unwinding these congruences back to `A`
and applying the local input at each `qᵢ` produces the desired `f`.
-/

open Ideal IsLocalization Function

namespace GromovWitten.Algebra

/-- In a Noetherian local domain `D` of Krull dimension at most `1` with maximal ideal `𝔪`, for any
nonzero `a` there is `N` such that every `c` congruent to `a` modulo `𝔪 ^ (N + 1)` is an associate
of `a`, i.e. `c = a * w` for some unit `w`. This is the key local input to the moving lemma: it
lets us perturb the "denominator" `a` by high `𝔪`-adic order and stay a unit multiple of `a`. -/
theorem exists_unit_of_sub_mem {D : Type*} [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [IsLocalRing D] (hD : Ring.KrullDimLE 1 D) (a : D) (ha : a ≠ 0) :
    ∃ N : ℕ, ∀ c : D, c - a ∈ IsLocalRing.maximalIdeal D ^ (N + 1) →
      ∃ w : Dˣ, c = a * (w : D) := by
  have := hD
  set 𝔪 := IsLocalRing.maximalIdeal D
  have hrad : 𝔪 ≤ (Ideal.span {a}).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro P ⟨haP, hP⟩
    by_contra hlt
    have hPmax : P ≤ 𝔪 := IsLocalRing.le_maximalIdeal hP.ne_top
    have hne : P ≠ 𝔪 := fun h => hlt (h ▸ le_refl _)
    have hPlt : P < 𝔪 := lt_of_le_of_ne hPmax hne
    have haP0 : a ∈ P := haP (Ideal.mem_span_singleton_self a)
    have hPbot : (⊥ : Ideal D) < P := by
      rw [bot_lt_iff_ne_bot]; intro h; apply ha; rw [h] at haP0; simpa using haP0
    have h1 : (⊥ : Ideal D).height + 1 ≤ P.height :=
      Ideal.height_add_one_le_of_lt_of_isPrime hPbot
    have h2 : P.height + 1 ≤ 𝔪.height := Ideal.height_add_one_le_of_lt_of_isPrime hPlt
    rw [Ideal.height_bot] at h1
    have hkrull : (𝔪.height : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
      rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
      exact Ring.krullDimLE_iff.mp inferInstance
    have hkrull' : 𝔪.height ≤ (1 : ℕ∞) := by exact_mod_cast hkrull
    have hge : (2 : ℕ∞) ≤ 𝔪.height := by
      calc (2:ℕ∞) = (0+1)+1 := by norm_num
      _ ≤ P.height + 1 := by gcongr
      _ ≤ 𝔪.height := h2
    have hcontra : (2 : ℕ∞) ≤ (1 : ℕ∞) := hge.trans hkrull'
    norm_num at hcontra
  have hfg : 𝔪.FG := IsNoetherian.noetherian 𝔪
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfg
  refine ⟨n, fun c hc => ?_⟩
  have hpow : 𝔪 ^ (n + 1) ≤ 𝔪 * Ideal.span {a} := by
    rw [pow_succ']; exact Ideal.mul_mono_right hn
  have hc' := hpow hc
  rw [mul_comm] at hc'
  obtain ⟨z, hz, hz'⟩ := Ideal.mem_span_singleton_mul.mp hc'
  have hunit : IsUnit (1 + z) := by
    have hnu : z ∈ nonunits D := hz
    have hnu' : (-z) ∈ nonunits D := by simpa [nonunits, IsUnit.neg_iff] using hnu
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-z) hnu'
    simpa using this
  refine ⟨hunit.unit, ?_⟩
  change c = a * (1 + z)
  have hc2 : c = a + a * z := by linear_combination -hz'
  rw [hc2]; ring

/-- Subtracting the image of an "integral" element `y` from a fraction `mk' S x s` with denominator
`s` amounts to changing the numerator to `x - y * s`. -/
theorem mk'_sub_algebraMap {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M : Submonoid R} [IsLocalization M S] (x y : R) (s : M) :
    IsLocalization.mk' S (x - y * s) s = IsLocalization.mk' S x s - algebraMap R S y := by
  rw [IsLocalization.mk'_eq_iff_eq_mul, sub_mul, IsLocalization.mk'_spec, ← map_mul, ← map_sub]

/-- The image under a fraction field map of the inverse of a unit is the inverse of the image. -/
theorem algebraMap_val_inv {D K : Type*} [CommRing D] [Field K] [Algebra D K] [IsDomain D]
    [IsFractionRing D K] (V : Dˣ) :
    algebraMap D K ((V⁻¹ : Dˣ) : D) = (algebraMap D K (V : D))⁻¹ := by
  have heq : algebraMap D K (V : D) * algebraMap D K ((V⁻¹ : Dˣ) : D) = 1 := by
    rw [← map_mul]; norm_cast; simp
  exact (DivisionMonoid.inv_eq_of_mul _ _ heq).symm

/-- If `X - Y * E ∈ I` for a unit `E`, then dividing the first term by `E` still lands in `I`. -/
theorem divide_by_unit_mem {D : Type*} [CommRing D] (I : Ideal D) (X Y : D) (E : Dˣ)
    (h : X - Y * E ∈ I) : X * ((E⁻¹ : Dˣ) : D) - Y ∈ I := by
  have hEE : (E : D) * ((E⁻¹ : Dˣ) : D) = 1 := by exact_mod_cast E.mul_inv
  have key : X * ((E⁻¹ : Dˣ) : D) - Y = ((E⁻¹ : Dˣ) : D) * (X - Y * E) := by
    linear_combination Y * hEE
  rw [key]; exact I.mul_mem_left _ h

section Semilocal

variable {A : Type*} [CommRing A] [IsDomain A] {ι : Type*} [Finite ι] (q : ι → Ideal A)
  [hqp : ∀ i, (q i).IsPrime]

/-- The submonoid of elements of `A` avoiding every `q i`. -/
noncomputable abbrev SemilocalSubmonoid : Submonoid A := ⨅ i, (q i).primeCompl

/-- The semilocalisation of `A` at the complement of the union of the `q i`. -/
noncomputable abbrev Semilocalization := Localization (SemilocalSubmonoid q)

noncomputable instance instCommRingSemilocalization : CommRing (Semilocalization q) := by
  unfold Semilocalization; infer_instance

noncomputable instance instAlgebraSemilocalization : Algebra A (Semilocalization q) := by
  unfold Semilocalization; infer_instance

instance instIsLocalizationSemilocalization :
    IsLocalization (SemilocalSubmonoid q) (Semilocalization q) := by
  unfold Semilocalization; infer_instance

omit [IsDomain A] [Finite ι] in
/-- The submonoid avoiding every `q i` is disjoint from `q i` for each `i`. -/
theorem disjoint_semilocalSubmonoid (i : ι) :
    Disjoint ((SemilocalSubmonoid q : Submonoid A) : Set A) (q i : Set A) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have : x ∈ (q i).primeCompl := (iInf_le (fun i => (q i).primeCompl) i) hx
  exact this hx'

/-- The extension of `q i` to the semilocalisation. -/
noncomputable abbrev extendedPrime (i : ι) : Ideal (Semilocalization q) :=
  (q i).map (algebraMap A (Semilocalization q))

omit [IsDomain A] [Finite ι] in
/-- The extension of `q i` to the semilocalisation is prime. -/
theorem isPrime_extendedPrime (i : ι) : (extendedPrime q i).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (SemilocalSubmonoid q) (Semilocalization q) (q i)
    inferInstance (disjoint_semilocalSubmonoid q i)

omit [IsDomain A] [Finite ι] in
/-- The extension of `q i` to the semilocalisation lies over `q i`. -/
theorem under_extendedPrime (i : ι) : (extendedPrime q i).under A = q i :=
  IsLocalization.under_map_of_isPrime_disjoint (SemilocalSubmonoid q) (Semilocalization q)
    inferInstance (disjoint_semilocalSubmonoid q i)

omit [IsDomain A] [Finite ι] in
/-- Extension of primes to the semilocalisation is injective on the `q i`. -/
theorem extendedPrime_injective (hqinj : Function.Injective q) (i j : ι)
    (h : extendedPrime q i = extendedPrime q j) : i = j := by
  apply hqinj
  rw [← under_extendedPrime q i, ← under_extendedPrime q j, h]

/-- Under the dimension hypothesis, the extension of `q i` to the semilocalisation is maximal:
any prime avoiding every `qⱼ` and containing `qᵢ` must equal `qᵢ`, since a strictly larger such
prime would witness `Aq_j` having dimension at least `2` for some `j`. -/
theorem isMaximal_extendedPrime (hdim : ∀ i, Ring.KrullDimLE 1 (Localization.AtPrime (q i)))
    (hq0 : ∀ i, q i ≠ ⊥) (hqinj : Function.Injective q) (i : ι) :
    (extendedPrime q i).IsMaximal := by
  have := isPrime_extendedPrime q i
  obtain ⟨m, hm, hle⟩ := (extendedPrime q i).exists_le_maximal (IsPrime.ne_top inferInstance)
  have hdisj : Disjoint (SemilocalSubmonoid q : Set A) ((m.under A : Ideal A) : Set A) :=
    (IsLocalization.disjoint_under_iff (SemilocalSubmonoid q) (Semilocalization q) m).mpr
      hm.ne_top
  have hsub : (m.under A : Set A) ⊆ ⋃ j, (q j : Set A) := by
    intro x hx
    by_contra hxc
    simp only [Set.mem_iUnion, not_exists] at hxc
    have hxM : x ∈ SemilocalSubmonoid q := Submonoid.mem_iInf.mpr fun j => hxc j
    exact (Set.disjoint_left.mp hdisj) hxM hx
  have hsub' :
      ((m.under A : Ideal A) : Set A) ⊆ ⋃ j ∈ (Set.univ : Set ι), (q j : Set A) := by
    intro x hx
    simpa using hsub hx
  obtain ⟨j, -, hj⟩ := (Ideal.subset_union_prime_finite Set.finite_univ i i
    (fun k _ _ _ => hqp k)).mp hsub'
  have hqi_le : q i ≤ m.under A := (under_extendedPrime q i) ▸ Ideal.comap_mono hle
  have hqi_le_qj : q i ≤ q j := hqi_le.trans hj
  by_cases hji : j = i
  · rw [hji] at hj
    have heq : m.under A = q i := le_antisymm hj hqi_le
    have hmap : m = Ideal.map (algebraMap A (Semilocalization q)) (m.under A) :=
      (IsLocalization.map_under (SemilocalSubmonoid q) (Semilocalization q) m).symm
    rw [heq] at hmap
    change (Ideal.map (algebraMap A (Semilocalization q)) (q i)).IsMaximal
    rw [← hmap]
    exact hm
  · exfalso
    have hqij : q i ≠ q j := fun h => hji (hqinj h).symm
    have hlt : q i < q j := lt_of_le_of_ne hqi_le_qj hqij
    have h1 : (⊥ : Ideal A).height + 1 ≤ (q i).height :=
      Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr (hq0 i))
    have h2 : (q i).height + 1 ≤ (q j).height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [Ideal.height_bot] at h1
    have hkrull : ((q j).height : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
      rw [← IsLocalization.AtPrime.ringKrullDim_eq_height (q j) (Localization.AtPrime (q j))]
      exact Ring.krullDimLE_iff.mp (hdim j)
    have hkrull' : (q j).height ≤ (1 : ℕ∞) := by exact_mod_cast hkrull
    have hge : (2 : ℕ∞) ≤ (q j).height := by
      calc (2:ℕ∞) = (0+1)+1 := by norm_num
      _ ≤ (q i).height + 1 := by gcongr
      _ ≤ (q j).height := h2
    have hcontra : (2 : ℕ∞) ≤ (1 : ℕ∞) := hge.trans hkrull'
    norm_num at hcontra

end Semilocal

/-- **The affine moving lemma for rational sections** (Fulton's Theorem 2.4, moving step). Let `A`
be a Noetherian domain, `q : ι → Ideal A` a finite family of pairwise distinct nonzero primes such
that `Localization.AtPrime (q i)` has Krull dimension `1` for every `i`, and `u : ι → Kˣ` a family
of units of `K := FractionRing A`. Then there is `f : Kˣ` such that for every `i`, `f * u i` is a
unit of `Localization.AtPrime (q i)`. -/
theorem exists_unit_mul_isUnit_atPrime {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {ι : Type*} [Finite ι] (q : ι → Ideal A) [∀ i, (q i).IsPrime]
    (hq0 : ∀ i, q i ≠ ⊥) (hqinj : Function.Injective q)
    (hdim : ∀ i, Ring.KrullDimLE 1 (Localization.AtPrime (q i)))
    (u : ι → (FractionRing A)ˣ) :
    ∃ f : (FractionRing A)ˣ, ∀ i, ∃ v : (Localization.AtPrime (q i))ˣ,
      algebraMap (Localization.AtPrime (q i)) (FractionRing A) v = f * u i := by
  rcases isEmpty_or_nonempty ι with hem | hne
  · exact ⟨1, fun i => hem.elim i⟩
  set K := FractionRing A
  -- Step 1: write `u i = aA i / bA i` with `aA i, bA i ≠ 0`.
  have hfrac : ∀ i, ∃ a b : A, a ≠ 0 ∧ b ≠ 0 ∧ (u i : K) = algebraMap A K a / algebraMap A K b := by
    intro i
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := A) (K := K) (u i : K)
    have hbne : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    refine ⟨a, b, ?_, hbne, hab.symm⟩
    intro ha0
    apply (u i).ne_zero
    rw [← hab, ha0, map_zero, zero_div]
  choose aA bA haA hbA hu using hfrac
  -- Step 2: choose a single exponent `N i` that works for both `aA i` and `bA i`.
  have hkey : ∀ i, ∃ N : ℕ,
      (∀ c : Localization.AtPrime (q i), c - algebraMap A _ (aA i) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime (q i)) ^ (N + 1) →
        ∃ w : (Localization.AtPrime (q i))ˣ, c = algebraMap A _ (aA i) * (w : _)) ∧
      (∀ c : Localization.AtPrime (q i), c - algebraMap A _ (bA i) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime (q i)) ^ (N + 1) →
        ∃ w : (Localization.AtPrime (q i))ˣ, c = algebraMap A _ (bA i) * (w : _)) := by
    intro i
    have hinj : Function.Injective (algebraMap A (Localization.AtPrime (q i))) :=
      IsLocalization.injective _ (q i).primeCompl_le_nonZeroDivisors
    have haAne : algebraMap A (Localization.AtPrime (q i)) (aA i) ≠ 0 := by
      rw [map_ne_zero_iff _ hinj]; exact haA i
    have hbAne : algebraMap A (Localization.AtPrime (q i)) (bA i) ≠ 0 := by
      rw [map_ne_zero_iff _ hinj]; exact hbA i
    obtain ⟨Na, hNa⟩ := exists_unit_of_sub_mem (hdim i) _ haAne
    obtain ⟨Nb, hNb⟩ := exists_unit_of_sub_mem (hdim i) _ hbAne
    refine ⟨max Na Nb, ?_, ?_⟩
    · intro c hc
      exact hNa c (Ideal.pow_le_pow_right (Nat.succ_le_succ (le_max_left Na Nb)) hc)
    · intro c hc
      exact hNb c (Ideal.pow_le_pow_right (Nat.succ_le_succ (le_max_right Na Nb)) hc)
  choose N hNa hNb using hkey
  -- Step 3: the extended primes to the appropriate power are pairwise coprime.
  have hcop : Pairwise (IsCoprime on fun i => (extendedPrime q i) ^ (N i + 1)) := by
    intro i j hij
    have hmax_i := isMaximal_extendedPrime q hdim hq0 hqinj i
    have hmax_j := isMaximal_extendedPrime q hdim hq0 hqinj j
    have hne' : extendedPrime q i ≠ extendedPrime q j :=
      fun h => hij (extendedPrime_injective q hqinj i j h)
    exact (isCoprime_of_isMaximal (I := extendedPrime q i) (J := extendedPrime q j) hne').pow
  -- Step 4: Chinese remainder theorem, applied to the `aA` and to the `bA` separately.
  obtain ⟨c, hc⟩ := Ideal.exists_forall_sub_mem_ideal hcop
    (fun i => algebraMap A (Semilocalization q) (aA i))
  obtain ⟨d, hd⟩ := Ideal.exists_forall_sub_mem_ideal hcop
    (fun i => algebraMap A (Semilocalization q) (bA i))
  -- Step 5: pick fraction representatives with a denominator avoiding every `q i`.
  obtain ⟨a', s, hs⟩ := IsLocalization.exists_mk'_eq (SemilocalSubmonoid q) c
  obtain ⟨b', t, ht⟩ := IsLocalization.exists_mk'_eq (SemilocalSubmonoid q) d
  -- Step 6: unwind a congruence modulo `(extendedPrime q i) ^ (N i + 1)` in the semilocalisation
  -- down to a unit-multiple relation in `K`, absorbing the extra denominators as units of
  -- `Localization.AtPrime (q i)` along the way. This is applied to both the `aA`- and
  -- `bA`-congruences below.
  have hunfold : ∀ (x' : A) (r : SemilocalSubmonoid q) (xA : ι → A)
      (hcong : ∀ i, IsLocalization.mk' (Semilocalization q) x' r -
        algebraMap A (Semilocalization q) (xA i) ∈ (extendedPrime q i) ^ (N i + 1)) (i : ι)
      (hxne : algebraMap A (Localization.AtPrime (q i)) (xA i) ≠ 0)
      (hloc : ∀ c : Localization.AtPrime (q i), c - algebraMap A _ (xA i) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime (q i)) ^ (N i + 1) →
        ∃ w : (Localization.AtPrime (q i))ˣ, c = algebraMap A _ (xA i) * (w : _)),
      ∃ V : (Localization.AtPrime (q i))ˣ, algebraMap A K x' =
        algebraMap A K (xA i) * algebraMap (Localization.AtPrime (q i)) K V := by
    intro x' r xA hcong i hxne hloc
    have hcongi := hcong i
    rw [← mk'_sub_algebraMap] at hcongi
    have hpoweq : ((q i) ^ (N i + 1)).map (algebraMap A (Semilocalization q)) =
        (extendedPrime q i) ^ (N i + 1) := Ideal.map_pow _ (q i) (N i + 1)
    rw [← hpoweq] at hcongi
    obtain ⟨s', hs'mem, hs'⟩ := (IsLocalization.mk'_mem_map_algebraMap_iff
      (SemilocalSubmonoid q) (Semilocalization q) ((q i) ^ (N i + 1)) _ r).mp hcongi
    set D := Localization.AtPrime (q i)
    have hmapeq : (q i).map (algebraMap A D) = IsLocalRing.maximalIdeal D :=
      IsLocalization.AtPrime.map_eq_maximalIdeal (q i) D
    have hmemq : algebraMap A D (s' * (x' - xA i * r)) ∈
        IsLocalRing.maximalIdeal D ^ (N i + 1) := by
      rw [← hmapeq, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem (algebraMap A D) hs'
    have hexpand : algebraMap A D (s' * (x' - xA i * r)) =
        algebraMap A D (s' * x') - algebraMap A D (xA i) * algebraMap A D (s' * (r : A)) := by
      push_cast; ring
    rw [hexpand] at hmemq
    have hEunit : IsUnit (algebraMap A D (s' * (r : A))) :=
      IsLocalization.map_units D ⟨s' * (r : A), (q i).primeCompl.mul_mem
        ((iInf_le (fun i => (q i).primeCompl) i) hs'mem)
        ((iInf_le (fun i => (q i).primeCompl) i) r.2)⟩
    set E := hEunit.unit
    have hEspec : (E : D) = algebraMap A D (s' * (r : A)) := hEunit.unit_spec
    have hdiv := divide_by_unit_mem (IsLocalRing.maximalIdeal D ^ (N i + 1))
      (algebraMap A D (s' * x')) (algebraMap A D (xA i)) E (by rw [hEspec]; exact hmemq)
    obtain ⟨w, hw⟩ := hloc _ hdiv
    have hVeq : algebraMap A D (s' * x') = algebraMap A D (xA i) * ((w * E : Dˣ) : D) := by
      have hE2 : ((E⁻¹ : Dˣ) : D) * (E : D) = 1 := by exact_mod_cast E.inv_mul
      calc algebraMap A D (s' * x') = algebraMap A D (s' * x') * ((E⁻¹ : Dˣ) : D) * (E : D) := by
              rw [mul_assoc, hE2, mul_one]
        _ = algebraMap A D (xA i) * (w : D) * (E : D) := by rw [hw]
        _ = algebraMap A D (xA i) * ((w * E : Dˣ) : D) := by rw [Units.val_mul]; ring
    have hpush : algebraMap A K (s' * x') =
        algebraMap A K (xA i) * algebraMap D K ((w * E : Dˣ) : D) := by
      have hcast1 : algebraMap A K (s' * x') = algebraMap D K (algebraMap A D (s' * x')) := by
        rw [← IsScalarTower.algebraMap_apply]
      have hcast2 : algebraMap A K (xA i) = algebraMap D K (algebraMap A D (xA i)) := by
        rw [← IsScalarTower.algebraMap_apply]
      rw [hcast1, hcast2, hVeq, map_mul]
    have hTunit : IsUnit (algebraMap A D s') :=
      IsLocalization.map_units D ⟨s', (iInf_le (fun i => (q i).primeCompl) i) hs'mem⟩
    set T := hTunit.unit
    have hTspec : (T : D) = algebraMap A D s' := hTunit.unit_spec
    have hTmap : algebraMap A K s' = algebraMap D K (T : D) := by
      rw [hTspec, ← IsScalarTower.algebraMap_apply]
    have hTne : algebraMap D K (T : D) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective D K)]; exact T.ne_zero
    refine ⟨w * E * T⁻¹, ?_⟩
    have hsplit : algebraMap A K (s' * x') = algebraMap A K s' * algebraMap A K x' :=
      map_mul _ _ _
    rw [hsplit, hTmap] at hpush
    have hfinal : algebraMap A K x' = algebraMap A K (xA i) *
        algebraMap D K ((w * E : Dˣ) : D) / algebraMap D K (T : D) := by
      rw [eq_div_iff hTne]
      linear_combination hpush
    rw [hfinal, div_eq_mul_inv, ← algebraMap_val_inv, mul_assoc, ← map_mul]
    congr 2
  -- Step 7: apply the unwinding to the `aA`- and `bA`-congruences.
  have hCa : ∀ i, ∃ V : (Localization.AtPrime (q i))ˣ, algebraMap A K a' =
      algebraMap A K (aA i) * algebraMap (Localization.AtPrime (q i)) K V := by
    intro i
    have hinj : Function.Injective (algebraMap A (Localization.AtPrime (q i))) :=
      IsLocalization.injective _ (q i).primeCompl_le_nonZeroDivisors
    have haAne : algebraMap A (Localization.AtPrime (q i)) (aA i) ≠ 0 := by
      rw [map_ne_zero_iff _ hinj]; exact haA i
    exact hunfold a' s aA (fun j => hs ▸ hc j) i haAne (hNa i)
  have hCb : ∀ i, ∃ V : (Localization.AtPrime (q i))ˣ, algebraMap A K b' =
      algebraMap A K (bA i) * algebraMap (Localization.AtPrime (q i)) K V := by
    intro i
    have hinj : Function.Injective (algebraMap A (Localization.AtPrime (q i))) :=
      IsLocalization.injective _ (q i).primeCompl_le_nonZeroDivisors
    have hbAne : algebraMap A (Localization.AtPrime (q i)) (bA i) ≠ 0 := by
      rw [map_ne_zero_iff _ hinj]; exact hbA i
    exact hunfold b' t bA (fun j => ht ▸ hd j) i hbAne (hNb i)
  -- Step 8: assemble `f := b' / a'` and the witnessing unit at each `i`.
  obtain ⟨i0⟩ := hne
  have hCane : algebraMap A K a' ≠ 0 := by
    obtain ⟨V, hV⟩ := hCa i0
    rw [hV]
    have h1 : algebraMap A K (aA i0) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective A K)]; exact haA _
    have h2 : algebraMap (Localization.AtPrime (q i0)) K (V : Localization.AtPrime (q i0)) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime (q i0)) K)]
      exact V.ne_zero
    exact mul_ne_zero h1 h2
  have hCbne : algebraMap A K b' ≠ 0 := by
    obtain ⟨V, hV⟩ := hCb i0
    rw [hV]
    have h1 : algebraMap A K (bA i0) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective A K)]; exact hbA _
    have h2 : algebraMap (Localization.AtPrime (q i0)) K (V : Localization.AtPrime (q i0)) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime (q i0)) K)]
      exact V.ne_zero
    exact mul_ne_zero h1 h2
  refine ⟨Units.mk0 _ (div_ne_zero hCbne hCane), fun i => ?_⟩
  obtain ⟨V, hV⟩ := hCa i
  obtain ⟨W, hW⟩ := hCb i
  refine ⟨W * V⁻¹, ?_⟩
  have haAmap : algebraMap A K (aA i) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective A K)]; exact haA i
  have hVmap : algebraMap (Localization.AtPrime (q i)) K (V : Localization.AtPrime (q i)) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime (q i)) K)]
    exact V.ne_zero
  have hfu : (Units.mk0 _ (div_ne_zero hCbne hCane) : K) * (u i : K) =
      algebraMap A K b' / algebraMap A K a' * (algebraMap A K (aA i) / algebraMap A K (bA i)) := by
    rw [Units.val_mk0, hu i]
  have hbAmap : algebraMap A K (bA i) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective A K)]; exact hbA i
  rw [hfu, hV, hW, Units.val_mul, map_mul, algebraMap_val_inv]
  field_simp
  ring

end GromovWitten.Algebra
