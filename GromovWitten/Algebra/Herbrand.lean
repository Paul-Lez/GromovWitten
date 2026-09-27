/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalOrdSymmetry
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Algebra.Exact.Basic
import Mathlib.Data.ENat.BigOperators

/-!
# Periodic complexes and Herbrand quotients

We formalise Sections 42.2 and 42.3 of the Stacks Project (Chapter "Chow Homology"):
`(2,1)`-periodic complexes `(M, φ, ψ)` over a commutative ring, their cohomology modules
`H⁰ = ker φ / im ψ` and `H¹ = ker ψ / im φ`, and the multiplicity (additive Herbrand quotient)
`e(M, φ, ψ) = length H⁰ - length H¹`.

## Main definitions

* `GromovWitten.Algebra.relLen A B`: the length of the subquotient `B ⧸ (A ∩ B)` of a module.
* `GromovWitten.Algebra.PeriodicComplex`: a `(2,1)`-periodic complex; `H0`, `H1`,
  `FiniteCohomology` (both cohomology modules have finite length) and `herbrand` (the
  multiplicity, an integer; it is only meaningful under `FiniteCohomology`).
* `PeriodicComplex.Hom`: morphisms of periodic complexes, with the induced maps `mapH0`, `mapH1`
  and, for a short exact sequence, the connecting map `Hom.connecting : H⁰(E) → H¹(C)`.
* `PeriodicComplex.smulComplex M x`: the complex `(M, 0, x)`; `smulLeft`, `smulRight`: the
  complexes `(M, xφ, ψ)` and `(M, φ, xψ)`; `powComplex`: `(M, φ^i, φ^(n-i))` when `φ^n = 0`;
  `powComplex'`: `(M, φ^i, φ^j)` when `φ^(i+j) = 0`.
* `PeriodicComplex.pi`: the product of a family of periodic complexes.

## Main results

* `herbrand_add_of_exact_of_outer`, `herbrand_add_of_exact_of_left`,
  `herbrand_add_of_exact_of_right` (Stacks, Lemma 42.2.3): for a short exact sequence
  `0 → C → D → E → 0` of periodic complexes, if two of the three have finite cohomology so does the
  third, and `e(D) = e(C) + e(E)`. The proof goes through the exactness of the six-term cyclic
  cohomology sequence (`Hom.exact_mapH0`, `Hom.exact_connecting_left`,
  `Hom.exact_connecting_right`).
* `herbrand_eq_zero_of_length_ne_top` (Stacks, Lemma 42.2.4, `(2,1)` case): on a module of finite
  length, the cohomology is finite and `e = 0`; `herbrand_eq_zero_of_exact`: an exact complex has
  `e = 0`; `herbrand_prod`, `herbrand_pi`: `e` is additive on binary and finite products.
* `finiteCohomology_congr`, `herbrand_congr`: a linear isomorphism intertwining the differentials
  preserves finiteness of cohomology and `e`; `herbrand_smulComplex_congr` and
  `herbrand_smulComplex_submodule_congr` are the special cases for `(M, 0, x)`.
* `finiteCohomology_iff_of_hom`, `herbrand_eq_of_hom` (Stacks, Lemma 42.2.5): a morphism with
  finite-length kernel and cokernel preserves and reflects finiteness of cohomology, and
  preserves `e`.
* `herbrand_smulComplex`: `e(M, 0, x) = length (M ⧸ xM) - length (ker x)`, i.e.
  `chiCoker x M - chiKer x M` in the notation of `LocalOrdSymmetry`.
* `herbrand_powComplex` (Stacks, Lemma 42.3.3): if `φ^n = 0`, `n > 0` and `ker φ / im φ^(n-1)` has
  finite length, then `(M, φ^i, φ^(n-i))` has finite cohomology and `e = 0` for `i ≤ n`;
  `herbrand_powComplex'`: the same for `(M, φ^i, φ^j)` with `φ^(i+j) = 0`.
* `herbrand_smulLeft`, `herbrand_smulRight` (Stacks, Lemma 42.3.4): over a Noetherian local ring,
  for `M` finite with `(M, φ, ψ)` of finite cohomology and `M ⧸ xM` of finite length,
  `e(M, xφ, ψ) = e(M, φ, ψ) - e(im φ, 0, x)` and `e(M, φ, xψ) = e(M, φ, ψ) + e(im ψ, 0, x)`
  (with all the finiteness statements).
* `herbrand_smulComplex_quotient` (Stacks, Lemma 42.3.1, cyclic case with support `{q, m}`):
  `e(A ⧸ J, 0, x) = ord_{A ⧸ q}(x) · length_{A_q}((A ⧸ J)_q)` for `A` Noetherian local, `q` a
  non-maximal prime, every prime containing `J` equal to `q` or `m`, and `x ∉ q`.
-/

namespace GromovWitten.Algebra

open GromovWitten.AlgebraicGeometry.IntersectionTheory

section RelLen

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The length of the subquotient `B ⧸ (A ∩ B)` of `M`, written as
`B ⧸ A.comap B.subtype`. For `A ≤ B` this is the length of the interval `[A, B]`. -/
noncomputable def relLen (A B : Submodule R M) : ℕ∞ :=
  Module.length R (B ⧸ A.comap B.subtype)

/-- `relLen A B` is the length of the image of `B` in `M ⧸ A`. -/
theorem relLen_eq_length_map (A B : Submodule R M) :
    relLen A B = Module.length R (B.map A.mkQ) := by
  have hker : LinearMap.ker (A.mkQ ∘ₗ B.subtype) = A.comap B.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range (A.mkQ ∘ₗ B.subtype) = B.map A.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [relLen, ← hker, ← hrange]
  exact (LinearMap.quotKerEquivRange _).length_eq

/-- `relLen A A = 0`. -/
theorem relLen_self (A : Submodule R M) : relLen A A = 0 := by
  rw [relLen, Submodule.comap_subtype_self]
  exact Module.length_eq_zero

/-- `relLen A B = 0` when `B ≤ A`. -/
theorem relLen_eq_zero_of_le {A B : Submodule R M} (h : B ≤ A) : relLen A B = 0 := by
  have : A.comap B.subtype = ⊤ := eq_top_iff.2 fun b _ ↦ h b.2
  rw [relLen, this]
  exact Module.length_eq_zero

/-- `relLen A ⊤` is the length of `M ⧸ A`. -/
theorem relLen_top (A : Submodule R M) : relLen A ⊤ = Module.length R (M ⧸ A) := by
  rw [relLen_eq_length_map, Submodule.map_top, Submodule.range_mkQ, Module.length_top]

/-- `relLen ⊥ B` is the length of `B`. -/
theorem relLen_bot (B : Submodule R M) : relLen ⊥ B = Module.length R B := by
  rw [relLen, Submodule.comap_bot, Submodule.ker_subtype]
  exact (Submodule.quotEquivOfEqBot _ rfl).length_eq

/-- For `A ≤ B`, `length B = length A + relLen A B`. -/
theorem length_eq_add_relLen {A B : Submodule R M} (h : A ≤ B) :
    Module.length R B = Module.length R A + relLen A B := by
  rw [Module.length_eq_add_of_exact (A.comap B.subtype).subtype (A.comap B.subtype).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _), LocalOrdSymmetry.length_comap_subtype,
    inf_eq_right.2 h, relLen]

/-- Invariance of `relLen` under a linear map which is injective on `B` modulo `A`. -/
theorem relLen_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    {A B : Submodule R M} (hAB : A ≤ B) (hker : LinearMap.ker f ⊓ B ≤ A) :
    relLen A B = relLen (A.map f) (B.map f) := by
  set S := (A.map f).comap (B.map f).subtype
  set h : B →ₗ[R] (B.map f ⧸ S) := S.mkQ ∘ₗ f.submoduleMap B with hh
  have hsurj : Function.Surjective h :=
    (Submodule.mkQ_surjective S).comp (LinearMap.submoduleMap_surjective f B)
  have hkerh : LinearMap.ker h = A.comap B.subtype := by
    ext ⟨b, hb⟩
    simp only [hh, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, S, LinearMap.submoduleMap_coe_apply, Submodule.mem_map]
    constructor
    · rintro ⟨a, ha, hfa⟩
      have hd : b - a ∈ LinearMap.ker f ⊓ B :=
        Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hfa, sub_self]),
          B.sub_mem hb (hAB ha)⟩
      have := A.add_mem (hker hd) ha
      rwa [sub_add_cancel] at this
    · intro hbA
      exact ⟨b, hbA, rfl⟩
  rw [relLen, relLen, ← hkerh]
  exact (LinearMap.quotKerEquivOfSurjective h hsurj).length_eq

/-- Additivity of `relLen` along a chain `A ≤ B ≤ C`. -/
theorem relLen_add {A B C : Submodule R M} (hAB : A ≤ B) (hBC : B ≤ C) :
    relLen A C = relLen A B + relLen B C := by
  rw [relLen_eq_length_map A C, relLen_eq_length_map A B,
    relLen_map A.mkQ hBC (by rw [Submodule.ker_mkQ]; exact inf_le_left.trans hAB)]
  exact length_eq_add_relLen (Submodule.map_mono hBC)

/-- Second isomorphism theorem for `relLen`. -/
theorem relLen_inf_eq_relLen_sup (B X : Submodule R M) :
    relLen (B ⊓ X) B = relLen X (B ⊔ X) := by
  have e := LinearMap.quotientInfEquivSupQuotient B X
  have h1 : Submodule.comap B.subtype B ⊓ Submodule.comap B.subtype X
      = (B ⊓ X).comap B.subtype := by
    rw [Submodule.comap_subtype_self, top_inf_eq, Submodule.comap_inf,
      Submodule.comap_subtype_self, top_inf_eq]
  rw [relLen, relLen, ← h1]
  exact e.length_eq

/-- Monotonicity of `relLen` in a chain `A ≤ A' ≤ B' ≤ B`. -/
theorem relLen_le_relLen {A A' B' B : Submodule R M} (h1 : A ≤ A') (h2 : A' ≤ B')
    (h3 : B' ≤ B) : relLen A' B' ≤ relLen A B := by
  rw [relLen_add h1 (h2.trans h3), relLen_add h2 h3]
  exact le_self_add.trans le_add_self

/-- Telescoping `relLen` along an increasing chain. -/
theorem relLen_eq_sum_of_monotone (X : ℕ → Submodule R M) (hX : Monotone X) (a k : ℕ) :
    relLen (X a) (X (a + k)) = ∑ m ∈ Finset.range k, relLen (X (a + m)) (X (a + m + 1)) := by
  induction k with
  | zero => simp [relLen_self]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, ← add_assoc]
    exact relLen_add (hX (by omega)) (hX (by omega))

/-- Telescoping `relLen` along a decreasing chain. -/
theorem relLen_eq_sum_of_antitone (U : ℕ → Submodule R M) (hU : Antitone U) (a k : ℕ) :
    relLen (U (a + k)) (U a) = ∑ m ∈ Finset.range k, relLen (U (a + m + 1)) (U (a + m)) := by
  induction k with
  | zero => simp [relLen_self]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, add_comm (relLen _ _), ← add_assoc]
    exact relLen_add (hU (by omega)) (hU (by omega))

end RelLen

section SixTerm

variable {R : Type*} [CommRing R]
variable {A₀ B₀ C₀ A₁ B₁ C₁ : Type*} [AddCommGroup A₀] [Module R A₀] [AddCommGroup B₀]
  [Module R B₀] [AddCommGroup C₀] [Module R C₀] [AddCommGroup A₁] [Module R A₁]
  [AddCommGroup B₁] [Module R B₁] [AddCommGroup C₁] [Module R C₁]

/-- For an exact pair `u, v`, the length of the middle term is the sum of the lengths of the
images of `u` and `v`. -/
theorem length_eq_range_add_range_of_exact {X Y Z : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] (u : X →ₗ[R] Y)
    (v : Y →ₗ[R] Z) (h : Function.Exact u v) :
    Module.length R Y = Module.length R (LinearMap.range u)
      + Module.length R (LinearMap.range v) := by
  rw [LocalOrdSymmetry.length_eq_ker_add_range v, LinearMap.exact_iff.1 h]

/-- Lengths along a cyclic exact sequence
`A₀ → B₀ → C₀ → A₁ → B₁ → C₁ → A₀` decompose as sums of lengths of the images. -/
theorem exists_lengths_of_cyclic_exact (f₁ : A₀ →ₗ[R] B₀) (g₁ : B₀ →ₗ[R] C₀)
    (d₀ : C₀ →ₗ[R] A₁) (f₂ : A₁ →ₗ[R] B₁) (g₂ : B₁ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] A₀)
    (e₁ : Function.Exact f₁ g₁) (e₂ : Function.Exact g₁ d₀) (e₃ : Function.Exact d₀ f₂)
    (e₄ : Function.Exact f₂ g₂) (e₅ : Function.Exact g₂ d₁) (e₆ : Function.Exact d₁ f₁) :
    ∃ i₁ j₁ k₁ i₂ j₂ k₂ : ℕ∞, Module.length R A₀ = i₁ + j₁ ∧ Module.length R B₀ = j₁ + k₁ ∧
      Module.length R C₀ = k₁ + i₂ ∧ Module.length R A₁ = i₂ + j₂ ∧
      Module.length R B₁ = j₂ + k₂ ∧ Module.length R C₁ = k₂ + i₁ := by
  exact ⟨_, _, _, _, _, _, length_eq_range_add_range_of_exact _ _ e₆,
    length_eq_range_add_range_of_exact _ _ e₁, length_eq_range_add_range_of_exact _ _ e₂,
    length_eq_range_add_range_of_exact _ _ e₃, length_eq_range_add_range_of_exact _ _ e₄,
    length_eq_range_add_range_of_exact _ _ e₅⟩

/-- Arithmetic of a cyclic six-term decomposition: two-out-of-three finiteness. -/
private theorem sixTerm_finite {a₀ b₀ c₀ a₁ b₁ c₁ : ℕ∞}
    (h : ∃ i₁ j₁ k₁ i₂ j₂ k₂ : ℕ∞, a₀ = i₁ + j₁ ∧ b₀ = j₁ + k₁ ∧ c₀ = k₁ + i₂ ∧
      a₁ = i₂ + j₂ ∧ b₁ = j₂ + k₂ ∧ c₁ = k₂ + i₁) :
    (a₀ ≠ ⊤ ∧ a₁ ≠ ⊤ → c₀ ≠ ⊤ ∧ c₁ ≠ ⊤ → b₀ ≠ ⊤ ∧ b₁ ≠ ⊤) ∧
    (a₀ ≠ ⊤ ∧ a₁ ≠ ⊤ → b₀ ≠ ⊤ ∧ b₁ ≠ ⊤ → c₀ ≠ ⊤ ∧ c₁ ≠ ⊤) ∧
    (b₀ ≠ ⊤ ∧ b₁ ≠ ⊤ → c₀ ≠ ⊤ ∧ c₁ ≠ ⊤ → a₀ ≠ ⊤ ∧ a₁ ≠ ⊤) := by
  obtain ⟨i₁, j₁, k₁, i₂, j₂, k₂, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  simp only [ne_eq, ENat.add_eq_top, not_or]
  tauto

/-- Arithmetic of a cyclic six-term decomposition: the alternating sum vanishes. -/
private theorem sixTerm_toNat {a₀ b₀ c₀ a₁ b₁ c₁ : ℕ∞}
    (h : ∃ i₁ j₁ k₁ i₂ j₂ k₂ : ℕ∞, a₀ = i₁ + j₁ ∧ b₀ = j₁ + k₁ ∧ c₀ = k₁ + i₂ ∧
      a₁ = i₂ + j₂ ∧ b₁ = j₂ + k₂ ∧ c₁ = k₂ + i₁)
    (ha : a₀ ≠ ⊤ ∧ a₁ ≠ ⊤) (hc : c₀ ≠ ⊤ ∧ c₁ ≠ ⊤) :
    (b₀.toNat : ℤ) - b₁.toNat = ((a₀.toNat : ℤ) - a₁.toNat) + ((c₀.toNat : ℤ) - c₁.toNat) := by
  obtain ⟨i₁, j₁, k₁, i₂, j₂, k₂, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  simp only [ne_eq, ENat.add_eq_top, not_or] at ha hc
  obtain ⟨⟨hi₁, hj₁⟩, hi₂, hj₂⟩ := ha
  obtain ⟨⟨hk₁, -⟩, hk₂, -⟩ := hc
  lift i₁ to ℕ using hi₁
  lift j₁ to ℕ using hj₁
  lift k₁ to ℕ using hk₁
  lift i₂ to ℕ using hi₂
  lift j₂ to ℕ using hj₂
  lift k₂ to ℕ using hk₂
  simp only [← Nat.cast_add, ENat.toNat_natCast]
  push_cast
  ring

end SixTerm

section Support

variable {R : Type*} [CommRing R]

open IsLocalRing

/-- Over a local ring, every prime in the support of a module of finite length is the maximal
ideal. -/
theorem eq_maximalIdeal_of_mem_support_of_length_ne_top [IsLocalRing R] {P : Type*}
    [AddCommGroup P] [Module R P] (hP : Module.length R P ≠ ⊤) (p : PrimeSpectrum R)
    (hp : p ∈ Module.support R P) : p.asIdeal = maximalIdeal R := by
  by_contra hne
  have hlt : ¬ maximalIdeal R ≤ p.asIdeal := fun h ↦
    hne (le_antisymm (le_maximalIdeal p.2.ne_top) h)
  obtain ⟨s, hsm, hsp⟩ := SetLike.not_le_iff_exists.1 hlt
  have hfl := isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 hP)
  have _ : IsNoetherian R P := hfl.1
  have _ : IsArtinian R P := hfl.2
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes (R := R) P s
  set N := LinearMap.range (s ^ n • LinearMap.id : P →ₗ[R] P) with hNdef
  have hN : N ≤ Ideal.span {s} • N := by
    rintro _ ⟨z, rfl⟩
    have hz : (s ^ n • LinearMap.id : P →ₗ[R] P) z
        ∈ LinearMap.range (s ^ (n + 1) • LinearMap.id : P →ₗ[R] P) := by
      rw [← hn (n + 1) (Nat.le_succ n)]
      exact ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hz
    rw [← hw]
    have : (s ^ (n + 1) • LinearMap.id : P →ₗ[R] P) w
        = s • ((s ^ n • LinearMap.id : P →ₗ[R] P) w) := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, pow_succ', mul_smul]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self s) ⟨w, rfl⟩
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {s}) N
    (IsNoetherian.noetherian N) hN
    ((Ideal.span_singleton_le_iff_mem _).2 (maximalIdeal_le_jacobson ⊥ hsm))
  have hann : s ^ n ∈ Module.annihilator R P := by
    refine Module.mem_annihilator.2 fun z ↦ ?_
    have hz : (s ^ n • LinearMap.id : P →ₗ[R] P) z ∈ N := ⟨z, rfl⟩
    rw [hbot, Submodule.mem_bot] at hz
    simpa using hz
  exact hsp (p.2.mem_of_pow_mem n (Module.annihilator_le_of_mem_support hp hann))

/-- Over a Noetherian local ring, a finite module whose support is contained in the closed point
has finite length. -/
theorem length_ne_top_of_support [IsNoetherianRing R] [IsLocalRing R] {P : Type*}
    [AddCommGroup P] [Module R P] [Module.Finite R P]
    (h : ∀ p ∈ Module.support R P, p.asIdeal = maximalIdeal R) : Module.length R P ≠ ⊤ := by
  rcases subsingleton_or_nontrivial P with hs | hs
  · rw [Module.length_eq_zero]
    exact ENat.zero_ne_top
  set I := Module.annihilator R P
  have hI : ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q = maximalIdeal R := fun Q hQ hIQ ↦
    h ⟨Q, hQ⟩ (Module.mem_support_iff_of_finite.2 hIQ)
  have hItop : I ≠ ⊤ := fun h1 ↦ not_subsingleton P (Module.annihilator_eq_top_iff.1 h1)
  have _ : IsArtinian R (R ⧸ I) := LocalOrdSymmetry.isArtinian_quotient_of_unique_prime
    (maximalIdeal R) I (le_maximalIdeal hItop) hI
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := P)
  have hsI : ∀ i, I ≤ LinearMap.ker (LinearMap.toSpanSingleton R P (s i)) := fun i r hr ↦ by
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact Module.mem_annihilator.1 hr (s i)
  let g : (Fin n → R ⧸ I) →ₗ[R] P :=
    LinearMap.lsum R (fun _ ↦ R ⧸ I) ℕ fun i ↦ Submodule.liftQ I _ (hsI i)
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i (Submodule.Quotient.mk 1), ?_⟩
    change LinearMap.lsum R (fun _ ↦ R ⧸ I) ℕ _ _ = _
    rw [LinearMap.lsum_piSingle, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply,
      one_smul]
  have _ : IsArtinian R P := isArtinian_of_surjective _ g hg
  exact Module.length_ne_top

/-- The range of multiplication by `x` is the submodule `(x) • M`. -/
theorem range_lsmul_eq_span_smul_top {M : Type*} [AddCommGroup M] [Module R M] (x : R) :
    LinearMap.range (LinearMap.lsmul R M x) = Ideal.span {x} • (⊤ : Submodule R M) := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) trivial
  · refine Submodule.smul_le.2 fun r hr n _ ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    exact ⟨a • n, by rw [LinearMap.lsmul_apply, smul_smul, mul_comm]⟩

/-- For a finite module `M`, a prime in the support of `M` containing `x` lies in the support of
`M ⧸ xM`. -/
theorem mem_support_quotient_lsmul {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) {p : PrimeSpectrum R} (hp : p ∈ Module.support R M) (hx : x ∈ p.asIdeal) :
    p ∈ Module.support R (M ⧸ LinearMap.range (LinearMap.lsmul R M x)) := by
  rw [range_lsmul_eq_span_smul_top, Module.support_quotient]
  refine ⟨hp, ?_⟩
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le]
  exact Set.singleton_subset_iff.2 hx

/-- Over a Noetherian local ring, if every prime of the support of a finite module `N` containing
`x` is maximal, then `N ⧸ xN` has finite length. -/
theorem chiCoker_ne_top_of_support [IsNoetherianRing R] [IsLocalRing R] {N : Type*}
    [AddCommGroup N] [Module R N] [Module.Finite R N] (x : R)
    (h : ∀ p ∈ Module.support R N, x ∈ p.asIdeal → p.asIdeal = maximalIdeal R) :
    LocalOrdSymmetry.chiCoker x N ≠ ⊤ := by
  apply length_ne_top_of_support
  intro p hp
  have hpN : p ∈ Module.support R N :=
    Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _) hp
  refine h p hpN (Module.annihilator_le_of_mem_support hp (Module.mem_annihilator.2 fun z ↦ ?_))
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨z, rfl⟩

/-- If `M ⧸ xM` has finite length over a local ring, every prime of the support of `M` containing
`x` is the maximal ideal. -/
theorem eq_maximalIdeal_of_chiCoker_ne_top [IsLocalRing R] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] {x : R} (hx : LocalOrdSymmetry.chiCoker x M ≠ ⊤) :
    ∀ p ∈ Module.support R M, x ∈ p.asIdeal → p.asIdeal = maximalIdeal R := fun p hp hxp ↦
  eq_maximalIdeal_of_mem_support_of_length_ne_top hx p (mem_support_quotient_lsmul x hp hxp)

/-- The cokernel of a surjective linear map has finite length (it is zero). -/
theorem length_quotient_range_ne_top_of_surjective {N P : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] {f : N →ₗ[R] P} (hf : Function.Surjective f) :
    Module.length R (P ⧸ LinearMap.range f) ≠ ⊤ := by
  rw [LinearMap.range_eq_top.2 hf, Module.length_eq_zero]
  exact ENat.zero_ne_top

/-- Powers of multiplication by `x` are multiplication by powers of `x`. -/
theorem lsmul_pow_eq {M : Type*} [AddCommGroup M] [Module R M] (x : R) (n : ℕ) :
    LinearMap.lsmul R M x ^ n = LinearMap.lsmul R M (x ^ n) := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext m
    change x ^ n • x • m = x ^ (n + 1) • m
    rw [pow_succ, mul_smul]

end Support

/-- A `(2,1)`-periodic complex `(M, φ, ψ)` over `R` (Stacks, Definition 42.2.1): two endomorphisms
`φ ψ` of `M` with `φ ∘ ψ = 0` and `ψ ∘ φ = 0`. -/
structure PeriodicComplex (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M]
    [Module R M] where
  /-- The first differential `φ`. -/
  φ : M →ₗ[R] M
  /-- The second differential `ψ`. -/
  ψ : M →ₗ[R] M
  /-- `φ ∘ ψ = 0`. -/
  φ_ψ : ∀ m, φ (ψ m) = 0
  /-- `ψ ∘ φ = 0`. -/
  ψ_φ : ∀ m, ψ (φ m) = 0

namespace PeriodicComplex

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N] {P : Type*} [AddCommGroup P] [Module R P]

/-- The complex `(M, ψ, φ)` obtained by exchanging the two differentials. -/
def swap (C : PeriodicComplex R M) : PeriodicComplex R M := ⟨C.ψ, C.φ, C.ψ_φ, C.φ_ψ⟩

/-- The zeroth cohomology `H⁰ = ker φ / im ψ`. -/
abbrev H0 (C : PeriodicComplex R M) : Type _ :=
  LinearMap.ker C.φ ⧸ (LinearMap.range C.ψ).comap (LinearMap.ker C.φ).subtype

/-- The first cohomology `H¹ = ker ψ / im φ` (defined as `H⁰` of the swapped complex). -/
abbrev H1 (C : PeriodicComplex R M) : Type _ := C.swap.H0

/-- Both cohomology modules of `C` have finite length. -/
def FiniteCohomology (C : PeriodicComplex R M) : Prop :=
  Module.length R C.H0 ≠ ⊤ ∧ Module.length R C.H1 ≠ ⊤

/-- The multiplicity (additive Herbrand quotient) `e(M, φ, ψ) = length H⁰ - length H¹`.
It is only meaningful when `C.FiniteCohomology` holds (infinite lengths are sent to `0`). -/
noncomputable def herbrand (C : PeriodicComplex R M) : ℤ :=
  ((Module.length R C.H0).toNat : ℤ) - (Module.length R C.H1).toNat

/-- The length of `H⁰` as a `relLen`. -/
theorem length_H0_eq_relLen (C : PeriodicComplex R M) :
    Module.length R C.H0 = relLen (LinearMap.range C.ψ) (LinearMap.ker C.φ) := rfl

/-- The length of `H¹` as a `relLen`. -/
theorem length_H1_eq_relLen (C : PeriodicComplex R M) :
    Module.length R C.H1 = relLen (LinearMap.range C.φ) (LinearMap.ker C.ψ) := rfl

/-- `im ψ ⊆ ker φ`. -/
theorem range_ψ_le_ker_φ (C : PeriodicComplex R M) : LinearMap.range C.ψ ≤ LinearMap.ker C.φ := by
  rintro _ ⟨m, rfl⟩
  exact C.φ_ψ m

@[simp] theorem swap_swap (C : PeriodicComplex R M) : C.swap.swap = C := rfl

/-- Swapping the differentials preserves finiteness of cohomology. -/
theorem finiteCohomology_swap_iff (C : PeriodicComplex R M) :
    C.swap.FiniteCohomology ↔ C.FiniteCohomology := And.comm

/-- Swapping the differentials negates the multiplicity. -/
theorem herbrand_swap (C : PeriodicComplex R M) : C.swap.herbrand = - C.herbrand := by
  simp only [herbrand]
  change _ - ((Module.length R C.H0).toNat : ℤ) = -(((Module.length R C.H0).toNat : ℤ) - _)
  ring

/-- `length H⁰ + length (im ψ) = length (ker φ)`. -/
theorem length_H0_add (C : PeriodicComplex R M) :
    Module.length R C.H0 + Module.length R (LinearMap.range C.ψ)
      = Module.length R (LinearMap.ker C.φ) := by
  rw [length_eq_add_relLen C.range_ψ_le_ker_φ, length_H0_eq_relLen, add_comm]

/-- A morphism of periodic complexes: a linear map commuting with both differentials. -/
structure Hom (C : PeriodicComplex R M) (D : PeriodicComplex R N) where
  /-- The underlying linear map. -/
  f : M →ₗ[R] N
  /-- `f` commutes with `φ`. -/
  comm_φ : ∀ m, f (C.φ m) = D.φ (f m)
  /-- `f` commutes with `ψ`. -/
  comm_ψ : ∀ m, f (C.ψ m) = D.ψ (f m)

namespace Hom

variable {C : PeriodicComplex R M} {D : PeriodicComplex R N} {E : PeriodicComplex R P}

/-- A morphism between the swapped complexes. -/
def swap (F : Hom C D) : Hom C.swap D.swap := ⟨F.f, F.comm_ψ, F.comm_φ⟩

/-- The map induced on `H⁰`. -/
noncomputable def mapH0 (F : Hom C D) : C.H0 →ₗ[R] D.H0 :=
  Submodule.mapQ _ _ (F.f.restrict (p := LinearMap.ker C.φ) (q := LinearMap.ker D.φ)
    fun m hm ↦ by rw [LinearMap.mem_ker] at hm ⊢; rw [← F.comm_φ, hm, map_zero])
    (by
      rintro ⟨m, hm⟩ ⟨y, hy⟩
      refine ⟨F.f y, ?_⟩
      change D.ψ (F.f y) = F.f m
      rw [← F.comm_ψ, hy]
      rfl)

/-- The induced map on `H⁰` on representatives. -/
theorem mapH0_mk (F : Hom C D) (m : LinearMap.ker C.φ) :
    F.mapH0 (Submodule.Quotient.mk m)
      = Submodule.Quotient.mk ⟨F.f m, by
          rw [LinearMap.mem_ker, ← F.comm_φ, LinearMap.mem_ker.1 m.2, map_zero]⟩ := rfl

/-- The map induced on `H¹`. -/
noncomputable def mapH1 (F : Hom C D) : C.H1 →ₗ[R] D.H1 := F.swap.mapH0

/-- The map induced on `H¹` of the swapped complexes is the map on `H⁰`. -/
theorem swap_mapH1 (F : Hom C D) : F.swap.mapH1 = F.mapH0 := rfl

variable (F : Hom C D) (G : Hom D E) (hF : Function.Injective F.f)
  (hG : Function.Surjective G.f) (hFG : Function.Exact F.f G.f)
include hF hG hFG

/-- Exactness of `H⁰(C) → H⁰(D) → H⁰(E)` for a short exact sequence of complexes. -/
theorem exact_mapH0 : Function.Exact F.mapH0 G.mapH0 := by
  intro z
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  constructor
  · intro h
    rw [mapH0_mk, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨w, hw⟩ := h
    obtain ⟨w, rfl⟩ := hG w
    change E.ψ (G.f w) = G.f y at hw
    have h0 : G.f (y - D.ψ w) = 0 := by rw [map_sub, G.comm_ψ, hw, sub_self]
    obtain ⟨x, hx⟩ := (hFG _).1 h0
    have hxk : C.φ x = 0 := hF (by
      rw [F.comm_φ, hx, map_zero, map_sub, D.φ_ψ, LinearMap.mem_ker.1 hy, sub_zero])
    refine ⟨Submodule.Quotient.mk ⟨x, hxk⟩, ?_⟩
    rw [mapH0_mk, Submodule.Quotient.eq]
    refine ⟨-w, ?_⟩
    change D.ψ (-w) = F.f x - y
    rw [hx, map_neg]
    abel
  · rintro ⟨z', hz'⟩
    rw [← hz']
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
    rw [mapH0_mk, mapH0_mk, Submodule.Quotient.mk_eq_zero]
    refine ⟨0, ?_⟩
    change E.ψ 0 = G.f (F.f x)
    rw [map_zero, hFG.apply_apply_eq_zero]

/-- Exactness of `H¹(C) → H¹(D) → H¹(E)` for a short exact sequence of complexes. -/
theorem exact_mapH1 : Function.Exact F.mapH1 G.mapH1 :=
  exact_mapH0 F.swap G.swap hF hG hFG

omit hG hFG in
/-- The inverse of `F` on its range. -/
private noncomputable abbrev invOnRange : LinearMap.range F.f →ₗ[R] M :=
  (LinearEquiv.ofInjective F.f hF).symm.toLinearMap

omit hG hFG in
/-- `F ∘ invOnRange = id` on the range of `F`. -/
private theorem apply_invOnRange (y : LinearMap.range F.f) : F.f (invOnRange F hF y) = y := by
  have := LinearEquiv.ofInjective_apply (f := F.f) (h := hF)
    ((LinearEquiv.ofInjective F.f hF).symm y)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

omit hG hFG in
/-- The domain of the connecting map: elements of `D` whose `φ` lies in the image of `C`. -/
abbrev connectingDomain : Submodule R N := (LinearMap.range F.f).comap D.φ

omit hF hG in
/-- `G` maps `connectingDomain` into `ker φ`. -/
theorem mem_ker_of_connectingDomain (c : connectingDomain F) : G.f c ∈ LinearMap.ker E.φ := by
  obtain ⟨x, hx⟩ := c.2
  rw [LinearMap.mem_ker, ← G.comm_φ, ← hx, hFG.apply_apply_eq_zero]

omit hG hF in
/-- The projection `connectingDomain → H⁰(E)`. -/
private noncomputable abbrev connProj : connectingDomain F →ₗ[R] E.H0 :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (LinearMap.ker E.φ) (G.f ∘ₗ (connectingDomain F).subtype)
    (mem_ker_of_connectingDomain F G hFG)

omit hG hFG in
/-- `F⁻¹ (φ c)` lies in `ker ψ` for `c ∈ connectingDomain`. -/
private theorem mem_ker_invOnRange (c : connectingDomain F) :
    invOnRange F hF ⟨D.φ c, c.2⟩ ∈ LinearMap.ker C.ψ := by
  rw [LinearMap.mem_ker]
  apply hF
  rw [F.comm_ψ, apply_invOnRange, map_zero]
  exact D.ψ_φ c

omit hG hFG in
/-- The map `connectingDomain → H¹(C)`, `c ↦ [F⁻¹ (φ c)]`. -/
private noncomputable abbrev connLift : connectingDomain F →ₗ[R] C.H1 :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (LinearMap.ker C.ψ)
    (invOnRange F hF ∘ₗ LinearMap.codRestrict (LinearMap.range F.f)
      (D.φ ∘ₗ (connectingDomain F).subtype) (fun c ↦ c.2)) (mem_ker_invOnRange F hF)

omit hF in
/-- The projection `connectingDomain → H⁰(E)` is surjective. -/
private theorem connProj_surjective : Function.Surjective (connProj F G hFG) := by
  intro z
  obtain ⟨⟨e, he⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨c, rfl⟩ := hG e
  have hc : D.φ c ∈ LinearMap.range F.f := by
    refine (hFG _).1 ?_
    rw [G.comm_φ]
    exact he
  exact ⟨⟨c, hc⟩, rfl⟩

/-- The kernel of `connProj` is killed by `connLift`, so the connecting map is well defined. -/
private theorem ker_connProj_le :
    LinearMap.ker (connProj F G hFG) ≤ LinearMap.ker (connLift F hF) := by
  rintro ⟨c, hc⟩ h
  rw [LinearMap.mem_ker] at h ⊢
  change Submodule.Quotient.mk _ = 0 at h
  rw [Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨w, hw⟩ := h
  obtain ⟨w, rfl⟩ := hG w
  change E.ψ (G.f w) = G.f c at hw
  have h0 : G.f (c - D.ψ w) = 0 := by rw [map_sub, G.comm_ψ, hw, sub_self]
  obtain ⟨u, hu⟩ := (hFG _).1 h0
  change Submodule.Quotient.mk _ = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨u, ?_⟩
  change C.φ u = invOnRange F hF ⟨D.φ c, hc⟩
  apply hF
  rw [apply_invOnRange, F.comm_φ, hu, map_sub, D.φ_ψ, sub_zero]

/-- The connecting map `H⁰(E) → H¹(C)` of a short exact sequence of periodic complexes. -/
noncomputable def connecting : E.H0 →ₗ[R] C.H1 :=
  (LinearMap.ker (connProj F G hFG)).liftQ (connLift F hF) (ker_connProj_le F G hF hG hFG) ∘ₗ
    ((connProj F G hFG).quotKerEquivOfSurjective (connProj_surjective F G hG hFG)).symm.toLinearMap

/-- Characterisation of the connecting map: if `φ c = F x` then `δ [G c] = [x]`. -/
theorem connecting_spec (c : N) (hc : D.φ c ∈ LinearMap.range F.f) (x : M)
    (hx : F.f x = D.φ c) (hxψ : C.ψ x = 0) :
    connecting F G hF hG hFG
        (Submodule.Quotient.mk ⟨G.f c, mem_ker_of_connectingDomain F G hFG ⟨c, hc⟩⟩)
      = Submodule.Quotient.mk ⟨x, hxψ⟩ := by
  have h1 : (Submodule.Quotient.mk ⟨G.f c, mem_ker_of_connectingDomain F G hFG ⟨c, hc⟩⟩ : E.H0)
      = connProj F G hFG ⟨c, hc⟩ := rfl
  rw [connecting, LinearMap.comp_apply, h1, LinearEquiv.coe_toLinearMap,
    (LinearEquiv.symm_apply_eq _).2 (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm,
    Submodule.liftQ_apply]
  change Submodule.Quotient.mk _ = _
  congr 1
  ext
  change invOnRange F hF ⟨D.φ c, hc⟩ = x
  apply hF
  rw [apply_invOnRange, hx]

/-- Exactness of `H⁰(D) → H⁰(E) → H¹(C)`. -/
theorem exact_connecting_left : Function.Exact G.mapH0 (connecting F G hF hG hFG) := by
  intro z
  obtain ⟨⟨e, he⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨c, rfl⟩ := hG e
  have hc : D.φ c ∈ LinearMap.range F.f := by
    refine (hFG _).1 ?_
    rw [G.comm_φ]
    exact he
  obtain ⟨x, hx⟩ := hc
  have hxψ : C.ψ x = 0 := hF (by rw [F.comm_ψ, hx, D.ψ_φ, map_zero])
  have hspec := connecting_spec F G hF hG hFG c ⟨x, hx⟩ x hx hxψ
  constructor
  · intro h
    rw [hspec, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨u, hu⟩ := h
    change C.φ u = x at hu
    have hk : c - F.f u ∈ LinearMap.ker D.φ := by
      rw [LinearMap.mem_ker, map_sub, ← F.comm_φ, hu, hx, sub_self]
    refine ⟨Submodule.Quotient.mk ⟨c - F.f u, hk⟩, ?_⟩
    rw [mapH0_mk]
    congr 2
    rw [map_sub, hFG.apply_apply_eq_zero, sub_zero]
  · rintro ⟨z', hz'⟩
    rw [← hz']
    obtain ⟨⟨c', hc'⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
    have hc0 : D.φ c' ∈ LinearMap.range F.f := ⟨0, by rw [map_zero, LinearMap.mem_ker.1 hc']⟩
    rw [mapH0_mk]
    have := connecting_spec F G hF hG hFG c' hc0 0 (by rw [map_zero, LinearMap.mem_ker.1 hc'])
      (map_zero _)
    refine this.trans ?_
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨0, map_zero _⟩

/-- Exactness of `H⁰(E) → H¹(C) → H¹(D)`. -/
theorem exact_connecting_right : Function.Exact (connecting F G hF hG hFG) F.mapH1 := by
  intro z
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hxψ : C.ψ x = 0 := hx
  constructor
  · intro h
    change F.swap.mapH0 _ = 0 at h
    rw [mapH0_mk, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨c, hc⟩ := h
    change D.φ c = F.f x at hc
    have hcr : D.φ c ∈ LinearMap.range F.f := ⟨x, hc.symm⟩
    exact ⟨_, connecting_spec F G hF hG hFG c hcr x hc.symm hxψ⟩
  · rintro ⟨z', hz'⟩
    rw [← hz']
    obtain ⟨⟨e, he⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
    obtain ⟨c, rfl⟩ := hG e
    have hc : D.φ c ∈ LinearMap.range F.f := by
      refine (hFG _).1 ?_
      rw [G.comm_φ]
      exact he
    obtain ⟨x', hx'⟩ := hc
    have hxψ' : C.ψ x' = 0 := hF (by rw [F.comm_ψ, hx', D.ψ_φ, map_zero])
    have hspec := connecting_spec F G hF hG hFG c ⟨x', hx'⟩ x' hx' hxψ'
    rw [hspec]
    change F.swap.mapH0 _ = 0
    rw [mapH0_mk, Submodule.Quotient.mk_eq_zero]
    exact ⟨c, hx'.symm⟩

end Hom

section Additivity

variable {C : PeriodicComplex R M} {D : PeriodicComplex R N} {E : PeriodicComplex R P}
  (F : Hom C D) (G : Hom D E) (hF : Function.Injective F.f)
  (hG : Function.Surjective G.f) (hFG : Function.Exact F.f G.f)
include hF hG hFG

/-- The six-term cyclic cohomology sequence of a short exact sequence of periodic complexes,
in terms of lengths. -/
theorem sixTerm_decomposition :
    ∃ i₁ j₁ k₁ i₂ j₂ k₂ : ℕ∞, Module.length R C.H0 = i₁ + j₁ ∧
      Module.length R D.H0 = j₁ + k₁ ∧ Module.length R E.H0 = k₁ + i₂ ∧
      Module.length R C.H1 = i₂ + j₂ ∧ Module.length R D.H1 = j₂ + k₂ ∧
      Module.length R E.H1 = k₂ + i₁ := by
  let d : E.H1 →ₗ[R] C.swap.swap.H0 := Hom.connecting F.swap G.swap hF hG hFG
  let d' : E.H1 →ₗ[R] C.H0 := d
  have e₅ : Function.Exact G.mapH1 d' := Hom.exact_connecting_left F.swap G.swap hF hG hFG
  have e₆ : Function.Exact d' F.mapH0 := Hom.exact_connecting_right F.swap G.swap hF hG hFG
  exact exists_lengths_of_cyclic_exact F.mapH0 G.mapH0 (Hom.connecting F G hF hG hFG) F.mapH1
    G.mapH1 d' (Hom.exact_mapH0 F G hF hG hFG)
    (Hom.exact_connecting_left F G hF hG hFG) (Hom.exact_connecting_right F G hF hG hFG)
    (Hom.exact_mapH1 F G hF hG hFG) e₅ e₆

/-- Additivity of the multiplicity (Stacks, Lemma 42.2.3), outer terms finite: for a short exact
sequence `0 → C → D → E → 0` of periodic complexes, if `C` and `E` have finite cohomology then so
does `D`, and `e(D) = e(C) + e(E)`. -/
theorem herbrand_add_of_exact_of_outer (h₁ : C.FiniteCohomology) (h₃ : E.FiniteCohomology) :
    D.FiniteCohomology ∧ D.herbrand = C.herbrand + E.herbrand :=
  ⟨(sixTerm_finite (sixTerm_decomposition F G hF hG hFG)).1 h₁ h₃,
    sixTerm_toNat (sixTerm_decomposition F G hF hG hFG) h₁ h₃⟩

/-- Additivity of the multiplicity (Stacks, Lemma 42.2.3), first two terms finite: for a short exact
sequence `0 → C → D → E → 0` of periodic complexes, if `C` and `D` have finite cohomology then so
does `E`, and `e(D) = e(C) + e(E)`. -/
theorem herbrand_add_of_exact_of_left (h₁ : C.FiniteCohomology) (h₂ : D.FiniteCohomology) :
    E.FiniteCohomology ∧ D.herbrand = C.herbrand + E.herbrand := by
  have h₃ := (sixTerm_finite (sixTerm_decomposition F G hF hG hFG)).2.1 h₁ h₂
  exact ⟨h₃, sixTerm_toNat (sixTerm_decomposition F G hF hG hFG) h₁ h₃⟩

/-- Additivity of the multiplicity (Stacks, Lemma 42.2.3), last two terms finite: for a short exact
sequence `0 → C → D → E → 0` of periodic complexes, if `D` and `E` have finite cohomology then so
does `C`, and `e(D) = e(C) + e(E)`. -/
theorem herbrand_add_of_exact_of_right (h₂ : D.FiniteCohomology) (h₃ : E.FiniteCohomology) :
    C.FiniteCohomology ∧ D.herbrand = C.herbrand + E.herbrand := by
  have h₁ := (sixTerm_finite (sixTerm_decomposition F G hF hG hFG)).2.2 h₂ h₃
  exact ⟨h₁, sixTerm_toNat (sixTerm_decomposition F G hF hG hFG) h₁ h₃⟩

end Additivity

/-- Arithmetic behind `herbrand_eq_zero_of_length_ne_top`. -/
private theorem finite_length_aux {h₀ h₁ a b k l m : ℕ∞} (e₁ : h₀ + b = k) (e₂ : h₁ + a = l)
    (e₃ : m = k + a) (e₄ : m = l + b) (hm : m ≠ ⊤) :
    h₀ ≠ ⊤ ∧ h₁ ≠ ⊤ ∧ ((h₀.toNat : ℤ) - h₁.toNat = 0) := by
  subst e₁ e₂ e₃
  have hm' := hm
  rw [e₄] at hm'
  simp only [ne_eq, ENat.add_eq_top, not_or] at hm hm'
  obtain ⟨⟨hh₀, hb⟩, ha⟩ := hm
  refine ⟨hh₀, hm'.1.1, ?_⟩
  lift h₀ to ℕ using hh₀
  lift h₁ to ℕ using hm'.1.1
  lift a to ℕ using ha
  lift b to ℕ using hb
  norm_cast at e₄
  simp only [ENat.toNat_natCast]
  omega

/-- A periodic complex on a module of finite length has finite cohomology and multiplicity `0`
(Stacks, Lemma 42.2.4). -/
theorem herbrand_eq_zero_of_length_ne_top (C : PeriodicComplex R M)
    (hM : Module.length R M ≠ ⊤) : C.FiniteCohomology ∧ C.herbrand = 0 := by
  have e₂ : Module.length R C.H1 + Module.length R (LinearMap.range C.φ)
      = Module.length R (LinearMap.ker C.ψ) := C.swap.length_H0_add
  obtain ⟨h₀, h₁, h⟩ := finite_length_aux C.length_H0_add e₂
    (LocalOrdSymmetry.length_eq_ker_add_range C.φ)
    (LocalOrdSymmetry.length_eq_ker_add_range C.ψ) hM
  exact ⟨⟨h₀, h₁⟩, h⟩

/-- An exact periodic complex has finite cohomology and multiplicity `0`. -/
theorem herbrand_eq_zero_of_exact (C : PeriodicComplex R M)
    (h₀ : LinearMap.ker C.φ ≤ LinearMap.range C.ψ)
    (h₁ : LinearMap.ker C.ψ ≤ LinearMap.range C.φ) :
    C.FiniteCohomology ∧ C.herbrand = 0 := by
  have a : Module.length R C.H0 = 0 := relLen_eq_zero_of_le h₀
  have b : Module.length R C.H1 = 0 := relLen_eq_zero_of_le h₁
  refine ⟨⟨by rw [a]; exact ENat.zero_ne_top, by rw [b]; exact ENat.zero_ne_top⟩, ?_⟩
  rw [herbrand, a, b]
  simp

section SubQuot

variable (C : PeriodicComplex R M) (S : Submodule R M) (hφ : ∀ x ∈ S, C.φ x ∈ S)
  (hψ : ∀ x ∈ S, C.ψ x ∈ S)

/-- The subcomplex on a submodule stable under both differentials. -/
def restrict : PeriodicComplex R S where
  φ := C.φ.restrict hφ
  ψ := C.ψ.restrict hψ
  φ_ψ m := Subtype.ext (C.φ_ψ m)
  ψ_φ m := Subtype.ext (C.ψ_φ m)

/-- The quotient complex by a submodule stable under both differentials. -/
def quotient : PeriodicComplex R (M ⧸ S) where
  φ := S.mapQ S C.φ hφ
  ψ := S.mapQ S C.ψ hψ
  φ_ψ m := by
    induction m using Submodule.Quotient.induction_on with
    | H x => rw [Submodule.mapQ_apply, Submodule.mapQ_apply, C.φ_ψ]; rfl
  ψ_φ m := by
    induction m using Submodule.Quotient.induction_on with
    | H x => rw [Submodule.mapQ_apply, Submodule.mapQ_apply, C.ψ_φ]; rfl

/-- The inclusion of a subcomplex. -/
def restrictHom : Hom (C.restrict S hφ hψ) C := ⟨S.subtype, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The projection onto a quotient complex. -/
def quotientHom : Hom C (C.quotient S hφ hψ) := ⟨S.mkQ, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The inclusion of a subcomplex is injective. -/
theorem restrictHom_injective : Function.Injective (C.restrictHom S hφ hψ).f :=
  S.injective_subtype

/-- The projection onto a quotient complex is surjective. -/
theorem quotientHom_surjective : Function.Surjective (C.quotientHom S hφ hψ).f :=
  S.mkQ_surjective

/-- `0 → S → M → M ⧸ S → 0` is exact. -/
theorem exact_restrictHom_quotientHom :
    Function.Exact (C.restrictHom S hφ hψ).f (C.quotientHom S hφ hψ).f :=
  LinearMap.exact_subtype_mkQ S

end SubQuot

section Compare

variable {C : PeriodicComplex R M} {D : PeriodicComplex R N} (F : Hom C D)

/-- The kernel of a morphism is stable under `φ`. -/
theorem ker_stable_φ : ∀ x ∈ LinearMap.ker F.f, C.φ x ∈ LinearMap.ker F.f := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [F.comm_φ, hx, map_zero]

/-- The kernel of a morphism is stable under `ψ`. -/
theorem ker_stable_ψ : ∀ x ∈ LinearMap.ker F.f, C.ψ x ∈ LinearMap.ker F.f := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [F.comm_ψ, hx, map_zero]

/-- The image of a morphism is stable under `φ`. -/
theorem range_stable_φ : ∀ x ∈ LinearMap.range F.f, D.φ x ∈ LinearMap.range F.f := by
  rintro _ ⟨y, rfl⟩
  exact ⟨C.φ y, F.comm_φ y⟩

/-- The image of a morphism is stable under `ψ`. -/
theorem range_stable_ψ : ∀ x ∈ LinearMap.range F.f, D.ψ x ∈ LinearMap.range F.f := by
  rintro _ ⟨y, rfl⟩
  exact ⟨C.ψ y, F.comm_ψ y⟩

/-- The corestriction of a morphism to the subcomplex on its image. -/
def rangeHom : Hom C (D.restrict _ (range_stable_φ F) (range_stable_ψ F)) :=
  ⟨F.f.rangeRestrict, fun m ↦ Subtype.ext (F.comm_φ m), fun m ↦ Subtype.ext (F.comm_ψ m)⟩

/-- `0 → ker F → C → im F → 0` is exact. -/
theorem exact_ker_rangeHom :
    Function.Exact (C.restrictHom _ (ker_stable_φ F) (ker_stable_ψ F)).f (rangeHom F).f := by
  rw [LinearMap.exact_iff]
  change LinearMap.ker F.f.rangeRestrict = LinearMap.range (LinearMap.ker F.f).subtype
  rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]

variable (hker : Module.length R (LinearMap.ker F.f) ≠ ⊤)
  (hcoker : Module.length R (N ⧸ LinearMap.range F.f) ≠ ⊤)
include hker hcoker

/-- Comparison (Stacks, Lemma 42.2.5), finiteness part: a morphism of periodic complexes whose
kernel and cokernel have finite length preserves and reflects finiteness of cohomology. -/
theorem finiteCohomology_iff_of_hom : C.FiniteCohomology ↔ D.FiniteCohomology := by
  have hK := (C.restrict _ (ker_stable_φ F) (ker_stable_ψ F)).herbrand_eq_zero_of_length_ne_top
    hker
  have hQ := (D.quotient _ (range_stable_φ F) (range_stable_ψ F)).herbrand_eq_zero_of_length_ne_top
    hcoker
  have s₁ := herbrand_add_of_exact_of_outer (restrictHom _ _ _ _) (rangeHom F)
    (restrictHom_injective _ _ _ _) F.f.surjective_rangeRestrict (exact_ker_rangeHom F)
  have s₁l := herbrand_add_of_exact_of_left (restrictHom _ _ _ _) (rangeHom F)
    (restrictHom_injective _ _ _ _) F.f.surjective_rangeRestrict (exact_ker_rangeHom F)
  have s₂ := herbrand_add_of_exact_of_outer (restrictHom _ _ _ _) (quotientHom _ _ _ _)
    (restrictHom_injective D _ (range_stable_φ F) (range_stable_ψ F))
    (quotientHom_surjective _ _ _ _) (exact_restrictHom_quotientHom _ _ _ _)
  have s₂r := herbrand_add_of_exact_of_right (restrictHom _ _ _ _) (quotientHom _ _ _ _)
    (restrictHom_injective D _ (range_stable_φ F) (range_stable_ψ F))
    (quotientHom_surjective _ _ _ _) (exact_restrictHom_quotientHom _ _ _ _)
  constructor
  · intro hC
    exact (s₂ (s₁l hK.1 hC).1 hQ.1).1
  · intro hD
    exact (s₁ hK.1 (s₂r hD hQ.1).1).1

/-- Comparison (Stacks, Lemma 42.2.5): a morphism of periodic complexes whose kernel and cokernel
have finite length, between complexes with finite cohomology, preserves the multiplicity. -/
theorem herbrand_eq_of_hom (hC : C.FiniteCohomology) : C.herbrand = D.herbrand := by
  have hK := (C.restrict _ (ker_stable_φ F) (ker_stable_ψ F)).herbrand_eq_zero_of_length_ne_top
    hker
  have hQ := (D.quotient _ (range_stable_φ F) (range_stable_ψ F)).herbrand_eq_zero_of_length_ne_top
    hcoker
  have s₁ := herbrand_add_of_exact_of_left (restrictHom _ _ _ _) (rangeHom F)
    (restrictHom_injective _ _ _ _) F.f.surjective_rangeRestrict (exact_ker_rangeHom F) hK.1 hC
  have s₂ := herbrand_add_of_exact_of_outer (restrictHom _ _ _ _) (quotientHom _ _ _ _)
    (restrictHom_injective D _ (range_stable_φ F) (range_stable_ψ F))
    (quotientHom_surjective _ _ _ _) (exact_restrictHom_quotientHom _ _ _ _) s₁.1 hQ.1
  rw [s₁.2, s₂.2, hK.2, hQ.2, zero_add, add_zero]

end Compare

/-- The direct sum `(M × N, φ × φ', ψ × ψ')` of two periodic complexes. -/
def prod (C : PeriodicComplex R M) (D : PeriodicComplex R N) : PeriodicComplex R (M × N) where
  φ := C.φ.prodMap D.φ
  ψ := C.ψ.prodMap D.ψ
  φ_ψ m := Prod.ext (C.φ_ψ m.1) (D.φ_ψ m.2)
  ψ_φ m := Prod.ext (C.ψ_φ m.1) (D.ψ_φ m.2)

/-- The multiplicity of a direct sum is the sum of the multiplicities. -/
theorem herbrand_prod (C : PeriodicComplex R M) (D : PeriodicComplex R N)
    (hC : C.FiniteCohomology) (hD : D.FiniteCohomology) :
    (C.prod D).FiniteCohomology ∧ (C.prod D).herbrand = C.herbrand + D.herbrand :=
  herbrand_add_of_exact_of_outer (C := C) (D := C.prod D) (E := D)
    ⟨LinearMap.inl R M N, fun _ ↦ Prod.ext rfl (map_zero D.φ).symm,
      fun _ ↦ Prod.ext rfl (map_zero D.ψ).symm⟩
    ⟨LinearMap.snd R M N, fun _ ↦ rfl, fun _ ↦ rfl⟩
    LinearMap.inl_injective LinearMap.snd_surjective Function.Exact.inl_snd hC hD

section Congr

variable {C : PeriodicComplex R M} {D : PeriodicComplex R N} (e : M ≃ₗ[R] N)
  (hφ : ∀ m, e (C.φ m) = D.φ (e m)) (hψ : ∀ m, e (C.ψ m) = D.ψ (e m))
include hφ hψ

/-- A linear isomorphism intertwining the differentials identifies the lengths of `H⁰`. -/
theorem length_H0_congr : Module.length R C.H0 = Module.length R D.H0 := by
  have hker : LinearMap.ker (e : M →ₗ[R] N) ⊓ LinearMap.ker C.φ ≤ LinearMap.range C.ψ := by
    rw [LinearEquiv.ker, bot_inf_eq]
    exact bot_le
  rw [length_H0_eq_relLen, length_H0_eq_relLen, relLen_map (e : M →ₗ[R] N) C.range_ψ_le_ker_φ hker]
  congr 1
  · ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
      exact ⟨e m, (hψ m).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨C.ψ (e.symm n), ⟨e.symm n, rfl⟩, by rw [hψ, LinearEquiv.apply_symm_apply]⟩
  · ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hφ, hx, map_zero]
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      apply e.injective
      rw [hφ, LinearEquiv.apply_symm_apply, hy, map_zero]

/-- A linear isomorphism intertwining the differentials identifies the lengths of `H¹`. -/
theorem length_H1_congr : Module.length R C.H1 = Module.length R D.H1 :=
  length_H0_congr (C := C.swap) (D := D.swap) e hψ hφ

/-- A linear isomorphism `e : M ≃ N` intertwining the differentials of `C` and `D` preserves and
reflects finiteness of cohomology. -/
theorem finiteCohomology_congr : C.FiniteCohomology ↔ D.FiniteCohomology := by
  rw [FiniteCohomology, FiniteCohomology, length_H0_congr e hφ hψ, length_H1_congr e hφ hψ]

/-- A linear isomorphism `e : M ≃ N` intertwining the differentials of `C` and `D` preserves the
multiplicity (with no finiteness hypothesis: both lengths of cohomology agree). -/
theorem herbrand_congr : C.herbrand = D.herbrand := by
  rw [herbrand, herbrand, length_H0_congr e hφ hψ, length_H1_congr e hφ hψ]

end Congr

section Pi

variable {ι : Type*} {Ms : ι → Type*} [∀ i, AddCommGroup (Ms i)] [∀ i, Module R (Ms i)]

/-- The product `(Π i, Ms i, Π φᵢ, Π ψᵢ)` of a family of periodic complexes. -/
def pi (C : ∀ i, PeriodicComplex R (Ms i)) : PeriodicComplex R (∀ i, Ms i) where
  φ := LinearMap.pi fun i ↦ (C i).φ ∘ₗ LinearMap.proj i
  ψ := LinearMap.pi fun i ↦ (C i).ψ ∘ₗ LinearMap.proj i
  φ_ψ m := funext fun i ↦ (C i).φ_ψ (m i)
  ψ_φ m := funext fun i ↦ (C i).ψ_φ (m i)

/-- For a finite family, the length of `H⁰` of the product is the sum of the lengths of the
`H⁰`'s (in `ℕ∞`). -/
theorem length_H0_pi [Fintype ι] (C : ∀ i, PeriodicComplex R (Ms i)) :
    Module.length R (pi C).H0 = ∑ i, Module.length R (C i).H0 := by
  let Φ : LinearMap.ker (pi C).φ →ₗ[R] (∀ i, (C i).H0) := LinearMap.pi fun i ↦
    Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (LinearMap.ker (C i).φ)
      (LinearMap.proj i ∘ₗ (LinearMap.ker (pi C).φ).subtype)
      (fun x ↦ congrFun (LinearMap.mem_ker.1 x.2) i)
  have hsurj : Function.Surjective Φ := by
    intro y
    choose z hz using fun i ↦ Submodule.Quotient.mk_surjective _ (y i)
    refine ⟨⟨fun i ↦ (z i).1, LinearMap.mem_ker.2 (funext fun i ↦ (z i).2)⟩, ?_⟩
    funext i
    exact hz i
  have hker : LinearMap.ker Φ
      = (LinearMap.range (pi C).ψ).comap (LinearMap.ker (pi C).φ).subtype := by
    ext x
    simp only [Φ, LinearMap.mem_ker, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, funext_iff, Pi.zero_apply,
      Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range]
    constructor
    · intro h
      choose w hw using h
      exact ⟨w, fun i ↦ hw i⟩
    · rintro ⟨w, hw⟩ i
      exact ⟨w i, hw i⟩
  calc Module.length R (pi C).H0 = Module.length R (LinearMap.ker (pi C).φ ⧸ LinearMap.ker Φ) :=
        (Submodule.quotEquivOfEq _ _ hker.symm).length_eq
    _ = Module.length R (∀ i, (C i).H0) := (Φ.quotKerEquivOfSurjective hsurj).length_eq
    _ = ∑ i, Module.length R (C i).H0 := Module.length_pi_of_fintype R _

/-- For a finite family, the length of `H¹` of the product is the sum of the lengths of the
`H¹`'s (in `ℕ∞`). -/
theorem length_H1_pi [Fintype ι] (C : ∀ i, PeriodicComplex R (Ms i)) :
    Module.length R (pi C).H1 = ∑ i, Module.length R (C i).H1 :=
  length_H0_pi fun i ↦ (C i).swap

/-- The multiplicity of a finite product of periodic complexes with finite cohomology is the sum of
the multiplicities, and the product has finite cohomology. -/
theorem herbrand_pi [Fintype ι] (C : ∀ i, PeriodicComplex R (Ms i))
    (h : ∀ i, (C i).FiniteCohomology) :
    (pi C).FiniteCohomology ∧ (pi C).herbrand = ∑ i, (C i).herbrand := by
  have h0 : ∀ i ∈ Finset.univ, Module.length R (C i).H0 ≠ ⊤ := fun i _ ↦ (h i).1
  have h1 : ∀ i ∈ Finset.univ, Module.length R (C i).H1 ≠ ⊤ := fun i _ ↦ (h i).2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [length_H0_pi]
    exact ENat.sum_ne_top.2 h0
  · rw [length_H1_pi]
    exact ENat.sum_ne_top.2 h1
  · rw [herbrand, length_H0_pi, length_H1_pi, ENat.toNat_sum h0, ENat.toNat_sum h1,
      Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    rfl

end Pi

/-- The special periodic complex `(M, 0, x)` for `x : R`. -/
def smulComplex (M : Type*) [AddCommGroup M] [Module R M] (x : R) : PeriodicComplex R M where
  φ := 0
  ψ := LinearMap.lsmul R M x
  φ_ψ _ := rfl
  ψ_φ _ := by simp

/-- `H⁰(M, 0, x) = M ⧸ xM`, in terms of lengths. -/
theorem length_H0_smulComplex (x : R) :
    Module.length R (smulComplex M x).H0 = LocalOrdSymmetry.chiCoker x M := by
  rw [length_H0_eq_relLen]
  change relLen _ (LinearMap.ker (0 : M →ₗ[R] M)) = _
  rw [LinearMap.ker_zero, relLen_top]
  rfl

/-- `H¹(M, 0, x)` is the `x`-torsion of `M`, in terms of lengths. -/
theorem length_H1_smulComplex (x : R) :
    Module.length R (smulComplex M x).H1 = LocalOrdSymmetry.chiKer x M := by
  rw [length_H1_eq_relLen]
  change relLen (LinearMap.range (0 : M →ₗ[R] M)) _ = _
  rw [LinearMap.range_zero, relLen_bot]
  rfl

/-- `(M, 0, x)` has finite cohomology iff `M ⧸ xM` and the `x`-torsion of `M` have finite
length. -/
theorem finiteCohomology_smulComplex_iff (x : R) :
    (smulComplex M x).FiniteCohomology ↔
      LocalOrdSymmetry.chiCoker x M ≠ ⊤ ∧ LocalOrdSymmetry.chiKer x M ≠ ⊤ := by
  rw [FiniteCohomology, length_H0_smulComplex, length_H1_smulComplex]

/-- `e(M, 0, x) = length (M ⧸ xM) - length (ker x)` (Stacks, Section 42.2). -/
theorem herbrand_smulComplex (x : R) :
    (smulComplex M x).herbrand
      = ((LocalOrdSymmetry.chiCoker x M).toNat : ℤ) - (LocalOrdSymmetry.chiKer x M).toNat := by
  rw [herbrand, length_H0_smulComplex, length_H1_smulComplex]

/-- `(S, 0, x)` and `(T, 0, x)` have the same multiplicity when the submodules `S` and `T` are
equal (a transport lemma avoiding dependent rewriting in the carrier type). -/
theorem herbrand_smulComplex_submodule_congr {S T : Submodule R M} (h : S = T) (x : R) :
    (smulComplex S x).herbrand = (smulComplex T x).herbrand := by
  subst h
  rfl

/-- `(S, 0, x)` and `(T, 0, x)` have the same finiteness of cohomology when `S = T`. -/
theorem finiteCohomology_smulComplex_submodule_congr {S T : Submodule R M} (h : S = T) (x : R) :
    (smulComplex S x).FiniteCohomology ↔ (smulComplex T x).FiniteCohomology := by
  subst h
  rfl

/-- `e(M, 0, x) = e(N, 0, x)` for linearly isomorphic modules `M ≃ N`. -/
theorem herbrand_smulComplex_congr (e : M ≃ₗ[R] N) (x : R) :
    (smulComplex M x).herbrand = (smulComplex N x).herbrand :=
  herbrand_congr e (fun _ ↦ map_zero e) (fun m ↦ map_smul e x m)

/-- `(M, 0, x)` has finite cohomology iff `(N, 0, x)` does, for linearly isomorphic `M ≃ N`. -/
theorem finiteCohomology_smulComplex_congr (e : M ≃ₗ[R] N) (x : R) :
    (smulComplex M x).FiniteCohomology ↔ (smulComplex N x).FiniteCohomology :=
  finiteCohomology_congr e (fun _ ↦ map_zero e) (fun m ↦ map_smul e x m)

section Nilpotent

variable (φ : M →ₗ[R] M)

/-- `φ^(a+b) x = φ^a (φ^b x)`. -/
private theorem pow_add_apply' (a b : ℕ) (x : M) : (φ ^ (a + b)) x = (φ ^ a) ((φ ^ b) x) := by
  rw [pow_add, Module.End.mul_apply]

/-- The decreasing chain `U k = φ^k (ker φ^(k+1))` of submodules of `ker φ` used in the proof of
Stacks, Lemma 42.3.3. -/
def nilChain (k : ℕ) : Submodule R M := (LinearMap.ker (φ ^ (k + 1))).map (φ ^ k)

/-- The chain `U k` is decreasing. -/
theorem nilChain_antitone : Antitone (nilChain φ) := by
  refine antitone_nat_of_succ_le fun k ↦ ?_
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨φ z, ?_, ?_⟩
  · simp only [SetLike.mem_coe, LinearMap.mem_ker] at hz ⊢
    have := pow_add_apply' φ (k + 1) 1 z
    rw [pow_one] at this
    rw [← this]
    exact hz
  · change (φ ^ k) ((φ ^ 1) z) = (φ ^ (k + 1)) z
    rw [← pow_add_apply']

/-- The kernels of the powers of `φ` increase. -/
theorem ker_pow_mono : Monotone fun j ↦ LinearMap.ker (φ ^ j) := by
  refine monotone_nat_of_le_succ fun j x hx ↦ ?_
  rw [LinearMap.mem_ker] at hx ⊢
  rw [add_comm, pow_add_apply', hx, map_zero]

/-- For `φ ^ (p + q) = 0`, the length of `ker φ^p / im φ^q` is `∑_{j < p} ∑_{m < q} d_{j+m}`
where `d_k = relLen (U (k+1)) (U k)`. -/
theorem relLen_range_pow_ker_pow (p q : ℕ) (hpq : φ ^ (p + q) = 0) :
    relLen (LinearMap.range (φ ^ q)) (LinearMap.ker (φ ^ p))
      = ∑ j ∈ Finset.range p, ∑ m ∈ Finset.range q,
          relLen (nilChain φ (j + m + 1)) (nilChain φ (j + m)) := by
  set T := LinearMap.range (φ ^ q)
  set X : ℕ → Submodule R M := fun j ↦ LinearMap.ker (φ ^ j) ⊔ T with hXdef
  have hX : Monotone X := fun a b hab ↦ sup_le_sup_right (ker_pow_mono φ hab) T
  have hX0 : X 0 = T := by
    simp only [hXdef, pow_zero, Module.End.one_eq_id, LinearMap.ker_id, bot_sup_eq]
  have hTp : T ≤ LinearMap.ker (φ ^ p) := by
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, ← pow_add_apply', hpq, LinearMap.zero_apply]
  have hXp : X p = LinearMap.ker (φ ^ p) := sup_eq_left.2 hTp
  have step : ∀ j, relLen (X j) (X (j + 1)) = relLen (nilChain φ (j + q)) (nilChain φ j) := by
    intro j
    have hX1 : X (j + 1) = LinearMap.ker (φ ^ (j + 1)) ⊔ X j := by
      apply le_antisymm
      · exact sup_le_sup_left le_sup_right _
      · exact sup_le le_sup_left (sup_le_sup_right (ker_pow_mono φ (Nat.le_succ j)) T)
    rw [hX1, ← relLen_inf_eq_relLen_sup, relLen_map (φ ^ j) inf_le_left]
    · congr 1
      ext y
      constructor
      · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
        obtain ⟨k, hk, t, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw2
        rw [LinearMap.mem_ker] at hk
        refine ⟨z, ?_, ?_⟩
        · change (φ ^ (j + 1)) (k + (φ ^ q) z) = 0 at hw1
          rw [SetLike.mem_coe, LinearMap.mem_ker, show j + q + 1 = (j + 1) + q by omega,
            pow_add_apply']
          rw [map_add, add_comm j 1, pow_add_apply' φ 1 j, hk, map_zero, zero_add] at hw1
          rwa [add_comm 1 j] at hw1
        · rw [map_add, hk, zero_add, pow_add_apply']
      · rintro ⟨z, hz, rfl⟩
        refine ⟨(φ ^ q) z, ⟨?_, ?_⟩, ?_⟩
        · simp only [SetLike.mem_coe, LinearMap.mem_ker] at hz ⊢
          rw [← pow_add_apply', show j + 1 + q = j + q + 1 by omega, hz]
        · exact Submodule.mem_sup_right ⟨z, rfl⟩
        · rw [← pow_add_apply']
    · intro x hx
      exact ⟨hx.2, Submodule.mem_sup_left hx.1⟩
  rw [← hX0, ← hXp]
  have h := relLen_eq_sum_of_monotone X hX 0 p
  simp only [zero_add] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [step j, relLen_eq_sum_of_antitone _ (nilChain_antitone φ) j q]

/-- Symmetry: for `φ^(p+q) = 0`, `ker φ^p / im φ^q` and `ker φ^q / im φ^p` have the same
length (in `ℕ∞`). -/
theorem relLen_range_pow_ker_pow_comm (p q : ℕ) (hpq : φ ^ (p + q) = 0) :
    relLen (LinearMap.range (φ ^ q)) (LinearMap.ker (φ ^ p))
      = relLen (LinearMap.range (φ ^ p)) (LinearMap.ker (φ ^ q)) := by
  rw [relLen_range_pow_ker_pow φ p q hpq,
    relLen_range_pow_ker_pow φ q p (by rwa [add_comm]), Finset.sum_comm]
  simp only [add_comm]

/-- Each step `d_k` with `k + 2 ≤ n` is bounded by the length of `ker φ / im φ^(n-1)`. -/
theorem relLen_nilChain_le {n : ℕ} (hn0 : 0 < n) (hn : φ ^ n = 0) (k : ℕ) (hk : k + 2 ≤ n) :
    relLen (nilChain φ (k + 1)) (nilChain φ k)
      ≤ relLen (LinearMap.range (φ ^ (n - 1))) (LinearMap.ker φ) := by
  have h0 : nilChain φ 0 = LinearMap.ker φ := by
    rw [nilChain, pow_zero, zero_add, pow_one, Module.End.one_eq_id, Submodule.map_id]
  have h1 : nilChain φ (n - 1) = LinearMap.range (φ ^ (n - 1)) := by
    rw [nilChain, Nat.sub_add_cancel hn0, hn, LinearMap.ker_zero, Submodule.map_top]
  rw [← h0, ← h1]
  exact relLen_le_relLen (nilChain_antitone φ (by omega : k + 1 ≤ n - 1))
    (nilChain_antitone φ (Nat.le_succ k)) (nilChain_antitone φ (Nat.zero_le k))

/-- The periodic complex `(M, φ^i, φ^(n-i))` for `φ ^ n = 0` and `i ≤ n`. -/
def powComplex {n : ℕ} (hn : φ ^ n = 0) (i : ℕ) (hi : i ≤ n) : PeriodicComplex R M where
  φ := φ ^ i
  ψ := φ ^ (n - i)
  φ_ψ m := by rw [← pow_add_apply', Nat.add_sub_cancel' hi, hn, LinearMap.zero_apply]
  ψ_φ m := by rw [← pow_add_apply', Nat.sub_add_cancel hi, hn, LinearMap.zero_apply]

/-- Stacks, Lemma 42.3.3: if `φ ^ n = 0` with `n > 0` and `ker φ / im φ^(n-1)` has finite length,
then for every `i ≤ n` the complex `(M, φ^i, φ^(n-i))` has finite cohomology and multiplicity
`0`. -/
theorem herbrand_powComplex {n : ℕ} (hn0 : 0 < n) (hn : φ ^ n = 0)
    (hfin : Module.length R (LinearMap.ker φ ⧸
      (LinearMap.range (φ ^ (n - 1))).comap (LinearMap.ker φ).subtype) ≠ ⊤)
    (i : ℕ) (hi : i ≤ n) :
    (powComplex φ hn i hi).FiniteCohomology ∧ (powComplex φ hn i hi).herbrand = 0 := by
  have hpq : φ ^ (i + (n - i)) = 0 := by rwa [Nat.add_sub_cancel' hi]
  have e0 : Module.length R (powComplex φ hn i hi).H0
      = relLen (LinearMap.range (φ ^ (n - i))) (LinearMap.ker (φ ^ i)) := rfl
  have e1 : Module.length R (powComplex φ hn i hi).H1
      = relLen (LinearMap.range (φ ^ i)) (LinearMap.ker (φ ^ (n - i))) := rfl
  have hsym := relLen_range_pow_ker_pow_comm φ i (n - i) hpq
  have hne : relLen (LinearMap.range (φ ^ (n - i))) (LinearMap.ker (φ ^ i)) ≠ ⊤ := by
    rw [relLen_range_pow_ker_pow φ i (n - i) hpq]
    refine ENat.sum_ne_top.2 fun j hj ↦ ENat.sum_ne_top.2 fun m hm ↦ ?_
    rw [Finset.mem_range] at hj hm
    exact ne_top_of_le_ne_top hfin (relLen_nilChain_le φ hn0 hn (j + m) (by omega))
  refine ⟨⟨by rwa [e0], by rwa [e1, ← hsym]⟩, ?_⟩
  rw [herbrand, e0, e1, ← hsym, sub_self]

/-- The periodic complex `(M, φ^i, φ^j)` for `φ ^ (i + j) = 0`. Unlike `powComplex`, the second
differential is a literal power `φ ^ j`, with no natural-number subtraction. -/
def powComplex' (i j : ℕ) (h : φ ^ (i + j) = 0) : PeriodicComplex R M where
  φ := φ ^ i
  ψ := φ ^ j
  φ_ψ m := by rw [← pow_add_apply', h, LinearMap.zero_apply]
  ψ_φ m := by rw [← pow_add_apply', add_comm, h, LinearMap.zero_apply]

/-- Stacks, Lemma 42.3.3, in the form `(M, φ^i, φ^j)`: if `φ ^ (i + j) = 0` and
`ker φ / im φ^(i+j-1)` has finite length, then `(M, φ^i, φ^j)` has finite cohomology and
multiplicity `0`. -/
theorem herbrand_powComplex' (i j : ℕ) (h : φ ^ (i + j) = 0)
    (hfin : Module.length R (LinearMap.ker φ ⧸
      (LinearMap.range (φ ^ (i + j - 1))).comap (LinearMap.ker φ).subtype) ≠ ⊤) :
    (powComplex' φ i j h).FiniteCohomology ∧ (powComplex' φ i j h).herbrand = 0 := by
  have e0 : Module.length R (powComplex' φ i j h).H0
      = relLen (LinearMap.range (φ ^ j)) (LinearMap.ker (φ ^ i)) := rfl
  have e1 : Module.length R (powComplex' φ i j h).H1
      = relLen (LinearMap.range (φ ^ i)) (LinearMap.ker (φ ^ j)) := rfl
  have hsym := relLen_range_pow_ker_pow_comm φ i j h
  have hne : relLen (LinearMap.range (φ ^ j)) (LinearMap.ker (φ ^ i)) ≠ ⊤ := by
    rw [relLen_range_pow_ker_pow φ i j h]
    refine ENat.sum_ne_top.2 fun a ha ↦ ENat.sum_ne_top.2 fun b hb ↦ ?_
    rw [Finset.mem_range] at ha hb
    exact ne_top_of_le_ne_top hfin (relLen_nilChain_le φ (by omega) h (a + b) (by omega))
  refine ⟨⟨by rwa [e0], by rwa [e1, ← hsym]⟩, ?_⟩
  rw [herbrand, e0, e1, ← hsym, sub_self]

end Nilpotent

section Multiply

/-- The complex `(M, x φ, ψ)`. -/
def smulLeft (C : PeriodicComplex R M) (x : R) : PeriodicComplex R M where
  φ := x • C.φ
  ψ := C.ψ
  φ_ψ m := by rw [LinearMap.smul_apply, C.φ_ψ, smul_zero]
  ψ_φ m := by rw [LinearMap.smul_apply, map_smul, C.ψ_φ, smul_zero]

/-- The complex `(M, φ, x ψ)`. -/
def smulRight (C : PeriodicComplex R M) (x : R) : PeriodicComplex R M where
  φ := C.φ
  ψ := x • C.ψ
  φ_ψ m := by rw [LinearMap.smul_apply, map_smul, C.φ_ψ, smul_zero]
  ψ_φ m := by rw [LinearMap.smul_apply, C.ψ_φ, smul_zero]

/-- `(M, φ, xψ)` is the swap of `(M, xψ, φ)`. -/
theorem smulRight_eq_swap (C : PeriodicComplex R M) (x : R) :
    C.smulRight x = (C.swap.smulLeft x).swap := rfl

/-- Stacks, Lemma 42.3.4, in the case where `x` is a nonzerodivisor on `M`. -/
theorem herbrand_smulLeft_of_injective (C : PeriodicComplex R M) (x : R)
    (hinj : ∀ m : M, x • m = 0 → m = 0) (hC : C.FiniteCohomology)
    (hcok : LocalOrdSymmetry.chiCoker x (LinearMap.range C.φ) ≠ ⊤) :
    (C.smulLeft x).FiniteCohomology ∧ (smulComplex (LinearMap.range C.φ) x).FiniteCohomology ∧
      (C.smulLeft x).herbrand = C.herbrand - (smulComplex (LinearMap.range C.φ) x).herbrand := by
  have hker : LinearMap.ker (C.smulLeft x).φ = LinearMap.ker C.φ := by
    ext m
    simp only [LinearMap.mem_ker]
    change x • C.φ m = 0 ↔ C.φ m = 0
    exact ⟨hinj _, fun h ↦ by rw [h, smul_zero]⟩
  have hrange_le : LinearMap.range (C.smulLeft x).φ ≤ LinearMap.range C.φ := by
    rintro _ ⟨m, rfl⟩
    refine ⟨x • m, ?_⟩
    change C.φ (x • m) = x • C.φ m
    rw [map_smul]
  have e0 : Module.length R (C.smulLeft x).H0 = Module.length R C.H0 := by
    rw [length_H0_eq_relLen, length_H0_eq_relLen, hker]
    rfl
  have hcomap : (LinearMap.range (C.smulLeft x).φ).comap (LinearMap.range C.φ).subtype
      = LinearMap.range (LinearMap.lsmul R (LinearMap.range C.φ) x) := by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨⟨C.φ m, m, rfl⟩, Subtype.ext ?_⟩
      exact hm
    · rintro ⟨⟨_, m, rfl⟩, hm⟩
      exact ⟨m, congrArg Subtype.val hm⟩
  have hcoker_eq : relLen (LinearMap.range (C.smulLeft x).φ) (LinearMap.range C.φ)
      = LocalOrdSymmetry.chiCoker x (LinearMap.range C.φ) := by
    rw [relLen, hcomap]
    rfl
  have hkerx : LocalOrdSymmetry.chiKer x (LinearMap.range C.φ) = 0 := by
    have : LinearMap.ker (LinearMap.lsmul R (LinearMap.range C.φ) x) = ⊥ :=
      LinearMap.ker_eq_bot'.2 fun z hz ↦ Subtype.ext (hinj _ (congrArg Subtype.val hz))
    rw [LocalOrdSymmetry.chiKer, this, Module.length_bot]
  have e1 : Module.length R (C.smulLeft x).H1
      = LocalOrdSymmetry.chiCoker x (LinearMap.range C.φ) + Module.length R C.H1 := by
    rw [length_H1_eq_relLen, length_H1_eq_relLen]
    change relLen (LinearMap.range (C.smulLeft x).φ) (LinearMap.ker C.ψ)
      = _ + relLen (LinearMap.range C.φ) (LinearMap.ker C.ψ)
    rw [relLen_add hrange_le
      (show LinearMap.range C.φ ≤ LinearMap.ker C.ψ from C.swap.range_ψ_le_ker_φ), hcoker_eq]
  refine ⟨⟨by rw [e0]; exact hC.1, ?_⟩, (finiteCohomology_smulComplex_iff x).2 ⟨hcok, ?_⟩, ?_⟩
  · rw [e1, ne_eq, ENat.add_eq_top, not_or]
    exact ⟨hcok, hC.2⟩
  · rw [hkerx]
    exact ENat.zero_ne_top
  · rw [herbrand_smulComplex, herbrand, herbrand, e0, e1, hkerx, ENat.toNat_add hcok hC.2,
      ENat.toNat_zero]
    push_cast
    ring

variable [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]

/-- Stacks, Lemma 42.3.4 (first formula): `R` Noetherian local, `M` finite, `(M, φ, ψ)` with finite
cohomology and `x ∈ R` with `M ⧸ xM` of finite length. Then `(M, xφ, ψ)` and `(im φ, 0, x)` have
finite cohomology and `e(M, xφ, ψ) = e(M, φ, ψ) - e(im φ, 0, x)`. -/
theorem herbrand_smulLeft (C : PeriodicComplex R M) (hC : C.FiniteCohomology) (x : R)
    (hx : LocalOrdSymmetry.chiCoker x M ≠ ⊤) :
    (C.smulLeft x).FiniteCohomology ∧ (smulComplex (LinearMap.range C.φ) x).FiniteCohomology ∧
      (C.smulLeft x).herbrand = C.herbrand - (smulComplex (LinearMap.range C.φ) x).herbrand := by
  have hsupp := eq_maximalIdeal_of_chiCoker_ne_top hx
  -- the `x`-power torsion submodule `M'`
  obtain ⟨k, hk⟩ : ∃ k, LinearMap.ker (LinearMap.lsmul R M (x ^ (k + 1)))
      = LinearMap.ker (LinearMap.lsmul R M (x ^ k)) := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (LinearMap.lsmul R M x).eventually_iSup_ker_pow_eq
    refine ⟨N, ?_⟩
    rw [← lsmul_pow_eq, ← lsmul_pow_eq, ← hN (N + 1) (Nat.le_succ N), hN N le_rfl]
  set M' := LinearMap.ker (LinearMap.lsmul R M (x ^ k)) with hM'
  have hMφ : ∀ m ∈ M', C.φ m ∈ M' := fun m hm ↦ by
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at hm ⊢
    rw [← map_smul, hm, map_zero]
  have hMψ : ∀ m ∈ M', C.ψ m ∈ M' := fun m hm ↦ by
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at hm ⊢
    rw [← map_smul, hm, map_zero]
  have hM'len : Module.length R M' ≠ ⊤ := by
    refine length_ne_top_of_support fun p hp ↦ hsupp p
      (Module.support_subset_of_injective M'.subtype M'.injective_subtype hp) ?_
    have hann : x ^ k ∈ Module.annihilator R M' := Module.mem_annihilator.2 fun m ↦
      Subtype.ext (LinearMap.mem_ker.1 m.2)
    exact p.2.mem_of_pow_mem k (Module.annihilator_le_of_mem_support hp hann)
  set C'' := C.quotient M' hMφ hMψ
  have hinj : ∀ m : M ⧸ M', x • m = 0 → m = 0 := by
    intro m hm
    induction m using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm
      rw [Submodule.Quotient.mk_eq_zero, ← hk, LinearMap.mem_ker, LinearMap.lsmul_apply,
        pow_succ, mul_smul]
      exact LinearMap.mem_ker.1 hm
  have hqker : Module.length R (LinearMap.ker (C.quotientHom M' hMφ hMψ).f) ≠ ⊤ := by
    change Module.length R (LinearMap.ker M'.mkQ) ≠ ⊤
    rw [Submodule.ker_mkQ]
    exact hM'len
  have hqcok : Module.length R ((M ⧸ M') ⧸ LinearMap.range (C.quotientHom M' hMφ hMψ).f) ≠ ⊤ :=
    length_quotient_range_ne_top_of_surjective (quotientHom_surjective C M' hMφ hMψ)
  have hC'' : C''.FiniteCohomology := (finiteCohomology_iff_of_hom _ hqker hqcok).1 hC
  have heC : C.herbrand = C''.herbrand := herbrand_eq_of_hom _ hqker hqcok hC
  let F₁ : Hom (C.smulLeft x) (C''.smulLeft x) := ⟨M'.mkQ, fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hr : ∀ y ∈ LinearMap.range C.φ, M'.mkQ y ∈ LinearMap.range C''.φ := by
    rintro _ ⟨m, rfl⟩
    exact ⟨M'.mkQ m, rfl⟩
  let g : LinearMap.range C.φ →ₗ[R] LinearMap.range C''.φ := M'.mkQ.restrict hr
  let F₂ : Hom (smulComplex (LinearMap.range C.φ) x) (smulComplex (LinearMap.range C''.φ) x) :=
    ⟨g, fun _ ↦ by change g 0 = 0; exact map_zero g,
      fun m ↦ by change g (x • m) = x • g m; exact map_smul g x m⟩
  have hg_surj : Function.Surjective g := by
    rintro ⟨_, ⟨m', rfl⟩⟩
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective M' m'
    exact ⟨⟨C.φ m, m, rfl⟩, rfl⟩
  have hgker : Module.length R (LinearMap.ker F₂.f) ≠ ⊤ := by
    let j : LinearMap.ker g →ₗ[R] M' := LinearMap.codRestrict M'
      ((LinearMap.range C.φ).subtype ∘ₗ (LinearMap.ker g).subtype) fun z ↦ by
        have hz := congrArg Subtype.val (LinearMap.mem_ker.1 z.2)
        exact (Submodule.Quotient.mk_eq_zero M').1 hz
    have hj : Function.Injective j := fun a b hab ↦ by
      have h' := Subtype.ext_iff.1 hab
      exact Subtype.ext (Subtype.ext h')
    exact ne_top_of_le_ne_top hM'len (Module.length_le_of_injective j hj)
  have hgcok : Module.length R (LinearMap.range C''.φ ⧸ LinearMap.range F₂.f) ≠ ⊤ :=
    length_quotient_range_ne_top_of_surjective hg_surj
  have hT'' : LocalOrdSymmetry.chiCoker x (LinearMap.range C''.φ) ≠ ⊤ := by
    refine chiCoker_ne_top_of_support x fun p hp hxp ↦ hsupp p ?_ hxp
    exact Module.support_subset_of_surjective M'.mkQ (Submodule.mkQ_surjective M')
      (Module.support_subset_of_injective _ (Submodule.injective_subtype _) hp)
  obtain ⟨h₁, h₂, h₃⟩ := herbrand_smulLeft_of_injective C'' x hinj hC'' hT''
  have h₁' := (finiteCohomology_iff_of_hom F₁ hqker hqcok).2 h₁
  have h₂' := (finiteCohomology_iff_of_hom F₂ hgker hgcok).2 h₂
  refine ⟨h₁', h₂', ?_⟩
  rw [herbrand_eq_of_hom F₁ hqker hqcok h₁', herbrand_eq_of_hom F₂ hgker hgcok h₂', heC, h₃]

/-- Stacks, Lemma 42.3.4 (second formula): `R` Noetherian local, `M` finite, `(M, φ, ψ)` with finite
cohomology and `x ∈ R` with `M ⧸ xM` of finite length. Then `(M, φ, xψ)` and `(im ψ, 0, x)` have
finite cohomology and `e(M, φ, xψ) = e(M, φ, ψ) + e(im ψ, 0, x)`. -/
theorem herbrand_smulRight (C : PeriodicComplex R M) (hC : C.FiniteCohomology) (x : R)
    (hx : LocalOrdSymmetry.chiCoker x M ≠ ⊤) :
    (C.smulRight x).FiniteCohomology ∧ (smulComplex (LinearMap.range C.ψ) x).FiniteCohomology ∧
      (C.smulRight x).herbrand = C.herbrand + (smulComplex (LinearMap.range C.ψ) x).herbrand := by
  obtain ⟨h₁, h₂, h₃⟩ :=
    herbrand_smulLeft C.swap ((finiteCohomology_swap_iff C).2 hC) x hx
  refine ⟨?_, h₂, ?_⟩
  · rw [smulRight_eq_swap, finiteCohomology_swap_iff]
    exact h₁
  · rw [smulRight_eq_swap, herbrand_swap, h₃, herbrand_swap]
    change -(-C.herbrand - (smulComplex (LinearMap.range C.ψ) x).herbrand) = _
    ring

end Multiply

section Cyclic

open IsLocalRing LocalOrdSymmetry

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- If every prime containing `I` is the maximal ideal, then `A ⧸ I` is an Artinian `A`-module. -/
theorem isArtinian_quotient_of_primes (I : Ideal A)
    (hI : ∀ P : Ideal A, P.IsPrime → I ≤ P → P = maximalIdeal A) : IsArtinian A (A ⧸ I) := by
  rcases eq_or_ne I ⊤ with rfl | hne
  · exact isArtinian_of_finite
  · exact isArtinian_quotient_of_unique_prime (maximalIdeal A) I (le_maximalIdeal hne) hI

/-- Stacks, Lemma 42.3.1, for the cyclic module `A ⧸ J` supported on `{q, m}`: `A` Noetherian local,
`q` a non-maximal prime, `J` an ideal such that every prime containing `J` is `q` or the maximal
ideal, and `x ∉ q`. Then `(A ⧸ J, 0, x)` has finite cohomology and
`e(A ⧸ J, 0, x) = ord_{A ⧸ q}(x) · length_{A_q}((A ⧸ J)_q)`. -/
theorem herbrand_smulComplex_quotient (q : Ideal A) [hq : q.IsPrime] (hqm : ¬ q.IsMaximal)
    (J : Ideal A) (hJ : ∀ P : Ideal A, P.IsPrime → J ≤ P → P = q ∨ P = maximalIdeal A)
    (x : A) (hx : x ∉ q) :
    (smulComplex (A ⧸ J) x).FiniteCohomology ∧
      (smulComplex (A ⧸ J) x).herbrand
        = ((Ring.ord (A ⧸ q) (Ideal.Quotient.mk q x)).toNat * (lengthAt q (A ⧸ J)).toNat : ℕ) := by
  have hqne : q ≠ maximalIdeal A := fun h ↦ hqm (h ▸ maximalIdeal.isMaximal A)
  by_cases hJq : J ≤ q
  · have hart : IsArtinian A (A ⧸ (J ⊔ Ideal.span {x})) := by
      refine isArtinian_quotient_of_primes _ fun P hP hle ↦ ?_
      rcases hJ P hP (le_sup_left.trans hle) with rfl | h
      · exact absurd (hle (le_sup_right (a := J) (Ideal.mem_span_singleton_self x))) hx
      · exact h
    have hqmin : q ∈ J.minimalPrimes := by
      refine ⟨⟨hq, hJq⟩, fun P hP hPq ↦ ?_⟩
      rcases hJ P hP.1 hP.2 with rfl | h
      · exact le_rfl
      · exact absurd (le_antisymm (le_maximalIdeal hq.ne_top) (h ▸ hPq)) hqne
    have hsum : ∀ g : PrimeSpectrum A → ℕ∞,
        ∑ Q ∈ ({⟨q, hq⟩} : Finset (PrimeSpectrum A)), lengthAt Q.asIdeal (A ⧸ J) * g Q
          = lengthAt q (A ⧸ J) * g ⟨q, hq⟩ := fun g ↦ Finset.sum_singleton _ _
    have key := devissage x J hart {⟨q, hq⟩}
      (fun Q hQ ↦ by
        rcases hJ Q.asIdeal Q.2 hQ.1.2 with h | h
        · exact Finset.mem_singleton.2 (PrimeSpectrum.ext h)
        · have h1 : q ≤ Q.asIdeal := by rw [h]; exact le_maximalIdeal hq.ne_top
          have h2 := hQ.2 hqmin.1 h1
          exact absurd (le_antisymm (le_maximalIdeal hq.ne_top) (by rw [← h]; exact h2)) hqne)
      (fun Q hQ ↦ by rw [Finset.mem_singleton.1 hQ]; exact hqmin)
      (fun Q hQ hJQ ↦ by
        rcases hJ Q hQ hJQ with rfl | rfl
        · exact Or.inl hqmin
        · exact Or.inr (maximalIdeal.isMaximal A))
      J le_rfl
    rw [hsum, hsum, chiKer_quotient_prime_eq_zero q hx, mul_zero, add_zero] at key
    rw [chiCoker_quotient_ord x q] at key
    have hcok : chiCoker x (A ⧸ J) ≠ ⊤ := chiCoker_ne_top x J hart J le_rfl
    have hker : chiKer x (A ⧸ J) ≠ ⊤ := ne_top_of_le_ne_top hcok (key ▸ le_self_add)
    have hprod : lengthAt q (A ⧸ J) * Ring.ord (A ⧸ q) (Ideal.Quotient.mk q x) ≠ ⊤ :=
      ne_top_of_le_ne_top hcok (key ▸ le_add_self)
    refine ⟨(finiteCohomology_smulComplex_iff x).2 ⟨hcok, hker⟩, ?_⟩
    rw [herbrand_smulComplex, key, ENat.toNat_add hker hprod, ENat.toNat_mul]
    push_cast
    ring
  · obtain ⟨t, htJ, htq⟩ := SetLike.not_le_iff_exists.1 hJq
    have hart : IsArtinian A (A ⧸ J) := by
      refine isArtinian_quotient_of_primes _ fun P hP hle ↦ ?_
      rcases hJ P hP hle with rfl | h
      · exact absurd (hle htJ) htq
      · exact h
    have hlen : Module.length A (A ⧸ J) ≠ ⊤ := Module.length_ne_top
    have hL : lengthAt q (A ⧸ J) = 0 := lengthAt_eq_zero q htq fun m ↦ smul_quotient_eq_zero htJ m
    obtain ⟨h₁, h₂⟩ := (smulComplex (A ⧸ J) x).herbrand_eq_zero_of_length_ne_top hlen
    refine ⟨h₁, ?_⟩
    rw [h₂, hL]
    simp

end Cyclic

end PeriodicComplex

end GromovWitten.Algebra
