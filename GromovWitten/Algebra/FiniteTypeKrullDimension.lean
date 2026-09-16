/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.Integral
import Mathlib.SetTheory.Cardinal.ENat
import Mathlib.RingTheory.FiniteStability

/-!
# Krull dimension of finitely generated algebras over a field

The Krull dimension of a finitely generated domain `A` over a field `k` is its transcendence
degree (`ringKrullDim_eq_toENat_trdeg`).  The proof is Noether normalization: `A` is finite over
a polynomial ring `k[X₁, …, Xₛ]`, integral extensions preserve Krull dimension
(`ringKrullDim_eq_of_isIntegral`, by going up and incomparability), and transcendence degree is
additive in towers and vanishes for algebraic extensions.

This is then used to compute the dimension of the closure of a point.  The coheight of a prime
`p` in `Spec A` is the dimension of `A ⧸ p` (`PrimeSpectrum.coheight_eq_ringKrullDim_quotient`),
so for a finitely generated `k`-algebra it is the transcendence degree of the residue field
`κ(p)` over `k` (`PrimeSpectrum.coheight_eq_toENat_trdeg_residueField`).

Finally, for a map `B → A` of finitely generated `k`-algebras and a prime `P` of `A` lying over
`Q`, the dimension of the closure of `P` is bounded by the dimension of the closure of `Q` plus
the dimension of the closure of `P` in the fibre `κ(Q) ⊗[B] A`
(`coheight_le_coheight_add_coheight_fiber`).  This is the algebraic form of the fibre-dimension
inequality for morphisms of schemes of finite type over a field.
-/

open TensorProduct

namespace GromovWitten.Algebra

universe u v

section Integral

variable (B A : Type*) [CommRing B] [CommRing A] [Algebra B A]

/-- An integral extension with injective structure map preserves Krull dimension: contraction
of primes is strictly monotone (incomparability) and chains lift (going up). -/
theorem ringKrullDim_eq_of_isIntegral [Algebra.IsIntegral B A] [FaithfulSMul B A] :
    ringKrullDim A = ringKrullDim B := by
  let f : PrimeSpectrum A → PrimeSpectrum B := PrimeSpectrum.comap (algebraMap B A)
  have hmono : StrictMono f := fun P Q h ↦ by
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at h ⊢
    exact Ideal.IsIntegral.comap_lt_comap h
  have hlift : ∀ (P : PrimeSpectrum A) (q : PrimeSpectrum B), f P < q →
      ∃ P', P < P' ∧ f P' = q := by
    intro P q hlt
    have hle : P.asIdeal.comap (algebraMap B A) ≤ q.asIdeal :=
      (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt |>.le
    obtain ⟨Q, hPQ, hQ, hQq⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral q.asIdeal P.asIdeal hle
    refine ⟨⟨Q, hQ⟩, ?_, PrimeSpectrum.ext hQq⟩
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    refine lt_of_le_of_ne hPQ fun hPQ' ↦ hlt.ne ?_
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal, hPQ', hQq]
  have hco : ∀ P : PrimeSpectrum A, Order.coheight P = Order.coheight (f P) :=
    Order.coheight_eq_of_strictMono f hmono hlift
  apply le_antisymm
  · rw [ringKrullDim, ringKrullDim, Order.krullDim_eq_iSup_coheight,
      Order.krullDim_eq_iSup_coheight]
    exact iSup_le fun P ↦ (hco P) ▸ le_iSup (fun q : PrimeSpectrum B ↦
      ((Order.coheight q : ℕ∞) : WithBot ℕ∞)) (f P)
  · rw [ringKrullDim, ringKrullDim, Order.krullDim_eq_iSup_coheight,
      Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun q ↦ ?_
    obtain ⟨⟨Q, hQ, hQq⟩⟩ := Ideal.nonempty_primesOver (S := A) q.asIdeal
    have hfQ : f ⟨Q, hQ⟩ = q := by
      apply PrimeSpectrum.ext
      rw [PrimeSpectrum.comap_asIdeal]
      exact hQq.over.symm
    rw [← hfQ, ← hco]
    exact le_iSup (fun P : PrimeSpectrum A ↦ ((Order.coheight P : ℕ∞) : WithBot ℕ∞)) _

end Integral

section Trdeg

/-- Transcendence degree is unchanged by an algebraic extension in a tower of domains. -/
theorem trdeg_eq_of_isAlgebraic (R : Type u) (S A : Type v) [CommRing R] [CommRing S]
    [CommRing A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Nontrivial R]
    [NoZeroDivisors A] [FaithfulSMul R S] [FaithfulSMul S A] [Algebra.IsAlgebraic S A] :
    Algebra.trdeg R A = Algebra.trdeg R S := by
  rw [← trdeg_add_eq R S (A := A), trdeg_eq_zero (R := S) (A := A), add_zero]

/-- Noether normalization: the Krull dimension of a finitely generated domain over a field is
its transcendence degree. -/
theorem ringKrullDim_eq_toENat_trdeg (k A : Type u) [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k A) : WithBot ℕ∞) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  algebraize [g.toRingHom]
  have : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := Algebra.IsIntegral.of_finite _ _
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  rw [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) k) A,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    trdeg_eq_of_isAlgebraic k (MvPolynomial (Fin s) k) A, MvPolynomial.trdeg_of_isDomain]
  simp

end Trdeg

section Coheight

variable {A : Type u} [CommRing A]

/-- The coheight of a prime `p` in `Spec A` is the Krull dimension of `A ⧸ p`. -/
theorem PrimeSpectrum.coheight_eq_ringKrullDim_quotient (p : PrimeSpectrum A) :
    ((Order.coheight p : ℕ∞) : WithBot ℕ∞) = ringKrullDim (A ⧸ p.asIdeal) := by
  let f : PrimeSpectrum (A ⧸ p.asIdeal) → PrimeSpectrum A :=
    PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal)
  have hmono : StrictMono f :=
    RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  have hrange : ∀ q : PrimeSpectrum A, p ≤ q → ∃ a, f a = q := by
    intro q hq
    have hmem : q ∈ Set.range f := by
      rw [range_comap_of_surjective _ (f := Ideal.Quotient.mk p.asIdeal)
        Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      exact hq
    exact hmem
  have hlift : ∀ a b, f a < b → ∃ a', a < a' ∧ f a' = b := by
    intro a b hab
    have hpb : p ≤ b := by
      refine le_trans ?_ hab.le
      change p.asIdeal ≤ a.asIdeal.comap (Ideal.Quotient.mk p.asIdeal)
      intro x hx
      change Ideal.Quotient.mk p.asIdeal x ∈ a.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact a.asIdeal.zero_mem
    obtain ⟨a', ha'⟩ := hrange b hpb
    refine ⟨a', ?_, ha'⟩
    rw [← ha'] at hab
    have hle : a ≤ a' := by
      change a.asIdeal ≤ a'.asIdeal
      rw [← Ideal.comap_le_comap_iff_of_surjective (Ideal.Quotient.mk p.asIdeal)
        Ideal.Quotient.mk_surjective]
      exact hab.le
    exact lt_of_le_of_ne hle fun h ↦ hab.ne (by rw [h])
  have h0 : f ⊥ = p := by
    apply PrimeSpectrum.ext
    change (⊥ : Ideal (A ⧸ p.asIdeal)).comap (Ideal.Quotient.mk p.asIdeal) = p.asIdeal
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have h1 : Order.coheight (⊥ : PrimeSpectrum (A ⧸ p.asIdeal)) = Order.coheight p := by
    rw [Order.coheight_eq_of_strictMono f hmono hlift ⊥, h0]
  rw [← h1, ringKrullDim, ← Order.coheight_bot_eq_krullDim]

/-- A fraction field is algebraic over its domain. -/
theorem isAlgebraic_of_isFractionRing' (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] : Algebra.IsAlgebraic A K :=
  ⟨fun x ↦ (IsFractionRing.isAlgebraic_iff A K K).mpr (Algebra.IsAlgebraic.isAlgebraic x)⟩

/-- The coheight of a prime of a finitely generated algebra over a field is the transcendence
degree of its residue field. -/
theorem PrimeSpectrum.coheight_eq_toENat_trdeg_residueField {k : Type u} [Field k] [Algebra k A]
    [Algebra.FiniteType k A] (p : PrimeSpectrum A) :
    Order.coheight p = Cardinal.toENat (Algebra.trdeg k p.asIdeal.ResidueField) := by
  have : Algebra.IsAlgebraic (A ⧸ p.asIdeal) p.asIdeal.ResidueField :=
    isAlgebraic_of_isFractionRing' _ _
  have h1 := PrimeSpectrum.coheight_eq_ringKrullDim_quotient p
  rw [ringKrullDim_eq_toENat_trdeg k (A ⧸ p.asIdeal),
    ← trdeg_eq_of_isAlgebraic k (A ⧸ p.asIdeal) p.asIdeal.ResidueField] at h1
  exact_mod_cast h1

end Coheight

section FiberDimension

variable {k B A : Type u} [Field k] [CommRing B] [CommRing A]
  [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A]

variable (B) in
/-- The prime of the fibre ring `κ(Q) ⊗[B] A` corresponding to a prime `P` of `A`, where `Q` is
the contraction of `P` to `B`. -/
noncomputable def fiberPrime (P : PrimeSpectrum A) :
    PrimeSpectrum ((PrimeSpectrum.comap (algebraMap B A) P).asIdeal.Fiber A) :=
  PrimeSpectrum.preimageOrderIsoFiber B A (PrimeSpectrum.comap (algebraMap B A) P) ⟨P, rfl⟩

variable (B) in
/-- The contraction of the fibre prime along `A → κ(Q) ⊗[B] A` is the original prime. -/
theorem fiberPrime_comap_includeRight (P : PrimeSpectrum A) :
    (fiberPrime B P).asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = P.asIdeal := by
  have h := PrimeSpectrum.preimageEquivFiber_symm_apply_coe B A
    (PrimeSpectrum.comap (algebraMap B A) P) (fiberPrime B P)
  have h' : (PrimeSpectrum.preimageEquivFiber B A (PrimeSpectrum.comap (algebraMap B A) P)).symm
      (fiberPrime B P) = ⟨P, rfl⟩ :=
    (PrimeSpectrum.preimageEquivFiber B A _).symm_apply_apply ⟨P, rfl⟩
  rw [h'] at h
  exact congrArg PrimeSpectrum.asIdeal h.symm

/-- In a tower `C ⊆ D ⊆ E` with `E` algebraic over `D`, and `C ⊆ κ ⊆ E` with `κ` algebraic
over `C`, the transcendence degrees of `D` over `C` and of `E` over `κ` agree. -/
theorem trdeg_eq_of_algebraic_towers (C D E κ : Type u) [CommRing C] [CommRing D] [CommRing E]
    [CommRing κ] [Nontrivial C] [NoZeroDivisors E] [Algebra C D] [Algebra D E] [Algebra C E]
    [Algebra C κ] [Algebra κ E] [IsScalarTower C D E] [IsScalarTower C κ E]
    [FaithfulSMul C D] [FaithfulSMul D E] [FaithfulSMul C κ] [FaithfulSMul κ E]
    [Algebra.IsAlgebraic D E] [Algebra.IsAlgebraic C κ] :
    Algebra.trdeg C D = Algebra.trdeg κ E := by
  have h1 := trdeg_add_eq C D (A := E)
  have h2 := trdeg_add_eq C κ (A := E)
  rw [trdeg_eq_zero (R := D) (A := E), add_zero] at h1
  rw [trdeg_eq_zero (R := C) (A := κ), zero_add] at h2
  rw [h1, h2]

set_option maxHeartbeats 800000 in
-- The tower of quotient and fibre algebras involves many instance diamonds to unfold.
variable (k B) in
/-- Fibre-dimension formula for a prime `P` of a finitely generated `k`-algebra `A` over a
finitely generated `k`-algebra `B`: the dimension of the closure of `P` is the dimension of the
closure of its contraction `Q` plus the dimension of the closure of `P` in the fibre
`κ(Q) ⊗[B] A`.  The proof is the additivity of transcendence degree in the tower
`k ⊆ B ⧸ Q ⊆ A ⧸ P`, together with the fact that `(κ(Q) ⊗[B] A) ⧸ P'` is algebraic over
`A ⧸ P` and over `κ(Q)`. -/
theorem coheight_eq_coheight_add_coheight_fiberPrime [Algebra.FiniteType k B]
    [Algebra.FiniteType k A] (P : PrimeSpectrum A) :
    Order.coheight P =
      Order.coheight (PrimeSpectrum.comap (algebraMap B A) P) +
        Order.coheight (fiberPrime B P) := by
  set Q := PrimeSpectrum.comap (algebraMap B A) P with hQ
  set P' := fiberPrime B P with hP'
  have hlies : P.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  have : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType k B A
  have instDomD : IsDomain (A ⧸ P.asIdeal) := Ideal.Quotient.isDomain P.asIdeal
  have instDomC : IsDomain (B ⧸ Q.asIdeal) := Ideal.Quotient.isDomain Q.asIdeal
  have instDomE : IsDomain (Q.asIdeal.Fiber A ⧸ P'.asIdeal) := Ideal.Quotient.isDomain P'.asIdeal
  have instFTF : Algebra.FiniteType Q.asIdeal.ResidueField (Q.asIdeal.Fiber A) :=
    Algebra.FiniteType.baseChange (R := B) (A := A) Q.asIdeal.ResidueField
  have instFTE : Algebra.FiniteType Q.asIdeal.ResidueField (Q.asIdeal.Fiber A ⧸ P'.asIdeal) :=
    inferInstance
  have instFTD : Algebra.FiniteType k (A ⧸ P.asIdeal) := inferInstance
  have instFTC : Algebra.FiniteType k (B ⧸ Q.asIdeal) := inferInstance
  -- The algebra structures on the quotient domains.
  let instCD : Algebra (B ⧸ Q.asIdeal) (A ⧸ P.asIdeal) :=
    Ideal.Quotient.algebraOfLiesOver P.asIdeal Q.asIdeal
  have hCD : ∀ b : B, algebraMap (B ⧸ Q.asIdeal) (A ⧸ P.asIdeal) (Ideal.Quotient.mk Q.asIdeal b) =
      Ideal.Quotient.mk P.asIdeal (algebraMap B A b) := fun b ↦
    Ideal.Quotient.algebraMap_mk_of_liesOver P.asIdeal Q.asIdeal b
  have hPcomap : P.asIdeal = P'.asIdeal.comap
      (Algebra.TensorProduct.includeRight (R := B) (A := Q.asIdeal.ResidueField)
        (B := A)).toRingHom :=
    (fiberPrime_comap_includeRight B P).symm
  -- `A` acts on the fibre through the right tensor factor.
  let _ : Algebra A (Q.asIdeal.Fiber A) := Algebra.TensorProduct.rightAlgebra
  have hAF : ∀ a : A, algebraMap A (Q.asIdeal.Fiber A) a = 1 ⊗ₜ[B] a := fun _ ↦ rfl
  have hPcomap' : P.asIdeal ≤ P'.asIdeal.comap (algebraMap A (Q.asIdeal.Fiber A)) :=
    le_of_eq hPcomap
  let instDE : Algebra (A ⧸ P.asIdeal) (Q.asIdeal.Fiber A ⧸ P'.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap hPcomap'
  have hψ : ∀ a : A, algebraMap (A ⧸ P.asIdeal) (Q.asIdeal.Fiber A ⧸ P'.asIdeal)
      (Ideal.Quotient.mk P.asIdeal a) = Ideal.Quotient.mk P'.asIdeal (1 ⊗ₜ[B] a) := fun a ↦ rfl
  have hψinj : Function.Injective
      (algebraMap (A ⧸ P.asIdeal) (Q.asIdeal.Fiber A ⧸ P'.asIdeal)) :=
    Ideal.quotientMap_injective' (le_of_eq hPcomap.symm)
  -- `B ⧸ Q` acts on the fibre quotient because `P'` lies over `Q`.
  have hCE : ∀ b : B, algebraMap (B ⧸ Q.asIdeal) (Q.asIdeal.Fiber A ⧸ P'.asIdeal)
      (Ideal.Quotient.mk Q.asIdeal b) =
      Ideal.Quotient.mk P'.asIdeal (algebraMap B (Q.asIdeal.Fiber A) b) := fun b ↦
    Ideal.Quotient.algebraMap_mk_of_liesOver P'.asIdeal Q.asIdeal b
  let instCE : Algebra (B ⧸ Q.asIdeal) (Q.asIdeal.Fiber A ⧸ P'.asIdeal) :=
    Ideal.Quotient.algebraOfLiesOver P'.asIdeal Q.asIdeal
  have towerCκE : @IsScalarTower (B ⧸ Q.asIdeal) Q.asIdeal.ResidueField
      (Q.asIdeal.Fiber A ⧸ P'.asIdeal) Algebra.toSMul Algebra.toSMul instCE.toSMul := by
    refine @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ _ _ instCE fun x ↦ ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hCE, show Ideal.Quotient.mk Q.asIdeal b = algebraMap B (B ⧸ Q.asIdeal) b from rfl,
      ← IsScalarTower.algebraMap_apply B (B ⧸ Q.asIdeal) Q.asIdeal.ResidueField]
    change _ = Ideal.Quotient.mk P'.asIdeal (algebraMap Q.asIdeal.ResidueField (Q.asIdeal.Fiber A)
      (algebraMap B Q.asIdeal.ResidueField b))
    rw [← IsScalarTower.algebraMap_apply B Q.asIdeal.ResidueField (Q.asIdeal.Fiber A)]
  have towerCDE : @IsScalarTower (B ⧸ Q.asIdeal) (A ⧸ P.asIdeal)
      (Q.asIdeal.Fiber A ⧸ P'.asIdeal) instCD.toSMul instDE.toSMul instCE.toSMul := by
    refine @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ instCD instDE instCE fun x ↦ ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hCE, hCD, hψ, IsScalarTower.algebraMap_apply B A (Q.asIdeal.Fiber A), hAF]
  have towerkCD : @IsScalarTower k (B ⧸ Q.asIdeal) (A ⧸ P.asIdeal)
      Algebra.toSMul instCD.toSMul Algebra.toSMul := by
    refine @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ _ instCD _ fun x ↦ ?_
    rw [IsScalarTower.algebraMap_apply k B (B ⧸ Q.asIdeal) x, Ideal.Quotient.algebraMap_eq, hCD,
      ← IsScalarTower.algebraMap_apply k B A, IsScalarTower.algebraMap_apply k A (A ⧸ P.asIdeal),
      Ideal.Quotient.algebraMap_eq]
  -- Injectivity of the structure maps.
  have : FaithfulSMul (B ⧸ Q.asIdeal) (A ⧸ P.asIdeal) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.quotientMap_injective
  have : FaithfulSMul (A ⧸ P.asIdeal) (Q.asIdeal.Fiber A ⧸ P'.asIdeal) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hψinj
  have : FaithfulSMul (B ⧸ Q.asIdeal) Q.asIdeal.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      Q.asIdeal.injective_algebraMap_quotient_residueField
  -- The fibre quotient is algebraic over `A ⧸ P`.
  have : Algebra.IsAlgebraic (A ⧸ P.asIdeal) (Q.asIdeal.Fiber A ⧸ P'.asIdeal) := by
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨r, hr, s, hrs⟩ := Ideal.Fiber.exists_smul_eq_one_tmul Q.asIdeal x
    have hy0 : algebraMap (A ⧸ P.asIdeal) (Q.asIdeal.Fiber A ⧸ P'.asIdeal)
        (Ideal.Quotient.mk P.asIdeal (algebraMap B A r)) ≠ 0 := by
      intro h
      have h' : Ideal.Quotient.mk P.asIdeal (algebraMap B A r) = 0 :=
        hψinj (by rw [h, map_zero])
      exact hr (Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp h'))
    have hmul : algebraMap (A ⧸ P.asIdeal) (Q.asIdeal.Fiber A ⧸ P'.asIdeal)
        (Ideal.Quotient.mk P.asIdeal (algebraMap B A r)) * Ideal.Quotient.mk P'.asIdeal x =
        algebraMap (A ⧸ P.asIdeal) (Q.asIdeal.Fiber A ⧸ P'.asIdeal)
          (Ideal.Quotient.mk P.asIdeal s) := by
      have h1 : (1 : Q.asIdeal.ResidueField) ⊗ₜ[B] algebraMap B A r =
          algebraMap B (Q.asIdeal.Fiber A) r := by
        rw [← Algebra.TensorProduct.includeRight_apply]
        exact Algebra.TensorProduct.includeRight.commutes r
      calc algebraMap (A ⧸ P.asIdeal) (Q.asIdeal.Fiber A ⧸ P'.asIdeal)
            (Ideal.Quotient.mk P.asIdeal (algebraMap B A r)) * Ideal.Quotient.mk P'.asIdeal x
          = Ideal.Quotient.mk P'.asIdeal (algebraMap B (Q.asIdeal.Fiber A) r * x) := by
            rw [hψ, ← map_mul, h1]
        _ = Ideal.Quotient.mk P'.asIdeal (r • x) := by rw [Algebra.smul_def]
        _ = Ideal.Quotient.mk P'.asIdeal ((1 : Q.asIdeal.ResidueField) ⊗ₜ[B] s) := by rw [hrs]
        _ = _ := (hψ s).symm
    have halg1 : IsAlgebraic (A ⧸ P.asIdeal) (algebraMap (A ⧸ P.asIdeal)
        (Q.asIdeal.Fiber A ⧸ P'.asIdeal) (Ideal.Quotient.mk P.asIdeal (algebraMap B A r))) :=
      isAlgebraic_algebraMap _
    have halg2 : IsAlgebraic (A ⧸ P.asIdeal) (algebraMap (A ⧸ P.asIdeal)
        (Q.asIdeal.Fiber A ⧸ P'.asIdeal) (Ideal.Quotient.mk P.asIdeal (algebraMap B A r)) *
        Ideal.Quotient.mk P'.asIdeal x) := by
      rw [hmul]
      exact isAlgebraic_algebraMap _
    have hy : algebraMap (A ⧸ P.asIdeal) (Q.asIdeal.Fiber A ⧸ P'.asIdeal)
        (Ideal.Quotient.mk P.asIdeal (algebraMap B A r)) ∈
        nonZeroDivisors (Q.asIdeal.Fiber A ⧸ P'.asIdeal) :=
      mem_nonZeroDivisors_of_ne_zero hy0
    exact IsAlgebraic.of_mul (R := A ⧸ P.asIdeal) (S := Q.asIdeal.Fiber A ⧸ P'.asIdeal)
      hy halg1 halg2
  have : Algebra.IsAlgebraic (B ⧸ Q.asIdeal) Q.asIdeal.ResidueField :=
    isAlgebraic_of_isFractionRing' _ _
  -- Assemble the transcendence-degree computation.
  have hP := PrimeSpectrum.coheight_eq_ringKrullDim_quotient P
  have hQ' := PrimeSpectrum.coheight_eq_ringKrullDim_quotient Q
  have hP'' := PrimeSpectrum.coheight_eq_ringKrullDim_quotient P'
  rw [ringKrullDim_eq_toENat_trdeg k] at hP hQ'
  rw [ringKrullDim_eq_toENat_trdeg Q.asIdeal.ResidueField] at hP''
  have hP1 : Order.coheight P = Cardinal.toENat (Algebra.trdeg k (A ⧸ P.asIdeal)) := by
    exact_mod_cast hP
  have hQ1 : Order.coheight Q = Cardinal.toENat (Algebra.trdeg k (B ⧸ Q.asIdeal)) := by
    exact_mod_cast hQ'
  have hP2 : Order.coheight P' =
      Cardinal.toENat (Algebra.trdeg Q.asIdeal.ResidueField (Q.asIdeal.Fiber A ⧸ P'.asIdeal)) := by
    exact_mod_cast hP''
  rw [hP1, hQ1, hP2, ← trdeg_eq_of_algebraic_towers (B ⧸ Q.asIdeal) (A ⧸ P.asIdeal)
    (Q.asIdeal.Fiber A ⧸ P'.asIdeal) Q.asIdeal.ResidueField,
    ← map_add, trdeg_add_eq k (B ⧸ Q.asIdeal) (A := A ⧸ P.asIdeal)]

end FiberDimension

end GromovWitten.Algebra
