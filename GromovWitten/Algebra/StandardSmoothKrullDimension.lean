/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Krull dimension of standard smooth algebras over a field

A standard smooth algebra of relative dimension `n` over a ring `R` factors as an étale algebra
over the polynomial ring `R[X₁, …, Xₙ]`.  Over a field `k` this pins down the Krull dimension:

* every maximal ideal of `k[X₁, …, Xₙ]` has height `n`
  (`MvPolynomial.height_eq_of_isMaximal`), by induction on `n` using the height formula for
  maximal ideals of a polynomial ring over a Noetherian Jacobson ring;
* an étale algebra `A` over `B = k[X₁, …, Xₙ]` has dimension at most `n`, because its fibres
  over `Spec B` are Artinian, and at least `n` when `A ≠ 0`, because the contraction of a
  maximal ideal of `A` is a maximal ideal of `B` (Zariski's lemma) whose chain of primes lifts
  along the flat map `B → A` by going down.

The resulting statement `ringKrullDim_eq_of_isStandardSmoothOfRelativeDimension` is the algebraic
input identifying the relative dimension of the smooth locus of a family of curves.
-/

open TensorProduct

namespace GromovWitten.Algebra

universe u v

section MvPolynomial

variable (k : Type u) [Field k]

/-- Every maximal ideal of `k[X₁, …, Xₙ]` has height `n`. -/
theorem MvPolynomial.height_eq_of_isMaximal :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal → M.height = n := by
  intro n
  induction n with
  | zero =>
    intro M hM
    let e : MvPolynomial (Fin 0) k ≃+* k := (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toRingEquiv
    have hmax : (M.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hbot : M.map e = ⊥ := (Ideal.eq_bot_or_top _).resolve_right hmax.ne_top
    have h := e.height_map M
    rw [← h]
    change (M.map e).height = _
    rw [hbot, Ideal.height_bot]
    simp
  | succ n ih =>
    intro M hM
    let e : MvPolynomial (Fin (n + 1)) k ≃+* Polynomial (MvPolynomial (Fin n) k) :=
      (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let M' : Ideal (Polynomial (MvPolynomial (Fin n) k)) := M.map e
    have hM' : M'.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p : Ideal (MvPolynomial (Fin n) k) := M'.comap Polynomial.C
    have hp : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing M'
    have : M'.LiesOver p := ⟨by
      change M'.comap (algebraMap _ _) = M'.comap Polynomial.C
      rw [Polynomial.algebraMap_eq]⟩
    have h1 : M'.height = p.height + 1 := Polynomial.height_eq_height_add_one p M'
    have h2 : p.height = n := ih p hp
    have h := e.height_map M
    rw [← h]
    change M'.height = _
    rw [h1, h2]
    push_cast
    rfl

end MvPolynomial

section StandardSmooth

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

/-- A nontrivial standard smooth algebra of relative dimension `n` over a field has Krull
dimension exactly `n`. -/
theorem ringKrullDim_eq_of_isStandardSmoothOfRelativeDimension [Nontrivial A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n k A] : ringKrullDim A = n := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n k A
  have : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  algebraize [g.toRingHom]
  have : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have hB : ringKrullDim (MvPolynomial (Fin n) k) = n := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have : Algebra.QuasiFinite (MvPolynomial (Fin n) k) A := inferInstance
  -- Upper bound: the fibres of `Spec A → Spec B` are Artinian, hence zero-dimensional.
  have hle : ringKrullDim A ≤ n := by
    have key := Order.krullDim_le_of_krullDim_preimage_le' (m := 0)
      (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) k) A))
      (fun _ _ h ↦ Ideal.comap_mono h) (fun p ↦ by
        rw [Order.krullDim_eq_of_orderIso
          (PrimeSpectrum.preimageOrderIsoFiber (MvPolynomial (Fin n) k) A p)]
        have h0 : Ring.KrullDimLE 0 (p.asIdeal.Fiber A) := inferInstance
        have := Ring.krullDimLE_iff.mp h0
        simpa [ringKrullDim] using this)
    change Order.krullDim (PrimeSpectrum A) ≤ (n : WithBot ℕ∞)
    have hB' : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin n) k)) = n := hB
    rw [hB'] at key
    simpa using key
  -- Lower bound: lift a maximal chain of `B` along the flat map `B → A`.
  have hge : (n : WithBot ℕ∞) ≤ ringKrullDim A := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal A
    have := hP
    let p : Ideal (MvPolynomial (Fin n) k) := P.under (MvPolynomial (Fin n) k)
    have hpprime : p.IsPrime := Ideal.IsPrime.under (MvPolynomial (Fin n) k) P
    have hpmax : p.IsMaximal := by
      let _ : Field (A ⧸ P) := Ideal.Quotient.field P
      have : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
      have : Algebra.IsIntegral k (A ⧸ P) := Algebra.IsIntegral.of_finite k (A ⧸ P)
      let φ : MvPolynomial (Fin n) k ⧸ p →ₐ[k] A ⧸ P :=
        Ideal.quotientMapₐ P (IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) A) le_rfl
      have hφ : Function.Injective φ := by
        change Function.Injective
          (Ideal.quotientMap P (algebraMap (MvPolynomial (Fin n) k) A) le_rfl)
        exact Ideal.quotientMap_injective
      have : Algebra.IsIntegral k (MvPolynomial (Fin n) k ⧸ p) :=
        ⟨fun x ↦ (isIntegral_algHom_iff φ hφ).mp (Algebra.IsIntegral.isIntegral (φ x))⟩
      exact Ideal.Quotient.maximal_of_isField p
        (isField_of_isIntegral_of_isField' (Field.toIsField k))
    have hpn : p.height = n := MvPolynomial.height_eq_of_isMaximal k n p hpmax
    obtain ⟨l, hl, hlen⟩ := p.exists_ltSeries_length_eq_height
    have : Algebra.HasGoingDown (MvPolynomial (Fin n) k) A := Algebra.HasGoingDown.of_flat
    have : P.LiesOver l.last.asIdeal := by
      rw [hl]
      exact ⟨rfl⟩
    obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
    have hlen' : l.length = n := by
      have := hlen.trans hpn
      exact_mod_cast this
    change (n : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum A)
    rw [Order.le_krullDim_iff]
    exact ⟨L, hL.trans hlen'⟩
  exact le_antisymm hle hge

end StandardSmooth

end GromovWitten.Algebra
