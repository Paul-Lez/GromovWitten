/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Finite modules with closed support

For a finite module over a Noetherian ring, support contained in the maximal spectrum is finite.
If the ring is a finite type algebra over a Noetherian Jacobson ring, the same support condition
also implies that the module is finite over the base ring.
-/

universe u

namespace Module

/-- A finite module over a Noetherian ring has finite support if every prime in its support is
maximal. -/
theorem support_finite_of_isNoetherianRing_of_support_maximal
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (h : ∀ p : PrimeSpectrum A, p ∈ Module.support A N → p.asIdeal.IsMaximal) :
    (Module.support A N).Finite := by
  have hf := Ideal.finite_minimalPrimes_of_isNoetherianRing A (Module.annihilator A N)
  have hinj : Function.Injective (PrimeSpectrum.asIdeal (R := A)) :=
    fun _ _ h => PrimeSpectrum.ext h
  apply (Set.Finite.preimage hinj.injOn hf).subset
  intro p hp
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le
    (Module.mem_support_iff_of_finite.mp hp)
  have hqs : (⟨q, hq.isPrime⟩ : PrimeSpectrum A) ∈ Module.support A N :=
    Module.mem_support_iff_of_finite.mpr hq.le
  have heq : q = p.asIdeal := (h _ hqs).eq_of_le p.isPrime.ne_top hqp
  change p.asIdeal ∈ (Module.annihilator A N).minimalPrimes
  rw [← heq]
  exact hq

end Module

section FiniteOverBase

variable {R A N : Type u} [CommRing R] [IsNoetherianRing R] [IsJacobsonRing R]
  [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
  [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
  [Module.Finite A N]

/-- A finite module supported only at maximal ideals is finite over a Noetherian Jacobson base
when its ambient algebra is of finite type. -/
theorem Module.finite_of_finiteType_of_support_maximal
    (h : ∀ p : PrimeSpectrum A, p ∈ Module.support A N → p.asIdeal.IsMaximal) :
    Module.Finite R N := by
  let I : Ideal A := Module.annihilator A N
  let Q : Type u := A ⧸ I
  let _ : Module Q N := Module.quotientAnnihilator
  have _ : Algebra.FiniteType R Q :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ_surjective R I)
  have _ : IsScalarTower R Q N :=
    (Module.isTorsionBySet_annihilator A N).isScalarTower (S := R)
  have _ : IsScalarTower A Q N :=
    (Module.isTorsionBySet_annihilator A N).isScalarTower (S := A)
  have hdim : Ring.KrullDimLE 0 Q := by
    apply Ring.KrullDimLE.mk₀
    intro J hJ
    let q : Ideal A := J.comap (Ideal.Quotient.mk I)
    have hqprime : q.IsPrime := Ideal.IsPrime.comap _
    have hIle : I ≤ q := by
      calc
        I = RingHom.ker (Ideal.Quotient.mk I) := by simp
        _ ≤ q := Ideal.ker_le_comap (Ideal.Quotient.mk I)
    have hsupport : (⟨q, hqprime⟩ : PrimeSpectrum A) ∈ Module.support A N := by
      rw [Module.mem_support_iff_of_finite]
      exact hIle
    have hqmax : q.IsMaximal := h _ hsupport
    have hqmap : (q.map (Ideal.Quotient.mk I)).IsMaximal :=
      hqmax.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (Ideal.ker_le_comap _)
    have hmap : q.map (Ideal.Quotient.mk I) = J := by
      change (J.comap (Ideal.Quotient.mk I)).map (Ideal.Quotient.mk I) = J
      exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective J
    rw [← hmap]
    exact hqmap
  have _ : IsNoetherianRing Q := Algebra.FiniteType.isNoetherianRing R Q
  have _ : IsArtinianRing Q :=
    (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero).2 ⟨inferInstance, hdim⟩
  have hQfinite : Module.Finite R Q := Module.finite_of_isArtinianRing R Q
  have hNQ : Module.Finite Q N :=
    Module.Finite.of_restrictScalars_finite A Q N
  exact Module.Finite.trans Q N

end FiniteOverBase
