/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors, OpenAI Codex
-/

import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Flatness from reduced fibre dimensions

Over a reduced ring, a finite module with locally constant residue-field fibre
dimension is flat; finite presentation then upgrades flatness to projectivity.
-/

open TensorProduct
open scoped TensorProduct
noncomputable section

namespace GromovWitten.Algebra

universe u v

variable {R : Type u} [CommRing R] [IsReduced R]
variable {M : Type v} [AddCommGroup M] [Module R M]

private theorem reduced_cover_injective {n : ℕ} (f : (Fin n → R) →ₗ[R] M)
    (hf : Function.Surjective f)
    (hdim : ∀ p : PrimeSpectrum R,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) = n) :
    Function.Injective f := by
  let : Module.Finite R M := Module.Finite.of_surjective f hf
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  funext i
  apply isNilpotent_iff_eq_zero.mp
  apply nilpotent_iff_mem_prime.mpr
  intro P hP
  let : P.IsPrime := hP
  let K := P.ResidueField
  have hsurj : Function.Surjective (f.baseChange K) := f.lTensor_surjective K hf
  have hdim' : Module.finrank K (K ⊗[R] (Fin n → R)) =
      Module.finrank K (K ⊗[R] M) := by
    rw [hdim ⟨P, hP⟩]
    simpa using Module.finrank_eq_card_basis ((Pi.basisFun R (Fin n)).baseChange K)
  have hinj : Function.Injective (f.baseChange K) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mpr hsurj
  have hx' : (1 : K) ⊗ₜ[R] x = 0 := by
    apply hinj
    simp only [LinearMap.baseChange_tmul, map_zero]
    rw [show f x = 0 from hx, TensorProduct.tmul_zero]
  have hi := congrArg
    (fun z => AlgebraTensorModule.rid R K K ((LinearMap.proj i).baseChange K z)) hx'
  apply Ideal.algebraMap_residueField_eq_zero.mp
  simpa only [map_zero, LinearMap.baseChange_tmul, LinearMap.proj_apply,
    AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one] using hi

private theorem reduced_local_free [IsLocalRing R] [Module.Finite R M]
    (hconst : ∀ p q : PrimeSpectrum R,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) =
      Module.finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] M)) :
    Module.Free R M := by
  let k := IsLocalRing.ResidueField R
  let n := Module.finrank k (k ⊗[R] M)
  let b := Module.finBasis k (k ⊗[R] M)
  obtain ⟨v, hv⟩ := (TensorProduct.mk_surjective R M k
    IsLocalRing.residue_surjective).comp_left b
  let f := Fintype.linearCombination R v
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis v b (congr_fun hv)
  have hdim : ∀ p : PrimeSpectrum R,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) = n := by
    intro p
    let m := IsLocalRing.maximalIdeal R
    let K := m.ResidueField
    rw [hconst p ⟨m, inferInstance⟩]
    change Module.finrank K (K ⊗[R] M) = Module.finrank k (k ⊗[R] M)
    rw [← (AlgebraTensorModule.cancelBaseChange R k K K M).finrank_eq]
    exact Module.finrank_baseChange
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f
    ⟨reduced_cover_injective f hf hdim, hf⟩)

universe w

variable {S : Type w} [CommRing S] [Algebra R S]

omit [IsReduced R] in
/-- Residue-field fibre dimensions are unchanged after scalar extension. -/
theorem fibre_dim_base_change (q : PrimeSpectrum S) :
    Module.finrank q.asIdeal.ResidueField
        (q.asIdeal.ResidueField ⊗[S] (S ⊗[R] M)) =
      Module.finrank (q.comap (algebraMap R S)).asIdeal.ResidueField
        ((q.comap (algebraMap R S)).asIdeal.ResidueField ⊗[R] M) := by
  let p := q.comap (algebraMap R S)
  let K := p.asIdeal.ResidueField
  let L := q.asIdeal.ResidueField
  let φ : K →+* L := Ideal.ResidueField.map p.asIdeal q.asIdeal
    (algebraMap R S) rfl
  let : Algebra K L := φ.toAlgebra
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R L r = φ (algebraMap R K r)
    exact (IsScalarTower.algebraMap_apply R S L r).trans
      (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal
        (algebraMap R S) rfl r).symm
  change Module.finrank L (L ⊗[S] (S ⊗[R] M)) = Module.finrank K (K ⊗[R] M)
  rw [(AlgebraTensorModule.cancelBaseChange R S L L M).finrank_eq,
    ← (AlgebraTensorModule.cancelBaseChange R K L L M).finrank_eq]
  exact Module.finrank_baseChange

omit [IsReduced R] in
private theorem locally_constant_equal [IsLocalRing R] (d : PrimeSpectrum R → ℕ)
    (hd : IsLocallyConstant d) (p q : PrimeSpectrum R) : d p = d q := by
  have heq (x : PrimeSpectrum R) : d x = d (IsLocalRing.closedPoint R) := by
    apply (IsLocalRing.specializes_closedPoint x).mem_open
      (hd.isOpen_fiber (d (IsLocalRing.closedPoint R)))
    rfl
  exact (heq p).trans (heq q).symm

variable [Module.Finite R M]

/-- A finite module over a reduced ring with locally constant fibre dimension is flat. -/
theorem reduced_fibre_flat (hd : IsLocallyConstant (fun p : PrimeSpectrum R =>
    Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M))) :
    Module.Flat R M := by
  apply Module.flat_of_localized_maximal
  intro P hP
  let S := Localization.AtPrime P
  have hdim : IsLocallyConstant (fun q : PrimeSpectrum S =>
      Module.finrank q.asIdeal.ResidueField
        (q.asIdeal.ResidueField ⊗[S] (S ⊗[R] M))) := by
    have h := hd.comp_continuous (PrimeSpectrum.continuous_comap (algebraMap R S))
    convert h using 1
    funext q
    exact fibre_dim_base_change (M := M) q
  have : Module.Free S (S ⊗[R] M) :=
    reduced_local_free (fun p q => locally_constant_equal _ hdim p q)
  have : Module.Free S (LocalizedModule P.primeCompl M) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct P.primeCompl M).symm
  exact Module.Flat.trans R S (LocalizedModule P.primeCompl M)

/-- A finitely presented module with locally constant fibre dimension is projective. -/
theorem reduced_fibre_projective [Module.FinitePresentation R M]
    (hd : IsLocallyConstant (fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R] M))) :
    Module.Projective R M := by
  let _ : Module.Flat R M := reduced_fibre_flat hd
  exact Module.Flat.projective_of_finitePresentation

end GromovWitten.Algebra
