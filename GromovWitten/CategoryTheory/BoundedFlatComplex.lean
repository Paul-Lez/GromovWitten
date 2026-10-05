/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.ScalarHomologyBaseChange
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Bounded flat cochain complexes

A bounded-above exact tail of flat modules has flat cycles and flat cokernels in
positive degrees. These facts make arbitrary scalar extension preserve the
corresponding kernels and homology comparisons.
-/

open CategoryTheory CategoryTheory.Limits
open ComplexShape HomologicalComplex

noncomputable section
universe u v

namespace CochainComplex
/-- Positive cycles of a bounded-above exact tail of flat modules are flat. -/
lemma bounded_exact_flat_cycles_at
    {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{v} R) ℕ)
    (hflat : ∀ n, Module.Flat R (C.X n))
    (N : ℕ) (htail : ∀ n, N ≤ n → IsZero (C.X n))
    (hexact : ∀ n, 2 ≤ n → C.ExactAt n)
    (j : ℕ) (hj : 1 ≤ j) :
    Module.Flat R (LinearMap.ker (C.d j (j + 1)).hom) := by
  have hdesc : ∀ k n, N - n = k → 1 ≤ n →
      Module.Flat R (LinearMap.ker (C.d n (n + 1)).hom) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n hkn hn
      by_cases hnN : N ≤ n
      · have : Subsingleton (C.X n) :=
          (ModuleCat.isZero_iff_subsingleton).mp (htail n hnN)
        have : Subsingleton (LinearMap.ker (C.d n (n + 1)).hom) := inferInstance
        let _ : Module.Free R (LinearMap.ker (C.d n (n + 1)).hom) :=
          Module.Free.of_subsingleton R _
        exact Module.Flat.of_free
      · have hnext : Module.Flat R (LinearMap.ker (C.d (n + 2) (n + 3)).hom) := by
          by_cases hn2N : N ≤ n + 2
          · have : Subsingleton (C.X (n + 2)) :=
              (ModuleCat.isZero_iff_subsingleton).mp (htail (n + 2) hn2N)
            have : Subsingleton (LinearMap.ker (C.d (n + 2) (n + 3)).hom) := inferInstance
            let _ : Module.Free R (LinearMap.ker (C.d (n + 2) (n + 3)).hom) :=
              Module.Free.of_subsingleton R _
            exact Module.Flat.of_free
          · have hn_lt : n < N := Nat.lt_of_not_ge hnN
            have hmeasure : N - (n + 2) < k := by omega
            have hn2 : 1 ≤ n + 2 := by omega
            exact ih (N - (n + 2)) hmeasure (n + 2) rfl hn2
        have : Module.Flat R (LinearMap.ker (C.d (n + 2) (n + 3)).hom) := hnext
        have : Module.Flat R (C.X n) := hflat n
        have : Module.Flat R (C.X (n + 1)) := hflat (n + 1)
        have hEx₁ : (C.sc' n (n + 1) (n + 2)).Exact :=
          (C.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).mp
            (hexact (n + 1) (by omega))
        have hEx₂ : (C.sc' (n + 1) (n + 2) (n + 3)).Exact :=
          (C.exactAt_iff' (n + 1) (n + 2) (n + 3) (by simp) (by simp)).mp
            (hexact (n + 2) (by omega))
        have hRange₁ : LinearMap.range (C.d n (n + 1)).hom =
            LinearMap.ker (C.d (n + 1) (n + 2)).hom :=
          hEx₁.moduleCat_range_eq_ker
        have hRange₂ : LinearMap.range (C.d (n + 1) (n + 2)).hom =
            LinearMap.ker (C.d (n + 2) (n + 3)).hom :=
          hEx₂.moduleCat_range_eq_ker
        let e₀ : (C.X (n + 1) ⧸ LinearMap.range (C.d n (n + 1)).hom) ≃ₗ[R]
            (C.X (n + 1) ⧸ LinearMap.ker (C.d (n + 1) (n + 2)).hom) :=
          Submodule.quotEquivOfEq _ _ hRange₁
        let e₁ : (C.X (n + 1) ⧸ LinearMap.ker (C.d (n + 1) (n + 2)).hom) ≃ₗ[R]
            LinearMap.range (C.d (n + 1) (n + 2)).hom :=
          LinearMap.quotKerEquivRange _
        let e₂ : LinearMap.range (C.d (n + 1) (n + 2)).hom ≃ₗ[R]
            LinearMap.ker (C.d (n + 2) (n + 3)).hom :=
          LinearEquiv.ofEq _ _ hRange₂
        let e := e₀.trans (e₁.trans e₂)
        have : Module.Flat R
            (C.X (n + 1) ⧸ LinearMap.range (C.d n (n + 1)).hom) :=
          Module.Flat.of_linearEquiv e
        exact (C.d n (n + 1)).hom.kernel_flat_of_flat_source_of_flat_target_of_flat_cokernel
  exact hdesc (N - j) j rfl hj

/-- Positive cycles of an integer-indexed bounded-above exact flat complex are flat. -/
lemma bounded_int_exact_flat_cycles_at
    {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt n)
    (j : ℕ) (hj : 1 ≤ j) :
    Module.Flat R (LinearMap.ker (K.d (j : ℤ) ((j + 1 : ℕ) : ℤ)).hom) := by
  let C : CochainComplex (ModuleCat.{v} R) ℕ := K.restriction ComplexShape.embeddingUpNat
  have hflatC : ∀ n : ℕ, Module.Flat R (C.X n) := by
    intro n
    exact hflat n
  have htailC : ∀ n : ℕ, N ≤ n → IsZero (C.X n) := by
    intro n hn
    exact htail n hn
  have hexactC : ∀ n : ℕ, 2 ≤ n → C.ExactAt n := by
    intro n hn
    have hk : (K.sc' ((n - 1 : ℕ) : ℤ) (n : ℤ) ((n + 1 : ℕ) : ℤ)).Exact := by
      exact (K.exactAt_iff' ((n - 1 : ℕ) : ℤ) (n : ℤ) ((n + 1 : ℕ) : ℤ)
        (by
          apply (ComplexShape.up ℤ).prev_eq'
          exact ComplexShape.up_mk _ _ (by omega))
        (by
          apply (ComplexShape.up ℤ).next_eq'
          exact ComplexShape.up_mk _ _ (by omega))).mp
        (hexact n hn)
    have he : C.sc' (n - 1) n (n + 1) ≅
        K.sc' ((n - 1 : ℕ) : ℤ) (n : ℤ) ((n + 1 : ℕ) : ℤ) := by
      exact HomologicalComplex.restriction.sc'Iso K ComplexShape.embeddingUpNat
        (n - 1) n (n + 1)
        (by rfl) (by rfl) (by rfl)
        (by
          apply (ComplexShape.up ℤ).prev_eq'
          exact ComplexShape.up_mk _ _ (by omega))
        (by
          apply (ComplexShape.up ℤ).next_eq'
          exact ComplexShape.up_mk _ _ (by omega))
    apply (C.exactAt_iff' (n - 1) n (n + 1)
      (by
        apply (ComplexShape.up ℕ).prev_eq'
        exact ComplexShape.up_mk _ _ (by omega))
      (by
        apply (ComplexShape.up ℕ).next_eq'
        exact ComplexShape.up_mk _ _ (by omega))).2
    exact (ShortComplex.exact_iff_of_iso he).2 hk
  have hcyc := bounded_exact_flat_cycles_at C hflatC N htailC hexactC j hj
  dsimp [C, HomologicalComplex.restriction, ComplexShape.embeddingUpNat] at hcyc
  change Module.Flat R
      (LinearMap.ker (K.d (j : ℤ) ((j + 1 : ℕ) : ℤ)).hom) at hcyc
  exact hcyc

/-- Positive-degree cokernels in a bounded-above exact flat complex are flat. -/
lemma bounded_int_exact_dn_cokernel_flat
    {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt n)
    (n : ℕ) (hn : 1 ≤ n) :
    Module.Flat R ((cokernel (K.d (n : ℤ) ((n + 1 : ℕ) : ℤ)) : ModuleCat R) : Type v) := by
  have hflatCycle : Module.Flat R
      (LinearMap.ker (K.d ((n + 2 : ℕ) : ℤ) ((n + 3 : ℕ) : ℤ)).hom) :=
    bounded_int_exact_flat_cycles_at K hflat N htail hexact (n + 2) (by omega)
  have hEx₁ : (K.sc' (n : ℤ) ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).Exact := by
    exact (K.exactAt_iff' (n : ℤ) ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)
      (by
        apply (ComplexShape.up ℤ).prev_eq'
        exact ComplexShape.up_mk _ _ (by omega))
      (by
        apply (ComplexShape.up ℤ).next_eq'
        exact ComplexShape.up_mk _ _ (by omega))).mp
      (hexact (n + 1) (by omega))
  have hEx₂ : (K.sc' ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ) ((n + 3 : ℕ) : ℤ)).Exact := by
    exact (K.exactAt_iff' ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ) ((n + 3 : ℕ) : ℤ)
      (by
        apply (ComplexShape.up ℤ).prev_eq'
        exact ComplexShape.up_mk _ _ (by omega))
      (by
        apply (ComplexShape.up ℤ).next_eq'
        exact ComplexShape.up_mk _ _ (by omega))).mp
      (hexact (n + 2) (by omega))
  have hRange₁ : LinearMap.range (K.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom =
      LinearMap.ker (K.d ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom :=
    hEx₁.moduleCat_range_eq_ker
  have hRange₂ : LinearMap.range (K.d ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom =
      LinearMap.ker (K.d ((n + 2 : ℕ) : ℤ) ((n + 3 : ℕ) : ℤ)).hom :=
    hEx₂.moduleCat_range_eq_ker
  let e₀ : (K.X ((n + 1 : ℕ) : ℤ) ⧸
      LinearMap.range (K.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom) ≃ₗ[R]
      (K.X ((n + 1 : ℕ) : ℤ) ⧸
        LinearMap.ker (K.d ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom) :=
    Submodule.quotEquivOfEq _ _ hRange₁
  let e₁ : (K.X ((n + 1 : ℕ) : ℤ) ⧸
      LinearMap.ker (K.d ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom) ≃ₗ[R]
      LinearMap.range (K.d ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom :=
    LinearMap.quotKerEquivRange _
  let e₂ : LinearMap.range (K.d ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom ≃ₗ[R]
      LinearMap.ker (K.d ((n + 2 : ℕ) : ℤ) ((n + 3 : ℕ) : ℤ)).hom :=
    LinearEquiv.ofEq _ _ hRange₂
  let e := e₀.trans (e₁.trans e₂)
  have hflatQuotient : Module.Flat R
      (K.X ((n + 1 : ℕ) : ℤ) ⧸
        LinearMap.range (K.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom) :=
    @Module.Flat.of_linearEquiv R _ _ _ _ _ _ _ hflatCycle e
  exact @Module.Flat.of_linearEquiv R _ _ _ _ _ _ _ hflatQuotient
    (ModuleCat.cokernelIsoRangeQuotient
      (K.d (n : ℤ) ((n + 1 : ℕ) : ℤ))).toLinearEquiv

/-- Scalar extension preserves the degree-one differential's kernel under
bounded flatness and exactness.

This exposes the canonical kernel-comparison isomorphism used in the compressed degree-zero model.
-/
noncomputable def bounded_int_d1_kernelComparisonIso
    {R T : Type u} [CommRing R] [CommRing T] (σ : R →+* T)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt n) :
    (ModuleCat.extendScalars σ).obj (kernel (K.d 1 2)) ≅
      kernel ((ModuleCat.extendScalars σ).map (K.d 1 2)) := by
  letI : Module.Flat R (K.X 2) := hflat 2
  have hflatCoker := bounded_int_exact_dn_cokernel_flat K hflat N htail hexact 1 (by omega)
  letI : Module.Flat R
      ((cokernel (K.d 1 2) : ModuleCat R) : Type u) := hflatCoker
  letI : PreservesLimit
      (parallelPair (K.d 1 2) 0) (ModuleCat.extendScalars σ) :=
    ModuleCat.preservesKernel_extendScalars_of_flat_cokernel σ
      (K.d 1 2)
  exact asIso (kernelComparison (K.d 1 2)
    (ModuleCat.extendScalars σ))

/-- The isomorphism above is the canonical homological-complex kernel comparison. -/
@[simp]
theorem bounded_int_d1_kernelComparisonIso_hom
    {R T : Type u} [CommRing R] [CommRing T] (σ : R →+* T)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt n) :
    (bounded_int_d1_kernelComparisonIso σ K hflat N htail hexact).hom =
      kernelComparison (K.d 1 2) (ModuleCat.extendScalars σ) := rfl

/-- Positive-degree homology commutes with arbitrary scalar extension for a bounded flat complex
that is exact in degrees at least two. -/
lemma bounded_int_positive_homologyComparison_isIso
    {R T : Type u} [CommRing R] [CommRing T] (σ : R →+* T)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt n)
    (n : ℕ) (hn : 1 ≤ n) :
    IsIso (K.homologyComparison (ModuleCat.extendScalars σ) (n : ℤ)) := by
  have hnext : (ComplexShape.up ℤ).next (n : ℤ) = ((n + 1 : ℕ) : ℤ) := by
    apply (ComplexShape.up ℤ).next_eq'
    exact ComplexShape.up_mk _ _ (by omega)
  have hflatTarget : Module.Flat R (K.X ((ComplexShape.up ℤ).next (n : ℤ))) := by
    rw [hnext]
    exact hflat (n + 1)
  have hflatCoker := bounded_int_exact_dn_cokernel_flat K hflat N htail hexact n hn
  have hflatCoker' : Module.Flat R
      ((cokernel (K.d (n : ℤ) ((ComplexShape.up ℤ).next (n : ℤ))) : ModuleCat R) : Type u) := by
    rw [hnext]
    exact hflatCoker
  exact @HomologicalComplex.isIso_homologyComparison_extendScalars_of_flat_cokernel
    R T inferInstance inferInstance ℤ (ComplexShape.up ℤ) K (n : ℤ) σ
    hflatTarget hflatCoker'

/-- Exactness in degrees at least two is preserved by arbitrary scalar extension. -/
lemma bounded_int_exact_after_extendScalars
    {R T : Type u} [CommRing R] [CommRing T] (σ : R →+* T)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt n) :
    ∀ n : ℕ, 2 ≤ n →
      (((ModuleCat.extendScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt
        (n : ℤ) := by
  intro n hn
  let L := ((ModuleCat.extendScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hzero : IsZero (K.homology (n : ℤ)) :=
    (K.exactAt_iff_isZero_homology (n : ℤ)).mp (hexact n hn)
  have hcomparison := bounded_int_positive_homologyComparison_isIso σ K hflat N htail
    hexact n (by omega)
  have hzeroF : IsZero ((ModuleCat.extendScalars σ).obj (K.homology (n : ℤ))) :=
    Functor.map_isZero (ModuleCat.extendScalars σ) hzero
  have hcomparisonIso :
      (ModuleCat.extendScalars σ).obj (K.homology (n : ℤ)) ≅ L.homology (n : ℤ) := by
    letI : IsIso (K.homologyComparison (ModuleCat.extendScalars σ) (n : ℤ)) := hcomparison
    exact asIso (K.homologyComparison (ModuleCat.extendScalars σ) (n : ℤ))
  have hzeroL : IsZero (L.homology (n : ℤ)) :=
    IsZero.of_iso hzeroF hcomparisonIso.symm
  exact (L.exactAt_iff_isZero_homology (n : ℤ)).mpr hzeroL

end CochainComplex
