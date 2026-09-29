/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.ResolutionComparison
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
/-!
# Uniqueness of resolution comparisons

Maps into a bounded-below complex of injectives are determined up to homotopy after
precomposition by a quasi-isomorphism. This follows from the fully faithful comparison
with the derived category for a K-injective target.
-/

open CategoryTheory Limits HomologicalComplex
noncomputable section
namespace CochainComplex
variable {C : Type*} [Category C] [Abelian C]
attribute [local instance] HasDerivedCategory.standard
lemma nonempty_homotopy_of_precomp_quasiIso
    {A K L : CochainComplex C ℤ} (a : A ⟶ K) [QuasiIso a] [L.IsKInjective]
    (f g : K ⟶ L) (h : a ≫ f = a ≫ g) : Nonempty (Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq f g ?_⟩
  apply (IsKInjective.Qh_map_bijective _ L).injective
  have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map a)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) a).mpr inferInstance
  apply (cancel_epi (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map a))).mp
  simp only [← Functor.map_comp, h]
end CochainComplex
namespace CochainComplex
variable {C : Type*} [Category C] [Abelian C]
lemma nonempty_homotopy_of_precomp_quasiIso_nat
    {A K L : CochainComplex C ℕ} (a : A ⟶ K) [QuasiIso a]
    [∀ n, Injective (L.X n)] (f g : K ⟶ L) (h : a ≫ f = a ≫ g) :
    Nonempty (Homotopy f g) := by
  have he : extendMap a ComplexShape.embeddingUpNat ≫ extendMap f ComplexShape.embeddingUpNat =
      extendMap a ComplexShape.embeddingUpNat ≫ extendMap g ComplexShape.embeddingUpNat := by
    simpa only [← extendMap_comp] using
      congrArg (fun t => extendMap t ComplexShape.embeddingUpNat) h
  obtain ⟨H⟩ := nonempty_homotopy_of_precomp_quasiIso
    (extendMap a ComplexShape.embeddingUpNat)
    (extendMap f ComplexShape.embeddingUpNat) (extendMap g ComplexShape.embeddingUpNat) he
  exact ⟨H.ofExtend⟩
end CochainComplex
