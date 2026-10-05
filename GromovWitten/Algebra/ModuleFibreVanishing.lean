/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.RingTheory.LocalRing.Module

/-!
# Detecting a finite module on residue-field fibres

A finitely generated module is zero if all its residue-field fibres are zero.
No Noetherian hypothesis on the base ring is needed.
-/

open scoped TensorProduct

universe u v

namespace Module

/-- A finite module with zero fibres at every prime is zero. -/
lemma subsingleton_of_residueField_tensorProduct
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hfibre : ∀ p : PrimeSpectrum R, Subsingleton (p.asIdeal.ResidueField ⊗[R] M)) :
    Subsingleton M := by
  apply (Module.support_eq_empty_iff (R := R) (M := M)).mp
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  have hnontrivial : Nontrivial (p.asIdeal.ResidueField ⊗[R] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct
      (R := R) (M := M) p).mp hp
  exact (not_nontrivial_iff_subsingleton.mpr (hfibre p)) hnontrivial

end Module
