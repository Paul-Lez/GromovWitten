/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Contraction of ideals and principal localization -/
noncomputable section
universe u v w z
namespace IsLocalization
/-- In a square obtained by localizing the same element in the source and target,
localization commutes with contraction of ideals. -/
lemma ideal_map_comap_away
    (R : Type u) (S : Type v) (A : Type w) (B : Type z)
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B]
    [Algebra S B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B]
    (r : R) [IsLocalization.Away r A]
    [IsLocalization.Away (algebraMap R S r) B] (I : Ideal S) :
    (I.comap (algebraMap R S)).map (algebraMap R A) =
      (I.map (algebraMap S B)).comap (algebraMap A B) := by
  apply (IsLocalization.orderEmbedding (.powers r) A).injective
  ext a
  change algebraMap R A a ∈ (I.comap (algebraMap R S)).map (algebraMap R A) ↔
    algebraMap A B (algebraMap R A a) ∈ I.map (algebraMap S B)
  rw [← IsScalarTower.algebraMap_apply R A B, IsScalarTower.algebraMap_apply R S B]
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (.powers r) A,
    IsLocalization.algebraMap_mem_map_algebraMap_iff (.powers (algebraMap R S r)) B]
  simp only [Submonoid.mem_powers_iff, exists_exists_eq_and, Ideal.mem_comap, map_mul,
    map_pow]
end IsLocalization
