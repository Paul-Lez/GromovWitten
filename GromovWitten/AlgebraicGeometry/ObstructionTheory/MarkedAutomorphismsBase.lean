/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.ObstructionTheory.MarkedAutomorphisms

/-!
# Automorphisms over the dual-number base

The automorphisms used in the marked tangent calculation are exactly the algebra equivalences
of the split family that preserve the dual-number base and reduce to the identity.  In particular,
fixing the square-zero ideal pointwise follows from these geometric conditions.
-/

namespace GromovWitten.AlgebraicGeometry.MarkedAutomorphisms

open CotangentComplex

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- An algebra equivalence over the dual-number base fixes the nilpotent parameter. -/
theorem equiv_eps_eq_of_preserves_base (E : DualNumber A ≃ₐ[k] DualNumber A)
    (hbase : E.toAlgHom.comp (dualLift (Algebra.ofId k A)) =
      dualLift (Algebra.ofId k A)) :
    E (DualNumber.eps : DualNumber A) = DualNumber.eps := by
  have h := DFunLike.congr_fun hbase (DualNumber.eps : DualNumber k)
  change E (dualLift (Algebra.ofId k A) (TrivSqZeroExt.inr 1)) =
    dualLift (Algebra.ofId k A) (TrivSqZeroExt.inr 1) at h
  rw [dualLift_inr, map_one] at h
  exact h

/-- Reduction to the identity and preservation of the dual base force pointwise fixing of the
square-zero ideal. -/
theorem equiv_inr_eq_of_preserves_base (E : DualNumber A ≃ₐ[k] DualNumber A)
    (hbase : E.toAlgHom.comp (dualLift (Algebra.ofId k A)) =
      dualLift (Algebra.ofId k A))
    (hred : ∀ x, (E x).fst = x.fst) (b : A) :
    E (TrivSqZeroExt.inr b) = TrivSqZeroExt.inr b := by
  have hb : (TrivSqZeroExt.inr b : DualNumber A) =
      DualNumber.eps * TrivSqZeroExt.inl b := by
    apply TrivSqZeroExt.ext <;> simp
  rw [hb, map_mul, equiv_eps_eq_of_preserves_base E hbase]
  apply TrivSqZeroExt.ext
  · simp
  · simp [hred]

/-- Construct the square-zero automorphism from an arbitrary actual algebra equivalence over
the dual-number base whose reduction is the identity. -/
noncomputable def autOfDualBaseEquiv (E : DualNumber A ≃ₐ[k] DualNumber A)
    (hbase : E.toAlgHom.comp (dualLift (Algebra.ofId k A)) =
      dualLift (Algebra.ofId k A))
    (hred : ∀ x, (E x).fst = x.fst) : SquareZero.Aut k (nilIdeal A) where
  hom := E.toAlgHom
  mk_hom x := by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    change (E x - x).fst = 0
    change (E x).fst - x.fst = 0
    rw [hred, sub_self]
  hom_mem m hm := by
    have hm' : m.fst = 0 := hm
    have heq : m = TrivSqZeroExt.inr m.snd := by
      apply TrivSqZeroExt.ext
      · exact hm'
      · rfl
    change E m = m
    rw [heq]
    exact equiv_inr_eq_of_preserves_base E hbase hred m.snd

/-- The construction preserves the given algebra equivalence itself. -/
@[simp]
theorem autOfDualBaseEquiv_toAlgEquiv (E : DualNumber A ≃ₐ[k] DualNumber A)
    (hbase : E.toAlgHom.comp (dualLift (Algebra.ofId k A)) =
      dualLift (Algebra.ofId k A))
    (hred : ∀ x, (E x).fst = x.fst) :
    (autOfDualBaseEquiv E hbase hred).toAlgEquiv = E := by
  apply AlgEquiv.ext
  intro x
  rfl

/-- The square-zero automorphisms are precisely the actual automorphisms over the dual-number
base that reduce to the identity. -/
theorem exists_squareZeroAut_iff (E : DualNumber A ≃ₐ[k] DualNumber A) :
    (∃ ψ : SquareZero.Aut k (nilIdeal A), ψ.toAlgEquiv = E) ↔
      E.toAlgHom.comp (dualLift (Algebra.ofId k A)) = dualLift (Algebra.ofId k A) ∧
        ∀ x, (E x).fst = x.fst := by
  constructor
  · rintro ⟨ψ, rfl⟩
    exact ⟨aut_preserves_dualBase ψ, aut_hom_fst ψ⟩
  · rintro ⟨hbase, hred⟩
    exact ⟨autOfDualBaseEquiv E hbase hred, autOfDualBaseEquiv_toAlgEquiv E hbase hred⟩

/-- The marked tangent construction accounts for every actual algebra equivalence over the dual
base reducing to the identity and preserving the target and marking maps. -/
theorem exists_markedAut_iff {C ι : Type*} [CommRing C] [Algebra k C]
    (target : C →ₐ[k] A) (eval : ι → (A →ₐ[k] k))
    (E : DualNumber A ≃ₐ[k] DualNumber A) :
    (∃ m : MarkedAut target eval, m.aut.toAlgEquiv = E) ↔
      E.toAlgHom.comp (dualLift (Algebra.ofId k A)) = dualLift (Algebra.ofId k A) ∧
      (∀ x, (E x).fst = x.fst) ∧
      E.toAlgHom.comp (dualLift target) = dualLift target ∧
      ∀ i, (dualLift (eval i)).comp E.toAlgHom = dualLift (eval i) := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨aut_preserves_dualBase m.aut, aut_hom_fst m.aut,
      m.target_preserved, m.marking_preserved⟩
  · rintro ⟨hbase, hred, htarget, hmark⟩
    refine ⟨⟨autOfDualBaseEquiv E hbase hred, htarget, hmark⟩, ?_⟩
    exact autOfDualBaseEquiv_toAlgEquiv E hbase hred

end GromovWitten.AlgebraicGeometry.MarkedAutomorphisms
