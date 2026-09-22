/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Fixed fields of continuous finite representations

Let `Ω/K` be an algebraic Galois extension and let a continuous representation of its
Krull-topological Galois group have finite discrete target.  The fixed field of the kernel is
finite Galois over `K`, with degree equal to the cardinality of the image.  This is the
Galois-theoretic construction used by torsion representations; it does not require a preselected
finite Galois ambient extension.

The hypotheses intentionally use `IsGalois K Ω`.  In particular, an algebraic closure may not be
used in place of `Ω` over an imperfect field; a separable closure (or another algebraic Galois
extension) supplies the needed hypothesis.
-/

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u v

noncomputable section

open scoped IntermediateField

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
variable [IsGalois K Ω]

namespace ContinuousFiniteRepresentation

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- The kernel of a continuous representation, viewed as a closed subgroup. -/
noncomputable def kernelClosedSubgroup (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) :
    ClosedSubgroup Gal(Ω/K) where
  toSubgroup := ρ.ker
  isClosed' := by
    change IsClosed (ρ.ker : Set Gal(Ω/K))
    rw [show (ρ.ker : Set Gal(Ω/K)) = ρ ⁻¹' ({1} : Set G) by
      ext σ
      change (ρ σ = 1) ↔ ρ σ = 1
      rfl]
    exact IsClosed.preimage hρ (isClosed_discrete _)

omit [IsGalois K Ω] in
theorem kernel_isOpen (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) :
    IsOpen (kernelClosedSubgroup ρ hρ : Set Gal(Ω/K)) := by
  change IsOpen (ρ.ker : Set Gal(Ω/K))
  rw [show (ρ.ker : Set Gal(Ω/K)) = ρ ⁻¹' ({1} : Set G) by
    ext σ
    change (ρ σ = 1) ↔ ρ σ = 1
    rfl]
  exact hρ.isOpen_preimage _ (isOpen_discrete _)

omit [IsGalois K Ω] in
theorem kernel_isClosed (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) :
    IsClosed (kernelClosedSubgroup ρ hρ : Set Gal(Ω/K)) := by
  exact (kernelClosedSubgroup ρ hρ).isClosed'

omit [IsGalois K Ω] [TopologicalSpace G] [DiscreteTopology G] in
theorem kernel_isNormal (ρ : Gal(Ω/K) →* G) : ρ.ker.Normal := by
  exact MonoidHom.normal_ker ρ

/-- The fixed field cut out by a continuous finite representation. -/
noncomputable def fixedField (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) :
    IntermediateField K Ω :=
  IntermediateField.fixedField (kernelClosedSubgroup ρ hρ : Subgroup Gal(Ω/K))

theorem fixedField.fixingSubgroup_eq (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) :
    (fixedField ρ hρ).fixingSubgroup = kernelClosedSubgroup ρ hρ := by
  exact InfiniteGalois.fixingSubgroup_fixedField (kernelClosedSubgroup ρ hρ)

theorem kernel_iff_restriction_trivial (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ)
    (σ : Gal(Ω/K)) :
    σ ∈ ρ.ker ↔ ∀ x : fixedField ρ hρ, σ (x : Ω) = (x : Ω) := by
  constructor
  · intro hσ x
    have hx := x.property
    change (x : Ω) ∈
      IntermediateField.fixedField (kernelClosedSubgroup ρ hρ : Subgroup Gal(Ω/K)) at hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact hx σ hσ
  · intro hσ
    have hfix : σ ∈ (fixedField ρ hρ).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hσ ⟨x, hx⟩
    rw [fixedField.fixingSubgroup_eq ρ hρ] at hfix
    exact hfix

/-- Restriction gives the homomorphism `Gal(Ω/E) → Gal(Ω/K)` for the constructed field `E`. -/
noncomputable def restrictToBase (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) :
    Gal(Ω/fixedField ρ hρ) →* Gal(Ω/K) where
  toFun σ := AlgEquiv.restrictScalars K σ
  map_one' := by ext; rfl
  map_mul' σ τ := by ext; rfl

theorem restrictToBase_mem_ker (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ)
    (σ : Gal(Ω/fixedField ρ hρ)) :
    restrictToBase ρ hρ σ ∈ ρ.ker := by
  apply (kernel_iff_restriction_trivial ρ hρ _).mpr
  intro x
  change (AlgEquiv.restrictScalars K σ) (x : Ω) = (x : Ω)
  rw [AlgEquiv.restrictScalars_apply]
  exact σ.commutes x

theorem restrictToBase_rho_eq_one (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ)
    (σ : Gal(Ω/fixedField ρ hρ)) :
    ρ (restrictToBase ρ hρ σ) = 1 := by
  exact MonoidHom.mem_ker.mp (restrictToBase_mem_ker ρ hρ σ)

theorem fixedField.finiteDimensional (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) :
    FiniteDimensional K (fixedField ρ hρ) := by
  apply (InfiniteGalois.isOpen_iff_finite (fixedField ρ hρ)).mp
  rw [fixedField.fixingSubgroup_eq ρ hρ]
  exact kernel_isOpen ρ hρ

theorem fixedField.isGalois (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) :
    IsGalois K (fixedField ρ hρ) := by
  apply (InfiniteGalois.normal_iff_isGalois (fixedField ρ hρ)).mp
  rw [fixedField.fixingSubgroup_eq ρ hρ]
  change ρ.ker.Normal
  exact MonoidHom.normal_ker ρ

theorem fixedField.isSeparable (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) :
    Algebra.IsSeparable K (fixedField ρ hρ) := by
  have hgal : IsGalois K (fixedField ρ hρ) := fixedField.isGalois ρ hρ
  exact hgal.to_isSeparable

theorem fixedField.finrank_eq_card_range (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) :
    Module.finrank K (fixedField ρ hρ) = Nat.card ρ.range := by
  let E := fixedField ρ hρ
  have hfix : E.fixingSubgroup = kernelClosedSubgroup ρ hρ :=
    fixedField.fixingSubgroup_eq ρ hρ
  change Module.finrank K E = Nat.card ρ.range
  have hindex : Module.finrank K E = E.fixingSubgroup.index :=
    IntermediateField.finrank_eq_fixingSubgroup_index Ω E
  rw [hindex, hfix]
  exact Subgroup.index_ker ρ

theorem fixedField.finrank_dvd_card (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) [Finite G] :
    Module.finrank K (fixedField ρ hρ) ∣ Nat.card G := by
  rw [fixedField.finrank_eq_card_range ρ hρ]
  exact ρ.range.card_subgroup_dvd_card

theorem fixedField.finrank_le_card (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) [Finite G] :
    Module.finrank K (fixedField ρ hρ) ≤ Nat.card G := by
  rw [fixedField.finrank_eq_card_range ρ hρ]
  exact Nat.card_le_card_of_injective (fun x : ρ.range => (x : G)) Subtype.val_injective

theorem fixedField.gal_card_eq_card_range (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) :
    Nat.card Gal(fixedField ρ hρ/K) = Nat.card ρ.range := by
  let _ : FiniteDimensional K (fixedField ρ hρ) := fixedField.finiteDimensional ρ hρ
  let _ : IsGalois K (fixedField ρ hρ) := fixedField.isGalois ρ hρ
  exact (IsGalois.card_aut_eq_finrank K (fixedField ρ hρ)).trans
    (fixedField.finrank_eq_card_range ρ hρ)

theorem fixedField.gal_card_eq_card_range_via_quotient
    (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) :
    Nat.card Gal(fixedField ρ hρ/K) = Nat.card ρ.range := by
  let H := kernelClosedSubgroup ρ hρ
  have hnormal : (H : Subgroup Gal(Ω/K)).Normal := by
    change ρ.ker.Normal
    exact MonoidHom.normal_ker ρ
  let _ : (H : Subgroup Gal(Ω/K)).Normal := hnormal
  have hcard : Nat.card Gal(IntermediateField.fixedField (H : Subgroup Gal(Ω/K))/K) =
      Nat.card (Gal(Ω/K) ⧸ (H : Subgroup Gal(Ω/K))) := by
    simpa using
      (Nat.card_congr (InfiniteGalois.normalAutEquivQuotient H).toEquiv).symm
  calc
    Nat.card Gal(fixedField ρ hρ/K) =
        Nat.card Gal(IntermediateField.fixedField (H : Subgroup Gal(Ω/K))/K) := by rfl
    _ = Nat.card (Gal(Ω/K) ⧸ (H : Subgroup Gal(Ω/K))) := hcard
    _ = (H : Subgroup Gal(Ω/K)).index :=
      (Subgroup.index_eq_card (H : Subgroup Gal(Ω/K))).symm
    _ = Nat.card ρ.range := by
      change ρ.ker.index = Nat.card ρ.range
      exact Subgroup.index_ker ρ

theorem fixedField.finrank_eq_gal_card (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ) :
    Module.finrank K (fixedField ρ hρ) = Nat.card Gal(fixedField ρ hρ/K) := by
  rw [fixedField.finrank_eq_card_range ρ hρ,
    (fixedField.gal_card_eq_card_range_via_quotient ρ hρ).symm]

end ContinuousFiniteRepresentation

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
