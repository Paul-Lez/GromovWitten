/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.TorsionDegreeBound

/-!
# Rationality of algebra-valued points

For a subgroup `H` of `Gal(Ω/K)`, an algebra-valued point whose coordinates are fixed by
`H` factors uniquely through the actual fixed field `Ωᴴ`.  The construction below is the
literal restriction/codomain-restriction equivalence for `AlgHom`s.  A family equivariant for a
finite representation therefore factors over the fixed field of the representation kernel.

No Jacobian or torsion group scheme is introduced here: the point and equivariance data are
ordinary algebra homomorphisms and equations between those homomorphisms.
-/

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u v w

noncomputable section

open scoped IntermediateField

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
variable {A : Type w} [CommRing A] [Algebra K A]

namespace RationalTorsionPoints

/-! ### The Galois action on algebra-valued points -/

/-- The natural action of a `K`-automorphism of `Ω` on a `K`-algebra-valued point. -/
def pointAction (σ : Gal(Ω/K)) (p : A →ₐ[K] Ω) : A →ₐ[K] Ω :=
  σ.toAlgHom.comp p

@[simp] theorem pointAction_apply (σ : Gal(Ω/K)) (p : A →ₐ[K] Ω) (a : A) :
    pointAction σ p a = σ (p a) := rfl

theorem pointAction_one (p : A →ₐ[K] Ω) : pointAction 1 p = p := by
  ext a
  rfl

theorem pointAction_mul (σ τ : Gal(Ω/K)) (p : A →ₐ[K] Ω) :
    pointAction (σ * τ) p = pointAction σ (pointAction τ p) := by
  ext a
  rfl

/-- A point is fixed by every element of a subgroup, as an equality of actual points. -/
def FixedBy (H : Subgroup Gal(Ω/K)) (p : A →ₐ[K] Ω) : Prop :=
  ∀ σ ∈ H, pointAction σ p = p

theorem fixedBy_iff (H : Subgroup Gal(Ω/K)) (p : A →ₐ[K] Ω) :
    FixedBy H p ↔ ∀ σ ∈ H, ∀ a : A, σ (p a) = p a := by
  constructor
  · intro hp σ hσ a
    exact congrArg (fun q : A →ₐ[K] Ω => q a) (hp σ hσ)
  · intro hp σ hσ
    ext a
    exact hp σ hσ a

/-! ### Restriction to the fixed field -/

section FixedField

variable (H : Subgroup Gal(Ω/K))

local notation "E" => IntermediateField.fixedField H

private def includeFixedField : E →ₐ[K] Ω :=
  IsScalarTower.toAlgHom K E Ω

/-- Compose with the inclusion of the fixed field into `Ω`. -/
def extend (p : A →ₐ[K] E) : A →ₐ[K] Ω :=
  (includeFixedField H).comp p

@[simp] theorem extend_apply (p : A →ₐ[K] E) (a : A) :
    extend H p a = (p a : Ω) := rfl

theorem extend_fixedBy (p : A →ₐ[K] E) : FixedBy H (extend H p) := by
  rw [fixedBy_iff]
  intro σ hσ a
  exact (IntermediateField.mem_fixedField_iff H (p a : Ω)).mp (p a).property σ hσ

/-- Restrict a point whose values lie in `E` by codomain restriction. -/
def restrict (p : A →ₐ[K] Ω) (hp : ∀ a : A, p a ∈ E) : A →ₐ[K] E :=
  { toFun := fun a => ⟨p a, hp a⟩
    map_one' := by ext; exact p.map_one
    map_mul' := by intro a b; ext; exact p.map_mul a b
    map_zero' := by ext; exact p.map_zero
    map_add' := by intro a b; ext; exact p.map_add a b
    commutes' := by intro k; ext; exact p.commutes k }

@[simp] theorem restrict_apply (p : A →ₐ[K] Ω) (hp : ∀ a : A, p a ∈ E) (a : A) :
    (restrict H p hp a : Ω) = p a := rfl

theorem restrict_extend (p : A →ₐ[K] E) :
    restrict H (extend H p) (fun a => (p a).property) = p := by
  ext a
  rfl

theorem extend_restrict (p : A →ₐ[K] Ω) (hp : ∀ a : A, p a ∈ E) :
    extend H (restrict H p hp) = p := by
  ext a
  change (↑((restrict H p hp) a) : Ω) = p a
  rfl

theorem extend_injective : Function.Injective (extend H : (A →ₐ[K] E) → A →ₐ[K] Ω) := by
  intro p q hpq
  ext a
  exact congrArg (fun r : A →ₐ[K] Ω => r a) hpq

private theorem fixedBy_mem_fixedField (p : A →ₐ[K] Ω) (hp : FixedBy H p) (a : A) :
    p a ∈ E := by
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  simpa only [pointAction_apply] using
    (congrArg (fun q : A →ₐ[K] Ω => q a) (hp σ hσ))

/-- Fixed `Ω`-valued points and points over the actual fixed field are equivalent. -/
def fixedPointEquiv : (A →ₐ[K] E) ≃ {p : A →ₐ[K] Ω // FixedBy H p} where
  toFun p := ⟨extend H p, extend_fixedBy H p⟩
  invFun p := restrict H p.1 (fixedBy_mem_fixedField H p.1 p.2)
  left_inv p := restrict_extend H p
  right_inv p := Subtype.ext (extend_restrict H p.1 (fixedBy_mem_fixedField H p.1 p.2))

theorem fixedPointEquiv_apply (p : A →ₐ[K] E) :
    (fixedPointEquiv H p : A →ₐ[K] Ω) = extend H p := rfl

theorem fixedPointEquiv_symm_apply (p : {p : A →ₐ[K] Ω // FixedBy H p}) :
    (fixedPointEquiv H).symm p = restrict H p.1 (fixedBy_mem_fixedField H p.1 p.2) := rfl

end FixedField

/-! ### Families equivariant for a finite representation -/

section EquivariantFamily

variable {G : Type*} [Group G]
variable {I : Type*} [MulAction G I]

/-- A family of `Ω`-valued points equivariant for a representation through `G`. -/
def Equivariant (ρ : Gal(Ω/K) →* G) (P : I → A →ₐ[K] Ω) : Prop :=
  ∀ σ i, pointAction σ (P i) = P (ρ σ • i)

theorem kernel_fixed (ρ : Gal(Ω/K) →* G) (P : I → A →ₐ[K] Ω)
    (hP : Equivariant ρ P) (i : I) :
    FixedBy (ρ.ker : Subgroup Gal(Ω/K)) (P i) := by
  rw [fixedBy_iff]
  intro τ hτ a
  have hτone : ρ τ = 1 := MonoidHom.mem_ker.mp hτ
  have hi := congrArg (fun q : A →ₐ[K] Ω => q a) (hP τ i)
  simpa [pointAction_apply, hτone] using hi

variable [TopologicalSpace G] [DiscreteTopology G]
variable [IsGalois K Ω]

omit [IsGalois K Ω] in
noncomputable def descendedPoint (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ)
    (P : I → A →ₐ[K] Ω) (hP : Equivariant ρ P) (i : I) :
    A →ₐ[K] ContinuousFiniteRepresentation.fixedField ρ hρ :=
  (show A →ₐ[K] IntermediateField.fixedField ρ.ker from
    (fixedPointEquiv ρ.ker).symm ⟨P i, kernel_fixed ρ P hP i⟩)

omit [IsGalois K Ω] in
theorem descendedPoint_extend (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ)
    (P : I → A →ₐ[K] Ω) (hP : Equivariant ρ P) (i : I) :
    extend (ContinuousFiniteRepresentation.kernelClosedSubgroup ρ hρ)
      (descendedPoint ρ hρ P hP i) = P i := by
  ext a
  rfl

/- The fixed field API takes the same kernel as a closed subgroup.  This is the pointwise factor
   through that actual field, with no abstract supplier for the factorization. -/
omit [IsGalois K Ω] in
theorem kernel_factor (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ)
    (P : I → A →ₐ[K] Ω) (hP : Equivariant ρ P) (i : I) :
    ∃! q : A →ₐ[K] ContinuousFiniteRepresentation.fixedField ρ hρ,
      extend (ContinuousFiniteRepresentation.kernelClosedSubgroup ρ hρ) q = P i := by
  let E := ContinuousFiniteRepresentation.fixedField ρ hρ
  let H : Subgroup Gal(Ω/K) := ContinuousFiniteRepresentation.kernelClosedSubgroup ρ hρ
  let q : A →ₐ[K] E := descendedPoint ρ hρ P hP i
  have hq : extend H q = P i := by
    exact descendedPoint_extend ρ hρ P hP i
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply extend_injective H
  exact hq'.trans hq.symm

theorem kernel_factor_field_properties (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ)
    (P : I → A →ₐ[K] Ω) (hP : Equivariant ρ P) (i : I) :
    ∃ q : A →ₐ[K] ContinuousFiniteRepresentation.fixedField ρ hρ,
      extend (ContinuousFiniteRepresentation.kernelClosedSubgroup ρ hρ) q = P i ∧
      FiniteDimensional K (ContinuousFiniteRepresentation.fixedField ρ hρ) ∧
      Algebra.IsSeparable K (ContinuousFiniteRepresentation.fixedField ρ hρ) := by
  obtain ⟨q, hq, -⟩ := kernel_factor ρ hρ P hP i
  exact ⟨q, hq,
    ContinuousFiniteRepresentation.fixedField.finiteDimensional ρ hρ,
    ContinuousFiniteRepresentation.fixedField.isSeparable ρ hρ⟩

theorem kernel_factor_finrank_le_card [Finite G]
    (ρ : Gal(Ω/K) →* G) (hρ : Continuous ρ)
    (P : I → A →ₐ[K] Ω) (hP : Equivariant ρ P) (i : I) :
    ∃ q : A →ₐ[K] ContinuousFiniteRepresentation.fixedField ρ hρ,
      extend (ContinuousFiniteRepresentation.kernelClosedSubgroup ρ hρ) q = P i ∧
      Module.finrank K (ContinuousFiniteRepresentation.fixedField ρ hρ) ≤ Nat.card G := by
  obtain ⟨q, hq, -⟩ := kernel_factor ρ hρ P hP i
  exact ⟨q, hq,
    ContinuousFiniteRepresentation.fixedField.finrank_le_card ρ hρ⟩

end EquivariantFamily

/-! ### The explicit bound for a linear torsion representation -/

section LinearRepresentation

variable {l : ℕ} [Fact l.Prime]
variable {V : Type*} [AddCommGroup V] [Module (ZMod l) V]
variable [FiniteDimensional (ZMod l) V]
variable [TopologicalSpace (LinearMap.GeneralLinearGroup (ZMod l) V)]
variable [DiscreteTopology (LinearMap.GeneralLinearGroup (ZMod l) V)]
variable [IsGalois K Ω]

theorem linear_kernel_factor_finrank_le_bound
    (ρ : TorsionDegreeBound.LinearRepresentation (K := K) (Ω := Ω) (V := V) (l := l))
    (hρ : Continuous ρ) (P : V → A →ₐ[K] Ω)
    (hP : Equivariant ρ P) (v : V) :
    ∃ q : A →ₐ[K] TorsionDegreeBound.splittingField ρ hρ,
      extend (ContinuousFiniteRepresentation.kernelClosedSubgroup ρ hρ) q = P v ∧
      Module.finrank K (TorsionDegreeBound.splittingField ρ hρ) ≤
        TorsionDegreeBound.linearBound l (Module.finrank (ZMod l) V) := by
  obtain ⟨q, hq, -⟩ :=
    kernel_factor_finrank_le_card ρ hρ P hP v
  refine ⟨q, hq, ?_⟩
  calc
    Module.finrank K (TorsionDegreeBound.splittingField ρ hρ) ≤
        Nat.card (TorsionDegreeBound.linearAutomorphisms (V := V) (l := l)) :=
      ContinuousFiniteRepresentation.fixedField.finrank_le_card ρ hρ
    _ = TorsionDegreeBound.linearBound l (Module.finrank (ZMod l) V) :=
      TorsionDegreeBound.linearAutomorphisms_card (V := V) (l := l)

end LinearRepresentation

end RationalTorsionPoints

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
