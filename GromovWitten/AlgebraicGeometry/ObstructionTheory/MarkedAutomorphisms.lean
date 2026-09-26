/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import GromovWitten.AlgebraicGeometry.CotangentComplex.SquareZeroExt
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-!
# Marked infinitesimal automorphisms of an affine map

For a `k`-algebra `A`, a map from a target algebra into `A`, and algebra maps evaluating a
finite or infinite family of markings, this file constructs the actual automorphisms of the
split first-order family `A[ε]`.  The automorphisms are instances of the square-zero extension
automorphisms from `CotangentComplex.SquareZero`; their displacement is the ordinary derivation
`D : A → A`.  Target and marking preservation cut out the kernel of an explicit linear map.

This is a fibrewise affine construction.  It does not assert representability of a global
automorphism functor or rigidity of stable maps in positive characteristic.
-/

namespace GromovWitten.AlgebraicGeometry

namespace MarkedAutomorphisms

open CotangentComplex

universe u v w

variable {k : Type u} {A : Type v} {C : Type w} {ι : Type*}
variable [CommRing k] [CommRing A] [CommRing C] [Algebra k A] [Algebra k C]

/-! ## The split first-order family -/

/-- The square-zero ideal of the dual-number family. -/
abbrev nilIdeal (A : Type v) [CommRing A] : Ideal (DualNumber A) :=
  TrivSqZeroExt.kerIdeal A A

instance isSquareZero_nilIdeal : SquareZero.IsSquareZero (nilIdeal A) where
  sq_eq_bot := TrivSqZeroExt.kerIdeal_sq A A

/-- Lift a map of affine coordinate rings to the split first-order families. -/
noncomputable def dualLift (f : C →ₐ[k] A) : DualNumber C →ₐ[k] DualNumber A :=
  DualNumber.lift ⟨
    ((TrivSqZeroExt.inlAlgHom k A A).comp f, DualNumber.eps),
    DualNumber.eps_mul_eps,
    fun _ => DualNumber.commute_eps_left _⟩

@[simp]
theorem dualLift_apply (f : C →ₐ[k] A) (x : DualNumber C) :
    dualLift f x = (f x.fst, f x.snd) := by
  simp only [dualLift, DualNumber.lift_apply_apply]
  apply TrivSqZeroExt.ext <;> simp [DualNumber.snd_eps, DualNumber.fst_eps,
    TrivSqZeroExt.snd_mul]

@[simp]
theorem dualLift_inl (f : C →ₐ[k] A) (c : C) :
    dualLift f (TrivSqZeroExt.inl c) = TrivSqZeroExt.inl (f c) := by
  rw [dualLift_apply]
  apply TrivSqZeroExt.ext <;> simp

@[simp]
theorem dualLift_fst (f : C →ₐ[k] A) (x : DualNumber C) :
    (dualLift f x).fst = f x.fst := by
  rw [dualLift_apply]
  rfl

@[simp]
theorem dualLift_snd (f : C →ₐ[k] A) (x : DualNumber C) :
    (dualLift f x).snd = f x.snd := by
  rw [dualLift_apply]
  rfl

@[simp]
theorem dualLift_inr (f : C →ₐ[k] A) (b : C) :
    dualLift f (TrivSqZeroExt.inr b) = TrivSqZeroExt.inr (f b) := by
  rw [dualLift_apply]
  apply TrivSqZeroExt.ext <;> simp

/-! ## Derivations and the actual square-zero automorphisms -/

private def autFormula (D : Derivation k A A) (x : DualNumber A) : DualNumber A :=
  (x.fst, x.snd + D x.fst)

/-- The automorphism of `A[ε]` attached to a derivation of `A`.

This is the concrete specialization of the square-zero automorphism construction: it sends
`a + bε` to `a + (b + D a)ε`. -/
noncomputable def autOfDerivation (D : Derivation k A A) :
    SquareZero.Aut k (nilIdeal A) where
  hom :=
    { toFun := autFormula D
      map_one' := by
        apply TrivSqZeroExt.ext <;> simp [autFormula, D.map_one_eq_zero]
      map_zero' := by
        apply TrivSqZeroExt.ext <;> simp [autFormula]
      map_add' := by
        intro x y
        rcases x with ⟨x₁, x₂⟩
        rcases y with ⟨y₁, y₂⟩
        change (x₁ + y₁, x₂ + y₂ + D (x₁ + y₁)) =
          (x₁ + y₁, (x₂ + D x₁) + (y₂ + D y₁))
        apply Prod.ext
        · rfl
        · change x₂ + y₂ + D (x₁ + y₁) = (x₂ + D x₁) + (y₂ + D y₁)
          rw [D.map_add]
          ring
      map_mul' := by
        intro x y
        rcases x with ⟨x₁, x₂⟩
        rcases y with ⟨y₁, y₂⟩
        change (x₁ * y₁, x₁ * y₂ + x₂ * y₁ + D (x₁ * y₁)) =
          (x₁ * y₁, x₁ * (y₂ + D y₁) + (x₂ + D x₁) * y₁)
        apply Prod.ext
        · rfl
        · rw [D.leibniz]
          ring
      commutes' := by
        intro r
        apply TrivSqZeroExt.ext
        · rfl
        · simpa only [TrivSqZeroExt.algebraMap_eq_inl', autFormula,
            TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_mk, TrivSqZeroExt.fst_inl, zero_add]
            using D.map_algebraMap r }
  mk_hom := by
    intro x
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    change autFormula D x - x ∈ nilIdeal A
    change (autFormula D x - x).fst = 0
    rcases x with ⟨a, b⟩
    change a - a = 0
    exact sub_self a
  hom_mem := by
    intro m hm
    apply TrivSqZeroExt.ext
    · rfl
    · have hm' : m.fst = 0 := hm
      change m.snd + D m.fst = m.snd
      rw [hm', D.map_zero, add_zero]

@[simp]
theorem autOfDerivation_snd (D : Derivation k A A) (x : DualNumber A) :
    ((autOfDerivation D).hom x).snd = x.snd + D x.fst := by
  rfl

@[simp]
theorem aut_hom_fst (ψ : SquareZero.Aut k (nilIdeal A)) (x : DualNumber A) :
    (ψ.hom x).fst = x.fst := by
  have h := ψ.sub_mem x
  change (ψ.hom x - x).fst = 0 at h
  have h' : (ψ.hom x).fst - x.fst = 0 := by
    simpa only [TrivSqZeroExt.fst_sub] using h
  exact sub_eq_zero.mp h'

/-- The first-order displacement of an actual square-zero automorphism. -/
noncomputable def derivationOfAut (ψ : SquareZero.Aut k (nilIdeal A)) : Derivation k A A where
  toFun a := (ψ.hom (TrivSqZeroExt.inl a)).snd
  map_add' a b := by
    have h := congrArg TrivSqZeroExt.snd (ψ.hom.map_add (TrivSqZeroExt.inl a)
      (TrivSqZeroExt.inl b))
    rw [← TrivSqZeroExt.inl_add] at h
    change TrivSqZeroExt.snd (ψ.hom (TrivSqZeroExt.inl (a + b))) =
      TrivSqZeroExt.snd (ψ.hom (TrivSqZeroExt.inl a)) +
        TrivSqZeroExt.snd (ψ.hom (TrivSqZeroExt.inl b)) at h
    exact h
  map_smul' r a := by
    have hc := ψ.hom.commutes r
    rw [Algebra.smul_def]
    change ψ.hom (TrivSqZeroExt.inl (algebraMap k A r)) =
        TrivSqZeroExt.inl (algebraMap k A r) at hc
    have hm := congrArg TrivSqZeroExt.snd (ψ.hom.map_mul
      (TrivSqZeroExt.inl (algebraMap k A r)) (TrivSqZeroExt.inl a))
    change TrivSqZeroExt.snd (ψ.hom (TrivSqZeroExt.inl (algebraMap k A r) *
      TrivSqZeroExt.inl a)) =
      TrivSqZeroExt.snd (ψ.hom (TrivSqZeroExt.inl (algebraMap k A r)) *
        ψ.hom (TrivSqZeroExt.inl a)) at hm
    have har : TrivSqZeroExt.inl (algebraMap k A r) * TrivSqZeroExt.inl a =
        TrivSqZeroExt.inl ((algebraMap k A r) * a) :=
      TrivSqZeroExt.inl_mul_inl A _ _
    rw [har] at hm
    rw [hc] at hm
    change TrivSqZeroExt.snd (ψ.hom (TrivSqZeroExt.inl ((algebraMap k A r) * a))) = _
    rw [Algebra.smul_def]
    simpa [TrivSqZeroExt.snd_mul] using hm
  map_one_eq_zero' := by
    have h := congrArg TrivSqZeroExt.snd (ψ.hom.map_one)
    change TrivSqZeroExt.snd (ψ.hom (TrivSqZeroExt.inl 1)) = 0
    rw [TrivSqZeroExt.inl_one]
    change TrivSqZeroExt.snd (ψ.hom.toRingHom 1) = 0
    simpa only [TrivSqZeroExt.snd_one] using h
  leibniz' a b := by
    have h := congrArg TrivSqZeroExt.snd (ψ.hom.map_mul
      (TrivSqZeroExt.inl a) (TrivSqZeroExt.inl b))
    change TrivSqZeroExt.snd (ψ.hom (TrivSqZeroExt.inl a * TrivSqZeroExt.inl b)) =
      TrivSqZeroExt.snd (ψ.hom (TrivSqZeroExt.inl a) * ψ.hom (TrivSqZeroExt.inl b)) at h
    have ha : (ψ.hom (TrivSqZeroExt.inl a)).fst = a := by
      have hm := ψ.sub_mem (TrivSqZeroExt.inl a)
      change (ψ.hom (TrivSqZeroExt.inl a) - TrivSqZeroExt.inl a).fst = 0 at hm
      have hm' : (ψ.hom (TrivSqZeroExt.inl a)).fst - a = 0 := hm
      exact sub_eq_zero.mp hm'
    have hb : (ψ.hom (TrivSqZeroExt.inl b)).fst = b := by
      have hm := ψ.sub_mem (TrivSqZeroExt.inl b)
      change (ψ.hom (TrivSqZeroExt.inl b) - TrivSqZeroExt.inl b).fst = 0 at hm
      have hm' : (ψ.hom (TrivSqZeroExt.inl b)).fst - b = 0 := hm
      exact sub_eq_zero.mp hm'
    have hab : TrivSqZeroExt.inl a * TrivSqZeroExt.inl b =
        TrivSqZeroExt.inl (a * b) := (TrivSqZeroExt.inl_mul A a b).symm
    rw [hab, TrivSqZeroExt.snd_mul, ha, hb] at h
    change TrivSqZeroExt.snd (ψ.hom (TrivSqZeroExt.inl (a * b))) =
      a • TrivSqZeroExt.snd (ψ.hom (TrivSqZeroExt.inl b)) +
        b • TrivSqZeroExt.snd (ψ.hom (TrivSqZeroExt.inl a))
    simpa only [IsCentralScalar.op_smul_eq_smul] using h

@[simp]
theorem derivationOfAut_autOfDerivation (D : Derivation k A A) :
    derivationOfAut (autOfDerivation D) = D := by
  ext a
  change ((autOfDerivation D).hom (TrivSqZeroExt.inl a)).snd = D a
  rw [autOfDerivation_snd]
  simp [TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl]

theorem aut_hom_inl (ψ : SquareZero.Aut k (nilIdeal A)) (a : A) :
    ψ.hom (TrivSqZeroExt.inl a) =
      TrivSqZeroExt.inl a + TrivSqZeroExt.inr (derivationOfAut ψ a) := by
  apply TrivSqZeroExt.ext
  · have hm := ψ.sub_mem (TrivSqZeroExt.inl a)
    change (ψ.hom (TrivSqZeroExt.inl a) - TrivSqZeroExt.inl a).fst = 0 at hm
    have hm' : (ψ.hom (TrivSqZeroExt.inl a)).fst - a = 0 := hm
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      add_zero]
    change (ψ.hom (TrivSqZeroExt.inl a)).fst = a
    exact sub_eq_zero.mp hm'
  · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
      zero_add]
    rfl

theorem aut_hom_inr (ψ : SquareZero.Aut k (nilIdeal A)) (b : A) :
    ψ.hom (TrivSqZeroExt.inr b) = TrivSqZeroExt.inr b := by
  apply ψ.hom_mem
  change (TrivSqZeroExt.inr b).fst = 0
  rfl

/-- Every square-zero automorphism is an automorphism over the split dual-number base
`DualNumber k`; this records both the base scalar action and the nilpotent generator. -/
theorem aut_preserves_dualBase (ψ : SquareZero.Aut k (nilIdeal A)) :
    ψ.hom.comp (dualLift (Algebra.ofId k A)) = dualLift (Algebra.ofId k A) := by
  apply TrivSqZeroExt.algHom_ext'
  · apply AlgHom.ext
    intro r
    change ψ.hom (dualLift (Algebra.ofId k A) (TrivSqZeroExt.inl r)) =
      dualLift (Algebra.ofId k A) (TrivSqZeroExt.inl r)
    rw [dualLift_inl]
    change ψ.hom (algebraMap k (DualNumber A) r) = algebraMap k (DualNumber A) r
    exact ψ.hom.commutes r
  · apply LinearMap.ext
    intro b
    change ψ.hom (dualLift (Algebra.ofId k A) (TrivSqZeroExt.inr b)) =
      dualLift (Algebra.ofId k A) (TrivSqZeroExt.inr b)
    rw [dualLift_inr, aut_hom_inr]

/-! The converse equality uses the actual `Aut` structure, rather than a supplier field. -/

theorem autOfDerivation_derivationOfAut (ψ : SquareZero.Aut k (nilIdeal A)) :
    autOfDerivation (derivationOfAut ψ) = ψ := by
  apply SquareZero.Aut.ext
  apply TrivSqZeroExt.algHom_ext'
  · apply AlgHom.ext
    intro a
    change autFormula (derivationOfAut ψ) (TrivSqZeroExt.inl a) =
      ψ.hom (TrivSqZeroExt.inl a)
    rw [aut_hom_inl]
    apply TrivSqZeroExt.ext <;> simp [autFormula]
  · apply LinearMap.ext
    intro b
    change autFormula (derivationOfAut ψ) (TrivSqZeroExt.inr b) =
      ψ.hom (TrivSqZeroExt.inr b)
    rw [aut_hom_inr]
    apply TrivSqZeroExt.ext <;> simp [autFormula]

/-- Actual automorphisms of the split first-order family are derivations of `A`. -/
noncomputable def autEquivDerivation :
    SquareZero.Aut k (nilIdeal A) ≃ Derivation k A A where
  toFun := derivationOfAut
  invFun := autOfDerivation
  left_inv := autOfDerivation_derivationOfAut
  right_inv := derivationOfAut_autOfDerivation

@[simp]
theorem autEquivDerivation_apply (ψ : SquareZero.Aut k (nilIdeal A)) :
    autEquivDerivation ψ = derivationOfAut ψ := rfl

@[simp]
theorem autOfDerivation_zero :
    autOfDerivation (0 : Derivation k A A) = (1 : SquareZero.Aut k (nilIdeal A)) := by
  apply (autEquivDerivation).injective
  change derivationOfAut (autOfDerivation (0 : Derivation k A A)) =
    derivationOfAut (1 : SquareZero.Aut k (nilIdeal A))
  rw [derivationOfAut_autOfDerivation]
  apply Derivation.ext
  intro a
  change 0 = ((1 : SquareZero.Aut k (nilIdeal A)).hom (TrivSqZeroExt.inl a)).snd
  rw [SquareZero.Aut.one_hom]
  rfl

@[simp]
theorem derivationOfAut_comp (ψ φ : SquareZero.Aut k (nilIdeal A)) :
    derivationOfAut (ψ.comp φ) = derivationOfAut ψ + derivationOfAut φ := by
  apply Derivation.ext
  intro a
  change (ψ.hom (φ.hom (TrivSqZeroExt.inl a))).snd = _
  rw [aut_hom_inl, map_add, aut_hom_inl, aut_hom_inr]
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
    zero_add]
  rw [Derivation.add_apply]

@[simp]
theorem autOfDerivation_mul (D E : Derivation k A A) :
    autOfDerivation D * autOfDerivation E = autOfDerivation (D + E) := by
  apply (autEquivDerivation).injective
  change derivationOfAut ((autOfDerivation D).comp (autOfDerivation E)) =
    derivationOfAut (autOfDerivation (D + E))
  simp only [derivationOfAut_comp, derivationOfAut_autOfDerivation]

@[simp]
theorem autOfDerivation_inv (D : Derivation k A A) :
    (autOfDerivation D)⁻¹ = autOfDerivation (-D) := by
  apply inv_eq_of_mul_eq_one_right
  rw [autOfDerivation_mul, add_neg_cancel, autOfDerivation_zero]

/-! ## Target and marking equations as an honest tangent kernel -/

/-- The linear map recording target and marking displacement. -/
def constraintMap (target : C →ₐ[k] A) (eval : ι → (A →ₐ[k] k)) :
    Derivation k A A →ₗ[k] ((C → A) × (ι → A → k)) where
  toFun D := (fun c => D (target c), fun i a => eval i (D a))
  map_add' D E := by
    ext c <;> simp [map_add]
  map_smul' r D := by
    ext c <;> simp

/-- The tangent space of marked infinitesimal automorphisms is the actual kernel. -/
def markedDerivations (target : C →ₐ[k] A) (eval : ι → (A →ₐ[k] k)) :
    Submodule k (Derivation k A A) :=
  LinearMap.ker (constraintMap target eval)

theorem mem_markedDerivations_iff (target : C →ₐ[k] A) (eval : ι → (A →ₐ[k] k))
    (D : Derivation k A A) :
    D ∈ markedDerivations target eval ↔
      (∀ c, D (target c) = 0) ∧ ∀ i a, eval i (D a) = 0 := by
  rw [markedDerivations, LinearMap.mem_ker]
  change ((fun c => D (target c)), (fun i a => eval i (D a))) = (0, 0) ↔ _
  rw [Prod.ext_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun c => congrFun h₁ c, fun i a => congrFun (congrFun h₂ i) a⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨funext h₁, funext fun i => funext (h₂ i)⟩

/-- An actual first-order automorphism preserving the target and every marking. -/
structure MarkedAut (target : C →ₐ[k] A) (eval : ι → (A →ₐ[k] k)) where
  aut : SquareZero.Aut k (nilIdeal A)
  target_preserved : aut.hom.comp (dualLift target) = dualLift target
  marking_preserved : ∀ i, (dualLift (eval i)).comp aut.hom = dualLift (eval i)

/-- The actual split-family automorphism attached to a derivation in the target/marking kernel. -/
noncomputable def markedAutOfDerivation (target : C →ₐ[k] A)
    (eval : ι → (A →ₐ[k] k)) (D : markedDerivations target eval) :
    MarkedAut target eval where
  aut := autOfDerivation (D : Derivation k A A)
  target_preserved := by
    apply AlgHom.ext
    intro x
    change (autOfDerivation (D : Derivation k A A)).hom (dualLift target x) =
      dualLift target x
    rcases x with ⟨c, b⟩
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq (⟨c, b⟩ : DualNumber C)]
    simp only [map_add, dualLift_inl, dualLift_inr, aut_hom_inl, aut_hom_inr]
    apply TrivSqZeroExt.ext
    · simp
    · have hD := ((mem_markedDerivations_iff target eval (D : Derivation k A A)).mp D.property).1 c
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        zero_add]
      simp only [derivationOfAut_autOfDerivation, TrivSqZeroExt.fst_mk,
        TrivSqZeroExt.snd_mk, hD, zero_add]
  marking_preserved := by
    intro i
    apply AlgHom.ext
    intro x
    change dualLift (eval i) ((autOfDerivation (D : Derivation k A A)).hom x) =
      dualLift (eval i) x
    rcases x with ⟨a, b⟩
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq (⟨a, b⟩ : DualNumber A)]
    simp only [map_add, dualLift_inl, dualLift_inr, aut_hom_inl, aut_hom_inr]
    apply TrivSqZeroExt.ext
    · simp
    · have hD :=
        ((mem_markedDerivations_iff target eval (D : Derivation k A A)).mp D.property).2 i a
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        zero_add]
      simp only [derivationOfAut_autOfDerivation, TrivSqZeroExt.fst_mk,
        TrivSqZeroExt.snd_mk, hD, zero_add]

theorem markedAut_iff (target : C →ₐ[k] A) (eval : ι → (A →ₐ[k] k))
    (ψ : SquareZero.Aut k (nilIdeal A)) :
    (∀ c, ψ.hom (dualLift target (TrivSqZeroExt.inl c)) =
      dualLift target (TrivSqZeroExt.inl c)) ∧
      (∀ i a, dualLift (eval i) (ψ.hom (TrivSqZeroExt.inl a)) =
        dualLift (eval i) (TrivSqZeroExt.inl a)) ↔
      derivationOfAut ψ ∈ markedDerivations target eval := by
  constructor
  · intro h
    rw [mem_markedDerivations_iff]
    constructor
    · intro c
      have hc := h.1 c
      rw [dualLift_inl, aut_hom_inl] at hc
      have hc' := congrArg TrivSqZeroExt.snd hc
      simpa only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        zero_add] using hc'
    · intro i a
      have ha := h.2 i a
      rw [aut_hom_inl] at ha
      have ha' := congrArg TrivSqZeroExt.snd ha
      simpa only [dualLift_snd, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, zero_add, map_zero] using ha'
  · intro h
    rw [mem_markedDerivations_iff] at h
    constructor
    · intro c
      rw [dualLift_inl, aut_hom_inl]
      apply TrivSqZeroExt.ext <;> simp [h.1 c]
    · intro i a
      rw [dualLift_inl]
      rw [aut_hom_inl]
      apply TrivSqZeroExt.ext
      · rw [dualLift_fst]
        simp
      · rw [dualLift_snd]
        simp [h.2 i a]

@[ext]
theorem markedAut_ext {target : C →ₐ[k] A} {eval : ι → (A →ₐ[k] k)}
    (m n : MarkedAut target eval) (h : m.aut = n.aut) : m = n := by
  cases m
  cases n
  cases h
  rfl

/-- Extract the target/marking-preserving derivation from an actual marked automorphism. -/
noncomputable def derivationOfMarkedAut (target : C →ₐ[k] A)
    (eval : ι → (A →ₐ[k] k)) (m : MarkedAut target eval) :
    markedDerivations target eval := by
  refine ⟨derivationOfAut m.aut, ?_⟩
  apply (markedAut_iff target eval m.aut).mp
  constructor
  · intro c
    have h := congrArg (fun F : DualNumber C →ₐ[k] DualNumber A =>
      F (TrivSqZeroExt.inl c)) m.target_preserved
    change m.aut.hom (dualLift target (TrivSqZeroExt.inl c)) =
      dualLift target (TrivSqZeroExt.inl c) at h
    exact h
  · intro i a
    have h := congrArg (fun F : DualNumber A →ₐ[k] DualNumber k =>
      F (TrivSqZeroExt.inl a)) (m.marking_preserved i)
    change dualLift (eval i) (m.aut.hom (TrivSqZeroExt.inl a)) =
      dualLift (eval i) (TrivSqZeroExt.inl a) at h
    exact h

/-- Actual marked first-order automorphisms are exactly the derivation kernel. -/
noncomputable def markedAutEquivDerivation (target : C →ₐ[k] A)
    (eval : ι → (A →ₐ[k] k)) :
    MarkedAut target eval ≃ markedDerivations target eval where
  toFun := derivationOfMarkedAut target eval
  invFun := markedAutOfDerivation target eval
  left_inv m := by
    apply markedAut_ext
    change autOfDerivation (derivationOfAut m.aut) = m.aut
    exact autOfDerivation_derivationOfAut m.aut
  right_inv D := by
    apply Subtype.ext
    exact derivationOfAut_autOfDerivation (D : Derivation k A A)

end MarkedAutomorphisms

end GromovWitten.AlgebraicGeometry
