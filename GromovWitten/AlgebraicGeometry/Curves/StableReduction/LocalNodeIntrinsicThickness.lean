/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNodeChart
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroup

/-!
# Intrinsic thickness of a local node

The thickness below is the length of the *actual* first differential Fitting quotient.  The
identification with `R/(a)` is proved from the computed Fitting ideal and the quotient
equivalence in `LocalNode`, rather than by choosing a coordinate normal form.  For a DVR this
length is the valuation exponent, and it is therefore unique.  Under a ramified injective DVR
extension, the node algebra has an explicit coefficient-base-change equivalence followed by a
coordinate map whose scaling factor is the powered unit `vⁿ`; its intrinsic length is multiplied
by the ramification index.

The persistent node `xy = 0` is kept separate: its intrinsic length is the length of the DVR
itself, hence `⊤`, rather than a finite positive integer.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct Polynomial

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

universe u v

noncomputable section

/-! ## The actual differential Fitting quotient -/

/-- The ring cut out by the actual first differential Fitting ideal of the node presentation. -/
abbrev differentialFittingQuotient (R : Type u) [CommRing R] (π : R) (n : ℕ) :=
  Ring R π n ⧸ AlgebraPresentation.differentialFittingIdeal
    (completeIntersectionPresentation R π n) 1

/-- The module length of the actual first differential Fitting quotient. -/
noncomputable def nodeThickness (R : Type u) [CommRing R] (π : R) (n : ℕ) : ℕ∞ :=
  Module.length R (differentialFittingQuotient R π n)

/-- The intrinsic thickness of a general smoothing equation `xy = a`, using its actual Fitting
quotient.  This is the `n = 1` case of `nodeThickness`. -/
noncomputable def intrinsicThickness (R : Type u) [CommRing R] (a : R) : ℕ∞ :=
  nodeThickness R a 1

/-- The actual differential Fitting quotient is canonically the coefficient quotient by the
parameter power. -/
noncomputable def differentialFittingQuotientEquiv (R : Type u) [CommRing R]
    (π : R) (n : ℕ) :
    differentialFittingQuotient R π n ≃ₐ[R]
      R ⧸ parameterPowerIdeal R π n := by
  exact (Ideal.quotientEquivAlgOfEq R
      (differentialFittingIdeal_one_eq_relativeJacobianIdeal R π n)).trans
    (relativeJacobianQuotientEquiv R π n)

/-- The actual Fitting length agrees with the length of the coefficient quotient. -/
theorem nodeThickness_eq_parameterLength (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    nodeThickness R π n =
      Module.length R (R ⧸ parameterPowerIdeal R π n) := by
  exact (differentialFittingQuotientEquiv R π n).toLinearEquiv.length_eq

theorem intrinsicThickness_eq_parameterLength (R : Type u) [CommRing R] (a : R) :
    intrinsicThickness R a = Module.length R (R ⧸ Ideal.span ({a} : Set R)) := by
  unfold intrinsicThickness
  rw [nodeThickness_eq_parameterLength]
  rw [parameterPowerIdeal, show ({a ^ 1} : Set R) = {a} by simp]

/-- Intrinsic node thickness is preserved by a flat local formally unramified essentially finite
type extension.  This general form includes zero and unit parameters; the DVR finite étale
specialization below uses it for standard node charts. -/
theorem intrinsicThickness_baseChange_eq
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] (a : R) :
    intrinsicThickness S (algebraMap R S a) = intrinsicThickness R a := by
  rw [intrinsicThickness_eq_parameterLength, intrinsicThickness_eq_parameterLength]
  exact Ring.ord_algebraMap_of_flat_formallyUnramified_local a

/-- For an irreducible uniformizer, the actual singular quotient has precisely the prescribed
finite length. -/
theorem nodeThickness_eq_of_irreducible {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) (n : ℕ) :
    nodeThickness R π n = n := by
  rw [nodeThickness_eq_parameterLength, parameterPowerIdeal, ← Ideal.span_singleton_pow,
    ← hπ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R n

/-- If `a = u πⁿ` with `u` a unit, the intrinsic Fitting length is `n`.  This is the coordinate
free exponent uniqueness statement used by a standard DVR chart. -/
theorem intrinsicThickness_eq_of_factorization {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a π : R} {n : ℕ} (hπ : Irreducible π) (u : Rˣ)
    (h : a = (u : R) * π ^ n) : intrinsicThickness R a = n := by
  rw [intrinsicThickness_eq_parameterLength, h,
    Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hπ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R n

/-- The exponent of a DVR factorization is recovered from the actual Fitting length, so two
factorizations of the same nonzero parameter have the same exponent. -/
theorem intrinsicThickness_factorization_exponent_unique {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a π : R} {m n : ℕ} (hπ : Irreducible π)
    (u v : Rˣ) (hu : a = (u : R) * π ^ m) (hv : a = (v : R) * π ^ n) : m = n := by
  have hmn : (m : ℕ∞) = n :=
    (intrinsicThickness_eq_of_factorization hπ u hu).symm.trans
      (intrinsicThickness_eq_of_factorization hπ v hv)
  exact_mod_cast hmn

/-! ## The zero parameter -/

private theorem dvr_length_ring_eq_top (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : Module.length R R = ⊤ := by
  rw [ENat.eq_top_iff_forall_ge]
  intro n
  let q : R →ₗ[R] R ⧸ IsLocalRing.maximalIdeal R ^ n :=
    { toFun := Ideal.Quotient.mk _
      map_add' := map_add _
      map_smul' := by intro r x; rfl }
  have hsurj : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hle := Module.length_le_of_surjective
    q hsurj
  rw [IsDiscreteValuationRing.length_quotient_pow_maximalIdeal] at hle
  exact hle

/-- The persistent node `xy = 0` has infinite intrinsic Fitting length. -/
theorem intrinsicThickness_zero {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : intrinsicThickness R 0 = ⊤ := by
  rw [intrinsicThickness_eq_parameterLength,
    show Ideal.span ({(0 : R)} : Set R) = ⊥ by simp]
  exact (AlgEquiv.quotientBot R R).toLinearEquiv.length_eq ▸ dvr_length_ring_eq_top R

/-! ## Unramified finite étale coefficient extension -/

/-- A formally unramified essentially finite-type local extension of DVRs carries a source
uniformizer to a target uniformizer up to a unit.  The proof uses maximal-ideal extension and
does not assume a ramification-index factorization. -/
theorem formallyUnramifiedDvr_map_uniformizer
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.FormallyUnramified R S]
    [Algebra.EssFiniteType R S]
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ) :
    ∃ u : Sˣ, algebraMap R S π = (u : S) * ϖ := by
  have hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
      IsLocalRing.maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hspan : Ideal.span ({algebraMap R S π} : Set S) = Ideal.span ({ϖ} : Set S) := by
    calc
      Ideal.span ({algebraMap R S π} : Set S) =
          (Ideal.span ({π} : Set R)).map (algebraMap R S) := by
            rw [Ideal.map_span]
            simp
      _ = (IsLocalRing.maximalIdeal R).map (algebraMap R S) := by
        rw [hπ.maximalIdeal_eq]
      _ = IsLocalRing.maximalIdeal S := hmax
      _ = Ideal.span ({ϖ} : Set S) := hϖ.maximalIdeal_eq
  rcases (Ideal.span_singleton_eq_span_singleton.mp hspan) with ⟨u, hu⟩
  refine ⟨u⁻¹, ?_⟩
  calc
    algebraMap R S π = algebraMap R S π * 1 := by simp
    _ = algebraMap R S π * ((↑(u⁻¹) : S) * (u : S)) := by simp
    _ = (↑(u⁻¹) : S) * (algebraMap R S π * (u : S)) := by ac_rfl
    _ = (↑(u⁻¹) : S) * ϖ := by rw [hu]

/-! ## Ramified coefficient extension -/

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/-- The powered unit occurring after ramified base change. -/
def ramifiedPoweredUnit (v : Sˣ) (n : ℕ) : Sˣ := v ^ n

private theorem ramified_power_formula {π : R} {ϖ : S} {e n : ℕ} (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    (algebraMap R S π) ^ n = (v : S) ^ n * ϖ ^ (e * n) := by
  rw [hπ, mul_pow, ← pow_mul]

/-- The coordinate map from the coefficient-extended node to the standard node. -/
noncomputable def ramifiedNodeMap
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    Ring S (algebraMap R S π) n →ₐ[S] Ring S ϖ (e * n) :=
  lift (algebraMap R S π) n
    (algebraMap S (Ring S ϖ (e * n)) ((v : S) ^ n) * x S ϖ (e * n))
    (y S ϖ (e * n)) (by
      calc
        algebraMap S (Ring S ϖ (e * n)) ((v : S) ^ n) *
            x S ϖ (e * n) * y S ϖ (e * n) =
            algebraMap S (Ring S ϖ (e * n)) ((v : S) ^ n) *
              algebraMap S (Ring S ϖ (e * n)) (ϖ ^ (e * n)) := by
                rw [mul_assoc, x_mul_y]
        _ = algebraMap S (Ring S ϖ (e * n))
            ((v : S) ^ n * ϖ ^ (e * n)) := by rw [map_mul]
        _ = algebraMap S (Ring S ϖ (e * n)) ((algebraMap R S π) ^ n) := by
          rw [ramified_power_formula (R := R) (S := S) (π := π) (ϖ := ϖ)
            (e := e) (n := n) v hπ])

/-- The inverse coordinate map, scaling the first branch by the inverse powered unit. -/
noncomputable def ramifiedNodeInverseMap
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    Ring S ϖ (e * n) →ₐ[S] Ring S (algebraMap R S π) n :=
  lift ϖ (e * n)
    (algebraMap S (Ring S (algebraMap R S π) n) ((↑(v⁻¹) : S) ^ n) *
      x S (algebraMap R S π) n)
    (y S (algebraMap R S π) n) (by
      calc
        algebraMap S (Ring S (algebraMap R S π) n) ((↑(v⁻¹) : S) ^ n) *
            x S (algebraMap R S π) n * y S (algebraMap R S π) n =
            algebraMap S (Ring S (algebraMap R S π) n) ((↑(v⁻¹) : S) ^ n) *
              algebraMap S (Ring S (algebraMap R S π) n)
                ((algebraMap R S π) ^ n) := by
                  rw [mul_assoc, x_mul_y]
        _ = algebraMap S (Ring S (algebraMap R S π) n)
            ((↑(v⁻¹) : S) ^ n * (algebraMap R S π) ^ n) := by rw [map_mul]
        _ = algebraMap S (Ring S (algebraMap R S π) n) (ϖ ^ (e * n)) := by
          rw [ramified_power_formula (R := R) (S := S) (π := π) (ϖ := ϖ)
            (e := e) (n := n) v hπ]
          congr 1
          rw [← mul_assoc, ← mul_pow]
          simp)

@[simp] theorem ramifiedNodeMap_x
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    ramifiedNodeMap R S π ϖ e n v hπ (x S (algebraMap R S π) n) =
      algebraMap S (Ring S ϖ (e * n)) ((v : S) ^ n) * x S ϖ (e * n) := by
  change lift (algebraMap R S π) n
      (algebraMap S (Ring S ϖ (e * n)) ((v : S) ^ n) * x S ϖ (e * n))
      (y S ϖ (e * n)) _ (x S (algebraMap R S π) n) = _
  apply lift_x

@[simp] theorem ramifiedNodeMap_y
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    ramifiedNodeMap R S π ϖ e n v hπ (y S (algebraMap R S π) n) = y S ϖ (e * n) := by
  change lift (algebraMap R S π) n
      (algebraMap S (Ring S ϖ (e * n)) ((v : S) ^ n) * x S ϖ (e * n))
      (y S ϖ (e * n)) _ (y S (algebraMap R S π) n) = _
  apply lift_y

@[simp] theorem ramifiedNodeInverseMap_x
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    ramifiedNodeInverseMap R S π ϖ e n v hπ (x S ϖ (e * n)) =
      algebraMap S (Ring S (algebraMap R S π) n) ((↑(v⁻¹) : S) ^ n) *
        x S (algebraMap R S π) n := by
  change lift ϖ (e * n)
      (algebraMap S (Ring S (algebraMap R S π) n) ((↑(v⁻¹) : S) ^ n) *
        x S (algebraMap R S π) n)
      (y S (algebraMap R S π) n) _ (x S ϖ (e * n)) = _
  apply lift_x

@[simp] theorem ramifiedNodeInverseMap_y
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    ramifiedNodeInverseMap R S π ϖ e n v hπ (y S ϖ (e * n)) =
      y S (algebraMap R S π) n := by
  change lift ϖ (e * n)
      (algebraMap S (Ring S (algebraMap R S π) n) ((↑(v⁻¹) : S) ^ n) *
        x S (algebraMap R S π) n)
      (y S (algebraMap R S π) n) _ (y S ϖ (e * n)) = _
  apply lift_y

theorem ramifiedNodeMap_comp_inverse
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    (ramifiedNodeMap R S π ϖ e n v hπ).comp
        (ramifiedNodeInverseMap R S π ϖ e n v hπ) =
      AlgHom.id S (Ring S ϖ (e * n)) := by
  apply algHom_ext ϖ (e * n)
  · simp only [AlgHom.coe_comp, Function.comp_apply, ramifiedNodeInverseMap_x,
      map_mul, AlgHom.commutes, ramifiedNodeMap_x, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul, ← mul_pow]
    simp
  · simp only [AlgHom.coe_comp, Function.comp_apply, ramifiedNodeInverseMap_y,
      ramifiedNodeMap_y, AlgHom.id_apply]

theorem ramifiedNodeInverse_comp_map
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    (ramifiedNodeInverseMap R S π ϖ e n v hπ).comp
        (ramifiedNodeMap R S π ϖ e n v hπ) =
      AlgHom.id S (Ring S (algebraMap R S π) n) := by
  apply algHom_ext (algebraMap R S π) n
  · simp only [AlgHom.coe_comp, Function.comp_apply, ramifiedNodeMap_x,
      map_mul, AlgHom.commutes, ramifiedNodeInverseMap_x, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul, ← mul_pow]
    simp
  · simp only [AlgHom.coe_comp, Function.comp_apply, ramifiedNodeMap_y,
      ramifiedNodeInverseMap_y, AlgHom.id_apply]

/-- The explicit `S`-algebra equivalence from the coefficient-extended node to the standard node. -/
noncomputable def ramifiedNodeEquiv
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    Ring S (algebraMap R S π) n ≃ₐ[S] Ring S ϖ (e * n) :=
  AlgEquiv.ofAlgHom (ramifiedNodeMap R S π ϖ e n v hπ)
    (ramifiedNodeInverseMap R S π ϖ e n v hπ)
    (ramifiedNodeMap_comp_inverse R S π ϖ e n v hπ)
    (ramifiedNodeInverse_comp_map R S π ϖ e n v hπ)

/-- Coefficient base change followed by the powered-unit coordinate normalization. -/
noncomputable def ramifiedNodeBaseChangeEquiv
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (_hι : Function.Injective (algebraMap R S))
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    S ⊗[R] Ring R π n ≃ₐ[S] Ring S ϖ (e * n) :=
  (baseChangeEquivLeft R S π n).trans (ramifiedNodeEquiv R S π ϖ e n v hπ)

@[simp] theorem ramifiedNodeBaseChangeEquiv_tmul_x
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (_hι : Function.Injective (algebraMap R S))
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    ramifiedNodeBaseChangeEquiv R S _hι π ϖ e n v hπ (1 ⊗ₜ[R] x R π n) =
      algebraMap S (Ring S ϖ (e * n)) ((v : S) ^ n) * x S ϖ (e * n) := by
  change ramifiedNodeEquiv R S π ϖ e n v hπ
      (baseChangeEquivLeft R S π n (1 ⊗ₜ[R] x R π n)) = _
  rw [baseChangeEquivLeft_tmul_x]
  exact ramifiedNodeMap_x R S π ϖ e n v hπ

@[simp] theorem ramifiedNodeBaseChangeEquiv_tmul_y
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (hι : Function.Injective (algebraMap R S))
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    ramifiedNodeBaseChangeEquiv R S hι π ϖ e n v hπ (1 ⊗ₜ[R] y R π n) =
      y S ϖ (e * n) := by
  change ramifiedNodeEquiv R S π ϖ e n v hπ
      (baseChangeEquivLeft R S π n (1 ⊗ₜ[R] y R π n)) = _
  rw [baseChangeEquivLeft_tmul_y]
  exact ramifiedNodeMap_y R S π ϖ e n v hπ

/-! ## Length and ramification formula -/

theorem nodeThickness_baseChange_eq_mul
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (_hι : Function.Injective (algebraMap R S))
    {π : R} {ϖ : S} (hϖ : Irreducible ϖ) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    nodeThickness S (algebraMap R S π) n = e * n := by
  rw [nodeThickness_eq_parameterLength, parameterPowerIdeal]
  have hpow := ramified_power_formula (R := R) (S := S) (π := π) (ϖ := ϖ)
    (e := e) (n := n) v hπ
  rw [hpow, Ideal.span_singleton_mul_left_unit (v.isUnit.pow n),
    ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal S (e * n)

/-- After a finite étale local DVR extension, the coefficient base change of a standard node
has the normalized target equation with the same exponent.  The returned equivalence is the
actual tensor-product node algebra equivalence, and the final equality records intrinsic
thickness preservation for this node. -/
theorem finiteEtaleDvr_nodeBaseChange_exists
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.Etale R S] [IsLocalHom (algebraMap R S)]
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ) (n : ℕ) :
    ∃ u : Sˣ, algebraMap R S π = (u : S) * ϖ ∧
      Nonempty (S ⊗[R] Ring R π n ≃ₐ[S] Ring S ϖ n) ∧
        nodeThickness S (algebraMap R S π) n = nodeThickness R π n := by
  obtain ⟨u, hu⟩ := formallyUnramifiedDvr_map_uniformizer hπ hϖ
  refine ⟨u, hu, ?_, ?_⟩
  · refine ⟨?_⟩
    have hn : 1 * n = n := Nat.one_mul n
    let E := (baseChangeEquivLeft R S π n).trans
      (ramifiedNodeEquiv R S π ϖ 1 n u (by simpa [pow_one] using hu))
    exact (congrArg (fun k : ℕ => S ⊗[R] Ring R π n ≃ₐ[S] Ring S ϖ k) hn).mp E
  · calc
      nodeThickness S (algebraMap R S π) n =
          intrinsicThickness S ((algebraMap R S π) ^ n) := by
        rw [nodeThickness_eq_parameterLength, parameterPowerIdeal,
          intrinsicThickness_eq_parameterLength]
      _ = intrinsicThickness S (algebraMap R S (π ^ n)) := by rw [map_pow]
      _ = intrinsicThickness R (π ^ n) :=
        intrinsicThickness_baseChange_eq (R := R) (S := S) (π ^ n)
      _ = nodeThickness R π n := by
        rw [intrinsicThickness_eq_parameterLength, nodeThickness_eq_parameterLength,
          parameterPowerIdeal]

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
