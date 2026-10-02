/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.Algebra.TameFactorization
import Mathlib.RingTheory.Norm.Transitivity

/-!
# The tame symbol (Stacks 42.5)

Let `D` be a Noetherian local domain of Krull dimension `≤ 1` with fraction field `K` and unit
differences (`VectorBundle.UnitDifferences D`). All rings below are subrings of the one field `K`
(subalgebras `Subalgebra D K`), and the factorization theory of `TameFactorization.lean`
(admissible overrings, `exists_admissible`) is used throughout.

* For a local ring `R` with a map to `K` and a factorization `f = u₁ π^e₁`, `g = u₂ π^e₂`
  (`PairFactorization`), the *local symbol* is
  `λ_R(f, g) = ((-1)^(e₁ e₂) ū₁^e₂ ū₂^(-e₁))^(ℓ_R(π)) ∈ κ(R)ˣ` (`localSymbol`, defined with a
  chosen factorization and `1` if there is none). When `R` is a Noetherian local domain of
  dimension `≤ 1` with fraction field `K`, it does not depend on the factorization (T0).
* For a subalgebra `C` of `K`, `tameOf D C f g = ∏_{P ∈ MaxSpec C} N_{κ(C_P)/κ(D)} λ_{C_P}(f, g)`.
  It agrees on any two admissible overrings (T1, T2), and `tameSymbol D K hU f g` is its value on
  the admissible overring of `exists_admissible`.

## Main results

* `ordZ`: the integer-valued `Ring.ordFrac` on `Kˣ` (`exp_ordZ`).
* `localSymbol_eq` (**T0**): the local symbol equals the value of any factorization;
  `localSymbol_eq_of_unit`: the canonical form `(-1)^(n₁ n₂) · w̄`, `w = f^n₂ g^(-n₁)`.
* `localSymbol_map`: transport of local symbols along compatible ring isomorphisms.
* `sum_resDeg_mul_ord`: Fulton A.3.1 inside `K`, `ℓ_E(π) = Σ_Q [κ(S_Q):κ(E)] ℓ_{S_Q}(π)`.
* `finprod_normSym_localizationAt`: local refinement, `λ_E = ∏_Q N_{κ(S_Q)/κ(E)} λ_{S_Q}`
  (normed to `κ(D)`), for `(f, g)` factoring in `E` and an overring `S` of `E`.
* `tameOf_eq_of_le` (**T1**) and `tameOf_eq_of_admissible` (**T2**).
* `tameSymbol`, `tameSymbol_eq_tameOf`: the tame symbol and its computation on any admissible
  overring.
* **T3**: `tameSymbol_mul_left`, `tameSymbol_mul_right`, `tameSymbol_one_left`,
  `tameSymbol_one_right`, `tameSymbol_inv_left`, `tameSymbol_inv_right`.
* **T4**: `tameSymbol_units_left` (`∂(u, g) = ū^(ordZ_D g)`), `tameSymbol_units_right`
  (`∂(g, u) = ū^(-ordZ_D g)`), `tameSymbol_units_units`; at the level of an admissible overring
  `tameOf_units_left/right`, using `sum_resDeg_mul_ordZ`.
* **T5**: `tameSymbol_eq_finprod_normDown`, the norm-down formula over an arbitrary overring `B`,
  via `normDown_tameSymbol` (relative tame symbols) and the fibre decomposition
  `tameOf_eq_finprod_semiLoc`.
* **T6**: `tameSymbol_ringEquiv` (invariance under compatible isomorphisms `D ≃+* D'`,
  `K ≃+* K'`) and `tameSymbol_algEquiv` (independence of the choice of fraction field).
-/

namespace GromovWitten.Algebra.Tame

open IsLocalRing

section OrdZ

variable {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [Field K] [Algebra R K] [IsFractionRing R K]

variable (R) in
/-- The integer-valued order `ordFrac_R` of a unit of the fraction field `K` of `R`. -/
noncomputable def ordZ (x : Kˣ) : ℤ := WithZero.log (Ring.ordFrac R (x : K))

/-- `Ring.ordFrac` does not vanish on units of `K`. -/
theorem ordFrac_ne_zero (x : Kˣ) : Ring.ordFrac R (x : K) ≠ 0 :=
  (map_ne_zero (Ring.ordFrac R (K := K))).2 x.ne_zero

/-- `ordZ` is additive. -/
theorem ordZ_mul (x y : Kˣ) : ordZ R (x * y) = ordZ R x + ordZ R y := by
  rw [ordZ, Units.val_mul, map_mul, WithZero.log_mul (ordFrac_ne_zero x) (ordFrac_ne_zero y)]
  rfl

/-- `ordZ 1 = 0`. -/
theorem ordZ_one : ordZ R (1 : Kˣ) = 0 := by
  simp [ordZ]

/-- `ordZ (x ^ n) = n * ordZ x`. -/
theorem ordZ_zpow (x : Kˣ) (n : ℤ) : ordZ R (x ^ n) = n * ordZ R x := by
  rw [ordZ, Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  rfl

/-- `ordZ x⁻¹ = - ordZ x`. -/
theorem ordZ_inv (x : Kˣ) : ordZ R x⁻¹ = - ordZ R x := by
  simpa using ordZ_zpow (R := R) x (-1)

/-- Units of `R` have `ordZ` zero. -/
theorem ordZ_units_map (u : Rˣ) : ordZ R (Units.map (algebraMap R K : R →* K) u) = 0 := by
  rw [ordZ, Units.coe_map, MonoidHom.coe_coe, Ring.ordFrac_of_isUnit u.isUnit]
  rfl

/-- For `r ∈ R` nonzero, `ordZ r` is the length `ℓ_R(R/r)`. -/
theorem ordZ_mk0 (r : R) (hr : algebraMap R K r ≠ 0) :
    ordZ R (Units.mk0 _ hr) = ((Ring.ord R r).toNat : ℤ) := by
  have hr0 : r ≠ 0 := fun h ↦ hr (by simp [h])
  have hnz : r ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hr0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  rw [ordZ, Units.val_mk0, Ring.ordFrac_eq_ord R hr0,
    Ring.ordMonoidWithZeroHom_eq_coe _ hnz hm.symm, ← hm]
  rfl

/-- `ordZ` is the integer underlying `Ring.ordFrac`: `exp (ordZ x) = ordFrac x` in `ℤᵐ⁰`. -/
theorem exp_ordZ (x : Kˣ) : WithZero.exp (ordZ R x) = Ring.ordFrac R (x : K) :=
  WithZero.exp_log (ordFrac_ne_zero x)

end OrdZ

section LocalSymbol

variable {R K : Type*} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]

variable (R) in
/-- A *factorization* of the pair `(f, g)` of units of `K` in the local ring `R` (with a ring map
`R → K`): an element `π` of `R` with nonzero image in `K`, integers `e₁, e₂` and units `u₁, u₂`
of `R` with `f = u₁ π ^ e₁` and `g = u₂ π ^ e₂` in `K`. -/
structure PairFactorization (f g : Kˣ) where
  /-- The common "uniformizer". -/
  π : R
  /-- The exponent of `f`. -/
  e₁ : ℤ
  /-- The exponent of `g`. -/
  e₂ : ℤ
  /-- The unit part of `f`. -/
  u₁ : Rˣ
  /-- The unit part of `g`. -/
  u₂ : Rˣ
  hπ : algebraMap R K π ≠ 0
  hf : (f : K) = algebraMap R K u₁ * algebraMap R K π ^ e₁
  hg : (g : K) = algebraMap R K u₂ * algebraMap R K π ^ e₂

variable (R) in
/-- Reduction of units of the local ring `R` to units of its residue field. -/
noncomputable abbrev resUnits : Rˣ →* (ResidueField R)ˣ :=
  Units.map (residue R : R →* ResidueField R)

variable {f g : Kˣ}

/-- The value `((-1)^(e₁ e₂) ū₁^e₂ ū₂^(-e₁))^(ℓ_R(π))` attached to a factorization. -/
noncomputable def PairFactorization.symbol (F : PairFactorization R f g) : (ResidueField R)ˣ :=
  ((-1) ^ (F.e₁ * F.e₂) * resUnits R F.u₁ ^ F.e₂ * resUnits R F.u₂ ^ (-F.e₁)) ^
    (Ring.ord R F.π).toNat

variable (R) in
/-- **The local tame symbol** `λ_R(f, g) ∈ κ(R)ˣ`: the value
`((-1)^(e₁ e₂) ū₁^e₂ ū₂^(-e₁))^(ℓ_R(π))` of a chosen factorization `f = u₁ π^e₁`, `g = u₂ π^e₂`
in `R` (see `localSymbol_eq` for independence of the choice), and `1` if the pair does not
factor in `R`. -/
noncomputable def localSymbol (f g : Kˣ) : (ResidueField R)ˣ :=
  open Classical in if h : Nonempty (PairFactorization R f g) then h.some.symbol else 1

section T0

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsFractionRing R K]

omit [IsLocalRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Units of `R` embed into units of its fraction field. -/
theorem units_map_injective_of_isFractionRing :
    Function.Injective (Units.map (algebraMap R K : R →* K)) :=
  Units.map_injective (IsFractionRing.injective R K)

omit [IsLocalRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsFractionRing R K] in
/-- The factorization of `f` as an identity in `Kˣ`. -/
theorem PairFactorization.eq_left (F : PairFactorization R f g) :
    f = Units.map (algebraMap R K : R →* K) F.u₁ * Units.mk0 _ F.hπ ^ F.e₁ :=
  Units.ext (by simp [F.hf])

omit [IsLocalRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsFractionRing R K] in
/-- The factorization of `g` as an identity in `Kˣ`. -/
theorem PairFactorization.eq_right (F : PairFactorization R f g) :
    g = Units.map (algebraMap R K : R →* K) F.u₂ * Units.mk0 _ F.hπ ^ F.e₂ :=
  Units.ext (by simp [F.hg])

omit [IsLocalRing R] in
/-- `ordZ f = e₁ · ℓ_R(π)` for a factorization. -/
theorem PairFactorization.ordZ_left (F : PairFactorization R f g) :
    ordZ R f = F.e₁ * ((Ring.ord R F.π).toNat : ℤ) := by
  rw [congrArg (ordZ R) F.eq_left, ordZ_mul, ordZ_units_map, ordZ_zpow, ordZ_mk0, zero_add]

omit [IsLocalRing R] in
/-- `ordZ g = e₂ · ℓ_R(π)` for a factorization. -/
theorem PairFactorization.ordZ_right (F : PairFactorization R f g) :
    ordZ R g = F.e₂ * ((Ring.ord R F.π).toNat : ℤ) := by
  rw [congrArg (ordZ R) F.eq_right, ordZ_mul, ordZ_units_map, ordZ_zpow, ordZ_mk0, zero_add]

private theorem zpow_mul_self_of_sq {G : Type*} [Group G] (s : G) (hs : s ^ (2 : ℤ) = 1)
    (m : ℤ) : s ^ (m * m) = s ^ m := by
  rw [zpow_eq_zpow_emod (m * m) hs, zpow_eq_zpow_emod m hs]
  congr 1
  refine Int.ModEq.eq (Int.modEq_iff_dvd.2 ?_)
  rw [show m - m * m = -(m * (m - 1)) by ring, dvd_neg]
  exact even_iff_two_dvd.1 (Int.even_mul_pred_self m)

private theorem comm_aux {G : Type*} [CommGroup G] (U₁ U₂ P : G) (a b m : ℤ) :
    (U₁ * P ^ a) ^ (b * m) * (U₂ * P ^ b) ^ (-(a * m)) = (U₁ ^ b * U₂ ^ (-a)) ^ m := by
  rw [mul_zpow, mul_zpow, mul_mul_mul_comm, ← zpow_mul, ← zpow_mul, ← zpow_add,
    show a * (b * m) + b * -(a * m) = 0 by ring, zpow_zero, mul_one, mul_zpow, ← zpow_mul,
    ← zpow_mul, neg_mul]

omit [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
private theorem symbol_eq_aux (π : R) (e₁ e₂ : ℤ) (u₁ u₂ : Rˣ) (hπ : algebraMap R K π ≠ 0)
    (m : ℕ) (w : Rˣ) (hw : Units.map (algebraMap R K : R →* K) w =
      (Units.map (algebraMap R K : R →* K) u₁ * Units.mk0 _ hπ ^ e₁) ^ (e₂ * (m : ℤ)) *
      (Units.map (algebraMap R K : R →* K) u₂ * Units.mk0 _ hπ ^ e₂) ^ (-(e₁ * (m : ℤ)))) :
    ((-1) ^ (e₁ * e₂) * resUnits R u₁ ^ e₂ * resUnits R u₂ ^ (-e₁)) ^ m =
      (-1) ^ (e₁ * (m : ℤ) * (e₂ * m)) * resUnits R w := by
  have hv : (u₁ ^ e₂ * u₂ ^ (-e₁)) ^ (m : ℤ) = w := by
    apply units_map_injective_of_isFractionRing (K := K)
    rw [hw, map_zpow, map_mul, map_zpow, map_zpow, comm_aux]
  rw [← hv, ← zpow_natCast, mul_assoc, mul_zpow, map_zpow, map_mul, map_zpow, map_zpow,
    show e₁ * (m : ℤ) * (e₂ * m) = e₁ * e₂ * (m * m) by ring]
  congr 1
  rw [zpow_mul (-1) (e₁ * e₂) (m * m),
    zpow_mul_self_of_sq _ (by rw [← zpow_mul, mul_comm, zpow_mul]; simp)]

/-- **Canonical form of the local symbol.** For any factorization, the symbol equals
`(-1)^(n₁ n₂) · w̄`, where `n₁ = ordZ f`, `n₂ = ordZ g` and `w` is the unit of `R` equal to
`f^n₂ g^(-n₁)` in `K`. -/
theorem PairFactorization.symbol_eq (F : PairFactorization R f g) (w : Rˣ)
    (hw : Units.map (algebraMap R K : R →* K) w = f ^ ordZ R g * g ^ (-ordZ R f)) :
    F.symbol = (-1) ^ (ordZ R f * ordZ R g) * resUnits R w := by
  rw [F.ordZ_left, F.ordZ_right] at hw ⊢
  exact symbol_eq_aux F.π F.e₁ F.e₂ F.u₁ F.u₂ F.hπ _ w
    (hw.trans (congrArg₂ (fun a b ↦ a ^ _ * b ^ _) F.eq_left F.eq_right))

omit [IsLocalRing R] in
/-- A factorization provides a unit `w` of `R` equal to `f^(ordZ g) g^(-ordZ f)`. -/
theorem PairFactorization.exists_unit (F : PairFactorization R f g) :
    ∃ w : Rˣ, Units.map (algebraMap R K : R →* K) w = f ^ ordZ R g * g ^ (-ordZ R f) := by
  refine ⟨(F.u₁ ^ F.e₂ * F.u₂ ^ (-F.e₁)) ^ ((Ring.ord R F.π).toNat : ℤ), ?_⟩
  rw [F.ordZ_left, F.ordZ_right, map_zpow, map_mul, map_zpow, map_zpow, ← comm_aux _ _
    (Units.mk0 _ F.hπ)]
  exact (congrArg₂ (fun a b ↦ a ^ _ * b ^ _) F.eq_left F.eq_right).symm

/-- **T0: the local symbol does not depend on the factorization.** For every factorization `F`
of `(f, g)` in `R`, `localSymbol R f g` is the value `((-1)^(e₁ e₂) ū₁^e₂ ū₂^(-e₁))^(ℓ_R(π))`
computed from `F`. -/
theorem localSymbol_eq (F : PairFactorization R f g) : localSymbol R f g = F.symbol := by
  have h : Nonempty (PairFactorization R f g) := ⟨F⟩
  rw [localSymbol, dif_pos h]
  obtain ⟨w, hw⟩ := F.exists_unit
  rw [h.some.symbol_eq w hw, F.symbol_eq w hw]

/-- The local symbol in canonical form: `(-1)^(n₁ n₂) · w̄` where `n₁ = ordZ f`,
`n₂ = ordZ g` and `w ∈ Rˣ` equals `f^n₂ g^(-n₁)` in `K`. -/
theorem localSymbol_eq_of_unit (F : PairFactorization R f g) (w : Rˣ)
    (hw : Units.map (algebraMap R K : R →* K) w = f ^ ordZ R g * g ^ (-ordZ R f)) :
    localSymbol R f g = (-1) ^ (ordZ R f * ordZ R g) * resUnits R w := by
  rw [localSymbol_eq F, F.symbol_eq w hw]

end T0

/-- If the pair does not factor in `R`, the local symbol is `1`. -/
theorem localSymbol_of_isEmpty (h : IsEmpty (PairFactorization R f g)) :
    localSymbol R f g = 1 := by
  rw [localSymbol, dif_neg (not_nonempty_iff.2 h)]

end LocalSymbol

section Transport

variable {R R' K K' : Type*} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [CommRing R'] [IsLocalRing R'] [Field K'] [Algebra R' K']
  (φ : R ≃+* R') (σ : K ≃+* K') (hσ : ∀ r : R, σ (algebraMap R K r) = algebraMap R' K' (φ r))

include hσ in
/-- Transport of a factorization along compatible isomorphisms. -/
noncomputable def PairFactorization.map {f g : Kˣ} (F : PairFactorization R f g) :
    PairFactorization R' (Units.map (σ : K →* K') f) (Units.map (σ : K →* K') g) where
  π := φ F.π
  e₁ := F.e₁
  e₂ := F.e₂
  u₁ := Units.map (φ : R →* R') F.u₁
  u₂ := Units.map (φ : R →* R') F.u₂
  hπ := by rw [← hσ]; exact (map_ne_zero σ).2 F.hπ
  hf := by simp [F.hf, hσ]
  hg := by simp [F.hg, hσ]

open GromovWitten.AlgebraicGeometry.IntersectionTheory in
include hσ in
/-- The value of a transported factorization is the transported value. -/
theorem PairFactorization.symbol_map {f g : Kˣ} (F : PairFactorization R f g) :
    (F.map φ σ hσ).symbol = Units.map (ResidueField.mapEquiv φ : ResidueField R →* _)
      F.symbol := by
  simp only [PairFactorization.symbol, PairFactorization.map, LocalOrdSymmetry.ord_ringEquiv,
    map_pow, map_mul, map_zpow]
  congr 3
  ext
  simp

omit [IsLocalRing R] [IsLocalRing R'] in
include hσ in
/-- A pair factors in `R` iff its transport factors in `R'`. -/
theorem nonempty_pairFactorization_map_iff {f g : Kˣ} :
    Nonempty (PairFactorization R' (Units.map (σ : K →* K') f) (Units.map (σ : K →* K') g)) ↔
      Nonempty (PairFactorization R f g) := by
  refine ⟨fun ⟨F'⟩ ↦ ?_, fun ⟨F⟩ ↦ ⟨F.map φ σ hσ⟩⟩
  have hσ' : ∀ r : R', σ.symm (algebraMap R' K' r) = algebraMap R K (φ.symm r) := by
    intro r
    rw [σ.symm_apply_eq, hσ, RingEquiv.apply_symm_apply]
  have e : ∀ x : Kˣ, Units.map (σ.symm : K' →* K) (Units.map (σ : K →* K') x) = x :=
    fun x ↦ Units.ext (by simp)
  have := F'.map φ.symm σ.symm hσ'
  rw [e, e] at this
  exact ⟨this⟩

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsFractionRing R K]
  [IsDomain R'] [IsNoetherianRing R'] [Ring.KrullDimLE 1 R'] [IsFractionRing R' K']

include hσ in
/-- **Transport of the local symbol** along isomorphisms `φ : R ≃+* R'`, `σ : K ≃+* K'`
compatible with the maps to the fraction fields. -/
theorem localSymbol_map (f g : Kˣ) :
    localSymbol R' (Units.map (σ : K →* K') f) (Units.map (σ : K →* K') g) =
      Units.map (ResidueField.mapEquiv φ : ResidueField R →* _) (localSymbol R f g) := by
  by_cases h : Nonempty (PairFactorization R f g)
  · obtain ⟨F⟩ := h
    rw [localSymbol_eq F, localSymbol_eq (F.map φ σ hσ), PairFactorization.symbol_map]
  · rw [localSymbol_of_isEmpty (not_nonempty_iff.1 h), localSymbol_of_isEmpty
      (not_nonempty_iff.1 fun h' ↦ h ((nonempty_pairFactorization_map_iff φ σ hσ).1 h')),
      map_one]

end Transport

section MapHom

variable {R R' K : Type*} [CommRing R] [Field K] [Algebra R K] [CommRing R'] [Algebra R' K]

/-- Push a factorization forward along a ring map compatible with the maps to `K`. -/
noncomputable def PairFactorization.mapHom {f g : Kˣ} (F : PairFactorization R f g)
    (ψ : R →+* R') (hψ : ∀ r, algebraMap R' K (ψ r) = algebraMap R K r) :
    PairFactorization R' f g where
  π := ψ F.π
  e₁ := F.e₁
  e₂ := F.e₂
  u₁ := Units.map (ψ : R →* R') F.u₁
  u₂ := Units.map (ψ : R →* R') F.u₂
  hπ := by rw [hψ]; exact F.hπ
  hf := by simp [F.hf, hψ]
  hg := by simp [F.hg, hψ]

end MapHom

/-- The norm of an element coming from an intermediate field. -/
theorem units_norm_algebraMap {k A B : Type*} [Field k] [Field A] [Field B] [Algebra k A]
    [Algebra A B] [Algebra k B] [IsScalarTower k A B] (s : Aˣ) :
    Units.map (Algebra.norm k : B →* k) (Units.map (algebraMap A B : A →* B) s) =
      Units.map (Algebra.norm k : A →* k) s ^ Module.finrank A B := by
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
  rw [← Algebra.norm_norm (S := A), Algebra.norm_algebraMap, map_pow]

section Extension

variable {R R' K : Type*} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [CommRing R'] [IsLocalRing R'] [Algebra R' K] [Algebra R R'] [IsLocalHom (algebraMap R R')]
  (hK : ∀ r : R, algebraMap R' K (algebraMap R R' r) = algebraMap R K r)

/-- The unit `(-1)^(e₁ e₂) ū₁^e₂ ū₂^(-e₁)` of `κ(R)` attached to a factorization; the symbol is its
`ℓ_R(π)`-th power. -/
noncomputable def PairFactorization.base {f g : Kˣ} (F : PairFactorization R f g) :
    (ResidueField R)ˣ :=
  (-1) ^ (F.e₁ * F.e₂) * resUnits R F.u₁ ^ F.e₂ * resUnits R F.u₂ ^ (-F.e₁)

/-- The symbol of a factorization is its base unit raised to `ℓ_R(π)`. -/
theorem PairFactorization.symbol_eq_base {f g : Kˣ} (F : PairFactorization R f g) :
    F.symbol = F.base ^ (Ring.ord R F.π).toNat := rfl

variable [IsDomain R'] [IsNoetherianRing R'] [Ring.KrullDimLE 1 R'] [IsFractionRing R' K]

include hK in
/-- **Local symbols after a local extension.** If `(f, g)` factors in `R` and `R → R'` is a
local homomorphism compatible with the maps to `K`, then `λ_{R'}(f,g)` is the image of the base
unit of the factorization raised to `ℓ_{R'}(π)`. -/
theorem localSymbol_of_localHom {f g : Kˣ} (F : PairFactorization R f g) :
    localSymbol R' f g = Units.map (algebraMap (ResidueField R) (ResidueField R') : _ →* _)
      F.base ^ (Ring.ord R' (algebraMap R R' F.π)).toNat := by
  rw [localSymbol_eq (F.mapHom (algebraMap R R') hK), PairFactorization.symbol_eq_base]
  congr 1
  simp only [PairFactorization.base, PairFactorization.mapHom, map_mul, map_zpow]
  congr 3
  ext
  simp

variable {A : Type*} [CommRing A] [IsLocalRing A] [Algebra A R] [Algebra A R']
  [IsLocalHom (algebraMap A R)] [IsLocalHom (algebraMap A R')] [IsScalarTower A R R']

include hK in
/-- **Norms of local symbols after a local extension.** With `A → R → R'` local, the norm to
`κ(A)` of `λ_{R'}(f, g)` is `N_{κ(R)/κ(A)}(base)^([κ(R'):κ(R)] · ℓ_{R'}(π))`. -/
theorem norm_localSymbol_of_localHom {f g : Kˣ} (F : PairFactorization R f g) :
    Units.map (Algebra.norm (ResidueField A) : ResidueField R' →* ResidueField A)
        (localSymbol R' f g) =
      Units.map (Algebra.norm (ResidueField A) : ResidueField R →* ResidueField A) F.base ^
        (Module.finrank (ResidueField R) (ResidueField R') *
          (Ring.ord R' (algebraMap R R' F.π)).toNat) := by
  rw [localSymbol_of_localHom hK F, map_pow, units_norm_algebraMap, pow_mul]

end Extension

section Subalgebra

variable {D K : Type*} [CommRing D] [IsDomain D] [Field K] [Algebra D K] [IsFractionRing D K]

/-- Every subalgebra of the fraction field `K` of `D` has fraction field `K`. -/
instance isFractionRing_subalgebra_tame (E : Subalgebra D K) : IsFractionRing E K :=
  IsFractionRing.of_field E K fun z ↦ by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := D) z
    exact ⟨algebraMap D E a, algebraMap D E b, rfl⟩

omit [IsDomain D] [IsFractionRing D K] in
/-- A factorization of `![f, g]` in the sense of `Factors` gives a `PairFactorization`. -/
theorem Factors.nonempty_pairFactorization {S : Subalgebra D K} {f g : Kˣ}
    (h : Factors S ![f, g]) : Nonempty (PairFactorization S f g) := by
  obtain ⟨π, e, u, hπ, hu⟩ := h
  exact ⟨⟨π, e 0, e 1, u 0, u 1, hπ, hu 0, hu 1⟩⟩

omit [IsDomain D] [IsFractionRing D K] in
/-- A `PairFactorization` gives a factorization of `![f, g]` in the sense of `Factors`. -/
theorem PairFactorization.factors {S : Subalgebra D K} {f g : Kˣ}
    (F : PairFactorization S f g) : Factors S ![f, g] :=
  ⟨F.π, ![F.e₁, F.e₂], ![F.u₁, F.u₂], F.hπ, fun i ↦ by
    fin_cases i
    · exact F.hf
    · exact F.hg⟩

variable (D K) in
/-- The canonical isomorphism `D ≃+* ⊥` onto the bottom subalgebra of `K`. -/
noncomputable def botRingEquiv : D ≃+* (⊥ : Subalgebra D K) :=
  (Algebra.botEquivOfInjective (IsFractionRing.injective D K)).symm.toRingEquiv

omit [IsDomain D] in
/-- `botRingEquiv` is `algebraMap D K` on underlying elements. -/
@[simp]
theorem coe_botRingEquiv (d : D) : ((botRingEquiv D K d : (⊥ : Subalgebra D K)) : K) =
    algebraMap D K d := by
  have : botRingEquiv D K d = algebraMap D (⊥ : Subalgebra D K) d :=
    ((Algebra.botEquivOfInjective (IsFractionRing.injective D K)).symm_apply_eq).2
      (by simp [Algebra.botEquivOfInjective])
  rw [this]
  rfl

/-- `⊥ ≅ D` is local if `D` is. -/
instance isLocalRing_bot_tame [IsLocalRing D] : IsLocalRing (⊥ : Subalgebra D K) :=
  IsLocalRing.of_surjective' (botRingEquiv D K : D →+* _) (botRingEquiv D K).surjective

/-- `⊥ ≅ D` is Noetherian if `D` is. -/
instance isNoetherianRing_bot_tame [IsNoetherianRing D] :
    IsNoetherianRing (⊥ : Subalgebra D K) :=
  isNoetherianRing_of_ringEquiv D (botRingEquiv D K)

/-- `⊥ ≅ D` has dimension `≤ 1` if `D` has. -/
instance krullDimLE_bot_tame [Ring.KrullDimLE 1 D] :
    Ring.KrullDimLE 1 (⊥ : Subalgebra D K) := by
  rw [Ring.krullDimLE_iff, ← ringKrullDim_eq_of_ringEquiv (botRingEquiv D K)]
  exact Ring.krullDimLE_iff.1 ‹_›

omit [IsDomain D] in
/-- `algebraMap D ⊥` is the isomorphism `botRingEquiv`. -/
theorem algebraMap_bot_eq :
    (algebraMap D (⊥ : Subalgebra D K)) = (botRingEquiv D K : D →+* _) :=
  RingHom.ext fun d ↦ Subtype.ext (coe_botRingEquiv d).symm

/-- `D → ⊥` is a local homomorphism. -/
instance isLocalHom_algebraMap_bot [IsLocalRing D] :
    IsLocalHom (algebraMap D (⊥ : Subalgebra D K)) := by
  rw [algebraMap_bot_eq]
  infer_instance

omit [IsDomain D] [IsFractionRing D K] in
/-- Local homomorphisms compose along inclusions of subalgebras. -/
theorem isLocalHom_algebraMap_of_le {E S : Subalgebra D K} (h : E ≤ S)
    [IsLocalHom (algebraMap D E)] [IsLocalHom (Subalgebra.inclusion h : E →+* S)] :
    IsLocalHom (algebraMap D S) := by
  have : algebraMap D S = (Subalgebra.inclusion h : E →+* S).comp (algebraMap D E) := rfl
  rw [this]
  infer_instance

omit [IsDomain D] [IsFractionRing D K] in
/-- The inclusion of a local subalgebra `E` into a localization of an overring at a maximal
ideal is a local homomorphism. -/
theorem isLocalHom_inclusion_localizationAt {E S : Subalgebra D K} [IsLocalRing E]
    (hES : IsOverring E S) (Q : Ideal S) [Q.IsMaximal] :
    IsLocalHom (Subalgebra.inclusion (hES.le.trans (le_localizationAt S Q)) :
      E →+* localizationAt S Q) := by
  refine ⟨fun e he ↦ ?_⟩
  by_contra hne
  have h1 : e ∈ maximalIdeal E := (mem_maximalIdeal e).2 hne
  rw [← hES.comap_eq_maximalIdeal Q, Ideal.mem_comap] at h1
  have h2 := (IsLocalization.AtPrime.to_map_mem_maximal_iff (localizationAt S Q) Q _).2 h1
  exact (mem_maximalIdeal _).1 h2 he

end Subalgebra

section NormSymbol

variable {D K : Type*} [CommRing D] [IsLocalRing D] [Field K] [Algebra D K]

/-- The norm `N_{κ(E)/κ(D)} : κ(E)ˣ → κ(D)ˣ` for a local subalgebra `E` of `K` such that `D → E`
is a local homomorphism (so that `κ(E)` is a `κ(D)`-algebra); the trivial map otherwise. For the
local rings of overrings of `D` the homomorphism is always local
(`isLocalHom_algebraMap_localizationAt`). -/
noncomputable def normDown (E : Subalgebra D K) [IsLocalRing E] :
    (ResidueField E)ˣ →* (ResidueField D)ˣ :=
  open Classical in if h : IsLocalHom (algebraMap D E) then
    haveI := h
    Units.map (Algebra.norm (ResidueField D) : ResidueField E →* ResidueField D)
  else 1

/-- `normDown E` is the residue-field norm when `D → E` is local. -/
theorem normDown_eq (E : Subalgebra D K) [IsLocalRing E] [IsLocalHom (algebraMap D E)] :
    normDown E = Units.map (Algebra.norm (ResidueField D) : ResidueField E →* ResidueField D) := by
  rw [normDown, dif_pos ‹_›]

/-- The norm down to `κ(D)ˣ` of the local symbol of a local subalgebra `E` of `K`
(see `normDown`). -/
noncomputable def normSym (E : Subalgebra D K) [IsLocalRing E] (f g : Kˣ) :
    (ResidueField D)ˣ :=
  normDown E (localSymbol E f g)

/-- `normSym E` is the residue-field norm of the local symbol when `D → E` is local. -/
theorem normSym_eq (E : Subalgebra D K) [IsLocalRing E] [IsLocalHom (algebraMap D E)]
    (f g : Kˣ) : normSym E f g =
      Units.map (Algebra.norm (ResidueField D) : ResidueField E →* ResidueField D)
        (localSymbol E f g) := by
  rw [normSym, normDown_eq]

/-- `normSym` only depends on the subalgebra. -/
theorem normSym_congr {E E' : Subalgebra D K} [IsLocalRing E] [IsLocalRing E'] (h : E = E')
    (f g : Kˣ) : normSym E f g = normSym E' f g := by
  subst h
  rfl

variable (D) in
/-- The candidate tame symbol computed on a subalgebra `C` of `K`: the product over the maximal
ideals `P` of `C` of `normSym (C_P) f g`. It is the tame symbol whenever `C` is an admissible
overring for `(f, g)` (see `tameSymbol_eq_tameOf`). -/
noncomputable def tameOf (C : Subalgebra D K) (f g : Kˣ) : (ResidueField D)ˣ :=
  ∏ᶠ P : MaximalSpectrum C, normSym (localizationAt C P.asIdeal) f g

end NormSymbol

section LocalRefinement

variable {D K : Type*} [CommRing D] [IsDomain D] [Field K] [Algebra D K] [IsFractionRing D K]

variable (D) in
/-- The residue degree `[κ(L) : κ(E)]` of local subalgebras `E ≤ L` of `K` whose inclusion is a
local homomorphism (`0` otherwise). -/
noncomputable def resDeg {E L : Subalgebra D K} [IsLocalRing E] [IsLocalRing L] (h : E ≤ L) : ℕ :=
  letI := (Subalgebra.inclusion h).toAlgebra
  open Classical in
  if hl : IsLocalHom (algebraMap E L) then
    haveI := hl
    Module.finrank (ResidueField E) (ResidueField L)
  else 0

omit [IsDomain D] [IsFractionRing D K] in
/-- `resDeg` is the residue degree for any algebra structure given by the inclusion. -/
theorem resDeg_eq {E L : Subalgebra D K} [IsLocalRing E] [IsLocalRing L] (h : E ≤ L)
    [Algebra E L] (hE : ∀ x, (algebraMap E L x : K) = x) [IsLocalHom (algebraMap E L)] :
    resDeg D h = Module.finrank (ResidueField E) (ResidueField L) := by
  have halg : ‹Algebra E L› = (Subalgebra.inclusion h).toAlgebra :=
    Algebra.algebra_ext _ _ fun x ↦ Subtype.ext (hE x)
  subst halg
  rw [resDeg, dif_pos ‹_›]

/-- **Fulton A.3.1 inside `K`.** For a Noetherian local subalgebra `E` of dimension `≤ 1`, an
overring `S` of `E` and `π ∈ E` nonzero, `ℓ_E(π) = Σ_Q [κ(S_Q) : κ(E)] ℓ_{S_Q}(π)`. -/
theorem sum_resDeg_mul_ord {E S : Subalgebra D K} [IsLocalRing E] [IsNoetherianRing E]
    [Ring.KrullDimLE 1 E] (hES : IsOverring E S) (π : E) (hπ : π ≠ 0) :
    ∑ᶠ Q : MaximalSpectrum S, resDeg D (hES.le.trans (le_localizationAt S Q.asIdeal)) *
      (Ring.ord (localizationAt S Q.asIdeal)
        (Subalgebra.inclusion (hES.le.trans (le_localizationAt S Q.asIdeal)) π)).toNat =
      (Ring.ord E π).toNat := by
  classical
  have := hES.finite_maximalSpectrum
  have : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  have := hES.isNoetherianRing
  have := hES.krullDimLE
  let _ : Algebra E S := (Subalgebra.inclusion hES.le).toAlgebra
  have : Module.Finite E S := hES.moduleFinite
  have hinj : Function.Injective (algebraMap E S) := Subalgebra.inclusion_injective _
  have hrank : ∀ b : S, ∃ (s : E) (a : E), s ≠ 0 ∧ s • b = algebraMap E S a := by
    intro b
    obtain ⟨x, y, hy, hb⟩ := IsFractionRing.div_surjective (A := D) (b : K)
    have hy0 : algebraMap D K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    refine ⟨algebraMap D E y, algebraMap D E x,
      fun h ↦ hy0 (by simpa using congrArg Subtype.val h), Subtype.ext ?_⟩
    change algebraMap D K y * (b : K) = algebraMap D K x
    rw [← hb]
    field_simp
  have key := OrderBirational.ord_eq_finsum hinj hrank hπ
  have hterm : ∀ Q : MaximalSpectrum S,
      (Module.finrank (ResidueField E) Q.asIdeal.ResidueField : ℕ∞) *
        Ring.ord (Localization.AtPrime Q.asIdeal)
          (algebraMap E (Localization.AtPrime Q.asIdeal) π) =
      ((resDeg D (hES.le.trans (le_localizationAt S Q.asIdeal)) *
        (Ring.ord (localizationAt S Q.asIdeal)
          (Subalgebra.inclusion (hES.le.trans (le_localizationAt S Q.asIdeal)) π)).toNat : ℕ) :
        ℕ∞) := by
    intro Q
    have hle := hES.le.trans (le_localizationAt S Q.asIdeal)
    let φ := (localizationAtEquiv S Q.asIdeal).toRingEquiv
    have hφ : ∀ e : E, φ (algebraMap E (Localization.AtPrime Q.asIdeal) e) =
        Subalgebra.inclusion hle e := by
      intro e
      rw [IsScalarTower.algebraMap_apply E S (Localization.AtPrime Q.asIdeal)]
      exact (localizationAtEquiv S Q.asIdeal).commutes _
    have hπL : Subalgebra.inclusion hle π ≠ 0 := fun h ↦ hπ (Subalgebra.inclusion_injective hle
      (by rw [h, map_zero]))
    have hord : Ring.ord (Localization.AtPrime Q.asIdeal)
        (algebraMap E (Localization.AtPrime Q.asIdeal) π) =
        Ring.ord (localizationAt S Q.asIdeal) (Subalgebra.inclusion hle π) := by
      rw [← hφ, GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalOrdSymmetry.ord_ringEquiv]
    let _ : Algebra E (localizationAt S Q.asIdeal) := (Subalgebra.inclusion hle).toAlgebra
    have : IsLocalHom (algebraMap E (localizationAt S Q.asIdeal)) :=
      isLocalHom_inclusion_localizationAt hES Q.asIdeal
    have hfr : Module.finrank (ResidueField E) Q.asIdeal.ResidueField =
        Module.finrank (ResidueField E) (ResidueField (localizationAt S Q.asIdeal)) := by
      have hc : ∀ x : ResidueField E, ResidueField.mapEquiv φ
          (algebraMap (ResidueField E) Q.asIdeal.ResidueField x) =
          algebraMap (ResidueField E) (ResidueField (localizationAt S Q.asIdeal)) x := by
        intro x
        obtain ⟨e, rfl⟩ := residue_surjective x
        rw [ResidueField.algebraMap_residue, ResidueField.algebraMap_residue,
          ResidueField.mapEquiv_apply, ResidueField.map_residue]
        exact congrArg (residue _) (hφ e)
      exact (AlgEquiv.ofRingEquiv hc).toLinearEquiv.finrank_eq
    rw [hord, hfr, resDeg_eq hle (fun _ ↦ rfl), Nat.cast_mul,
      ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hπL))]
  rw [finsum_congr hterm, finsum_eq_sum_of_fintype, ← Nat.cast_sum,
    ← finsum_eq_sum_of_fintype] at key
  rw [key, ENat.toNat_natCast]

variable [IsLocalRing D] {f g : Kˣ}

omit [IsDomain D] in
/-- The normed local symbol at a localization of an overring, computed from a factorization in
the local base `E`. -/
theorem normSym_localizationAt_of_factorization {E S : Subalgebra D K} [IsLocalRing E]
    [IsLocalHom (algebraMap D E)] (hES : IsOverring E S) [IsNoetherianRing E]
    [Ring.KrullDimLE 1 E] (Q : Ideal S) [Q.IsMaximal] (F : PairFactorization E f g) :
    normSym (localizationAt S Q) f g =
      Units.map (Algebra.norm (ResidueField D) : ResidueField E →* ResidueField D) F.base ^
        (resDeg D (hES.le.trans (le_localizationAt S Q)) *
          (Ring.ord (localizationAt S Q)
            (Subalgebra.inclusion (hES.le.trans (le_localizationAt S Q)) F.π)).toNat) := by
  have hle := hES.le.trans (le_localizationAt S Q)
  have := hES.isNoetherianRing
  have := hES.krullDimLE
  have hloc := isLocalHom_inclusion_localizationAt hES Q
  have := isLocalHom_algebraMap_of_le hle
  let _ : Algebra E (localizationAt S Q) := (Subalgebra.inclusion hle).toAlgebra
  have : IsLocalHom (algebraMap E (localizationAt S Q)) := hloc
  have : IsScalarTower D E (localizationAt S Q) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  rw [normSym_eq,
    norm_localSymbol_of_localHom (A := D) (R := E) (R' := localizationAt S Q) (fun _ ↦ rfl) F,
    resDeg_eq hle (fun _ ↦ rfl)]
  rfl

/-- **Local refinement.** If `(f, g)` factors in the Noetherian local subalgebra `E` (of
dimension `≤ 1`, with `D → E` local) and `S` is an overring of `E`, then the product over the
maximal ideals `Q` of `S` of `normSym (S_Q) f g` equals `normSym E f g`. -/
theorem finprod_normSym_localizationAt {E S : Subalgebra D K} [IsLocalRing E]
    [IsLocalHom (algebraMap D E)] (hES : IsOverring E S) [IsNoetherianRing E]
    [Ring.KrullDimLE 1 E] (F : PairFactorization E f g) :
    ∏ᶠ Q : MaximalSpectrum S, normSym (localizationAt S Q.asIdeal) f g = normSym E f g := by
  have := hES.finite_maximalSpectrum
  have : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  have hπ : F.π ≠ 0 := fun h ↦ F.hπ (by rw [h, map_zero])
  rw [finprod_eq_prod_of_fintype]
  simp_rw [normSym_localizationAt_of_factorization hES _ F]
  rw [Finset.prod_pow_eq_pow_sum, ← finsum_eq_sum_of_fintype, sum_resDeg_mul_ord hES F.π hπ,
    normSym_eq, localSymbol_eq F, F.symbol_eq_base, map_pow]

end LocalRefinement

section SemiLoc

variable {D K : Type*} [CommRing D] [Field K] [Algebra D K] {B C : Subalgebra D K}

/-- For `B ≤ C` and a prime `P` of `B`, the localization `(B \ P)⁻¹ C` of `C` taken inside `K`:
the elements `x` with `s * x ∈ C` for some `s ∈ B \ P`. -/
def semiLoc (hBC : B ≤ C) (P : Ideal B) [P.IsPrime] : Subalgebra D K where
  carrier := {x | ∃ s : B, s ∉ P ∧ (s : K) * x ∈ C}
  mul_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨s', hs', hy⟩
    refine ⟨s * s', fun h ↦ (‹P.IsPrime›.mem_or_mem h).elim hs hs', ?_⟩
    convert C.mul_mem hx hy using 1
    push_cast; ring
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨s', hs', hy⟩
    refine ⟨s * s', fun h ↦ (‹P.IsPrime›.mem_or_mem h).elim hs hs', ?_⟩
    convert C.add_mem (C.mul_mem (hBC s'.2) hx) (C.mul_mem (hBC s.2) hy) using 1
    push_cast; ring
  algebraMap_mem' r := ⟨1, (Ideal.ne_top_iff_one P).1 ‹P.IsPrime›.ne_top,
    by simp⟩

variable (hBC : B ≤ C) (P : Ideal B) [P.IsPrime]

/-- Membership in `semiLoc`. -/
theorem mem_semiLoc {x : K} : x ∈ semiLoc hBC P ↔ ∃ s : B, s ∉ P ∧ (s : K) * x ∈ C := Iff.rfl

/-- `C ≤ (B \ P)⁻¹ C`. -/
theorem le_semiLoc : C ≤ semiLoc hBC P :=
  fun x hx ↦ ⟨1, (Ideal.ne_top_iff_one P).1 ‹P.IsPrime›.ne_top, by simpa using hx⟩

/-- `B_P ≤ (B \ P)⁻¹ C`. -/
theorem localizationAt_le_semiLoc : localizationAt B P ≤ semiLoc hBC P := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, hBC hx⟩

/-- `(B \ P)⁻¹ C` is an overring of `B_P` when `C` is an overring of `B`. -/
theorem isOverring_semiLoc (h : IsOverring B C) :
    IsOverring (localizationAt B P) (semiLoc h.le P) := by
  refine ⟨localizationAt_le_semiLoc h.le P, ?_⟩
  obtain ⟨G, hG⟩ := h.fg
  refine ⟨G, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro x hx
    have hxC : x ∈ (overSubalgebra h.le).toSubmodule :=
      span_eq_overSubalgebra h.le ▸ hG ▸ Submodule.subset_span hx
    exact Submodule.subset_span (le_semiLoc h.le P hxC)
  · rw [Submodule.span_le]
    rintro x ⟨s, hs, hsx⟩
    have hs0 : (s : K) ≠ 0 := fun h0 ↦ hs (by
      rw [show s = 0 from Subtype.ext h0]; exact P.zero_mem)
    have hsinv : (s : K)⁻¹ ∈ localizationAt B P := ⟨s, hs, by simp [hs0]⟩
    have h1 : (s : K) * x ∈ Submodule.span (localizationAt B P) (G : Set K) := by
      have : (s : K) * x ∈ Submodule.span B (G : Set K) := hG ▸ Submodule.subset_span hsx
      rw [← Submodule.span_span_of_tower B (localizationAt B P)]
      exact Submodule.subset_span this
    have : x = (⟨_, hsinv⟩ : localizationAt B P) • ((s : K) * x) := by
      rw [Subalgebra.smul_def, smul_eq_mul, ← mul_assoc]
      simp [hs0]
    rw [this]
    exact Submodule.smul_mem _ _ h1

end SemiLoc

section Fibre

variable {D K : Type*} [CommRing D] [Field K] [Algebra D K] {B C : Subalgebra D K}
  (h : IsOverring B C) (P : Ideal B) [P.IsMaximal]

include h in
/-- An element of `B` lies in a maximal ideal `Q'` of `(B \ P)⁻¹ C` iff it lies in `P`. -/
theorem mem_maximal_semiLoc_iff (Q' : Ideal (semiLoc h.le P)) [Q'.IsMaximal] (b : B) :
    (⟨b, le_semiLoc h.le P (h.le b.2)⟩ : semiLoc h.le P) ∈ Q' ↔ b ∈ P := by
  have hc := (isOverring_semiLoc P h).comap_eq_maximalIdeal Q'
  have key : (⟨b, le_semiLoc h.le P (h.le b.2)⟩ : semiLoc h.le P) ∈ Q' ↔
      algebraMap B (localizationAt B P) b ∈ maximalIdeal (localizationAt B P) := by
    rw [← hc]
    rfl
  rw [key]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff (localizationAt B P) P b

/-- The contraction to `C` of an ideal of `(B \ P)⁻¹ C`. -/
abbrev semiLocContract (Q' : Ideal (semiLoc h.le P)) : Ideal C :=
  Q'.comap (Subalgebra.inclusion (le_semiLoc h.le P))

/-- The contraction of a maximal ideal of `(B \ P)⁻¹ C` lies over `P`. -/
theorem comap_semiLocContract (Q' : Ideal (semiLoc h.le P)) [Q'.IsMaximal] :
    (semiLocContract h P Q').comap (Subalgebra.inclusion h.le) = P := by
  ext b
  exact mem_maximal_semiLoc_iff h P Q' b

/-- The contraction of a maximal ideal of `(B \ P)⁻¹ C` to `C` is maximal. -/
theorem isMaximal_semiLocContract (Q' : Ideal (semiLoc h.le P)) [Q'.IsMaximal] :
    (semiLocContract h P Q').IsMaximal := by
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' _ h.ringHom_isIntegral _ ?_
  change ((semiLocContract h P Q').comap (Subalgebra.inclusion h.le)).IsMaximal
  rw [comap_semiLocContract]
  infer_instance

/-- The local rings of `(B \ P)⁻¹ C` are local rings of `C`. -/
theorem localizationAt_semiLoc_eq (Q' : Ideal (semiLoc h.le P)) [Q'.IsMaximal] :
    haveI := isMaximal_semiLocContract h P Q'
    localizationAt (semiLoc h.le P) Q' = localizationAt C (semiLocContract h P Q') := by
  have := isMaximal_semiLocContract h P Q'
  have hBQ : ∀ b : B, b ∉ P →
      (⟨b, h.le b.2⟩ : C) ∉ semiLocContract h P Q' := fun b hb hbQ ↦
    hb ((mem_maximal_semiLoc_iff h P Q' b).1 hbQ)
  ext x
  constructor
  · rintro ⟨t, ht, htx⟩
    obtain ⟨b, hb, hbt⟩ := t.2
    obtain ⟨b', hb', hbtx⟩ := htx
    refine ⟨⟨(b' : K) * ((b : K) * t), C.mul_mem (h.le b'.2) hbt⟩, ?_, ?_⟩
    · intro hmem
      have hmem' : (⟨b', h.le b'.2⟩ : C) * ⟨(b : K) * t, hbt⟩ ∈ semiLocContract h P Q' := hmem
      rcases Ideal.IsPrime.mem_or_mem inferInstance hmem' with h1 | h1
      · exact hBQ b' hb' h1
      · have h2 : (⟨b, le_semiLoc h.le P (h.le b.2)⟩ : semiLoc h.le P) * t ∈ Q' := h1
        rcases Ideal.IsPrime.mem_or_mem inferInstance h2 with h3 | h3
        · exact hb ((mem_maximal_semiLoc_iff h P Q' b).1 h3)
        · exact ht h3
    · change (b' : K) * ((b : K) * t) * x ∈ C
      have := C.mul_mem (h.le b.2) hbtx
      convert this using 1
      ring
  · rintro ⟨s, hs, hsx⟩
    exact ⟨Subalgebra.inclusion (le_semiLoc h.le P) s, hs, le_semiLoc h.le P hsx⟩

/-- Two maximal ideals of `(B \ P)⁻¹ C` with the same contraction to `C` are equal. -/
theorem semiLocContract_injective (Q₁ Q₂ : Ideal (semiLoc h.le P)) [Q₁.IsMaximal]
    [Q₂.IsMaximal] (he : semiLocContract h P Q₁ = semiLocContract h P Q₂) : Q₁ = Q₂ := by
  have key : ∀ (Q : Ideal (semiLoc h.le P)) [Q.IsMaximal] (y : semiLoc h.le P),
      y ∈ Q ↔ ∃ (b : B) (hb : b ∉ P) (hy : (b : K) * y ∈ C),
        (⟨_, hy⟩ : C) ∈ semiLocContract h P Q := by
    intro Q _ y
    obtain ⟨b, hb, hby⟩ := y.2
    constructor
    · intro hyQ
      refine ⟨b, hb, hby, ?_⟩
      change (⟨b, le_semiLoc h.le P (h.le b.2)⟩ : semiLoc h.le P) * y ∈ Q
      exact Q.mul_mem_left _ hyQ
    · rintro ⟨b', hb', hy', hmem⟩
      have hmem' : (⟨b', le_semiLoc h.le P (h.le b'.2)⟩ : semiLoc h.le P) * y ∈ Q := hmem
      rcases Ideal.IsPrime.mem_or_mem inferInstance hmem' with h1 | h1
      · exact absurd ((mem_maximal_semiLoc_iff h P Q b').1 h1) hb'
      · exact h1
  ext y
  rw [key Q₁, key Q₂, he]

/-- Every maximal ideal of `C` over `P` is the contraction of a maximal ideal of
`(B \ P)⁻¹ C`. -/
theorem exists_semiLocContract_eq (Q : Ideal C) [Q.IsMaximal]
    (hQ : Q.comap (Subalgebra.inclusion h.le) = P) :
    ∃ (Q' : Ideal (semiLoc h.le P)) (_ : Q'.IsMaximal), semiLocContract h P Q' = Q := by
  have hle : semiLoc h.le P ≤ localizationAt C Q := by
    rintro x ⟨b, hb, hbx⟩
    refine ⟨⟨b, h.le b.2⟩, fun hbQ ↦ hb ?_, hbx⟩
    rw [← hQ]
    exact hbQ
  let Q' : Ideal (semiLoc h.le P) :=
    (maximalIdeal (localizationAt C Q)).comap (Subalgebra.inclusion hle)
  have hQ'C : semiLocContract h P Q' = Q := by
    have := IsLocalization.AtPrime.under_maximalIdeal (localizationAt C Q) Q
    rw [← this]
    rfl
  let J : Ideal (localizationAt B P) :=
    Q'.comap (Subalgebra.inclusion (isOverring_semiLoc P h).le)
  have hQ'B : Ideal.under B J = P := by
    refine Ideal.ext fun b ↦ Iff.trans ?_ (Ideal.ext_iff.1 hQ b)
    rw [← hQ'C]
    rfl
  have hmax : J.IsMaximal := by
    have hmap := IsLocalization.map_under P.primeCompl (localizationAt B P) J
    rw [hQ'B, IsLocalization.AtPrime.map_eq_maximalIdeal] at hmap
    rw [← hmap]
    infer_instance
  have : Q'.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' _
    (isOverring_semiLoc P h).ringHom_isIntegral Q' hmax
  exact ⟨Q', this, hQ'C⟩

end Fibre

section Refinement

variable {D K : Type*} [CommRing D] [Field K] [Algebra D K]

/-- An overring of `E` is an overring of every intermediate subalgebra. -/
theorem isOverring_of_le_of_le {E B C : Subalgebra D K} (h : IsOverring E C) (h1 : E ≤ B)
    (h2 : B ≤ C) : IsOverring B C := by
  refine ⟨h2, ?_⟩
  obtain ⟨G, hG⟩ := h.fg
  let _ : Algebra E B := (Subalgebra.inclusion h1).toAlgebra
  have : IsScalarTower E B K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨G, ?_⟩
  rw [← Submodule.span_span_of_tower E B, hG, Submodule.span_span_of_tower E B]

/-- Maximal ideals of an overring contract to maximal ideals. -/
theorem IsOverring.isMaximal_comap {B C : Subalgebra D K} (h : IsOverring B C) (Q : Ideal C)
    [Q.IsMaximal] : (Q.comap (Subalgebra.inclusion h.le)).IsMaximal :=
  Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ h.ringHom_isIntegral Q

/-- The contraction map `MaxSpec C → MaxSpec B` for an overring `C` of `B`. -/
def IsOverring.contract {B C : Subalgebra D K} (h : IsOverring B C) (Q : MaximalSpectrum C) :
    MaximalSpectrum B :=
  ⟨Q.asIdeal.comap (Subalgebra.inclusion h.le), h.isMaximal_comap Q.asIdeal⟩

variable [IsDomain D] [IsFractionRing D K] [IsLocalRing D] [IsNoetherianRing D]
  [Ring.KrullDimLE 1 D] {f g : Kˣ}

omit [IsDomain D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- **Fibre decomposition.** For `B ≤ C` overrings of `D`, the product defining `tameOf C`
regroups over the maximal ideals `P` of `B` as products over the maximal ideals of the
overrings `(B \ P)⁻¹ C` of `B_P`. -/
theorem tameOf_eq_finprod_semiLoc {B C : Subalgebra D K} (h : IsOverring B C)
    (hB : IsOverring ⊥ B) (hC : IsOverring ⊥ C) :
    tameOf D C f g = ∏ᶠ P : MaximalSpectrum B, ∏ᶠ Q : MaximalSpectrum (semiLoc h.le P.asIdeal),
      normSym (localizationAt (semiLoc h.le P.asIdeal) Q.asIdeal) f g := by
  classical
  have := hC.finite_maximalSpectrum
  have : Fintype (MaximalSpectrum C) := Fintype.ofFinite _
  have := hB.finite_maximalSpectrum
  have : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  rw [tameOf, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype,
    ← Finset.prod_fiberwise Finset.univ h.contract]
  refine Finset.prod_congr rfl fun P _ ↦ ?_
  have := (isOverring_semiLoc P.asIdeal h).finite_maximalSpectrum
  have : Fintype (MaximalSpectrum (semiLoc h.le P.asIdeal)) := Fintype.ofFinite _
  rw [finprod_eq_prod_of_fintype]
  symm
  refine Finset.prod_bij (fun Q' _ ↦ (⟨semiLocContract h P.asIdeal Q'.asIdeal,
    isMaximal_semiLocContract h P.asIdeal Q'.asIdeal⟩ : MaximalSpectrum C))
    (fun Q' _ ↦ ?_) (fun Q₁ _ Q₂ _ he ↦ ?_) (fun Q hQ ↦ ?_) (fun Q' _ ↦ ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact MaximalSpectrum.ext (comap_semiLocContract h P.asIdeal Q'.asIdeal)
  · exact MaximalSpectrum.ext (semiLocContract_injective h P.asIdeal _ _
      (congrArg MaximalSpectrum.asIdeal he))
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ
    obtain ⟨Q', hQ', hQ'e⟩ := exists_semiLocContract_eq h P.asIdeal Q.asIdeal
      (congrArg MaximalSpectrum.asIdeal hQ)
    exact ⟨⟨Q', hQ'⟩, Finset.mem_univ _, MaximalSpectrum.ext hQ'e⟩
  · exact normSym_congr (localizationAt_semiLoc_eq h P.asIdeal Q'.asIdeal) f g

/-- **T1 (refinement).** If `B` is an admissible overring of `D` for `(f, g)` and `C ⊇ B` is an
overring of `D`, then `tameOf C = tameOf B`. -/
theorem tameOf_eq_of_le {B C : Subalgebra D K} (hB : Admissible ⊥ B ![f, g])
    (hC : IsOverring ⊥ C) (hBC : B ≤ C) : tameOf D C f g = tameOf D B f g := by
  have h := isOverring_of_le_of_le hC bot_le hBC
  rw [tameOf_eq_finprod_semiLoc h hB.isOverring hC, tameOf]
  refine finprod_congr fun P ↦ ?_
  have := hB.isOverring.isNoetherianRing
  have := hB.isOverring.krullDimLE
  have := isLocalHom_inclusion_localizationAt hB.isOverring P.asIdeal
  have := isLocalHom_algebraMap_of_le (hB.isOverring.le.trans (le_localizationAt B P.asIdeal))
  obtain ⟨F⟩ := (hB.factors P.asIdeal).nonempty_pairFactorization
  exact finprod_normSym_localizationAt (isOverring_semiLoc P.asIdeal h) F

/-- **T2 (independence of the admissible overring).** Any two admissible overrings of `D` for
`(f, g)` give the same value of `tameOf`. -/
theorem tameOf_eq_of_admissible {B B' : Subalgebra D K} (hB : Admissible ⊥ B ![f, g])
    (hB' : Admissible ⊥ B' ![f, g]) : tameOf D B f g = tameOf D B' f g := by
  have hs := hB.isOverring.sup hB'.isOverring
  rw [← tameOf_eq_of_le hB hs le_sup_left, ← tameOf_eq_of_le hB' hs le_sup_right]

end Refinement

section Bimultiplicative

variable {D K : Type*} [CommRing D] [Field K] [Algebra D K] [IsFractionRing D K]

private theorem symbol_mul_aux {G : Type*} [CommGroup G] [HasDistribNeg G] (U U' V : G)
    (a a' b : ℤ) (m : ℕ) :
    ((-1) ^ ((a + a') * b) * (U * U') ^ b * V ^ (-(a + a'))) ^ m =
      ((-1) ^ (a * b) * U ^ b * V ^ (-a)) ^ m * ((-1) ^ (a' * b) * U' ^ b * V ^ (-a')) ^ m := by
  rw [← mul_pow]
  congr 1
  rw [add_mul, zpow_add, mul_zpow, neg_add, zpow_add]
  simp only [mul_comm, mul_assoc, mul_left_comm]

private theorem symbol_mul_aux' {G : Type*} [CommGroup G] [HasDistribNeg G] (U V V' : G)
    (a b b' : ℤ) (m : ℕ) :
    ((-1) ^ (a * (b + b')) * U ^ (b + b') * (V * V') ^ (-a)) ^ m =
      ((-1) ^ (a * b) * U ^ b * V ^ (-a)) ^ m * ((-1) ^ (a * b') * U ^ b' * V' ^ (-a)) ^ m := by
  rw [← mul_pow]
  congr 1
  rw [mul_add, zpow_add, zpow_add, mul_zpow]
  simp only [mul_comm, mul_assoc, mul_left_comm]

variable {S : Subalgebra D K} [IsLocalRing S] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]

/-- The local symbol is multiplicative in the first argument, for a triple with a common
factorization. -/
theorem localSymbol_mul_left {f f' g : Kˣ} (h : Factors S ![f, f', g]) :
    localSymbol S (f * f') g = localSymbol S f g * localSymbol S f' g := by
  obtain ⟨π, e, u, hπ, hu⟩ := h
  have h0 : (f : K) = ((u 0 : S) : K) * (π : K) ^ e 0 := hu 0
  have h1 : (f' : K) = ((u 1 : S) : K) * (π : K) ^ e 1 := hu 1
  have h2 : (g : K) = ((u 2 : S) : K) * (π : K) ^ e 2 := hu 2
  let F₁ : PairFactorization S f g := ⟨π, e 0, e 2, u 0, u 2, hπ, h0, h2⟩
  let F₂ : PairFactorization S f' g := ⟨π, e 1, e 2, u 1, u 2, hπ, h1, h2⟩
  let F₃ : PairFactorization S (f * f') g := ⟨π, e 0 + e 1, e 2, u 0 * u 1, u 2, hπ,
    by
      change ((f * f' : Kˣ) : K) = ((u 0 * u 1 : S) : K) * (π : K) ^ (e 0 + e 1)
      rw [Units.val_mul, h0, h1, zpow_add₀ hπ]; push_cast; ring, h2⟩
  rw [localSymbol_eq F₁, localSymbol_eq F₂, localSymbol_eq F₃]
  simp only [PairFactorization.symbol, F₁, F₂, F₃, map_mul]
  exact symbol_mul_aux _ _ _ _ _ _ _

/-- The local symbol is multiplicative in the second argument, for a triple with a common
factorization. -/
theorem localSymbol_mul_right {f g g' : Kˣ} (h : Factors S ![f, g, g']) :
    localSymbol S f (g * g') = localSymbol S f g * localSymbol S f g' := by
  obtain ⟨π, e, u, hπ, hu⟩ := h
  have h0 : (f : K) = ((u 0 : S) : K) * (π : K) ^ e 0 := hu 0
  have h1 : (g : K) = ((u 1 : S) : K) * (π : K) ^ e 1 := hu 1
  have h2 : (g' : K) = ((u 2 : S) : K) * (π : K) ^ e 2 := hu 2
  let F₁ : PairFactorization S f g := ⟨π, e 0, e 1, u 0, u 1, hπ, h0, h1⟩
  let F₂ : PairFactorization S f g' := ⟨π, e 0, e 2, u 0, u 2, hπ, h0, h2⟩
  let F₃ : PairFactorization S f (g * g') := ⟨π, e 0, e 1 + e 2, u 0, u 1 * u 2, hπ, h0,
    by
      change ((g * g' : Kˣ) : K) = ((u 1 * u 2 : S) : K) * (π : K) ^ (e 1 + e 2)
      rw [Units.val_mul, h1, h2, zpow_add₀ hπ]; push_cast; ring⟩
  rw [localSymbol_eq F₁, localSymbol_eq F₂, localSymbol_eq F₃]
  simp only [PairFactorization.symbol, F₁, F₂, F₃, map_mul]
  exact symbol_mul_aux' _ _ _ _ _ _ _

end Bimultiplicative

section UnitSymbol

variable {R K : Type*} [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
  [Ring.KrullDimLE 1 R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- `λ_R(u, g) = ū^(ordZ g)` for a unit `u` of `R`, whenever `(u, g)` factors in `R`. -/
theorem localSymbol_units_left (u : Rˣ) {g : Kˣ}
    (F : PairFactorization R (Units.map (algebraMap R K : R →* K) u) g) :
    localSymbol R (Units.map (algebraMap R K : R →* K) u) g = resUnits R u ^ ordZ R g := by
  rw [localSymbol_eq_of_unit F (u ^ ordZ R g) (by simp [ordZ_units_map]), ordZ_units_map,
    zero_mul, zpow_zero, one_mul, map_zpow]

/-- `λ_R(g, u) = ū^(-ordZ g)` for a unit `u` of `R`, whenever `(g, u)` factors in `R`. -/
theorem localSymbol_units_right (u : Rˣ) {g : Kˣ}
    (F : PairFactorization R g (Units.map (algebraMap R K : R →* K) u)) :
    localSymbol R g (Units.map (algebraMap R K : R →* K) u) = resUnits R u ^ (-ordZ R g) := by
  rw [localSymbol_eq_of_unit F (u ^ (-ordZ R g)) (by simp [ordZ_units_map]), ordZ_units_map,
    mul_zero, zpow_zero, one_mul, map_zpow]

end UnitSymbol

/-- `a ^ (Σ n) = Π a ^ n` in a commutative group. -/
theorem zpow_sum_tame {G ι : Type*} [CommGroup G] (a : G) (s : Finset ι) (n : ι → ℤ) :
    ∏ k ∈ s, a ^ n k = a ^ (∑ k ∈ s, n k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, zpow_add, ih]

section TameOfProperties

variable {D K : Type*} [CommRing D] [Field K] [Algebra D K] [IsFractionRing D K]
  [IsLocalRing D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D]

omit [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- For an overring `C` of `D` and a maximal ideal `P` of `C`, `D → C_P` is local. -/
theorem isLocalHom_algebraMap_localizationAt {C : Subalgebra D K} (hC : IsOverring ⊥ C)
    (P : Ideal C) [P.IsMaximal] : IsLocalHom (algebraMap D (localizationAt C P)) := by
  have := isLocalHom_inclusion_localizationAt hC P
  exact isLocalHom_algebraMap_of_le (hC.le.trans (le_localizationAt C P))

omit [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- The residue degree over `⊥` is the residue degree over `D`. -/
theorem resDeg_bot_eq (L : Subalgebra D K) [IsLocalRing L] [IsLocalHom (algebraMap D L)] :
    resDeg D (bot_le : ⊥ ≤ L) = Module.finrank (ResidueField D) (ResidueField L) := by
  let _ : Algebra (⊥ : Subalgebra D K) L := (Subalgebra.inclusion (bot_le : ⊥ ≤ L)).toAlgebra
  have hcomp : ∀ d : D, algebraMap (⊥ : Subalgebra D K) L (botRingEquiv D K d) =
      algebraMap D L d := fun d ↦ Subtype.ext (coe_botRingEquiv d)
  have : IsLocalHom (algebraMap (⊥ : Subalgebra D K) L) := by
    refine ⟨fun b hb ↦ ?_⟩
    obtain ⟨d, rfl⟩ := (botRingEquiv D K).surjective b
    rw [hcomp] at hb
    exact (IsLocalHom.map_nonunit d hb).map _
  rw [resDeg_eq bot_le (fun _ ↦ rfl)]
  refine (Algebra.finrank_eq_of_equiv_equiv (ResidueField.mapEquiv (botRingEquiv D K))
    (RingEquiv.refl _) ?_).symm
  ext x
  obtain ⟨d, rfl⟩ := residue_surjective x
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
    Function.comp_apply, ResidueField.mapEquiv_apply, ResidueField.map_residue,
    ResidueField.algebraMap_residue, RingEquiv.coe_ringHom_refl, RingHom.id_apply]
  exact congrArg (residue L) (hcomp d)

omit [IsLocalRing D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- `Ring.ord` on `⊥` agrees with `Ring.ord` on `D`, for elements of `D`. -/
theorem ord_botRingEquiv_toNat (x : D) :
    ((Ring.ord (⊥ : Subalgebra D K) (botRingEquiv D K x)).toNat : ℤ) =
      ((Ring.ord D x).toNat : ℤ) := by
  rw [GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalOrdSymmetry.ord_ringEquiv]

/-- **Fulton A.3.1 for `ordZ`.** For an overring `C` of `D` and `g ∈ Kˣ`,
`Σ_P [κ(C_P) : κ(D)] · ordZ_{C_P}(g) = ordZ_D(g)`. -/
theorem sum_resDeg_mul_ordZ [IsDomain D] {C : Subalgebra D K} (hC : IsOverring ⊥ C)
    [IsNoetherianRing C] [Ring.KrullDimLE 1 C] (g : Kˣ) :
    ∑ᶠ P : MaximalSpectrum C, (resDeg D (bot_le : ⊥ ≤ localizationAt C P.asIdeal) : ℤ) *
      ordZ (localizationAt C P.asIdeal) g = ordZ D g := by
  classical
  have := hC.finite_maximalSpectrum
  have : Fintype (MaximalSpectrum C) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  -- the elementwise statement
  have key : ∀ (x : D) (hx : algebraMap D K x ≠ 0),
      ∑ P : MaximalSpectrum C, (resDeg D (bot_le : ⊥ ≤ localizationAt C P.asIdeal) : ℤ) *
        ordZ (localizationAt C P.asIdeal) (Units.mk0 _ hx) = ordZ D (K := K) (Units.mk0 _ hx) := by
    intro x hx
    have hx0 : botRingEquiv D K x ≠ 0 := fun h ↦ hx (by
      rw [← coe_botRingEquiv, h]; rfl)
    have hs := sum_resDeg_mul_ord hC (botRingEquiv D K x) hx0
    rw [finsum_eq_sum_of_fintype] at hs
    rw [ordZ_mk0 (K := K), ← ord_botRingEquiv_toNat (K := K) x, ← hs, Nat.cast_sum]
    refine Finset.sum_congr rfl fun P _ ↦ ?_
    have e : Subalgebra.inclusion (hC.le.trans (le_localizationAt C P.asIdeal))
        (botRingEquiv D K x) = algebraMap D (localizationAt C P.asIdeal) x :=
      Subtype.ext (coe_botRingEquiv x)
    rw [e, Nat.cast_mul, ← ordZ_mk0 (R := localizationAt C P.asIdeal) (K := K)]
    rfl
  obtain ⟨x, y, hy, hg⟩ := IsFractionRing.div_surjective (A := D) (g : K)
  have hy0 : algebraMap D K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hx0 : algebraMap D K x ≠ 0 := fun h ↦ g.ne_zero (by rw [← hg, h, zero_div])
  have hg' : g = Units.mk0 _ hx0 * (Units.mk0 _ hy0)⁻¹ := Units.ext (by simp [← hg, div_eq_mul_inv])
  rw [hg']
  simp only [ordZ_mul, ordZ_inv, mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    key]

omit [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- The normed local symbol `normSym E (u, g)` for a unit `u` of `D`. -/
theorem normSym_units_left (E : Subalgebra D K) [IsLocalRing E] [IsNoetherianRing E]
    [Ring.KrullDimLE 1 E] [IsLocalHom (algebraMap D E)] (u : Dˣ) {g : Kˣ}
    (h : Nonempty (PairFactorization E (Units.map (algebraMap D K : D →* K) u) g)) :
    normSym E (Units.map (algebraMap D K : D →* K) u) g =
      resUnits D u ^ ((resDeg D (bot_le : ⊥ ≤ E) : ℤ) * ordZ E g) := by
  have e : Units.map (algebraMap D K : D →* K) u =
      Units.map (algebraMap E K : E →* K) (Units.map (algebraMap D E : D →* E) u) :=
    Units.ext rfl
  obtain ⟨F⟩ := h
  rw [e] at F ⊢
  rw [normSym_eq, localSymbol_units_left _ F, resDeg_bot_eq, zpow_mul, map_zpow]
  congr 1
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [← ResidueField.algebraMap_residue, Algebra.norm_algebraMap]
  rfl

omit [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- The normed local symbol `normSym E (g, u)` for a unit `u` of `D`. -/
theorem normSym_units_right (E : Subalgebra D K) [IsLocalRing E] [IsNoetherianRing E]
    [Ring.KrullDimLE 1 E] [IsLocalHom (algebraMap D E)] (u : Dˣ) {g : Kˣ}
    (h : Nonempty (PairFactorization E g (Units.map (algebraMap D K : D →* K) u))) :
    normSym E g (Units.map (algebraMap D K : D →* K) u) =
      resUnits D u ^ (-((resDeg D (bot_le : ⊥ ≤ E) : ℤ) * ordZ E g)) := by
  have e : Units.map (algebraMap D K : D →* K) u =
      Units.map (algebraMap E K : E →* K) (Units.map (algebraMap D E : D →* E) u) :=
    Units.ext rfl
  obtain ⟨F⟩ := h
  rw [e] at F ⊢
  rw [normSym_eq, localSymbol_units_right _ F, resDeg_bot_eq, ← mul_neg, zpow_mul, map_zpow]
  congr 1
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [← ResidueField.algebraMap_residue, Algebra.norm_algebraMap]
  rfl

variable {f f' g g' : Kˣ}

/-- Bimultiplicativity of `tameOf` in the first argument, on an overring admissible for
`(f, f', g)`. -/
theorem tameOf_mul_left {C : Subalgebra D K} (hC : Admissible ⊥ C ![f, f', g]) :
    tameOf D C (f * f') g = tameOf D C f g * tameOf D C f' g := by
  classical
  have := hC.isOverring.finite_maximalSpectrum
  have : Fintype (MaximalSpectrum C) := Fintype.ofFinite _
  have := hC.isOverring.isNoetherianRing
  have := hC.isOverring.krullDimLE
  simp only [tameOf, finprod_eq_prod_of_fintype, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun P _ ↦ ?_
  have := isLocalHom_algebraMap_localizationAt hC.isOverring P.asIdeal
  rw [normSym_eq, normSym_eq, normSym_eq, localSymbol_mul_left (hC.factors P.asIdeal), map_mul]

/-- Bimultiplicativity of `tameOf` in the second argument, on an overring admissible for
`(f, g, g')`. -/
theorem tameOf_mul_right {C : Subalgebra D K} (hC : Admissible ⊥ C ![f, g, g']) :
    tameOf D C f (g * g') = tameOf D C f g * tameOf D C f g' := by
  classical
  have := hC.isOverring.finite_maximalSpectrum
  have : Fintype (MaximalSpectrum C) := Fintype.ofFinite _
  have := hC.isOverring.isNoetherianRing
  have := hC.isOverring.krullDimLE
  simp only [tameOf, finprod_eq_prod_of_fintype, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun P _ ↦ ?_
  have := isLocalHom_algebraMap_localizationAt hC.isOverring P.asIdeal
  rw [normSym_eq, normSym_eq, normSym_eq, localSymbol_mul_right (hC.factors P.asIdeal), map_mul]

/-- Normalization of `tameOf` on an admissible overring, unit in the first argument. -/
theorem tameOf_units_left [IsDomain D] {C : Subalgebra D K} (u : Dˣ)
    (hC : Admissible ⊥ C ![Units.map (algebraMap D K : D →* K) u, g]) :
    tameOf D C (Units.map (algebraMap D K : D →* K) u) g = resUnits D u ^ ordZ D g := by
  classical
  have := hC.isOverring.finite_maximalSpectrum
  have : Fintype (MaximalSpectrum C) := Fintype.ofFinite _
  have := hC.isOverring.isNoetherianRing
  have := hC.isOverring.krullDimLE
  rw [← sum_resDeg_mul_ordZ hC.isOverring g, finsum_eq_sum_of_fintype, ← zpow_sum_tame,
    tameOf, finprod_eq_prod_of_fintype]
  refine Finset.prod_congr rfl fun P _ ↦ ?_
  have := isLocalHom_algebraMap_localizationAt hC.isOverring P.asIdeal
  exact normSym_units_left _ u (hC.factors P.asIdeal).nonempty_pairFactorization

/-- Normalization of `tameOf` on an admissible overring, unit in the second argument. -/
theorem tameOf_units_right [IsDomain D] {C : Subalgebra D K} (u : Dˣ)
    (hC : Admissible ⊥ C ![g, Units.map (algebraMap D K : D →* K) u]) :
    tameOf D C g (Units.map (algebraMap D K : D →* K) u) = resUnits D u ^ (-ordZ D g) := by
  classical
  have := hC.isOverring.finite_maximalSpectrum
  have : Fintype (MaximalSpectrum C) := Fintype.ofFinite _
  have := hC.isOverring.isNoetherianRing
  have := hC.isOverring.krullDimLE
  rw [← sum_resDeg_mul_ordZ hC.isOverring g, finsum_eq_sum_of_fintype, ← Finset.sum_neg_distrib,
    ← zpow_sum_tame, tameOf, finprod_eq_prod_of_fintype]
  refine Finset.prod_congr rfl fun P _ ↦ ?_
  have := isLocalHom_algebraMap_localizationAt hC.isOverring P.asIdeal
  exact normSym_units_right _ u (hC.factors P.asIdeal).nonempty_pairFactorization

end TameOfProperties

section FactorsPairs

variable {D K : Type*} [CommRing D] [Field K] [Algebra D K] {S : Subalgebra D K}
  {f f' g g' : Kˣ}

/-- From a common factorization of `(f, f', g)`, factorizations of `(f, g)`, `(f', g)` and
`(f f', g)`. -/
theorem Factors.pairs_of_triple_left (h : Factors S ![f, f', g]) :
    Factors S ![f, g] ∧ Factors S ![f', g] ∧ Factors S ![f * f', g] := by
  obtain ⟨π, e, u, hπ, hu⟩ := h
  have h0 : (f : K) = ((u 0 : S) : K) * (π : K) ^ e 0 := hu 0
  have h1 : (f' : K) = ((u 1 : S) : K) * (π : K) ^ e 1 := hu 1
  have h2 : (g : K) = ((u 2 : S) : K) * (π : K) ^ e 2 := hu 2
  refine ⟨(⟨π, e 0, e 2, u 0, u 2, hπ, h0, h2⟩ : PairFactorization S f g).factors,
    (⟨π, e 1, e 2, u 1, u 2, hπ, h1, h2⟩ : PairFactorization S f' g).factors,
    (⟨π, e 0 + e 1, e 2, u 0 * u 1, u 2, hπ, ?_, h2⟩ : PairFactorization S (f * f') g).factors⟩
  change ((f * f' : Kˣ) : K) = ((u 0 * u 1 : S) : K) * (π : K) ^ (e 0 + e 1)
  rw [Units.val_mul, h0, h1, zpow_add₀ hπ]
  push_cast
  ring

/-- From a common factorization of `(f, g, g')`, factorizations of `(f, g)`, `(f, g')` and
`(f, g g')`. -/
theorem Factors.pairs_of_triple_right (h : Factors S ![f, g, g']) :
    Factors S ![f, g] ∧ Factors S ![f, g'] ∧ Factors S ![f, g * g'] := by
  obtain ⟨π, e, u, hπ, hu⟩ := h
  have h0 : (f : K) = ((u 0 : S) : K) * (π : K) ^ e 0 := hu 0
  have h1 : (g : K) = ((u 1 : S) : K) * (π : K) ^ e 1 := hu 1
  have h2 : (g' : K) = ((u 2 : S) : K) * (π : K) ^ e 2 := hu 2
  refine ⟨(⟨π, e 0, e 1, u 0, u 1, hπ, h0, h1⟩ : PairFactorization S f g).factors,
    (⟨π, e 0, e 2, u 0, u 2, hπ, h0, h2⟩ : PairFactorization S f g').factors,
    (⟨π, e 0, e 1 + e 2, u 0, u 1 * u 2, hπ, h0, ?_⟩ : PairFactorization S f (g * g')).factors⟩
  change ((g * g' : Kˣ) : K) = ((u 1 * u 2 : S) : K) * (π : K) ^ (e 1 + e 2)
  rw [Units.val_mul, h1, h2, zpow_add₀ hπ]
  push_cast
  ring

variable {E C : Subalgebra D K}

/-- An overring admissible for `(f, f', g)` is admissible for `(f, g)`, `(f', g)`, `(f f', g)`. -/
theorem Admissible.pairs_of_triple_left (h : Admissible E C ![f, f', g]) :
    Admissible E C ![f, g] ∧ Admissible E C ![f', g] ∧ Admissible E C ![f * f', g] :=
  ⟨⟨h.isOverring, fun P _ ↦ (h.factors P).pairs_of_triple_left.1⟩,
    ⟨h.isOverring, fun P _ ↦ (h.factors P).pairs_of_triple_left.2.1⟩,
    ⟨h.isOverring, fun P _ ↦ (h.factors P).pairs_of_triple_left.2.2⟩⟩

/-- An overring admissible for `(f, g, g')` is admissible for `(f, g)`, `(f, g')`, `(f, g g')`. -/
theorem Admissible.pairs_of_triple_right (h : Admissible E C ![f, g, g']) :
    Admissible E C ![f, g] ∧ Admissible E C ![f, g'] ∧ Admissible E C ![f, g * g'] :=
  ⟨⟨h.isOverring, fun P _ ↦ (h.factors P).pairs_of_triple_right.1⟩,
    ⟨h.isOverring, fun P _ ↦ (h.factors P).pairs_of_triple_right.2.1⟩,
    ⟨h.isOverring, fun P _ ↦ (h.factors P).pairs_of_triple_right.2.2⟩⟩

end FactorsPairs

section TameSymbol

open GromovWitten.AlgebraicGeometry.IntersectionTheory.VectorBundle (UnitDifferences)

/-- Unit differences transport along injective ring homomorphisms (universe-polymorphic). -/
theorem unitDifferences_of_injective_tame {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (h : UnitDifferences R) : UnitDifferences S := by
  obtain ⟨Λ, hinf, hunit⟩ := h
  refine ⟨φ '' Λ, hinf.image hφ.injOn, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
  rw [← map_sub]
  exact (hunit x hx y hy fun hxy ↦ hne (by rw [hxy])).map φ

variable {D K : Type*} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
  [Ring.KrullDimLE 1 D] [Field K] [Algebra D K] [IsFractionRing D K]

omit [IsDomain D] [IsLocalRing D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- `⊥ ≅ D` inherits unit differences from `D`. -/
theorem unitDifferences_bot (hU : UnitDifferences D) : UnitDifferences (⊥ : Subalgebra D K) :=
  unitDifferences_of_injective_tame (botRingEquiv D K : D →+* _) (botRingEquiv D K).injective hU

variable (D K) in
/-- **The tame symbol** `∂_D(f, g) ∈ κ(D)ˣ` of two units of the fraction field `K` of a
Noetherian local domain `D` of dimension `≤ 1` with unit differences (Stacks 42.5): the value
`tameOf D C f g` on the admissible overring `C` for `(f, g)` supplied by `exists_admissible`.
By `tameSymbol_eq_tameOf` it may be computed on any admissible overring. -/
noncomputable def tameSymbol (hU : UnitDifferences D) (f g : Kˣ) : (ResidueField D)ˣ :=
  tameOf D (exists_admissible (⊥ : Subalgebra D K) (unitDifferences_bot hU) ![f, g]).choose f g

variable (hU : UnitDifferences D) {f f' g g' : Kˣ}

/-- **T2.** The tame symbol can be computed on any admissible overring. -/
theorem tameSymbol_eq_tameOf {C : Subalgebra D K} (hC : Admissible ⊥ C ![f, g]) :
    tameSymbol D K hU f g = tameOf D C f g :=
  tameOf_eq_of_admissible
    (exists_admissible (⊥ : Subalgebra D K) (unitDifferences_bot hU) ![f, g]).choose_spec hC

/-- **T3.** The tame symbol is multiplicative in the first argument. -/
theorem tameSymbol_mul_left (f f' g : Kˣ) :
    tameSymbol D K hU (f * f') g = tameSymbol D K hU f g * tameSymbol D K hU f' g := by
  obtain ⟨C, hC⟩ := exists_admissible (⊥ : Subalgebra D K) (unitDifferences_bot hU) ![f, f', g]
  obtain ⟨h1, h2, h3⟩ := hC.pairs_of_triple_left
  rw [tameSymbol_eq_tameOf hU h1, tameSymbol_eq_tameOf hU h2, tameSymbol_eq_tameOf hU h3,
    tameOf_mul_left hC]

/-- **T3.** The tame symbol is multiplicative in the second argument. -/
theorem tameSymbol_mul_right (f g g' : Kˣ) :
    tameSymbol D K hU f (g * g') = tameSymbol D K hU f g * tameSymbol D K hU f g' := by
  obtain ⟨C, hC⟩ := exists_admissible (⊥ : Subalgebra D K) (unitDifferences_bot hU) ![f, g, g']
  obtain ⟨h1, h2, h3⟩ := hC.pairs_of_triple_right
  rw [tameSymbol_eq_tameOf hU h1, tameSymbol_eq_tameOf hU h2, tameSymbol_eq_tameOf hU h3,
    tameOf_mul_right hC]

/-- `∂_D(1, g) = 1`. -/
@[simp]
theorem tameSymbol_one_left (g : Kˣ) : tameSymbol D K hU 1 g = 1 := by
  have := tameSymbol_mul_left hU 1 1 g
  rw [mul_one] at this
  exact left_eq_mul.1 this

/-- `∂_D(f, 1) = 1`. -/
@[simp]
theorem tameSymbol_one_right (f : Kˣ) : tameSymbol D K hU f 1 = 1 := by
  have := tameSymbol_mul_right hU f 1 1
  rw [mul_one] at this
  exact left_eq_mul.1 this

/-- `∂_D(f⁻¹, g) = ∂_D(f, g)⁻¹`. -/
theorem tameSymbol_inv_left (f g : Kˣ) :
    tameSymbol D K hU f⁻¹ g = (tameSymbol D K hU f g)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← tameSymbol_mul_left, inv_mul_cancel, tameSymbol_one_left]

/-- `∂_D(f, g⁻¹) = ∂_D(f, g)⁻¹`. -/
theorem tameSymbol_inv_right (f g : Kˣ) :
    tameSymbol D K hU f g⁻¹ = (tameSymbol D K hU f g)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← tameSymbol_mul_right, inv_mul_cancel, tameSymbol_one_right]

/-- **T4 (normalization).** For a unit `u` of `D`,
`∂_D(u, g) = ū ^ ordZ_D(g)`, where `ordZ_D` is the integer-valued `Ring.ordFrac D`. -/
theorem tameSymbol_units_left (u : Dˣ) (g : Kˣ) :
    tameSymbol D K hU (Units.map (algebraMap D K : D →* K) u) g = resUnits D u ^ ordZ D g := by
  obtain ⟨C, hC⟩ := exists_admissible (⊥ : Subalgebra D K) (unitDifferences_bot hU)
    ![Units.map (algebraMap D K : D →* K) u, g]
  rw [tameSymbol_eq_tameOf hU hC, tameOf_units_left u hC]

/-- **T4 (normalization).** For a unit `u` of `D`, `∂_D(g, u) = ū ^ (-ordZ_D(g))`. -/
theorem tameSymbol_units_right (u : Dˣ) (g : Kˣ) :
    tameSymbol D K hU g (Units.map (algebraMap D K : D →* K) u) =
      resUnits D u ^ (-ordZ D g) := by
  obtain ⟨C, hC⟩ := exists_admissible (⊥ : Subalgebra D K) (unitDifferences_bot hU)
    ![g, Units.map (algebraMap D K : D →* K) u]
  rw [tameSymbol_eq_tameOf hU hC, tameOf_units_right u hC]

/-- **T4.** The tame symbol of two units of `D` is trivial. -/
theorem tameSymbol_units_units (u v : Dˣ) :
    tameSymbol D K hU (Units.map (algebraMap D K : D →* K) u)
      (Units.map (algebraMap D K : D →* K) v) = 1 := by
  rw [tameSymbol_units_left, ordZ_units_map, zpow_zero]

end TameSymbol

section CarrierTransport

variable {R₁ R₂ K K' : Type*} [CommRing R₁] [CommRing R₂] [Field K] [Field K'] [Algebra R₁ K]
  [Algebra R₂ K'] (σ : K ≃+* K') {A : Subalgebra R₁ K} {A' : Subalgebra R₂ K'}
  (h : ∀ x, x ∈ A ↔ σ x ∈ A')

/-- The ring isomorphism between subalgebras `A ⊆ K`, `A' ⊆ K'` (over possibly different base
rings) induced by a field isomorphism `σ : K ≃+* K'` mapping `A` onto `A'`. -/
def subEquiv : A ≃+* A' where
  toFun x := ⟨σ x, (h x).1 x.2⟩
  invFun y := ⟨σ.symm y, (h _).2 (by simp)⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv y := Subtype.ext (σ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul σ (x : K) y)
  map_add' x y := Subtype.ext (map_add σ (x : K) y)

/-- `subEquiv σ h` acts as `σ` on elements. -/
@[simp]
theorem coe_subEquiv (x : A) : ((subEquiv σ h x : A') : K') = σ x := rfl

/-- The inverse of `subEquiv σ h` acts as `σ⁻¹` on elements. -/
@[simp]
theorem coe_subEquiv_symm (y : A') : (((subEquiv σ h).symm y : A) : K) = σ.symm y := rfl

/-- `σ` maps the localization `A_Q` onto the localization of `A'` at the transported ideal. -/
theorem mem_localizationAt_subEquiv_iff (Q : Ideal A) [Q.IsPrime] (x : K) :
    x ∈ localizationAt A Q ↔ σ x ∈ localizationAt A' (Q.comap (subEquiv σ h).symm) := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    refine ⟨subEquiv σ h s, by simpa using hs, ?_⟩
    rw [coe_subEquiv, ← map_mul]
    exact (h _).1 hsx
  · rintro ⟨s', hs', hsx⟩
    refine ⟨(subEquiv σ h).symm s', hs', (h _).2 ?_⟩
    rw [map_mul, coe_subEquiv_symm, σ.apply_symm_apply]
    exact hsx

/-- The induced isomorphism of local rings. -/
def locEquiv (Q : Ideal A) [Q.IsPrime] :
    localizationAt A Q ≃+* localizationAt A' (Q.comap (subEquiv σ h).symm) :=
  subEquiv σ (mem_localizationAt_subEquiv_iff σ h Q)

/-- `locEquiv σ h Q` acts as `σ` on elements. -/
@[simp]
theorem coe_locEquiv (Q : Ideal A) [Q.IsPrime] (x : localizationAt A Q) :
    ((locEquiv σ h Q x : localizationAt A' (Q.comap (subEquiv σ h).symm)) : K') = σ x := rfl

/-- The induced bijection of maximal spectra. -/
def maxSpecEquiv : MaximalSpectrum A ≃ MaximalSpectrum A' where
  toFun Q := ⟨Q.asIdeal.comap (subEquiv σ h).symm,
    Ideal.comap_isMaximal_of_surjective _ (subEquiv σ h).symm.surjective⟩
  invFun Q' := ⟨Q'.asIdeal.comap (subEquiv σ h),
    Ideal.comap_isMaximal_of_surjective _ (subEquiv σ h).surjective⟩
  left_inv Q := MaximalSpectrum.ext (by
    ext x
    change (subEquiv σ h).symm (subEquiv σ h x) ∈ Q.asIdeal ↔ _
    rw [RingEquiv.symm_apply_apply])
  right_inv Q' := MaximalSpectrum.ext (by
    ext x
    change (subEquiv σ h) ((subEquiv σ h).symm x) ∈ Q'.asIdeal ↔ _
    rw [RingEquiv.apply_symm_apply])

/-- The ideal underlying `maxSpecEquiv σ h Q`. -/
theorem maxSpecEquiv_asIdeal (Q : MaximalSpectrum A) :
    (maxSpecEquiv σ h Q).asIdeal = Q.asIdeal.comap (subEquiv σ h).symm := rfl

include h in
/-- Factorizations transport along `σ`. -/
theorem Factors.transport {ι : Type*} {f : ι → Kˣ} (hf : Factors A f) :
    Factors A' (fun i ↦ Units.map (σ : K →* K') (f i)) := by
  obtain ⟨π, e, u, hπ, hu⟩ := hf
  refine ⟨subEquiv σ h π, e, fun i ↦ Units.map (subEquiv σ h : A →* A') (u i), ?_, fun i ↦ ?_⟩
  · rw [coe_subEquiv]
    exact (map_ne_zero σ).2 hπ
  · simp [hu i]

end CarrierTransport

section Relative

variable {D K : Type*} [CommRing D] [Field K] [Algebra D K] [IsFractionRing D K]
  [IsLocalRing D]

omit [IsFractionRing D K] [IsLocalRing D] in
/-- Over any base, `IsOverring ⊥ C` means that the base-span of `C` is finitely generated. -/
theorem isOverring_bot_iff_span {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    {C : Subalgebra R L} : IsOverring ⊥ C ↔ (Submodule.span R (C : Set L)).FG := by
  have hs : Function.Surjective (algebraMap R (⊥ : Subalgebra R L)) := by
    rintro ⟨x, hx⟩
    obtain ⟨d, rfl⟩ := Algebra.mem_bot.1 hx
    exact ⟨d, rfl⟩
  constructor
  · rintro ⟨-, G, hG⟩
    refine ⟨G, ?_⟩
    rw [← Submodule.restrictScalars_span R _ hs, hG, Submodule.restrictScalars_span R _ hs]
  · rintro ⟨G, hG⟩
    refine ⟨bot_le, G, Submodule.restrictScalars_injective R _ _ ?_⟩
    rw [Submodule.restrictScalars_span R _ hs, hG, Submodule.restrictScalars_span R _ hs]

variable {E S : Subalgebra D K} {f g : Kˣ}

omit [IsFractionRing D K] [IsLocalRing D] in
/-- An overring `S` of `E`, viewed as a subalgebra over `E`, is an overring of `E`. -/
theorem isOverring_overSubalgebra (hS : IsOverring E S) :
    IsOverring (⊥ : Subalgebra E K) (overSubalgebra hS.le) :=
  isOverring_bot_iff_span.2 hS.fg

omit [IsFractionRing D K] [IsLocalRing D] in
/-- Admissibility over `E` transfers to admissibility over `⊥ : Subalgebra E K`. -/
theorem admissible_overSubalgebra (hS : Admissible E S ![f, g]) :
    Admissible (⊥ : Subalgebra E K) (overSubalgebra hS.isOverring.le) ![f, g] := by
  refine ⟨isOverring_overSubalgebra hS.isOverring, fun Q' _ ↦ ?_⟩
  let h : ∀ x, x ∈ S ↔ (RingEquiv.refl K) x ∈ overSubalgebra hS.isOverring.le :=
    fun _ ↦ Iff.rfl
  let Q : MaximalSpectrum S := (maxSpecEquiv (RingEquiv.refl K) h).symm ⟨Q', ‹_›⟩
  have hQ : maxSpecEquiv (RingEquiv.refl K) h Q = ⟨Q', ‹_›⟩ := Equiv.apply_symm_apply _ _
  have := (hS.factors Q.asIdeal).transport (RingEquiv.refl K)
    (mem_localizationAt_subEquiv_iff (RingEquiv.refl K) h Q.asIdeal)
  have e1 : (fun i ↦ Units.map ((RingEquiv.refl K : K ≃+* K) : K →* K) (![f, g] i)) = ![f, g] :=
    funext fun i ↦ Units.ext rfl
  rw [e1] at this
  have e2 : Q.asIdeal.comap (subEquiv (RingEquiv.refl K) h).symm = Q' :=
    congrArg MaximalSpectrum.asIdeal hQ
  convert this using 2
  rw [e2]

variable [IsLocalRing E] [IsNoetherianRing E] [Ring.KrullDimLE 1 E]
  [IsLocalHom (algebraMap D E)]

omit [IsNoetherianRing E] [Ring.KrullDimLE 1 E] in
/-- **Comparison of local factors.** Let `L` be a local subalgebra of `K` over `D` containing
`E`, and `L'` the same ring viewed as a subalgebra over `E`. Then the norm to `κ(D)` of the
`κ(E)`-normed local symbol of `L'` is the `κ(D)`-normed local symbol of `L`. -/
theorem normDown_normSym_of_carrier {L : Subalgebra D K} {L' : Subalgebra E K} [IsLocalRing L]
    [IsLocalRing L'] [IsNoetherianRing L] [Ring.KrullDimLE 1 L] [IsNoetherianRing L']
    [Ring.KrullDimLE 1 L'] (hLL' : ∀ x, x ∈ L ↔ (RingEquiv.refl K) x ∈ L') (hle : E ≤ L)
    [IsLocalHom (algebraMap E L')] [IsLocalHom (Subalgebra.inclusion hle : E →+* L)] :
    normDown E (normSym L' f g) = normSym L f g := by
  have hDL : IsLocalHom (algebraMap D L) := isLocalHom_algebraMap_of_le hle
  let _ : Algebra E L := (Subalgebra.inclusion hle).toAlgebra
  have : IsLocalHom (algebraMap E L) := ‹IsLocalHom (Subalgebra.inclusion hle : E →+* L)›
  have : IsScalarTower D E L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hsym : localSymbol L' f g =
      Units.map (ResidueField.mapEquiv (subEquiv (RingEquiv.refl K) hLL') :
        ResidueField L →* ResidueField L') (localSymbol L f g) := by
    have := localSymbol_map (subEquiv (RingEquiv.refl K) hLL') (RingEquiv.refl K)
      (fun _ ↦ rfl) f g
    have e : ∀ x : Kˣ, Units.map ((RingEquiv.refl K : K ≃+* K) : K →* K) x = x :=
      fun x ↦ Units.ext rfl
    rwa [e, e] at this
  have hc : ∀ x : ResidueField E, ResidueField.mapEquiv (subEquiv (RingEquiv.refl K) hLL')
      (algebraMap (ResidueField E) (ResidueField L) x) =
      algebraMap (ResidueField E) (ResidueField L') x := by
    intro x
    obtain ⟨e, rfl⟩ := residue_surjective x
    rw [ResidueField.algebraMap_residue, ResidueField.algebraMap_residue,
      ResidueField.mapEquiv_apply, ResidueField.map_residue]
    rfl
  have : Module.Free (ResidueField E) (ResidueField L) := Module.Free.of_divisionRing _ _
  rw [normSym_eq, hsym, normSym_eq, normDown_eq]
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [← AlgEquiv.ofRingEquiv_apply hc, Algebra.norm_eq_of_algEquiv, Algebra.norm_norm]

open GromovWitten.AlgebraicGeometry.IntersectionTheory.VectorBundle (UnitDifferences) in
/-- **Relative tame symbols.** If `S` is an admissible overring of the local subalgebra `E` for
`(f, g)`, then the norm to `κ(D)` of the tame symbol of `E` (a Noetherian local domain of
dimension `≤ 1` with fraction field `K`) is the product over the maximal ideals `Q` of `S` of
`normSym (S_Q) f g`. -/
theorem normDown_tameSymbol (hU : UnitDifferences E) (hS : Admissible E S ![f, g]) :
    normDown E (tameSymbol E K hU f g) =
      ∏ᶠ Q : MaximalSpectrum S, normSym (localizationAt S Q.asIdeal) f g := by
  classical
  let h : ∀ x, x ∈ S ↔ (RingEquiv.refl K) x ∈ overSubalgebra hS.isOverring.le :=
    fun _ ↦ Iff.rfl
  have hS' := admissible_overSubalgebra hS
  have := hS.isOverring.finite_maximalSpectrum
  have : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  have : Fintype (MaximalSpectrum (overSubalgebra hS.isOverring.le)) :=
    Fintype.ofEquiv _ (maxSpecEquiv (RingEquiv.refl K) h)
  rw [tameSymbol_eq_tameOf hU hS', tameOf, finprod_eq_prod_of_fintype,
    finprod_eq_prod_of_fintype, map_prod]
  refine (Fintype.prod_equiv (maxSpecEquiv (RingEquiv.refl K) h) _ _ fun Q ↦ ?_).symm
  have hS'' := hS'.isOverring
  have := hS.isOverring.isNoetherianRing
  have := hS.isOverring.krullDimLE
  have := hS''.isNoetherianRing
  have := hS''.krullDimLE
  have : (Q.asIdeal.comap (subEquiv (RingEquiv.refl K) h).symm).IsMaximal :=
    (maxSpecEquiv (RingEquiv.refl K) h Q).isMaximal
  have := isLocalHom_algebraMap_localizationAt hS''
    (Q.asIdeal.comap (subEquiv (RingEquiv.refl K) h).symm)
  have := isLocalHom_inclusion_localizationAt hS.isOverring Q.asIdeal
  exact (normDown_normSym_of_carrier
    (mem_localizationAt_subEquiv_iff (RingEquiv.refl K) h Q.asIdeal)
    (hS.isOverring.le.trans (le_localizationAt S Q.asIdeal))).symm

end Relative

section NormDown

open GromovWitten.AlgebraicGeometry.IntersectionTheory.VectorBundle (UnitDifferences)

variable {D K : Type*} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
  [Ring.KrullDimLE 1 D] [Field K] [Algebra D K] [IsFractionRing D K]

omit [IsDomain D] [IsLocalRing D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- Every subalgebra of `K` inherits unit differences from `D`. -/
theorem unitDifferences_subalgebra (hU : UnitDifferences D) (E : Subalgebra D K) :
    UnitDifferences E :=
  unitDifferences_of_injective_tame (algebraMap D E)
    (fun _ _ hxy ↦ IsFractionRing.injective D K (congrArg Subtype.val hxy)) hU

omit [IsDomain D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- For an overring `B` of `D`, `normDown (B_P)` is the norm `N_{κ(B_P)/κ(D)}` (the homomorphism
`D → B_P` being local). -/
theorem normDown_localizationAt_eq {B : Subalgebra D K} (hB : IsOverring ⊥ B) (P : Ideal B)
    [P.IsMaximal] :
    haveI := isLocalHom_algebraMap_localizationAt hB P
    normDown (localizationAt B P) = Units.map (Algebra.norm (ResidueField D) :
      ResidueField (localizationAt B P) →* ResidueField D) := by
  have := isLocalHom_algebraMap_localizationAt hB P
  exact normDown_eq _

/-- **T5 (norm-down, Stacks 42.5.3).** For any overring `B` of `D` (the Noetherian and
dimension instances on `B` follow from `hB` via `IsOverring.isNoetherianRing` and
`IsOverring.krullDimLE`),
`∂_D(f, g) = ∏_{P ∈ MaxSpec B} N_{κ(B_P)/κ(D)} ∂_{B_P}(f, g)`,
where `∂_{B_P}` is the tame symbol of the local ring `B_P` (with fraction field `K`) and the norm
`normDown` is `Algebra.norm` since `D → B_P` is local (`normDown_eq`,
`isLocalHom_algebraMap_localizationAt`). -/
theorem tameSymbol_eq_finprod_normDown (hU : UnitDifferences D) {B : Subalgebra D K}
    (hB : IsOverring ⊥ B) [IsNoetherianRing B] [Ring.KrullDimLE 1 B] (f g : Kˣ) :
    tameSymbol D K hU f g = ∏ᶠ P : MaximalSpectrum B, normDown (localizationAt B P.asIdeal)
      (tameSymbol (localizationAt B P.asIdeal) K
        (unitDifferences_subalgebra hU (localizationAt B P.asIdeal)) f g) := by
  obtain ⟨C₀, hC₀⟩ := exists_admissible (⊥ : Subalgebra D K) (unitDifferences_bot hU) ![f, g]
  have hCo : IsOverring ⊥ (C₀ ⊔ B) := hC₀.isOverring.sup hB
  have hC : Admissible ⊥ (C₀ ⊔ B) ![f, g] :=
    hC₀.of_isOverring_right (isOverring_of_le_of_le hCo bot_le le_sup_left)
  have hBC : IsOverring B (C₀ ⊔ B) := isOverring_of_le_of_le hCo bot_le le_sup_right
  rw [tameSymbol_eq_tameOf hU hC, tameOf_eq_finprod_semiLoc hBC hB hCo]
  refine finprod_congr fun P ↦ ?_
  have := isLocalHom_algebraMap_localizationAt hB P.asIdeal
  have hadm : Admissible (localizationAt B P.asIdeal) (semiLoc hBC.le P.asIdeal) ![f, g] := by
    refine ⟨isOverring_semiLoc P.asIdeal hBC, fun Q' _ ↦ ?_⟩
    have := isMaximal_semiLocContract hBC P.asIdeal Q'
    rw [localizationAt_semiLoc_eq hBC P.asIdeal Q']
    exact hC.factors _
  rw [normDown_tameSymbol _ hadm]

end NormDown

section Invariance

open GromovWitten.AlgebraicGeometry.IntersectionTheory.VectorBundle (UnitDifferences)

/-- Norms commute with compatible isomorphisms of field extensions. -/
theorem norm_ringEquiv_compat {A A' B B' : Type*} [Field A] [Field A'] [Field B] [Field B']
    [Algebra A B] [Algebra A' B'] (ΨA : A ≃+* A') (Ψ : B ≃+* B')
    (hc : ∀ a, Ψ (algebraMap A B a) = algebraMap A' B' (ΨA a)) (x : B) :
    Algebra.norm A' (Ψ x) = ΨA (Algebra.norm A x) := by
  let _ : Algebra A B' := ((algebraMap A' B').comp (ΨA : A →+* A')).toAlgebra
  let Φ : B ≃ₐ[A] B' := AlgEquiv.ofRingEquiv (f := Ψ) hc
  rw [← Algebra.norm_eq_of_algEquiv Φ x]
  exact (Algebra.norm_eq_of_ringEquiv ΨA rfl (Ψ x)).symm

variable {D K D' K' : Type*} [CommRing D] [Field K] [Algebra D K] [IsFractionRing D K]
  [CommRing D'] [Field K'] [Algebra D' K'] [IsFractionRing D' K']
  (e : D ≃+* D') (σ : K ≃+* K') (hσ : ∀ d : D, σ (algebraMap D K d) = algebraMap D' K' (e d))

include hσ in
omit [IsFractionRing D K] [IsFractionRing D' K'] in
/-- `σ⁻¹` is compatible with `e⁻¹`. -/
theorem symm_algebraMap_of_compat (d' : D') :
    σ.symm (algebraMap D' K' d') = algebraMap D K (e.symm d') := by
  rw [σ.symm_apply_eq, hσ, RingEquiv.apply_symm_apply]

/-- The image of a subalgebra `C` of `K` under `σ`, as a subalgebra of `K'` over `D'`. -/
def mapSub (C : Subalgebra D K) : Subalgebra D' K' where
  carrier := {y | σ.symm y ∈ C}
  mul_mem' {x y} hx hy := by
    change σ.symm (x * y) ∈ C
    rw [map_mul]
    exact C.mul_mem hx hy
  add_mem' {x y} hx hy := by
    change σ.symm (x + y) ∈ C
    rw [map_add]
    exact C.add_mem hx hy
  algebraMap_mem' d' := by
    change σ.symm (algebraMap D' K' d') ∈ C
    rw [symm_algebraMap_of_compat e σ hσ]
    exact C.algebraMap_mem _

omit [IsFractionRing D K] [IsFractionRing D' K'] in
/-- `σ` maps `C` onto `mapSub e σ hσ C`. -/
theorem mem_mapSub_iff (C : Subalgebra D K) (x : K) : x ∈ C ↔ σ x ∈ mapSub e σ hσ C := by
  change x ∈ C ↔ σ.symm (σ x) ∈ C
  rw [σ.symm_apply_apply]

omit [IsFractionRing D K] [IsFractionRing D' K'] in
/-- Overrings transport along compatible isomorphisms. -/
theorem isOverring_mapSub {C : Subalgebra D K} (hC : IsOverring ⊥ C) :
    IsOverring ⊥ (mapSub e σ hσ C) := by
  rw [isOverring_bot_iff_span] at *
  have : RingHomSurjective (e : D →+* D') := ⟨e.surjective⟩
  let σₛₗ : K →ₛₗ[(e : D →+* D')] K' :=
    { toFun := σ
      map_add' := map_add σ
      map_smul' := fun d x ↦ by
        rw [Algebra.smul_def, map_mul, hσ, Algebra.smul_def]
        rfl }
  have hset : σₛₗ '' (C : Set K) = (mapSub e σ hσ C : Set K') := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_mapSub_iff e σ hσ C x).1 hx
    · intro hy
      exact ⟨σ.symm y, hy, σ.apply_symm_apply y⟩
  rw [← hset, ← Submodule.map_span]
  exact hC.map σₛₗ

variable {f g : Kˣ}

omit [IsFractionRing D K] [IsFractionRing D' K'] in
/-- Admissible overrings transport along compatible isomorphisms. -/
theorem admissible_mapSub {C : Subalgebra D K} (hC : Admissible ⊥ C ![f, g]) :
    Admissible ⊥ (mapSub e σ hσ C)
      ![Units.map (σ : K →* K') f, Units.map (σ : K →* K') g] := by
  refine ⟨isOverring_mapSub e σ hσ hC.isOverring, fun Q' _ ↦ ?_⟩
  let h := mem_mapSub_iff e σ hσ C
  let Q : MaximalSpectrum C := (maxSpecEquiv σ h).symm ⟨Q', ‹_›⟩
  have hQ : maxSpecEquiv σ h Q = ⟨Q', ‹_›⟩ := Equiv.apply_symm_apply _ _
  have := (hC.factors Q.asIdeal).transport σ (mem_localizationAt_subEquiv_iff σ h Q.asIdeal)
  have e1 : (fun i ↦ Units.map (σ : K →* K') (![f, g] i)) =
      ![Units.map (σ : K →* K') f, Units.map (σ : K →* K') g] := by
    funext i
    fin_cases i <;> rfl
  rw [e1] at this
  have e2 : Q.asIdeal.comap (subEquiv σ h).symm = Q' := congrArg MaximalSpectrum.asIdeal hQ
  convert this using 2
  rw [e2]

variable [IsDomain D] [IsLocalRing D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D]
  [IsDomain D'] [IsLocalRing D'] [IsNoetherianRing D'] [Ring.KrullDimLE 1 D']

omit [IsDomain D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D] [IsDomain D'] [IsNoetherianRing D']
  [Ring.KrullDimLE 1 D'] in
/-- Local factors transport along compatible isomorphisms. -/
theorem normSym_locEquiv {C : Subalgebra D K} (hC : IsOverring ⊥ C) [IsNoetherianRing C]
    [Ring.KrullDimLE 1 C] (Q : Ideal C) [Q.IsMaximal] :
    normSym (localizationAt (mapSub e σ hσ C) (Q.comap
      (subEquiv σ (mem_mapSub_iff e σ hσ C)).symm)) (Units.map (σ : K →* K') f)
      (Units.map (σ : K →* K') g) =
      Units.map (ResidueField.mapEquiv e : ResidueField D →* ResidueField D')
        (normSym (localizationAt C Q) f g) := by
  let h := mem_mapSub_iff e σ hσ C
  have hC' := isOverring_mapSub e σ hσ hC
  have : IsNoetherianRing (mapSub e σ hσ C) :=
    isNoetherianRing_of_ringEquiv C (subEquiv σ h)
  have : Ring.KrullDimLE 1 (mapSub e σ hσ C) := by
    rw [Ring.krullDimLE_iff, ← ringKrullDim_eq_of_ringEquiv (subEquiv σ h)]
    exact Ring.krullDimLE_iff.1 ‹_›
  have : (Q.comap (subEquiv σ h).symm).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ (subEquiv σ h).symm.surjective
  have := isLocalHom_algebraMap_localizationAt hC Q
  have := isLocalHom_algebraMap_localizationAt hC' (Q.comap (subEquiv σ h).symm)
  let ψ := locEquiv σ h Q
  rw [normSym_eq, normSym_eq, localSymbol_map ψ σ (fun _ ↦ rfl)]
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  refine norm_ringEquiv_compat (ResidueField.mapEquiv e) (ResidueField.mapEquiv ψ) (fun a ↦ ?_) _
  obtain ⟨d, rfl⟩ := residue_surjective a
  rw [ResidueField.algebraMap_residue, ResidueField.mapEquiv_apply, ResidueField.map_residue,
    ResidueField.mapEquiv_apply, ResidueField.map_residue, ResidueField.algebraMap_residue]
  congr 1
  exact Subtype.ext (hσ d)

include hσ in
/-- **T6 (invariance).** If `e : D ≃+* D'` and `σ : K ≃+* K'` are compatible with the maps to the
fraction fields, then `∂_{D'}(σ f, σ g)` is the image of `∂_D(f, g)` under the induced
isomorphism of residue fields. -/
theorem tameSymbol_ringEquiv (hU : UnitDifferences D) (hU' : UnitDifferences D') (f g : Kˣ) :
    tameSymbol D' K' hU' (Units.map (σ : K →* K') f) (Units.map (σ : K →* K') g) =
      Units.map (ResidueField.mapEquiv e : ResidueField D →* ResidueField D')
        (tameSymbol D K hU f g) := by
  classical
  obtain ⟨C, hC⟩ := exists_admissible (⊥ : Subalgebra D K) (unitDifferences_bot hU) ![f, g]
  let h := mem_mapSub_iff e σ hσ C
  have := hC.isOverring.finite_maximalSpectrum
  have : Fintype (MaximalSpectrum C) := Fintype.ofFinite _
  have : Fintype (MaximalSpectrum (mapSub e σ hσ C)) := Fintype.ofEquiv _ (maxSpecEquiv σ h)
  have := hC.isOverring.isNoetherianRing
  have := hC.isOverring.krullDimLE
  rw [tameSymbol_eq_tameOf hU' (admissible_mapSub e σ hσ hC), tameSymbol_eq_tameOf hU hC, tameOf,
    tameOf, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, map_prod]
  refine (Fintype.prod_equiv (maxSpecEquiv σ h) _ _ fun Q ↦ ?_).symm
  exact (normSym_locEquiv e σ hσ hC.isOverring Q.asIdeal).symm

/-- **T6, same ring.** The tame symbol does not depend on the choice of fraction field: for a
`D`-algebra isomorphism `σ : K ≃ₐ[D] K'` of fraction fields, `∂_D` computed in `K'` on
`(σ f, σ g)` equals `∂_D(f, g)` computed in `K`. -/
theorem tameSymbol_algEquiv [Algebra D K'] [IsFractionRing D K'] (hU : UnitDifferences D)
    (τ : K ≃ₐ[D] K') (f g : Kˣ) :
    tameSymbol D K' hU (Units.map (τ : K →* K') f) (Units.map (τ : K →* K') g) =
      tameSymbol D K hU f g := by
  have := tameSymbol_ringEquiv (RingEquiv.refl D) τ.toRingEquiv (fun d ↦ τ.commutes d) hU hU f g
  have e1 : ∀ x : Kˣ, Units.map (τ.toRingEquiv : K →* K') x = Units.map (τ : K →* K') x :=
    fun x ↦ Units.ext rfl
  have e2 : ∀ y : (ResidueField D)ˣ,
      Units.map (ResidueField.mapEquiv (RingEquiv.refl D) : ResidueField D →* ResidueField D) y =
        y := fun y ↦ by rw [ResidueField.mapEquiv_refl]; exact Units.ext rfl
  rw [e1, e1, e2] at this
  exact this

end Invariance

end GromovWitten.Algebra.Tame
