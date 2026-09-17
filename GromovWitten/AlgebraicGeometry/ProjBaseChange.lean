/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change of `Proj`

Let `𝒜` be a graded algebra over a ring `A` and let `ℬ` be a graded algebra over an `A`-algebra
`B`.  A graded ring map `ψ : 𝒜 → ℬ` lying over `A → B` *exhibits `ℬ` as the base change of `𝒜`*
when, in every degree `n`, the induced map `𝒜ₙ ⊗_A B → ℬₙ` is bijective
(`GradedHomOver.IsBaseChange`).  The main theorem `isPullback_map` shows that the induced
morphism `Proj ℬ ⟶ Proj 𝒜` is then the base change of the structure morphism
`Proj 𝒜 ⟶ Spec A` along `Spec B ⟶ Spec A`:

```
Proj ℬ ⟶ Proj 𝒜
  |          |
Spec B ⟶ Spec A
```
is cartesian.  No flatness is needed: `Proj` commutes with arbitrary base change.

The proof is chart by chart.  For a homogeneous `s ∈ 𝒜_d` of positive degree the comparison
`(𝒜_s)₀ ⊗_A B → (ℬ_{ψ s})₀` is proved bijective (`chartTensorMap_bijective`): every element of
`(𝒜_s)₀ ⊗_A B` has a common denominator `sⁿ`, the map is then `x ⊗ b ↦ ψ x · b / (ψ s)ⁿ`, and
injectivity follows from the degreewise bijectivity after clearing denominators.  Each chart
square is therefore cartesian, and cartesianness is local on the target.

This is the general form of the flat base change of Rees blowups proved in
`Curves/StableReduction/ReesBaseChange.lean`, and it is the input for gluing relative `Proj`
over a base scheme.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace HomogeneousLocalization TensorProduct

namespace GromovWitten.AlgebraicGeometry.ProjBaseChange

universe u

noncomputable section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {S T : Type u} [CommRing S] [CommRing T] [Algebra A S] [Algebra B T] [Algebra A T]
  [IsScalarTower A B T]
variable (𝒜 : ℕ → Submodule A S) [GradedAlgebra 𝒜] (ℬ : ℕ → Submodule B T) [GradedAlgebra ℬ]

/-! ### Graded maps over the base -/

/-- A graded ring map `𝒜 → ℬ` lying over the structure maps of the base rings. -/
structure GradedHomOver extends 𝒜 →+*ᵍ ℬ where
  commutes' : ∀ a : A, toRingHom (algebraMap A S a) = algebraMap A T a

namespace GradedHomOver

variable {𝒜 ℬ} (ψ : GradedHomOver 𝒜 ℬ)

omit [Algebra A B] [IsScalarTower A B T] [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem commutes (a : A) : ψ.toRingHom (algebraMap A S a) = algebraMap A T a := ψ.commutes' a

/-- The underlying `A`-algebra map. -/
def algHom : S →ₐ[A] T := { ψ.toRingHom with commutes' := ψ.commutes' }

omit [Algebra A B] [IsScalarTower A B T] [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
@[simp]
theorem algHom_apply (x : S) : ψ.algHom x = ψ.toRingHom x := rfl

/-- The comparison map `S ⊗_A B → T`. -/
def tensorAlgHom : S ⊗[A] B →ₐ[A] T :=
  Algebra.TensorProduct.lift ψ.algHom (IsScalarTower.toAlgHom A B T) fun _ _ ↦ Commute.all _ _

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
@[simp]
theorem tensorAlgHom_tmul (x : S) (b : B) :
    ψ.tensorAlgHom (x ⊗ₜ b) = ψ.toRingHom x * algebraMap B T b := by
  simp [tensorAlgHom]

/-- The degree-`n` comparison map `𝒜ₙ ⊗_A B → T`. -/
def degreeMap (n : ℕ) : (𝒜 n) ⊗[A] B →ₗ[A] T :=
  ψ.tensorAlgHom.toLinearMap ∘ₗ TensorProduct.map (𝒜 n).subtype LinearMap.id

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
@[simp]
theorem degreeMap_tmul (n : ℕ) (x : 𝒜 n) (b : B) :
    ψ.degreeMap n (x ⊗ₜ b) = ψ.toRingHom x * algebraMap B T b := by
  simp [degreeMap]

/-- `ψ` exhibits `ℬ` as the base change of `𝒜` along `A → B`: in every degree the comparison
map `𝒜ₙ ⊗_A B → T` is injective with image `ℬₙ`. -/
structure IsBaseChange : Prop where
  injective : ∀ n, Function.Injective (ψ.degreeMap n)
  range_eq : ∀ n, LinearMap.range (ψ.degreeMap n) = (ℬ n).restrictScalars A

variable {ψ}

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem IsBaseChange.mem_range (h : ψ.IsBaseChange) {n : ℕ} {y : T} (hy : y ∈ ℬ n) :
    ∃ z, ψ.degreeMap n z = y := by
  have : y ∈ LinearMap.range (ψ.degreeMap n) := by
    rw [h.range_eq]
    exact hy
  exact LinearMap.mem_range.mp this

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem IsBaseChange.degreeMap_mem (h : ψ.IsBaseChange) (n : ℕ) (z : (𝒜 n) ⊗[A] B) :
    ψ.degreeMap n z ∈ ℬ n := by
  have : ψ.degreeMap n z ∈ LinearMap.range (ψ.degreeMap n) := ⟨z, rfl⟩
  rw [h.range_eq] at this
  exact this

/-- The image of the irrelevant ideal generates the irrelevant ideal, so `Proj.map` applies. -/
theorem IsBaseChange.irrelevant_le (h : ψ.IsBaseChange) :
    HomogeneousIdeal.irrelevant ℬ ≤
      HomogeneousIdeal.map ψ.toGradedRingHom (HomogeneousIdeal.irrelevant 𝒜) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi y hy
  obtain ⟨z, rfl⟩ := h.mem_range (show y ∈ ℬ i from hy)
  clear hy
  change ψ.degreeMap i z ∈ (HomogeneousIdeal.map ψ.toGradedRingHom
    (HomogeneousIdeal.irrelevant 𝒜)).toIdeal
  rw [HomogeneousIdeal.toIdeal_map]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    rw [degreeMap_tmul]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    change (x : S) ∈ HomogeneousIdeal.irrelevant 𝒜
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_ne 𝒜 x.2 hi.ne']
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

end GradedHomOver

/-! ### The charts -/

section Chart

variable {𝒜 ℬ} (ψ : GradedHomOver 𝒜 ℬ) {s : S} {d : ℕ} (hs : s ∈ 𝒜 d)

/-- The base ring acts on a homogeneous localization through degree zero; the scalar action is
the existing one on numerators. -/
@[instance_reducible]
def awayAlgebra (s : S) : Algebra A (Away 𝒜 s) where
  toSMul := inferInstance
  algebraMap := (fromZeroRingHom 𝒜 (Submonoid.powers s)).comp (algebraMap A (𝒜 0))
  commutes' _ _ := mul_comm _ _
  smul_def' a x := by
    apply val_injective
    change (a • x).val =
      (HomogeneousLocalization.mk ⟨0, algebraMap A (𝒜 0) a, 1, one_mem _⟩ * x).val
    rw [val_smul, val_mul, val_mk, Algebra.smul_def,
      IsScalarTower.algebraMap_apply A S (Localization (Submonoid.powers s)),
      ← Localization.mk_one_eq_algebraMap]
    rfl

/-- The original base ring acts on a homogeneous localization of `ℬ` through `B`. -/
@[instance_reducible]
def awayBaseAlgebra (t : T) : Algebra A (Away ℬ t) :=
  (((fromZeroRingHom ℬ (Submonoid.powers t)).comp (algebraMap B (ℬ 0))).comp
    (algebraMap A B)).toAlgebra

attribute [local instance 1100] awayAlgebra
attribute [local instance 900] awayBaseAlgebra

instance awayScalarTower (t : T) : IsScalarTower A B (Away ℬ t) :=
  IsScalarTower.of_algebraMap_eq (R := A) (S := B) (A := Away ℬ t) fun _ ↦ rfl

omit [Algebra A B] [IsScalarTower A B T] in
theorem val_algebraMap_away (a : A) :
    (algebraMap A (Away 𝒜 s) a).val = Localization.mk (algebraMap A S a) 1 := by
  change (HomogeneousLocalization.mk ⟨0, algebraMap A (𝒜 0) a, 1, one_mem _⟩).val = _
  rw [val_mk]
  rfl

omit [Algebra A B] [IsScalarTower A B T] in
theorem val_algebraMap_awayBase (t : T) (b : B) :
    (algebraMap B (Away ℬ t) b).val = Localization.mk (algebraMap B T b) 1 := by
  change (HomogeneousLocalization.mk ⟨0, algebraMap B (ℬ 0) b, 1, one_mem _⟩).val = _
  rw [val_mk]
  rfl

omit [Algebra A B] [IsScalarTower A B T] in
theorem awayMap_fromZeroRingHom (z : 𝒜 0) :
    Away.map ψ.toGradedRingHom s (fromZeroRingHom 𝒜 _ z) =
      fromZeroRingHom ℬ _ ⟨ψ.toRingHom z, ψ.map_mem z.2⟩ := by
  apply val_injective
  change (map ψ.toGradedRingHom _ (HomogeneousLocalization.mk ⟨0, z, 1, one_mem _⟩)).val =
    (HomogeneousLocalization.mk ⟨0, _, 1, one_mem _⟩).val
  rw [map_mk, val_mk, val_mk]
  congr 1
  exact Subtype.ext (map_one _)

/-- The chart map as an `A`-algebra morphism. -/
def awayMapAlgHom : Away 𝒜 s →ₐ[A] Away ℬ (ψ.toRingHom s) where
  toFun := Away.map ψ.toGradedRingHom s
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' a := by
    change Away.map ψ.toGradedRingHom s (fromZeroRingHom 𝒜 _ (algebraMap A (𝒜 0) a)) =
      fromZeroRingHom ℬ _ (algebraMap B (ℬ 0) (algebraMap A B a))
    rw [awayMap_fromZeroRingHom]
    congr 1
    apply Subtype.ext
    change ψ.toRingHom (algebraMap A S a) = algebraMap B T (algebraMap A B a)
    rw [ψ.commutes, IsScalarTower.algebraMap_apply A B T]

@[simp]
theorem awayMapAlgHom_apply (z : Away 𝒜 s) :
    awayMapAlgHom ψ (s := s) z = Away.map ψ.toGradedRingHom s z := rfl

/-- The comparison map from the scalar extension of a chart of `Proj 𝒜` to the corresponding
chart of `Proj ℬ`. -/
def chartTensorMap : Away 𝒜 s ⊗[A] B →ₐ[A] Away ℬ (ψ.toRingHom s) :=
  Algebra.TensorProduct.lift (awayMapAlgHom ψ (s := s)) (IsScalarTower.toAlgHom A B _)
    fun _ _ ↦ Commute.all _ _

@[simp]
theorem chartTensorMap_tmul (z : Away 𝒜 s) (b : B) :
    chartTensorMap ψ (s := s) (z ⊗ₜ b) =
      Away.map ψ.toGradedRingHom s z * algebraMap B (Away ℬ (ψ.toRingHom s)) b := by
  simp only [chartTensorMap, Algebra.TensorProduct.lift_tmul, IsScalarTower.toAlgHom_apply]
  rfl

/-! #### Common denominators -/

theorem away_mk_add (n : ℕ) {x y : S} (hx : x ∈ 𝒜 (n • d)) (hy : y ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hs n (x + y) (add_mem hx hy) = Away.mk 𝒜 hs n x hx + Away.mk 𝒜 hs n y hy := by
  apply val_injective
  rw [val_add, Away.val_mk, Away.val_mk, Away.val_mk, Localization.add_mk_self]

theorem away_mk_congr (n : ℕ) {x y : S} (hxy : x = y) (hx : x ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hs n x hx = Away.mk 𝒜 hs n y (hxy ▸ hx) := by
  subst hxy
  rfl

theorem away_mk_zero (n : ℕ) : Away.mk 𝒜 hs n 0 (zero_mem _) = 0 := by
  apply val_injective
  rw [val_zero, Away.val_mk, Localization.mk_zero]

theorem away_mk_eq_zero_iff (n : ℕ) {x : S} (hx : x ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hs n x hx = 0 ↔ ∃ m : ℕ, s ^ m * x = 0 := by
  rw [← away_mk_zero hs n]
  constructor
  · intro h
    have h' := congrArg HomogeneousLocalization.val h
    rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h'
    obtain ⟨⟨c, m, rfl⟩, hc⟩ := h'
    refine ⟨m + n, ?_⟩
    rw [pow_add, mul_assoc]
    simpa using hc
  · rintro ⟨m, hm⟩
    apply val_injective
    rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨⟨s ^ m, m, rfl⟩, ?_⟩
    simp only [mul_zero]
    rw [← mul_assoc, mul_comm (s ^ m), mul_assoc, hm, mul_zero]

/-- The degree-`n • d` part, mapped into the chart by `x ↦ x / sⁿ`. -/
def mkLinear (n : ℕ) : 𝒜 (n • d) →ₗ[A] Away 𝒜 s where
  toFun x := Away.mk 𝒜 hs n x x.2
  map_add' x y := away_mk_add hs n x.2 y.2
  map_smul' a x := by
    apply val_injective
    rw [RingHom.id_apply]
    erw [val_smul, Away.val_mk, Away.val_mk, Localization.smul_mk]
    rfl

@[simp]
theorem mkLinear_apply (n : ℕ) (x : 𝒜 (n • d)) : mkLinear hs n x = Away.mk 𝒜 hs n x x.2 := rfl

/-- Raising the denominator: multiplication by `s ^ (m - n)` from degree `n • d` to `m • d`. -/
def shiftLinear {n m : ℕ} (h : n ≤ m) : 𝒜 (n • d) →ₗ[A] 𝒜 (m • d) where
  toFun x := ⟨s ^ (m - n) * x, by
    have := SetLike.mul_mem_graded (SetLike.pow_mem_graded (m - n) hs) x.2
    rwa [← add_smul, Nat.sub_add_cancel h] at this⟩
  map_add' x y := Subtype.ext (by simp [mul_add])
  map_smul' a x := Subtype.ext (by simp [Algebra.smul_def]; ring)

@[simp]
theorem coe_shiftLinear {n m : ℕ} (h : n ≤ m) (x : 𝒜 (n • d)) :
    (shiftLinear hs h x : S) = s ^ (m - n) * x := rfl

theorem mkLinear_shiftLinear {n m : ℕ} (h : n ≤ m) (x : 𝒜 (n • d)) :
    mkLinear hs m (shiftLinear hs h x) = mkLinear hs n x := by
  apply val_injective
  simp only [mkLinear_apply, Away.val_mk, coe_shiftLinear]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le h]

/-- The tensor version of `mkLinear`. -/
def mkTensor (n : ℕ) : (𝒜 (n • d)) ⊗[A] B →ₗ[A] Away 𝒜 s ⊗[A] B :=
  TensorProduct.map (mkLinear hs n) LinearMap.id

/-- The tensor version of `shiftLinear`. -/
def shiftTensor {n m : ℕ} (h : n ≤ m) : (𝒜 (n • d)) ⊗[A] B →ₗ[A] (𝒜 (m • d)) ⊗[A] B :=
  TensorProduct.map (shiftLinear hs h) LinearMap.id

theorem mkTensor_shiftTensor {n m : ℕ} (h : n ≤ m) (z : (𝒜 (n • d)) ⊗[A] B) :
    mkTensor hs m (shiftTensor hs h z) = mkTensor hs n z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    simp only [mkTensor, shiftTensor, TensorProduct.map_tmul, LinearMap.id_apply,
      mkLinear_shiftLinear]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- Every element of `(𝒜_s)₀ ⊗_A B` has a common denominator. -/
theorem exists_mkTensor (w : Away 𝒜 s ⊗[A] B) : ∃ n z, mkTensor hs n z = w := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, map_zero _⟩
  | tmul z b =>
    obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 hs z
    exact ⟨n, ⟨x, hx⟩ ⊗ₜ b, by simp [mkTensor]⟩
  | add w₁ w₂ h₁ h₂ =>
    obtain ⟨n₁, z₁, rfl⟩ := h₁
    obtain ⟨n₂, z₂, rfl⟩ := h₂
    refine ⟨max n₁ n₂, shiftTensor hs (le_max_left n₁ n₂) z₁ +
      shiftTensor hs (le_max_right n₁ n₂) z₂, ?_⟩
    rw [map_add, mkTensor_shiftTensor, mkTensor_shiftTensor]

/-! #### The comparison on common denominators -/

variable (hψs : ψ.toRingHom s ∈ ℬ d)

theorem chartTensorMap_mkTensor (h : ψ.IsBaseChange) (n : ℕ) (z : (𝒜 (n • d)) ⊗[A] B) :
    chartTensorMap ψ (s := s) (mkTensor hs n z) =
      Away.mk ℬ (ψ.map_mem hs) n (ψ.degreeMap (n • d) z) (h.degreeMap_mem _ z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    symm
    rw [away_mk_eq_zero_iff]
    exact ⟨0, by rw [map_zero, mul_zero]⟩
  | tmul x b =>
    rw [mkTensor, TensorProduct.map_tmul, chartTensorMap_tmul, LinearMap.id_apply,
      mkLinear_apply, Away.map_mk, away_mk_congr (ψ.map_mem hs) n (ψ.degreeMap_tmul _ x b)]
    apply val_injective
    rw [val_mul, Away.val_mk, Away.val_mk, val_algebraMap_awayBase, Localization.mk_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp⟩
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, ← away_mk_add]
    exact away_mk_congr (ψ.map_mem hs) n (map_add (ψ.degreeMap _) x y).symm _

omit [GradedAlgebra ℬ] in
theorem degreeMap_shiftTensor {n m : ℕ} (hnm : n ≤ m) (z : (𝒜 (n • d)) ⊗[A] B) :
    ψ.degreeMap (m • d) (shiftTensor hs hnm z) =
      ψ.toRingHom s ^ (m - n) * ψ.degreeMap (n • d) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [shiftTensor, mul_assoc]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]

include hs in
theorem chartTensorMap_injective (h : ψ.IsBaseChange) :
    Function.Injective (chartTensorMap ψ (s := s)) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨n, z, rfl⟩ := exists_mkTensor hs w
  rw [chartTensorMap_mkTensor ψ hs h, away_mk_eq_zero_iff] at hw
  obtain ⟨m, hm⟩ := hw
  have hz : shiftTensor hs (Nat.le_add_right n m) z = 0 := by
    apply h.injective
    rw [degreeMap_shiftTensor, map_zero, Nat.add_sub_cancel_left]
    exact hm
  rw [← mkTensor_shiftTensor hs (Nat.le_add_right n m), hz, map_zero]

include hs in
theorem chartTensorMap_surjective (h : ψ.IsBaseChange) :
    Function.Surjective (chartTensorMap ψ (s := s)) := by
  intro y
  obtain ⟨n, y', hy', rfl⟩ := Away.mk_surjective ℬ (ψ.map_mem hs) y
  obtain ⟨z, hz⟩ := h.mem_range hy'
  subst hz
  exact ⟨mkTensor hs n z, chartTensorMap_mkTensor ψ hs h n z⟩

include hs in
theorem chartTensorMap_bijective (h : ψ.IsBaseChange) :
    Function.Bijective (chartTensorMap ψ (s := s)) :=
  ⟨chartTensorMap_injective ψ hs h, chartTensorMap_surjective ψ hs h⟩

/-! #### The cartesian chart square -/

include hs in
/-- The chart square of a base change of `Proj` is cartesian. -/
theorem chart_isPullback (h : ψ.IsBaseChange) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map ψ.toGradedRingHom s)))
      (Spec.map (CommRingCat.ofHom (algebraMap B (Away ℬ (ψ.toRingHom s)))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Away 𝒜 s))))
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  have hiso : IsIso (Spec.map (CommRingCat.ofHom (chartTensorMap ψ (s := s)).toRingHom)) := by
    rw [isIso_SpecMap_iff]
    exact chartTensorMap_bijective ψ hs h
  have hcomm : Spec.map (CommRingCat.ofHom (Away.map ψ.toGradedRingHom s)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Away 𝒜 s))) =
      Spec.map (CommRingCat.ofHom (algebraMap B (Away ℬ (ψ.toRingHom s)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro a
    exact (awayMapAlgHom ψ (s := s)).commutes a
  refine IsPullback.of_iso_pullback ⟨hcomm⟩
    (asIso (Spec.map (CommRingCat.ofHom (chartTensorMap ψ (s := s)).toRingHom)) ≪≫
      (pullbackSpecIso A (Away 𝒜 s) B).symm) ?_ ?_
  · rw [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc, pullbackSpecIso_inv_fst,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro z
    change chartTensorMap ψ (s := s) (z ⊗ₜ[A] (1 : B)) = Away.map ψ.toGradedRingHom s z
    rw [chartTensorMap_tmul, map_one, mul_one]
  · rw [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc, pullbackSpecIso_inv_snd,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro b
    change chartTensorMap ψ (s := s) ((1 : Away 𝒜 s) ⊗ₜ[A] b) =
      algebraMap B (Away ℬ (ψ.toRingHom s)) b
    rw [chartTensorMap_tmul, map_one, one_mul]

end Chart

/-! ### The global cartesian square -/

section Global

attribute [local instance 1100] awayAlgebra
attribute [local instance 900] awayBaseAlgebra

/- The index type of Mathlib's affine cover of `Proj` is a sigma type only up to unfolding, as
in Mathlib's own `Proj.map_comp`. -/
set_option backward.isDefEq.respectTransparency false

/-- The structure morphism of `Proj 𝒜` to the spectrum of the base ring. -/
def projection : Proj 𝒜 ⟶ Spec (.of A) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap A (𝒜 0)))

/-- If the graded algebra is of finite type over its degree-zero part and the degree-zero part
is the base ring, the structure morphism of `Proj` is proper. -/
theorem projection_isProper [Algebra.FiniteType (𝒜 0) S]
    (h0 : Function.Bijective (algebraMap A (𝒜 0))) : IsProper (projection 𝒜) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap A (𝒜 0)))) := by
    rw [isIso_SpecMap_iff]
    exact h0
  unfold projection
  infer_instance

theorem awayι_projection {s : S} {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    Proj.awayι 𝒜 s hs hd ≫ projection 𝒜 =
      Spec.map (CommRingCat.ofHom (algebraMap A (Away 𝒜 s))) := by
  rw [projection, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

variable {𝒜 ℬ} (ψ : GradedHomOver 𝒜 ℬ) (h : ψ.IsBaseChange)

section chart

variable {s : S} {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d)

/-- The chart of `Proj ℬ` attached to a homogeneous element of `𝒜`. -/
abbrev chartι : Spec (.of (Away ℬ (ψ.toGradedRingHom s))) ⟶ Proj ℬ :=
  Proj.awayι ℬ (ψ.toGradedRingHom s) (ψ.map_mem hs) hd

theorem chartι_comp_map :
    chartι ψ hs hd ≫ Proj.map ψ.toGradedRingHom h.irrelevant_le =
      Spec.map (CommRingCat.ofHom (Away.map ψ.toGradedRingHom s)) ≫ Proj.awayι 𝒜 s hs hd :=
  Proj.awayι_comp_map _ _ _ _ _

omit [Algebra A B] [IsScalarTower A B T] [GradedAlgebra 𝒜] in
theorem chartι_projection :
    chartι ψ hs hd ≫ projection ℬ =
      Spec.map (CommRingCat.ofHom (algebraMap B (Away ℬ (ψ.toGradedRingHom s)))) :=
  awayι_projection ℬ (s := ψ.toGradedRingHom s) (ψ.map_mem hs) hd

omit hd in
theorem awayMap_comp_algebraMap :
    (Away.map ψ.toGradedRingHom s).comp (algebraMap A (Away 𝒜 s)) =
      (algebraMap B (Away ℬ (ψ.toGradedRingHom s))).comp (algebraMap A B) :=
  RingHom.ext fun a ↦ (awayMapAlgHom ψ (s := s)).commutes a

theorem awayι_map_projection :
    chartι ψ hs hd ≫ Proj.map ψ.toGradedRingHom h.irrelevant_le ≫ projection 𝒜 =
      chartι ψ hs hd ≫ projection ℬ ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
  rw [← Category.assoc, chartι_comp_map ψ h hs hd, Category.assoc, awayι_projection 𝒜 hs hd,
    ← Category.assoc, chartι_projection, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, awayMap_comp_algebraMap]

theorem chartι_isPullback_map :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map ψ.toGradedRingHom s)))
      (chartι ψ hs hd) (Proj.awayι 𝒜 s hs hd) (Proj.map ψ.toGradedRingHom h.irrelevant_le) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (chartι_comp_map ψ h hs hd) ?_
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.map_preimage_basicOpen]

include h in
theorem chart_isPullback_projection :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map ψ.toGradedRingHom s)))
      (chartι ψ hs hd ≫ projection ℬ) (Proj.awayι 𝒜 s hs hd ≫ projection 𝒜)
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  rw [awayι_projection 𝒜 hs hd, chartι_projection]
  exact chart_isPullback ψ hs h

end chart

theorem map_projection :
    Proj.map ψ.toGradedRingHom h.irrelevant_le ≫ projection 𝒜 =
      projection ℬ ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
  refine (Proj.mapAffineOpenCover _ h.irrelevant_le).openCover.hom_ext _ _ ?_
  rintro ⟨⟨d, hd⟩, s, hs⟩
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  exact awayι_map_projection ψ h hs hd

/-- The comparison morphism from `Proj ℬ` to the base change of `Proj 𝒜`. -/
def comparison :
    Proj ℬ ⟶ pullback (projection 𝒜) (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  pullback.lift (Proj.map ψ.toGradedRingHom h.irrelevant_le) (projection ℬ) (map_projection ψ h)

section chart

variable {s : S} {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d)

variable (B) in
/-- The member of the cover of the base change attached to a chart of `Proj 𝒜`. -/
def chartPullbackMap :
    pullback (Proj.awayι 𝒜 s hs hd ≫ projection 𝒜)
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⟶
      pullback (projection 𝒜) (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  pullback.map _ _ _ _ (Proj.awayι 𝒜 s hs hd) (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem isIso_snd_comparison :
    IsIso (pullback.snd (comparison ψ h) (chartPullbackMap B hs hd)) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  have hfst : comparison ψ h ≫ pullback.fst (projection 𝒜) g =
      Proj.map ψ.toGradedRingHom h.irrelevant_le := pullback.lift_fst _ _ _
  have hsnd : comparison ψ h ≫ pullback.snd (projection 𝒜) g = projection ℬ :=
    pullback.lift_snd _ _ _
  have hmfst : chartPullbackMap B hs hd ≫ pullback.fst (projection 𝒜) g =
      pullback.fst (Proj.awayι 𝒜 s hs hd ≫ projection 𝒜) g ≫ Proj.awayι 𝒜 s hs hd :=
    pullback.lift_fst _ _ _
  have hmsnd : chartPullbackMap B hs hd ≫ pullback.snd (projection 𝒜) g =
      pullback.snd (Proj.awayι 𝒜 s hs hd ≫ projection 𝒜) g := by
    rw [chartPullbackMap, pullback.lift_snd, Category.comp_id]
  have hδfst := (chart_isPullback_projection ψ h hs hd).isoPullback_hom_fst
  have hδsnd := (chart_isPullback_projection ψ h hs hd).isoPullback_hom_snd
  have hS3 : IsPullback (pullback.fst (Proj.awayι 𝒜 s hs hd ≫ projection 𝒜) g)
      (chartPullbackMap B hs hd) (Proj.awayι 𝒜 s hs hd) (pullback.fst (projection 𝒜) g) := by
    refine IsPullback.of_bot ?_ hmfst.symm (IsPullback.of_hasPullback _ _)
    rw [hmsnd]
    exact IsPullback.of_hasPullback _ _
  have hp : (chart_isPullback_projection ψ h hs hd).isoPullback.hom ≫
      chartPullbackMap B hs hd = chartι ψ hs hd ≫ comparison ψ h := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmfst, ← Category.assoc, hδfst, Category.assoc, hfst]
      exact (chartι_comp_map ψ h hs hd).symm
    · rw [Category.assoc, hmsnd, hδsnd, Category.assoc, hsnd]
  have hS4 : IsPullback (chart_isPullback_projection ψ h hs hd).isoPullback.hom
      (chartι ψ hs hd) (chartPullbackMap B hs hd) (comparison ψ h) := by
    refine IsPullback.of_right ?_ hp hS3
    rw [hδfst, hfst]
    exact chartι_isPullback_map ψ h hs hd
  have hres : pullback.snd (comparison ψ h) (chartPullbackMap B hs hd) =
      hS4.flip.isoPullback.inv ≫ (chart_isPullback_projection ψ h hs hd).isoPullback.hom := by
    rw [Iso.eq_inv_comp]
    exact hS4.flip.isoPullback_hom_snd
  rw [hres]
  infer_instance

end chart

theorem isIso_comparison : IsIso (comparison ψ h) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_openCover
    (Scheme.Pullback.openCoverOfLeft (Proj.affineOpenCover 𝒜).openCover (projection 𝒜)
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))) ?_
  rintro ⟨⟨d, hd⟩, s, hs⟩
  rw [MorphismProperty.isomorphisms.iff]
  exact isIso_snd_comparison ψ h hs hd

/-- **Base change of `Proj`.**  If `ψ : 𝒜 → ℬ` exhibits `ℬ` as the base change of `𝒜` along
`A → B`, then `Proj ℬ` is the base change of `Proj 𝒜` along `Spec B → Spec A`. -/
theorem isPullback_map :
    IsPullback (Proj.map ψ.toGradedRingHom h.irrelevant_le) (projection ℬ) (projection 𝒜)
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  have := isIso_comparison ψ h
  exact IsPullback.of_iso_pullback ⟨map_projection ψ h⟩ (asIso (comparison ψ h))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end Global

/-! ### Base change along an explicit ring map -/

section Explicit

variable {A B S T : Type u} [CommRing A] [CommRing B] [CommRing S] [CommRing T] [Algebra A S]
  [Algebra B T] (f : A →+* B) (𝒜 : ℕ → Submodule A S) [GradedAlgebra 𝒜]
  (ℬ : ℕ → Submodule B T) [GradedAlgebra ℬ] (φ : 𝒜 →+*ᵍ ℬ)

/-- A graded ring map `φ : 𝒜 → ℬ` exhibits `ℬ` as the base change of `𝒜` along an explicit ring
map `f : A → B` when it lies over `f` and is a base change in every degree. -/
def IsGradedBaseChangeAlong : Prop :=
  letI := f.toAlgebra
  letI : Algebra A T := ((algebraMap B T).comp f).toAlgebra
  haveI : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  ∃ ψ : GradedHomOver 𝒜 ℬ, ψ.toGradedRingHom = φ ∧ ψ.IsBaseChange

variable {f 𝒜 ℬ φ}

theorem IsGradedBaseChangeAlong.irrelevant_le (h : IsGradedBaseChangeAlong f 𝒜 ℬ φ) :
    HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map φ (HomogeneousIdeal.irrelevant 𝒜) := by
  let _ := f.toAlgebra
  let _ : Algebra A T := ((algebraMap B T).comp f).toAlgebra
  have : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨ψ, rfl, hψ⟩ := h
  exact hψ.irrelevant_le

/-- Base change of `Proj` along an explicit ring map. -/
theorem IsGradedBaseChangeAlong.isPullback (h : IsGradedBaseChangeAlong f 𝒜 ℬ φ) :
    IsPullback (Proj.map φ h.irrelevant_le) (projection ℬ) (projection 𝒜)
      (Spec.map (CommRingCat.ofHom f)) := by
  let _ := f.toAlgebra
  let _ : Algebra A T := ((algebraMap B T).comp f).toAlgebra
  have : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨ψ, rfl, hψ⟩ := h
  exact isPullback_map ψ hψ

theorem IsGradedBaseChangeAlong.map_projection (h : IsGradedBaseChangeAlong f 𝒜 ℬ φ) :
    Proj.map φ h.irrelevant_le ≫ projection 𝒜 = projection ℬ ≫ Spec.map (CommRingCat.ofHom f) :=
  h.isPullback.w

end Explicit

end

end GromovWitten.AlgebraicGeometry.ProjBaseChange
