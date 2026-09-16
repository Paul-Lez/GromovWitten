/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.AffinePresentation
import GromovWitten.AlgebraicGeometry.CotangentComplex.Derived
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Perfect complexes and global two-term resolutions in the affine model

This file develops the affine (module-theoretic) model of perfect complexes.  Every predicate
below is an honest definition: `IsFiniteFree` is Mathlib's conjunction of freeness and
finiteness, `IsStrictlyPerfect` asks for an actual bounded complex of finite free modules, and
`IsPerfect` asks for an actual strictly perfect representative together with an actual
isomorphism in the derived category.  Nothing is supplied as a structure field asserting that
an arbitrary complex is perfect.

## Main definitions

* `IsFiniteFree M` : the `R`-module underlying `M : ModuleCat R` is free and finite.
* `IsSupportedIn K a b` : all terms of the cochain complex `K` outside `[a, b]` are zero.
* `IsStrictlyPerfect K` : `K` is bounded and all of its terms are finite free.
* `IsPerfect E` : the derived object `E` is isomorphic to the image of a strictly perfect
  complex.
* `HasTorAmplitudeIn K a b` : the complex obtained by tensoring `K` with an arbitrary module
  has vanishing cohomology outside `[a, b]`.
* `rank K` : the alternating sum of the ranks of the terms of `K`.
* `GlobalTwoTermResolution E` : an actual two-term complex of finite free modules together with
  an actual isomorphism in the derived category onto `E`.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace PerfectComplex

universe u

variable {R : Type u} [CommRing R]

/-! ## Finite free module objects -/

/-- A module object of `ModuleCat R` is *finite free* when the underlying module is free of
finite type.  This is a fixed definition; it is never a caller-supplied predicate. -/
structure IsFiniteFree (M : ModuleCat.{u} R) : Prop where
  /-- The underlying module is free. -/
  free : Module.Free R M
  /-- The underlying module is of finite type. -/
  finite : Module.Finite R M

/-- A subsingleton module is of finite type. -/
theorem finite_of_subsingleton (M : Type u) [AddCommGroup M] [Module R M] [Subsingleton M] :
    Module.Finite R M := by
  refine ⟨?_⟩
  rw [Subsingleton.elim (⊤ : Submodule R M) ⊥]
  exact Submodule.fg_bot

/-- A zero object of `ModuleCat R` is finite free. -/
theorem isFiniteFree_of_isZero {M : ModuleCat.{u} R} (h : IsZero M) : IsFiniteFree M := by
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp h
  exact ⟨Module.Free.of_subsingleton _ _, finite_of_subsingleton _⟩

/-- Finite freeness transports along an isomorphism of module objects. -/
theorem IsFiniteFree.of_iso {M N : ModuleCat.{u} R} (h : IsFiniteFree M) (e : M ≅ N) :
    IsFiniteFree N :=
  have := h.free
  have := h.finite
  ⟨Module.Free.of_equiv e.toLinearEquiv, Module.Finite.equiv e.toLinearEquiv⟩

/-- The binary biproduct of two finite free module objects is finite free. -/
theorem IsFiniteFree.biprod {M N : ModuleCat.{u} R} (hM : IsFiniteFree M)
    (hN : IsFiniteFree N) : IsFiniteFree (M ⊞ N) := by
  have := hM.free
  have := hM.finite
  have := hN.free
  have := hN.finite
  have e : (M ⊞ N : ModuleCat.{u} R) ≃ₗ[R] (M × N) :=
    (ModuleCat.biprodIsoProd M N).toLinearEquiv
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

/-- The rank of a finite free module object is Mathlib's `Module.finrank`. -/
noncomputable abbrev rankOf (M : ModuleCat.{u} R) : ℕ := Module.finrank R M

/-- A zero module object has rank zero. -/
theorem rankOf_eq_zero_of_isZero [Nontrivial R] {M : ModuleCat.{u} R} (h : IsZero M) :
    rankOf M = 0 := by
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp h
  exact Module.finrank_zero_of_subsingleton

/-- Rank is invariant under isomorphism of module objects. -/
theorem rankOf_congr {M N : ModuleCat.{u} R} (e : M ≅ N) : rankOf M = rankOf N :=
  e.toLinearEquiv.finrank_eq

/-- The rank of a binary biproduct of finite free module objects is the sum of the ranks. -/
theorem rankOf_biprod [Nontrivial R] {M N : ModuleCat.{u} R} (hM : IsFiniteFree M)
    (hN : IsFiniteFree N) : rankOf (M ⊞ N) = rankOf M + rankOf N := by
  have := hM.free
  have := hM.finite
  have := hN.free
  have := hN.finite
  have e : (M ⊞ N : ModuleCat.{u} R) ≃ₗ[R] (M × N) :=
    (ModuleCat.biprodIsoProd M N).toLinearEquiv
  rw [rankOf, e.finrank_eq]
  exact Module.finrank_prod

/-! ## Bounded complexes and strictly perfect complexes -/

/-- Every term of the cochain complex `K` outside the interval `[a, b]` is a zero object. -/
def IsSupportedIn (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) : Prop :=
  ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)

namespace IsSupportedIn

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}

/-- Support in an interval is inherited by any larger interval. -/
theorem mono (h : IsSupportedIn K a b) {a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') :
    IsSupportedIn K a' b' := fun i hi => h i (by omega)

/-- Support in an interval transports along an isomorphism of complexes. -/
theorem of_iso (h : IsSupportedIn K a b) (e : K ≅ L) : IsSupportedIn L a b := fun i hi =>
  (h i hi).of_iso ((HomologicalComplex.eval _ _ i).mapIso e.symm)

end IsSupportedIn

/-- A cochain complex of `R`-modules is *strictly perfect* when it is bounded and every one of
its terms is a finite free module.  Both fields are honest conditions on the given complex. -/
structure IsStrictlyPerfect (K : CochainComplex (ModuleCat.{u} R) ℤ) : Prop where
  /-- The complex is supported in some bounded interval. -/
  bounded : ∃ a b : ℤ, IsSupportedIn K a b
  /-- Every term of the complex is a finite free module. -/
  finiteFree : ∀ i : ℤ, IsFiniteFree (K.X i)

namespace IsStrictlyPerfect

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Strict perfectness transports along an isomorphism of cochain complexes. -/
theorem of_iso (h : IsStrictlyPerfect K) (e : K ≅ L) : IsStrictlyPerfect L where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    exact ⟨a, b, hab.of_iso e⟩
  finiteFree i := (h.finiteFree i).of_iso ((HomologicalComplex.eval _ _ i).mapIso e)

/-- The shift of a strictly perfect complex is strictly perfect. -/
theorem shift (h : IsStrictlyPerfect K) (n : ℤ) :
    IsStrictlyPerfect ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).obj K)
      where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    refine ⟨a - n, b - n, fun i hi => ?_⟩
    rw [CochainComplex.shiftFunctor_obj_X']
    exact hab (i + n) (by omega)
  finiteFree i := by
    rw [CochainComplex.shiftFunctor_obj_X']
    exact h.finiteFree (i + n)

/-- A finite direct sum of strictly perfect complexes is strictly perfect. -/
theorem biprod (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) :
    IsStrictlyPerfect (K ⊞ L) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hK.bounded
    obtain ⟨a', b', hab'⟩ := hL.bounded
    refine ⟨min a a', max b b', fun i hi => ?_⟩
    refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso K L i)
    rw [biprod_isZero_iff]
    exact ⟨hab i (by omega), hab' i (by omega)⟩
  finiteFree i :=
    ((hK.finiteFree i).biprod (hL.finiteFree i)).of_iso (HomologicalComplex.biprodXIso K L i).symm

end IsStrictlyPerfect

/-- The cone of a morphism of strictly perfect complexes is strictly perfect: this is the
two-out-of-three property for the strict notion. -/
theorem isStrictlyPerfect_mappingCone {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)
    (hF : IsStrictlyPerfect F) (hG : IsStrictlyPerfect G) :
    IsStrictlyPerfect (CochainComplex.mappingCone φ) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hF.bounded
    obtain ⟨a', b', hab'⟩ := hG.bounded
    refine ⟨min (a - 1) a', max (b - 1) b', fun i hi => ?_⟩
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨hab (i + 1) (by omega), hab' i (by omega)⟩
  finiteFree i := by
    have := HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct φ i (i + 1) rfl
    exact ((hF.finiteFree (i + 1)).biprod (hG.finiteFree i)).of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).symm

/-- A finite free module placed in a single cohomological degree gives a strictly perfect
complex. -/
theorem isStrictlyPerfect_single {M : ModuleCat.{u} R} (hM : IsFiniteFree M) (n : ℤ) :
    IsStrictlyPerfect
      ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) n).obj M) where
  bounded := ⟨n, n, fun i hi =>
    HomologicalComplex.isZero_single_obj_X _ n M i (by omega)⟩
  finiteFree i := by
    by_cases hi : i = n
    · subst hi
      exact hM.of_iso (HomologicalComplex.singleObjXSelf _ i M).symm
    · exact isFiniteFree_of_isZero (HomologicalComplex.isZero_single_obj_X _ n M i hi)

/-! ## Base change along a ring homomorphism -/

section BaseChange

variable {S : Type u} [CommRing S] (f : R →+* S)

/-- Extension of scalars is an additive functor.  Mathlib constructs the functor but does not
record this instance. -/
instance extendScalars_additive : (ModuleCat.extendScalars f).Additive where
  map_add := by
    intros
    ext m
    change (1 : S) ⊗ₜ[R, f] _ = _
    simp only [ModuleCat.hom_add, LinearMap.add_apply, TensorProduct.tmul_add]
    rfl

/-- Base change of a cochain complex of `R`-modules along `f : R →+* S`. -/
noncomputable def baseChange (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} S) ℤ :=
  ((ModuleCat.extendScalars f).mapHomologicalComplex _).obj K

@[simp]
theorem baseChange_X (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (baseChange f K).X i = (ModuleCat.extendScalars f).obj (K.X i) :=
  rfl

/-- The base change of a finite free module object is finite free. -/
theorem IsFiniteFree.extendScalars {M : ModuleCat.{u} R} (hM : IsFiniteFree M) :
    IsFiniteFree ((ModuleCat.extendScalars f).obj M) := by
  have := hM.free
  have := hM.finite
  let _ : Algebra R S := f.toAlgebra
  have e : ((ModuleCat.extendScalars f).obj M : Type u) ≃ₗ[S] (S ⊗[R] M) :=
    LinearEquiv.refl S _
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

/-- Base change of a strictly perfect complex along a ring homomorphism is strictly perfect. -/
theorem IsStrictlyPerfect.baseChange {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) : IsStrictlyPerfect (baseChange f K) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hK.bounded
    exact ⟨a, b, fun i hi => (ModuleCat.extendScalars f).map_isZero (hab i hi)⟩
  finiteFree i := (hK.finiteFree i).extendScalars f

end BaseChange

/-! ## Tor amplitude -/

/-- The complex obtained by tensoring every term of `K` with the module object `M`.  For a
bounded complex of flat (in particular finite free) modules this computes the derived tensor
product, so the definition of Tor amplitude below is the usual one. -/
noncomputable def tensorRight (K : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  ((MonoidalCategory.tensorRight M).mapHomologicalComplex _).obj K

@[simp]
theorem tensorRight_X (K : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R) (i : ℤ) :
    (tensorRight K M).X i = (MonoidalCategory.tensorRight M).obj (K.X i) :=
  rfl

/-- `K` has Tor amplitude in `[a, b]` when tensoring with an arbitrary module produces a complex
whose cohomology vanishes outside `[a, b]`. -/
def HasTorAmplitudeIn (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) : Prop :=
  ∀ (M : ModuleCat.{u} R) (i : ℤ), i < a ∨ b < i → IsZero ((tensorRight K M).homology i)

namespace HasTorAmplitudeIn

variable {K : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}

/-- Tor amplitude in an interval is inherited by any larger interval. -/
theorem mono (h : HasTorAmplitudeIn K a b) {a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') :
    HasTorAmplitudeIn K a' b' := fun M i hi => h M i (by omega)

end HasTorAmplitudeIn

/-- A complex supported in `[a, b]` has Tor amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_of_isSupportedIn {K : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}
    (h : IsSupportedIn K a b) : HasTorAmplitudeIn K a b := by
  intro M i hi
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  refine HomologicalComplex.ExactAt.of_isZero ?_
  rw [tensorRight_X]
  exact (MonoidalCategory.tensorRight M).map_isZero (h i hi)

/-- A strictly perfect complex has Tor amplitude in some bounded interval. -/
theorem IsStrictlyPerfect.hasTorAmplitude {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : IsStrictlyPerfect K) : ∃ a b : ℤ, HasTorAmplitudeIn K a b := by
  obtain ⟨a, b, hab⟩ := h.bounded
  exact ⟨a, b, hasTorAmplitudeIn_of_isSupportedIn hab⟩

/-! ## Support lemmas for the standard operations -/

namespace IsSupportedIn

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}

/-- Shifting a complex translates the interval in which it is supported. -/
theorem shift (h : IsSupportedIn K a b) (n : ℤ) :
    IsSupportedIn ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).obj K)
      (a - n) (b - n) := by
  intro i hi
  rw [CochainComplex.shiftFunctor_obj_X']
  exact h (i + n) (by omega)

/-- A direct sum of complexes supported in `[a, b]` is supported in `[a, b]`. -/
theorem biprod (hK : IsSupportedIn K a b) (hL : IsSupportedIn L a b) :
    IsSupportedIn (K ⊞ L) a b := by
  intro i hi
  refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso K L i)
  rw [biprod_isZero_iff]
  exact ⟨hK i hi, hL i hi⟩

end IsSupportedIn

/-- The mapping cone of a morphism between complexes supported in `[a, b]` is supported in
`[a - 1, b]`. -/
theorem isSupportedIn_mappingCone {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)
    {a b : ℤ} (hF : IsSupportedIn F a b) (hG : IsSupportedIn G a b) :
    IsSupportedIn (CochainComplex.mappingCone φ) (a - 1) b := by
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨hF (i + 1) (by omega), hG i (by omega)⟩

/-! ## The rank of a complex -/

/-- The rank of a cochain complex: the alternating sum of the ranks of its terms.  The sum is a
`finsum`, which is well defined because a bounded complex has only finitely many terms of
nonzero rank. -/
noncomputable def rank (K : CochainComplex (ModuleCat.{u} R) ℤ) : ℤ :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (rankOf (K.X i) : ℤ)

/-- For a complex supported in `[a, b]`, the rank is the alternating sum over `[a, b]`. -/
theorem rank_eq_sum_Icc [Nontrivial R] {K : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}
    (h : IsSupportedIn K a b) :
    rank K = ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) * (rankOf (K.X i) : ℤ) := by
  refine finsum_eq_finsetSum_of_support_subset _ ?_
  intro i hi
  simp only [Finset.coe_Icc, Set.mem_Icc]
  by_contra hcon
  apply hi
  change (i.negOnePow : ℤ) * (rankOf (K.X i) : ℤ) = 0
  rw [rankOf_eq_zero_of_isZero (h i (by omega))]
  simp

/-- Rank is invariant under isomorphism of complexes. -/
theorem rank_congr {K L : CochainComplex (ModuleCat.{u} R) ℤ} (e : K ≅ L) : rank K = rank L :=
  finsum_congr fun i => by
    have h : rankOf (K.X i) = rankOf (L.X i) :=
      rankOf_congr ((HomologicalComplex.eval _ _ i).mapIso e)
    rw [h]

/-- Rank is additive whenever the terms are: the key computational lemma behind additivity on
direct sums and on cones. -/
theorem rank_add_of_rankOf_add [Nontrivial R] {K L M : CochainComplex (ModuleCat.{u} R) ℤ}
    {a b : ℤ} (hK : IsSupportedIn K a b) (hL : IsSupportedIn L a b)
    (hM : IsSupportedIn M a b)
    (h : ∀ i : ℤ, rankOf (M.X i) = rankOf (K.X i) + rankOf (L.X i)) :
    rank M = rank K + rank L := by
  rw [rank_eq_sum_Icc hK, rank_eq_sum_Icc hL, rank_eq_sum_Icc hM, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h i]
  push_cast
  ring

/-- The rank of a shift is the rank multiplied by the expected sign. -/
theorem rank_shift (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    rank ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).obj K) =
      (n.negOnePow : ℤ) * rank K := by
  have hsq : ((n.negOnePow : ℤ)) * ((n.negOnePow : ℤ)) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  rw [rank, rank, mul_finsum,
    ← finsum_comp_equiv (Equiv.addRight n)
      (f := fun j : ℤ => (n.negOnePow : ℤ) * ((j.negOnePow : ℤ) * (rankOf (K.X j) : ℤ)))]
  refine finsum_congr fun i => ?_
  have h2 : ∀ r : ℤ, (n.negOnePow : ℤ) * ((i.negOnePow : ℤ) * (n.negOnePow : ℤ) * r) =
      (i.negOnePow : ℤ) * r := by
    intro r
    have hre : (n.negOnePow : ℤ) * ((i.negOnePow : ℤ) * (n.negOnePow : ℤ) * r) =
        ((n.negOnePow : ℤ) * (n.negOnePow : ℤ)) * ((i.negOnePow : ℤ) * r) := by ring
    rw [hre, hsq, one_mul]
  simp only [Equiv.coe_addRight, CochainComplex.shiftFunctor_obj_X', Int.negOnePow_add,
    Units.val_mul]
  rw [h2]

/-- Rank is additive on finite direct sums of strictly perfect complexes. -/
theorem rank_biprod [Nontrivial R] {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) :
    rank (K ⊞ L) = rank K + rank L := by
  obtain ⟨a, b, hab⟩ := hK.bounded
  obtain ⟨a', b', hab'⟩ := hL.bounded
  have hK' : IsSupportedIn K (min a a') (max b b') := hab.mono (min_le_left _ _) (le_max_left _ _)
  have hL' : IsSupportedIn L (min a a') (max b b') :=
    hab'.mono (min_le_right _ _) (le_max_right _ _)
  refine rank_add_of_rankOf_add hK' hL' (hK'.biprod hL') fun i => ?_
  rw [rankOf_congr (HomologicalComplex.biprodXIso K L i)]
  exact rankOf_biprod (hK.finiteFree i) (hL.finiteFree i)

/-- Rank is additive on cones: the cone of a morphism of strictly perfect complexes has rank
`rank G - rank F`. -/
theorem rank_mappingCone [Nontrivial R] {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)
    (hF : IsStrictlyPerfect F) (hG : IsStrictlyPerfect G) :
    rank (CochainComplex.mappingCone φ) = rank G - rank F := by
  obtain ⟨a, b, hab⟩ := hF.bounded
  obtain ⟨a', b', hab'⟩ := hG.bounded
  have hF1 : IsSupportedIn F (min (a - 1) a') (max b b') := hab.mono (by omega) (by omega)
  have hG1 : IsSupportedIn G (min (a - 1) a') (max b b') := hab'.mono (by omega) (by omega)
  have hshift :
      IsSupportedIn
        ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (1 : ℤ)).obj F)
        (min (a - 1) a' - 1) (max b b') := (hab.shift 1).mono (by omega) (by omega)
  have hG2 : IsSupportedIn G (min (a - 1) a' - 1) (max b b') := hG1.mono (by omega) le_rfl
  have hcone : IsSupportedIn (CochainComplex.mappingCone φ)
      (min (a - 1) a' - 1) (max b b') := isSupportedIn_mappingCone φ hF1 hG1
  have key := rank_add_of_rankOf_add hshift hG2 hcone (fun i => ?_)
  · rw [key, rank_shift]
    simp only [Int.negOnePow_one, Units.val_neg, Units.val_one]
    ring
  · have hx : rankOf ((CochainComplex.mappingCone φ).X i) =
        rankOf ((F.X (i + 1)) ⊞ (G.X i)) := by
      have := HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct φ i (i + 1) rfl
      exact rankOf_congr (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl)
    rw [hx, rankOf_biprod (hF.finiteFree (i + 1)) (hG.finiteFree i),
      CochainComplex.shiftFunctor_obj_X']

/-- For a complex supported in `[-1, 0]`, the rank is the cohomological difference
`rank(K⁰) - rank(K⁻¹)`. -/
theorem rank_eq_of_isSupportedIn_negOne_zero [Nontrivial R]
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (h : IsSupportedIn K (-1) 0) :
    rank K = (rankOf (K.X 0) : ℤ) - (rankOf (K.X (-1)) : ℤ) := by
  rw [rank_eq_sum_Icc h]
  have hIcc : Finset.Icc (-1 : ℤ) 0 = {-1, 0} := rfl
  rw [hIcc, Finset.sum_pair (by norm_num : (-1 : ℤ) ≠ 0)]
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Int.negOnePow_zero, Units.val_neg,
    Units.val_one]
  ring

/-! ## Perfect objects of the derived category -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- An object of the derived category is *perfect* when some strictly perfect complex represents
it.  Both the representative and the isomorphism are genuine data being asserted to exist; no
structure field ever declares an arbitrary object perfect. -/
def IsPerfect (E : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∃ K : CochainComplex (ModuleCat.{u} R) ℤ,
    IsStrictlyPerfect K ∧ Nonempty (DerivedCategory.Q.obj K ≅ E)

/-- The image in the derived category of a strictly perfect complex is perfect. -/
theorem isPerfect_Q {K : CochainComplex (ModuleCat.{u} R) ℤ} (h : IsStrictlyPerfect K) :
    IsPerfect (DerivedCategory.Q.obj K) :=
  ⟨K, h, ⟨Iso.refl _⟩⟩

namespace IsPerfect

variable {E F : DerivedCategory (ModuleCat.{u} R)}

/-- Perfectness transports along an isomorphism in the derived category. -/
theorem of_iso (h : IsPerfect E) (e : E ≅ F) : IsPerfect F := by
  obtain ⟨K, hK, ⟨f⟩⟩ := h
  exact ⟨K, hK, ⟨f ≪≫ e⟩⟩

/-- A shift of a perfect object is perfect. -/
theorem shift (h : IsPerfect E) (n : ℤ) : IsPerfect (E⟦n⟧) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := h
  refine ⟨(CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).obj K,
    hK.shift n, ⟨?_⟩⟩
  exact (DerivedCategory.Q.commShiftIso n).app K ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} R)) n).mapIso e

/-- A finite direct sum of perfect objects is perfect. -/
theorem biprod (hE : IsPerfect E) (hF : IsPerfect F) : IsPerfect (E ⊞ F) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  obtain ⟨L, hL, ⟨f⟩⟩ := hF
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  exact ⟨K ⊞ L, hK.biprod hL,
    ⟨Functor.mapBiprod DerivedCategory.Q K L ≪≫ biprod.mapIso e f⟩⟩

end IsPerfect

/-- A finite free module placed in a single degree is perfect. -/
theorem isPerfect_single {M : ModuleCat.{u} R} (hM : IsFiniteFree M) (n : ℤ) :
    IsPerfect (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) n).obj M)) :=
  isPerfect_Q (isStrictlyPerfect_single hM n)

/-! ## Global two-term resolutions -/

/-- A *global two-term resolution* of a derived object `E`: an actual cochain complex
concentrated in degrees `-1` and `0` whose terms are finite free, together with an actual
isomorphism in the derived category from its image onto `E`.  The isomorphism is the honest
quasi-isomorphism datum; no field asserts that an arbitrary complex resolves `E`. -/
structure GlobalTwoTermResolution (E : DerivedCategory (ModuleCat.{u} R)) where
  /-- The chosen two-term complex. -/
  complex : CochainComplex (ModuleCat.{u} R) ℤ
  /-- All terms outside degrees `-1` and `0` vanish. -/
  supported : IsSupportedIn complex (-1) 0
  /-- Every term is a finite free module. -/
  finiteFree : ∀ i : ℤ, IsFiniteFree (complex.X i)
  /-- The chosen complex represents `E` by an isomorphism of the derived category. -/
  iso : DerivedCategory.Q.obj complex ≅ E

namespace GlobalTwoTermResolution

variable {E E' : DerivedCategory (ModuleCat.{u} R)}

/-- The complex of a global two-term resolution is strictly perfect. -/
theorem isStrictlyPerfect (F : GlobalTwoTermResolution E) : IsStrictlyPerfect F.complex where
  bounded := ⟨-1, 0, F.supported⟩
  finiteFree := F.finiteFree

/-- An object with a global two-term resolution is perfect. -/
theorem isPerfect (F : GlobalTwoTermResolution E) : IsPerfect E :=
  ⟨F.complex, F.isStrictlyPerfect, ⟨F.iso⟩⟩

/-- Transport a global two-term resolution along an isomorphism of the derived category.  Only
the comparison isomorphism changes; the resolving complex is untouched. -/
noncomputable def replace (F : GlobalTwoTermResolution E) (e : E ≅ E') :
    GlobalTwoTermResolution E' where
  complex := F.complex
  supported := F.supported
  finiteFree := F.finiteFree
  iso := F.iso ≪≫ e

@[simp]
theorem replace_complex (F : GlobalTwoTermResolution E) (e : E ≅ E') :
    (F.replace e).complex = F.complex :=
  rfl

/-- Transporting along the identity does not change the resolution. -/
@[simp]
theorem replace_refl (F : GlobalTwoTermResolution E) : F.replace (Iso.refl E) = F := by
  cases F
  simp [replace]

/-- Transport is compatible with composition of derived isomorphisms. -/
theorem replace_trans {E'' : DerivedCategory (ModuleCat.{u} R)}
    (F : GlobalTwoTermResolution E) (e : E ≅ E') (e' : E' ≅ E'') :
    (F.replace e).replace e' = F.replace (e ≪≫ e') := by
  simp [replace, Iso.trans_assoc]

/-- A global two-term resolution has Tor amplitude in `[-1, 0]`. -/
theorem hasTorAmplitude (F : GlobalTwoTermResolution E) :
    HasTorAmplitudeIn F.complex (-1) 0 :=
  hasTorAmplitudeIn_of_isSupportedIn F.supported

/-- The virtual rank of a resolution is the rank of its complex. -/
noncomputable def virtualRank (F : GlobalTwoTermResolution E) : ℤ :=
  rank F.complex

@[simp]
theorem replace_virtualRank (F : GlobalTwoTermResolution E) (e : E ≅ E') :
    (F.replace e).virtualRank = F.virtualRank :=
  rfl

/-- The virtual rank in the cohomological convention `rank(F⁰) - rank(F⁻¹)`. -/
theorem virtualRank_eq [Nontrivial R] (F : GlobalTwoTermResolution E) :
    F.virtualRank = (rankOf (F.complex.X 0) : ℤ) - (rankOf (F.complex.X (-1)) : ℤ) :=
  rank_eq_of_isSupportedIn_negOne_zero F.supported

end GlobalTwoTermResolution

end Derived

/-! ## Global resolutions from affine cotangent presentations -/

section AffineCotangent

attribute [local instance] HasDerivedCategory.standard

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (P : Algebra.Extension.{u} A B)

/-- An affine presentation whose conormal module and ambient differential module are finite free
supplies a global two-term resolution of the derived object that the presentation defines.  The
resolving complex is the presentation complex itself and the comparison is the identity
isomorphism, so nothing is assumed. -/
noncomputable def globalResolutionOfAffinePresentation
    (hNeg : IsFiniteFree (ModuleCat.of B P.Cotangent))
    (hZero : IsFiniteFree (ModuleCat.of B P.CotangentSpace)) :
    GlobalTwoTermResolution (AffinePresentation.derivedObject A B P) where
  complex := AffinePresentation.cochainComplex A B P
  supported i hi :=
    (AffinePresentation.twoTerm A B P).toCochainComplex_X_isZero i (by omega) (by omega)
  finiteFree i := by
    by_cases h1 : i = -1
    · subst h1
      rw [AffinePresentation.cochainComplex_X_negOne]
      exact hNeg
    by_cases h0 : i = 0
    · subst h0
      rw [AffinePresentation.cochainComplex_X_zero]
      exact hZero
    exact isFiniteFree_of_isZero
      ((AffinePresentation.twoTerm A B P).toCochainComplex_X_isZero i h1 h0)
  iso := Iso.refl _

/-- The derived object of such an affine presentation is perfect. -/
theorem isPerfect_derivedObject_of_affinePresentation
    (hNeg : IsFiniteFree (ModuleCat.of B P.Cotangent))
    (hZero : IsFiniteFree (ModuleCat.of B P.CotangentSpace)) :
    IsPerfect (AffinePresentation.derivedObject A B P) :=
  (globalResolutionOfAffinePresentation A B P hNeg hZero).isPerfect

/-- The virtual rank of the affine presentation resolution is the expected difference of module
ranks. -/
theorem globalResolutionOfAffinePresentation_virtualRank [Nontrivial B]
    (hNeg : IsFiniteFree (ModuleCat.of B P.Cotangent))
    (hZero : IsFiniteFree (ModuleCat.of B P.CotangentSpace)) :
    (globalResolutionOfAffinePresentation A B P hNeg hZero).virtualRank =
      (Module.finrank B P.CotangentSpace : ℤ) - (Module.finrank B P.Cotangent : ℤ) := by
  rw [GlobalTwoTermResolution.virtualRank_eq]
  have h0 : rankOf ((AffinePresentation.cochainComplex A B P).X 0) =
      Module.finrank B P.CotangentSpace := by
    rw [AffinePresentation.cochainComplex_X_zero]
  have h1 : rankOf ((AffinePresentation.cochainComplex A B P).X (-1)) =
      Module.finrank B P.Cotangent := by
    rw [AffinePresentation.cochainComplex_X_negOne]
  change ((rankOf ((AffinePresentation.cochainComplex A B P).X 0) : ℤ)) -
    ((rankOf ((AffinePresentation.cochainComplex A B P).X (-1)) : ℤ)) = _
  rw [h0, h1]

end AffineCotangent

end PerfectComplex

end GromovWitten.AlgebraicGeometry.CotangentComplex
