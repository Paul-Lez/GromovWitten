/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.AllDegree

/-!
# Augmentation to Kähler differentials

The counit of the polynomial cotriple induces an `S`-linear map from every
scalar-extended differential module to `Ω[S⁄R]`. These maps agree after all
faces and are surjective. This file does not assert the stronger homology
comparison for the associated chain complex.
-/

open CategoryTheory
open scoped TensorProduct
universe u
namespace GromovWitten.AlgebraicGeometry.CotangentComplex.AllDegree.Cotriple
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
/-- The differential map induced by the actual cotriple augmentation. -/
noncomputable def moduleAugmentation (n : ℕ) : module R S n →ₗ[S] Ω[S⁄R] := by
  let : Algebra (P R S n) S := (augmentationHom R S n).toRingHom.toAlgebra
  let : IsScalarTower R (P R S n) S := IsScalarTower.of_algHom (augmentationHom R S n)
  exact (TensorProduct.isBaseChange (P R S n) Ω[P R S n⁄R] S).lift
    (KaehlerDifferential.map R R (P R S n) S)

/-- The augmentation takes a differential generator to the differential of its image. -/
@[simp]
lemma moduleAugmentation_one_tmul_D (n : ℕ) (x : P R S n) :
    let : Algebra (P R S n) S := (augmentationHom R S n).toRingHom.toAlgebra
    moduleAugmentation R S n (1 ⊗ₜ[P R S n] KaehlerDifferential.D R _ x) =
      KaehlerDifferential.D R S (augmentationHom R S n x) := by
  let : Algebra (P R S n) S := (augmentationHom R S n).toRingHom.toAlgebra
  let : IsScalarTower R (P R S n) S := IsScalarTower.of_algHom (augmentationHom R S n)
  change (TensorProduct.isBaseChange (P R S n) Ω[P R S n⁄R] S).lift _
    ((TensorProduct.mk (P R S n) S Ω[P R S n⁄R] 1)
      (KaehlerDifferential.D R _ x)) = _
  rw [IsBaseChange.lift_eq]
  exact KaehlerDifferential.map_D R R (P R S n) S x

/-- Every face induces the same map to the differential module of the augmented algebra. -/
lemma moduleAugmentation_faceMap (n : ℕ) (i : Fin (n + 2)) :
    (moduleAugmentation R S n).comp (faceMap R S n i) =
      moduleAugmentation R S (n + 1) := by
  let : Algebra (P R S (n + 1)) S :=
    (augmentationHom R S (n + 1)).toRingHom.toAlgebra
  let : Algebra (P R S n) S := (augmentationHom R S n).toRingHom.toAlgebra
  apply CotangentModule.linearMap_ext_of_D (R := R) (A := P R S (n + 1)) (T := S)
  intro x
  change moduleAugmentation R S n
    (faceMap R S n i (1 ⊗ₜ[P R S (n + 1)] KaehlerDifferential.D R _ x)) = _
  rw [faceMap_one_tmul_D, moduleAugmentation_one_tmul_D, moduleAugmentation_one_tmul_D]
  congr 1
  exact AlgHom.congr_fun (face_augmentation R S n i) x

/-- The iterated polynomial counit is surjective, with explicit variable preimages. -/
lemma augmentationHom_surjective (n : ℕ) :
    Function.Surjective (augmentationHom R S n) := by
  induction n with
  | zero =>
      intro s
      refine ⟨MvPolynomial.X s, ?_⟩
      change MvPolynomial.aeval (fun x : S => x) (MvPolynomial.X s) = s
      exact MvPolynomial.aeval_X _ _
  | succ n ih =>
      intro s
      obtain ⟨p, hp⟩ := ih s
      refine ⟨MvPolynomial.X p, ?_⟩
      change augmentationHom R S n
        (MvPolynomial.aeval (fun x : P R S n => x) (MvPolynomial.X p)) = s
      rw [MvPolynomial.aeval_X, hp]

/-- Every differential of the target algebra lifts to a cotriple differential module. -/
lemma moduleAugmentation_surjective (n : ℕ) :
    Function.Surjective (moduleAugmentation R S n) := by
  let : Algebra (P R S n) S := (augmentationHom R S n).toRingHom.toAlgebra
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← KaehlerDifferential.span_range_derivation R S]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  obtain ⟨p, hp⟩ := augmentationHom_surjective R S n s
  refine ⟨1 ⊗ₜ[P R S n] KaehlerDifferential.D R _ p, ?_⟩
  rw [moduleAugmentation_one_tmul_D, hp]
end GromovWitten.AlgebraicGeometry.CotangentComplex.AllDegree.Cotriple
