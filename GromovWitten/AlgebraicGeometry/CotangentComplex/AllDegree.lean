/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.SimplicialResolution
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The polynomial cotangent terms of the cotriple resolution

For a commutative square of actual `R`-algebra maps, this file constructs the
induced map between the scalar-extended modules of Kähler differentials.  The
construction uses the universal derivation and the tensor universal property.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AllDegree

noncomputable section

namespace CotangentModule

variable (R A B T : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing T]
  [Algebra R A] [Algebra R B] [Algebra R T]

/-- The scalar-extended relative differential module associated with an actual
`R`-algebra map `a : A → T`. -/
abbrev term (a : A →ₐ[R] T) : Type u :=
  letI : Algebra A T := a.toRingHom.toAlgebra
  T ⊗[A] Ω[A⁄R]

/-- The linearized map on Kähler differentials for a commutative square. -/
noncomputable def linearizedMap
    (f : A →ₐ[R] B) (a : A →ₐ[R] T) (b : B →ₐ[R] T)
    (h : b.comp f = a) : term R A T a →ₗ[T] term R B T b := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra B T := b.toRingHom.toAlgebra
  let : Algebra A T := a.toRingHom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algHom f
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq
    (fun x => (AlgHom.congr_fun h x).symm)
  exact (TensorProduct.isBaseChange A Ω[A⁄R] T).lift
    (((TensorProduct.mk B T Ω[B⁄R] 1).restrictScalars A).comp
      (KaehlerDifferential.map R R A B))

@[simp]
theorem linearizedMap_one_tmul_D
    (f : A →ₐ[R] B) (a : A →ₐ[R] T) (b : B →ₐ[R] T)
    (h : b.comp f = a) (x : A) :
    letI : Algebra A T := a.toRingHom.toAlgebra
    letI : Algebra B T := b.toRingHom.toAlgebra
    linearizedMap R A B T f a b h
        (1 ⊗ₜ[A] KaehlerDifferential.D R A x) =
      1 ⊗ₜ[B] KaehlerDifferential.D R B (f x) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra B T := b.toRingHom.toAlgebra
  let : Algebra A T := a.toRingHom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algHom f
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq
    (fun x => (AlgHom.congr_fun h x).symm)
  change (TensorProduct.isBaseChange A Ω[A⁄R] T).lift _
    ((TensorProduct.mk A T Ω[A⁄R] 1) (KaehlerDifferential.D R A x)) = _
  rw [IsBaseChange.lift_eq]
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    KaehlerDifferential.map_D, TensorProduct.mk_apply,
    RingHom.algebraMap_toAlgebra]
  rfl

omit [Algebra R T] in
theorem linearMap_ext_of_D
    [Algebra A T] [AddCommGroup N] [Module T N]
    (u v : T ⊗[A] Ω[A⁄R] →ₗ[T] N)
    (h : ∀ x : A,
      u (1 ⊗ₜ[A] KaehlerDifferential.D R A x) =
        v (1 ⊗ₜ[A] KaehlerDifferential.D R A x)) :
    u = v := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul t w =>
      have hw : u (1 ⊗ₜ[A] w) = v (1 ⊗ₜ[A] w) := by
        have hw : w ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
          rw [KaehlerDifferential.span_range_derivation]
          trivial
        induction hw using Submodule.span_induction with
        | mem x hx => obtain ⟨x, rfl⟩ := hx; exact h x
        | zero => simp
        | add x y _ _ hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
        | smul a x _ hx =>
          have hs : (1 : T) ⊗ₜ[A] (a • x) =
              algebraMap A T a • ((1 : T) ⊗ₜ[A] x) := by
            simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul,
              mul_one, Algebra.smul_def]
          rw [hs, map_smul, map_smul, hx]
      have ht : t ⊗ₜ[A] w = t • ((1 : T) ⊗ₜ[A] w) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, map_smul, map_smul, hw]

end CotangentModule

/-! ## The actual cotriple terms and face maps -/

namespace Cotriple

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

abbrev G : Comonad (CommAlgCat.{u} R) := SimplicialResolution.comonad R

/-- The `(n+1)`st polynomial algebra in the cotriple resolution of `S`. -/
abbrev P (n : ℕ) : CommAlgCat.{u} R :=
  (SimplicialResolution.power (G R) (n + 1)).obj (CommAlgCat.of R S)

/-- The iterated counit augmentation of the cotriple resolution. -/
abbrev augmentation (n : ℕ) : P R S n ⟶ CommAlgCat.of R S :=
  SimplicialResolution.augmentationPower (G R) n (CommAlgCat.of R S)

abbrev augmentationHom (n : ℕ) : (P R S n : Type u) →ₐ[R] S :=
  (augmentation R S n).hom

/-- The scalar-extended differential module in simplicial degree `n`. -/
abbrev module (n : ℕ) : Type u :=
  CotangentModule.term R (P R S n) S (augmentationHom R S n)

theorem face_augmentation (n : ℕ) (i : Fin (n + 2)) :
    (augmentationHom R S n).comp
        (SimplicialResolution.facePower (G R) (n + 1) i
          (CommAlgCat.of R S)).hom = augmentationHom R S (n + 1) := by
  simpa only [CommAlgCat.hom_comp, augmentationHom, augmentation, P] using
    congrArg (fun q : (SimplicialResolution.power (G R) (n + 2)).obj
        (CommAlgCat.of R S) ⟶ CommAlgCat.of R S => q.hom)
      (SimplicialResolution.facePower_augmentationPower (G R) n i
        (CommAlgCat.of R S))

/-- The actual `S`-linear map induced by the `i`th algebra face. -/
noncomputable def faceMap (n : ℕ) (i : Fin (n + 2)) :
    module R S (n + 1) →ₗ[S] module R S n :=
  CotangentModule.linearizedMap R (P R S (n + 1)) (P R S n) S
    (SimplicialResolution.facePower (G R) (n + 1) i (CommAlgCat.of R S)).hom
    (augmentationHom R S (n + 1)) (augmentationHom R S n) (face_augmentation R S n i)

@[simp]
theorem faceMap_one_tmul_D (n : ℕ) (i : Fin (n + 2)) (x : P R S (n + 1)) :
    let : Algebra (P R S (n + 1)) S :=
      (augmentationHom R S (n + 1)).toRingHom.toAlgebra
    let : Algebra (P R S n) S := (augmentationHom R S n).toRingHom.toAlgebra
    faceMap R S n i (1 ⊗ₜ[P R S (n + 1)] KaehlerDifferential.D R _ x) =
      1 ⊗ₜ[P R S n] KaehlerDifferential.D R _
        ((SimplicialResolution.facePower (G R) (n + 1) i
      (CommAlgCat.of R S)).hom x) := by
  let : Algebra (P R S (n + 1)) S :=
    (augmentationHom R S (n + 1)).toRingHom.toAlgebra
  let : Algebra (P R S n) S := (augmentationHom R S n).toRingHom.toAlgebra
  exact CotangentModule.linearizedMap_one_tmul_D R (P R S (n + 1)) (P R S n) S
    (SimplicialResolution.facePower (G R) (n + 1) i (CommAlgCat.of R S)).hom
    (augmentationHom R S (n + 1)) (augmentationHom R S n) (face_augmentation R S n i) x

theorem faceMap_comp_faceMap (n : ℕ) (i j : Fin (n + 2)) (hij : i ≤ j) :
    let : Algebra (P R S (n + 2)) S :=
      (augmentationHom R S (n + 2)).toRingHom.toAlgebra
    let : Algebra (P R S (n + 1)) S :=
      (augmentationHom R S (n + 1)).toRingHom.toAlgebra
    let : Algebra (P R S n) S := (augmentationHom R S n).toRingHom.toAlgebra
    (faceMap R S n i).comp (faceMap R S (n + 1) j.succ) =
      (faceMap R S n j).comp (faceMap R S (n + 1) i.castSucc) := by
  let : Algebra (P R S (n + 2)) S :=
    (augmentationHom R S (n + 2)).toRingHom.toAlgebra
  let : Algebra (P R S (n + 1)) S :=
    (augmentationHom R S (n + 1)).toRingHom.toAlgebra
  let : Algebra (P R S n) S := (augmentationHom R S n).toRingHom.toAlgebra
  dsimp only
  refine CotangentModule.linearMap_ext_of_D (R := R) (A := P R S (n + 2))
    (T := S) (N := module R S n)
    (LinearMap.comp (faceMap R S n i) (faceMap R S (n + 1) j.succ))
    (LinearMap.comp (faceMap R S n j) (faceMap R S (n + 1) i.castSucc)) ?_
  intro x
  change faceMap R S n i
      (faceMap R S (n + 1) j.succ
        (1 ⊗ₜ[P R S (n + 2)] KaehlerDifferential.D R _ x)) =
    faceMap R S n j
      (faceMap R S (n + 1) i.castSucc
        (1 ⊗ₜ[P R S (n + 2)] KaehlerDifferential.D R _ x))
  rw [faceMap_one_tmul_D, faceMap_one_tmul_D,
    faceMap_one_tmul_D, faceMap_one_tmul_D]
  congr 2
  exact congrArg (fun q : P R S (n + 2) ⟶ P R S n => q.hom x)
    (SimplicialResolution.facePower_facePower (G R) (n + 1) i j hij
      (CommAlgCat.of R S))

end Cotriple

end
end AllDegree
end GromovWitten.AlgebraicGeometry.CotangentComplex
