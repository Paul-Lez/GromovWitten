/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Scalar extension along an algebra map

`ModuleCat.extendScalars` uses the module structure induced by a ring homomorphism. Transport
along `toAlgebra_algebraMap` identifies it with the tensor product using an existing algebra
structure; the comparison sends each pure tensor to the same pure tensor.
-/

open CategoryTheory TensorProduct
open scoped ChangeOfRings
noncomputable section
universe u
namespace ModuleCat
variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension along an algebra map is the usual tensor product. -/
def extendScalarsAlgebraIso (N : ModuleCat.{u} A) :
    (extendScalars (algebraMap A C)).obj N ≅ ModuleCat.of C (C ⊗[A] N) := by
  let obj : Algebra A C → ModuleCat C := fun a =>
    letI := a
    ModuleCat.of C (C ⊗[A] N)
  exact eqToIso (congrArg obj (toAlgebra_algebraMap (R := A) (S := C)))

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma extendScalarsAlgebraIso_hom_tmul (N : ModuleCat.{u} A) (c : C) (n : N) :
    (extendScalarsAlgebraIso N).hom (c ⊗ₜ[A, algebraMap A C] n) = c ⊗ₜ[A] n := by
  let obj : Algebra A C → ModuleCat C := fun a =>
    letI := a
    ModuleCat.of C (C ⊗[A] N)
  let elem (a : Algebra A C) : obj a := by
    letI := a
    exact c ⊗ₜ[A] n
  have h (a b : Algebra A C) (e : a = b) :
      (eqToHom (congrArg obj e)) (elem a) = elem b := by
    subst b
    rfl
  exact h _ _ (toAlgebra_algebraMap (R := A) (S := C))
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma extendScalarsAlgebraIso_inv_tmul (N : ModuleCat.{u} A) (c : C) (n : N) :
    (extendScalarsAlgebraIso N).inv (c ⊗ₜ[A] n) = c ⊗ₜ[A, algebraMap A C] n := by
  apply (ConcreteCategory.bijective_of_isIso (extendScalarsAlgebraIso N).hom).1
  simp only [Iso.inv_hom_id_apply]
  exact (extendScalarsAlgebraIso_hom_tmul (C := C) N c n).symm

set_option backward.isDefEq.respectTransparency false in
/-- Extension of scalars commutes with a map under the tensor comparison isomorphisms. -/
lemma extendScalarsAlgebraIso_naturality {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (extendScalars (algebraMap A C)).map f ≫ (extendScalarsAlgebraIso N).hom =
      (extendScalarsAlgebraIso M).hom ≫
        ModuleCat.ofHom (AlgebraTensorModule.lTensor C C f.hom) := by
  apply ExtendScalars.hom_ext
  intro n
  change (extendScalarsAlgebraIso N).hom
      ((extendScalars (algebraMap A C)).map f
        ((1 : C) ⊗ₜ[A, algebraMap A C] n)) =
    (AlgebraTensorModule.lTensor C C f.hom)
      ((extendScalarsAlgebraIso M).hom ((1 : C) ⊗ₜ[A, algebraMap A C] n))
  rw [ExtendScalars.map_tmul]
  exact (extendScalarsAlgebraIso_hom_tmul (C := C) N 1 (f n)).trans
    ((congrArg (AlgebraTensorModule.lTensor C C f.hom)
      (extendScalarsAlgebraIso_hom_tmul (C := C) M 1 n)).trans
        (AlgebraTensorModule.lTensor_tmul f.hom (1 : C) n)).symm
set_option backward.isDefEq.respectTransparency false in
/-- Restriction along an algebra map agrees with a compatible scalar action. -/
def restrictScalarsAlgebraIso (M : ModuleCat.{u} C) [Module A M] [IsScalarTower A C M] :
    (restrictScalars (algebraMap A C)).obj M ≅ ModuleCat.of A M :=
  LinearEquiv.toModuleIso
    (X₁ := (restrictScalars (algebraMap A C)).obj M) (X₂ := ModuleCat.of A M)
    { __ := AddEquiv.refl M
      map_smul' := by
        intro a m
        change (algebraMap A C a) • (show M from m) = a • (show M from m)
        exact IsScalarTower.algebraMap_smul C a (show M from m) }
@[simp]
lemma restrictScalarsAlgebraIso_hom_apply (M : ModuleCat.{u} C)
    [Module A M] [IsScalarTower A C M] (m : M) :
    (restrictScalarsAlgebraIso (A := A) M).hom m = m := rfl
@[simp]
lemma restrictScalarsAlgebraIso_inv_apply (M : ModuleCat.{u} C)
    [Module A M] [IsScalarTower A C M] (m : M) :
    (restrictScalarsAlgebraIso (A := A) M).inv m = m := rfl
section
variable {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
  [Algebra B D] [Algebra C D] [SMulCommClass B C D]
set_option backward.isDefEq.respectTransparency false in
/-- Compare a tensor product with extension followed by restriction of scalars. -/
def restrictExtendScalarsAlgebraIso (N : ModuleCat.{u} B) :
    ModuleCat.of C (D ⊗[B] N) ≅
      (restrictScalars (algebraMap C D)).obj ((extendScalars (algebraMap B D)).obj N) :=
  (restrictScalarsAlgebraIso (A := C) (ModuleCat.of D (D ⊗[B] N))).symm ≪≫
    ((restrictScalars (algebraMap C D)).mapIso (extendScalarsAlgebraIso (C := D) N)).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma restrictExtendScalarsAlgebraIso_hom_tmul (N : ModuleCat.{u} B) (d : D) (n : N) :
    (restrictExtendScalarsAlgebraIso (C := C) (D := D) N).hom (d ⊗ₜ[B] n) =
      d ⊗ₜ[B, algebraMap B D] n :=
  extendScalarsAlgebraIso_inv_tmul N d n
end

section
variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra B D] [Algebra C D] [SMulCommClass B C D]
local instance (N : ModuleCat.{u} B) : Module A N := Module.compHom N (algebraMap A B)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of scalars has the original carrier with its induced module structure. -/
def restrictScalarsNativeIso (N : ModuleCat.{u} B) :
    (restrictScalars (algebraMap A B)).obj N ≅ ModuleCat.of A N := Iso.refl _

lemma restrictScalarsNativeIso_hom_apply (N : ModuleCat.{u} B) (n : N) :
    (restrictScalarsNativeIso (A := A) N).hom n = n := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Transport a tensor-product isomorphism to extension and restriction of scalars. -/
def extendRestrictScalarsAlgebraIso (N : ModuleCat.{u} B)
    (e : ModuleCat.of C (C ⊗[A] N) ≅ ModuleCat.of C (D ⊗[B] N)) :
    (extendScalars (algebraMap A C)).obj ((restrictScalars (algebraMap A B)).obj N) ≅
      (restrictScalars (algebraMap C D)).obj ((extendScalars (algebraMap B D)).obj N) :=
  (extendScalars (algebraMap A C)).mapIso (restrictScalarsNativeIso (A := A) N) ≪≫
    extendScalarsAlgebraIso (ModuleCat.of A N) ≪≫ e ≪≫
    restrictExtendScalarsAlgebraIso (C := C) (D := D) N

set_option backward.isDefEq.respectTransparency false in
lemma extendRestrictScalarsAlgebraIso_hom_tmul (N : ModuleCat.{u} B)
    (e : ModuleCat.of C (C ⊗[A] N) ≅ ModuleCat.of C (D ⊗[B] N))
    (c : C) (d : D) (n : N) (he : e.hom (c ⊗ₜ[A] n) = d ⊗ₜ[B] n) :
    (extendRestrictScalarsAlgebraIso N e).hom (c ⊗ₜ[A, algebraMap A C] n) =
      d ⊗ₜ[B, algebraMap B D] n := by
  dsimp only [extendRestrictScalarsAlgebraIso, Iso.trans_hom]
  simp only [ConcreteCategory.comp_apply, Functor.mapIso_hom]
  rw [ExtendScalars.map_tmul, restrictScalarsNativeIso_hom_apply,
    extendScalarsAlgebraIso_hom_tmul, he]
  exact restrictExtendScalarsAlgebraIso_hom_tmul N d n

set_option backward.isDefEq.respectTransparency false in
/-- A scalar-extension map is invertible if it agrees on generators with a tensor-product
isomorphism. -/
lemma isIso_of_tensorProduct_iso (N : ModuleCat.{u} B)
    (f : (extendScalars (algebraMap A C)).obj ((restrictScalars (algebraMap A B)).obj N) ⟶
      (restrictScalars (algebraMap C D)).obj ((extendScalars (algebraMap B D)).obj N))
    (e : ModuleCat.of C (C ⊗[A] N) ≅ ModuleCat.of C (D ⊗[B] N))
    (he : ∀ n : N, e.hom ((1 : C) ⊗ₜ[A] n) = (1 : D) ⊗ₜ[B] n)
    (hf : ∀ n : N, f ((1 : C) ⊗ₜ[A, algebraMap A C] n) =
      (1 : D) ⊗ₜ[B, algebraMap B D] n) : IsIso f := by
  have h : f = (extendRestrictScalarsAlgebraIso N e).hom := by
    apply ExtendScalars.hom_ext
    intro n
    exact (hf n).trans (extendRestrictScalarsAlgebraIso_hom_tmul N e 1 1 n (he n)).symm
  rw [h]
  infer_instance
end

section
variable {R T : Type u} [CommRing R] [CommRing T]

/-- Extending scalars commutes with the binary product of modules, with the canonical
identification induced by the tensor-product product map. -/
def extendScalarsProdIso (φ : R →+* T) (M N : ModuleCat.{u} R) :
    (extendScalars φ).obj (ModuleCat.of R (M × N)) ≅
      ModuleCat.of T ((extendScalars φ).obj M × (extendScalars φ).obj N) := by
  letI : Algebra R T := φ.toAlgebra
  exact (TensorProduct.prodRight R T T M N).toModuleIso

/-- The scalar-extension product isomorphism sends the canonical generator to the pair of
canonical generators. -/
lemma extendScalarsProdIso_one_tmul (φ : R →+* T) (M N : ModuleCat.{u} R)
    (m : M) (n : N) :
    (extendScalarsProdIso φ M N).hom ((1 : T) ⊗ₜ[R, φ] (m, n)) =
      (((1 : T) ⊗ₜ[R, φ] m), ((1 : T) ⊗ₜ[R, φ] n)) := by
  rfl
end
end ModuleCat
