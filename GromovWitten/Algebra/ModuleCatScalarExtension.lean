/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

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
end ModuleCat
