/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineBaseChange
import GromovWitten.Algebra.ModuleCatScalarExtension

/-!
# The canonical tensor-product base-change mate

For a pushout of commutative rings presented as a tensor product, the mate of the
commuting restriction-of-scalars square is an isomorphism. Its comparison with
the native tensor-product equivalence is proved on the adjunction generators.
-/

open CategoryTheory TensorProduct
open scoped ChangeOfRings
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
local notation "P" => B ⊗[A] C
local instance : Algebra B P := Algebra.TensorProduct.leftAlgebra
local instance : Algebra C P := Algebra.TensorProduct.rightAlgebra

/-- The commuting restriction-of-scalars square for a tensor product of algebras. -/
def tensorBaseChangeRestrictionIso :
    ModuleCat.restrictScalars (algebraMap B P) ⋙ ModuleCat.restrictScalars (algebraMap A B) ≅
      ModuleCat.restrictScalars (algebraMap C P) ⋙ ModuleCat.restrictScalars (algebraMap A C) :=
  (ModuleCat.restrictScalarsComp (algebraMap A B) (algebraMap B P)).symm ≪≫
    ModuleCat.restrictScalarsCongr Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap ≪≫
    ModuleCat.restrictScalarsComp (algebraMap A C) (algebraMap C P)

set_option backward.isDefEq.respectTransparency false in
/-- The unit map whose adjoint is the canonical algebraic base-change map. -/
def tensorBaseChangeUnit (N : ModuleCat.{u} B) :
    (ModuleCat.restrictScalars (algebraMap A B)).obj N ⟶
      (ModuleCat.restrictScalars (algebraMap A C)).obj
        ((ModuleCat.restrictScalars (algebraMap C P)).obj
          ((ModuleCat.extendScalars (algebraMap B P)).obj N)) :=
  (ModuleCat.restrictScalars (algebraMap A B)).map
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap B P)).unit.app N) ≫
      (tensorBaseChangeRestrictionIso (A := A) (B := B) (C := C)).hom.app
        ((ModuleCat.extendScalars (algebraMap B P)).obj N)

set_option backward.isDefEq.respectTransparency false in
lemma tensorBaseChangeUnit_apply (N : ModuleCat.{u} B) (n : N) :
    tensorBaseChangeUnit (A := A) (C := C) N n =
      (1 : P) ⊗ₜ[B, algebraMap B P] n := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical base-change map obtained as the mate of the restriction square. -/
def tensorBaseChangeMate (N : ModuleCat.{u} B) :
    (ModuleCat.extendScalars (algebraMap A C)).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj N) ⟶
      (ModuleCat.restrictScalars (algebraMap C P)).obj
        ((ModuleCat.extendScalars (algebraMap B P)).obj N) :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap A C)).homEquiv _ _).symm
    (tensorBaseChangeUnit (A := A) (C := C) N)

set_option backward.isDefEq.respectTransparency false in
lemma tensorBaseChangeMate_one_tmul (N : ModuleCat.{u} B) (n : N) :
    tensorBaseChangeMate (A := A) (C := C) N ((1 : C) ⊗ₜ[A, algebraMap A C] n) =
      (1 : P) ⊗ₜ[B, algebraMap B P] n := by
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap A C)
  have h := (adj.homEquiv _ _).apply_symm_apply (tensorBaseChangeUnit (A := A) (C := C) N)
  have hv := ConcreteCategory.congr_hom h n
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] at hv
  exact hv.trans (tensorBaseChangeUnit_apply N n)

local instance (N : ModuleCat.{u} B) : Module A N := Module.compHom N (algebraMap A B)
local instance (N : ModuleCat.{u} B) : IsScalarTower A B N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

set_option backward.isDefEq.respectTransparency false in
lemma affineTensorBaseChangeIso_symm_tmul (N : ModuleCat.{u} B) (c : C) (n : N) :
    (affineTensorBaseChangeIso (A := A) (B := B) (C := C) N).symm
      (c ⊗ₜ[A] n) = ((1 : B) ⊗ₜ[A] c) ⊗ₜ[B] n := by
  apply (affineTensorBaseChangeIso (A := A) (B := B) (C := C) N).injective
  rw [LinearEquiv.apply_symm_apply, affineTensorBaseChangeIso_tmul, one_smul]

set_option backward.isDefEq.respectTransparency false in
lemma affineTensorBaseChangeModuleIso_inv_one_tmul (N : ModuleCat.{u} B) (n : N) :
    (affineTensorBaseChangeModuleIso (A := A) (B := B) (C := C) N).inv
      ((1 : C) ⊗ₜ[A] n) = (1 : P) ⊗ₜ[B] n := by
  change (affineTensorBaseChangeIso N).symm ((1 : C) ⊗ₜ[A] n) = _
  rw [affineTensorBaseChangeIso_symm_tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
instance tensorBaseChangeMate_isIso (N : ModuleCat.{u} B) :
    IsIso (tensorBaseChangeMate (A := A) (C := C) N) :=
  ModuleCat.isIso_of_tensorProduct_iso N (tensorBaseChangeMate N)
    (affineTensorBaseChangeModuleIso (A := A) (B := B) (C := C) N).symm
    (affineTensorBaseChangeModuleIso_inv_one_tmul N) (tensorBaseChangeMate_one_tmul N)

end GromovWitten.AlgebraicGeometry.Curves
