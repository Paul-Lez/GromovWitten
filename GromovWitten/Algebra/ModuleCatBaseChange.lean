/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.ModuleCatScalarExtension
import Mathlib.RingTheory.IsTensorProduct
/-!
# Module base change for an algebra pushout

The mate of the commuting restriction-of-scalars square gives the canonical
base-change map. For a pushout of commutative algebras it is invertible, by
Mathlib's `Algebra.IsPushout.cancelBaseChange` tensor equivalence. The proof
compares the two maps on scalar-extension adjunction generators.
-/

open CategoryTheory TensorProduct
open scoped ChangeOfRings
noncomputable section
universe u
namespace ModuleCat
variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
  [IsScalarTower A B D] [IsScalarTower A C D]
/-- The commuting restriction-of-scalars square of a commutative algebra diagram. -/
def algebraBaseChangeRestrictionIso :
    restrictScalars (algebraMap B D) ⋙ restrictScalars (algebraMap A B) ≅
      restrictScalars (algebraMap C D) ⋙ restrictScalars (algebraMap A C) :=
  (restrictScalarsComp (algebraMap A B) (algebraMap B D)).symm ≪≫
    restrictScalarsCongr ((IsScalarTower.algebraMap_eq A B D).symm.trans
      (IsScalarTower.algebraMap_eq A C D)) ≪≫
    restrictScalarsComp (algebraMap A C) (algebraMap C D)
set_option backward.isDefEq.respectTransparency false in
/-- The pushforward of the scalar-extension unit followed by the restriction square. -/
def algebraBaseChangeUnit (N : ModuleCat.{u} B) :
    (restrictScalars (algebraMap A B)).obj N ⟶
      (restrictScalars (algebraMap A C)).obj
        ((restrictScalars (algebraMap C D)).obj ((extendScalars (algebraMap B D)).obj N)) :=
  (restrictScalars (algebraMap A B)).map ((extendRestrictScalarsAdj (algebraMap B D)).unit.app N) ≫
    (algebraBaseChangeRestrictionIso (A := A) (B := B) (C := C) (D := D)).hom.app
      ((extendScalars (algebraMap B D)).obj N)
set_option backward.isDefEq.respectTransparency false in
lemma algebraBaseChangeUnit_apply (N : ModuleCat.{u} B) (n : N) :
    algebraBaseChangeUnit (A := A) (C := C) (D := D) N n =
      (1 : D) ⊗ₜ[B, algebraMap B D] n := rfl
set_option backward.isDefEq.respectTransparency false in
/-- The canonical scalar-extension base-change map for a commuting algebra square. -/
def algebraBaseChangeMate (N : ModuleCat.{u} B) :
    (extendScalars (algebraMap A C)).obj ((restrictScalars (algebraMap A B)).obj N) ⟶
      (restrictScalars (algebraMap C D)).obj ((extendScalars (algebraMap B D)).obj N) :=
  ((extendRestrictScalarsAdj (algebraMap A C)).homEquiv _ _).symm
    (algebraBaseChangeUnit (A := A) (C := C) (D := D) N)
set_option backward.isDefEq.respectTransparency false in
lemma algebraBaseChangeMate_one_tmul (N : ModuleCat.{u} B) (n : N) :
    algebraBaseChangeMate (A := A) (C := C) (D := D) N
        ((1 : C) ⊗ₜ[A, algebraMap A C] n) = (1 : D) ⊗ₜ[B, algebraMap B D] n := by
  have h := ((extendRestrictScalarsAdj (algebraMap A C)).homEquiv _ _).apply_symm_apply
    (algebraBaseChangeUnit (A := A) (C := C) (D := D) N)
  have hv := ConcreteCategory.congr_hom h n
  rw [extendRestrictScalarsAdj_homEquiv_apply] at hv
  exact hv.trans (algebraBaseChangeUnit_apply N n)
set_option backward.isDefEq.respectTransparency false in
/-- The canonical algebra base-change map is natural in the module. -/
lemma algebraBaseChangeMate_naturality {M N : ModuleCat.{u} B} (f : M ⟶ N) :
    (extendScalars (algebraMap A C)).map ((restrictScalars (algebraMap A B)).map f) ≫
        algebraBaseChangeMate (D := D) N =
      algebraBaseChangeMate (D := D) M ≫
        (restrictScalars (algebraMap C D)).map ((extendScalars (algebraMap B D)).map f) := by
  apply ExtendScalars.hom_ext
  intro n
  simp only [ConcreteCategory.comp_apply, ExtendScalars.map_tmul]
  change algebraBaseChangeMate (A := A) (C := C) (D := D) N
      ((1 : C) ⊗ₜ[A, algebraMap A C] (f n)) =
    ((extendScalars (algebraMap B D)).map f)
      (algebraBaseChangeMate (A := A) (C := C) (D := D) M
        ((1 : C) ⊗ₜ[A, algebraMap A C] n))
  rw [algebraBaseChangeMate_one_tmul, algebraBaseChangeMate_one_tmul,
    ExtendScalars.map_tmul]

local instance (N : ModuleCat.{u} B) : Module A N := Module.compHom N (algebraMap A B)
local instance (N : ModuleCat.{u} B) : IsScalarTower A B N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
set_option backward.isDefEq.respectTransparency false in
/-- Base change of modules along an algebra pushout is an isomorphism. -/
instance algebraBaseChangeMate_isIso [Algebra.IsPushout A B C D] (N : ModuleCat.{u} B) :
    IsIso (algebraBaseChangeMate (A := A) (C := C) (D := D) N) := by
  have : Algebra.IsPushout A C B D := Algebra.IsPushout.symm inferInstance
  let e : ModuleCat.of C (C ⊗[A] N) ≅ ModuleCat.of C (D ⊗[B] N) :=
    LinearEquiv.toModuleIso (Algebra.IsPushout.cancelBaseChange A C B D N).symm
  refine isIso_of_tensorProduct_iso N _ e ?_ (algebraBaseChangeMate_one_tmul N)
  intro n
  change (Algebra.IsPushout.cancelBaseChange A C B D N).symm ((1 : C) ⊗ₜ[A] n) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one]
end ModuleCat
