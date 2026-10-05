/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Quasi-isomorphisms of cones and cocones

Quasi-isomorphisms on the sides of a commutative square induce quasi-isomorphisms
on its cones and cocones. The same conclusion holds after applying an additive
functor whenever the two side maps become quasi-isomorphisms; exactness of the
functor is not required.
-/

open CategoryTheory Limits HomologicalComplex

universe u v

namespace CochainComplex

set_option backward.isDefEq.respectTransparency false in
/-- A square with quasi-isomorphisms on both sides induces a quasi-isomorphism of cones. -/
lemma mappingCone_map_quasiIso
    {A : Type u} [Category.{v} A] [Abelian A]
    {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) [QuasiIso a] [QuasiIso b] :
    QuasiIso (mappingCone.map φ₁ φ₂ a b comm) := by
  let _ := HasDerivedCategory.standard A
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso A _).mp
  exact Pretriangulated.isIso₃_of_isIso₁₂
    (DerivedCategory.Q.mapTriangle.map (mappingCone.triangleMap φ₁ φ₂ a b comm))
    (DerivedCategory.mappingCone_triangle_distinguished φ₁)
    (DerivedCategory.mappingCone_triangle_distinguished φ₂)
    (inferInstanceAs (IsIso (DerivedCategory.Q.map a)))
    (inferInstanceAs (IsIso (DerivedCategory.Q.map b)))

set_option backward.isDefEq.respectTransparency false in
/-- A square with quasi-isomorphisms on both sides induces a quasi-isomorphism of cocones. -/
lemma mappingCocone_map_quasiIso
    {A : Type u} [Category.{v} A] [Abelian A]
    {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) [QuasiIso a] [QuasiIso b] :
    QuasiIso ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1)).map
      (mappingCone.map φ₁ φ₂ a b comm)) := by
  have := mappingCone_map_quasiIso φ₁ φ₂ a b comm
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- An additive functor sends the cone map of a square to a quasi-isomorphism when it sends
both sides to quasi-isomorphisms. -/
lemma mappingCone_map_quasiIso_after_additive
    {A B : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A] [Category* B] [Abelian B]
    (H : A ⥤ B) [H.Additive]
    {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂)
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map a)]
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map b)] :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      (mappingCone.map φ₁ φ₂ a b comm)) := by
  let _ := HasDerivedCategory.standard B
  let F := H.mapHomologicalComplex (.up ℤ)
  have hd {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
      DerivedCategory.Q.mapTriangle.obj (F.mapTriangle.obj (mappingCone.triangle φ)) ∈
        distTriang (DerivedCategory B) := by
    exact Pretriangulated.isomorphic_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished (F.map φ)) _
      (DerivedCategory.Q.mapTriangle.mapIso (mappingCone.mapTriangleIso φ H))
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso B _).mp
  exact Pretriangulated.isIso₃_of_isIso₁₂
    (DerivedCategory.Q.mapTriangle.map
      (F.mapTriangle.map (mappingCone.triangleMap φ₁ φ₂ a b comm)))
    (hd φ₁) (hd φ₂)
    (inferInstanceAs (IsIso (DerivedCategory.Q.map (F.map a))))
    (inferInstanceAs (IsIso (DerivedCategory.Q.map (F.map b))))

set_option backward.isDefEq.respectTransparency false in
/-- An additive functor sends the cocone map of a square to a quasi-isomorphism when it sends
both sides to quasi-isomorphisms. -/
lemma mappingCocone_map_quasiIso_after_additive
    {A B : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A] [Category* B] [Abelian B]
    (H : A ⥤ B) [H.Additive]
    {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂)
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map a)]
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map b)] :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1)).map
        (mappingCone.map φ₁ φ₂ a b comm))) := by
  let F := H.mapHomologicalComplex (.up ℤ)
  let g := mappingCone.map φ₁ φ₂ a b comm
  have : QuasiIso (F.map g) := mappingCone_map_quasiIso_after_additive H φ₁ φ₂ a b comm
  apply (quasiIso_iff_comp_right _ ((F.commShiftIso (-1 : ℤ)).hom.app _)).mp
  rw [F.commShiftIso_hom_naturality]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private lemma isIso_map_biprodMap
    {A B : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    [Category* B] [Preadditive B] [HasBinaryBiproducts B]
    (F : A ⥤ B) [F.Additive]
    {K₁ L₁ K₂ L₂ : A} (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    [IsIso (F.map a)] [IsIso (F.map b)] : IsIso (F.map (biprod.map a b)) := by
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  have h : F.map (biprod.map a b) ≫ (F.mapBiprod K₂ L₂).hom =
      (F.mapBiprod K₁ L₁).hom ≫ biprod.map (F.map a) (F.map b) := by
    apply biprod.hom_ext
    · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst,
        biprod.map_fst, biprod.lift_fst_assoc, ← F.map_comp]
    · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_snd,
        biprod.map_snd, biprod.lift_snd_assoc, ← F.map_comp]
  have : IsIso (biprod.map (F.map a) (F.map b)) :=
    (biprod.mapIso (asIso (F.map a)) (asIso (F.map b))).isIso_hom
  have : IsIso (F.map (biprod.map a b) ≫ (F.mapBiprod K₂ L₂).hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.mapBiprod K₂ L₂).hom

set_option backward.isDefEq.respectTransparency false in
/-- An additive functor sends a biproduct map to a quasi-isomorphism when it sends
both summand maps to quasi-isomorphisms. -/
lemma biprod_map_quasiIso_after_additive
    {A B : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A] [Category* B] [Abelian B]
    (H : A ⥤ B) [H.Additive]
    {K₁ L₁ K₂ L₂ : CochainComplex A ℤ} (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map a)]
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map b)] :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map (biprod.map a b)) := by
  let _ := HasDerivedCategory.standard B
  let : HasBinaryBiproducts (CochainComplex A ℤ) := ⟨fun _ _ => inferInstance⟩
  let F := H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  have : IsIso (F.map a) := inferInstanceAs
    (IsIso (DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map a)))
  have : IsIso (F.map b) := inferInstanceAs
    (IsIso (DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map b)))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).mp (isIso_map_biprodMap F a b)

end CochainComplex
