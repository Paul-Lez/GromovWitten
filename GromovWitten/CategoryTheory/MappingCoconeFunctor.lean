/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Functoriality of mapping cocones

Mapping cocones are functorial in commutative squares. Additive functors commute with
this construction and with its canonical lifts with zero homotopy. These identities
control the augmentation maps in iterated Mayer–Vietoris complexes.
-/

open CategoryTheory Limits CochainComplex.HomComplex
namespace CochainComplex
section Maps
variable {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
/-- The map of mapping cocones induced by a commutative square. -/
noncomputable def mappingCoconeMap {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) :
    CochainComplex.mappingCocone φ₁ ⟶ CochainComplex.mappingCocone φ₂ :=
  (CategoryTheory.shiftFunctor (CochainComplex (A) ℤ) (-1)).map
    (CochainComplex.mappingCone.map φ₁ φ₂ a b comm)

lemma mappingCoconeMap_id {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    mappingCoconeMap φ φ (𝟙 K) (𝟙 L) (by simp) = 𝟙 _ := by
  change (CategoryTheory.shiftFunctor (CochainComplex (A) ℤ) (-1)).map
      (CochainComplex.mappingCone.map φ φ (𝟙 K) (𝟙 L) _) =
    𝟙 ((CategoryTheory.shiftFunctor (CochainComplex (A) ℤ) (-1)).obj
      (CochainComplex.mappingCone φ))
  rw [CochainComplex.mappingCone.map_id]
  rfl

lemma mappingCoconeMap_comp {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (φ₃ : K₃ ⟶ L₃)
    (a₁ : K₁ ⟶ K₂) (b₁ : L₁ ⟶ L₂) (h₁ : φ₁ ≫ b₁ = a₁ ≫ φ₂)
    (a₂ : K₂ ⟶ K₃) (b₂ : L₂ ⟶ L₃) (h₂ : φ₂ ≫ b₂ = a₂ ≫ φ₃) :
    mappingCoconeMap φ₁ φ₃ (a₁ ≫ a₂) (b₁ ≫ b₂)
        (by rw [reassoc_of% h₁, h₂, Category.assoc]) =
      mappingCoconeMap φ₁ φ₂ a₁ b₁ h₁ ≫ mappingCoconeMap φ₂ φ₃ a₂ b₂ h₂ := by
  have hcomp : φ₁ ≫ (b₁ ≫ b₂) = (a₁ ≫ a₂) ≫ φ₃ := by
    calc
      φ₁ ≫ (b₁ ≫ b₂) = (φ₁ ≫ b₁) ≫ b₂ := (Category.assoc _ _ _).symm
      _ = (a₁ ≫ φ₂) ≫ b₂ := congrArg (fun t => t ≫ b₂) h₁
      _ = a₁ ≫ (φ₂ ≫ b₂) := Category.assoc _ _ _
      _ = a₁ ≫ (a₂ ≫ φ₃) := congrArg (fun t => a₁ ≫ t) h₂
      _ = (a₁ ≫ a₂) ≫ φ₃ := (Category.assoc _ _ _).symm
  change (CategoryTheory.shiftFunctor (CochainComplex (A) ℤ) (-1)).map
      (CochainComplex.mappingCone.map φ₁ φ₃ (a₁ ≫ a₂) (b₁ ≫ b₂) hcomp) =
    (CategoryTheory.shiftFunctor (CochainComplex (A) ℤ) (-1)).map
      (CochainComplex.mappingCone.map φ₁ φ₂ a₁ b₁ h₁) ≫
    (CategoryTheory.shiftFunctor (CochainComplex (A) ℤ) (-1)).map
      (CochainComplex.mappingCone.map φ₂ φ₃ a₂ b₂ h₂)
  rw [← Functor.map_comp]
  congr 1
  exact CochainComplex.mappingCone.map_comp φ₁ φ₂ φ₃ a₁ b₁ h₁ a₂ b₂ h₂

/-- An isomorphism of arrows induces an isomorphism of mapping cocones. -/
noncomputable def mappingCoconeMapIso
    {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ≅ K₂) (b : L₁ ≅ L₂)
    (comm : φ₁ ≫ b.hom = a.hom ≫ φ₂) :
    CochainComplex.mappingCocone φ₁ ≅ CochainComplex.mappingCocone φ₂ := by
  let invComm : φ₂ ≫ b.inv = a.inv ≫ φ₁ := by
    calc
      φ₂ ≫ b.inv = (a.inv ≫ a.hom) ≫ φ₂ ≫ b.inv := by simp
      _ = a.inv ≫ (a.hom ≫ φ₂) ≫ b.inv := by simp [Category.assoc]
      _ = a.inv ≫ (φ₁ ≫ b.hom) ≫ b.inv := by rw [← comm]
      _ = a.inv ≫ φ₁ := by simp [Category.assoc]
  refine ⟨mappingCoconeMap φ₁ φ₂ a.hom b.hom comm,
    mappingCoconeMap φ₂ φ₁ a.inv b.inv invComm, ?_, ?_⟩
  · rw [← mappingCoconeMap_comp
      φ₁ φ₂ φ₁ a.hom b.hom comm a.inv b.inv invComm]
    simpa [Iso.hom_inv_id] using
      (mappingCoconeMap_id φ₁)
  · rw [← mappingCoconeMap_comp
      φ₂ φ₁ φ₂ a.inv b.inv invComm a.hom b.hom comm]
    simpa [Iso.inv_hom_id] using
      (mappingCoconeMap_id φ₂)

lemma mappingConeMap_fst {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (n m : ℤ) (h : n + 1 = m) :
    (CochainComplex.mappingCone.map φ₁ φ₂ a b comm).f n ≫
        (CochainComplex.mappingCone.fst φ₂).1.v n m h =
      (CochainComplex.mappingCone.fst φ₁).1.v n m h ≫ a.f m := by
  apply CochainComplex.mappingCone.ext_from φ₁ m n h
  · simp only [CochainComplex.mappingCone.map, ← Category.assoc,
      CochainComplex.mappingCone.inl_v_desc_f]
    simp [Category.assoc]
  · simp only [CochainComplex.mappingCone.map, ← Category.assoc,
      CochainComplex.mappingCone.inr_f_desc_f]
    simp [Category.assoc]

lemma mappingConeMap_snd {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (n : ℤ) :
    (CochainComplex.mappingCone.map φ₁ φ₂ a b comm).f n ≫
        (CochainComplex.mappingCone.snd φ₂).v n n (add_zero n) =
      (CochainComplex.mappingCone.snd φ₁).v n n (add_zero n) ≫ b.f n := by
  apply CochainComplex.mappingCone.ext_from φ₁ (n + 1) n rfl
  · simp only [CochainComplex.mappingCone.map, ← Category.assoc,
      CochainComplex.mappingCone.inl_v_desc_f]
    simp [Category.assoc]
  · simp only [CochainComplex.mappingCone.map, ← Category.assoc,
      CochainComplex.mappingCone.inr_f_desc_f]
    simp [Category.assoc]

@[reassoc]
lemma mappingCone_inl_map {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (n m : ℤ) (h : m + 1 = n) :
    (CochainComplex.mappingCone.inl φ₁).v n m (by omega) ≫
        (CochainComplex.mappingCone.map φ₁ φ₂ a b comm).f m =
      a.f n ≫ (CochainComplex.mappingCone.inl φ₂).v n m (by omega) := by
  simp [CochainComplex.mappingCone.map]

@[reassoc]
lemma mappingCone_inr_map {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (n : ℤ) :
    (CochainComplex.mappingCone.inr φ₁).f n ≫
        (CochainComplex.mappingCone.map φ₁ φ₂ a b comm).f n =
      b.f n ≫ (CochainComplex.mappingCone.inr φ₂).f n := by
  simp [CochainComplex.mappingCone.map]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma mappingCocone_inl_map {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (n : ℤ) :
    (CochainComplex.mappingCocone.inl φ₁).v n n (add_zero n) ≫
        (mappingCoconeMap φ₁ φ₂ a b comm).f n =
      a.f n ≫ (CochainComplex.mappingCocone.inl φ₂).v n n (add_zero n) := by
  simp only [CochainComplex.mappingCocone.inl, mappingCoconeMap,
    CochainComplex.shiftFunctor_map_f']
  rw [Cochain.rightShift_v _ (-1) 0 (by omega) n n (add_zero n) (n + -1) rfl,
    Cochain.rightShift_v _ (-1) 0 (by omega) n n (add_zero n) (n + -1) rfl]
  simp [mappingCone_inl_map]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma mappingCocone_inr_map {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (n m : ℤ) (h : n + 1 = m) :
    (CochainComplex.mappingCocone.inr φ₁).1.v n m h ≫
        ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1)).map
          (CochainComplex.mappingCone.map φ₁ φ₂ a b comm)).f m =
      b.f n ≫ (CochainComplex.mappingCocone.inr φ₂).1.v n m h := by
  subst m
  simp only [CochainComplex.mappingCocone.inr, Cocycle.rightShift_coe,
    CochainComplex.shiftFunctor_map_f']
  rw [Cochain.rightShift_v _ (-1) 1 (by omega) n (n + 1) rfl n (add_zero n),
    Cochain.rightShift_v _ (-1) 1 (by omega) n (n + 1) rfl n (add_zero n)]
  simp only [Cocycle.ofHom_coe, Cochain.ofHom_v,
    CochainComplex.shiftFunctorObjXIso]
  rw [Category.assoc, ← HomologicalComplex.XIsoOfEq_inv_naturality]
  rw [← Category.assoc, mappingCone_inr_map, Category.assoc]

lemma mappingCocone_lift_zero_factors_inl {M K L : CochainComplex A ℤ}
    (φ : K ⟶ L) (α : M ⟶ K)
    (h : CochainComplex.HomComplex.δ (-1) 0 0 +
      CochainComplex.HomComplex.Cochain.ofHom (α ≫ φ) = 0) (i : ℤ) :
    (CochainComplex.mappingCocone.lift φ α 0 h).f i =
      α.f i ≫ (CochainComplex.mappingCocone.inl φ).v i i (add_zero i) := by
  calc
    (CochainComplex.mappingCocone.lift φ α 0 h).f i =
        (CochainComplex.mappingCocone.lift φ α 0 h).f i ≫ 𝟙 _ := by simp
    _ = (CochainComplex.mappingCocone.lift φ α 0 h).f i ≫
        ((CochainComplex.mappingCocone.fst φ).f i ≫
            (CochainComplex.mappingCocone.inl φ).v i i (add_zero i) +
          (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
            (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) := by
      rw [CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)]
    _ = α.f i ≫ (CochainComplex.mappingCocone.inl φ).v i i (add_zero i) := by
      simp [CochainComplex.mappingCocone.lift]


end Maps
section Functor
variable {A B : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
  [Category* B] [Preadditive B] [HasBinaryBiproducts B]
  (H : A ⥤ B) [H.Additive]
  {K L : CochainComplex A ℤ} (φ : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
lemma map_cone_inl (n m : ℤ) (h : m + 1 = n) :
    H.map ((mappingCone.inl φ).v n m (by omega)) ≫
        (mappingCone.mapHomologicalComplexIso φ H).hom.f m =
      (mappingCone.inl ((H.mapHomologicalComplex (.up ℤ)).map φ)).v n m (by omega) := by
  change H.map ((mappingCone.inl φ).v n m _) ≫
      (mappingCone.mapHomologicalComplexXIso φ H m).hom = _
  rw [mappingCone.mapHomologicalComplexXIso_eq φ H m n h]
  simp [mappingCone.mapHomologicalComplexXIso'_hom, ← H.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
noncomputable def mapCoconeIso :
    (H.mapHomologicalComplex (.up ℤ)).obj (mappingCocone φ) ≅
      mappingCocone ((H.mapHomologicalComplex (.up ℤ)).map φ) := by
  dsimp only [mappingCocone]
  exact ((H.mapHomologicalComplex (.up ℤ)).commShiftIso (-1 : ℤ)).app (mappingCone φ) ≪≫
    (CategoryTheory.shiftFunctor (CochainComplex B ℤ) (-1 : ℤ)).mapIso
      (mappingCone.mapHomologicalComplexIso φ H)

set_option backward.isDefEq.respectTransparency false in
lemma map_cocone_inl (n : ℤ) :
    H.map ((mappingCocone.inl φ).v n n (add_zero n)) ≫
        (mapCoconeIso H φ).hom.f n =
      (mappingCocone.inl ((H.mapHomologicalComplex (.up ℤ)).map φ)).v n n (add_zero n) := by
  change H.map ((mappingCocone.inl φ).v n n _) ≫
    (((H.mapHomologicalComplex (.up ℤ)).commShiftIso (-1 : ℤ)).hom.app
      (mappingCone φ)).f n ≫
    ((CategoryTheory.shiftFunctor (CochainComplex B ℤ) (-1 : ℤ)).map
      (mappingCone.mapHomologicalComplexIso φ H).hom).f n = _
  rw [Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  dsimp only [mappingCocone, Functor.comp_obj, Functor.mapHomologicalComplex_obj_X,
    shiftFunctor_obj_X', shiftFunctor_map_f']
  dsimp only [mappingCocone.inl]
  rw [Cochain.rightShift_v _ (-1) 0 (by omega) n n (add_zero n) (n + -1) rfl,
    Cochain.rightShift_v _ (-1) 0 (by omega) n n (add_zero n) (n + -1) rfl]
  simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
    Category.comp_id]
  change H.map ((mappingCone.inl φ).v n (n + -1) _) ≫
    𝟙 (H.obj ((mappingCone φ).X (n + -1))) ≫
      (mappingCone.mapHomologicalComplexIso φ H).hom.f (n + -1) = _
  rw [Category.id_comp]
  exact map_cone_inl H φ n (n + -1) (by omega)

set_option backward.isDefEq.respectTransparency false in
lemma map_cocone_lift_zero {M : CochainComplex A ℤ} (α : M ⟶ K)
    (h : δ (-1) 0 0 + Cochain.ofHom (α ≫ φ) = 0)
    (hH : δ (-1) 0 0 + Cochain.ofHom
      ((H.mapHomologicalComplex (.up ℤ)).map α ≫
        (H.mapHomologicalComplex (.up ℤ)).map φ) = 0) :
    (H.mapHomologicalComplex (.up ℤ)).map (mappingCocone.lift φ α 0 h) ≫
      (mapCoconeIso H φ).hom =
    mappingCocone.lift ((H.mapHomologicalComplex (.up ℤ)).map φ)
      ((H.mapHomologicalComplex (.up ℤ)).map α) 0 hH := by
  apply HomologicalComplex.hom_ext
  intro i
  change H.map ((mappingCocone.lift φ α 0 h).f i) ≫ (mapCoconeIso H φ).hom.f i = _
  rw [mappingCocone_lift_zero_factors_inl,
    mappingCocone_lift_zero_factors_inl, H.map_comp, Category.assoc,
    map_cocone_inl]
  rfl

end Functor
section Lifts
variable {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
  {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
  (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
  (comm : φ₁ ≫ b = a ≫ φ₂)
set_option backward.isDefEq.respectTransparency false in
lemma cocone_lift_zero_map {M : CochainComplex A ℤ}
    (α₁ : M ⟶ K₁) (α₂ : M ⟶ K₂) (hα : α₁ ≫ a = α₂)
    (h₁ : δ (-1) 0 0 + Cochain.ofHom (α₁ ≫ φ₁) = 0)
    (h₂ : δ (-1) 0 0 + Cochain.ofHom (α₂ ≫ φ₂) = 0) :
    mappingCocone.lift φ₁ α₁ 0 h₁ ≫
      (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
        (mappingCone.map φ₁ φ₂ a b comm) = mappingCocone.lift φ₂ α₂ 0 h₂ := by
  change mappingCocone.lift φ₁ α₁ 0 h₁ ≫ mappingCoconeMap φ₁ φ₂ a b comm = _
  apply HomologicalComplex.hom_ext
  intro i
  simp only [HomologicalComplex.comp_f,
    mappingCocone_lift_zero_factors_inl, Category.assoc, mappingCocone_inl_map]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, hα]

end Lifts
end CochainComplex
