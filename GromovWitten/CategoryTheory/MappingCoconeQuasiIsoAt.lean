/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import GromovWitten.CategoryTheory.MappingCoconeFunctor
import GromovWitten.CategoryTheory.MappingCoconeQuasiIso
import GromovWitten.CategoryTheory.ShortComplexKernelComparison

/-!
# Pointwise quasi-isomorphisms of mapping cocones

For a commutative square, an additive functor sends its cocone map to a
quasi-isomorphism in degree n if it does so for both sides and the mapped target
complexes are exact in degree n−1. The proof identifies cocone homology with a
kernel in the long exact sequence. No exactness of the functor is required.
-/

open CategoryTheory Limits HomologicalComplex Pretriangulated

noncomputable section

namespace CochainComplex

set_option backward.isDefEq.respectTransparency false in
private lemma mappingCoconeMap_fst
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) :
    mappingCoconeMap φ₁ φ₂ a b comm ≫ mappingCocone.fst φ₂ =
      mappingCocone.fst φ₁ ≫ a := by
  apply HomologicalComplex.hom_ext
  intro i
  have hi : (i - 1) + 1 = i := by omega
  have hleft :
    (mappingCocone.inl φ₁).v i i (add_zero i) ≫
        (mappingCoconeMap φ₁ φ₂ a b comm).f i ≫
          (mappingCocone.fst φ₂).f i = a.f i := by
    calc
      _ = a.f i ≫ (mappingCocone.inl φ₂).v i i (add_zero i) ≫
          (mappingCocone.fst φ₂).f i := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ (mappingCocone.fst φ₂).f i)
            (mappingCocone_inl_map φ₁ φ₂ a b comm i)
      _ = a.f i := by simp
  have hright :
      (mappingCocone.snd φ₁).v i (i - 1) (by omega) ≫
        (mappingCocone.inr φ₁).1.v (i - 1) i hi ≫
          (mappingCoconeMap φ₁ φ₂ a b comm).f i ≫
            (mappingCocone.fst φ₂).f i = 0 := by
    have hmap := mappingCocone_inr_map φ₁ φ₂ a b comm (i - 1) i hi
    calc
      _ = (mappingCocone.snd φ₁).v i (i - 1) (by omega) ≫
          ((mappingCocone.inr φ₁).1.v (i - 1) i hi ≫
            (mappingCoconeMap φ₁ φ₂ a b comm).f i ≫
              (mappingCocone.fst φ₂).f i) := by simp
      _ = (mappingCocone.snd φ₁).v i (i - 1) (by omega) ≫
          ((b.f (i - 1) ≫ (mappingCocone.inr φ₂).1.v
            (i - 1) i hi) ≫ (mappingCocone.fst φ₂).f i) := by
          simpa only [mappingCoconeMap, Category.assoc] using congrArg
            (fun f => (mappingCocone.snd φ₁).v i (i - 1) (by omega) ≫
              (f ≫ (mappingCocone.fst φ₂).f i)) hmap
      _ = 0 := by simp [Category.assoc]
  calc
    (mappingCoconeMap φ₁ φ₂ a b comm).f i ≫
        (mappingCocone.fst φ₂).f i =
      (𝟙 _) ≫ ((mappingCoconeMap φ₁ φ₂ a b comm).f i ≫
        (mappingCocone.fst φ₂).f i) := by simp
    _ = ((mappingCocone.fst φ₁).f i ≫
        (mappingCocone.inl φ₁).v i i (add_zero i) +
        (mappingCocone.snd φ₁).v i (i - 1) (by omega) ≫
        (mappingCocone.inr φ₁).1.v (i - 1) i hi) ≫
        ((mappingCoconeMap φ₁ φ₂ a b comm).f i ≫
          (mappingCocone.fst φ₂).f i) := by
      rw [← mappingCocone.id_X φ₁ i (i - 1) (by omega)]
    _ = (mappingCocone.fst φ₁).f i ≫
          ((mappingCocone.inl φ₁).v i i (add_zero i) ≫
            (mappingCoconeMap φ₁ φ₂ a b comm).f i ≫
            (mappingCocone.fst φ₂).f i) +
        (mappingCocone.snd φ₁).v i (i - 1) (by omega) ≫
          ((mappingCocone.inr φ₁).1.v (i - 1) i hi ≫
            (mappingCoconeMap φ₁ φ₂ a b comm).f i ≫
            (mappingCocone.fst φ₂).f i) := by
      simp only [Preadditive.add_comp, Category.assoc]
    _ = (mappingCocone.fst φ₁).f i ≫ a.f i := by
      rw [hleft, hright]
      simp

set_option backward.isDefEq.respectTransparency false in
private lemma additive_mappingCocone_triangle_distinguished
    {A B : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    [Category* B] [Abelian B] [HasDerivedCategory B] (H : A ⥤ B) [H.Additive]
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    DerivedCategory.Q.mapTriangle.obj
      ((H.mapHomologicalComplex (.up ℤ)).mapTriangle.obj (mappingCocone.triangle φ)) ∈
        distTriang (DerivedCategory B) := by
  let F := H.mapHomologicalComplex (.up ℤ)
  have hc : DerivedCategory.Q.mapTriangle.obj (F.mapTriangle.obj (mappingCone.triangle φ)) ∈
      distTriang (DerivedCategory B) :=
    isomorphic_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished (F.map φ)) _
      (DerivedCategory.Q.mapTriangle.mapIso (mappingCone.mapTriangleIso φ H))
  rw [rotate_distinguished_triangle]
  exact isomorphic_distinguished _ hc _
    (DerivedCategory.Q.mapTriangleRotateIso.app _ ≪≫
      DerivedCategory.Q.mapTriangle.mapIso (F.mapTriangleRotateIso.app _) ≪≫
      DerivedCategory.Q.mapTriangle.mapIso
        (F.mapTriangle.mapIso (mappingCocone.rotateTriangleIso φ)))

set_option backward.isDefEq.respectTransparency false in
/-- Applying an additive functor preserves pointwise quasi-isomorphisms of mapping cocones
when the target complexes are exact one degree below. -/
lemma mappingCoconeMap_quasiIsoAt_after_additive_of_exact_below
    {A B : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    [Category* B] [Abelian B] (H : A ⥤ B) [H.Additive]
    {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (n : ℤ)
    [QuasiIsoAt ((H.mapHomologicalComplex (.up ℤ)).map a) n]
    [QuasiIsoAt ((H.mapHomologicalComplex (.up ℤ)).map b) n]
    (hL₁ : ((H.mapHomologicalComplex (.up ℤ)).obj L₁).ExactAt (n - 1))
    (hL₂ : ((H.mapHomologicalComplex (.up ℤ)).obj L₂).ExactAt (n - 1)) :
    QuasiIsoAt ((H.mapHomologicalComplex (.up ℤ)).map
      (mappingCoconeMap φ₁ φ₂ a b comm)) n := by
  let _ := HasDerivedCategory.standard B
  let F := H.mapHomologicalComplex (.up ℤ)
  let c := mappingCoconeMap φ₁ φ₂ a b comm
  let T₁ : Triangle (DerivedCategory B) :=
    DerivedCategory.Q.mapTriangle.obj (F.mapTriangle.obj (mappingCocone.triangle φ₁))
  let T₂ : Triangle (DerivedCategory B) :=
    DerivedCategory.Q.mapTriangle.obj (F.mapTriangle.obj (mappingCocone.triangle φ₂))
  have hT₁ : T₁ ∈ distTriang _ := by
    dsimp [T₁]
    exact additive_mappingCocone_triangle_distinguished H φ₁
  have hT₂ : T₂ ∈ distTriang _ := by
    dsimp [T₂]
    exact additive_mappingCocone_triangle_distinguished H φ₂
  let Hn := DerivedCategory.homologyFunctor B n
  let S₁ : ShortComplex B := ShortComplex.mk (Hn.map T₁.mor₁) (Hn.map T₁.mor₂) (by
    simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT₁, Functor.map_zero])
  let S₂ : ShortComplex B := ShortComplex.mk (Hn.map T₂.mor₁) (Hn.map T₂.mor₂) (by
    simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT₂, Functor.map_zero])
  have hS₁ : S₁.Exact := by
    dsimp [S₁]
    exact DerivedCategory.HomologySequence.exact₂ T₁ hT₁ n
  have hzero₁ :
      IsZero ((DerivedCategory.homologyFunctor B (n - 1)).obj T₁.obj₃) := by
    have hz := (((F.obj L₁).exactAt_iff_isZero_homology (n - 1)).mp hL₁)
    have e : (DerivedCategory.homologyFunctor B (n - 1)).obj T₁.obj₃ ≅
        (F.obj L₁).homology (n - 1) := by
      change (DerivedCategory.homologyFunctor B (n - 1)).obj
        (DerivedCategory.Q.obj (F.obj L₁)) ≅ (F.obj L₁).homology (n - 1)
      exact (DerivedCategory.homologyFunctorFactors B (n - 1)).app (F.obj L₁)
    exact IsZero.of_iso hz e
  have hzero₂ :
      IsZero ((DerivedCategory.homologyFunctor B (n - 1)).obj T₂.obj₃) := by
    have hz := (((F.obj L₂).exactAt_iff_isZero_homology (n - 1)).mp hL₂)
    have e : (DerivedCategory.homologyFunctor B (n - 1)).obj T₂.obj₃ ≅
        (F.obj L₂).homology (n - 1) := by
      change (DerivedCategory.homologyFunctor B (n - 1)).obj
        (DerivedCategory.Q.obj (F.obj L₂)) ≅ (F.obj L₂).homology (n - 1)
      exact (DerivedCategory.homologyFunctorFactors B (n - 1)).app (F.obj L₂)
    exact IsZero.of_iso hz e
  have hδ₁ : DerivedCategory.HomologySequence.δ T₁ (n - 1) n (by omega) = 0 :=
    IsZero.eq_of_src hzero₁ _ _
  have hδ₂ : DerivedCategory.HomologySequence.δ T₂ (n - 1) n (by omega) = 0 :=
    IsZero.eq_of_src hzero₂ _ _
  have hmono₁ : Mono S₁.f := by
    change Mono ((DerivedCategory.homologyFunctor B n).map T₁.mor₁)
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T₁ hT₁ (n - 1) n (by omega)]
    exact hδ₁
  have hmono₂ : Mono S₂.f := by
    change Mono ((DerivedCategory.homologyFunctor B n).map T₂.mor₁)
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T₂ hT₂ (n - 1) n (by omega)]
    exact hδ₂
  have hIsoa : IsIso ((DerivedCategory.homologyFunctor B n).map
      (DerivedCategory.Q.map (F.map a))) := by
    apply (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors B n) (F.map a)).2
    exact (quasiIsoAt_iff_isIso_homologyMap (F.map a) n).mp inferInstance
  have hIsob : IsIso ((DerivedCategory.homologyFunctor B n).map
      (DerivedCategory.Q.map (F.map b))) := by
    apply (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors B n) (F.map b)).2
    exact (quasiIsoAt_iff_isIso_homologyMap (F.map b) n).mp inferInstance
  let η : S₁ ⟶ S₂ := {
    τ₁ := by
      change Hn.obj (DerivedCategory.Q.obj (F.obj (mappingCocone φ₁))) ⟶
        Hn.obj (DerivedCategory.Q.obj (F.obj (mappingCocone φ₂)))
      exact Hn.map (DerivedCategory.Q.map (F.map c))
    τ₂ := by
      change Hn.obj (DerivedCategory.Q.obj (F.obj K₁)) ⟶
        Hn.obj (DerivedCategory.Q.obj (F.obj K₂))
      exact Hn.map (DerivedCategory.Q.map (F.map a))
    τ₃ := by
      change Hn.obj (DerivedCategory.Q.obj (F.obj L₁)) ⟶
        Hn.obj (DerivedCategory.Q.obj (F.obj L₂))
      exact Hn.map (DerivedCategory.Q.map (F.map b))
    comm₁₂ := by
      change Hn.map (DerivedCategory.Q.map (F.map c)) ≫
          Hn.map (DerivedCategory.Q.map (F.map (mappingCocone.fst φ₂))) =
        Hn.map (DerivedCategory.Q.map (F.map (mappingCocone.fst φ₁))) ≫
          Hn.map (DerivedCategory.Q.map (F.map a))
      simp only [← Functor.map_comp]
      exact congrArg (fun f => Hn.map (DerivedCategory.Q.map (F.map f)))
        (mappingCoconeMap_fst φ₁ φ₂ a b comm)
    comm₂₃ := by
      change Hn.map (DerivedCategory.Q.map (F.map a)) ≫
          Hn.map (DerivedCategory.Q.map (F.map φ₂)) =
        Hn.map (DerivedCategory.Q.map (F.map φ₁)) ≫
          Hn.map (DerivedCategory.Q.map (F.map b))
      simp only [← Functor.map_comp]
      exact congrArg (fun f => Hn.map (DerivedCategory.Q.map (F.map f))) comm.symm
  }
  have hIsoη₁ : IsIso η.τ₁ := by
    let : Mono S₁.f := hmono₁
    let : Mono S₂.f := hmono₂
    let : IsIso η.τ₂ := hIsoa
    let : IsIso η.τ₃ := hIsob
    let : Mono η.τ₃ := inferInstance
    exact ShortComplex.isIso_τ₁_of_exact_of_mono_f η hS₁
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors B n) (F.map c)).1 hIsoη₁

end CochainComplex

end
