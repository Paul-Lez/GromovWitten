/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Exact-functor compatibility for the snake connecting morphism

An additive functor preserving homology maps snake inputs to snake inputs and
commutes with their connecting morphisms.
-/

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

namespace ShortComplex.SnakeInput

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
/-- Maps a snake input through an additive functor preserving homology. -/
noncomputable def mapExact (S : SnakeInput C) (F : C ⥤ D)
    [F.Additive] [F.PreservesHomology] : SnakeInput D := by
  letI : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  letI : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  exact
    { L₀ := S.L₀.map F
      L₁ := S.L₁.map F
      L₂ := S.L₂.map F
      L₃ := S.L₃.map F
      v₀₁ := F.mapShortComplex.map S.v₀₁
      v₁₂ := F.mapShortComplex.map S.v₁₂
      v₂₃ := F.mapShortComplex.map S.v₂₃
      w₀₂ := by
        ext <;> simp [← F.map_comp]
      w₁₃ := by
        ext <;> simp [← F.map_comp]
      h₀ := by
        apply ShortComplex.isLimitOfIsLimitπ
        · exact (KernelFork.isLimitMapConeEquiv _ _).symm
            (isLimitForkMapOfIsLimit' F S.w₀₂_τ₁ S.h₀τ₁)
        · exact (KernelFork.isLimitMapConeEquiv _ _).symm
            (isLimitForkMapOfIsLimit' F S.w₀₂_τ₂ S.h₀τ₂)
        · exact (KernelFork.isLimitMapConeEquiv _ _).symm
            (isLimitForkMapOfIsLimit' F S.w₀₂_τ₃ S.h₀τ₃)
      h₃ := by
        apply ShortComplex.isColimitOfIsColimitπ
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
            (isColimitCoforkMapOfIsColimit' F S.w₁₃_τ₁ S.h₃τ₁)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
            (isColimitCoforkMapOfIsColimit' F S.w₁₃_τ₂ S.h₃τ₂)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
            (isColimitCoforkMapOfIsColimit' F S.w₁₃_τ₃ S.h₃τ₃)
      L₁_exact := S.L₁_exact.map F
      epi_L₁_g := by
        have := S.epi_L₁_g
        change Epi (F.map S.L₁.g)
        infer_instance
      L₂_exact := S.L₂_exact.map F
      mono_L₂_f := by
        have := S.mono_L₂_f
        change Mono (F.map S.L₂.f)
        infer_instance }

set_option backward.isDefEq.respectTransparency false in
/-- The snake connecting morphism commutes with `mapExact`. -/
lemma mapExact_δ (S : SnakeInput C) (F : C ⥤ D)
    [F.Additive] [F.PreservesHomology] : F.map S.δ = (S.mapExact F).δ := by
  let T := S.mapExact F
  let c : F.obj S.P ⟶ T.P := pullbackComparison F S.L₁.g S.v₀₁.τ₃
  have hc_fst : c ≫ (pullback.fst _ _ : T.P ⟶ F.obj S.L₁.X₂) =
      F.map (pullback.fst S.L₁.g S.v₀₁.τ₃) := pullbackComparison_comp_fst F _ _
  have hc_snd : c ≫ (pullback.snd _ _ : T.P ⟶ T.L₀.X₃) =
      F.map (pullback.snd S.L₁.g S.v₀₁.τ₃) := pullbackComparison_comp_snd F _ _
  have hφ : c ≫ T.φ₁ = F.map S.φ₁ := by
    apply (cancel_mono (F.map S.L₂.f)).mp
    rw [Category.assoc]
    change c ≫ T.φ₁ ≫ T.L₂.f = F.map S.φ₁ ≫ F.map S.L₂.f
    rw [T.φ₁_L₂_f, ← F.map_comp, S.φ₁_L₂_f]
    change c ≫ (pullback.fst _ _ : T.P ⟶ F.obj S.L₁.X₂) ≫ F.map S.v₁₂.τ₂ =
      F.map ((pullback.fst _ _ : S.P ⟶ S.L₁.X₂) ≫ S.v₁₂.τ₂)
    rw [← Category.assoc, hc_fst, F.map_comp]
  have hE : Epi (F.map (pullback.snd S.L₁.g S.v₀₁.τ₃)) := inferInstance
  apply (cancel_epi (F.map (pullback.snd S.L₁.g S.v₀₁.τ₃))).mp
  calc
    _ = F.map S.φ₁ ≫ F.map S.v₂₃.τ₁ := by rw [← F.map_comp, S.snd_δ, F.map_comp]
    _ = c ≫ T.φ₁ ≫ T.v₂₃.τ₁ := by rw [← hφ, Category.assoc]; rfl
    _ = c ≫ (pullback.snd _ _ : T.P ⟶ T.L₀.X₃) ≫ T.δ := by
      exact congrArg (fun t => c ≫ t) T.snd_δ.symm
    _ = _ := by rw [← Category.assoc, hc_snd]

end ShortComplex.SnakeInput
end CategoryTheory
