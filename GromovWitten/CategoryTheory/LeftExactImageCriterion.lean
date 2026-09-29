/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Image criteria for left-exact functors

An additive left-exact functor maps an exact short complex to an exact short
complex when the image factor of its first map becomes epi.  Consequently it
preserves a supplied cokernel cofork when its projection also becomes epi.
-/

open CategoryTheory Limits Abelian

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

noncomputable section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D]

/-- An additive left-exact functor maps an exact short complex to an exact
short complex when the image factor of its first map becomes epi. -/
theorem map_exact_of_epi_factorThruImage
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (S : ShortComplex C) (hS : S.Exact)
    [Epi (F.map (Abelian.factorThruImage S.f))] :
    (S.map F).Exact := by
  let T : ShortComplex C :=
    ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
  have hT : T.Exact := (S.exact_iff_exact_image_ι).1 hS
  have hTF : (T.map F).Exact :=
    hT.map_of_mono_of_preservesKernel F inferInstance inferInstance
  have hSF : (S.map F).Exact := by
    let φ : S.map F ⟶ T.map F :=
      { τ₁ := F.map (Abelian.factorThruImage S.f)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by
          change F.map (Abelian.factorThruImage S.f) ≫ F.map (Abelian.image.ι S.f) =
            F.map S.f ≫ 𝟙 _
          rw [← F.map_comp, Abelian.image.fac, Category.comp_id]
        comm₂₃ := by
          change 𝟙 _ ≫ F.map S.g = F.map S.g ≫ 𝟙 _
          simp }
    have : Epi φ.τ₁ := by
      change Epi (F.map (Abelian.factorThruImage S.f))
      infer_instance
    have : IsIso φ.τ₂ := by
      change IsIso (𝟙 _)
      infer_instance
    have : Mono φ.τ₃ := by
      change Mono (𝟙 _)
      infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hTF
  exact hSF

/-- An additive left-exact functor preserves a supplied cokernel cofork of `f`
when it maps the image factor of `f` and the cofork projection to epimorphisms. -/
theorem preservesCokernel_of_epi_factorThruImage
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {X Y : C} (f : X ⟶ Y) (c : CokernelCofork f) (hc : IsColimit c)
    [Epi (F.map (Abelian.factorThruImage f))]
    [Epi (F.map c.π)] :
  PreservesColimit (parallelPair f 0) F := by
  let S : ShortComplex C := ShortComplex.mk f c.π c.condition
  have hS : S.Exact := by
    apply ShortComplex.exact_of_g_is_cokernel S
    exact IsColimit.ofIsoColimit hc (Cofork.isoCoforkOfπ c)
  have : Epi (F.map (Abelian.factorThruImage S.f)) := by
    change Epi (F.map (Abelian.factorThruImage f))
    infer_instance
  have hSF : (S.map F).Exact := map_exact_of_epi_factorThruImage F S hS
  refine preservesColimit_of_preserves_colimit_cocone hc ?_
  apply (CokernelCofork.isColimitMapCoconeEquiv c F).2
  have : Epi (S.map F).g := by
    change Epi (F.map c.π)
    infer_instance
  exact hSF.gIsCokernel

end

end CategoryTheory.Functor
