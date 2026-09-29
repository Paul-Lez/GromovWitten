/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Five-term exact complexes

This file packages three consecutive exact rows into the canonical five-term short
complex obtained from a cokernel and a kernel.
-/

open CategoryTheory Limits
namespace CategoryTheory.ShortComplex
noncomputable section
variable {C : Type*} [Category C] [Abelian C]
variable {A B D E F : C}

set_option backward.isDefEq.respectTransparency false in
/-- The canonical short complex associated with three consecutive exact rows. -/
def fiveTermShortComplex
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (k : E ⟶ F)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) (hhk : h ≫ k = 0) :
    ShortComplex C :=
  ShortComplex.mk (cokernel.desc f g hfg) (kernel.lift k h hhk) (by
    apply (cancel_epi (cokernel.π f)).mp
    apply (cancel_mono (kernel.ι k)).mp
    simpa only [Category.assoc, cokernel.π_desc_assoc, kernel.lift_ι,
      comp_zero, zero_comp] using hgh)

set_option backward.isDefEq.respectTransparency false in
/-- Three consecutive exact rows make the canonical five-term complex short exact. -/
lemma fiveTerm_shortExact
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (k : E ⟶ F)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) (hhk : h ≫ k = 0)
    (he₁ : (ShortComplex.mk f g hfg).Exact)
    (he₂ : (ShortComplex.mk g h hgh).Exact)
    (he₃ : (ShortComplex.mk h k hhk).Exact) :
    (fiveTermShortComplex f g h k hfg hgh hhk).ShortExact := by
  let u := cokernel.desc f g hfg
  let v := kernel.lift k h hhk
  let huv := (fiveTermShortComplex f g h k hfg hgh hhk).zero
  let S := ShortComplex.mk g h hgh
  let T := ShortComplex.mk u h (by
    apply (cancel_epi (cokernel.π f)).mp
    simpa only [u, cokernel.π_desc_assoc, comp_zero] using hgh)
  let W := ShortComplex.mk u v huv
  let α : S ⟶ T := { τ₁ := cokernel.π f, τ₂ := 𝟙 _, τ₃ := 𝟙 _
                     comm₁₂ := by simp [S, T, u]
                     comm₂₃ := by simp [S, T] }
  let β : W ⟶ T := { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι k
                     comm₁₂ := by simp [W, T]
                     comm₂₃ := by simp [W, T, v] }
  have ht : T.Exact := (exact_iff_of_epi_of_isIso_of_mono α).mp he₂
  have hw : W.Exact := (exact_iff_of_epi_of_isIso_of_mono β).mpr ht
  have hu : Mono u := he₁.mono_cokernelDesc
  have hv : Epi v := he₃.epi_kernelLift
  exact { exact := hw, mono_f := hu, epi_g := hv }
end
end CategoryTheory.ShortComplex
