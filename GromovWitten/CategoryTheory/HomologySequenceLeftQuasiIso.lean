/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import GromovWitten.CategoryTheory.ShortComplexKernelComparison

/-!
# The left term of a short exact homology sequence

The five-lemma argument shows that a morphism between short exact sequences
of cochain complexes is a quasi-isomorphism on the left when it is one on the
middle and right.  Degree zero uses the kernel comparison for monomorphisms; positive
degrees use the five-term piece of the long exact homology sequence.
-/

open CategoryTheory Limits
open HomologicalComplex

noncomputable section

universe u v

namespace HomologicalComplex.HomologySequence

variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma homologyMap_isIso_of_quasiIso
    {K L : CochainComplex C ℕ} (f : K ⟶ L) [QuasiIso f] (n : ℕ) :
    IsIso (homologyMap f n) := by
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private lemma isIso_homologyMap_τ₁_zero
    {S T : ShortComplex (CochainComplex C ℕ)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (h₂ : IsIso (homologyMap φ.τ₂ 0)) (h₃ : IsIso (homologyMap φ.τ₃ 0)) :
    IsIso (homologyMap φ.τ₁ 0) := by
  have : Mono S.f := hS.mono_f
  have : Mono T.f := hT.mono_f
  have : Mono (homologyMap S.f 0) :=
    mono_homologyMap_of_mono_of_not_rel S.f 0 (by
      intro i hi
      simp at hi)
  have : Mono (homologyMap T.f 0) :=
    mono_homologyMap_of_mono_of_not_rel T.f 0 (by
      intro i hi
      simp at hi)
  have : IsIso (homologyMap φ.τ₂ 0) := h₂
  have : IsIso (homologyMap φ.τ₃ 0) := h₃
  let H₀ := homologyFunctor C (.up ℕ) 0
  have : IsIso (H₀.mapShortComplex.map φ).τ₂ := by
    change IsIso (homologyMap φ.τ₂ 0)
    infer_instance
  have : Mono (H₀.mapShortComplex.map φ).τ₃ := by
    change Mono (homologyMap φ.τ₃ 0)
    infer_instance
  have : Mono (H₀.mapShortComplex.obj S).f := by
    change Mono (homologyMap S.f 0)
    infer_instance
  have : Mono (H₀.mapShortComplex.obj T).f := by
    change Mono (homologyMap T.f 0)
    infer_instance
  have h₀ := ShortComplex.isIso_τ₁_of_exact_of_mono_f
    (H₀.mapShortComplex.map φ) (hS.homology_exact₂ 0)
  change IsIso (homologyMap φ.τ₁ 0) at h₀
  exact h₀

set_option backward.isDefEq.respectTransparency false in
private lemma isIso_homologyMap_τ₁_succ
    {S T : ShortComplex (CochainComplex C ℕ)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ)
    (h₂n : IsIso (homologyMap φ.τ₂ n))
    (h₃n : IsIso (homologyMap φ.τ₃ n))
    (h₂n₁ : IsIso (homologyMap φ.τ₂ (n + 1)))
    (h₃n₁ : IsIso (homologyMap φ.τ₃ (n + 1))) :
    IsIso (homologyMap φ.τ₁ (n + 1)) := by
  let ψ := mapComposableArrows₅ φ hS hT n (n + 1) rfl
  let ψ₀ := ComposableArrows.δ₀Functor.map ψ
  have hR₁ := (composableArrows₅_exact hS n (n + 1) rfl).δ₀
  have hR₂ := (composableArrows₅_exact hT n (n + 1) rfl).δ₀
  have : IsIso (homologyMap φ.τ₂ n) := h₂n
  have : IsIso (homologyMap φ.τ₃ n) := h₃n
  have : IsIso (homologyMap φ.τ₂ (n + 1)) := h₂n₁
  have : IsIso (homologyMap φ.τ₃ (n + 1)) := h₃n₁
  have h := Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    hR₁ hR₂ ψ₀
    (by change Epi (homologyMap φ.τ₂ n); infer_instance)
    (by change IsIso (homologyMap φ.τ₃ n); infer_instance)
    (by change IsIso (homologyMap φ.τ₂ (n + 1)); infer_instance)
    (by change Mono (homologyMap φ.τ₃ (n + 1)); infer_instance)
  exact h

/-- A morphism between short exact sequences of cochain complexes is a
quasi-isomorphism on the left when it is a quasi-isomorphism on the middle and
right. -/
lemma quasiIso_τ₁
    {S T : ShortComplex (CochainComplex C ℕ)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    [QuasiIso φ.τ₂] [QuasiIso φ.τ₃] :
    QuasiIso φ.τ₁ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h₂ : ∀ n, IsIso (homologyMap φ.τ₂ n) := by
    intro n
    exact homologyMap_isIso_of_quasiIso φ.τ₂ n
  have h₃ : ∀ n, IsIso (homologyMap φ.τ₃ n) := by
    intro n
    exact homologyMap_isIso_of_quasiIso φ.τ₃ n
  cases n with
  | zero =>
    exact isIso_homologyMap_τ₁_zero hS hT φ (h₂ 0) (h₃ 0)
  | succ n =>
    exact isIso_homologyMap_τ₁_succ hS hT φ n (h₂ n) (h₃ n)
      (h₂ (n + 1)) (h₃ (n + 1))

end HomologicalComplex.HomologySequence
