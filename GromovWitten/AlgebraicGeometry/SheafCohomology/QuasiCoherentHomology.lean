/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.QuasiCoherentExtensions
import GromovWitten.AlgebraicGeometry.SheafCohomology.QuasiCoherentKernels
import GromovWitten.CategoryTheory.FiveTermExact
import Mathlib.Algebra.Homology.HomologySequence

/-!
# Quasicoherence in exact complexes and homology

On a locally Noetherian scheme, quasicoherence is closed under the exact
five-term constructions controlling homology.  In particular, in a short
exact sequence of cochain complexes, quasicoherence of the second and third
homologies in every degree implies quasicoherence of the first.
-/

open CategoryTheory Limits AlgebraicGeometry HomologicalComplex
open _root_.AlgebraicGeometry
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- In an exact module short complex, a monic first map and quasicoherent
middle and right terms imply quasicoherence of the left term. -/
lemma isQuasicoherent_left_of_exact (T : ShortComplex X.Modules) (hT : T.Exact)
    [Mono T.f] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent] :
    T.X₁.IsQuasicoherent := by
  let e : T.X₁ ≅ kernel T.g :=
    hT.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)
  have : (kernel T.g).IsQuasicoherent := isQuasicoherent_kernel T.g
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- In a five-term exact sequence over a locally Noetherian scheme,
quasicoherence of the four outer terms implies quasicoherence of the middle
term. -/
lemma isQuasicoherent_middle_of_fiveTerm [IsLocallyNoetherian X]
    {A B D E F : X.Modules} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (k : E ⟶ F)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) (hhk : h ≫ k = 0)
    (he₁ : (ShortComplex.mk f g hfg).Exact)
    (he₂ : (ShortComplex.mk g h hgh).Exact)
    (he₃ : (ShortComplex.mk h k hhk).Exact)
    [A.IsQuasicoherent] [B.IsQuasicoherent] [E.IsQuasicoherent] [F.IsQuasicoherent] :
    D.IsQuasicoherent := by
  have : (cokernel f).IsQuasicoherent := isQuasicoherent_cokernel f
  have : (kernel k).IsQuasicoherent := isQuasicoherent_kernel k
  let T := ShortComplex.fiveTermShortComplex f g h k hfg hgh hhk
  let _ : T.X₁.IsQuasicoherent := ‹(cokernel f).IsQuasicoherent›
  let _ : T.X₃.IsQuasicoherent := ‹(kernel k).IsQuasicoherent›
  exact isQuasicoherent_middle_of_shortExact
    T
    (ShortComplex.fiveTerm_shortExact f g h k hfg hgh hhk he₁ he₂ he₃)

set_option backward.isDefEq.respectTransparency false in
/-- For a short exact sequence of cochain complexes over a locally Noetherian
scheme, quasicoherence of the second and third homologies in every
natural-number degree implies quasicoherence of the first homology object in
every natural-number degree. -/
lemma isQuasicoherent_homology_left [IsLocallyNoetherian X]
    (T : ShortComplex (CochainComplex X.Modules ℕ)) (hT : T.ShortExact)
    (h₂ : ∀ n, (T.X₂.homology n).IsQuasicoherent)
    (h₃ : ∀ n, (T.X₃.homology n).IsQuasicoherent) (n : ℕ) :
    (T.X₁.homology n).IsQuasicoherent := by
  cases n with
  | zero =>
    have := hT.mono_f
    have := mono_homologyMap_of_mono_of_not_rel T.f 0 (by
      intro i hi
      simp at hi)
    have := h₂ 0
    have := h₃ 0
    exact isQuasicoherent_left_of_exact _ (hT.homology_exact₂ 0)
  | succ n =>
    have := h₂ n
    have := h₃ n
    have := h₂ (n + 1)
    have := h₃ (n + 1)
    exact isQuasicoherent_middle_of_fiveTerm
      (homologyMap T.g n) (hT.δ n (n + 1) rfl)
      (homologyMap T.f (n + 1)) (homologyMap T.g (n + 1))
      (hT.comp_δ n (n + 1) rfl) (hT.δ_comp n (n + 1) rfl)
      (by rw [← homologyMap_comp, T.zero, homologyMap_zero])
      (hT.homology_exact₃ n (n + 1) rfl) (hT.homology_exact₁ n (n + 1) rfl)
      (hT.homology_exact₂ (n + 1))

end GromovWitten.AlgebraicGeometry.SheafCohomology
