/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Degree-zero quasi-isomorphisms and left exact functors

An additive left exact functor preserves degree-zero quasi-isomorphisms of
nonnegative cochain complexes, since their degree-zero homology is a kernel.
-/

open CategoryTheory Limits HomologicalComplex

namespace CategoryTheory.Functor

/-- An additive functor preserving finite limits preserves quasi-isomorphisms at degree zero
of nonnegative cochain complexes. -/
lemma quasiIsoAt_zero_map_of_preservesFiniteLimits {C D : Type*} [Category* C] [Abelian C]
    [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {K L : CochainComplex C ℕ} (f : K ⟶ L)
    [QuasiIsoAt f 0] :
    QuasiIsoAt ((F.mapHomologicalComplex (.up ℕ)).map f) 0 := by
  let S := K.sc' 0 0 1
  let T := L.sc' 0 0 1
  have : F.PreservesLeftHomologyOf S := F.preservesLeftHomology_of_zero_f S (by
    exact K.shape 0 0 (by simp))
  have : F.PreservesLeftHomologyOf T := F.preservesLeftHomology_of_zero_f T (by
    exact L.shape 0 0 (by simp))
  have : ShortComplex.QuasiIso ((shortComplexFunctor' C (.up ℕ) 0 0 1).map f) :=
    (CochainComplex.quasiIsoAt₀_iff f).mp inferInstance
  rw [CochainComplex.quasiIsoAt₀_iff]
  change ShortComplex.QuasiIso (F.mapShortComplex.map
    ((shortComplexFunctor' C (.up ℕ) 0 0 1).map f))
  infer_instance


end CategoryTheory.Functor
