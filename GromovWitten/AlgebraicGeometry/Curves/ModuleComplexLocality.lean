/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeLocal
import GromovWitten.AlgebraicGeometry.Curves.ModulePullbackExact
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Locality of complex quasi-isomorphisms

Quasi-isomorphisms of module complexes can be checked after pullback to affine
open neighbourhoods.
-/

open CategoryTheory Limits HomologicalComplex
open _root_.AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of module complexes is a quasi-isomorphism when its pullback to
an open neighbourhood of every point is a quasi-isomorphism. -/
lemma moduleComplex_quasiIso_of_open_pullbacks {X : Scheme.{u}}
    {K J : CochainComplex X.Modules ℕ} (φ : K ⟶ J)
    (h : ∀ x : X, ∃ (U : X.Opens) (_hx : x ∈ U),
      QuasiIso (((Scheme.Modules.pullback U.ι).mapHomologicalComplex (.up ℕ)).map φ)) :
    QuasiIso φ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply module_isIso_of_open_pullbacks
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  refine ⟨U, hx, ?_⟩
  let F := Scheme.Modules.pullback U.ι
  have : QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map φ) := hU
  have he : homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) n ≫
      ((J.sc n).mapHomologyIso F).hom =
      ((K.sc n).mapHomologyIso F).hom ≫ F.map (homologyMap φ n) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor X.Modules (.up ℕ) n).map φ) F
  have : IsIso (((K.sc n).mapHomologyIso F).hom ≫ F.map (homologyMap φ n)) := by
    rw [← he]
    infer_instance
  exact IsIso.of_isIso_comp_left ((K.sc n).mapHomologyIso F).hom _
end GromovWitten.AlgebraicGeometry.Curves
