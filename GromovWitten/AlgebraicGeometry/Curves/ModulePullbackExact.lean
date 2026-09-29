/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModulePullbackStalk
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Exactness of scalar extension and flat pullback -/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open scoped ZeroObject

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

/-- Flat extension of scalars preserves homology of module short complexes. -/
lemma moduleExtendScalars_preservesHomology_of_flat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat) :
    (ModuleCat.extendScalars.{u,u,u} f).PreservesHomology := by
  let _ := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  infer_instance


/-- In the affine flat case, extension of scalars carries monomorphisms to
monomorphisms. -/
lemma moduleExtendScalars_preservesMonomorphisms_of_flat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    : Functor.PreservesMonomorphisms (ModuleCat.extendScalars.{u,u,u} f) := by
  let _ := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  infer_instance

/-- Pointwise form of
`moduleExtendScalars_preservesMonomorphisms_of_flat`. -/
lemma moduleExtendScalars_map_mono_of_flat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    {M N : ModuleCat R} (φ : M ⟶ N) [Mono φ] :
    Mono ((ModuleCat.extendScalars.{u,u,u} f).map φ) :=
  (moduleExtendScalars_preservesMonomorphisms_of_flat f hf).preserves φ

variable {X Y : Scheme.{u}}

/-- Pullback along a flat scheme morphism preserves monomorphisms. -/
instance moduleFlatPullback_preservesMonomorphisms (f : X ⟶ Y) [Flat f] :
    (Scheme.Modules.pullback f).PreservesMonomorphisms where
  preserves {M N} φ hφ := by
    apply mono_of_moduleStalk_mono
    intro x
    let _ := moduleExtendScalars_preservesMonomorphisms_of_flat
      (f.stalkMap x).hom (Flat.stalkMap f x)
    let _ : (Scheme.Modules.pullback f ⋙ moduleStalk X x).PreservesMonomorphisms :=
      CategoryTheory.Functor.PreservesMonomorphisms.of_iso (modulePullbackStalkIso f x).symm
    exact inferInstanceAs (Mono ((Scheme.Modules.pullback f ⋙ moduleStalk X x).map φ))

/-- Pullback along a flat scheme morphism is exact on sheaves of modules. -/
instance moduleFlatPullback_preservesHomology (f : X ⟶ Y) [Flat f] :
    (Scheme.Modules.pullback f).PreservesHomology :=
  CategoryTheory.Functor.preservesHomology_of_preservesMonos_and_cokernels _


end
end GromovWitten.AlgebraicGeometry.Curves
