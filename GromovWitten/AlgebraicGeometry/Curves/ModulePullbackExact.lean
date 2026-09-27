/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChange
import GromovWitten.AlgebraicGeometry.SheafCohomology.OpenRestriction
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Exactness of scalar extension and open pullback -/

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

/- The finite-limit argument above is the categorical affine shadow of the
stalkwise argument needed for scheme pullback.  The colimit half is supplied
by the fact that extension of scalars is a left adjoint. -/

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

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
instance moduleRestriction_preservesMonomorphisms :
    (Scheme.Modules.restrictFunctor f).PreservesMonomorphisms where
  preserves {M N} φ hφ := by
    apply (moduleToSheafAb X).mono_of_mono_map
    change Mono ((f.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).map
      ((moduleToSheafAb Y).map φ))
    infer_instance
instance moduleOpenPullback_preservesMonomorphisms :
    (Scheme.Modules.pullback f).PreservesMonomorphisms :=
  CategoryTheory.Functor.PreservesMonomorphisms.of_iso (Scheme.Modules.restrictFunctorIsoPullback f)
instance moduleOpenPullback_preservesHomology :
    (Scheme.Modules.pullback f).PreservesHomology :=
  CategoryTheory.Functor.preservesHomology_of_preservesMonos_and_cokernels _

end
end GromovWitten.AlgebraicGeometry.Curves
