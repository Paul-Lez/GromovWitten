/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineBaseChange
import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPushforward
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Module.Presentation.Finite
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-!
# Finite presentation under affine finite pushforward

The affine calculation identifies global sections of a pushforward with restriction of
scalars.  A finite algebra over a Noetherian ring therefore carries finite presentations
to finite presentations, and the associated module sheaves inherit the result.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open AlgebraicGeometry Scheme.Modules

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

/-- The sheaf associated to a finitely presented module is locally finitely presented. -/
lemma tilde_isFinitePresentation
    {R : CommRingCat.{u}} (N : ModuleCat R)
    [Module.FinitePresentation R (N : Type u)] :
    SheafOfModules.IsFinitePresentation (C := Opens (Spec R))
      (R := (Spec R).ringCatSheaf) (AlgebraicGeometry.tilde N) := by
  obtain ⟨s, hs, hker⟩ := Module.FinitePresentation.out (R := (R : Type u))
    (M := (N : Type u))
  obtain ⟨G : Type u, hG, g, hg⟩ :=
    Submodule.fg_iff_exists_finite_generating_family.mp hker
  let t : Set ((s : Set (N : Type u)) →₀ (R : Type u)) := Set.range g
  have ht : Submodule.span (R : Type u) t =
      (Finsupp.linearCombination (R : Type u) Subtype.val).ker := hg
  let P := AlgebraicGeometry.presentationTilde N (s : Set (N : Type u)) hs t ht
  let _ : Finite (s : Set (N : Type u)) := s.finite_toSet
  let _ : Finite t := Set.toFinite _
  have hP : P.IsFinite := by
    refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
    · constructor
      exact s.finite_toSet
    · constructor
      exact Set.toFinite _
  let _ : P.IsFinite := hP
  constructor
  refine ⟨P.quasicoherentData, ?_⟩
  constructor
  intro i
  change (Spec R).Opens at i
  let _ : (SheafOfModules.pushforward.{u}
      (𝟙 (Sheaf.over (Spec R).ringCatSheaf i))).IsLeftAdjoint :=
    inferInstance
  have hcolim : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      (SheafOfModules.pushforward.{u}
        (𝟙 (Sheaf.over (Spec R).ringCatSheaf i))) :=
    (SheafOfModules.overPushforwardOverAdj
      (R := (Spec R).ringCatSheaf) i).leftAdjoint_preservesColimits
  let _ : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      (SheafOfModules.pushforward.{u}
        (𝟙 (Sheaf.over (Spec R).ringCatSheaf i))) := hcolim
  let F := SheafOfModules.pushforward.{u}
    (𝟙 (Sheaf.over (Spec R).ringCatSheaf i))
  let Q := P.map F (Iso.refl _)
  change Q.IsFinite
  refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
  · dsimp [Q]
    constructor
    change Finite P.generators.I
    exact s.finite_toSet
  · dsimp [Q]
    constructor
    change Finite P.relations.I
    exact Set.toFinite _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A quasi-coherent affine module sheaf is finitely presented if its global sections are. -/
lemma spec_module_isFinitePresentation
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [IsIso M.fromTildeΓ]
    [Module.FinitePresentation R ((moduleSpecΓFunctor.obj M : Type u))] :
    M.IsFinitePresentation := by
  let N := moduleSpecΓFunctor.obj M
  have hN : SheafOfModules.IsFinitePresentation (C := Opens (Spec R))
      (R := (Spec R).ringCatSheaf) (AlgebraicGeometry.tilde N) :=
    tilde_isFinitePresentation N
  let e : AlgebraicGeometry.tilde N ≅ M := asIso M.fromTildeΓ
  exact (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
    e hN

/-- The affine pushforward statement for an arbitrary module sheaf whose global sections
are finitely presented. -/
lemma modulePushforward_spec_isFinitePresentation
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec S).Modules)
    [IsNoetherianRing R] (hφ : RingHom.Finite φ.hom)
    [IsIso M.fromTildeΓ]
    [Module.FinitePresentation S ((moduleSpecΓFunctor.obj M : Type u))] :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj M).IsFinitePresentation := by
  let P := (Scheme.Modules.pushforward (Spec.map φ)).obj M
  let _ : IsIso P.fromTildeΓ := AlgebraicGeometry.isIso_fromTildeΓ_pushforward φ M
  let B := moduleSpecΓFunctor.obj M
  let A := moduleSpecΓFunctor.obj P
  let e := (affineGammaIso φ).app M
  let Bᵣ := (ModuleCat.restrictScalars φ.hom).obj B
  let _ : Algebra (R : Type u) (S : Type u) := φ.hom.toAlgebra
  let _ : Module.Finite (R : Type u) (S : Type u) := by
    change Module.Finite (R : Type u) (S : Type u) at hφ
    exact hφ
  let _ : IsScalarTower (R : Type u) (S : Type u) (Bᵣ : Type u) :=
    IsScalarTower.of_compHom (R : Type u) (S : Type u) (Bᵣ : Type u)
  let _ : Module.Finite (S : Type u) (Bᵣ : Type u) := by
    change Module.Finite (S : Type u) (B : Type u)
    infer_instance
  let _ : Module.Finite (R : Type u) (Bᵣ : Type u) :=
    Module.Finite.trans (R := (R : Type u)) (A := (S : Type u)) (M := (Bᵣ : Type u))
  let _ : Module.FinitePresentation (R : Type u) (Bᵣ : Type u) :=
    Module.finitePresentation_of_finite (R := (R : Type u)) (M := (Bᵣ : Type u))
  let _ : Module.FinitePresentation R (A : Type u) := by
    exact Module.FinitePresentation.of_equiv (R := (R : Type u))
      (M := (Bᵣ : Type u)) (N := (A : Type u)) e.symm.toLinearEquiv
  exact spec_module_isFinitePresentation P

/-- The associated-module instance is the common input for the affine calculation. -/
lemma modulePushforward_spec_tilde_isFinitePresentation
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (N : ModuleCat S)
    [IsNoetherianRing R] (hφ : RingHom.Finite φ.hom)
    [Module.FinitePresentation S (N : Type u)] :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj
      ((AlgebraicGeometry.tilde.functor (R := S)).obj N)).IsFinitePresentation := by
  let M := (AlgebraicGeometry.tilde.functor (R := S)).obj N
  let _ : IsIso M.fromTildeΓ := inferInstance
  let B := moduleSpecΓFunctor.obj M
  let u := (AlgebraicGeometry.tilde.toTildeΓNatIso (R := S)).app N
  let _ : Module.FinitePresentation (S : Type u) (B : Type u) :=
    Module.FinitePresentation.of_equiv (R := (S : Type u))
      (M := (N : Type u)) (N := (B : Type u)) u.toLinearEquiv
  exact modulePushforward_spec_isFinitePresentation φ M hφ

end
end GromovWitten.AlgebraicGeometry.Curves
