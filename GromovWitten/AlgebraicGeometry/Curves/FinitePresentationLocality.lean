/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FinitePresentationPullback
import GromovWitten.AlgebraicGeometry.Curves.AffineFinitePresentation

/-!
# Zariski-local finite presentations

Finite presentation of a module sheaf can be glued from finite presentations on
an open cover.  The pointwise form chooses one open neighbourhood at each
point and applies the open-cover form.

-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open AlgebraicGeometry Scheme.Modules

noncomputable section

universe u u₁ u₂ v₁ v₂

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X : Scheme.{u}}

section BindFinite

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat]

private lemma presentation_map_isFinite
    {C₀ : Type u₁} [Category.{v₁} C₀] {J₀ : GrothendieckTopology C₀}
    {R₀ : Sheaf J₀ RingCat.{u}}
    [HasSheafify J₀ AddCommGrpCat] [J₀.WEqualsLocallyBijective AddCommGrpCat]
    {D₀ : Type u₂} [Category.{v₂} D₀] {K₀ : GrothendieckTopology D₀}
    {S₀ : Sheaf K₀ RingCat.{u}}
    [HasSheafify K₀ AddCommGrpCat] [K₀.WEqualsLocallyBijective AddCommGrpCat]
    (F : SheafOfModules R₀ ⥤ SheafOfModules S₀)
    [PreservesColimitsOfSize.{u, u} F]
    (η : SheafOfModules.unit S₀ ≅ F.obj (SheafOfModules.unit R₀))
    {N : SheafOfModules R₀} (P : SheafOfModules.Presentation N) [P.IsFinite] :
    (P.map F η).IsFinite := by
  refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
  · constructor
    change Finite P.generators.I
    infer_instance
  · constructor
    change Finite P.relations.I
    infer_instance

private lemma quasicoherentData_bind_isFinitePresentation
    (M : SheafOfModules R) {I : Type u} (X : I → C) (hX : J.CoversTop X)
    (D : ∀ i, SheafOfModules.QuasicoherentData (M.over (X i)))
    (hD : ∀ i, (D i).IsFinitePresentation) :
    (SheafOfModules.QuasicoherentData.bind M X hX D).IsFinitePresentation := by
  let Q := SheafOfModules.QuasicoherentData.bind M X hX D
  refine { isFinite_presentation := ?_ }
  rintro ⟨i, j⟩
  let _ : (D i).IsFinitePresentation := hD i
  let e := SheafOfModules.pushforwardPushforwardEquivalence
    ((D i).X j).iteratedSliceEquiv
      (S := (R.over (X i)).over ((D i).X j))
      (R := R.over ((D i).X j).left)
      (𝟙 _) (𝟙 _) (by
        ext : 2
        exact R.1.map_id _) (by
        ext : 2
        exact R.1.map_id _)
  let P := ((D i).presentation j).map e.inverse (.refl _)
  let _ : P.IsFinite := by
    exact presentation_map_isFinite e.inverse (.refl _) ((D i).presentation j)
  dsimp [Q, SheafOfModules.QuasicoherentData.bind]
  change (P.ofIsIso _).IsFinite
  infer_instance

end BindFinite

/-- Glue finite presentations on an open cover of a scheme. -/
lemma module_isFinitePresentation_of_over_openCover
    (M : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : IsOpenCover U)
    (hM : ∀ i, (M.over (U i)).IsFinitePresentation) :
    M.IsFinitePresentation := by
  let D : ∀ i, (M.over (U i)).QuasicoherentData := fun i ↦
    let : (M.over (U i)).IsFinitePresentation := hM i
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (M.over (U i))).choose
  have hD : ∀ i, (D i).IsFinitePresentation := fun i ↦
    let : (M.over (U i)).IsFinitePresentation := hM i
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (M.over (U i))).choose_spec
  refine { exists_quasicoherentData := ?_ }
  exact ⟨SheafOfModules.QuasicoherentData.bind M U
    ((Opens.coversTop_iff X U).mpr hU) D,
    quasicoherentData_bind_isFinitePresentation M U
      ((Opens.coversTop_iff X U).mpr hU) D hD⟩

/-- Glue finite presentations of the restrictions on an open cover. -/
lemma module_isFinitePresentation_of_presentation_openCover
    (M : X.Modules) {I : Type u} (U : I → X.Opens) (hU : IsOpenCover U)
    (hP : ∀ i, ∃ P : (M.restrict (U i).ι).Presentation, P.IsFinite) :
    M.IsFinitePresentation := by
  classical
  let P := fun i ↦ (hP i).choose
  have hP' : ∀ i, (P i).IsFinite := fun i ↦ (hP i).choose_spec
  let Q : M.QuasicoherentData := {
    I := I
    X := U
    coversTop := (Opens.coversTop_iff X U).mpr hU
    presentation := fun i ↦ modulePresentationOver (U i) (P i) }
  refine { exists_quasicoherentData := ?_ }
  refine ⟨Q, ?_⟩
  constructor
  intro i
  exact modulePresentationOver_isFinite' (U i) (P i) (hP' i)

/-- Finite presentation is local on affine pullbacks of a locally Noetherian scheme. -/
lemma module_isFinitePresentation_of_affine_pullbacks
    {X : Scheme.{u}} [IsLocallyNoetherian X] (M : X.Modules)
    (hM : ∀ U : X.affineOpens, ((Scheme.Modules.pullback U.1.ι).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  apply module_isFinitePresentation_of_presentation_openCover M (fun U : X.affineOpens ↦ U.1)
  · rw [IsOpenCover]
    exact iSup_affineOpens_eq_top X
  · intro U
    let : IsAffine U.1.toScheme := U.2
    have hP : ((Scheme.Modules.pullback U.1.ι).obj M).IsFinitePresentation := hM U
    have : (M.restrict U.1.ι).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf).prop_of_iso
        ((Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app M).symm hP
    exact presentation_of_affine_isFinitePresentation (M.restrict U.1.ι)

/-- Glue finite presentations from a finite-presentation neighbourhood at every point. -/
lemma module_isFinitePresentation_of_locally_over
    (M : X.Modules)
    (hM : ∀ x : X, ∃ U : X.Opens,
      x ∈ U ∧ (M.over U).IsFinitePresentation) :
    M.IsFinitePresentation := by
  classical
  let U : X → X.Opens := fun x ↦ (hM x).choose
  have hUmem : ∀ x : X, x ∈ U x := fun x ↦ (hM x).choose_spec.1
  have hU : IsOpenCover U := by
    apply IsOpenCover.mk
    ext x
    change x ∈ (iSup U : X.Opens) ↔ x ∈ (⊤ : X.Opens)
    rw [Opens.mem_iSup]
    constructor
    · intro _
      exact Opens.mem_top x
    · intro _
      exact ⟨x, hUmem x⟩
  apply module_isFinitePresentation_of_over_openCover M U hU
  intro x
  exact (hM x).choose_spec.2

end GromovWitten.AlgebraicGeometry.Curves
