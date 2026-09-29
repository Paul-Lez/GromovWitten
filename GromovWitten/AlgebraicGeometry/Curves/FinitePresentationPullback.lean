/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPullback

/-!
# Finite presentations and module pullback

Pullback carries a finite local presentation to a finite local presentation.  The
cover is pulled back along the scheme morphism; the presentation is transported
across the restriction-pullback isomorphism and then localized on the inverse
image open.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- Transport a presentation backwards across an isomorphism. -/
def modulePresentationOfIso {M N : X.Modules} (e : M ≅ N) (P : N.Presentation) :
    M.Presentation := by
  let g : N ⟶ M := e.inv
  letI hIso : IsIso g :=
    ⟨⟨e.hom, by dsimp [g]; exact e.inv_hom_id,
      by dsimp [g]; exact e.hom_inv_id⟩⟩
  exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ N M g hIso P

set_option backward.isDefEq.respectTransparency false in
/-- Finiteness is preserved by `modulePresentationOfIso`. -/
lemma modulePresentationOfIso_isFinite {M N : X.Modules} (e : M ≅ N)
    (P : N.Presentation) [P.IsFinite] : (modulePresentationOfIso e P).IsFinite := by
  refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
  · constructor
    dsimp [modulePresentationOfIso, SheafOfModules.Presentation.ofIsIso]
    infer_instance
  · constructor
    dsimp [modulePresentationOfIso, SheafOfModules.Presentation.ofIsIso]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Transport a presentation on an open subscheme back to the restriction. -/
def modulePresentationRestrict {M : X.Modules} (U : X.Opens)
    (P : (M.over U).Presentation) : (M.restrict U.ι).Presentation := by
  let e := Scheme.Modules.overEquiv U
  exact (P.map e.functor (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm).ofIsIso
    ((Scheme.Modules.overFunctorEquiv U).app M).hom

set_option backward.isDefEq.respectTransparency false in
/-- Finiteness is preserved by `modulePresentationRestrict`. -/
lemma modulePresentationRestrict_isFinite {M : X.Modules} (U : X.Opens)
    (P : (M.over U).Presentation) [P.IsFinite] :
    (modulePresentationRestrict U P).IsFinite := by
  let e := Scheme.Modules.overEquiv U
  let Q := P.map e.functor (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm
  have hQ : Q.IsFinite := by
    refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
    · constructor
      rw [show Q.generators.I = P.generators.I by
        dsimp [Q]; rw [SheafOfModules.Presentation.map_generators_I]]
      infer_instance
    · constructor
      rw [show Q.relations.I = P.relations.I by
        dsimp [Q]; rw [SheafOfModules.Presentation.map_relations_I]]
      infer_instance
  dsimp [modulePresentationRestrict]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Finiteness is preserved by pulling back a presentation. -/
lemma modulePresentationPullback_isFinite {M : Y.Modules} (P : M.Presentation)
    [P.IsFinite] : (modulePresentationPullback f P).IsFinite := by
  refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
  · constructor
    rw [modulePresentationPullback, SheafOfModules.Presentation.map_generators_I]
    infer_instance
  · constructor
    rw [modulePresentationPullback, SheafOfModules.Presentation.map_relations_I]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Finiteness is preserved by transporting a presentation to an open subscheme. -/
lemma modulePresentationOver_isFinite {M : X.Modules} (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) [P.IsFinite] :
    (modulePresentationOver U P).IsFinite := by
  let e := Scheme.Modules.overEquiv U
  let i : e.inverse.obj ((Scheme.Modules.restrictFunctor U.ι).obj M) ≅ M.over U :=
    e.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
      e.unitIso.symm.app (M.over U)
  let Q := P.map e.inverse (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  have hQ : Q.IsFinite := by
    refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
    · constructor
      rw [show Q.generators.I = P.generators.I by
        dsimp [Q]; rw [SheafOfModules.Presentation.map_generators_I]]
      infer_instance
    · constructor
      rw [show Q.relations.I = P.relations.I by
        dsimp [Q]; rw [SheafOfModules.Presentation.map_relations_I]]
      infer_instance
  dsimp [modulePresentationOver]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Explicit-proof form of `modulePresentationOver_isFinite`. -/
lemma modulePresentationOver_isFinite' {M : X.Modules} (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) (hP : P.IsFinite) :
    (modulePresentationOver U P).IsFinite := by
  let _ : P.IsFinite := hP
  exact modulePresentationOver_isFinite U P

set_option backward.isDefEq.respectTransparency false in
/-- Pullback preserves finite presentation. -/
instance modulePullback_isFinitePresentation {M : Y.Modules}
    [M.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let V : q.I → X.Opens := fun i => f ⁻¹ᵁ q.X i
  have hqcover : IsOpenCover q.X := by
    exact (Opens.coversTop_iff _ _).mp q.coversTop
  have hV : IsOpenCover V := by
    rw [IsOpenCover]
    change iSup ((Opens.map f.base).obj ∘ q.X) = ⊤
    rw [← Opens.map_iSup, hqcover]
    simp
  let Q : ((Scheme.Modules.pullback f).obj M).QuasicoherentData :=
    { I := q.I
      X := V
      coversTop := by simpa only [Opens.coversTop_iff] using hV
      presentation := fun i => by
        let P := modulePresentationRestrict (q.X i) (q.presentation i)
        let PB := modulePresentationPullback (f.resLE (q.X i) (V i) le_rfl) P
        exact modulePresentationOver (V i) (modulePresentationOfIso
          ((modulePullbackOpenRestrictIso f (q.X i)).app M) PB) }
  refine { exists_quasicoherentData := ?_ }
  refine ⟨Q, ?_⟩
  refine { isFinite_presentation := ?_ }
  intro i
  let _ : (q.presentation i).IsFinite := hq.isFinite_presentation i
  let P := modulePresentationRestrict (q.X i) (q.presentation i)
  have hP : P.IsFinite := by
    exact modulePresentationRestrict_isFinite (q.X i) (q.presentation i)
  let _ : P.IsFinite := hP
  let PB := modulePresentationPullback (f.resLE (q.X i) (V i) le_rfl) P
  have hPB : PB.IsFinite := by
    exact modulePresentationPullback_isFinite (f.resLE (q.X i) (V i) le_rfl) P
  let _ : PB.IsFinite := hPB
  let R := modulePresentationOfIso ((modulePullbackOpenRestrictIso f (q.X i)).app M) PB
  have hR : R.IsFinite := modulePresentationOfIso_isFinite _ _
  let _ : R.IsFinite := hR
  simpa only [Q] using (modulePresentationOver_isFinite' (V i) R hR)

end GromovWitten.AlgebraicGeometry.Curves
