/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Quasi-coherence of module pullback

Pullback preserves the structure sheaf and colimits, hence presentations. Restricting to the
inverse images of a cover carrying local presentations proves quasi-coherence without any
flatness or Noetherian hypothesis.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
set_option backward.isDefEq.respectTransparency false in
/-- Pullback carries the structure sheaf, viewed as a module, to the structure sheaf. -/
def modulePullbackUnitIso : (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
    SheafOfModules.unit X.ringCatSheaf := by
  let _ : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  let _ : PreservesLimit (Functor.empty.{0} (Opens Y)) (Opens.map f.base) := by
    apply preservesLimit_of_preserves_limit_cone (isTerminalTop (α := Opens Y))
    exact (isLimitMapConeEmptyConeEquiv (Opens.map f.base) ⊤).symm
      (by simpa using (isTerminalTop (α := Opens X)))
  let _ : (Opens.map f.base).Final := inferInstance
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := by
    infer_instance
  exact asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back a presentation gives a presentation of the pullback module. -/
def modulePresentationPullback {M : Y.Modules} (P : M.Presentation) :
    ((Scheme.Modules.pullback f).obj M).Presentation := by
  let _ : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  exact P.map (Scheme.Modules.pullback f) (modulePullbackUnitIso f).symm

set_option backward.isDefEq.respectTransparency false in
private def modulePresentationOver {M : X.Modules} (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation := by
  let e := Scheme.Modules.overEquiv U
  let i : e.inverse.obj ((Scheme.Modules.restrictFunctor U.ι).obj M) ≅ M.over U :=
    e.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
      e.unitIso.symm.app (M.over U)
  exact (P.map e.inverse (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).ofIsIso i.hom

open Scheme.Modules in
/-- Module pullback commutes with restriction to the inverse image of an open set. -/
def modulePullbackRestrictIso (U : Y.Opens) :
    pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι ≅
      restrictFunctor U.ι ⋙ pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl) :=
  Functor.isoWhiskerLeft _ (restrictFunctorIsoPullback _) ≪≫
    pullbackComp _ _ ≪≫ pullbackCongr (f.resLE_comp_ι le_rfl).symm ≪≫
    (pullbackComp _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictFunctorIsoPullback _).symm _

set_option backward.isDefEq.respectTransparency false in
/-- Pullback along any scheme morphism preserves quasi-coherence. -/
instance modulePullback_isQuasicoherent (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent := by
  classical
  obtain ⟨ι, U, P, hU, _⟩ := M.exists_isOpenCover_presentation
  let V : ι → X.Opens := fun i => f ⁻¹ᵁ U i
  have hV : IsOpenCover V := by
    rw [IsOpenCover] at hU ⊢
    change iSup ((Opens.map f.base).obj ∘ U) = ⊤
    rw [← Opens.map_iSup, hU]
    simp
  let Q : ((Scheme.Modules.pullback f).obj M).QuasicoherentData :=
    { I := ι
      X := V
      coversTop := by simpa only [Opens.coversTop_iff] using hV
      presentation := fun i => modulePresentationOver (V i)
        ((modulePresentationPullback (f.resLE (U i) (V i) le_rfl) (P i)).ofIsIso
          ((modulePullbackRestrictIso f (U i)).app M).inv) }
  exact Q.isQuasicoherent

end GromovWitten.AlgebraicGeometry.Curves
