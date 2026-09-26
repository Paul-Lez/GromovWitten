/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.AtlasRefinement

/-!
# Scheme presentations used by atlas refinements

The represented stack map associated to an actual scheme morphism has an explicit
scheme valued presentation.  This is the small bridge needed when a chart map is
factored through a scheme projection: the construction below retains the full
object comparison and its classifying equation.
-/

open CategoryTheory CategoryTheory.Limits
open GromovWitten.AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u

namespace FppfStack

/-! ## The presentation of a promoted scheme morphism -/

/-- The actual scheme pullback presenting the promoted map of represented stacks. -/
noncomputable def schemeHomPresentation {S T : Scheme.{u}} (f : S ⟶ T)
    {T₀ : Scheme.{u}} (y : StackFiber (representedStack T) T₀) :
    StackMorphismPresentation (mapOfSchemeHom f) T₀ y where
  space := Limits.pullback f y.as.down
  map := Limits.pullback.snd f y.as.down
  object := Discrete.mk (ULift.up (Limits.pullback.fst f y.as.down))
  comparison := by
    apply Discrete.eqToIso
    apply ULift.ext
    change Limits.pullback.fst f y.as.down ≫ f =
      (Limits.pullback.snd f y.as.down) ≫ y.as.down
    exact Limits.pullback.condition
  lift toBase x comparison :=
    Limits.pullback.lift x.as.down toBase
      (congrArg ULift.down (Discrete.eq_of_hom comparison.hom))
  lift_map toBase x comparison := by
    apply Limits.pullback.lift_snd
  liftObjectIso toBase x comparison := by
    apply Discrete.eqToIso
    apply ULift.ext
    change x.as.down =
      Limits.pullback.lift x.as.down toBase
          (congrArg ULift.down (Discrete.eq_of_hom comparison.hom)) ≫
        Limits.pullback.fst f y.as.down
    exact (Limits.pullback.lift_fst _ _ _).symm
  lift_compatible toBase x comparison := by
    refine ⟨?_, ?_⟩
    · exact Limits.pullback.lift_snd _ _ _
    · apply Iso.ext
      change @Eq (ULift (PLift (_ = _))) _ _
      apply Subsingleton.elim
  liftObjectIso_unique toBase x comparison objectIso compatible := by
    cases x
    apply Iso.ext
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  lift_unique toBase x comparison g objectIso compatible := by
    obtain ⟨map_eq, hcomp⟩ := compatible
    have hx : x = Discrete.mk x.as := by
      apply Discrete.ext
      rfl
    rw [hx] at objectIso
    apply Limits.pullback.hom_ext
    · have hobj := objectIso.hom
      change Discrete.mk _ ⟶ Discrete.mk _ at hobj
      have hobj' := Discrete.eq_of_hom hobj
      have hobj'' : x.as.down = g ≫ Limits.pullback.fst f y.as.down :=
        congrArg ULift.down hobj'
      exact hobj''.symm.trans (Limits.pullback.lift_fst _ _ _).symm
    · exact map_eq.trans (Limits.pullback.lift_snd _ _ _).symm

/-- A promoted scheme morphism has a representable property whenever its scheme map has that
property; the representing pullbacks are the explicit scheme pullbacks above. -/
theorem mapOfSchemeHom_hasRepresentableProperty
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {S T : Scheme.{u}} (f : S ⟶ T) (hf : P f) :
    (mapOfSchemeHom f).HasRepresentableProperty P := by
  refine ⟨mapOfSchemeHom f, ⟨StackIso2.refl _⟩, ?_⟩
  intro T₀ y
  refine ⟨⟨schemeHomPresentation f y, ?_⟩⟩
  exact P.pullback_snd f y.as.down hf

end FppfStack

namespace StackChart

variable {X : FppfStack.{u}} {A : StackChart X}

set_option backward.isDefEq.respectTransparency false in
/-- The induced comparison for a chart presentation is the chart comparison after the
canonical equality isomorphism from the represented source object.  This is the coherence
identity used when transporting an actual chart presentation through a scheme map. -/
lemma stackMorphismInducedComparison_chart_raw
    {T S : Scheme.{u}} {y : StackFiber X T}
    (p : A.PullbackPresentation T y)
    (m : S ⟶ p.space) (x : StackFiber (representedStack A.scheme) S)
    (objectIso : x ≅ (stackPullback (representedStack A.scheme) m).obj
      (Discrete.mk (ULift.up p.snd))) :
    stackMorphismInducedComparison A.map p.fst (Discrete.mk (ULift.up p.snd)) y
      p.comparison m x objectIso =
      (A.objIsoOfEq
          (congrArg ULift.down (Discrete.eq_of_hom objectIso.hom)).symm).symm.trans
        (A.inducedComparison p.fst p.snd p.comparison m) := by
  obtain ⟨⟨x⟩⟩ := x
  have hobj : objectIso = Discrete.eqToIso (Discrete.eq_of_hom objectIso.hom) := by
    apply Iso.ext
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  rw [hobj]
  apply Iso.ext
  simp only [stackMorphismInducedComparison, inducedComparison, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  let h := Discrete.eq_of_hom objectIso.hom
  have hdown : x = m ≫ p.snd := congrArg ULift.down h
  have hd : (Discrete.eqToIso h).hom = Discrete.eqToHom h := by rfl
  have hi : (A.map.appFunctor S).map (Discrete.eqToHom h) =
      (A.objIsoOfEq hdown).hom := by
    exact (A.objIsoOfEq_hom hdown).symm
  have hflip : (A.objIsoOfEq hdown.symm).inv = (A.objIsoOfEq hdown).hom := by
    cases hdown
    simp only [objIsoOfEq, Iso.refl_inv, Iso.refl_hom]
  rw [hd, hi, hflip]

end StackChart

end GromovWitten.AlgebraicGeometry
