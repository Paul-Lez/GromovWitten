/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.SchemeAtlasRefinement
import GromovWitten.AlgebraicGeometry.Stacks.PresentationTransport

/-!
# Chart presentations as presentations of stack morphisms

A scheme presentation of a chart pullback gives a presentation of its induced
stack morphism. The comparison lemmas retain the isomorphism in the target
stack; only the represented source fibre is discrete. Consequently any
representable morphism property of a chart also holds for its stack morphism.
-/

open CategoryTheory CategoryTheory.Limits
open GromovWitten.AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackChart

variable {X : FppfStack.{u}} {A : StackChart X}

set_option backward.isDefEq.respectTransparency false in
lemma stackMorphismInducedComparison_chart_raw'
    {T U S : Scheme.{u}} {y : StackFiber X T}
    (fst : U ⟶ T) (snd : U ⟶ A.scheme)
    (universal : A.obj U snd ≅ (stackPullback X fst).obj y)
    (m : S ⟶ U) (x : StackFiber (representedStack A.scheme) S)
    (objectIso : x ≅ (stackPullback (representedStack A.scheme) m).obj
      (Discrete.mk (ULift.up snd))) :
    stackMorphismInducedComparison A.map fst (Discrete.mk (ULift.up snd)) y universal
      m x objectIso =
      (A.objIsoOfEq
          (congrArg ULift.down (Discrete.eq_of_hom objectIso.hom)).symm).symm.trans
        (A.inducedComparison fst snd universal m) := by
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
  have hdown : x = m ≫ snd := congrArg ULift.down h
  have hd : (Discrete.eqToIso h).hom = Discrete.eqToHom h := by rfl
  have hi : (A.map.appFunctor S).map (Discrete.eqToHom h) =
      (A.objIsoOfEq hdown).hom := by
    exact (A.objIsoOfEq_hom hdown).symm
  have hflip : (A.objIsoOfEq hdown.symm).inv = (A.objIsoOfEq hdown).hom := by
    cases hdown
    simp only [objIsoOfEq, Iso.refl_inv, Iso.refl_hom]
  rw [hd, hi, hflip]

set_option backward.isDefEq.respectTransparency false in
/-- Convert a chart pullback presentation into a stack-morphism presentation,
with the same representing scheme and projection. -/
noncomputable def toStackMorphismPresentation {T : Scheme.{u}} {y : StackFiber X T}
    (p : A.PullbackPresentation T y) : StackMorphismPresentation A.map T y where
  space := p.space
  map := p.fst
  object := Discrete.mk (ULift.up p.snd)
  comparison := p.comparison
  lift toBase x c := p.lift toBase x.as.down c
  lift_map toBase x c := p.lift_fst toBase x.as.down c
  liftObjectIso toBase x c :=
    Discrete.eqToIso (congrArg ULift.up (p.lift_snd toBase x.as.down c).symm)
  lift_compatible toBase x c := by
    obtain ⟨⟨x⟩⟩ := x
    obtain ⟨hf, hs, hc⟩ := p.lift_compatible toBase _ c
    refine ⟨hf, ?_⟩
    rw [stackMorphismInducedComparison_chart_raw]
    simpa only [Iso.trans_assoc] using hc
  liftObjectIso_unique toBase x c objectIso compatible := by
    apply Iso.ext
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  lift_unique toBase x c g objectIso compatible := by
    obtain ⟨⟨x⟩⟩ := x
    obtain ⟨hf, hc⟩ := compatible
    have hs := (congrArg ULift.down (Discrete.eq_of_hom objectIso.hom)).symm
    apply p.lift_unique toBase _ c g
    refine ⟨hf, hs, ?_⟩
    rw [stackMorphismInducedComparison_chart_raw] at hc
    simpa only [Iso.trans_assoc] using hc

end StackChart

namespace StackHom

theorem hasRepresentablePropertyRaw_of_chart
    {Y : FppfStack.{u}} {A : StackChart Y} (P : MorphismProperty Scheme.{u})
    (hA : A.HasRepresentableProperty P) :
    A.map.HasRepresentablePropertyRaw P := by
  intro T y
  obtain ⟨p⟩ := hA.1 T y
  exact ⟨⟨StackChart.toStackMorphismPresentation p, hA.2 T y p⟩⟩

theorem hasRepresentableProperty_of_chart
    {X : FppfStack.{u}} {A : StackChart X} (P : MorphismProperty Scheme.{u})
    (hA : A.HasRepresentableProperty P) :
    A.map.HasRepresentableProperty P :=
  (hasRepresentableProperty_iff_raw P).mpr
    (StackHom.hasRepresentablePropertyRaw_of_chart (A := A) P hA)

end StackHom

end GromovWitten.AlgebraicGeometry
