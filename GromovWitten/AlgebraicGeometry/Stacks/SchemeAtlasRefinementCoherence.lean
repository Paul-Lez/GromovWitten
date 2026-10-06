/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.SchemeAtlasRefinementReverse

/-!
# The comparison 2-cell of a common scheme atlas

The overlap comparison is assembled into natural isomorphisms on scheme
fibres and then an invertible modification between the two composite chart
maps. Discreteness is used only for arrows in the represented source fibre.
-/

open CategoryTheory CategoryTheory.Limits
open GromovWitten.AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u

/-! ## Coherence of the common atlas comparison -/

namespace StackChart

variable {X : FppfStack.{u}} {A B : StackChart X}

-- Component formula for composing strong transformations.
set_option backward.isDefEq.respectTransparency false in
private lemma comp_naturality_app {U V W : FppfStack.{u}}
    (η : StackHom U V) (θ : StackHom V W) {S T : Scheme.{u}}
    (h : S ⟶ T) (x : StackFiber U T) :
    ((Pseudofunctor.StrongTrans.vcomp η θ).naturality ⟨h.op⟩).hom.toNatTrans.app x =
      (θ.appFunctor S).map ((η.naturality ⟨h.op⟩).hom.toNatTrans.app x) ≫
      (θ.naturality ⟨h.op⟩).hom.toNatTrans.app ((η.appFunctor T).obj x) := by
  have hc := congrArg (fun k => k.toNatTrans.app x)
    (Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom η θ ⟨h.op⟩)
  change ((Pseudofunctor.StrongTrans.vcomp η θ).naturality ⟨h.op⟩).hom.toNatTrans.app x = _ at hc
  simp at hc
  exact hc.trans (Category.id_comp _)

-- The scheme-map naturality arrow is the inverse represented compositor.
-- Its image under the chart is governed by strong-transformation coherence.
set_option backward.isDefEq.respectTransparency false in
private lemma schemeComp_naturality (C : StackChart X)
    {R S T : Scheme.{u}} (h : R ⟶ S) (g : S ⟶ T) (k : T ⟶ C.scheme) :
    ((Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSchemeHom k) C.map).naturality
      ⟨h.op⟩).hom.toNatTrans.app (Discrete.mk g) ≫
      (stackPullback X h).map (C.objPullbackIso g k).hom ≫
      (stackPullbackCompIso X h g (C.obj T k)).hom =
        (C.objPullbackIso (h ≫ g) k).hom := by
  rw [comp_naturality_app]
  have hd : ((FppfStack.mapOfSchemeHom k).naturality ⟨h.op⟩).hom.toNatTrans.app
      (Discrete.mk g) =
      (stackPullbackCompIso (representedStack C.scheme) h g (Discrete.mk k)).inv := by
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  rw [hd]
  have hc := stackHomNaturalityCompPullback C.map h g (Discrete.mk k)
  have hc' := congrArg (fun z => (C.map.appFunctor R).map
    (stackPullbackCompIso (representedStack C.scheme) h g (Discrete.mk k)).inv ≫ z) hc
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id] at hc'
  rw [(C.map.appFunctor R).map_id, Category.id_comp] at hc'
  simpa only [Category.assoc, objPullbackIso, Iso.app_hom, Cat.Hom.toNatIso_hom] using! hc'.symm

/-- The overlap comparison as an isomorphism of functors on a scheme fibre. -/
noncomputable def commonSchemeAtlasComparisonAt
    (p : B.PullbackPresentation A.scheme
      (A.obj A.scheme (𝟙 A.scheme)))
    (S : Scheme.{u}) :
    (Pseudofunctor.StrongTrans.vcomp
      (FppfStack.mapOfSchemeHom p.fst) A.map).app
        (LocallyDiscrete.mk (Opposite.op S)) ≅
      (Pseudofunctor.StrongTrans.vcomp
        (FppfStack.mapOfSchemeHom p.snd) B.map).app
          (LocallyDiscrete.mk (Opposite.op S)) := by
  apply Cat.Hom.isoMk
  refine NatIso.ofComponents (fun x => commonSchemeAtlasComparison p x.as) ?_
  intro x y f
  have hxy : x = y := by
    apply Discrete.ext
    exact Discrete.eq_of_hom f
  subst y
  have hf : f = 𝟙 x := by
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  subst f
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The invertible comparison 2-cell between the two maps from the common atlas. -/
noncomputable def commonSchemeAtlasComparisonIso
    (p : B.PullbackPresentation A.scheme
      (A.obj A.scheme (𝟙 A.scheme))) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (FppfStack.mapOfSchemeHom p.fst) A.map)
      (Pseudofunctor.StrongTrans.vcomp
        (FppfStack.mapOfSchemeHom p.snd) B.map) := by
  let e := Pseudofunctor.StrongTrans.isoMk
    (fun (a : LocallyDiscrete (Opposite Scheme.{u})) =>
      commonSchemeAtlasComparisonAt p a.as.unop)
    (by
      intro a b f
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext x
      dsimp [commonSchemeAtlasComparisonAt]
      let h : b.as.unop ⟶ a.as.unop := f.as.unop
      let g : a.as.unop ⟶ p.space := x.as
      change (commonSchemeAtlasComparison p (h ≫ g)).hom ≫
        ((Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSchemeHom p.snd) B.map).naturality
          ⟨h.op⟩).hom.toNatTrans.app (Discrete.mk g) =
        ((Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSchemeHom p.fst) A.map).naturality
          ⟨h.op⟩).hom.toNatTrans.app (Discrete.mk g) ≫
          (stackPullback X h).map (commonSchemeAtlasComparison p g).hom
      -- Cancel an invertible tail; no target-stack arrow is discarded.
      let tail := ((stackPullback X h).mapIso (B.objPullbackIso g p.snd)).trans
        (stackPullbackCompIso X h g (B.obj p.space p.snd))
      apply (cancel_mono tail.hom).mp
      dsimp only [tail, Iso.trans_hom, Functor.mapIso_hom]
      simp only [Category.assoc]
      rw [schemeComp_naturality B h g p.snd]
      simp only [commonSchemeAtlasComparison, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, Functor.map_comp, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      have hb : (stackPullback X h).map (B.objPullbackIso g p.snd).inv ≫
          (stackPullback X h).map (B.objPullbackIso g p.snd).hom = 𝟙 _ := by
        rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
      rw [reassoc_of% hb]
      -- Move the universal comparison through the target pullback compositor.
      let e0 := (A.identityObjectPullbackComparison p.fst).trans p.comparison.symm
      have hn := (Cat.Hom.toNatIso
        (X.toPseudofunctor.mapComp ⟨g.op⟩ ⟨h.op⟩)).inv.naturality e0.hom
      change (stackPullback X h).map ((stackPullback X g).map e0.hom) ≫
          (stackPullbackCompIso X h g (B.obj p.space p.snd)).hom =
        (stackPullbackCompIso X h g (A.obj p.space p.fst)).hom ≫
          (stackPullback X (h ≫ g)).map e0.hom at hn
      dsimp only [e0, Iso.trans_hom, Iso.symm_hom] at hn
      simp only [Functor.map_comp, Category.assoc] at hn
      rw [hn]
      rw [reassoc_of% schemeComp_naturality A h g p.fst])
  exact
    { hom := e.hom.as
      inv := e.inv.as
      hom_inv_id := congrArg Pseudofunctor.StrongTrans.Hom.as e.hom_inv_id
      inv_hom_id := congrArg Pseudofunctor.StrongTrans.Hom.as e.inv_hom_id }

end StackChart

end GromovWitten.AlgebraicGeometry
