/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.StackProdCoherence

/-!
# Pasting of genuine two-pullbacks

This file proves the pasting law for genuine bicategorical pullbacks of fppf stacks and
deduces the composition half of pseudofunctoriality of base change of cone stacks.

## Main results

* `StackTwoPullback.projectionIso2`: two morphisms to a genuine two-pullback are 2-isomorphic
  as soon as their two projections are, compatibly with the comparison cell.  This strengthens
  the uniqueness clause `StackTwoPullback.IsBilimit.lift_unique`, which produces an invertible
  2-cell with no control at all on its projections, and it is what makes the pasting law
  provable.
* `StackTwoPullback.pastingEquivalence`: the **pasting law**.  If `P` is a genuine two-pullback
  of `p` along `g`, `Q` is a genuine two-pullback of `P.snd` along `f`, and `R` is any genuine
  two-pullback of `p` along `f ≫ g`, then `Q.pullback` and `R.pullback` are equivalent as fppf
  stacks.  `StackTwoPullback.pastingEquivalenceFst` and
  `StackTwoPullback.pastingEquivalenceSnd` identify the two projections of `R` with the
  composite of the two first projections and with the second projection of `Q`.
* `ConeStack.baseChangeCompEquivalence`: the **composition half of the pseudofunctoriality of
  base change** of cone stacks, together with
  `ConeStack.baseChangeCompEquivalenceProjection`, `ConeStack.baseChangeCompEquivalenceFst`
  and `ConeStack.baseChangeCompEquivalenceVertex`, which say that the comparison is compatible
  with the projection to the new base, with the projection to the original total stack, and
  with the vertices.

## What is not done

The comparison is constructed as an equivalence of total stacks compatible with the
projections and the vertices; it is **not** upgraded to a `ConeStack.Iso`, which would
additionally require the compatibility of the comparison with the scalar contractions (the
`equivariant` field of `ConeStack.Hom`) in both directions.  No associativity coherence for
three composable base changes is proved.
-/

open CategoryTheory
open CategoryTheory.Pseudofunctor.StrongTrans (vcomp)

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackIso2

/-- The fibre components of the inverse of an associator are identities. -/
@[simp]
theorem associator_appIso_inv_app {A B C D : FppfStack.{u}}
    (q : StackHom A B) (r : StackHom B C) (s : StackHom C D)
    (U : Scheme.{u}) (x : StackFiber A U) :
    ((StackIso2.associator q r s).appIso U).inv.app x = 𝟙 _ := rfl

end StackIso2

namespace StackTwoPullback

/-! ### Right whiskering of modifications -/

section Whiskering

variable {A B D : FppfStack.{u}} {h k l : StackHom A B}

/-- Right whiskering of modifications is compatible with vertical composition. -/
theorem whiskerRightModification_vcomp
    (eta : Pseudofunctor.StrongTrans.Modification h k)
    (theta : Pseudofunctor.StrongTrans.Modification k l) (q : StackHom B D) :
    whiskerRightModification
        (Pseudofunctor.StrongTrans.Modification.vcomp eta theta) q =
      Pseudofunctor.StrongTrans.Modification.vcomp
        (whiskerRightModification eta q) (whiskerRightModification theta q) := by
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext a
  simp only [Pseudofunctor.StrongTrans.Modification.vcomp]
  exact Bicategory.comp_whiskerRight _ _ _

/-- Right whiskering of the identity modification is the identity modification. -/
theorem whiskerRightModification_id (q : StackHom B D) :
    whiskerRightModification
        (Pseudofunctor.StrongTrans.Modification.id h) q =
      Pseudofunctor.StrongTrans.Modification.id (vcomp h q) := by
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext a
  simp only [Pseudofunctor.StrongTrans.Modification.id]
  exact Bicategory.id_whiskerRight _ _

/-- The fibre component of a right whiskering of modifications. -/
theorem whiskerRightModification_toNatTrans_app
    (eta : Pseudofunctor.StrongTrans.Modification h k) (q : StackHom B D)
    (U : Scheme.{u}) (x : StackFiber A U) :
    ((whiskerRightModification eta q).app
        (LocallyDiscrete.mk (Opposite.op U))).toNatTrans.app x =
      (StackHom.appFunctor q U).map
        ((eta.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans.app x) :=
  rfl

end Whiskering

/-- Cancelling the image of an identity arrow at the end of a triple composite.  The instance
path of these identities in stack fibres is not syntactically the one `Functor.map_id` expects,
so the cancellation has to be performed by an abstract lemma applied at default
transparency. -/
theorem comp3_mapId {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {a : C}
    {d1 d2 d3 : D} (v1 : d1 ⟶ d2) (v2 : d2 ⟶ d3) (v3 : d3 ⟶ F.obj a) :
    v1 ≫ v2 ≫ v3 ≫ F.map (𝟙 a) = v1 ≫ v2 ≫ v3 := by
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Cancelling a trailing identity arrow in a triple composite, at default transparency. -/
theorem comp3_id {C : Type*} [Category C] {a b c d : C} (v1 : a ⟶ b) (v2 : b ⟶ c)
    (v3 : c ⟶ d) (w : a ⟶ d) (h : v1 ≫ v2 ≫ v3 = w) : v1 ≫ v2 ≫ v3 ≫ 𝟙 d = w := by
  rw [Category.comp_id, h]

/-- Inverting a commuting square whose two horizontal edges are isomorphisms. -/
theorem inv_comm_square {C : Type*} [Category C] {a b c d : C} (A : a ≅ b) (B : c ≅ d)
    (u : b ⟶ d) (v : a ⟶ c) (hyp : A.hom ≫ u = v ≫ B.hom) :
    A.inv ≫ v = u ≫ B.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, hyp, Category.assoc, B.hom_inv_id,
    Category.comp_id]

/-! ### Lifting a compatible pair of invertible projected 2-cells -/

section ProjectionIso

variable {X Y Z : FppfStack.{u}} {f : StackHom X Z} {g : StackHom Y Z}

/-- Compatibility of a pair of projected 2-cells with the comparison cell of a two-pullback.
This is the 2-dimensional analogue of `ConeLiftClassifies`. -/
def ProjectedCompat (P : StackTwoPullback f g) {T : FppfStack.{u}}
    {h k : StackHom T P.pullback}
    (efst : StackIso2 (vcomp h P.fst) (vcomp k P.fst))
    (esnd : StackIso2 (vcomp h P.snd) (vcomp k P.snd)) : Prop :=
  ∀ (U : Scheme.{u}) (x : StackFiber T U),
    (StackHom.appFunctor f U).map ((efst.appIso U).hom.app x) ≫
        (P.comparison.appIso U).hom.app ((StackHom.appFunctor k U).obj x) =
      (P.comparison.appIso U).hom.app ((StackHom.appFunctor h U).obj x) ≫
        (StackHom.appFunctor g U).map ((esnd.appIso U).hom.app x)

variable (P : StackTwoPullback f g) {T : FppfStack.{u}}
  {h k : StackHom T P.pullback}
  (efst : StackIso2 (vcomp h P.fst) (vcomp k P.fst))
  (esnd : StackIso2 (vcomp h P.snd) (vcomp k P.snd))

/-- A compatible pair of invertible projected 2-cells, as a `ProjectionTwoCell`. -/
def projectionTwoCellHom (compat : ProjectedCompat P efst esnd) :
    ProjectionTwoCell P h k where
  fst := efst.hom
  snd := esnd.hom
  compatibility := compat

/-- The inverses of a compatible pair of invertible projected 2-cells are again compatible. -/
theorem projectedCompat_symm (compat : ProjectedCompat P efst esnd) :
    ProjectedCompat P efst.symm esnd.symm := by
  intro U x
  exact inv_comm_square ((StackHom.appFunctor f U).mapIso ((efst.appIso U).app x))
    ((StackHom.appFunctor g U).mapIso ((esnd.appIso U).app x)) _ _ (compat U x)

variable (PG : Genuine f g) {h k : StackHom T PG.pullback}
  (efst' : StackIso2 (vcomp h PG.fst) (vcomp k PG.fst))
  (esnd' : StackIso2 (vcomp h PG.snd) (vcomp k PG.snd))

/-- The modification with prescribed projections, produced by the hom-category bijection of a
genuine two-pullback. -/
noncomputable def projectionModification
    (compat : ProjectedCompat PG.toStackTwoPullback efst' esnd') :
    Pseudofunctor.StrongTrans.Modification h k :=
  ((PG.bilimit.projectedTwoCell_bijective h k).2
    (projectionTwoCellHom PG.toStackTwoPullback efst' esnd' compat)).choose

/-- The first projection of `projectionModification` is the prescribed one. -/
theorem projectionModification_fst
    (compat : ProjectedCompat PG.toStackTwoPullback efst' esnd') :
    whiskerRightModification (projectionModification PG efst' esnd' compat) PG.fst =
      efst'.hom :=
  congrArg ProjectionTwoCell.fst
    ((PG.bilimit.projectedTwoCell_bijective h k).2
      (projectionTwoCellHom PG.toStackTwoPullback efst' esnd' compat)).choose_spec

/-- The second projection of `projectionModification` is the prescribed one. -/
theorem projectionModification_snd
    (compat : ProjectedCompat PG.toStackTwoPullback efst' esnd') :
    whiskerRightModification (projectionModification PG efst' esnd' compat) PG.snd =
      esnd'.hom :=
  congrArg ProjectionTwoCell.snd
    ((PG.bilimit.projectedTwoCell_bijective h k).2
      (projectionTwoCellHom PG.toStackTwoPullback efst' esnd' compat)).choose_spec

/-- Two morphisms to a genuine two-pullback are 2-isomorphic as soon as their two projections
are, compatibly with the comparison 2-cell.  This strengthens the uniqueness clause of
`IsBilimit`, which produces an invertible 2-cell without any control on its projections. -/
noncomputable def projectionIso2
    (compat : ProjectedCompat PG.toStackTwoPullback efst' esnd') : StackIso2 h k where
  hom := projectionModification PG efst' esnd' compat
  inv := projectionModification PG efst'.symm esnd'.symm
    (projectedCompat_symm PG.toStackTwoPullback efst' esnd' compat)
  hom_inv_id := by
    apply (PG.bilimit.projectedTwoCell_bijective h h).1
    apply ProjectionTwoCell.ext
    · dsimp only [projectedTwoCell]
      rw [whiskerRightModification_vcomp, whiskerRightModification_id,
        projectionModification_fst, projectionModification_fst]
      exact efst'.hom_inv_id
    · dsimp only [projectedTwoCell]
      rw [whiskerRightModification_vcomp, whiskerRightModification_id,
        projectionModification_snd, projectionModification_snd]
      exact esnd'.hom_inv_id
  inv_hom_id := by
    apply (PG.bilimit.projectedTwoCell_bijective k k).1
    apply ProjectionTwoCell.ext
    · dsimp only [projectedTwoCell]
      rw [whiskerRightModification_vcomp, whiskerRightModification_id,
        projectionModification_fst, projectionModification_fst]
      exact efst'.inv_hom_id
    · dsimp only [projectedTwoCell]
      rw [whiskerRightModification_vcomp, whiskerRightModification_id,
        projectionModification_snd, projectionModification_snd]
      exact esnd'.inv_hom_id

/-- The first projected component of `projectionIso2` is the prescribed one. -/
theorem projectionIso2_fst_app
    (compat : ProjectedCompat PG.toStackTwoPullback efst' esnd')
    (U : Scheme.{u}) (x : StackFiber T U) :
    (StackHom.appFunctor PG.fst U).map
        (((projectionIso2 PG efst' esnd' compat).appIso U).hom.app x) =
      (efst'.appIso U).hom.app x :=
  congrArg
    (fun m ↦ ((Pseudofunctor.StrongTrans.Modification.app m
      (LocallyDiscrete.mk (Opposite.op U))).toNatTrans).app x)
    (projectionModification_fst PG efst' esnd' compat)

/-- The second projected component of `projectionIso2` is the prescribed one. -/
theorem projectionIso2_snd_app
    (compat : ProjectedCompat PG.toStackTwoPullback efst' esnd')
    (U : Scheme.{u}) (x : StackFiber T U) :
    (StackHom.appFunctor PG.snd U).map
        (((projectionIso2 PG efst' esnd' compat).appIso U).hom.app x) =
      (esnd'.appIso U).hom.app x :=
  congrArg
    (fun m ↦ ((Pseudofunctor.StrongTrans.Modification.app m
      (LocallyDiscrete.mk (Opposite.op U))).toNatTrans).app x)
    (projectionModification_snd PG efst' esnd' compat)

end ProjectionIso


/-! ### Fibre components of vertical composites and self-cones -/

section Helpers

variable {A B C : FppfStack.{u}}

/-- The fibre functor of a vertical composite, on objects. -/
theorem vcomp_appFunctor_obj (a : StackHom A B) (b : StackHom B C)
    (U : Scheme.{u}) (x : StackFiber A U) :
    (StackHom.appFunctor (vcomp a b) U).obj x =
      (StackHom.appFunctor b U).obj ((StackHom.appFunctor a U).obj x) := rfl

/-- The fibre functor of a vertical composite, on morphisms. -/
theorem vcomp_appFunctor_map (a : StackHom A B) (b : StackHom B C)
    (U : Scheme.{u}) {x y : StackFiber A U} (m : x ⟶ y) :
    (StackHom.appFunctor (vcomp a b) U).map m =
      (StackHom.appFunctor b U).map ((StackHom.appFunctor a U).map m) := rfl

variable {X Y Z : FppfStack.{u}} {f : StackHom X Z} {g : StackHom Y Z}

/-- The first leg of the self-cone of a two-pullback presentation. -/
theorem selfCone_fst (P : StackTwoPullback f g) : P.selfCone.fst = P.fst := rfl

/-- The second leg of the self-cone of a two-pullback presentation. -/
theorem selfCone_snd (P : StackTwoPullback f g) : P.selfCone.snd = P.snd := rfl

/-- The comparison cell of the self-cone of a two-pullback presentation. -/
theorem selfCone_comparison (P : StackTwoPullback f g) :
    P.selfCone.comparison = P.comparison := rfl

end Helpers

/-! ### The canonical genuine two-pullback, in terms of its explicit lifts -/

section Canonical

variable {X Y Z : FppfStack.{u}} (q : StackHom X Z) (r : StackHom Y Z)

/-- The first projection of the canonical genuine two-pullback. -/
theorem canonicalGenuine_fst : (canonicalGenuine q r).fst = fiberTwoPullbackFst q r := rfl

/-- The second projection of the canonical genuine two-pullback. -/
theorem canonicalGenuine_snd : (canonicalGenuine q r).snd = fiberTwoPullbackSnd q r := rfl

/-- The comparison cell of the canonical genuine two-pullback. -/
theorem canonicalGenuine_comparison :
    (canonicalGenuine q r).comparison = (canonical q r).comparison := rfl

variable {T : FppfStack.{u}} (c : Cone (f := q) (g := r) T)

/-- The bilimit lift of the canonical genuine two-pullback. -/
theorem canonicalGenuine_lift :
    (canonicalGenuine q r).bilimit.lift c = canonicalLift q r c := rfl

/-- The first projection comparison of the canonical bilimit lift. -/
theorem canonicalGenuine_lift_fst :
    (canonicalGenuine q r).bilimit.lift_fst c = canonicalLiftFstIso q r c := rfl

/-- The second projection comparison of the canonical bilimit lift. -/
theorem canonicalGenuine_lift_snd :
    (canonicalGenuine q r).bilimit.lift_snd c = canonicalLiftSndIso q r c := rfl

end Canonical

/-! ### Pasting of two genuine two-pullbacks -/

section Pasting

variable {E B B' B'' : FppfStack.{u}} {p : StackHom E B} {g : StackHom B' B}
  {f : StackHom B'' B'}

/-- The comparison 2-cell of the outer rectangle obtained by pasting two two-pullback
squares. -/
noncomputable def pastedComparison (P : Genuine p g) (Q : Genuine P.snd f) :
    StackIso2 (vcomp (vcomp Q.fst P.fst) p) (vcomp Q.snd (vcomp f g)) :=
  (StackIso2.associator Q.fst P.fst p).trans
    ((StackIso2.whiskerLeft Q.fst P.comparison).trans
      ((StackIso2.associator Q.fst P.snd g).symm.trans
        ((StackIso2.whiskerRight Q.comparison g).trans
          (StackIso2.associator Q.snd f g))))

/-- The fibre components of the pasted comparison 2-cell. -/
@[simp]
theorem pastedComparison_appIso_hom_app (P : Genuine p g) (Q : Genuine P.snd f)
    (U : Scheme.{u}) (n : StackFiber Q.pullback U) :
    ((pastedComparison P Q).appIso U).hom.app n =
      (P.comparison.appIso U).hom.app ((StackHom.appFunctor Q.fst U).obj n) ≫
        (StackHom.appFunctor g U).map ((Q.comparison.appIso U).hom.app n) := by
  simp only [pastedComparison, trans_appIso_hom_app,
    StackIso2.associator_appIso_hom_app, StackIso2.symm_appIso_hom_app,
    StackIso2.associator_appIso_inv_app, StackIso2.whiskerLeft_appIso_hom_app,
    StackIso2.whiskerRight_appIso_hom_app]
  exact (Category.id_comp _).trans
    (congrArg _ ((Category.id_comp _).trans (Category.comp_id _)))

variable (P : Genuine p g) (Q : Genuine P.snd f)

/-- The outer cone presented by the iterated two-pullback. -/
noncomputable abbrev pastedCone : Cone (f := p) (g := vcomp f g) Q.pullback where
  fst := vcomp Q.fst P.fst
  snd := Q.snd
  comparison := pastedComparison P Q

variable {T : FppfStack.{u}}

/-- The cone over the first cospan induced by a cone over the pasted cospan. -/
noncomputable abbrev innerCone (c : Cone (f := p) (g := vcomp f g) T) :
    Cone (f := p) (g := g) T where
  fst := c.fst
  snd := vcomp c.snd f
  comparison := c.comparison.trans (StackIso2.associator c.snd f g).symm

/-- The cone over the second cospan induced by a cone over the pasted cospan. -/
noncomputable abbrev midCone (c : Cone (f := p) (g := vcomp f g) T) :
    Cone (f := P.snd) (g := f) T where
  fst := P.bilimit.lift (innerCone c)
  snd := c.snd
  comparison := P.bilimit.lift_snd (innerCone c)

/-- The lift of a cone over the pasted cospan through the iterated two-pullback. -/
noncomputable def pastedLift (c : Cone (f := p) (g := vcomp f g) T) :
    StackHom T Q.pullback :=
  Q.bilimit.lift (midCone P c)

variable (R : Genuine p (vcomp f g))

/-- The comparison morphism from the iterated two-pullback to a genuine two-pullback of the
composite cospan. -/
noncomputable def pasteHom : StackHom Q.pullback R.pullback :=
  R.bilimit.lift (pastedCone P Q)

/-- The comparison morphism back from a genuine two-pullback of the composite cospan. -/
noncomputable def pasteInv : StackHom R.pullback Q.pullback :=
  pastedLift P Q R.toStackTwoPullback.selfCone

/-- First projection comparison for the round trip on the composite two-pullback. -/
noncomputable def pasteRoundTripFst : StackIso2
    (vcomp (vcomp (pasteInv P Q R) (pasteHom P Q R)) R.fst) R.fst :=
  (StackIso2.associator (pasteInv P Q R) (pasteHom P Q R) R.fst).trans
    ((StackIso2.whiskerLeft (pasteInv P Q R)
        (R.bilimit.lift_fst (pastedCone P Q))).trans
      ((StackIso2.associator (pasteInv P Q R) Q.fst P.fst).symm.trans
        ((StackIso2.whiskerRight
            (Q.bilimit.lift_fst (midCone P R.toStackTwoPullback.selfCone)) P.fst).trans
          (P.bilimit.lift_fst (innerCone R.toStackTwoPullback.selfCone)))))

/-- Second projection comparison for the round trip on the composite two-pullback. -/
noncomputable def pasteRoundTripSnd : StackIso2
    (vcomp (vcomp (pasteInv P Q R) (pasteHom P Q R)) R.snd) R.snd :=
  (StackIso2.associator (pasteInv P Q R) (pasteHom P Q R) R.snd).trans
    ((StackIso2.whiskerLeft (pasteInv P Q R)
        (R.bilimit.lift_snd (pastedCone P Q))).trans
      (Q.bilimit.lift_snd (midCone P R.toStackTwoPullback.selfCone)))

-- The projection comparisons unfold to composites whose intermediate objects are only
-- definitionally equal, so the default transparency restriction has to be relaxed.
set_option backward.isDefEq.respectTransparency false in
/-- The round trip on the composite two-pullback classifies its own cone. -/
theorem pasteRoundTripClassifies :
    ConeLiftClassifies R.toStackTwoPullback R.toStackTwoPullback.selfCone
      (vcomp (pasteInv P Q R) (pasteHom P Q R))
      (pasteRoundTripFst P Q R) (pasteRoundTripSnd P Q R) := by
  intro U k
  apply Iso.ext
  have h2 := congrArg Iso.hom
    (P.bilimit.lift_compatible (innerCone R.toStackTwoPullback.selfCone) U k)
  have h3 := congrArg Iso.hom
    (Q.bilimit.lift_compatible (midCone P R.toStackTwoPullback.selfCone) U k)
  have h1 := congrArg Iso.hom
    (R.bilimit.lift_compatible (pastedCone P Q) U
      ((StackHom.appFunctor (pasteInv P Q R) U).obj k))
  have hnat := (P.comparison.appIso U).hom.naturality
    (((Q.bilimit.lift_fst (midCone P R.toStackTwoPullback.selfCone)).appIso U).hom.app k)
  dsimp only [pasteRoundTripFst, pasteRoundTripSnd, pasteHom, pasteInv, pastedLift,
    selfCone_fst, selfCone_snd, selfCone_comparison, vcomp_appFunctor_obj,
    vcomp_appFunctor_map] at h1 h2 h3 hnat ⊢
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, trans_appIso_hom_app,
    pastedComparison_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.symm_appIso_hom_app, StackIso2.associator_appIso_inv_app,
    StackIso2.whiskerLeft_appIso_hom_app, StackIso2.whiskerRight_appIso_hom_app,
    Functor.map_comp, Category.id_comp, Category.comp_id, vcomp_appFunctor_obj,
    vcomp_appFunctor_map, Category.assoc] at h1 h2 h3 hnat ⊢
  have h3' := congrArg (fun m ↦ (StackHom.appFunctor g U).map m) h3
  simp only [Functor.map_comp] at h3'
  rw [h2, reassoc_of% hnat, h3', reassoc_of% h1]


/-- The round trip on the composite two-pullback is 2-isomorphic to the identity. -/
noncomputable def pasteRoundTripIso : StackIso2
    (vcomp (pasteInv P Q R) (pasteHom P Q R))
    (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor) :=
  (R.bilimit.lift_unique R.toStackTwoPullback.selfCone
      (vcomp (pasteInv P Q R) (pasteHom P Q R))
      (pasteRoundTripFst P Q R) (pasteRoundTripSnd P Q R)
      (pasteRoundTripClassifies P Q R)).trans
    (R.bilimit.lift_unique R.toStackTwoPullback.selfCone
      (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor)
      (StackIso2.leftUnitor R.fst) (StackIso2.leftUnitor R.snd)
      (identitySelfConeClassifies R.toStackTwoPullback)).symm

/-- The lift of the inner cone determined by a genuine two-pullback of the composite
cospan. -/
noncomputable def pasteMid : StackHom R.pullback P.pullback :=
  P.bilimit.lift (innerCone R.toStackTwoPullback.selfCone)

/-- First projected comparison between `pasteHom ≫ pasteMid` and the first projection of the
iterated two-pullback. -/
noncomputable def pasteInnerFst : StackIso2
    (vcomp (vcomp (pasteHom P Q R) (pasteMid P R)) P.fst) (vcomp Q.fst P.fst) :=
  (StackIso2.associator (pasteHom P Q R) (pasteMid P R) P.fst).trans
    ((StackIso2.whiskerLeft (pasteHom P Q R)
        (P.bilimit.lift_fst (innerCone R.toStackTwoPullback.selfCone))).trans
      (R.bilimit.lift_fst (pastedCone P Q)))

/-- Second projected comparison between `pasteHom ≫ pasteMid` and the first projection of the
iterated two-pullback. -/
noncomputable def pasteInnerSnd : StackIso2
    (vcomp (vcomp (pasteHom P Q R) (pasteMid P R)) P.snd) (vcomp Q.fst P.snd) :=
  (StackIso2.associator (pasteHom P Q R) (pasteMid P R) P.snd).trans
    ((StackIso2.whiskerLeft (pasteHom P Q R)
        (P.bilimit.lift_snd (innerCone R.toStackTwoPullback.selfCone))).trans
      ((StackIso2.associator (pasteHom P Q R) R.snd f).symm.trans
        ((StackIso2.whiskerRight (R.bilimit.lift_snd (pastedCone P Q)) f).trans
          Q.comparison.symm)))

-- The projection comparisons unfold to composites whose intermediate objects are only
-- definitionally equal, so the default transparency restriction has to be relaxed.
set_option backward.isDefEq.respectTransparency false in
/-- The two projected comparisons of `pasteHom ≫ pasteMid` are compatible with the comparison
2-cell of the first square. -/
theorem pasteInnerCompat : ProjectedCompat P.toStackTwoPullback
    (pasteInnerFst P Q R) (pasteInnerSnd P Q R) := by
  intro U n
  have h2 := congrArg Iso.hom
    (P.bilimit.lift_compatible (innerCone R.toStackTwoPullback.selfCone) U
      ((StackHom.appFunctor (pasteHom P Q R) U).obj n))
  have h1 := congrArg Iso.hom
    (R.bilimit.lift_compatible (pastedCone P Q) U n)
  dsimp only [pasteInnerFst, pasteInnerSnd, pasteHom, pasteMid,
    selfCone_fst, selfCone_snd, selfCone_comparison, vcomp_appFunctor_obj,
    vcomp_appFunctor_map] at h1 h2 ⊢
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, trans_appIso_hom_app,
    pastedComparison_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.symm_appIso_hom_app, StackIso2.associator_appIso_inv_app,
    StackIso2.whiskerLeft_appIso_hom_app, StackIso2.whiskerRight_appIso_hom_app,
    Functor.map_comp, Category.id_comp, Category.comp_id, vcomp_appFunctor_obj,
    vcomp_appFunctor_map, Category.assoc] at h1 h2 ⊢
  rw [← reassoc_of% h2, ← reassoc_of% h1, ← Functor.map_comp, Iso.hom_inv_id_app]
  exact (comp3_mapId (StackHom.appFunctor g U) _ _ _).symm

/-- The comparison `pasteHom ≫ pasteMid ≅ Q.fst`, with prescribed projections. -/
noncomputable def pasteInnerIso :
    StackIso2 (vcomp (pasteHom P Q R) (pasteMid P R)) Q.fst :=
  projectionIso2 P (pasteInnerFst P Q R) (pasteInnerSnd P Q R) (pasteInnerCompat P Q R)

/-- First projection comparison for the round trip on the iterated two-pullback. -/
noncomputable def pasteBackFst : StackIso2
    (vcomp (vcomp (pasteHom P Q R) (pasteInv P Q R)) Q.fst) Q.fst :=
  (StackIso2.associator (pasteHom P Q R) (pasteInv P Q R) Q.fst).trans
    ((StackIso2.whiskerLeft (pasteHom P Q R)
        (Q.bilimit.lift_fst (midCone P R.toStackTwoPullback.selfCone))).trans
      (pasteInnerIso P Q R))

/-- Second projection comparison for the round trip on the iterated two-pullback. -/
noncomputable def pasteBackSnd : StackIso2
    (vcomp (vcomp (pasteHom P Q R) (pasteInv P Q R)) Q.snd) Q.snd :=
  (StackIso2.associator (pasteHom P Q R) (pasteInv P Q R) Q.snd).trans
    ((StackIso2.whiskerLeft (pasteHom P Q R)
        (Q.bilimit.lift_snd (midCone P R.toStackTwoPullback.selfCone))).trans
      (R.bilimit.lift_snd (pastedCone P Q)))

-- The projection comparisons unfold to composites whose intermediate objects are only
-- definitionally equal, so the default transparency restriction has to be relaxed.
set_option backward.isDefEq.respectTransparency false in
/-- The round trip on the iterated two-pullback classifies its own cone. -/
theorem pasteBackClassifies :
    ConeLiftClassifies Q.toStackTwoPullback Q.toStackTwoPullback.selfCone
      (vcomp (pasteHom P Q R) (pasteInv P Q R))
      (pasteBackFst P Q R) (pasteBackSnd P Q R) := by
  intro U n
  apply Iso.ext
  have h3 := congrArg Iso.hom
    (Q.bilimit.lift_compatible (midCone P R.toStackTwoPullback.selfCone) U
      ((StackHom.appFunctor (pasteHom P Q R) U).obj n))
  have hG := projectionIso2_snd_app P (pasteInnerFst P Q R) (pasteInnerSnd P Q R)
    (pasteInnerCompat P Q R) U n
  dsimp only [pasteBackFst, pasteBackSnd, pasteInnerIso, pasteInnerSnd, pasteHom,
    pasteInv, pastedLift, pasteMid, selfCone_fst, selfCone_snd, selfCone_comparison,
    vcomp_appFunctor_obj, vcomp_appFunctor_map] at h3 hG ⊢
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, trans_appIso_hom_app,
    StackIso2.associator_appIso_hom_app, StackIso2.symm_appIso_hom_app,
    StackIso2.associator_appIso_inv_app, StackIso2.whiskerLeft_appIso_hom_app,
    StackIso2.whiskerRight_appIso_hom_app, Functor.map_comp, Category.id_comp,
    vcomp_appFunctor_obj, Category.assoc] at h3 hG ⊢
  rw [hG, Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  refine comp3_id _ _ _ _ ?_
  rw [reassoc_of% h3]

/-- The round trip on the iterated two-pullback is 2-isomorphic to the identity. -/
noncomputable def pasteBackIso : StackIso2
    (vcomp (pasteHom P Q R) (pasteInv P Q R))
    (Pseudofunctor.StrongTrans.id Q.pullback.toPseudofunctor) :=
  (Q.bilimit.lift_unique Q.toStackTwoPullback.selfCone
      (vcomp (pasteHom P Q R) (pasteInv P Q R))
      (pasteBackFst P Q R) (pasteBackSnd P Q R) (pasteBackClassifies P Q R)).trans
    (Q.bilimit.lift_unique Q.toStackTwoPullback.selfCone
      (Pseudofunctor.StrongTrans.id Q.pullback.toPseudofunctor)
      (StackIso2.leftUnitor Q.fst) (StackIso2.leftUnitor Q.snd)
      (identitySelfConeClassifies Q.toStackTwoPullback)).symm

/-- **Pasting law for genuine two-pullbacks of fppf stacks.**  If `P` is a genuine
two-pullback of `p` along `g` and `Q` is a genuine two-pullback of its second projection
along `f`, then the outer rectangle presents a genuine two-pullback of `p` along `f ≫ g`:
its total stack is equivalent to that of any genuine two-pullback `R` of the composite
cospan. -/
noncomputable def pastingEquivalence : StackEquivalenceData Q.pullback R.pullback where
  hom := pasteHom P Q R
  inv := pasteInv P Q R
  homInv := pasteBackIso P Q R
  invHom := pasteRoundTripIso P Q R

/-- The pasting equivalence carries the first projection of `R` to the composite of the two
first projections. -/
noncomputable def pastingEquivalenceFst : StackIso2
    (vcomp (pastingEquivalence P Q R).hom R.fst) (vcomp Q.fst P.fst) :=
  R.bilimit.lift_fst (pastedCone P Q)

/-- The pasting equivalence carries the second projection of `R` to the second projection of
the iterated two-pullback. -/
noncomputable def pastingEquivalenceSnd : StackIso2
    (vcomp (pastingEquivalence P Q R).hom R.snd) Q.snd :=
  R.bilimit.lift_snd (pastedCone P Q)

end Pasting

end StackTwoPullback

namespace ConeStack

/-! ### Composition of base changes of cone stacks -/

section BaseChangeComp

variable {base base' base'' : FppfStack.{u}} {O : FppfScalarRings.{u}}
  (C : ConeStack base O) (g : StackHom base' base) (f : StackHom base'' base')

/-- The genuine two-pullback presenting the base change of `C` along `g`. -/
noncomputable abbrev baseChangeSquare : StackTwoPullback.Genuine C.projection g :=
  StackTwoPullback.canonicalGenuine C.projection g

/-- The genuine two-pullback presenting the base change of `baseChange C g` along `f`. -/
noncomputable abbrev baseChangeSquareSecond :
    StackTwoPullback.Genuine (baseChangeSquare C g).snd f :=
  StackTwoPullback.canonicalGenuine (baseChangeSquare C g).snd f

/-- The genuine two-pullback presenting the base change of `C` along the composite. -/
noncomputable abbrev baseChangeSquareTotal :
    StackTwoPullback.Genuine C.projection (vcomp f g) :=
  StackTwoPullback.canonicalGenuine C.projection (vcomp f g)

variable (hc : BaseChangeCoherence C g)

/-- **Composition half of the pseudofunctoriality of base change of cone stacks.**  Base
changing first along `g` and then along `f` gives a cone stack whose total stack is equivalent
to the total stack of the base change along the composite `f ≫ g`.  The equivalence is
constructed from the bicategorical universal properties of the three genuine two-pullbacks
involved, through the pasting law `StackTwoPullback.pastingEquivalence`. -/
noncomputable def baseChangeCompEquivalence
    (hc' : BaseChangeCoherence (baseChange C g hc) f)
    (hc'' : BaseChangeCoherence C (vcomp f g)) :
    StackEquivalenceData (baseChange (baseChange C g hc) f hc').total
      (baseChange C (vcomp f g) hc'').total :=
  StackTwoPullback.pastingEquivalence (baseChangeSquare C g)
    (baseChangeSquareSecond C g f) (baseChangeSquareTotal C g f)

/-- The composition comparison commutes with the projections to the new base. -/
noncomputable def baseChangeCompEquivalenceProjection
    (hc' : BaseChangeCoherence (baseChange C g hc) f)
    (hc'' : BaseChangeCoherence C (vcomp f g)) :
    StackIso2
      (vcomp (baseChangeCompEquivalence C g f hc hc' hc'').hom
        (baseChange C (vcomp f g) hc'').projection)
      (baseChange (baseChange C g hc) f hc').projection :=
  StackTwoPullback.pastingEquivalenceSnd (baseChangeSquare C g)
    (baseChangeSquareSecond C g f) (baseChangeSquareTotal C g f)

/-- The composition comparison commutes with the projections to the original cone stack. -/
noncomputable def baseChangeCompEquivalenceFst
    (hc' : BaseChangeCoherence (baseChange C g hc) f)
    (hc'' : BaseChangeCoherence C (vcomp f g)) :
    StackIso2
      (vcomp (baseChangeCompEquivalence C g f hc hc' hc'').hom
        (baseChangeFst C (vcomp f g)))
      (vcomp (baseChangeFst (baseChange C g hc) f) (baseChangeFst C g)) :=
  StackTwoPullback.pastingEquivalenceFst (baseChangeSquare C g)
    (baseChangeSquareSecond C g f) (baseChangeSquareTotal C g f)

/-- The composition comparison for base changes of a *coherent* cone stack, where no coherence
hypothesis has to be supplied. -/
noncomputable def baseChangeOfCoherentCompEquivalence {C : ConeStack base O}
    (hC : IsCoherent C) (g : StackHom base' base) (f : StackHom base'' base') :
    StackEquivalenceData
      (baseChangeOfCoherent (isCoherent_baseChangeOfCoherent hC g) f).total
      (baseChangeOfCoherent hC (vcomp f g)).total :=
  StackTwoPullback.pastingEquivalence (baseChangeSquare C g)
    (baseChangeSquareSecond C g f) (baseChangeSquareTotal C g f)

/-! #### Compatibility of the composition comparison with the vertices -/

/-- The vertex of a base change, without unfolding the whole cone-stack structure. -/
theorem baseChange_vertex (hc : BaseChangeCoherence C g) :
    (baseChange C g hc).vertex = baseChangeVertex C g := rfl

/-- The projection of a base change, without unfolding the whole cone-stack structure. -/
theorem baseChange_projection (hc : BaseChangeCoherence C g) :
    (baseChange C g hc).projection = baseChangeProjection C g := rfl

/-- The section comparison of a base change, without unfolding the whole cone-stack
structure. -/
theorem baseChange_vertexProjectionIso (hc : BaseChangeCoherence C g) :
    (baseChange C g hc).vertexProjectionIso = baseChangeVertexProjectionIso C g := rfl

variable (hc' : BaseChangeCoherence (baseChange C g hc) f)
  (hc'' : BaseChangeCoherence C (vcomp f g))

/-- First projection comparison for the vertex of the iterated base change. -/
noncomputable def baseChangeCompVertexFst : StackIso2
    (vcomp (vcomp (baseChange (baseChange C g hc) f hc').vertex
        (baseChangeCompEquivalence C g f hc hc' hc'').hom)
      (baseChangeSquareTotal C g f).fst)
    (baseChangeVertexCone C (vcomp f g)).fst :=
  (StackIso2.associator (baseChange (baseChange C g hc) f hc').vertex
      (baseChangeCompEquivalence C g f hc hc' hc'').hom
      (baseChangeSquareTotal C g f).fst).trans
    ((StackIso2.whiskerLeft (baseChange (baseChange C g hc) f hc').vertex
        (StackTwoPullback.pastingEquivalenceFst (baseChangeSquare C g)
          (baseChangeSquareSecond C g f) (baseChangeSquareTotal C g f))).trans
      ((StackIso2.associator (baseChange (baseChange C g hc) f hc').vertex
          (baseChangeSquareSecond C g f).fst (baseChangeSquare C g).fst).symm.trans
        ((StackIso2.whiskerRight
            (StackTwoPullback.canonicalLiftFstIso (baseChangeSquare C g).snd f
              (baseChangeVertexCone (baseChange C g hc) f))
            (baseChangeSquare C g).fst).trans
          ((StackIso2.associator f (baseChange C g hc).vertex
              (baseChangeSquare C g).fst).trans
            ((StackIso2.whiskerLeft f
                (StackTwoPullback.canonicalLiftFstIso C.projection g
                  (baseChangeVertexCone C g))).trans
              (StackIso2.associator f g C.vertex).symm)))))

/-- Second projection comparison for the vertex of the iterated base change. -/
noncomputable def baseChangeCompVertexSnd : StackIso2
    (vcomp (vcomp (baseChange (baseChange C g hc) f hc').vertex
        (baseChangeCompEquivalence C g f hc hc' hc'').hom)
      (baseChangeSquareTotal C g f).snd)
    (baseChangeVertexCone C (vcomp f g)).snd :=
  (StackIso2.associator (baseChange (baseChange C g hc) f hc').vertex
      (baseChangeCompEquivalence C g f hc hc' hc'').hom
      (baseChangeSquareTotal C g f).snd).trans
    ((StackIso2.whiskerLeft (baseChange (baseChange C g hc) f hc').vertex
        (StackTwoPullback.pastingEquivalenceSnd (baseChangeSquare C g)
          (baseChangeSquareSecond C g f) (baseChangeSquareTotal C g f))).trans
      (StackTwoPullback.canonicalLiftSndIso (baseChangeSquare C g).snd f
        (baseChangeVertexCone (baseChange C g hc) f)))

-- The comparisons unfold to composites whose intermediate objects are only definitionally
-- equal, so the default transparency restriction has to be relaxed.
set_option backward.isDefEq.respectTransparency false in
/-- The transported vertex of the iterated base change classifies the vertex cone of the base
change along the composite. -/
theorem baseChangeCompVertexClassifies :
    StackTwoPullback.ConeLiftClassifies (baseChangeSquareTotal C g f).toStackTwoPullback
      (baseChangeVertexCone C (vcomp f g))
      (vcomp (baseChange (baseChange C g hc) f hc').vertex
        (baseChangeCompEquivalence C g f hc hc' hc'').hom)
      (baseChangeCompVertexFst C g f hc hc' hc'')
      (baseChangeCompVertexSnd C g f hc hc' hc'') := by
  intro U z
  apply CategoryTheory.Iso.ext
  have hb0 := StackTwoPullback.canonicalLift_compatible (f := (baseChangeSquare C g).snd)
    (g := f) (baseChangeVertexCone (baseChange C g hc) f) U z
  have hb := congrArg CategoryTheory.Iso.hom hb0
  have hcc0 := StackTwoPullback.canonicalLift_compatible (f := C.projection) (g := g)
    (baseChangeVertexCone C g) U ((StackHom.appFunctor f U).obj z)
  have hcc := congrArg CategoryTheory.Iso.hom hcc0
  have hd0 := (baseChangeSquareTotal C g f).bilimit.lift_compatible
    (StackTwoPullback.pastedCone (baseChangeSquare C g) (baseChangeSquareSecond C g f)) U
    ((StackHom.appFunctor (baseChange (baseChange C g hc) f hc').vertex U).obj z)
  have hd := congrArg CategoryTheory.Iso.hom hd0
  clear hb0 hcc0 hd0
  have hnat := ((baseChangeSquare C g).comparison.appIso U).hom.naturality
    (((StackTwoPullback.canonicalLiftFstIso (baseChangeSquare C g).snd f
      (baseChangeVertexCone (baseChange C g hc) f)).appIso U).hom.app z)
  dsimp only [baseChange_vertex, baseChange_projection, baseChange_vertexProjectionIso,
    baseChangeVertexProjectionIso, baseChangeVertex,
    baseChangeVertexCone, baseChangeProjection, baseChangeFst,
    baseChangeCompEquivalence,
    StackTwoPullback.pastingEquivalence, StackTwoPullback.pasteHom,
    StackTwoPullback.pastingEquivalenceFst, StackTwoPullback.pastingEquivalenceSnd,
    baseChangeCompVertexFst, baseChangeCompVertexSnd,
    StackTwoPullback.canonicalGenuine_fst, StackTwoPullback.canonicalGenuine_snd,
    StackTwoPullback.canonicalGenuine_comparison, StackTwoPullback.canonicalGenuine_lift,
    StackTwoPullback.canonicalGenuine_lift_fst, StackTwoPullback.canonicalGenuine_lift_snd,
    StackTwoPullback.vcomp_appFunctor_obj,
    StackTwoPullback.vcomp_appFunctor_map] at hb hcc hd hnat ⊢
  simp only [CategoryTheory.Iso.trans_hom, Functor.mapIso_hom,
    CategoryTheory.Iso.app_hom,
    StackTwoPullback.trans_appIso_hom_app,
    StackTwoPullback.pastedComparison_appIso_hom_app,
    StackTwoPullback.canonicalGenuine_fst, StackTwoPullback.canonicalGenuine_snd,
    StackTwoPullback.canonicalGenuine_comparison,
    StackIso2.associator_appIso_hom_app, StackIso2.symm_appIso_hom_app,
    StackIso2.associator_appIso_inv_app, StackIso2.whiskerLeft_appIso_hom_app,
    StackIso2.whiskerRight_appIso_hom_app, StackTwoPullback.rightUnitor_appIso_hom_app,
    StackTwoPullback.leftUnitor_appIso_inv_app, Functor.map_comp, Category.id_comp,
    Category.comp_id, StackTwoPullback.vcomp_appFunctor_obj,
    StackTwoPullback.vcomp_appFunctor_map, Category.assoc] at hb hcc hd hnat ⊢
  have hb' := congrArg (fun m ↦ (StackHom.appFunctor g U).map m) hb
  simp only [Functor.map_comp] at hb'
  rw [hcc, reassoc_of% hnat, hb', reassoc_of% hd]

/-- **Compatibility of the composition comparison with the vertices.**  The vertex of the
iterated base change, transported along the comparison equivalence, is 2-isomorphic to the
vertex of the base change along the composite. -/
noncomputable def baseChangeCompEquivalenceVertex : StackIso2
    (vcomp (baseChange (baseChange C g hc) f hc').vertex
      (baseChangeCompEquivalence C g f hc hc' hc'').hom)
    (baseChange C (vcomp f g) hc'').vertex :=
  (baseChangeSquareTotal C g f).bilimit.lift_unique (baseChangeVertexCone C (vcomp f g))
    (vcomp (baseChange (baseChange C g hc) f hc').vertex
      (baseChangeCompEquivalence C g f hc hc' hc'').hom)
    (baseChangeCompVertexFst C g f hc hc' hc'')
    (baseChangeCompVertexSnd C g f hc hc' hc'')
    (baseChangeCompVertexClassifies C g f hc hc' hc'')

end BaseChangeComp

end ConeStack

end GromovWitten.AlgebraicGeometry
