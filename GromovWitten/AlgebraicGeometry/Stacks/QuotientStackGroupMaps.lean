/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.QuotientStackClassifying
import GromovWitten.AlgebraicGeometry.Stacks.TorsorPushoutFunctoriality
import GromovWitten.AlgebraicGeometry.Stacks.TorsorStackBundle

/-!
# Quotient-stack maps from equivariant maps through a homomorphism of groups

Let `r : G ⟶ H` be a homomorphism of group algebraic spaces, `U` a `G`-space, `V` an `H`-space
and `f : U.space ⟶ V.space` a map intertwining the two actions through `r`
(`AlgebraicSpaceAction.HomOver`).  This file constructs, over every test scheme `T`, the induced
functor on the fibres of the quotient stacks

`ActionTorsor.pushoutFunctor r f : ActionTorsor G U T ⥤ ActionTorsor H V T`,
`P ↦ (r_* P, r_* P ⟶ V)`,

On objects it is the contraction `TorsorPushout.pushoutActionTorsor` of
`Stacks/TorsorPushout.lean`; on arrows it is the functoriality `TorsorPushout.pushoutMap` of
`Stacks/TorsorPushoutFunctoriality.lean`.  The compatibility of the induced arrow with the maps to
`V` (`ActionTorsor.pushoutMap_comp_target`) is proved from the uniqueness of the evaluation
pairing, i.e. from `TorsorPushout.comp_targetMap_pt` and
`TorsorPushout.PushoutTorsor.ev_pushMap_cover`.

These fibrewise functors are then assembled into the quotient-stack map of issue #36 itself,

`ActionTorsor.pushoutStrongTrans r f :
  Pseudofunctor.StrongTrans (pullbackPseudofunctor G U) (pullbackPseudofunctor H V)`,

a strong transformation of the base-change pseudofunctors, whose naturality 2-isomorphisms are the
base-change comparisons `ActionTorsor.pushoutPullbackNatIso`.  The two nontrivial coherence laws
reduce to the unit and composition compatibilities of the base-change comparison of the pushout,
`TorsorPushout.PushoutTorsor.pushoutPullbackFst_id` and
`TorsorPushout.PushoutTorsor.pushoutPullbackFst_comp`, which are proved from the uniqueness
`TorsorPushout.PushoutTorsor.eq_pushMap` of a map out of a pushout datum.  Specialising to the
one-point `H`-space gives the structure map `[U/G] ⟶ BH` of a homomorphism of groups
(`ActionTorsor.toClassifyingStrongTrans`).

## Main declarations

* `AlgebraicSpaceAction.HomOver r U V`: the equivariant-map data, generalising
  `AlgebraicSpaceAction.Hom` (which is the case `r = 𝟙 G`, `Hom.toHomOver`).
* `AlgebraicSpaceAction.HomOver.isEquivariantOver`: the pointwise form of the equivariance, the
  hypothesis required by `TorsorPushout.targetMap`.
* `AlgebraicSpaceAction.HomOver.toPointOver`: the unique map to the one-point `H`-space.
* `ActionTorsor.Hom.toFppfHom`: the underlying arrow of torsors of an arrow of action torsors.
* `ActionTorsor.pushoutObj`, `ActionTorsor.pushoutFunctor`: the induced object `r_* P` and the
  induced functor `ActionTorsor G U T ⥤ ActionTorsor H V T`, i.e. the fibrewise part of the
  quotient-stack map `[U/G] ⟶ [V/H]`.
* `ActionTorsor.pushoutMap_comp_target`: the induced arrow of pushout torsors commutes with the
  maps to `V`.
* `ActionTorsor.pushoutPullbackObjIso`, `ActionTorsor.pushoutPullbackObjHom_naturality` and
  `ActionTorsor.pushoutPullbackNatIso`: the induced functor commutes with base change of action
  torsors, `r_* (b^* P) ≅ b^* (r_* P)`, naturally in `P` — the natural isomorphism
  `b^* ⋙ r_* ≅ r_* ⋙ b^*`, which is the naturality datum of the strong transformation
  `[U/G] ⟶ [V/H]`.  It comes from `TorsorPushout.PushoutTorsor.pushoutPullbackHom` together with
  `ActionTorsor.pushoutPullbackHom_comp_target` and
  `TorsorPushout.PushoutTorsor.pushMap_comp_pushoutPullbackFst`.
* `ActionTorsor.toClassifyingFunctor`: the special case `V = pointAction H`, the fibrewise
  structure map `[U/G] ⟶ BH` of a homomorphism `r : G ⟶ H`.
* `TorsorPushout.PushoutTorsor.pushoutPullbackFst_id` and
  `TorsorPushout.PushoutTorsor.pushoutPullbackFst_comp`: the unit and composition compatibilities
  of the base-change comparison of the pushout torsor, the mathematical content of the coherence
  laws below.
* `ActionTorsor.pushoutPullbackNatIso_naturality`, `ActionTorsor.pushoutPullbackNatIso_id`,
  `ActionTorsor.pushoutPullbackNatIso_comp`: the three coherence laws of a strong transformation,
  stated for natural transformations of the fibre functors.
* `ActionTorsor.pushoutStrongTrans`: **the quotient-stack map `[U/G] ⟶ [V/H]`**, as a strong
  transformation `pullbackPseudofunctor G U ⟶ pullbackPseudofunctor H V`; and
  `ActionTorsor.quotientStackMap` for the bundled quotient stacks.
* `ActionTorsor.toClassifyingStrongTrans`, `ActionTorsor.toClassifyingStackMap`: the special case
  `V = pointAction H`, the structure map `[U/G] ⟶ BH` of a homomorphism `r : G ⟶ H`.

## Implementation notes

The coherence laws are proved in the shape used by `Stacks/QuotientStackPullback.lean` for
`pullbackPseudofunctor` itself: they are stated for natural transformations (with
`Functor.whiskerLeft`/`Functor.whiskerRight`/`Functor.associator`) and transported to the
bicategory `Cat` by `Cat.Hom₂.ext` followed by `simpa … using!`.  The `!` is essential: the
`Cat`-specific whiskering lemmas are stated with the 2-cell quiver `Cat.Hom.instQuiver`, while the
2-cells of the goals come from `Bicategory.homCategory`, so `simp`/`rw` never match them although
the two sides are definitionally equal.

Not carried out here: the comparison of the case `r = 𝟙 G` with `ActionTorsor.mapTargetFunctor`
(it needs `TorsorPushout.PushoutTorsor.pushoutIdIso` together with a target compatibility).
-/

open CategoryTheory CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace GromovWitten.AlgebraicGeometry

universe u

/-- **Two morphisms into an iterated fibre product agree** as soon as they agree after the two
projections `fst ≫ fst` and `snd`; the remaining leg `fst ≫ snd` is then forced by the pullback
condition of the outer square. -/
theorem hom_ext_pullback₂ {C : Type*} [CategoryTheory.Category C] {A B D E S : C} (p : A ⟶ B)
    (g₁ : D ⟶ B) (g₂ : E ⟶ D) [Limits.HasPullback p g₁]
    [Limits.HasPullback (Limits.pullback.snd p g₁) g₂]
    {u v : S ⟶ Limits.pullback (Limits.pullback.snd p g₁) g₂}
    (hfst : u ≫ Limits.pullback.fst (Limits.pullback.snd p g₁) g₂ ≫
        Limits.pullback.fst p g₁ =
      v ≫ Limits.pullback.fst (Limits.pullback.snd p g₁) g₂ ≫ Limits.pullback.fst p g₁)
    (hsnd : u ≫ Limits.pullback.snd (Limits.pullback.snd p g₁) g₂ =
      v ≫ Limits.pullback.snd (Limits.pullback.snd p g₁) g₂) :
    u = v := by
  have key : ∀ w : S ⟶ Limits.pullback (Limits.pullback.snd p g₁) g₂,
      (w ≫ Limits.pullback.fst (Limits.pullback.snd p g₁) g₂) ≫ Limits.pullback.snd p g₁ =
        (w ≫ Limits.pullback.snd (Limits.pullback.snd p g₁) g₂) ≫ g₂ := fun w => by
    rw [Category.assoc, Limits.pullback.condition, Category.assoc]
  refine Limits.pullback.hom_ext (Limits.pullback.hom_ext ?_ ?_) hsnd
  · exact (Category.assoc _ _ _).trans (hfst.trans (Category.assoc _ _ _).symm)
  · rw [key u, key v, hsnd]

/-- Substituting `q ≫ v = z ≫ t` inside a length-five composite, together with the
reassociation needed to compare a left-bracketed with a right-bracketed composite. -/
theorem reassoc_of_comp_eq {C : Type*} [CategoryTheory.Category C] {A₁ A₂ A₃ A₄ A₅ A₆ A₇ : C}
    (m : A₁ ⟶ A₂) (n : A₂ ⟶ A₃) (q : A₃ ⟶ A₄) (v : A₄ ⟶ A₅) (w : A₅ ⟶ A₆)
    (z : A₃ ⟶ A₇) (t : A₇ ⟶ A₅) (hq : q ≫ v = z ≫ t) :
    (m ≫ n ≫ q) ≫ v ≫ w = m ≫ (n ≫ z) ≫ t ≫ w := by
  simp only [Category.assoc]
  rw [← Category.assoc q v w, hq, Category.assoc]

namespace AlgebraicSpaceAction

variable {G H : AlgebraicSpaceGroup.{u}}

/-- **Equivariant map data through a homomorphism of groups.**  A map `U.space ⟶ V.space` of the
underlying algebraic spaces which intertwines the `G`-action on `U` and the `H`-action on `V`
through a homomorphism `r : G.space.toSheaf ⟶ H.space.toSheaf`.  Specialising to `H = G` and
`r = 𝟙 G.space.toSheaf` recovers `AlgebraicSpaceAction.Hom` (`HomOver.toHom`). -/
structure HomOver (r : G.space.toSheaf ⟶ H.space.toSheaf) (U : AlgebraicSpaceAction G)
    (V : AlgebraicSpaceAction H) where
  /-- The underlying map of algebraic spaces. -/
  hom : U.space ⟶ V.space
  /-- Equivariance through `r`: acting by `g` then mapping agrees with mapping then acting by
  `r g`. -/
  equivariant :
    ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) ≫ hom.hom =
      lift (fst G.space.toSheaf U.space.toSheaf ≫ r) (snd G.space.toSheaf U.space.toSheaf ≫
        hom.hom) ≫ ModObj.smul (M := H.space.toSheaf) (X := V.space.toSheaf)

@[ext]
theorem HomOver.ext {r : G.space.toSheaf ⟶ H.space.toSheaf} {U : AlgebraicSpaceAction G}
    {V : AlgebraicSpaceAction H} (f g : HomOver r U V) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  simp only [HomOver.mk.injEq]
  exact h

/-- A `G`-equivariant map (`AlgebraicSpaceAction.Hom`) is equivariant through the identity
homomorphism. -/
def Hom.toHomOver {U V : AlgebraicSpaceAction G} (f : U ⟶ V) :
    HomOver (𝟙 G.space.toSheaf) U V where
  hom := f.hom
  equivariant := by
    have h := f.equivariant
    have e : (G.space.toSheaf ◁ f.hom.hom) =
        lift (fst G.space.toSheaf U.space.toSheaf ≫ 𝟙 G.space.toSheaf)
          (snd G.space.toSheaf U.space.toSheaf ≫ f.hom.hom) := by
      ext <;> simp
    rwa [e] at h

/-- **The pointwise form of the equivariance of a `HomOver`**: this is the hypothesis
`TorsorPushout.IsEquivariantOver` required to build the induced map on the pushout torsor. -/
theorem HomOver.isEquivariantOver {r : G.space.toSheaf ⟶ H.space.toSheaf}
    {U : AlgebraicSpaceAction G} {V : AlgebraicSpaceAction H} (f : HomOver r U V) :
    TorsorPushout.IsEquivariantOver r f.hom.hom := by
  intro Z g x
  have key : lift g x ≫ lift (fst G.space.toSheaf U.space.toSheaf ≫ r)
      (snd G.space.toSheaf U.space.toSheaf ≫ f.hom.hom) = lift (g ≫ r) (x ≫ f.hom.hom) := by
    rw [comp_lift, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd]
  rw [TorsorPushout.actPt, TorsorPushout.actPt, Category.assoc, f.equivariant,
    ← Category.assoc, key]

/-- The unique map to the one-point `H`-space is equivariant through any homomorphism `r`. -/
noncomputable def HomOver.toPointOver {G H : AlgebraicSpaceGroup.{u}}
    (r : G.space.toSheaf ⟶ H.space.toSheaf) (U : AlgebraicSpaceAction G) :
    HomOver r U (pointAction H) where
  hom := AlgebraicSpace.homMk (pointIsTerminal.from U.space.toSheaf)
  equivariant := pointIsTerminal.hom_ext _ _

end AlgebraicSpaceAction

namespace TorsorPushout

namespace PushoutTorsor

section BaseChangeFst

variable {G G' : AlgebraicSpaceGroup.{u}} {T T' T'' : Scheme.{u}}
  {r : G.space.toSheaf ⟶ G'.space.toSheaf} [IsMonHom r]

-- The action on a base-changed torsor is not a global instance; make it one here so that the
-- statements below about points of base-changed torsors elaborate.
attribute [local instance] FppfTorsor.pullbackAction

/-- **The base-change comparison of the pushouts lies over the base change**: composing
`pushoutPullbackFst` with the structure morphism of `r_* X` is the structure morphism of
`r_* (b^* X)` followed by `b`.  Checked on the trivialising cover with
`PushoutTorsor.pushoutPullbackFst_cond`. -/
theorem pushoutPullbackFst_proj (X : FppfTorsor G T) (b : T' ⟶ T) :
    pushoutPullbackFst X r b ≫ (pushoutTorsor X r).projection =
      (pushoutTorsor (X.pullbackTorsor b) r).projection ≫ fppfYoneda.map b := by
  have hcond : Limits.pullback.fst X.projection (fppfYoneda.map b) ≫ X.projection =
      (X.pullbackTorsor b).projection ≫ fppfYoneda.map b := Limits.pullback.condition
  refine hom_ext_of_cmp (A := pushoutTorsor (X.pullbackTorsor b) r) (fun β c hc => ?_)
  have h₂ : β ≫ (pushoutTorsor (X.pullbackTorsor b) r).projection =
      coverPt c ≫ (X.pullbackTorsor b).projection := hc.trans (coverPt_proj c).symm
  have key := pushoutPullbackFst_cond X r b β (coverPt c) h₂
  calc β ≫ pushoutPullbackFst X r b ≫ (pushoutTorsor X r).projection
      = (β ≫ pushoutPullbackFst X r b) ≫ (pushoutTorsor X r).projection :=
        (Category.assoc _ _ _).symm
    _ = (coverPt c ≫ Limits.pullback.fst X.projection (fppfYoneda.map b)) ≫ X.projection := key
    _ = coverPt c ≫ Limits.pullback.fst X.projection (fppfYoneda.map b) ≫ X.projection :=
        Category.assoc _ _ _
    _ = coverPt c ≫ (X.pullbackTorsor b).projection ≫ fppfYoneda.map b := by rw [hcond]
    _ = (coverPt c ≫ (X.pullbackTorsor b).projection) ≫ fppfYoneda.map b :=
        (Category.assoc _ _ _).symm
    _ = (β ≫ (pushoutTorsor (X.pullbackTorsor b) r).projection) ≫ fppfYoneda.map b := by
        rw [h₂]
    _ = β ≫ (pushoutTorsor (X.pullbackTorsor b) r).projection ≫ fppfYoneda.map b :=
        Category.assoc _ _ _

/-- **Unit compatibility of the base-change comparison of the pushout.**  For `b = 𝟙 T` the
comparison `r_* (b^* X) ⟶ r_* X` is the functoriality `pushMap` of the canonical isomorphism
`(𝟙 T)^* X ≅ X`.  Both sides are morphisms out of a pushout datum, so they agree by the
uniqueness `PushoutTorsor.eq_pushMap` once their evaluation pairings agree on the trivialising
cover, which is `PushoutTorsor.ev_pushoutPullbackFst`. -/
theorem pushoutPullbackFst_id (X : FppfTorsor G T) (φ : X.pullbackTorsor (𝟙 T) ⟶ X)
    (hφ : φ.iso.hom = Limits.pullback.fst X.projection (fppfYoneda.map (𝟙 T))) :
    pushoutPullbackFst X r (𝟙 T) =
      pushMap (pushoutTorsor (X.pullbackTorsor (𝟙 T)) r) (pushoutTorsor X r) φ := by
  have hid : fppfYoneda.map (𝟙 T) = 𝟙 (fppfYoneda.obj T) := fppfYoneda.map_id T
  refine eq_pushMap (pushoutTorsor (X.pullbackTorsor (𝟙 T)) r) (pushoutTorsor X r) φ
    (pushoutPullbackFst X r (𝟙 T)) ?_ ?_
  · refine (pushoutPullbackFst_proj X (𝟙 T)).trans ?_
    rw [hid, Category.comp_id]
  · intro W β c hc h₁ h₂
    have h₁' : (β ≫ pushoutPullbackFst X r (𝟙 T)) ≫ (pushoutTorsor X r).projection =
        (coverPt c ≫ Limits.pullback.fst X.projection (fppfYoneda.map (𝟙 T))) ≫ X.projection :=
      pushoutPullbackFst_cond X r (𝟙 T) β (coverPt c) h₂
    refine ((pushoutTorsor X r).ev_congr rfl
      (congrArg (fun x => coverPt c ≫ x) hφ) h₁ h₁').trans ?_
    exact ev_pushoutPullbackFst X r (𝟙 T) β (coverPt c) h₂ h₁'

/-- **Composition compatibility of the base-change comparison of the pushout.**  The comparison
for a composite `b₂ ≫ b₁` factors as the functoriality `pushMap` of `FppfTorsor.pullbackCompIso`
followed by the two comparisons for `b₂` and `b₁`.  All the maps involved are computed at the
tautological points of the trivialising cover of `(b₂ ≫ b₁)^* X` by
`PushoutTorsor.ev_pushoutPullbackFst` and `PushoutTorsor.ev_pushMap_cover`, where they agree
because `FppfTorsor.pullbackCompIso` matches the first projections. -/
theorem pushoutPullbackFst_comp (X : FppfTorsor G T) (b₁ : T' ⟶ T) (b₂ : T'' ⟶ T')
    (ψ : X.pullbackTorsor (b₂ ≫ b₁) ⟶ (X.pullbackTorsor b₁).pullbackTorsor b₂)
    (hψ : ψ.iso.hom = (FppfTorsor.pullbackCompIso X b₂ b₁).hom) :
    pushoutPullbackFst X r (b₂ ≫ b₁) =
      pushMap (pushoutTorsor (X.pullbackTorsor (b₂ ≫ b₁)) r)
          (pushoutTorsor ((X.pullbackTorsor b₁).pullbackTorsor b₂) r) ψ ≫
        pushoutPullbackFst (X.pullbackTorsor b₁) r b₂ ≫ pushoutPullbackFst X r b₁ := by
  have hfstfst : (FppfTorsor.pullbackCompIso X b₂ b₁).hom ≫
      Limits.pullback.fst (X.pullbackTorsor b₁).projection (fppfYoneda.map b₂) ≫
        Limits.pullback.fst X.projection (fppfYoneda.map b₁) =
      Limits.pullback.fst X.projection (fppfYoneda.map (b₂ ≫ b₁)) :=
    FppfTorsor.pullbackCompIso_hom_fst_fst X b₂ b₁
  refine hom_ext_of_cmp (A := pushoutTorsor (X.pullbackTorsor (b₂ ≫ b₁)) r)
    (fun α c hc => ?_)
  have hcov : α ≫ (pushoutTorsor (X.pullbackTorsor (b₂ ≫ b₁)) r).projection =
      coverPt c ≫ (X.pullbackTorsor (b₂ ≫ b₁)).projection := hc.trans (coverPt_proj c).symm
  have hL0 : (α ≫ pushoutPullbackFst X r (b₂ ≫ b₁)) ≫ (pushoutTorsor X r).projection =
      (coverPt c ≫ Limits.pullback.fst X.projection (fppfYoneda.map (b₂ ≫ b₁))) ≫
        X.projection :=
    pushoutPullbackFst_cond X r (b₂ ≫ b₁) α (coverPt c) hcov
  have evL := ev_pushoutPullbackFst X r (b₂ ≫ b₁) α (coverPt c) hcov hL0
  have h1 : (α ≫ pushMap (pushoutTorsor (X.pullbackTorsor (b₂ ≫ b₁)) r)
        (pushoutTorsor ((X.pullbackTorsor b₁).pullbackTorsor b₂) r) ψ) ≫
        (pushoutTorsor ((X.pullbackTorsor b₁).pullbackTorsor b₂) r).projection =
      (coverPt c ≫ ψ.iso.hom) ≫ ((X.pullbackTorsor b₁).pullbackTorsor b₂).projection := by
    rw [Category.assoc, pushMap_proj, hcov, Category.assoc, ψ.over]
  have ev1 := ev_pushMap_cover (pushoutTorsor (X.pullbackTorsor (b₂ ≫ b₁)) r)
    (pushoutTorsor ((X.pullbackTorsor b₁).pullbackTorsor b₂) r) ψ α c hc h1 hcov
  have h2 : ((α ≫ pushMap (pushoutTorsor (X.pullbackTorsor (b₂ ≫ b₁)) r)
        (pushoutTorsor ((X.pullbackTorsor b₁).pullbackTorsor b₂) r) ψ) ≫
        pushoutPullbackFst (X.pullbackTorsor b₁) r b₂) ≫
        (pushoutTorsor (X.pullbackTorsor b₁) r).projection =
      ((coverPt c ≫ ψ.iso.hom) ≫
        Limits.pullback.fst (X.pullbackTorsor b₁).projection (fppfYoneda.map b₂)) ≫
        (X.pullbackTorsor b₁).projection :=
    pushoutPullbackFst_cond (X.pullbackTorsor b₁) r b₂ _ _ h1
  have ev2 := ev_pushoutPullbackFst (X.pullbackTorsor b₁) r b₂ _ _ h1 h2
  have h3 : (((α ≫ pushMap (pushoutTorsor (X.pullbackTorsor (b₂ ≫ b₁)) r)
        (pushoutTorsor ((X.pullbackTorsor b₁).pullbackTorsor b₂) r) ψ) ≫
        pushoutPullbackFst (X.pullbackTorsor b₁) r b₂) ≫
        pushoutPullbackFst X r b₁) ≫ (pushoutTorsor X r).projection =
      ((((coverPt c ≫ ψ.iso.hom) ≫
        Limits.pullback.fst (X.pullbackTorsor b₁).projection (fppfYoneda.map b₂)) ≫
        Limits.pullback.fst X.projection (fppfYoneda.map b₁))) ≫ X.projection :=
    pushoutPullbackFst_cond X r b₁ _ _ h2
  have ev3 := ev_pushoutPullbackFst X r b₁ _ _ h2 h3
  have hpt : (((coverPt c ≫ ψ.iso.hom) ≫
        Limits.pullback.fst (X.pullbackTorsor b₁).projection (fppfYoneda.map b₂)) ≫
        Limits.pullback.fst X.projection (fppfYoneda.map b₁)) =
      coverPt c ≫ Limits.pullback.fst X.projection (fppfYoneda.map (b₂ ≫ b₁)) := by
    rw [hψ]
    simp only [Category.assoc]
    rw [hfstfst]
  have hassoc : α ≫ (pushMap (pushoutTorsor (X.pullbackTorsor (b₂ ≫ b₁)) r)
        (pushoutTorsor ((X.pullbackTorsor b₁).pullbackTorsor b₂) r) ψ ≫
        pushoutPullbackFst (X.pullbackTorsor b₁) r b₂ ≫ pushoutPullbackFst X r b₁) =
      ((α ≫ pushMap (pushoutTorsor (X.pullbackTorsor (b₂ ≫ b₁)) r)
        (pushoutTorsor ((X.pullbackTorsor b₁).pullbackTorsor b₂) r) ψ) ≫
        pushoutPullbackFst (X.pullbackTorsor b₁) r b₂) ≫ pushoutPullbackFst X r b₁ :=
    (Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm
  have hRfin : (α ≫ (pushMap (pushoutTorsor (X.pullbackTorsor (b₂ ≫ b₁)) r)
        (pushoutTorsor ((X.pullbackTorsor b₁).pullbackTorsor b₂) r) ψ ≫
        pushoutPullbackFst (X.pullbackTorsor b₁) r b₂ ≫ pushoutPullbackFst X r b₁)) ≫
        (pushoutTorsor X r).projection =
      (coverPt c ≫ Limits.pullback.fst X.projection (fppfYoneda.map (b₂ ≫ b₁))) ≫
        X.projection := by
    rw [hassoc]
    exact h3.trans (congrArg (fun x => x ≫ X.projection) hpt)
  refine (pushoutTorsor X r).ev_injective
    (coverPt c ≫ Limits.pullback.fst X.projection (fppfYoneda.map (b₂ ≫ b₁))) hL0 hRfin ?_
  refine evL.trans ?_
  exact (((pushoutTorsor X r).ev_congr hassoc hpt.symm hRfin h3).trans
    (ev3.trans (ev2.trans ev1))).symm

end BaseChangeFst

end PushoutTorsor

end TorsorPushout

namespace ActionTorsor

open TorsorPushout

variable {G H : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G}
  {V : AlgebraicSpaceAction H} {T T' : Scheme.{u}}

/-- The underlying arrow of fppf torsors of an arrow of action torsors. -/
def Hom.toFppfHom {P Q : ActionTorsor G U T} (φ : P ⟶ Q) :
    P.toFppfTorsor ⟶ Q.toFppfTorsor where
  iso := φ.iso
  over := φ.over
  equivariant := φ.equivariant

/-- The underlying morphism of sheaves is unchanged. -/
@[simp]
theorem Hom.toFppfHom_iso_hom {P Q : ActionTorsor G U T} (φ : P ⟶ Q) :
    (Hom.toFppfHom φ).iso.hom = φ.iso.hom :=
  rfl

/-- Forgetting the map to `U` preserves identities. -/
@[simp]
theorem Hom.toFppfHom_id (P : ActionTorsor G U T) :
    Hom.toFppfHom (𝟙 P) = 𝟙 P.toFppfTorsor :=
  FppfTorsor.Hom.ext _ _ rfl

/-- Forgetting the map to `U` preserves composition. -/
@[simp]
theorem Hom.toFppfHom_comp {P Q R : ActionTorsor G U T} (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    Hom.toFppfHom (φ ≫ ψ) = Hom.toFppfHom φ ≫ Hom.toFppfHom ψ :=
  FppfTorsor.Hom.ext _ _ rfl

variable (r : G.space.toSheaf ⟶ H.space.toSheaf) [IsMonHom r]
  (f : AlgebraicSpaceAction.HomOver r U V)

/-- **The contraction of an action torsor along `r` and `f`**: the pushout torsor `r_* P` with the
induced equivariant map to `V`. -/
noncomputable def pushoutObj (P : ActionTorsor G U T) : ActionTorsor H V T :=
  pushoutActionTorsor P r f.hom.hom f.isEquivariantOver

/-- The underlying torsor of the contraction is the pushout torsor. -/
@[simp]
theorem pushoutObj_toFppfTorsor (P : ActionTorsor G U T) :
    (pushoutObj r f P).toFppfTorsor = pushoutFppfTorsor P.toFppfTorsor r :=
  rfl

/-- The map to `V` of the contraction is the induced map. -/
@[simp]
theorem pushoutObj_target (P : ActionTorsor G U T) :
    (pushoutObj r f P).target = targetMap P r f.hom.hom f.isEquivariantOver :=
  rfl

/-- **The induced arrow of pushout torsors commutes with the maps to `V`.**  Both sides are
computed at the tautological points of the trivialising cover of `P` by
`TorsorPushout.comp_targetMap_pt`, where they agree by
`TorsorPushout.PushoutTorsor.ev_pushMap_cover` and the compatibility of `φ` with the maps to
`U`. -/
theorem pushoutMap_comp_target {P Q : ActionTorsor G U T} (φ : P ⟶ Q) :
    (pushoutMap (Hom.toFppfHom φ) r).iso.hom ≫
        targetMap Q r f.hom.hom f.isEquivariantOver =
      targetMap P r f.hom.hom f.isEquivariantOver := by
  rw [pushoutMap_iso_hom]
  refine PushoutTorsor.hom_ext_of_cmp (fun α c hc => ?_)
  have hcov : α ≫ (pushoutTorsor P.toFppfTorsor r).projection =
      coverPt c ≫ P.toFppfTorsor.projection :=
    hc.trans (coverPt_proj c).symm
  have hB : (α ≫ PushoutTorsor.pushMap (pushoutTorsor P.toFppfTorsor r)
        (pushoutTorsor Q.toFppfTorsor r) (Hom.toFppfHom φ)) ≫
        (pushoutTorsor Q.toFppfTorsor r).projection =
      (coverPt c ≫ φ.iso.hom) ≫ Q.projection := by
    rw [Category.assoc, PushoutTorsor.pushMap_proj, Category.assoc, φ.over]
    exact hcov
  have hev : evPt Q.toFppfTorsor r (α ≫ PushoutTorsor.pushMap (pushoutTorsor P.toFppfTorsor r)
        (pushoutTorsor Q.toFppfTorsor r) (Hom.toFppfHom φ)) (coverPt c ≫ φ.iso.hom) hB =
      evPt P.toFppfTorsor r α (coverPt c) hcov :=
    PushoutTorsor.ev_pushMap_cover (pushoutTorsor P.toFppfTorsor r)
      (pushoutTorsor Q.toFppfTorsor r) (Hom.toFppfHom φ) α c hc hB hcov
  have htgt : (coverPt c ≫ φ.iso.hom) ≫ Q.target ≫ f.hom.hom =
      coverPt c ≫ P.target ≫ f.hom.hom := by
    rw [Category.assoc, ← Category.assoc φ.iso.hom Q.target f.hom.hom, φ.target]
  calc α ≫ PushoutTorsor.pushMap (pushoutTorsor P.toFppfTorsor r)
          (pushoutTorsor Q.toFppfTorsor r) (Hom.toFppfHom φ) ≫
        targetMap Q r f.hom.hom f.isEquivariantOver
      = (α ≫ PushoutTorsor.pushMap (pushoutTorsor P.toFppfTorsor r)
          (pushoutTorsor Q.toFppfTorsor r) (Hom.toFppfHom φ)) ≫
          targetMap Q r f.hom.hom f.isEquivariantOver := (Category.assoc _ _ _).symm
    _ = actPt (evPt Q.toFppfTorsor r (α ≫ PushoutTorsor.pushMap
            (pushoutTorsor P.toFppfTorsor r) (pushoutTorsor Q.toFppfTorsor r)
            (Hom.toFppfHom φ)) (coverPt c ≫ φ.iso.hom) hB)
          ((coverPt c ≫ φ.iso.hom) ≫ Q.target ≫ f.hom.hom) :=
        comp_targetMap_pt Q r f.isEquivariantOver _ _ hB
    _ = actPt (evPt P.toFppfTorsor r α (coverPt c) hcov)
          (coverPt c ≫ P.target ≫ f.hom.hom) := by rw [hev, htgt]
    _ = α ≫ targetMap P r f.hom.hom f.isEquivariantOver :=
        (comp_targetMap_pt P r f.isEquivariantOver α (coverPt c) hcov).symm

/-- **The functor induced on the fibres of the quotient stacks by an equivariant map through a
homomorphism of groups**: `P ↦ r_* P` with the induced map to `V`.  This is the fibrewise part of
the quotient-stack map `[U/G] ⟶ [V/H]`. -/
noncomputable def pushoutFunctor : ActionTorsor G U T ⥤ ActionTorsor H V T where
  obj P := pushoutObj r f P
  map {P Q} φ :=
    { iso := (pushoutMap (Hom.toFppfHom φ) r).iso
      over := (pushoutMap (Hom.toFppfHom φ) r).over
      equivariant := (pushoutMap (Hom.toFppfHom φ) r).equivariant
      target := pushoutMap_comp_target r f φ }
  map_id P := by
    refine Hom.ext _ _ ?_
    simp only [Hom.toFppfHom_id, pushoutMap_iso_hom]
    exact PushoutTorsor.pushMap_id (pushoutTorsor P.toFppfTorsor r)
  map_comp {P Q R} φ ψ := by
    refine Hom.ext _ _ ?_
    simp only [Hom.toFppfHom_comp, pushoutMap_iso_hom, comp_iso_hom]
    exact (PushoutTorsor.pushMap_comp (pushoutTorsor P.toFppfTorsor r)
      (pushoutTorsor Q.toFppfTorsor r) (pushoutTorsor R.toFppfTorsor r)
      (Hom.toFppfHom φ) (Hom.toFppfHom ψ)).symm

/-- **The base-change comparison of the pushout torsors is compatible with the maps to `V`.**
Both sides are computed at the tautological points of the trivialising cover of the base-changed
torsor by `TorsorPushout.comp_targetMap_pt`, where they agree because the evaluation pairing of
the base-changed pushout datum is the evaluation pairing of the first projections. -/
theorem pushoutPullbackHom_comp_target (b : T' ⟶ T) (P : ActionTorsor G U T) :
    (PushoutTorsor.pushoutPullbackHom P.toFppfTorsor r b).iso.hom ≫
        (pullbackObj b (pushoutObj r f P)).target =
      (pushoutObj r f (pullbackObj b P)).target := by
  refine PushoutTorsor.hom_ext_of_cmp (fun α c hc => ?_)
  have hcov : α ≫ (pushoutTorsor (P.toFppfTorsor.pullbackTorsor b) r).projection =
      coverPt c ≫ (P.toFppfTorsor.pullbackTorsor b).projection :=
    hc.trans (coverPt_proj c).symm
  have hY : (α ≫ (PushoutTorsor.pushoutPullbackHom P.toFppfTorsor r b).iso.hom) ≫
        Limits.pullback.snd (pushoutObj r f P).projection (fppfYoneda.map b) =
      coverPt c ≫ (P.toFppfTorsor.pullbackTorsor b).projection :=
    ((Category.assoc α _ _).trans (congrArg (fun x => α ≫ x)
      (PushoutTorsor.cmpMap_proj (pushoutTorsor (P.toFppfTorsor.pullbackTorsor b) r)
        (PushoutTorsor.pullbackDatum (pushoutTorsor P.toFppfTorsor r) b)))).trans hcov
  have h1 : ((α ≫ (PushoutTorsor.pushoutPullbackHom P.toFppfTorsor r b).iso.hom) ≫
        Limits.pullback.fst (pushoutObj r f P).projection (fppfYoneda.map b)) ≫
        pushoutProj P.toFppfTorsor r =
      (coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ P.projection :=
    PushoutTorsor.pullback_ev_cond (pushoutTorsor P.toFppfTorsor r) b _ (coverPt c) hY
  have hkey : evPt P.toFppfTorsor r
        ((α ≫ (PushoutTorsor.pushoutPullbackHom P.toFppfTorsor r b).iso.hom) ≫
          Limits.pullback.fst (pushoutObj r f P).projection (fppfYoneda.map b))
        (coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) h1 =
      evPt (P.toFppfTorsor.pullbackTorsor b) r α (coverPt c) hcov :=
    ((PushoutTorsor.pullbackDatum (pushoutTorsor P.toFppfTorsor r) b).ev_congr
      (PushoutTorsor.cmpMap_spec (pushoutTorsor (P.toFppfTorsor.pullbackTorsor b) r)
        (PushoutTorsor.pullbackDatum (pushoutTorsor P.toFppfTorsor r) b) α c hc)
      rfl hY (PushoutTorsor.cmpLocal_proj α c hc)).trans
      (PushoutTorsor.ev_cmpLocal α c hc)
  have htgt : (coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫
        P.target ≫ f.hom.hom =
      coverPt c ≫ (pullbackObj b P).target ≫ f.hom.hom := by
    rw [pullbackObj_target, Category.assoc, Category.assoc]
  calc α ≫ (PushoutTorsor.pushoutPullbackHom P.toFppfTorsor r b).iso.hom ≫
        (pullbackObj b (pushoutObj r f P)).target
      = ((α ≫ (PushoutTorsor.pushoutPullbackHom P.toFppfTorsor r b).iso.hom) ≫
          Limits.pullback.fst (pushoutObj r f P).projection (fppfYoneda.map b)) ≫
          targetMap P r f.hom.hom f.isEquivariantOver :=
        ((Category.assoc _ _ _).trans (Category.assoc α _ _)).symm
    _ = actPt (evPt P.toFppfTorsor r
          ((α ≫ (PushoutTorsor.pushoutPullbackHom P.toFppfTorsor r b).iso.hom) ≫
            Limits.pullback.fst (pushoutObj r f P).projection (fppfYoneda.map b))
          (coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) h1)
          ((coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫
            P.target ≫ f.hom.hom) :=
        comp_targetMap_pt P r f.isEquivariantOver _ _ h1
    _ = actPt (evPt (P.toFppfTorsor.pullbackTorsor b) r α (coverPt c) hcov)
          (coverPt c ≫ (pullbackObj b P).target ≫ f.hom.hom) := by rw [hkey, htgt]
    _ = α ≫ (pushoutObj r f (pullbackObj b P)).target :=
        (comp_targetMap_pt (pullbackObj b P) r f.isEquivariantOver α (coverPt c) hcov).symm

/-- **The comparison of the pushout with base change, as an arrow of action torsors.** -/
noncomputable def pushoutPullbackObjHom (b : T' ⟶ T) (P : ActionTorsor G U T) :
    pushoutObj r f (pullbackObj b P) ⟶ pullbackObj b (pushoutObj r f P) where
  iso := (PushoutTorsor.pushoutPullbackHom P.toFppfTorsor r b).iso
  over := (PushoutTorsor.pushoutPullbackHom P.toFppfTorsor r b).over
  equivariant := (PushoutTorsor.pushoutPullbackHom P.toFppfTorsor r b).equivariant
  target := pushoutPullbackHom_comp_target r f b P

/-- **`r_* (b^* P) ≅ b^* (r_* P)` for action torsors.**  The induced functor on the fibres of the
quotient stacks commutes with base change. -/
noncomputable def pushoutPullbackObjIso (b : T' ⟶ T) (P : ActionTorsor G U T) :
    pushoutObj r f (pullbackObj b P) ≅ pullbackObj b (pushoutObj r f P) :=
  ⟨pushoutPullbackObjHom r f b P, Groupoid.inv (pushoutPullbackObjHom r f b P),
    Groupoid.comp_inv _, Groupoid.inv_comp _⟩

/-- **The base-change comparison is natural in the action torsor.** -/
theorem pushoutPullbackObjHom_naturality (b : T' ⟶ T) {P Q : ActionTorsor G U T} (φ : P ⟶ Q) :
    (pushoutFunctor r f).map ((pullbackFunctor b).map φ) ≫ pushoutPullbackObjHom r f b Q =
      pushoutPullbackObjHom r f b P ≫ (pullbackFunctor b).map ((pushoutFunctor r f).map φ) := by
  have key := PushoutTorsor.pushMap_comp_pushoutPullbackFst (Hom.toFppfHom φ) r b
    (Hom.toFppfHom ((pullbackFunctor b).map φ)) rfl
  refine Hom.ext _ _ (Limits.pullback.hom_ext ?_ ?_)
  · have e1 : ((pushoutFunctor r f).map ((pullbackFunctor b).map φ) ≫
          pushoutPullbackObjHom r f b Q).iso.hom ≫
        Limits.pullback.fst (pushoutObj r f Q).projection (fppfYoneda.map b) =
        PushoutTorsor.pushMap (pushoutTorsor (P.toFppfTorsor.pullbackTorsor b) r)
          (pushoutTorsor (Q.toFppfTorsor.pullbackTorsor b) r)
          (Hom.toFppfHom ((pullbackFunctor b).map φ)) ≫
          PushoutTorsor.pushoutPullbackFst Q.toFppfTorsor r b :=
      Category.assoc _ _ _
    have e3 : PushoutTorsor.pushoutPullbackFst P.toFppfTorsor r b ≫
          PushoutTorsor.pushMap (pushoutTorsor P.toFppfTorsor r)
            (pushoutTorsor Q.toFppfTorsor r) (Hom.toFppfHom φ) =
        (pushoutPullbackObjHom r f b P ≫
          (pullbackFunctor b).map ((pushoutFunctor r f).map φ)).iso.hom ≫
          Limits.pullback.fst (pushoutObj r f Q).projection (fppfYoneda.map b) :=
      ((Category.assoc _ _ _).trans (congrArg
        (fun x => (PushoutTorsor.pushoutPullbackHom P.toFppfTorsor r b).iso.hom ≫ x)
        (FppfTorsor.pullbackMap_fst b ((pushoutFunctor r f).map φ).iso.hom
          ((pushoutFunctor r f).map φ).over).symm)).trans (Category.assoc _ _ _).symm
    exact (e1.trans key).trans e3
  · exact (((pushoutFunctor r f).map ((pullbackFunctor b).map φ) ≫
      pushoutPullbackObjHom r f b Q).over).trans
      ((pushoutPullbackObjHom r f b P ≫
        (pullbackFunctor b).map ((pushoutFunctor r f).map φ)).over).symm

/-- **The induced functor commutes with base change, naturally**: the natural isomorphism
`b^* ⋙ r_* ≅ r_* ⋙ b^*` of functors `ActionTorsor G U T ⥤ ActionTorsor H V T'`.  This is the
naturality datum of the prospective strong transformation `[U/G] ⟶ [V/H]`. -/
noncomputable def pushoutPullbackNatIso (b : T' ⟶ T) :
    pullbackFunctor b ⋙ pushoutFunctor (T := T') r f ≅
      pushoutFunctor (T := T) r f ⋙ pullbackFunctor b :=
  NatIso.ofComponents (fun P => pushoutPullbackObjIso r f b P)
    (fun {_ _} φ => pushoutPullbackObjHom_naturality r f b φ)

/-- The induced functor on objects. -/
@[simp]
theorem pushoutFunctor_obj (P : ActionTorsor G U T) :
    (pushoutFunctor (T := T) r f).obj P = pushoutObj r f P :=
  rfl

/-- The induced functor on arrows. -/
@[simp]
theorem pushoutFunctor_map_iso_hom {P Q : ActionTorsor G U T} (φ : P ⟶ Q) :
    ((pushoutFunctor (T := T) r f).map φ).iso.hom = (pushoutMap (Hom.toFppfHom φ) r).iso.hom :=
  rfl

/-- **The fibrewise structure map `[U/G] ⟶ BH`** induced by a homomorphism `r : G ⟶ H` of group
algebraic spaces: send a `G`-torsor with equivariant map to `U` to the pushout `H`-torsor with its
(unique) map to the one-point `H`-space. -/
noncomputable def toClassifyingFunctor :
    ActionTorsor G U T ⥤ ActionTorsor H (AlgebraicSpaceAction.pointAction H) T :=
  pushoutFunctor r (AlgebraicSpaceAction.HomOver.toPointOver r U)

/-! ### The coherence laws of the strong transformation -/

section Coherence

variable {T'' : Scheme.{u}}

/-- **Naturality of the base-change comparison in the 2-cells** (the component form of
`naturality_naturality` for `ActionTorsor.pushoutStrongTrans`): the source bicategory is locally
discrete, so the only 2-cells are identities and the law is vacuous. -/
theorem pushoutPullbackNatIso_naturality (b : T' ⟶ T) :
    Functor.whiskerRight (𝟙 (pullbackFunctor (U := U) b)) (pushoutFunctor (T := T') r f) ≫
        (pushoutPullbackNatIso r f b).hom =
      (pushoutPullbackNatIso r f b).hom ≫
        Functor.whiskerLeft (pushoutFunctor (T := T) r f)
          (𝟙 (pullbackFunctor (U := V) b)) := by
  simp

/-- **Unit coherence of the base-change comparison of the induced functor** (the component form
of `naturality_id` for `ActionTorsor.pushoutStrongTrans`): the comparison
`r_* ((𝟙 T)^* -) ≅ (𝟙 T)^* (r_* -)` matches the unit comparisons `pullbackFunctorIdIso` of base
change on the two sides.  Reduced to `TorsorPushout.PushoutTorsor.pushoutPullbackFst_id`. -/
theorem pushoutPullbackNatIso_id :
    (pushoutPullbackNatIso r f (𝟙 T)).hom ≫
        Functor.whiskerLeft (pushoutFunctor (T := T) r f) (pullbackFunctorIdIso (U := V)).hom =
      Functor.whiskerRight (pullbackFunctorIdIso (U := U)).hom (pushoutFunctor (T := T) r f) ≫
        (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv := by
  ext P
  refine Hom.ext _ _ ?_
  simp only [NatTrans.comp_app, comp_iso_hom, id_iso_hom, Category.comp_id,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  exact PushoutTorsor.pushoutPullbackFst_id P.toFppfTorsor _ rfl

/-- **Composition coherence of the base-change comparison, on objects**: the comparison for a
composite `b₂ ≫ b₁` is the composite of the comparison for `b₂`, the base change along `b₂` of
the comparison for `b₁`, and the comparison isomorphisms `pullbackCompIsoApp` of base change.
The two sides are morphisms into an iterated fibre product; their `snd` legs agree because both
lie over `T''`, and their `fst ≫ fst` legs agree by
`TorsorPushout.PushoutTorsor.pushoutPullbackFst_comp`. -/
theorem pushoutPullbackObjHom_comp (b₁ : T' ⟶ T) (b₂ : T'' ⟶ T') (P : ActionTorsor G U T) :
    pushoutPullbackObjHom r f (b₂ ≫ b₁) P ≫
        (pullbackCompIsoApp b₂ b₁ (pushoutObj r f P)).hom =
      (pushoutFunctor r f).map ((pullbackCompIsoApp b₂ b₁ P).hom) ≫
        pushoutPullbackObjHom r f b₂ (pullbackObj b₁ P) ≫
          (pullbackFunctor b₂).map (pushoutPullbackObjHom r f b₁ P) := by
  have key := PushoutTorsor.pushoutPullbackFst_comp (r := r) P.toFppfTorsor b₁ b₂
    (Hom.toFppfHom (pullbackCompIsoApp b₂ b₁ P).hom) rfl
  refine Hom.ext _ _ (hom_ext_pullback₂ (pushoutObj r f P).projection
    (fppfYoneda.map b₁) (fppfYoneda.map b₂) ?_ ?_)
  · have hK : (FppfTorsor.pullbackCompIso (pushoutObj r f P).toFppfTorsor b₂ b₁).hom ≫
        Limits.pullback.fst (Limits.pullback.snd (pushoutObj r f P).projection
            (fppfYoneda.map b₁)) (fppfYoneda.map b₂) ≫
          Limits.pullback.fst (pushoutObj r f P).projection (fppfYoneda.map b₁) =
        Limits.pullback.fst (pushoutObj r f P).projection (fppfYoneda.map (b₂ ≫ b₁)) :=
      FppfTorsor.pullbackCompIso_hom_fst_fst (pushoutObj r f P).toFppfTorsor b₂ b₁
    have hq : FppfTorsor.pullbackMap b₂ (pushoutPullbackObjHom r f b₁ P).iso.hom
          (pushoutPullbackObjHom r f b₁ P).over ≫
          Limits.pullback.fst (Limits.pullback.snd (pushoutObj r f P).projection
            (fppfYoneda.map b₁)) (fppfYoneda.map b₂) =
        Limits.pullback.fst (pushoutObj r f (pullbackObj b₁ P)).projection
            (fppfYoneda.map b₂) ≫ (pushoutPullbackObjHom r f b₁ P).iso.hom :=
      FppfTorsor.pullbackMap_fst b₂ _ _
    have hR : (PushoutTorsor.pushMap
            (pushoutTorsor (P.toFppfTorsor.pullbackTorsor (b₂ ≫ b₁)) r)
            (pushoutTorsor ((P.toFppfTorsor.pullbackTorsor b₁).pullbackTorsor b₂) r)
            (Hom.toFppfHom (pullbackCompIsoApp b₂ b₁ P).hom) ≫
          (PushoutTorsor.pushoutPullbackHom (P.toFppfTorsor.pullbackTorsor b₁) r b₂).iso.hom ≫
            FppfTorsor.pullbackMap b₂ (pushoutPullbackObjHom r f b₁ P).iso.hom
              (pushoutPullbackObjHom r f b₁ P).over) ≫
          Limits.pullback.fst (Limits.pullback.snd (pushoutObj r f P).projection
            (fppfYoneda.map b₁)) (fppfYoneda.map b₂) ≫
            Limits.pullback.fst (pushoutObj r f P).projection (fppfYoneda.map b₁) =
        PushoutTorsor.pushMap (pushoutTorsor (P.toFppfTorsor.pullbackTorsor (b₂ ≫ b₁)) r)
            (pushoutTorsor ((P.toFppfTorsor.pullbackTorsor b₁).pullbackTorsor b₂) r)
            (Hom.toFppfHom (pullbackCompIsoApp b₂ b₁ P).hom) ≫
          ((PushoutTorsor.pushoutPullbackHom (P.toFppfTorsor.pullbackTorsor b₁) r b₂).iso.hom ≫
            Limits.pullback.fst (pushoutObj r f (pullbackObj b₁ P)).projection
              (fppfYoneda.map b₂)) ≫
            (pushoutPullbackObjHom r f b₁ P).iso.hom ≫
              Limits.pullback.fst (pushoutObj r f P).projection (fppfYoneda.map b₁) :=
      reassoc_of_comp_eq _ _ _ _ _ _ _ hq
    exact ((Category.assoc _ _ _).trans (congrArg (fun x =>
      (PushoutTorsor.pushoutPullbackHom P.toFppfTorsor r (b₂ ≫ b₁)).iso.hom ≫ x)
      hK)).trans (key.trans hR.symm)
  · exact (pushoutPullbackObjHom r f (b₂ ≫ b₁) P ≫
      (pullbackCompIsoApp b₂ b₁ (pushoutObj r f P)).hom).over.trans
      ((pushoutFunctor r f).map ((pullbackCompIsoApp b₂ b₁ P).hom) ≫
        pushoutPullbackObjHom r f b₂ (pullbackObj b₁ P) ≫
          (pullbackFunctor b₂).map (pushoutPullbackObjHom r f b₁ P)).over.symm

/-- **Composition coherence of the base-change comparison of the induced functor** (the
component form of `naturality_comp` for `ActionTorsor.pushoutStrongTrans`). -/
theorem pushoutPullbackNatIso_comp (b₁ : T' ⟶ T) (b₂ : T'' ⟶ T') :
    (pushoutPullbackNatIso r f (b₂ ≫ b₁)).hom ≫
        Functor.whiskerLeft (pushoutFunctor (T := T) r f)
          (pullbackFunctorCompIso (U := V) b₂ b₁).hom =
      Functor.whiskerRight (pullbackFunctorCompIso (U := U) b₂ b₁).hom
          (pushoutFunctor (T := T'') r f) ≫
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (pullbackFunctor (U := U) b₁) (pushoutPullbackNatIso r f b₂).hom ≫
            (Functor.associator _ _ _).inv ≫
              Functor.whiskerRight (pushoutPullbackNatIso r f b₁).hom
                  (pullbackFunctor (U := V) b₂) ≫
                (Functor.associator _ _ _).hom := by
  ext P
  refine Hom.ext _ _ ?_
  simp only [NatTrans.comp_app, comp_iso_hom, Category.comp_id, Category.id_comp,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  exact congrArg (fun x => Hom.iso x |>.hom) (pushoutPullbackObjHom_comp r f b₁ b₂ P)

/-- **The quotient-stack map `[U/G] ⟶ [V/H]` induced by an equivariant map through a
homomorphism of group algebraic spaces**, as a strong transformation of the base-change
pseudofunctors of equivariant torsors.  Its components are the fibrewise functors
`ActionTorsor.pushoutFunctor r f` and its naturality 2-isomorphisms are the base-change
comparisons `ActionTorsor.pushoutPullbackNatIso`; the three coherence laws are
`ActionTorsor.pushoutPullbackNatIso_id` and `ActionTorsor.pushoutPullbackNatIso_comp` (the
naturality in the 2-cells is automatic because the source bicategory is locally discrete). -/
noncomputable def pushoutStrongTrans :
    Pseudofunctor.StrongTrans (pullbackPseudofunctor G U) (pullbackPseudofunctor H V) where
  app a := (pushoutFunctor (T := a.as.unop) r f).toCatHom
  naturality {_ _} g := Cat.Hom.isoMk (pushoutPullbackNatIso r f g.as.unop)
  naturality_naturality {_ _ _ _} eta := by
    obtain rfl := obj_ext_of_isDiscrete eta
    obtain rfl : eta = 𝟙 _ := Subsingleton.elim _ _
    ext1
    simpa only [PrelaxFunctor.map₂_id, pullbackPseudofunctor_map] using!
      pushoutPullbackNatIso_naturality r f _
  naturality_id a := by
    ext1
    simpa [pullbackPseudofunctor_mapId, pullbackPseudofunctor_map] using!
      pushoutPullbackNatIso_id r f
  naturality_comp {a b c} g₁ g₂ := by
    ext1
    simpa [pullbackPseudofunctor_mapComp, pullbackPseudofunctor_map] using!
      pushoutPullbackNatIso_comp r f g₁.as.unop g₂.as.unop

/-- **The quotient-stack map `[U/G] ⟶ [V/H]` at the level of the bundled quotient stacks.** -/
noncomputable def quotientStackMap :
    Pseudofunctor.StrongTrans (quotientStack G U).toPseudofunctor
      (quotientStack H V).toPseudofunctor :=
  pushoutStrongTrans r f

/-- **The structure map `[U/G] ⟶ BH` of a homomorphism `r : G ⟶ H`**, as a strong
transformation: contract a `G`-torsor with equivariant map to `U` to the pushout `H`-torsor,
with its unique map to the one-point `H`-space. -/
noncomputable def toClassifyingStrongTrans (U : AlgebraicSpaceAction G) :
    Pseudofunctor.StrongTrans (pullbackPseudofunctor G U)
      (pullbackPseudofunctor H (AlgebraicSpaceAction.pointAction H)) :=
  pushoutStrongTrans r (AlgebraicSpaceAction.HomOver.toPointOver r U)

/-- **The structure map `[U/G] ⟶ BH` at the level of the bundled stacks.** -/
noncomputable def toClassifyingStackMap (U : AlgebraicSpaceAction G) :
    Pseudofunctor.StrongTrans (quotientStack G U).toPseudofunctor
      (classifyingStack H).toPseudofunctor :=
  toClassifyingStrongTrans r U

end Coherence

end ActionTorsor

end GromovWitten.AlgebraicGeometry
