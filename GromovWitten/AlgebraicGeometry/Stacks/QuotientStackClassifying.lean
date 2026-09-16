/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.QuotientStackMaps

/-!
# The quotient prestack `[U/G]` and the classifying prestack `BG`

This file exports the two quotient constructions attached to a group algebraic space `G`:

* `quotientPrestack G U`, the groupoid-valued pseudofunctor `[U/G]` on the big fppf site of
  schemes whose fibre over a scheme `T` is *literally* the groupoid `ActionTorsor G U T` of
  `G`-torsors over `T` with an equivariant map to `U`, base change being
  `ActionTorsor.pullbackFunctor`;
* `classifyingPrestack G = BG`, the special case `U = pt` for the one-point algebraic space
  with its trivial `G`-action.

Both are obtained from the already constructed pseudofunctor
`ActionTorsor.pullbackPseudofunctor`; no stackification and no fibre equivalence is supplied by
a caller.  The fibre identification of `BG` is proved rather than assumed: the forgetful functor
`ActionTorsor.forgetTarget` is an equivalence `ActionTorsor G (pointAction G) T ≌ FppfTorsor G T`
(`ActionTorsor.classifyingFibreEquiv`), and these equivalences commute strictly with base change
(`ActionTorsor.classifyingFibreEquivPullbackIso`).

The trivial torsor `FppfTorsor.trivial G T = G × T` is constructed with all of its data: the
left-multiplication action, the principal isomorphism `G × P ≅ P ×_T P` (whose inverse uses the
inverse of the group object), and its global section.  Hence every fibre of `BG` is nonempty.

Finally, `quotientPrestackMap` turns an equivariant map of `G`-spaces into a morphism of
quotient prestacks, and `quotientToClassifying` is the resulting structure morphism
`[U/G] ⟶ BG`.

**What is still missing.**  These objects are *prestacks*: they are not bundled as `FppfStack`
because `Pseudofunctor.IsStack Scheme.fppfTopology (pullbackPseudofunctor G U)` is not
available.  Concretely, two statements remain open and neither is assumed anywhere below:

1. *Descent of arrows*: for torsors `M N : ActionTorsor G U S`, the presheaf
   `(pullbackPseudofunctor G U).presheafHom M N` on `Over S` is an fppf sheaf.  This is the
   statement that a morphism of fppf sheaves over `h_S` may be glued from compatible morphisms
   defined after base change along the members of an fppf covering family of `S`.
2. *Effectiveness of descent*: for a covering sieve `R ∈ Scheme.fppfTopology S`, the functor
   `(pullbackPseudofunctor G U).toDescentData` into the category of descent data is essentially
   surjective, i.e. a compatible family of torsors on a cover glues to a torsor over `S`.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace AlgebraicSpaceAction

variable (G : AlgebraicSpaceGroup.{u})

/-- The trivial action of a group algebraic space on an algebraic space. -/
noncomputable def trivial (X : AlgebraicSpace.{u}) : AlgebraicSpaceAction G where
  space := X
  action :=
    { smul := snd G.space.toSheaf X.toSheaf
      one_smul := by
        simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
          MonoidalCategory.selfLeftAction_actionUnitIso]
        simp [leftUnitor_hom]
      mul_smul := by
        simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
          MonoidalCategory.selfLeftAction_actionHomRight,
          MonoidalCategory.selfLeftAction_actionAssocIso]
        simp }

@[simp]
theorem trivial_space (X : AlgebraicSpace.{u}) : (trivial G X).space = X :=
  rfl

/-- The one-point algebraic space, used as the target of the classifying prestack. -/
noncomputable def point : AlgebraicSpace.{u} :=
  AlgebraicSpace.ofScheme.obj (⊤_ Scheme.{u})

/-- The fppf sheaf of the one-point algebraic space is a terminal object. -/
noncomputable def pointIsTerminal : IsTerminal (point.{u}).toSheaf :=
  IsTerminal.isTerminalObj fppfYoneda _ terminalIsTerminal

/-- The trivial `G`-action on the one-point algebraic space. -/
noncomputable def pointAction : AlgebraicSpaceAction G :=
  trivial G point

variable {G}

/-- The unique equivariant map from a `G`-space to the one-point `G`-space. -/
noncomputable def toPoint (U : AlgebraicSpaceAction G) : U ⟶ pointAction G where
  hom := AlgebraicSpace.homMk (pointIsTerminal.from U.space.toSheaf)
  equivariant := pointIsTerminal.hom_ext _ _

end AlgebraicSpaceAction

/-- The quotient prestack `[U/G]`: the groupoid-valued pseudofunctor on the big fppf site of
schemes whose fibre over `T` is the groupoid of `G`-torsors over `T` equipped with an
equivariant map to `U`.  Its fppf descent condition is not yet established, so this is not
bundled as an `FppfStack`. -/
noncomputable abbrev quotientPrestack (G : AlgebraicSpaceGroup.{u})
    (U : AlgebraicSpaceAction G) :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u + 1, u + 1} :=
  ActionTorsor.pullbackPseudofunctor G U

/-- The classifying prestack `BG = [pt/G]`. -/
noncomputable abbrev classifyingPrestack (G : AlgebraicSpaceGroup.{u}) :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u + 1, u + 1} :=
  quotientPrestack G (AlgebraicSpaceAction.pointAction G)

/-- An equivariant map `U ⟶ V` of `G`-spaces induces a morphism of quotient prestacks
`[U/G] ⟶ [V/G]`. -/
noncomputable abbrev quotientPrestackMap {G : AlgebraicSpaceGroup.{u}}
    {U V : AlgebraicSpaceAction G} (q : U ⟶ V) :
    Pseudofunctor.StrongTrans (quotientPrestack G U) (quotientPrestack G V) :=
  ActionTorsor.mapTargetStrongTrans q

/-- The structure morphism `[U/G] ⟶ BG`, induced by the unique equivariant map from `U` to the
one-point `G`-space. -/
noncomputable abbrev quotientToClassifying {G : AlgebraicSpaceGroup.{u}}
    (U : AlgebraicSpaceAction G) :
    Pseudofunctor.StrongTrans (quotientPrestack G U) (classifyingPrestack G) :=
  quotientPrestackMap U.toPoint

namespace FppfTorsor

variable {G : AlgebraicSpaceGroup.{u}} {T T' : Scheme.{u}}

/-- An arrow of fppf `G`-torsors over a fixed base is an equivariant isomorphism over that
base. -/
structure Hom (P Q : FppfTorsor G T) where
  /-- The underlying isomorphism of fppf sheaves. -/
  iso : P.P ≅ Q.P
  /-- Compatibility with the projections to the base. -/
  over : iso.hom ≫ Q.projection = P.projection
  /-- Equivariance. -/
  equivariant :
    ModObj.smul (M := G.space.toSheaf) (X := P.P) ≫ iso.hom =
      G.space.toSheaf ◁ iso.hom ≫
        ModObj.smul (M := G.space.toSheaf) (X := Q.P)

@[ext]
theorem Hom.ext {P Q : FppfTorsor G T} (f g : Hom P Q)
    (h : f.iso.hom = g.iso.hom) : f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  exact Iso.ext h

/-- Torsors over a fixed base form a category. -/
instance : Category (FppfTorsor G T) where
  Hom := Hom
  id P :=
    { iso := Iso.refl _
      over := by simp
      equivariant := by simp }
  comp f g :=
    { iso := f.iso ≪≫ g.iso
      over := by simp [Category.assoc, g.over, f.over]
      equivariant := by
        rw [Iso.trans_hom]
        calc
          _ = (G.space.toSheaf ◁ f.iso.hom ≫
                ModObj.smul (M := G.space.toSheaf) (X := _)) ≫ g.iso.hom := by
              rw [← Category.assoc, f.equivariant]
          _ = G.space.toSheaf ◁ f.iso.hom ≫
                (ModObj.smul (M := G.space.toSheaf) (X := _) ≫ g.iso.hom) := by
              simp only [Category.assoc]
          _ = G.space.toSheaf ◁ f.iso.hom ≫
                (G.space.toSheaf ◁ g.iso.hom ≫
                  ModObj.smul (M := G.space.toSheaf) (X := _)) := by
              rw [g.equivariant]
          _ = G.space.toSheaf ◁ (f.iso.hom ≫ g.iso.hom) ≫
                ModObj.smul (M := G.space.toSheaf) (X := _) := by
              simp }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

/-- Every arrow of torsors is invertible. -/
instance : Groupoid (FppfTorsor G T) where
  inv f :=
    { iso := f.iso.symm
      over := by
        apply (cancel_epi f.iso.hom).1
        simp [f.over]
      equivariant := by
        apply (cancel_mono f.iso.hom).1
        simp only [Category.assoc, f.equivariant]
        simp }
  inv_comp f := by
    apply Hom.ext
    exact f.iso.inv_hom_id
  comp_inv f := by
    apply Hom.ext
    exact f.iso.hom_inv_id

@[simp]
theorem id_iso_hom (P : FppfTorsor G T) : (𝟙 P : P ⟶ P).iso.hom = 𝟙 P.P :=
  rfl

@[simp]
theorem comp_iso_hom {P Q R : FppfTorsor G T} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).iso.hom = f.iso.hom ≫ g.iso.hom :=
  rfl

/-- Base change of fppf torsors along a morphism of schemes. -/
@[reducible]
noncomputable def pullbackFunctor (b : T' ⟶ T) : FppfTorsor G T ⥤ FppfTorsor G T' where
  obj P := P.pullbackTorsor b
  map {P Q} f :=
    { iso := pullbackMapIso b f.iso f.over
      over := pullbackMap_snd b f.iso.hom f.over
      equivariant := pullbackSmul_pullbackMap b f.iso.hom f.over f.equivariant }
  map_id P := by
    apply Hom.ext
    exact pullbackMap_id b (by simp)
  map_comp f g := by
    apply Hom.ext
    exact pullbackMap_comp b f.iso.hom g.iso.hom f.over g.over
      (by rw [Category.assoc, g.over, f.over])

section Trivial

variable (G : AlgebraicSpaceGroup.{u}) (T : Scheme.{u})

/-- The action map of the trivial `G`-torsor over `T`: left multiplication on the first
factor. -/
noncomputable def trivialSmul :
    G.space.toSheaf ⊗ (G.space.toSheaf ⊗ fppfYoneda.obj T) ⟶
      G.space.toSheaf ⊗ fppfYoneda.obj T :=
  lift (fst _ _ * (snd _ _ ≫ fst _ _)) (snd _ _ ≫ snd _ _)

@[reassoc (attr := simp)]
theorem trivialSmul_fst :
    trivialSmul G T ≫ fst _ _ =
      fst _ _ * (snd G.space.toSheaf (G.space.toSheaf ⊗ fppfYoneda.obj T) ≫ fst _ _) :=
  lift_fst _ _

@[reassoc (attr := simp)]
theorem trivialSmul_snd :
    trivialSmul G T ≫ snd _ _ =
      snd G.space.toSheaf (G.space.toSheaf ⊗ fppfYoneda.obj T) ≫ snd _ _ :=
  lift_snd _ _

/-- The trivial `G`-action on `G × T`. -/
@[instance_reducible]
noncomputable def trivialAction :
    ModObj G.space.toSheaf (G.space.toSheaf ⊗ fppfYoneda.obj T) where
  smul := trivialSmul G T
  one_smul := by
    simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
      MonoidalCategory.selfLeftAction_actionUnitIso]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, trivialSmul_fst, MonObj.comp_mul, whiskerRight_fst,
        ← Category.assoc, whiskerRight_snd]
      rw [show fst (𝟙_ FppfSheaf.{u}) (G.space.toSheaf ⊗ fppfYoneda.obj T) ≫ η =
          (1 : _ ⟶ G.space.toSheaf) from
        congrArg (· ≫ η) (toUnit_unique (fst _ _) (toUnit _))]
      simp [leftUnitor_hom]
    · rw [Category.assoc, trivialSmul_snd, ← Category.assoc, whiskerRight_snd]
      simp [leftUnitor_hom]
  mul_smul := by
    have hmul : ∀ {X : FppfSheaf.{u}} (k : X ⟶ G.space.toSheaf ⊗ G.space.toSheaf),
        k ≫ μ = (k ≫ fst _ _) * (k ≫ snd _ _) := by
      intro X k
      rw [CategoryTheory.Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
    simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
      MonoidalCategory.selfLeftAction_actionHomRight,
      MonoidalCategory.selfLeftAction_actionAssocIso]
    apply CartesianMonoidalCategory.hom_ext
    · simp [MonObj.comp_mul, hmul, mul_assoc]
    · simp

/-- Composition into an inverse is the inverse of the composition. -/
theorem comp_inv_hom {X Y : FppfSheaf.{u}} (k : X ⟶ Y) (g : Y ⟶ G.space.toSheaf) :
    k ≫ g⁻¹ = (k ≫ g)⁻¹ := by
  simp [CategoryTheory.Hom.inv_def]

/-- The principal map of the trivial `G`-torsor over `T`. -/
noncomputable def trivialPrincipalMap :
    G.space.toSheaf ⊗ (G.space.toSheaf ⊗ fppfYoneda.obj T) ⟶
      Limits.pullback (snd G.space.toSheaf (fppfYoneda.obj T))
        (snd G.space.toSheaf (fppfYoneda.obj T)) :=
  Limits.pullback.lift (trivialSmul G T) (snd _ _) (trivialSmul_snd G T)

/-- The inverse of the principal map of the trivial `G`-torsor over `T`. -/
noncomputable def trivialPrincipalInv :
    Limits.pullback (snd G.space.toSheaf (fppfYoneda.obj T))
        (snd G.space.toSheaf (fppfYoneda.obj T)) ⟶
      G.space.toSheaf ⊗ (G.space.toSheaf ⊗ fppfYoneda.obj T) :=
  lift ((Limits.pullback.fst _ _ ≫ fst _ _) * (Limits.pullback.snd _ _ ≫ fst _ _)⁻¹)
    (Limits.pullback.snd _ _)

theorem trivialPrincipalMap_inv :
    trivialPrincipalMap G T ≫ trivialPrincipalInv G T = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, trivialPrincipalInv, lift_fst, MonObj.comp_mul, comp_inv_hom,
      ← Category.assoc, ← Category.assoc, trivialPrincipalMap, Limits.pullback.lift_fst,
      Limits.pullback.lift_snd, trivialSmul_fst]
    simp
  · rw [Category.assoc, trivialPrincipalInv, lift_snd, trivialPrincipalMap,
      Limits.pullback.lift_snd]
    simp

theorem trivialPrincipalInv_map :
    trivialPrincipalInv G T ≫ trivialPrincipalMap G T = 𝟙 _ := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, trivialPrincipalMap, Limits.pullback.lift_fst, Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, trivialSmul_fst, MonObj.comp_mul, ← Category.assoc,
        trivialPrincipalInv, lift_fst]
      simp
    · rw [Category.assoc, trivialSmul_snd, ← Category.assoc, trivialPrincipalInv,
        lift_snd]
      exact Limits.pullback.condition.symm
  · rw [Category.assoc, trivialPrincipalMap, Limits.pullback.lift_snd,
      trivialPrincipalInv, lift_snd, Category.id_comp]

instance : IsIso (trivialPrincipalMap G T) :=
  ⟨trivialPrincipalInv G T, trivialPrincipalMap_inv G T, trivialPrincipalInv_map G T⟩

/-- The canonical fppf-local section of the trivial torsor: it is globally trivial, so the
cover is the identity of `T`. -/
noncomputable def trivialLocalSection :
    FppfLocalSection (G.space.toSheaf ⊗ fppfYoneda.obj T) T
      (snd G.space.toSheaf (fppfYoneda.obj T)) where
  coverScheme := T
  cover := 𝟙 T
  flat := inferInstance
  locallyOfFinitePresentation := inferInstance
  surjective := inferInstance
  localLift := lift (1 : fppfYoneda.obj T ⟶ G.space.toSheaf) (𝟙 _)
  localLift_over := by simp

/-- The trivial `G`-torsor `G × T` over a scheme `T`.  In particular every fibre of the
classifying prestack `BG` is nonempty. -/
noncomputable def trivial : FppfTorsor G T where
  P := G.space.toSheaf ⊗ fppfYoneda.obj T
  action := trivialAction G T
  projection := snd _ _
  action_over := trivialSmul_snd G T
  principalMap := trivialPrincipalMap G T
  principal_fst := Limits.pullback.lift_fst _ _ _
  principal_snd := Limits.pullback.lift_snd _ _ _
  principal_isIso := inferInstance
  locallyTrivial := trivialLocalSection G T

instance : Nonempty (FppfTorsor G T) :=
  ⟨trivial G T⟩

end Trivial

end FppfTorsor

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T T' : Scheme.{u}}

/-- Forgetting the equivariant map to `U` sends an object of `[U/G]` to the underlying
`G`-torsor. -/
noncomputable def forgetTarget : ActionTorsor G U T ⥤ FppfTorsor G T where
  obj P := P.toFppfTorsor
  map f :=
    { iso := f.iso
      over := f.over
      equivariant := f.equivariant }
  map_id P := by
    apply FppfTorsor.Hom.ext
    rfl
  map_comp f g := by
    apply FppfTorsor.Hom.ext
    rfl

/-- Forgetting the target map commutes strictly with base change. -/
noncomputable def forgetTargetPullbackIso (b : T' ⟶ T) :
    pullbackFunctor (U := U) b ⋙ forgetTarget (T := T') ≅
      forgetTarget (T := T) ⋙ FppfTorsor.pullbackFunctor b :=
  Iso.refl _

section Classifying

variable {G : AlgebraicSpaceGroup.{u}} {T T' : Scheme.{u}}

/-- A `G`-torsor over `T`, regarded as an object of the fibre of `BG` over `T`.  The equivariant
map to the one-point space is the unique such map. -/
noncomputable def ofFppfTorsor (P : FppfTorsor G T) :
    ActionTorsor G (AlgebraicSpaceAction.pointAction G) T where
  toFppfTorsor := P
  target := AlgebraicSpaceAction.pointIsTerminal.from P.P
  target_equivariant := AlgebraicSpaceAction.pointIsTerminal.hom_ext _ _

@[simp]
theorem ofFppfTorsor_toFppfTorsor (P : FppfTorsor G T) :
    (ofFppfTorsor P).toFppfTorsor = P :=
  rfl

/-- The functor promoting a `G`-torsor to an object of the fibre of `BG`. -/
noncomputable def ofFppfTorsorFunctor :
    FppfTorsor G T ⥤ ActionTorsor G (AlgebraicSpaceAction.pointAction G) T where
  obj := ofFppfTorsor
  map f :=
    { iso := f.iso
      over := f.over
      equivariant := f.equivariant
      target := AlgebraicSpaceAction.pointIsTerminal.hom_ext _ _ }
  map_id P := by
    apply Hom.ext
    rfl
  map_comp f g := by
    apply Hom.ext
    rfl

/-- The fibre of the classifying prestack `BG` over a scheme `T` is the groupoid of fppf
`G`-torsors over `T`.  The equivalence is the forgetful functor; no fibre equivalence is
supplied by a caller. -/
noncomputable def classifyingFibreEquiv (G : AlgebraicSpaceGroup.{u}) (T : Scheme.{u}) :
    ActionTorsor G (AlgebraicSpaceAction.pointAction G) T ≌ FppfTorsor G T where
  functor := forgetTarget
  inverse := ofFppfTorsorFunctor
  unitIso := NatIso.ofComponents
    (fun P ↦ asIso
      { iso := Iso.refl _
        over := Category.id_comp _
        equivariant := by rfl
        target := AlgebraicSpaceAction.pointIsTerminal.hom_ext _ _ })
    (fun {P Q} f ↦ by
      apply Hom.ext
      change f.iso.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.iso.hom
      simp)
  counitIso := Iso.refl _
  functor_unitIso_comp P := by
    apply FppfTorsor.Hom.ext
    change 𝟙 P.P ≫ 𝟙 P.P = 𝟙 P.P
    simp

@[simp]
theorem classifyingFibreEquiv_functor (G : AlgebraicSpaceGroup.{u}) (T : Scheme.{u}) :
    (classifyingFibreEquiv G T).functor = forgetTarget :=
  rfl

/-- Every fibre of the classifying prestack is inhabited by the trivial torsor. -/
instance (G : AlgebraicSpaceGroup.{u}) (T : Scheme.{u}) :
    Nonempty (ActionTorsor G (AlgebraicSpaceAction.pointAction G) T) :=
  ⟨ofFppfTorsor (FppfTorsor.trivial G T)⟩

/-- The fibre equivalences of `BG` commute strictly with base change along a scheme
morphism. -/
noncomputable def classifyingFibreEquivPullbackIso (b : T' ⟶ T) :
    pullbackFunctor (U := AlgebraicSpaceAction.pointAction G) b ⋙
        (classifyingFibreEquiv G T').functor ≅
      (classifyingFibreEquiv G T).functor ⋙ FppfTorsor.pullbackFunctor b :=
  forgetTargetPullbackIso b

end Classifying

end ActionTorsor

end GromovWitten.AlgebraicGeometry
