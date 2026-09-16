/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.Algebraic
import GromovWitten.AlgebraicGeometry.Stacks.QuotientPresentation
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Torsor groupoids for a future quotient-stack construction

The action groupoid of points is only the prestack presentation of a quotient.  This file
constructs the expected groupoid over a fixed test scheme: objects are torsors equipped with an
equivariant map, and arrows are equivariant isomorphisms over the base.

No quotient stack is exported here.  The former presentation records, which accepted
stackification, fibre equivalences, algebraicity, and Deligne--Mumford conclusions as fields,
are retained below only inside a block comment.  Constructing pullback of these torsors,
fppf stackification, and the geometric properties of the result remains open.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

/-- A group algebraic space, represented as an internal group in fppf sheaves together with an
algebraic-space structure on its underlying sheaf. -/
structure AlgebraicSpaceGroup where
  space : AlgebraicSpace.{u}
  group : GrpObj space.toSheaf

attribute [instance] AlgebraicSpaceGroup.group

/-- An action of a group algebraic space on an algebraic space.  Mathlib's internal-module
object records the unit and associativity diagrams of the action. -/
structure AlgebraicSpaceAction (G : AlgebraicSpaceGroup.{u}) where
  space : AlgebraicSpace.{u}
  action : ModObj G.space.toSheaf space.toSheaf

attribute [instance] AlgebraicSpaceAction.action

namespace AlgebraicSpaceAction

variable {G : AlgebraicSpaceGroup.{u}}

/-- A morphism of algebraic spaces carrying one `G`-action to another.  The equation is imposed
on the actual fppf sheaves underlying the algebraic spaces. -/
structure Hom (U V : AlgebraicSpaceAction G) where
  hom : U.space ⟶ V.space
  equivariant :
    ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) ≫ hom.hom =
      G.space.toSheaf ◁ hom.hom ≫
        ModObj.smul (M := G.space.toSheaf) (X := V.space.toSheaf)

@[ext]
theorem Hom.ext {U V : AlgebraicSpaceAction G} (f g : Hom U V)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  simp only [Hom.mk.injEq]
  exact h

/-- Equivariant algebraic-space maps form a category. -/
instance : Category (AlgebraicSpaceAction G) where
  Hom := Hom
  id U :=
    { hom := 𝟙 U.space
      equivariant := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      equivariant := by
        change ModObj.smul (M := G.space.toSheaf) (X := _) ≫
              (f.hom.hom ≫ g.hom.hom) =
            G.space.toSheaf ◁ (f.hom.hom ≫ g.hom.hom) ≫
              ModObj.smul (M := G.space.toSheaf) (X := _)
        rw [← Category.assoc, f.equivariant, Category.assoc, g.equivariant]
        simp }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

@[simp]
theorem id_hom (U : AlgebraicSpaceAction G) :
    (𝟙 U : U ⟶ U).hom = 𝟙 U.space :=
  rfl

@[simp]
theorem comp_hom {U V W : AlgebraicSpaceAction G} (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

end AlgebraicSpaceAction

/-- A single fppf-local section of a sheaf over a scheme.  The map furnishing the section is
required to be flat, locally of finite presentation, and surjective. -/
structure FppfLocalSection (P : FppfSheaf.{u}) (T : Scheme.{u})
    (projection : P ⟶ fppfYoneda.obj T) where
  coverScheme : Scheme.{u}
  cover : coverScheme ⟶ T
  flat : _root_.AlgebraicGeometry.Flat cover
  locallyOfFinitePresentation :
    _root_.AlgebraicGeometry.LocallyOfFinitePresentation cover
  surjective : _root_.AlgebraicGeometry.Surjective cover
  localLift : fppfYoneda.obj coverScheme ⟶ P
  localLift_over : localLift ≫ projection = fppfYoneda.map cover

/-- An fppf torsor under an internal group sheaf.  The principal map identifies
`G × P` with `P ×_T P`; its two projection equations force it to be the usual
`(g,p) ↦ (g.p,p)` map. -/
structure FppfTorsor (G : AlgebraicSpaceGroup.{u}) (T : Scheme.{u}) where
  P : FppfSheaf.{u}
  action : ModObj G.space.toSheaf P
  projection : P ⟶ fppfYoneda.obj T
  action_over :
    ModObj.smul (M := G.space.toSheaf) (X := P) ≫ projection =
      snd G.space.toSheaf P ≫ projection
  principalMap : G.space.toSheaf ⊗ P ⟶ pullback projection projection
  principal_fst : principalMap ≫ pullback.fst projection projection =
    ModObj.smul (M := G.space.toSheaf) (X := P)
  principal_snd : principalMap ≫ pullback.snd projection projection =
    snd G.space.toSheaf P
  principal_isIso : IsIso principalMap
  locallyTrivial : FppfLocalSection P T projection

attribute [instance] FppfTorsor.action FppfTorsor.principal_isIso

/-- A `T`-object of the quotient stack `[U/G]`: an fppf `G`-torsor over `T` and an
equivariant map from its total sheaf to `U`. -/
structure ActionTorsor (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (T : Scheme.{u}) : Type (u + 1) extends FppfTorsor G T where
  target : P ⟶ U.space.toSheaf
  target_equivariant :
    ModObj.smul (M := G.space.toSheaf) (X := P) ≫ target =
      G.space.toSheaf ◁ target ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G}
  {T : Scheme.{u}}

/-- An arrow of quotient-stack objects is an equivariant torsor isomorphism over the base which
commutes with the maps to `U`. -/
structure Hom (P Q : ActionTorsor G U T) where
  iso : P.P ≅ Q.P
  over : iso.hom ≫ Q.projection = P.projection
  equivariant :
    ModObj.smul (M := G.space.toSheaf) (X := P.P) ≫ iso.hom =
      G.space.toSheaf ◁ iso.hom ≫
        ModObj.smul (M := G.space.toSheaf) (X := Q.P)
  target : iso.hom ≫ Q.target = P.target

@[ext]
theorem Hom.ext {P Q : ActionTorsor G U T} (f g : Hom P Q)
    (h : f.iso.hom = g.iso.hom) : f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  exact Iso.ext h

/-- Quotient-stack arrows compose as the underlying torsor isomorphisms. -/
instance : Category (ActionTorsor G U T) where
  Hom := Hom
  id P :=
    { iso := Iso.refl _
      over := by simp
      equivariant := by simp
      target := by simp }
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
              simp
      target := by simp [Category.assoc, g.target, f.target] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

/-- Every arrow of torsor objects is invertible, so the quotient fibre is a groupoid. -/
instance : Groupoid (ActionTorsor G U T) where
  inv f :=
    { iso := f.iso.symm
      over := by
        apply (cancel_epi f.iso.hom).1
        simp [f.over]
      equivariant := by
        apply (cancel_mono f.iso.hom).1
        simp only [Category.assoc, f.equivariant]
        simp
      target := by
        apply (cancel_epi f.iso.hom).1
        simp [f.target] }
  inv_comp f := by
    apply Hom.ext
    exact f.iso.inv_hom_id
  comp_inv f := by
    apply Hom.ext
    exact f.iso.hom_inv_id

/-- The underlying isomorphism of sheaves of any quotient-stack arrow. -/
abbrev homIso {P Q : ActionTorsor G U T} (f : P ⟶ Q) : P.P ≅ Q.P := f.iso

variable {V : AlgebraicSpaceAction G}

/-- Postcomposing the target map of an action torsor with an equivariant morphism gives an
object of the target quotient groupoid.  The torsor itself is unchanged. -/
def mapTarget (q : U ⟶ V) (P : ActionTorsor G U T) : ActionTorsor G V T where
  toFppfTorsor := P.toFppfTorsor
  target := P.target ≫ q.hom.hom
  target_equivariant := by
    rw [← Category.assoc, P.target_equivariant, Category.assoc, q.equivariant]
    simp

/-- An equivariant morphism induces the expected functor between quotient torsor groupoids. -/
def mapTargetFunctor (q : U ⟶ V) :
    ActionTorsor G U T ⥤ ActionTorsor G V T where
  obj := mapTarget q
  map {P Q} f :=
    { iso := f.iso
      over := f.over
      equivariant := f.equivariant
      target := by
        change f.iso.hom ≫ (Q.target ≫ q.hom.hom) = P.target ≫ q.hom.hom
        rw [← Category.assoc, f.target] }
  map_id P := by
    apply Hom.ext
    rfl
  map_comp f g := by
    apply Hom.ext
    rfl

@[simp]
theorem mapTarget_P (q : U ⟶ V) (P : ActionTorsor G U T) :
    (mapTarget q P).P = P.P :=
  rfl

@[simp]
theorem mapTarget_projection (q : U ⟶ V) (P : ActionTorsor G U T) :
    (mapTarget q P).projection = P.projection :=
  rfl

@[simp]
theorem mapTarget_target (q : U ⟶ V) (P : ActionTorsor G U T) :
    (mapTarget q P).target = P.target ≫ q.hom.hom :=
  rfl

@[simp]
theorem mapTargetFunctor_map_iso_hom (q : U ⟶ V) {P Q : ActionTorsor G U T}
    (f : P ⟶ Q) : ((mapTargetFunctor q).map f).iso.hom = f.iso.hom :=
  rfl

/-- Component of the unital comparison for the quotient functor on equivariant maps.  It is the
identity torsor isomorphism; only the target equation uses the categorical right unit law. -/
noncomputable def mapTargetIdIsoApp (P : ActionTorsor G U T) :
    mapTarget (𝟙 U) P ≅ P :=
  asIso
    { iso := Iso.refl _
      over := by simp
      equivariant := by rfl
      target := by
        dsimp [mapTarget]
        simp }

/-- Quotienting the identity equivariant map is naturally isomorphic to the identity functor. -/
noncomputable def mapTargetFunctorIdIso :
    mapTargetFunctor (T := T) (𝟙 U) ≅ 𝟭 (ActionTorsor G U T) :=
  NatIso.ofComponents mapTargetIdIsoApp (fun {P Q} f ↦ by
    apply Hom.ext
    change f.iso.hom = f.iso.hom
    rfl)

/-- Component of the composition comparison for the quotient functor on equivariant maps. -/
noncomputable def mapTargetCompIsoApp (q : U ⟶ V) (r : V ⟶ W)
    (P : ActionTorsor G U T) :
    mapTarget (q ≫ r) P ≅ mapTarget r (mapTarget q P) :=
  asIso
    { iso := Iso.refl _
      over := by simp
      equivariant := by rfl
      target := by
        change (𝟙 P.P) ≫ (P.target ≫ q.hom.hom) ≫ r.hom.hom =
          P.target ≫ (q ≫ r).hom.hom
        simp }

/-- The functor induced on torsor quotients respects composition of equivariant maps up to the
canonical associativity isomorphism. -/
noncomputable def mapTargetFunctorCompIso (q : U ⟶ V) (r : V ⟶ W) :
    mapTargetFunctor (T := T) (q ≫ r) ≅
      mapTargetFunctor (T := T) q ⋙ mapTargetFunctor (T := T) r :=
  NatIso.ofComponents (mapTargetCompIsoApp q r) (fun {P Q} f ↦ by
    apply Hom.ext
    change f.iso.hom = f.iso.hom
    rfl)

end ActionTorsor

/-
Retired provisional quotient-stack presentations.  The former records accepted stackification,
fibre equivalences, algebraicity, and Deligne--Mumford conclusions as fields.  The concrete
action-torsor groupoids above remain active; producing their fppf stackification and proving its
geometry remains open.

/-- A stackification presentation of `[U/G]`.  Its fibres are identified with the actual torsor
groupoids, and reindexing is compared by a specified natural isomorphism. -/
structure QuotientStackPresentation (G : AlgebraicSpaceGroup.{u})
    (U : AlgebraicSpaceAction G) where
  stack : FppfStack.{u}
  pullbackTorsor {S T : Scheme.{u}} (f : S ⟶ T) :
    ActionTorsor G U T ⥤ ActionTorsor G U S
  pullback_id (T : Scheme.{u}) : pullbackTorsor (𝟙 T) ≅ 𝟭 _
  pullback_comp {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    pullbackTorsor (f ≫ g) ≅ pullbackTorsor g ⋙ pullbackTorsor f
  fiberEquivalence (T : Scheme.{u}) :
    StackFiber stack T ≌ ActionTorsor G U T
  fiberEquivalence_naturality {S T : Scheme.{u}} (f : S ⟶ T) :
    stackPullback stack f ⋙ (fiberEquivalence S).functor ≅
      (fiberEquivalence T).functor ⋙ pullbackTorsor f

namespace QuotientStackPresentation

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G}

/-- Every object of a presented quotient stack is, fibrewise, an honest equivariant torsor. -/
def torsorOfObject (Q : QuotientStackPresentation G U) (T : Scheme.{u})
    (x : StackFiber Q.stack T) : ActionTorsor G U T :=
  (Q.fiberEquivalence T).functor.obj x

/-- Pullback of quotient-stack objects agrees, up to the specified isomorphism, with pullback of
their equivariant torsors. -/
def pullbackTorsorIso (Q : QuotientStackPresentation G U)
    {S T : Scheme.{u}} (f : S ⟶ T) (x : StackFiber Q.stack T) :
    Q.torsorOfObject S ((stackPullback Q.stack f).obj x) ≅
      (Q.pullbackTorsor f).obj (Q.torsorOfObject T x) :=
  (Q.fiberEquivalence_naturality f).app x

end QuotientStackPresentation

/-- Geometric hypotheses ensuring that a quotient-stack presentation is algebraic.  The stack
itself remains the torsor stack above; the atlas and diagonal proofs only add its algebraicity. -/
structure AlgebraicQuotientPresentation (G : AlgebraicSpaceGroup.{u})
    (U : AlgebraicSpaceAction G) : Type (u + 2) extends QuotientStackPresentation G U where
  diagonal : HasRepresentableDiagonal stack
  atlas : ∃ A : StackChart stack, A.IsSmoothSurjective

namespace AlgebraicQuotientPresentation

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G}

/-- The torsor quotient of a flat locally finitely presented group action is an algebraic stack
once the representable diagonal and smooth atlas have been established. -/
def algebraicStack (Q : AlgebraicQuotientPresentation G U) : AlgebraicStack.{u} where
  toStack := Q.stack
  diagonal_representable := Q.diagonal
  smoothAtlas := Q.atlas

end AlgebraicQuotientPresentation

/-- Additional finite-etale and proper-action data which make an algebraic quotient
Deligne--Mumford and separated. -/
structure DeligneMumfordQuotientPresentation (G : AlgebraicSpaceGroup.{u})
    (U : AlgebraicSpaceAction G) : Type (u + 2) extends AlgebraicQuotientPresentation G U where
  etaleAtlas : ∃ A : StackChart stack, A.IsEtaleSurjective
  unramifiedDiagonal :
    DiagonalHasProperty stack
      (@GromovWitten.AlgebraicGeometry.Unramified : MorphismProperty Scheme.{u})
  separatedDiagonal :
    DiagonalHasProperty stack
      (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u})

namespace DeligneMumfordQuotientPresentation

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G}

/-- The Deligne--Mumford quotient stack associated to a finite-etale proper action. -/
def deligneMumfordStack (Q : DeligneMumfordQuotientPresentation G U) :
    DeligneMumfordStack.{u} where
  toAlgebraicStack := Q.toAlgebraicQuotientPresentation.algebraicStack
  etaleAtlas := Q.etaleAtlas
  diagonal_unramified := Q.unramifiedDiagonal

/-- Properness of the quotient diagonal, the separatedness criterion for a DM stack. -/
theorem isSeparated (Q : DeligneMumfordQuotientPresentation G U) :
    DiagonalHasProperty Q.stack
      (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) :=
  Q.separatedDiagonal

end DeligneMumfordQuotientPresentation

-/

end GromovWitten.AlgebraicGeometry
