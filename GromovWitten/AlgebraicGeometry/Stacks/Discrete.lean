/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.GroupoidValued
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-!
# Sheaves of sets as discrete stacks

This file proves the missing bridge between ordinary sheaves of types and groupoid-valued
stacks.  A presheaf is sent fibrewise to its discrete category.  Its descent category is then
shown equivalent to the discrete category of global sections precisely by using the sheaf
gluing and separatedness axioms.  Thus representable stacks do not need an independently
assumed stack condition.
-/

open CategoryTheory
open CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C]

/-- A presheaf of types regarded fibrewise as a pseudofunctor of discrete categories. -/
def ofPresheafOfTypes (P : Cᵒᵖ ⥤ Type w) :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w, w} :=
  (P ⋙ typeToCat).toPseudofunctor'

/-- Every fibre of the discrete pseudofunctor of a presheaf is a groupoid. -/
noncomputable instance (P : Cᵒᵖ ⥤ Type w) :
    IsGroupoidValued (ofPresheafOfTypes P) where
  fiber X := by
    change IsGroupoid (Discrete (P.obj (Opposite.op X)))
    infer_instance

/-- A sheaf of types satisfies effective descent when regarded as a discrete
groupoid-valued pseudofunctor.

The proof is constructive at the categorical level: full faithfulness is sheaf
separatedness, while essential surjectivity glues the objects of a descent datum. -/
theorem ofPresheafOfTypes_isStack
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type w)
    (hP : Presieve.IsSheaf J P) :
    (ofPresheafOfTypes P).IsStack J := by
  apply IsStack.of_isStackFor
  intro S R hR
  rw [isStackFor_iff]
  let F := ofPresheafOfTypes P
  let f (i : R.arrows.category) := i.obj.hom
  have hSheaf : Presieve.IsSheafFor P R.arrows := hP R hR
  let hff : (F.toDescentData f).FullyFaithful := {
    preimage := fun {M N} φ => Discrete.eqToHom <| hSheaf.isSeparatedFor.ext fun {Y} {g} hg => by
      let i : R.arrows.category := ⟨Over.mk g, hg⟩
      have hi := φ.hom i
      change Discrete.mk (P.map g.op M.as) ⟶ Discrete.mk (P.map g.op N.as) at hi
      exact Discrete.eq_of_hom hi
    map_preimage := fun φ => by
      apply DescentData.hom_ext
      intro i
      change @Eq (ULift (PLift (_ = _))) _ _
      apply Subsingleton.elim
    preimage_map := fun {M N} φ => by
      change @Eq (ULift (PLift (M.as = N.as))) _ _
      apply Subsingleton.elim }
  let hess : (F.toDescentData f).EssSurj := {
    mem_essImage := fun D => by
      let x : Presieve.FamilyOfElements P R.arrows := fun {Y} g hg =>
        (D.obj ⟨Over.mk g, hg⟩).as
      have hx : x.Compatible := by
        intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ h
        let i₁ : R.arrows.category := ⟨Over.mk f₁, h₁⟩
        let i₂ : R.arrows.category := ⟨Over.mk f₂, h₂⟩
        have hi := D.hom (g₁ ≫ f₁) (i₁ := i₁) (i₂ := i₂) g₁ g₂ rfl h.symm
        change Discrete.mk (P.map g₁.op (x f₁ h₁)) ⟶
          Discrete.mk (P.map g₂.op (x f₂ h₂)) at hi
        exact Discrete.eq_of_hom hi
      let t := hSheaf.amalgamate x hx
      let e : (F.toDescentData f).obj (Discrete.mk t) ≅ D :=
        DescentData.isoMk (fun i => Discrete.eqToIso <| by
          let j : R.arrows.category := ⟨Over.mk i.obj.hom, i.property⟩
          have hi := hSheaf.valid_glue hx i.obj.hom i.property
          have hglue : P.map i.obj.hom.op t = (D.obj j).as := by
            dsimp [t, j]
            exact hi
          have hd := D.hom i.obj.hom (i₁ := j) (i₂ := i)
            (𝟙 i.obj.left) (𝟙 i.obj.left) (by simp [f, j]) (by simp [f])
          change Discrete.mk (P.map (𝟙 i.obj.left).op (D.obj j).as) ⟶
            Discrete.mk (P.map (𝟙 i.obj.left).op (D.obj i).as) at hd
          have hdes := Discrete.eq_of_hom hd
          simp only [op_id, Functor.map_id] at hdes
          change P.map i.obj.hom.op t = (D.obj i).as
          exact hglue.trans hdes) (by
            intros
            change @Eq (ULift (PLift (_ = _))) _ _
            apply Subsingleton.elim)
      exact ⟨Discrete.mk t, ⟨e⟩⟩ }
  exact { faithful := hff.faithful, full := hff.full, essSurj := hess }

/-- A natural transformation of presheaves induces a strong transformation between their
discrete pseudofunctors.  The strong naturality cell is the equality supplied by ordinary
naturality, viewed inside the discrete target categories. -/
def strongTransOfNatTrans {P Q : Cᵒᵖ ⥤ Type w} (η : P ⟶ Q) :
    StrongTrans (ofPresheafOfTypes P) (ofPresheafOfTypes Q) where
  app a := typeToCat.map (η.app a.as)
  naturality {a b} f := eqToIso (by
    apply Cat.Hom.ext
    fapply Functor.ext
    · intro X
      apply Discrete.ext
      exact congrArg (fun h => h X.as)
        (congrArg ConcreteCategory.hom (η.naturality f.as))
    · intro X Y g
      change @Eq (ULift (PLift (_ = _))) _ _
      apply Subsingleton.elim)
  naturality_naturality {a b f g} θ := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  naturality_id a := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim

@[simp]
theorem strongTransOfNatTrans_app_obj {P Q : Cᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    (X : C) (x : Discrete (P.obj (Opposite.op X))) :
    ((strongTransOfNatTrans η).app ⟨Opposite.op X⟩).toFunctor.obj x =
      Discrete.mk (η.app (Opposite.op X) x.as) :=
  rfl

/-- Extract the underlying natural transformation of types from a strong transformation
between discrete pseudofunctors. -/
def natTransOfStrongTrans {P Q : Cᵒᵖ ⥤ Type w}
    (η : StrongTrans (ofPresheafOfTypes P) (ofPresheafOfTypes Q)) : P ⟶ Q where
  app X := ↾fun x => (((η.app ⟨X⟩).toFunctor.obj (Discrete.mk x)) : Discrete _).as
  naturality X Y f := by
    ext x
    have h := (Cat.Hom.toNatIso (η.naturality ⟨f⟩)).hom.app (Discrete.mk x)
    exact Discrete.eq_of_hom h

@[simp]
theorem natTransOfStrongTrans_app {P Q : Cᵒᵖ ⥤ Type w}
    (η : StrongTrans (ofPresheafOfTypes P) (ofPresheafOfTypes Q))
    (X : Cᵒᵖ) (x : P.obj X) :
    (natTransOfStrongTrans η).app X x =
      (((η.app ⟨X⟩).toFunctor.obj (Discrete.mk x)) : Discrete _).as :=
  rfl

@[simp]
theorem natTransOfStrongTrans_strongTransOfNatTrans {P Q : Cᵒᵖ ⥤ Type w}
    (η : P ⟶ Q) : natTransOfStrongTrans (strongTransOfNatTrans η) = η := by
  ext X x
  rfl

/-- The canonical modification from the discrete strong transformation reconstructed from
`η` back to `η`.  Its components are identities after unwrapping the discrete categories. -/
def discreteCounitHom
    {P Q : Cᵒᵖ ⥤ Type w}
    (η : StrongTrans (ofPresheafOfTypes P) (ofPresheafOfTypes Q)) :
    StrongTrans.Modification (strongTransOfNatTrans (natTransOfStrongTrans η)) η where
  app a := NatTrans.toCatHom₂ {
    app := fun x => Discrete.eqToHom rfl
    naturality := by intros; apply Subsingleton.elim }
  naturality f := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim

/-- The inverse canonical modification for `discreteCounitHom`. -/
def discreteCounitInv
    {P Q : Cᵒᵖ ⥤ Type w}
    (η : StrongTrans (ofPresheafOfTypes P) (ofPresheafOfTypes Q)) :
    StrongTrans.Modification η (strongTransOfNatTrans (natTransOfStrongTrans η)) where
  app a := NatTrans.toCatHom₂ {
    app := fun x => Discrete.eqToHom rfl
    naturality := by intros; apply Subsingleton.elim }
  naturality f := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim

/-- Invertible modification data between strong transformations. -/
structure StrongTransIso2
    {P Q : Cᵒᵖ ⥤ Type w}
    (η θ : StrongTrans (ofPresheafOfTypes P) (ofPresheafOfTypes Q)) where
  hom : StrongTrans.Modification η θ
  inv : StrongTrans.Modification θ η
  hom_inv_id : StrongTrans.Modification.vcomp hom inv = StrongTrans.Modification.id η
  inv_hom_id : StrongTrans.Modification.vcomp inv hom = StrongTrans.Modification.id θ

/-- Every strong transformation between discrete pseudofunctors is canonically isomorphic to
the one induced by its underlying natural transformation of presheaves. -/
def discreteCounitIso2
    {P Q : Cᵒᵖ ⥤ Type w}
    (η : StrongTrans (ofPresheafOfTypes P) (ofPresheafOfTypes Q)) :
    StrongTransIso2 (strongTransOfNatTrans (natTransOfStrongTrans η)) η where
  hom := discreteCounitHom η
  inv := discreteCounitInv η
  hom_inv_id := by
    apply StrongTrans.Modification.ext
    funext a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  inv_hom_id := by
    apply StrongTrans.Modification.ext
    funext a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim

/-- A modification between strong transformations of discrete pseudofunctors forces equality
of their underlying natural transformations. -/
theorem natTransOfStrongTrans_eq_of_modification
    {P Q : Cᵒᵖ ⥤ Type w}
    {η θ : StrongTrans (ofPresheafOfTypes P) (ofPresheafOfTypes Q)}
    (Γ : StrongTrans.Modification η θ) :
    natTransOfStrongTrans η = natTransOfStrongTrans θ := by
  ext X x
  exact Discrete.eq_of_hom
    ((Γ.app ⟨X⟩).toNatTrans.app (Discrete.mk x))

end CategoryTheory.Pseudofunctor

namespace GromovWitten.AlgebraicGeometry

/-- A sheaf of types, promoted canonically to a stack with discrete groupoid fibres. -/
noncomputable def StackInGroupoids.ofSheafOfTypes
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Sheaf J (Type w)) : StackInGroupoids.{v, w, u, w} C J where
  toPseudofunctor := Pseudofunctor.ofPresheafOfTypes P.obj
  isGroupoidValued := inferInstance
  isStack := Pseudofunctor.ofPresheafOfTypes_isStack J P.obj
    ((isSheaf_iff_isSheaf_of_type J P.obj).1 P.property)

@[simp]
theorem StackInGroupoids.ofSheafOfTypes_fiber
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Sheaf J (Type w)) (X : C) :
    (StackInGroupoids.ofSheafOfTypes J P).toPseudofunctor.obj
      ⟨Opposite.op X⟩ = Cat.of (Discrete (P.obj.obj (Opposite.op X))) :=
  rfl

end GromovWitten.AlgebraicGeometry
