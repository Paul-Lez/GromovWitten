/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.Geometry
import GromovWitten.AlgebraicGeometry.Stacks.PropertiesDescent

/-!
# The inertia stack

This file constructs the inertia stack `I_X = X ×_{X × X} X` of an fppf stack `X` as the
genuine bicategorical self two-pullback of the diagonal, and proves the automorphism
interpretation of its fibres.

The absolute product `X × X` is built as the genuine two-pullback of the structural morphism
`X ⟶ terminalStack` with itself, where `terminalStack` is the stack of one-point discrete
groupoids constructed here from the terminal sheaf of types.  The diagonal is the
already-constructed `StackTwoPullback.Genuine.relativeDiagonal` of that presentation, and the
inertia stack is the canonical genuine two-pullback of that diagonal with itself, so neither the
product, nor the diagonal, nor the inertia stack is accepted as data.

## Main results

* `terminalStack`, `FppfStack.toTerminal`, `FppfStack.terminalIso2`,
  `FppfStack.terminal_modification_subsingleton`: the terminal fppf stack, together with the
  proof that its hom-categories out of any stack are contractible.
* `stackSelfProduct`, `stackDiagonal`, `inertiaStack`, `inertiaProjection`: the product, the
  diagonal `X ⟶ X × X`, the inertia stack and its projection.
* `inertiaFiberEquivalence`: over every test scheme `T` the fibre of the inertia stack is
  equivalent to the category `AutObj (StackFiber X T)` of objects of `X(T)` equipped with an
  automorphism.  This is derived from the constructed two-pullback, not assumed, and
  `inertiaFiberEquivalence_comp_forget` identifies the inertia projection with the functor
  forgetting the automorphism.
* `inertiaFiberEquivalenceOfStackEquivalence`: inertia is invariant under equivalence of stacks.
* `inertiaFiberEquivalenceOfThin` and `representedStack_inertiaFiberEquivalence`: a stack with
  thin fibres, for instance a scheme, has trivial inertia.
* `inertiaProjection_hasRepresentableProperty`, `inertiaProjection_unramified`: the inertia
  projection is a genuine base change of the diagonal, hence inherits every multiplicative
  representable scheme-morphism property of it.  In particular a Deligne--Mumford (unramified)
  diagonal forces the inertia projection to be unramified.

## Deligne--Mumford diagonal criterion: what is still missing

`DeligneMumfordStack` in `Stacks.Algebraic` stores only an etale surjective atlas; it has no
redundant diagonal field, so nothing has to be eliminated there.  What is not proved here is the
equivalence between the existence of an etale atlas and unramifiedness of the diagonal.  The two
obstructions are internal to this development rather than missing from Mathlib:

* `DiagonalHasProperty` (isomorphism sheaves, `DiagonalPresentation`) and
  `StackHom.HasRepresentableProperty` applied to `stackDiagonal` (base changes of a stack
  morphism, `StackMorphismPresentation`) are two different encodings of the same diagonal, and
  no comparison between them exists yet.  All descent results in `Stacks.PropertiesDescent`,
  including `StackHom.unramified_of_smoothCover`, are stated for the second encoding.
* Deducing an unramified diagonal from an etale atlas needs the base change of `stackDiagonal`
  along `U × U ⟶ X × X`, that is, products of stack morphisms and a pasting calculus for
  genuine two-pullbacks; only self base change (`GenuineBaseChange`) and composition
  (`Stacks.Properties`) are available.  The scheme-level inputs are available:
  `StackChart.unramified_of_isEtaleSurjective` records that an etale atlas is representably
  unramified, and `MorphismProperty.HasOfPostcompProperty @Etale @Etale` in Mathlib supplies the
  cancellation step.

The converse direction (an unramified diagonal produces an etale atlas) is the hard half of the
Deligne--Mumford theorem; it needs the existence of etale slices through a smooth atlas, for
which neither Mathlib nor this development has any input.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

/-! ### The terminal stack -/

/-- The constant one-point presheaf of types on the big fppf site of schemes. -/
def terminalFppfPresheaf : Scheme.{u}ᵒᵖ ⥤ Type u :=
  (Functor.const _).obj PUnit.{u + 1}

/-- The constant one-point presheaf is an fppf sheaf: every compatible family has the unique
amalgamation given by the unique point. -/
theorem terminalFppfPresheaf_isSheaf :
    Presieve.IsSheaf
      (_root_.AlgebraicGeometry.Scheme.fppfTopology : GrothendieckTopology Scheme.{u})
      terminalFppfPresheaf.{u} := by
  intro Z S _ x _
  exact ⟨PUnit.unit, fun _ _ _ ↦ Subsingleton.elim (α := PUnit.{u + 1}) _ _,
    fun _ _ ↦ Subsingleton.elim (α := PUnit.{u + 1}) _ _⟩

/-- The terminal sheaf of types on the big fppf site. -/
def terminalFppfSheaf : FppfSheaf.{u} :=
  ⟨terminalFppfPresheaf, (isSheaf_iff_isSheaf_of_type _ _).2 terminalFppfPresheaf_isSheaf⟩

/-- The terminal fppf stack: the terminal sheaf of types viewed as a stack with one-point
discrete fibres. -/
noncomputable def terminalStack : FppfStack.{u} :=
  FppfStack.ofSheaf terminalFppfSheaf

/-- Every fibre of the terminal stack is the one-point discrete groupoid. -/
theorem terminalStack_fiber (T : Scheme.{u}) :
    StackFiber terminalStack.{u} T = Discrete PUnit.{u + 1} := rfl

/-- Natural transformations into a one-point discrete groupoid are unique. -/
theorem terminal_natTrans_subsingleton {C : Type u} [Category.{u} C]
    (F G : C ⥤ Discrete PUnit.{u + 1}) : Subsingleton (F ⟶ G) :=
  ⟨fun _ _ ↦ by
    apply NatTrans.ext
    funext _
    apply Subsingleton.elim⟩

/-- Arrows between objects of a fibre of the terminal stack are unique. -/
theorem terminalStack_hom_subsingleton {T : Scheme.{u}}
    (a b : StackFiber terminalStack.{u} T) : Subsingleton (a ⟶ b) :=
  Discrete.instSubsingletonDiscreteHom a b

/-- The structural morphism from an arbitrary fppf stack to the terminal stack.  All of its
coherence data is forced, because every fibre of the target is a one-point groupoid. -/
noncomputable def FppfStack.toTerminal (X : FppfStack.{u}) : StackHom X terminalStack where
  app _ := (Functor.star _).toCatHom
  naturality _ := Cat.Hom.isoMk (Functor.punitExt _ _)
  naturality_naturality _ := by
    apply Cat.Hom₂.ext
    exact (terminal_natTrans_subsingleton _ _).elim _ _
  naturality_id _ := by
    apply Cat.Hom₂.ext
    exact (terminal_natTrans_subsingleton _ _).elim _ _
  naturality_comp _ _ := by
    apply Cat.Hom₂.ext
    exact (terminal_natTrans_subsingleton _ _).elim _ _

/-- Modifications between two morphisms into the terminal stack are unique, so the hom-category
from any stack into the terminal stack is contractible. -/
theorem FppfStack.terminal_modification_subsingleton {X : FppfStack.{u}}
    (f g : StackHom X terminalStack) :
    Subsingleton (Pseudofunctor.StrongTrans.Modification f g) :=
  ⟨fun _ _ ↦ by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext _
    apply Cat.Hom₂.ext
    exact (terminal_natTrans_subsingleton _ _).elim _ _⟩

/-- Any two morphisms from a stack to the terminal stack are canonically 2-isomorphic, so the
terminal stack really is terminal in the bicategory of fppf stacks. -/
noncomputable def FppfStack.terminalIso2 {X : FppfStack.{u}}
    (f g : StackHom X terminalStack) : StackIso2 f g where
  hom :=
    { app := fun _ ↦ NatTrans.toCatHom₂ (Functor.punitExt _ _).hom
      naturality := fun _ ↦ by
        apply Cat.Hom₂.ext
        exact (terminal_natTrans_subsingleton _ _).elim _ _ }
  inv :=
    { app := fun _ ↦ NatTrans.toCatHom₂ (Functor.punitExt _ _).hom
      naturality := fun _ ↦ by
        apply Cat.Hom₂.ext
        exact (terminal_natTrans_subsingleton _ _).elim _ _ }
  hom_inv_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext _
    apply Cat.Hom₂.ext
    exact (terminal_natTrans_subsingleton _ _).elim _ _
  inv_hom_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext _
    apply Cat.Hom₂.ext
    exact (terminal_natTrans_subsingleton _ _).elim _ _

/-! ### The absolute product and the diagonal -/

/-- The genuine bicategorical product `X × X`, constructed as the canonical two-pullback of the
structural morphism to the terminal stack with itself. -/
noncomputable def stackSelfProduct (X : FppfStack.{u}) :
    StackTwoPullback.Genuine X.toTerminal X.toTerminal :=
  StackTwoPullback.canonicalGenuine _ _

/-- The diagonal morphism `X ⟶ X × X`, obtained from the proved bicategorical universal
property of the self product. -/
noncomputable def stackDiagonal (X : FppfStack.{u}) :
    StackHom X (stackSelfProduct X).pullback :=
  (stackSelfProduct X).relativeDiagonal

/-- The diagonal sends an object of a fibre to the pair consisting of that object twice,
together with the identity comparison. -/
@[simp]
theorem stackDiagonal_appFunctor_obj (X : FppfStack.{u}) (T : Scheme.{u})
    (x : StackFiber X T) :
    ((stackDiagonal X).appFunctor T).obj x =
      { fst := x, snd := x, iso := Iso.refl _ } := rfl

/-- The first component of the diagonal image of a fibre object is that object. -/
@[simp]
theorem stackDiagonal_obj_fst (X : FppfStack.{u}) (T : Scheme.{u}) (x : StackFiber X T) :
    CategoricalPullback.fst (((stackDiagonal X).appFunctor T).obj x) = x := rfl

/-- The second component of the diagonal image of a fibre object is that object. -/
@[simp]
theorem stackDiagonal_obj_snd (X : FppfStack.{u}) (T : Scheme.{u}) (x : StackFiber X T) :
    CategoricalPullback.snd (((stackDiagonal X).appFunctor T).obj x) = x := rfl

/-- The comparison isomorphism of the diagonal image of a fibre object is the identity. -/
@[simp]
theorem stackDiagonal_obj_iso (X : FppfStack.{u}) (T : Scheme.{u}) (x : StackFiber X T) :
    (((stackDiagonal X).appFunctor T).obj x).iso = Iso.refl _ := rfl

/-- The first component of the diagonal image of a fibre arrow is that arrow. -/
@[simp]
theorem stackDiagonal_map_fst (X : FppfStack.{u}) (T : Scheme.{u})
    {x y : StackFiber X T} (h : x ⟶ y) :
    (((stackDiagonal X).appFunctor T).map h).fst = h := rfl

/-- The second component of the diagonal image of a fibre arrow is that arrow. -/
@[simp]
theorem stackDiagonal_map_snd (X : FppfStack.{u}) (T : Scheme.{u})
    {x y : StackFiber X T} (h : x ⟶ y) :
    (((stackDiagonal X).appFunctor T).map h).snd = h := rfl

/-! ### The inertia stack -/

/-- The inertia stack presentation: the canonical genuine self two-pullback of the diagonal. -/
noncomputable def inertiaPresentation (X : FppfStack.{u}) :
    StackTwoPullback.Genuine (stackDiagonal X) (stackDiagonal X) :=
  StackTwoPullback.canonicalGenuine _ _

/-- The inertia stack `I_X = X ×_{X × X} X` of an fppf stack. -/
noncomputable def inertiaStack (X : FppfStack.{u}) : FppfStack.{u} :=
  (inertiaPresentation X).pullback

/-- The projection from the inertia stack to the underlying stack. -/
noncomputable def inertiaProjection (X : FppfStack.{u}) :
    StackHom (inertiaStack X) X :=
  (inertiaPresentation X).fst

/-- The inertia projection acts on every fibre as the first categorical-pullback projection. -/
theorem inertiaProjection_appFunctor (X : FppfStack.{u}) (T : Scheme.{u}) :
    (inertiaProjection X).appFunctor T =
      CategoricalPullback.π₁ ((stackDiagonal X).appFunctor T)
        ((stackDiagonal X).appFunctor T) := rfl


/-! ### Objects equipped with an automorphism -/

/-- An object of a category together with a distinguished endomorphism.  Applied to the fibre
`X(T)` of a stack in groupoids, this is the expected description of a point of the inertia
stack: an object of `X(T)` together with an automorphism of it. -/
structure AutObj (C : Type*) [Category* C] where
  /-- The underlying object. -/
  obj : C
  /-- Its distinguished endomorphism. -/
  aut : obj ⟶ obj

namespace AutObj

variable {C : Type*} [Category* C]

/-- A morphism of objects-with-endomorphism is an arrow commuting with the two distinguished
endomorphisms. -/
@[ext]
structure Hom (p q : AutObj C) where
  /-- The underlying arrow. -/
  hom : p.obj ⟶ q.obj
  /-- Compatibility with the distinguished endomorphisms. -/
  w : p.aut ≫ hom = hom ≫ q.aut

/-- Objects with a distinguished endomorphism form a category. -/
instance : Category (AutObj C) where
  Hom := Hom
  id p := ⟨𝟙 p.obj, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by rw [← Category.assoc, f.w, Category.assoc, g.w,
    Category.assoc]⟩

/-- The underlying arrow of an identity morphism. -/
@[simp]
theorem id_hom (p : AutObj C) : Hom.hom (𝟙 p) = 𝟙 p.obj := rfl

/-- The underlying arrow of a composite morphism. -/
@[simp]
theorem comp_hom {p q r : AutObj C} (f : p ⟶ q) (g : q ⟶ r) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- Morphisms of objects-with-automorphism are determined by their underlying arrows. -/
@[ext]
theorem hom_ext {p q : AutObj C} {f g : p ⟶ q} (h : Hom.hom f = Hom.hom g) : f = g :=
  Hom.ext h

/-- Constructor for isomorphisms of objects-with-automorphism. -/
def mkIso {p q : AutObj C} (e : p.obj ≅ q.obj)
    (w : p.aut ≫ e.hom = e.hom ≫ q.aut) : p ≅ q where
  hom := ⟨e.hom, w⟩
  inv := ⟨e.inv, by
    rw [Iso.comp_inv_eq, Category.assoc, w, ← Category.assoc, e.inv_hom_id,
      Category.id_comp]⟩
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

/-- In a groupoid the distinguished endomorphism is an automorphism. -/
noncomputable def autIso [IsGroupoid C] (p : AutObj C) : p.obj ≅ p.obj :=
  asIso p.aut

/-- The underlying arrow of `AutObj.autIso`. -/
@[simp]
theorem autIso_hom [IsGroupoid C] (p : AutObj C) : (autIso p).hom = p.aut := rfl

/-- The forgetful functor discarding the distinguished endomorphism. -/
def forget (C : Type*) [Category* C] : AutObj C ⥤ C where
  obj p := p.obj
  map f := f.hom

end AutObj

/-! ### The automorphism interpretation of the inertia fibres -/

/-- The fibre of the inertia stack over a test scheme, as a genuine categorical pullback of the
diagonal with itself. -/
abbrev InertiaFiber (X : FppfStack.{u}) (T : Scheme.{u}) : Type u :=
  CategoricalPullback ((stackDiagonal X).appFunctor T) ((stackDiagonal X).appFunctor T)

/-- The fibre of the inertia stack really is the categorical pullback of the diagonal with
itself; no comparison is inserted. -/
theorem inertiaStack_fiber_eq (X : FppfStack.{u}) (T : Scheme.{u}) :
    StackFiber (inertiaStack X) T = InertiaFiber X T := rfl

namespace InertiaFiber

variable {X : FppfStack.{u}} {T : Scheme.{u}}

/-- The first leg of a point of the inertia fibre, viewed as an isomorphism of the two
underlying objects. -/
noncomputable def firstLeg (p : InertiaFiber X T) :
    CategoricalPullback.fst p ≅ CategoricalPullback.snd p where
  hom := p.iso.hom.fst
  inv := p.iso.inv.fst
  hom_inv_id := congrArg CategoricalPullback.Hom.fst p.iso.hom_inv_id
  inv_hom_id := congrArg CategoricalPullback.Hom.fst p.iso.inv_hom_id

/-- The second leg of a point of the inertia fibre, viewed as an isomorphism of the two
underlying objects. -/
noncomputable def secondLeg (p : InertiaFiber X T) :
    CategoricalPullback.fst p ≅ CategoricalPullback.snd p where
  hom := p.iso.hom.snd
  inv := p.iso.inv.snd
  hom_inv_id := congrArg CategoricalPullback.Hom.snd p.iso.hom_inv_id
  inv_hom_id := congrArg CategoricalPullback.Hom.snd p.iso.inv_hom_id

/-- The automorphism attached to a point of the inertia fibre: the first leg followed by the
inverse of the second leg. -/
noncomputable def aut (p : InertiaFiber X T) :
    CategoricalPullback.fst p ⟶ CategoricalPullback.fst p :=
  (firstLeg p).hom ≫ (secondLeg p).inv

/-- Unfolding of the automorphism attached to a point of the inertia fibre. -/
theorem aut_eq (p : InertiaFiber X T) :
    aut p = (firstLeg p).hom ≫ (secondLeg p).inv := rfl

/-- The first leg is natural in the point of the inertia fibre. -/
theorem firstLeg_naturality {p q : InertiaFiber X T} (u : p ⟶ q) :
    u.fst ≫ (firstLeg q).hom = (firstLeg p).hom ≫ u.snd :=
  congrArg CategoricalPullback.Hom.fst u.w

/-- The second leg is natural in the point of the inertia fibre. -/
theorem secondLeg_naturality {p q : InertiaFiber X T} (u : p ⟶ q) :
    u.fst ≫ (secondLeg q).hom = (secondLeg p).hom ≫ u.snd :=
  congrArg CategoricalPullback.Hom.snd u.w

/-- Naturality of the inverse of the second leg. -/
theorem secondLeg_inv_naturality {p q : InertiaFiber X T} (u : p ⟶ q) :
    (secondLeg p).inv ≫ u.fst = u.snd ≫ (secondLeg q).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← secondLeg_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The attached automorphism is natural in the point of the inertia fibre. -/
theorem aut_naturality {p q : InertiaFiber X T} (u : p ⟶ q) :
    aut p ≫ u.fst = u.fst ≫ aut q := by
  rw [aut_eq, aut_eq, Category.assoc, secondLeg_inv_naturality, ← Category.assoc,
    ← firstLeg_naturality, Category.assoc]

end InertiaFiber

variable (X : FppfStack.{u}) (T : Scheme.{u})

/-- A point of the inertia fibre determines an object of `X(T)` with an automorphism. -/
noncomputable def inertiaToAutObj : InertiaFiber X T ⥤ AutObj (StackFiber X T) where
  obj p := ⟨CategoricalPullback.fst p, InertiaFiber.aut p⟩
  map {_ _} u := ⟨u.fst, InertiaFiber.aut_naturality u⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An object of `X(T)` with an automorphism determines a point of the inertia fibre, with the
automorphism as first leg and the identity as second leg. -/
noncomputable def autObjToInertia : AutObj (StackFiber X T) ⥤ InertiaFiber X T where
  obj a :=
    { fst := a.obj
      snd := a.obj
      iso := CategoricalPullback.mkIso a.autIso (Iso.refl a.obj)
        ((terminalStack_hom_subsingleton _ _).elim _ _) }
  map {p q} h :=
    { fst := h.hom
      snd := h.hom
      w := by
        apply CategoricalPullback.hom_ext
        · exact h.w.symm
        · exact (Category.comp_id _).trans (Category.id_comp _).symm }
  map_id _ := rfl
  map_comp _ _ := rfl


/-- Going from an object-with-automorphism to the inertia fibre and back recovers the original
object-with-automorphism. -/
noncomputable def autObjToInertiaCounitIso :
    autObjToInertia X T ⋙ inertiaToAutObj X T ≅ 𝟭 (AutObj (StackFiber X T)) :=
  NatIso.ofComponents
    (fun a ↦ AutObj.mkIso (Iso.refl a.obj)
      (((Category.comp_id _).trans (Category.comp_id _)).trans (Category.id_comp _).symm))
    (fun _ ↦ by
      apply AutObj.hom_ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Going from the inertia fibre to an object-with-automorphism and back recovers the original
point of the inertia fibre, up to a canonical isomorphism built from its second leg. -/
noncomputable def inertiaToAutObjUnitIso :
    𝟭 (InertiaFiber X T) ≅ inertiaToAutObj X T ⋙ autObjToInertia X T :=
  NatIso.ofComponents
    (fun p ↦ CategoricalPullback.mkIso (Iso.refl (CategoricalPullback.fst p))
      (InertiaFiber.secondLeg p).symm
      (by
        apply CategoricalPullback.hom_ext
        · exact Category.id_comp _
        · exact (Category.id_comp _).trans (InertiaFiber.secondLeg p).hom_inv_id.symm))
    (fun u ↦ by
      apply CategoricalPullback.hom_ext
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      · exact (InertiaFiber.secondLeg_inv_naturality u).symm)

/-- **Automorphism interpretation of the inertia stack.**  Over every test scheme the fibre of
the inertia stack is equivalent to the category of objects of `X(T)` equipped with an
automorphism.  The equivalence is constructed from the bicategorical two-pullback, not
assumed. -/
noncomputable def inertiaFiberEquivalence : InertiaFiber X T ≌ AutObj (StackFiber X T) :=
  CategoryTheory.Equivalence.mk (inertiaToAutObj X T) (autObjToInertia X T)
    (inertiaToAutObjUnitIso X T) (autObjToInertiaCounitIso X T)

/-- The automorphism interpretation is compatible with the inertia projection: the underlying
object of the pair attached to a point of the inertia fibre is its image under the
projection. -/
theorem inertiaFiberEquivalence_comp_forget :
    (inertiaFiberEquivalence X T).functor ⋙ AutObj.forget (StackFiber X T) =
      (inertiaProjection X).appFunctor T := rfl


/-! ### Functoriality of objects-with-automorphism -/

section Functoriality

variable {C D : Type*} [Category* C] [Category* D]

namespace AutObj

/-- Transport of objects-with-endomorphism along a functor. -/
def map (F : C ⥤ D) : AutObj C ⥤ AutObj D where
  obj p := ⟨F.obj p.obj, F.map p.aut⟩
  map h := ⟨F.map h.hom, by rw [← F.map_comp, h.w, F.map_comp]⟩
  map_id _ := by
    apply AutObj.hom_ext
    exact F.map_id _
  map_comp _ _ := by
    apply AutObj.hom_ext
    exact F.map_comp _ _

/-- Transport along the identity functor is the identity. -/
theorem map_id' : map (𝟭 C) = 𝟭 (AutObj C) := rfl

/-- Transport along a composite functor is the composite transport. -/
theorem map_comp' {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) :
    map (F ⋙ G) = map F ⋙ map G := rfl

/-- A natural isomorphism of functors induces a natural isomorphism of the transports. -/
def mapNatIso {F G : C ⥤ D} (α : F ≅ G) : map F ≅ map G :=
  NatIso.ofComponents
    (fun p ↦ AutObj.mkIso (α.app p.obj) (α.hom.naturality p.aut))
    (fun h ↦ by
      apply AutObj.hom_ext
      exact α.hom.naturality h.hom)

/-- An equivalence of categories induces an equivalence of the categories of objects with a
distinguished endomorphism. -/
noncomputable def mapEquivalence (E : C ≌ D) : AutObj C ≌ AutObj D :=
  CategoryTheory.Equivalence.mk (map E.functor) (map E.inverse)
    (mapNatIso E.unitIso) (mapNatIso E.counitIso)

end AutObj

/-- A stack equivalence induces an equivalence of every scheme fibre. -/
noncomputable def StackEquivalenceData.fiberEquivalence {A B : FppfStack.{u}}
    (e : StackEquivalenceData A B) (S : Scheme.{u}) : StackFiber A S ≌ StackFiber B S :=
  CategoryTheory.Equivalence.mk (e.hom.appFunctor S) (e.inv.appFunctor S)
    (e.homInv.appIso S).symm (e.invHom.appIso S)

/-- **Invariance of inertia under equivalence of stacks.**  Equivalent stacks have equivalent
inertia fibres over every test scheme. -/
noncomputable def inertiaFiberEquivalenceOfStackEquivalence {A B : FppfStack.{u}}
    (e : StackEquivalenceData A B) (S : Scheme.{u}) :
    InertiaFiber A S ≌ InertiaFiber B S :=
  (inertiaFiberEquivalence A S).trans
    ((AutObj.mapEquivalence (e.fiberEquivalence S)).trans
      (inertiaFiberEquivalence B S).symm)

/-- The automorphism description of the inertia fibre, transported along any identification of
the stack fibre with another category.  This is the general form in which the description
applies to a presented quotient stack, whose fibres are identified with a groupoid of torsors;
the quotient stack itself is not yet constructed in `Stacks.QuotientStack`. -/
noncomputable def inertiaFiberEquivalenceOfFiberEquivalence {A : FppfStack.{u}}
    {S : Scheme.{u}} {C : Type*} [Category* C] (E : StackFiber A S ≌ C) :
    InertiaFiber A S ≌ AutObj C :=
  (inertiaFiberEquivalence A S).trans (AutObj.mapEquivalence E)

end Functoriality

/-! ### Stacks with thin fibres, in particular schemes -/

section Thin

variable {A : FppfStack.{u}} {S : Scheme.{u}}

/-- If a stack fibre has at most one arrow between any two objects, then forgetting the
automorphism is an equivalence of categories. -/
noncomputable def AutObj.forgetEquivalence {C : Type*} [Category* C]
    (h : ∀ x y : C, Subsingleton (x ⟶ y)) :
    AutObj C ≌ C :=
  CategoryTheory.Equivalence.mk (AutObj.forget C)
    { obj := fun x ↦ ⟨x, 𝟙 x⟩
      map := fun f ↦ ⟨f, (h _ _).elim _ _⟩
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
    (NatIso.ofComponents (fun p ↦ AutObj.mkIso (Iso.refl p.obj) ((h _ _).elim _ _))
      (fun _ ↦ by
        apply AutObj.hom_ext
        exact (h _ _).elim _ _))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm))

/-- **Inertia of a stack with thin fibres is trivial.**  If every fibre arrow is unique, the
inertia fibre is equivalent to the fibre itself. -/
noncomputable def inertiaFiberEquivalenceOfThin
    (h : ∀ x y : StackFiber A S, Subsingleton (x ⟶ y)) :
    InertiaFiber A S ≌ StackFiber A S :=
  (inertiaFiberEquivalence A S).trans (AutObj.forgetEquivalence h)

end Thin

/-- Arrows between objects of a fibre of a represented stack are unique. -/
theorem representedStack_hom_subsingleton (S T : Scheme.{u})
    (x y : StackFiber (representedStack S) T) : Subsingleton (x ⟶ y) :=
  Discrete.instSubsingletonDiscreteHom x y

/-- **Inertia of a scheme is the scheme itself.**  Over every test scheme the inertia fibre of a
represented stack is equivalent to its fibre. -/
noncomputable def representedStack_inertiaFiberEquivalence (S T : Scheme.{u}) :
    InertiaFiber (representedStack S) T ≌ StackFiber (representedStack S) T :=
  inertiaFiberEquivalenceOfThin (representedStack_hom_subsingleton S T)


/-! ### Representable properties of the diagonal and of inertia -/

/-- Representable properties of a chart are monotone in the scheme-morphism property. -/
theorem StackChart.hasRepresentableProperty_mono {A : FppfStack.{u}} (C : StackChart A)
    {P Q : MorphismProperty Scheme.{u}} (hPQ : P ≤ Q)
    (h : C.HasRepresentableProperty P) : C.HasRepresentableProperty Q :=
  ⟨h.1, fun T x p ↦ hPQ _ (h.2 T x p)⟩

/-- Etale scheme morphisms are unramified. -/
theorem unramified_of_etale {V W : Scheme.{u}} (f : V ⟶ W)
    [_root_.AlgebraicGeometry.Etale f] : Unramified f where

/-- Etale and surjective morphisms are in particular unramified. -/
theorem etaleSurjective_le_unramified :
    ((@_root_.AlgebraicGeometry.Etale ⊓ @_root_.AlgebraicGeometry.Surjective) :
      MorphismProperty Scheme.{u}) ≤ (@Unramified : MorphismProperty Scheme.{u}) :=
  fun _ _ f hf ↦ @unramified_of_etale _ _ f hf.1

/-- An etale surjective atlas is in particular representably unramified.  This is the
scheme-level input to the Deligne--Mumford diagonal criterion. -/
theorem StackChart.unramified_of_isEtaleSurjective {A : FppfStack.{u}} (C : StackChart A)
    (h : C.IsEtaleSurjective) :
    C.HasRepresentableProperty (@Unramified : MorphismProperty Scheme.{u}) :=
  C.hasRepresentableProperty_mono etaleSurjective_le_unramified h

/-- The second projection of the inertia stack is a genuine base change of the diagonal, so it
inherits every multiplicative representable scheme-morphism property of the diagonal. -/
theorem inertiaSnd_hasRepresentableProperty (A : FppfStack.{u})
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    (h : (stackDiagonal A).HasRepresentableProperty P) :
    (inertiaPresentation A).snd.HasRepresentableProperty P :=
  StackHom.twoPullbackSnd_hasRepresentableProperty _ _ (inertiaPresentation A) P h

/-- The inertia projection is a genuine base change of the diagonal, so it inherits every
multiplicative representable scheme-morphism property of the diagonal. -/
theorem inertiaProjection_hasRepresentableProperty (A : FppfStack.{u})
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    (h : (stackDiagonal A).HasRepresentableProperty P) :
    (inertiaProjection A).HasRepresentableProperty P :=
  StackHom.twoPullbackSnd_hasRepresentableProperty _ _
    (StackTwoPullback.swap (inertiaPresentation A)) P h

/-- **An unramified diagonal makes inertia unramified over the stack.**  This is the geometric
content of the Deligne--Mumford condition on automorphism groups. -/
theorem inertiaProjection_unramified (A : FppfStack.{u})
    (h : (stackDiagonal A).Unramified) : (inertiaProjection A).Unramified :=
  inertiaProjection_hasRepresentableProperty A _ h

/-- **An etale diagonal makes inertia etale over the stack.** -/
theorem inertiaProjection_etale (A : FppfStack.{u})
    (h : (stackDiagonal A).Etale) : (inertiaProjection A).Etale :=
  inertiaProjection_hasRepresentableProperty A _ h

/-- The relative Deligne--Mumford condition on the structural morphism to the terminal stack is
exactly unramifiedness of the constructed absolute diagonal. -/
theorem relativeDeligneMumford_toTerminal_iff (A : FppfStack.{u}) :
    Nonempty (RelativeDeligneMumfordMorphism A.toTerminal) ↔
      (stackDiagonal A).Unramified :=
  ⟨fun h ↦ h.some.diagonal_unramified, fun h ↦ ⟨⟨h⟩⟩⟩

/-- The inertia stack of an algebraic stack. -/
noncomputable def AlgebraicStack.inertiaStack (A : AlgebraicStack.{u}) : FppfStack.{u} :=
  _root_.GromovWitten.AlgebraicGeometry.inertiaStack A.toStack

/-- The projection from the inertia stack of an algebraic stack. -/
noncomputable def AlgebraicStack.inertiaProjection (A : AlgebraicStack.{u}) :
    StackHom A.inertiaStack A.toStack :=
  _root_.GromovWitten.AlgebraicGeometry.inertiaProjection A.toStack

/-- The fibre of the inertia stack of an algebraic stack over a test scheme is the category of
objects of the fibre equipped with an automorphism. -/
noncomputable def AlgebraicStack.inertiaFiberEquivalence (A : AlgebraicStack.{u})
    (T : Scheme.{u}) : InertiaFiber A.toStack T ≌ AutObj (StackFiber A.toStack T) :=
  _root_.GromovWitten.AlgebraicGeometry.inertiaFiberEquivalence A.toStack T

/-- The fibre of the inertia stack of a Deligne--Mumford stack over a test scheme is the
category of objects of the fibre equipped with an automorphism. -/
noncomputable def DeligneMumfordStack.inertiaFiberEquivalence (A : DeligneMumfordStack.{u})
    (T : Scheme.{u}) : InertiaFiber A.toStack T ≌ AutObj (StackFiber A.toStack T) :=
  _root_.GromovWitten.AlgebraicGeometry.inertiaFiberEquivalence A.toStack T

/-- The automorphism attached to a point of the inertia fibre of a Deligne--Mumford stack is an
element of the inertia group recorded in `DeligneMumfordStack.inertia`. -/
theorem DeligneMumfordStack.inertia_eq_autObj_aut (A : DeligneMumfordStack.{u})
    (T : Scheme.{u}) (p : AutObj (StackFiber A.toStack T)) :
    A.inertia T p.obj = (p.obj ⟶ p.obj) := rfl

end GromovWitten.AlgebraicGeometry
