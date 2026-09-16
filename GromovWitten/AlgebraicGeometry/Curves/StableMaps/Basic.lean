/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Endomorphism

/-!
# Marked maps of schemes

This file packages the diagram underlying a family of marked maps.  It deliberately imposes no
geometric conditions on the source: nodality, properness, and stability belong in later layers.
Keeping the diagram separate makes its category, changes of marking set, and changes of target
available without pretending that the current algebraic-geometry library already has a theory of
prestable curves.
-/

open CategoryTheory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableMaps

universe u v w

/-- A family of `I`-marked maps to `V` over `S`.

The equations say that every marking is a section of the source over `S` and that the map to the
target is a morphism over `S`.  No separation, finiteness, smoothness, or nodality assumptions are
included. -/
structure MarkedMap {V S : Scheme.{u}} (q : V ⟶ S) (I : Type v) where
  source : Scheme.{u}
  toBase : source ⟶ S
  marking : I → (S ⟶ source)
  marking_toBase : ∀ i, marking i ≫ toBase = 𝟙 S
  map : source ⟶ V
  map_toBase : map ≫ q = toBase

namespace MarkedMap

variable {V S : Scheme.{u}} {q : V ⟶ S} {I : Type v}

/-- A morphism of marked maps preserves the structure map, every marking, and the map to the
target. -/
structure Hom (F G : MarkedMap q I) where
  hom : F.source ⟶ G.source
  over_base : hom ≫ G.toBase = F.toBase
  marking_comm : ∀ i, F.marking i ≫ hom = G.marking i
  map_comm : hom ≫ G.map = F.map

@[ext]
lemma Hom.ext {F G : MarkedMap q I} {f g : Hom F G} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Marked maps to a fixed target over a fixed base, with a fixed marking type, form a category. -/
instance : Category (MarkedMap q I) where
  Hom := Hom
  id F :=
    { hom := 𝟙 F.source
      over_base := by simp
      marking_comm := by simp
      map_comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      over_base := by rw [Category.assoc, g.over_base, f.over_base]
      marking_comm := by
        intro i
        rw [← Category.assoc, f.marking_comm, g.marking_comm]
      map_comm := by rw [Category.assoc, g.map_comm, f.map_comm] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

@[simp]
lemma id_hom (F : MarkedMap q I) : Hom.hom (𝟙 F) = 𝟙 F.source := rfl

@[simp]
lemma comp_hom {F G H : MarkedMap q I} (f : F ⟶ G) (g : G ⟶ H) :
    Hom.hom (f ≫ g) = f.hom ≫ g.hom := rfl

/-- Forget everything except the source scheme and the underlying source morphism. -/
@[simps]
def sourceFunctor : MarkedMap q I ⥤ Scheme where
  obj F := F.source
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restrict or repeat markings along an arbitrary map of index types. -/
@[simps]
def restrictMarkings {J : Type w} (F : MarkedMap q I) (ρ : J → I) : MarkedMap q J where
  source := F.source
  toBase := F.toBase
  marking j := F.marking (ρ j)
  marking_toBase j := F.marking_toBase (ρ j)
  map := F.map
  map_toBase := F.map_toBase

/-- Restriction of markings is functorial on morphisms. -/
@[simps]
def restrictMarkingsFunctor {J : Type w} (ρ : J → I) : MarkedMap q I ⥤ MarkedMap q J where
  obj F := F.restrictMarkings ρ
  map f :=
    { hom := f.hom
      over_base := f.over_base
      marking_comm j := f.marking_comm (ρ j)
      map_comm := f.map_comm }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Reindex the markings along an equivalence.  The direction is from the new index type to the
old one, matching precomposition of the marking function. -/
abbrev reindex {J : Type w} (F : MarkedMap q I) (e : J ≃ I) : MarkedMap q J :=
  F.restrictMarkings e

@[simp]
lemma restrictMarkings_id (F : MarkedMap q I) : F.restrictMarkings id = F := rfl

lemma restrictMarkings_comp {J : Type w} {K : Type*} (F : MarkedMap q I)
    (ρ : J → I) (σ : K → J) :
    (F.restrictMarkings ρ).restrictMarkings σ = F.restrictMarkings (ρ ∘ σ) := rfl

/-- Postcompose with a morphism of targets over the same base. -/
@[simps]
def postcompose {W : Scheme.{u}} {q' : W ⟶ S} (F : MarkedMap q I) (f : V ⟶ W)
    (hf : f ≫ q' = q) : MarkedMap q' I where
  source := F.source
  toBase := F.toBase
  marking := F.marking
  marking_toBase := F.marking_toBase
  map := F.map ≫ f
  map_toBase := by rw [Category.assoc, hf, F.map_toBase]

/-- Postcomposition with a fixed target morphism is a functor. -/
@[simps]
def postcomposeFunctor {W : Scheme.{u}} {q' : W ⟶ S} (f : V ⟶ W) (hf : f ≫ q' = q) :
    MarkedMap q I ⥤ MarkedMap q' I where
  obj F := F.postcompose f hf
  map g :=
    { hom := g.hom
      over_base := g.over_base
      marking_comm := g.marking_comm
      map_comm := by
        dsimp only [postcompose]
        rw [← Category.assoc, g.map_comm] }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Postcomposition by a monomorphism of targets loses no morphisms of marked maps. -/
def postcomposeFunctorFullyFaithful {W : Scheme.{u}} {q' : W ⟶ S}
    (f : V ⟶ W) (hf : f ≫ q' = q) [Mono f] :
    (postcomposeFunctor (I := I) f hf).FullyFaithful where
  preimage {F G} g := by
    change Hom (F.postcompose f hf) (G.postcompose f hf) at g
    exact
      { hom := g.hom
        over_base := g.over_base
        marking_comm := g.marking_comm
        map_comm := by
          apply (cancel_mono f).1
          have hg := g.map_comm
          dsimp only [postcompose] at hg
          exact (Category.assoc g.hom G.map f).trans hg }
  map_preimage _ := Hom.ext rfl
  preimage_map _ := Hom.ext rfl

/-- Postcomposition by the identity is canonically the identity on marked maps. -/
def postcomposeIdIso (F : MarkedMap q I) :
    F.postcompose (𝟙 V) (Category.id_comp q) ≅ F where
  hom :=
    { hom := 𝟙 _
      over_base := Category.id_comp _
      marking_comm := fun _ ↦ Category.comp_id _
      map_comm := by simp [postcompose] }
  inv :=
    { hom := 𝟙 _
      over_base := Category.id_comp _
      marking_comm := fun _ ↦ Category.comp_id _
      map_comm := by simp [postcompose] }
  hom_inv_id := by
    apply Hom.ext
    change 𝟙 F.source ≫ 𝟙 F.source = 𝟙 F.source
    simp
  inv_hom_id := by
    apply Hom.ext
    change 𝟙 F.source ≫ 𝟙 F.source = 𝟙 F.source
    simp

/-- Functor-level identity law for target postcomposition. -/
def postcomposeIdNatIso :
    postcomposeFunctor (I := I) (𝟙 V) (Category.id_comp q) ≅ 𝟭 (MarkedMap q I) :=
  NatIso.ofComponents postcomposeIdIso (fun f ↦ by
    apply Hom.ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)

/-- The two orders of a pair of target postcompositions are canonically isomorphic. -/
def postcomposeCompIso {W Z : Scheme.{u}} {q' : W ⟶ S} {q'' : Z ⟶ S}
    (F : MarkedMap q I) (f : V ⟶ W) (g : W ⟶ Z)
    (hf : f ≫ q' = q) (hg : g ≫ q'' = q') :
    (F.postcompose f hf).postcompose g hg ≅
      F.postcompose (f ≫ g) (by rw [Category.assoc, hg, hf]) where
  hom :=
    { hom := 𝟙 _
      over_base := Category.id_comp _
      marking_comm := fun _ ↦ Category.comp_id _
      map_comm := by simp [postcompose, Category.assoc] }
  inv :=
    { hom := 𝟙 _
      over_base := Category.id_comp _
      marking_comm := fun _ ↦ Category.comp_id _
      map_comm := by simp [postcompose, Category.assoc] }
  hom_inv_id := by
    apply Hom.ext
    change 𝟙 F.source ≫ 𝟙 F.source = 𝟙 F.source
    simp
  inv_hom_id := by
    apply Hom.ext
    change 𝟙 F.source ≫ 𝟙 F.source = 𝟙 F.source
    simp

/-- Functor-level composition law for target postcomposition. -/
def postcomposeCompNatIso {W Z : Scheme.{u}} {q' : W ⟶ S} {q'' : Z ⟶ S}
    (f : V ⟶ W) (g : W ⟶ Z) (hf : f ≫ q' = q) (hg : g ≫ q'' = q') :
    postcomposeFunctor (I := I) f hf ⋙ postcomposeFunctor g hg ≅
      postcomposeFunctor (f ≫ g) (by rw [Category.assoc, hg, hf]) :=
  NatIso.ofComponents (fun F ↦ postcomposeCompIso F f g hf hg) (fun h ↦ by
    apply Hom.ext
    change h.hom ≫ 𝟙 _ = 𝟙 _ ≫ h.hom
    simp)

/-- Functor-level composition law for restriction and reindexing of markings. -/
def restrictMarkingsCompNatIso {J : Type w} {K : Type*} (ρ : J → I) (σ : K → J) :
    restrictMarkingsFunctor (q := q) ρ ⋙ restrictMarkingsFunctor σ ≅
      restrictMarkingsFunctor (ρ ∘ σ) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun h ↦ by
    apply Hom.ext
    change h.hom ≫ 𝟙 _ = 𝟙 _ ≫ h.hom
    simp)

@[simp]
lemma restrictMarkings_postcompose {J : Type w} {W : Scheme.{u}} {q' : W ⟶ S}
    (F : MarkedMap q I) (ρ : J → I) (f : V ⟶ W) (hf : f ≫ q' = q) :
    (F.postcompose f hf).restrictMarkings ρ = (F.restrictMarkings ρ).postcompose f hf := rfl

/-- Isomorphisms and automorphisms are the categorical ones for the category above. -/
abbrev Iso (F G : MarkedMap q I) := F ≅ G

abbrev Aut (F : MarkedMap q I) := CategoryTheory.Aut F

end MarkedMap

end GromovWitten.AlgebraicGeometry.Curves.StableMaps
