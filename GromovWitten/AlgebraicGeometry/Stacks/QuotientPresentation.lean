/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Groupoid
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Quotient-groupoid presentations

An action quotient is groupoid-valued: its objects are points and an arrow `x ⟶ y` is a group
element carrying `x` to `y`.  This is the local categorical model for quotient stacks `[U/G]`.
The construction retains stabilizers and all arrows rather than passing to the set of orbits.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u v

/-- The object type of the quotient groupoid of a group action. -/
def QuotientGroupoid (G : Type u) [Group G] (X : Type v) [MulAction G X] := X

namespace QuotientGroupoid

variable (G : Type u) [Group G] {X Y Z : Type v}
  [MulAction G X] [MulAction G Y] [MulAction G Z]

instance quotientMulAction : MulAction G (QuotientGroupoid G X) := by
  dsimp only [QuotientGroupoid]
  infer_instance

/-- An arrow in the quotient groupoid is a group element carrying source to target. -/
structure Hom (x y : QuotientGroupoid G X) where
  val : G
  smul_source : val • x = y

@[ext]
theorem Hom.ext {x y : QuotientGroupoid G X} {f g : Hom G x y} (h : f.val = g.val) : f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  exact h

/-- Category structure on an action quotient.  Composition uses multiplication in the order
dictated by a left action. -/
instance : Category (QuotientGroupoid G X) where
  Hom := Hom G
  id x := ⟨1, one_smul G x⟩
  comp f g := ⟨g.val * f.val, by rw [mul_smul, f.smul_source, g.smul_source]⟩
  id_comp f := by
    apply Hom.ext
    change f.val * 1 = f.val
    exact mul_one f.val
  comp_id f := by
    apply Hom.ext
    change 1 * f.val = f.val
    exact one_mul f.val
  assoc f g h := by
    apply Hom.ext
    change h.val * (g.val * f.val) = (h.val * g.val) * f.val
    exact (mul_assoc h.val g.val f.val).symm

/-- Every quotient category of a group action is a groupoid. -/
instance : Groupoid (QuotientGroupoid G X) where
  inv f := ⟨f.val⁻¹, by
    rw [inv_smul_eq_iff]
    exact f.smul_source.symm⟩
  inv_comp f := by
    apply Hom.ext
    change f.val * f.val⁻¹ = 1
    exact mul_inv_cancel f.val
  comp_inv f := by
    apply Hom.ext
    change f.val⁻¹ * f.val = 1
    exact inv_mul_cancel f.val

/-- The underlying point of an object of the quotient groupoid. -/
abbrev back (x : QuotientGroupoid G X) : X := x

@[simp]
theorem id_val (x : QuotientGroupoid G X) : (𝟙 x : Hom G x x).val = 1 :=
  rfl

@[simp]
theorem comp_val {x y z : QuotientGroupoid G X} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = g.val * f.val :=
  rfl

/-- Arrows in the quotient groupoid are exactly witnesses that two points lie in one orbit. -/
theorem nonempty_hom_iff (x y : QuotientGroupoid G X) :
    Nonempty (x ⟶ y) ↔ ∃ g : G, g • back G x = back G y := by
  constructor
  · rintro ⟨f⟩
    exact ⟨f.val, f.smul_source⟩
  · rintro ⟨g, hg⟩
    exact ⟨⟨g, hg⟩⟩

/-- The automorphism group at a quotient point is its stabilizer. -/
def autEquivStabilizer (x : QuotientGroupoid G X) :
    (x ⟶ x) ≃ MulAction.stabilizer G (back G x) where
  toFun f := ⟨f.val, f.smul_source⟩
  invFun g := ⟨g, g.property⟩
  left_inv f := by apply Hom.ext; rfl
  right_inv g := by apply Subtype.ext; rfl

/-- An equivariant map, with its compatibility equation exposed. -/
structure EquivariantMap (X Y : Type v) [MulAction G X] [MulAction G Y] where
  toFun : X → Y
  map_smul : ∀ (g : G) (x : X), toFun (g • x) = g • toFun x

instance : CoeFun (EquivariantMap G X Y) (fun _ ↦ X → Y) :=
  ⟨EquivariantMap.toFun⟩

namespace EquivariantMap

/-- Identity equivariant map. -/
def id : EquivariantMap G X X where
  toFun x := x
  map_smul _ _ := rfl

/-- Composition of equivariant maps. -/
def comp (f : EquivariantMap G X Y) (g : EquivariantMap G Y Z) :
    EquivariantMap G X Z where
  toFun x := g (f x)
  map_smul h x := by rw [f.map_smul, g.map_smul]

/-- An equivariant map induces a functor of quotient groupoids with the same arrow labels. -/
def quotientFunctor (f : EquivariantMap G X Y) :
    QuotientGroupoid G X ⥤ QuotientGroupoid G Y where
  obj x := f (back G x)
  map {x y} a := ⟨a.val, by
    change a.val • f (back G x) = f (back G y)
    rw [← f.map_smul]
    congr 1
    exact a.smul_source⟩
  map_id x := by apply Hom.ext; rfl
  map_comp a b := by apply Hom.ext; rfl

@[simp]
theorem quotientFunctor_obj (f : EquivariantMap G X Y) (x : QuotientGroupoid G X) :
    f.quotientFunctor.obj x = f (back G x) :=
  rfl

@[simp]
theorem quotientFunctor_map_val (f : EquivariantMap G X Y)
    {x y : QuotientGroupoid G X} (a : x ⟶ y) :
    (f.quotientFunctor.map a).val = a.val :=
  rfl

@[simp]
theorem quotientFunctor_id : (id G (X := X)).quotientFunctor =
    𝟭 (QuotientGroupoid G X) :=
  rfl

@[simp]
theorem quotientFunctor_comp (f : EquivariantMap G X Y) (g : EquivariantMap G Y Z) :
    (comp G f g).quotientFunctor = f.quotientFunctor ⋙ g.quotientFunctor :=
  rfl

end EquivariantMap

/-- The one-orbit quotient groupoid, the fibre model of the classifying stack `BG`. -/
abbrev classifyingGroupoid := QuotientGroupoid G (G ⧸ (⊤ : Subgroup G))

instance classifyingSubsingleton : Subsingleton (classifyingGroupoid G) where
  allEq x y := by
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    exact QuotientGroup.eq_iff_div_mem.mpr (Subgroup.mem_top _)

/-- A distinguished object of the one-orbit classifying groupoid. -/
def classifyingPoint : classifyingGroupoid G :=
  (1 : G ⧸ (⊤ : Subgroup G))

/-- Every object of the classifying groupoid is isomorphic to its distinguished point. -/
theorem classifying_connected (x : classifyingGroupoid G) :
    Nonempty (classifyingPoint G ≅ x) := by
  let f : classifyingPoint G ⟶ x := ⟨1, Subsingleton.elim _ _⟩
  exact ⟨asIso f⟩

/-- Automorphisms of the distinguished point of `BG` are precisely the elements of `G`. -/
def classifyingAutEquiv : (classifyingPoint G ⟶ classifyingPoint G) ≃ G where
  toFun f := f.val
  invFun g := ⟨g, Subsingleton.elim _ _⟩
  left_inv f := by apply Hom.ext; rfl
  right_inv _ := rfl

end QuotientGroupoid

end GromovWitten.AlgebraicGeometry
