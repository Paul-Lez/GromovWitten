/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Groupoid
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# The quotient groupoid of a two-term complex

For a linear map `d : E₀ ⟶ E₁`, the groupoid `[E₁/E₀]` has objects `x : E₁`; an arrow
`x ⟶ y` is an element `a : E₀` such that `x + d(a) = y`.  This is the fibrewise algebraic
model of `h¹/h⁰([E₀ ⟶ E₁])`.  It remembers automorphisms (the kernel of `d`) and is not
the set-valued cokernel.

Scalar contraction acts simultaneously on objects and arrows, which is the action required of a
cone-stack presentation.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R]
  (E₀ E₁ : Type u) [AddCommGroup E₀] [AddCommGroup E₁] [Module R E₀] [Module R E₁]

/-- Objects of the translation quotient `[E₁/E₀]` associated to a differential `d`. -/
structure TwoTermQuotient (d : E₀ →ₗ[R] E₁) where
  /-- The underlying element of `E₁`. -/
  back : E₁

namespace TwoTermQuotient

variable {R E₀ E₁} (d : E₀ →ₗ[R] E₁)

/-- An arrow is a translation in `E₀` whose image under `d` carries source to target. -/
structure Hom (x y : TwoTermQuotient R E₀ E₁ d) where
  val : E₀
  translate : x.back + d val = y.back

@[ext]
theorem Hom.ext {x y : TwoTermQuotient R E₀ E₁ d} {f g : Hom d x y}
    (h : f.val = g.val) : f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  exact h

/-- Composition is addition of translations. -/
instance : Category (TwoTermQuotient R E₀ E₁ d) where
  Hom := Hom d
  id x := ⟨0, by simp⟩
  comp f g := ⟨f.val + g.val, by
    rw [map_add, ← add_assoc, f.translate, g.translate]⟩
  id_comp f := by apply Hom.ext; simp
  comp_id f := by apply Hom.ext; simp
  assoc f g h := by apply Hom.ext; exact add_assoc f.val g.val h.val

/-- Every translation is invertible, by translating by its negative. -/
instance : Groupoid (TwoTermQuotient R E₀ E₁ d) where
  inv f := ⟨-f.val, by
    rw [map_neg, ← f.translate]
    simp⟩
  inv_comp f := by
    apply Hom.ext
    change -f.val + f.val = 0
    exact neg_add_cancel f.val
  comp_inv f := by
    apply Hom.ext
    change f.val + -f.val = 0
    exact add_neg_cancel f.val

/-- The vertex object. -/
abbrev vertex : TwoTermQuotient R E₀ E₁ d := ⟨0⟩

@[simp]
theorem id_val (x : TwoTermQuotient R E₀ E₁ d) :
    (𝟙 x : Hom d x x).val = 0 :=
  rfl

@[simp]
theorem comp_val {x y z : TwoTermQuotient R E₀ E₁ d} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = f.val + g.val :=
  rfl

/-- Scalar contraction on `[E₁/E₀]`, acting on both objects and arrows. -/
def contraction (r : R) :
    TwoTermQuotient R E₀ E₁ d ⥤ TwoTermQuotient R E₀ E₁ d where
  obj x := ⟨r • x.back⟩
  map {x y} f := ⟨r • f.val, by
    change r • x.back + d (r • f.val) = r • y.back
    rw [map_smul, ← smul_add]
    exact congrArg (r • ·) f.translate⟩
  map_id x := by apply Hom.ext; simp
  map_comp f g := by apply Hom.ext; simp

@[simp]
theorem contraction_obj_back (r : R) (x : TwoTermQuotient R E₀ E₁ d) :
    ((contraction d r).obj x).back = r • x.back :=
  rfl

@[simp]
theorem contraction_map_val (r : R) {x y : TwoTermQuotient R E₀ E₁ d} (f : x ⟶ y) :
    ((contraction d r).map f).val = r • f.val :=
  rfl

/-- The unit law for scalar contraction, as a specified natural isomorphism. -/
noncomputable def contractionOneIso : contraction d 1 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun x ↦ asIso ({ val := 0, translate := by simp } : (contraction d 1).obj x ⟶ x))
    (fun {_ _} f ↦ by apply Hom.ext; simp)

/-- The multiplication law for scalar contraction, as a specified natural isomorphism. -/
def contractionMulHom (r s : R) (x : TwoTermQuotient R E₀ E₁ d) :
    (contraction d (r * s)).obj x ⟶ ((contraction d s ⋙ contraction d r).obj x) where
  val := 0
  translate := by
    change (r * s) • x.back + d 0 = r • s • x.back
    simp [smul_smul]

/-- The multiplication law for scalar contraction, as a specified natural isomorphism. -/
noncomputable def contractionMulIso (r s : R) :
    contraction d (r * s) ≅ contraction d s ⋙ contraction d r :=
  NatIso.ofComponents
    (fun x ↦ asIso (contractionMulHom d r s x))
    (fun {_ _} f ↦ by apply Hom.ext; simp [contractionMulHom, smul_smul])

@[simp]
theorem contractionOneIso_hom_app_val (x : TwoTermQuotient R E₀ E₁ d) :
    ((contractionOneIso d).hom.app x).val = 0 := by
  simp [contractionOneIso]

@[simp]
theorem contractionMulIso_hom_app_val (r s : R) (x : TwoTermQuotient R E₀ E₁ d) :
    ((contractionMulIso d r s).hom.app x).val = 0 := by
  simp [contractionMulIso, contractionMulHom]

/-- Automorphisms of the vertex are precisely elements of the kernel of `d`. -/
def vertexAutEquivKernel : (vertex d ⟶ vertex d) ≃ LinearMap.ker d where
  toFun f := ⟨f.val, by simpa using f.translate⟩
  invFun a := ⟨a, by
    rw [zero_add]
    exact LinearMap.mem_ker.mp a.property⟩
  left_inv f := by apply Hom.ext; rfl
  right_inv a := by apply Subtype.ext; rfl

/-- Two objects are connected by an arrow exactly when their difference lies in the range of
the differential. -/
theorem nonempty_hom_iff (x y : TwoTermQuotient R E₀ E₁ d) :
    Nonempty (x ⟶ y) ↔ y.back - x.back ∈ LinearMap.range d := by
  constructor
  · rintro ⟨f⟩
    refine ⟨f.val, ?_⟩
    rw [← f.translate]
    abel
  · rintro ⟨a, ha⟩
    refine ⟨⟨a, ?_⟩⟩
    rw [ha]
    abel

/-- Isomorphism classes of objects are detected by the cokernel of `d`. -/
theorem quotient_mk_eq_iff_nonempty_hom (x y : TwoTermQuotient R E₀ E₁ d) :
    (Submodule.Quotient.mk x.back : E₁ ⧸ (LinearMap.range d : Submodule R E₁)) =
        Submodule.Quotient.mk y.back ↔ Nonempty (x ⟶ y) := by
  rw [Submodule.Quotient.eq, nonempty_hom_iff]
  constructor
  · intro h
    simpa only [neg_sub] using (LinearMap.range d).neg_mem h
  · intro h
    simpa only [neg_sub] using (LinearMap.range d).neg_mem h

/-- Since the quotient is a groupoid, the same cokernel criterion detects isomorphic objects. -/
theorem nonempty_iso_iff (x y : TwoTermQuotient R E₀ E₁ d) :
    Nonempty (x ≅ y) ↔ y.back - x.back ∈ LinearMap.range d := by
  rw [← nonempty_hom_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨e.hom⟩
  · rintro ⟨f⟩
    exact ⟨asIso f⟩

end TwoTermQuotient

end GromovWitten.AlgebraicGeometry
