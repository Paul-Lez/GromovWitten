/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.QuotientStackClassifying
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Trivialising an equivariant torsor by a section

The quotient atlas is governed by a concrete fact about the torsor fibres.  A section of an
fppf `G`-torsor identifies it with `G × T`; the map is obtained from the action and its inverse
from the inverse of the principal isomorphism.  All maps below are maps of fppf sheaves, so the
construction applies to algebraic spaces without choosing points of their underlying sets.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace QuotientGeometryTrivialization

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

/- These three calculations are the cartesian-monoidal Yoneda calculations used below. -/

@[reassoc]
theorem lift_whiskerLeft {Z X Y Y' : C} (f : Z ⟶ X) (g : Z ⟶ Y) (h : Y ⟶ Y') :
    lift f g ≫ (X ◁ h) = lift f (g ≫ h) := by
  ext <;> simp

theorem lift_mul_smul {M X Z : C} [MonObj M] [ModObj M X]
    (a b : Z ⟶ M) (p : Z ⟶ X) :
    lift (a * b) p ≫ ModObj.smul (M := M) (X := X) =
      lift a (lift b p ≫ ModObj.smul (M := M) (X := X)) ≫
        ModObj.smul (M := M) (X := X) := by
  have h1 : lift (a * b) p = lift (lift a b) p ≫ (MonObj.mul ▷ X) := by
    rw [lift_whiskerRight]
    rfl
  have h2 : ((MonObj.mul : M ⊗ M ⟶ M) ▷ X) ≫ ModObj.smul (M := M) (X := X) =
      (α_ M M X).hom ≫ (M ◁ ModObj.smul (M := M) (X := X)) ≫
        ModObj.smul (M := M) (X := X) := by simp
  rw [h1, Category.assoc, h2, ← Category.assoc]
  rw [show lift (lift a b) p ≫ (α_ M M X).hom = lift a (lift b p) by
    ext <;> simp]
  rw [← Category.assoc, lift_whiskerLeft]

theorem whiskerLeft_eq_lift (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    X ◁ f = lift (fst _ _) (snd _ _ ≫ f) := by
  ext <;> simp

theorem lift_one_smul {M X Z : C} [MonObj M] [ModObj M X]
    (p : Z ⟶ X) :
    lift (1 : Z ⟶ M) p ≫ ModObj.smul (M := M) (X := X) = p := by
  have h1 : lift (1 : Z ⟶ M) p = lift (toUnit Z) p ≫ (MonObj.one ▷ X) := by
    rw [lift_whiskerRight]
    rfl
  have h2 : (MonObj.one ▷ X) ≫ ModObj.smul (M := M) (X := X) = (λ_ X).hom := by simp
  rw [h1, Category.assoc, h2, leftUnitor_hom, lift_snd]

end QuotientGeometryTrivialization

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T : Scheme.{u}}

/-! ### Trivial torsors and their distinguished sections -/

variable (G T) in
/-- The unit section of the trivial torsor `G × T`. -/
noncomputable def trivialSection :
    fppfYoneda.obj T ⟶ G.space.toSheaf ⊗ fppfYoneda.obj T :=
  lift 1 (𝟙 _)

@[reassoc (attr := simp)]
theorem trivialSection_fst : trivialSection G T ≫ fst _ _ = 1 :=
  lift_fst _ _

@[reassoc (attr := simp)]
theorem trivialSection_snd : trivialSection G T ≫ snd _ _ = 𝟙 _ :=
  lift_snd _ _

/-! ### Trivialisation maps from a section -/

section SectionTrivialization

variable (P : ActionTorsor G U T)
variable (s : fppfYoneda.obj T ⟶ P.P)

/-- The map `G × T ⟶ P` attached to a section: `(g,t) ↦ g · s(t)`. -/
noncomputable def sectionMap : G.space.toSheaf ⊗ fppfYoneda.obj T ⟶ P.P :=
  (G.space.toSheaf ◁ s) ≫ ModObj.smul (M := G.space.toSheaf) (X := P.P)

theorem sectionMap_eq_lift :
    sectionMap P s = lift (fst _ _) (snd _ _ ≫ s) ≫
      ModObj.smul (M := G.space.toSheaf) (X := P.P) := by
  rw [sectionMap, QuotientGeometryTrivialization.whiskerLeft_eq_lift]

theorem inv_principalMap_smul :
    inv P.principalMap ≫ ModObj.smul (M := G.space.toSheaf) (X := P.P) =
      Limits.pullback.fst P.projection P.projection := by
  rw [← P.principal_fst, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

theorem inv_principalMap_snd :
    inv P.principalMap ≫ snd _ _ =
      Limits.pullback.snd P.projection P.projection := by
  rw [← P.principal_snd, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

variable (hs : s ≫ P.projection = 𝟙 _)

include hs

@[reassoc (attr := simp)]
theorem sectionMap_projection :
    sectionMap P s ≫ P.projection = snd _ _ := by
  rw [sectionMap, Category.assoc, P.action_over, ← Category.assoc,
    whiskerLeft_snd, Category.assoc, hs, Category.comp_id]

/-- The pair `(p,s(π p))` in `P ×_T P`. -/
noncomputable def sectionPair : P.P ⟶ Limits.pullback P.projection P.projection :=
  Limits.pullback.lift (𝟙 P.P) (P.projection ≫ s) (by
    rw [Category.id_comp, Category.assoc, hs, Category.comp_id])

/-- The inverse map, formed with the inverse principal isomorphism. -/
noncomputable def sectionInv : P.P ⟶ G.space.toSheaf ⊗ fppfYoneda.obj T :=
  lift (sectionPair P s hs ≫ inv P.principalMap ≫ fst _ _) P.projection

theorem sectionInv_sectionMap : sectionInv P s hs ≫ sectionMap P s = 𝟙 P.P := by
  have h1 : lift (sectionPair P s hs ≫ inv P.principalMap ≫ fst _ _) (P.projection ≫ s) =
      sectionPair P s hs ≫ inv P.principalMap := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, Category.assoc]
    · rw [lift_snd, Category.assoc, inv_principalMap_snd, sectionPair,
        Limits.pullback.lift_snd]
  rw [sectionInv, sectionMap, QuotientGeometryTrivialization.lift_whiskerLeft_assoc,
    h1, Category.assoc, inv_principalMap_smul, sectionPair,
    Limits.pullback.lift_fst]

theorem sectionMap_sectionInv : sectionMap P s ≫ sectionInv P s hs = 𝟙 _ := by
  have hm : lift (fst _ _) (snd _ _ ≫ s) ≫ P.principalMap =
      sectionMap P s ≫ sectionPair P s hs := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, P.principal_fst, Category.assoc, sectionPair,
        Limits.pullback.lift_fst, Category.comp_id, sectionMap_eq_lift]
    · rw [Category.assoc, P.principal_snd, lift_snd, Category.assoc, sectionPair,
        Limits.pullback.lift_snd, ← Category.assoc, sectionMap_projection P s hs]
  have hq : sectionMap P s ≫ sectionPair P s hs ≫ inv P.principalMap =
      lift (fst _ _) (snd _ _ ≫ s) := by
    rw [← Category.assoc, ← hm, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, sectionInv, lift_fst, ← Category.assoc, ← Category.assoc,
      Category.assoc (sectionMap P s) (sectionPair P s hs) (inv P.principalMap), hq,
      lift_fst, Category.id_comp]
  · rw [Category.assoc, sectionInv, lift_snd, sectionMap_projection P s hs,
      Category.id_comp]

/-- The sheaf isomorphism `G × T ≅ P` attached to a section. -/
noncomputable def sectionIso : (G.space.toSheaf ⊗ fppfYoneda.obj T) ≅ P.P where
  hom := sectionMap P s
  inv := sectionInv P s hs
  hom_inv_id := sectionMap_sectionInv P s hs
  inv_hom_id := sectionInv_sectionMap P s hs

omit hs in
theorem trivialSmul_comp_sectionMap :
    FppfTorsor.trivialSmul G T ≫ sectionMap P s =
      (G.space.toSheaf ◁ sectionMap P s) ≫
        ModObj.smul (M := G.space.toSheaf) (X := P.P) := by
  rw [FppfTorsor.trivialSmul, sectionMap,
    QuotientGeometryTrivialization.lift_whiskerLeft_assoc,
    QuotientGeometryTrivialization.lift_mul_smul,
    QuotientGeometryTrivialization.whiskerLeft_eq_lift _
      ((G.space.toSheaf ◁ s) ≫ ModObj.smul (M := G.space.toSheaf) (X := P.P)),
    QuotientGeometryTrivialization.whiskerLeft_eq_lift _ s, comp_lift_assoc]
  simp only [Category.assoc]

omit hs in
theorem sectionMap_comp_target :
    sectionMap P s ≫ P.target =
      (G.space.toSheaf ◁ (s ≫ P.target)) ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) := by
  rw [sectionMap, Category.assoc, P.target_equivariant, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp]

/-! ### The trivial object attached to a point of `U` -/

omit hs in
noncomputable def trivialWithPoint (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    ActionTorsor G U T where
  toFppfTorsor := FppfTorsor.trivial G T
  target := (G.space.toSheaf ◁ x) ≫
    ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)
  target_equivariant := by
    change FppfTorsor.trivialSmul G T ≫ ((G.space.toSheaf ◁ x) ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)) =
      (G.space.toSheaf ◁ ((G.space.toSheaf ◁ x) ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf))) ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)
    rw [FppfTorsor.trivialSmul,
      QuotientGeometryTrivialization.lift_whiskerLeft_assoc,
      QuotientGeometryTrivialization.lift_mul_smul,
      QuotientGeometryTrivialization.whiskerLeft_eq_lift _
        ((G.space.toSheaf ◁ x) ≫ ModObj.smul
          (M := G.space.toSheaf) (X := U.space.toSheaf)),
      QuotientGeometryTrivialization.whiskerLeft_eq_lift _ x, comp_lift_assoc]
    simp only [Category.assoc]

omit hs in
@[simp]
theorem trivialWithPoint_target (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    (trivialWithPoint x).target =
      (G.space.toSheaf ◁ x) ≫ ModObj.smul (M := G.space.toSheaf)
        (X := U.space.toSheaf) := rfl

omit hs in
@[simp]
theorem trivialWithPoint_projection (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    (trivialWithPoint x).projection = snd _ _ := rfl

omit hs in
theorem trivialSection_comp_target (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    trivialSection G T ≫ (trivialWithPoint x).target = x := by
  rw [trivialWithPoint_target, QuotientGeometryTrivialization.whiskerLeft_eq_lift,
    ← Category.assoc, comp_lift, trivialSection_fst, trivialSection_snd_assoc,
    QuotientGeometryTrivialization.lift_one_smul]

/-! ### A section gives an isomorphism in the quotient fibre -/

/-- A torsor with a section is isomorphic to the trivial torsor attached to its induced point. -/
noncomputable def isoTrivialOfSection : trivialWithPoint (s ≫ P.target) ≅ P :=
  (Groupoid.isoEquivHom _ _).symm
    { iso := sectionIso P s hs
      over := sectionMap_projection P s hs
      equivariant := trivialSmul_comp_sectionMap P s
      target := sectionMap_comp_target P s }

/-! ### Sections and maps out of a fixed trivial object -/

end SectionTrivialization

section HomSection

variable (P : ActionTorsor G U T)

/-- A global section of a torsor, represented by an actual fppf-sheaf arrow. -/
structure TorsorSection (P : ActionTorsor G U T) where
  hom : fppfYoneda.obj T ⟶ P.P
  over : hom ≫ P.projection = 𝟙 _

theorem TorsorSection.ext {P : ActionTorsor G U T} (s₁ s₂ : TorsorSection P)
    (h : s₁.hom = s₂.hom) : s₁ = s₂ := by
  cases s₁
  cases s₂
  simp only [TorsorSection.mk.injEq]
  exact h

noncomputable def homSheaf (x : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (f : trivialWithPoint x ⟶ P) :
    G.space.toSheaf ⊗ fppfYoneda.obj T ⟶ P.P := by
  simpa only [trivialWithPoint, FppfTorsor.trivial] using f.iso.hom

theorem trivialSection_comp_sectionMap (s : fppfYoneda.obj T ⟶ P.P) :
    trivialSection G T ≫ sectionMap P s = s := by
  rw [sectionMap, QuotientGeometryTrivialization.whiskerLeft_eq_lift,
    ← Category.assoc, comp_lift, trivialSection_fst,
    trivialSection_snd_assoc, QuotientGeometryTrivialization.lift_one_smul]

theorem sectionMap_of_hom (x : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (f : trivialWithPoint x ⟶ P) :
    sectionMap P (trivialSection G T ≫ homSheaf P x f) = homSheaf P x f := by
  have hequiv : (G.space.toSheaf ◁ homSheaf P x f) ≫
      ModObj.smul (M := G.space.toSheaf) (X := P.P) =
      FppfTorsor.trivialSmul G T ≫ homSheaf P x f := by
    change (G.space.toSheaf ◁ f.iso.hom) ≫
        ModObj.smul (M := G.space.toSheaf) (X := P.P) =
      FppfTorsor.trivialSmul G T ≫ f.iso.hom
    exact f.equivariant.symm
  have hunit : lift (fst G.space.toSheaf (fppfYoneda.obj T))
      (snd G.space.toSheaf (fppfYoneda.obj T) ≫ trivialSection G T) ≫
      FppfTorsor.trivialSmul G T = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, FppfTorsor.trivialSmul_fst, MonObj.comp_mul,
        lift_fst, lift_snd_assoc]
      simp [trivialSection_fst, MonObj.comp_one]
    · rw [Category.assoc, FppfTorsor.trivialSmul_snd, lift_snd_assoc,
        Category.assoc]
      simp [trivialSection_snd]
  have hunit' : (G.space.toSheaf ◁ trivialSection G T) ≫
      FppfTorsor.trivialSmul G T = 𝟙 _ := by
    rw [QuotientGeometryTrivialization.whiskerLeft_eq_lift G.space.toSheaf]
    exact hunit
  rw [sectionMap, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    hequiv, ← Category.assoc, hunit', Category.id_comp]

/-- Morphisms from the trivial torsor attached to `x` are exactly sections over `T` whose
    induced map to `U` is `x`. -/
noncomputable def homSectionEquiv (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    (trivialWithPoint x ⟶ P) ≃
      {s : TorsorSection P // s.hom ≫ P.target = x} where
  toFun f :=
    ⟨⟨trivialSection G T ≫ homSheaf P x f, by
      have hover : homSheaf P x f ≫ P.projection =
          (trivialWithPoint x).projection := by
        simpa only [homSheaf, trivialWithPoint, FppfTorsor.trivial,
          FppfTorsor.trivialAction] using f.over
      rw [Category.assoc, hover, trivialWithPoint_projection,
        trivialSection_snd]⟩, by
      have htarget : homSheaf P x f ≫ P.target =
          (trivialWithPoint x).target := by
        simpa only [homSheaf, trivialWithPoint, FppfTorsor.trivial,
          FppfTorsor.trivialAction] using f.target
      rw [Category.assoc, htarget, trivialSection_comp_target]⟩
  invFun s :=
    { iso := by
        simpa only [trivialWithPoint, FppfTorsor.trivial] using
          sectionIso P s.1.hom s.1.over
      over := sectionMap_projection P s.1.hom s.1.over
      equivariant := by
        change FppfTorsor.trivialSmul G T ≫ sectionMap P s.1.hom =
          (G.space.toSheaf ◁ sectionMap P s.1.hom) ≫
            ModObj.smul (M := G.space.toSheaf) (X := P.P)
        exact trivialSmul_comp_sectionMap P s.1.hom
      target := by
        change sectionMap P s.1.hom ≫ P.target =
          (G.space.toSheaf ◁ x) ≫
            ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)
        exact (sectionMap_comp_target P s.1.hom).trans
          (congrArg (fun z => (G.space.toSheaf ◁ z) ≫
            ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)) s.2) }
  left_inv f := by
    apply ActionTorsor.Hom.ext
    change sectionMap P (trivialSection G T ≫ homSheaf P x f) = homSheaf P x f
    exact sectionMap_of_hom P x f
  right_inv s := by
    apply Subtype.ext
    apply TorsorSection.ext
    change trivialSection G T ≫ sectionMap P s.1.hom = s.1.hom
    exact trivialSection_comp_sectionMap P s.1.hom

/-- An equivariant arrow out of a trivial torsor is determined by the image of its identity
section. This allows coherence equations to be checked on sections. -/
theorem hom_ext_of_trivialSection (x : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (f g : trivialWithPoint x ⟶ P)
    (h : trivialSection G T ≫ homSheaf P x f =
      trivialSection G T ≫ homSheaf P x g) : f = g := by
  apply (homSectionEquiv P x).injective
  apply Subtype.ext
  apply TorsorSection.ext
  exact h

end HomSection

end ActionTorsor

end GromovWitten.AlgebraicGeometry
