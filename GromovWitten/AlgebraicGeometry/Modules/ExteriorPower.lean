/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Modules.Stack
import GromovWitten.AlgebraicGeometry.Modules.TensorCoherence
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower

/-!
# Exterior powers of module presheaves

Exterior powers are formed sectionwise.  Their restriction maps are induced by the universal
alternating map, and the resulting presheaf construction is then sheafified for module sheaves.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry.Modules

universe w v u

variable {C : Type u} [Category.{v} C]
  [UnivLE.{max u v, w}]

namespace PresheafExteriorPower

variable {R : Cᵒᵖ ⥤ CommRingCat.{w}}

abbrev PM := PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)

noncomputable def mapLinear {M : PM} {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ℕ) :
    (M.obj X).exteriorPower n →ₗ[(R ⋙ forget₂ CommRingCat RingCat).obj X]
      (ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
      ((M.obj Y).exteriorPower n) := by
  letI : CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj X) :=
    inferInstanceAs (CommRing (R.obj X))
  letI : CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj Y) :=
    inferInstanceAs (CommRing (R.obj Y))
  letI : Algebra ((R ⋙ forget₂ CommRingCat RingCat).obj X)
      ((R ⋙ forget₂ CommRingCat RingCat).obj Y) :=
    ((R ⋙ forget₂ CommRingCat RingCat).map f).hom.toAlgebra
  letI : Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) (M.obj Y) :=
    inferInstanceAs (Module ((R ⋙ forget₂ CommRingCat RingCat).obj X)
      ((ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
        (M.obj Y)))
  letI : IsScalarTower ((R ⋙ forget₂ CommRingCat RingCat).obj X)
      ((R ⋙ forget₂ CommRingCat RingCat).obj Y) (M.obj Y) :=
    IsScalarTower.of_compHom _ _ (M.obj Y)
  letI : Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) ((M.obj Y).exteriorPower n) :=
    inferInstanceAs (Module ((R ⋙ forget₂ CommRingCat RingCat).obj X)
      ((ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
        ((M.obj Y).exteriorPower n)))
  let q := exteriorPower.ιMulti ((R ⋙ forget₂ CommRingCat RingCat).obj Y) n
    (M := M.obj Y)
  let qA : (M.obj Y) [⋀^Fin n]→ₗ[(R ⋙ forget₂ CommRingCat RingCat).obj X]
      (M.obj Y).exteriorPower n := {
    toMultilinearMap := q.toMultilinearMap.restrictScalars
      ((R ⋙ forget₂ CommRingCat RingCat).obj X)
    map_eq_zero_of_eq' := q.map_eq_zero_of_eq' }
  exact exteriorPower.alternatingMapLinearEquiv
    (qA.compLinearMap (M.map f).hom)

omit [UnivLE.{max u v, w}] in
lemma mapLinear_ιMulti {M : PM} {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ℕ)
    (x : Fin n → M.obj X) :
    mapLinear (R := R) f n (exteriorPower.ιMulti (R.obj X) n x) =
      (exteriorPower.ιMulti (R.obj Y) n (fun i => (M.map f (x i) : M.obj Y)) :
        ((ModuleCat.restrictScalars
          ((R ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
          ((M.obj Y).exteriorPower n) : Type _)) := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

end PresheafExteriorPower

namespace PresheafExteriorPower

variable {R : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The exterior power of a presheaf of modules, formed sectionwise. -/
noncomputable def obj (M : PM (R := R)) (n : ℕ) : PM (R := R) where
  obj X := (M.obj X).exteriorPower n
  map {X Y} f := by
    letI : CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj X) :=
      inferInstanceAs (CommRing (R.obj X))
    letI : CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj Y) :=
      inferInstanceAs (CommRing (R.obj Y))
    letI : Algebra ((R ⋙ forget₂ CommRingCat RingCat).obj X)
        ((R ⋙ forget₂ CommRingCat RingCat).obj Y) :=
      ((R ⋙ forget₂ CommRingCat RingCat).map f).hom.toAlgebra
    letI : Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) (M.obj Y) :=
      inferInstanceAs (Module ((R ⋙ forget₂ CommRingCat RingCat).obj X)
        ((ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
          (M.obj Y)))
    letI : IsScalarTower ((R ⋙ forget₂ CommRingCat RingCat).obj X)
        ((R ⋙ forget₂ CommRingCat RingCat).obj Y) (M.obj Y) :=
      IsScalarTower.of_compHom _ _ (M.obj Y)
    letI : Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) ((M.obj Y).exteriorPower n) :=
      inferInstanceAs (Module ((R ⋙ forget₂ CommRingCat RingCat).obj X)
        ((ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
          ((M.obj Y).exteriorPower n)))
    exact ModuleCat.ofHom (mapLinear (R := R) f n)
  map_id X := by
    apply ModuleCat.exteriorPower.hom_ext
    ext x
    change mapLinear (R := R) (𝟙 X) n
        (exteriorPower.ιMulti (R.obj X) n x) =
      (ModuleCat.restrictScalarsId'
        ((R ⋙ forget₂ CommRingCat RingCat).map (𝟙 X)).hom
        (congrArg RingCat.Hom.hom ((R ⋙ forget₂ CommRingCat RingCat).map_id X))).inv.app
          ((M.obj X).exteriorPower n)
        (exteriorPower.ιMulti ((R ⋙ forget₂ CommRingCat RingCat).obj X) n x :
          ((ModuleCat.restrictScalars
            ((R ⋙ forget₂ CommRingCat RingCat).map (𝟙 X)).hom).obj
            ((M.obj X).exteriorPower n) : Type _))
    rw [mapLinear_ιMulti]
    simp only [PresheafOfModules.map_id]
    rfl
  map_comp {X Y Z} f g := by
    apply ModuleCat.exteriorPower.hom_ext
    ext x
    change mapLinear (R := R) (f ≫ g) n
        (exteriorPower.ιMulti (R.obj X) n x) =
      mapLinear (R := R) g n
        (mapLinear (R := R) f n
          (exteriorPower.ιMulti (R.obj X) n x))
    rw [mapLinear_ιMulti (R := R) (M := M) (f ≫ g) n x]
    rw [mapLinear_ιMulti (R := R) (M := M) f n x]
    change
      exteriorPower.ιMulti (R.obj Z) n
          (fun i => M.restrictₛₗ (f ≫ g) (x i)) =
        mapLinear (R := R) g n
          (exteriorPower.ιMulti (R.obj Y) n
            (fun i => M.restrictₛₗ f (x i)))
    rw [mapLinear_ιMulti (R := R) (M := M) g n
      (fun i => M.restrictₛₗ f (x i))]
    apply congrArg (exteriorPower.ιMulti (R.obj Z) n)
    funext i
    simpa only [PresheafOfModules.restrictₛₗ_apply] using
      congrArg (fun z => (z : M.obj Z))
        (PresheafOfModules.map_comp_apply M f g (x i))

end PresheafExteriorPower

namespace PresheafExteriorPower

variable {R : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The map on sectionwise exterior powers induced by a morphism of presheaves. -/
noncomputable def map {M N : PM (R := R)} (f : M ⟶ N) (n : ℕ) :
    obj M n ⟶ obj N n where
  app X := by
    dsimp [obj]
    exact ModuleCat.exteriorPower.map (f.app X) n
  naturality {X Y} g := by
    apply ModuleCat.exteriorPower.hom_ext
    ext x
    change ModuleCat.exteriorPower.map (f.app Y) n
        (mapLinear (R := R) g n
          (exteriorPower.ιMulti (R.obj X) n x)) =
      mapLinear (R := R) (M := N) g n
        (ModuleCat.exteriorPower.map (f.app X) n
          (exteriorPower.ιMulti (R.obj X) n x))
    rw [mapLinear_ιMulti]
    change ModuleCat.exteriorPower.map (f.app Y) n
        (ModuleCat.exteriorPower.mk
          (fun i => M.restrictₛₗ g (x i))) =
      mapLinear (R := R) (M := N) g n
        (ModuleCat.exteriorPower.map (f.app X) n
          (ModuleCat.exteriorPower.mk
            x))
    rw [ModuleCat.exteriorPower.map_mk, ModuleCat.exteriorPower.map_mk]
    change
      exteriorPower.ιMulti (R.obj Y) n
          (fun i => (f.app Y (M.restrictₛₗ g (x i)) : N.obj Y)) =
        mapLinear (R := R) (M := N) g n
          (exteriorPower.ιMulti (R.obj X) n
            (fun i => (f.app X (x i) : N.obj X)))
    rw [mapLinear_ιMulti]
    change
      exteriorPower.ιMulti (R.obj Y) n
          (fun i => (f.app Y (M.restrictₛₗ g (x i)) : N.obj Y)) =
        exteriorPower.ιMulti (R.obj Y) n
          (fun i => N.restrictₛₗ g (f.app X (x i)))
    apply congrArg (exteriorPower.ιMulti (R.obj Y) n)
    funext i
    simpa only [PresheafOfModules.restrictₛₗ_apply] using
      PresheafOfModules.naturality_apply f g (x i)

/-- The sectionwise exterior power construction as a functor on presheaves. -/
noncomputable def functor (n : ℕ) : PM (R := R) ⥤ PM (R := R) where
  obj M := obj M n
  map f := map f n
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro X
    dsimp [map]
    change ModuleCat.exteriorPower.map (𝟙 (M.obj X)) n =
      𝟙 ((M.obj X).exteriorPower n)
    exact (ModuleCat.exteriorPower.functor
      ((R ⋙ forget₂ CommRingCat RingCat).obj X) n).map_id (M.obj X)
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro X
    dsimp [map]
    change ModuleCat.exteriorPower.map (f.app X ≫ g.app X) n =
      ModuleCat.exteriorPower.map (f.app X) n ≫
        ModuleCat.exteriorPower.map (g.app X) n
    exact (ModuleCat.exteriorPower.functor
      ((R ⋙ forget₂ CommRingCat RingCat).obj X) n).map_comp (f.app X) (g.app X)

end PresheafExteriorPower

namespace PresheafExteriorPower

variable {R : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The canonical degree-zero comparison with the presheaf of scalars. -/
noncomputable def iso₀ (M : PM (R := R)) :
    obj M 0 ≅ PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.isoMk
    (fun X ↦ ModuleCat.exteriorPower.iso₀ (M.obj X)) (by
      intro X Y f
      apply ModuleCat.exteriorPower.hom_ext
      ext x
      change (ModuleCat.exteriorPower.iso₀ (M.obj Y)).hom
          (mapLinear (R := R) f 0
            (exteriorPower.ιMulti (R.obj X) 0 x)) =
        (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).map f
          ((ModuleCat.exteriorPower.iso₀ (M.obj X)).hom
            (exteriorPower.ιMulti (R.obj X) 0 x))
      rw [mapLinear_ιMulti]
      change
        (ModuleCat.exteriorPower.iso₀ (M.obj Y)).hom
            (ModuleCat.exteriorPower.mk
              (fun i => M.restrictₛₗ f (x i))) =
          (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).map f
            ((ModuleCat.exteriorPower.iso₀ (M.obj X)).hom
              (ModuleCat.exteriorPower.mk _))
      rw [ModuleCat.exteriorPower.iso₀_hom_apply,
        ModuleCat.exteriorPower.iso₀_hom_apply]
      exact (PresheafOfModules.unit_map_one
        (R := R ⋙ forget₂ CommRingCat RingCat) f).symm)

/-- The canonical degree-one comparison with the original presheaf. -/
noncomputable def iso₁ (M : PM (R := R)) : obj M 1 ≅ M :=
  PresheafOfModules.isoMk
    (fun X ↦ ModuleCat.exteriorPower.iso₁ (M.obj X)) (by
      intro X Y f
      apply ModuleCat.exteriorPower.hom_ext
      ext x
      change (ModuleCat.exteriorPower.iso₁ (M.obj Y)).hom
          (mapLinear (R := R) f 1
            (exteriorPower.ιMulti (R.obj X) 1 x)) =
        M.map f ((ModuleCat.exteriorPower.iso₁ (M.obj X)).hom
          (exteriorPower.ιMulti (R.obj X) 1 x))
      rw [mapLinear_ιMulti]
      change
        (ModuleCat.exteriorPower.iso₁ (M.obj Y)).hom
            (ModuleCat.exteriorPower.mk
              (fun i => M.restrictₛₗ f (x i))) =
          M.map f ((ModuleCat.exteriorPower.iso₁ (M.obj X)).hom
            (ModuleCat.exteriorPower.mk _))
      rw [ModuleCat.exteriorPower.iso₁_hom_apply,
        ModuleCat.exteriorPower.iso₁_hom_apply]
      rfl)

end PresheafExteriorPower

namespace SheafExteriorPower

variable (S : Sites.RingedSite.{w} C)
  [HasWeakSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The exterior power of a module sheaf, obtained by sheafifying its sectionwise construction. -/
noncomputable def functor (n : ℕ) : S.Modules ⥤ S.Modules :=
  (SheafOfModules.forget S.ringStructureSheaf) ⋙
    PresheafExteriorPower.functor (R := S.structureSheaf.obj) n ⋙
    moduleSheafification S

/-- The sheafified degree-zero comparison with the structure sheaf. -/
noncomputable def iso₀ (M : S.Modules) :
    (functor S 0).obj M ≅ SheafOfModules.unit S.ringStructureSheaf := by
  let sh := moduleSheafification S
  let adj := PresheafOfModules.sheafificationAdjunction
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)
  letI : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  change sh.obj ((PresheafExteriorPower.obj (M.val) 0)) ≅ _
  exact sh.mapIso (PresheafExteriorPower.iso₀ M.val) ≪≫
    (asIso adj.counit).app (SheafOfModules.unit S.ringStructureSheaf)

/-- The sheafified degree-one comparison with the original module sheaf. -/
noncomputable def iso₁ (M : S.Modules) : (functor S 1).obj M ≅ M := by
  let sh := moduleSheafification S
  let adj := PresheafOfModules.sheafificationAdjunction
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)
  letI : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  change sh.obj ((PresheafExteriorPower.obj (M.val) 1)) ≅ M
  exact sh.mapIso (PresheafExteriorPower.iso₁ M.val) ≪≫
    (asIso adj.counit).app M

end SheafExteriorPower

end GromovWitten.AlgebraicGeometry.Modules
