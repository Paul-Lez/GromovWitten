/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleExact
import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Module-valued stalk functors

The module structure on a stalk is the one defined by Mathlib's filtered-colimit construction.
Morphisms are linear because every scalar and section can be represented on a common
neighborhood. On a scheme, forgetting scalars recovers the usual abelian-sheaf stalk functor,
so the module-valued stalk functor is exact.
-/

open CategoryTheory Limits Opposite TopologicalSpace
noncomputable section
universe u
namespace PresheafOfModules
variable {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u}) (x : X)
/-- The stalk as a module over the stalk of the coefficient ring. -/
def stalkObjComm (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    ModuleCat.{u} (R.stalk x) :=
  ModuleCat.of _ (↑(TopCat.Presheaf.stalk M.presheaf x) : Type u)

set_option backward.isDefEq.respectTransparency false in
/-- The induced linear map between module stalks. -/
def stalkMapComm {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N) :
    stalkObjComm R x M ⟶ stalkObjComm R x N :=
  ModuleCat.ofHom
    { __ := ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f)).hom
      map_smul' := by
        intro r m
        let g : TopCat.Presheaf.stalk M.presheaf x ⟶ TopCat.Presheaf.stalk N.presheaf x :=
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f)
        change g (r • m) = r • g m
        obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
        obtain ⟨V, hVU, hy, t, rfl⟩ := R.exists_le_germ_eq r hx
        rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hVU) x hy s]
        rw [← M.germ_smul x V hy]
        have hg (a : M.obj (op V)) :
            g (TopCat.Presheaf.germ M.presheaf V x hy a) =
              TopCat.Presheaf.germ N.presheaf V x hy (f.app (op V) a) :=
          TopCat.Presheaf.stalkFunctor_map_germ_apply V x hy
            ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f) a
        rw [hg, hg]
        rw [map_smul, N.germ_smul] }

/-- Taking module-valued stalks is functorial. -/
def stalkFunctorComm :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) ⥤ ModuleCat.{u} (R.stalk x) where
  obj := stalkObjComm R x
  map := stalkMapComm R x
  map_id M := by
    ext s
    exact ConcreteCategory.congr_hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_id M.presheaf) s
  map_comp f g := by
    ext s
    exact ConcreteCategory.congr_hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp
        ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f)
        ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map g)) s

@[simp]
lemma stalkFunctorComm_map_germ {M N : PresheafOfModules.{u}
    (R ⋙ forget₂ CommRingCat RingCat)} (φ : M ⟶ N) (U : Opens X) (hx : x ∈ U)
    (m : M.obj (op U)) :
    (stalkFunctorComm R x).map φ (TopCat.Presheaf.germ M.presheaf U x hx m) =
      TopCat.Presheaf.germ N.presheaf U x hx (φ.app (op U) m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map φ) m

set_option backward.isDefEq.respectTransparency false in
/-- Germwise linearity suffices to make an additive stalk map linear. -/
def stalkHomOfGermLinear
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (N : ModuleCat.{u} (R.stalk x))
    (φ : TopCat.Presheaf.stalk M.presheaf x ⟶ AddCommGrpCat.of N)
    (hφ : ∀ (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)),
      φ (TopCat.Presheaf.germ M.presheaf U x hx (r • m)) =
        R.germ U x hx r • φ (TopCat.Presheaf.germ M.presheaf U x hx m)) :
    stalkObjComm R x M ⟶ N :=
  ModuleCat.ofHom
    { __ := φ.hom
      map_smul' := by
        intro r m
        obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
        obtain ⟨V, hVU, hy, t, rfl⟩ := R.exists_le_germ_eq r hx
        rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hVU) x hy s]
        rw [← M.germ_smul x V hy]
        exact hφ V hy t (M.map (homOfLE hVU).op s) }

end PresheafOfModules
namespace GromovWitten.AlgebraicGeometry.Curves
open _root_.AlgebraicGeometry
variable (X : Scheme.{u}) (x : X)
/-- The stalk functor for sheaves of modules on a scheme. -/
def moduleStalk : X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  SheafOfModules.forget X.ringCatSheaf ⋙ PresheafOfModules.stalkFunctorComm X.presheaf x
instance : (moduleStalk X x).Additive where
  map_add {M N} f g := by
    ext s
    exact ConcreteCategory.congr_hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_add
        (f := f.mapPresheaf) (g := g.mapPresheaf)) s
/-- Forgetting scalars recovers the usual abelian-sheaf stalk. -/
def moduleStalkForgetIso : moduleStalk X x ⋙ forget₂ _ AddCommGrpCat.{u} ≅
    moduleToSheafAb X ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x :=
  NatIso.ofComponents (fun _ => Iso.refl _)

instance : PreservesFiniteLimits (moduleStalk X x) := by
  have : PreservesFiniteLimits (moduleStalk X x ⋙ forget₂ _ AddCommGrpCat.{u}) :=
    preservesFiniteLimits_of_natIso (moduleStalkForgetIso X x).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (moduleStalk X x) (forget₂ _ AddCommGrpCat.{u})
instance : PreservesFiniteColimits (moduleStalk X x) := by
  have : PreservesFiniteColimits (moduleStalk X x ⋙ forget₂ _ AddCommGrpCat.{u}) :=
    preservesFiniteColimits_of_natIso (moduleStalkForgetIso X x).symm
  exact preservesFiniteColimits_of_reflects_of_preserves
    (moduleStalk X x) (forget₂ _ AddCommGrpCat.{u})
instance : (moduleStalk X x).PreservesHomology := by infer_instance

/-- Monomorphisms of sheaves of modules are detected on their module stalks. -/
lemma mono_of_moduleStalk_mono {M N : X.Modules} (φ : M ⟶ N)
    (hφ : ∀ x, Mono ((moduleStalk X x).map φ)) : Mono φ := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  change Function.Injective (φ.mapPresheaf.app U)
  apply TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
    (C := AddCommGrpCat.{u}) (X := X.toTopCat)
    (F := (moduleToSheafAb X).obj M) φ.mapPresheaf U.unop
  intro y _
  exact (ModuleCat.mono_iff_injective ((moduleStalk X y).map φ)).mp (hφ y)
end GromovWitten.AlgebraicGeometry.Curves
