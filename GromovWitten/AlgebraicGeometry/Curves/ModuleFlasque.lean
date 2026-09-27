/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleGrothendieck
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Flasqueness of injective module sheaves

Injectivity in the category of sheaves of modules implies flasqueness of the
underlying abelian sheaf. The proof uses the sheafified free module on each
representable open. Its map along an open inclusion is monic, and injectivity
extends a map from the smaller free module to the larger one.
-/

open CategoryTheory Limits Opposite
open _root_.AlgebraicGeometry
open scoped AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- The morphism of sheafified free modules induced by an inclusion of opens. -/
noncomputable abbrev moduleFreeYonedaMap {U V : X.Opens} (i : U ⟶ V) :
    moduleFreeYoneda X U ⟶ moduleFreeYoneda X V :=
  (moduleSheafification X).map
    ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i))

instance moduleFreeYoneda_map_mono {U V : X.Opens} (i : U ⟶ V) :
    Mono (moduleFreeYonedaMap (X := X) i) := by
  change Mono ((moduleSheafification X).map
    ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i)))
  have : Mono ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i)) := by
    apply PresheafOfModules.mono_of_injective
    intro W
    change Function.Injective ⇑((ModuleCat.free (X.ringCatSheaf.obj.obj W)).map
      ((yoneda.map i).app W))
    apply Finsupp.mapDomain_injective
    intro a b h
    change a ≫ i = b ≫ i at h
    exact (cancel_mono i).mp h
  exact preserves_mono_of_preservesLimit
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) _

lemma moduleFreeYonedaHomEquiv_naturality {U V : X.Opens} (i : U ⟶ V)
    (M : X.Modules) (a : moduleFreeYoneda X V ⟶ M) :
    moduleFreeYonedaHomEquiv (moduleFreeYonedaMap i ≫ a) =
      M.presheaf.map i.op (moduleFreeYonedaHomEquiv a) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  change PresheafOfModules.freeYonedaEquiv
      (adj.homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i)) ≫ a)) = _
  calc
    _ = PresheafOfModules.freeYonedaEquiv
        (((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i)) ≫
          (adj.homEquiv _ _ a)) :=
      congrArg PresheafOfModules.freeYonedaEquiv
        (adj.homEquiv_naturality_left
          ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i)) a)
    _ = _ := by
      rw [PresheafOfModules.freeYonedaEquiv_comp]
      have hfree :
          PresheafOfModules.freeYonedaEquiv
              ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i)) =
            ModuleCat.freeMk i := by
        change ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i)).app
            (Opposite.op U) (ModuleCat.freeMk (𝟙 U)) = ModuleCat.freeMk i
        change ((ModuleCat.free (X.ringCatSheaf.obj.obj (Opposite.op U))).map
          ((yoneda.map i).app (Opposite.op U))) (ModuleCat.freeMk (𝟙 U)) = _
        rw [ModuleCat.free_map_apply]
        change ModuleCat.freeMk i = ModuleCat.freeMk i
        rfl
      rw [hfree]
      let φ := adj.homEquiv _ _ a
      change (φ.app (Opposite.op U)) (ModuleCat.freeMk i) =
        (((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj M).map i.op)
          ((φ.app (Opposite.op V)) (ModuleCat.freeMk (𝟙 V)))
      have hnat := congrArg
        (fun q => q (ModuleCat.freeMk (𝟙 V)))
        (φ.naturality i.op)
      change (φ.app (Opposite.op U))
          (((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V)).map i.op
            (ModuleCat.freeMk (𝟙 V))) =
        (((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj M).map i.op)
          ((φ.app (Opposite.op V)) (ModuleCat.freeMk (𝟙 V))) at hnat
      have hmap :
          ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V)).map i.op
              (ModuleCat.freeMk (𝟙 V)) = ModuleCat.freeMk i := by
        change (ConcreteCategory.hom
          ((PresheafOfModules.freeObj (R := X.ringCatSheaf.obj) (yoneda.obj V)).map i.op))
            (ModuleCat.freeMk (𝟙 V)) = ModuleCat.freeMk i
        rw [PresheafOfModules.freeObj_map]
        exact ModuleCat.freeDesc_apply _ _
      rw [hmap] at hnat
      exact hnat

instance module_isFlasque_of_injective (M : X.Modules) [Injective M] :
    TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj M) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    let a := (moduleFreeYonedaHomEquiv (X := X) (U := V.unop) (M := M)).symm s
    let b := Injective.factorThru a (moduleFreeYonedaMap i.unop)
    refine ⟨moduleFreeYonedaHomEquiv (X := X) (U := U.unop) (M := M) b, ?_⟩
    dsimp [moduleToSheafAb] at s
    change M.presheaf.map i
      (moduleFreeYonedaHomEquiv (X := X) (U := U.unop) (M := M) b) = s
    have hn := moduleFreeYonedaHomEquiv_naturality (X := X) i.unop M b
    have hnat : M.presheaf.map i
          (moduleFreeYonedaHomEquiv (X := X) (U := U.unop) (M := M) b) =
        moduleFreeYonedaHomEquiv (X := X) (U := V.unop) (M := M)
          (moduleFreeYonedaMap i.unop ≫ b) := by
      simpa only [Quiver.Hom.op_unop] using hn.symm
    rw [hnat]
    have hb : moduleFreeYonedaMap i.unop ≫ b = a :=
      Injective.comp_factorThru a (moduleFreeYonedaMap i.unop)
    rw [hb]
    dsimp [a]
    exact (moduleFreeYonedaHomEquiv (X := X) (U := V.unop) (M := M)).apply_symm_apply s

end
end GromovWitten.AlgebraicGeometry.Curves
