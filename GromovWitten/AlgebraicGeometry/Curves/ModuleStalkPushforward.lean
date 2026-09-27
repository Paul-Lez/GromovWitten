/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleStalk
/-!
# Stalks of module pushforwards

The usual map from a pushforward stalk to the source stalk is semilinear over the
scheme's stalk map. Its naturality supplies a comparison between module-valued stalk
functors with the required restriction of scalars.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (M : X.Modules)
set_option backward.isDefEq.respectTransparency false in
/-- The canonical semilinear map from a pushforward stalk to the source stalk. -/
def moduleStalkPushforward :
    (moduleStalk Y (f x)).obj ((Scheme.Modules.pushforward f).obj M) →ₛₗ[(f.stalkMap x).hom]
      (moduleStalk X x).obj M where
  __ := (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.base M.val.presheaf x).hom
  map_smul' := by
    intro r m
    let N := (Scheme.Modules.pushforward f).obj M
    let g : TopCat.Presheaf.stalk N.val.presheaf (f x) ⟶ TopCat.Presheaf.stalk M.val.presheaf x :=
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.base M.val.presheaf x
    change g (r • m) = f.stalkMap x r • g m
    obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq N.val.presheaf m
    obtain ⟨V, hVU, hy, t, rfl⟩ := Y.presheaf.exists_le_germ_eq r hx
    rw [← TopCat.Presheaf.germ_res_apply N.val.presheaf (homOfLE hVU) (f x) hy s]
    rw [← N.val.germ_smul (R := Y.presheaf) (f x) V hy]
    have hg (a : N.val.obj (op V)) :
        g (TopCat.Presheaf.germ N.val.presheaf V (f x) hy a) =
          TopCat.Presheaf.germ M.val.presheaf ((Opens.map f.base).obj V) x hy a :=
      ConcreteCategory.congr_hom
        (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat.{u} f.base M.val.presheaf V x hy) a
    rw [hg, hg]
    have hs := M.val.germ_smul (R := X.presheaf) x ((Opens.map f.base).obj V) hy
      (f.app V t) (N.val.map (homOfLE hVU).op s)
    rw [f.germ_stalkMap_apply]
    convert hs using 1 <;> rfl

@[simp]
lemma moduleStalkPushforward_germ (U : Y.Opens) (hx : f x ∈ U)
    (m : ((Scheme.Modules.pushforward f).obj M).val.obj (op U)) :
    moduleStalkPushforward f x M
      (TopCat.Presheaf.germ ((Scheme.Modules.pushforward f).obj M).val.presheaf U (f x) hx m) =
        TopCat.Presheaf.germ M.val.presheaf ((Opens.map f.base).obj U) x hx m :=
  ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat.{u} f.base M.val.presheaf U x hx) m

set_option backward.isDefEq.respectTransparency false in
/-- The pushforward-to-stalk comparison, with its scalar restriction explicit. -/
def moduleStalkPushforwardNat :
    Scheme.Modules.pushforward f ⋙ moduleStalk Y (f x) ⟶
      moduleStalk X x ⋙ ModuleCat.restrictScalars (f.stalkMap x).hom where
  app M := ModuleCat.semilinearMapAddEquiv (f.stalkMap x).hom _ _
    (moduleStalkPushforward f x M)
  naturality M N φ := by
    ext s
    obtain ⟨U, hx, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      ((Scheme.Modules.pushforward f).obj M).val.presheaf s
    change moduleStalkPushforward f x N
      ((moduleStalk Y (f x)).map ((Scheme.Modules.pushforward f).map φ)
        (TopCat.Presheaf.germ ((Scheme.Modules.pushforward f).obj M).val.presheaf U (f x) hx t)) =
      (moduleStalk X x).map φ (moduleStalkPushforward f x M
        (TopCat.Presheaf.germ ((Scheme.Modules.pushforward f).obj M).val.presheaf U (f x) hx t))
    rw [moduleStalkPushforward_germ]
    change moduleStalkPushforward f x N
      ((PresheafOfModules.stalkFunctorComm Y.presheaf (f x)).map
        (((Scheme.Modules.pushforward f).map φ).val)
        (TopCat.Presheaf.germ ((Scheme.Modules.pushforward f).obj M).val.presheaf U (f x) hx t)) = _
    rw [PresheafOfModules.stalkFunctorComm_map_germ, moduleStalkPushforward_germ]
    exact (PresheafOfModules.stalkFunctorComm_map_germ X.presheaf x φ.val
      ((Opens.map f.base).obj U) hx t).symm
end GromovWitten.AlgebraicGeometry.Curves
