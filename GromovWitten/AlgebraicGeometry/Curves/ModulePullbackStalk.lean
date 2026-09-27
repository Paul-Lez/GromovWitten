/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleSkyscraperAdjunction
/-!
# Stalks of module pullback

The module skyscraper functor commutes with pushforward after restriction of scalars along the
stalk map. Uniqueness of left adjoints then identifies pullback followed by a stalk with scalar
extension of the stalk downstairs.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
set_option backward.isDefEq.respectTransparency false in
private def skyPushforwardHom (M : ModuleCat.{u} (X.presheaf.stalk x)) :
    (Scheme.Modules.pushforward f).obj ((moduleSkyscraper X x).obj M) ⟶
      (moduleSkyscraper Y (f x)).obj ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj M) :=
  ⟨PresheafOfModules.homMk (𝟙 _) (by
    intro U r m
    by_cases hx : f x ∈ U.unop
    · let e : (skyscraperPresheaf (f x) (AddCommGrpCat.of M)).obj U =
          AddCommGrpCat.of M := if_pos hx
      apply (ConcreteCategory.bijective_of_isIso (eqToHom e)).1
      have hX := PresheafOfModules.skyscraperModuleAt_smul X.presheaf x M
        (op ((Opens.map f.base).obj U.unop)) hx (f.app U.unop r) m
      have hY := PresheafOfModules.skyscraperModuleAt_smul Y.presheaf (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj M) U hx r m
      let _ := PresheafOfModules.skyscraperModuleAt X.presheaf x M
        (op ((Opens.map f.base).obj U.unop))
      let _ := PresheafOfModules.skyscraperModuleAt Y.presheaf (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj M) U
      let smulX : SMul (X.presheaf.obj (op ((Opens.map f.base).obj U.unop)))
          ((PresheafOfModules.skyscraperModuleUnderlying X.presheaf x M).obj
            (op ((Opens.map f.base).obj U.unop))) := inferInstance
      let smulY : SMul (Y.presheaf.obj U)
          ((PresheafOfModules.skyscraperModuleUnderlying Y.presheaf (f x)
            ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj M)).obj U) := inferInstance
      change (eqToHom e) (@SMul.smul _ _ smulX (f.app U.unop r) m) =
        (eqToHom e) (@SMul.smul _ _ smulY r m)
      erw [hX, hY]
      change X.presheaf.germ ((Opens.map f.base).obj U.unop) x hx (f.app U.unop r) •
          (eqToHom e) m =
        f.stalkMap x (Y.presheaf.germ U.unop (f x) hx r) • (eqToHom e) m
      rw [f.germ_stalkMap_apply]
    · have hz : IsZero ((skyscraperPresheaf (f x) (AddCommGrpCat.of M)).obj U) := by
        rw [show (skyscraperPresheaf (f x) (AddCommGrpCat.of M)).obj U =
          ⊤_ AddCommGrpCat.{u} from if_neg hx]
        exact (isZero_zero AddCommGrpCat.{u}).of_iso HasZeroObject.zeroIsoTerminal.symm
      exact @Subsingleton.elim ((skyscraperPresheaf (f x) (AddCommGrpCat.of M)).obj U)
        (AddCommGrpCat.subsingleton_of_isZero hz) _ _)⟩

private instance skyPushforwardHom_isIso (M : ModuleCat.{u} (X.presheaf.stalk x)) :
    IsIso (skyPushforwardHom f x M) := by
  have : IsIso ((moduleToSheafAb Y).map (skyPushforwardHom f x M)) := by
    change IsIso (𝟙 _)
    infer_instance
  exact isIso_of_reflects_iso (skyPushforwardHom f x M) (moduleToSheafAb Y)

/-- Pushing forward a module skyscraper restricts scalars along the stalk map. -/
def moduleSkyscraperPushforwardIso : moduleSkyscraper X x ⋙ Scheme.Modules.pushforward f ≅
    ModuleCat.restrictScalars (f.stalkMap x).hom ⋙ moduleSkyscraper Y (f x) :=
  NatIso.ofComponents (fun M => asIso (skyPushforwardHom f x M)) (by
    intro M N φ
    apply (moduleToSheafAb Y).map_injective
    rfl)

/-- Pullback on module stalks is extension of scalars along the local ring map. -/
def modulePullbackStalkIso : Scheme.Modules.pullback f ⋙ moduleStalk X x ≅
    moduleStalk Y (f x) ⋙ ModuleCat.extendScalars (f.stalkMap x).hom :=
  Adjunction.leftAdjointUniq
    (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (moduleStalkSkyscraperAdjunction X x)).ofNatIsoRight (moduleSkyscraperPushforwardIso f x))
    ((moduleStalkSkyscraperAdjunction Y (f x)).comp
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom))
end GromovWitten.AlgebraicGeometry.Curves
