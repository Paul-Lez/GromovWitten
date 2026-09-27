/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleSkyscraper

/-!
# The module stalk–skyscraper adjunction

The additive stalk–skyscraper correspondence respects module structures: sections act through
their germs. This gives the right adjoint to the module-valued stalk functor.
-/

open CategoryTheory Limits Opposite TopologicalSpace
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
namespace PresheafOfModules
variable {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u}) (x : X)
    (M : ModuleCat.{u} (R.stalk x))

set_option backward.isDefEq.respectTransparency false in
private def fromSky (P : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))
    (φ : P ⟶ skyscraperModule R x M) : PresheafOfModules.stalkObjComm R x P ⟶ M :=
  PresheafOfModules.stalkHomOfGermLinear R x P M
    (StalkSkyscraperPresheafAdjunctionAuxs.fromStalk x
      ((PresheafOfModules.toPresheaf _).map φ)) (by
    intro U hx r m
    have hg (m : P.obj (op U)) := ConcreteCategory.congr_hom
      (StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk x
        ((PresheafOfModules.toPresheaf _).map φ) U hx) m
    simp only [ConcreteCategory.comp_apply] at hg
    change _ = R.germ U x hx r • _
    erw [hg, hg]
    change (eqToHom (show (skyscraperModuleUnderlying R x M).obj (op U) = AddCommGrpCat.of M
        from if_pos hx))
      (φ.app (op U) (r • m)) = _
    rw [map_smul]
    exact skyscraperModuleAt_smul R x M (op U) hx r (φ.app (op U) m))

set_option backward.isDefEq.respectTransparency false in
private def toSky (P : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))
    (φ : PresheafOfModules.stalkObjComm R x P ⟶ M) : P ⟶ skyscraperModule R x M :=
  PresheafOfModules.homMk
    (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x
      ((forget₂ _ AddCommGrpCat).map φ)) (by
    intro U r m
    by_cases hx : x ∈ U.unop
    · let e : (skyscraperModuleUnderlying R x M).obj U = AddCommGrpCat.of M := if_pos hx
      apply (ConcreteCategory.bijective_of_isIso (eqToHom e)).1
      erw [skyscraperModuleAt_smul R x M U hx]
      simp only [StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app, dif_pos hx]
      change ((TopCat.Presheaf.germ P.presheaf U.unop x hx ≫
        (forget₂ _ AddCommGrpCat).map φ ≫ eqToHom e.symm) ≫ eqToHom e) (r • m) =
        R.germ U.unop x hx r •
          ((TopCat.Presheaf.germ P.presheaf U.unop x hx ≫
            (forget₂ _ AddCommGrpCat).map φ ≫ eqToHom e.symm) ≫ eqToHom e) m
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      change φ (TopCat.Presheaf.germ P.presheaf U.unop x hx (r • m)) =
        R.germ U.unop x hx r • φ (TopCat.Presheaf.germ P.presheaf U.unop x hx m)
      rw [P.germ_smul x U.unop hx, map_smul]
    · have hz : IsZero ((skyscraperModuleUnderlying R x M).obj U) := by
        rw [show (skyscraperModuleUnderlying R x M).obj U = ⊤_ AddCommGrpCat.{u} from if_neg hx]
        exact (isZero_zero AddCommGrpCat.{u}).of_iso HasZeroObject.zeroIsoTerminal.symm
      exact @Subsingleton.elim ((skyscraperModuleUnderlying R x M).obj U)
        (AddCommGrpCat.subsingleton_of_isZero hz) _ _)

set_option backward.isDefEq.respectTransparency false in
private lemma from_to (P : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))
    (φ : PresheafOfModules.stalkObjComm R x P ⟶ M) :
    fromSky R x M P (toSky R x M P φ) = φ := by
  ext m
  exact ConcreteCategory.congr_hom
    (StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper x
      ((forget₂ _ AddCommGrpCat).map φ)) m

set_option backward.isDefEq.respectTransparency false in
private lemma to_from (P : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))
    (φ : P ⟶ skyscraperModule R x M) :
    toSky R x M P (fromSky R x M P φ) = φ := by
  apply (PresheafOfModules.toPresheaf _).map_injective
  exact StalkSkyscraperPresheafAdjunctionAuxs.to_skyscraper_fromStalk x
    ((PresheafOfModules.toPresheaf _).map φ)

/-- The module-linear stalk/skyscraper hom equivalence. -/
def stalkSkyscraperHomEquiv (P : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.stalkObjComm R x P ⟶ M) ≃ (P ⟶ skyscraperModule R x M) where
  toFun := toSky R x M P
  invFun := fromSky R x M P
  left_inv := from_to R x M P
  right_inv := to_from R x M P

set_option backward.isDefEq.respectTransparency false in
private lemma fromSky_germ (P : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))
    (φ : P ⟶ skyscraperModule R x M) (U : Opens X) (hx : x ∈ U) (m : P.obj (op U)) :
    fromSky R x M P φ (TopCat.Presheaf.germ P.presheaf U x hx m) =
      (eqToHom (show (skyscraperModuleUnderlying R x M).obj (op U) = AddCommGrpCat.of M
        from if_pos hx))
        (φ.app (op U) m) :=
  ConcreteCategory.congr_hom
    (StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk x
      ((PresheafOfModules.toPresheaf _).map φ) U hx) m

set_option backward.isDefEq.respectTransparency false in
private lemma fromSky_comp {P Q : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (f : P ⟶ Q) (φ : Q ⟶ skyscraperModule R x M) :
    fromSky R x M P (f ≫ φ) =
      (PresheafOfModules.stalkFunctorComm R x).map f ≫ fromSky R x M Q φ := by
  ext m
  obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf m
  change fromSky R x M P (f ≫ φ) (TopCat.Presheaf.germ P.presheaf U x hx m) =
    fromSky R x M Q φ ((PresheafOfModules.stalkFunctorComm R x).map f
      (TopCat.Presheaf.germ P.presheaf U x hx m))
  rw [PresheafOfModules.stalkFunctorComm_map_germ, fromSky_germ, fromSky_germ]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma toSkyscraper_comp {P : X.Presheaf AddCommGrpCat.{u}} {A B : AddCommGrpCat.{u}}
    (f : P.stalk x ⟶ A) (g : A ⟶ B) :
    StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x (f ≫ g) =
      StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x f ≫
        (skyscraperPresheafFunctor x).map g := by
  apply NatTrans.ext
  funext U
  by_cases hx : x ∈ U.unop
  · simp [StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app,
      skyscraperPresheafFunctor, SkyscraperPresheafFunctor.map'_app, hx]
  · exact ((if_neg hx).symm.ndrec terminalIsTerminal).hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
/-- Taking module-valued stalks is left adjoint to the module skyscraper functor. -/
def stalkSkyscraperAdjunction : stalkFunctorComm R x ⊣ skyscraperModuleFunctor R x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P N => stalkSkyscraperHomEquiv R x N P
      homEquiv_naturality_left_symm := fun f g => fromSky_comp R x _ f g
      homEquiv_naturality_right := by
        intro P N N' f g
        apply (PresheafOfModules.toPresheaf _).map_injective
        exact toSkyscraper_comp x ((forget₂ _ AddCommGrpCat).map f)
          ((forget₂ _ AddCommGrpCat).map g) }

end PresheafOfModules

namespace GromovWitten.AlgebraicGeometry.Curves
open _root_.AlgebraicGeometry
variable (X : Scheme.{u}) (x : X)

/-- A skyscraper sheaf of modules on a scheme, with scalars acting through the stalk. -/
def moduleSkyscraper : ModuleCat.{u} (X.presheaf.stalk x) ⥤ X.Modules :=
  PresheafOfModules.skyscraperModuleSheafFunctor (𝓡 := X.sheaf) x

set_option backward.isDefEq.respectTransparency false in
/-- The module-valued stalk functor on a scheme is left adjoint to its skyscraper functor. -/
def moduleStalkSkyscraperAdjunction : moduleStalk X x ⊣ moduleSkyscraper X x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P N =>
        ((PresheafOfModules.stalkSkyscraperAdjunction X.presheaf x).homEquiv P.val N).trans
          ((SheafOfModules.fullyFaithfulForget X.ringCatSheaf).homEquiv
            (X := P) (Y := (moduleSkyscraper X x).obj N)).symm
      homEquiv_naturality_left_symm := by
        intro P Q N f g
        let adj := PresheafOfModules.stalkSkyscraperAdjunction X.presheaf x
        exact adj.homEquiv_naturality_left_symm f.val g.val
      homEquiv_naturality_right := by
        intro P N N' f g
        apply SheafOfModules.hom_ext
        let adj := PresheafOfModules.stalkSkyscraperAdjunction X.presheaf x
        exact adj.homEquiv_naturality_right f g }

end GromovWitten.AlgebraicGeometry.Curves
