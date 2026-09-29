/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenus
import GromovWitten.AlgebraicGeometry.Curves.ModuleStalk
import GromovWitten.AlgebraicGeometry.Curves.OpenPullbackSectionsLinear
import Mathlib.RingTheory.Flat.Basic

/-!
# Relative stalk modules

This file equips module stalks with the base-ring action induced by a scheme
structure morphism.  It records scalar compatibility for germs and open
restrictions, then transfers the resulting linear equivalences and flatness
statements through open pullback.
-/

open CategoryTheory TopCat AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

local instance nativeStalkModule (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) := by
  let P := (Scheme.Modules.toPresheafOfModules X).obj M
  exact @PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    _ _ P x

/-- The stalk of a module, regarded as a module over the base ring. -/
def relativeStalkBase (s : X ⟶ Spec R) (M : X.Modules) (x : X) : ModuleCat R :=
  (ModuleCat.restrictScalars
    ((X.presheaf.Γgerm x).hom.comp (baseRingHom (R : Type u) s))).obj
      (ModuleCat.of (X.presheaf.stalk x) (M.presheaf.stalk x))

set_option backward.isDefEq.respectTransparency false in
/-- Germs are linear for the relative base-ring action. -/
lemma relative_germ_smul (s : X ⟶ Spec R) (M : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (r : R) (m : Γ(M, U)) :
    M.presheaf.germ U x hx ((baseToSections s U).hom r • m) =
      (show relativeStalkBase s M x from r • (show relativeStalkBase s M x from
        M.presheaf.germ U x hx m)) := by
  let P := (Scheme.Modules.toPresheafOfModules X).obj M
  change _ = ((X.presheaf.Γgerm x).hom (baseRingHom R s r)) •
    M.presheaf.germ U x hx m
  erw [PresheafOfModules.germ_smul P x U hx]
  congr 1
  exact X.presheaf.Γgerm_res_apply x hx _

variable {Y : Scheme.{u}}

/-- Base-ring section maps commute with restriction along an open immersion. -/
lemma baseToSections_open (s : Y ⟶ Spec R) (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) :
    baseToSections (f ≫ s) U ≫ (f.appIso U).inv = baseToSections s (f ''ᵁ U) := by
  simp only [baseToSections]
  rw [Scheme.Hom.comp_appTop]
  simp only [Category.assoc, Scheme.Hom.appIso_inv_naturality]
  have h : f.appTop ≫ (f.appIso (⊤ : X.Opens)).inv =
      Y.presheaf.map (homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op :=
    Scheme.Hom.app_appIso_inv f ⊤
  rw [← Category.assoc f.appTop, h]
  rw [← Functor.map_comp]
  rfl

/-- Isomorphic modules have linearly equivalent relative stalks. -/
def relativeStalkLinearEquiv (s : X ⟶ Spec R) {M N : X.Modules}
    (e : M ≅ N) (x : X) : relativeStalkBase s M x ≃ₗ[R] relativeStalkBase s N x :=
  ((ModuleCat.restrictScalars
    ((X.presheaf.Γgerm x).hom.comp (baseRingHom R s))).mapIso
      ((moduleStalk X x).mapIso e)).toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along an open immersion induces a base-linear stalk map. -/
def relativeRestrictStalkLinear (s : Y ⟶ Spec R) (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (x : X) :
    relativeStalkBase (f ≫ s) (M.restrict f) x →ₗ[R] relativeStalkBase s M (f x) where
  __ := ((Scheme.Modules.restrictStalkNatIso f x).hom.app M).hom
  map_smul' r m := by
    let : Module R ((M.restrict f).presheaf.stalk x) :=
      (relativeStalkBase (f ≫ s) (M.restrict f) x).isModule
    let : Module R (M.presheaf.stalk (f x)) := (relativeStalkBase s M (f x)).isModule
    change (show (M.restrict f).presheaf.stalk x ⟶ M.presheaf.stalk (f x) from
      (Scheme.Modules.restrictStalkNatIso f x).hom.app M) (r • m) =
      r • (show (M.restrict f).presheaf.stalk x ⟶ M.presheaf.stalk (f x) from
        (Scheme.Modules.restrictStalkNatIso f x).hom.app M) m
    obtain ⟨U, hx, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq (M.restrict f).presheaf m
    have hs : r • (M.restrict f).presheaf.germ U x hx y =
        (M.restrict f).presheaf.germ U x hx ((baseToSections (f ≫ s) U).hom r • y) :=
      (relative_germ_smul (f ≫ s) (M.restrict f) x U hx r y).symm
    rw [hs]
    have hg (z : Γ(M.restrict f, U)) :
        (show (M.restrict f).presheaf.stalk x ⟶ M.presheaf.stalk (f x) from
          (Scheme.Modules.restrictStalkNatIso f x).hom.app M)
            ((M.restrict f).presheaf.germ U x hx z) =
          M.presheaf.germ (f ''ᵁ U) (f x) (by simpa) z :=
      congrArg (fun k => k z) (Scheme.Modules.germ_restrictStalkNatIso_hom_app f x M hx)
    rw [hg, hg]
    change M.presheaf.germ (f ''ᵁ U) (f x) _
      (((f.appIso U).inv ((baseToSections (f ≫ s) U).hom r)) •
        (show Γ(M, f ''ᵁ U) from y)) = _
    have hr : (f.appIso U).inv ((baseToSections (f ≫ s) U).hom r) =
        (baseToSections s (f ''ᵁ U)).hom r :=
      congrArg (fun k => k r) (baseToSections_open s f U)
    rw [hr, relative_germ_smul]

/-- Restriction along an open immersion induces a base-linear stalk equivalence. -/
def relativeRestrictStalkLinearEquiv (s : Y ⟶ Spec R) (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (x : X) :
    relativeStalkBase (f ≫ s) (M.restrict f) x ≃ₗ[R] relativeStalkBase s M (f x) :=
  LinearEquiv.ofBijective (relativeRestrictStalkLinear s f M x)
    (ConcreteCategory.bijective_of_isIso ((Scheme.Modules.restrictStalkNatIso f x).hom.app M))

/-- Pullback along an open immersion preserves the relative stalk up to a base-linear
equivalence. -/
def relativeOpenPullbackStalkLinearEquiv (s : Y ⟶ Spec R) (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (x : X) :
    relativeStalkBase (f ≫ s) ((Scheme.Modules.pullback f).obj M) x ≃ₗ[R]
      relativeStalkBase s M (f x) :=
  (relativeStalkLinearEquiv (f ≫ s)
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm x).trans
      (relativeRestrictStalkLinearEquiv s f M x)

/-- Flatness over the base ring transfers to relative stalks after open pullback. -/
lemma relativeOpenPullbackStalk_flat (s : Y ⟶ Spec R) (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules)
    (h : ∀ y : Y, Module.Flat R (relativeStalkBase s M y)) (x : X) :
    Module.Flat R (relativeStalkBase (f ≫ s) ((Scheme.Modules.pullback f).obj M) x) := by
  have := h (f x)
  exact Module.Flat.of_linearEquiv (relativeOpenPullbackStalkLinearEquiv s f M x)

end GromovWitten.AlgebraicGeometry.Curves
