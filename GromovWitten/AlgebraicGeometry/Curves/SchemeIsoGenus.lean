/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenus
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Functors
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

open CategoryTheory TopologicalSpace

universe u v w

noncomputable section

variable (C : Type u) [Category.{v} C] {X Y : TopCat.{w}}

def sheafEquivOfIso (e : X ≅ Y) : X.Sheaf C ≌ Y.Sheaf C := by
  let E := Opens.mapMapIso e
  let JX := Opens.grothendieckTopology X
  let JY := Opens.grothendieckTopology Y
  letI : E.functor.IsContinuous JY JX := by
    change (Opens.map e.hom).IsContinuous _ _
    infer_instance
  letI : E.inverse.IsContinuous JX JY := by
    change (Opens.map e.inv).IsContinuous _ _
    infer_instance
  letI := Functor.isContinuous_comp E.inverse E.functor JX JY JX
  letI := Functor.isContinuous_comp E.functor E.inverse JY JX JY
  let unit : 𝟭 (X.Sheaf C) ≅
      TopCat.Sheaf.pushforward C e.hom ⋙ TopCat.Sheaf.pushforward C e.inv :=
    (Functor.sheafPushforwardContinuousId C JX).symm ≪≫
    Functor.sheafPushforwardContinuousIso E.counitIso.symm C JX JX ≪≫
    (Functor.sheafPushforwardContinuousComp E.inverse E.functor C JX JY JX).symm
  let counit : TopCat.Sheaf.pushforward C e.inv ⋙ TopCat.Sheaf.pushforward C e.hom ≅
      𝟭 (Y.Sheaf C) :=
    Functor.sheafPushforwardContinuousComp E.functor E.inverse C JY JX JY ≪≫
    Functor.sheafPushforwardContinuousIso E.unitIso.symm C JY JY ≪≫
    Functor.sheafPushforwardContinuousId C JY
  exact CategoryTheory.Equivalence.mk _ _ unit counit

variable [HasWeakSheafify (Opens.grothendieckTopology X) C]
  [HasWeakSheafify (Opens.grothendieckTopology Y) C]

def constantPushforwardIso (e : X ≅ Y) :
    constantSheaf (Opens.grothendieckTopology X) C ⋙ (sheafEquivOfIso C e).functor ≅
      constantSheaf (Opens.grothendieckTopology Y) C :=
  ((constantSheafAdj (Opens.grothendieckTopology X) C
      (Limits.IsTerminal.ofUnique (⊤ : Opens X))).comp
      (sheafEquivOfIso C e).toAdjunction).leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology Y) C
      (Limits.IsTerminal.ofUnique (⊤ : Opens Y)))

open CategoryTheory.Abelian

variable {X Y : TopCat.{w}}

set_option backward.isDefEq.respectTransparency false in
noncomputable def cohomologyPushforwardAddEquiv (e : X ≅ Y)
    (A : X.Sheaf AddCommGrpCat.{w}) (n : ℕ) :
    Sheaf.H.{w} A n ≃+ Sheaf.H.{w} ((sheafEquivOfIso AddCommGrpCat.{w} e).functor.obj A) n := by
  let E := sheafEquivOfIso AddCommGrpCat.{w} e
  let F := E.functor
  letI : F.Additive := Functor.additive_of_preserves_binary_products F
  let T := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj
    (AddCommGrpCat.of (ULift.{w} ℤ))
  let h₁ : Ext.{w} T A n ≃+ Ext.{w} (F.obj T) (F.obj A) n :=
    AddEquiv.ofBijective (F.mapExtAddHom T A n)
      (F.mapExt_bijective_of_preservesInjectiveObjects T A n)
  let c := (constantPushforwardIso AddCommGrpCat.{w} e).app
    (AddCommGrpCat.of (ULift.{w} ℤ))
  let h₂ := (((extFunctor.{w} n).mapIso c.op).app (F.obj A)).addCommGroupIsoToAddEquiv
  exact h₁.trans h₂.symm

set_option backward.isDefEq.respectTransparency false in
theorem cohomologyPushforwardAddEquiv_naturality (e : X ≅ Y)
    {A B : X.Sheaf AddCommGrpCat.{w}} (φ : A ⟶ B) (n : ℕ) (x : Sheaf.H.{w} A n) :
    cohomologyPushforwardAddEquiv e B n (Sheaf.H.map φ n x) =
      Sheaf.H.map ((sheafEquivOfIso AddCommGrpCat.{w} e).functor.map φ) n
        (cohomologyPushforwardAddEquiv e A n x) := by
  let F := (sheafEquivOfIso AddCommGrpCat.{w} e).functor
  let _ : F.Additive := Functor.additive_of_preserves_binary_products F
  let c := (constantPushforwardIso AddCommGrpCat.{w} e).app
    (AddCommGrpCat.of (ULift.{w} ℤ))
  change (Ext.mk₀ c.inv).comp ((x.comp (Ext.mk₀ φ) (Nat.add_zero n)).mapExactFunctor F)
      (Nat.zero_add n) =
    ((Ext.mk₀ c.inv).comp (x.mapExactFunctor F) (Nat.zero_add n)).comp
      (Ext.mk₀ (F.map φ)) (Nat.add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc _ _ _ _ _ (by omega)).symm

namespace GromovWitten.AlgebraicGeometry.Curves

open CategoryTheory Limits
open _root_.AlgebraicGeometry

noncomputable section

def pushforwardStructureModuleIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.pushforward e.hom).obj (structureModule X) ≅ structureModule Y := by
  let φ := SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom
  haveI : IsIso φ := (Scheme.Modules.Hom.isIso_iff_isIso_app).2 (by
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    have h := ConcreteCategory.bijective_of_isIso (e.hom.app U)
    change Function.Bijective (e.hom.app U)
    exact h)
  exact (asIso φ).symm

def cohomologySchemeIsoAddEquiv {X Y : Scheme.{u}} (e : X ≅ Y) :
    cohomology X (structureModule X) 1 ≃+ cohomology Y (structureModule Y) 1 := by
  let q := pushforwardStructureModuleIso e
  let E := TopCat.isoOfHomeo e.schemeIsoToHomeo
  let h₁ : (cohomology X (structureModule X) 1 : Type u) ≃+
      (cohomology Y ((Scheme.Modules.pushforward e.hom).obj (structureModule X)) 1 : Type u) := by
    exact cohomologyPushforwardAddEquiv E
      ((moduleToSheafAb X).obj (structureModule X)) 1
  let h₂ := (cohomologyMapLinearEquiv q 1).toAddEquiv
  exact h₁.trans h₂

theorem baseRingHom_comp_schemeIso {k : Type u} [CommRing k]
    {X Y : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Spec (CommRingCat.of k)) :
    baseRingHom k (e.hom ≫ f) = (e.hom.appTop).hom.comp (baseRingHom k f) := by
  unfold baseRingHom
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem sectionSMul_pushforward_eq {X Y : Scheme.{u}} (e : X ≅ Y)
    (a : Γ(X, ⊤)) (b : Γ(Y, ⊤))
    (hab : e.hom.appTop b = a) :
    let E := TopCat.isoOfHomeo e.schemeIsoToHomeo
    ((sheafEquivOfIso AddCommGrpCat E).functor.map
      (sectionSMul (structureModule X) a)) =
      sectionSMul ((Scheme.Modules.pushforward e.hom).obj (structureModule X)) b := by
  dsimp
  apply sheafAb_hom_ext
  ext U x
  change ((sectionSMul (structureModule X) a).hom.app
      (Opposite.op (e.hom ⁻¹ᵁ U.unop))).hom x = _
  simp only [sectionSMul, sectionSMulPresheaf]
  have hn := Scheme.Hom.naturality e.hom
    (homOfLE (show U.unop ≤ (⊤ : Y.Opens) from le_top)).op
  have hrestr :
      restrictTop X (e.hom ⁻¹ᵁ U.unop) a =
        (e.hom.app U.unop) (restrictTop Y U.unop b) := by
    rw [← hab]
    exact congrArg (fun z ↦ z b) hn.symm
  rw [hrestr]
  rfl

theorem cohomologySchemeIsoAddEquiv_smul {k : Type u} [CommRing k]
    {X Y : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Spec (CommRingCat.of k))
    (c : k) (x : cohomology X (structureModule X) 1) :
    cohomologySchemeIsoAddEquiv e
        (baseRingHom k (e.hom ≫ f) c • x) =
      baseRingHom k f c • cohomologySchemeIsoAddEquiv e x := by
  let q := pushforwardStructureModuleIso e
  let E := TopCat.isoOfHomeo e.schemeIsoToHomeo
  let h₁ : (cohomology X (structureModule X) 1 : Type u) ≃+
      (cohomology Y ((Scheme.Modules.pushforward e.hom).obj (structureModule X)) 1 : Type u) := by
    exact cohomologyPushforwardAddEquiv E
      ((moduleToSheafAb X).obj (structureModule X)) 1
  let h₂ := (cohomologyMapLinearEquiv q 1)
  let x' : Sheaf.H ((moduleToSheafAb X).obj (structureModule X)) 1 := x
  change h₂ (cohomologyPushforwardAddEquiv E
      ((moduleToSheafAb X).obj (structureModule X)) 1
      (Sheaf.H.map (sectionSMul (structureModule X)
        (baseRingHom k (e.hom ≫ f) c)) 1 x')) =
    baseRingHom k f c • h₂ (cohomologyPushforwardAddEquiv E
      ((moduleToSheafAb X).obj (structureModule X)) 1 x')
  have hn := cohomologyPushforwardAddEquiv_naturality E
    (sectionSMul (structureModule X) (baseRingHom k (e.hom ≫ f) c)) 1 x'
  rw [hn]
  rw [sectionSMul_pushforward_eq e
    (baseRingHom k (e.hom ≫ f) c) (baseRingHom k f c)]
  · exact h₂.map_smul _ _
  · rw [baseRingHom_comp_schemeIso]
    rfl

def cohomologySchemeIsoLinearEquiv {k : Type u} [CommRing k]
    {X Y : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Spec (CommRingCat.of k)) :
    cohomologyModuleCat k (e.hom ≫ f) (structureModule X) 1 ≃ₗ[k]
      cohomologyModuleCat k f (structureModule Y) 1 := by
  let h := cohomologySchemeIsoAddEquiv e
  let L : cohomologyModuleCat k (e.hom ≫ f) (structureModule X) 1 →ₗ[k]
      cohomologyModuleCat k f (structureModule Y) 1 :=
    { toFun := h
      map_add' := h.map_add
      map_smul' := by
        intro c x
        exact cohomologySchemeIsoAddEquiv_smul e f c x }
  exact LinearEquiv.ofBijective L h.bijective

theorem arithmeticGenus_eq_of_scheme_iso {k : Type u} [Field k]
    {X Y : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Spec (CommRingCat.of k)) :
    arithmeticGenus k (e.hom ≫ f) = arithmeticGenus k f := by
  unfold arithmeticGenus hDim
  exact (cohomologySchemeIsoLinearEquiv e f).finrank_eq

end
end GromovWitten.AlgebraicGeometry.Curves
