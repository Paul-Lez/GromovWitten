/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleDerived

/-!
# Derived base change for module-valued pushforward

For a Cartesian square of schemes, the ordinary Beck--Chevalley morphism is a natural
transformation between the two corresponding functors on sheaves of modules.  Applying the
right-derived construction gives the canonical derived base-change morphism in every degree.

The component in degree zero is deliberately the existing
`canonicalPushforwardBaseChangeComparison`: the derived construction adds no independently chosen
comparison map or module structure.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open scoped AlgebraicGeometry ZeroObject

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X S : Scheme.{u}}

/-- The adjoint form of the ordinary module-valued Beck--Chevalley map. -/
def moduleBaseChangePullbackMap {T Z : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (M : X.Modules) :
    (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward f).obj M)) ⟶
      (Scheme.Modules.pullback p).obj M :=
  (Scheme.Modules.pullbackComp g b).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
    (Scheme.Modules.pullbackCongr h.w.symm).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
      (Scheme.Modules.pullbackComp p f).inv.app ((Scheme.Modules.pushforward f).obj M) ≫
        (Scheme.Modules.pullback p).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)

lemma moduleBaseChangePullbackMap_naturality {T Z : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) {M N : X.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback g).map
        ((Scheme.Modules.pullback b).map ((Scheme.Modules.pushforward f).map φ)) ≫
        moduleBaseChangePullbackMap f b p g h N =
      moduleBaseChangePullbackMap f b p g h M ≫ (Scheme.Modules.pullback p).map φ := by
  dsimp [moduleBaseChangePullbackMap]
  rw [← Functor.comp_map]
  simp only [Category.assoc]
  rw [(Scheme.Modules.pullbackComp g b).hom.naturality_assoc
    ((Scheme.Modules.pushforward f).map φ) _]
  rw [(Scheme.Modules.pullbackCongr h.w.symm).hom.naturality_assoc
    ((Scheme.Modules.pushforward f).map φ) _]
  rw [(Scheme.Modules.pullbackComp p f).inv.naturality_assoc
    ((Scheme.Modules.pushforward f).map φ) _]
  rw [Functor.comp_map]
  rw [← Functor.map_comp]
  rw [← Functor.comp_map]
  rw [(Scheme.Modules.pullbackPushforwardAdjunction f).counit.naturality]
  simp only [Functor.id_map, ← Functor.map_comp]

/-- The ordinary module-valued Beck--Chevalley natural transformation. -/
def modulePushforwardBaseChangeNatTrans {T Z : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback b ⟶
      Scheme.Modules.pullback p ⋙ Scheme.Modules.pushforward g where
  app M := (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
    (moduleBaseChangePullbackMap f b p g h M)
  naturality M N φ := by
    let adj := Scheme.Modules.pullbackPushforwardAdjunction g
    rw [← adj.homEquiv_naturality_left]
    simp only [Functor.comp_map]
    rw [← adj.homEquiv_naturality_right]
    exact congrArg (adj.homEquiv _ _)
      (moduleBaseChangePullbackMap_naturality f b p g h φ)

/-- The ordinary component of `modulePushforwardBaseChangeNatTrans` is exactly the canonical
Beck--Chevalley comparison used by the curve cohomology API. -/
@[simp]
theorem modulePushforwardBaseChangeNatTrans_app_eq_canonical {T Z : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (M : X.Modules) :
    (modulePushforwardBaseChangeNatTrans f b p g h).app M =
      canonicalPushforwardBaseChangeComparison f M b p g h :=
  rfl

/-- The canonical derived base-change morphism in degree `n`. -/
def moduleDerivedBaseChangeNatTrans {T Z : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ) :
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback b).rightDerived n ⟶
      (Scheme.Modules.pullback p ⋙ Scheme.Modules.pushforward g).rightDerived n :=
  NatTrans.rightDerived (modulePushforwardBaseChangeNatTrans f b p g h) n

/-- A natural isomorphism of ordinary base-change functors induces an isomorphism of their
right-derived functors.  This is the honest transfer step used once a geometric ordinary
base-change theorem supplies the isomorphism `e`. -/
def moduleDerivedBaseChangeIsoOfOrdinaryIso {T Z : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (_h : IsPullback p g f b)
    (e : (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback b) ≅
      (Scheme.Modules.pullback p ⋙ Scheme.Modules.pushforward g)) (n : ℕ) :
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback b).rightDerived n ≅
      (Scheme.Modules.pullback p ⋙ Scheme.Modules.pushforward g).rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

end
end GromovWitten.AlgebraicGeometry.Curves
