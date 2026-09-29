/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModulePullbackExact
import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChange
import GromovWitten.AlgebraicGeometry.SheafCohomology.DerivedBaseChange

/-!
# Higher direct-image base-change maps

When the two pullback functors in a Cartesian square are exact, the ordinary
Beck--Chevalley map induces an actual comparison `b* Rⁿ f* M ⟶ Rⁿ g* (p* M)`.
The source and target are higher direct images in the categories of modules. Flatness of the
base-change morphism supplies the required exactness of both pullbacks.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X S T Z : Scheme.{u}}
/-- The higher direct-image comparison for a square with exact pullbacks. -/
def moduleHigherBaseChangeNatTrans
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology] (n : ℕ) :
    (Scheme.Modules.pushforward f).rightDerived n ⋙ Scheme.Modules.pullback b ⟶
      Scheme.Modules.pullback p ⋙ (Scheme.Modules.pushforward g).rightDerived n :=
  NatTrans.rightDerivedBaseChange (modulePushforwardBaseChangeNatTrans f b p g h) n

/-- In degree zero, the higher comparison is the canonical Beck--Chevalley map. -/
theorem moduleHigherBaseChange_zero
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology] (M : X.Modules) :
    (Scheme.Modules.pullback b).map
        ((Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf.inv.app M) ≫
      (moduleHigherBaseChangeNatTrans f b p g h 0).app M ≫
        (Scheme.Modules.pushforward g).rightDerivedZeroIsoSelf.hom.app
          ((Scheme.Modules.pullback p).obj M) =
      canonicalPushforwardBaseChangeComparison f M b p g h :=
  NatTrans.rightDerivedBaseChange_zero (modulePushforwardBaseChangeNatTrans f b p g h) M

/-- The higher direct-image comparison for flat base change. -/
def moduleFlatHigherBaseChangeNatTrans
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) [Flat b] (n : ℕ) :
    (Scheme.Modules.pushforward f).rightDerived n ⋙ Scheme.Modules.pullback b ⟶
      Scheme.Modules.pullback p ⋙ (Scheme.Modules.pushforward g).rightDerived n := by
  let _ : Flat p := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  exact moduleHigherBaseChangeNatTrans f b p g h n

/-- The flat-base-change comparison agrees with ordinary base change in degree zero. -/
theorem moduleFlatHigherBaseChange_zero
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) [Flat b] (M : X.Modules) :
    (Scheme.Modules.pullback b).map
        ((Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf.inv.app M) ≫
      (moduleFlatHigherBaseChangeNatTrans f b p g h 0).app M ≫
        (Scheme.Modules.pushforward g).rightDerivedZeroIsoSelf.hom.app
          ((Scheme.Modules.pullback p).obj M) =
      canonicalPushforwardBaseChangeComparison f M b p g h := by
  let _ : Flat p := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  exact moduleHigherBaseChange_zero f b p g h M

end GromovWitten.AlgebraicGeometry.Curves
