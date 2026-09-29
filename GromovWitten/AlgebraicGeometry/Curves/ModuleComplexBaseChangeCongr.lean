/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.ComplexBaseChangeHomotopy
import GromovWitten.AlgebraicGeometry.Curves.HigherBaseChange

/-!
# Congruence for complex base-change maps

Quasi-isomorphism of the complex base-change map is unchanged when the base
and pullback morphisms are replaced by equal morphisms.
-/

open CategoryTheory Limits HomologicalComplex
noncomputable section
open _root_.AlgebraicGeometry
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
variable {X S T Y : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false in
/-- Equal base and pullback maps give equivalent complex base-change maps. -/
lemma moduleComplexBaseChange_quasiIso_congr_iff
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b)
    (b' : T ⟶ S) (p' : Y ⟶ X) (hb : b = b') (hp : p = p')
    (h' : IsPullback p' g s b')
    {K : CochainComplex X.Modules ℕ} {J : CochainComplex Y.Modules ℕ}
    (φ : ((Scheme.Modules.pullback p').mapHomologicalComplex (.up ℕ)).obj K ⟶ J)
:
    QuasiIso (NatTrans.complexBaseChangeMap (Scheme.Modules.pushforward s)
      (Scheme.Modules.pullback b) (Scheme.Modules.pullback p) (Scheme.Modules.pushforward g)
      (modulePushforwardBaseChangeNatTrans s b p g h)
      ((NatIso.mapHomologicalComplex (Scheme.Modules.pullbackCongr hp) (.up ℕ)).hom.app K ≫
        φ)) ↔
    QuasiIso (NatTrans.complexBaseChangeMap (Scheme.Modules.pushforward s)
      (Scheme.Modules.pullback b') (Scheme.Modules.pullback p') (Scheme.Modules.pushforward g)
      (modulePushforwardBaseChangeNatTrans s b' p' g h') φ) := by
  subst b'
  subst p'
  change QuasiIso (NatTrans.complexBaseChangeMap (Scheme.Modules.pushforward s)
      (Scheme.Modules.pullback b) (Scheme.Modules.pullback p) (Scheme.Modules.pushforward g)
      (modulePushforwardBaseChangeNatTrans s b p g h) (𝟙 _ ≫ φ)) ↔ _
  rw [Category.id_comp]
end GromovWitten.AlgebraicGeometry.Curves
