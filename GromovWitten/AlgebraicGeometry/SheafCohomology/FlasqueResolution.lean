/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.FlasqueNatComplex
import GromovWitten.AlgebraicGeometry.SheafCohomology.ResolutionComparison

/-!
# Computing derived pushforward with a flasque resolution

Any resolution by flasque abelian sheaves computes the right derived pushforward.
The comparison map into an injective resolution is a quasi-isomorphism between
flasque complexes, and stays a quasi-isomorphism after pushforward.
-/

open CategoryTheory Limits HomologicalComplex

namespace TopCat.Sheaf

universe u

noncomputable section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable [(pushforward AddCommGrpCat.{u} f).Additive]
variable [EnoughInjectives (Sheaf AddCommGrpCat.{u} X)]

/-- A flasque resolution computes all right derived pushforwards. -/
def flasqueResolutionRightDerivedIso {F : Sheaf AddCommGrpCat.{u} X}
    {K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ}
    (a : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso a]
    (hK : ∀ n, IsFlasque (K.X n)) (n : ℕ) :
    ((pushforward AddCommGrpCat f).rightDerived n).obj F ≅
      ((pushforward AddCommGrpCat f).mapHomologicalComplex (.up ℕ) |>.obj K).homology n := by
  let I := InjectiveResolution.of F
  let φ := (I.exists_desc_of_quasiIso a).choose
  have : QuasiIso φ := (I.exists_desc_of_quasiIso a).choose_spec.2
  have hI (k : ℕ) : IsFlasque (I.cocomplex.X k) := isFlasque_of_injective X _
  have := pushforward_quasiIso_of_flasque f φ hK hI
  exact I.isoRightDerivedObj (pushforward AddCommGrpCat f) n ≪≫
    (isoOfQuasiIsoAt ((pushforward AddCommGrpCat f).mapHomologicalComplex _ |>.map φ) n).symm

end

end TopCat.Sheaf
