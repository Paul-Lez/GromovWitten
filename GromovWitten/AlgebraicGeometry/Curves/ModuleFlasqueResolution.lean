/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleDerived

/-!
# Flasque resolutions for module-valued pushforward

The underlying abelian pushforward of a flasque module sheaf is flasque.
Consequently a flasque module resolution computes the module-valued
higher direct image.
-/

open CategoryTheory Limits HomologicalComplex
open _root_.AlgebraicGeometry

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X Y : Scheme.{u}}

/-- Pushforward preserves quasi-isomorphisms between complexes of flasque module sheaves. -/
lemma modulePushforward_quasiIso_of_flasque (f : X ⟶ Y)
    {K L : CochainComplex X.Modules ℕ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (L.X n))) :
    QuasiIso (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).map φ) := by
  apply (quasiIso_map_iff_of_preservesHomology _ (moduleToSheafAb Y)).mp
  exact TopCat.Sheaf.pushforward_quasiIso_of_flasque f.base
    (((moduleToSheafAb X).mapHomologicalComplex (.up ℕ)).map φ) hK hL

/-- Pushforward preserves flasqueness of the underlying abelian sheaf of a
flasque module sheaf. -/
lemma modulePushforward_isFlasque (f : X ⟶ Y) (M : X.Modules)
    [TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj M)] :
    TopCat.Sheaf.IsFlasque
      ((moduleToSheafAb Y).obj ((Scheme.Modules.pushforward f).obj M)) := by
  change TopCat.Sheaf.IsFlasque
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
      ((moduleToSheafAb X).obj M))
  exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque ((moduleToSheafAb X).obj M) f.base

/-- A quasi-isomorphic resolution by flasque module sheaves computes the
module-valued higher direct image. -/
noncomputable def moduleFlasqueResolutionRightDerivedIso
    (f : X ⟶ Y) {M : X.Modules}
    {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ _).obj M ⟶ K) [QuasiIso a]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (n : ℕ) :
    higherDirectImageModule f M n ≅
      ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ) |>.obj K).homology n := by
  let I : InjectiveResolution M := InjectiveResolution.of M
  let φ := (I.exists_desc_of_quasiIso a).choose
  have : QuasiIso φ := (I.exists_desc_of_quasiIso a).choose_spec.2
  have hI (k : ℕ) : TopCat.Sheaf.IsFlasque
      ((moduleToSheafAb X).obj (I.cocomplex.X k)) :=
    module_isFlasque_of_injective _
  have : QuasiIso
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).map φ) :=
    modulePushforward_quasiIso_of_flasque f φ hK hI
  exact I.isoRightDerivedObj (Scheme.Modules.pushforward f) n ≪≫
    (isoOfQuasiIsoAt
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).map φ) n).symm

end GromovWitten.AlgebraicGeometry.Curves
