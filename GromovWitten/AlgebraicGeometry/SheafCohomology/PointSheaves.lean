/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
/-!
# Global sections of abelian sheaves on a point

The only neighborhood of the point is the whole space, so taking global sections is
naturally isomorphic to taking its stalk. It therefore preserves homology and detects
zero sheaves. This lets derived pushforward to a point be computed on global sections.
-/

open CategoryTheory Limits Opposite TopologicalSpace
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.SheafCohomology.PointSheaves
/-- The one-point space in the same universe as the abelian groups. -/
abbrev point : TopCat.{u} := TopCat.of PUnit.{u + 1}

/-- Global sections on the one-point space. -/
def globalSections : TopCat.Sheaf AddCommGrpCat.{u} point.{u} ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤)

private def topNhds : OpenNhds (X := point.{u}) PUnit.unit := ⟨⊤, trivial⟩
private def topNhdsIsInitial : IsInitial topNhds.{u} := by
  let _ : ∀ U : OpenNhds (X := point.{u}) PUnit.unit, Unique (topNhds ⟶ U) := fun U =>
    ⟨⟨homOfLE (by
      intro x _
      have : x = PUnit.unit := Subsingleton.elim _ _
      simpa only [this] using U.2)⟩, fun _ => Subsingleton.elim _ _⟩
  exact IsInitial.ofUnique _

/-- A global section is uniquely determined by its germ at the unique point. -/
instance germTop_isIso (F : TopCat.Presheaf AddCommGrpCat.{u} point.{u}) :
    IsIso (F.Γgerm PUnit.unit) := by
  exact isIso_ι_of_isTerminal topNhdsIsInitial.op _

/-- On a point, global sections are naturally the stalk. -/
def globalSectionsStalkIso : globalSections ≅
    TopCat.Sheaf.forget AddCommGrpCat.{u} point.{u} ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := point.{u}) PUnit.unit :=
  NatIso.ofComponents (fun F => by
    exact @asIso _ _ _ _
      (TopCat.Presheaf.Γgerm (X := point.{u}) F.obj PUnit.unit) (germTop_isIso F.obj)) (fun f => by
    exact (TopCat.Presheaf.stalkFunctor_map_germ ⊤ PUnit.unit trivial f.hom).symm)

instance : PreservesFiniteLimits globalSections :=
  preservesFiniteLimits_of_natIso globalSectionsStalkIso.symm
instance : PreservesColimits globalSections :=
  preservesColimits_of_natIso globalSectionsStalkIso.symm
instance : globalSections.PreservesHomology := by infer_instance

/-- Global sections detect zero sheaves on a point. -/
lemma isZero_of_globalSections_obj (F : TopCat.Sheaf AddCommGrpCat.{u} point.{u})
    (h : IsZero (globalSections.obj F)) : IsZero F := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
    (C := AddCommGrpCat.{u}) (X := point.{u}) F).mpr
  intro x
  have hx : x = PUnit.unit := Subsingleton.elim _ _
  subst x
  exact h.of_iso (globalSectionsStalkIso.app F).symm
end GromovWitten.AlgebraicGeometry.SheafCohomology.PointSheaves
