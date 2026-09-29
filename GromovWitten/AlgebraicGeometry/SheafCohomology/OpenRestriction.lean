/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.SectionsMayerVietoris
import GromovWitten.AlgebraicGeometry.SheafCohomology.RightDerivedComposition
import Mathlib.Topology.Sheaves.Functors
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
/-!
# Derived sections and restriction to open subspaces

Naive restriction along an open embedding is exact and preserves flasque sheaves.
Restricting an injective resolution therefore gives a flasque resolution. This identifies
cohomology on the open subspace with the right derived functors of taking sections on its image.
We also compare derived global sections with derived pushforward to a point.
-/

open CategoryTheory Limits Opposite TopologicalSpace
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology
variable {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : Topology.IsOpenEmbedding f)
instance openRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (hf.sheafPullback AddCommGrpCat.{u}) := by
  let _ : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} Y) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _))
  have : PreservesFiniteLimits
      (hf.sheafPullback AddCommGrpCat.{u} ⋙ TopCat.Sheaf.forget AddCommGrpCat X) := by
    change PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat Y ⋙
      (Functor.whiskeringLeft _ _ _).obj hf.functor.op)
    exact inferInstanceAs (PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj hf.functor.op))
  exact preservesFiniteLimits_of_reflects_of_preserves
    (hf.sheafPullback AddCommGrpCat) (TopCat.Sheaf.forget AddCommGrpCat X)
instance openRestriction_preservesColimits :
    PreservesColimits (hf.sheafPullback AddCommGrpCat.{u}) :=
  preservesColimits_of_natIso (hf.sheafPullbackIso AddCommGrpCat)
instance openRestriction_additive : (hf.sheafPullback AddCommGrpCat.{u}).Additive :=
  ⟨by intros; rfl⟩
instance openRestriction_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{u} Y)
    [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque ((hf.sheafPullback AddCommGrpCat).obj F) where
  epi i := by change Epi (F.obj.map _); infer_instance
end GromovWitten.AlgebraicGeometry.SheafCohomology
namespace GromovWitten.AlgebraicGeometry.SheafCohomology
variable (X : TopCat.{u})
def toPoint : X ⟶ PointSheaves.point.{u} := TopCat.isTerminalPUnit.from X
instance : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toPoint X)).Additive := ⟨by intros; rfl⟩
instance : PointSheaves.globalSections.{u}.Additive := ⟨by intros; rfl⟩
def sectionsTopIso :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toPoint X) ⋙ PointSheaves.globalSections ≅
      sections (⊤ : Opens X) := NatIso.ofComponents (fun _ => Iso.refl _)

def derivedSectionsTopIso (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    ((sections (⊤ : Opens X)).rightDerived n).obj F ≅
      PointSheaves.globalSections.obj
        (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toPoint X)).rightDerived n).obj F) := by
  exact ((CategoryTheory.NatIso.rightDerivedIso (sectionsTopIso X) n).app F).symm ≪≫
    Functor.rightDerivedCompExactIso _ _ F n


def flasqueResolutionSectionsTopIso {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ}
    (a : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso a]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (n : ℕ) :
    ((sections (⊤ : Opens X)).rightDerived n).obj F ≅
      (((sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).obj K).homology n := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toPoint X)
  exact derivedSectionsTopIso X F n ≪≫
    PointSheaves.globalSections.mapIso
      (TopCat.Sheaf.flasqueResolutionRightDerivedIso (toPoint X) a hK n) ≪≫
    (ShortComplex.mapHomologyIso ((P.mapHomologicalComplex (.up ℕ) |>.obj K).sc n)
      PointSheaves.globalSections).symm

variable {X} {Y : TopCat.{u}} {f : X ⟶ Y}
/-- Cohomology on an open subspace is the derived section functor on its image. -/
def derivedSectionsOpenIso (hf : Topology.IsOpenEmbedding f)
    (F : TopCat.Sheaf AddCommGrpCat.{u} Y) (n : ℕ) :
    ((sections (hf.functor.obj ⊤)).rightDerived n).obj F ≅
      ((sections (⊤ : Opens X)).rightDerived n).obj
        ((hf.sheafPullback AddCommGrpCat).obj F) := by
  let I := InjectiveResolution.of F
  let R := hf.sheafPullback AddCommGrpCat.{u}
  have : R.PreservesHomology := by infer_instance
  let K := (R.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let a := (HomologicalComplex.singleMapHomologicalComplex R (.up ℕ) 0).inv.app F ≫
    (R.mapHomologicalComplex (.up ℕ)).map I.ι
  have : QuasiIso a := by infer_instance
  have hK (k : ℕ) : TopCat.Sheaf.IsFlasque (K.X k) := by
    let _ := TopCat.Sheaf.isFlasque_of_injective Y (I.cocomplex.X k)
    exact openRestriction_isFlasque hf _
  exact I.isoRightDerivedObj (sections (hf.functor.obj ⊤)) n ≪≫
    (flasqueResolutionSectionsTopIso X a hK n).symm
end GromovWitten.AlgebraicGeometry.SheafCohomology
