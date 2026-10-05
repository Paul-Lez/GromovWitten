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

/-- The comparison between derived sections and derived global sections is natural in the sheaf. -/
lemma derivedSectionsTopIso_hom_naturality
    (F F' : TopCat.Sheaf AddCommGrpCat.{u} X) (f : F ⟶ F') (n : ℕ) :
    ((sections (⊤ : Opens X)).rightDerived n).map f ≫
        (derivedSectionsTopIso X F' n).hom =
      (derivedSectionsTopIso X F n).hom ≫
        PointSheaves.globalSections.map
          (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toPoint X)).rightDerived n).map f) := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toPoint X)
  let Q := PointSheaves.globalSections.{u}
  let e := CategoryTheory.NatIso.rightDerivedIso (sectionsTopIso X) n
  have he := e.inv.naturality f
  dsimp [derivedSectionsTopIso]
  calc
    _ = (((sections (⊤ : Opens X)).rightDerived n).map f ≫ e.inv.app F') ≫
        (CategoryTheory.Functor.rightDerivedCompExactIso P Q F' n).hom := by
      simp only [e, P, Q, Category.assoc]
    _ = (e.inv.app F ≫
        ((P ⋙ Q).rightDerived n).map f) ≫
        (CategoryTheory.Functor.rightDerivedCompExactIso P Q F' n).hom := by
      rw [he]
    _ = e.inv.app F ≫
        (((P ⋙ Q).rightDerived n).map f ≫
          (CategoryTheory.Functor.rightDerivedCompExactIso P Q F' n).hom) := by
      simp only [Category.assoc]
    _ = e.inv.app F ≫
        ((CategoryTheory.Functor.rightDerivedCompExactIso P Q F n).hom ≫
          Q.map ((P.rightDerived n).map f)) := by
      rw [CategoryTheory.Functor.rightDerivedCompExactIso_hom_naturality P Q f n]
    _ = _ := by
      simp only [e, P, Q, Category.assoc]


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

set_option backward.isDefEq.respectTransparency false in
/-- The sections-to-homology comparison is natural for compatible flasque resolutions. -/
lemma flasqueResolutionSectionsTopIso_hom_naturality
    {F F' : TopCat.Sheaf AddCommGrpCat.{u} X}
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ}
    (a : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso a]
    (b : (CochainComplex.single₀ _).obj F' ⟶ L) [QuasiIso b]
    (f : F ⟶ F') (φ : K ⟶ L)
    (hφ : a ≫ φ = (CochainComplex.single₀ _).map f ≫ b)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) (n : ℕ) :
    ((sections (⊤ : Opens X)).rightDerived n).map f ≫
        (flasqueResolutionSectionsTopIso X b hL n).hom =
      (flasqueResolutionSectionsTopIso X a hK n).hom ≫
        HomologicalComplex.homologyMap
          (((sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).map φ) n := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toPoint X)
  let Q := PointSheaves.globalSections.{u}
  let eF := derivedSectionsTopIso X F n
  let eF' := derivedSectionsTopIso X F' n
  let rF := TopCat.Sheaf.flasqueResolutionRightDerivedIso (toPoint X) a hK n
  let rF' := TopCat.Sheaf.flasqueResolutionRightDerivedIso (toPoint X) b hL n
  let hF :
      (((Q.mapHomologicalComplex (.up ℕ)).obj
        ((P.mapHomologicalComplex (.up ℕ)).obj K)).homology n) ≅
        Q.obj (((P.mapHomologicalComplex (.up ℕ)).obj K).homology n) :=
    ShortComplex.mapHomologyIso ((P.mapHomologicalComplex (.up ℕ) |>.obj K).sc n) Q
  let hF' :
      (((Q.mapHomologicalComplex (.up ℕ)).obj
        ((P.mapHomologicalComplex (.up ℕ)).obj L)).homology n) ≅
        Q.obj (((P.mapHomologicalComplex (.up ℕ)).obj L).homology n) :=
    ShortComplex.mapHomologyIso ((P.mapHomologicalComplex (.up ℕ) |>.obj L).sc n) Q
  have he := derivedSectionsTopIso_hom_naturality X F F' f n
  have he' : ((sections (⊤ : Opens X)).rightDerived n).map f ≫ eF'.hom =
      eF.hom ≫ Q.map ((P.rightDerived n).map f) := by
    simpa only [eF, eF'] using he
  have hr := TopCat.Sheaf.flasqueResolutionRightDerivedIso_hom_naturality
    (toPoint X) a b f φ hφ hK hL n
  let ψ := (P.mapHomologicalComplex (.up ℕ)).map φ
  have hq := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) n).map ψ) Q
  have hsection :
      HomologicalComplex.homologyMap
          ((Q.mapHomologicalComplex (.up ℕ)).map ψ) n =
        HomologicalComplex.homologyMap
          (((sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).map φ) n := by
    rfl
  have hq' : Q.map (HomologicalComplex.homologyMap ψ n) ≫ hF'.inv =
      hF.inv ≫ HomologicalComplex.homologyMap
        ((Q.mapHomologicalComplex (.up ℕ)).map ψ) n := by
    convert hq using 1 <;> rfl
  have hbase : Q.map ((P.rightDerived n).map f) ≫ Q.map rF'.hom ≫ hF'.inv =
      Q.map rF.hom ≫ hF.inv ≫ HomologicalComplex.homologyMap
        ((Q.mapHomologicalComplex (.up ℕ)).map ψ) n := by
    calc
      _ = Q.map ((P.rightDerived n).map f ≫ rF'.hom) ≫ hF'.inv := by
        simp only [Functor.map_comp, Category.assoc]
      _ = Q.map (rF.hom ≫ HomologicalComplex.homologyMap ψ n) ≫ hF'.inv := by
        rw [hr]
      _ = (Q.map rF.hom ≫ Q.map (HomologicalComplex.homologyMap ψ n)) ≫ hF'.inv := by
        rw [Functor.map_comp]
      _ = Q.map rF.hom ≫ (Q.map (HomologicalComplex.homologyMap ψ n) ≫ hF'.inv) := by
        simp only [Category.assoc]
      _ = _ := by
        rw [hq']
  change ((sections (⊤ : Opens X)).rightDerived n).map f ≫
      (eF' ≪≫ Q.mapIso rF' ≪≫ hF'.symm).hom =
    (eF ≪≫ Q.mapIso rF ≪≫ hF.symm).hom ≫
      HomologicalComplex.homologyMap
        (((sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).map φ) n
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  have heComp := congrArg (fun z => z ≫ Q.map rF'.hom ≫ hF'.inv) he'
  have hbaseComp : eF.hom ≫ Q.map ((P.rightDerived n).map f) ≫
      Q.map rF'.hom ≫ hF'.inv =
      eF.hom ≫ Q.map rF.hom ≫ hF.inv ≫
        HomologicalComplex.homologyMap
          ((Q.mapHomologicalComplex (.up ℕ)).map ψ) n := by
    simpa only [Category.assoc] using congrArg (fun t => eF.hom ≫ t) hbase
  have hsectionComp : eF.hom ≫ Q.map rF.hom ≫ hF.inv ≫
      HomologicalComplex.homologyMap
        ((Q.mapHomologicalComplex (.up ℕ)).map ψ) n =
      eF.hom ≫ Q.map rF.hom ≫ hF.inv ≫
        HomologicalComplex.homologyMap
          (((sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).map φ) n :=
    congrArg (fun t => eF.hom ≫ Q.map rF.hom ≫ hF.inv ≫ t) hsection
  calc
    _ = (eF.hom ≫ Q.map ((P.rightDerived n).map f)) ≫
        Q.map rF'.hom ≫ hF'.inv := by
      simpa only [Category.assoc] using heComp
    _ = eF.hom ≫ Q.map rF.hom ≫ hF.inv ≫
        HomologicalComplex.homologyMap
          ((Q.mapHomologicalComplex (.up ℕ)).map ψ) n := by
      exact hbaseComp
    _ = eF.hom ≫ Q.map rF.hom ≫ hF.inv ≫
        HomologicalComplex.homologyMap
          (((sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).map φ) n := by
      exact hsectionComp
    _ = _ := by
      rfl

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
