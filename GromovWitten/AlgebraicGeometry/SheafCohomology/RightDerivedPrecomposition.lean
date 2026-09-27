/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.ComparisonUniqueness
/-!
# Derivation and exact precomposition

An exact functor sends an injective resolution to an exact augmented complex. Comparing
that complex to a target injective resolution induces the canonical map
`Rⁿ(L ⋙ F) ⟶ L ⋙ RⁿF`. Uniqueness up to homotopy makes the comparison natural even when
`L` does not preserve injective objects.
-/

open CategoryTheory Limits HomologicalComplex
noncomputable section
namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [EnoughInjectives C] [EnoughInjectives D]
    (L : C ⥤ D) [L.Additive] [L.PreservesHomology]
private def resolutionAug (A : C) :
    (CochainComplex.single₀ D).obj (L.obj A) ⟶
      (L.mapHomologicalComplex (.up ℕ)).obj (injectiveResolution A).cocomplex :=
  (singleMapHomologicalComplex L (.up ℕ) 0).inv.app A ≫
    (L.mapHomologicalComplex (.up ℕ)).map (injectiveResolution A).ι
private instance (A : C) : QuasiIso (resolutionAug L A) := by
  dsimp [resolutionAug]
  infer_instance
private def resolutionComparison (A : C) :
    (L.mapHomologicalComplex (.up ℕ)).obj (injectiveResolution A).cocomplex ⟶
      (injectiveResolution (L.obj A)).cocomplex :=
  ((injectiveResolution (L.obj A)).exists_desc_of_quasiIso (resolutionAug L A)).choose
private lemma resolutionComparison_comm (A : C) :
    resolutionAug L A ≫ resolutionComparison L A = (injectiveResolution (L.obj A)).ι :=
  ((injectiveResolution (L.obj A)).exists_desc_of_quasiIso (resolutionAug L A)).choose_spec.1

omit [EnoughInjectives D] [L.PreservesHomology] in
set_option backward.isDefEq.respectTransparency false in
private lemma resolutionAug_naturality {A B : C} (f : A ⟶ B) :
    resolutionAug L A ≫ (L.mapHomologicalComplex (.up ℕ)).map
      (InjectiveResolution.desc f (injectiveResolution B) (injectiveResolution A)) =
        (CochainComplex.single₀ D).map (L.map f) ≫ resolutionAug L B := by
  dsimp only [resolutionAug]
  rw [Category.assoc, ← Functor.map_comp, InjectiveResolution.desc_commutes,
    Functor.map_comp, ← Category.assoc]
  simpa only [Category.assoc, Functor.comp_obj, Functor.comp_map, CochainComplex.single₀] using
    congrArg (fun t => t ≫ (L.mapHomologicalComplex (.up ℕ)).map
    (injectiveResolution B).ι)
    ((singleMapHomologicalComplex L (.up ℕ) 0).inv.naturality f).symm

set_option backward.isDefEq.respectTransparency false in
/-- Apply an exact functor to an injective resolution and compare to the target resolution. -/
def resolutionPrecompComparison :
    L.rightDerivedToHomotopyCategory ⟶ L ⋙ injectiveResolutions D where
  app A := (HomotopyCategory.quotient _ _).map (resolutionComparison L A)
  naturality A B f := by
    change (L.mapHomotopyCategory (.up ℕ)).map
      ((HomotopyCategory.quotient _ _).map
        (InjectiveResolution.desc f (injectiveResolution B) (injectiveResolution A))) ≫ _ = _
    rw [Functor.mapHomotopyCategory_map, ← Functor.map_comp]
    change (HomotopyCategory.quotient _ _).map _ =
      (HomotopyCategory.quotient _ _).map (resolutionComparison L A) ≫
        (HomotopyCategory.quotient _ _).map
          (InjectiveResolution.desc (L.map f) (injectiveResolution (L.obj B))
            (injectiveResolution (L.obj A)))
    rw [← Functor.map_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply Classical.choice (CochainComplex.nonempty_homotopy_of_precomp_quasiIso_nat
      (resolutionAug L A) _ _ ?_)
    rw [← Category.assoc, resolutionAug_naturality, Category.assoc, resolutionComparison_comm,
      ← Category.assoc, resolutionComparison_comm, InjectiveResolution.desc_commutes]

/-- Any comparison extending the augmentation represents the same homotopy-category map. -/
lemma resolutionPrecompComparison_app_eq (A : C)
    (φ : (L.mapHomologicalComplex (.up ℕ)).obj (injectiveResolution A).cocomplex ⟶
      (injectiveResolution (L.obj A)).cocomplex)
    (hφ : (singleMapHomologicalComplex L (.up ℕ) 0).inv.app A ≫
      (L.mapHomologicalComplex (.up ℕ)).map (injectiveResolution A).ι ≫ φ =
        (injectiveResolution (L.obj A)).ι) :
    (resolutionPrecompComparison L).app A = (HomotopyCategory.quotient _ _).map φ := by
  apply HomotopyCategory.eq_of_homotopy
  apply Classical.choice (CochainComplex.nonempty_homotopy_of_precomp_quasiIso_nat
    (resolutionAug L A) _ _ ?_)
  rw [resolutionComparison_comm]
  simpa only [resolutionAug, Category.assoc] using hφ.symm

variable {E : Type*} [Category E] [Abelian E] (F : D ⥤ E) [F.Additive]
/-- Comparison from deriving a composite to exact precomposition of the derived functor. -/
def rightDerivedPrecompComparison (n : ℕ) :
    (L ⋙ F).rightDerived n ⟶ L ⋙ F.rightDerived n :=
  whiskerRight
    ((isoWhiskerLeft (injectiveResolutions C)
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ F)) (.up ℕ))).inv ≫
        whiskerRight (resolutionPrecompComparison L) (F.mapHomotopyCategory (.up ℕ)))
    (HomotopyCategory.homologyFunctor E (.up ℕ) n)
end CategoryTheory.Functor
