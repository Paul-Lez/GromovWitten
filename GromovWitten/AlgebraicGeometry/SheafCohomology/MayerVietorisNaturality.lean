/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.MayerVietorisSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Naturality of the Mayer–Vietoris connecting map

A sheaf morphism lifts to a map of the chosen injective resolutions. Naturality
of the homology connecting map then gives a natural transformation on actual
derived section functors.
-/

open CategoryTheory CategoryTheory.Abelian
open TopologicalSpace Opposite

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {X : TopCat.{u}}

private def sectionsComplexMVMap
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ}
    (φ : K ⟶ L) (U V : Opens X) :
    sectionsComplexMV K U V ⟶ sectionsComplexMV L U V where
  τ₁ := ((sections (U ⊔ V)).mapHomologicalComplex (.up ℕ)).map φ
  τ₂ := ((sectionsPairFunctor U V).mapHomologicalComplex (.up ℕ)).map φ
  τ₃ := ((sections (U ⊓ V)).mapHomologicalComplex (.up ℕ)).map φ
  comm₁₂ := ((NatTrans.mapHomologicalComplex (sectionsToPairNat U V) (.up ℕ)).naturality φ)
  comm₂₃ := ((NatTrans.mapHomologicalComplex (sectionsFromPairNat U V) (.up ℕ)).naturality φ)

set_option backward.isDefEq.respectTransparency false in
/-- The Mayer–Vietoris connecting map is natural in the sheaf. -/
lemma mvRightDerivedConnecting_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (U V : Opens X) (n : ℕ) :
    ((sections (U ⊓ V)).rightDerived n).map f ≫
      mvRightDerivedConnecting (F := G) U V n =
    mvRightDerivedConnecting (F := F) U V n ≫
      ((sections (U ⊔ V)).rightDerived (n + 1)).map f := by
  let I := InjectiveResolution.of F
  let J := InjectiveResolution.of G
  let φ := InjectiveResolution.desc f J I
  let hI := sectionsComplexMV_shortExact I.cocomplex
    (fun k => TopCat.Sheaf.isFlasque_of_injective X _) U V
  let hJ := sectionsComplexMV_shortExact J.cocomplex
    (fun k => TopCat.Sheaf.isFlasque_of_injective X _) U V
  let eCI := I.isoRightDerivedHomologyObj (sections (U ⊓ V)) n
  let eCJ := J.isoRightDerivedHomologyObj (sections (U ⊓ V)) n
  let eAI := I.isoRightDerivedHomologyObj (sections (U ⊔ V)) (n + 1)
  let eAJ := J.isoRightDerivedHomologyObj (sections (U ⊔ V)) (n + 1)
  let hrel : (ComplexShape.up ℕ).Rel n (n + 1) := by rfl
  have hw := InjectiveResolution.desc_commutes f J I
  rw [I.rightDerived_map_eq_homologyMap J f φ hw,
      I.rightDerived_map_eq_homologyMap J f φ hw]
  change (eCI.hom ≫ _ ≫ eCJ.inv) ≫ (eCJ.hom ≫ hJ.δ n (n + 1) hrel ≫ eAJ.inv) =
    (eCI.hom ≫ hI.δ n (n + 1) hrel ≫ eAI.inv) ≫ (eAI.hom ≫ _ ≫ eAJ.inv)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hn := HomologicalComplex.HomologySequence.δ_naturality
    (sectionsComplexMVMap φ U V) hI hJ n (n + 1) hrel
  dsimp only [sectionsComplexMVMap] at hn
  simpa only [Category.assoc] using
    congrArg (fun k => eCI.hom ≫ k ≫ eAJ.inv) hn.symm

/-- The natural connecting transformation in the derived Mayer–Vietoris sequence. -/
noncomputable def mvRightDerivedConnectingNat (U V : Opens X) (n : ℕ) :
    (sections (U ⊓ V)).rightDerived n ⟶
      (sections (U ⊔ V)).rightDerived (n + 1) where
  app F := mvRightDerivedConnecting (F := F) U V n
  naturality _ _ f := mvRightDerivedConnecting_naturality f U V n

/-- The mvRightDerivedConnecting map can be computed with any injective resolution. -/
lemma mvRightDerivedConnecting_eq
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (U V : Opens X) (n : ℕ) :
    mvRightDerivedConnecting (F := F) U V n =
      (I.isoRightDerivedHomologyObj (sections (U ⊓ V)) n).hom ≫
        (sectionsComplexMV_shortExact I.cocomplex
          (fun _ => TopCat.Sheaf.isFlasque_of_injective X _) U V).δ n (n + 1) (by rfl) ≫
        (I.isoRightDerivedHomologyObj (sections (U ⊔ V)) (n + 1)).inv := by
  let J := InjectiveResolution.of F
  let φ := InjectiveResolution.desc (𝟙 F) J I
  let φS := sectionsComplexMVMap φ U V
  have hφ : I.ι ≫ φ = (CochainComplex.single₀ _).map (𝟙 F) ≫ J.ι := by
    exact InjectiveResolution.desc_commutes (𝟙 F) J I
  let hSI := sectionsComplexMV_shortExact I.cocomplex
    (fun _ => TopCat.Sheaf.isFlasque_of_injective X _) U V
  let hSJ := sectionsComplexMV_shortExact J.cocomplex
    (fun _ => TopCat.Sheaf.isFlasque_of_injective X _) U V
  dsimp [sectionsComplexMV] at hSI hSJ
  let eI0 := I.isoRightDerivedHomologyObj (sections (U ⊓ V)) n
  let eJ0 := J.isoRightDerivedHomologyObj (sections (U ⊓ V)) n
  let eIn := I.isoRightDerivedHomologyObj (sections (U ⊔ V)) (n + 1)
  let eJn := J.isoRightDerivedHomologyObj (sections (U ⊔ V)) (n + 1)
  let p0 := HomologicalComplex.homologyMap
    (((sections (U ⊓ V)).mapHomologicalComplex (.up ℕ)).map φ) n
  let pn := HomologicalComplex.homologyMap
    (((sections (U ⊔ V)).mapHomologicalComplex (.up ℕ)).map φ) (n + 1)
  have hQ0 := I.rightDerived_map_eq_homologyMap J (𝟙 F) φ hφ
    (sections (U ⊓ V)) n
  have hQn := I.rightDerived_map_eq_homologyMap J (𝟙 F) φ hφ
    (sections (U ⊔ V)) (n + 1)
  have hQ0' : eI0.hom ≫ p0 ≫ eJ0.inv = 𝟙 _ := by
    simpa [eI0, eJ0, p0] using hQ0.symm
  have hQn' : eIn.hom ≫ pn ≫ eJn.inv = 𝟙 _ := by
    simpa [eIn, eJn, pn] using hQn.symm
  have hQ0_hom : eI0.hom ≫ p0 = eJ0.hom := by
    calc
      eI0.hom ≫ p0 = (eI0.hom ≫ p0 ≫ eJ0.inv) ≫ eJ0.hom := by simp
      _ = (𝟙 _) ≫ eJ0.hom := by rw [hQ0']
      _ = eJ0.hom := by simp
  have hQn_inv : pn ≫ eJn.inv = eIn.inv := by
    calc
      pn ≫ eJn.inv = eIn.inv ≫ eIn.hom ≫ pn ≫ eJn.inv := by simp
      _ = eIn.inv ≫ (eIn.hom ≫ pn ≫ eJn.inv) := by simp
      _ = eIn.inv ≫ 𝟙 _ := by rw [hQn']
      _ = eIn.inv := by simp
  let hrel : (ComplexShape.up ℕ).Rel n (n + 1) := by rfl
  have hδ := HomologicalComplex.HomologySequence.δ_naturality φS hSI hSJ n (n + 1) hrel
  have hδ' : hSI.δ n (n + 1) hrel ≫ pn =
      p0 ≫ hSJ.δ n (n + 1) hrel := by
    simpa [φS, sectionsComplexMVMap, p0, pn, sectionsComplexMV] using hδ
  dsimp [mvRightDerivedConnecting]
  change eJ0.hom ≫ hSJ.δ n (n + 1) hrel ≫ eJn.inv =
    eI0.hom ≫ hSI.δ n (n + 1) hrel ≫ eIn.inv
  calc
    eJ0.hom ≫ hSJ.δ n (n + 1) hrel ≫ eJn.inv =
        eI0.hom ≫ p0 ≫ hSJ.δ n (n + 1) hrel ≫ eJn.inv := by
          rw [← hQ0_hom]
          simp [Category.assoc]
    _ = eI0.hom ≫ (p0 ≫ hSJ.δ n (n + 1) hrel) ≫ eJn.inv := by simp [Category.assoc]
    _ = eI0.hom ≫ (hSI.δ n (n + 1) hrel ≫ pn) ≫ eJn.inv := by rw [hδ']
    _ = eI0.hom ≫ hSI.δ n (n + 1) hrel ≫ (pn ≫ eJn.inv) := by simp [Category.assoc]
    _ = eI0.hom ≫ hSI.δ n (n + 1) hrel ≫ eIn.inv := by rw [hQn_inv]

end GromovWitten.AlgebraicGeometry.SheafCohomology
