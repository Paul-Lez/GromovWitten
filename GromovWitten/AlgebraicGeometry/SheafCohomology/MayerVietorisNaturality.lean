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

end GromovWitten.AlgebraicGeometry.SheafCohomology
