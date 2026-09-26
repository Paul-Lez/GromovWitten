/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TotalNormalization
import GromovWitten.AlgebraicGeometry.Curves.ComponentGenericResidue
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ModelNormalizationGeneric

/-!
# Total normalization of normal schemes

For an integral scheme the generic-point coproduct reduces to its function-field point.
This identifies total normalization with ordinary normalization and proves that its map is
an isomorphism for a normal integral scheme. The isomorphism property passes to étale charts.
-/

open CategoryTheory Limits AlgebraicGeometry Topology
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
variable (X : Scheme.{u}) [IsIntegral X]

instance uniqueGenericPointSet : Unique (GenericPointSet X) where
  default := ⟨genericPoint X, by rw [genericPoint_spec X, irreducibleComponents_eq_singleton]; rfl⟩
  uniq x := by
    apply Subtype.ext
    apply eq_of_specializes_generic (show closure {genericPoint X} ∈ irreducibleComponents X by
      rw [genericPoint_spec X, irreducibleComponents_eq_singleton]; rfl)
    apply specializes_iff_mem_closure.mpr
    have h : closure {x.val} = Set.univ := by
      simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using x.property
    rw [h]
    trivial

set_option backward.isDefEq.respectTransparency false in
def integralGenericPointIso : Spec X.functionField ≅ genericPointCoproduct X :=
  genericFunctionFieldResidueSpecIso (𝟙 X) ≪≫
    (coproductUniqueIso (genericPointSpectrum X)).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)] lemma integralGenericPointIso_hom_toScheme :
    (integralGenericPointIso X).hom ≫ genericPointsToScheme X =
      Normalization.genericPointMap X := by
  simp only [integralGenericPointIso, Iso.trans_hom, Iso.symm_hom,
    coproductUniqueIso_inv, Category.assoc, genericPointsToScheme, Sigma.ι_desc]
  change (genericFunctionFieldResidueSpecIso (𝟙 X)).hom ≫
    X.fromSpecResidueField (genericPoint X) = X.fromSpecStalk (genericPoint X)
  have h := genericFunctionFieldResidueSpecIso_commutes (𝟙 X)
  rw [Category.comp_id] at h
  exact h

variable [IsNoetherian X]

def totalNormalizationIntegralIso : Normalization.scheme X ≅ totalNormalization X :=
  (Scheme.Hom.normalizationCongr (integralGenericPointIso_hom_toScheme X)).symm ≪≫
    Scheme.Hom.normalizationPrecompIso (genericPointsToScheme X) (integralGenericPointIso X)

@[reassoc (attr := simp)] lemma totalNormalizationIntegralIso_hom_toScheme :
    (totalNormalizationIntegralIso X).hom ≫ totalNormalizationToScheme X =
      Normalization.toCurve X := by
  dsimp only [totalNormalizationIntegralIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Scheme.Hom.normalizationPrecompIso_hom_fromNormalization]
  apply (Iso.inv_comp_eq _).mpr
  exact (Scheme.Hom.normalizationCongr_hom_fromNormalization
    (integralGenericPointIso_hom_toScheme X)).symm

lemma totalNormalizationToScheme_isIso_of_normal (h : IsNormalScheme X) :
    IsIso (totalNormalizationToScheme X) := by
  let _ := Normalization.isIso_toCurve_of_isNormalScheme X h
  have hi : IsIso ((totalNormalizationIntegralIso X).hom ≫
      totalNormalizationToScheme X) := by
    rw [totalNormalizationIntegralIso_hom_toScheme]
    infer_instance
  exact (isIso_comp_left_iff (totalNormalizationIntegralIso X).hom
    (totalNormalizationToScheme X)).mp hi

end
end GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves
universe u
lemma totalNormalizationToScheme_isIso_of_etale {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [Etale f]
    [IsIso (totalNormalizationToScheme Y)] : IsIso (totalNormalizationToScheme X) := by
  have hi : IsIso ((totalNormalizationEtaleIso f).hom ≫
      pullback.snd (totalNormalizationToScheme Y) f) := inferInstance
  rwa [totalNormalizationEtaleIso_hom_snd] at hi
end GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
theorem spec_isNormalScheme (R : Type u) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] :
    IsNormalScheme (Spec (.of R)) := by
  let X : Scheme := Spec (.of R)
  let _ : IsIntegral X := by infer_instance
  intro U hne
  let hU : IsAffineOpen U.1 := U.2
  let B := Γ(X, U.1)
  let _ : IsDomain B := inferInstance
  let xu (P : Ideal B) [P.IsMaximal] : U.1 := by
    change Ideal Γ(X, U.1) at P
    let p : Spec Γ(X, U.1) := ⟨P, inferInstance⟩
    refine ⟨hU.fromSpec p, by
      change hU.fromSpec p ∈ (U.1 : Set X)
      rw [← hU.range_fromSpec]
      exact ⟨p, rfl⟩⟩
  let Rₚ (P : Ideal B) [P.IsMaximal] : Type u :=
    (X.presheaf.stalk (xu P).1).carrier
  let _ (P : Ideal B) [P.IsMaximal] : Algebra B (Rₚ P) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (xu P)
  let _ (P : Ideal B) [P.IsMaximal] : IsLocalization.AtPrime (Rₚ P) P := by
    let hloc := hU.isLocalization_stalk (xu P)
    let p : Spec Γ(X, U.1) := ⟨P, inferInstance⟩
    have hfrom : hU.fromSpec (hU.primeIdealOf (xu P)) = hU.fromSpec p := by
      calc
        hU.fromSpec (hU.primeIdealOf (xu P)) = (xu P).1 :=
          hU.fromSpec_primeIdealOf _
        _ = hU.fromSpec p := rfl
    have hp : hU.primeIdealOf (xu P) = p :=
      hU.fromSpec.isOpenEmbedding.injective hfrom
    simpa only [Rₚ, hp] using hloc
  refine IsIntegrallyClosed.of_isLocalization_maximal (Rₚ := Rₚ) (fun P _ => ?_)
  change Ideal Γ(X, U.1) at P
  let p : Spec (Γ(X, U.1)) := ⟨P, inferInstance⟩
  let x : U.1 := xu P
  let _ : Algebra B (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let htop : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  let xtop : (⊤ : X.Opens) := ⟨x.1, Set.mem_univ _⟩
  let q := htop.primeIdealOf xtop
  let _ : Algebra (Γ(X, (⊤ : X.Opens))) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf xtop
  let _ : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal :=
    htop.isLocalization_stalk xtop
  have htopIC : IsIntegrallyClosed (Γ(X, (⊤ : X.Opens))) := by
    exact IsIntegrallyClosed.of_equiv
      (h := (inferInstance : IsIntegrallyClosed R))
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  let _ : IsIntegrallyClosed (Γ(X, (⊤ : X.Opens))) := htopIC
  change IsIntegrallyClosed (X.presheaf.stalk x)
  exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
    q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors

end
end GromovWitten.AlgebraicGeometry.Curves
