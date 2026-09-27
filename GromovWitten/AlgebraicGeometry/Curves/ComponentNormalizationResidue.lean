/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TotalNormalization
import GromovWitten.AlgebraicGeometry.Curves.ComponentGenericResidue

/-!
# Component normalization and generic residue fields

The normalization of an integral component agrees, over the ambient curve, with
normalization relative to the residue field of its generic image. The comparison
uses integral postcomposition and the generic residue-field isomorphism.
-/

open CategoryTheory Limits AlgebraicGeometry Topology
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
variable {A B Y X : Scheme.{u}} (g : A ⟶ Y) (i : Y ⟶ X)
  [IsIntegralHom i] [QuasiCompact g] [QuasiSeparated g]
  (r : B ⟶ X) [QuasiCompact r] [QuasiSeparated r] (e : A ≅ B) (h : e.hom ≫ r = g ≫ i)

/-- Relative normalization is unchanged by a generic source isomorphism and
integral postcomposition. -/
private def normalizationComposeIso : g.normalization ≅ r.normalization :=
  (Scheme.Hom.normalizationIntegralPostcompIso g i).symm ≪≫
    (Scheme.Hom.normalizationCongr h).symm ≪≫
    Scheme.Hom.normalizationPrecompIso r e

private lemma normalizationCongr_inv_projection {f g : A ⟶ X} [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] (h : f = g) :
    (Scheme.Hom.normalizationCongr h).inv ≫ f.fromNormalization = g.fromNormalization := by
  apply (Iso.inv_comp_eq _).mpr
  exact (Scheme.Hom.normalizationCongr_hom_fromNormalization h).symm

private lemma normalizationComposeIso_projection :
    (normalizationComposeIso g i r e h).hom ≫ r.fromNormalization =
      g.fromNormalization ≫ i := by
  dsimp only [normalizationComposeIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [Scheme.Hom.normalizationPrecompIso_hom_fromNormalization,
    normalizationCongr_inv_projection,
    Scheme.Hom.normalizationIntegralPostcompIso_inv_fromNormalization]

variable {C : Scheme.{u}} [IsIntegral C] (j : C ⟶ X)
  [IsIntegralHom j] [SurjectiveOnStalks j]

/-- Normalize an integral scheme through the residue field of its generic image. -/
def integralImmersionNormalizationResidueIso : Normalization.scheme C ≅
    (X.fromSpecResidueField (j (genericPoint C))).normalization :=
  normalizationComposeIso (Normalization.genericPointMap C) j _ _
    (genericFunctionFieldResidueSpecIso_commutes j)

lemma integralImmersionNormalizationResidueIso_hom_toCurve :
    (integralImmersionNormalizationResidueIso j).hom ≫
      (X.fromSpecResidueField (j (genericPoint C))).fromNormalization =
        Normalization.toCurve C ≫ j :=
  normalizationComposeIso_projection _ _ _ _ _
variable {K : Type u} [Field K] (f : X ⟶ Spec (.of K)) [PrestableFamily f]

set_option backward.isDefEq.respectTransparency false in
/-- The normalized component as a relative normalization over the ambient curve. -/
def componentNormalizationResidueIso (C : Component X) :
    normalizedComponentScheme f C ≅
      (X.fromSpecResidueField
        (componentInclusion f C (componentGenericPoint f C))).normalization := by
  let _ : IsNoetherian X := isNoetherian_of_quasiCompact f
  let _ := componentScheme_isIntegral f C
  let i := componentInclusion f C
  let _ : IsClosedImmersion i := by
    change IsClosedImmersion (X.irreducibleComponentIdeal C C.property).radical.subschemeι
    infer_instance
  exact integralImmersionNormalizationResidueIso i

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)] lemma componentNormalizationResidueIso_hom_toCurve (C : Component X) :
    (componentNormalizationResidueIso f C).hom ≫
      (X.fromSpecResidueField
        (componentInclusion f C (componentGenericPoint f C))).fromNormalization =
        normalizedComponentToCurve f C := by
  let _ : IsNoetherian X := isNoetherian_of_quasiCompact f
  let _ := componentScheme_isIntegral f C
  let i := componentInclusion f C
  let _ : IsClosedImmersion i := by
    change IsClosedImmersion (X.irreducibleComponentIdeal C C.property).radical.subschemeι
    infer_instance
  exact integralImmersionNormalizationResidueIso_hom_toCurve i

end
end GromovWitten.AlgebraicGeometry.Curves
