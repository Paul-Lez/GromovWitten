/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TotalNormalization
import GromovWitten.AlgebraicGeometry.Curves.NormalizationSigma
import GromovWitten.AlgebraicGeometry.Curves.ComponentNormalizationResidue

open CategoryTheory Limits AlgebraicGeometry Topology

namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable {f : X ⟶ Spec (.of K)} [PrestableFamily f] [IsNoetherian X]

omit [AlgebraicGeometry.IsNoetherian X] in
theorem componentGenericPoint_eq (C : Component X) :
    componentGenericPoint f C =
      @genericPoint (componentScheme f C) _ _ (componentScheme_isIrreducibleSpace f C) := rfl

noncomputable abbrev componentToGenericPoint (C : Component X) : GenericPointSet X :=
  ⟨componentInclusion f C (componentGenericPoint f C), by
    rw [componentInclusion_genericPoint_closure f C]
    exact C.2⟩

omit [AlgebraicGeometry.IsNoetherian X] in
theorem componentToGenericPoint_component (C : Component X) :
    genericPoints.component (componentToGenericPoint (f := f) C) = C := by
  apply Subtype.ext
  change closure {(componentToGenericPoint (f := f) C).val} = (C : Set X)
  exact componentInclusion_genericPoint_closure f C

noncomputable def componentGenericPointEquiv : Component X ≃ GenericPointSet X where
  toFun := fun C => componentToGenericPoint (f := f) C
  invFun := genericPoints.component
  left_inv C := componentToGenericPoint_component (f := f) C
  right_inv x := by
    apply genericPoints.component_injective
    exact componentToGenericPoint_component (f := f) (genericPoints.component x)

abbrev componentNormalizationFamily (C : Component X) : Scheme :=
  normalizedComponentScheme f C

abbrev genericResidueNormalizationFamily (x : GenericPointSet X) : Scheme :=
  (X.fromSpecResidueField x.val).normalization

abbrev genericSummandFamily (x : GenericPointSet X) : Scheme :=
  (Sigma.ι (genericPointSpectrum X) x ≫ genericPointsToScheme X).normalization

omit [AlgebraicGeometry.IsNoetherian X] in
lemma genericPointSummand_eq (x : GenericPointSet X) :
    Sigma.ι (genericPointSpectrum X) x ≫ genericPointsToScheme X =
      X.fromSpecResidueField x.val := by
  simp [genericPointsToScheme]

omit [AlgebraicGeometry.IsNoetherian X] in
lemma componentGenericPointEquiv_val (C : Component X) :
    (componentGenericPointEquiv (f := f) C).val =
      componentInclusion f C (componentGenericPoint f C) := rfl

noncomputable def componentNormalizationIsoFamily (C : Component X) :
    componentNormalizationFamily (f := f) C ≅
      (genericResidueNormalizationFamily (X := X) ∘
        componentGenericPointEquiv (f := f)) C := by
  change normalizedComponentScheme f C ≅
    (X.fromSpecResidueField
      (componentInclusion f C (componentGenericPoint f C))).normalization
  exact componentNormalizationResidueIso f C

omit [AlgebraicGeometry.IsNoetherian X] in
theorem componentNormalizationIsoFamily_hom_toCurve
    (C : Component X) :
    (componentNormalizationIsoFamily (f := f) C).hom ≫
        (X.fromSpecResidueField (componentGenericPointEquiv (f := f) C).val).fromNormalization =
      normalizedComponentToCurve f C := by
  exact componentNormalizationResidueIso_hom_toCurve f C

noncomputable def genericPointSigmaIso :
    (∐ fun C : Component X => componentNormalizationFamily (f := f) C) ≅
      ∐ genericSummandFamily (X := X) := by
  let e := componentGenericPointEquiv (f := f)
  let qIso : ∀ x : GenericPointSet X,
      genericResidueNormalizationFamily (X := X) x ≅
        genericSummandFamily (X := X) x := fun x => by
    change (X.fromSpecResidueField x.val).normalization ≅
      (Sigma.ι (genericPointSpectrum X) x ≫ genericPointsToScheme X).normalization
    exact Scheme.Hom.normalizationCongr (genericPointSummand_eq (X := X) x).symm
  exact Sigma.mapIso (componentNormalizationIsoFamily (f := f)) ≪≫
    Sigma.reindex e (genericResidueNormalizationFamily (X := X)) ≪≫
    Sigma.mapIso qIso

noncomputable def componentToTotalNormalization :
    NormalizedComponents.Point (f := f) ≃ totalNormalization X := by
  haveI : Fintype (GenericPointSet X) := Fintype.ofFinite _
  let h := genericPointSigmaIso (f := f)
  let n := Scheme.Hom.normalizationSigmaIso (genericPointsToScheme X)
  let t := h ≪≫ n
  exact (sigmaMk (fun C : Component X => componentNormalizationFamily (f := f) C)).toEquiv.trans
    (Equiv.ofBijective t.hom (ConcreteCategory.bijective_of_isIso _))

theorem componentToTotalNormalization_toScheme
    (p : NormalizedComponents.Point (f := f)) :
    totalNormalizationToScheme X (componentToTotalNormalization (f := f) p) =
      NormalizedComponents.pointToCurve (f := f) p := by
  let h := genericPointSigmaIso (f := f)
  let n := Scheme.Hom.normalizationSigmaIso (genericPointsToScheme X)
  have hc (C : Component X) :
      Sigma.ι (fun C : Component X => componentNormalizationFamily (f := f) C) C ≫
          h.hom ≫ n.hom ≫ totalNormalizationToScheme X =
        normalizedComponentToCurve f C := by
    dsimp only [h, n, genericPointSigmaIso, Iso.trans_hom,
      totalNormalizationToScheme]
    simp only [Category.assoc]
    rw [Sigma.ι_mapIso_hom_assoc]
    rw [Sigma.ι_reindex_hom_assoc]
    rw [Sigma.ι_mapIso_hom_assoc]
    rw [Scheme.Hom.sigma_ι_normalizationSigmaIso_hom_fromNormalization]
    change (componentNormalizationIsoFamily (f := f) C).hom ≫
      (Scheme.Hom.normalizationCongr
        (genericPointSummand_eq (X := X)
          (componentGenericPointEquiv (f := f) C)).symm).hom ≫
      (Sigma.ι (genericPointSpectrum X)
        (componentGenericPointEquiv (f := f) C) ≫ genericPointsToScheme X).fromNormalization = _
    rw [Scheme.Hom.normalizationCongr_hom_fromNormalization]
    exact componentNormalizationIsoFamily_hom_toCurve (f := f) C
  change totalNormalizationToScheme X
      ((h.hom ≫ n.hom) (sigmaMk
        (fun C : Component X => componentNormalizationFamily (f := f) C) ⟨p.1, p.2⟩)) = _
  rw [sigmaMk_mk, ← Scheme.Hom.comp_apply]
  change (Sigma.ι (fun C : Component X => componentNormalizationFamily (f := f) C) p.1 ≫
      h.hom ≫ n.hom ≫ totalNormalizationToScheme X) p.2 = _
  rw [hc p.1]
  rfl

end
end GromovWitten.AlgebraicGeometry.Curves
