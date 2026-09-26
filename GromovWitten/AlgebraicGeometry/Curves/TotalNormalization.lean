/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import GromovWitten.AlgebraicGeometry.Curves.NormalizedComponentIso
import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.RingTheory.Unramified.Field

/-!
# Normalization in all generic residue fields

For a Noetherian scheme, take the relative normalization in the coproduct of the residue
fields at its irreducible-component generic points. This construction commutes with étale
base change. The comparison is proved by identifying the generic-point coproduct after base
change, then applying the universal property of relative normalization. The final fibre
comparison applies when the residue-field map at the chosen point is an isomorphism.
-/

universe u
open CategoryTheory Limits AlgebraicGeometry Topology
namespace GromovWitten.AlgebraicGeometry.Curves
noncomputable section

/-- Generic points of the irreducible components, without an ordering of components. -/
abbrev GenericPointSet (X : Scheme.{u}) :=
  {x : X // closure {x} ∈ irreducibleComponents X}

lemma eq_of_specializes_generic {X : Scheme.{u}} {x y : X}
    (hy : closure {y} ∈ irreducibleComponents X) (h : x ⤳ y) : x = y := by
  have hh : closure {y} = closure {x} := hy.eq_of_le isIrreducible_singleton.closure
    (closure_minimal (Set.singleton_subset_iff.mpr h.mem_closure) isClosed_closure)
  exact (h.antisymm (specializes_iff_mem_closure.mpr (hh.symm ▸ subset_closure rfl))).eq

instance genericPointSet_finite (X : Scheme.{u}) [IsNoetherian X] : Finite (GenericPointSet X) := by
  let _ : Finite (irreducibleComponents X) := finite_component
  apply Finite.of_injective (fun x : GenericPointSet X ↦
    (⟨closure {x.val}, x.property⟩ : irreducibleComponents X))
  intro x y h
  apply Subtype.ext
  have hh := congrArg Subtype.val h
  exact eq_of_specializes_generic y.property
    (specializes_iff_mem_closure.mpr (by
      change closure {x.val} = closure {y.val} at hh
      rw [hh]
      exact subset_closure rfl))

instance genericPointSet_t1 (X : Scheme.{u}) : T1Space (GenericPointSet X) := by
  apply t1Space_iff_specializes_imp_eq.mpr
  intro x y h
  apply Subtype.ext
  exact eq_of_specializes_generic y.property (h.map continuous_subtype_val)

instance genericPointSet_discrete (X : Scheme.{u}) [IsNoetherian X] :
    DiscreteTopology (GenericPointSet X) := inferInstance

abbrev genericPointSpectrum (X : Scheme.{u}) (x : GenericPointSet X) : Scheme.{u} :=
  Spec (X.residueField x.val)

abbrev genericPointCoproduct (X : Scheme.{u}) : Scheme.{u} := ∐ genericPointSpectrum X

def genericPointsToScheme (X : Scheme.{u}) : genericPointCoproduct X ⟶ X :=
  Sigma.desc (fun x : GenericPointSet X ↦ X.fromSpecResidueField x.val)

@[simp] lemma genericPointsToScheme_sigmaMk (X : Scheme.{u})
    (x : GenericPointSet X) (p : genericPointSpectrum X x) :
    genericPointsToScheme X (sigmaMk (genericPointSpectrum X) ⟨x, p⟩) = x.val := by
  rw [sigmaMk_mk, ← Scheme.Hom.comp_apply]
  simp only [genericPointsToScheme, Sigma.ι_desc, Scheme.fromSpecResidueField_apply]

instance genericPointSpectrum_subsingleton (X : Scheme.{u}) (x : GenericPointSet X) :
    Subsingleton (genericPointSpectrum X x) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum (X.residueField x.val)))

instance genericPointCoproduct_finite (X : Scheme.{u}) [IsNoetherian X] :
    Finite (genericPointCoproduct X) :=
  (sigmaMk (genericPointSpectrum X)).toEquiv.finite_iff.mp inferInstance

instance genericPointsToScheme_surjectiveOnStalks (X : Scheme.{u}) :
    SurjectiveOnStalks (genericPointsToScheme X) := by
  exact IsZariskiLocalAtSource.sigmaDesc (fun x ↦
    inferInstanceAs (SurjectiveOnStalks (X.fromSpecResidueField x.val)))


instance genericPointCoproduct_discrete (X : Scheme.{u}) :
    DiscreteTopology (genericPointCoproduct X) :=
  (sigmaMk (genericPointSpectrum X)).discreteTopology_iff.mp inferInstance

def genericPointCoproductEquiv (X : Scheme.{u}) :
    genericPointCoproduct X ≃ GenericPointSet X where
  toFun q := ((sigmaMk (genericPointSpectrum X)).symm q).1
  invFun x := sigmaMk (genericPointSpectrum X)
    ⟨x, IsLocalRing.closedPoint (X.residueField x.val)⟩
  left_inv q := by
    obtain ⟨⟨x, p⟩, rfl⟩ := (sigmaMk (genericPointSpectrum X)).surjective q
    dsimp only
    rw [Homeomorph.symm_apply_apply]
    congr 1
    exact Sigma.mk.inj_iff.mpr ⟨rfl, heq_of_eq (Subsingleton.elim _ _)⟩
  right_inv x := by simp

@[simp] lemma genericPointCoproductEquiv_val (X : Scheme.{u}) (q : genericPointCoproduct X) :
    (genericPointCoproductEquiv X q).val = genericPointsToScheme X q := by
  obtain ⟨⟨x, p⟩, rfl⟩ := (sigmaMk (genericPointSpectrum X)).surjective q
  change ((sigmaMk (genericPointSpectrum X)).symm
    ((sigmaMk (genericPointSpectrum X)) ⟨x, p⟩)).1.val = _
  rw [Homeomorph.symm_apply_apply, genericPointsToScheme_sigmaMk]

instance genericPointsToScheme_isPreimmersion (X : Scheme.{u}) [IsNoetherian X] :
    IsPreimmersion (genericPointsToScheme X) where
  isEmbedding := by
    have hh : (fun q ↦ genericPointsToScheme X q) =
        (fun q ↦ (genericPointCoproductEquiv X q).val) := by
      funext q
      exact (genericPointCoproductEquiv_val X q).symm
    change IsEmbedding (fun q ↦ genericPointsToScheme X q)
    rw [hh]
    exact IsEmbedding.subtypeVal.comp
      (genericPointCoproductEquiv X).toHomeomorphOfDiscrete.isEmbedding
  stalkMap_surjective := (genericPointsToScheme X).stalkMap_surjective

instance genericPointsToScheme_quasiCompact (X : Scheme.{u}) [IsNoetherian X] :
    QuasiCompact (genericPointsToScheme X) := ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩

instance genericPointsToScheme_quasiSeparated (X : Scheme.{u}) [IsNoetherian X] :
    QuasiSeparated (genericPointsToScheme X) := inferInstance


instance genericPointCoproduct_isReduced (X : Scheme.{u}) :
    IsReduced (genericPointCoproduct X) := by
  let _ : ∀ x : (sigmaOpenCover (genericPointSpectrum X)).I₀,
      IsReduced ((sigmaOpenCover (genericPointSpectrum X)).X x) := by
    intro x
    change IsReduced (Spec (X.residueField x.val))
    infer_instance
  exact IsReduced.of_openCover _ (sigmaOpenCover (genericPointSpectrum X))

instance genericPointCoproduct_isLocallyArtinian (X : Scheme.{u}) :
    IsLocallyArtinian (genericPointCoproduct X) := by
  apply (isLocallyArtinian_iff_openCover (sigmaOpenCover (genericPointSpectrum X))).mpr
  intro x
  change IsLocallyArtinian (Spec (X.residueField x.val))
  infer_instance

end
end GromovWitten.AlgebraicGeometry.Curves

open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry

lemma isReduced_of_etale_to_field {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Etale f] : IsReduced X := by
  let _ (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    let Y := Spec (.of K)
    have hx : f x = genericPoint Y := Subsingleton.elim _ _
    have hfield : IsField (Y.presheaf.stalk (f x)) := by
      rw [hx]
      exact Field.toIsField Y.functionField
    let _ := hfield.toField
    algebraize [(f.stalkMap x).hom]
    let _ : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      LocallyOfFiniteType.stalkMap f x
    let _ : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      FormallyUnramified.stalkMap f x
    exact Algebra.FormallyUnramified.isReduced_of_field
      (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
  exact isReduced_of_isReduced_stalk X

lemma geometricallyReduced_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] :
    GeometricallyReduced f := by
  constructor
  intro K _ g P a b h
  let _ : Etale b := MorphismProperty.of_isPullback h ‹Etale f›
  exact isReduced_of_etale_to_field b

lemma isReduced_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    [IsReduced Y] [IsLocallyNoetherian Y] : IsReduced X := by
  let _ := geometricallyReduced_of_etale f
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f

end AlgebraicGeometry

namespace AlgebraicGeometry

lemma isField_stalk_of_reduced_discrete (X : Scheme.{u}) [IsReduced X]
    [DiscreteTopology X] (x : X) : IsField (X.presheaf.stalk x) := by
  apply isField_stalk_of_closure_mem_irreducibleComponents
  rw [closure_singleton]
  refine ⟨isIrreducible_singleton, ?_⟩
  intro s hs hxs y hy
  exact hs.isPreirreducible.subsingleton hy (hxs rfl)

lemma isIso_of_preimmersion_surjective_reduced_discrete {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] [Surjective f] [IsReduced Y] [DiscreteTopology Y] : IsIso f := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨?_, inferInstance⟩
  apply IsOpenImmersion.iff_isIso_stalkMap.mpr
  refine ⟨⟨f.isEmbedding, isOpen_discrete _⟩, ?_⟩
  intro x
  let _ := (isField_stalk_of_reduced_discrete Y (f x)).toField
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨(f.stalkMap x).hom.injective, f.stalkMap_surjective x⟩

end AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]

lemma genericBaseChange_isReduced : IsReduced (pullback (genericPointsToScheme Y) f) := by
  exact isReduced_of_etale (pullback.fst (genericPointsToScheme Y) f)

lemma genericBaseChange_discrete :
    DiscreteTopology (pullback (genericPointsToScheme Y) f : Scheme.{u}) := by
  let _ := locallyQuasiFinite_of_etale (pullback.fst (genericPointsToScheme Y) f)
  let _ := IsLocallyArtinian.of_locallyQuasiFinite (pullback.fst (genericPointsToScheme Y) f)
  infer_instance

end GromovWitten.AlgebraicGeometry.Curves


namespace GromovWitten.AlgebraicGeometry.Curves
noncomputable section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hg : ∀ x : GenericPointSet X, closure {f x.val} ∈ irreducibleComponents Y)

def genericPointsMap : genericPointCoproduct X ⟶ genericPointCoproduct Y :=
  Sigma.desc (fun x : GenericPointSet X ↦
    Spec.map (f.residueFieldMap x.val) ≫ Sigma.ι (genericPointSpectrum Y) ⟨f x.val, hg x⟩)

@[reassoc (attr := simp)] lemma genericPointsMap_toScheme :
    genericPointsMap f hg ≫ genericPointsToScheme Y = genericPointsToScheme X ≫ f := by
  apply Sigma.hom_ext
  intro x
  simp only [genericPointsMap, genericPointsToScheme, Sigma.ι_desc_assoc,
    Category.assoc, Sigma.ι_desc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

def genericBaseChangeLift : genericPointCoproduct X ⟶ pullback (genericPointsToScheme Y) f :=
  pullback.lift (genericPointsMap f hg) (genericPointsToScheme X) (genericPointsMap_toScheme f hg)

@[reassoc (attr := simp)] lemma genericBaseChangeLift_snd :
    genericBaseChangeLift f hg ≫ pullback.snd (genericPointsToScheme Y) f =
      genericPointsToScheme X := by
  unfold genericBaseChangeLift
  rw [pullback.lift_snd]

lemma genericBaseChangeLift_isIso [IsNoetherian X] [IsNoetherian Y] [Etale f]
    (hr : ∀ x : X, closure {f x} ∈ irreducibleComponents Y →
      closure {x} ∈ irreducibleComponents X) : IsIso (genericBaseChangeLift f hg) := by
  let q := pullback.snd (genericPointsToScheme Y) f
  let _ : IsPreimmersion (genericBaseChangeLift f hg ≫ q) := by
    dsimp only [q]
    rw [genericBaseChangeLift_snd]
    infer_instance
  let _ : IsPreimmersion (genericBaseChangeLift f hg) :=
    IsPreimmersion.of_comp (genericBaseChangeLift f hg) q
  let _ : Surjective (genericBaseChangeLift f hg) := by
    constructor
    intro p
    have hx : closure {q p} ∈ irreducibleComponents X := by
      apply hr
      have hp := (genericPointCoproductEquiv Y
        (pullback.fst (genericPointsToScheme Y) f p)).property
      rw [genericPointCoproductEquiv_val] at hp
      simpa only [q, ← Scheme.Hom.comp_apply, pullback.condition] using hp
    let x : GenericPointSet X := ⟨q p, hx⟩
    let a := sigmaMk (genericPointSpectrum X)
      ⟨x, IsLocalRing.closedPoint (X.residueField x.val)⟩
    refine ⟨a, q.isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, genericBaseChangeLift_snd]
    exact genericPointsToScheme_sigmaMk X x _
  let _ := genericBaseChange_isReduced f
  let _ := genericBaseChange_discrete f
  exact isIso_of_preimmersion_surjective_reduced_discrete (genericBaseChangeLift f hg)

end
end GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves
noncomputable section
lemma closure_map_mem_irreducibleComponents_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyQuasiFinite f] (x : X) :
    closure {f x} ∈ irreducibleComponents Y ↔
      closure {x} ∈ irreducibleComponents X := by
  constructor
  · intro hfx
    let C : Set X := irreducibleComponent x
    have hC : C ∈ irreducibleComponents X :=
      irreducibleComponent_mem_irreducibleComponents x
    let c : X := hC.1.genericPoint
    have hcx : c ⤳ x := by
      apply specializes_iff_mem_closure.mpr
      rw [hC.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents C hC)]
      exact mem_irreducibleComponent (x := x)
    have hfcx : f c = f x := by
      apply eq_of_specializes_generic hfx
      exact hcx.map f.continuous
    let s : Set X := f ⁻¹' {f x}
    let _ : DiscreteTopology s := isDiscrete_iff_discreteTopology.mp
      (f.isDiscrete_preimage_singleton (f x))
    let a : s := ⟨c, by simp [s, hfcx]⟩
    let b : s := ⟨x, by simp [s]⟩
    have hab : a ⤳ b := Topology.IsInducing.subtypeVal.specializes_iff.mp hcx
    have hac : c = x := congrArg Subtype.val hab.eq
    rw [← hac]
    exact (hC.1.closure_genericPoint
      (isClosed_of_mem_irreducibleComponents C hC)).symm ▸ hC
  · intro hx
    let D : Set Y := irreducibleComponent (f x)
    have hD : D ∈ irreducibleComponents Y :=
      irreducibleComponent_mem_irreducibleComponents (f x)
    let d : Y := hD.1.genericPoint
    have hdx : d ⤳ f x := by
      apply specializes_iff_mem_closure.mpr
      rw [hD.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents D hD)]
      exact mem_irreducibleComponent (x := f x)
    obtain ⟨c, hcx, hfc⟩ := (Flat.generalizingMap f) hdx
    have hcx' : c = x := eq_of_specializes_generic hx hcx
    have hfd : f x = d := by simpa [hcx'] using hfc
    rw [hfd]
    exact (hD.1.closure_genericPoint
      (isClosed_of_mem_irreducibleComponents D hD)).symm ▸ hD

end
end GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves
noncomputable section
variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]

def genericEtaleBaseChangeIso (f : X ⟶ Y) [Etale f] :
    genericPointCoproduct X ≅ pullback (genericPointsToScheme Y) f := by
  let _ := locallyQuasiFinite_of_etale f
  let hg := fun x : GenericPointSet X ↦
    (closure_map_mem_irreducibleComponents_iff f x.val).mpr x.property
  let hr := fun x : X ↦ (closure_map_mem_irreducibleComponents_iff f x).mp
  exact @asIso _ _ _ _ (genericBaseChangeLift f hg) (genericBaseChangeLift_isIso f hg hr)

@[reassoc (attr := simp)] lemma genericEtaleBaseChangeIso_hom_snd (f : X ⟶ Y) [Etale f] :
    (genericEtaleBaseChangeIso f).hom ≫ pullback.snd (genericPointsToScheme Y) f =
      genericPointsToScheme X := by
  exact genericBaseChangeLift_snd _ _

abbrev totalNormalization (X : Scheme.{u}) [IsNoetherian X] : Scheme.{u} :=
  (genericPointsToScheme X).normalization

abbrev totalNormalizationToScheme (X : Scheme.{u}) [IsNoetherian X] :
    totalNormalization X ⟶ X := (genericPointsToScheme X).fromNormalization

def totalNormalizationEtaleIso (f : X ⟶ Y) [Etale f] :
    totalNormalization X ≅ pullback (totalNormalizationToScheme Y) f :=
  (Scheme.Hom.normalizationCongr (genericEtaleBaseChangeIso_hom_snd f)).symm ≪≫
    Scheme.Hom.normalizationPrecompIso (pullback.snd (genericPointsToScheme Y) f)
      (genericEtaleBaseChangeIso f) ≪≫
    asIso ((genericPointsToScheme Y).normalizationPullback f)

@[reassoc (attr := simp)] lemma totalNormalizationEtaleIso_hom_snd (f : X ⟶ Y) [Etale f] :
    (totalNormalizationEtaleIso f).hom ≫ pullback.snd (totalNormalizationToScheme Y) f =
      totalNormalizationToScheme X := by
  dsimp only [totalNormalizationEtaleIso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  rw [Category.assoc, Category.assoc, Scheme.Hom.normalizationPullback_snd,
    Scheme.Hom.normalizationPrecompIso_hom_fromNormalization]
  apply (Iso.inv_comp_eq _).mpr
  exact (Scheme.Hom.normalizationCongr_hom_fromNormalization
    (genericEtaleBaseChangeIso_hom_snd f)).symm

end
end GromovWitten.AlgebraicGeometry.Curves

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom
variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
  {f : X ⟶ Z} {g : Y ⟶ Z}

noncomputable def fibrePullbackIso (h : IsPullback fst snd f g) (y : Y)
    [IsIso (g.residueFieldMap y)] : snd.fiber y ≅ f.fiber (g y) := by
  let m := pullback.map snd (Y.fromSpecResidueField y)
    f (Z.fromSpecResidueField (g y)) fst (Spec.map (g.residueFieldMap y)) g
    h.w.symm (by simp)
  have hp := isPullback_fiberToSpecResidueField_of_isPullback h y
  have hm : IsIso m := hp.isIso_fst_of_isIso
  exact @asIso _ _ _ _ m hm

noncomputable def fibrePullbackEquiv (h : IsPullback fst snd f g) (y : Y)
    [IsIso (g.residueFieldMap y)] :
    {p : P // snd p = y} ≃ {x : X // f x = g y} :=
  (snd.fiberHomeo y).toEquiv.symm.trans
    ((fibrePullbackIso h y).hom.homeomorph.toEquiv.trans (f.fiberHomeo (g y)).toEquiv)

@[simp] theorem fibrePullbackEquiv_apply (h : IsPullback fst snd f g) (y : Y)
    [IsIso (g.residueFieldMap y)] (p : {p : P // snd p = y}) :
    (fibrePullbackEquiv h y p).1 = fst p := by
  change f.fiberι (g y) ((fibrePullbackIso h y).hom ((snd.fiberHomeo y).symm p)) = _
  rw [← Scheme.Hom.comp_apply]
  change (pullback.map _ _ _ _ fst (Spec.map (g.residueFieldMap y)) g h.w.symm (by simp) ≫
    pullback.fst _ _) _ = _
  simp only [pullback.map, pullback.lift_fst]
  exact congrArg fst (snd.fiberι_fiberHomeo_symm y p)

theorem residueFieldMap_isIso_of_closed
    {K : Type u} [Field K] [IsAlgClosed K] (g : Y ⟶ Z) (b : Z ⟶ Spec (.of K))
    [LocallyOfFiniteType b] [LocallyOfFiniteType (g ≫ b)]
    (y : Y) (hy : IsClosed {y}) (hz : IsClosed {g y}) :
    IsIso (g.residueFieldMap y) := by
  have heq : g.residueFieldMap y =
      (residueFieldIsoBase b (g y) hz).hom ≫
        (residueFieldIsoBase (g ≫ b) y hy).inv := by
    rw [← cancel_epi (residueFieldIsoBase b (g y) hz).inv]
    simp only [Iso.inv_hom_id_assoc]
    apply Spec.map_injective
    simp only [Spec.map_comp, SpecMap_residueFieldIsoBase_inv]
    rw [← Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      Category.assoc]
  rw [heq]
  infer_instance

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme
variable {X Y Z : Scheme.{u}}

noncomputable def fibreEquivOfIso (e : X ≅ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : e.hom ≫ g = f) (z : Z) : {x : X // f x = z} ≃ {y : Y // g y = z} where
  toFun x := ⟨e.hom x, by rw [← Scheme.Hom.comp_apply, h]; exact x.2⟩
  invFun y := ⟨e.inv y, by
    rw [← h, ← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]
    exact y.2⟩
  left_inv x := Subtype.ext (by simp [← Scheme.Hom.comp_apply])
  right_inv y := Subtype.ext (by simp [← Scheme.Hom.comp_apply])

end AlgebraicGeometry.Scheme

namespace GromovWitten.AlgebraicGeometry.Curves
noncomputable section
variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]

def totalNormalizationEtaleFibreEquiv (f : X ⟶ Y) [Etale f] (x : X)
    [IsIso (f.residueFieldMap x)] :
    {p : totalNormalization X // totalNormalizationToScheme X p = x} ≃
      {q : totalNormalization Y // totalNormalizationToScheme Y q = f x} :=
  (Scheme.fibreEquivOfIso (totalNormalizationEtaleIso f)
    (totalNormalizationToScheme X) (pullback.snd (totalNormalizationToScheme Y) f)
    (totalNormalizationEtaleIso_hom_snd f) x).trans
      (Scheme.Hom.fibrePullbackEquiv
        (IsPullback.of_hasPullback (totalNormalizationToScheme Y) f) x)

end
end GromovWitten.AlgebraicGeometry.Curves
