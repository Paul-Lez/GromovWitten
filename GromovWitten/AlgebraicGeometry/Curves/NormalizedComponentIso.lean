/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.GeometricDualGraph
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Topology

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

open StableReduction

namespace Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (I : X.IdealSheafData) (e : X ≅ Y)

theorem map_radical : I.radical.map e.hom = (I.map e.hom).radical := by
  ext U : 2
  simp only [_root_.AlgebraicGeometry.Scheme.IdealSheafData.radical_ideal]
  rw [_root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_map_of_isAffineHom I.radical e.hom U,
    _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_map_of_isAffineHom I e.hom U]
  exact Ideal.comap_radical (CommRingCat.Hom.hom (Scheme.Hom.app e.hom ↑U)) _

end Scheme.IdealSheafData

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)}
  [PrestableFamily f] [PrestableFamily g] [IsNoetherian X] [IsNoetherian Y]
  (e : X ≅ Y) (C : Component X)

noncomputable def transportedComponent : Component Y :=
  irreducibleComponentsEquivOfSchemeIso e C

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
theorem transportedComponent_mem (x : X) :
    x ∈ (C : Set X) ↔ e.hom x ∈ (transportedComponent e C : Set Y) := by
  rw [← mem_irreducibleComponentsEquivOfSchemeIso_symm]
  simp [transportedComponent]

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
theorem transportedComponent_image :
    e.hom '' (C : Set X) = (transportedComponent e C : Set Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (transportedComponent_mem e C x).mp hx
  · intro hy
    refine ⟨e.inv y, ?_, ?_⟩
    · exact (transportedComponent_mem e C (e.inv y)).mpr (by simpa using hy)
    · simp

theorem componentIdeal_radical_map :
    ((X.irreducibleComponentIdeal C C.2).radical.map e.hom) =
      (Y.irreducibleComponentIdeal (transportedComponent e C)
        (transportedComponent e C).2).radical := by
  let I := X.irreducibleComponentIdeal C C.2
  let J := Y.irreducibleComponentIdeal (transportedComponent e C)
    (transportedComponent e C).2
  have hI : (I.radical.support : Set X) = (C : Set X) := by
    rw [Scheme.IdealSheafData.support_radical]
    rfl
  have hJ : (J.radical.support : Set Y) = (transportedComponent e C : Set Y) := by
    rw [Scheme.IdealSheafData.support_radical]
    rfl
  have hsupport : (I.radical.map e.hom).support = J.radical.support := by
    rw [Scheme.IdealSheafData.support_map]
    apply SetLike.coe_injective
    change closure (e.hom '' (I.radical.support : Set X)) =
      (J.radical.support : Set Y)
    rw [hI, transportedComponent_image e C, hJ]
    exact (isClosed_of_mem_irreducibleComponents _ (transportedComponent e C).2).closure_eq
  have hsupport' : (I.map e.hom).support = J.radical.support := by
    rw [← Scheme.IdealSheafData.support_radical]
    rw [← Scheme.IdealSheafData.map_radical I e]
    exact hsupport
  calc
    I.radical.map e.hom = (I.map e.hom).radical :=
      Scheme.IdealSheafData.map_radical I e
    _ = Scheme.IdealSheafData.vanishingIdeal (I.map e.hom).support :=
      Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = Scheme.IdealSheafData.vanishingIdeal J.radical.support := by
      rw [hsupport']
    _ = J.radical := by
      simpa only [Scheme.IdealSheafData.support_radical] using
        (@Scheme.IdealSheafData.vanishingIdeal_support _ J)

noncomputable def componentSubschemeIso_raw :
    ((X.irreducibleComponentIdeal C C.2).radical.subscheme ≅
      (Y.irreducibleComponentIdeal (transportedComponent e C)
        (transportedComponent e C).2).radical.subscheme) := by
  let D := transportedComponent e C
  let I := (X.irreducibleComponentIdeal C C.2).radical
  let J := (Y.irreducibleComponentIdeal D D.2).radical
  have hIJ : I.map e.hom = J := componentIdeal_radical_map e C
  have hJI : J.map e.inv = I := by
    have h := componentIdeal_radical_map e.symm D
    have hD : transportedComponent e.symm D = C := by
      apply Subtype.ext
      ext x
      constructor
      · intro hx
        have hx' : e.hom x ∈ (D : Set Y) := by
          have hx'' := (transportedComponent_mem e.symm D (e.hom x)).mpr
            (by simpa using hx)
          simpa using hx''
        exact (transportedComponent_mem e C x).mpr hx'
      · intro hx
        have hx' : e.hom x ∈ (D : Set Y) := (transportedComponent_mem e C x).mp hx
        have hx'' := (transportedComponent_mem e.symm D (e.hom x)).mp hx'
        simpa using hx''
    rw [hD] at h
    exact h
  let u : I.subscheme ⟶ J.subscheme :=
    Scheme.IdealSheafData.subschemeMap I J e.hom hIJ.symm.le
  let v : J.subscheme ⟶ I.subscheme :=
    Scheme.IdealSheafData.subschemeMap J I e.inv hJI.symm.le
  have huv : u ≫ v = 𝟙 _ := by
    apply (cancel_mono I.subschemeι).1
    simp [u, v, Category.assoc]
  have hvu : v ≫ u = 𝟙 _ := by
    apply (cancel_mono J.subschemeι).1
    simp [u, v, Category.assoc]
  exact ⟨u, v, huv, hvu⟩

theorem componentSubschemeIso_raw_hom_subschemeι :
    (componentSubschemeIso_raw e C).hom ≫
        (Y.irreducibleComponentIdeal (transportedComponent e C)
          (transportedComponent e C).2).radical.subschemeι =
      (X.irreducibleComponentIdeal C C.2).radical.subschemeι ≫ e.hom := by
  let D := transportedComponent e C
  let I := (X.irreducibleComponentIdeal C C.2).radical
  let J := (Y.irreducibleComponentIdeal D D.2).radical
  have hIJ : I.map e.hom = J := componentIdeal_radical_map e C
  change (componentSubschemeIso_raw e C).hom ≫ J.subschemeι = I.subschemeι ≫ e.hom
  change (Scheme.IdealSheafData.subschemeMap I J e.hom hIJ.symm.le) ≫
    J.subschemeι = I.subschemeι ≫ e.hom
  exact Scheme.IdealSheafData.subschemeMap_subschemeι I J e.hom hIJ.symm.le

noncomputable def componentSchemeIso :
    componentScheme f C ≅ componentScheme g (transportedComponent e C) := by
  unfold componentScheme
  exact componentSubschemeIso_raw e C

theorem componentSchemeIso_hom_inclusion :
    (componentSchemeIso e C).hom ≫
        componentInclusion g (transportedComponent e C) =
      componentInclusion f C ≫ e.hom := by
  unfold componentSchemeIso componentInclusion
  exact componentSubschemeIso_raw_hom_subschemeι e C

theorem componentSchemeIso_hom_toBase (he : e.hom ≫ g = f) :
    (componentSchemeIso e C).hom ≫
        componentToBase g (transportedComponent e C) =
      componentToBase f C := by
  change (componentSchemeIso e C).hom ≫
      componentInclusion g (transportedComponent e C) ≫ g =
        componentInclusion f C ≫ f
  rw [← Category.assoc, componentSchemeIso_hom_inclusion e C, Category.assoc, he]

end
end GromovWitten.AlgebraicGeometry.Curves

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (e : Y ≅ X)
  [QuasiCompact f] [QuasiSeparated f]

noncomputable def normalizationPrecompIso : (e.hom ≫ f).normalization ≅ f.normalization where
  hom := (e.hom ≫ f).normalizationDesc (e.hom ≫ f.toNormalization)
    f.fromNormalization (by simp)
  inv := f.normalizationDesc (e.inv ≫ (e.hom ≫ f).toNormalization)
    (e.hom ≫ f).fromNormalization (by simp)
  hom_inv_id := by
    apply normalization.hom_ext (e.hom ≫ f) _ _ (e.hom ≫ f).fromNormalization <;> simp
  inv_hom_id := by
    apply normalization.hom_ext f _ _ f.fromNormalization <;> simp

@[reassoc (attr := simp)] theorem normalizationPrecompIso_hom_fromNormalization :
    (normalizationPrecompIso f e).hom ≫ f.fromNormalization =
      (e.hom ≫ f).fromNormalization := by
  simp [normalizationPrecompIso]

@[reassoc (attr := simp)] theorem toNormalization_normalizationPrecompIso_hom :
    (e.hom ≫ f).toNormalization ≫ (normalizationPrecompIso f e).hom =
      e.hom ≫ f.toNormalization := by
  simp [normalizationPrecompIso]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

lemma fromSpecStalk_congr (X : Scheme.{u}) (x y : X) (h : x = y) :
    Spec.map (eqToHom (congrArg X.presheaf.stalk h).symm) ≫ X.fromSpecStalk y =
      X.fromSpecStalk x := by
  subst y
  simp

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} {f g : X ⟶ Y}
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]

noncomputable def normalizationCongr (h : f = g) : f.normalization ≅ g.normalization := by
  subst g
  exact Iso.refl _

@[reassoc (attr := simp)] theorem normalizationCongr_hom_fromNormalization (h : f = g) :
    (normalizationCongr h).hom ≫ g.fromNormalization = f.fromNormalization := by
  subst g
  simp [normalizationCongr]

@[reassoc (attr := simp)] theorem toNormalization_normalizationCongr_hom (h : f = g) :
    f.toNormalization ≫ (normalizationCongr h).hom = g.toNormalization := by
  subst g
  simp [normalizationCongr]

end AlgebraicGeometry.Scheme.Hom

namespace GromovWitten.AlgebraicGeometry.Curves.Normalization

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

noncomputable def genericPointIso (e : X ≅ Y) : Spec X.functionField ≅ Spec Y.functionField :=
  Scheme.Spec.mapIso ((eqToIso (congrArg Y.presheaf.stalk
    (genericPoint_eq_of_isOpenImmersion e.hom))).symm ≪≫
      asIso (e.hom.stalkMap (genericPoint X))).op

theorem genericPointIso_hom_genericPointMap (e : X ≅ Y) :
    (genericPointIso e).hom ≫ genericPointMap Y = genericPointMap X ≫ e.hom := by
  change Spec.map (eqToHom (congrArg Y.presheaf.stalk
    (genericPoint_eq_of_isOpenImmersion e.hom)).symm ≫ e.hom.stalkMap (genericPoint X)) ≫
    Y.fromSpecStalk (genericPoint Y) = _
  rw [Spec.map_comp, Category.assoc, Scheme.fromSpecStalk_congr,
    Scheme.SpecMap_stalkMap_fromSpecStalk]
  exact genericPoint_eq_of_isOpenImmersion e.hom

noncomputable def mapIso (e : X ≅ Y) : scheme X ≅ scheme Y :=
  (Scheme.Hom.normalizationIntegralPostcompIso (genericPointMap X) e.hom).symm ≪≫
    Scheme.Hom.normalizationCongr (genericPointIso_hom_genericPointMap e).symm ≪≫
      Scheme.Hom.normalizationPrecompIso (genericPointMap Y) (genericPointIso e)

@[reassoc (attr := simp)] theorem mapIso_hom_toCurve (e : X ≅ Y) :
    (mapIso e).hom ≫ toCurve Y = toCurve X ≫ e.hom := by
  let E := Scheme.Hom.normalizationIntegralPostcompIso (genericPointMap X) e.hom
  apply (cancel_epi E.hom).mp
  dsimp only [mapIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [Scheme.Hom.normalizationPrecompIso_hom_fromNormalization,
    Scheme.Hom.normalizationCongr_hom_fromNormalization]
  rw [← Category.assoc, E.hom_inv_id, Category.id_comp]
  exact (Scheme.Hom.normalizationIntegralPostcompIso_hom_fromNormalization
    (genericPointMap X) e.hom).symm

@[reassoc (attr := simp)] theorem genericLift_mapIso_hom (e : X ≅ Y) :
    genericLift X ≫ (mapIso e).hom = (genericPointIso e).hom ≫ genericLift Y := by
  let E := Scheme.Hom.normalizationIntegralPostcompIso (genericPointMap X) e.hom
  have h : genericLift X ≫ E.inv = (genericPointMap X ≫ e.hom).toNormalization := by
    apply (cancel_mono E.hom).mp
    simp only [Category.assoc, E.inv_hom_id, Category.comp_id]
    exact (Scheme.Hom.toNormalization_normalizationIntegralPostcompIso_hom
      (genericPointMap X) e.hom).symm
  change genericLift X ≫ E.inv ≫ _ = _
  rw [← Category.assoc, h]
  dsimp only [Iso.trans_hom]
  rw [← Category.assoc, Scheme.Hom.toNormalization_normalizationCongr_hom,
    Scheme.Hom.toNormalization_normalizationPrecompIso_hom]

end GromovWitten.AlgebraicGeometry.Curves.Normalization

namespace GromovWitten.AlgebraicGeometry.Curves

noncomputable section

open StableReduction

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)}
  [PrestableFamily f] [PrestableFamily g] [IsNoetherian X] [IsNoetherian Y]
  (e : X ≅ Y) (C : Component X)

noncomputable def normalizedComponentSchemeIso :
    normalizedComponentScheme f C ≅
      normalizedComponentScheme g (transportedComponent e C) := by
  letI := componentScheme_isIntegral f C
  letI := componentScheme_isIntegral g (transportedComponent e C)
  exact Normalization.mapIso (componentSchemeIso e C)

theorem normalizedComponentSchemeIso_hom_toCurve :
    (normalizedComponentSchemeIso e C).hom ≫
        normalizedComponentToCurve g (transportedComponent e C) =
      normalizedComponentToCurve f C ≫ e.hom := by
  let _ := componentScheme_isIntegral f C
  let _ := componentScheme_isIntegral g (transportedComponent e C)
  change (Normalization.mapIso (componentSchemeIso e C)).hom ≫
      Normalization.toCurve (componentScheme g (transportedComponent e C)) ≫
        componentInclusion g (transportedComponent e C) =
      Normalization.toCurve (componentScheme f C) ≫
        componentInclusion f C ≫ e.hom
  rw [← Category.assoc, Normalization.mapIso_hom_toCurve]
  rw [Category.assoc, componentSchemeIso_hom_inclusion]

theorem normalizedComponentSchemeIso_hom_toBase (he : e.hom ≫ g = f) :
    (normalizedComponentSchemeIso e C).hom ≫
        normalizedComponentToBase g (transportedComponent e C) =
      normalizedComponentToBase f C := by
  change (normalizedComponentSchemeIso e C).hom ≫
      normalizedComponentToCurve g (transportedComponent e C) ≫ g =
        normalizedComponentToCurve f C ≫ f
  rw [← Category.assoc, normalizedComponentSchemeIso_hom_toCurve e C,
    Category.assoc, he]

end
end GromovWitten.AlgebraicGeometry.Curves
