/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.BaseSectionsCechRestriction
import GromovWitten.CategoryTheory.MappingCoconeShortExact

/-!
# Finite Čech comparison for flasque complexes

The canonical finite Čech augmentation of a termwise flasque complex is a
quasi-isomorphism on each open covered by the chosen finite list. The proof
identifies the binary construction with the short exact Mayer–Vietoris sequence
and then applies finite-cover induction, including the empty cover.
-/

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace AlgebraicGeometry
open CochainComplex
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

private lemma baseSectionsComplex_empty_isZero (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) :
    IsZero (((baseSectionsFunctor s ⊥).mapHomologicalComplex (.up ℤ)).obj K) := by
  let L := ((baseSectionsFunctor s ⊥).mapHomologicalComplex (.up ℤ)).obj K
  have hz (i : ℤ) : IsZero (L.X i) := by
    let F := (moduleToSheafAb X).obj (K.X i)
    have hAb : IsZero (F.obj.obj (op (⊥ : X.Opens))) :=
      (TopCat.Sheaf.isTerminalOfEmpty F).isZero
    have hs : Subsingleton (L.X i) := AddCommGrpCat.subsingleton_of_isZero hAb
    exact ModuleCat.isZero_iff_subsingleton.mpr hs
  let e : L ≅ (HomologicalComplex.zero : CochainComplex (ModuleCat R) ℤ) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (hz i).iso (Limits.isZero_zero (ModuleCat R)))
      (fun i _ _ => (hz i).eq_of_src _ _)
  exact HomologicalComplex.isZero_zero.of_iso e

private lemma supportedFiniteCechAugmentation_baseSections_nil_quasiIso
    (s : X ⟶ Spec R) (K : CochainComplex X.Modules ℤ) (W : X.Opens) :
    QuasiIso ((evaluatePresheafComplexMap
      (supportedFiniteCechAugmentation
        (((baseSectionsPresheafFunctor s).mapHomologicalComplex (.up ℤ)).obj K) []).hom).app
          (op W)) := by
  let F := ((baseSectionsPresheafFunctor s).mapHomologicalComplex (.up ℤ)).obj K
  let E := ((evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op W)).mapHomologicalComplex (.up ℤ)
  have hs : IsZero (E.obj ((restrictionComplexFunctor (⊥ : X.Opens)).obj F)) := by
    change IsZero (((baseSectionsFunctor s (W ⊓ ⊥)).mapHomologicalComplex (.up ℤ)).obj K)
    rw [inf_bot_eq]
    exact baseSectionsComplex_empty_isZero s K
  have ht : IsZero (E.obj (finiteCechData F []).complex) :=
    E.map_isZero HomologicalComplex.isZero_zero
  have : IsIso (E.map (supportedFiniteCechAugmentation F []).hom) := hs.isIso ht _
  change QuasiIso (E.map (supportedFiniteCechAugmentation F []).hom)
  infer_instance

private abbrev baseSectionsPresheafComplex (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) :
    PresheafComplex (TopCat.of X) (R : Type u) :=
  ((baseSectionsPresheafFunctor s).mapHomologicalComplex (.up ℤ)).obj K

private abbrev baseSectionsComplexAt (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) (W : X.Opens) :
    CochainComplex (ModuleCat R) ℤ :=
  ((baseSectionsFunctor s W).mapHomologicalComplex (.up ℤ)).obj K

private abbrev presheafEvaluationAt (W : X.Opens) :
    Presheaves (TopCat.of X) (R : Type u) ⥤ ModuleCat R :=
  (evaluation (Opens (TopCat.of X))ᵒᵖ (ModuleCat R)).obj (op W)

private noncomputable def evaluateRestrictionIso (U W : X.Opens)
    (T : PresheafComplex (TopCat.of X) (R : Type u)) :
    ((presheafEvaluationAt (R := R) W).mapHomologicalComplex (.up ℤ)).obj
        ((restrictionComplexFunctor
          (X := TopCat.of X) (R := R) U).obj T) ≅
      ((presheafEvaluationAt (R := R) (W ⊓ U)).mapHomologicalComplex (.up ℤ)).obj T := Iso.refl _

private noncomputable def evaluateBaseSectionsRestrictionIso
    (s : X ⟶ Spec R) (K : CochainComplex X.Modules ℤ) (U W : X.Opens) :
    ((presheafEvaluationAt (R := R) W).mapHomologicalComplex (.up ℤ)).obj
        ((restrictionComplexFunctor
          (X := TopCat.of X) (R := R) U).obj (baseSectionsPresheafComplex s K)) ≅
      baseSectionsComplexAt s K (W ⊓ U) := Iso.refl _

private noncomputable def presheafMayerVietorisComplex
    (F : PresheafComplex (TopCat.of X) (R : Type u))
    (U V : X.Opens) :
    ShortComplex (PresheafComplex (TopCat.of X) (R : Type u)) := by
  let α := (restrictionComplexNatTrans V).app F
  let β := 𝟙 ((restrictionComplexFunctor V).obj F)
  refine ShortComplex.mk
    (biprod.lift
      ((restrictionComplexLENatTrans
        (le_sup_left : U ≤ U ⊔ V)).app F)
      (((restrictionComplexLENatTrans
        (le_sup_right : V ≤ U ⊔ V)).app F) ≫ β))
    (biprod.desc
      ((restrictionComplexFunctor U).map α)
      (-((restrictionComplexNatTrans U).app
        ((restrictionComplexFunctor V).obj F)))) ?_
  · exact supported_augmentation_cons_zero F
      ((restrictionComplexFunctor V).obj F) U V α β (by simp [α, β])

private noncomputable def evaluatedMayerVietorisComplex
    (s : X ⟶ Spec R) (K : CochainComplex X.Modules ℤ)
    (U V W : X.Opens) : ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
  (presheafMayerVietorisComplex (baseSectionsPresheafComplex s K) U V).map
    ((presheafEvaluationAt (R := R) W).mapHomologicalComplex (.up ℤ))

private lemma opens_inf_sup_eq (W U V : X.Opens) :
    W ⊓ (U ⊔ V) = (W ⊓ U) ⊔ (W ⊓ V) := inf_sup_left W U V

private lemma opens_left_restriction_arrow (W U V : X.Opens) :
    (homOfLE (le_sup_left : (W ⊓ U) ≤ (W ⊓ U) ⊔ (W ⊓ V))) ≫
        eqToHom (opens_inf_sup_eq W U V).symm =
      homOfLE (inf_le_inf_left W (le_sup_left : U ≤ U ⊔ V)) := by
  apply Subsingleton.elim

private lemma opens_right_restriction_arrow (W U V : X.Opens) :
    (homOfLE (le_sup_right : (W ⊓ V) ≤ (W ⊓ U) ⊔ (W ⊓ V))) ≫
        eqToHom (opens_inf_sup_eq W U V).symm =
      homOfLE (inf_le_inf_left W (le_sup_right : V ≤ U ⊔ V)) := by
  apply Subsingleton.elim

set_option backward.isDefEq.respectTransparency false in
private noncomputable def evaluatedMayerVietorisIso
    (s : X ⟶ Spec R) (K : CochainComplex X.Modules ℤ)
    (U V W : X.Opens) :
    evaluatedMayerVietorisComplex s K U V W ≅
      baseSectionsComplexMV s K (W ⊓ U) (W ⊓ V) := by
  let F := baseSectionsPresheafComplex s K
  let H := (presheafEvaluationAt (R := R) W).mapHomologicalComplex (.up ℤ)
  let S := evaluatedMayerVietorisComplex s K U V W
  let T := baseSectionsComplexMV s K (W ⊓ U) (W ⊓ V)
  let A := baseSectionsComplexAt s K (W ⊓ U)
  let B := baseSectionsComplexAt s K (W ⊓ V)
  let pairIso := baseSectionsPairComplexIso s K (W ⊓ U) (W ⊓ V)
  let hOpen := opens_inf_sup_eq W U V
  let e₁ := (evaluateBaseSectionsRestrictionIso s K (U ⊔ V) W).trans
    (eqToIso (congrArg (fun O => baseSectionsComplexAt s K O) hOpen))
  let eU := evaluateBaseSectionsRestrictionIso s K U W
  let eV := evaluateBaseSectionsRestrictionIso s K V W
  have : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  let eB := H.mapBiprod
      ((restrictionComplexFunctor U).obj F)
      ((restrictionComplexFunctor V).obj F)
  let e₂ := eB.trans ((biprod.mapIso eU eV).trans pairIso.symm)
  have hmeet : (W ⊓ U) ⊓ V = (W ⊓ U) ⊓ (W ⊓ V) := by
    simp [inf_left_comm, inf_comm]
  let e₃ := (evaluateRestrictionIso (R := R) U W
      ((restrictionComplexFunctor V).obj F)).trans
    ((evaluateBaseSectionsRestrictionIso s K V (W ⊓ U)).trans
      (eqToIso (congrArg (fun O => baseSectionsComplexAt s K O) hmeet)))
  let rU := (restrictionComplexLENatTrans
    (le_sup_left : U ≤ U ⊔ V)).app F
  let rV := (restrictionComplexLENatTrans
    (le_sup_right : V ≤ U ⊔ V)).app F
  let gU := ((restrictionComplexFunctor U).map
    ((restrictionComplexNatTrans V).app F))
  let gV := ((restrictionComplexNatTrans U).app
    ((restrictionComplexFunctor V).obj F))
  let pU := homOfLE (le_sup_left : (W ⊓ U) ≤ (W ⊓ U) ⊔ (W ⊓ V))
  let pV := homOfLE (le_sup_right : (W ⊓ V) ≤ (W ⊓ U) ⊔ (W ⊓ V))
  let mU := homOfLE (inf_le_left : (W ⊓ U) ⊓ (W ⊓ V) ≤ W ⊓ U)
  let mV := homOfLE (inf_le_right : (W ⊓ U) ⊓ (W ⊓ V) ≤ W ⊓ V)
  have he₁ : e₁.hom = baseSectionsComplexRestriction s K (eqToHom hOpen.symm) := by
    dsimp [e₁, Iso.trans_hom, evaluateBaseSectionsRestrictionIso]
    exact (baseSectionsComplexRestriction_eqToHom s K hOpen).symm
  have he₃ : e₃.hom = baseSectionsComplexRestriction s K (eqToHom hmeet.symm) := by
    dsimp [e₃, Iso.trans_hom, evaluateRestrictionIso, evaluateBaseSectionsRestrictionIso]
    exact (baseSectionsComplexRestriction_eqToHom s K hmeet).symm
  have hU : e₁.hom ≫ baseSectionsComplexRestriction s K pU = H.map rU := by
    calc
      e₁.hom ≫ baseSectionsComplexRestriction s K pU =
          baseSectionsComplexRestriction s K (eqToHom hOpen.symm) ≫
            baseSectionsComplexRestriction s K pU := by
              rw [he₁]
      _ = baseSectionsComplexRestriction s K (pU ≫ eqToHom hOpen.symm) := by
            rw [baseSectionsComplexRestriction_comp]
      _ = baseSectionsComplexRestriction s K
            (homOfLE (inf_le_inf_left W (le_sup_left : U ≤ U ⊔ V))) := by
            exact congrArg (baseSectionsComplexRestriction s K)
              (opens_left_restriction_arrow W U V)
      _ = H.map rU := by
            rw [evaluate_baseSections_restrictionLE]
  have hV : e₁.hom ≫ baseSectionsComplexRestriction s K pV = H.map rV := by
    calc
      e₁.hom ≫ baseSectionsComplexRestriction s K pV =
          baseSectionsComplexRestriction s K (eqToHom hOpen.symm) ≫
            baseSectionsComplexRestriction s K pV := by
              rw [he₁]
      _ = baseSectionsComplexRestriction s K (pV ≫ eqToHom hOpen.symm) := by
            rw [baseSectionsComplexRestriction_comp]
      _ = baseSectionsComplexRestriction s K
            (homOfLE (inf_le_inf_left W (le_sup_right : V ≤ U ⊔ V))) := by
            exact congrArg (baseSectionsComplexRestriction s K)
              (opens_right_restriction_arrow W U V)
      _ = H.map rV := by
            rw [evaluate_baseSections_restrictionLE]
  have hgU : H.map gU ≫ e₃.hom = baseSectionsComplexRestriction s K mU := by
    calc
      H.map gU ≫ e₃.hom =
            baseSectionsComplexRestriction s K
              (homOfLE (inf_le_left : (W ⊓ U) ⊓ V ≤ W ⊓ U)) ≫
            baseSectionsComplexRestriction s K (eqToHom hmeet.symm) := by
              rw [evaluate_baseSections_restricted_unit]
              rw [he₃]
      _ = baseSectionsComplexRestriction s K
            (eqToHom hmeet.symm ≫
              homOfLE (inf_le_left : (W ⊓ U) ⊓ V ≤ W ⊓ U)) := by
            rw [baseSectionsComplexRestriction_comp]
      _ = baseSectionsComplexRestriction s K mU := by
            exact congrArg (baseSectionsComplexRestriction s K) (Subsingleton.elim _ _)
  have hgV : H.map gV ≫ e₃.hom = baseSectionsComplexRestriction s K mV := by
    calc
      H.map gV ≫ e₃.hom =
            baseSectionsComplexRestriction s K
              (homOfLE (inf_le_inf_right V (inf_le_left : W ⊓ U ≤ W))) ≫
            baseSectionsComplexRestriction s K (eqToHom hmeet.symm) := by
              rw [evaluate_baseSections_unit_restriction]
              rw [he₃]
      _ = baseSectionsComplexRestriction s K
            (eqToHom hmeet.symm ≫
              homOfLE (inf_le_inf_right V (inf_le_left : W ⊓ U ≤ W))) := by
            rw [baseSectionsComplexRestriction_comp]
      _ = baseSectionsComplexRestriction s K mV := by
            exact congrArg (baseSectionsComplexRestriction s K) (Subsingleton.elim _ _)
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · have hpair : e₂.hom ≫ pairIso.hom = eB.hom := by
      have hMapId : biprod.map
          (𝟙 (H.obj ((restrictionComplexFunctor U).obj F)))
          (𝟙 (H.obj ((restrictionComplexFunctor V).obj F))) =
            𝟙 (H.obj ((restrictionComplexFunctor U).obj F) ⊞
            H.obj ((restrictionComplexFunctor V).obj F)) := by
        apply biprod.hom_ext
        · simp only [biprod.map_fst, Category.id_comp, Category.comp_id]
        · simp only [biprod.map_snd, Category.id_comp, Category.comp_id]
      calc
        e₂.hom ≫ pairIso.hom = eB.hom ≫
              biprod.map (𝟙 (H.obj ((restrictionComplexFunctor U).obj F)))
              (𝟙 (H.obj ((restrictionComplexFunctor V).obj F))) := by
                simp [e₂, eU, eV]
                rfl
        _ = eB.hom := by rw [hMapId, Category.comp_id]
    have hLift : S.f ≫ eB.hom = biprod.lift (H.map rU) (H.map rV) := by
      change H.map (biprod.lift rU (rV ≫ 𝟙 _)) ≫ eB.hom = _
      rw [biprod.map_lift_mapBiprod]
      simp only [Category.comp_id]
    have hcomm : (e₁.hom ≫ T.f) ≫ pairIso.hom = (S.f ≫ e₂.hom) ≫ pairIso.hom := by
     calc
      (e₁.hom ≫ T.f) ≫ pairIso.hom = e₁.hom ≫ (T.f ≫ pairIso.hom) := by
        simp only [Category.assoc]
      _ = e₁.hom ≫ biprod.lift
            (baseSectionsComplexRestriction s K pU)
            (baseSectionsComplexRestriction s K pV) := by
            rw [GromovWitten.AlgebraicGeometry.Curves.baseSectionsComplexMV_f_pairIso]
      _ = biprod.lift (H.map rU) (H.map rV) := by
            apply biprod.hom_ext
            · calc
                (e₁.hom ≫ biprod.lift
                    (baseSectionsComplexRestriction s K pU)
                    (baseSectionsComplexRestriction s K pV)) ≫ biprod.fst =
                    e₁.hom ≫ baseSectionsComplexRestriction s K pU := by
                      simp only [Category.assoc, biprod.lift_fst]
                _ = H.map rU := hU
                _ = biprod.lift (H.map rU) (H.map rV) ≫ biprod.fst := by
                      rw [biprod.lift_fst]
            · calc
                (e₁.hom ≫ biprod.lift
                    (baseSectionsComplexRestriction s K pU)
                    (baseSectionsComplexRestriction s K pV)) ≫ biprod.snd =
                    e₁.hom ≫ baseSectionsComplexRestriction s K pV := by
                      simp only [Category.assoc, biprod.lift_snd]
                _ = H.map rV := hV
                _ = biprod.lift (H.map rU) (H.map rV) ≫ biprod.snd := by
                      rw [biprod.lift_snd]
      _ = (S.f ≫ e₂.hom) ≫ pairIso.hom := by
            rw [Category.assoc, hpair, hLift]
    exact (cancel_mono pairIso.hom).mp hcomm
  · have hpair : eB.inv ≫ e₂.hom = pairIso.inv := by
      have hMapId : biprod.map
          (𝟙 (H.obj ((restrictionComplexFunctor U).obj F)))
          (𝟙 (H.obj ((restrictionComplexFunctor V).obj F))) =
            𝟙 (H.obj ((restrictionComplexFunctor U).obj F) ⊞
            H.obj ((restrictionComplexFunctor V).obj F)) := by
        apply biprod.hom_ext
        · simp only [biprod.map_fst, Category.id_comp, Category.comp_id]
        · simp only [biprod.map_snd, Category.id_comp, Category.comp_id]
      calc
        eB.inv ≫ e₂.hom =
            biprod.map (𝟙 (H.obj ((restrictionComplexFunctor U).obj F)))
              (𝟙 (H.obj
                ((restrictionComplexFunctor V).obj F))) ≫
              pairIso.inv := by
                simp [e₂, eU, eV]
                rfl
        _ = pairIso.inv := by rw [hMapId]; simp
    have hDesc : eB.inv ≫ S.g = biprod.desc (H.map gU) (-(H.map gV)) := by
      change eB.inv ≫ H.map (biprod.desc gU (-gV)) = _
      rw [← biprod.mapBiprod_hom_desc]
      change eB.inv ≫ eB.hom ≫ biprod.desc (H.map gU) (H.map (-gV)) = _
      rw [Iso.inv_hom_id_assoc, Functor.map_neg]
      rfl
    have hcomm : eB.inv ≫ e₂.hom ≫ T.g = eB.inv ≫ S.g ≫ e₃.hom := by
     calc
      eB.inv ≫ e₂.hom ≫ T.g = pairIso.inv ≫ T.g := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ T.g) hpair
      _ = biprod.desc (baseSectionsComplexRestriction s K mU)
            (-(baseSectionsComplexRestriction s K mV)) := by
            exact GromovWitten.AlgebraicGeometry.Curves.baseSectionsPairIso_inv_MV_g
              s K (W ⊓ U) (W ⊓ V)
      _ = (eB.inv ≫ S.g) ≫ e₃.hom := by
            rw [hDesc]
            apply biprod.hom_ext'
            · simpa only [biprod.inl_desc, biprod.inl_desc_assoc] using hgU.symm
            · simpa only [biprod.inr_desc, biprod.inr_desc_assoc, Preadditive.neg_comp] using
                (congrArg Neg.neg hgV).symm
    exact (cancel_epi eB.inv).mp hcomm

private lemma evaluatedMayerVietorisComplex_shortExact
    (s : X ⟶ Spec R) (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (U V W : X.Opens) : (evaluatedMayerVietorisComplex s K U V W).ShortExact := by
  exact (ShortComplex.shortExact_iff_of_iso
    (evaluatedMayerVietorisIso s K U V W)).mpr
      (baseSectionsComplexMV_shortExact s K hK (W ⊓ U) (W ⊓ V))

private lemma evaluatedMayerVietorisCocone_quasiIso
    (s : X ⟶ Spec R) (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (U V W : X.Opens) :
    QuasiIso (CochainComplex.mappingCocone.lift
      (evaluatedMayerVietorisComplex s K U V W).g
      (evaluatedMayerVietorisComplex s K U V W).f 0 (by simp)) :=
  CochainComplex.mappingCocone_lift_quasiIso_of_shortExact
    (evaluatedMayerVietorisComplex s K U V W)
    (evaluatedMayerVietorisComplex_shortExact s K hK U V W)

private lemma supportedCechConsMap_baseSections_quasiIso
    (s : X ⟶ Spec R) (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (U V W : X.Opens) :
    QuasiIso ((evaluatePresheafComplexMap
      (supportedCechConsMap
        (baseSectionsPresheafComplex s K)
        ((restrictionComplexFunctor V).obj
          (baseSectionsPresheafComplex s K)) U V
        ((restrictionComplexNatTrans V).app
          (baseSectionsPresheafComplex s K)) (𝟙 _) (by simp))).app (op W)) := by
  let F := baseSectionsPresheafComplex s K
  let H := presheafEvaluationAt (R := R) W
  let E := H.mapHomologicalComplex (.up ℤ)
  let B : PresheafComplex (TopCat.of X) (R : Type u) :=
    (restrictionComplexFunctor V).obj F
  let α : F ⟶ B := (restrictionComplexNatTrans V).app F
  let φ : (restrictionComplexFunctor U).obj F ⊞ B ⟶
      (restrictionComplexFunctor U).obj B :=
    cechDifference F B U α
  let a : (restrictionComplexFunctor (U ⊔ V)).obj F ⟶
      (restrictionComplexFunctor U).obj F ⊞ B := biprod.lift
    ((restrictionComplexLENatTrans
      (le_sup_left : U ≤ U ⊔ V)).app F)
    (((restrictionComplexLENatTrans
      (le_sup_right : V ≤ U ⊔ V)).app F) ≫ 𝟙 _)
  have hz : a ≫ φ = 0 := by
    exact supported_augmentation_cons_zero
      F B U V α (𝟙 _) (by rfl)
  have hLift : CochainComplex.HomComplex.δ (-1) 0 0 +
      CochainComplex.HomComplex.Cochain.ofHom (a ≫ φ) = 0 := by
    rw [hz]
    simp
  have hH : CochainComplex.HomComplex.δ (-1) 0 0 +
      CochainComplex.HomComplex.Cochain.ofHom (E.map a ≫ E.map φ) = 0 := by
    rw [← E.map_comp, hz]
    simp
  have hcanonical : QuasiIso (CochainComplex.mappingCocone.lift
      (E.map φ) (E.map a) 0 hH) := by
    exact evaluatedMayerVietorisCocone_quasiIso s K hK U V W
  have hsupport :
      supportedCechConsMap F B U V α (𝟙 _) (by simp [α]) =
        CochainComplex.mappingCocone.lift φ a 0 hLift := by
    rfl
  have hcomp : QuasiIso
      (E.map (supportedCechConsMap F B U V α
        (𝟙 _) (by simp [α])) ≫ (mapCoconeIso H φ).hom) := by
    rw [hsupport, map_cocone_lift_zero (H := H) φ a hLift hH]
    exact hcanonical
  change QuasiIso (E.map (supportedCechConsMap F B U V α
    (𝟙 _) (by simp [α])))
  exact (quasiIso_iff_comp_right _ (mapCoconeIso H φ).hom).mp hcomp

/-- A finite cover computes sections of a termwise flasque complex through its
canonical Čech augmentation. -/
lemma finiteCechAugmentation_baseSections_quasiIso
    (s : X ⟶ Spec R) (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (U : List X.Opens) (W : X.Opens)
    (hcover : W ≤ coverUnion U) :
    QuasiIso ((finiteCechAugmentation
      (((baseSectionsPresheafFunctor s).mapHomologicalComplex (.up ℤ)).obj K) U).app (op W)) := by
  let F := baseSectionsPresheafComplex s K
  have hnil : ∀ W, QuasiIso ((evaluatePresheafComplexMap
      (supportedFiniteCechAugmentation F []).hom).app (op W)) := by
    intro W
    exact supportedFiniteCechAugmentation_baseSections_nil_quasiIso s K W
  have hMV : ∀ U V W, QuasiIso ((evaluatePresheafComplexMap
      (supportedCechConsMap F
        ((restrictionComplexFunctor V).obj F) U V
        ((restrictionComplexNatTrans V).app F)
        (𝟙 _) (by simp))).app (op W)) := by
    intro U V W
    exact supportedCechConsMap_baseSections_quasiIso s K hK U V W
  have hsupported := supportedFiniteCechAugmentation_quasiIso_of_MV
    F hnil hMV U
  have hQI : QuasiIso ((evaluatePresheafComplexMap
      (supportedFiniteCechAugmentation F U).hom).app (op W)) :=
    hsupported W
  exact @finiteCechAugmentation_quasiIso_of_supported
    (TopCat.of X) (R : Type u) inferInstance F U W hcover hQI


end GromovWitten.AlgebraicGeometry.Curves
