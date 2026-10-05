/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.BaseSectionsPresheaf
import GromovWitten.AlgebraicGeometry.Curves.ResolutionSectionsAugmentation
import GromovWitten.AlgebraicGeometry.Curves.ModuleExact
import GromovWitten.AlgebraicGeometry.SheafCohomology.OpenRestriction
import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineCoverVanishing
import GromovWitten.AlgebraicGeometry.SheafCohomology.FlasqueResolution
import GromovWitten.CategoryTheory.LeftExactComplexZero

/-!
# Flasque resolutions on affine opens

For a quasi-coherent module on a locally Noetherian scheme, affine-open sections
send a termwise flasque resolution augmentation to a quasi-isomorphism. Degree
zero follows from left exactness; positive degrees follow from affine vanishing.
The degree-zero comparison is also proved separately for sections on any open,
without affine, Noetherian, quasi-coherence, or flasque hypotheses.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry HomologicalComplex TopologicalSpace
open GromovWitten.AlgebraicGeometry.SheafCohomology

universe u

noncomputable section

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

private def underlyingBaseSectionsIso (s : X ⟶ Spec R) (U : X.Opens) :
    (baseSectionsFunctor s U ⋙ forget₂ (ModuleCat R) AddCommGrpCat) ≅
      moduleToSheafAb X ⋙ sections U := by
  refine NatIso.ofComponents (fun M => Iso.refl _) ?_
  intro M N f
  rfl


private theorem open_image_top {U : X.Opens} :
    U.ι.isOpenEmbedding.functor.obj (⊤ : Opens U.toScheme.toTopCat) = U := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, by trivial⟩

private def sectionsOpenIso (U : X.Opens) :
    (U.ι.isOpenEmbedding.sheafPullback AddCommGrpCat.{u} ⋙
      sections (⊤ : Opens U.toScheme.toTopCat)) ≅ sections U := by
  let h := open_image_top (U := U)
  refine NatIso.ofComponents
    (fun F => (F.obj.mapIso ((eqToIso h).op)).symm) ?_
  intro F G φ
  ext x
  change (φ.hom.app (op (U.ι.isOpenEmbedding.functor.obj ⊤)) ≫
      G.obj.map ((eqToIso h).op).inv) x =
    (F.obj.map ((eqToIso h).op).inv ≫ φ.hom.app (op U)) x
  exact (ConcreteCategory.congr_hom
    (φ.hom.naturality ((eqToIso h).op).inv) x).symm

/-- On any open, a termwise flasque resolution computes derived sections. -/
private noncomputable def flasqueResolutionSectionsOpenIso
    (s : X ⟶ Spec R) {M : X.Modules} {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ _).obj M ⟶ K) [QuasiIso a]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (U : X.Opens) (n : ℕ) :
    (((baseSectionsFunctor s U ⋙ forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (.up ℕ)).obj K).homology n ≅
      ((sections U).rightDerived n).obj ((moduleToSheafAb X).obj M) := by
  let A := moduleToSheafAb X
  let V := U.toScheme.toTopCat
  let Restr := U.ι.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}
  let S := sections (⊤ : Opens V)
  let e : (Restr ⋙ S) ≅ sections U := sectionsOpenIso U
  let H := baseSectionsFunctor s U ⋙ forget₂ (ModuleCat R) AddCommGrpCat
  let eBase : H ≅ A ⋙ sections U := underlyingBaseSectionsIso s U
  let eTotal : H ≅ A ⋙ (Restr ⋙ S) :=
    eBase ≪≫ (Functor.isoWhiskerLeft A e).symm
  let KAb : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
    (A.mapHomologicalComplex (.up ℕ)).obj K
  let aAb : (CochainComplex.single₀ _).obj (A.obj M) ⟶ KAb :=
    (singleMapHomologicalComplex A (.up ℕ) 0).inv.app M ≫
      (A.mapHomologicalComplex (.up ℕ)).map a
  have hqaAb : QuasiIso aAb := by infer_instance
  let aR : (CochainComplex.single₀ _).obj (Restr.obj (A.obj M)) ⟶
      (Restr.mapHomologicalComplex (.up ℕ)).obj KAb :=
    (singleMapHomologicalComplex Restr (.up ℕ) 0).inv.app (A.obj M) ≫
      (Restr.mapHomologicalComplex (.up ℕ)).map aAb
  have hqaR : QuasiIso aR := by
    dsimp [aR]
    infer_instance
  have hKR (i : ℕ) : TopCat.Sheaf.IsFlasque
      (((Restr.mapHomologicalComplex (.up ℕ)).obj KAb).X i) := by
    change TopCat.Sheaf.IsFlasque (Restr.obj (A.obj (K.X i)))
    exact openRestriction_isFlasque U.ι.isOpenEmbedding _
  let D := flasqueResolutionSectionsTopIso V aR hKR n
  let E₁ := Functor.mapHomologicalComplexCompIso (Iso.refl (Restr ⋙ S)) (.up ℕ)
  let E₂ := Functor.mapHomologicalComplexCompIso
    (Iso.refl (A ⋙ (Restr ⋙ S))) (.up ℕ)
  let E₃ := Functor.isoWhiskerLeft (A.mapHomologicalComplex (.up ℕ)) E₁ ≪≫ E₂
  let E₄ := NatIso.mapHomologicalComplex eTotal (.up ℕ)
  let E := (E₄.app K) ≪≫ (E₃.app K).symm
  let hopen := derivedSectionsOpenIso U.ι.isOpenEmbedding (A.obj M) n
  have hopen' : ((sections (⊤ : Opens V)).rightDerived n).obj (Restr.obj (A.obj M)) ≅
      ((sections U).rightDerived n).obj (A.obj M) := by
    rw [open_image_top] at hopen
    exact hopen.symm
  exact (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) n).mapIso E ≪≫
    D.symm ≪≫ hopen'


private lemma preservesFiniteLimits_sections {Y : TopCat.{u}} (W : Opens Y) :
    PreservesFiniteLimits (sections W) := by
  unfold sections
  have hForget : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat Y) :=
    inferInstanceAs (PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}))
  have hEval : PreservesFiniteLimits
      ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (op W)) := by infer_instance
  infer_instance

/-- Sections on any open, with their affine-base module structure, preserve finite limits. -/
lemma baseSections_preservesFiniteLimits
    (s : X ⟶ Spec R) (U : X.Opens) :
    PreservesFiniteLimits (baseSectionsFunctor s U) := by
  let F := baseSectionsFunctor s U
  let H := F ⋙ forget₂ (ModuleCat R) AddCommGrpCat
  let A := moduleToSheafAb X
  let e : H ≅ A ⋙ sections U := underlyingBaseSectionsIso s U
  have hSections : PreservesFiniteLimits (sections U) :=
    preservesFiniteLimits_sections U
  have hA : PreservesFiniteLimits A := inferInstance
  have hT : PreservesFiniteLimits (A ⋙ sections U) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ A (sections U) hA hSections
  have hH : PreservesFiniteLimits H :=
    @preservesFiniteLimits_of_natIso _ _ _ _ H (A ⋙ sections U) e.symm hT
  exact @preservesFiniteLimits_of_reflects_of_preserves _ _ _ _ _ _ F
    (forget₂ (ModuleCat R) AddCommGrpCat) hH inferInstance

/-- The affine-open section functor sends a flasque module resolution augmentation to a
quasi-isomorphism. Its degree-zero part follows from left exactness; in positive degrees the
flasque comparison identifies the target homology with affine right-derived sections, which
vanish for quasi-coherent modules. -/
theorem affineOpen_sections_augmentation_quasiIso
    [IsLocallyNoetherian X] (s : X ⟶ Spec R) (U : X.Opens) (hU : IsAffineOpen U)
    (M : X.Modules) [M.IsQuasicoherent] {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ _).obj M ⟶ K) [QuasiIso a]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n))) :
    QuasiIso (((baseSectionsFunctor s U).mapHomologicalComplex (.up ℕ)).map a) := by
  let F := baseSectionsFunctor s U
  have hF : PreservesFiniteLimits F := baseSections_preservesFiniteLimits s U
  have h0 : QuasiIsoAt ((F.mapHomologicalComplex (.up ℕ)).map a) 0 :=
    @CategoryTheory.Functor.quasiIsoAt_zero_map_of_preservesFiniteLimits X.Modules (ModuleCat R)
      inferInstance inferInstance inferInstance inferInstance F inferInstance hF
      ((CochainComplex.single₀ _).obj M) K a inferInstance
  apply (quasiIso_iff _).2
  intro i
  cases i with
  | zero => exact h0
  | succ n =>
      let q := n + 1
      let T := (F.mapHomologicalComplex (.up ℕ)).obj K
      let Uforget := forget₂ (ModuleCat R) AddCommGrpCat
      let H := F ⋙ Uforget
      let Ec := Functor.mapHomologicalComplexCompIso (Iso.refl H) (.up ℕ)
      let Ehom := (ShortComplex.mapHomologyIso (T.sc q) Uforget).symm
      let E := Ehom ≪≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) q).mapIso (Ec.app K)
      have hOpen := flasqueResolutionSectionsOpenIso s a hK U q
      have hVan := isZero_rightDerived_sections_affineOpen_succ U hU M n
      have hAb : IsZero (Uforget.obj (T.homology q)) :=
        IsZero.of_iso hVan (E ≪≫ hOpen)
      have hTarget : IsZero (T.homology q) := by
        have hs : Subsingleton (Uforget.obj (T.homology q)) :=
          AddCommGrpCat.subsingleton_of_isZero hAb
        exact @ModuleCat.isZero_of_subsingleton R inferInstance (T.homology q) hs
      let eSingle := (singleMapHomologicalComplex F (.up ℕ) 0).app M
      let ESingle := (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) q).mapIso eSingle
      have hSource : IsZero (((F.mapHomologicalComplex (.up ℕ)).obj
          ((CochainComplex.single₀ _).obj M)).homology q) := by
        have hs := HomologicalComplex.isZero_single_obj_homology
          (c := .up ℕ) (j := 0) (F.obj M) q (by omega)
        exact IsZero.of_iso hs ESingle
      rw [quasiIsoAt_iff_isIso_homologyMap]
      exact hSource.isIso hTarget _


set_option backward.isDefEq.respectTransparency false in
/-- On every open, the section-presheaf augmentation of a nonnegative resolution
is a quasi-isomorphism in degree zero, without affine or Noetherian assumptions. -/
lemma resolutionSectionsAugmentation_quasiIsoAt_zero (s : X ⟶ Spec R)
    {M : X.Modules} {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ _).obj M ⟶ K) (W : X.Opens) [QuasiIsoAt a 0] :
    QuasiIsoAt
      ((((evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op W)).mapHomologicalComplex (.up ℤ)).map
        (resolutionSectionsAugmentation s a)) (0 : ℤ) := by
  let F := baseSectionsPresheafFunctor s
  let H := (evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op W)
  let E := H.mapHomologicalComplex (.up ℤ)
  let B := F.mapHomologicalComplex (.up ℤ)
  let e := HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl
  have : PreservesFiniteLimits (baseSectionsFunctor s W) :=
    baseSections_preservesFiniteLimits s W
  have : QuasiIsoAt (((baseSectionsFunctor s W).mapHomologicalComplex (.up ℕ)).map a) 0 :=
    Functor.quasiIsoAt_zero_map_of_preservesFiniteLimits (baseSectionsFunctor s W) a
  have hq : QuasiIsoAt (E.map (B.map (HomologicalComplex.extendMap a
      ComplexShape.embeddingUpNat))) (0 : ℤ) := by
    change QuasiIsoAt (((baseSectionsFunctor s W).mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat)) (0 : ℤ)
    exact Functor.quasiIsoAt_map_extendMap (baseSectionsFunctor s W)
      ComplexShape.embeddingUpNat _ a 0
  change QuasiIsoAt (E.map
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M ≫
      B.map (e.inv ≫ HomologicalComplex.extendMap a ComplexShape.embeddingUpNat))) (0 : ℤ)
  rw [E.map_comp, B.map_comp, E.map_comp]
  infer_instance

end GromovWitten.AlgebraicGeometry.Curves
