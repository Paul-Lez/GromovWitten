/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineSectionsFunctor
import GromovWitten.AlgebraicGeometry.Curves.AffineSectionsBaseChange
import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenus
import GromovWitten.AlgebraicGeometry.Curves.ModuleExact
import GromovWitten.AlgebraicGeometry.SheafCohomology.CechPairModule
import GromovWitten.AlgebraicGeometry.SheafCohomology.OpenRestriction
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Derived global sections from flasque module resolutions

Flasque resolutions compute derived global sections both after forgetting to abelian sheaves and
with the module structure induced from the base affine scheme. In positive degrees, the result
also identifies the computed module with the corresponding Ext-based cohomology module.
-/

open CategoryTheory Limits HomologicalComplex
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {R : CommRingCat.{u}} {X : Scheme.{u}}

private def sectionSMulNatTrans (r : Γ(X, ⊤)) :
    moduleToSheafAb X ⟶ moduleToSheafAb X where
  app M := sectionSMul M r
  naturality := fun {_ _} φ => sectionSMul_naturality φ r

set_option backward.isDefEq.respectTransparency false in
private lemma sectionSMulNatTrans_augmentation {M : X.Modules}
    {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ X.Modules).obj M ⟶ K) (r : Γ(X, ⊤)) :
    ((singleMapHomologicalComplex (moduleToSheafAb X) (.up ℕ) 0).inv.app M ≫
      ((moduleToSheafAb X).mapHomologicalComplex (.up ℕ)).map a) ≫
        (NatTrans.mapHomologicalComplex (sectionSMulNatTrans (X := X) r) (.up ℕ)).app K =
    (CochainComplex.single₀ _).map (sectionSMul M r) ≫
      ((singleMapHomologicalComplex (moduleToSheafAb X) (.up ℕ) 0).inv.app M ≫
        ((moduleToSheafAb X).mapHomologicalComplex (.up ℕ)).map a) := by
  apply from_single_hom_ext
  simp only [comp_f, singleMapHomologicalComplex_inv_app_self,
    CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Functor.mapHomologicalComplex_map_f,
    CochainComplex.single₀, single_map_f_self,
    NatTrans.mapHomologicalComplex_app_f]
  change ((moduleToSheafAb X).map (𝟙 M) ≫ (moduleToSheafAb X).map (a.f 0)) ≫
      sectionSMul (K.X 0) r =
    sectionSMul M r ≫ (moduleToSheafAb X).map (𝟙 M) ≫
      (moduleToSheafAb X).map (a.f 0)
  erw [(moduleToSheafAb X).map_id]
  have h := sectionSMul_naturality ((singleObjXSelf (.up ℕ) 0 M).inv ≫ a.f 0) r
  simp only [Functor.map_comp, CochainComplex.single₀ObjXSelf, Iso.refl_inv] at h
  erw [(moduleToSheafAb X).map_id] at h
  simpa only [Category.id_comp] using h

private lemma directForgetHomology_smul (s : X ⟶ Spec R) (K : CochainComplex X.Modules ℕ)
    (n : ℕ) (r : R) :
    let U := forget₂ (ModuleCat R) AddCommGrpCat
    let V := ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℕ)).obj
      (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℕ)).obj K)
    let E := (ShortComplex.mapHomologyIso (V.sc n) U).symm
    U.map (r • 𝟙 (V.homology n)) ≫ E.hom =
      E.hom ≫ HomologicalComplex.homologyMap
        (((sections (⊤ : X.Opens)).mapHomologicalComplex (.up ℕ)).map
          ((NatTrans.mapHomologicalComplex
            (sectionSMulNatTrans (X := X) (baseRingHom R s r)) (.up ℕ)).app K)) n := by
  dsimp only
  let U := forget₂ (ModuleCat R) AddCommGrpCat
  let P := Scheme.Modules.pushforward s
  let G := moduleSpecΓFunctor (R := R)
  let B := sections (⊤ : X.Opens)
  let V := (G.mapHomologicalComplex (.up ℕ)).obj ((P.mapHomologicalComplex (.up ℕ)).obj K)
  let σ := (NatTrans.mapHomologicalComplex
    (sectionSMulNatTrans (X := X) (baseRingHom R s r)) (.up ℕ)).app K
  let q : V ⟶ V := r • 𝟙 V
  let e := (V.sc n).mapHomologyIso U
  have hsc :
      (HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℕ) n).map q =
        r • 𝟙 (V.sc n) := by
    ext j <;> rfl
  have hq : HomologicalComplex.homologyMap q n = r • 𝟙 (V.homology n) := by
    change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℕ) n).map q) = _
    rw [hsc, ShortComplex.homologyMap_smul]
    change r • HomologicalComplex.homologyMap (𝟙 V) n = _
    rw [HomologicalComplex.homologyMap_id]
  have hchain :
      (U.mapHomologicalComplex (.up ℕ)).map q =
        ((sections (⊤ : X.Opens)).mapHomologicalComplex (.up ℕ)).map σ := by
    apply HomologicalComplex.hom_ext
    intro i
    change U.map (q.f i) = (sections (⊤ : X.Opens)).map
      (sectionSMul (K.X i) (baseRingHom R s r))
    ext x
    change r • (show ((Scheme.Modules.pushforward s ⋙
        moduleSpecΓFunctor (R := R)).obj (K.X i)) from x) =
      restrictTop X ⊤ (baseRingHom R s r) • (show Γ(K.X i, ⊤) from x)
    rw [restrictTop_top]
    exact (pushforwardSectionsBaseLinearEquiv s (K.X i)).map_smul r x
  change U.map (r • 𝟙 (V.homology n)) ≫ e.inv =
    e.inv ≫ HomologicalComplex.homologyMap
      (((sections (⊤ : X.Opens)).mapHomologicalComplex (.up ℕ)).map σ) n
  have hnat : U.map (HomologicalComplex.homologyMap q n) ≫ e.inv =
      e.inv ≫ HomologicalComplex.homologyMap
        ((U.mapHomologicalComplex (.up ℕ)).map q) n := by
    convert (ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℕ) n).map q) U)
      using 1
    rfl
  rw [hq, hchain] at hnat
  exact hnat

/-- A flasque resolution by module sheaves computes derived global sections as a module. -/
noncomputable def moduleFlasqueResolutionSectionsIsoDerived
    (s : X ⟶ Spec R) {M : X.Modules} {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ _).obj M ⟶ K) [QuasiIso a]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (n : ℕ) :
    (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℕ)).obj
      (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℕ)).obj K)).homology n ≅
    (ModuleCat.restrictScalars (baseRingHom R s)).obj
      (derivedSectionsModuleCat M (⊤ : X.Opens) n) := by
  let A := moduleToSheafAb X
  let U := forget₂ (ModuleCat R) AddCommGrpCat
  let V : CochainComplex (ModuleCat R) ℕ :=
    ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℕ)).obj
      (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℕ)).obj K)
  let KAb := (A.mapHomologicalComplex (.up ℕ)).obj K
  let aAb : (CochainComplex.single₀ _).obj (A.obj M) ⟶ KAb :=
    (singleMapHomologicalComplex A (.up ℕ) 0).inv.app M ≫
      (A.mapHomologicalComplex (.up ℕ)).map a
  have hqa : QuasiIso aAb := by infer_instance
  let T : ModuleCat R := (ModuleCat.restrictScalars (baseRingHom R s)).obj
    (derivedSectionsModuleCat M (⊤ : X.Opens) n)
  let D : ((sections (⊤ : X.Opens)).rightDerived n).obj (A.obj M) ≅
      (((sections (⊤ : X.Opens)).mapHomologicalComplex (.up ℕ)).obj KAb).homology n :=
    flasqueResolutionSectionsTopIso X aAb hK n
  let E : U.obj (V.homology n) ≅
      (((sections (⊤ : X.Opens)).mapHomologicalComplex (.up ℕ)).obj KAb).homology n :=
    (ShortComplex.mapHomologyIso (V.sc n) U).symm
  let e : U.obj (V.homology n) ≅ U.obj T := E ≪≫ D.symm
  refine ModuleCat.isoMk (M := V.homology n) (N := T) e ?_
  intro r
  let φ := (NatTrans.mapHomologicalComplex
    (sectionSMulNatTrans (X := X) (baseRingHom R s r)) (.up ℕ)).app K
  have haug : aAb ≫ φ =
      (CochainComplex.single₀ _).map (sectionSMul M (baseRingHom R s r)) ≫ aAb :=
    sectionSMulNatTrans_augmentation (X := X) a (baseRingHom R s r)
  have hnat : ((sections (⊤ : X.Opens)).rightDerived n).map
        (sectionSMul M (baseRingHom R s r)) ≫ D.hom =
      D.hom ≫ HomologicalComplex.homologyMap
        (((sections (⊤ : X.Opens)).mapHomologicalComplex (.up ℕ)).map φ) n :=
    flasqueResolutionSectionsTopIso_hom_naturality X aAb aAb
      (sectionSMul M (baseRingHom R s r)) φ haug hK hK n
  have hscalar : U.map (r • 𝟙 (V.homology n)) ≫ E.hom =
      E.hom ≫ HomologicalComplex.homologyMap
        (((sections (⊤ : X.Opens)).mapHomologicalComplex (.up ℕ)).map φ) n :=
    directForgetHomology_smul s K n r
  change e.hom ≫ ((sections (⊤ : X.Opens)).rightDerived n).map
      (sectionSMul M (baseRingHom R s r)) = U.map (r • 𝟙 (V.homology n)) ≫ e.hom
  apply (cancel_mono D.hom).mp
  change ((E.hom ≫ D.inv) ≫ ((sections (⊤ : X.Opens)).rightDerived n).map
      (sectionSMul M (baseRingHom R s r))) ≫ D.hom =
    (U.map (r • 𝟙 (V.homology n)) ≫ E.hom ≫ D.inv) ≫ D.hom
  simp only [Category.assoc]
  rw [hnat, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact hscalar.symm


/-- A flasque module resolution computes positive cohomology as the corresponding Ext module. -/
noncomputable def moduleFlasqueResolutionSectionsIsoCohomology
    (s : X ⟶ Spec R) {M : X.Modules} {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ _).obj M ⟶ K) [QuasiIso a]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (n : ℕ) :
    (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℕ)).obj
      (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℕ)).obj K)).homology (n + 1) ≅
    cohomologyModuleCat R s M (n + 1) := by
  exact moduleFlasqueResolutionSectionsIsoDerived s a hK (n + 1) ≪≫
    ((ModuleCat.restrictScalars (baseRingHom R s)).mapIso
      (cohomologyRightDerivedSectionsLinearEquiv M n).toModuleIso).symm

end GromovWitten.AlgebraicGeometry.Curves
