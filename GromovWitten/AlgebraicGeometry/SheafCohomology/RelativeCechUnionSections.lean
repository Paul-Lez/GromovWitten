/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.RelativeCechUnionSheaves
import GromovWitten.AlgebraicGeometry.SheafCohomology.RelativeCechSections

/-!
# Sections of the relative Čech union complex

Sections of the union, pair, and intersection sheaves identify with the
ordinary Mayer--Vietoris sections complex on the corresponding inverse-image
opens.  A flasque module gives a short exact union complex without a
cover-equals-top hypothesis, and the same comparison applies degreewise to a
flasque complex.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open Scheme.Modules
open GromovWitten.AlgebraicGeometry.Curves
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.SheafCohomology
variable {X S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Sections identify the relative union pushforward with sections on the
union of the two inverse-image opens. -/
def relativeCechUnionSectionsLeftIso (s : X ⟶ S) (M : X.Modules)
    (U V : X.Opens) (W : S.Opens) :
    (moduleToSheafAb S ⋙ sections W).obj ((relativeOpenPushforward s (U ⊔ V)).obj M) ≅
      (sections ((U ⊓ s ⁻¹ᵁ W) ⊔ (V ⊓ s ⁻¹ᵁ W))).obj ((moduleToSheafAb X).obj M) :=
  relativeOpenSectionsIso s M (U ⊔ V) W ≪≫
    M.presheaf.mapIso (eqToIso (by rw [inf_sup_right])).op

set_option backward.isDefEq.respectTransparency false in
private lemma unionToPairSections_fst (s : X ⟶ S) (M : X.Modules)
    (U V : X.Opens) (W : S.Opens) :
    (moduleToSheafAb S ⋙ sections W).map (relativeCechUnionToPair s M U V) ≫
      (relativePairSectionsIso s M U V W).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      (relativeOpenSectionsIso s M (U ⊔ V) W).hom ≫
        M.presheaf.map (homOfLE
          (inf_le_inf_right (s ⁻¹ᵁ W) (le_sup_left : U ≤ U ⊔ V))).op := by
  rw [relativePairSectionsIso_hom_fst, ← Category.assoc, ← Functor.map_comp]
  dsimp only [relativeCechUnionToPair]
  erw [prod.lift_fst]
  exact relativeOpenSectionsIso_restriction s M le_sup_left W

set_option backward.isDefEq.respectTransparency false in
private lemma unionToPairSections_snd (s : X ⟶ S) (M : X.Modules)
    (U V : X.Opens) (W : S.Opens) :
    (moduleToSheafAb S ⋙ sections W).map (relativeCechUnionToPair s M U V) ≫
      (relativePairSectionsIso s M U V W).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      (relativeOpenSectionsIso s M (U ⊔ V) W).hom ≫
        M.presheaf.map (homOfLE
          (inf_le_inf_right (s ⁻¹ᵁ W) (le_sup_right : V ≤ U ⊔ V))).op := by
  rw [relativePairSectionsIso_hom_snd, ← Category.assoc, ← Functor.map_comp]
  dsimp only [relativeCechUnionToPair]
  erw [prod.lift_snd]
  exact relativeOpenSectionsIso_restriction s M le_sup_right W

set_option backward.isDefEq.respectTransparency false in
/-- The union-to-pair map commutes with the section comparisons to the
ordinary Mayer--Vietoris pair on the inverse-image opens. -/
lemma relativeCechUnionToPairSections_comm (s : X ⟶ S) (M : X.Modules)
    (U V : X.Opens) (W : S.Opens) :
    (relativeCechUnionSectionsLeftIso s M U V W).hom ≫
        sectionsToPair ((moduleToSheafAb X).obj M) (U ⊓ s ⁻¹ᵁ W) (V ⊓ s ⁻¹ᵁ W) =
      (moduleToSheafAb S ⋙ sections W).map (relativeCechUnionToPair s M U V) ≫
        (relativePairSectionsIso s M U V W).hom := by
  have hfst : (relativeCechUnionSectionsLeftIso s M U V W).hom ≫
        sectionsToPair ((moduleToSheafAb X).obj M) (U ⊓ s ⁻¹ᵁ W) (V ⊓ s ⁻¹ᵁ W) ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      (moduleToSheafAb S ⋙ sections W).map (relativeCechUnionToPair s M U V) ≫
        (relativePairSectionsIso s M U V W).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) := by
    rw [unionToPairSections_fst]
    change (relativeCechUnionSectionsLeftIso s M U V W).hom ≫
      M.presheaf.map (homOfLE le_sup_left).op = _
    dsimp only [relativeCechUnionSectionsLeftIso, Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc]
    congr 1
    erw [← Functor.map_comp]
    congr 1
  have hsnd : (relativeCechUnionSectionsLeftIso s M U V W).hom ≫
        sectionsToPair ((moduleToSheafAb X).obj M) (U ⊓ s ⁻¹ᵁ W) (V ⊓ s ⁻¹ᵁ W) ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      (moduleToSheafAb S ⋙ sections W).map (relativeCechUnionToPair s M U V) ≫
        (relativePairSectionsIso s M U V W).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) := by
    rw [unionToPairSections_snd]
    change (relativeCechUnionSectionsLeftIso s M U V W).hom ≫
      M.presheaf.map (homOfLE le_sup_right).op = _
    dsimp only [relativeCechUnionSectionsLeftIso, Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc]
    congr 1
    erw [← Functor.map_comp]
    congr 1
  apply AddCommGrpCat.hom_ext
  ext x
  exact Prod.ext (ConcreteCategory.congr_hom hfst x) (ConcreteCategory.congr_hom hsnd x)

set_option backward.isDefEq.respectTransparency false in
/-- Sections identify the relative Čech union short complex with the ordinary
Mayer--Vietoris short complex on the inverse-image opens. -/
def relativeCechUnionSectionsIso (s : X ⟶ S) (M : X.Modules)
    (U V : X.Opens) (W : S.Opens) :
    (relativeCechUnionShortComplex s M U V).map (moduleToSheafAb S ⋙ sections W) ≅
      sectionsMV ((moduleToSheafAb X).obj M) (U ⊓ s ⁻¹ᵁ W) (V ⊓ s ⁻¹ᵁ W) :=
  ShortComplex.isoMk (relativeCechUnionSectionsLeftIso s M U V W)
    (relativePairSectionsIso s M U V W) (relativeIntersectionSectionsIso s M U V W)
    (relativeCechUnionToPairSections_comm s M U V W)
    (relativeFromPairSections_comm s M U V W).symm

set_option backward.isDefEq.respectTransparency false in
/-- A flasque module gives a short exact relative Čech union complex without
assuming that the two opens cover the whole source. -/
lemma relativeCechUnionShortComplex_shortExact (s : X ⟶ S) (M : X.Modules)
    (U V : X.Opens) [TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj M)] :
    (relativeCechUnionShortComplex s M U V).ShortExact := by
  apply module_shortExact_of_sections_shortExact
  intro W
  exact ShortComplex.shortExact_of_iso (relativeCechUnionSectionsIso s M U V W).symm
    (sectionsMV_shortExact _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- A flasque complex gives a degreewise short exact relative Čech union
complex. -/
lemma relativeCechUnionComplexMV_shortExact (K : CochainComplex X.Modules ℕ)
    (s : X ⟶ S) (U V : X.Opens)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n))) :
    (relativeCechUnionComplexMV K s U V).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let _ := hK n
  exact relativeCechUnionShortComplex_shortExact s (K.X n) U V
end GromovWitten.AlgebraicGeometry.SheafCohomology
