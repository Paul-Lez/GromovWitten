/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.MayerVietorisNaturality
import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineCoverVanishing
import GromovWitten.AlgebraicGeometry.SheafCohomology.SheafHComparison

/-!
# The two-open Čech comparison in degree one

The cokernel of the difference of restrictions to an intersection computes derived sections
in degree one whenever the two opens have vanishing first cohomology. The comparison is
induced by the Mayer–Vietoris connecting map, with its characteristic equation and naturality.

For a quasi-coherent module on a locally Noetherian scheme covered by two affine opens,
acyclicity is proved geometrically. No separatedness assumption is needed in degree one.
The final additive equivalence identifies this Čech group with Mathlib's Ext-based `Sheaf.H`.
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open TopologicalSpace Opposite
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {X : TopCat.{u}}

/-! The degree-one two-open Čech object. -/

/-- The degree-one Čech cohomology group of a sheaf for the two-open family `U, V`.

It is the cokernel of the restriction-difference map from the pair of section groups
to the intersection section group. -/
def cechPairCohomology (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) :
    AddCommGrpCat.{u} :=
  cokernel (sectionsFromPair F U V)

private lemma preservesFiniteLimits_sections (U : Opens X) :
    PreservesFiniteLimits (sections U) := by
  unfold sections
  have : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat X) :=
    inferInstanceAs (PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat))
  have : PreservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U)) := by infer_instance
  infer_instance

private noncomputable def pairZeroComparisonIso
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) :
    sectionsPair F U V ≅
      ((sectionsPairFunctor U V).rightDerived 0).obj F := by
  have : PreservesFiniteLimits (sections U) := preservesFiniteLimits_sections U
  have : PreservesFiniteLimits (sections V) := preservesFiniteLimits_sections V
  exact (AddCommGrpCat.biprodIsoProd ((sections U).obj F) ((sections V).obj F)).symm ≪≫
    biprod.mapIso ((Functor.rightDerivedZeroIsoSelf (sections U)).app F).symm
      ((Functor.rightDerivedZeroIsoSelf (sections V)).app F).symm ≪≫
    (sectionsPairRightDerivedIso U V F 0).symm

private lemma pairZeroComparisonIso_eq
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) :
    (pairZeroComparisonIso F U V).hom =
      (Functor.toRightDerivedZero (sectionsPairFunctor U V)).app F := by
  have : PreservesFiniteLimits (sections U) := preservesFiniteLimits_sections U
  have : PreservesFiniteLimits (sections V) := preservesFiniteLimits_sections V
  let eU := (Functor.rightDerivedZeroIsoSelf (sections U)).app F
  let eV := (Functor.rightDerivedZeroIsoSelf (sections V)).app F
  have heU : eU.inv = (Functor.toRightDerivedZero (sections U)).app F := by rfl
  have heV : eV.inv = (Functor.toRightDerivedZero (sections V)).app F := by rfl
  let ePair := sectionsPairRightDerivedIso U V F 0
  let rawU : AddCommGrpCat := (sections U).obj F
  let rawV : AddCommGrpCat := (sections V).obj F
  let eProd : (rawU ⊞ rawV) ≅ sectionsPair F U V :=
    AddCommGrpCat.biprodIsoProd rawU rawV
  have hProdFst : eProd.inv ≫ biprod.fst = (sectionsPairFstNat U V).app F := by
    change (rawU.biprodIsoProd rawV).inv ≫ biprod.fst =
      AddCommGrpCat.ofHom (AddMonoidHom.fst (↑rawU) (↑rawV))
    exact AddCommGrpCat.biprodIsoProd_inv_comp_fst rawU rawV
  have hProdSnd : eProd.inv ≫ biprod.snd = (sectionsPairSndNat U V).app F := by
    change (rawU.biprodIsoProd rawV).inv ≫ biprod.snd =
      AddCommGrpCat.ofHom (AddMonoidHom.snd (↑rawU) (↑rawV))
    exact AddCommGrpCat.biprodIsoProd_inv_comp_snd rawU rawV
  have hfst :
      (Functor.toRightDerivedZero (sectionsPairFunctor U V)).app F ≫ ePair.hom ≫
          biprod.fst =
        (sectionsPairFstNat U V).app F ≫
          (Functor.toRightDerivedZero (sections U)).app F := by
    have he : ePair.hom ≫ biprod.fst =
        (NatTrans.rightDerived (sectionsPairFstNat U V) 0).app F := by
      dsimp [ePair, sectionsPairRightDerivedIso]
      simp
    rw [he]
    exact NatTrans.toRightDerivedZero_comp (sectionsPairFstNat U V) F
  have hsnd :
      (Functor.toRightDerivedZero (sectionsPairFunctor U V)).app F ≫ ePair.hom ≫
          biprod.snd =
        (sectionsPairSndNat U V).app F ≫
          (Functor.toRightDerivedZero (sections V)).app F := by
    have he : ePair.hom ≫ biprod.snd =
        (NatTrans.rightDerived (sectionsPairSndNat U V) 0).app F := by
      dsimp [ePair, sectionsPairRightDerivedIso]
      simp
    rw [he]
    exact NatTrans.toRightDerivedZero_comp (sectionsPairSndNat U V) F
  dsimp [sectionsPairFunctor] at hfst hsnd ⊢
  apply (cancel_mono ePair.hom).mp
  apply biprod.hom_ext
  · simp only [Category.assoc]
    change (eProd.inv ≫ biprod.map eU.inv eV.inv ≫ ePair.inv) ≫ ePair.hom ≫
      biprod.fst = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.map_fst]
    rw [← Category.assoc, hProdFst, heU, ← hfst]
    rfl
  · simp only [Category.assoc]
    change (eProd.inv ≫ biprod.map eU.inv eV.inv ≫ ePair.inv) ≫ ePair.hom ≫
      biprod.snd = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.map_snd]
    rw [← Category.assoc, hProdSnd, heV, ← hsnd]
    rfl

private def pairZeroComparison
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) :
    sectionsPair F U V ⟶
      ((sectionsPairFunctor U V).rightDerived 0).obj F :=
  (pairZeroComparisonIso F U V).hom

private lemma pairZeroComparison_naturality
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) :
    pairZeroComparison F U V ≫ (mvRightDerivedFromPair (F := F) U V 0) =
      (sectionsFromPairNat U V).app F ≫
        (Functor.toRightDerivedZero (sections (U ⊓ V))).app F := by
  have h := NatTrans.toRightDerivedZero_comp (sectionsFromPairNat U V) F
  change (Functor.toRightDerivedZero (sectionsPairFunctor U V)).app F ≫
      (NatTrans.rightDerived (sectionsFromPairNat U V) 0).app F = _ at h
  rw [pairZeroComparison, pairZeroComparisonIso_eq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The Čech cokernel computes degree-one derived sections on the union of two acyclic opens. -/
def cechPairCohomologyIsoRightDerived
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X)
    (hU : IsZero (((sections U).rightDerived 1).obj F))
    (hV : IsZero (((sections V).rightDerived 1).obj F)) :
    cechPairCohomology F U V ≅
      ((sections (U ⊔ V)).rightDerived 1).obj F := by
  have : PreservesFiniteLimits (sections U) := preservesFiniteLimits_sections U
  have : PreservesFiniteLimits (sections V) := preservesFiniteLimits_sections V
  have : PreservesFiniteLimits (sections (U ⊓ V)) :=
    preservesFiniteLimits_sections (U ⊓ V)
  have hPair : IsZero (((sectionsPairFunctor U V).rightDerived 1).obj F) := by
    apply IsZero.of_iso ((biprod_isZero_iff _ _).mpr ⟨hU, hV⟩)
      (sectionsPairRightDerivedIso U V F 1)
  let δ := mvRightDerivedConnecting (F := F) U V 0
  let eInt := (Functor.rightDerivedZeroIsoSelf (sections (U ⊓ V))).app F
  let k := eInt.inv ≫ δ
  have hδepi : Epi δ := by
    let Snext := ShortComplex.mk (mvRightDerivedConnecting (F := F) U V 0)
      (mvRightDerivedToPair (F := F) U V (0 + 1))
      (mvRightDerivedConnecting_comp_mvRightDerivedToPair (F := F) U V 0)
    have hnext : Snext.Exact := by
      simpa [Snext] using (mvRightDerived_exact_at_next_union (F := F) U V 0)
    have htargetzero : IsZero (((sectionsPairFunctor U V).rightDerived (0 + 1)).obj F) := by
      simpa using hPair
    have hgzero : Snext.g = 0 := htargetzero.eq_of_tgt _ _
    exact hnext.epi_f hgzero
  have : Epi δ := hδepi
  have hk : sectionsFromPair F U V ≫ k = 0 := by
    dsimp [k]
    change (sectionsFromPairNat U V).app F ≫ eInt.inv ≫ δ = 0
    have heInt : eInt.inv = (Functor.toRightDerivedZero (sections (U ⊓ V))).app F := by
      rfl
    have hnat := pairZeroComparison_naturality F U V
    dsimp [sectionsPairFunctor] at hnat
    rw [heInt]
    change ((sectionsFromPairNat U V).app F ≫
      (Functor.toRightDerivedZero (sections (U ⊓ V))).app F) ≫ δ = 0
    have hnat' := congrArg (fun q => q ≫ δ) hnat.symm
    calc
      ((sectionsFromPairNat U V).app F ≫
          (Functor.toRightDerivedZero (sections (U ⊓ V))).app F) ≫ δ =
          (pairZeroComparison F U V ≫ mvRightDerivedFromPair (F := F) U V 0) ≫ δ := by
        simpa only [sectionsPairFunctor, Category.assoc] using hnat'
      _ = 0 := by
        rw [Category.assoc, mvRightDerivedFromPair_comp_mvRightDerivedConnecting, comp_zero]
  have : IsIso (pairZeroComparison F U V) := by
    dsimp [pairZeroComparison]
    infer_instance
  have : Epi (pairZeroComparison F U V) := by infer_instance
  have hraw :
      IsColimit (CokernelCofork.ofπ k hk) := by
    have hder := (mvRightDerived_exact_at_intersection (F := F) U V 0)
    have hderc : IsColimit (CokernelCofork.ofπ δ (by
        exact mvRightDerivedFromPair_comp_mvRightDerivedConnecting (F := F) U V 0)) :=
      hder.gIsCokernel
    have : Epi k := by
      dsimp [k]
      infer_instance
    apply CokernelCofork.IsColimit.ofπ' k hk
    intro W φ hφ
    have hφ' : mvRightDerivedFromPair (F := F) U V 0 ≫ eInt.hom ≫ φ = 0 := by
      change (sectionsFromPairNat U V).app F ≫ φ = 0 at hφ
      apply (cancel_epi (pairZeroComparison F U V)).mp
      have hnat := pairZeroComparison_naturality F U V
      dsimp [sectionsPairFunctor] at hnat
      change (pairZeroComparison F U V ≫ mvRightDerivedFromPair (F := F) U V 0) ≫
        eInt.hom ≫ φ = pairZeroComparison F U V ≫ 0
      have hnat' := congrArg (fun q => q ≫ eInt.hom ≫ φ) hnat
      have heInt : eInt.inv =
          (Functor.toRightDerivedZero (sections (U ⊓ V))).app F := by rfl
      calc
        (pairZeroComparison F U V ≫ mvRightDerivedFromPair (F := F) U V 0) ≫
            eInt.hom ≫ φ =
            ((sectionsFromPairNat U V).app F ≫
              (Functor.toRightDerivedZero (sections (U ⊓ V))).app F) ≫
              eInt.hom ≫ φ := by
                simpa only [sectionsPairFunctor, Category.assoc] using hnat'
        _ = pairZeroComparison F U V ≫ 0 := by
          rw [← heInt, Category.assoc, eInt.inv_hom_id_assoc, hφ, comp_zero]
    let s' : CokernelCofork (mvRightDerivedFromPair (F := F) U V 0) :=
      CokernelCofork.ofπ (eInt.hom ≫ φ) hφ'
    refine ⟨hderc.desc s', ?_⟩
    have hfac : δ ≫ hderc.desc s' = eInt.hom ≫ φ := by
      simpa [s'] using (hderc.fac s' WalkingParallelPair.one)
    dsimp [k]
    rw [Category.assoc, hfac]
    simp
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    hraw

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma cokernel_π_cechPairCohomologyIsoRightDerived_hom
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X)
    (hU : IsZero (((sections U).rightDerived 1).obj F))
    (hV : IsZero (((sections V).rightDerived 1).obj F)) :
    cokernel.π (sectionsFromPair F U V) ≫
      (cechPairCohomologyIsoRightDerived F U V hU hV).hom =
        (sections (U ⊓ V)).toRightDerivedZero.app F ≫
          mvRightDerivedConnecting (F := F) U V 0 := by
  dsimp only [cechPairCohomologyIsoRightDerived]
  change cokernel.π (sectionsFromPair F U V) ≫
    (cokernelIsCokernel (sectionsFromPair F U V)).desc _ = _
  exact Cofork.IsColimit.π_desc (cokernelIsCokernel (sectionsFromPair F U V))

set_option backward.isDefEq.respectTransparency false in
/-- The two-open Čech comparison is natural in the sheaf. -/
lemma cechPairCohomologyIsoRightDerived_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (φ : F ⟶ G) (U V : Opens X)
    (hFU : IsZero (((sections U).rightDerived 1).obj F))
    (hFV : IsZero (((sections V).rightDerived 1).obj F))
    (hGU : IsZero (((sections U).rightDerived 1).obj G))
    (hGV : IsZero (((sections V).rightDerived 1).obj G)) :
    cokernel.map (sectionsFromPair F U V) (sectionsFromPair G U V)
        ((sectionsPairFunctor U V).map φ) ((sections (U ⊓ V)).map φ)
        ((sectionsFromPairNat U V).naturality φ).symm ≫
      (cechPairCohomologyIsoRightDerived G U V hGU hGV).hom =
    (cechPairCohomologyIsoRightDerived F U V hFU hFV).hom ≫
      ((sections (U ⊔ V)).rightDerived 1).map φ := by
  apply (cancel_epi (cokernel.π (sectionsFromPair F U V))).mp
  rw [cokernel.π_desc_assoc, Category.assoc,
    cokernel_π_cechPairCohomologyIsoRightDerived_hom,
    cokernel_π_cechPairCohomologyIsoRightDerived_hom_assoc]
  rw [← Category.assoc, (sections (U ⊓ V)).toRightDerivedZero.naturality φ,
    Category.assoc, mvRightDerivedConnecting_naturality]

/-- The comparison specializes to a two-affine cover of a locally Noetherian scheme, using the
geometric affine acyclicity theorem for the two section terms. -/
def cechPairCohomologyIsoRightDerived_of_affine
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = (⊤ : X.Opens)) (M : X.Modules) [M.IsQuasicoherent] :
    cechPairCohomology ((moduleToSheafAb X).obj M) U V ≅
      ((sections (⊤ : Opens X)).rightDerived 1).obj ((moduleToSheafAb X).obj M) := by
  rw [← hcover]
  exact cechPairCohomologyIsoRightDerived _ U V
    (isZero_rightDerived_sections_affineOpen_succ U hU M 0)
    (isZero_rightDerived_sections_affineOpen_succ V hV M 0)

set_option backward.isDefEq.respectTransparency false in
/-- The two-affine Čech cokernel computes the Ext-based sheaf cohomology group in degree one. -/
def cechPairCohomologyAddEquivSheafH_of_affine
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = (⊤ : X.Opens)) (M : X.Modules) [M.IsQuasicoherent] :
    (cechPairCohomology ((moduleToSheafAb X).obj M) U V : Type u) ≃+
      CategoryTheory.Sheaf.H
        ((moduleToSheafAb X).obj M :
          Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) 1 :=
  (isoToAddEquiv (cechPairCohomologyIsoRightDerived_of_affine U V hU hV hcover M)).trans
    (sheafHRightDerivedSectionsAddEquiv
      (F := ((moduleToSheafAb X).obj M :
        Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) 0).symm

end GromovWitten.AlgebraicGeometry.SheafCohomology
