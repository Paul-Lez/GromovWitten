/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.SectionsMayerVietoris
import GromovWitten.AlgebraicGeometry.SheafCohomology.RightDerivedHomology
import GromovWitten.AlgebraicGeometry.SheafCohomology.DerivedSectionsPair

/-!
# Derived sections in a two-open Mayer–Vietoris cover

The maps below are the maps induced on actual right-derived sections by the
restriction difference sequence. Exactness at every position and the initial
monomorphism are obtained from the short exact sequence of section complexes
on an injective resolution. The connecting map is natural in the sheaf, as
proved in `MayerVietorisNaturality`.
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open TopologicalSpace Opposite
open GromovWitten.AlgebraicGeometry.SheafCohomology
open CochainComplex

noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {X : TopCat.{u}}

private lemma sectionsToPairNat_comp_zero (U V : Opens X) :
    sectionsToPairNat U V ≫ sectionsFromPairNat U V = 0 := by
  apply NatTrans.ext
  funext F
  exact sectionsToPair_fromPair F U V

/-- The canonical derived map from sections on a union to the pair of sections. -/
noncomputable def mvRightDerivedToPair
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (U V : Opens X) (n : ℕ) :
    ((sections (U ⊔ V)).rightDerived n).obj F ⟶
      ((sectionsPairFunctor U V).rightDerived n).obj F :=
  (NatTrans.rightDerived (sectionsToPairNat U V) n).app F

/-- The canonical derived restriction-difference map to an intersection. -/
noncomputable def mvRightDerivedFromPair
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (U V : Opens X) (n : ℕ) :
    ((sectionsPairFunctor U V).rightDerived n).obj F ⟶
      ((sections (U ⊓ V)).rightDerived n).obj F :=
  (NatTrans.rightDerived (sectionsFromPairNat U V) n).app F

/-- Consecutive maps in the derived Mayer–Vietoris sequence compose to zero. -/
lemma mvRightDerivedToPair_comp_mvRightDerivedFromPair
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (U V : Opens X) (n : ℕ) :
    mvRightDerivedToPair (F := F) U V n ≫
      mvRightDerivedFromPair (F := F) U V n = 0 := by
  change ((NatTrans.rightDerived (sectionsToPairNat U V) n ≫
    NatTrans.rightDerived (sectionsFromPairNat U V) n).app F) = 0
  rw [← NatTrans.rightDerived_comp, sectionsToPairNat_comp_zero]
  let I := InjectiveResolution.of F
  rw [InjectiveResolution.rightDerived_app_eq (P := I)]
  have hz := (show
      (NatTrans.mapHomologicalComplex
        (0 : sections (U ⊔ V) ⟶ sections (U ⊓ V)) (.up ℕ)).app
        I.cocomplex = 0 by
      ext i
      rfl)
  simp only [hz, Functor.map_zero, zero_comp, comp_zero]

/-- The connecting morphism, computed from the fixed resolution of `F`.

Mathlib does not expose the connecting component of the derived-functor long exact
sequence as a natural transformation, so this definition uses its canonical
`InjectiveResolution.of F` computation. -/
noncomputable def mvRightDerivedConnecting
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (U V : Opens X) (n : ℕ) :
    ((sections (U ⊓ V)).rightDerived n).obj F ⟶
      ((sections (U ⊔ V)).rightDerived (n + 1)).obj F := by
  let I := InjectiveResolution.of F
  let S := sectionsComplexMV I.cocomplex U V
  let hS := sectionsComplexMV_shortExact I.cocomplex
    (fun k => TopCat.Sheaf.isFlasque_of_injective X _) U V
  let A :=
    ((sections (U ⊔ V)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let C :=
    ((sections (U ⊓ V)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let Hn := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) n
  let Hnext :=
    HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) (n + 1)
  let eA : Hnext.obj A ≅ A.homology (n + 1) :=
    eqToIso (HomologicalComplex.homologyFunctor_obj
      AddCommGrpCat (.up ℕ) (n + 1) A)
  let eC : Hn.obj C ≅ C.homology n :=
    eqToIso (HomologicalComplex.homologyFunctor_obj
      AddCommGrpCat (.up ℕ) n C)
  let hrel : (ComplexShape.up ℕ).Rel n (n + 1) := by rfl
  exact (I.isoRightDerivedObj (sections (U ⊓ V)) n).hom ≫ eC.hom ≫
    hS.δ n (n + 1) hrel ≫ eA.inv ≫
    (I.isoRightDerivedObj (sections (U ⊔ V)) (n + 1)).inv

set_option backward.isDefEq.respectTransparency false in
/-- Degreewise exactness of the actual derived Mayer–Vietoris sequence.

The pair term is canonically isomorphic to the biproduct of derived sections
on the two opens, via `sectionsPairRightDerivedIso`; its map to the
intersection is induced by the difference of the two restriction maps. -/
theorem mvRightDerived_exact
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U V : Opens X) (n : ℕ) :
    (ShortComplex.mk (mvRightDerivedToPair (F := F) U V n)
      (mvRightDerivedFromPair (F := F) U V n)
      (mvRightDerivedToPair_comp_mvRightDerivedFromPair (F := F) U V n)).Exact := by
  let hS := sectionsComplexMV_shortExact I.cocomplex
    (fun k => TopCat.Sheaf.isFlasque_of_injective X _) U V
  let eA := I.isoRightDerivedHomologyObj (sections (U ⊔ V)) n
  let eB := I.isoRightDerivedHomologyObj (sectionsPairFunctor U V) n
  let eC := I.isoRightDerivedHomologyObj (sections (U ⊓ V)) n
  let R := ShortComplex.mk (mvRightDerivedToPair (F := F) U V n)
    (mvRightDerivedFromPair (F := F) U V n)
    (mvRightDerivedToPair_comp_mvRightDerivedFromPair (F := F) U V n)
  let S := sectionsComplexMV I.cocomplex U V
  let H := ShortComplex.mk (HomologicalComplex.homologyMap S.f n)
    (HomologicalComplex.homologyMap S.g n) (by
      rw [← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero])
  let e : R ≅ H := ShortComplex.isoMk eA eB eC
    (by
      dsimp only [R, H, mvRightDerivedToPair]
      rw [I.rightDerived_app_eq_homologyMap (sectionsToPairNat U V) n]
      simp [Category.assoc, eA, eB, S, sectionsComplexMV])
    (by
      dsimp only [R, H, mvRightDerivedFromPair]
      rw [I.rightDerived_app_eq_homologyMap (sectionsFromPairNat U V) n]
      simp [Category.assoc, eB, eC, S, sectionsComplexMV])
  exact ShortComplex.exact_of_iso e.symm (hS.homology_exact₂ n)

/-- The connecting map is followed by the union-to-pair map by zero. -/
lemma mvRightDerivedConnecting_comp_mvRightDerivedToPair
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (U V : Opens X) (n : ℕ) :
    mvRightDerivedConnecting U V n ≫
      mvRightDerivedToPair (F := F) U V (n + 1) = 0 := by
  let I := InjectiveResolution.of F
  let hS := sectionsComplexMV_shortExact I.cocomplex
    (fun k => TopCat.Sheaf.isFlasque_of_injective X _) U V
  dsimp [sectionsComplexMV] at hS
  let eC := I.isoRightDerivedHomologyObj (sections (U ⊓ V)) n
  let eA := I.isoRightDerivedHomologyObj (sections (U ⊔ V)) (n + 1)
  let eB := I.isoRightDerivedHomologyObj (sectionsPairFunctor U V) (n + 1)
  let f :=
    (NatTrans.mapHomologicalComplex (sectionsToPairNat U V) (.up ℕ)).app
      I.cocomplex
  let hrel : (ComplexShape.up ℕ).Rel n (n + 1) := by rfl
  dsimp [mvRightDerivedConnecting, mvRightDerivedToPair]
  change eC.hom ≫ hS.δ n (n + 1) hrel ≫ eA.inv ≫
      (NatTrans.rightDerived (sectionsToPairNat U V) (n + 1)).app F = 0
  rw [I.rightDerived_app_eq_homologyMap (sectionsToPairNat U V) (n + 1)]
  dsimp [eC, eA, eB, f, InjectiveResolution.isoRightDerivedHomologyObj]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Preadditive.IsIso.comp_left_eq_zero]
  rw [← Category.assoc (hS.δ n (n + 1) hrel), hS.δ_comp]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The derived Mayer–Vietoris sequence starts with a monomorphism in degree zero. -/
lemma mono_mvRightDerivedToPair_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) :
    Mono (mvRightDerivedToPair (F := F) U V 0) := by
  let I := InjectiveResolution.of F
  let φ := (NatTrans.mapHomologicalComplex (sectionsToPairNat U V) (.up ℕ)).app I.cocomplex
  have : Mono (φ.f 0) := (AddCommGrpCat.mono_iff_injective _).mpr
    (sectionsToPair_injective (I.cocomplex.X 0) U V)
  have : Mono (HomologicalComplex.homologyMap φ 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel φ 0
      (fun i => Nat.succ_ne_zero i)
  dsimp only [mvRightDerivedToPair]
  rw [I.rightDerived_app_eq_homologyMap (sectionsToPairNat U V) 0]
  infer_instance

/-- The restriction-difference map followed by the connecting map is zero. -/
lemma mvRightDerivedFromPair_comp_mvRightDerivedConnecting
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (U V : Opens X) (n : ℕ) :
    mvRightDerivedFromPair (F := F) U V n ≫ mvRightDerivedConnecting (F := F) U V n = 0 := by
  let I := InjectiveResolution.of F
  let hS := sectionsComplexMV_shortExact I.cocomplex
    (fun k => TopCat.Sheaf.isFlasque_of_injective X _) U V
  dsimp [sectionsComplexMV] at hS
  let eB := I.isoRightDerivedHomologyObj (sectionsPairFunctor U V) n
  let eC := I.isoRightDerivedHomologyObj (sections (U ⊓ V)) n
  let eA := I.isoRightDerivedHomologyObj (sections (U ⊔ V)) (n + 1)
  let g := (NatTrans.mapHomologicalComplex (sectionsFromPairNat U V) (.up ℕ)).app
    I.cocomplex
  let hrel : (ComplexShape.up ℕ).Rel n (n + 1) := by rfl
  dsimp [mvRightDerivedFromPair, mvRightDerivedConnecting]
  rw [I.rightDerived_app_eq_homologyMap (sectionsFromPairNat U V) n]
  change eB.hom ≫ HomologicalComplex.homologyMap g n ≫ eC.inv ≫ eC.hom ≫
    hS.δ n (n + 1) hrel ≫ eA.inv = 0
  simp only [Iso.inv_hom_id_assoc, Preadditive.IsIso.comp_left_eq_zero]
  have hz : HomologicalComplex.homologyMap g n ≫ hS.δ n (n + 1) hrel = 0 := by
    simpa [g] using hS.comp_δ n (n + 1) hrel
  rw [← Category.assoc, hz, zero_comp]

/-- Exactness of the derived Mayer–Vietoris sequence at the intersection term. -/
lemma mvRightDerived_exact_at_intersection
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (U V : Opens X) (n : ℕ) :
    (ShortComplex.mk (mvRightDerivedFromPair (F := F) U V n)
      (mvRightDerivedConnecting (F := F) U V n)
      (mvRightDerivedFromPair_comp_mvRightDerivedConnecting (F := F) U V n)).Exact := by
  let I := InjectiveResolution.of F
  let S := sectionsComplexMV I.cocomplex U V
  let hS := sectionsComplexMV_shortExact I.cocomplex
    (fun k => TopCat.Sheaf.isFlasque_of_injective X _) U V
  dsimp [sectionsComplexMV] at hS
  let eA := I.isoRightDerivedHomologyObj (sections (U ⊔ V)) n
  let eB := I.isoRightDerivedHomologyObj (sectionsPairFunctor U V) n
  let eC := I.isoRightDerivedHomologyObj (sections (U ⊓ V)) n
  let g := (NatTrans.mapHomologicalComplex (sectionsFromPairNat U V) (.up ℕ)).app
    I.cocomplex
  let hrel : (ComplexShape.up ℕ).Rel n (n + 1) := by rfl
  let R := ShortComplex.mk (mvRightDerivedFromPair (F := F) U V n)
    (mvRightDerivedConnecting (F := F) U V n)
    (mvRightDerivedFromPair_comp_mvRightDerivedConnecting (F := F) U V n)
  let H := ShortComplex.mk (HomologicalComplex.homologyMap g n)
    (hS.δ n (n + 1) hrel)
    (hS.comp_δ n (n + 1) hrel)
  let e : R ≅ H := ShortComplex.isoMk eB eC
    (I.isoRightDerivedHomologyObj (sections (U ⊔ V)) (n + 1)) (by
      change eB.hom ≫ HomologicalComplex.homologyMap g n =
        (NatTrans.rightDerived (sectionsFromPairNat U V) n).app F ≫ eC.hom
      rw [I.rightDerived_app_eq_homologyMap (sectionsFromPairNat U V) n]
      simp [eB, eC, g, Category.assoc]) (by
      change eC.hom ≫ hS.δ n (n + 1) hrel =
        mvRightDerivedConnecting (F := F) U V n ≫
          (I.isoRightDerivedHomologyObj (sections (U ⊔ V)) (n + 1)).hom
      simp [I, mvRightDerivedConnecting, eC, sectionsComplexMV,
        InjectiveResolution.isoRightDerivedHomologyObj, Category.assoc])
  exact ShortComplex.exact_of_iso e.symm (hS.homology_exact₃ n (n + 1) hrel)

/-- Exactness of the derived Mayer–Vietoris sequence at the next union term. -/
lemma mvRightDerived_exact_at_next_union
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (U V : Opens X) (n : ℕ) :
    (ShortComplex.mk (mvRightDerivedConnecting (F := F) U V n)
      (mvRightDerivedToPair (F := F) U V (n + 1))
      (mvRightDerivedConnecting_comp_mvRightDerivedToPair (F := F) U V n)).Exact := by
  let I := InjectiveResolution.of F
  let S := sectionsComplexMV I.cocomplex U V
  let hS := sectionsComplexMV_shortExact I.cocomplex
    (fun k => TopCat.Sheaf.isFlasque_of_injective X _) U V
  dsimp [sectionsComplexMV] at hS
  let eC := I.isoRightDerivedHomologyObj (sections (U ⊓ V)) n
  let eA := I.isoRightDerivedHomologyObj (sections (U ⊔ V)) (n + 1)
  let eB := I.isoRightDerivedHomologyObj (sectionsPairFunctor U V) (n + 1)
  let f := (NatTrans.mapHomologicalComplex (sectionsToPairNat U V) (.up ℕ)).app
    I.cocomplex
  let hrel : (ComplexShape.up ℕ).Rel n (n + 1) := by rfl
  let R := ShortComplex.mk (mvRightDerivedConnecting (F := F) U V n)
    (mvRightDerivedToPair (F := F) U V (n + 1))
    (mvRightDerivedConnecting_comp_mvRightDerivedToPair (F := F) U V n)
  let H := ShortComplex.mk (hS.δ n (n + 1) hrel)
    (HomologicalComplex.homologyMap f (n + 1))
    (hS.δ_comp n (n + 1) hrel)
  let e : R ≅ H := ShortComplex.isoMk eC eA eB (by
      change eC.hom ≫ hS.δ n (n + 1) hrel =
        mvRightDerivedConnecting (F := F) U V n ≫ eA.hom
      simp [I, mvRightDerivedConnecting, eA, eC, sectionsComplexMV,
        InjectiveResolution.isoRightDerivedHomologyObj, Category.assoc]) (by
      change eA.hom ≫ HomologicalComplex.homologyMap f (n + 1) =
        (NatTrans.rightDerived (sectionsToPairNat U V) (n + 1)).app F ≫ eB.hom
      rw [I.rightDerived_app_eq_homologyMap (sectionsToPairNat U V) (n + 1)]
      simp [eA, eB, f, Category.assoc])
  exact ShortComplex.exact_of_iso e.symm (hS.homology_exact₁ n (n + 1) hrel)


/-- Vanishing on the two opens in consecutive degrees makes the connecting map
an isomorphism from intersection cohomology to the next union cohomology. -/
lemma isIso_mvRightDerivedConnecting
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (U V : Opens X) (n : ℕ)
    (hU : IsZero (((sections U).rightDerived n).obj F))
    (hV : IsZero (((sections V).rightDerived n).obj F))
    (hU' : IsZero (((sections U).rightDerived (n + 1)).obj F))
    (hV' : IsZero (((sections V).rightDerived (n + 1)).obj F)) :
    IsIso (mvRightDerivedConnecting (F := F) U V n) := by
  have hn := ((biprod_isZero_iff _ _).mpr ⟨hU, hV⟩).of_iso
    (sectionsPairRightDerivedIso U V F n)
  have hsucc := ((biprod_isZero_iff _ _).mpr ⟨hU', hV'⟩).of_iso
    (sectionsPairRightDerivedIso U V F (n + 1))
  have : Mono (mvRightDerivedConnecting (F := F) U V n) :=
    (mvRightDerived_exact_at_intersection (F := F) U V n).mono_g (hn.eq_of_src _ _)
  have : Epi (mvRightDerivedConnecting (F := F) U V n) :=
    (mvRightDerived_exact_at_next_union (F := F) U V n).epi_f (hsucc.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end GromovWitten.AlgebraicGeometry.SheafCohomology
