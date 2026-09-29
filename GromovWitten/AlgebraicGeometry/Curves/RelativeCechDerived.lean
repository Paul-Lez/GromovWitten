/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.RelativeCechSections
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechAcyclicity
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechQuasiCoherent
import GromovWitten.AlgebraicGeometry.Curves.DerivedOpenPushforward
import GromovWitten.AlgebraicGeometry.SheafCohomology.RightDerivedComposition
import GromovWitten.CategoryTheory.HomologyCokernel
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Derived relative Čech complexes

Restriction and the relative two-open Čech pair functor preserve finite limits.  For a
locally Noetherian source and a quasicoherent module, the cokernel of the relative two-open
Čech difference map identifies with the first higher direct image when both open composites
are affine over the base.  Quasicoherence of that higher direct image additionally uses an
affine intersection.  The comparison is natural in the quasicoherent module.
-/

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
open GromovWitten.AlgebraicGeometry.Curves

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {X S : Scheme.{u}}

/-- Restriction to an open subscheme preserves finite limits. -/
instance restrictFunctor_preservesFiniteLimits (U : X.Opens) :
    PreservesFiniteLimits (restrictFunctor U.ι) := by
  let _ : PreservesFiniteLimits (pullback U.ι) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  exact preservesFiniteLimits_of_natIso (restrictFunctorIsoPullback U.ι).symm

set_option backward.isDefEq.respectTransparency false in
/-- The pair of relative open pushforwards preserves finite limits. -/
instance relativeCechPairFunctor_preservesFiniteLimits (s : X ⟶ S) (U V : X.Opens) :
    PreservesFiniteLimits (relativeCechPairFunctor s U V) := by
  let D := pair (relativeOpenPushforward s U) (relativeOpenPushforward s V)
  have hD : PreservesFiniteLimits D.flip := by
    apply preservesFiniteLimits_of_evaluation
    rintro ⟨j⟩
    cases j <;>
      change PreservesFiniteLimits (relativeOpenPushforward s _)
    all_goals infer_instance
  let _ : PreservesFiniteLimits D.flip := hD
  let e : relativeCechPairFunctor s U V ≅ D.flip ⋙ lim :=
    NatIso.ofComponents (fun M =>
      (HasLimit.isoOfNatIso (diagramIsoPair (D.flip.obj M))).symm) (by
      intro M N f
      apply limit.hom_ext
      rintro ⟨j⟩
      cases j <;>
        simp [relativeCechPairFunctor, D, HasLimit.isoOfNatIso_inv_π])
  exact preservesFiniteLimits_of_natIso e.symm

end GromovWitten.AlgebraicGeometry.SheafCohomology

namespace GromovWitten.AlgebraicGeometry.Curves

universe v w z

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable {D : Type w} [Category.{z} D] [Abelian D]
variable {F G : C ⥤ D} [F.Additive] [G.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteLimits G]
variable {M : C} (I : InjectiveResolution M)

private def zeroHomologyIso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] :
    F.obj M ≅ ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology 0 :=
  asIso (F.toRightDerivedZero.app M) ≪≫ I.isoRightDerivedObj F 0

set_option backward.isDefEq.respectTransparency false in
private lemma zeroHomologyIso_naturality (α : F ⟶ G) :
    α.app M ≫ (zeroHomologyIso I G).hom =
      (zeroHomologyIso I F).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex α _).app I.cocomplex) 0 := by
  dsimp only [zeroHomologyIso, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, ← NatTrans.toRightDerivedZero_comp, Category.assoc,
    I.rightDerived_app_eq α 0]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def cokernelZeroHomologyIso (α : F ⟶ G) :
    cokernel (α.app M) ≅
      cokernel (HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α _).app I.cocomplex) 0) :=
  cokernel.mapIso _ _ (zeroHomologyIso I F) (zeroHomologyIso I G)
    (zeroHomologyIso_naturality I α)

@[reassoc]
private lemma cokernelZeroHomologyIso_π (α : F ⟶ G) :
    cokernel.π (α.app M) ≫ (cokernelZeroHomologyIso I α).hom =
      (zeroHomologyIso I G).hom ≫ cokernel.π
        (HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex α _).app I.cocomplex) 0) :=
  cokernel.π_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
private lemma zeroHomologyIso_map {N : C} (J : InjectiveResolution N)
    (f : M ⟶ N) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] :
    F.map f ≫ (zeroHomologyIso J F).hom =
      (zeroHomologyIso I F).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) 0 := by
  dsimp only [zeroHomologyIso, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, F.toRightDerivedZero.naturality, Category.assoc]
  simpa only [Category.assoc, Functor.comp_map, HomologicalComplex.homologyFunctor_map] using
    congrArg (fun t => F.toRightDerivedZero.app M ≫ t)
      (InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ hφ F 0)

set_option backward.isDefEq.respectTransparency false in
private lemma cokernelZeroHomologyIso_map {N : C} (J : InjectiveResolution N)
    (f : M ⟶ N) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (α : F ⟶ G) :
    cokernel.map (α.app M) (α.app N) (F.map f) (G.map f) (α.naturality f).symm ≫
        (cokernelZeroHomologyIso J α).hom =
      (cokernelZeroHomologyIso I α).hom ≫
        cokernel.map
          (HomologicalComplex.homologyMap
            ((NatTrans.mapHomologicalComplex α _).app I.cocomplex) 0)
          (HomologicalComplex.homologyMap
            ((NatTrans.mapHomologicalComplex α _).app J.cocomplex) 0)
          (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) 0)
          (HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℕ)).map φ) 0)
          (by rw [← HomologicalComplex.homologyMap_comp,
            ← HomologicalComplex.homologyMap_comp,
            (NatTrans.mapHomologicalComplex α _).naturality φ]) := by
  apply (cancel_epi (cokernel.π (α.app M))).mp
  simp only [cokernel.π_desc_assoc, Category.assoc, cokernelZeroHomologyIso_π,
    cokernelZeroHomologyIso_π_assoc, cokernel.π_desc]
  rw [← Category.assoc, zeroHomologyIso_map I J f φ hφ G, Category.assoc]

section Comparison
variable {X S : Scheme.{u}}
open GromovWitten.AlgebraicGeometry.SheafCohomology

/-- The relative Čech pair has no degree-one homology when both open pieces are affine.

This is the acyclicity input used to identify the degree-one homology of the full
relative Čech complex with the cokernel of its pair differential.
-/
lemma isZero_relativeCechPair_homology_one
    {M : X.Modules} (I : InjectiveResolution M) (s : X ⟶ S) (U V : X.Opens)
    [IsLocallyNoetherian X] [M.IsQuasicoherent]
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)] :
    IsZero ((((relativeCechPairFunctor s U V).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).homology 1) := by
  have hU : IsZero
      ((((relativeOpenPushforward s U).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology 1) :=
    (isZero_relativeOpenPushforward_rightDerived_succ s U M 0).of_iso
      (I.isoRightDerivedObj (relativeOpenPushforward s U) 1).symm
  have hV : IsZero
      ((((relativeOpenPushforward s V).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology 1) :=
    (isZero_relativeOpenPushforward_rightDerived_succ s V M 0).of_iso
      (I.isoRightDerivedObj (relativeOpenPushforward s V) 1).symm
  exact isZero_relativeCechPair_homology s U V I.cocomplex 1 hU hV

set_option backward.isDefEq.respectTransparency false in
/-- The relative Čech cokernel computes the first higher direct image.

The source is locally Noetherian and the module is quasicoherent; only the two open
composites are required to be affine for this comparison.  No affine-intersection
hypothesis is needed for the isomorphism.
-/
def relativeCechCokernelIsoHigherDirectImageOneOfResolution
    (s : X ⟶ S) (M : X.Modules) (I : InjectiveResolution M)
    [IsLocallyNoetherian X] [M.IsQuasicoherent] (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)] :
    cokernel (relativeCechFromPair s M U V) ≅ higherDirectImageModule s M 1 := by
  have hseq : (relativeCechComplexMV I.cocomplex s U V).ShortExact :=
    relativeCechComplexMV_shortExact I.cocomplex s U V hcover
      (fun n => module_isFlasque_of_injective (I.cocomplex.X n))
  have hp := isZero_relativeCechPair_homology_one I s U V
  let C := relativeCechComplexMV I.cocomplex s U V
  let e₀ : cokernel (relativeCechFromPair s M U V) ≅
      cokernel (HomologicalComplex.homologyMap C.g 0) :=
    cokernelZeroHomologyIso I (relativeCechFromPairNat s U V)
  let e₁ : cokernel (HomologicalComplex.homologyMap C.g 0) ≅ C.X₁.homology 1 :=
    CategoryTheory.ShortComplex.ShortExact.homologyCokernelIso 0 1 rfl hseq hp
  let e₂ : C.X₁.homology 1 ≅ higherDirectImageModule s M 1 :=
    (I.isoRightDerivedObj (pushforward s) 1).symm
  exact e₀ ≪≫ e₁ ≪≫ e₂

/-- The selected-resolution instance of the relative Čech comparison. -/
def relativeCechCokernelIsoHigherDirectImageOne (s : X ⟶ S) (M : X.Modules)
    [IsLocallyNoetherian X] [M.IsQuasicoherent] (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)] :
    cokernel (relativeCechFromPair s M U V) ≅ higherDirectImageModule s M 1 :=
  relativeCechCokernelIsoHigherDirectImageOneOfResolution
    s M (InjectiveResolution.of M) U V hcover

/-- The morphism of relative Čech Mayer--Vietoris complexes induced by a cochain map. -/
def relativeCechComplexMVMap
    {K L : CochainComplex X.Modules ℕ} (φ : K ⟶ L)
    (s : X ⟶ S) (U V : X.Opens) :
    relativeCechComplexMV K s U V ⟶ relativeCechComplexMV L s U V where
  τ₁ := ((pushforward s).mapHomologicalComplex (.up ℕ)).map φ
  τ₂ := ((relativeCechPairFunctor s U V).mapHomologicalComplex (.up ℕ)).map φ
  τ₃ := ((relativeOpenPushforward s (U ⊓ V)).mapHomologicalComplex (.up ℕ)).map φ
  comm₁₂ := (NatTrans.mapHomologicalComplex (relativeCechToPairNat s U V) _).naturality φ
  comm₂₃ := (NatTrans.mapHomologicalComplex (relativeCechFromPairNat s U V) _).naturality φ

set_option backward.isDefEq.respectTransparency false in
/-- The Čech comparison is natural in the module for fixed opens and base morphism. -/
lemma relativeCechCokernelIsoHigherDirectImageOneOfResolution_naturality
    (s : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    [IsLocallyNoetherian X] [M.IsQuasicoherent] [N.IsQuasicoherent]
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)] :
    cokernel.map (relativeCechFromPair s M U V) (relativeCechFromPair s N U V)
        ((relativeCechPairFunctor s U V).map f)
        ((relativeOpenPushforward s (U ⊓ V)).map f)
        ((relativeCechFromPairNat s U V).naturality f).symm ≫
      (relativeCechCokernelIsoHigherDirectImageOneOfResolution s N J U V hcover).hom =
    (relativeCechCokernelIsoHigherDirectImageOneOfResolution s M I U V hcover).hom ≫
      ((pushforward s).rightDerived 1).map f := by
  let hI := relativeCechComplexMV_shortExact I.cocomplex s U V hcover
    (fun n => module_isFlasque_of_injective (I.cocomplex.X n))
  let hJ := relativeCechComplexMV_shortExact J.cocomplex s U V hcover
    (fun n => module_isFlasque_of_injective (J.cocomplex.X n))
  have hpI := isZero_relativeCechPair_homology_one I s U V
  have hpJ := isZero_relativeCechPair_homology_one J s U V
  let CI := relativeCechComplexMV I.cocomplex s U V
  let CJ := relativeCechComplexMV J.cocomplex s U V
  let Φ := relativeCechComplexMVMap φ s U V
  let eI₀ : cokernel (relativeCechFromPair s M U V) ≅
      cokernel (HomologicalComplex.homologyMap CI.g 0) :=
    cokernelZeroHomologyIso I (relativeCechFromPairNat s U V)
  let eJ₀ : cokernel (relativeCechFromPair s N U V) ≅
      cokernel (HomologicalComplex.homologyMap CJ.g 0) :=
    cokernelZeroHomologyIso J (relativeCechFromPairNat s U V)
  let eI₁ := CategoryTheory.ShortComplex.ShortExact.homologyCokernelIso 0 1 rfl hI hpI
  let eJ₁ := CategoryTheory.ShortComplex.ShortExact.homologyCokernelIso 0 1 rfl hJ hpJ
  let qI := I.isoRightDerivedObj (pushforward s) 1
  let qJ := J.isoRightDerivedObj (pushforward s) 1
  let κ := cokernel.map (HomologicalComplex.homologyMap CI.g 0)
    (HomologicalComplex.homologyMap CJ.g 0)
    (HomologicalComplex.homologyMap Φ.τ₂ 0) (HomologicalComplex.homologyMap Φ.τ₃ 0)
    (by rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp, Φ.comm₂₃])
  let κ₀ := cokernel.map (relativeCechFromPair s M U V) (relativeCechFromPair s N U V)
    ((relativeCechPairFunctor s U V).map f)
    ((relativeOpenPushforward s (U ⊓ V)).map f)
    ((relativeCechFromPairNat s U V).naturality f).symm
  have h₀ : κ₀ ≫ eJ₀.hom = eI₀.hom ≫ κ :=
    cokernelZeroHomologyIso_map I J f φ hφ (relativeCechFromPairNat s U V)
  have h₁ : κ ≫ eJ₁.hom = eI₁.hom ≫ HomologicalComplex.homologyMap Φ.τ₁ 1 :=
    CategoryTheory.ShortComplex.ShortExact.homologyCokernelIso_naturality Φ 0 1 rfl
      hI hJ hpI hpJ
  have h₂ : qI.inv ≫ ((pushforward s).rightDerived 1).map f =
      HomologicalComplex.homologyMap Φ.τ₁ 1 ≫ qJ.inv :=
    InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ hφ (pushforward s) 1
  change κ₀ ≫ eJ₀.hom ≫ eJ₁.hom ≫ qJ.inv =
    (eI₀.hom ≫ eI₁.hom ≫ qI.inv) ≫ ((pushforward s).rightDerived 1).map f
  calc
    _ = eI₀.hom ≫ κ ≫ eJ₁.hom ≫ qJ.inv := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ eJ₁.hom ≫ qJ.inv) h₀
    _ = eI₀.hom ≫ eI₁.hom ≫ HomologicalComplex.homologyMap Φ.τ₁ 1 ≫ qJ.inv := by
      simpa only [Category.assoc] using congrArg (fun t => eI₀.hom ≫ t ≫ qJ.inv) h₁
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun t => eI₀.hom ≫ eI₁.hom ≫ t) h₂.symm

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the selected-resolution relative Čech comparison. -/
lemma relativeCechCokernelIsoHigherDirectImageOne_naturality
    (s : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    [IsLocallyNoetherian X] [M.IsQuasicoherent] [N.IsQuasicoherent]
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)] :
    cokernel.map (relativeCechFromPair s M U V) (relativeCechFromPair s N U V)
        ((relativeCechPairFunctor s U V).map f)
        ((relativeOpenPushforward s (U ⊓ V)).map f)
        ((relativeCechFromPairNat s U V).naturality f).symm ≫
      (relativeCechCokernelIsoHigherDirectImageOne s N U V hcover).hom =
    (relativeCechCokernelIsoHigherDirectImageOne s M U V hcover).hom ≫
      ((pushforward s).rightDerived 1).map f := by
  let I := InjectiveResolution.of M
  let J := InjectiveResolution.of N
  let φ := InjectiveResolution.desc f J I
  have hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero f J I
  change cokernel.map (relativeCechFromPair s M U V) (relativeCechFromPair s N U V)
        ((relativeCechPairFunctor s U V).map f)
        ((relativeOpenPushforward s (U ⊓ V)).map f)
        ((relativeCechFromPairNat s U V).naturality f).symm ≫
      (relativeCechCokernelIsoHigherDirectImageOneOfResolution s N J U V hcover).hom =
    (relativeCechCokernelIsoHigherDirectImageOneOfResolution s M I U V hcover).hom ≫
      ((pushforward s).rightDerived 1).map f
  exact relativeCechCokernelIsoHigherDirectImageOneOfResolution_naturality
    s f I J φ hφ U V hcover

set_option backward.isDefEq.respectTransparency false in
/-- The Cech comparison is independent of the chosen injective resolution. -/
lemma relativeCechCokernelIsoHigherDirectImageOneOfResolution_eq
    (s : X ⟶ S) (M : X.Modules) (I J : InjectiveResolution M)
    [IsLocallyNoetherian X] [M.IsQuasicoherent]
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)] :
    relativeCechCokernelIsoHigherDirectImageOneOfResolution s M I U V hcover =
      relativeCechCokernelIsoHigherDirectImageOneOfResolution s M J U V hcover := by
  apply Iso.ext
  let φ := InjectiveResolution.desc (𝟙 M) I J
  have hφ : J.ι.f 0 ≫ φ.f 0 = 𝟙 M ≫ I.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero (𝟙 M) I J
  have hnat := relativeCechCokernelIsoHigherDirectImageOneOfResolution_naturality
    s (𝟙 M) J I φ hφ U V hcover
  change
    (relativeCechCokernelIsoHigherDirectImageOneOfResolution
      s M I U V hcover).hom =
      (relativeCechCokernelIsoHigherDirectImageOneOfResolution
        s M J U V hcover).hom ≫
        𝟙 ((pushforward s).rightDerived 1).obj M
  simpa using hnat

set_option backward.isDefEq.respectTransparency false in
/-- The selected-resolution relative Čech comparison carries the cokernel
projection to the connecting map and the chosen first derived comparison. -/
lemma relativeCechCokernelIsoHigherDirectImageOneOfResolution_π
    (s : X ⟶ S) (M : X.Modules) (I : InjectiveResolution M)
    [IsLocallyNoetherian X] [M.IsQuasicoherent] (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)]
    (hseq : (relativeCechComplexMV I.cocomplex s U V).ShortExact) :
    cokernel.π (relativeCechFromPair s M U V) ≫
        (relativeCechCokernelIsoHigherDirectImageOneOfResolution
          s M I U V hcover).hom =
      (relativeOpenPushforward s (U ⊓ V)).toRightDerivedZero.app M ≫
        (I.isoRightDerivedObj (relativeOpenPushforward s (U ⊓ V)) 0).hom ≫
        hseq.δ 0 1 rfl ≫
        (I.isoRightDerivedObj (pushforward s) 1).inv := by
  let C := relativeCechComplexMV I.cocomplex s U V
  let hp : IsZero (C.X₂.homology 1) := isZero_relativeCechPair_homology_one I s U V
  let e₀ : cokernel (relativeCechFromPair s M U V) ≅
      cokernel (HomologicalComplex.homologyMap C.g 0) :=
    cokernelZeroHomologyIso I (relativeCechFromPairNat s U V)
  let e₁ := CategoryTheory.ShortComplex.ShortExact.homologyCokernelIso
    0 1 rfl hseq hp
  let q := I.isoRightDerivedObj (pushforward s) 1
  have h₀ : cokernel.π (relativeCechFromPair s M U V) ≫ e₀.hom =
      (zeroHomologyIso I (relativeOpenPushforward s (U ⊓ V))).hom ≫
        cokernel.π (HomologicalComplex.homologyMap C.g 0) :=
    cokernelZeroHomologyIso_π I (relativeCechFromPairNat s U V)
  have h₁ : cokernel.π (HomologicalComplex.homologyMap C.g 0) ≫ e₁.hom =
      hseq.δ 0 1 rfl :=
    CategoryTheory.ShortComplex.ShortExact.homologyCokernelIso_π 0 1 rfl hseq hp
  change cokernel.π (relativeCechFromPair s M U V) ≫
      e₀.hom ≫ e₁.hom ≫ q.inv = _
  calc
    _ = (zeroHomologyIso I (relativeOpenPushforward s (U ⊓ V))).hom ≫
        cokernel.π (HomologicalComplex.homologyMap C.g 0) ≫ e₁.hom ≫ q.inv := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ e₁.hom ≫ q.inv) h₀
    _ = (zeroHomologyIso I (relativeOpenPushforward s (U ⊓ V))).hom ≫
        hseq.δ 0 1 rfl ≫ q.inv := by
      simpa only [Category.assoc] using congrArg
        (fun t => (zeroHomologyIso I (relativeOpenPushforward s (U ⊓ V))).hom ≫
          t ≫ q.inv) h₁
    _ = _ := by simp only [q, zeroHomologyIso, Iso.trans_hom, asIso_hom, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The selected-resolution relative Čech comparison has the same projection
formula after transport to any selected injective resolution. -/
lemma relativeCechCokernelIsoHigherDirectImageOne_π
    (s : X ⟶ S) (M : X.Modules) (I : InjectiveResolution M)
    [IsLocallyNoetherian X] [M.IsQuasicoherent] (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)]
    (hseq : (relativeCechComplexMV I.cocomplex s U V).ShortExact) :
    cokernel.π (relativeCechFromPair s M U V) ≫
        (relativeCechCokernelIsoHigherDirectImageOne s M U V hcover).hom =
      (relativeOpenPushforward s (U ⊓ V)).toRightDerivedZero.app M ≫
        (I.isoRightDerivedObj (relativeOpenPushforward s (U ⊓ V)) 0).hom ≫
        hseq.δ 0 1 rfl ≫
        (I.isoRightDerivedObj (pushforward s) 1).inv := by
  rw [show relativeCechCokernelIsoHigherDirectImageOne s M U V hcover =
      relativeCechCokernelIsoHigherDirectImageOneOfResolution
        s M (InjectiveResolution.of M) U V hcover by rfl]
  rw [relativeCechCokernelIsoHigherDirectImageOneOfResolution_eq
    s M (InjectiveResolution.of M) I U V hcover]
  exact relativeCechCokernelIsoHigherDirectImageOneOfResolution_π
    s M I U V hcover hseq

set_option backward.isDefEq.respectTransparency false in
/-- The first higher direct image is quasicoherent on a two-affine cover.

In addition to the hypotheses for the Čech comparison, the intersection composite is
assumed affine so that the Čech cokernel is quasicoherent.
-/
lemma isQuasicoherent_higherDirectImageModule_one_of_twoAffine
    (s : X ⟶ S) (M : X.Modules) [IsLocallyNoetherian X] [M.IsQuasicoherent]
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)] [IsAffineHom ((U ⊓ V).ι ≫ s)] :
    (higherDirectImageModule s M 1).IsQuasicoherent := by
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (relativeCechCokernelIsoHigherDirectImageOne s M U V hcover)
    (relativeCechFromPair_cokernel_isQuasicoherent s M U V)
end Comparison
end GromovWitten.AlgebraicGeometry.Curves
