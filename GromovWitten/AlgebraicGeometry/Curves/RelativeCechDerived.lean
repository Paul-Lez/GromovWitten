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
affine intersection.
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

section Comparison
variable {X S : Scheme.{u}}
open GromovWitten.AlgebraicGeometry.SheafCohomology

set_option backward.isDefEq.respectTransparency false in
/-- The relative Čech cokernel computes the first higher direct image.

The source is locally Noetherian and the module is quasicoherent; only the two open
composites are required to be affine for this comparison.  No affine-intersection
hypothesis is needed for the isomorphism.
-/
def relativeCechCokernelIsoHigherDirectImageOne (s : X ⟶ S) (M : X.Modules)
    [IsLocallyNoetherian X] [M.IsQuasicoherent] (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)] :
    cokernel (relativeCechFromPair s M U V) ≅ higherDirectImageModule s M 1 := by
  let I := InjectiveResolution.of M
  have hseq : (relativeCechComplexMV I.cocomplex s U V).ShortExact :=
    relativeCechComplexMV_shortExact I.cocomplex s U V hcover
      (fun n => module_isFlasque_of_injective (I.cocomplex.X n))
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
  have hp := isZero_relativeCechPair_homology s U V I.cocomplex 1 hU hV
  let C := relativeCechComplexMV I.cocomplex s U V
  let e₀ : cokernel (relativeCechFromPair s M U V) ≅
      cokernel (HomologicalComplex.homologyMap C.g 0) :=
    cokernelZeroHomologyIso I (relativeCechFromPairNat s U V)
  let e₁ : cokernel (HomologicalComplex.homologyMap C.g 0) ≅ C.X₁.homology 1 :=
    CategoryTheory.ShortComplex.ShortExact.homologyCokernelIso 0 1 rfl hseq hp
  let e₂ : C.X₁.homology 1 ≅ higherDirectImageModule s M 1 :=
    (I.isoRightDerivedObj (pushforward s) 1).symm
  exact e₀ ≪≫ e₁ ≪≫ e₂

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
