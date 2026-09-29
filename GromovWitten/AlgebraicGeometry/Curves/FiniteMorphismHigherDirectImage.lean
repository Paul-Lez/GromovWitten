/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteHigherDirectImage
import GromovWitten.AlgebraicGeometry.Curves.AffineFinitePresentation
import GromovWitten.AlgebraicGeometry.Curves.FinitePresentationPullback
import GromovWitten.AlgebraicGeometry.Curves.FinitePresentationLocality
import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPushforward
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finitely presented higher direct images under finite morphisms

A finite morphism to a locally Noetherian scheme preserves finite presentation
of module sheaves. The proof reduces degree zero to finite ring maps on affine
opens, constructs finite presentations there, and glues them over the target.
Positive higher direct images vanish by affine cohomology vanishing.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open AlgebraicGeometry Scheme.Modules
open scoped ZeroObject
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves

private lemma finite_pushforward_isFinitePresentation_of_affines
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y] [IsFinite f]
    [IsLocallyNoetherian Y] (M : X.Modules) [M.IsFinitePresentation]
    (hSpecFP : ∀ {R S : CommRingCat.{u}} [IsNoetherianRing R] (φ : R ⟶ S)
      (_hφ : RingHom.Finite φ.hom) (N : (Spec S).Modules)
      [N.IsFinitePresentation],
      ((Scheme.Modules.pushforward (Spec.map φ)).obj N).IsFinitePresentation) :
    ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation := by
  let _ : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  let N := (Scheme.Modules.pushforward X.isoSpec.hom).obj M
  have hN : N.IsFinitePresentation := by
    let e := Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.inv
    have hP : ((Scheme.Modules.pullback X.isoSpec.inv).obj M).IsFinitePresentation := inferInstance
    have hR : ((Scheme.Modules.restrictFunctor X.isoSpec.inv).obj M).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
        (e.symm.app M) hP
    exact (SheafOfModules.isFinitePresentation (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      ((modulePushforwardIsoRestrict X.isoSpec).app M).symm hR
  let P := (Scheme.Modules.pushforward (Spec.map f.appTop)).obj N
  have hP : P.IsFinitePresentation := hSpecFP f.appTop f.finite_appTop N
  let Q := (Scheme.Modules.pushforward Y.isoSpec.inv).obj P
  have hQ : Q.IsFinitePresentation := by
    let e := Scheme.Modules.restrictFunctorIsoPullback Y.isoSpec.hom
    have hR : ((Scheme.Modules.restrictFunctor Y.isoSpec.hom).obj P).IsFinitePresentation := by
      have hPB : ((Scheme.Modules.pullback Y.isoSpec.hom).obj P).IsFinitePresentation :=
        inferInstance
      exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
        (e.symm.app P) hPB
    exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
      ((modulePushforwardIsoRestrict Y.isoSpec.symm).app P).symm hR
  have hf : X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv = f := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  let e : Scheme.Modules.pushforward X.isoSpec.hom ⋙
      Scheme.Modules.pushforward (Spec.map f.appTop) ⋙
      Scheme.Modules.pushforward Y.isoSpec.inv ≅ Scheme.Modules.pushforward f :=
    Functor.isoWhiskerLeft _ (Scheme.Modules.pushforwardComp _ _) ≪≫
      Scheme.Modules.pushforwardComp _ _ ≪≫ Scheme.Modules.pushforwardCongr hf
  exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso (e.app M) hQ

private lemma finite_pushforward_restrict_isFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsFinitePresentation]
    (hSpecFP : ∀ {R S : CommRingCat.{u}} [IsNoetherianRing R] (φ : R ⟶ S)
      (_hφ : RingHom.Finite φ.hom) (N : (Spec S).Modules)
      [N.IsFinitePresentation],
      ((Scheme.Modules.pushforward (Spec.map φ)).obj N).IsFinitePresentation)
    (U : Y.affineOpens) :
    (((Scheme.Modules.pushforward f).obj M).restrict U.1.ι).IsFinitePresentation := by
  let V : X.Opens := f ⁻¹ᵁ U.1
  let _ : IsAffine V.toScheme := IsAffineHom.isAffine_preimage _ U.2
  let _ : IsAffine U.1.toScheme := U.2
  let _ : IsAffineHom (f ∣_ U.1) := inferInstance
  let _ : IsNoetherianRing Γ(U.1.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩
  let P := (Scheme.Modules.pushforward (f ∣_ U.1)).obj (M.restrict V.ι)
  have hM : (M.restrict V.ι).IsFinitePresentation := by
    let e := Scheme.Modules.restrictFunctorIsoPullback V.ι
    have hP : ((Scheme.Modules.pullback V.ι).obj M).IsFinitePresentation := inferInstance
    exact (SheafOfModules.isFinitePresentation V.toScheme.ringCatSheaf).prop_of_iso
      (e.symm.app M) hP
  have hP : P.IsFinitePresentation := by
    exact finite_pushforward_isFinitePresentation_of_affines (f ∣_ U.1)
      (M.restrict V.ι) hSpecFP
  exact (SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf).prop_of_iso
    ((modulePushforwardOpenRestrictIso f U.1).app M).symm hP

/-- Finite pushforward preserves finite presentation over a locally Noetherian target. -/
theorem finite_pushforward_isFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation := by
  let P := (Scheme.Modules.pushforward f).obj M
  let hSpecFP : ∀ {R S : CommRingCat.{u}} [IsNoetherianRing R] (φ : R ⟶ S)
      (_hφ : RingHom.Finite φ.hom) (N : (Spec S).Modules)
      [N.IsFinitePresentation],
      ((Scheme.Modules.pushforward (Spec.map φ)).obj N).IsFinitePresentation := by
    intro R S _ φ hφ N _
    let _ : Algebra R S := φ.hom.toAlgebra
    let _ : Module.Finite R S := hφ
    let _ : IsNoetherianRing S := IsNoetherianRing.of_finite R S
    let _ : N.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation N
    let _ : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
    let _ : Module.FinitePresentation S ((moduleSpecΓFunctor.obj N : Type u)) :=
      moduleSpecΓ_isFinitePresentation N
    exact modulePushforward_spec_isFinitePresentation φ N hφ
  let hLocal : ∀ U : Y.affineOpens,
      (P.restrict U.1.ι).IsFinitePresentation := by
    intro U
    exact finite_pushforward_restrict_isFinitePresentation f M hSpecFP U
  apply module_isFinitePresentation_of_presentation_openCover P (fun U : Y.affineOpens ↦ U.1)
  · rw [IsOpenCover]
    exact iSup_affineOpens_eq_top Y
  · intro U
    let : IsAffine U.1.toScheme := U.2
    let hR := hLocal U
    let : (P.restrict U.1.ι).IsFinitePresentation := hR
    exact presentation_of_affine_isFinitePresentation (P.restrict U.1.ι)


/-- Every higher direct image under a finite morphism to a locally Noetherian scheme
is finitely presented when the input sheaf is finitely presented. -/
theorem finite_higherDirectImageModule_isFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsFinitePresentation] (n : ℕ) :
    (higherDirectImageModule f M n).IsFinitePresentation := by
  let h0 : ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation :=
    finite_pushforward_isFinitePresentation f M
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : M.IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  cases n with
  | zero =>
      exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
        (higherDirectImageModuleZeroIso f M).symm h0
  | succ n =>
      exact module_isFinitePresentation_of_isZero _
        (isZero_higherDirectImageModule_affine_succ f M n)

end GromovWitten.AlgebraicGeometry.Curves
