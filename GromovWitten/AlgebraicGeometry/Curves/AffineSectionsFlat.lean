/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffinePullbackGamma
import GromovWitten.AlgebraicGeometry.Curves.ModuleStalk
import Mathlib.RingTheory.Flat.Localization

/-!
# Flatness of affine sections from flat stalks

On an affine scheme, quasi-coherent sections are flat over a base ring when
the geometric stalks are flat over that base. The proof uses the stalk
localization criterion for flatness together with the quasi-coherent tilde
comparison.
-/

open CategoryTheory TopCat AlgebraicGeometry Opposite
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

open AlgebraicGeometry.tilde

variable {S : CommRingCat.{u}}

local instance affineSectionsNativeStalkModule (M : (Spec S).Modules) (x : PrimeSpectrum.Top S) :
    Module ((structurePresheafInCommRingCat S).stalk x) (M.presheaf.stalk x) := by
  let P := (Scheme.Modules.toPresheafOfModules (Spec S)).obj M
  exact @PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    _ _ P x

local instance affineSectionsBaseStalkModule (M : (Spec S).Modules) (x : PrimeSpectrum.Top S) :
    Module S (M.presheaf.stalk x) :=
  Module.compHom (M.presheaf.stalk x) (StructureSheaf.toStalk (S : Type u) x).hom

private def affineStalkLinearEquiv {M N : (Spec S).Modules} (e : M ≅ N)
    (x : PrimeSpectrum.Top S) : M.presheaf.stalk x ≃ₗ[S] N.presheaf.stalk x :=
  ((ModuleCat.restrictScalars (StructureSheaf.toStalk (S : Type u) x).hom).mapIso
    ((moduleStalk (Spec S) x).mapIso e)).toLinearEquiv

variable (R : CommRingCat.{u}) [Algebra R S]

/-- The canonical base-ring action on an affine stalk, induced by `R ⟶ S ⟶ 𝒪ₓ`. -/
def affineStalkBase (M : (Spec S).Modules) (x : PrimeSpectrum.Top S) : ModuleCat R :=
  (ModuleCat.restrictScalars (algebraMap R S)).obj
    (ModuleCat.of S (M.presheaf.stalk x))

/-- A quasi-coherent module on an affine scheme has flat sections when all stalks
are flat over the base ring. -/
lemma affineSections_flat_of_stalks (M : (Spec S).Modules) [M.IsQuasicoherent]
    (h : ∀ x : PrimeSpectrum.Top S, Module.Flat R (affineStalkBase R M x)) :
    Module.Flat R ((ModuleCat.restrictScalars (algebraMap R S)).obj
      (moduleSpecΓFunctor.obj M)) := by
  let N := moduleSpecΓFunctor.obj M
  let : Module R N := Module.compHom N (algebraMap R S)
  let (x : PrimeSpectrum.Top S) : Module R ((tilde N).presheaf.stalk x) :=
    Module.compHom _ (algebraMap R S)
  let (x : PrimeSpectrum.Top S) : Module R (M.presheaf.stalk x) :=
    Module.compHom _ (algebraMap R S)
  have (x : PrimeSpectrum.Top S) : IsScalarTower R S ((tilde N).presheaf.stalk x) :=
    IsScalarTower.of_compHom R S _
  have (x : PrimeSpectrum.Top S) : IsScalarTower R S (M.presheaf.stalk x) :=
    IsScalarTower.of_compHom R S _
  have ht (x : PrimeSpectrum.Top S) : Module.Flat R ((tilde N).presheaf.stalk x) := by
    have : Module.Flat R (M.presheaf.stalk x) := h x
    let e : (tilde N).presheaf.stalk x ≃ₗ[S] M.presheaf.stalk x :=
      affineStalkLinearEquiv (asIso M.fromTildeΓ) x
    exact Module.Flat.of_linearEquiv (e.restrictScalars R)
  let pt (P : Ideal S) [P.IsMaximal] : PrimeSpectrum.Top S := ⟨P, inferInstance⟩
  let Mₚ : ∀ (P : Ideal S) [P.IsMaximal], Type u :=
    fun P _ => (tilde N).presheaf.stalk (pt P)
  let f : ∀ (P : Ideal S) [P.IsMaximal], N →ₗ[S] Mₚ P :=
    fun P _ => (tilde.toStalk N (pt P)).hom
  have : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  have hloc (P : Ideal S) [P.IsMaximal] : IsLocalizedModule.AtPrime P (f P) := by
    have : (pt P).asIdeal.IsPrime := (pt P).isPrime
    change IsLocalizedModule (pt P).asIdeal.primeCompl (tilde.toStalk N (pt P)).hom
    exact instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
      N (pt P)
  change Module.Flat R N
  exact @Module.flat_of_isLocalized_maximal R S _ _ _ N _ _ _ _ Mₚ _ _ _ _ f
    hloc (fun P _ => ht (pt P))

end GromovWitten.AlgebraicGeometry.Curves
