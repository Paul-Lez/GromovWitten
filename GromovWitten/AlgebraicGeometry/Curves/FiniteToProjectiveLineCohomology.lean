/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.ProjectiveLineCechComparison
import GromovWitten.AlgebraicGeometry.Curves.FiniteMorphismHigherDirectImage
import GromovWitten.AlgebraicGeometry.Curves.TwoAffinePushforwardCohomology
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineHigherVanishing
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineFiniteComplex

/-!
# Cohomology of finite morphisms to the projective line

Finite morphisms to the projective line carry finitely presented module sheaves to cohomology
modules that are finite over the Noetherian base ring in every degree.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X : Scheme.{u}}

open GromovWitten.AlgebraicGeometry.ProjectiveLine in
/-- Every cohomology module of a finitely presented module on a finite scheme over the projective
line is finite over the Noetherian base ring. -/
theorem finite_cohomology_of_finite_to_projectiveLine
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (f : X ⟶ scheme A) [IsFinite f]
    (M : X.Modules) [M.IsFinitePresentation] (n : ℕ) :
    Module.Finite A (cohomologyModuleCat A (f ≫ structureMap A) M n) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation :=
    finite_pushforward_isFinitePresentation f M
  let _ : M.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  let _ : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation
      ((Scheme.Modules.pushforward f).obj M)
  cases n with
  | zero =>
    have := finite_cohomology_zero A (M := (Scheme.Modules.pushforward f).obj M)
    exact Module.Finite.equiv (pushforwardCohomologyZeroIso (structureMap A) f M
      (chartZero A).opensRange (chartOne A).opensRange
      (opensRange_chartZero_sup_chartOne A)).toLinearEquiv
  | succ n =>
    cases n with
    | zero =>
      have := finite_cohomology_one A (M := (Scheme.Modules.pushforward f).obj M)
      exact Module.Finite.equiv (affinePushforwardCohomologyOneIso (structureMap A) f M
        (chartZero A).opensRange (chartOne A).opensRange
        (isAffineOpen_opensRange_chartZero A) (isAffineOpen_opensRange_chartOne A)
        (opensRange_chartZero_sup_chartOne A)).toLinearEquiv
    | succ n =>
      have hI : IsAffineOpen ((chartZero A).opensRange ⊓ (chartOne A).opensRange) := by
        rw [opensRange_chartZero_inf_chartOne A]
        exact isAffineOpen_opensRange _
      have hz := isZero_cohomology_succ_succ_of_affine_twoAffine f M
        (chartZero A).opensRange (chartOne A).opensRange
        (isAffineOpen_opensRange_chartZero A) (isAffineOpen_opensRange_chartOne A)
        hI (opensRange_chartZero_sup_chartOne A) n
      let _ : Subsingleton (cohomologyModuleCat A (f ≫ structureMap A) M (n + 2)) :=
        AddCommGrpCat.subsingleton_of_isZero hz
      infer_instance

open GromovWitten.AlgebraicGeometry.ProjectiveLine in
/-- A finite flat two-term replacement for the Čech differential on the inverse images of the
two standard affine charts of the projective line. -/
theorem exists_finiteFlatTwoTerm_of_finite_to_projectiveLine
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (f : X ⟶ scheme A) [IsFinite f]
    (M : X.Modules) [M.IsFinitePresentation]
    (hflat : ∀ x : X,
      Module.Flat A (relativeStalkBase (f ≫ structureMap A) M x)) :
    ∃ (n : ℕ) (q : (Fin n → A) →ₗ[A]
        baseSectionModule (f ≫ structureMap A)
          ((f ⁻¹ᵁ (chartZero A).opensRange) ⊓ (f ⁻¹ᵁ (chartOne A).opensRange)) M),
      Function.Surjective
          ((LinearMap.range (baseCechPairMap (f ≫ structureMap A) M
            (f ⁻¹ᵁ (chartZero A).opensRange) (f ⁻¹ᵁ (chartOne A).opensRange)).hom).mkQ.comp q) ∧
        Module.Flat A
          (LinearMap.ker (LinearMap.finiteFlatTwoTermMap
            (baseCechPairMap (f ≫ structureMap A) M
              (f ⁻¹ᵁ (chartZero A).opensRange) (f ⁻¹ᵁ (chartOne A).opensRange)).hom q)) ∧
        Module.Finite A
          (LinearMap.ker (LinearMap.finiteFlatTwoTermMap
            (baseCechPairMap (f ≫ structureMap A) M
              (f ⁻¹ᵁ (chartZero A).opensRange) (f ⁻¹ᵁ (chartOne A).opensRange)).hom q)) ∧
        Module.Projective A
          (LinearMap.ker (LinearMap.finiteFlatTwoTermMap
            (baseCechPairMap (f ≫ structureMap A) M
              (f ⁻¹ᵁ (chartZero A).opensRange) (f ⁻¹ᵁ (chartOne A).opensRange)).hom q)) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : M.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  let U : X.Opens := f ⁻¹ᵁ (chartZero A).opensRange
  let V : X.Opens := f ⁻¹ᵁ (chartOne A).opensRange
  have hU : IsAffineOpen U := by
    dsimp [U]
    exact IsAffineHom.isAffine_preimage (f := f) _
      (isAffineOpen_opensRange_chartZero A)
  have hV : IsAffineOpen V := by
    dsimp [V]
    exact IsAffineHom.isAffine_preimage (f := f) _
      (isAffineOpen_opensRange_chartOne A)
  have hIbase : IsAffineOpen (overlapι A).opensRange :=
    isAffineOpen_opensRange _
  have hI : IsAffineOpen (U ⊓ V) := by
    dsimp [U, V]
    rw [← Scheme.Hom.preimage_inf, opensRange_chartZero_inf_chartOne A]
    exact IsAffineHom.isAffine_preimage (f := f) _ hIbase
  have hcover : U ⊔ V = ⊤ := by
    dsimp [U, V]
    rw [← Scheme.Hom.preimage_sup, opensRange_chartZero_sup_chartOne A,
      Scheme.Hom.preimage_top]
  have h0 : Module.Finite A
      (cohomologyModuleCat A (f ≫ structureMap A) M 0) :=
    finite_cohomology_of_finite_to_projectiveLine A f M 0
  have h1 : Module.Finite A
      (cohomologyModuleCat A (f ≫ structureMap A) M 1) :=
    finite_cohomology_of_finite_to_projectiveLine A f M 1
  simpa [U, V] using
    (exists_finiteFlatTwoTerm_of_twoAffine (s := f ≫ structureMap A) M U V
      hU hV hI hcover hflat h0 h1)

open GromovWitten.AlgebraicGeometry.ProjectiveLine in
/-- Higher direct images vanish for an affine morphism to the projective line over a Noetherian
base, using the inverse images of the two standard affine charts. -/
theorem isZero_higherDirectImageModule_of_affine_to_projectiveLine
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (f : X ⟶ scheme R) [IsAffineHom f] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (higherDirectImageModule (f ≫ structureMap R) M (n + 2)) := by
  let U : X.Opens := f ⁻¹ᵁ (chartZero R).opensRange
  let V : X.Opens := f ⁻¹ᵁ (chartOne R).opensRange
  have hU : IsAffineOpen U := by
    dsimp [U]
    exact IsAffineHom.isAffine_preimage (f := f) _
      (isAffineOpen_opensRange_chartZero R)
  have hV : IsAffineOpen V := by
    dsimp [V]
    exact IsAffineHom.isAffine_preimage (f := f) _
      (isAffineOpen_opensRange_chartOne R)
  have hIbase : IsAffineOpen (overlapι R).opensRange :=
    isAffineOpen_opensRange _
  have hI : IsAffineOpen (U ⊓ V) := by
    dsimp [U, V]
    rw [← Scheme.Hom.preimage_inf, opensRange_chartZero_inf_chartOne R]
    exact IsAffineHom.isAffine_preimage (f := f) _ hIbase
  have hcover : U ⊔ V = ⊤ := by
    dsimp [U, V]
    rw [← Scheme.Hom.preimage_sup, opensRange_chartZero_sup_chartOne R,
      Scheme.Hom.preimage_top]
  let _ : IsAffine U.toScheme := hU
  let _ : IsAffine V.toScheme := hV
  let _ : IsAffine (U ⊓ V).toScheme := hI
  let _ : IsAffineHom (U.ι ≫ (f ≫ structureMap R)) := inferInstance
  let _ : IsAffineHom (V.ι ≫ (f ≫ structureMap R)) := inferInstance
  let _ : IsAffineHom ((U ⊓ V).ι ≫ (f ≫ structureMap R)) := inferInstance
  exact isZero_higherDirectImageModule_twoAffineCover (f ≫ structureMap R) U V hcover M n

end GromovWitten.AlgebraicGeometry.Curves
