/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FinitePushforward
import GromovWitten.AlgebraicGeometry.Curves.AffineHigherDirectImage
import GromovWitten.AlgebraicGeometry.Curves.FinitePresentationPullback

/-!
# Finitely presented higher direct images for finite affine morphisms

For a finite ring map over a Noetherian ring, all actual module-valued higher direct
images of an associated finitely presented module are finitely presented. Degree zero
is restriction of scalars; positive degrees vanish by affine cohomology vanishing.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open scoped ZeroObject
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section

private lemma isFinitePresentation_of_isZero {Y : Scheme.{u}} (N : Y.Modules)
    (hN : IsZero N) : N.IsFinitePresentation := by
  let R : CommRingCat := Γ(Y, ⊤)
  let A : ModuleCat R := 0
  have : Subsingleton A := ModuleCat.subsingleton_of_isZero (isZero_zero _)
  let T := (tilde.functor (R := R)).obj A
  have hT : T.IsFinitePresentation := tilde_isFinitePresentation A
  let P := (Scheme.Modules.pullback Y.toSpecΓ).obj T
  have hP : P.IsFinitePresentation := inferInstance
  have hTz : IsZero T := (tilde.functor (R := R)).map_isZero (isZero_zero _)
  have hPz : IsZero P := (Scheme.Modules.pullback Y.toSpecΓ).map_isZero hTz
  exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso (hPz.iso hN) hP

/-- All higher direct images along a finite affine map are finitely presented
for a finitely presented associated module over a Noetherian base ring. -/
theorem isFinitePresentation_higherDirectImageModule_spec_tilde
    {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsNoetherianRing R]
    (hφ : RingHom.Finite φ.hom) (N : ModuleCat S)
    [Module.FinitePresentation S (N : Type u)] (n : ℕ) :
    (higherDirectImageModule (Spec.map φ)
      ((tilde.functor (R := S)).obj N) n).IsFinitePresentation := by
  let _ : Algebra R S := φ.hom.toAlgebra
  have : Module.Finite R S := hφ
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  have : ((tilde.functor (R := S)).obj N).IsQuasicoherent :=
    (presentationTilde N Set.univ (by simp) _ (Submodule.span_eq _)).isQuasicoherent
  cases n with
  | zero =>
      exact (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
        (higherDirectImageModuleZeroIso (Spec.map φ) ((tilde.functor (R := S)).obj N)).symm
        (modulePushforward_spec_tilde_isFinitePresentation φ N hφ)
  | succ n =>
      exact isFinitePresentation_of_isZero _
        (isZero_higherDirectImageModule_affine_succ (Spec.map φ)
          ((tilde.functor (R := S)).obj N) n)

end
end GromovWitten.AlgebraicGeometry.Curves
