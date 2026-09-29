/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.CohomologyVanishing
import GromovWitten.AlgebraicGeometry.Curves.CohomologyExactSequence
import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineSectionsFunctor

/-!
# Exactness of affine global sections for quasicoherent modules

Global sections on the spectrum of a Noetherian ring sends a short exact sequence
with quasicoherent first term to a short exact sequence.  The epimorphism is
obtained from affine cohomology vanishing.
-/

open CategoryTheory Limits Abelian
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {R : CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Global sections on the spectrum of a Noetherian ring sends a short exact
complex whose first term is quasicoherent to a short exact complex. -/
lemma moduleSpecΓFunctor_map_shortExact_of_isQuasicoherent
    [IsNoetherianRing R]
    (S : ShortComplex (Spec (CommRingCat.of (R : Type u))).Modules)
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] :
    (S.map (moduleSpecΓFunctor (R := R))).ShortExact := by
  let _ : PreservesFiniteLimits (moduleSpecΓFunctor (R := R)) :=
    ⟨fun J _ _ =>
      (tilde.adjunction (R := R)).rightAdjoint_preservesLimits.preservesLimitsOfShape⟩
  let _ : IsLocallyNoetherian (Spec (CommRingCat.of (R : Type u))) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  let _ : IsNoetherianRing (affineGlobalRing (Spec (CommRingCat.of (R : Type u)))) :=
    @IsLocallyNoetherian.component_noetherian
      (Spec (CommRingCat.of (R : Type u))) inferInstance
      ⟨⊤, @isAffineOpen_top (Spec (CommRingCat.of (R : Type u))) inferInstance⟩
  have hleft :
      (S.map (moduleSpecΓFunctor (R := R))).Exact ∧
        Mono ((moduleSpecΓFunctor (R := R)).map S.f) :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (moduleSpecΓFunctor (R := R))).1 inferInstance S hS
  refine { exact := hleft.1, mono_f := hleft.2, epi_g := ?_ }
  rw [ModuleCat.epi_iff_surjective]
  intro y
  let y' : cohomology (Spec (CommRingCat.of (R : Type u))) S.X₃ 0 :=
    (cohomologyZeroAddEquiv S.X₃).symm y
  let hsub : Subsingleton
      (cohomology (Spec (CommRingCat.of (R : Type u))) S.X₁ 1) :=
    AddCommGrpCat.subsingleton_of_isZero (isZero_cohomology_affine_succ S.X₁ 0)
  obtain ⟨x', hx'⟩ := (cohomology_exact_at_X₃ hS 0 y').1 (hsub.elim _ _)
  change cohomology (Spec (CommRingCat.of (R : Type u))) S.X₂ 0 at x'
  refine ⟨cohomologyZeroAddEquiv S.X₂ x', ?_⟩
  change ((moduleSpecΓFunctor (R := R)).map S.g)
      (cohomologyZeroAddEquiv S.X₂ x') = y
  have hmap (z : (moduleSpecΓFunctor (R := R)).obj S.X₂) :
      ((moduleSpecΓFunctor (R := R)).map S.g) z =
        (((moduleToSheafAb (Spec (CommRingCat.of (R : Type u)))).map S.g).hom.app
          (Opposite.op ⊤)) z := by
    rfl
  rw [hmap]
  have hy : cohomologyZeroAddEquiv S.X₃ y' = y := by simp [y']
  rw [← hy]
  change ((moduleToSheafAb (Spec (CommRingCat.of (R : Type u)))).map S.g).hom.app
      (Opposite.op ⊤)
      (Sheaf.H.equiv₀ ((moduleToSheafAb (Spec (CommRingCat.of (R : Type u)))).obj S.X₂)
        (isTerminal_top _) x') =
    Sheaf.H.equiv₀ ((moduleToSheafAb (Spec (CommRingCat.of (R : Type u)))).obj S.X₃)
      (isTerminal_top _) y'
  rw [Sheaf.H.equiv₀_naturality]
  exact congrArg (cohomologyZeroAddEquiv S.X₃) hx'

end GromovWitten.AlgebraicGeometry.SheafCohomology
