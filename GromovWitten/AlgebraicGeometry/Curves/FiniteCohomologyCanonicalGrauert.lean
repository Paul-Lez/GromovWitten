/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteCohomologyGrauert
import GromovWitten.AlgebraicGeometry.Curves.FiniteCohomologyCanonicalBaseChange

/-!
# Canonical base change from the finite-cohomology Grauert hypotheses

Locally constant actual fibre H¹ dimensions over a reduced base make actual H¹ projective,
and hence flat. This supplies the H¹-flatness premise for canonical base change
without any Noetherian assumption on the target. Finite generation of actual
higher cohomology remains an explicit hypothesis.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : Type u} [CommRing R] [CommRing T] {X Y : Scheme.{u}}

/-- Under the finite-cohomology Grauert hypotheses, locally constant actual fibre H¹ dimensions
give the canonical sheaf-level pushforward base-change isomorphism. -/
lemma family_canonicalPushforwardBaseChangeComparison_isIso_of_locallyConstant_fibre
    [IsNoetherianRing R] [IsReduced R]
    (s : X ⟶ Spec (CommRingCat.of R)) [FamilyOfCurves s]
    (φ : CommRingCat.of R ⟶ CommRingCat.of T)
    (p : Y ⟶ X) (g : Y ⟶ Spec (CommRingCat.of T))
    (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfiniteTail : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    (hfiniteOne : Module.Finite R (cohomologyModuleCat R s M 1))
    (hd : IsLocallyConstant (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 1))) :
    IsIso (canonicalPushforwardBaseChangeComparison s M (Spec.map φ) p g h) := by
  have hp1 : Module.Projective R (cohomologyModuleCat R s M 1) :=
    family_projective_cohomology_one_of_locallyConstant_fibre
      s M hflat hfiniteTail hfiniteOne hd
  let _ : Module.Projective R (cohomologyModuleCat R s M 1) := hp1
  let hflatOne : Module.Flat R (cohomologyModuleCat R s M 1) := inferInstance
  exact family_canonicalPushforwardBaseChangeComparison_isIso_of_finite
    s φ p g h M hflat hfiniteTail hflatOne

/-- The same hypotheses give the canonical degree-zero cohomology base-change isomorphism. -/
lemma family_canonicalCohomologyZeroBaseChangeMap_isIso_of_locallyConstant_fibre
    [IsNoetherianRing R] [IsReduced R]
    (s : X ⟶ Spec (CommRingCat.of R)) [FamilyOfCurves s]
    (φ : CommRingCat.of R ⟶ CommRingCat.of T)
    (p : Y ⟶ X) (g : Y ⟶ Spec (CommRingCat.of T))
    (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfiniteTail : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    (hfiniteOne : Module.Finite R (cohomologyModuleCat R s M 1))
    (hd : IsLocallyConstant (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 1))) :
    IsIso (canonicalCohomologyZeroBaseChangeMap s φ p g h M) := by
  have hp1 : Module.Projective R (cohomologyModuleCat R s M 1) :=
    family_projective_cohomology_one_of_locallyConstant_fibre
      s M hflat hfiniteTail hfiniteOne hd
  let _ : Module.Projective R (cohomologyModuleCat R s M 1) := hp1
  let hflatOne : Module.Flat R (cohomologyModuleCat R s M 1) := inferInstance
  exact family_canonicalCohomologyZeroBaseChangeMap_isIso_of_finite
    s φ p g h M hflat hfiniteTail hflatOne

end GromovWitten.AlgebraicGeometry.Curves
