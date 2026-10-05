/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineTargetBaseChange
import GromovWitten.AlgebraicGeometry.Curves.FiniteCohomologyCanonicalGrauert

/-!
# Canonical base change for curve families over arbitrary target schemes

Over a Noetherian affine base, relative stalk flatness, finite actual cohomology above
degree one, and flat actual H¹ imply invertibility of canonical pushforward base change
for every target scheme. Over a reduced base, finite H¹ and locally constant actual
fibre H¹ dimensions supply the flatness of H¹. These are conditional results: geometric
proper-family cohomology finiteness is not proved here.
-/

open CategoryTheory Limits AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : Type u} [CommRing R] {X Y S : Scheme.{u}}

/-- Finite higher cohomology and flat actual H¹ imply canonical pushforward base change
for arbitrary scheme-valued base changes. -/
lemma family_canonicalPushforwardBaseChangeComparison_isIso_of_finite_arbitrary_target
    [IsNoetherianRing R]
    (s : X ⟶ Spec (CommRingCat.of R)) [FamilyOfCurves s]
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    (hflatOne : Module.Flat R (cohomologyModuleCat R s M 1))
    (b : S ⟶ Spec (CommRingCat.of R))
    (p : Y ⟶ X) (g : Y ⟶ S) (h : IsPullback p g s b) :
    IsIso (canonicalPushforwardBaseChangeComparison s M b p g h) := by
  apply canonicalPushforwardBaseChangeComparison_isIso_of_affine_target_local s M ?_ b p g h
  intro T φ Y q k h'
  exact family_canonicalPushforwardBaseChangeComparison_isIso_of_finite
    s φ q k h' M hflat hfinite hflatOne

/-- Locally constant actual fibre H¹ dimensions give arbitrary scheme-valued canonical
pushforward base change under the finite-cohomology hypotheses. -/
lemma family_canonicalPushforwardBaseChangeComparison_isIso_of_locallyConstant_fibre_arbitrary
    [IsNoetherianRing R] [IsReduced R]
    (s : X ⟶ Spec (CommRingCat.of R)) [FamilyOfCurves s]
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfiniteTail : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    (hfiniteOne : Module.Finite R (cohomologyModuleCat R s M 1))
    (hd : IsLocallyConstant (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 1)))
    (b : S ⟶ Spec (CommRingCat.of R))
    (p : Y ⟶ X) (g : Y ⟶ S) (h : IsPullback p g s b) :
    IsIso (canonicalPushforwardBaseChangeComparison s M b p g h) := by
  have hp1 := family_projective_cohomology_one_of_locallyConstant_fibre
    s M hflat hfiniteTail hfiniteOne hd
  let _ : Module.Projective R (cohomologyModuleCat R s M 1) := hp1
  let hflatOne : Module.Flat R (cohomologyModuleCat R s M 1) := inferInstance
  exact family_canonicalPushforwardBaseChangeComparison_isIso_of_finite_arbitrary_target
    s M hflat hfiniteTail hflatOne b p g h

/-- Finite cohomology and flat actual H¹ produce arbitrary-target pushforward base-change data. -/
theorem family_pushforwardBaseChangeData_of_finite
    [IsNoetherianRing R]
    (s : X ⟶ Spec (CommRingCat.of R)) [FamilyOfCurves s]
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    (hflatOne : Module.Flat R (cohomologyModuleCat R s M 1)) :
    PushforwardBaseChangeData s M where
  comparison_isIso := by
    intro T Y b p g h
    exact family_canonicalPushforwardBaseChangeComparison_isIso_of_finite_arbitrary_target
      s M hflat hfinite hflatOne b p g h

/-- Locally constant actual fibre H¹ dimensions produce arbitrary-target pushforward
base-change data under the finite-cohomology hypotheses. -/
theorem family_pushforwardBaseChangeData_of_locallyConstant_fibre
    [IsNoetherianRing R] [IsReduced R]
    (s : X ⟶ Spec (CommRingCat.of R)) [FamilyOfCurves s]
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfiniteTail : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    (hfiniteOne : Module.Finite R (cohomologyModuleCat R s M 1))
    (hd : IsLocallyConstant (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 1))) :
    PushforwardBaseChangeData s M where
  comparison_isIso := by
    intro T Y b p g h
    exact family_canonicalPushforwardBaseChangeComparison_isIso_of_locallyConstant_fibre_arbitrary
      s M hflat hfiniteTail hfiniteOne hd b p g h

end GromovWitten.AlgebraicGeometry.Curves
end
