/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteCohomologyVanishing
import GromovWitten.CategoryTheory.BoundedFlatBaseChange
import GromovWitten.AlgebraicGeometry.Curves.FiniteAffineQuasiCoherentPushforward
import GromovWitten.AlgebraicGeometry.Curves.CohomologyZeroBaseChangeMap
/-!
# Canonical degree-zero base change with finite cohomology

For a relatively flat quasi-coherent module on a curve family over a Noetherian
affine base, finite actual cohomology in degrees at least two and flat actual
first cohomology imply invertibility of the canonical degree-zero base-change
map. The result identifies the actual global-sections and Beck–Chevalley maps,
and places no Noetherian hypothesis on the base-change target.

Proper-family finite generation remains an explicit input; it is not proved here.
-/

open CategoryTheory Limits HomologicalComplex Opposite AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}
private lemma family_finiteCech_homologyComparison_zero_isIso
    [IsNoetherianRing R]
    (s : X ⟶ Spec R) [FamilyOfCurves s] (φ : R ⟶ T)
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, 2 ≤ n → Module.Finite R (cohomologyModuleCat R s M n))
    (hflatOne : Module.Flat R (cohomologyModuleCat R s M 1))
    (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W)
    (hcover : coverUnion U = ⊤) :
    IsIso ((baseFiniteCechComplex s M U).homologyComparison
      (ModuleCat.extendScalars φ.hom) (0 : ℤ)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from s]
    infer_instance⟩
  let K := baseFiniteCechComplex s M U
  have hflatK : ∀ i : ℕ, Module.Flat R (K.X i) := by
    intro i
    exact baseFiniteCechComplex_flat s M U hU hflat (i : ℤ)
  have htail : ∀ i : ℕ, U.length ≤ i → IsZero (K.X i) := by
    intro i hi
    apply baseFiniteCechComplex_bounded s M U (i : ℤ)
    right
    exact_mod_cast hi
  have hexact : ∀ i : ℕ, 2 ≤ i → K.ExactAt (i : ℤ) := by
    intro i hi
    exact (K.exactAt_iff_isZero_homology (i : ℤ)).2
      (IsZero.of_iso (family_cohomology_isZero_of_finite s M hflat hfinite i hi)
        (baseFiniteCechHomologyIso s M U hU hcover i))
  let : Module.Flat R (cohomologyModuleCat R s M 1) := hflatOne
  let : Module.Flat R (K.homology (1 : ℤ)) :=
    Module.Flat.of_linearEquiv
      (baseFiniteCechHomologyIso s M U hU hcover 1).toLinearEquiv
  exact CochainComplex.bounded_int_zero_homologyComparison_isIso_of_flat_one
      φ.hom K hflatK U.length htail hexact
/-- Under finite higher cohomology and flat first cohomology, the canonical
map on global sections commutes with arbitrary base-ring change. -/
lemma family_sectionsBaseChangeMap_isIso_of_finite
    [IsNoetherianRing R]
    (s : X ⟶ Spec R) [FamilyOfCurves s]
    (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, 2 ≤ n → Module.Finite R (cohomologyModuleCat R s M n))
    (hflatOne : Module.Flat R (cohomologyModuleCat R s M 1)) :
    IsIso (sectionsBaseChangeMap s φ p g h M) := by
  let : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from s]
    infer_instance⟩
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨U, hU, hcover⟩ := exists_list_affine_cover (X := X)
  have := family_finiteCech_homologyComparison_zero_isIso
    s φ M hflat hfinite hflatOne U hU hcover
  exact sectionsBaseChangeMap_isIso_of_finiteCech_comparison s φ p g h M U hU hcover

/-- The actual canonical degree-zero cohomology comparison is invertible. -/
lemma family_canonicalCohomologyZeroBaseChangeMap_isIso_of_finite
    [IsNoetherianRing R]
    (s : X ⟶ Spec R) [FamilyOfCurves s]
    (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, 2 ≤ n → Module.Finite R (cohomologyModuleCat R s M n))
    (hflatOne : Module.Flat R (cohomologyModuleCat R s M 1)) :
    IsIso (canonicalCohomologyZeroBaseChangeMap s φ p g h M) := by
  have := family_sectionsBaseChangeMap_isIso_of_finite s φ p g h M hflat hfinite hflatOne
  unfold canonicalCohomologyZeroBaseChangeMap
  infer_instance

/-- The canonical sheaf-level Beck–Chevalley map is invertible for arbitrary
base-ring change, under the stated finite-cohomology and flatness hypotheses. -/
lemma family_canonicalPushforwardBaseChangeComparison_isIso_of_finite
    [IsNoetherianRing R]
    (s : X ⟶ Spec R) [FamilyOfCurves s]
    (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, 2 ≤ n → Module.Finite R (cohomologyModuleCat R s M n))
    (hflatOne : Module.Flat R (cohomologyModuleCat R s M 1)) :
    IsIso (canonicalPushforwardBaseChangeComparison s M (Spec.map φ) p g h) := by
  let : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from s]
    infer_instance⟩
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨U, hU, hcover⟩ := exists_list_affine_cover (X := X)
  have := family_finiteCech_homologyComparison_zero_isIso
    s φ M hflat hfinite hflatOne U hU hcover
  exact canonicalPushforwardBaseChangeComparison_isIso_of_finiteCech_comparison
    s φ p g h M U hU hcover

end GromovWitten.AlgebraicGeometry.Curves
