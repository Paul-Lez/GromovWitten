/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AcyclicCohomologyExact
import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineSectionsExact
import GromovWitten.AlgebraicGeometry.SheafCohomology.FlasqueCohomology
import GromovWitten.CategoryTheory.CochainBoundarySequences
import GromovWitten.CategoryTheory.LeftExactImageCriterion

/-!
# Global sections and homology of acyclic complexes

This file compares homology after applying affine global sections with global
sections of homology for nonnegative complexes. It also records the flasque,
quasicoherent specialization used for affine calculations.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

variable {X : Scheme.{u}}

/-- A nonnegative complex with acyclic terms and homology has acyclic cycles. -/
lemma subsingleton_cohomology_cycles
    (K : CochainComplex X.Modules ℕ)
    (hK : ∀ n k, Subsingleton (cohomology X (K.X n) (k + 1)))
    (hH : ∀ n k, Subsingleton (cohomology X (K.homology n) (k + 1))) :
    ∀ n k, Subsingleton (cohomology X (K.cycles n) (k + 1)) := by
  intro n
  induction n with
  | zero =>
    intro k
    let _ := hH 0 k
    exact (cohomologyMapLinearEquiv (asIso (K.homologyπ 0)) (k + 1)).injective.subsingleton
  | succ n ih =>
    have hB := subsingleton_cohomology_X₃_of_subsingleton_cohomology_X₁_X₂
      (CochainComplex.cyclesBoundaryShortComplex_shortExact K n) ih (hK n)
    exact subsingleton_cohomology_X₂_of_subsingleton_cohomology_X₁_X₃
      (CochainComplex.boundaryHomologyShortComplex_shortExact K n) hB (hH (n + 1))

/-- A nonnegative complex with acyclic terms and homology has acyclic boundaries. -/
lemma subsingleton_cohomology_boundaries
    (K : CochainComplex X.Modules ℕ)
    (hK : ∀ n k, Subsingleton (cohomology X (K.X n) (k + 1)))
    (hH : ∀ n k, Subsingleton (cohomology X (K.homology n) (k + 1))) (n : ℕ) :
    ∀ k, Subsingleton
      (cohomology X (Abelian.image (K.toCycles n (n + 1))) (k + 1)) :=
  subsingleton_cohomology_X₃_of_subsingleton_cohomology_X₁_X₂
    (CochainComplex.cyclesBoundaryShortComplex_shortExact K n)
    (subsingleton_cohomology_cycles K hK hH n) (hK n)

variable {R : CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Global sections preserve left homology under the acyclicity hypotheses
needed to compare a nonnegative complex with its homology. -/
lemma moduleSpecΓ_preservesLeftHomology_of_acyclic
    (K : CochainComplex (Spec R).Modules ℕ)
    (hK : ∀ n k, Subsingleton (cohomology (Spec R) (K.X n) (k + 1)))
    (hH : ∀ n k, Subsingleton (cohomology (Spec R) (K.homology n) (k + 1))) (n : ℕ) :
    (moduleSpecΓFunctor (R := R)).PreservesLeftHomologyOf (K.sc n) := by
  let F := moduleSpecΓFunctor (R := R)
  let _ : PreservesFiniteLimits F :=
    ⟨fun J _ _ =>
      (tilde.adjunction (R := R)).rightAdjoint_preservesLimits.preservesLimitsOfShape⟩
  cases n with
  | zero =>
    apply F.preservesLeftHomology_of_zero_f (K.sc 0)
    change K.d ((ComplexShape.up ℕ).prev 0) 0 = 0
    exact K.shape _ _ (by simp)
  | succ n =>
    have hZ := subsingleton_cohomology_cycles K hK hH
    have hB := subsingleton_cohomology_boundaries K hK hH n
    have hΓ₁ := moduleSpecΓFunctor_map_shortExact_of_subsingleton_h1
      (CochainComplex.cyclesBoundaryShortComplex K n)
      (CochainComplex.cyclesBoundaryShortComplex_shortExact K n) (hZ n 0)
    have hΓ₂ := moduleSpecΓFunctor_map_shortExact_of_subsingleton_h1
      (CochainComplex.boundaryHomologyShortComplex K n)
      (CochainComplex.boundaryHomologyShortComplex_shortExact K n) (hB 0)
    have : Epi (F.map (Abelian.factorThruImage (K.toCycles n (n + 1)))) := hΓ₁.epi_g
    have : Epi (F.map (K.homologyπ (n + 1))) := hΓ₂.epi_g
    let c := CokernelCofork.ofπ (K.homologyπ (n + 1))
      (K.toCycles_comp_homologyπ n (n + 1))
    have : Epi (F.map c.π) := by
      change Epi (F.map (K.homologyπ (n + 1)))
      infer_instance
    have hpres : PreservesColimit (parallelPair (K.toCycles n (n + 1)) 0) F :=
      F.preservesCokernel_of_epi_factorThruImage _ c
        (K.homologyIsCokernel n (n + 1) (by simp))
    let H := ShortComplex.LeftHomologyData.canonical (K.sc (n + 1))
    let _ : H.IsPreservedBy F :=
      { g := inferInstance
        f' := by
          change PreservesColimit
            (parallelPair (K.toCycles ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)) 0) F
          rw [show (ComplexShape.up ℕ).prev (n + 1) = n by simp]
          exact hpres }
    exact Functor.PreservesLeftHomologyOf.mk' F H

set_option backward.isDefEq.respectTransparency false in
/-- Global sections commute with homology for a nonnegative complex whose terms
and homology have vanishing positive cohomology. -/
def moduleSpecΓHomologyIsoOfAcyclic
    (K : CochainComplex (Spec R).Modules ℕ)
    (hK : ∀ n k, Subsingleton (cohomology (Spec R) (K.X n) (k + 1)))
    (hH : ∀ n k, Subsingleton (cohomology (Spec R) (K.homology n) (k + 1))) (n : ℕ) :
    (moduleSpecΓFunctor (R := R)).obj (K.homology n) ≅
      (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℕ)).obj K).homology n := by
  let F := moduleSpecΓFunctor (R := R)
  let _ : F.Additive := inferInstance
  let _ : F.PreservesZeroMorphisms := inferInstance
  let _ : F.PreservesLeftHomologyOf (K.sc n) :=
    moduleSpecΓ_preservesLeftHomology_of_acyclic K hK hH n
  exact ((K.sc n).mapHomologyIso F).symm

set_option backward.isDefEq.respectTransparency false in
/-- On a Noetherian affine spectrum, global sections commute with homology of a
nonnegative complex of flasque module sheaves with quasicoherent homology. -/
def moduleSpecΓHomologyIsoOfFlasque [IsNoetherianRing R]
    (K : CochainComplex (Spec R).Modules ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb (Spec R)).obj (K.X n)))
    (hH : ∀ n, (K.homology n).IsQuasicoherent) (n : ℕ) :
    (moduleSpecΓFunctor (R := R)).obj (K.homology n) ≅
      (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℕ)).obj K).homology n := by
  let _ : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_Spec.mpr inferInstance
  let _ : IsNoetherianRing (affineGlobalRing (Spec R)) :=
    @IsLocallyNoetherian.component_noetherian (Spec R) inferInstance
      ⟨⊤, @isAffineOpen_top (Spec R) inferInstance⟩
  apply moduleSpecΓHomologyIsoOfAcyclic K
  · intro j k
    let _ := hK j
    exact AddCommGrpCat.subsingleton_of_isZero
      (isZero_sheafH_of_isFlasque ((moduleToSheafAb (Spec R)).obj (K.X j)) k)
  · intro j k
    let _ := hH j
    exact AddCommGrpCat.subsingleton_of_isZero
      (isZero_cohomology_affine_succ (K.homology j) k)

end
end GromovWitten.AlgebraicGeometry.SheafCohomology
