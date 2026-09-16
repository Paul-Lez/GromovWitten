/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNodeCentralChart
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNodeNodal
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNodeRegularity

/-!
# Acceptance certificate for the explicit DVR node

This file collects the theorem-backed parts of the local-node acceptance example in one
declaration.  For a DVR parameter represented by an irreducible element `π`, the chart
`R[x,y]/(xy-πⁿ)` has the explicit fibrewise nodal certificate, its total ring is regular
exactly for `n ≤ 1`, and a thickness-at-least-two origin is two-dimensional with embedding
dimension three and is nonregular.  The algebraic central-chart process strictly lowers
thickness by two, ends at the regular parity chart, and principalizes the origin ideal.

The closed-origin blowup itself is the projective spectrum of the graded Rees algebra.  Its
three distinguished degree-one generators give a genuine affine open cover.  At every
nonterminal thickness `k+2`, the chart rings are identified with the central thickness-`k` node
and the two regular thickness-one side nodes, and those identifications intertwine the blowup
projection with the explicit substitutions.
-/

open AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

universe u

noncomputable section

/-- A single proposition packaging every theorem-backed clause of the explicit local-node
acceptance example over a DVR. -/
structure DVRAcceptanceCertificate
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (n : ℕ) : Prop where
  fibrewiseNodal : ExplicitNodalFiberCertificate R π n
  atWorstNodalFamily :
    GromovWitten.AlgebraicGeometry.Curves.AtWorstNodal (toBaseSpec R π n)
  totalSpaceRegular_iff : IsRegularRing (Ring R π n) ↔ n ≤ 1
  thickOriginDimension : 2 ≤ n → ringKrullDim (OriginRing R π hπ n) = 2
  thickOriginEmbeddingDimension :
    2 ≤ n → (originMaximalIdeal R π hπ n).spanFinrank = 3
  thickOriginNotRegular : 2 ≤ n → ¬ IsRegularLocalRing (OriginRing R π hπ n)
  preterminalThicknessAtLeastTwo :
    ∀ i, i < n / 2 → 2 ≤ centralReductionThickness n i
  reductionLowersThickness :
    ∀ i, i < n / 2 →
      centralReductionThickness n (i + 1) + 2 = centralReductionThickness n i
  reductionStrictlyDecreases :
    ∀ i, i < n / 2 →
      centralReductionThickness n (i + 1) < centralReductionThickness n i
  terminalThickness : centralReductionThickness n (n / 2) = n % 2
  terminalThicknessAtMostOne : centralReductionThickness n (n / 2) ≤ 1
  terminalTotalSpaceRegular : IsRegularRing (Ring R π (n % 2))
  xBlowupChartOpen : IsOpenImmersion (originBlowupXChartMap R π n)
  yBlowupChartOpen : IsOpenImmersion (originBlowupYChartMap R π n)
  parameterBlowupChartOpen : IsOpenImmersion (originBlowupParameterChartMap R π n)
  parameterBlowupChartIdentified : ∀ k, n = k + 2 →
    Nonempty (originBlowupParameterChart R π n ≅ Spec (.of (Ring R π k)))
  xBlowupChartIdentified : ∀ k, n = k + 2 →
    Nonempty (originBlowupXChart R π n ≅ Spec (.of (Ring R π 1)))
  yBlowupChartIdentified : ∀ k, n = k + 2 →
    Nonempty (originBlowupYChart R π n ≅ Spec (.of (Ring R π 1)))
  parityReductionPrincipalizesOrigin : 2 ≤ n →
    (totalSpaceOriginIdeal R π n).map (parityReductionMap R π n).toRingHom =
      Ideal.span {algebraMap R (Ring R π (n % 2)) π}

/-- The explicit node `xy = πⁿ` satisfies the complete algebraic DVR acceptance
certificate. -/
theorem dvrAcceptanceCertificate
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (n : ℕ) :
    DVRAcceptanceCertificate R π hπ n where
  fibrewiseNodal := explicitNodalFiberCertificate R π n
  atWorstNodalFamily := toBaseSpec_atWorstNodal R π n
  totalSpaceRegular_iff := ring_isRegularRing_iff_le_one R π hπ n
  thickOriginDimension := fun hn ↦
    originRing_ringKrullDim_eq_two R π hπ n (by omega)
  thickOriginEmbeddingDimension := fun hn ↦
    originMaximalIdeal_spanFinrank_eq_three R π hπ n hn
  thickOriginNotRegular := fun hn hregular ↦ by
    have hn1 := (originRing_isRegularLocalRing_iff R π hπ n (by omega)).mp hregular
    omega
  preterminalThicknessAtLeastTwo := fun i hi ↦
    two_le_centralReductionThickness n i hi
  reductionLowersThickness := fun i hi ↦
    centralReductionThickness_succ n i hi
  reductionStrictlyDecreases := fun i hi ↦
    centralReductionThickness_strictAnti n i hi
  terminalThickness := centralReductionThickness_terminal n
  terminalThicknessAtMostOne := centralReduction_terminates n
  terminalTotalSpaceRegular :=
    (ring_isRegularRing_iff_le_one R π hπ (n % 2)).mpr (centralChartTerminal_le_one n)
  xBlowupChartOpen := inferInstance
  yBlowupChartOpen := inferInstance
  parameterBlowupChartOpen := inferInstance
  parameterBlowupChartIdentified := by
    intro k hk
    subst n
    exact ⟨parameterReesChartIso R π hπ k⟩
  xBlowupChartIdentified := by
    intro k hk
    subst n
    exact ⟨xReesChartIso R π hπ k⟩
  yBlowupChartIdentified := by
    intro k hk
    subst n
    exact ⟨yReesChartIso R π hπ k⟩
  parityReductionPrincipalizesOrigin := fun hn ↦
    parityReductionMap_originIdeal R π n hn

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
