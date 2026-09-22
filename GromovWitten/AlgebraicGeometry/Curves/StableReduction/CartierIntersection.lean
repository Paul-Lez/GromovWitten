/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.StalkIntersection
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Cartier intersections from intrinsic ideal sheaves

This file keeps the local intersection construction intrinsic.  A local equation is obtained
from the defining effective-Cartier condition, and all additivity statements use the actual
product of ideal sheaves together with a non-zero-divisor condition on the other divisor.
Finiteness is deduced from a radical/maximal-ideal hypothesis in a Noetherian local stalk.
-/

open CategoryTheory
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

variable {X : Scheme.{u}}

section Ring

variable {R : Type u} [CommRing R]

/-- Changing a generator of either principal ideal does not change the local intersection length.
This is the precise generator-independence statement needed for Cartier local equations; no
choice of a generator is hidden in the definition. -/
theorem localIntersectionMultiplicity_eq_of_span_eq_left
    {f f' g : R} (h : Ideal.span {f} = Ideal.span {f'}) :
    localIntersectionMultiplicity f g = localIntersectionMultiplicity f' g := by
  unfold localIntersectionMultiplicity
  rw [h]

theorem localIntersectionMultiplicity_eq_of_span_eq_right
    {f g g' : R} (h : Ideal.span {g} = Ideal.span {g'}) :
    localIntersectionMultiplicity f g = localIntersectionMultiplicity f g' := by
  unfold localIntersectionMultiplicity
  rw [h]

end Ring

section NoetherianLocal

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A zero-dimensional intersection in a Noetherian local ring has finite length.  The proof uses
the actual minimal-prime criterion for the Artinian quotient; no Artinian quotient is assumed. -/
theorem idealIntersectionMultiplicity_ne_top_of_radical_eq_maximalIdeal
    (I J : Ideal R)
    (hrad : (I ⊔ J).radical = IsLocalRing.maximalIdeal R) :
    idealIntersectionMultiplicity I J ≠ ⊤ := by
  let _ : (IsLocalRing.maximalIdeal R).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  have hmem : IsLocalRing.maximalIdeal R ∈ (I ⊔ J).minimalPrimes := by
    have hradMin : (I ⊔ J).minimalPrimes =
        ((I ⊔ J).radical).minimalPrimes :=
      (Ideal.radical_minimalPrimes (I := I ⊔ J)).symm
    rw [hradMin, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    simp
  have hart : IsArtinianRing (R ⧸ (I ⊔ J)) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
      (I ⊔ J) hmem
  let _ : IsArtinianRing (R ⧸ (I ⊔ J)) := hart
  unfold idealIntersectionMultiplicity
  have hscalar : Module.length R (R ⧸ (I ⊔ J)) =
      Module.length (R ⧸ (I ⊔ J)) (R ⧸ (I ⊔ J)) :=
    Module.length_eq_of_surjective (Ideal.Quotient.mk (I ⊔ J)).surjective
  rw [hscalar]
  exact Module.length_ne_top

theorem localIntersectionMultiplicity_ne_top_of_radical_eq_maximalIdeal
    (f g : R)
    (hrad : (Ideal.span {f} ⊔ Ideal.span {g}).radical = IsLocalRing.maximalIdeal R) :
    localIntersectionMultiplicity f g ≠ ⊤ := by
  exact idealIntersectionMultiplicity_ne_top_of_radical_eq_maximalIdeal
    (Ideal.span {f}) (Ideal.span {g}) hrad

end NoetherianLocal

section Scheme

variable (D E : Curves.EffectiveCartierDivisor X) (x : X)

/-- The intrinsic local equation supplied by the effective Cartier condition, transported to the
stalk at the chosen point. -/
def stalkLocalEquation : X.presheaf.stalk x :=
  X.presheaf.germ (D.localEquationOpen x).1 x (D.mem_localEquationOpen x) (D.localEquation x)

@[simp]
theorem stalkLocalEquation_eq_germ :
    stalkLocalEquation D x =
      X.presheaf.germ (D.localEquationOpen x).1 x (D.mem_localEquationOpen x)
        (D.localEquation x) := rfl

theorem stalkIdeal_eq_span_stalkLocalEquation :
    stalkIdeal D.idealSheaf x = Ideal.span {stalkLocalEquation D x} := by
  rw [stalkIdeal_eq_map D.idealSheaf x (D.localEquationOpen x)
    (D.mem_localEquationOpen x), D.ideal_localEquationOpen,
    Ideal.map_span, Set.image_singleton]
  rfl

/-- The chosen stalk equation is regular.  On an affine neighbourhood the stalk is the
localization at the corresponding prime, and flatness carries regularity to the localization. -/
theorem stalkLocalEquation_isRegular : IsRegular (stalkLocalEquation D x) := by
  let U : X.affineOpens := D.localEquationOpen x
  let hxU : x ∈ U.1 := D.mem_localEquationOpen x
  let xU : U.1 := ⟨x, hxU⟩
  let _ := X.presheaf.algebra_section_stalk xU
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (U.2.primeIdealOf xU).asIdeal := U.2.isLocalization_stalk xU
  let _ : Module.Flat Γ(X, U.1) (X.presheaf.stalk x) :=
    IsLocalization.flat (X.presheaf.stalk x) (U.2.primeIdealOf xU).asIdeal.primeCompl
  have hs : IsSMulRegular (X.presheaf.stalk x) (D.localEquation x) :=
    Module.Flat.isSMulRegular_of_isRegular (D.localEquation_isRegular x)
  change IsRegular (algebraMap Γ(X, U.1) (X.presheaf.stalk x) (D.localEquation x))
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply hs
    simpa [Algebra.smul_def] using hab
  · intro a b hab
    apply hs
    simpa [Algebra.smul_def, mul_comm] using hab

/-- Intrinsic Cartier intersection multiplicity in terms of the regular stalk equations selected
by the effective Cartier structures. -/
theorem effectiveCartierIntersectionMultiplicity_eq_stalkLocal
    (D E : Curves.EffectiveCartierDivisor X) (x : X) :
    effectiveCartierIntersectionMultiplicity D E x =
      localIntersectionMultiplicity (stalkLocalEquation D x) (stalkLocalEquation E x) := by
  rw [effectiveCartierIntersectionMultiplicity,
    idealSheafIntersectionMultiplicity_eq_idealIntersectionMultiplicity,
    stalkIdeal_eq_span_stalkLocalEquation,
    stalkIdeal_eq_span_stalkLocalEquation]
  rfl

theorem effectiveCartierIntersectionMultiplicity_eq_of_stalk_generators
    (D E : Curves.EffectiveCartierDivisor X) (x : X)
    (r s : X.presheaf.stalk x)
    (hD : stalkIdeal D.idealSheaf x = Ideal.span {r})
    (hE : stalkIdeal E.idealSheaf x = Ideal.span {s}) :
    effectiveCartierIntersectionMultiplicity D E x =
      localIntersectionMultiplicity r s := by
  rw [effectiveCartierIntersectionMultiplicity,
    idealSheafIntersectionMultiplicity_eq_idealIntersectionMultiplicity, hD, hE]
  rfl

/-- Additivity in the first Cartier divisor, under the genuine proper-intersection condition that
the second summand's stalk equation remains a non-zero-divisor modulo the other divisor. -/
theorem effectiveCartierIntersectionMultiplicity_sum_left
    (D F E : Curves.EffectiveCartierDivisor X) (x : X)
    (hreg : Ideal.Quotient.mk (Ideal.span {stalkLocalEquation E x})
      (stalkLocalEquation F x) ∈
        nonZeroDivisors (X.presheaf.stalk x ⧸ Ideal.span {stalkLocalEquation E x})) :
    effectiveCartierIntersectionMultiplicity (D.sum F) E x =
      effectiveCartierIntersectionMultiplicity D E x +
        effectiveCartierIntersectionMultiplicity F E x := by
  rw [effectiveCartierIntersectionMultiplicity,
    idealSheafIntersectionMultiplicity_eq_idealIntersectionMultiplicity,
    effectiveCartierIntersectionMultiplicity,
    idealSheafIntersectionMultiplicity_eq_idealIntersectionMultiplicity,
    effectiveCartierIntersectionMultiplicity,
    idealSheafIntersectionMultiplicity_eq_idealIntersectionMultiplicity,
    EffectiveCartierDivisor.sum_idealSheaf, stalkIdeal_mul,
    stalkIdeal_eq_span_stalkLocalEquation,
    stalkIdeal_eq_span_stalkLocalEquation,
    stalkIdeal_eq_span_stalkLocalEquation,
    Ideal.span_singleton_mul_span_singleton]
  exact localIntersectionMultiplicity_mul_left _ _ _ hreg

theorem effectiveCartierIntersectionMultiplicity_sum_right
    (D E F : Curves.EffectiveCartierDivisor X) (x : X)
    (hreg : Ideal.Quotient.mk (Ideal.span {stalkLocalEquation D x})
      (stalkLocalEquation F x) ∈
        nonZeroDivisors (X.presheaf.stalk x ⧸ Ideal.span {stalkLocalEquation D x})) :
    effectiveCartierIntersectionMultiplicity D (E.sum F) x =
      effectiveCartierIntersectionMultiplicity D E x +
        effectiveCartierIntersectionMultiplicity D F x := by
  calc
    effectiveCartierIntersectionMultiplicity D (E.sum F) x =
        effectiveCartierIntersectionMultiplicity (E.sum F) D x :=
      effectiveCartierIntersectionMultiplicity_comm D (E.sum F) x
    _ = effectiveCartierIntersectionMultiplicity E D x +
        effectiveCartierIntersectionMultiplicity F D x :=
      effectiveCartierIntersectionMultiplicity_sum_left E F D x hreg
    _ = effectiveCartierIntersectionMultiplicity D E x +
        effectiveCartierIntersectionMultiplicity D F x := by
      rw [effectiveCartierIntersectionMultiplicity_comm E D x,
        effectiveCartierIntersectionMultiplicity_comm F D x]

/-- On the support of an ideal sheaf, every section germ lies in the maximal ideal of the stalk.
This is the local-ring form of the zero-locus description of support. -/
theorem stalkIdeal_le_maximalIdeal_of_mem_support
    (I : X.IdealSheafData) {x : X} (hx : x ∈ I.support) :
    stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hxZ : x ∈ X.zeroLocus (U := U) (I.ideal ⟨U, hU⟩) :=
    (I.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hx
  rw [stalkIdeal_eq_map I x ⟨U, hU⟩ hxU]
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  change X.presheaf.germ U x hxU f ∈
    IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  rw [Scheme.mem_zeroLocus_iff] at hxZ
  have hxnot : x ∉ X.basicOpen f := hxZ f hf
  exact hxnot ((X.mem_basicOpen f x hxU).mpr hunit)

/-- The stalk ideal is proper exactly at the support of the ideal sheaf. -/
theorem stalkIdeal_ne_top_iff_mem_support
    (I : X.IdealSheafData) {x : X} :
    stalkIdeal I x ≠ ⊤ ↔ x ∈ I.support := by
  constructor
  · intro hne
    by_contra hx
    exact hne (stalkIdeal_eq_top_of_not_mem_support I hx)
  · intro hx
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (stalkIdeal_le_maximalIdeal_of_mem_support I hx)

/-- Positivity is exactly simultaneous membership in the two scheme-theoretic supports. -/
theorem idealSheafIntersectionMultiplicity_pos_iff_mem_support
    (I J : X.IdealSheafData) (x : X) :
    0 < idealSheafIntersectionMultiplicity I J x ↔
      x ∈ I.support ∧ x ∈ J.support := by
  rw [idealSheafIntersectionMultiplicity, Module.length_pos_iff,
    Ideal.Quotient.nontrivial_iff]
  constructor
  · intro hq
    have hI : stalkIdeal I x ≠ ⊤ := by
      intro htop
      apply hq
      rw [htop, top_sup_eq]
    have hJ : stalkIdeal J x ≠ ⊤ := by
      intro htop
      apply hq
      rw [htop, sup_top_eq]
    exact ⟨(stalkIdeal_ne_top_iff_mem_support I).mp hI,
      (stalkIdeal_ne_top_iff_mem_support J).mp hJ⟩
  · rintro ⟨hxI, hxJ⟩
    have hI := stalkIdeal_le_maximalIdeal_of_mem_support I hxI
    have hJ := stalkIdeal_le_maximalIdeal_of_mem_support J hxJ
    intro htop
    have hle : stalkIdeal I x ⊔ stalkIdeal J x ≤
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := sup_le hI hJ
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (htop ▸ hle))

theorem effectiveCartierIntersectionMultiplicity_pos_iff_mem_support
    (D E : Curves.EffectiveCartierDivisor X) (x : X) :
    0 < effectiveCartierIntersectionMultiplicity D E x ↔
      x ∈ D.support ∧ x ∈ E.support := by
  change 0 < idealSheafIntersectionMultiplicity D.idealSheaf E.idealSheaf x ↔
    x ∈ D.idealSheaf.support ∧ x ∈ E.idealSheaf.support
  exact idealSheafIntersectionMultiplicity_pos_iff_mem_support
    D.idealSheaf E.idealSheaf x

/-- The radical criterion specializes directly to Cartier divisors once the stalk is known to be
Noetherian and local. -/
theorem effectiveCartierIntersectionMultiplicity_ne_top_of_radical_eq_maximalIdeal
    (D E : Curves.EffectiveCartierDivisor X) (x : X)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (hrad : (stalkIdeal D.idealSheaf x ⊔ stalkIdeal E.idealSheaf x).radical =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    effectiveCartierIntersectionMultiplicity D E x ≠ ⊤ := by
  exact idealIntersectionMultiplicity_ne_top_of_radical_eq_maximalIdeal
    (stalkIdeal D.idealSheaf x) (stalkIdeal E.idealSheaf x) hrad

end Scheme

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
