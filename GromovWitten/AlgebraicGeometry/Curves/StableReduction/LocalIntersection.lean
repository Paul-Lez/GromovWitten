/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalOrdSymmetry
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Length-theoretic local intersection multiplicities

This file develops a ring-theoretic local model for the intersection of two ideals and its
principal-Cartier specialization.  For elements `f g` of a Noetherian local ring `R`, the
multiplicity is the length of `R/(f,g)`.  All values live in `ℕ∞`; finiteness is therefore an
explicit geometric hypothesis rather than an unproved field or Artinian assumption.
-/

open scoped BigOperators

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

variable {R : Type u} [CommRing R]

/-- The length of the scheme-theoretic intersection defined by two ideals.  The definition is
ring-theoretic and does not package a claimed geometric finiteness statement. -/
def idealIntersectionMultiplicity (I J : Ideal R) : ℕ∞ :=
  Module.length R (R ⧸ (I ⊔ J))

/-- The ideal-intersection length for two principal Cartier equations. -/
def localIntersectionMultiplicity (f g : R) : ℕ∞ :=
  idealIntersectionMultiplicity (Ideal.span {f}) (Ideal.span {g})

@[simp]
theorem idealIntersectionMultiplicity_comm (I J : Ideal R) :
    idealIntersectionMultiplicity I J = idealIntersectionMultiplicity J I := by
  unfold idealIntersectionMultiplicity
  rw [sup_comm]

@[simp]
theorem localIntersectionMultiplicity_comm (f g : R) :
    localIntersectionMultiplicity f g = localIntersectionMultiplicity g f := by
  unfold localIntersectionMultiplicity
  rw [idealIntersectionMultiplicity_comm]

theorem length_quotient_quotient_eq_length_sup (f g : R) :
    Module.length (R ⧸ Ideal.span {g})
        ((R ⧸ Ideal.span {g}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) f}) =
      localIntersectionMultiplicity f g := by
  let I : Ideal R := Ideal.span {g}
  let S := R ⧸ I
  let q : R →+* S := Ideal.Quotient.mk I
  have hscalar : Module.length R (S ⧸ Ideal.span {q f}) =
      Module.length S (S ⧸ Ideal.span {q f}) :=
    Module.length_eq_of_surjective q.surjective
  have hmap : Ideal.span {q f} = (Ideal.span {f}).map q := by
    rw [Ideal.map_span, Set.image_singleton]
  have heq : (S ⧸ Ideal.span {q f}) ≃ₗ[R]
      (R ⧸ (I ⊔ Ideal.span {f})) := by
    rw [hmap]
    exact (DoubleQuot.quotQuotEquivQuotSupₐ R I (Ideal.span {f})).toLinearEquiv
  unfold localIntersectionMultiplicity idealIntersectionMultiplicity
  rw [sup_comm]
  rw [← hscalar]
  exact heq.length_eq

/-- Product additivity in one equation: if `f'` is a non-zero-divisor after restricting to
`V(g)`, then the intersection length of `f f'` with `g` is the sum of the two intersection
lengths.  The assertion is in `ℕ∞`, so it remains valid without silently assuming finite length. -/
theorem localIntersectionMultiplicity_mul_left (f f' g : R)
    (hreg : Ideal.Quotient.mk (Ideal.span {g}) f' ∈
      nonZeroDivisors (R ⧸ Ideal.span {g})) :
    localIntersectionMultiplicity (f * f') g =
      localIntersectionMultiplicity f g + localIntersectionMultiplicity f' g := by
  let S := R ⧸ Ideal.span {g}
  let q : R →+* S := Ideal.Quotient.mk (Ideal.span {g})
  have hmul : q (f * f') = q f * q f' := map_mul q f f'
  calc
    localIntersectionMultiplicity (f * f') g =
        Module.length S (S ⧸ Ideal.span {q (f * f')}) :=
      (length_quotient_quotient_eq_length_sup (f * f') g).symm
    _ = Ring.ord S (q f * q f') := by rw [hmul, Ring.ord]
    _ = Ring.ord S (q f) + Ring.ord S (q f') := Ring.ord_mul S hreg
    _ = Module.length S (S ⧸ Ideal.span {q f}) +
        Module.length S (S ⧸ Ideal.span {q f'}) := by rfl
    _ = localIntersectionMultiplicity f g + localIntersectionMultiplicity f' g := by
      rw [length_quotient_quotient_eq_length_sup f g,
        length_quotient_quotient_eq_length_sup f' g]

/-- The same product formula with the regularity hypothesis in the usual `IsRegular` form. -/
theorem localIntersectionMultiplicity_mul_left_of_isRegular (f f' g : R)
    (hreg : IsRegular (Ideal.Quotient.mk (Ideal.span {g}) f')) :
    localIntersectionMultiplicity (f * f') g =
      localIntersectionMultiplicity f g + localIntersectionMultiplicity f' g :=
  localIntersectionMultiplicity_mul_left f f' g hreg.mem_nonZeroDivisors

/-- Product additivity with regularity of the first factor instead of the second factor. -/
theorem localIntersectionMultiplicity_mul_right (f f' g : R)
    (hreg : Ideal.Quotient.mk (Ideal.span {g}) f ∈
      nonZeroDivisors (R ⧸ Ideal.span {g})) :
    localIntersectionMultiplicity (f * f') g =
      localIntersectionMultiplicity f g + localIntersectionMultiplicity f' g := by
  rw [mul_comm f f', localIntersectionMultiplicity_mul_left f' f g hreg, add_comm]

/-- In a DVR, the intersection of two principal equations is the smaller of their two
valuation lengths.  This specialization also covers zero equations, whose valuation is `⊤`. -/
theorem localIntersectionMultiplicity_eq_min_addVal
    [IsDomain R] [IsDiscreteValuationRing R] (f g : R) :
    localIntersectionMultiplicity f g =
      min (IsDiscreteValuationRing.addVal R f) (IsDiscreteValuationRing.addVal R g) := by
  rcases le_total (IsDiscreteValuationRing.addVal R f)
      (IsDiscreteValuationRing.addVal R g) with hfg | hgf
  · have hdiv : f ∣ g := (IsDiscreteValuationRing.addVal_le_iff_dvd).1 hfg
    have hspan : Ideal.span {g} ≤ Ideal.span {f} :=
      Ideal.span_singleton_le_span_singleton.2 hdiv
    rw [localIntersectionMultiplicity, idealIntersectionMultiplicity,
      sup_eq_left.mpr hspan, min_eq_left hfg,
      ← Ring.ord_eq_addVal f, Ring.ord]
  · have hdiv : g ∣ f := (IsDiscreteValuationRing.addVal_le_iff_dvd).1 hgf
    have hspan : Ideal.span {f} ≤ Ideal.span {g} :=
      Ideal.span_singleton_le_span_singleton.2 hdiv
    rw [localIntersectionMultiplicity, idealIntersectionMultiplicity,
      sup_eq_right.mpr hspan, min_eq_right hgf,
      ← Ring.ord_eq_addVal g, Ring.ord]

section NoetherianLocal

variable [IsNoetherianRing R]

/-- Finiteness of an ideal intersection length from the actual Artinian quotient hypothesis. -/
theorem idealIntersectionMultiplicity_ne_top_of_isArtinian (I J : Ideal R)
    (hart : IsArtinian R (R ⧸ (I ⊔ J))) :
    idealIntersectionMultiplicity I J ≠ ⊤ := by
  unfold idealIntersectionMultiplicity
  let _ : IsArtinian R (R ⧸ (I ⊔ J)) := hart
  exact Module.length_ne_top

/-- Finiteness of a local intersection length is proved from the actual Artinian quotient
hypothesis.  In geometric applications this is supplied by proper zero-dimensional support. -/
theorem localIntersectionMultiplicity_ne_top_of_isArtinian (f g : R)
    (hart : IsArtinian R (R ⧸ (Ideal.span {f} ⊔ Ideal.span {g}))) :
    localIntersectionMultiplicity f g ≠ ⊤ := by
  unfold localIntersectionMultiplicity
  exact idealIntersectionMultiplicity_ne_top_of_isArtinian _ _ hart

end NoetherianLocal

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
