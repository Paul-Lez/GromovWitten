/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroup

/-!
# Grading transport and the rank-zero point Gysin map

For the explicit proper-point calculation, the obstruction bundle is the constructed rank-zero
bundle.  Its total space and base have the same Chow grading, so its zero-section Gysin map is
defined directly by transport along `i + 0 = i`.

The former general `VectorBundleHomotopyInvariance` record accepted the hard homotopy-invariance
equivalence as a field.  It has been removed from the active API; a general vector-bundle Gysin
map will return only when the equivalence has been proved from vector-bundle geometry.
-/

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

/-- A dimension-graded family of rational-equivalence systems on a scheme. -/
abbrev RationalChowGrading (X : Scheme.{u}) (dimension : DimensionFunction X) :=
  ∀ i : ℤ, RationalEquivalenceSystem X dimension i

namespace RationalChowGrading

variable {X : Scheme.{u}} {dimension : DimensionFunction X}

/-- The dimension-`i` rational Chow group selected by a grading. -/
abbrev group (R : RationalChowGrading X dimension) (i : ℤ) :=
  (R i).ChowGroup

/-- Transport a dimension-pure cycle along equality of grading indices. -/
def cyclesCast {i j : ℤ} (h : i = j) :
    cyclesOfDimension X dimension i →ₗ[ℚ] cyclesOfDimension X dimension j := by
  subst j
  exact LinearMap.id

@[simp]
theorem coe_cyclesCast {i j : ℤ} (h : i = j)
    (z : cyclesOfDimension X dimension i) :
    ((cyclesCast h z : cyclesOfDimension X dimension j) : AlgebraicCycle X ℚ) = z := by
  subst j
  rfl

/-- Rational-linear transport between propositionally equal grading indices. -/
def cast {R : RationalChowGrading X dimension} {i j : ℤ} (h : i = j) :
    R.group i →ₗ[ℚ] R.group j := by
  subst j
  exact LinearMap.id

/-- Invertible transport between propositionally equal grading indices. -/
def castEquiv {R : RationalChowGrading X dimension} {i j : ℤ} (h : i = j) :
    R.group i ≃ₗ[ℚ] R.group j := by
  subst j
  exact LinearEquiv.refl _ _

@[simp]
theorem castEquiv_apply {R : RationalChowGrading X dimension} {i j : ℤ}
    (h : i = j) (z : R.group i) : castEquiv h z = cast h z := by
  subst j
  rfl

@[simp]
theorem castEquiv_symm_apply {R : RationalChowGrading X dimension} {i j : ℤ}
    (h : i = j) (z : R.group j) : (castEquiv h).symm z = cast h.symm z := by
  subst j
  rfl

@[simp]
theorem cast_rfl {R : RationalChowGrading X dimension} {i : ℤ} :
    cast (R := R) (rfl : i = i) = LinearMap.id :=
  rfl

@[simp]
theorem cast_apply_rfl {R : RationalChowGrading X dimension} {i : ℤ}
    (z : R.group i) : cast (R := R) (rfl : i = i) z = z :=
  rfl

/-- Proof irrelevance makes every self-transport act as the identity. -/
@[simp]
theorem cast_apply_self {R : RationalChowGrading X dimension} {i : ℤ}
    (h : i = i) (z : R.group i) : cast (R := R) h z = z := by
  rw [Subsingleton.elim h rfl]
  rfl

@[simp]
theorem cast_cast {R : RationalChowGrading X dimension} {i j k : ℤ}
    (h : i = j) (h' : j = k) (z : R.group i) :
    cast (R := R) h' (cast (R := R) h z) = cast (R := R) (h.trans h') z := by
  subst j
  subst k
  rfl

/-- Transport in the grading commutes with passage from cycles to rational Chow classes. -/
theorem cast_quotientMap {R : RationalChowGrading X dimension} {i j : ℤ}
    (h : i = j) (z : cyclesOfDimension X dimension i) :
    cast h ((R i).quotientMap z) =
      (R j).quotientMap (cyclesCast h z) := by
  subst j
  rfl

end RationalChowGrading

namespace PointChow

variable (k : Type u) [Field k]

/-- The dimension-graded rational Chow theory constructed for `Spec(k)`. -/
noncomputable def grading : RationalChowGrading
    (_root_.AlgebraicGeometry.Spec (.of k)) (DimensionFunction.specField k) :=
  rationalEquivalence k

/-- Pullback along the rank-zero identity bundle on a point.  This is equality transport, not a
caller-supplied homotopy-invariance theorem. -/
noncomputable def zeroBundlePullback (i : ℤ) :
    (grading k).group i →ₗ[ℚ] (grading k).group (i + 0) :=
  RationalChowGrading.cast (by omega)

@[simp]
theorem zeroBundlePullback_apply (i : ℤ) (z : (grading k).group i) :
    zeroBundlePullback k i z =
      RationalChowGrading.cast (by omega) z := by
  rfl

/-- Zero-section Gysin for the constructed rank-zero identity bundle. -/
noncomputable def zeroBundleGysin (i : ℤ) :
    (grading k).group (i + 0) →ₗ[ℚ] (grading k).group i :=
  RationalChowGrading.cast (by omega)

@[simp]
theorem zeroBundle_zeroGysin (i : ℤ) (z : (grading k).group (i + 0)) :
    zeroBundleGysin k i z =
      RationalChowGrading.cast (by omega) z := by
  rfl

end PointChow

end GromovWitten.AlgebraicGeometry.IntersectionTheory
