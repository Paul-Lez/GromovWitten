/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNodeBaseChange
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ReesBlowup
import GromovWitten.AlgebraicGeometry.RegularScheme
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Algebraic substitutions for the local blowup charts

This file formalizes the algebraic substitutions expected on the three standard charts in the
blowup of `xy = π^(k+2)`.  The central substitution writes `x = π x'` and `y = π y'`,
leaving `x'y' = π^k`.  The two side substitutions identify thickness-one node algebras by
writing either `y = π^(k+1)y'` or `x = π^(k+1)x'`.  Every resulting scheme morphism is over
`Spec R`, is an isomorphism wherever `π` is invertible, and commutes with arbitrary
coefficient-ring base change.  Each substitution principalizes the pullback of the closed-origin
ideal by the expected chart generator.  The central morphism also iterates functorially to the
parity thickness, with an explicit strictly decreasing thickness invariant and termination bound.

The file also instantiates the repository's graded-Rees/`Proj` construction at the closed origin,
so the three distinguished degree-one generators define genuine affine open charts of the
scheme-theoretic blowup.  The formulas and principalization theorems below provide the remaining
inputs for identifying those opens with the explicit substitution rings.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

universe u v

noncomputable section

/-! ## Regular chart generators -/

/-- A nonzero parameter remains a non-zero-divisor in every local-node algebra. -/
theorem parameter_isRegular
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (n : ℕ) :
    IsRegular (algebraMap R (Ring R π n) π) := by
  have hπreg : IsRegular π := IsRegular.of_ne_zero' hπ.ne_zero
  have hsmul : IsSMulRegular (Ring R π n) π :=
    Module.Flat.isSMulRegular_of_isRegular hπreg
  have hsmul' : IsSMulRegular (Ring R π n) (algebraMap R (Ring R π n) π) :=
    (isSMulRegular_algebraMap_iff (Ring R π n)).mpr hsmul
  have hleft : IsLeftRegular (algebraMap R (Ring R π n) π) := by
    intro a b hab
    apply hsmul'
    simpa only [smul_eq_mul] using hab
  exact ⟨hleft, hleft.right_of_commute fun _ ↦ mul_comm _ _⟩

/-- The `x` coordinate is a non-zero-divisor on the regular thickness-one side chart. -/
theorem x_one_isRegular
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) :
    IsRegular (x R π 1) := by
  have hprod : IsRegular (x R π 1 * y R π 1) := by
    rw [x_mul_y]
    simpa only [pow_one] using parameter_isRegular R π hπ 1
  exact hprod.of_mul_left

/-- The `y` coordinate is a non-zero-divisor on the regular thickness-one side chart. -/
theorem y_one_isRegular
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) :
    IsRegular (y R π 1) := by
  have hprod : IsRegular (x R π 1 * y R π 1) := by
    rw [x_mul_y]
    simpa only [pow_one] using parameter_isRegular R π hπ 1
  exact hprod.of_mul_right

/-- The central-chart substitution from thickness `k + 2` to thickness `k`, sending the old
coordinates to `πx` and `πy`. -/
def centralChartMap (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    Ring R π (k + 2) →ₐ[R] Ring R π k :=
  lift π (k + 2)
    (algebraMap R (Ring R π k) π * x R π k)
    (algebraMap R (Ring R π k) π * y R π k) (by
      rw [mul_mul_mul_comm, x_mul_y, ← map_mul, ← map_mul]
      congr 1
      ring)

@[simp] theorem centralChartMap_x (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    centralChartMap R π k (x R π (k + 2)) =
      algebraMap R (Ring R π k) π * x R π k := by
  apply lift_x

@[simp] theorem centralChartMap_y (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    centralChartMap R π k (y R π (k + 2)) =
      algebraMap R (Ring R π k) π * y R π k := by
  apply lift_y

/-- The induced affine-scheme morphism from the thickness-`k` chart to the original
thickness-`k+2` node. -/
def centralChartSpec (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    Spec (.of (Ring R π k)) ⟶ Spec (.of (Ring R π (k + 2))) :=
  Spec.map (CommRingCat.ofHom (centralChartMap R π k).toRingHom)

/-- The central-chart morphism commutes with the structural maps to `Spec R`. -/
@[reassoc (attr := simp)] theorem centralChartSpec_toBaseSpec
    (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    centralChartSpec R π k ≫ toBaseSpec R π (k + 2) = toBaseSpec R π k := by
  rw [centralChartSpec, toBaseSpec, toBaseSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  exact RingHom.ext fun r => (centralChartMap R π k).commutes r

/-! ## The two side-chart substitutions -/

/-- The `x`-side substitution from thickness `k + 2` to thickness one.  It keeps `x` and
replaces the old `y` by `π^(k+1)y`. -/
def xSideChartMap (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    Ring R π (k + 2) →ₐ[R] Ring R π 1 :=
  lift π (k + 2)
    (x R π 1)
    (algebraMap R (Ring R π 1) (π ^ (k + 1)) * y R π 1) (by
      rw [show x R π 1 *
          (algebraMap R (Ring R π 1) (π ^ (k + 1)) * y R π 1) =
          algebraMap R (Ring R π 1) (π ^ (k + 1)) * (x R π 1 * y R π 1) by ring,
        x_mul_y, ← map_mul]
      congr 1
      ring)

@[simp] theorem xSideChartMap_x (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    xSideChartMap R π k (x R π (k + 2)) = x R π 1 := by
  apply lift_x

@[simp] theorem xSideChartMap_y (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    xSideChartMap R π k (y R π (k + 2)) =
      algebraMap R (Ring R π 1) (π ^ (k + 1)) * y R π 1 := by
  apply lift_y

/-- The `y`-side substitution from thickness `k + 2` to thickness one.  It keeps `y` and
replaces the old `x` by `π^(k+1)x`. -/
def ySideChartMap (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    Ring R π (k + 2) →ₐ[R] Ring R π 1 :=
  lift π (k + 2)
    (algebraMap R (Ring R π 1) (π ^ (k + 1)) * x R π 1)
    (y R π 1) (by
      rw [show (algebraMap R (Ring R π 1) (π ^ (k + 1)) * x R π 1) *
          y R π 1 =
          algebraMap R (Ring R π 1) (π ^ (k + 1)) * (x R π 1 * y R π 1) by ring,
        x_mul_y, ← map_mul]
      congr 1
      ring)

@[simp] theorem ySideChartMap_x (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    ySideChartMap R π k (x R π (k + 2)) =
      algebraMap R (Ring R π 1) (π ^ (k + 1)) * x R π 1 := by
  apply lift_x

@[simp] theorem ySideChartMap_y (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    ySideChartMap R π k (y R π (k + 2)) = y R π 1 := by
  apply lift_y

/-! ## Principalization of the blowup centre -/

/-- The closed total-space origin ideal in the node coordinate ring. -/
def totalSpaceOriginIdeal (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ideal (Ring R π n) :=
  Ideal.span ({x R π n, y R π n,
    algebraMap R (Ring R π n) π} : Set (Ring R π n))

/-! ## The genuine Rees blowup and its three distinguished charts -/

/-- The blowup of the local node at its closed total-space origin. -/
noncomputable abbrev originBlowup (R : Type u) [CommRing R] (π : R) (n : ℕ) : Scheme :=
  ReesBlowup.scheme (totalSpaceOriginIdeal R π n)

/-- The projective Rees morphism from the origin blowup to the local node. -/
noncomputable def originBlowupProjection (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    originBlowup R π n ⟶ Spec (.of (Ring R π n)) :=
  ReesBlowup.projection (totalSpaceOriginIdeal R π n)

/-- The `x` generator of the blowup centre. -/
def originCenterX (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    totalSpaceOriginIdeal R π n :=
  ⟨x R π n, by
    apply Ideal.subset_span
    exact Set.mem_insert _ _⟩

/-- The `y` generator of the blowup centre. -/
def originCenterY (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    totalSpaceOriginIdeal R π n :=
  ⟨y R π n, by
    apply Ideal.subset_span
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)⟩

/-- The base parameter generator of the blowup centre. -/
def originCenterParameter (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    totalSpaceOriginIdeal R π n :=
  ⟨algebraMap R (Ring R π n) π, by
    apply Ideal.subset_span
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

/-- The three ordered generators `x`, `y`, and `π` of the closed-origin ideal. -/
def originCenterFamily (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Fin 3 → Ring R π n :=
  ![x R π n, y R π n, algebraMap R (Ring R π n) π]

theorem totalSpaceOriginIdeal_eq_span_range_originCenterFamily
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    totalSpaceOriginIdeal R π n = Ideal.span (Set.range (originCenterFamily R π n)) := by
  apply congr_arg Ideal.span
  ext z
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [originCenterFamily]

/-- The standard `x`-chart of the origin blowup. -/
noncomputable abbrev originBlowupXChart (R : Type u) [CommRing R] (π : R) (n : ℕ) : Scheme :=
  ReesBlowup.chart (totalSpaceOriginIdeal R π n) (originCenterX R π n)

/-- The standard `y`-chart of the origin blowup. -/
noncomputable abbrev originBlowupYChart (R : Type u) [CommRing R] (π : R) (n : ℕ) : Scheme :=
  ReesBlowup.chart (totalSpaceOriginIdeal R π n) (originCenterY R π n)

/-- The standard parameter chart of the origin blowup. -/
noncomputable abbrev originBlowupParameterChart
    (R : Type u) [CommRing R] (π : R) (n : ℕ) : Scheme :=
  ReesBlowup.chart (totalSpaceOriginIdeal R π n) (originCenterParameter R π n)

/-- Coordinate ring of the parameter chart for the blowup of a thickness-`k+2` node. -/
abbrev ParameterChartRing (R : Type u) [CommRing R] (π : R) (k : ℕ) :=
  HomogeneousLocalization.Away
    (ReesBlowup.grade (totalSpaceOriginIdeal R π (k + 2)))
    (ReesBlowup.generator (totalSpaceOriginIdeal R π (k + 2))
      (originCenterParameter R π (k + 2)))

/-- Coordinate ring of the `x` chart for the blowup of a thickness-`k+2` node. -/
abbrev XChartRing (R : Type u) [CommRing R] (π : R) (k : ℕ) :=
  HomogeneousLocalization.Away
    (ReesBlowup.grade (totalSpaceOriginIdeal R π (k + 2)))
    (ReesBlowup.generator (totalSpaceOriginIdeal R π (k + 2))
      (originCenterX R π (k + 2)))

/-- Coordinate ring of the `y` chart for the blowup of a thickness-`k+2` node. -/
abbrev YChartRing (R : Type u) [CommRing R] (π : R) (k : ℕ) :=
  HomogeneousLocalization.Away
    (ReesBlowup.grade (totalSpaceOriginIdeal R π (k + 2)))
    (ReesBlowup.generator (totalSpaceOriginIdeal R π (k + 2))
      (originCenterY R π (k + 2)))

noncomputable instance parameterChartAlgebra
    (R : Type u) [CommRing R] (π : R) (k : ℕ) : Algebra R (ParameterChartRing R π k) :=
  ((ReesBlowup.baseRingHom (totalSpaceOriginIdeal R π (k + 2))
    (originCenterParameter R π (k + 2))).comp
      (algebraMap R (Ring R π (k + 2)))).toAlgebra

noncomputable instance xChartAlgebra
    (R : Type u) [CommRing R] (π : R) (k : ℕ) : Algebra R (XChartRing R π k) :=
  ((ReesBlowup.baseRingHom (totalSpaceOriginIdeal R π (k + 2))
    (originCenterX R π (k + 2))).comp
      (algebraMap R (Ring R π (k + 2)))).toAlgebra

noncomputable instance yChartAlgebra
    (R : Type u) [CommRing R] (π : R) (k : ℕ) : Algebra R (YChartRing R π k) :=
  ((ReesBlowup.baseRingHom (totalSpaceOriginIdeal R π (k + 2))
    (originCenterY R π (k + 2))).comp
      (algebraMap R (Ring R π (k + 2)))).toAlgebra

/-- The original node ring acts on its parameter Rees chart through degree-zero functions. -/
noncomputable def parameterChartBaseAlgHom
    (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    Ring R π (k + 2) →ₐ[R] ParameterChartRing R π k where
  toRingHom := ReesBlowup.baseRingHom (totalSpaceOriginIdeal R π (k + 2))
    (originCenterParameter R π (k + 2))
  commutes' _ := rfl

/-- The original node ring acts on its `x` Rees chart through degree-zero functions. -/
noncomputable def xChartBaseAlgHom
    (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    Ring R π (k + 2) →ₐ[R] XChartRing R π k where
  toRingHom := ReesBlowup.baseRingHom (totalSpaceOriginIdeal R π (k + 2))
    (originCenterX R π (k + 2))
  commutes' _ := rfl

/-- The original node ring acts on its `y` Rees chart through degree-zero functions. -/
noncomputable def yChartBaseAlgHom
    (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    Ring R π (k + 2) →ₐ[R] YChartRing R π k where
  toRingHom := ReesBlowup.baseRingHom (totalSpaceOriginIdeal R π (k + 2))
    (originCenterY R π (k + 2))
  commutes' _ := rfl

/-- The `x`-chart open immersion into the blowup. -/
noncomputable def originBlowupXChartMap (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    originBlowupXChart R π n ⟶ originBlowup R π n :=
  ReesBlowup.chartMap (totalSpaceOriginIdeal R π n) (originCenterX R π n)

/-- The `y`-chart open immersion into the blowup. -/
noncomputable def originBlowupYChartMap (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    originBlowupYChart R π n ⟶ originBlowup R π n :=
  ReesBlowup.chartMap (totalSpaceOriginIdeal R π n) (originCenterY R π n)

/-- The parameter-chart open immersion into the blowup. -/
noncomputable def originBlowupParameterChartMap
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    originBlowupParameterChart R π n ⟶ originBlowup R π n :=
  ReesBlowup.chartMap (totalSpaceOriginIdeal R π n) (originCenterParameter R π n)

instance originBlowupXChartMap_isOpenImmersion
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    IsOpenImmersion (originBlowupXChartMap R π n) := by
  change IsOpenImmersion (ReesBlowup.chartMap _ _)
  infer_instance

instance originBlowupYChartMap_isOpenImmersion
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    IsOpenImmersion (originBlowupYChartMap R π n) := by
  change IsOpenImmersion (ReesBlowup.chartMap _ _)
  infer_instance

instance originBlowupParameterChartMap_isOpenImmersion
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    IsOpenImmersion (originBlowupParameterChartMap R π n) := by
  change IsOpenImmersion (ReesBlowup.chartMap _ _)
  infer_instance

/-- The canonical affine cover of the origin blowup by precisely the `x`, `y`, and parameter
charts. -/
noncomputable def originBlowupThreeChartCover
    (R : Type u) [CommRing R] (π : R) (n : ℕ) : (originBlowup R π n).AffineOpenCover :=
  ReesBlowup.affineOpenCoverOfSpan (totalSpaceOriginIdeal R π n)
    (originCenterFamily R π n)
    (totalSpaceOriginIdeal_eq_span_range_originCenterFamily R π n)

/-- A cover generator agrees with any named element of the centre having the same underlying
ring element.  Keeping the cover index general avoids dependence on the proof field of a
particular `Fin 3` term. -/
theorem originCenterFamily_generator_eq
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (i : Fin 3)
    (r : totalSpaceOriginIdeal R π n)
    (hr : originCenterFamily R π n i = r.1) :
    ReesBlowup.generatorOfFamily (totalSpaceOriginIdeal R π n)
        (originCenterFamily R π n)
        (totalSpaceOriginIdeal_eq_span_range_originCenterFamily R π n) i =
      ReesBlowup.generator (totalSpaceOriginIdeal R π n) r := by
  unfold ReesBlowup.generatorOfFamily
  apply congrArg (ReesBlowup.generator (totalSpaceOriginIdeal R π n))
  apply Subtype.ext
  exact hr

/-- The first generator used by the three-chart cover is the named `x` generator.  This
lemma makes the equality of the two ideal-membership witnesses explicit. -/
theorem originCenterFamily_generator_zero
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    ReesBlowup.generatorOfFamily (totalSpaceOriginIdeal R π n)
        (originCenterFamily R π n)
        (totalSpaceOriginIdeal_eq_span_range_originCenterFamily R π n) 0 =
      ReesBlowup.generator (totalSpaceOriginIdeal R π n) (originCenterX R π n) := by
  unfold ReesBlowup.generatorOfFamily
  apply congrArg (ReesBlowup.generator (totalSpaceOriginIdeal R π n))
  apply Subtype.ext
  rfl

/-- The second generator used by the three-chart cover is the named `y` generator. -/
theorem originCenterFamily_generator_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    ReesBlowup.generatorOfFamily (totalSpaceOriginIdeal R π n)
        (originCenterFamily R π n)
        (totalSpaceOriginIdeal_eq_span_range_originCenterFamily R π n) 1 =
      ReesBlowup.generator (totalSpaceOriginIdeal R π n) (originCenterY R π n) := by
  unfold ReesBlowup.generatorOfFamily
  apply congrArg (ReesBlowup.generator (totalSpaceOriginIdeal R π n))
  apply Subtype.ext
  rfl

/-- The third generator used by the three-chart cover is the named parameter generator. -/
theorem originCenterFamily_generator_two
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    ReesBlowup.generatorOfFamily (totalSpaceOriginIdeal R π n)
        (originCenterFamily R π n)
        (totalSpaceOriginIdeal_eq_span_range_originCenterFamily R π n) 2 =
      ReesBlowup.generator (totalSpaceOriginIdeal R π n)
        (originCenterParameter R π n) := by
  unfold ReesBlowup.generatorOfFamily
  apply congrArg (ReesBlowup.generator (totalSpaceOriginIdeal R π n))
  apply Subtype.ext
  rfl

/-- The central substitution makes the pullback of the origin ideal principal, generated by
`π`. -/
theorem centralChartMap_originIdeal
    (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    (totalSpaceOriginIdeal R π (k + 2)).map (centralChartMap R π k).toRingHom =
      Ideal.span {algebraMap R (Ring R π k) π} := by
  rw [totalSpaceOriginIdeal, Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z ⟨w, (rfl | rfl | rfl), rfl⟩
    · change centralChartMap R π k (x R π (k + 2)) ∈ _
      rw [centralChartMap_x]
      exact (Ideal.span {algebraMap R (Ring R π k) π}).mul_mem_right _
        (Ideal.subset_span (Set.mem_singleton _))
    · change centralChartMap R π k (y R π (k + 2)) ∈ _
      rw [centralChartMap_y]
      exact (Ideal.span {algebraMap R (Ring R π k) π}).mul_mem_right _
        (Ideal.subset_span (Set.mem_singleton _))
    · change centralChartMap R π k (algebraMap R (Ring R π (k + 2)) π) ∈ _
      rw [(centralChartMap R π k).commutes]
      exact Ideal.subset_span (Set.mem_singleton _)
  · rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    apply Ideal.subset_span
    refine ⟨algebraMap R (Ring R π (k + 2)) π, ?_, ?_⟩
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact (centralChartMap R π k).commutes π

/-- The `x`-side substitution makes the pullback of the origin ideal principal, generated by
`x`. -/
theorem xSideChartMap_originIdeal
    (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    (totalSpaceOriginIdeal R π (k + 2)).map (xSideChartMap R π k).toRingHom =
      Ideal.span {x R π 1} := by
  rw [totalSpaceOriginIdeal, Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z ⟨w, (rfl | rfl | rfl), rfl⟩
    · change xSideChartMap R π k (x R π (k + 2)) ∈ _
      rw [xSideChartMap_x]
      exact Ideal.subset_span (Set.mem_singleton _)
    · change xSideChartMap R π k (y R π (k + 2)) ∈ _
      rw [xSideChartMap_y, map_pow]
      rw [show algebraMap R (Ring R π 1) π = x R π 1 * y R π 1 by
        simpa only [pow_one] using (x_mul_y R π 1).symm]
      rw [mul_pow]
      exact (Ideal.span {x R π 1}).mul_mem_right _
        ((Ideal.span {x R π 1}).mul_mem_right _
          ((Ideal.span {x R π 1}).pow_mem_of_mem
            (Ideal.subset_span (Set.mem_singleton _)) (k + 1) (by omega)))
    · change xSideChartMap R π k (algebraMap R (Ring R π (k + 2)) π) ∈ _
      rw [(xSideChartMap R π k).commutes]
      rw [show algebraMap R (Ring R π 1) π = x R π 1 * y R π 1 by
        simpa only [pow_one] using (x_mul_y R π 1).symm]
      exact (Ideal.span {x R π 1}).mul_mem_right _
        (Ideal.subset_span (Set.mem_singleton _))
  · rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    apply Ideal.subset_span
    refine ⟨x R π (k + 2), Set.mem_insert _ _, ?_⟩
    exact xSideChartMap_x R π k

/-- The `y`-side substitution makes the pullback of the origin ideal principal, generated by
`y`. -/
theorem ySideChartMap_originIdeal
    (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    (totalSpaceOriginIdeal R π (k + 2)).map (ySideChartMap R π k).toRingHom =
      Ideal.span {y R π 1} := by
  rw [totalSpaceOriginIdeal, Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z ⟨w, (rfl | rfl | rfl), rfl⟩
    · change ySideChartMap R π k (x R π (k + 2)) ∈ _
      rw [ySideChartMap_x, map_pow]
      rw [show algebraMap R (Ring R π 1) π = x R π 1 * y R π 1 by
        simpa only [pow_one] using (x_mul_y R π 1).symm]
      rw [mul_pow]
      exact (Ideal.span {y R π 1}).mul_mem_right _
        ((Ideal.span {y R π 1}).mul_mem_left _
          ((Ideal.span {y R π 1}).pow_mem_of_mem
            (Ideal.subset_span (Set.mem_singleton _)) (k + 1) (by omega)))
    · change ySideChartMap R π k (y R π (k + 2)) ∈ _
      rw [ySideChartMap_y]
      exact Ideal.subset_span (Set.mem_singleton _)
    · change ySideChartMap R π k (algebraMap R (Ring R π (k + 2)) π) ∈ _
      rw [(ySideChartMap R π k).commutes]
      rw [show algebraMap R (Ring R π 1) π = x R π 1 * y R π 1 by
        simpa only [pow_one] using (x_mul_y R π 1).symm]
      exact (Ideal.span {y R π 1}).mul_mem_left _
        (Ideal.subset_span (Set.mem_singleton _))
  · rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    apply Ideal.subset_span
    refine ⟨y R π (k + 2), Set.mem_insert_of_mem _ (Set.mem_insert _ _), ?_⟩
    exact ySideChartMap_y R π k

/-! ## Maps from the genuine Rees charts to the explicit node rings -/

/-- The parameter Rees chart maps canonically to the central thickness-`k` substitution ring. -/
noncomputable def parameterReesChartToCentralRingHom
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    HomogeneousLocalization.Away
        (ReesBlowup.grade (totalSpaceOriginIdeal R π (k + 2)))
        (ReesBlowup.generator (totalSpaceOriginIdeal R π (k + 2))
          (originCenterParameter R π (k + 2))) →+*
      Ring R π k :=
  ReesBlowup.chartLift (totalSpaceOriginIdeal R π (k + 2))
    (centralChartMap R π k).toRingHom (originCenterParameter R π (k + 2)) (by
      simpa [originCenterParameter] using parameter_isRegular R π hπ k) (by
      simpa [originCenterParameter] using centralChartMap_originIdeal R π k)

/-- The `x` Rees chart maps canonically to the regular thickness-one `x`-side ring. -/
noncomputable def xReesChartToSideRingHom
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    HomogeneousLocalization.Away
        (ReesBlowup.grade (totalSpaceOriginIdeal R π (k + 2)))
        (ReesBlowup.generator (totalSpaceOriginIdeal R π (k + 2))
          (originCenterX R π (k + 2))) →+*
      Ring R π 1 :=
  ReesBlowup.chartLift (totalSpaceOriginIdeal R π (k + 2))
    (xSideChartMap R π k).toRingHom (originCenterX R π (k + 2)) (by
      simpa [originCenterX] using x_one_isRegular R π hπ) (by
      simpa [originCenterX] using xSideChartMap_originIdeal R π k)

/-- The `y` Rees chart maps canonically to the regular thickness-one `y`-side ring. -/
noncomputable def yReesChartToSideRingHom
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    HomogeneousLocalization.Away
        (ReesBlowup.grade (totalSpaceOriginIdeal R π (k + 2)))
        (ReesBlowup.generator (totalSpaceOriginIdeal R π (k + 2))
          (originCenterY R π (k + 2))) →+*
      Ring R π 1 :=
  ReesBlowup.chartLift (totalSpaceOriginIdeal R π (k + 2))
    (ySideChartMap R π k).toRingHom (originCenterY R π (k + 2)) (by
      simpa [originCenterY] using y_one_isRegular R π hπ) (by
      simpa [originCenterY] using ySideChartMap_originIdeal R π k)

/-- The parameter-chart map as a morphism of algebras over the DVR. -/
noncomputable def parameterReesChartToCentralAlgHom
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    ParameterChartRing R π k →ₐ[R] Ring R π k where
  toRingHom := parameterReesChartToCentralRingHom R π hπ k
  commutes' a := by
    change parameterReesChartToCentralRingHom R π hπ k
      (ReesBlowup.baseRingHom (totalSpaceOriginIdeal R π (k + 2))
        (originCenterParameter R π (k + 2))
        (algebraMap R (Ring R π (k + 2)) a)) = _
    rw [parameterReesChartToCentralRingHom, ReesBlowup.chartLift_baseRingHom]
    exact (centralChartMap R π k).commutes a

/-- The `x`-chart map as a morphism of algebras over the DVR. -/
noncomputable def xReesChartToSideAlgHom
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    XChartRing R π k →ₐ[R] Ring R π 1 where
  toRingHom := xReesChartToSideRingHom R π hπ k
  commutes' a := by
    change xReesChartToSideRingHom R π hπ k
      (ReesBlowup.baseRingHom (totalSpaceOriginIdeal R π (k + 2))
        (originCenterX R π (k + 2))
        (algebraMap R (Ring R π (k + 2)) a)) = _
    rw [xReesChartToSideRingHom, ReesBlowup.chartLift_baseRingHom]
    exact (xSideChartMap R π k).commutes a

/-- The `y`-chart map as a morphism of algebras over the DVR. -/
noncomputable def yReesChartToSideAlgHom
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    YChartRing R π k →ₐ[R] Ring R π 1 where
  toRingHom := yReesChartToSideRingHom R π hπ k
  commutes' a := by
    change yReesChartToSideRingHom R π hπ k
      (ReesBlowup.baseRingHom (totalSpaceOriginIdeal R π (k + 2))
        (originCenterY R π (k + 2))
        (algebraMap R (Ring R π (k + 2)) a)) = _
    rw [yReesChartToSideRingHom, ReesBlowup.chartLift_baseRingHom]
    exact (ySideChartMap R π k).commutes a

/-- The explicit central node ring maps back to the parameter Rees chart by the ratios
`x/π` and `y/π`. -/
noncomputable def centralRingToParameterReesChartHom
    (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    Ring R π k →ₐ[R] ParameterChartRing R π k := by
  let I := totalSpaceOriginIdeal R π (k + 2)
  let r := originCenterParameter R π (k + 2)
  exact lift π k
    (ReesBlowup.ratioElement I r (originCenterX R π (k + 2)))
    (ReesBlowup.ratioElement I r (originCenterY R π (k + 2))) (by
      rw [ReesBlowup.ratioElement_mul_ratioElement_eq_baseElement I r
        (originCenterX R π (k + 2)) (originCenterY R π (k + 2))
        (algebraMap R (Ring R π (k + 2)) (π ^ k))]
      · change ReesBlowup.baseElement I r
            (algebraMap R (Ring R π (k + 2)) (π ^ k)) =
          algebraMap R (ParameterChartRing R π k) (π ^ k)
        rw [show algebraMap R (ParameterChartRing R π k) (π ^ k) =
          ReesBlowup.baseRingHom I r
            (algebraMap R (Ring R π (k + 2)) (π ^ k)) from rfl]
        rw [ReesBlowup.baseRingHom_apply]
      · change x R π (k + 2) * y R π (k + 2) =
          (algebraMap R (Ring R π (k + 2)) π) ^ 2 *
            algebraMap R (Ring R π (k + 2)) (π ^ k)
        rw [x_mul_y, map_pow, map_pow, ← pow_add]
        congr 1
        omega)

/-- The regular thickness-one `x`-side ring maps back to the `x` Rees chart. -/
noncomputable def xSideRingToXReesChartHom
    (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    Ring R π 1 →ₐ[R] XChartRing R π k := by
  let I := totalSpaceOriginIdeal R π (k + 2)
  let r := originCenterX R π (k + 2)
  exact lift π 1
    (ReesBlowup.baseElement I r (x R π (k + 2)))
    (ReesBlowup.ratioElement I r (originCenterParameter R π (k + 2))) (by
      change ReesBlowup.baseElement I r r.1 *
          ReesBlowup.ratioElement I r (originCenterParameter R π (k + 2)) = _
      rw [ReesBlowup.baseElement_mul_ratioElement I r
        (originCenterParameter R π (k + 2))]
      change ReesBlowup.baseElement I r
          (algebraMap R (Ring R π (k + 2)) π) =
        algebraMap R (XChartRing R π k) (π ^ 1)
      rw [pow_one]
      rw [show algebraMap R (XChartRing R π k) π =
        ReesBlowup.baseRingHom I r
          (algebraMap R (Ring R π (k + 2)) π) from rfl]
      rw [ReesBlowup.baseRingHom_apply])

/-- The regular thickness-one `y`-side ring maps back to the `y` Rees chart. -/
noncomputable def ySideRingToYReesChartHom
    (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    Ring R π 1 →ₐ[R] YChartRing R π k := by
  let I := totalSpaceOriginIdeal R π (k + 2)
  let r := originCenterY R π (k + 2)
  exact lift π 1
    (ReesBlowup.ratioElement I r (originCenterParameter R π (k + 2)))
    (ReesBlowup.baseElement I r (y R π (k + 2))) (by
      rw [mul_comm]
      change ReesBlowup.baseElement I r r.1 *
          ReesBlowup.ratioElement I r (originCenterParameter R π (k + 2)) = _
      rw [ReesBlowup.baseElement_mul_ratioElement I r
        (originCenterParameter R π (k + 2))]
      change ReesBlowup.baseElement I r
          (algebraMap R (Ring R π (k + 2)) π) =
        algebraMap R (YChartRing R π k) (π ^ 1)
      rw [pow_one]
      rw [show algebraMap R (YChartRing R π k) π =
        ReesBlowup.baseRingHom I r
          (algebraMap R (Ring R π (k + 2)) π) from rfl]
      rw [ReesBlowup.baseRingHom_apply])

/-- The affine-scheme morphism induced by the `x`-side substitution. -/
def xSideChartSpec (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    Spec (.of (Ring R π 1)) ⟶ Spec (.of (Ring R π (k + 2))) :=
  Spec.map (CommRingCat.ofHom (xSideChartMap R π k).toRingHom)

/-- The affine-scheme morphism induced by the `y`-side substitution. -/
def ySideChartSpec (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    Spec (.of (Ring R π 1)) ⟶ Spec (.of (Ring R π (k + 2))) :=
  Spec.map (CommRingCat.ofHom (ySideChartMap R π k).toRingHom)

/-- The `x`-side substitution is over `Spec R`. -/
@[reassoc (attr := simp)] theorem xSideChartSpec_toBaseSpec
    (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    xSideChartSpec R π k ≫ toBaseSpec R π (k + 2) = toBaseSpec R π 1 := by
  rw [xSideChartSpec, toBaseSpec, toBaseSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  exact RingHom.ext fun r => (xSideChartMap R π k).commutes r

/-- The `y`-side substitution is over `Spec R`. -/
@[reassoc (attr := simp)] theorem ySideChartSpec_toBaseSpec
    (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    ySideChartSpec R π k ≫ toBaseSpec R π (k + 2) = toBaseSpec R π 1 := by
  rw [ySideChartSpec, toBaseSpec, toBaseSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  exact RingHom.ext fun r => (ySideChartMap R π k).commutes r

private theorem unit_inv_mul_parameter
    (R : Type u) [CommRing R] (π : R) (hπ : IsUnit π) :
    (↑hπ.unit⁻¹ : R) * π = 1 := by
  calc
    (↑hπ.unit⁻¹ : R) * π = ↑hπ.unit⁻¹ * ↑hπ.unit :=
      congrArg ((↑hπ.unit⁻¹ : R) * ·) hπ.unit_spec.symm
    _ = 1 := by simp

private theorem unit_parameter_mul_inv
    (R : Type u) [CommRing R] (π : R) (hπ : IsUnit π) :
    π * (↑hπ.unit⁻¹ : R) = 1 := by
  calc
    π * (↑hπ.unit⁻¹ : R) = ↑hπ.unit * ↑hπ.unit⁻¹ :=
      congrArg (· * (↑hπ.unit⁻¹ : R)) hπ.unit_spec.symm
    _ = 1 := by simp

private theorem unit_inv_pow_mul_parameter_pow
    (R : Type u) [CommRing R] (π : R) (hπ : IsUnit π) (m : ℕ) :
    (↑hπ.unit⁻¹ : R) ^ m * π ^ m = 1 := by
  rw [← mul_pow, unit_inv_mul_parameter R π hπ, one_pow]

private theorem unit_parameter_pow_mul_inv_pow
    (R : Type u) [CommRing R] (π : R) (hπ : IsUnit π) (m : ℕ) :
    π ^ m * (↑hπ.unit⁻¹ : R) ^ m = 1 := by
  rw [← mul_pow, unit_parameter_mul_inv R π hπ, one_pow]

/-- Inverse `x`-side substitution when `π` is a unit. -/
def xSideChartInverseMapOfIsUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    Ring R π 1 →ₐ[R] Ring R π (k + 2) :=
  lift π 1
    (x R π (k + 2))
    (algebraMap R (Ring R π (k + 2)) ((↑hπ.unit⁻¹ : R) ^ (k + 1)) *
      y R π (k + 2)) (by
      rw [show x R π (k + 2) *
          (algebraMap R (Ring R π (k + 2)) ((↑hπ.unit⁻¹ : R) ^ (k + 1)) *
            y R π (k + 2)) =
          algebraMap R (Ring R π (k + 2)) ((↑hπ.unit⁻¹ : R) ^ (k + 1)) *
            (x R π (k + 2) * y R π (k + 2)) by ring,
        x_mul_y, ← map_mul]
      congr 1
      have hpow := unit_inv_pow_mul_parameter_pow R π hπ (k + 1)
      calc
        (↑hπ.unit⁻¹ : R) ^ (k + 1) * π ^ (k + 2) =
            ((↑hπ.unit⁻¹ : R) ^ (k + 1) * π ^ (k + 1)) * π := by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_add, pow_one]
          ring
        _ = π ^ 1 := by rw [hpow, one_mul, pow_one])

@[simp] theorem xSideChartInverseMapOfIsUnit_x
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    xSideChartInverseMapOfIsUnit R π k hπ (x R π 1) = x R π (k + 2) := by
  apply lift_x

@[simp] theorem xSideChartInverseMapOfIsUnit_y
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    xSideChartInverseMapOfIsUnit R π k hπ (y R π 1) =
      algebraMap R (Ring R π (k + 2)) ((↑hπ.unit⁻¹ : R) ^ (k + 1)) *
        y R π (k + 2) := by
  apply lift_y

/-- Inverse `y`-side substitution when `π` is a unit. -/
def ySideChartInverseMapOfIsUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    Ring R π 1 →ₐ[R] Ring R π (k + 2) :=
  lift π 1
    (algebraMap R (Ring R π (k + 2)) ((↑hπ.unit⁻¹ : R) ^ (k + 1)) *
      x R π (k + 2))
    (y R π (k + 2)) (by
      rw [show
          (algebraMap R (Ring R π (k + 2)) ((↑hπ.unit⁻¹ : R) ^ (k + 1)) *
            x R π (k + 2)) * y R π (k + 2) =
          algebraMap R (Ring R π (k + 2)) ((↑hπ.unit⁻¹ : R) ^ (k + 1)) *
            (x R π (k + 2) * y R π (k + 2)) by ring,
        x_mul_y, ← map_mul]
      congr 1
      have hpow := unit_inv_pow_mul_parameter_pow R π hπ (k + 1)
      calc
        (↑hπ.unit⁻¹ : R) ^ (k + 1) * π ^ (k + 2) =
            ((↑hπ.unit⁻¹ : R) ^ (k + 1) * π ^ (k + 1)) * π := by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_add, pow_one]
          ring
        _ = π ^ 1 := by rw [hpow, one_mul, pow_one])

@[simp] theorem ySideChartInverseMapOfIsUnit_x
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    ySideChartInverseMapOfIsUnit R π k hπ (x R π 1) =
      algebraMap R (Ring R π (k + 2)) ((↑hπ.unit⁻¹ : R) ^ (k + 1)) *
        x R π (k + 2) := by
  apply lift_x

@[simp] theorem ySideChartInverseMapOfIsUnit_y
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    ySideChartInverseMapOfIsUnit R π k hπ (y R π 1) = y R π (k + 2) := by
  apply lift_y

/-- The `x`-side substitution followed by its inverse is the identity when `π` is a unit. -/
theorem xSideChartMap_comp_inverse_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    (xSideChartMap R π k).comp (xSideChartInverseMapOfIsUnit R π k hπ) =
      AlgHom.id R (Ring R π 1) := by
  apply algHom_ext π 1
  · simp
  · simp only [AlgHom.coe_comp, Function.comp_apply, xSideChartInverseMapOfIsUnit_y,
      map_mul, AlgHom.commutes, xSideChartMap_y, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul,
      unit_inv_pow_mul_parameter_pow R π hπ (k + 1), map_one, one_mul]

/-- The inverse `x`-side substitution followed by the chart map is the identity when `π` is
a unit. -/
theorem xSideChartInverse_comp_map_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    (xSideChartInverseMapOfIsUnit R π k hπ).comp (xSideChartMap R π k) =
      AlgHom.id R (Ring R π (k + 2)) := by
  apply algHom_ext π (k + 2)
  · simp
  · simp only [AlgHom.coe_comp, Function.comp_apply, xSideChartMap_y, map_mul,
      AlgHom.commutes, xSideChartInverseMapOfIsUnit_y, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul,
      unit_parameter_pow_mul_inv_pow R π hπ (k + 1), map_one, one_mul]

/-- The `y`-side substitution followed by its inverse is the identity when `π` is a unit. -/
theorem ySideChartMap_comp_inverse_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    (ySideChartMap R π k).comp (ySideChartInverseMapOfIsUnit R π k hπ) =
      AlgHom.id R (Ring R π 1) := by
  apply algHom_ext π 1
  · simp only [AlgHom.coe_comp, Function.comp_apply, ySideChartInverseMapOfIsUnit_x,
      map_mul, AlgHom.commutes, ySideChartMap_x, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul,
      unit_inv_pow_mul_parameter_pow R π hπ (k + 1), map_one, one_mul]
  · simp

/-- The inverse `y`-side substitution followed by the chart map is the identity when `π` is
a unit. -/
theorem ySideChartInverse_comp_map_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    (ySideChartInverseMapOfIsUnit R π k hπ).comp (ySideChartMap R π k) =
      AlgHom.id R (Ring R π (k + 2)) := by
  apply algHom_ext π (k + 2)
  · simp only [AlgHom.coe_comp, Function.comp_apply, ySideChartMap_x, map_mul,
      AlgHom.commutes, ySideChartInverseMapOfIsUnit_x, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul,
      unit_parameter_pow_mul_inv_pow R π hπ (k + 1), map_one, one_mul]
  · simp

/-- The `x`-side chart is an algebra equivalence wherever `π` is a unit. -/
def xSideChartEquivOfIsUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    Ring R π (k + 2) ≃ₐ[R] Ring R π 1 :=
  AlgEquiv.ofAlgHom (xSideChartMap R π k) (xSideChartInverseMapOfIsUnit R π k hπ)
    (xSideChartMap_comp_inverse_of_isUnit R π k hπ)
    (xSideChartInverse_comp_map_of_isUnit R π k hπ)

/-- The `y`-side chart is an algebra equivalence wherever `π` is a unit. -/
def ySideChartEquivOfIsUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    Ring R π (k + 2) ≃ₐ[R] Ring R π 1 :=
  AlgEquiv.ofAlgHom (ySideChartMap R π k) (ySideChartInverseMapOfIsUnit R π k hπ)
    (ySideChartMap_comp_inverse_of_isUnit R π k hπ)
    (ySideChartInverse_comp_map_of_isUnit R π k hπ)

/-- Inverse central-chart substitution when `π` is a unit, dividing both coordinates by
`π`. -/
def centralChartInverseMapOfIsUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    Ring R π k →ₐ[R] Ring R π (k + 2) :=
  lift π k
    (algebraMap R (Ring R π (k + 2)) (↑hπ.unit⁻¹) * x R π (k + 2))
    (algebraMap R (Ring R π (k + 2)) (↑hπ.unit⁻¹) * y R π (k + 2)) (by
      rw [mul_mul_mul_comm, x_mul_y, ← map_mul, ← map_mul]
      congr 1
      have hinv_mul := unit_inv_mul_parameter R π hπ
      rw [pow_add, pow_two]
      calc
        (↑hπ.unit⁻¹ : R) * ↑hπ.unit⁻¹ * (π ^ k * (π * π)) =
            π ^ k * (((↑hπ.unit⁻¹ : R) * π) * (↑hπ.unit⁻¹ * π)) := by ring
        _ = π ^ k := by rw [hinv_mul]; simp)

@[simp] theorem centralChartInverseMapOfIsUnit_x
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    centralChartInverseMapOfIsUnit R π k hπ (x R π k) =
      algebraMap R (Ring R π (k + 2)) (↑hπ.unit⁻¹) * x R π (k + 2) := by
  apply lift_x

@[simp] theorem centralChartInverseMapOfIsUnit_y
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    centralChartInverseMapOfIsUnit R π k hπ (y R π k) =
      algebraMap R (Ring R π (k + 2)) (↑hπ.unit⁻¹) * y R π (k + 2) := by
  apply lift_y

/-- The chart substitution followed by division by `π` is the identity when `π` is a unit. -/
theorem centralChartMap_comp_inverse_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    (centralChartMap R π k).comp (centralChartInverseMapOfIsUnit R π k hπ) =
      AlgHom.id R (Ring R π k) := by
  apply algHom_ext π k
  · simp only [AlgHom.coe_comp, Function.comp_apply, centralChartInverseMapOfIsUnit_x,
      map_mul, AlgHom.commutes, centralChartMap_x, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul]
    have hinv_mul := unit_inv_mul_parameter R π hπ
    rw [hinv_mul, map_one, one_mul]
  · simp only [AlgHom.coe_comp, Function.comp_apply, centralChartInverseMapOfIsUnit_y,
      map_mul, AlgHom.commutes, centralChartMap_y, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul]
    have hinv_mul := unit_inv_mul_parameter R π hπ
    rw [hinv_mul, map_one, one_mul]

/-- Division by `π` followed by the chart substitution is the identity when `π` is a unit. -/
theorem centralChartInverse_comp_map_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    (centralChartInverseMapOfIsUnit R π k hπ).comp (centralChartMap R π k) =
      AlgHom.id R (Ring R π (k + 2)) := by
  apply algHom_ext π (k + 2)
  · simp only [AlgHom.coe_comp, Function.comp_apply, centralChartMap_x,
      map_mul, AlgHom.commutes, centralChartInverseMapOfIsUnit_x, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul]
    have hmul_inv := unit_parameter_mul_inv R π hπ
    rw [hmul_inv, map_one, one_mul]
  · simp only [AlgHom.coe_comp, Function.comp_apply, centralChartMap_y,
      map_mul, AlgHom.commutes, centralChartInverseMapOfIsUnit_y, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul]
    have hmul_inv := unit_parameter_mul_inv R π hπ
    rw [hmul_inv, map_one, one_mul]

/-- The central thickness-reduction map is an algebra equivalence wherever `π` is a unit. -/
def centralChartEquivOfIsUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    Ring R π (k + 2) ≃ₐ[R] Ring R π k :=
  AlgEquiv.ofAlgHom (centralChartMap R π k) (centralChartInverseMapOfIsUnit R π k hπ)
    (centralChartMap_comp_inverse_of_isUnit R π k hπ)
    (centralChartInverse_comp_map_of_isUnit R π k hπ)

/-! ## Injectivity before passing to the Rees charts -/

/-- The central substitution commutes with coefficient extension to the fraction field. -/
theorem centralChartMap_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (k : ℕ) :
    (coefficientAlgHom R (FractionRing R) π k).comp
        (centralChartMap R π k) =
      ((centralChartMap (FractionRing R)
        (algebraMap R (FractionRing R) π) k).restrictScalars R).comp
          (coefficientAlgHom R (FractionRing R) π (k + 2)) := by
  apply algHom_ext π (k + 2)
  · simp only [AlgHom.coe_comp, Function.comp_apply, centralChartMap_x, map_mul,
      AlgHom.commutes, coefficientAlgHom_x]
    change _ = centralChartMap (FractionRing R)
      (algebraMap R (FractionRing R) π) k
        (x (FractionRing R) (algebraMap R (FractionRing R) π) (k + 2))
    rw [centralChartMap_x]
    rw [← IsScalarTower.algebraMap_apply R (FractionRing R)]
  · simp only [AlgHom.coe_comp, Function.comp_apply, centralChartMap_y, map_mul,
      AlgHom.commutes, coefficientAlgHom_y]
    change _ = centralChartMap (FractionRing R)
      (algebraMap R (FractionRing R) π) k
        (y (FractionRing R) (algebraMap R (FractionRing R) π) (k + 2))
    rw [centralChartMap_y]
    rw [← IsScalarTower.algebraMap_apply R (FractionRing R)]

/-- The `x`-side substitution commutes with coefficient extension to the fraction field. -/
theorem xSideChartMap_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (k : ℕ) :
    (coefficientAlgHom R (FractionRing R) π 1).comp
        (xSideChartMap R π k) =
      ((xSideChartMap (FractionRing R)
        (algebraMap R (FractionRing R) π) k).restrictScalars R).comp
          (coefficientAlgHom R (FractionRing R) π (k + 2)) := by
  apply algHom_ext π (k + 2)
  · simp only [AlgHom.coe_comp, Function.comp_apply, xSideChartMap_x,
      coefficientAlgHom_x]
    change _ = xSideChartMap (FractionRing R)
      (algebraMap R (FractionRing R) π) k
        (x (FractionRing R) (algebraMap R (FractionRing R) π) (k + 2))
    rw [xSideChartMap_x]
  · simp only [AlgHom.coe_comp, Function.comp_apply, xSideChartMap_y, map_mul,
      AlgHom.commutes, coefficientAlgHom_y]
    change _ = xSideChartMap (FractionRing R)
      (algebraMap R (FractionRing R) π) k
        (y (FractionRing R) (algebraMap R (FractionRing R) π) (k + 2))
    rw [xSideChartMap_y, ← map_pow,
      ← IsScalarTower.algebraMap_apply R (FractionRing R)]

/-- The `y`-side substitution commutes with coefficient extension to the fraction field. -/
theorem ySideChartMap_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (k : ℕ) :
    (coefficientAlgHom R (FractionRing R) π 1).comp
        (ySideChartMap R π k) =
      ((ySideChartMap (FractionRing R)
        (algebraMap R (FractionRing R) π) k).restrictScalars R).comp
          (coefficientAlgHom R (FractionRing R) π (k + 2)) := by
  apply algHom_ext π (k + 2)
  · simp only [AlgHom.coe_comp, Function.comp_apply, ySideChartMap_x, map_mul,
      AlgHom.commutes, coefficientAlgHom_x]
    change _ = ySideChartMap (FractionRing R)
      (algebraMap R (FractionRing R) π) k
        (x (FractionRing R) (algebraMap R (FractionRing R) π) (k + 2))
    rw [ySideChartMap_x, ← map_pow,
      ← IsScalarTower.algebraMap_apply R (FractionRing R)]
  · simp only [AlgHom.coe_comp, Function.comp_apply, ySideChartMap_y,
      coefficientAlgHom_y]
    change _ = ySideChartMap (FractionRing R)
      (algebraMap R (FractionRing R) π) k
        (y (FractionRing R) (algebraMap R (FractionRing R) π) (k + 2))
    rw [ySideChartMap_y]

/-- The central substitution is injective over a domain with irreducible smoothing parameter. -/
theorem centralChartMap_injective
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    Function.Injective (centralChartMap R π k) := by
  have hRK : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  have hπK : IsUnit (algebraMap R (FractionRing R) π) :=
    isUnit_iff_ne_zero.mpr (by simpa using hRK.ne hπ.ne_zero)
  intro a b hab
  apply coefficientMap_injective_of_injective R (FractionRing R) π (k + 2) hRK
  apply (centralChartEquivOfIsUnit (FractionRing R)
    (algebraMap R (FractionRing R) π) k hπK).injective
  change centralChartMap (FractionRing R) (algebraMap R (FractionRing R) π) k
      (coefficientAlgHom R (FractionRing R) π (k + 2) a) =
    centralChartMap (FractionRing R) (algebraMap R (FractionRing R) π) k
      (coefficientAlgHom R (FractionRing R) π (k + 2) b)
  have hab' := congrArg (coefficientAlgHom R (FractionRing R) π k) hab
  have ha := congrArg (fun q ↦ q a) (centralChartMap_fractionRing R π k)
  have hb := congrArg (fun q ↦ q b) (centralChartMap_fractionRing R π k)
  have hresult := ha.symm.trans (hab'.trans hb)
  simp only [AlgHom.coe_comp, Function.comp_apply] at hresult
  change centralChartMap (FractionRing R) (algebraMap R (FractionRing R) π) k
      (coefficientAlgHom R (FractionRing R) π (k + 2) a) =
    centralChartMap (FractionRing R) (algebraMap R (FractionRing R) π) k
      (coefficientAlgHom R (FractionRing R) π (k + 2) b) at hresult
  exact hresult

/-- The `x`-side substitution is injective over a domain with irreducible smoothing parameter. -/
theorem xSideChartMap_injective
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    Function.Injective (xSideChartMap R π k) := by
  have hRK : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  have hπK : IsUnit (algebraMap R (FractionRing R) π) :=
    isUnit_iff_ne_zero.mpr (by simpa using hRK.ne hπ.ne_zero)
  intro a b hab
  apply coefficientMap_injective_of_injective R (FractionRing R) π (k + 2) hRK
  apply (xSideChartEquivOfIsUnit (FractionRing R)
    (algebraMap R (FractionRing R) π) k hπK).injective
  change xSideChartMap (FractionRing R) (algebraMap R (FractionRing R) π) k
      (coefficientAlgHom R (FractionRing R) π (k + 2) a) =
    xSideChartMap (FractionRing R) (algebraMap R (FractionRing R) π) k
      (coefficientAlgHom R (FractionRing R) π (k + 2) b)
  have hab' := congrArg (coefficientAlgHom R (FractionRing R) π 1) hab
  have ha := congrArg (fun q ↦ q a) (xSideChartMap_fractionRing R π k)
  have hb := congrArg (fun q ↦ q b) (xSideChartMap_fractionRing R π k)
  have hresult := ha.symm.trans (hab'.trans hb)
  simp only [AlgHom.coe_comp, Function.comp_apply] at hresult
  change xSideChartMap (FractionRing R) (algebraMap R (FractionRing R) π) k
      (coefficientAlgHom R (FractionRing R) π (k + 2) a) =
    xSideChartMap (FractionRing R) (algebraMap R (FractionRing R) π) k
      (coefficientAlgHom R (FractionRing R) π (k + 2) b) at hresult
  exact hresult

/-- The `y`-side substitution is injective over a domain with irreducible smoothing parameter. -/
theorem ySideChartMap_injective
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    Function.Injective (ySideChartMap R π k) := by
  have hRK : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  have hπK : IsUnit (algebraMap R (FractionRing R) π) :=
    isUnit_iff_ne_zero.mpr (by simpa using hRK.ne hπ.ne_zero)
  intro a b hab
  apply coefficientMap_injective_of_injective R (FractionRing R) π (k + 2) hRK
  apply (ySideChartEquivOfIsUnit (FractionRing R)
    (algebraMap R (FractionRing R) π) k hπK).injective
  change ySideChartMap (FractionRing R) (algebraMap R (FractionRing R) π) k
      (coefficientAlgHom R (FractionRing R) π (k + 2) a) =
    ySideChartMap (FractionRing R) (algebraMap R (FractionRing R) π) k
      (coefficientAlgHom R (FractionRing R) π (k + 2) b)
  have hab' := congrArg (coefficientAlgHom R (FractionRing R) π 1) hab
  have ha := congrArg (fun q ↦ q a) (ySideChartMap_fractionRing R π k)
  have hb := congrArg (fun q ↦ q b) (ySideChartMap_fractionRing R π k)
  have hresult := ha.symm.trans (hab'.trans hb)
  simp only [AlgHom.coe_comp, Function.comp_apply] at hresult
  change ySideChartMap (FractionRing R) (algebraMap R (FractionRing R) π) k
      (coefficientAlgHom R (FractionRing R) π (k + 2) a) =
    ySideChartMap (FractionRing R) (algebraMap R (FractionRing R) π) k
      (coefficientAlgHom R (FractionRing R) π (k + 2) b) at hresult
  exact hresult

/-! ## Identification of the three Rees charts -/

/-- The forward parameter-chart map followed by its explicit inverse is the identity. -/
theorem parameterReesChartToCentral_comp_inverse
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    (parameterReesChartToCentralAlgHom R π hπ k).comp
        (centralRingToParameterReesChartHom R π k) =
      AlgHom.id R (Ring R π k) := by
  apply algHom_ext π k
  · simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply,
      centralRingToParameterReesChartHom, lift_x]
    change parameterReesChartToCentralRingHom R π hπ k
      (ReesBlowup.ratioElement (totalSpaceOriginIdeal R π (k + 2))
        (originCenterParameter R π (k + 2)) (originCenterX R π (k + 2))) =
      x R π k
    rw [parameterReesChartToCentralRingHom,
      ReesBlowup.chartLift_ratioElement _ _ _ _ _ _ (x R π k)]
    change x R π k * centralChartMap R π k
        (algebraMap R (Ring R π (k + 2)) π) =
      centralChartMap R π k (x R π (k + 2))
    rw [(centralChartMap R π k).commutes, centralChartMap_x]
    ring
  · simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply,
      centralRingToParameterReesChartHom, lift_y]
    change parameterReesChartToCentralRingHom R π hπ k
      (ReesBlowup.ratioElement (totalSpaceOriginIdeal R π (k + 2))
        (originCenterParameter R π (k + 2)) (originCenterY R π (k + 2))) =
      y R π k
    rw [parameterReesChartToCentralRingHom,
      ReesBlowup.chartLift_ratioElement _ _ _ _ _ _ (y R π k)]
    change y R π k * centralChartMap R π k
        (algebraMap R (Ring R π (k + 2)) π) =
      centralChartMap R π k (y R π (k + 2))
    rw [(centralChartMap R π k).commutes, centralChartMap_y]
    ring

/-- The forward `x`-chart map followed by its explicit inverse is the identity. -/
theorem xReesChartToSide_comp_inverse
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    (xReesChartToSideAlgHom R π hπ k).comp
        (xSideRingToXReesChartHom R π k) =
      AlgHom.id R (Ring R π 1) := by
  apply algHom_ext π 1
  · simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply,
      xSideRingToXReesChartHom, lift_x]
    change xReesChartToSideRingHom R π hπ k
      (ReesBlowup.baseElement (totalSpaceOriginIdeal R π (k + 2))
        (originCenterX R π (k + 2)) (x R π (k + 2))) = x R π 1
    rw [xReesChartToSideRingHom, ReesBlowup.chartLift_baseElement]
    exact xSideChartMap_x R π k
  · simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply,
      xSideRingToXReesChartHom, lift_y]
    change xReesChartToSideRingHom R π hπ k
      (ReesBlowup.ratioElement (totalSpaceOriginIdeal R π (k + 2))
        (originCenterX R π (k + 2)) (originCenterParameter R π (k + 2))) =
      y R π 1
    rw [xReesChartToSideRingHom,
      ReesBlowup.chartLift_ratioElement _ _ _ _ _ _ (y R π 1)]
    change y R π 1 * xSideChartMap R π k (x R π (k + 2)) =
      xSideChartMap R π k (algebraMap R (Ring R π (k + 2)) π)
    rw [xSideChartMap_x, (xSideChartMap R π k).commutes]
    simpa only [pow_one, mul_comm] using x_mul_y R π 1

/-- The forward `y`-chart map followed by its explicit inverse is the identity. -/
theorem yReesChartToSide_comp_inverse
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    (yReesChartToSideAlgHom R π hπ k).comp
        (ySideRingToYReesChartHom R π k) =
      AlgHom.id R (Ring R π 1) := by
  apply algHom_ext π 1
  · simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply,
      ySideRingToYReesChartHom, lift_x]
    change yReesChartToSideRingHom R π hπ k
      (ReesBlowup.ratioElement (totalSpaceOriginIdeal R π (k + 2))
        (originCenterY R π (k + 2)) (originCenterParameter R π (k + 2))) =
      x R π 1
    rw [yReesChartToSideRingHom,
      ReesBlowup.chartLift_ratioElement _ _ _ _ _ _ (x R π 1)]
    change x R π 1 * ySideChartMap R π k (y R π (k + 2)) =
      ySideChartMap R π k (algebraMap R (Ring R π (k + 2)) π)
    rw [ySideChartMap_y, (ySideChartMap R π k).commutes]
    simpa only [pow_one] using x_mul_y R π 1
  · simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply,
      ySideRingToYReesChartHom, lift_y]
    change yReesChartToSideRingHom R π hπ k
      (ReesBlowup.baseElement (totalSpaceOriginIdeal R π (k + 2))
        (originCenterY R π (k + 2)) (y R π (k + 2))) = y R π 1
    rw [yReesChartToSideRingHom, ReesBlowup.chartLift_baseElement]
    exact ySideChartMap_y R π k

/-- The parameter Rees-chart map is injective. -/
theorem parameterReesChartToCentral_injective
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    Function.Injective (parameterReesChartToCentralAlgHom R π hπ k) := by
  change Function.Injective (parameterReesChartToCentralRingHom R π hπ k)
  rw [parameterReesChartToCentralRingHom]
  apply ReesBlowup.chartLift_injective
  exact centralChartMap_injective R π hπ k

/-- The `x` Rees-chart map is injective. -/
theorem xReesChartToSide_injective
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    Function.Injective (xReesChartToSideAlgHom R π hπ k) := by
  change Function.Injective (xReesChartToSideRingHom R π hπ k)
  rw [xReesChartToSideRingHom]
  apply ReesBlowup.chartLift_injective
  exact xSideChartMap_injective R π hπ k

/-- The `y` Rees-chart map is injective. -/
theorem yReesChartToSide_injective
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    Function.Injective (yReesChartToSideAlgHom R π hπ k) := by
  change Function.Injective (yReesChartToSideRingHom R π hπ k)
  rw [yReesChartToSideRingHom]
  apply ReesBlowup.chartLift_injective
  exact ySideChartMap_injective R π hπ k

/-- The explicit inverse followed by the parameter-chart map is the identity. -/
theorem centralInverse_comp_parameterReesChartToCentral
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    (centralRingToParameterReesChartHom R π k).comp
        (parameterReesChartToCentralAlgHom R π hπ k) =
      AlgHom.id R (ParameterChartRing R π k) := by
  apply DFunLike.ext _ _
  intro z
  apply parameterReesChartToCentral_injective R π hπ k
  have h := congrArg (fun q ↦ q (parameterReesChartToCentralAlgHom R π hπ k z))
    (parameterReesChartToCentral_comp_inverse R π hπ k)
  simpa only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply] using h

/-- The explicit inverse followed by the `x`-chart map is the identity. -/
theorem xSideInverse_comp_xReesChartToSide
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    (xSideRingToXReesChartHom R π k).comp
        (xReesChartToSideAlgHom R π hπ k) =
      AlgHom.id R (XChartRing R π k) := by
  apply DFunLike.ext _ _
  intro z
  apply xReesChartToSide_injective R π hπ k
  have h := congrArg (fun q ↦ q (xReesChartToSideAlgHom R π hπ k z))
    (xReesChartToSide_comp_inverse R π hπ k)
  simpa only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply] using h

/-- The explicit inverse followed by the `y`-chart map is the identity. -/
theorem ySideInverse_comp_yReesChartToSide
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    (ySideRingToYReesChartHom R π k).comp
        (yReesChartToSideAlgHom R π hπ k) =
      AlgHom.id R (YChartRing R π k) := by
  apply DFunLike.ext _ _
  intro z
  apply yReesChartToSide_injective R π hπ k
  have h := congrArg (fun q ↦ q (yReesChartToSideAlgHom R π hπ k z))
    (yReesChartToSide_comp_inverse R π hπ k)
  simpa only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply] using h

/-- The parameter Rees chart is the explicit central thickness-`k` node chart. -/
noncomputable def parameterReesChartEquiv
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    ParameterChartRing R π k ≃ₐ[R] Ring R π k :=
  AlgEquiv.ofAlgHom (parameterReesChartToCentralAlgHom R π hπ k)
    (centralRingToParameterReesChartHom R π k)
    (parameterReesChartToCentral_comp_inverse R π hπ k)
    (centralInverse_comp_parameterReesChartToCentral R π hπ k)

/-- The `x` Rees chart is the explicit regular thickness-one side chart. -/
noncomputable def xReesChartEquiv
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    XChartRing R π k ≃ₐ[R] Ring R π 1 :=
  AlgEquiv.ofAlgHom (xReesChartToSideAlgHom R π hπ k)
    (xSideRingToXReesChartHom R π k)
    (xReesChartToSide_comp_inverse R π hπ k)
    (xSideInverse_comp_xReesChartToSide R π hπ k)

/-- The `y` Rees chart is the explicit regular thickness-one side chart. -/
noncomputable def yReesChartEquiv
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    YChartRing R π k ≃ₐ[R] Ring R π 1 :=
  AlgEquiv.ofAlgHom (yReesChartToSideAlgHom R π hπ k)
    (ySideRingToYReesChartHom R π k)
    (yReesChartToSide_comp_inverse R π hπ k)
    (ySideInverse_comp_yReesChartToSide R π hπ k)

/-- Scheme-level identification of the parameter Rees chart with the central node chart. -/
noncomputable def parameterReesChartIso
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    originBlowupParameterChart R π (k + 2) ≅ Spec (.of (Ring R π k)) :=
  Scheme.Spec.mapIso
    (parameterReesChartEquiv R π hπ k).toRingEquiv.toCommRingCatIso.op.symm

/-- Scheme-level identification of the `x` Rees chart with the regular side chart. -/
noncomputable def xReesChartIso
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    originBlowupXChart R π (k + 2) ≅ Spec (.of (Ring R π 1)) :=
  Scheme.Spec.mapIso
    (xReesChartEquiv R π hπ k).toRingEquiv.toCommRingCatIso.op.symm

/-- Scheme-level identification of the `y` Rees chart with the regular side chart. -/
noncomputable def yReesChartIso
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    originBlowupYChart R π (k + 2) ≅ Spec (.of (Ring R π 1)) :=
  Scheme.Spec.mapIso
    (yReesChartEquiv R π hπ k).toRingEquiv.toCommRingCatIso.op.symm

/-! ## Regularity of the explicit blowup charts -/

/-- The parameter chart is regular whenever its lower-thickness node ring is regular. -/
theorem parameterBlowupChart_isRegular
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ)
    (hregular : IsRegularRing (Ring R π k)) :
    SchemeIsRegular (originBlowupParameterChart R π (k + 2)) := by
  let _ : IsRegularRing (Ring R π k) := hregular
  exact (SchemeIsRegular.iso_iff (parameterReesChartIso R π hπ k)).2
    (SchemeIsRegular.spec (Ring R π k))

/-- Every `x`-side chart of the local node blowup is regular. -/
theorem xBlowupChart_isRegular
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (k : ℕ) :
    SchemeIsRegular (originBlowupXChart R π (k + 2)) := by
  let _ : IsRegularRing (Ring R π 1) := ring_one_isRegularRing R π hπ
  exact (SchemeIsRegular.iso_iff (xReesChartIso R π hπ k)).2
    (SchemeIsRegular.spec (Ring R π 1))

/-- Every `y`-side chart of the local node blowup is regular. -/
theorem yBlowupChart_isRegular
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (k : ℕ) :
    SchemeIsRegular (originBlowupYChart R π (k + 2)) := by
  let _ : IsRegularRing (Ring R π 1) := ring_one_isRegularRing R π hπ
  exact (SchemeIsRegular.iso_iff (yReesChartIso R π hπ k)).2
    (SchemeIsRegular.spec (Ring R π 1))

/-- If the lower-thickness central chart is regular, then the whole blowup is regular.  The
proof uses the genuine three-chart affine cover of the Rees `Proj`; the two side charts are
always thickness one. -/
theorem originBlowup_isRegular_of_central
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (k : ℕ)
    (hregular : IsRegularRing (Ring R π k)) :
    SchemeIsRegular (originBlowup R π (k + 2)) := by
  apply SchemeIsRegular.of_affineOpenCover
    (originBlowupThreeChartCover R π (k + 2))
  change ∀ i : Fin 3,
    SchemeIsRegular
      (Spec (.of
        (HomogeneousLocalization.Away
          (ReesBlowup.grade (totalSpaceOriginIdeal R π (k + 2)))
          (ReesBlowup.generatorOfFamily (totalSpaceOriginIdeal R π (k + 2))
            (originCenterFamily R π (k + 2))
            (totalSpaceOriginIdeal_eq_span_range_originCenterFamily R π (k + 2)) i))))
  intro i
  fin_cases i
  · simp only
    rw [originCenterFamily_generator_eq R π (k + 2) _ (originCenterX R π (k + 2))
      (by simp [originCenterFamily, originCenterX])]
    exact xBlowupChart_isRegular R π hπ k
  · simp only
    rw [originCenterFamily_generator_eq R π (k + 2) _ (originCenterY R π (k + 2))
      (by simp [originCenterFamily, originCenterY])]
    exact yBlowupChart_isRegular R π hπ k
  · simp only
    rw [originCenterFamily_generator_eq R π (k + 2) _
      (originCenterParameter R π (k + 2))
      (by simp [originCenterFamily, originCenterParameter])]
    exact parameterBlowupChart_isRegular R π hπ k hregular

/-- Blowing up a thickness-two node at its closed origin gives a regular scheme. -/
theorem originBlowup_two_isRegular
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) :
    SchemeIsRegular (originBlowup R π 2) := by
  have hregular : IsRegularRing (Ring R π 0) := ring_zero_isRegularRing R π
  simpa using originBlowup_isRegular_of_central R π hπ 0 hregular

/-- Blowing up a thickness-three node at its closed origin gives a regular scheme. -/
theorem originBlowup_three_isRegular
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) :
    SchemeIsRegular (originBlowup R π 3) := by
  have hregular : IsRegularRing (Ring R π 1) := ring_one_isRegularRing R π hπ
  simpa using originBlowup_isRegular_of_central R π hπ 1 hregular

/-- Under the parameter-chart identification, the degree-zero map is the central
substitution. -/
theorem centralInverse_comp_centralChartMap
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    (centralRingToParameterReesChartHom R π k).comp (centralChartMap R π k) =
      parameterChartBaseAlgHom R π k := by
  apply DFunLike.ext _ _
  intro a
  apply parameterReesChartToCentral_injective R π hπ k
  calc
    parameterReesChartToCentralAlgHom R π hπ k
        (((centralRingToParameterReesChartHom R π k).comp
          (centralChartMap R π k)) a) = centralChartMap R π k a := by
      have h := congrArg (fun q ↦ q (centralChartMap R π k a))
        (parameterReesChartToCentral_comp_inverse R π hπ k)
      simpa only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply] using h
    _ = parameterReesChartToCentralAlgHom R π hπ k
        (parameterChartBaseAlgHom R π k a) := by
      change centralChartMap R π k a = parameterReesChartToCentralRingHom R π hπ k
        (ReesBlowup.baseRingHom (totalSpaceOriginIdeal R π (k + 2))
          (originCenterParameter R π (k + 2)) a)
      rw [parameterReesChartToCentralRingHom, ReesBlowup.chartLift_baseRingHom]
      rfl

/-- Under the `x`-chart identification, the degree-zero map is the side substitution. -/
theorem xSideInverse_comp_xSideChartMap
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    (xSideRingToXReesChartHom R π k).comp (xSideChartMap R π k) =
      xChartBaseAlgHom R π k := by
  apply DFunLike.ext _ _
  intro a
  apply xReesChartToSide_injective R π hπ k
  calc
    xReesChartToSideAlgHom R π hπ k
        (((xSideRingToXReesChartHom R π k).comp (xSideChartMap R π k)) a) =
      xSideChartMap R π k a := by
        have h := congrArg (fun q ↦ q (xSideChartMap R π k a))
          (xReesChartToSide_comp_inverse R π hπ k)
        simpa only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply] using h
    _ = xReesChartToSideAlgHom R π hπ k (xChartBaseAlgHom R π k a) := by
      change xSideChartMap R π k a = xReesChartToSideRingHom R π hπ k
        (ReesBlowup.baseRingHom (totalSpaceOriginIdeal R π (k + 2))
          (originCenterX R π (k + 2)) a)
      rw [xReesChartToSideRingHom, ReesBlowup.chartLift_baseRingHom]
      rfl

/-- Under the `y`-chart identification, the degree-zero map is the side substitution. -/
theorem ySideInverse_comp_ySideChartMap
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    (ySideRingToYReesChartHom R π k).comp (ySideChartMap R π k) =
      yChartBaseAlgHom R π k := by
  apply DFunLike.ext _ _
  intro a
  apply yReesChartToSide_injective R π hπ k
  calc
    yReesChartToSideAlgHom R π hπ k
        (((ySideRingToYReesChartHom R π k).comp (ySideChartMap R π k)) a) =
      ySideChartMap R π k a := by
        have h := congrArg (fun q ↦ q (ySideChartMap R π k a))
          (yReesChartToSide_comp_inverse R π hπ k)
        simpa only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply] using h
    _ = yReesChartToSideAlgHom R π hπ k (yChartBaseAlgHom R π k a) := by
      change ySideChartMap R π k a = yReesChartToSideRingHom R π hπ k
        (ReesBlowup.baseRingHom (totalSpaceOriginIdeal R π (k + 2))
          (originCenterY R π (k + 2)) a)
      rw [yReesChartToSideRingHom, ReesBlowup.chartLift_baseRingHom]
      rfl

/-- The parameter-chart isomorphism identifies the blowup projection with the central
substitution. -/
theorem parameterReesChartIso_projection
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    (parameterReesChartIso R π hπ k).hom ≫ centralChartSpec R π k =
      originBlowupParameterChartMap R π (k + 2) ≫
        originBlowupProjection R π (k + 2) := by
  rw [originBlowupParameterChartMap, originBlowupProjection,
    ReesBlowup.chartMap_projection]
  simp only [parameterReesChartIso, Functor.mapIso_hom, Iso.symm_hom, Scheme.Spec_map]
  rw [centralChartSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  change ((centralRingToParameterReesChartHom R π k).comp
    (centralChartMap R π k)).toRingHom = (parameterChartBaseAlgHom R π k).toRingHom
  exact congrArg AlgHom.toRingHom (centralInverse_comp_centralChartMap R π hπ k)

/-- The `x`-chart isomorphism identifies the blowup projection with the `x`-side
substitution. -/
theorem xReesChartIso_projection
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    (xReesChartIso R π hπ k).hom ≫ xSideChartSpec R π k =
      originBlowupXChartMap R π (k + 2) ≫ originBlowupProjection R π (k + 2) := by
  rw [originBlowupXChartMap, originBlowupProjection, ReesBlowup.chartMap_projection]
  simp only [xReesChartIso, Functor.mapIso_hom, Iso.symm_hom, Scheme.Spec_map]
  rw [xSideChartSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  change ((xSideRingToXReesChartHom R π k).comp
    (xSideChartMap R π k)).toRingHom = (xChartBaseAlgHom R π k).toRingHom
  exact congrArg AlgHom.toRingHom (xSideInverse_comp_xSideChartMap R π hπ k)

/-- The `y`-chart isomorphism identifies the blowup projection with the `y`-side
substitution. -/
theorem yReesChartIso_projection
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (k : ℕ) :
    (yReesChartIso R π hπ k).hom ≫ ySideChartSpec R π k =
      originBlowupYChartMap R π (k + 2) ≫ originBlowupProjection R π (k + 2) := by
  rw [originBlowupYChartMap, originBlowupProjection, ReesBlowup.chartMap_projection]
  simp only [yReesChartIso, Functor.mapIso_hom, Iso.symm_hom, Scheme.Spec_map]
  rw [ySideChartSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  change ((ySideRingToYReesChartHom R π k).comp
    (ySideChartMap R π k)).toRingHom = (yChartBaseAlgHom R π k).toRingHom
  exact congrArg AlgHom.toRingHom (ySideInverse_comp_ySideChartMap R π hπ k)

/-- The coordinate-ring map of the central chart is an isomorphism when `π` is invertible. -/
theorem centralChartRingMap_isIso_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    IsIso (CommRingCat.ofHom (centralChartMap R π k).toRingHom) := by
  change IsIso
    (centralChartEquivOfIsUnit R π k hπ).toRingEquiv.toCommRingCatIso.hom
  infer_instance

/-- The central-chart scheme morphism is an isomorphism away from the closed fibre. -/
theorem centralChartSpec_isIso_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    IsIso (centralChartSpec R π k) := by
  let _ : IsIso (CommRingCat.ofHom (centralChartMap R π k).toRingHom) :=
    centralChartRingMap_isIso_of_isUnit R π k hπ
  rw [centralChartSpec]
  infer_instance

/-- The coordinate-ring map of the `x`-side chart is an isomorphism when `π` is invertible. -/
theorem xSideChartRingMap_isIso_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    IsIso (CommRingCat.ofHom (xSideChartMap R π k).toRingHom) := by
  change IsIso
    (xSideChartEquivOfIsUnit R π k hπ).toRingEquiv.toCommRingCatIso.hom
  infer_instance

/-- The coordinate-ring map of the `y`-side chart is an isomorphism when `π` is invertible. -/
theorem ySideChartRingMap_isIso_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    IsIso (CommRingCat.ofHom (ySideChartMap R π k).toRingHom) := by
  change IsIso
    (ySideChartEquivOfIsUnit R π k hπ).toRingEquiv.toCommRingCatIso.hom
  infer_instance

/-- The `x`-side scheme morphism is an isomorphism away from the closed fibre. -/
theorem xSideChartSpec_isIso_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    IsIso (xSideChartSpec R π k) := by
  let _ : IsIso (CommRingCat.ofHom (xSideChartMap R π k).toRingHom) :=
    xSideChartRingMap_isIso_of_isUnit R π k hπ
  rw [xSideChartSpec]
  infer_instance

/-- The `y`-side scheme morphism is an isomorphism away from the closed fibre. -/
theorem ySideChartSpec_isIso_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k : ℕ) (hπ : IsUnit π) :
    IsIso (ySideChartSpec R π k) := by
  let _ : IsIso (CommRingCat.ofHom (ySideChartMap R π k).toRingHom) :=
    ySideChartRingMap_isIso_of_isUnit R π k hπ
  rw [ySideChartSpec]
  infer_instance

/-! ## Iterated central charts -/

/-- The thickness obtained by starting at `k` and reversing `m` central-chart reductions. -/
def centralChartThickness (k : ℕ) : ℕ → ℕ
  | 0 => k
  | m + 1 => centralChartThickness k m + 2

@[simp] theorem centralChartThickness_zero (k : ℕ) :
    centralChartThickness k 0 = k := rfl

@[simp] theorem centralChartThickness_succ (k m : ℕ) :
    centralChartThickness k (m + 1) = centralChartThickness k m + 2 := rfl

/-- After `m` central reductions, the starting thickness is `k + 2m`. -/
theorem centralChartThickness_eq (k m : ℕ) :
    centralChartThickness k m = k + 2 * m := by
  induction m with
  | zero => simp
  | succ m ih => simp [ih, Nat.mul_add, Nat.add_assoc]

/-- The composite coordinate-ring map for `m` central thickness reductions. -/
def iteratedCentralChartMap (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    (m : ℕ) → Ring R π (centralChartThickness k m) →ₐ[R] Ring R π k
  | 0 => AlgHom.id R (Ring R π k)
  | m + 1 => (iteratedCentralChartMap R π k m).comp
      (centralChartMap R π (centralChartThickness k m))

@[simp] theorem iteratedCentralChartMap_zero
    (R : Type u) [CommRing R] (π : R) (k : ℕ) :
    iteratedCentralChartMap R π k 0 = AlgHom.id R (Ring R π k) := rfl

@[simp] theorem iteratedCentralChartMap_succ
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) :
    iteratedCentralChartMap R π k (m + 1) =
      (iteratedCentralChartMap R π k m).comp
        (centralChartMap R π (centralChartThickness k m)) := rfl

/-- After `m` central reductions, the original `x` coordinate is scaled by `π^m`. -/
@[simp] theorem iteratedCentralChartMap_x
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) :
    iteratedCentralChartMap R π k m (x R π (centralChartThickness k m)) =
      algebraMap R (Ring R π k) (π ^ m) * x R π k := by
  induction m with
  | zero =>
      change (AlgHom.id R (Ring R π k)) (x R π k) =
        algebraMap R (Ring R π k) (π ^ 0) * x R π k
      simp
  | succ m ih =>
      rw [iteratedCentralChartMap_succ]
      change iteratedCentralChartMap R π k m
        (centralChartMap R π (centralChartThickness k m)
          (x R π (centralChartThickness k m + 2))) = _
      rw [centralChartMap_x, map_mul, AlgHom.commutes, ih, pow_succ, map_mul]
      ring

/-- After `m` central reductions, the original `y` coordinate is scaled by `π^m`. -/
@[simp] theorem iteratedCentralChartMap_y
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) :
    iteratedCentralChartMap R π k m (y R π (centralChartThickness k m)) =
      algebraMap R (Ring R π k) (π ^ m) * y R π k := by
  induction m with
  | zero =>
      change (AlgHom.id R (Ring R π k)) (y R π k) =
        algebraMap R (Ring R π k) (π ^ 0) * y R π k
      simp
  | succ m ih =>
      rw [iteratedCentralChartMap_succ]
      change iteratedCentralChartMap R π k m
        (centralChartMap R π (centralChartThickness k m)
          (y R π (centralChartThickness k m + 2))) = _
      rw [centralChartMap_y, map_mul, AlgHom.commutes, ih, pow_succ, map_mul]
      ring

/-- Every nonempty composite of central charts still principalizes the original origin ideal,
now by the terminal chart's parameter. -/
theorem iteratedCentralChartMap_originIdeal
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) (hm : 0 < m) :
    (totalSpaceOriginIdeal R π (centralChartThickness k m)).map
        (iteratedCentralChartMap R π k m).toRingHom =
      Ideal.span {algebraMap R (Ring R π k) π} := by
  rw [totalSpaceOriginIdeal, Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z ⟨w, (rfl | rfl | rfl), rfl⟩
    · change iteratedCentralChartMap R π k m
        (x R π (centralChartThickness k m)) ∈ _
      rw [iteratedCentralChartMap_x, map_pow]
      exact (Ideal.span {algebraMap R (Ring R π k) π}).mul_mem_right _
        ((Ideal.span {algebraMap R (Ring R π k) π}).pow_mem_of_mem
          (Ideal.subset_span (Set.mem_singleton _)) m hm)
    · change iteratedCentralChartMap R π k m
        (y R π (centralChartThickness k m)) ∈ _
      rw [iteratedCentralChartMap_y, map_pow]
      exact (Ideal.span {algebraMap R (Ring R π k) π}).mul_mem_right _
        ((Ideal.span {algebraMap R (Ring R π k) π}).pow_mem_of_mem
          (Ideal.subset_span (Set.mem_singleton _)) m hm)
    · change iteratedCentralChartMap R π k m
        (algebraMap R (Ring R π (centralChartThickness k m)) π) ∈ _
      rw [(iteratedCentralChartMap R π k m).commutes]
      exact Ideal.subset_span (Set.mem_singleton _)
  · rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    apply Ideal.subset_span
    refine ⟨algebraMap R (Ring R π (centralChartThickness k m)) π, ?_, ?_⟩
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact (iteratedCentralChartMap R π k m).commutes π

/-- Inverse of an iterated central-chart substitution when `π` is a unit, scaling both
coordinates by `(1 / π)^m`. -/
def iteratedCentralChartInverseMapOfIsUnit
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) (hπ : IsUnit π) :
    Ring R π k →ₐ[R] Ring R π (centralChartThickness k m) :=
  lift π k
    (algebraMap R (Ring R π (centralChartThickness k m)) ((↑hπ.unit⁻¹ : R) ^ m) *
      x R π (centralChartThickness k m))
    (algebraMap R (Ring R π (centralChartThickness k m)) ((↑hπ.unit⁻¹ : R) ^ m) *
      y R π (centralChartThickness k m)) (by
      rw [mul_mul_mul_comm, x_mul_y, ← map_mul, ← map_mul]
      congr 1
      rw [← pow_add, show m + m = 2 * m by omega, centralChartThickness_eq, pow_add]
      calc
        (↑hπ.unit⁻¹ : R) ^ (2 * m) * (π ^ k * π ^ (2 * m)) =
            π ^ k * ((↑hπ.unit⁻¹ : R) ^ (2 * m) * π ^ (2 * m)) := by ring
        _ = π ^ k := by
          rw [unit_inv_pow_mul_parameter_pow R π hπ (2 * m), mul_one])

@[simp] theorem iteratedCentralChartInverseMapOfIsUnit_x
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) (hπ : IsUnit π) :
    iteratedCentralChartInverseMapOfIsUnit R π k m hπ (x R π k) =
      algebraMap R (Ring R π (centralChartThickness k m)) ((↑hπ.unit⁻¹ : R) ^ m) *
        x R π (centralChartThickness k m) := by
  apply lift_x

@[simp] theorem iteratedCentralChartInverseMapOfIsUnit_y
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) (hπ : IsUnit π) :
    iteratedCentralChartInverseMapOfIsUnit R π k m hπ (y R π k) =
      algebraMap R (Ring R π (centralChartThickness k m)) ((↑hπ.unit⁻¹ : R) ^ m) *
        y R π (centralChartThickness k m) := by
  apply lift_y

/-- An iterated central-chart map followed by division by `π^m` is the identity when `π`
is a unit. -/
theorem iteratedCentralChartMap_comp_inverse_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) (hπ : IsUnit π) :
    (iteratedCentralChartMap R π k m).comp
        (iteratedCentralChartInverseMapOfIsUnit R π k m hπ) =
      AlgHom.id R (Ring R π k) := by
  apply algHom_ext π k
  · simp only [AlgHom.coe_comp, Function.comp_apply,
      iteratedCentralChartInverseMapOfIsUnit_x, map_mul, AlgHom.commutes,
      iteratedCentralChartMap_x, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul,
      unit_inv_pow_mul_parameter_pow R π hπ m, map_one, one_mul]
  · simp only [AlgHom.coe_comp, Function.comp_apply,
      iteratedCentralChartInverseMapOfIsUnit_y, map_mul, AlgHom.commutes,
      iteratedCentralChartMap_y, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul,
      unit_inv_pow_mul_parameter_pow R π hπ m, map_one, one_mul]

/-- Division by `π^m` followed by an iterated central-chart map is the identity when `π` is
a unit. -/
theorem iteratedCentralChartInverse_comp_map_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) (hπ : IsUnit π) :
    (iteratedCentralChartInverseMapOfIsUnit R π k m hπ).comp
        (iteratedCentralChartMap R π k m) =
      AlgHom.id R (Ring R π (centralChartThickness k m)) := by
  apply algHom_ext π (centralChartThickness k m)
  · simp only [AlgHom.coe_comp, Function.comp_apply, iteratedCentralChartMap_x, map_mul,
      AlgHom.commutes, iteratedCentralChartInverseMapOfIsUnit_x, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul,
      unit_parameter_pow_mul_inv_pow R π hπ m, map_one, one_mul]
  · simp only [AlgHom.coe_comp, Function.comp_apply, iteratedCentralChartMap_y, map_mul,
      AlgHom.commutes, iteratedCentralChartInverseMapOfIsUnit_y, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul,
      unit_parameter_pow_mul_inv_pow R π hπ m, map_one, one_mul]

/-- Every iterated central-chart substitution is an algebra equivalence wherever `π` is a
unit. -/
def iteratedCentralChartEquivOfIsUnit
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) (hπ : IsUnit π) :
    Ring R π (centralChartThickness k m) ≃ₐ[R] Ring R π k :=
  AlgEquiv.ofAlgHom (iteratedCentralChartMap R π k m)
    (iteratedCentralChartInverseMapOfIsUnit R π k m hπ)
    (iteratedCentralChartMap_comp_inverse_of_isUnit R π k m hπ)
    (iteratedCentralChartInverse_comp_map_of_isUnit R π k m hπ)

/-- Taking `n / 2` central reductions leaves the parity thickness `n % 2`. -/
theorem centralChartThickness_mod_div (n : ℕ) :
    centralChartThickness (n % 2) (n / 2) = n := by
  rw [centralChartThickness_eq]
  omega

/-- The parity thickness reached by the central reduction process is at most one. -/
theorem centralChartTerminal_le_one (n : ℕ) : n % 2 ≤ 1 := by
  omega

/-! ## Descending thickness and termination -/

/-- Thickness after `i` successive central reductions from initial thickness `n`. -/
def centralReductionThickness (n i : ℕ) : ℕ := n - 2 * i

@[simp] theorem centralReductionThickness_zero (n : ℕ) :
    centralReductionThickness n 0 = n := by
  simp [centralReductionThickness]

/-- Every preterminal central reduction lowers thickness by exactly two. -/
theorem centralReductionThickness_succ (n i : ℕ) (hi : i < n / 2) :
    centralReductionThickness n (i + 1) + 2 = centralReductionThickness n i := by
  simp only [centralReductionThickness]
  omega

/-- Every stage before the terminal one still has thickness at least two. -/
theorem two_le_centralReductionThickness (n i : ℕ) (hi : i < n / 2) :
    2 ≤ centralReductionThickness n i := by
  simp only [centralReductionThickness]
  omega

/-- Thickness strictly decreases at every stage before termination. -/
theorem centralReductionThickness_strictAnti (n i : ℕ) (hi : i < n / 2) :
    centralReductionThickness n (i + 1) < centralReductionThickness n i := by
  have h := centralReductionThickness_succ n i hi
  omega

/-- The descending process agrees with the reverse indexing used by the iterated chart map. -/
theorem centralReductionThickness_eq_reverse (n i : ℕ) (hi : i ≤ n / 2) :
    centralReductionThickness n i =
      centralChartThickness (n % 2) (n / 2 - i) := by
  rw [centralReductionThickness, centralChartThickness_eq]
  omega

/-- After exactly `n / 2` reductions, the remaining thickness is the parity of `n`. -/
theorem centralReductionThickness_terminal (n : ℕ) :
    centralReductionThickness n (n / 2) = n % 2 := by
  rw [centralReductionThickness]
  omega

/-- Successive central reductions terminate after `n / 2` steps at thickness at most one. -/
theorem centralReduction_terminates (n : ℕ) :
    centralReductionThickness n (n / 2) ≤ 1 := by
  rw [centralReductionThickness_terminal]
  omega

/-! ## The exact parity-reduction map -/

/-- The central reduction written directly with source thickness `n` and target thickness
`n % 2`. -/
def parityReductionMap (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ring R π n →ₐ[R] Ring R π (n % 2) :=
  lift π n
    (algebraMap R (Ring R π (n % 2)) (π ^ (n / 2)) * x R π (n % 2))
    (algebraMap R (Ring R π (n % 2)) (π ^ (n / 2)) * y R π (n % 2)) (by
      rw [mul_mul_mul_comm, x_mul_y, ← map_mul, ← map_mul]
      congr 1
      rw [← pow_add, ← pow_add]
      congr 1
      omega)

/-- The exact parity-reduction map scales `x` by `π^(n/2)`. -/
@[simp] theorem parityReductionMap_x
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    parityReductionMap R π n (x R π n) =
      algebraMap R (Ring R π (n % 2)) (π ^ (n / 2)) * x R π (n % 2) := by
  apply lift_x

/-- The exact parity-reduction map scales `y` by `π^(n/2)`. -/
@[simp] theorem parityReductionMap_y
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    parityReductionMap R π n (y R π n) =
      algebraMap R (Ring R π (n % 2)) (π ^ (n / 2)) * y R π (n % 2) := by
  apply lift_y

/-- For thickness at least two, the exact map to the terminal parity chart principalizes the
original origin ideal by `π`. -/
theorem parityReductionMap_originIdeal
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hn : 2 ≤ n) :
    (totalSpaceOriginIdeal R π n).map (parityReductionMap R π n).toRingHom =
      Ideal.span {algebraMap R (Ring R π (n % 2)) π} := by
  rw [totalSpaceOriginIdeal, Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z ⟨w, (rfl | rfl | rfl), rfl⟩
    · change parityReductionMap R π n (x R π n) ∈ _
      rw [parityReductionMap_x, map_pow]
      exact (Ideal.span {algebraMap R (Ring R π (n % 2)) π}).mul_mem_right _
        ((Ideal.span {algebraMap R (Ring R π (n % 2)) π}).pow_mem_of_mem
          (Ideal.subset_span (Set.mem_singleton _)) (n / 2) (by omega))
    · change parityReductionMap R π n (y R π n) ∈ _
      rw [parityReductionMap_y, map_pow]
      exact (Ideal.span {algebraMap R (Ring R π (n % 2)) π}).mul_mem_right _
        ((Ideal.span {algebraMap R (Ring R π (n % 2)) π}).pow_mem_of_mem
          (Ideal.subset_span (Set.mem_singleton _)) (n / 2) (by omega))
    · change parityReductionMap R π n (algebraMap R (Ring R π n) π) ∈ _
      rw [(parityReductionMap R π n).commutes]
      exact Ideal.subset_span (Set.mem_singleton _)
  · rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    apply Ideal.subset_span
    refine ⟨algebraMap R (Ring R π n) π, ?_, ?_⟩
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact (parityReductionMap R π n).commutes π

/-- Inverse of the exact parity reduction when `π` is a unit. -/
def parityReductionInverseMapOfIsUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    Ring R π (n % 2) →ₐ[R] Ring R π n :=
  lift π (n % 2)
    (algebraMap R (Ring R π n) ((↑hπ.unit⁻¹ : R) ^ (n / 2)) * x R π n)
    (algebraMap R (Ring R π n) ((↑hπ.unit⁻¹ : R) ^ (n / 2)) * y R π n) (by
      rw [mul_mul_mul_comm, x_mul_y, ← map_mul, ← map_mul]
      congr 1
      rw [← pow_add, show n / 2 + n / 2 = 2 * (n / 2) by omega]
      have hparameter : π ^ n = π ^ (n % 2) * π ^ (2 * (n / 2)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hparameter]
      calc
        (↑hπ.unit⁻¹ : R) ^ (2 * (n / 2)) * (π ^ (n % 2) * π ^ (2 * (n / 2))) =
            π ^ (n % 2) *
              ((↑hπ.unit⁻¹ : R) ^ (2 * (n / 2)) * π ^ (2 * (n / 2))) := by ring
        _ = π ^ (n % 2) := by
          rw [unit_inv_pow_mul_parameter_pow R π hπ (2 * (n / 2)), mul_one])

@[simp] theorem parityReductionInverseMapOfIsUnit_x
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    parityReductionInverseMapOfIsUnit R π n hπ (x R π (n % 2)) =
      algebraMap R (Ring R π n) ((↑hπ.unit⁻¹ : R) ^ (n / 2)) * x R π n := by
  apply lift_x

@[simp] theorem parityReductionInverseMapOfIsUnit_y
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    parityReductionInverseMapOfIsUnit R π n hπ (y R π (n % 2)) =
      algebraMap R (Ring R π n) ((↑hπ.unit⁻¹ : R) ^ (n / 2)) * y R π n := by
  apply lift_y

theorem parityReductionMap_comp_inverse_of_isUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    (parityReductionMap R π n).comp (parityReductionInverseMapOfIsUnit R π n hπ) =
      AlgHom.id R (Ring R π (n % 2)) := by
  apply algHom_ext π (n % 2)
  · simp only [AlgHom.coe_comp, Function.comp_apply, parityReductionInverseMapOfIsUnit_x,
      map_mul, AlgHom.commutes, parityReductionMap_x, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul,
      unit_inv_pow_mul_parameter_pow R π hπ (n / 2), map_one, one_mul]
  · simp only [AlgHom.coe_comp, Function.comp_apply, parityReductionInverseMapOfIsUnit_y,
      map_mul, AlgHom.commutes, parityReductionMap_y, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul,
      unit_inv_pow_mul_parameter_pow R π hπ (n / 2), map_one, one_mul]

theorem parityReductionInverse_comp_map_of_isUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    (parityReductionInverseMapOfIsUnit R π n hπ).comp (parityReductionMap R π n) =
      AlgHom.id R (Ring R π n) := by
  apply algHom_ext π n
  · simp only [AlgHom.coe_comp, Function.comp_apply, parityReductionMap_x, map_mul,
      AlgHom.commutes, parityReductionInverseMapOfIsUnit_x, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul,
      unit_parameter_pow_mul_inv_pow R π hπ (n / 2), map_one, one_mul]
  · simp only [AlgHom.coe_comp, Function.comp_apply, parityReductionMap_y, map_mul,
      AlgHom.commutes, parityReductionInverseMapOfIsUnit_y, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul,
      unit_parameter_pow_mul_inv_pow R π hπ (n / 2), map_one, one_mul]

/-- The exact parity reduction is an algebra equivalence wherever `π` is a unit. -/
def parityReductionEquivOfIsUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    Ring R π n ≃ₐ[R] Ring R π (n % 2) :=
  AlgEquiv.ofAlgHom (parityReductionMap R π n)
    (parityReductionInverseMapOfIsUnit R π n hπ)
    (parityReductionMap_comp_inverse_of_isUnit R π n hπ)
    (parityReductionInverse_comp_map_of_isUnit R π n hπ)

/-- The coordinate-ring map of the exact parity reduction is an isomorphism when `π` is
invertible. -/
theorem parityReductionRingMap_isIso_of_isUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    IsIso (CommRingCat.ofHom (parityReductionMap R π n).toRingHom) := by
  change IsIso
    (parityReductionEquivOfIsUnit R π n hπ).toRingEquiv.toCommRingCatIso.hom
  infer_instance

/-- The coordinate-ring map of every iterated central chart is an isomorphism when `π` is
invertible. -/
theorem iteratedCentralChartRingMap_isIso_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) (hπ : IsUnit π) :
    IsIso (CommRingCat.ofHom (iteratedCentralChartMap R π k m).toRingHom) := by
  change IsIso
    (iteratedCentralChartEquivOfIsUnit R π k m hπ).toRingEquiv.toCommRingCatIso.hom
  infer_instance

/-- The affine-scheme morphism obtained by composing `m` central-chart substitutions. -/
def iteratedCentralChartSpec
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) :
    Spec (.of (Ring R π k)) ⟶ Spec (.of (Ring R π (centralChartThickness k m))) :=
  Spec.map (CommRingCat.ofHom (iteratedCentralChartMap R π k m).toRingHom)

/-- The exact parity-reduction morphism from the terminal thickness-`n % 2` chart to the
original thickness-`n` node. -/
def parityReductionSpec (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Spec (.of (Ring R π (n % 2))) ⟶ Spec (.of (Ring R π n)) :=
  Spec.map (CommRingCat.ofHom (parityReductionMap R π n).toRingHom)

/-- The exact parity-reduction scheme morphism is an isomorphism away from the closed
fibre. -/
theorem parityReductionSpec_isIso_of_isUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    IsIso (parityReductionSpec R π n) := by
  let _ : IsIso (CommRingCat.ofHom (parityReductionMap R π n).toRingHom) :=
    parityReductionRingMap_isIso_of_isUnit R π n hπ
  rw [parityReductionSpec]
  infer_instance

/-- The exact parity-reduction morphism is over `Spec R`. -/
@[reassoc (attr := simp)] theorem parityReductionSpec_toBaseSpec
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    parityReductionSpec R π n ≫ toBaseSpec R π n = toBaseSpec R π (n % 2) := by
  rw [parityReductionSpec, toBaseSpec, toBaseSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  exact RingHom.ext fun r => (parityReductionMap R π n).commutes r

/-- Every iterated central-chart scheme morphism is an isomorphism away from the closed
fibre. -/
theorem iteratedCentralChartSpec_isIso_of_isUnit
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) (hπ : IsUnit π) :
    IsIso (iteratedCentralChartSpec R π k m) := by
  let _ : IsIso (CommRingCat.ofHom (iteratedCentralChartMap R π k m).toRingHom) :=
    iteratedCentralChartRingMap_isIso_of_isUnit R π k m hπ
  rw [iteratedCentralChartSpec]
  infer_instance

/-- Every iterated central-chart morphism is over `Spec R`. -/
@[reassoc (attr := simp)] theorem iteratedCentralChartSpec_toBaseSpec
    (R : Type u) [CommRing R] (π : R) (k m : ℕ) :
    iteratedCentralChartSpec R π k m ≫ toBaseSpec R π (centralChartThickness k m) =
      toBaseSpec R π k := by
  rw [iteratedCentralChartSpec, toBaseSpec, toBaseSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  exact RingHom.ext fun r => (iteratedCentralChartMap R π k m).commutes r

/-! ## Compatibility with coefficient base change -/

section BaseChange

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Tensoring the central-chart map with a coefficient algebra. -/
def centralChartBaseChangeMap (π : R) (k : ℕ) :
    Ring R π (k + 2) ⊗[R] S →ₐ[R] Ring R π k ⊗[R] S :=
  Algebra.TensorProduct.map (centralChartMap R π k) (AlgHom.id R S)

/-- Tensoring an iterated central-chart map with a coefficient algebra. -/
def iteratedCentralChartBaseChangeMap (π : R) (k m : ℕ) :
    Ring R π (centralChartThickness k m) ⊗[R] S →ₐ[R] Ring R π k ⊗[R] S :=
  Algebra.TensorProduct.map (iteratedCentralChartMap R π k m) (AlgHom.id R S)

/-- Tensoring the exact parity-reduction map with a coefficient algebra. -/
def parityReductionBaseChangeMap (π : R) (n : ℕ) :
    Ring R π n ⊗[R] S →ₐ[R] Ring R π (n % 2) ⊗[R] S :=
  Algebra.TensorProduct.map (parityReductionMap R π n) (AlgHom.id R S)

/-- Tensoring the `x`-side chart map with a coefficient algebra. -/
def xSideChartBaseChangeMap (π : R) (k : ℕ) :
    Ring R π (k + 2) ⊗[R] S →ₐ[R] Ring R π 1 ⊗[R] S :=
  Algebra.TensorProduct.map (xSideChartMap R π k) (AlgHom.id R S)

/-- Tensoring the `y`-side chart map with a coefficient algebra. -/
def ySideChartBaseChangeMap (π : R) (k : ℕ) :
    Ring R π (k + 2) ⊗[R] S →ₐ[R] Ring R π 1 ⊗[R] S :=
  Algebra.TensorProduct.map (ySideChartMap R π k) (AlgHom.id R S)

/-- Under the canonical node-algebra base-change equivalences, tensoring the central chart is
the central chart formed after arbitrary coefficient base change. -/
theorem centralChartMap_baseChange (π : R) (k : ℕ) :
    ((baseChangeEquiv R S π k).toAlgHom.restrictScalars R).comp
        (centralChartBaseChangeMap R S π k) =
      ((centralChartMap S (algebraMap R S π) k).restrictScalars R).comp
        ((baseChangeEquiv R S π (k + 2)).toAlgHom.restrictScalars R) := by
  ext z
  · let f : Ring R π (k + 2) →ₐ[R] Ring S (algebraMap R S π) k :=
      ((baseChangeEquiv R S π k).toAlgHom.restrictScalars R).comp
        (Algebra.TensorProduct.includeLeft.comp (centralChartMap R π k))
    let g : Ring R π (k + 2) →ₐ[R] Ring S (algebraMap R S π) k :=
      ((centralChartMap S (algebraMap R S π) k).restrictScalars R).comp
        (((baseChangeEquiv R S π (k + 2)).toAlgHom.restrictScalars R).comp
          Algebra.TensorProduct.includeLeft)
    have hfg : f = g := by
      apply algHom_ext π (k + 2)
      · dsimp [f, g]
        rw [centralChartMap_x]
        have hscalar : baseChangeEquiv R S π k
            (algebraMap R (Ring R π k) π ⊗ₜ[R] (1 : S)) =
            algebraMap S (Ring S (algebraMap R S π) k) (algebraMap R S π) := by
          rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
          exact (baseChangeEquiv R S π k).commutes (algebraMap R S π)
        rw [show (algebraMap R (Ring R π k) π * x R π k) ⊗ₜ[R] (1 : S) =
            (algebraMap R (Ring R π k) π ⊗ₜ[R] (1 : S)) *
              (x R π k ⊗ₜ[R] (1 : S)) by rw [Algebra.TensorProduct.tmul_mul_tmul]; simp,
          map_mul, hscalar, baseChangeEquiv_tmul_x]
        rw [baseChangeEquiv_tmul_x, centralChartMap_x]
      · dsimp [f, g]
        rw [centralChartMap_y]
        have hscalar : baseChangeEquiv R S π k
            (algebraMap R (Ring R π k) π ⊗ₜ[R] (1 : S)) =
            algebraMap S (Ring S (algebraMap R S π) k) (algebraMap R S π) := by
          rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
          exact (baseChangeEquiv R S π k).commutes (algebraMap R S π)
        rw [show (algebraMap R (Ring R π k) π * y R π k) ⊗ₜ[R] (1 : S) =
            (algebraMap R (Ring R π k) π ⊗ₜ[R] (1 : S)) *
              (y R π k ⊗ₜ[R] (1 : S)) by rw [Algebra.TensorProduct.tmul_mul_tmul]; simp,
          map_mul, hscalar, baseChangeEquiv_tmul_y]
        rw [baseChangeEquiv_tmul_y, centralChartMap_y]
    simpa [f, g, centralChartBaseChangeMap] using congrArg (fun h => h z) hfg
  · have hbc : centralChartBaseChangeMap R S π k
        (Algebra.TensorProduct.includeRight z) =
          (Algebra.TensorProduct.includeRight z : Ring R π k ⊗[R] S) := by
      simp [centralChartBaseChangeMap]
    have hbaseSmall : ((baseChangeEquiv R S π k).toAlgHom.restrictScalars R)
        (Algebra.TensorProduct.includeRight z) =
          algebraMap S (Ring S (algebraMap R S π) k) z := by
      exact (baseChangeEquiv R S π k).commutes z
    have hbaseBig : ((baseChangeEquiv R S π (k + 2)).toAlgHom.restrictScalars R)
        (Algebra.TensorProduct.includeRight z) =
          algebraMap S (Ring S (algebraMap R S π) (k + 2)) z := by
      exact (baseChangeEquiv R S π (k + 2)).commutes z
    have hchart : ((centralChartMap S (algebraMap R S π) k).restrictScalars R)
        (algebraMap S (Ring S (algebraMap R S π) (k + 2)) z) =
          algebraMap S (Ring S (algebraMap R S π) k) z := by
      exact (centralChartMap S (algebraMap R S π) k).commutes z
    change ((baseChangeEquiv R S π k).toAlgHom.restrictScalars R)
        (centralChartBaseChangeMap R S π k (Algebra.TensorProduct.includeRight z)) =
      ((centralChartMap S (algebraMap R S π) k).restrictScalars R)
        (((baseChangeEquiv R S π (k + 2)).toAlgHom.restrictScalars R)
          (Algebra.TensorProduct.includeRight z))
    rw [hbc, hbaseSmall, hbaseBig, hchart]

/-- Under the canonical node-algebra base-change equivalences, tensoring an arbitrary
iterated central chart is the corresponding iteration after coefficient base change. -/
theorem iteratedCentralChartMap_baseChange (π : R) (k m : ℕ) :
    ((baseChangeEquiv R S π k).toAlgHom.restrictScalars R).comp
        (iteratedCentralChartBaseChangeMap R S π k m) =
      ((iteratedCentralChartMap S (algebraMap R S π) k m).restrictScalars R).comp
        ((baseChangeEquiv R S π (centralChartThickness k m)).toAlgHom.restrictScalars R) := by
  ext z
  · let f : Ring R π (centralChartThickness k m) →ₐ[R]
        Ring S (algebraMap R S π) k :=
      ((baseChangeEquiv R S π k).toAlgHom.restrictScalars R).comp
        (Algebra.TensorProduct.includeLeft.comp (iteratedCentralChartMap R π k m))
    let g : Ring R π (centralChartThickness k m) →ₐ[R]
        Ring S (algebraMap R S π) k :=
      ((iteratedCentralChartMap S (algebraMap R S π) k m).restrictScalars R).comp
        (((baseChangeEquiv R S π (centralChartThickness k m)).toAlgHom.restrictScalars R).comp
          Algebra.TensorProduct.includeLeft)
    have hfg : f = g := by
      apply algHom_ext π (centralChartThickness k m)
      · dsimp [f, g]
        rw [iteratedCentralChartMap_x]
        have hscalar : baseChangeEquiv R S π k
            (algebraMap R (Ring R π k) (π ^ m) ⊗ₜ[R] (1 : S)) =
            algebraMap S (Ring S (algebraMap R S π) k)
              ((algebraMap R S π) ^ m) := by
          rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
          rw [map_pow]
          exact (baseChangeEquiv R S π k).commutes ((algebraMap R S π) ^ m)
        rw [show (algebraMap R (Ring R π k) (π ^ m) * x R π k) ⊗ₜ[R] (1 : S) =
            (algebraMap R (Ring R π k) (π ^ m) ⊗ₜ[R] (1 : S)) *
              (x R π k ⊗ₜ[R] (1 : S)) by
                rw [Algebra.TensorProduct.tmul_mul_tmul]; simp,
          map_mul, hscalar, baseChangeEquiv_tmul_x]
        rw [baseChangeEquiv_tmul_x, iteratedCentralChartMap_x]
      · dsimp [f, g]
        rw [iteratedCentralChartMap_y]
        have hscalar : baseChangeEquiv R S π k
            (algebraMap R (Ring R π k) (π ^ m) ⊗ₜ[R] (1 : S)) =
            algebraMap S (Ring S (algebraMap R S π) k)
              ((algebraMap R S π) ^ m) := by
          rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
          rw [map_pow]
          exact (baseChangeEquiv R S π k).commutes ((algebraMap R S π) ^ m)
        rw [show (algebraMap R (Ring R π k) (π ^ m) * y R π k) ⊗ₜ[R] (1 : S) =
            (algebraMap R (Ring R π k) (π ^ m) ⊗ₜ[R] (1 : S)) *
              (y R π k ⊗ₜ[R] (1 : S)) by
                rw [Algebra.TensorProduct.tmul_mul_tmul]; simp,
          map_mul, hscalar, baseChangeEquiv_tmul_y]
        rw [baseChangeEquiv_tmul_y, iteratedCentralChartMap_y]
    simpa [f, g, iteratedCentralChartBaseChangeMap] using congrArg (fun h => h z) hfg
  · have hbc : iteratedCentralChartBaseChangeMap R S π k m
        (Algebra.TensorProduct.includeRight z) =
          (Algebra.TensorProduct.includeRight z : Ring R π k ⊗[R] S) := by
      simp [iteratedCentralChartBaseChangeMap]
    have hbaseSmall : ((baseChangeEquiv R S π k).toAlgHom.restrictScalars R)
        (Algebra.TensorProduct.includeRight z) =
          algebraMap S (Ring S (algebraMap R S π) k) z := by
      exact (baseChangeEquiv R S π k).commutes z
    have hbaseBig :
        ((baseChangeEquiv R S π (centralChartThickness k m)).toAlgHom.restrictScalars R)
          (Algebra.TensorProduct.includeRight z) =
            algebraMap S (Ring S (algebraMap R S π) (centralChartThickness k m)) z := by
      exact (baseChangeEquiv R S π (centralChartThickness k m)).commutes z
    have hchart : ((iteratedCentralChartMap S (algebraMap R S π) k m).restrictScalars R)
        (algebraMap S (Ring S (algebraMap R S π) (centralChartThickness k m)) z) =
          algebraMap S (Ring S (algebraMap R S π) k) z := by
      exact (iteratedCentralChartMap S (algebraMap R S π) k m).commutes z
    change ((baseChangeEquiv R S π k).toAlgHom.restrictScalars R)
        (iteratedCentralChartBaseChangeMap R S π k m
          (Algebra.TensorProduct.includeRight z)) =
      ((iteratedCentralChartMap S (algebraMap R S π) k m).restrictScalars R)
        (((baseChangeEquiv R S π (centralChartThickness k m)).toAlgHom.restrictScalars R)
          (Algebra.TensorProduct.includeRight z))
    rw [hbc, hbaseSmall, hbaseBig, hchart]

/-- The exact thickness-`n` to thickness-`n % 2` reduction commutes with arbitrary
coefficient base change. -/
theorem parityReductionMap_baseChange (π : R) (n : ℕ) :
    ((baseChangeEquiv R S π (n % 2)).toAlgHom.restrictScalars R).comp
        (parityReductionBaseChangeMap R S π n) =
      ((parityReductionMap S (algebraMap R S π) n).restrictScalars R).comp
        ((baseChangeEquiv R S π n).toAlgHom.restrictScalars R) := by
  ext z
  · let f : Ring R π n →ₐ[R] Ring S (algebraMap R S π) (n % 2) :=
      ((baseChangeEquiv R S π (n % 2)).toAlgHom.restrictScalars R).comp
        (Algebra.TensorProduct.includeLeft.comp (parityReductionMap R π n))
    let g : Ring R π n →ₐ[R] Ring S (algebraMap R S π) (n % 2) :=
      ((parityReductionMap S (algebraMap R S π) n).restrictScalars R).comp
        (((baseChangeEquiv R S π n).toAlgHom.restrictScalars R).comp
          Algebra.TensorProduct.includeLeft)
    have hfg : f = g := by
      apply algHom_ext π n
      · dsimp [f, g]
        rw [parityReductionMap_x]
        have hscalar : baseChangeEquiv R S π (n % 2)
            (algebraMap R (Ring R π (n % 2)) (π ^ (n / 2)) ⊗ₜ[R] (1 : S)) =
            algebraMap S (Ring S (algebraMap R S π) (n % 2))
              ((algebraMap R S π) ^ (n / 2)) := by
          rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
          rw [map_pow]
          exact (baseChangeEquiv R S π (n % 2)).commutes
            ((algebraMap R S π) ^ (n / 2))
        rw [show (algebraMap R (Ring R π (n % 2)) (π ^ (n / 2)) *
              x R π (n % 2)) ⊗ₜ[R] (1 : S) =
            (algebraMap R (Ring R π (n % 2)) (π ^ (n / 2)) ⊗ₜ[R] (1 : S)) *
              (x R π (n % 2) ⊗ₜ[R] (1 : S)) by
                rw [Algebra.TensorProduct.tmul_mul_tmul]; simp,
          map_mul, hscalar, baseChangeEquiv_tmul_x]
        rw [baseChangeEquiv_tmul_x, parityReductionMap_x]
      · dsimp [f, g]
        rw [parityReductionMap_y]
        have hscalar : baseChangeEquiv R S π (n % 2)
            (algebraMap R (Ring R π (n % 2)) (π ^ (n / 2)) ⊗ₜ[R] (1 : S)) =
            algebraMap S (Ring S (algebraMap R S π) (n % 2))
              ((algebraMap R S π) ^ (n / 2)) := by
          rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
          rw [map_pow]
          exact (baseChangeEquiv R S π (n % 2)).commutes
            ((algebraMap R S π) ^ (n / 2))
        rw [show (algebraMap R (Ring R π (n % 2)) (π ^ (n / 2)) *
              y R π (n % 2)) ⊗ₜ[R] (1 : S) =
            (algebraMap R (Ring R π (n % 2)) (π ^ (n / 2)) ⊗ₜ[R] (1 : S)) *
              (y R π (n % 2) ⊗ₜ[R] (1 : S)) by
                rw [Algebra.TensorProduct.tmul_mul_tmul]; simp,
          map_mul, hscalar, baseChangeEquiv_tmul_y]
        rw [baseChangeEquiv_tmul_y, parityReductionMap_y]
    simpa [f, g, parityReductionBaseChangeMap] using congrArg (fun h => h z) hfg
  · have hbc : parityReductionBaseChangeMap R S π n
        (Algebra.TensorProduct.includeRight z) =
          (Algebra.TensorProduct.includeRight z : Ring R π (n % 2) ⊗[R] S) := by
      simp [parityReductionBaseChangeMap]
    have hbaseSmall :
        ((baseChangeEquiv R S π (n % 2)).toAlgHom.restrictScalars R)
          (Algebra.TensorProduct.includeRight z) =
            algebraMap S (Ring S (algebraMap R S π) (n % 2)) z := by
      exact (baseChangeEquiv R S π (n % 2)).commutes z
    have hbaseBig : ((baseChangeEquiv R S π n).toAlgHom.restrictScalars R)
        (Algebra.TensorProduct.includeRight z) =
          algebraMap S (Ring S (algebraMap R S π) n) z := by
      exact (baseChangeEquiv R S π n).commutes z
    have hchart : ((parityReductionMap S (algebraMap R S π) n).restrictScalars R)
        (algebraMap S (Ring S (algebraMap R S π) n) z) =
          algebraMap S (Ring S (algebraMap R S π) (n % 2)) z := by
      exact (parityReductionMap S (algebraMap R S π) n).commutes z
    change ((baseChangeEquiv R S π (n % 2)).toAlgHom.restrictScalars R)
        (parityReductionBaseChangeMap R S π n (Algebra.TensorProduct.includeRight z)) =
      ((parityReductionMap S (algebraMap R S π) n).restrictScalars R)
        (((baseChangeEquiv R S π n).toAlgHom.restrictScalars R)
          (Algebra.TensorProduct.includeRight z))
    rw [hbc, hbaseSmall, hbaseBig, hchart]

/-- Under the canonical node-algebra base-change equivalences, tensoring the `x`-side chart
is the `x`-side chart formed after arbitrary coefficient base change. -/
theorem xSideChartMap_baseChange (π : R) (k : ℕ) :
    ((baseChangeEquiv R S π 1).toAlgHom.restrictScalars R).comp
        (xSideChartBaseChangeMap R S π k) =
      ((xSideChartMap S (algebraMap R S π) k).restrictScalars R).comp
        ((baseChangeEquiv R S π (k + 2)).toAlgHom.restrictScalars R) := by
  ext z
  · let f : Ring R π (k + 2) →ₐ[R] Ring S (algebraMap R S π) 1 :=
      ((baseChangeEquiv R S π 1).toAlgHom.restrictScalars R).comp
        (Algebra.TensorProduct.includeLeft.comp (xSideChartMap R π k))
    let g : Ring R π (k + 2) →ₐ[R] Ring S (algebraMap R S π) 1 :=
      ((xSideChartMap S (algebraMap R S π) k).restrictScalars R).comp
        (((baseChangeEquiv R S π (k + 2)).toAlgHom.restrictScalars R).comp
          Algebra.TensorProduct.includeLeft)
    have hfg : f = g := by
      apply algHom_ext π (k + 2)
      · dsimp [f, g]
        rw [xSideChartMap_x, baseChangeEquiv_tmul_x, baseChangeEquiv_tmul_x,
          xSideChartMap_x]
      · dsimp [f, g]
        rw [xSideChartMap_y]
        have hscalar : baseChangeEquiv R S π 1
            (algebraMap R (Ring R π 1) (π ^ (k + 1)) ⊗ₜ[R] (1 : S)) =
            algebraMap S (Ring S (algebraMap R S π) 1)
              ((algebraMap R S π) ^ (k + 1)) := by
          rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
          rw [map_pow]
          exact (baseChangeEquiv R S π 1).commutes
            ((algebraMap R S π) ^ (k + 1))
        rw [show (algebraMap R (Ring R π 1) (π ^ (k + 1)) * y R π 1) ⊗ₜ[R]
              (1 : S) =
            (algebraMap R (Ring R π 1) (π ^ (k + 1)) ⊗ₜ[R] (1 : S)) *
              (y R π 1 ⊗ₜ[R] (1 : S)) by
                rw [Algebra.TensorProduct.tmul_mul_tmul]; simp,
          map_mul, hscalar, baseChangeEquiv_tmul_y]
        rw [baseChangeEquiv_tmul_y, xSideChartMap_y]
    simpa [f, g, xSideChartBaseChangeMap] using congrArg (fun h => h z) hfg
  · have hbc : xSideChartBaseChangeMap R S π k
        (Algebra.TensorProduct.includeRight z) =
          (Algebra.TensorProduct.includeRight z : Ring R π 1 ⊗[R] S) := by
      simp [xSideChartBaseChangeMap]
    have hbaseSmall : ((baseChangeEquiv R S π 1).toAlgHom.restrictScalars R)
        (Algebra.TensorProduct.includeRight z) =
          algebraMap S (Ring S (algebraMap R S π) 1) z := by
      exact (baseChangeEquiv R S π 1).commutes z
    have hbaseBig : ((baseChangeEquiv R S π (k + 2)).toAlgHom.restrictScalars R)
        (Algebra.TensorProduct.includeRight z) =
          algebraMap S (Ring S (algebraMap R S π) (k + 2)) z := by
      exact (baseChangeEquiv R S π (k + 2)).commutes z
    have hchart : ((xSideChartMap S (algebraMap R S π) k).restrictScalars R)
        (algebraMap S (Ring S (algebraMap R S π) (k + 2)) z) =
          algebraMap S (Ring S (algebraMap R S π) 1) z := by
      exact (xSideChartMap S (algebraMap R S π) k).commutes z
    change ((baseChangeEquiv R S π 1).toAlgHom.restrictScalars R)
        (xSideChartBaseChangeMap R S π k (Algebra.TensorProduct.includeRight z)) =
      ((xSideChartMap S (algebraMap R S π) k).restrictScalars R)
        (((baseChangeEquiv R S π (k + 2)).toAlgHom.restrictScalars R)
          (Algebra.TensorProduct.includeRight z))
    rw [hbc, hbaseSmall, hbaseBig, hchart]

/-- Under the canonical node-algebra base-change equivalences, tensoring the `y`-side chart
is the `y`-side chart formed after arbitrary coefficient base change. -/
theorem ySideChartMap_baseChange (π : R) (k : ℕ) :
    ((baseChangeEquiv R S π 1).toAlgHom.restrictScalars R).comp
        (ySideChartBaseChangeMap R S π k) =
      ((ySideChartMap S (algebraMap R S π) k).restrictScalars R).comp
        ((baseChangeEquiv R S π (k + 2)).toAlgHom.restrictScalars R) := by
  ext z
  · let f : Ring R π (k + 2) →ₐ[R] Ring S (algebraMap R S π) 1 :=
      ((baseChangeEquiv R S π 1).toAlgHom.restrictScalars R).comp
        (Algebra.TensorProduct.includeLeft.comp (ySideChartMap R π k))
    let g : Ring R π (k + 2) →ₐ[R] Ring S (algebraMap R S π) 1 :=
      ((ySideChartMap S (algebraMap R S π) k).restrictScalars R).comp
        (((baseChangeEquiv R S π (k + 2)).toAlgHom.restrictScalars R).comp
          Algebra.TensorProduct.includeLeft)
    have hfg : f = g := by
      apply algHom_ext π (k + 2)
      · dsimp [f, g]
        rw [ySideChartMap_x]
        have hscalar : baseChangeEquiv R S π 1
            (algebraMap R (Ring R π 1) (π ^ (k + 1)) ⊗ₜ[R] (1 : S)) =
            algebraMap S (Ring S (algebraMap R S π) 1)
              ((algebraMap R S π) ^ (k + 1)) := by
          rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
          rw [map_pow]
          exact (baseChangeEquiv R S π 1).commutes
            ((algebraMap R S π) ^ (k + 1))
        rw [show (algebraMap R (Ring R π 1) (π ^ (k + 1)) * x R π 1) ⊗ₜ[R]
              (1 : S) =
            (algebraMap R (Ring R π 1) (π ^ (k + 1)) ⊗ₜ[R] (1 : S)) *
              (x R π 1 ⊗ₜ[R] (1 : S)) by
                rw [Algebra.TensorProduct.tmul_mul_tmul]; simp,
          map_mul, hscalar, baseChangeEquiv_tmul_x]
        rw [baseChangeEquiv_tmul_x, ySideChartMap_x]
      · dsimp [f, g]
        rw [ySideChartMap_y, baseChangeEquiv_tmul_y, baseChangeEquiv_tmul_y,
          ySideChartMap_y]
    simpa [f, g, ySideChartBaseChangeMap] using congrArg (fun h => h z) hfg
  · have hbc : ySideChartBaseChangeMap R S π k
        (Algebra.TensorProduct.includeRight z) =
          (Algebra.TensorProduct.includeRight z : Ring R π 1 ⊗[R] S) := by
      simp [ySideChartBaseChangeMap]
    have hbaseSmall : ((baseChangeEquiv R S π 1).toAlgHom.restrictScalars R)
        (Algebra.TensorProduct.includeRight z) =
          algebraMap S (Ring S (algebraMap R S π) 1) z := by
      exact (baseChangeEquiv R S π 1).commutes z
    have hbaseBig : ((baseChangeEquiv R S π (k + 2)).toAlgHom.restrictScalars R)
        (Algebra.TensorProduct.includeRight z) =
          algebraMap S (Ring S (algebraMap R S π) (k + 2)) z := by
      exact (baseChangeEquiv R S π (k + 2)).commutes z
    have hchart : ((ySideChartMap S (algebraMap R S π) k).restrictScalars R)
        (algebraMap S (Ring S (algebraMap R S π) (k + 2)) z) =
          algebraMap S (Ring S (algebraMap R S π) 1) z := by
      exact (ySideChartMap S (algebraMap R S π) k).commutes z
    change ((baseChangeEquiv R S π 1).toAlgHom.restrictScalars R)
        (ySideChartBaseChangeMap R S π k (Algebra.TensorProduct.includeRight z)) =
      ((ySideChartMap S (algebraMap R S π) k).restrictScalars R)
        (((baseChangeEquiv R S π (k + 2)).toAlgHom.restrictScalars R)
          (Algebra.TensorProduct.includeRight z))
    rw [hbc, hbaseSmall, hbaseBig, hchart]

end BaseChange

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
