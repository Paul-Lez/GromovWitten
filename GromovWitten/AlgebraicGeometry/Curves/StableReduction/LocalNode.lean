/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib
import GromovWitten.Algebra.CompleteIntersection
import GromovWitten.Algebra.RegularLocalHypersurface
import GromovWitten.AlgebraicGeometry.FittingIdeals
import GromovWitten.AlgebraicGeometry.Morphisms.Syntomic
import GromovWitten.AlgebraicGeometry.Morphisms.Unramified

/-!
# The algebra of a local node smoothing

This file isolates the algebraic presentation `R[x,y]/(xy - π^n)`, its relative Jacobian locus,
its generic Laurent form, and the two closed affine-line branches of every positive special
fibre.  The Jacobian quotient is `R/(πⁿ)`; its map to `R` is unramified both in Mathlib's
affine ring-theoretic sense and through the scheme-morphism interface, and the corresponding
spectrum map is a closed immersion.  For an
irreducible parameter the equation lies in `(x,y,π)²` exactly at thickness at least two.  The
corresponding hypersurface local ring at the origin is regular exactly at positive thickness one,
and the full node ring over a DVR is regular exactly when `n ≤ 1`.  The
two coordinate principal opens are Laurent polynomial algebras; their smoothness implies that
the relative nonsmooth locus is contained in the computed Jacobian zero locus.  The branch
coordinate rings form a pushout and their spectra a pullback at the common origin.  The reverse
Jacobian-locus inclusion and blowup claims still require geometric infrastructure from later
roadmap layers; the shared nodal-family packaging is supplied in `LocalNodeNodal`.
-/

open CategoryTheory Limits
open AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u v

noncomputable section

open scoped MonomialOrder Pointwise Polynomial

namespace LocalNode

/-- The polynomial `xy - π^n` in two variables. -/
def equation (R : Type u) [CommRing R] (π : R) (n : ℕ) : MvPolynomial (Fin 2) R :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (π ^ n)

/-- The principal ideal cutting out the local node smoothing. -/
def relationIdeal (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span {equation R π n}

/-- The presented algebra `R[x,y]/(xy - π^n)`. -/
abbrev Ring (R : Type u) [CommRing R] (π : R) (n : ℕ) :=
  MvPolynomial (Fin 2) R ⧸ relationIdeal R π n

/-- The image of the first polynomial variable. -/
def x (R : Type u) [CommRing R] (π : R) (n : ℕ) : Ring R π n :=
  Ideal.Quotient.mk (relationIdeal R π n) (MvPolynomial.X 0)

/-- The image of the second polynomial variable. -/
def y (R : Type u) [CommRing R] (π : R) (n : ℕ) : Ring R π n :=
  Ideal.Quotient.mk (relationIdeal R π n) (MvPolynomial.X 1)

/-- The partial derivative of the node equation with respect to `x` is `y`. -/
@[simp] theorem pderiv_zero_equation (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    MvPolynomial.pderiv 0 (equation R π n) = MvPolynomial.X 1 := by
  simp [equation]

/-- The partial derivative of the node equation with respect to `y` is `x`. -/
@[simp] theorem pderiv_one_equation (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    MvPolynomial.pderiv 1 (equation R π n) = MvPolynomial.X 0 := by
  simp [equation]

/-- The node equation is nonzero over every nontrivial coefficient ring. -/
theorem equation_ne_zero (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    equation R π n ≠ 0 := by
  intro h
  have hp := congrArg (MvPolynomial.pderiv 0) h
  simp at hp

/-- The exponent of the leading monomial `xy` in the node equation. -/
def xyExponent : Fin 2 →₀ ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 1

lemma xyExponent_ne_zero : xyExponent ≠ 0 := by
  intro h
  have := DFunLike.congr_fun h (0 : Fin 2)
  simp [xyExponent] at this

/-- For any monomial order, the leading exponent of `xy - πⁿ` is `(1, 1)`. -/
theorem equation_degree (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ)
    (m : MonomialOrder (Fin 2)) :
    m.degree (equation R π n) = xyExponent := by
  classical
  have heq : MvPolynomial.X 0 * MvPolynomial.X 1 =
      MvPolynomial.monomial xyExponent (1 : R) := by
    simp [xyExponent, MvPolynomial.X, MvPolynomial.monomial_mul]
  rw [equation, heq, m.degree_sub_of_lt]
  · rw [m.degree_monomial, if_neg one_ne_zero]
  · rw [m.degree_C, m.degree_monomial, if_neg one_ne_zero]
    exact m.toSyn_strictMono (bot_lt_iff_ne_bot.mpr xyExponent_ne_zero)

/-- For any monomial order, the node equation has leading coefficient one. -/
theorem equation_leadingCoeff (R : Type u) [CommRing R] [Nontrivial R]
    (π : R) (n : ℕ) (m : MonomialOrder (Fin 2)) :
    m.leadingCoeff (equation R π n) = 1 := by
  classical
  have heq : MvPolynomial.X 0 * MvPolynomial.X 1 =
      MvPolynomial.monomial xyExponent (1 : R) := by
    simp [xyExponent, MvPolynomial.X, MvPolynomial.monomial_mul]
  have hlt : m.degree (MvPolynomial.C (π ^ n)) ≺[m]
      m.degree (MvPolynomial.monomial xyExponent (1 : R)) := by
    rw [m.degree_C, m.degree_monomial, if_neg one_ne_zero]
    exact m.toSyn_strictMono (bot_lt_iff_ne_bot.mpr xyExponent_ne_zero)
  rw [equation, heq, m.leadingCoeff_sub_of_lt hlt, MonomialOrder.leadingCoeff,
    m.degree_monomial, if_neg one_ne_zero]
  simp [xyExponent]

/-- Multiplication by the node equation is injective over every nontrivial commutative
coefficient ring. -/
theorem equation_isSMulRegular
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    IsSMulRegular (MvPolynomial (Fin 2) R) (equation R π n) := by
  let m : MonomialOrder (Fin 2) := MonomialOrder.lex
  have hregular : equation R π n ∈ nonZeroDivisors (MvPolynomial (Fin 2) R) :=
    m.mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors (by
      rw [equation_leadingCoeff]
      exact Submonoid.one_mem _)
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro b hb
  change equation R π n * b = 0 at hb
  exact hregular.1 b hb

/-- The principal relation ideal is proper over every nontrivial commutative coefficient
ring.  Evaluation at `(x,y) = (1,πⁿ)` supplies a section of the hypersurface equation. -/
theorem relationIdeal_ne_top
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    relationIdeal R π n ≠ ⊤ := by
  let e : MvPolynomial (Fin 2) R →ₐ[R] R := MvPolynomial.aeval ![1, π ^ n]
  have hle : relationIdeal R π n ≤ RingHom.ker e.toRingHom := by
    rw [relationIdeal, Ideal.span_le]
    rintro _ rfl
    simp [e, equation]
  intro htop
  have hone : (1 : MvPolynomial (Fin 2) R) ∈ relationIdeal R π n := by
    rw [htop]
    simp
  have := hle hone
  change e 1 = 0 at this
  simp only [map_one] at this
  exact one_ne_zero this

/-- The node equation is not a unit over any nontrivial commutative coefficient ring. -/
theorem equation_not_isUnit
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    ¬ IsUnit (equation R π n) := by
  intro h
  apply relationIdeal_ne_top R π n
  rw [relationIdeal, Ideal.span_singleton_eq_top]
  exact h

/-- The node algebra over every nontrivial commutative coefficient ring is nontrivial. -/
instance ring_nontrivial
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    Nontrivial (Ring R π n) :=
  Ideal.Quotient.nontrivial_iff.mpr (relationIdeal_ne_top R π n)

/-- The singleton node equation is a weakly regular sequence over every nontrivial
commutative coefficient ring. -/
theorem equation_isWeaklyRegular
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin 2) R) [equation R π n] := by
  rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact equation_isSMulRegular R π n

/-- Over every nontrivial commutative ring, `[xy - πⁿ]` is a regular sequence in
`R[x,y]`.  This is the precise commutative-algebra complete-intersection input for the local
node presentation, and it is robust under arbitrary nontrivial coefficient base change. -/
theorem equation_isRegular
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    RingTheory.Sequence.IsRegular
      (MvPolynomial (Fin 2) R) [equation R π n] := by
  refine
    { toIsWeaklyRegular := equation_isWeaklyRegular R π n
      top_ne_smul := ?_ }
  rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul]
  intro htop
  have hone : (1 : MvPolynomial (Fin 2) R) ∈
      equation R π n • (⊤ : Submodule (MvPolynomial (Fin 2) R)
        (MvPolynomial (Fin 2) R)) := by
    rw [← htop]
    exact Submodule.mem_top
  obtain ⟨b, -, hb⟩ :=
    (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hone
  apply equation_not_isUnit R π n
  exact isUnit_iff_exists_inv.mpr ⟨b, by simpa [smul_eq_mul] using hb⟩

/-- The single displayed relation used by the finite presentation of the node algebra. -/
private def presentationRelation (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Fin 1 → MvPolynomial (Fin 2) R :=
  fun _ ↦ equation R π n

/-- The node algebra as a finite presentation on the variables `x,y` and the single relation
`xy - πⁿ`. -/
noncomputable def completeIntersectionPresentation
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Algebra.Presentation R (Ring R π n) (Fin 2) (Fin 1) := by
  let P := Algebra.Presentation.naive
    (R := R) (v := presentationRelation R π n)
  let e :
      (MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range (presentationRelation R π n)))
        ≃ₐ[R] Ring R π n :=
    Ideal.quotientEquivAlgOfEq R (by
      rw [relationIdeal]
      congr 1
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        rfl
      · rintro rfl
        exact ⟨0, rfl⟩)
  exact P.ofAlgEquiv e

@[simp] theorem completeIntersectionPresentation_relation
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (i : Fin 1) :
    (completeIntersectionPresentation R π n).relation i = equation R π n := by
  rfl

/-- The structural map from the polynomial ring of the displayed presentation is the
quotient map defining the local-node ring. -/
@[simp] theorem completeIntersectionPresentation_algebraMap
    (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (p : (completeIntersectionPresentation R π n).Ring) :
    algebraMap (completeIntersectionPresentation R π n).Ring (Ring R π n) p =
      Ideal.Quotient.mk (relationIdeal R π n) p := by
  rw [(completeIntersectionPresentation R π n).algebraMap_apply]
  change MvPolynomial.aeval
      (completeIntersectionPresentation R π n).val p =
    Ideal.Quotient.mk (relationIdeal R π n) p
  let f : MvPolynomial (Fin 2) R →ₐ[R] Ring R π n :=
    MvPolynomial.aeval (completeIntersectionPresentation R π n).val
  let q : MvPolynomial (Fin 2) R →ₐ[R] Ring R π n :=
    Ideal.Quotient.mkₐ R (relationIdeal R π n)
  have h : f = q := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [f, q, completeIntersectionPresentation]
  exact DFunLike.congr_fun h p

/-- The relation matrix presenting the Kähler differentials of the displayed local-node
presentation is its Jacobian column. -/
@[simp] theorem completeIntersectionPresentation_differentials_relationMatrix
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (g : Fin 2) (r : Fin 1) :
    Module.Presentation.relationMatrix
        (completeIntersectionPresentation R π n).differentials g r =
      Ideal.Quotient.mk (relationIdeal R π n)
        (MvPolynomial.pderiv g (equation R π n)) := by
  change algebraMap (completeIntersectionPresentation R π n).Ring (Ring R π n)
      (((KaehlerDifferential.mvPolynomialBasis R (Fin 2)).repr
        (KaehlerDifferential.D R (MvPolynomial (Fin 2) R)
          ((completeIntersectionPresentation R π n).relation r))) g) = _
  rw [completeIntersectionPresentation_algebraMap]
  rw [completeIntersectionPresentation_relation]
  simp

/-- The displayed node presentation is a complete-intersection presentation over every
nontrivial commutative coefficient ring. -/
theorem completeIntersectionPresentation_isCompleteIntersection
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    (completeIntersectionPresentation R π n).IsCompleteIntersection := by
  simpa [Algebra.Presentation.IsCompleteIntersection] using equation_isRegular R π n

/-- The node algebra is a global complete intersection over every nontrivial commutative
coefficient ring. -/
instance node_isCompleteIntersection
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    Algebra.IsCompleteIntersection R (Ring R π n) where
  exists_presentation :=
    ⟨2, 1, completeIntersectionPresentation R π n,
      completeIntersectionPresentation_isCompleteIntersection R π n⟩

/-- The relative Jacobian ideal of the hypersurface presentation, generated in the quotient
by the images of the two partial derivatives. -/
def relativeJacobianIdeal (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ideal (Ring R π n) :=
  Ideal.span
    {Ideal.Quotient.mk (relationIdeal R π n)
        (MvPolynomial.pderiv 0 (equation R π n)),
      Ideal.Quotient.mk (relationIdeal R π n)
        (MvPolynomial.pderiv 1 (equation R π n))}

/-- For `xy - πⁿ`, the relative Jacobian ideal is exactly the ideal `(x, y)`. -/
theorem relativeJacobianIdeal_eq (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    relativeJacobianIdeal R π n =
      Ideal.span ({x R π n, y R π n} : Set (Ring R π n)) := by
  simp [relativeJacobianIdeal, x, y, Set.pair_comm]

/-- The first differential Fitting ideal of the genuine Kähler-differential presentation is
exactly the explicitly computed relative Jacobian ideal of the local node. -/
theorem differentialFittingIdeal_one_eq_relativeJacobianIdeal
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    AlgebraPresentation.differentialFittingIdeal
        (completeIntersectionPresentation R π n) 1 =
      relativeJacobianIdeal R π n := by
  rw [relativeJacobianIdeal_eq]
  change Matrix.minorIdeal
      (Module.Presentation.relationMatrix
        (completeIntersectionPresentation R π n).differentials)
      (Fintype.card
        (completeIntersectionPresentation R π n).differentials.G - 1) = _
  rw [AlgebraPresentation.card_differentials_generators]
  norm_num
  let A : Matrix (Fin 2) (Fin 1) (Ring R π n) :=
    fun g r ↦ Module.Presentation.relationMatrix
      (completeIntersectionPresentation R π n).differentials g r
  change Matrix.minorIdeal A 1 = _
  rw [Matrix.minorIdeal_fin_two_fin_one_one]
  change Ideal.span ({A 0 0, A 1 0} : Set (Ring R π n)) = _
  rw [show A 0 0 = _ from
      completeIntersectionPresentation_differentials_relationMatrix R π n 0 0,
    show A 1 0 = _ from
      completeIntersectionPresentation_differentials_relationMatrix R π n 1 0]
  simp [x, y, Set.pair_comm]

/-- The relative singular scheme of the displayed affine local-node presentation. -/
abbrev relativeSingularScheme (R : Type u) [CommRing R] (π : R) (n : ℕ) : Scheme :=
  Spec (.of (Ring R π n ⧸ relativeJacobianIdeal R π n))

/-- The relative singular scheme is a closed subscheme of the affine local node. -/
def relativeSingularι (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    relativeSingularScheme R π n ⟶ Spec (.of (Ring R π n)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (relativeJacobianIdeal R π n)))

instance relativeSingularι_isClosedImmersion
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    IsClosedImmersion (relativeSingularι R π n) := by
  apply IsClosedImmersion.spec_of_surjective
  exact Ideal.Quotient.mk_surjective

/-- For the local node, the affine differential Fitting scheme is definitionally the same
closed subscheme after rewriting its computed ideal as the Jacobian ideal. -/
theorem differentialFittingScheme_one_eq_relativeSingularScheme
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    AffineFittingLocus.differentialScheme
        (completeIntersectionPresentation R π n) 1 =
      relativeSingularScheme R π n := by
  change Spec (.of (Ring R π n ⧸
      AlgebraPresentation.differentialFittingIdeal
        (completeIntersectionPresentation R π n) 1)) = _
  rw [differentialFittingIdeal_one_eq_relativeJacobianIdeal]

/-- The defining equation holds in the quotient. -/
@[simp] theorem x_mul_y (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    x R π n * y R π n = algebraMap R (Ring R π n) (π ^ n) := by
  change Ideal.Quotient.mk (relationIdeal R π n)
      (MvPolynomial.X 0 * MvPolynomial.X 1) =
    Ideal.Quotient.mk (relationIdeal R π n) (MvPolynomial.C (π ^ n))
  rw [Ideal.Quotient.eq]
  exact Ideal.subset_span (Set.mem_singleton (equation R π n))

/-- When the smoothing parameter is invertible, the relative Jacobian ideal is the unit ideal.
This is the algebraic empty-critical-locus calculation underlying generic smoothness. -/
theorem relativeJacobianIdeal_eq_top_of_isUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    relativeJacobianIdeal R π n = ⊤ := by
  rw [relativeJacobianIdeal_eq, Ideal.eq_top_iff_one]
  have hx : x R π n ∈
      Ideal.span ({x R π n, y R π n} : Set (Ring R π n)) :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hxy := (Ideal.span ({x R π n, y R π n} : Set (Ring R π n))).mul_mem_right
    (y R π n) hx
  rw [x_mul_y] at hxy
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp (hπ.pow n)
  have ha' : algebraMap R (Ring R π n) a *
      algebraMap R (Ring R π n) (π ^ n) = 1 := by
    rw [← map_mul]
    simpa [mul_comm] using congrArg (algebraMap R (Ring R π n)) ha
  rw [← ha']
  exact (Ideal.span ({x R π n, y R π n} : Set (Ring R π n))).mul_mem_left _ hxy

/-- The universal map out of `R[x,y]/(xy - π^n)`: it exists whenever the chosen images have
product equal to the image of `π^n`. -/
def lift {R : Type u} [CommRing R] (π : R) (n : ℕ)
    {A : Type v} [CommRing A] [Algebra R A] (a b : A)
    (h : a * b = algebraMap R A (π ^ n)) : Ring R π n →ₐ[R] A := by
  refine Ideal.Quotient.liftₐ (relationIdeal R π n) (MvPolynomial.aeval ![a, b]) ?_
  intro p hp
  have hpker := (show relationIdeal R π n ≤
      RingHom.ker (MvPolynomial.aeval ![a, b]).toRingHom by
    rw [relationIdeal, Ideal.span_le]
    rintro _ rfl
    simp [equation, h]) hp
  change MvPolynomial.aeval ![a, b] p = 0 at hpker
  exact hpker

@[simp] theorem lift_x {R : Type u} [CommRing R] (π : R) (n : ℕ)
    {A : Type v} [CommRing A] [Algebra R A] (a b : A)
    (h : a * b = algebraMap R A (π ^ n)) :
    lift π n a b h (x R π n) = a := by
  change ((lift π n a b h).comp
    (Ideal.Quotient.mkₐ R (relationIdeal R π n))) (MvPolynomial.X 0) = a
  rw [lift, Ideal.Quotient.liftₐ_comp, MvPolynomial.aeval_X]
  rfl

@[simp] theorem lift_y {R : Type u} [CommRing R] (π : R) (n : ℕ)
    {A : Type v} [CommRing A] [Algebra R A] (a b : A)
    (h : a * b = algebraMap R A (π ^ n)) :
    lift π n a b h (y R π n) = b := by
  change ((lift π n a b h).comp
    (Ideal.Quotient.mkₐ R (relationIdeal R π n))) (MvPolynomial.X 1) = b
  rw [lift, Ideal.Quotient.liftₐ_comp, MvPolynomial.aeval_X]
  rfl

/-- Two algebra maps out of the local-node presentation agree if they agree on `x` and `y`. -/
theorem algHom_ext {R : Type u} [CommRing R] (π : R) (n : ℕ)
    {A : Type v} [CommRing A] [Algebra R A] {f g : Ring R π n →ₐ[R] A}
    (hx : f (x R π n) = g (x R π n))
    (hy : f (y R π n) = g (y R π n)) : f = g := by
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simpa [x] using hx
  · simpa [y] using hy

/-- The quotient has the expected universal property, including uniqueness. -/
theorem lift_unique {R : Type u} [CommRing R] (π : R) (n : ℕ)
    {A : Type v} [CommRing A] [Algebra R A] (a b : A)
    (h : a * b = algebraMap R A (π ^ n))
    (f : Ring R π n →ₐ[R] A) (hfx : f (x R π n) = a)
    (hfy : f (y R π n) = b) : f = lift π n a b h :=
  algHom_ext π n (hfx.trans (lift_x π n a b h).symm)
    (hfy.trans (lift_y π n a b h).symm)

/-- The base-ring ideal generated by the smoothing parameter power `πⁿ`. -/
def parameterPowerIdeal (R : Type u) [CommRing R] (π : R) (n : ℕ) : Ideal R :=
  Ideal.span {π ^ n}

/-- The relative critical-locus quotient sends both node coordinates to zero and reduces
scalars modulo `πⁿ`. -/
def relativeCriticalPoint (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ring R π n →ₐ[R] R ⧸ parameterPowerIdeal R π n :=
  lift π n 0 0 (by
    rw [zero_mul]
    symm
    change Ideal.Quotient.mk (parameterPowerIdeal R π n) (π ^ n) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _))

@[simp] theorem relativeCriticalPoint_x (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    relativeCriticalPoint R π n (x R π n) = 0 := by
  apply lift_x

@[simp] theorem relativeCriticalPoint_y (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    relativeCriticalPoint R π n (y R π n) = 0 := by
  apply lift_y

theorem relativeCriticalPoint_surjective
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Function.Surjective (relativeCriticalPoint R π n) := by
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨algebraMap R (Ring R π n) r, by
    rw [(relativeCriticalPoint R π n).commutes]
    rfl⟩

/-- The map from the Jacobian quotient of the node algebra to `R/(πⁿ)`. -/
def relativeJacobianQuotientMap (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (Ring R π n ⧸ relativeJacobianIdeal R π n) →ₐ[R]
      R ⧸ parameterPowerIdeal R π n :=
  Ideal.Quotient.liftₐ (relativeJacobianIdeal R π n)
    (relativeCriticalPoint R π n) (by
      intro z hz
      change relativeCriticalPoint R π n z = 0
      rw [relativeJacobianIdeal_eq] at hz
      exact (show Ideal.span ({x R π n, y R π n} : Set (Ring R π n)) ≤
          RingHom.ker (relativeCriticalPoint R π n).toRingHom by
        rw [Ideal.span_le]
        rintro _ (rfl | rfl) <;> simp) hz)

/-- The scalar section from `R/(πⁿ)` to the Jacobian quotient. -/
def relativeJacobianQuotientSection (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (R ⧸ parameterPowerIdeal R π n) →ₐ[R]
      (Ring R π n ⧸ relativeJacobianIdeal R π n) :=
  Ideal.Quotient.liftₐ (parameterPowerIdeal R π n)
    ((Ideal.Quotient.mkₐ R (relativeJacobianIdeal R π n)).comp
      (Algebra.ofId R (Ring R π n))) (by
        intro r hr
        change Ideal.Quotient.mk (relativeJacobianIdeal R π n)
          (algebraMap R (Ring R π n) r) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        rw [parameterPowerIdeal, Ideal.mem_span_singleton'] at hr
        obtain ⟨a, rfl⟩ := hr
        rw [map_mul]
        apply (relativeJacobianIdeal R π n).mul_mem_left
        rw [← x_mul_y]
        rw [relativeJacobianIdeal_eq]
        exact (Ideal.span ({x R π n, y R π n} : Set (Ring R π n))).mul_mem_right _
          (Ideal.subset_span (Set.mem_insert _ _)))

theorem relativeJacobianQuotientMap_comp_section
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (relativeJacobianQuotientMap R π n).comp
      (relativeJacobianQuotientSection R π n) =
      AlgHom.id R (R ⧸ parameterPowerIdeal R π n) := by
  apply Ideal.Quotient.algHom_ext R
  rw [AlgHom.comp_assoc, relativeJacobianQuotientSection, Ideal.Quotient.liftₐ_comp,
    AlgHom.id_comp]
  ext

theorem relativeJacobianQuotientSection_comp_map
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (relativeJacobianQuotientSection R π n).comp
      (relativeJacobianQuotientMap R π n) =
      AlgHom.id R (Ring R π n ⧸ relativeJacobianIdeal R π n) := by
  apply Ideal.Quotient.algHom_ext R
  rw [AlgHom.comp_assoc, relativeJacobianQuotientMap, Ideal.Quotient.liftₐ_comp,
    AlgHom.id_comp]
  apply algHom_ext (R := R) (π := π) (n := n)
    (A := Ring R π n ⧸ relativeJacobianIdeal R π n)
  · simp only [AlgHom.coe_comp, Function.comp_apply, relativeCriticalPoint_x,
      map_zero, Ideal.Quotient.mkₐ_eq_mk]
    symm
    rw [Ideal.Quotient.eq_zero_iff_mem, relativeJacobianIdeal_eq]
    exact Ideal.subset_span (Set.mem_insert _ _)
  · simp only [AlgHom.coe_comp, Function.comp_apply, relativeCriticalPoint_y,
      map_zero, Ideal.Quotient.mkₐ_eq_mk]
    symm
    rw [Ideal.Quotient.eq_zero_iff_mem, relativeJacobianIdeal_eq]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- The full scheme structure of the relative Jacobian locus is `Spec(R/(πⁿ))`: killing the
two partial derivatives in the node algebra leaves precisely the parameter-power quotient. -/
def relativeJacobianQuotientEquiv (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (Ring R π n ⧸ relativeJacobianIdeal R π n) ≃ₐ[R]
      R ⧸ parameterPowerIdeal R π n :=
  AlgEquiv.ofAlgHom (relativeJacobianQuotientMap R π n)
    (relativeJacobianQuotientSection R π n)
    (relativeJacobianQuotientMap_comp_section R π n)
    (relativeJacobianQuotientSection_comp_map R π n)

/-- The kernel of the critical-locus quotient is exactly the relative Jacobian ideal. -/
theorem relativeCriticalPoint_ker (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    RingHom.ker (relativeCriticalPoint R π n).toRingHom =
      relativeJacobianIdeal R π n := by
  apply le_antisymm
  · intro z hz
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply (relativeJacobianQuotientEquiv R π n).injective
    change relativeCriticalPoint R π n z = relativeJacobianQuotientEquiv R π n 0
    simpa [relativeJacobianQuotientEquiv, relativeJacobianQuotientMap] using hz
  · rw [relativeJacobianIdeal_eq, Ideal.span_le]
    rintro _ (rfl | rfl) <;> simp

/-- The relative Jacobian locus as a closed affine subscheme of the node chart. -/
def relativeCriticalLocusSpec (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Spec (.of (R ⧸ parameterPowerIdeal R π n)) ⟶ Spec (.of (Ring R π n)) :=
  Spec.map (CommRingCat.ofHom (relativeCriticalPoint R π n).toRingHom)

instance relativeCriticalLocusSpec_isClosedImmersion
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    IsClosedImmersion (relativeCriticalLocusSpec R π n) := by
  apply IsClosedImmersion.spec_of_surjective
  exact relativeCriticalPoint_surjective R π n

/-- The carrier of the relative critical-locus subscheme is the Jacobian zero locus. -/
theorem range_relativeCriticalLocusSpec
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Set.range (relativeCriticalLocusSpec R π n) =
      (PrimeSpectrum.zeroLocus (relativeJacobianIdeal R π n) :
        Set (PrimeSpectrum (Ring R π n))) := by
  change Set.range (PrimeSpectrum.comap (relativeCriticalPoint R π n).toRingHom) = _
  rw [range_comap_of_surjective _ (relativeCriticalPoint R π n).toRingHom
      (relativeCriticalPoint_surjective R π n), relativeCriticalPoint_ker]

/-- If `π` is invertible, the relative critical-locus carrier is empty. -/
theorem zeroLocus_relativeJacobianIdeal_eq_empty_of_isUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    (PrimeSpectrum.zeroLocus (relativeJacobianIdeal R π n) :
      Set (PrimeSpectrum (Ring R π n))) = ∅ := by
  rw [relativeJacobianIdeal_eq_top_of_isUnit R π n hπ]
  simp

/-! ## Tangent order at the total-space origin -/

/-- The polynomial-ring ideal `(x, y, π)` of the total-space origin over the closed base
point. -/
def totalOriginIdeal (R : Type u) [CommRing R] (π : R) :
    Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.C π}

/-- At every thickness at least two, the node equation lies in `(x, y, π)²`. -/
theorem equation_mem_totalOriginIdeal_sq_of_two_le
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hn : 2 ≤ n) :
    equation R π n ∈ totalOriginIdeal R π ^ 2 := by
  rw [equation]
  apply Ideal.sub_mem
  · rw [pow_two]
    exact Ideal.mul_mem_mul
      (Ideal.subset_span (Set.mem_insert _ _))
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, map_mul, pow_two]
    have hcc : MvPolynomial.C π * MvPolynomial.C π ∈
        totalOriginIdeal R π * totalOriginIdeal R π := Ideal.mul_mem_mul
      (Ideal.subset_span (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
      (Ideal.subset_span (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    simpa [pow_two, mul_assoc] using
      (totalOriginIdeal R π * totalOriginIdeal R π).mul_mem_right
        (MvPolynomial.C (π ^ k)) hcc

/-- Evaluation of both polynomial coordinates at zero. -/
def totalOriginEvaluation (R : Type u) [CommRing R] :
    MvPolynomial (Fin 2) R →ₐ[R] R :=
  MvPolynomial.aeval ![0, 0]

/-- Evaluating the total-origin ideal at `x=y=0` gives exactly `(π)`. -/
theorem totalOriginIdeal_map_originEvaluation
    (R : Type u) [CommRing R] (π : R) :
    (totalOriginIdeal R π).map (totalOriginEvaluation R) = Ideal.span {π} := by
  apply le_antisymm
  · rw [totalOriginIdeal, Ideal.map_span, Ideal.span_le]
    rintro z ⟨w, hw, rfl⟩
    rcases hw with rfl | rfl | rfl
    · simp [totalOriginEvaluation]
    · simp [totalOriginEvaluation]
    · simp [totalOriginEvaluation]
  · rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hc : MvPolynomial.C π ∈ totalOriginIdeal R π := by
      rw [totalOriginIdeal]
      exact Ideal.subset_span (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have h := Ideal.mem_map_of_mem (totalOriginEvaluation R) hc
    simpa [totalOriginEvaluation] using h

/-- At thickness one, the node equation vanishes at the total-space origin. -/
theorem equation_one_mem_totalOriginIdeal (R : Type u) [CommRing R] (π : R) :
    equation R π 1 ∈ totalOriginIdeal R π := by
  rw [equation, pow_one]
  apply Ideal.sub_mem
  · exact (totalOriginIdeal R π).mul_mem_right _
      (Ideal.subset_span (Set.mem_insert _ _))
  · exact Ideal.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- For an irreducible parameter, the thickness-zero equation does not pass through the
displayed total-space origin. -/
theorem equation_zero_not_mem_totalOriginIdeal
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) :
    equation R π 0 ∉ totalOriginIdeal R π := by
  intro heq
  have heval : totalOriginEvaluation R (equation R π 0) ∈
      (totalOriginIdeal R π).map (totalOriginEvaluation R) :=
    Ideal.mem_map_of_mem (totalOriginEvaluation R) heq
  rw [totalOriginIdeal_map_originEvaluation] at heval
  have hneg : -(1 : R) ∈ Ideal.span {π} := by
    simpa [totalOriginEvaluation, equation] using heval
  have hone : (1 : R) ∈ Ideal.span {π} :=
    (Ideal.neg_mem_iff (Ideal.span {π})).mp hneg
  have htop : Ideal.span {π} = ⊤ := (Ideal.eq_top_iff_one _).mpr hone
  exact hπ.not_isUnit (Ideal.span_singleton_eq_top.mp htop)

/-- If `π` is irreducible (in particular, a DVR uniformizer), the thickness-one equation has
nonzero linear term modulo `(x, y, π)²`.  Together with
`equation_mem_totalOriginIdeal_sq_of_two_le`, this is the algebraic tangent-order boundary
between thickness one and higher thickness. -/
theorem equation_one_not_mem_totalOriginIdeal_sq
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) :
    equation R π 1 ∉ totalOriginIdeal R π ^ 2 := by
  intro heq
  let e := totalOriginEvaluation R
  have hmap : (totalOriginIdeal R π).map e ≤ Ideal.span {π} :=
    (totalOriginIdeal_map_originEvaluation R π).le
  have heval : e (equation R π 1) ∈ (totalOriginIdeal R π ^ 2).map e :=
    Ideal.mem_map_of_mem e heq
  rw [Ideal.map_pow] at heval
  have heval' : e (equation R π 1) ∈ Ideal.span {π} ^ 2 :=
    (pow_le_pow_left' hmap 2) heval
  rw [Ideal.span_singleton_pow] at heval'
  have hmem : π ∈ Ideal.span {π ^ 2} := by
    have hneg : -π ∈ Ideal.span {π ^ 2} := by
      simpa [e, totalOriginEvaluation, equation] using heval'
    exact (Ideal.neg_mem_iff (Ideal.span {π ^ 2})).mp hneg
  rw [Ideal.mem_span_singleton'] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hpi0 : π ≠ 0 := hπ.ne_zero
  have hunit : IsUnit π := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨a, ?_⟩
    apply mul_left_cancel₀ hpi0
    calc
      π * (π * a) = a * π ^ 2 := by ring
      _ = π := ha
      _ = π * 1 := by simp
  exact hπ.not_isUnit hunit

/-- For an irreducible parameter, membership of `xy - πⁿ` in `(x, y, π)²` is equivalent to
having thickness at least two. -/
theorem equation_mem_totalOriginIdeal_sq_iff
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (hπ : Irreducible π) (n : ℕ) :
    equation R π n ∈ totalOriginIdeal R π ^ 2 ↔ 2 ≤ n := by
  constructor
  · intro h
    by_contra hn
    have hnlt : n < 2 := Nat.lt_of_not_ge hn
    interval_cases n
    · exact equation_zero_not_mem_totalOriginIdeal R π hπ
        (Ideal.pow_le_self two_ne_zero h)
    · exact equation_one_not_mem_totalOriginIdeal_sq R π hπ h
  · exact equation_mem_totalOriginIdeal_sq_of_two_le R π n

/-- A formal partial derivative sends the square of an ideal into the ideal. -/
theorem pderiv_mem_of_mem_sq
    (R : Type u) [CommRing R] (p : Ideal (MvPolynomial (Fin 2) R))
    (i : Fin 2) {f : MvPolynomial (Fin 2) R} (hf : f ∈ p ^ 2) :
    MvPolynomial.pderiv i f ∈ p := by
  rw [pow_two] at hf
  refine Submodule.mul_induction_on hf ?_ ?_
  · intro a ha b hb
    rw [MvPolynomial.pderiv_mul]
    exact p.add_mem (p.mul_mem_left _ hb) (p.mul_mem_right _ ha)
  · intro a b ha hb
    simpa only [map_add] using p.add_mem ha hb

/-- Evaluation at the total-space origin is surjective because constant polynomials map to their
coefficients. -/
theorem totalOriginEvaluation_surjective
    (R : Type u) [CommRing R] :
    Function.Surjective (totalOriginEvaluation R) := by
  intro r
  exact ⟨MvPolynomial.C r, by simp [totalOriginEvaluation]⟩

/-- Removing the value at the origin leaves a polynomial in the ideal generated by the two
coordinates, hence in `(x,y,π)`. -/
theorem sub_C_totalOriginEvaluation_mem_totalOriginIdeal
    (R : Type u) [CommRing R] (π : R) (p : MvPolynomial (Fin 2) R) :
    p - MvPolynomial.C (totalOriginEvaluation R p) ∈ totalOriginIdeal R π := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [totalOriginEvaluation]
  | add p q hp hq =>
      simpa only [map_add, MvPolynomial.C_add, add_sub_add_comm] using
        (totalOriginIdeal R π).add_mem hp hq
  | mul_X p i hp =>
      have hXi : MvPolynomial.X i ∈ totalOriginIdeal R π := by
        rw [totalOriginIdeal]
        fin_cases i
        · exact Ideal.subset_span (Set.mem_insert _ _)
        · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      fin_cases i
      · simpa [totalOriginEvaluation] using
          (totalOriginIdeal R π).mul_mem_left p hXi
      · simpa [totalOriginEvaluation] using
          (totalOriginIdeal R π).mul_mem_left p hXi

/-- The total-origin ideal is the inverse image of `(π)` under evaluation at `x=y=0`. -/
theorem totalOriginIdeal_eq_comap_originEvaluation
    (R : Type u) [CommRing R] (π : R) :
    totalOriginIdeal R π =
      (Ideal.span {π}).comap (totalOriginEvaluation R) := by
  rw [← totalOriginIdeal_map_originEvaluation R π,
    Ideal.comap_map_of_surjective (totalOriginEvaluation R)
      (totalOriginEvaluation_surjective R)]
  symm
  apply sup_eq_left.mpr
  intro p hp
  change totalOriginEvaluation R p = 0 at hp
  have h := sub_C_totalOriginEvaluation_mem_totalOriginIdeal R π p
  simpa only [hp, map_zero, MvPolynomial.C_0, sub_zero] using h

/-- If `π` generates the maximal ideal of a local base, `(x,y,π)` is maximal in the ambient
polynomial ring. -/
theorem totalOriginIdeal_isMaximal
    (R : Type u) [CommRing R] [IsLocalRing R] (π : R)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal R) :
    (totalOriginIdeal R π).IsMaximal := by
  rw [totalOriginIdeal_eq_comap_originEvaluation, hπ]
  exact Ideal.comap_isMaximal_of_surjective (totalOriginEvaluation R)
    (totalOriginEvaluation_surjective R)

/-- For an irreducible uniformizer of a DVR, `(x,y,π)` is the total-space origin's maximal
ideal. -/
theorem totalOriginIdeal_isMaximal_of_irreducible
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) :
    (totalOriginIdeal R π).IsMaximal := by
  apply totalOriginIdeal_isMaximal R π
  exact hπ.maximalIdeal_eq.symm

/-- At thickness one, the equation has order exactly one at every ambient prime through the
hypersurface.  Indeed, order at least two forces both partial derivatives `x` and `y` into the
prime, then also `π`; maximality of `(x,y,π)` reduces to the origin computation. -/
theorem equation_one_not_mem_prime_sq
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (p : Ideal (MvPolynomial (Fin 2) R))
    [p.IsPrime] (heq : equation R π 1 ∈ p) :
    equation R π 1 ∉ p ^ 2 := by
  intro heq2
  have hy : MvPolynomial.X 1 ∈ p := by
    simpa using pderiv_mem_of_mem_sq R p 0 heq2
  have hx : MvPolynomial.X 0 ∈ p := by
    simpa using pderiv_mem_of_mem_sq R p 1 heq2
  have hπp : MvPolynomial.C π ∈ p := by
    have hxy : MvPolynomial.X 0 * MvPolynomial.X 1 ∈ p := p.mul_mem_left _ hy
    have h := p.sub_mem hxy heq
    simpa [equation] using h
  have horigin : totalOriginIdeal R π ≤ p := by
    rw [totalOriginIdeal, Ideal.span_le]
    rintro z (rfl | rfl | rfl)
    · exact hx
    · exact hy
    · exact hπp
  have hp_eq : p = totalOriginIdeal R π :=
    ((totalOriginIdeal_isMaximal_of_irreducible R π hπ).eq_of_le
      (inferInstance : p.IsPrime).ne_top horigin).symm
  rw [hp_eq] at heq2
  exact equation_one_not_mem_totalOriginIdeal_sq R π hπ heq2

/-- The regular ambient polynomial plane localized at an arbitrary prime. -/
abbrev PrimeAmbientRing
    (R : Type u) [CommRing R] (p : Ideal (MvPolynomial (Fin 2) R)) [p.IsPrime] :=
  Localization.AtPrime p

/-- The node equation inside an arbitrary ambient prime localization. -/
def primeEquation
    (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (p : Ideal (MvPolynomial (Fin 2) R)) [p.IsPrime] : PrimeAmbientRing R p :=
  algebraMap (MvPolynomial (Fin 2) R) (PrimeAmbientRing R p) (equation R π n)

instance primeAmbientRing_isRegular
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (p : Ideal (MvPolynomial (Fin 2) R)) [p.IsPrime] :
    IsRegularLocalRing (PrimeAmbientRing R p) := by
  infer_instance

/-- The node equation remains a nonzerodivisor after localization at any ambient prime. -/
theorem primeEquation_isRegular
    (R : Type u) [CommRing R] [IsDomain R] (π : R) (n : ℕ)
    (p : Ideal (MvPolynomial (Fin 2) R)) [p.IsPrime] :
    IsSMulRegular (PrimeAmbientRing R p) (primeEquation R π n p) := by
  have hbase : equation R π n ∈ nonZeroDivisors (MvPolynomial (Fin 2) R) := by
    rw [mem_nonZeroDivisors_iff_left]
    intro z hz
    exact (equation_isSMulRegular R π n).right_eq_zero_of_smul (by
      simpa only [smul_eq_mul] using hz)
  have hlocal : primeEquation R π n p ∈ nonZeroDivisors (PrimeAmbientRing R p) :=
    IsLocalization.nonZeroDivisors_le_comap p.primeCompl (PrimeAmbientRing R p) hbase
  rw [mem_nonZeroDivisors_iff_left] at hlocal
  exact isSMulRegular_iff_right_eq_zero_of_smul.mpr fun z hz => hlocal z (by
    simpa only [smul_eq_mul] using hz)

/-- An equation through an ambient prime belongs to the maximal ideal after localization. -/
theorem primeEquation_mem_maximalIdeal
    (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (p : Ideal (MvPolynomial (Fin 2) R)) [p.IsPrime]
    (heq : equation R π n ∈ p) :
    primeEquation R π n p ∈ IsLocalRing.maximalIdeal (PrimeAmbientRing R p) := by
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (PrimeAmbientRing R p) p (equation R π n)).mpr heq

/-- The thickness-one equation remains outside the square of the maximal ideal after
localization at every prime through the hypersurface. -/
theorem primeEquation_one_not_mem_maximalIdeal_sq
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (p : Ideal (MvPolynomial (Fin 2) R))
    [p.IsPrime] (heq : equation R π 1 ∈ p) :
    primeEquation R π 1 p ∉ IsLocalRing.maximalIdeal (PrimeAmbientRing R p) ^ 2 := by
  intro hlocal
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p, ← Ideal.map_pow] at hlocal
  change algebraMap (MvPolynomial (Fin 2) R) (PrimeAmbientRing R p)
      (equation R π 1) ∈
        Ideal.map (algebraMap (MvPolynomial (Fin 2) R) (PrimeAmbientRing R p)) (p ^ 2)
    at hlocal
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl] at hlocal
  obtain ⟨s, hs, hsf⟩ := hlocal
  have hpartial (i : Fin 2) : s * MvPolynomial.pderiv i (equation R π 1) ∈ p := by
    have hderiv := pderiv_mem_of_mem_sq R p i hsf
    rw [MvPolynomial.pderiv_mul] at hderiv
    have h := p.sub_mem hderiv
      (p.mul_mem_left (MvPolynomial.pderiv i s) heq)
    simpa using h
  have hy : MvPolynomial.X 1 ∈ p := by
    have h := (inferInstance : p.IsPrime).mem_or_mem (hpartial 0)
    simpa [equation] using h.resolve_left (Ideal.mem_primeCompl_iff.mp hs)
  have hx : MvPolynomial.X 0 ∈ p := by
    have h := (inferInstance : p.IsPrime).mem_or_mem (hpartial 1)
    simpa [equation] using h.resolve_left (Ideal.mem_primeCompl_iff.mp hs)
  have hπp : MvPolynomial.C π ∈ p := by
    have hxy : MvPolynomial.X 0 * MvPolynomial.X 1 ∈ p := p.mul_mem_left _ hy
    have h := p.sub_mem hxy heq
    simpa [equation] using h
  have horigin : totalOriginIdeal R π ≤ p := by
    rw [totalOriginIdeal, Ideal.span_le]
    rintro z (rfl | rfl | rfl)
    · exact hx
    · exact hy
    · exact hπp
  have hp_eq : p = totalOriginIdeal R π :=
    ((totalOriginIdeal_isMaximal_of_irreducible R π hπ).eq_of_le
      (inferInstance : p.IsPrime).ne_top horigin).symm
  have hsnot : (s : MvPolynomial (Fin 2) R) ∉ totalOriginIdeal R π := by
    rw [← hp_eq]
    exact Ideal.mem_primeCompl_iff.mp hs
  have hsf' : (s : MvPolynomial (Fin 2) R) * equation R π 1 ∈
      totalOriginIdeal R π ^ 2 := by
    rw [← hp_eq]
    exact hsf
  let : (totalOriginIdeal R π).IsMaximal :=
    totalOriginIdeal_isMaximal_of_irreducible R π hπ
  exact equation_one_not_mem_totalOriginIdeal_sq R π hπ
    ((Ideal.IsMaximal.mul_mem_pow _ hsf').resolve_left hsnot)

/-- A localized node hypersurface is regular whenever its equation has order one in the
ambient regular local ring. -/
theorem primeHypersurface_isRegularLocalRing_of_not_mem_sq
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (n : ℕ) (p : Ideal (MvPolynomial (Fin 2) R))
    [p.IsPrime] (heq : equation R π n ∈ p)
    (horder : primeEquation R π n p ∉
      IsLocalRing.maximalIdeal (PrimeAmbientRing R p) ^ 2) :
    IsRegularLocalRing
      (PrimeAmbientRing R p ⧸ Ideal.span {primeEquation R π n p}) := by
  rw [IsRegularLocalRing.quotient_span_singleton_iff
    (primeEquation_isRegular R π n p) (primeEquation_mem_maximalIdeal R π n p heq)]
  exact horder

/-- Every local hypersurface chart of the thickness-one model is a regular local ring. -/
theorem primeHypersurface_one_isRegularLocalRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (p : Ideal (MvPolynomial (Fin 2) R))
    [p.IsPrime] (heq : equation R π 1 ∈ p) :
    IsRegularLocalRing
      (PrimeAmbientRing R p ⧸ Ideal.span {primeEquation R π 1 p}) :=
  primeHypersurface_isRegularLocalRing_of_not_mem_sq R π 1 p heq
    (primeEquation_one_not_mem_maximalIdeal_sq R π hπ p heq)

/-- A pointwise order-one test for the defining equation proves that the entire node
hypersurface ring is regular.  This packages localization commuting with quotient. -/
theorem ring_isRegularRing_of_primeEquation_not_mem_sq
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (n : ℕ)
    (horder : ∀ (p : Ideal (MvPolynomial (Fin 2) R)) [p.IsPrime],
      equation R π n ∈ p → primeEquation R π n p ∉
        IsLocalRing.maximalIdeal (PrimeAmbientRing R p) ^ 2) :
    IsRegularRing (Ring R π n) := by
  rw [isRegularRing_iff]
  intro q hq
  let p : Ideal (MvPolynomial (Fin 2) R) :=
    q.comap (Ideal.Quotient.mk (relationIdeal R π n))
  let : p.IsPrime := hq.comap (Ideal.Quotient.mk (relationIdeal R π n))
  let S := PrimeAmbientRing R p
  let J : Ideal S :=
    (relationIdeal R π n).map (algebraMap (MvPolynomial (Fin 2) R) S)
  let T := S ⧸ J
  have heq : equation R π n ∈ p := by
    change Ideal.Quotient.mk (relationIdeal R π n) (equation R π n) ∈ q
    have heq0 : Ideal.Quotient.mk (relationIdeal R π n) (equation R π n) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton _)
    rw [heq0]
    exact q.zero_mem
  have hJ : J = Ideal.span {primeEquation R π n p} := by
    dsimp [J, S]
    simp [relationIdeal, primeEquation, Ideal.map_span]
  have hregSpan : IsRegularLocalRing
      (S ⧸ Ideal.span {primeEquation R π n p}) :=
    primeHypersurface_isRegularLocalRing_of_not_mem_sq R π n p heq (horder p heq)
  let : IsRegularLocalRing (S ⧸ Ideal.span {primeEquation R π n p}) := hregSpan
  let hregT : IsRegularLocalRing T := by
    change IsRegularLocalRing (S ⧸ J)
    exact @IsRegularLocalRing.of_ringEquiv
      (S ⧸ Ideal.span {primeEquation R π n p}) _ inferInstance (S ⧸ J) _
      (Ideal.quotEquivOfEq hJ).symm
  let : IsRegularLocalRing T := hregT
  have hmonoid : Algebra.algebraMapSubmonoid (Ring R π n) p.primeCompl = q.primeCompl := by
    exact q.map_primeCompl_comap_of_surjective
      (Ideal.Quotient.mk (relationIdeal R π n)) Ideal.Quotient.mk_surjective
  let : Algebra (Ring R π n) T := inferInstance
  have hloc : IsLocalization
      (Algebra.algebraMapSubmonoid (Ring R π n) p.primeCompl) T := inferInstance
  have hloc' : IsLocalization.AtPrime T q := by
    change IsLocalization q.primeCompl T
    rw [← hmonoid]
    exact hloc
  let : IsLocalization.AtPrime T q := hloc'
  exact @IsRegularLocalRing.of_ringEquiv T _ inferInstance (Localization.AtPrime q) _
    (IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)).toRingEquiv

/-- At exponent zero, the equation `xy - 1` has order one at every ambient prime through it. -/
theorem primeEquation_zero_not_mem_maximalIdeal_sq
    (R : Type u) [CommRing R] [IsDomain R]
    (π : R) (p : Ideal (MvPolynomial (Fin 2) R))
    [p.IsPrime] (heq : equation R π 0 ∈ p) :
    primeEquation R π 0 p ∉ IsLocalRing.maximalIdeal (PrimeAmbientRing R p) ^ 2 := by
  intro hlocal
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p, ← Ideal.map_pow] at hlocal
  change algebraMap (MvPolynomial (Fin 2) R) (PrimeAmbientRing R p)
      (equation R π 0) ∈
        Ideal.map (algebraMap (MvPolynomial (Fin 2) R) (PrimeAmbientRing R p)) (p ^ 2)
    at hlocal
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl] at hlocal
  obtain ⟨s, hs, hsf⟩ := hlocal
  have hpartial (i : Fin 2) : s * MvPolynomial.pderiv i (equation R π 0) ∈ p := by
    have hderiv := pderiv_mem_of_mem_sq R p i hsf
    rw [MvPolynomial.pderiv_mul] at hderiv
    have h := p.sub_mem hderiv
      (p.mul_mem_left (MvPolynomial.pderiv i s) heq)
    simpa using h
  have hy : MvPolynomial.X 1 ∈ p := by
    have h := (inferInstance : p.IsPrime).mem_or_mem (hpartial 0)
    simpa [equation] using h.resolve_left (Ideal.mem_primeCompl_iff.mp hs)
  have hx : MvPolynomial.X 0 ∈ p := by
    have h := (inferInstance : p.IsPrime).mem_or_mem (hpartial 1)
    simpa [equation] using h.resolve_left (Ideal.mem_primeCompl_iff.mp hs)
  have hxy : MvPolynomial.X 0 * MvPolynomial.X 1 ∈ p := p.mul_mem_left _ hy
  have hone : (1 : MvPolynomial (Fin 2) R) ∈ p := by
    have h := p.sub_mem hxy heq
    simpa [equation] using h
  exact (inferInstance : p.IsPrime).ne_top ((Ideal.eq_top_iff_one p).mpr hone)

/-- The exponent-zero node presentation is a regular ring. -/
theorem ring_zero_isRegularRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) : IsRegularRing (Ring R π 0) := by
  exact ring_isRegularRing_of_primeEquation_not_mem_sq R π 0 fun p _ heq =>
    primeEquation_zero_not_mem_maximalIdeal_sq R π p heq

/-- The thickness-one node presentation is a regular ring. -/
theorem ring_one_isRegularRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) : IsRegularRing (Ring R π 1) := by
  exact ring_isRegularRing_of_primeEquation_not_mem_sq R π 1 fun p _ heq =>
    primeEquation_one_not_mem_maximalIdeal_sq R π hπ p heq

/-- Every positive-thickness equation passes through the displayed total-space origin. -/
theorem equation_mem_totalOriginIdeal_of_pos
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hn : 0 < n) :
    equation R π n ∈ totalOriginIdeal R π := by
  rcases n with _ | n
  · simp at hn
  · rcases n with _ | n
    · exact equation_one_mem_totalOriginIdeal R π
    · exact Ideal.pow_le_self two_ne_zero <|
        equation_mem_totalOriginIdeal_sq_of_two_le R π (n + 2) (by omega)

section OriginLocalRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (π : R) (hπ : Irreducible π)

/-- The regular local ambient polynomial plane at `(x,y,π)`.  The irreducibility proof is an
explicit argument because it selects the corresponding prime-complement localization. -/
abbrev OriginAmbientRing :=
  @Localization.AtPrime (MvPolynomial (Fin 2) R) _ (totalOriginIdeal R π)
    (totalOriginIdeal_isMaximal_of_irreducible R π hπ).isPrime

/-- The node equation inside the local ambient polynomial ring. -/
def originEquation (n : ℕ) : OriginAmbientRing R π hπ :=
  algebraMap (MvPolynomial (Fin 2) R) (OriginAmbientRing R π hπ) (equation R π n)

/-- The local ring of the node hypersurface at the total-space origin. -/
abbrev OriginRing (n : ℕ) :=
  OriginAmbientRing R π hπ ⧸ Ideal.span {originEquation R π hπ n}

instance originAmbientRing_isRegular :
    IsRegularLocalRing (OriginAmbientRing R π hπ) := by
  let : (totalOriginIdeal R π).IsMaximal :=
    totalOriginIdeal_isMaximal_of_irreducible R π hπ
  infer_instance

/-- The localized node equation remains a nonzerodivisor. -/
theorem originEquation_isRegular (n : ℕ) :
    IsSMulRegular (OriginAmbientRing R π hπ) (originEquation R π hπ n) := by
  let : (totalOriginIdeal R π).IsMaximal :=
    totalOriginIdeal_isMaximal_of_irreducible R π hπ
  have hbase : equation R π n ∈ nonZeroDivisors (MvPolynomial (Fin 2) R) := by
    rw [mem_nonZeroDivisors_iff_left]
    intro z hz
    exact (equation_isSMulRegular R π n).right_eq_zero_of_smul (by
      simpa only [smul_eq_mul] using hz)
  have hlocal : originEquation R π hπ n ∈
      nonZeroDivisors (OriginAmbientRing R π hπ) :=
    IsLocalization.nonZeroDivisors_le_comap
      (totalOriginIdeal R π).primeCompl (OriginAmbientRing R π hπ) hbase
  rw [mem_nonZeroDivisors_iff_left] at hlocal
  exact isSMulRegular_iff_right_eq_zero_of_smul.mpr fun z hz => hlocal z (by
    simpa only [smul_eq_mul] using hz)

/-- A positive-thickness node equation belongs to the maximal ideal of the localized ambient
plane. -/
theorem originEquation_mem_maximalIdeal (n : ℕ) (hn : 0 < n) :
    originEquation R π hπ n ∈ IsLocalRing.maximalIdeal (OriginAmbientRing R π hπ) := by
  let : (totalOriginIdeal R π).IsMaximal :=
    totalOriginIdeal_isMaximal_of_irreducible R π hπ
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (OriginAmbientRing R π hπ) (totalOriginIdeal R π) (equation R π n)).mpr
      (equation_mem_totalOriginIdeal_of_pos R π n hn)

/-- The first coordinate in the node's local ring at the total-space origin. -/
def originX (n : ℕ) : OriginRing R π hπ n :=
  Ideal.Quotient.mk _
    (algebraMap (MvPolynomial (Fin 2) R) (OriginAmbientRing R π hπ) (MvPolynomial.X 0))

/-- The second coordinate in the node's local ring at the total-space origin. -/
def originY (n : ℕ) : OriginRing R π hπ n :=
  Ideal.Quotient.mk _
    (algebraMap (MvPolynomial (Fin 2) R) (OriginAmbientRing R π hπ) (MvPolynomial.X 1))

/-- The uniformizer in the node's local ring at the total-space origin. -/
def originParameter (n : ℕ) : OriginRing R π hπ n :=
  Ideal.Quotient.mk _
    (algebraMap (MvPolynomial (Fin 2) R) (OriginAmbientRing R π hπ) (MvPolynomial.C π))

/-- The image of the ambient maximal ideal in the node's local ring. -/
def originMaximalIdeal (n : ℕ) : Ideal (OriginRing R π hπ n) :=
  (IsLocalRing.maximalIdeal (OriginAmbientRing R π hπ)).map
    (Ideal.Quotient.mk (Ideal.span {originEquation R π hπ n}))

/-- At positive thickness, the displayed origin ideal is maximal. -/
theorem originMaximalIdeal_isMaximal (n : ℕ) (hn : 0 < n) :
    (originMaximalIdeal R π hπ n).IsMaximal := by
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker]
  exact Ideal.span_le.mpr fun z hz => by
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact originEquation_mem_maximalIdeal R π hπ n hn

/-- The origin ideal has its expected three-element generating set `x,y,π`. -/
theorem originMaximalIdeal_eq_span (n : ℕ) :
    originMaximalIdeal R π hπ n =
      Ideal.span ({originX R π hπ n, originY R π hπ n,
        originParameter R π hπ n} : Set (OriginRing R π hπ n)) := by
  let : (totalOriginIdeal R π).IsMaximal :=
    totalOriginIdeal_isMaximal_of_irreducible R π hπ
  let q : OriginAmbientRing R π hπ →+* OriginRing R π hπ n :=
    Ideal.Quotient.mk (Ideal.span {originEquation R π hπ n})
  calc
    originMaximalIdeal R π hπ n =
        (IsLocalRing.maximalIdeal (OriginAmbientRing R π hπ)).map q := rfl
    _ = ((totalOriginIdeal R π).map
        (algebraMap (MvPolynomial (Fin 2) R) (OriginAmbientRing R π hπ))).map q := by
      rw [IsLocalization.AtPrime.map_eq_maximalIdeal]
    _ = Ideal.span ({originX R π hπ n, originY R π hπ n,
        originParameter R π hπ n} : Set (OriginRing R π hπ n)) := by
      change ((Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1,
        MvPolynomial.C π}).map
          (algebraMap (MvPolynomial (Fin 2) R) (OriginAmbientRing R π hπ))).map q = _
      rw [Ideal.map_span, Ideal.map_span]
      congr 1
      rw [Set.image_image, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
      rfl

/-- Consequently, the origin ideal can be generated by at most three elements. -/
theorem originMaximalIdeal_spanFinrank_le_three (n : ℕ) :
    (originMaximalIdeal R π hπ n).spanFinrank ≤ 3 := by
  rw [originMaximalIdeal_eq_span R π hπ n]
  apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (by simp))
  calc
    Set.ncard ({originX R π hπ n, originY R π hπ n,
      originParameter R π hπ n} : Set (OriginRing R π hπ n)) ≤
        Set.ncard ({originY R π hπ n, originParameter R π hπ n} :
          Set (OriginRing R π hπ n)) + 1 := Set.ncard_insert_le _ _
    _ ≤ (Set.ncard ({originParameter R π hπ n} :
          Set (OriginRing R π hπ n)) + 1) + 1 := by
      exact Nat.add_le_add_right (Set.ncard_insert_le _ _) 1
    _ = 3 := by simp

/-- Localization preserves the tangent-order test: the local equation belongs to the square of
the ambient maximal ideal exactly at thickness at least two. -/
theorem originEquation_mem_maximalIdeal_sq_iff (n : ℕ) :
    originEquation R π hπ n ∈ IsLocalRing.maximalIdeal (OriginAmbientRing R π hπ) ^ 2 ↔
      2 ≤ n := by
  let : (totalOriginIdeal R π).IsMaximal :=
    totalOriginIdeal_isMaximal_of_irreducible R π hπ
  change algebraMap (MvPolynomial (Fin 2) R) (OriginAmbientRing R π hπ)
      (equation R π n) ∈ IsLocalRing.maximalIdeal (OriginAmbientRing R π hπ) ^ 2 ↔ _
  rw [← Ideal.mem_comap]
  change equation R π n ∈
      (IsLocalRing.maximalIdeal (OriginAmbientRing R π hπ) ^ 2).under
        (MvPolynomial (Fin 2) R) ↔ _
  rw [IsLocalization.AtPrime.under_maximalIdeal_pow
      (p := totalOriginIdeal R π) (Rₚ := OriginAmbientRing R π hπ),
    equation_mem_totalOriginIdeal_sq_iff R π hπ n]

/-- The node's local ring at the total-space origin is regular exactly at thickness one. -/
theorem originRing_isRegularLocalRing_iff (n : ℕ) (hn : 0 < n) :
    IsRegularLocalRing (OriginRing R π hπ n) ↔ n = 1 := by
  rw [IsRegularLocalRing.quotient_span_singleton_iff
    (originEquation_isRegular R π hπ n) (originEquation_mem_maximalIdeal R π hπ n hn),
    originEquation_mem_maximalIdeal_sq_iff R π hπ n]
  omega

end OriginLocalRing

/-- If the global node ring is regular, then its local ring at the total-space origin is
regular.  The proof explicitly identifies localization after quotient with quotient after
localization. -/
theorem originRing_isRegularLocalRing_of_isRegularRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n)
    (hreg : IsRegularRing (Ring R π n)) :
    IsRegularLocalRing (OriginRing R π hπ n) := by
  let A := MvPolynomial (Fin 2) R
  let I : Ideal A := relationIdeal R π n
  let m : Ideal A := totalOriginIdeal R π
  have hIm : I ≤ m := by
    change relationIdeal R π n ≤ totalOriginIdeal R π
    rw [relationIdeal, Ideal.span_le]
    rintro z rfl
    exact equation_mem_totalOriginIdeal_of_pos R π n hn
  let : m.IsMaximal := by
    dsimp [m]
    exact totalOriginIdeal_isMaximal_of_irreducible R π hπ
  let q : Ideal (Ring R π n) := m.map (Ideal.Quotient.mk I)
  have hqmax : q.IsMaximal := by
    dsimp [q]
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by
      simpa [I] using hIm)
  let : q.IsPrime := hqmax.isPrime
  let : IsRegularRing (Ring R π n) := hreg
  have hcanon : IsRegularLocalRing (Localization.AtPrime q) := inferInstance
  let S := OriginAmbientRing R π hπ
  let J : Ideal S := I.map (algebraMap A S)
  let T := S ⧸ J
  have hJ : J = Ideal.span {originEquation R π hπ n} := by
    dsimp [J, I, A, S]
    simp [relationIdeal, originEquation, Ideal.map_span]
  have hcomap : q.comap (Ideal.Quotient.mk I) = m := by
    dsimp [q]
    exact Ideal.comap_map_mk hIm
  have hmcompl : m.primeCompl =
      (q.comap (Ideal.Quotient.mk I)).primeCompl := by
    apply SetLike.ext
    intro x
    simp only [Ideal.mem_primeCompl_iff]
    rw [hcomap]
  have hmonoid : Algebra.algebraMapSubmonoid (Ring R π n) m.primeCompl = q.primeCompl := by
    change Submonoid.map (Ideal.Quotient.mk I) m.primeCompl = q.primeCompl
    exact Eq.trans
      (congrArg (Submonoid.map (Ideal.Quotient.mk I)) hmcompl)
      (q.map_primeCompl_comap_of_surjective
        (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective)
  let : Algebra (Ring R π n) T := inferInstance
  have hloc : IsLocalization
      (Algebra.algebraMapSubmonoid (Ring R π n) m.primeCompl) T := inferInstance
  have hloc' : IsLocalization.AtPrime T q := by
    change IsLocalization q.primeCompl T
    rw [← hmonoid]
    exact hloc
  let : IsLocalization.AtPrime T q := hloc'
  let : IsRegularLocalRing (Localization.AtPrime q) := hcanon
  have hregT : IsRegularLocalRing T :=
    @IsRegularLocalRing.of_ringEquiv (Localization.AtPrime q) _ inferInstance T _
      (IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)).toRingEquiv.symm
  let : IsRegularLocalRing T := hregT
  exact @IsRegularLocalRing.of_ringEquiv T _ inferInstance (OriginRing R π hπ n) _
    (Ideal.quotEquivOfEq hJ)

/-- At thickness at least two, the node ring is not regular: its origin local ring has equation
in the square of the ambient maximal ideal. -/
theorem ring_not_isRegularRing_of_two_le
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 2 ≤ n) :
    ¬ IsRegularRing (Ring R π n) := by
  intro hreg
  have hlocal := originRing_isRegularLocalRing_of_isRegularRing R π hπ n (by omega) hreg
  have hn1 := (originRing_isRegularLocalRing_iff R π hπ n (by omega)).mp hlocal
  omega

/-- The total space `R[x,y]/(xy-πⁿ)` is regular exactly for exponent at most one. -/
theorem ring_isRegularRing_iff_le_one
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (n : ℕ) :
    IsRegularRing (Ring R π n) ↔ n ≤ 1 := by
  constructor
  · intro hreg
    by_contra hn
    exact ring_not_isRegularRing_of_two_le R π hπ n (by omega) hreg
  · intro hn
    interval_cases n
    · exact ring_zero_isRegularRing R π
    · exact ring_one_isRegularRing R π hπ

/-- Polynomial division by the monic equation `xy - πⁿ` leaves a remainder supported on
the two coordinate axes. -/
theorem exists_normalForm (R : Type u) [CommRing R] [Nontrivial R]
    (π : R) (n : ℕ) (p : MvPolynomial (Fin 2) R) :
    ∃ q r : MvPolynomial (Fin 2) R,
      p = q * equation R π n + r ∧
        ∀ c ∈ r.support, c 0 = 0 ∨ c 1 = 0 := by
  classical
  obtain ⟨q, r, hp, -, hr⟩ := MonomialOrder.lex.div_single
    (b := equation R π n) (by rw [equation_leadingCoeff]; exact isUnit_one) p
  refine ⟨q, r, hp, ?_⟩
  intro c hc
  have hnot := hr c hc
  rw [equation_degree] at hnot
  by_contra haxes
  push Not at haxes
  apply hnot
  intro i
  fin_cases i
  · simpa [xyExponent] using Nat.one_le_iff_ne_zero.mpr haxes.1
  · simpa [xyExponent] using Nat.one_le_iff_ne_zero.mpr haxes.2

/-- An axis-supported polynomial in the relation ideal is zero. This is the uniqueness half of
the normal-form theorem. -/
theorem eq_zero_of_mem_relationIdeal_of_support_axes
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ)
    (r : MvPolynomial (Fin 2) R)
    (hr : ∀ c ∈ r.support, c 0 = 0 ∨ c 1 = 0)
    (hmem : r ∈ relationIdeal R π n) : r = 0 := by
  classical
  rw [relationIdeal, Ideal.mem_span_singleton'] at hmem
  obtain ⟨q, hq⟩ := hmem
  by_cases hq0 : q = 0
  · simpa [hq0] using hq.symm
  let m : MonomialOrder (Fin 2) := MonomialOrder.lex
  have hleadq : m.leadingCoeff q ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hq0
  have hprod : m.leadingCoeff q * m.leadingCoeff (equation R π n) ≠ 0 := by
    rw [equation_leadingCoeff]
    simpa using hleadq
  have hdegree : m.degree r = m.degree q + xyExponent := by
    rw [← hq, m.degree_mul_of_mul_leadingCoeff_ne_zero hprod, equation_degree]
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz, m.degree_zero] at hdegree
    have hcoord := DFunLike.congr_fun hdegree (0 : Fin 2)
    simp [xyExponent] at hcoord
  have haxes := hr (m.degree r) (m.degree_mem_support hr0)
  rw [hdegree] at haxes
  rcases haxes with haxes | haxes
  · simp [xyExponent] at haxes
  · simp [xyExponent] at haxes

/-- Axis-supported representatives of a quotient class are unique. -/
theorem eq_of_mk_eq_mk_of_support_axes
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ)
    {r s : MvPolynomial (Fin 2) R}
    (hr : ∀ c ∈ r.support, c 0 = 0 ∨ c 1 = 0)
    (hs : ∀ c ∈ s.support, c 0 = 0 ∨ c 1 = 0)
    (h : Ideal.Quotient.mk (relationIdeal R π n) r =
      Ideal.Quotient.mk (relationIdeal R π n) s) : r = s := by
  rw [← sub_eq_zero]
  apply eq_zero_of_mem_relationIdeal_of_support_axes R π n (r - s)
  · intro c hc
    rw [MvPolynomial.mem_support_iff] at hc
    by_cases hrc : MvPolynomial.coeff c r = 0
    · apply hs c
      rw [MvPolynomial.mem_support_iff]
      intro hsc
      apply hc
      simp [hrc, hsc]
    · exact hr c (MvPolynomial.mem_support_iff.mpr hrc)
  · rw [Ideal.Quotient.eq] at h
    exact h

/-- Every quotient class has a unique representative supported on the two coordinate axes. -/
theorem existsUnique_axisRepresentative
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) (z : Ring R π n) :
    ∃! r : MvPolynomial (Fin 2) R,
      (∀ c ∈ r.support, c 0 = 0 ∨ c 1 = 0) ∧
        Ideal.Quotient.mk (relationIdeal R π n) r = z := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨q, r, hp, hr⟩ := exists_normalForm R π n p
  have heq_mem : equation R π n ∈ relationIdeal R π n :=
    Ideal.subset_span (Set.mem_singleton _)
  have hmk : Ideal.Quotient.mk (relationIdeal R π n) p =
      Ideal.Quotient.mk (relationIdeal R π n) r := by
    rw [hp]
    simp only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr heq_mem,
      mul_zero, zero_add]
  refine ⟨r, ⟨hr, hmk.symm⟩, ?_⟩
  intro s hs
  exact eq_of_mk_eq_mk_of_support_axes R π n hs.1 hr (hs.2.trans hmk)

/-- Exponents of the normal-form monomials, namely those lying on at least one coordinate
axis.  The constant monomial occurs only once. -/
def AxisExponent :=
  {c : Fin 2 →₀ ℕ // c 0 = 0 ∨ c 1 = 0}

/-- Embed finitely supported axis coefficients in the ambient multivariate polynomial ring. -/
def axisPolynomialLinearMap (R : Type u) [CommRing R] :
    (AxisExponent →₀ R) →ₗ[R] MvPolynomial (Fin 2) R :=
  (AddMonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap.comp
    (Finsupp.lmapDomain R R (fun c : AxisExponent ↦ c.1))

/-- The linear map from finitely supported axis coefficients to the node algebra. -/
def axisLinearMap (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (AxisExponent →₀ R) →ₗ[R] Ring R π n :=
  (Ideal.Quotient.mkₐ R (relationIdeal R π n)).toLinearMap.comp
    (axisPolynomialLinearMap R)

/-- Distinct axis normal forms define distinct elements of the node algebra. -/
theorem axisLinearMap_injective
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    Function.Injective (axisLinearMap R π n) := by
  let f : AxisExponent ↪ (Fin 2 →₀ ℕ) := ⟨Subtype.val, Subtype.val_injective⟩
  rw [injective_iff_map_eq_zero (axisLinearMap R π n)]
  intro a ha
  change Ideal.Quotient.mk (relationIdeal R π n)
      (axisPolynomialLinearMap R a) = 0 at ha
  rw [Ideal.Quotient.eq_zero_iff_mem] at ha
  have haxes : ∀ c ∈ (axisPolynomialLinearMap R a).support,
      c 0 = 0 ∨ c 1 = 0 := by
    intro c hc
    rw [← MvPolynomial.finsupp_support_eq_support] at hc
    change c ∈ (Finsupp.mapDomain (fun c : AxisExponent ↦ c.1) a).support at hc
    have hcne : Finsupp.mapDomain (fun c : AxisExponent ↦ c.1) a c ≠ 0 :=
      Finsupp.mem_support_iff.mp hc
    obtain ⟨d, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hcne
    exact d.2
  have hz := eq_zero_of_mem_relationIdeal_of_support_axes R π n _ haxes ha
  have hzcoeff := congrArg (AddMonoidAlgebra.coeffLinearEquiv R) hz
  change Finsupp.mapDomain f a = 0 at hzcoeff
  exact Finsupp.mapDomain_injective f.injective hzcoeff

/-- Every element of the node algebra is a linear combination of axis monomials. -/
theorem axisLinearMap_surjective
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    Function.Surjective (axisLinearMap R π n) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨q, r, hp, hr⟩ := exists_normalForm R π n p
  let f : AxisExponent ↪ (Fin 2 →₀ ℕ) := ⟨Subtype.val, Subtype.val_injective⟩
  let rc : (Fin 2 →₀ ℕ) →₀ R := (AddMonoidAlgebra.coeffLinearEquiv R) r
  let a : AxisExponent →₀ R := Finsupp.comapDomain f rc f.injective.injOn
  have hrcsupport : rc.support = r.support := by
    rfl
  have hrsupport : (rc.support : Set (Fin 2 →₀ ℕ)) ⊆ Set.range f := by
    intro c hc
    have hc' : c ∈ r.support := by
      rwa [← hrcsupport]
    exact ⟨⟨c, hr c hc'⟩, rfl⟩
  have hpoly : axisPolynomialLinearMap R a = r := by
    apply (AddMonoidAlgebra.coeffLinearEquiv R).injective
    change Finsupp.mapDomain f a = rc
    exact Finsupp.mapDomain_comapDomain f f.injective rc hrsupport
  refine ⟨a, ?_⟩
  change Ideal.Quotient.mk (relationIdeal R π n)
      (axisPolynomialLinearMap R a) =
        Ideal.Quotient.mk (relationIdeal R π n) p
  rw [hpoly, Ideal.Quotient.eq, hp]
  have hqe : q * equation R π n ∈ relationIdeal R π n :=
    (relationIdeal R π n).mul_mem_left q
      (Ideal.subset_span (Set.mem_singleton _))
  convert (relationIdeal R π n).neg_mem hqe using 1
  ring

/-- The axis normal form is an explicit linear equivalence with a free module. -/
noncomputable def axisLinearEquiv
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    (AxisExponent →₀ R) ≃ₗ[R] Ring R π n :=
  LinearEquiv.ofBijective (axisLinearMap R π n)
    ⟨axisLinearMap_injective R π n, axisLinearMap_surjective R π n⟩

/-- As a module over its coefficient ring, every node algebra is free. -/
instance ring_free (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Module.Free R (Ring R π n) := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
      let _ := h
      exact Module.Free.of_subsingleton' R (Ring R π n)
  | inr h =>
      let _ := h
      exact Module.Free.of_equiv (axisLinearEquiv R π n)

/-- The first coordinate remains nonzero in every nontrivial local-node presentation. -/
theorem x_ne_zero (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    x R π n ≠ 0 := by
  intro h
  have hp : MvPolynomial.X (0 : Fin 2) = (0 : MvPolynomial (Fin 2) R) :=
    eq_of_mk_eq_mk_of_support_axes R π n
      (r := MvPolynomial.X 0) (s := 0) (by
        intro c hc
        simp only [MvPolynomial.support_X, Finset.mem_singleton] at hc
        subst c
        right
        simp)
      (by simp) h
  have := congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1)) hp
  simp at this

/-- The second coordinate remains nonzero in every nontrivial local-node presentation. -/
theorem y_ne_zero (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    y R π n ≠ 0 := by
  intro h
  have hp : MvPolynomial.X (1 : Fin 2) = (0 : MvPolynomial (Fin 2) R) :=
    eq_of_mk_eq_mk_of_support_axes R π n
      (r := MvPolynomial.X 1) (s := 0) (by
        intro c hc
        simp only [MvPolynomial.support_X, Finset.mem_singleton] at hc
        subst c
        left
        simp)
      (by simp) h
  have := congrArg (MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1)) hp
  simp at this

/-- For positive exponent and zero smoothing parameter, the two nonzero coordinates multiply
to zero, so the special-fibre node algebra is not a domain. -/
theorem not_isDomain_zero_parameter (R : Type u) [CommRing R] [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) : ¬ IsDomain (Ring R 0 n) := by
  intro h
  let _ : IsDomain (Ring R 0 n) := h
  exact (mul_ne_zero (x_ne_zero R 0 n) (y_ne_zero R 0 n)) (by
    rw [x_mul_y]
    simp [hn])

/-! ## The two branches of a positive-exponent special fibre -/

/-- Projection to the `x`-axis of the special fibre `xy = 0`. -/
def xBranch (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Ring R 0 n →ₐ[R] R[X] :=
  lift 0 n Polynomial.X 0 (by simp [hn])

@[simp] theorem xBranch_x (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    xBranch R n hn (x R 0 n) = Polynomial.X := by
  apply lift_x

@[simp] theorem xBranch_y (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    xBranch R n hn (y R 0 n) = 0 := by
  apply lift_y

/-- The projection to the `x`-axis is surjective. -/
theorem xBranch_surjective (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (xBranch R n hn) := by
  intro p
  refine ⟨Polynomial.aeval (x R 0 n) p, ?_⟩
  have h := Polynomial.map_aeval_eq_aeval_map (φ := RingHom.id R)
    (ψ := (xBranch R n hn).toRingHom) (by ext; simp) p (x R 0 n)
  change xBranch R n hn (Polynomial.aeval (x R 0 n) p) = _ at h
  simpa using h

/-- Projection to the `y`-axis of the special fibre `xy = 0`. -/
def yBranch (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Ring R 0 n →ₐ[R] R[X] :=
  lift 0 n 0 Polynomial.X (by simp [hn])

@[simp] theorem yBranch_x (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    yBranch R n hn (x R 0 n) = 0 := by
  apply lift_x

@[simp] theorem yBranch_y (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    yBranch R n hn (y R 0 n) = Polynomial.X := by
  apply lift_y

/-- The projection to the `y`-axis is surjective. -/
theorem yBranch_surjective (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (yBranch R n hn) := by
  intro p
  refine ⟨Polynomial.aeval (y R 0 n) p, ?_⟩
  have h := Polynomial.map_aeval_eq_aeval_map (φ := RingHom.id R)
    (ψ := (yBranch R n hn).toRingHom) (by ext; simp) p (y R 0 n)
  change yBranch R n hn (Polynomial.aeval (y R 0 n) p) = _ at h
  simpa using h

/-- The map from the quotient by the `y`-coordinate ideal to the `x`-axis. -/
def xBranchQuotientMap (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    (Ring R 0 n ⧸ Ideal.span {y R 0 n}) →ₐ[R] R[X] :=
  Ideal.Quotient.liftₐ (Ideal.span {y R 0 n}) (xBranch R n hn) (by
    intro z hz
    apply (show Ideal.span {y R 0 n} ≤ RingHom.ker (xBranch R n hn).toRingHom by
      rw [Ideal.span_le]
      rintro _ rfl
      simp) hz)

/-- The inverse candidate sending the affine-line coordinate to `x` modulo `y`. -/
def xAxisQuotientMap (R : Type u) [CommRing R] (n : ℕ) :
    R[X] →ₐ[R] (Ring R 0 n ⧸ Ideal.span {y R 0 n}) :=
  (Ideal.Quotient.mkₐ R (Ideal.span {y R 0 n})).comp
    (Polynomial.aeval (x R 0 n))

theorem xBranchQuotientMap_comp_xAxisQuotientMap
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    (xBranchQuotientMap R n hn).comp (xAxisQuotientMap R n) = AlgHom.id R R[X] := by
  apply Polynomial.algHom_ext
  change xBranch R n hn (Polynomial.aeval (x R 0 n) Polynomial.X) = Polynomial.X
  simp

theorem xAxisQuotientMap_comp_xBranchQuotientMap
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    (xAxisQuotientMap R n).comp (xBranchQuotientMap R n hn) =
      AlgHom.id R (Ring R 0 n ⧸ Ideal.span {y R 0 n}) := by
  apply Ideal.Quotient.algHom_ext R
  apply algHom_ext (R := R) (A := Ring R 0 n ⧸ Ideal.span {y R 0 n}) 0 n
  · change Ideal.Quotient.mk (Ideal.span {y R 0 n})
      (Polynomial.aeval (x R 0 n) (xBranch R n hn (x R 0 n))) =
        Ideal.Quotient.mk (Ideal.span {y R 0 n}) (x R 0 n)
    simp
  · simp [xBranchQuotientMap, xAxisQuotientMap]

/-- Killing `y` in the positive special fibre leaves the polynomial algebra generated by `x`. -/
def xBranchQuotientEquiv (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    (Ring R 0 n ⧸ Ideal.span {y R 0 n}) ≃ₐ[R] R[X] :=
  AlgEquiv.ofAlgHom (xBranchQuotientMap R n hn) (xAxisQuotientMap R n)
    (xBranchQuotientMap_comp_xAxisQuotientMap R n hn)
    (xAxisQuotientMap_comp_xBranchQuotientMap R n hn)

/-- The kernel cutting out the `x`-axis is exactly the ideal generated by `y`. -/
theorem xBranch_ker (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    RingHom.ker (xBranch R n hn).toRingHom = Ideal.span {y R 0 n} := by
  apply le_antisymm
  · intro z hz
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply (xBranchQuotientEquiv R n hn).injective
    change xBranch R n hn z = xBranchQuotientEquiv R n hn 0
    simpa [xBranchQuotientEquiv, xBranchQuotientMap] using hz
  · rw [Ideal.span_le]
    rintro _ rfl
    simp

/-- The map from the quotient by the `x`-coordinate ideal to the `y`-axis. -/
def yBranchQuotientMap (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    (Ring R 0 n ⧸ Ideal.span {x R 0 n}) →ₐ[R] R[X] :=
  Ideal.Quotient.liftₐ (Ideal.span {x R 0 n}) (yBranch R n hn) (by
    intro z hz
    apply (show Ideal.span {x R 0 n} ≤ RingHom.ker (yBranch R n hn).toRingHom by
      rw [Ideal.span_le]
      rintro _ rfl
      simp) hz)

/-- The inverse candidate sending the affine-line coordinate to `y` modulo `x`. -/
def yAxisQuotientMap (R : Type u) [CommRing R] (n : ℕ) :
    R[X] →ₐ[R] (Ring R 0 n ⧸ Ideal.span {x R 0 n}) :=
  (Ideal.Quotient.mkₐ R (Ideal.span {x R 0 n})).comp
    (Polynomial.aeval (y R 0 n))

theorem yBranchQuotientMap_comp_yAxisQuotientMap
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    (yBranchQuotientMap R n hn).comp (yAxisQuotientMap R n) = AlgHom.id R R[X] := by
  apply Polynomial.algHom_ext
  change yBranch R n hn (Polynomial.aeval (y R 0 n) Polynomial.X) = Polynomial.X
  simp

theorem yAxisQuotientMap_comp_yBranchQuotientMap
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    (yAxisQuotientMap R n).comp (yBranchQuotientMap R n hn) =
      AlgHom.id R (Ring R 0 n ⧸ Ideal.span {x R 0 n}) := by
  apply Ideal.Quotient.algHom_ext R
  apply algHom_ext (R := R) (A := Ring R 0 n ⧸ Ideal.span {x R 0 n}) 0 n
  · simp [yBranchQuotientMap, yAxisQuotientMap]
  · change Ideal.Quotient.mk (Ideal.span {x R 0 n})
      (Polynomial.aeval (y R 0 n) (yBranch R n hn (y R 0 n))) =
        Ideal.Quotient.mk (Ideal.span {x R 0 n}) (y R 0 n)
    simp

/-- Killing `x` in the positive special fibre leaves the polynomial algebra generated by `y`. -/
def yBranchQuotientEquiv (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    (Ring R 0 n ⧸ Ideal.span {x R 0 n}) ≃ₐ[R] R[X] :=
  AlgEquiv.ofAlgHom (yBranchQuotientMap R n hn) (yAxisQuotientMap R n)
    (yBranchQuotientMap_comp_yAxisQuotientMap R n hn)
    (yAxisQuotientMap_comp_yBranchQuotientMap R n hn)

/-- The kernel cutting out the `y`-axis is exactly the ideal generated by `x`. -/
theorem yBranch_ker (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    RingHom.ker (yBranch R n hn).toRingHom = Ideal.span {x R 0 n} := by
  apply le_antisymm
  · intro z hz
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply (yBranchQuotientEquiv R n hn).injective
    change yBranch R n hn z = yBranchQuotientEquiv R n hn 0
    simpa [yBranchQuotientEquiv, yBranchQuotientMap] using hz
  · rw [Ideal.span_le]
    rintro _ rfl
    simp

/-- The `x`-axis is a closed affine-line branch of the special fibre. -/
def xBranchSpec (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Spec (.of R[X]) ⟶ Spec (.of (Ring R 0 n)) :=
  Spec.map (CommRingCat.ofHom (xBranch R n hn).toRingHom)

instance xBranchSpec_isClosedImmersion (R : Type u) [CommRing R]
    (n : ℕ) (hn : n ≠ 0) : IsClosedImmersion (xBranchSpec R n hn) := by
  apply IsClosedImmersion.spec_of_surjective
  exact xBranch_surjective R n hn

/-- The `y`-axis is a closed affine-line branch of the special fibre. -/
def yBranchSpec (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Spec (.of R[X]) ⟶ Spec (.of (Ring R 0 n)) :=
  Spec.map (CommRingCat.ofHom (yBranch R n hn).toRingHom)

instance yBranchSpec_isClosedImmersion (R : Type u) [CommRing R]
    (n : ℕ) (hn : n ≠ 0) : IsClosedImmersion (yBranchSpec R n hn) := by
  apply IsClosedImmersion.spec_of_surjective
  exact yBranch_surjective R n hn

/-- The carrier of the `x`-axis is the vanishing locus of `y`. -/
theorem range_xBranchSpec (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Set.range (xBranchSpec R n hn) =
      PrimeSpectrum.zeroLocus (Ideal.span {y R 0 n} : Ideal (Ring R 0 n)) := by
  change Set.range (PrimeSpectrum.comap (xBranch R n hn).toRingHom) = _
  rw [range_comap_of_surjective _ (xBranch R n hn).toRingHom
      (xBranch_surjective R n hn), xBranch_ker]

/-- The carrier of the `y`-axis is the vanishing locus of `x`. -/
theorem range_yBranchSpec (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Set.range (yBranchSpec R n hn) =
      PrimeSpectrum.zeroLocus (Ideal.span {x R 0 n} : Ideal (Ring R 0 n)) := by
  change Set.range (PrimeSpectrum.comap (yBranch R n hn).toRingHom) = _
  rw [range_comap_of_surjective _ (yBranch R n hn).toRingHom
      (yBranch_surjective R n hn), yBranch_ker]

/-- The two quotient maps distinguish the two coordinates. -/
theorem xBranch_ne_yBranch (R : Type u) [CommRing R] [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) : xBranch R n hn ≠ yBranch R n hn := by
  intro h
  have hx := AlgHom.congr_fun h (x R 0 n)
  simp at hx

/-- Over a nontrivial ring the two closed affine-line branches are distinct. -/
theorem xBranchSpec_ne_yBranchSpec (R : Type u) [CommRing R] [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) : xBranchSpec R n hn ≠ yBranchSpec R n hn := by
  intro h
  simp only [xBranchSpec, yBranchSpec] at h
  rw [Spec.map_inj] at h
  apply xBranch_ne_yBranch R n hn
  apply AlgHom.coe_ringHom_injective
  exact congrArg CommRingCat.Hom.hom h

/-- The common origin of the two branches of the special fibre. -/
def nodeOrigin (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Ring R 0 n →ₐ[R] R :=
  lift 0 n 0 0 (by simp [hn])

@[simp] theorem nodeOrigin_x (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    nodeOrigin R n hn (x R 0 n) = 0 := by
  apply lift_x

@[simp] theorem nodeOrigin_y (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    nodeOrigin R n hn (y R 0 n) = 0 := by
  apply lift_y

theorem nodeOrigin_surjective (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (nodeOrigin R n hn) := by
  intro r
  exact ⟨algebraMap R (Ring R 0 n) r, (nodeOrigin R n hn).commutes r⟩

/-- The map from the quotient by both coordinate ideals to the base ring. -/
def nodeOriginQuotientMap (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    (Ring R 0 n ⧸ Ideal.span ({x R 0 n, y R 0 n} : Set (Ring R 0 n))) →ₐ[R] R :=
  Ideal.Quotient.liftₐ (Ideal.span ({x R 0 n, y R 0 n} : Set (Ring R 0 n)))
    (nodeOrigin R n hn) (by
      intro z hz
      change (nodeOrigin R n hn).toRingHom z = 0
      exact (show Ideal.span ({x R 0 n, y R 0 n} : Set (Ring R 0 n)) ≤
          RingHom.ker (nodeOrigin R n hn).toRingHom by
        rw [Ideal.span_le]
        rintro _ (rfl | rfl) <;> simp) hz)

/-- The scalar section into the quotient by both node coordinates. -/
def nodeOriginSection (R : Type u) [CommRing R] (n : ℕ) :
    R →ₐ[R] (Ring R 0 n ⧸ Ideal.span ({x R 0 n, y R 0 n} : Set (Ring R 0 n))) :=
  (Ideal.Quotient.mkₐ R
    (Ideal.span ({x R 0 n, y R 0 n} : Set (Ring R 0 n)))).comp
      (Algebra.ofId R (Ring R 0 n))

theorem nodeOriginQuotientMap_comp_nodeOriginSection
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    (nodeOriginQuotientMap R n hn).comp (nodeOriginSection R n) = AlgHom.id R R := by
  ext

theorem nodeOriginQuotientMap_comp_quotientMk
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    (nodeOriginQuotientMap R n hn).comp
      (Ideal.Quotient.mkₐ R
        (Ideal.span ({x R 0 n, y R 0 n} : Set (Ring R 0 n)))) =
      nodeOrigin R n hn := by
  apply Ideal.Quotient.liftₐ_comp

theorem nodeOriginSection_comp_nodeOriginQuotientMap
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    (nodeOriginSection R n).comp (nodeOriginQuotientMap R n hn) =
      AlgHom.id R
        (Ring R 0 n ⧸ Ideal.span ({x R 0 n, y R 0 n} : Set (Ring R 0 n))) := by
  apply Ideal.Quotient.algHom_ext R
  rw [AlgHom.comp_assoc, nodeOriginQuotientMap_comp_quotientMk, AlgHom.id_comp]
  apply algHom_ext (R := R) (π := (0 : R)) (n := n)
    (A := Ring R 0 n ⧸ Ideal.span ({x R 0 n, y R 0 n} : Set (Ring R 0 n)))
  · simp only [AlgHom.coe_comp, Function.comp_apply, nodeOrigin_x, map_zero,
      Ideal.Quotient.mkₐ_eq_mk]
    symm
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_insert _ _)
  · simp only [AlgHom.coe_comp, Function.comp_apply, nodeOrigin_y, map_zero,
      Ideal.Quotient.mkₐ_eq_mk]
    symm
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Killing both coordinates in the node leaves exactly the scalar ring. -/
def nodeOriginQuotientEquiv (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    (Ring R 0 n ⧸ Ideal.span ({x R 0 n, y R 0 n} : Set (Ring R 0 n))) ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (nodeOriginQuotientMap R n hn) (nodeOriginSection R n)
    (nodeOriginQuotientMap_comp_nodeOriginSection R n hn)
    (nodeOriginSection_comp_nodeOriginQuotientMap R n hn)

/-- The common-origin kernel is exactly the ideal generated by both node coordinates. -/
theorem nodeOrigin_ker (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    RingHom.ker (nodeOrigin R n hn).toRingHom =
      Ideal.span ({x R 0 n, y R 0 n} : Set (Ring R 0 n)) := by
  apply le_antisymm
  · intro z hz
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply (nodeOriginQuotientEquiv R n hn).injective
    change nodeOrigin R n hn z = nodeOriginQuotientEquiv R n hn 0
    simpa [nodeOriginQuotientEquiv, nodeOriginQuotientMap] using hz
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl) <;> simp

/-- Evaluation at the origin of the affine line. -/
def affineLineOrigin (R : Type u) [CommRing R] : R[X] →ₐ[R] R :=
  Polynomial.aeval (R := R) (0 : R)

@[simp] theorem affineLineOrigin_X (R : Type u) [CommRing R] :
    affineLineOrigin R Polynomial.X = 0 := by
  simp [affineLineOrigin]

theorem affineLineOrigin_surjective (R : Type u) [CommRing R] :
    Function.Surjective (affineLineOrigin R) := by
  intro r
  exact ⟨Polynomial.C r, by simp [affineLineOrigin]⟩

theorem xBranch_comp_affineLineOrigin (R : Type u) [CommRing R]
    (n : ℕ) (hn : n ≠ 0) :
    (affineLineOrigin R).comp (xBranch R n hn) = nodeOrigin R n hn := by
  apply algHom_ext 0 n <;> simp

theorem yBranch_comp_affineLineOrigin (R : Type u) [CommRing R]
    (n : ℕ) (hn : n ≠ 0) :
    (affineLineOrigin R).comp (yBranch R n hn) = nodeOrigin R n hn := by
  apply algHom_ext 0 n <;> simp

/-- The common branch origin as a point-valued morphism of affine schemes. -/
def nodeOriginSpec (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Spec (.of R) ⟶ Spec (.of (Ring R 0 n)) :=
  Spec.map (CommRingCat.ofHom (nodeOrigin R n hn).toRingHom)

instance nodeOriginSpec_isClosedImmersion (R : Type u) [CommRing R]
    (n : ℕ) (hn : n ≠ 0) : IsClosedImmersion (nodeOriginSpec R n hn) := by
  apply IsClosedImmersion.spec_of_surjective
  exact nodeOrigin_surjective R n hn

/-- The carrier of the common origin is the simultaneous vanishing locus of `x` and `y`. -/
theorem range_nodeOriginSpec (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Set.range (nodeOriginSpec R n hn) = PrimeSpectrum.zeroLocus
      (Ideal.span ({x R 0 n, y R 0 n} : Set (Ring R 0 n))) := by
  change Set.range (PrimeSpectrum.comap (nodeOrigin R n hn).toRingHom) = _
  rw [range_comap_of_surjective _ (nodeOrigin R n hn).toRingHom
      (nodeOrigin_surjective R n hn), nodeOrigin_ker]

/-- On a positive-exponent special fibre, the relative Jacobian zero locus is exactly the
scheme-theoretic common-origin carrier of the two branches. -/
theorem zeroLocus_relativeJacobianIdeal_zero
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    PrimeSpectrum.zeroLocus (relativeJacobianIdeal R 0 n) =
      Set.range (nodeOriginSpec R n hn) := by
  rw [relativeJacobianIdeal_eq, range_nodeOriginSpec]

/-- The zero section of the affine line. -/
def affineLineOriginSpec (R : Type u) [CommRing R] :
    Spec (.of R) ⟶ Spec (.of R[X]) :=
  Spec.map (CommRingCat.ofHom (affineLineOrigin R).toRingHom)

instance affineLineOriginSpec_isClosedImmersion (R : Type u) [CommRing R] :
    IsClosedImmersion (affineLineOriginSpec R) := by
  apply IsClosedImmersion.spec_of_surjective
  exact affineLineOrigin_surjective R

@[reassoc (attr := simp)]
theorem affineLineOriginSpec_xBranchSpec
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    affineLineOriginSpec R ≫ xBranchSpec R n hn = nodeOriginSpec R n hn := by
  rw [affineLineOriginSpec, xBranchSpec, nodeOriginSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (xBranch_comp_affineLineOrigin R n hn)

@[reassoc (attr := simp)]
theorem affineLineOriginSpec_yBranchSpec
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    affineLineOriginSpec R ≫ yBranchSpec R n hn = nodeOriginSpec R n hn := by
  rw [affineLineOriginSpec, yBranchSpec, nodeOriginSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (yBranch_comp_affineLineOrigin R n hn)

/-- The coordinate-ring map cutting out the `x`-axis. -/
def xBranchRingMap (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    CommRingCat.of (Ring R 0 n) ⟶ CommRingCat.of R[X] :=
  CommRingCat.ofHom (xBranch R n hn).toRingHom

/-- The coordinate-ring map cutting out the `y`-axis. -/
def yBranchRingMap (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    CommRingCat.of (Ring R 0 n) ⟶ CommRingCat.of R[X] :=
  CommRingCat.ofHom (yBranch R n hn).toRingHom

/-- Evaluation at the affine-line origin as a morphism of commutative-ring objects. -/
def affineLineOriginRingMap (R : Type u) [CommRing R] :
    CommRingCat.of R[X] ⟶ CommRingCat.of R :=
  CommRingCat.ofHom (affineLineOrigin R).toRingHom

/-- The two branch quotient rings have pushout equal to their common scalar ring.  This is
the affine coordinate-ring form of scheme-theoretic transverse intersection at the origin. -/
theorem branchRingSquare_isPushout
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    IsPushout (xBranchRingMap R n hn) (yBranchRingMap R n hn)
      (affineLineOriginRingMap R) (affineLineOriginRingMap R) := by
  let w : xBranchRingMap R n hn ≫ affineLineOriginRingMap R =
      yBranchRingMap R n hn ≫ affineLineOriginRingMap R := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom
      ((xBranch_comp_affineLineOrigin R n hn).trans
        (yBranch_comp_affineLineOrigin R n hn).symm)
  refine { w := w, isColimit' := ⟨PushoutCocone.IsColimit.mk w
    (fun s => CommRingCat.ofHom
      (s.inl.hom.comp (algebraMap R R[X]))) ?_ ?_ ?_⟩ }
  · intro s
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simp [affineLineOriginRingMap, affineLineOrigin]
    · have hx := congrArg
        (fun f : CommRingCat.of (Ring R 0 n) ⟶ s.pt => f.hom (x R 0 n))
        s.condition
      simpa [xBranchRingMap, yBranchRingMap, affineLineOriginRingMap,
        affineLineOrigin] using hx.symm
  · intro s
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      have hc := congrArg
        (fun f : CommRingCat.of (Ring R 0 n) ⟶ s.pt =>
          f.hom (algebraMap R (Ring R 0 n) r)) s.condition
      simpa [xBranchRingMap, yBranchRingMap, affineLineOriginRingMap,
        affineLineOrigin] using hc
    · have hy := congrArg
        (fun f : CommRingCat.of (Ring R 0 n) ⟶ s.pt => f.hom (y R 0 n))
        s.condition
      simpa [xBranchRingMap, yBranchRingMap, affineLineOriginRingMap,
        affineLineOrigin] using hy
  · intro s m hm _
    apply CommRingCat.hom_ext
    ext r
    have h := congrArg
      (fun f : CommRingCat.of R[X] ⟶ s.pt => f.hom (Polynomial.C r)) hm
    simpa [affineLineOriginRingMap, affineLineOrigin] using h

/-- Scheme-theoretically, the pullback of the two closed branches is their displayed common
origin `Spec R`. -/
theorem affineLineOrigins_isPullback
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    IsPullback (affineLineOriginSpec R) (affineLineOriginSpec R)
      (xBranchSpec R n hn) (yBranchSpec R n hn) := by
  exact isPullback_SpecMap_of_isPushout
    (xBranchRingMap R n hn) (yBranchRingMap R n hn)
    (affineLineOriginRingMap R) (affineLineOriginRingMap R)
    (branchRingSquare_isPushout R n hn)

set_option backward.isDefEq.respectTransparency false in
/-- The two affine-line branches cover the carrier of every positive-exponent special fibre. -/
theorem range_xBranchSpec_union_range_yBranchSpec
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Set.range (xBranchSpec R n hn) ∪ Set.range (yBranchSpec R n hn) = Set.univ := by
  rw [range_xBranchSpec, range_yBranchSpec]
  ext p
  simp only [Set.mem_univ, iff_true]
  have hxy : x R 0 n * y R 0 n ∈ p.asIdeal := by
    rw [x_mul_y]
    simp [hn]
  rcases p.isPrime.mem_or_mem hxy with hx | hy
  · right
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
      Set.singleton_subset_iff]
    exact hx
  · left
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
      Set.singleton_subset_iff]
    exact hy

set_option backward.isDefEq.respectTransparency false in
/-- The intersection of the two branch carriers is exactly the common-origin carrier. -/
theorem range_xBranchSpec_inter_range_yBranchSpec
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Set.range (xBranchSpec R n hn) ∩ Set.range (yBranchSpec R n hn) =
      Set.range (nodeOriginSpec R n hn) := by
  rw [range_xBranchSpec, range_yBranchSpec, range_nodeOriginSpec]
  change (PrimeSpectrum.zeroLocus
      (Ideal.span {y R 0 n} : Ideal (Ring R 0 n)) ∩
        PrimeSpectrum.zeroLocus (Ideal.span {x R 0 n} : Ideal (Ring R 0 n)) :
      Set (PrimeSpectrum (Ring R 0 n))) =
    PrimeSpectrum.zeroLocus
      (Ideal.span ({x R 0 n, y R 0 n} : Set (Ring R 0 n)))
  ext p
  simp [PrimeSpectrum.mem_zeroLocus, Set.pair_subset_iff, and_comm]

/-- Over a domain, `R[x,y]/(xy - πⁿ)` has no scalar torsion as an `R`-module. -/
instance ring_isTorsionFree (R : Type u) [CommRing R] [IsDomain R]
    (π : R) (n : ℕ) : Module.IsTorsionFree R (Ring R π n) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro a z haz
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨q, r, hp, hr⟩ := exists_normalForm R π n p
  let I := relationIdeal R π n
  have heq_mem : equation R π n ∈ I :=
    Ideal.subset_span (Set.mem_singleton _)
  have hmk : Ideal.Quotient.mk I p = Ideal.Quotient.mk I r := by
    rw [hp]
    simp only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr heq_mem,
      mul_zero, zero_add]
  have har : a • Ideal.Quotient.mk I r = 0 := by
    rw [← hmk]
    exact haz
  have harmem : a • r ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change (Ideal.Quotient.mkₐ R I) (a • r) = 0
    exact (Ideal.Quotient.mkₐ R I).toLinearMap.map_smul a r |>.trans har
  have har_axes : ∀ c ∈ (a • r).support, c 0 = 0 ∨ c 1 = 0 := by
    intro c hc
    apply hr c
    rw [MvPolynomial.mem_support_iff] at hc ⊢
    intro hcoeff
    apply hc
    simp [MvPolynomial.coeff_smul, hcoeff]
  have har_zero : a • r = 0 :=
    eq_zero_of_mem_relationIdeal_of_support_axes R π n (a • r) har_axes harmem
  have hr_zero : r = 0 := by
    ext c
    have hc := congrArg (MvPolynomial.coeff c) har_zero
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_zero, smul_eq_mul] at hc
    exact (mul_eq_zero.mp hc).resolve_left ha
  rw [hmk, hr_zero, map_zero]

/-- For exponent zero the relation is `xy = 1`. -/
@[simp] theorem x_mul_y_zero (R : Type u) [CommRing R] (π : R) :
    x R π 0 * y R π 0 = 1 := by
  simp

/-- At exponent zero, `x` is a unit whose displayed inverse is `y`. -/
def xUnitZero (R : Type u) [CommRing R] (π : R) : (Ring R π 0)ˣ where
  val := x R π 0
  inv := y R π 0
  val_inv := x_mul_y_zero R π
  inv_val := by rw [mul_comm, x_mul_y_zero]

@[simp] theorem xUnitZero_val (R : Type u) [CommRing R] (π : R) :
    (xUnitZero R π : Ring R π 0) = x R π 0 := rfl

@[simp] theorem xUnitZero_inv (R : Type u) [CommRing R] (π : R) :
    ↑((xUnitZero R π)⁻¹) = y R π 0 := rfl

/-- At exponent zero, send `x` and `y` to the Laurent monomials `T` and `T⁻¹`. -/
def toLaurent (R : Type u) [CommRing R] (π : R) :
    Ring R π 0 →ₐ[R] LaurentPolynomial R :=
  lift π 0 (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) (by
    rw [← LaurentPolynomial.T_add]
    norm_num)

@[simp] theorem toLaurent_x (R : Type u) [CommRing R] (π : R) :
    toLaurent R π (x R π 0) = LaurentPolynomial.T 1 := by
  apply lift_x

@[simp] theorem toLaurent_y (R : Type u) [CommRing R] (π : R) :
    toLaurent R π (y R π 0) = LaurentPolynomial.T (-1) := by
  apply lift_y

/-- The Laurent-polynomial map sending `T` to the unit `x`. -/
def fromLaurent (R : Type u) [CommRing R] (π : R) :
    LaurentPolynomial R →ₐ[R] Ring R π 0 where
  toRingHom := LaurentPolynomial.eval₂ (algebraMap R (Ring R π 0)) (xUnitZero R π)
  commutes' r := by
    change LaurentPolynomial.eval₂ (algebraMap R (Ring R π 0)) (xUnitZero R π)
      (LaurentPolynomial.C r) = algebraMap R (Ring R π 0) r
    rw [LaurentPolynomial.eval₂_C]

@[simp] theorem fromLaurent_C (R : Type u) [CommRing R] (π r : R) :
    fromLaurent R π (LaurentPolynomial.C r) = algebraMap R (Ring R π 0) r := by
  change LaurentPolynomial.eval₂ (algebraMap R (Ring R π 0)) (xUnitZero R π)
    (LaurentPolynomial.C r) = algebraMap R (Ring R π 0) r
  rw [LaurentPolynomial.eval₂_C]

@[simp] theorem fromLaurent_T_one (R : Type u) [CommRing R] (π : R) :
    fromLaurent R π (LaurentPolynomial.T 1) = x R π 0 := by
  change LaurentPolynomial.eval₂ (algebraMap R (Ring R π 0)) (xUnitZero R π)
    (LaurentPolynomial.T 1) = x R π 0
  rw [LaurentPolynomial.eval₂_T]
  simp

@[simp] theorem fromLaurent_T_neg_one (R : Type u) [CommRing R] (π : R) :
    fromLaurent R π (LaurentPolynomial.T (-1)) = y R π 0 := by
  change LaurentPolynomial.eval₂ (algebraMap R (Ring R π 0)) (xUnitZero R π)
    (LaurentPolynomial.T (-1)) = y R π 0
  rw [LaurentPolynomial.eval₂_T]
  simp

private theorem toLaurent_comp_fromLaurent (R : Type u) [CommRing R] (π : R) :
    (toLaurent R π).comp (fromLaurent R π) = AlgHom.id R (LaurentPolynomial R) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

private theorem fromLaurent_comp_toLaurent (R : Type u) [CommRing R] (π : R) :
    (fromLaurent R π).comp (toLaurent R π) = AlgHom.id R (Ring R π 0) := by
  apply algHom_ext π 0 <;> simp

/-- The exponent-zero presentation is the Laurent polynomial algebra `R[T,T⁻¹]`. -/
noncomputable def zeroEquivLaurent (R : Type u) [CommRing R] (π : R) :
    Ring R π 0 ≃ₐ[R] LaurentPolynomial R :=
  AlgEquiv.ofAlgHom (toLaurent R π) (fromLaurent R π)
    (toLaurent_comp_fromLaurent R π) (fromLaurent_comp_toLaurent R π)

@[simp] theorem zeroEquivLaurent_x (R : Type u) [CommRing R] (π : R) :
    zeroEquivLaurent R π (x R π 0) = LaurentPolynomial.T 1 := by
  change toLaurent R π (x R π 0) = LaurentPolynomial.T 1
  exact toLaurent_x R π

@[simp] theorem zeroEquivLaurent_y (R : Type u) [CommRing R] (π : R) :
    zeroEquivLaurent R π (y R π 0) = LaurentPolynomial.T (-1) := by
  change toLaurent R π (y R π 0) = LaurentPolynomial.T (-1)
  exact toLaurent_y R π

/-! ## Laurent form when the smoothing parameter is invertible -/

/-- If the smoothing parameter is a unit, `x` is a unit at every exponent. -/
def xUnitOfIsUnit (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    (Ring R π n)ˣ where
  val := x R π n
  inv := algebraMap R (Ring R π n) (↑(hπ.unit ^ n)⁻¹) * y R π n
  val_inv := by
    calc
      x R π n * (algebraMap R (Ring R π n) (↑(hπ.unit ^ n)⁻¹) * y R π n) =
          algebraMap R (Ring R π n) (↑(hπ.unit ^ n)⁻¹) *
            (x R π n * y R π n) := by ac_rfl
      _ = algebraMap R (Ring R π n)
          (↑(hπ.unit ^ n)⁻¹ * π ^ n) := by rw [x_mul_y, map_mul]
      _ = 1 := by
        have hu : (↑(hπ.unit ^ n) : R) = π ^ n := by
          rw [Units.val_pow_eq_pow_val, hπ.unit_spec]
        rw [← hu, Units.inv_mul, map_one]
  inv_val := by
    calc
      (algebraMap R (Ring R π n) (↑(hπ.unit ^ n)⁻¹) * y R π n) * x R π n =
          algebraMap R (Ring R π n) (↑(hπ.unit ^ n)⁻¹) *
            (x R π n * y R π n) := by ac_rfl
      _ = algebraMap R (Ring R π n)
          (↑(hπ.unit ^ n)⁻¹ * π ^ n) := by rw [x_mul_y, map_mul]
      _ = 1 := by
        have hu : (↑(hπ.unit ^ n) : R) = π ^ n := by
          rw [Units.val_pow_eq_pow_val, hπ.unit_spec]
        rw [← hu, Units.inv_mul, map_one]

@[simp] theorem xUnitOfIsUnit_val (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (hπ : IsUnit π) :
    (xUnitOfIsUnit R π n hπ : Ring R π n) = x R π n := rfl

@[simp] theorem xUnitOfIsUnit_inv (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (hπ : IsUnit π) :
    ↑((xUnitOfIsUnit R π n hπ)⁻¹) =
      algebraMap R (Ring R π n) (↑(hπ.unit ^ n)⁻¹) * y R π n := rfl

/-- Over a base where `π` is invertible, send `x` to `T` and `y` to `πⁿT⁻¹`. -/
def toLaurentOfIsUnit (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (_hπ : IsUnit π) : Ring R π n →ₐ[R] LaurentPolynomial R :=
  lift π n (LaurentPolynomial.T 1)
    (LaurentPolynomial.C (π ^ n) * LaurentPolynomial.T (-1)) (by
      rw [mul_comm (LaurentPolynomial.T 1), mul_assoc, ← LaurentPolynomial.T_add]
      norm_num)

@[simp] theorem toLaurentOfIsUnit_x (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (hπ : IsUnit π) :
    toLaurentOfIsUnit R π n hπ (x R π n) = LaurentPolynomial.T 1 := by
  apply lift_x

@[simp] theorem toLaurentOfIsUnit_y (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (hπ : IsUnit π) :
    toLaurentOfIsUnit R π n hπ (y R π n) =
      LaurentPolynomial.C (π ^ n) * LaurentPolynomial.T (-1) := by
  apply lift_y

/-- The inverse Laurent-polynomial map, sending `T` to the unit `x`. -/
def fromLaurentOfIsUnit (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (hπ : IsUnit π) : LaurentPolynomial R →ₐ[R] Ring R π n where
  toRingHom := LaurentPolynomial.eval₂ (algebraMap R (Ring R π n))
    (xUnitOfIsUnit R π n hπ)
  commutes' r := by
    change LaurentPolynomial.eval₂ (algebraMap R (Ring R π n))
      (xUnitOfIsUnit R π n hπ) (LaurentPolynomial.C r) =
        algebraMap R (Ring R π n) r
    rw [LaurentPolynomial.eval₂_C]

@[simp] theorem fromLaurentOfIsUnit_C (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (hπ : IsUnit π) (r : R) :
    fromLaurentOfIsUnit R π n hπ (LaurentPolynomial.C r) =
      algebraMap R (Ring R π n) r := by
  change LaurentPolynomial.eval₂ (algebraMap R (Ring R π n))
    (xUnitOfIsUnit R π n hπ) (LaurentPolynomial.C r) = _
  rw [LaurentPolynomial.eval₂_C]

@[simp] theorem fromLaurentOfIsUnit_T_one (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (hπ : IsUnit π) :
    fromLaurentOfIsUnit R π n hπ (LaurentPolynomial.T 1) = x R π n := by
  change LaurentPolynomial.eval₂ (algebraMap R (Ring R π n))
    (xUnitOfIsUnit R π n hπ) (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T]
  simp

@[simp] theorem fromLaurentOfIsUnit_T_neg_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    fromLaurentOfIsUnit R π n hπ (LaurentPolynomial.T (-1)) =
      algebraMap R (Ring R π n) (↑(hπ.unit ^ n)⁻¹) * y R π n := by
  change LaurentPolynomial.eval₂ (algebraMap R (Ring R π n))
    (xUnitOfIsUnit R π n hπ) (LaurentPolynomial.T (-1)) = _
  rw [LaurentPolynomial.eval₂_T]
  simp

private theorem toLaurentOfIsUnit_comp_fromLaurentOfIsUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    (toLaurentOfIsUnit R π n hπ).comp (fromLaurentOfIsUnit R π n hπ) =
      AlgHom.id R (LaurentPolynomial R) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp [fromLaurentOfIsUnit]

private theorem fromLaurentOfIsUnit_comp_toLaurentOfIsUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    (fromLaurentOfIsUnit R π n hπ).comp (toLaurentOfIsUnit R π n hπ) =
      AlgHom.id R (Ring R π n) := by
  apply algHom_ext π n
  · simp [fromLaurentOfIsUnit]
  · simp only [AlgHom.comp_apply, toLaurentOfIsUnit_y, map_mul,
      fromLaurentOfIsUnit_C, fromLaurentOfIsUnit_T_neg_one, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul]
    have hu : (↑(hπ.unit ^ n) : R) = π ^ n := by
      rw [Units.val_pow_eq_pow_val, hπ.unit_spec]
    rw [← hu, Units.mul_inv, map_one, one_mul]

/-- If `π` is a unit, the node presentation is the Laurent polynomial algebra for every
thickness `n`. -/
noncomputable def unitEquivLaurent (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (hπ : IsUnit π) : Ring R π n ≃ₐ[R] LaurentPolynomial R :=
  AlgEquiv.ofAlgHom (toLaurentOfIsUnit R π n hπ) (fromLaurentOfIsUnit R π n hπ)
    (toLaurentOfIsUnit_comp_fromLaurentOfIsUnit R π n hπ)
    (fromLaurentOfIsUnit_comp_toLaurentOfIsUnit R π n hπ)

@[simp] theorem unitEquivLaurent_x (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (hπ : IsUnit π) :
    unitEquivLaurent R π n hπ (x R π n) = LaurentPolynomial.T 1 := by
  exact toLaurentOfIsUnit_x R π n hπ

@[simp] theorem unitEquivLaurent_y (R : Type u) [CommRing R] (π : R) (n : ℕ)
    (hπ : IsUnit π) :
    unitEquivLaurent R π n hπ (y R π n) =
      LaurentPolynomial.C (π ^ n) * LaurentPolynomial.T (-1) := by
  exact toLaurentOfIsUnit_y R π n hπ

/-! ## Laurent form away from either node coordinate -/

/-- Send the node to the Laurent line by `x ↦ T` and `y ↦ πⁿT⁻¹`.  Unlike the generic-fibre
map, this map does not require `π` to be invertible. -/
def xAwayNodeToLaurent (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ring R π n →ₐ[R] LaurentPolynomial R :=
  lift π n (LaurentPolynomial.T 1)
    (LaurentPolynomial.C (π ^ n) * LaurentPolynomial.T (-1)) (by
      rw [mul_comm (LaurentPolynomial.T 1), mul_assoc, ← LaurentPolynomial.T_add]
      norm_num)

@[simp] theorem xAwayNodeToLaurent_x
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    xAwayNodeToLaurent R π n (x R π n) = LaurentPolynomial.T 1 := by
  apply lift_x

@[simp] theorem xAwayNodeToLaurent_y
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    xAwayNodeToLaurent R π n (y R π n) =
      LaurentPolynomial.C (π ^ n) * LaurentPolynomial.T (-1) := by
  apply lift_y

/-- The induced map from the localization where `x` is invertible to the Laurent line. -/
def xAwayToLaurent (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Localization.Away (x R π n) →ₐ[R] LaurentPolynomial R :=
  IsLocalization.Away.liftAlgHom (f := xAwayNodeToLaurent R π n)
    (x R π n) (by
      rw [xAwayNodeToLaurent_x]
      exact LaurentPolynomial.isUnit_T 1)

@[simp] theorem xAwayToLaurent_algebraMap_x
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    xAwayToLaurent R π n (algebraMap _ _ (x R π n)) =
      LaurentPolynomial.T 1 := by
  simp [xAwayToLaurent, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem xAwayToLaurent_algebraMap_y
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    xAwayToLaurent R π n (algebraMap _ _ (y R π n)) =
      LaurentPolynomial.C (π ^ n) * LaurentPolynomial.T (-1) := by
  simp [xAwayToLaurent, IsLocalization.Away.liftAlgHom_apply]

/-- The canonical unit represented by `x` in its away localization. -/
def xAwayUnit (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (Localization.Away (x R π n))ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (x R π n)).unit

/-- Send `T` to the canonical unit represented by `x`. -/
def laurentToXAway (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    LaurentPolynomial R →ₐ[R] Localization.Away (x R π n) where
  toRingHom := LaurentPolynomial.eval₂ (algebraMap R _) (xAwayUnit R π n)
  commutes' r := by
    change LaurentPolynomial.eval₂ (algebraMap R _)
      (xAwayUnit R π n) (LaurentPolynomial.C r) = _
    rw [LaurentPolynomial.eval₂_C]

@[simp] theorem laurentToXAway_C
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (r : R) :
    laurentToXAway R π n (LaurentPolynomial.C r) = algebraMap R _ r := by
  rw [laurentToXAway]
  exact LaurentPolynomial.eval₂_C _ _ _

@[simp] theorem laurentToXAway_T_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    laurentToXAway R π n (LaurentPolynomial.T 1) =
      algebraMap _ _ (x R π n) := by
  change LaurentPolynomial.eval₂ (algebraMap R _)
      (xAwayUnit R π n) (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  exact (IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (x R π n)) (x R π n)).unit_spec

@[simp] theorem xAwayToLaurent_xAwayUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    xAwayToLaurent R π n (xAwayUnit R π n) = LaurentPolynomial.T 1 := by
  rw [show (xAwayUnit R π n : Localization.Away (x R π n)) =
      algebraMap _ _ (x R π n) from
    (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (x R π n)) (x R π n)).unit_spec]
  exact xAwayToLaurent_algebraMap_x R π n

@[simp] theorem laurentToXAway_T_neg_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    laurentToXAway R π n (LaurentPolynomial.T (-1)) =
      ↑((xAwayUnit R π n)⁻¹) := by
  change LaurentPolynomial.eval₂ (algebraMap R _)
      (xAwayUnit R π n) (LaurentPolynomial.T (-1)) = _
  rw [LaurentPolynomial.eval₂_T, zpow_neg, zpow_one]

private theorem xAwayToLaurent_comp_laurentToXAway
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (xAwayToLaurent R π n).comp (laurentToXAway R π n) =
      AlgHom.id R (LaurentPolynomial R) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

private theorem laurentToXAway_comp_xAwayToLaurent
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (laurentToXAway R π n).comp (xAwayToLaurent R π n) =
      AlgHom.id R (Localization.Away (x R π n)) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (x R π n))
  apply algHom_ext π n
  · change laurentToXAway R π n
      (xAwayToLaurent R π n (algebraMap _ _ (x R π n))) =
        algebraMap _ _ (x R π n)
    rw [xAwayToLaurent_algebraMap_x, laurentToXAway_T_one]
  · change laurentToXAway R π n
      (xAwayToLaurent R π n (algebraMap _ _ (y R π n))) =
        algebraMap _ _ (y R π n)
    rw [xAwayToLaurent_algebraMap_y, map_mul, laurentToXAway_C,
      laurentToXAway_T_neg_one]
    rw [← IsUnit.mul_left_inj (xAwayUnit R π n).isUnit]
    simp only [mul_assoc, Units.inv_mul, mul_one]
    rw [show (xAwayUnit R π n : Localization.Away (x R π n)) =
        algebraMap _ _ (x R π n) from
      (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (x R π n)) (x R π n)).unit_spec]
    rw [mul_comm, ← map_mul, x_mul_y]
    exact IsScalarTower.algebraMap_apply R
      (Ring R π n) (Localization.Away (x R π n)) (π ^ n)

/-- On the principal open where `x` is invertible, the node algebra is exactly the Laurent
polynomial algebra over the original coefficient ring. -/
noncomputable def xAwayEquivLaurent
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Localization.Away (x R π n) ≃ₐ[R] LaurentPolynomial R :=
  AlgEquiv.ofAlgHom (xAwayToLaurent R π n) (laurentToXAway R π n)
    (xAwayToLaurent_comp_laurentToXAway R π n)
    (laurentToXAway_comp_xAwayToLaurent R π n)

/-- Send the node to the Laurent line by `x ↦ πⁿT⁻¹` and `y ↦ T`. -/
def yAwayNodeToLaurent (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ring R π n →ₐ[R] LaurentPolynomial R :=
  lift π n
    (LaurentPolynomial.C (π ^ n) * LaurentPolynomial.T (-1))
    (LaurentPolynomial.T 1) (by
      rw [mul_assoc, ← LaurentPolynomial.T_add]
      norm_num)

@[simp] theorem yAwayNodeToLaurent_x
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    yAwayNodeToLaurent R π n (x R π n) =
      LaurentPolynomial.C (π ^ n) * LaurentPolynomial.T (-1) := by
  apply lift_x

@[simp] theorem yAwayNodeToLaurent_y
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    yAwayNodeToLaurent R π n (y R π n) = LaurentPolynomial.T 1 := by
  apply lift_y

/-- The induced map from the localization where `y` is invertible to the Laurent line. -/
def yAwayToLaurent (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Localization.Away (y R π n) →ₐ[R] LaurentPolynomial R :=
  IsLocalization.Away.liftAlgHom (f := yAwayNodeToLaurent R π n)
    (y R π n) (by
      rw [yAwayNodeToLaurent_y]
      exact LaurentPolynomial.isUnit_T 1)

@[simp] theorem yAwayToLaurent_algebraMap_x
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    yAwayToLaurent R π n (algebraMap _ _ (x R π n)) =
      LaurentPolynomial.C (π ^ n) * LaurentPolynomial.T (-1) := by
  simp [yAwayToLaurent, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem yAwayToLaurent_algebraMap_y
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    yAwayToLaurent R π n (algebraMap _ _ (y R π n)) =
      LaurentPolynomial.T 1 := by
  simp [yAwayToLaurent, IsLocalization.Away.liftAlgHom_apply]

/-- The canonical unit represented by `y` in its away localization. -/
def yAwayUnit (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (Localization.Away (y R π n))ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (y R π n)).unit

/-- Send `T` to the canonical unit represented by `y`. -/
def laurentToYAway (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    LaurentPolynomial R →ₐ[R] Localization.Away (y R π n) where
  toRingHom := LaurentPolynomial.eval₂ (algebraMap R _) (yAwayUnit R π n)
  commutes' r := by
    change LaurentPolynomial.eval₂ (algebraMap R _)
      (yAwayUnit R π n) (LaurentPolynomial.C r) = _
    rw [LaurentPolynomial.eval₂_C]

@[simp] theorem laurentToYAway_C
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (r : R) :
    laurentToYAway R π n (LaurentPolynomial.C r) = algebraMap R _ r := by
  rw [laurentToYAway]
  exact LaurentPolynomial.eval₂_C _ _ _

@[simp] theorem laurentToYAway_T_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    laurentToYAway R π n (LaurentPolynomial.T 1) =
      algebraMap _ _ (y R π n) := by
  change LaurentPolynomial.eval₂ (algebraMap R _)
      (yAwayUnit R π n) (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  exact (IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (y R π n)) (y R π n)).unit_spec

@[simp] theorem yAwayToLaurent_yAwayUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    yAwayToLaurent R π n (yAwayUnit R π n) = LaurentPolynomial.T 1 := by
  rw [show (yAwayUnit R π n : Localization.Away (y R π n)) =
      algebraMap _ _ (y R π n) from
    (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (y R π n)) (y R π n)).unit_spec]
  exact yAwayToLaurent_algebraMap_y R π n

@[simp] theorem laurentToYAway_T_neg_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    laurentToYAway R π n (LaurentPolynomial.T (-1)) =
      ↑((yAwayUnit R π n)⁻¹) := by
  change LaurentPolynomial.eval₂ (algebraMap R _)
      (yAwayUnit R π n) (LaurentPolynomial.T (-1)) = _
  rw [LaurentPolynomial.eval₂_T, zpow_neg, zpow_one]

private theorem yAwayToLaurent_comp_laurentToYAway
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (yAwayToLaurent R π n).comp (laurentToYAway R π n) =
      AlgHom.id R (LaurentPolynomial R) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

private theorem laurentToYAway_comp_yAwayToLaurent
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (laurentToYAway R π n).comp (yAwayToLaurent R π n) =
      AlgHom.id R (Localization.Away (y R π n)) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (y R π n))
  apply algHom_ext π n
  · change laurentToYAway R π n
      (yAwayToLaurent R π n (algebraMap _ _ (x R π n))) =
        algebraMap _ _ (x R π n)
    rw [yAwayToLaurent_algebraMap_x, map_mul, laurentToYAway_C,
      laurentToYAway_T_neg_one]
    rw [← IsUnit.mul_left_inj (yAwayUnit R π n).isUnit]
    simp only [mul_assoc, Units.inv_mul, mul_one]
    rw [show (yAwayUnit R π n : Localization.Away (y R π n)) =
        algebraMap _ _ (y R π n) from
      (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (y R π n)) (y R π n)).unit_spec]
    rw [← map_mul, x_mul_y]
    exact IsScalarTower.algebraMap_apply R
      (Ring R π n) (Localization.Away (y R π n)) (π ^ n)
  · change laurentToYAway R π n
      (yAwayToLaurent R π n (algebraMap _ _ (y R π n))) =
        algebraMap _ _ (y R π n)
    rw [yAwayToLaurent_algebraMap_y, laurentToYAway_T_one]

/-- On the principal open where `y` is invertible, the node algebra is exactly the Laurent
polynomial algebra over the original coefficient ring. -/
noncomputable def yAwayEquivLaurent
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Localization.Away (y R π n) ≃ₐ[R] LaurentPolynomial R :=
  AlgEquiv.ofAlgHom (yAwayToLaurent R π n) (laurentToYAway R π n)
    (yAwayToLaurent_comp_laurentToYAway R π n)
    (laurentToYAway_comp_yAwayToLaurent R π n)

/-- Over a domain, the local-node algebra is itself a domain wherever the smoothing parameter
is invertible. -/
theorem isDomain_of_isUnit (R : Type u) [CommRing R] [IsDomain R]
    (π : R) (n : ℕ) (hπ : IsUnit π) : IsDomain (Ring R π n) := by
  exact (unitEquivLaurent R π n hπ).toRingEquiv.toMulEquiv.isDomain _

/-! ## Dimension over a field -/

/-- The Laurent polynomial ring over a field has Krull dimension at least one.  Evaluation at
`T = 1` exhibits a field quotient whose kernel contains the non-zero-divisor `T - 1`. -/
theorem laurentPolynomial_one_le_ringKrullDim
    (F : Type u) [Field F] : 1 ≤ ringKrullDim (LaurentPolynomial F) := by
  let f : LaurentPolynomial F →+* F :=
    LaurentPolynomial.eval₂ (RingHom.id F) (1 : Fˣ)
  have hf : Function.Surjective f := by
    intro a
    exact ⟨LaurentPolynomial.C a, by simp [f]⟩
  let r : LaurentPolynomial F := LaurentPolynomial.T 1 - 1
  have hr0 : r ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun p : LaurentPolynomial F => p.coeff 0) h
    simp [r] at hcoeff
  have hr : r ∈ nonZeroDivisors (LaurentPolynomial F) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hr0
  have hfr : f r = 0 := by simp [f, r]
  have hdim := ringKrullDim_succ_le_of_surjective f hf hr hfr
  simpa [ringKrullDim_eq_zero_of_field] using hdim

/-- Every node algebra over a field has Krull dimension at most one.  It is a quotient of the
two-variable polynomial ring by the non-zero-divisor `xy - πⁿ`. -/
theorem ringKrullDim_le_one
    (F : Type u) [Field F] (π : F) (n : ℕ) :
    ringKrullDim (Ring F π n) ≤ 1 := by
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr (equation_ne_zero F π n))
  change ringKrullDim (Ring F π n) + 1 ≤
    ringKrullDim (MvPolynomial (Fin 2) F) at h
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field] at h
  rw [← ENat.WithBot.add_le_add_one_right_iff]
  convert h using 1
  norm_num

/-- Every node algebra over a field has Krull dimension at least one.  For a nonzero parameter
it is a Laurent line; for a positive exponent and zero parameter it surjects onto either affine
line branch. -/
theorem one_le_ringKrullDim
    (F : Type u) [Field F] (π : F) (n : ℕ) :
    1 ≤ ringKrullDim (Ring F π n) := by
  cases n with
  | zero =>
      rw [ringKrullDim_eq_of_ringEquiv (zeroEquivLaurent F π).toRingEquiv]
      exact laurentPolynomial_one_le_ringKrullDim F
  | succ n =>
      by_cases hπ : π = 0
      · subst π
        have h := ringKrullDim_le_of_surjective
          (xBranch F (n + 1) (Nat.succ_ne_zero n)).toRingHom
          (xBranch_surjective F (n + 1) (Nat.succ_ne_zero n))
        simpa [Polynomial.ringKrullDim_of_isNoetherianRing,
          ringKrullDim_eq_zero_of_field] using h
      · have hunit : IsUnit π := isUnit_iff_ne_zero.mpr hπ
        rw [ringKrullDim_eq_of_ringEquiv
          (unitEquivLaurent F π (n + 1) hunit).toRingEquiv]
        exact laurentPolynomial_one_le_ringKrullDim F

/-- The affine node `F[x,y]/(xy - πⁿ)` has Krull dimension exactly one for every field `F`,
parameter `π`, and exponent `n`. -/
theorem ringKrullDim_eq_one
    (F : Type u) [Field F] (π : F) (n : ℕ) :
    ringKrullDim (Ring F π n) = 1 :=
  le_antisymm (ringKrullDim_le_one F π n) (one_le_ringKrullDim F π n)

/-! ## Irreducible components over a field -/

/-- The `x` coordinate does not vanish identically on the `x`-axis of a positive special
fibre. -/
theorem x_not_mem_span_y (F : Type u) [Field F] (n : ℕ) (hn : n ≠ 0) :
    x F 0 n ∉ Ideal.span {y F 0 n} := by
  rw [← xBranch_ker F n hn]
  simp

/-- The `y` coordinate does not vanish identically on the `y`-axis of a positive special
fibre. -/
theorem y_not_mem_span_x (F : Type u) [Field F] (n : ℕ) (hn : n ≠ 0) :
    y F 0 n ∉ Ideal.span {x F 0 n} := by
  rw [← yBranch_ker F n hn]
  simp

/-- The two coordinate-axis ideals are exactly the minimal primes of a positive special-fibre
node over a field. -/
theorem minimalPrimes_zero_parameter_eq
    (F : Type u) [Field F] (n : ℕ) (hn : n ≠ 0) :
    minimalPrimes (Ring F 0 n) =
      {Ideal.span {x F 0 n}, Ideal.span {y F 0 n}} := by
  let Ix : Ideal (Ring F 0 n) := Ideal.span {x F 0 n}
  let Iy : Ideal (Ring F 0 n) := Ideal.span {y F 0 n}
  have hIx : Ix.IsPrime := by
    dsimp only [Ix]
    rw [← yBranch_ker F n hn]
    exact RingHom.ker_isPrime _
  have hIy : Iy.IsPrime := by
    dsimp only [Iy]
    rw [← xBranch_ker F n hn]
    exact RingHom.ker_isPrime _
  have hxmin : Ix ∈ minimalPrimes (Ring F 0 n) := by
    rw [minimalPrimes_eq_minimals]
    change Minimal Ideal.IsPrime Ix
    rw [minimal_iff]
    refine ⟨hIx, ?_⟩
    intro J hJ hJIx
    have hxy : x F 0 n * y F 0 n ∈ J := by simp [x_mul_y, hn]
    rcases hJ.mem_or_mem hxy with hx | hy
    · apply le_antisymm
      · change Ideal.span {x F 0 n} ≤ J
        rw [Ideal.span_le]
        simpa using hx
      · exact hJIx
    · exact ((y_not_mem_span_x F n hn) (hJIx hy)).elim
  have hymin : Iy ∈ minimalPrimes (Ring F 0 n) := by
    rw [minimalPrimes_eq_minimals]
    change Minimal Ideal.IsPrime Iy
    rw [minimal_iff]
    refine ⟨hIy, ?_⟩
    intro J hJ hJIy
    have hxy : x F 0 n * y F 0 n ∈ J := by simp [x_mul_y, hn]
    rcases hJ.mem_or_mem hxy with hx | hy
    · exact ((x_not_mem_span_y F n hn) (hJIy hx)).elim
    · apply le_antisymm
      · change Ideal.span {y F 0 n} ≤ J
        rw [Ideal.span_le]
        simpa using hy
      · exact hJIy
  ext I
  constructor
  · intro hI
    rw [minimalPrimes_eq_minimals] at hI
    have hxy : x F 0 n * y F 0 n ∈ I := by simp [x_mul_y, hn]
    rcases hI.prop.mem_or_mem hxy with hx | hy
    · have hle : Ix ≤ I := by
        change Ideal.span {x F 0 n} ≤ I
        rw [Ideal.span_le]
        simpa using hx
      have : I = Ix := (hI.eq_of_le hIx hle).symm
      simp [this, Ix]
    · have hle : Iy ≤ I := by
        change Ideal.span {y F 0 n} ≤ I
        rw [Ideal.span_le]
        simpa using hy
      have : I = Iy := (hI.eq_of_le hIy hle).symm
      simp [this, Iy]
  · intro hI
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hI
    rcases hI with rfl | rfl
    · exact hxmin
    · exact hymin

/-- The two closed affine-line branches are exactly the irreducible components of a positive
special-fibre node over a field. -/
theorem irreducibleComponents_zero_parameter_eq
    (F : Type u) [Field F] (n : ℕ) (hn : n ≠ 0) :
    irreducibleComponents (PrimeSpectrum (Ring F 0 n)) =
      {Set.range (xBranchSpec F n hn), Set.range (yBranchSpec F n hn)} := by
  rw [← PrimeSpectrum.zeroLocus_minimalPrimes,
    minimalPrimes_zero_parameter_eq F n hn,
    range_xBranchSpec, range_yBranchSpec]
  rw [Set.image_pair]
  change
    {PrimeSpectrum.zeroLocus
        (Ideal.span {x F 0 n} : Set (Ring F 0 n)),
      PrimeSpectrum.zeroLocus
        (Ideal.span {y F 0 n} : Set (Ring F 0 n))} = _
  rw [PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_span]
  exact Set.pair_comm _ _

/-- The `x`-axis component of a positive special-fibre node has dimension one. -/
theorem topologicalKrullDim_range_xBranchSpec_eq_one
    (F : Type u) [Field F] (n : ℕ) (hn : n ≠ 0) :
    topologicalKrullDim (Set.range (xBranchSpec F n hn)) = 1 := by
  rw [← (xBranchSpec F n hn).isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq,
    show topologicalKrullDim (Spec (.of F[X])) =
      topologicalKrullDim (PrimeSpectrum F[X]) from rfl,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Polynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field]
  norm_num

/-- The `y`-axis component of a positive special-fibre node has dimension one. -/
theorem topologicalKrullDim_range_yBranchSpec_eq_one
    (F : Type u) [Field F] (n : ℕ) (hn : n ≠ 0) :
    topologicalKrullDim (Set.range (yBranchSpec F n hn)) = 1 := by
  rw [← (yBranchSpec F n hn).isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq,
    show topologicalKrullDim (Spec (.of F[X])) =
      topologicalKrullDim (PrimeSpectrum F[X]) from rfl,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Polynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field]
  norm_num

/-- Every irreducible component of every affine node over a field has topological Krull
dimension one. -/
theorem component_topologicalKrullDim_eq_one
    (F : Type u) [Field F] (π : F) (n : ℕ)
    (Z : Set (PrimeSpectrum (Ring F π n)))
    (hZ : Z ∈ irreducibleComponents (PrimeSpectrum (Ring F π n))) :
    topologicalKrullDim Z = 1 := by
  cases n with
  | zero =>
      let _ : IsDomain (Ring F π 0) :=
        (zeroEquivLaurent F π).toRingEquiv.toMulEquiv.isDomain _
      rw [irreducibleComponents_eq_singleton] at hZ
      simp only [Set.mem_singleton_iff] at hZ
      subst Z
      rw [(Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq,
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
        ringKrullDim_eq_one]
  | succ n =>
      by_cases hπ : π = 0
      · subst π
        rw [irreducibleComponents_zero_parameter_eq F (n + 1)
          (Nat.succ_ne_zero n)] at hZ
        rcases hZ with rfl | rfl
        · exact topologicalKrullDim_range_xBranchSpec_eq_one F (n + 1)
            (Nat.succ_ne_zero n)
        · exact topologicalKrullDim_range_yBranchSpec_eq_one F (n + 1)
            (Nat.succ_ne_zero n)
      · let _ : IsDomain (Ring F π (n + 1)) :=
          isDomain_of_isUnit F π (n + 1) (isUnit_iff_ne_zero.mpr hπ)
        rw [irreducibleComponents_eq_singleton] at hZ
        simp only [Set.mem_singleton_iff] at hZ
        subst Z
        rw [(Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq,
          PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
          ringKrullDim_eq_one]

/-- For exponent one the relation is the standard smoothing equation `xy = π`. -/
@[simp] theorem x_mul_y_one (R : Type u) [CommRing R] (π : R) :
    x R π 1 * y R π 1 = algebraMap R (Ring R π 1) π := by
  simp

/-- The presentation is finitely presented as an `R`-algebra. -/
instance finitePresentation (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Algebra.FinitePresentation R (Ring R π n) := by
  apply Algebra.FinitePresentation.quotient
  rw [relationIdeal]
  exact Submodule.fg_span (Set.finite_singleton _)

/-- The presentation is finite as an `R`-algebra. -/
instance finiteType (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Algebra.FiniteType R (Ring R π n) := by
  infer_instance

/-- Over every commutative coefficient ring, the local-node algebra is flat because its axis
normal form exhibits it as a free module. -/
instance ring_flat (R : Type u) [CommRing R]
    (π : R) (n : ℕ) : Module.Flat R (Ring R π n) := by
  infer_instance

/-- Over every nontrivial commutative base, the node algebra is flat and has its explicit finite
global complete-intersection presentation. -/
instance ring_isGloballySyntomic (R : Type u) [CommRing R] [Nontrivial R]
    (π : R) (n : ℕ) : Algebra.IsGloballySyntomic R (Ring R π n) where

/-- The affine scheme defined by the local-node equation, mapped to its coefficient scheme. -/
def toBaseSpec (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Spec (.of (Ring R π n)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n)))

/-- The relative critical locus `Spec(R/(πⁿ))`, with its structural map to `Spec R`. -/
def relativeCriticalLocusToBase (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Spec (.of (R ⧸ parameterPowerIdeal R π n)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ parameterPowerIdeal R π n)))

/-- The quotient map defining the relative critical locus is surjective. -/
theorem relativeCriticalQuotient_algebraMap_surjective
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Function.Surjective (algebraMap R (R ⧸ parameterPowerIdeal R π n)) :=
  Ideal.Quotient.mk_surjective

/-- The coordinate algebra of the critical locus is formally unramified over `R`. -/
theorem relativeCriticalQuotient_formallyUnramified
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Algebra.FormallyUnramified R (R ⧸ parameterPowerIdeal R π n) := by
  infer_instance

/-- The coordinate algebra of the critical locus is unramified over `R` in Mathlib's affine
ring-theoretic sense: it is formally unramified and of finite type. -/
theorem relativeCriticalQuotient_unramified
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Algebra.Unramified R (R ⧸ parameterPowerIdeal R π n) := by
  refine ⟨relativeCriticalQuotient_formallyUnramified R π n, ?_⟩
  exact Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ R (parameterPowerIdeal R π n))
    (relativeCriticalQuotient_algebraMap_surjective R π n)

/-- The relative critical locus is a closed subscheme of the coefficient scheme. -/
instance relativeCriticalLocusToBase_isClosedImmersion
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    IsClosedImmersion (relativeCriticalLocusToBase R π n) := by
  apply IsClosedImmersion.spec_of_surjective
  exact relativeCriticalQuotient_algebraMap_surjective R π n

/-- The structural morphism of the relative critical locus is unramified. -/
instance relativeCriticalLocusToBase_unramified
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Unramified (relativeCriticalLocusToBase R π n) := by
  rw [relativeCriticalLocusToBase,
    GromovWitten.AlgebraicGeometry.Unramified.SpecMap_algebraMap_iff]
  exact relativeCriticalQuotient_unramified R π n

/-- The two constituent scheme-level properties of the unramified critical-locus map. -/
theorem relativeCriticalLocusToBase_unramified_properties
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    FormallyUnramified (relativeCriticalLocusToBase R π n) ∧
      LocallyOfFiniteType (relativeCriticalLocusToBase R π n) := by
  exact ⟨inferInstance, inferInstance⟩

/-- The diagonal of the critical-locus structural morphism is an open immersion. -/
theorem relativeCriticalLocusToBase_diagonal_isOpenImmersion
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    IsOpenImmersion (pullback.diagonal (relativeCriticalLocusToBase R π n)) := by
  infer_instance

/-- The critical-locus inclusion into the node factors through its structural map exactly as
the quotient map `R → R/(πⁿ)`. -/
@[reassoc (attr := simp)] theorem relativeCriticalLocusSpec_toBaseSpec
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    relativeCriticalLocusSpec R π n ≫ toBaseSpec R π n =
      relativeCriticalLocusToBase R π n := by
  rw [relativeCriticalLocusSpec, toBaseSpec, relativeCriticalLocusToBase,
    ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  exact RingHom.ext fun r => (relativeCriticalPoint R π n).commutes r

/-- The affine line over `R`, with its structural morphism. -/
def affineLineToBaseSpec (R : Type u) [CommRing R] :
    Spec (.of R[X]) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R R[X]))

@[reassoc (attr := simp)]
theorem xBranchSpec_toBaseSpec (R : Type u) [CommRing R]
    (n : ℕ) (hn : n ≠ 0) :
    xBranchSpec R n hn ≫ toBaseSpec R 0 n = affineLineToBaseSpec R := by
  rw [xBranchSpec, toBaseSpec, affineLineToBaseSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  ext r
  simp

@[reassoc (attr := simp)]
theorem yBranchSpec_toBaseSpec (R : Type u) [CommRing R]
    (n : ℕ) (hn : n ≠ 0) :
    yBranchSpec R n hn ≫ toBaseSpec R 0 n = affineLineToBaseSpec R := by
  rw [yBranchSpec, toBaseSpec, affineLineToBaseSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  ext r
  simp

@[reassoc (attr := simp)]
theorem nodeOriginSpec_toBaseSpec (R : Type u) [CommRing R]
    (n : ℕ) (hn : n ≠ 0) :
    nodeOriginSpec R n hn ≫ toBaseSpec R 0 n = 𝟙 (Spec (.of R)) := by
  rw [nodeOriginSpec, toBaseSpec, ← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
  apply CommRingCat.hom_ext
  ext r
  simp

@[reassoc (attr := simp)]
theorem affineLineOriginSpec_toBaseSpec (R : Type u) [CommRing R] :
    affineLineOriginSpec R ≫ affineLineToBaseSpec R = 𝟙 (Spec (.of R)) := by
  rw [affineLineOriginSpec, affineLineToBaseSpec, ← Spec.map_comp, ← Spec.map_id,
    Spec.map_inj]
  apply CommRingCat.hom_ext
  ext r
  simp [affineLineOrigin]

/-- The structural morphism of the local-node presentation is affine. -/
instance toBaseSpec_isAffine (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    IsAffineHom (toBaseSpec R π n) := by
  infer_instance

/-- The structural morphism of the local-node presentation is quasi-compact. -/
instance toBaseSpec_quasiCompact (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    QuasiCompact (toBaseSpec R π n) := by
  infer_instance

/-- The structural morphism of the local-node presentation is flat over every commutative base. -/
instance toBaseSpec_flat (R : Type u) [CommRing R]
    (π : R) (n : ℕ) : Flat (toBaseSpec R π n) := by
  rw [toBaseSpec, Flat.SpecMap_iff]
  change (algebraMap R (Ring R π n)).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The structural morphism is locally of finite presentation, by the displayed one-relation
presentation. -/
instance toBaseSpec_locallyOfFinitePresentation
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    LocallyOfFinitePresentation (toBaseSpec R π n) := by
  rw [toBaseSpec, LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- Over every nontrivial commutative base, the structural morphism of the local-node chart is
syntomic: it is flat and its one-relation presentation is a local complete intersection. -/
instance toBaseSpec_syntomic (R : Type u) [CommRing R] [Nontrivial R]
    (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Syntomic (toBaseSpec R π n) := by
  rw [toBaseSpec]
  exact GromovWitten.AlgebraicGeometry.Syntomic.specMap_algebraMap

end LocalNode

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
