/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import GromovWitten.AlgebraicGeometry.Curves.CartierDivisorDegree

/-!
# Linear-equivalence invariance of the degree for rational functions algebraic over `k` (#141)

`Curves/CartierDivisorDegree.lean` proves, for a nonzero rational function `r` on a regular proper
curve `C` over a field `k`, that the divisors of zeros and of poles of `r` have the same degree
(`degree_divisorOfZeros_eq_degree_divisorOfPoles`), and that this degree is unchanged under adding
`div r` to a formal difference of effective Cartier divisors
(`degree_sum_divisorOfZeros_sub_degree_sum_divisorOfPoles`). Both statements are proved there for
`r` transcendental over `k`, because the concrete divisors `divisorOfZeros`/`divisorOfPoles` are
built from `EffectiveCartierDivisor.ofChartSection`, which needs the domain of definition of `r`
(`Scheme.regularLocus r`) to be an *affine* open, and this affineness is only established
(`IntersectionTheory.ProperCurveDegree.RegularProperCurve.isAffineOpen_regularLocus`) when `r` is
transcendental.

This file treats the complementary case, `r` algebraic over `k`. There `Scheme.regularLocus r` and
`Scheme.regularLocus r⁻¹` are *both* the whole curve
(`IntersectionTheory.ProperCurveDegree.mem_regularLocus_inf_of_monic`), which is generally not
affine, so `divisorOfZeros`/`divisorOfPoles` cannot be built by the same route. But this is exactly
the case where `r` is a unit at *every* point of `C.W`
(`IntersectionTheory.ProperCurveDegree.ord_eq_zero_of_mem_regularLocus_inf`), so its order of
vanishing is identically zero and its "divisor of zeros" and "divisor of poles" both are the empty
(zero) divisor `EffectiveCartierDivisor.empty C.W`: no chart construction is needed at all.

The upshot is that `Curves.CartierDivisorDegree.degree_eq_of_multiplicity_sub_eq_ord` -- the
*abstract* invariance of the degree under the pointwise identity `mult D₀ - mult D₁ = ord r`,
already proved there with no affineness hypothesis whatsoever -- covers both cases uniformly, once
that pointwise hypothesis is discharged: via `multiplicity_divisorOfZeros_sub_divisorOfPoles` in the
transcendental case, and via `multiplicity_empty` together with `ord_eq_zero_of_isAlgebraic` here in
the algebraic case.

## Main declarations

* `ord_eq_zero_of_isAlgebraic` -- **`Scheme.ord r x = 0` at every point of a regular proper curve,
  for `r` algebraic over `k`** (stated with Mathlib's `IsAlgebraic k r`, for the `k`-algebra
  structure `functionFieldAlgebra` on the function field induced by the structure morphism).
* `functionFieldAlgebra` -- the (file-local) `k`-algebra structure on `C.W.functionField` used to
  state `IsAlgebraic k r`; it agrees with the `RationalFunction.kFunctionField C.f`-based
  formulation used throughout `IntersectionTheory.ProperCurveDegree*` (`aeval_eq_eval₂RingHom`).
* `support_empty_eq_empty`, `multiplicity_empty`, `hasFiniteDegree_empty` -- the empty effective
  Cartier divisor `EffectiveCartierDivisor.empty` has empty support, multiplicity `0` everywhere,
  and a (trivially) well-defined degree.
* `degree_sub_invariant_of_linearEquiv` -- **the assembled abstract invariance**: for two effective
  Cartier divisors `D₀`, `D₁` on `C.W` whose multiplicities differ pointwise by `C.W.ord r`, adding
  `D₀` to `E₁` and `D₁` to `E₂` does not change `deg E₁ - deg E₂`. This is exactly
  `Curves.degree_eq_of_multiplicity_sub_eq_ord` combined with additivity of the degree
  (`EffectiveCartierDivisor.degree_add`); it needs no hypothesis on `r` beyond nonzeroness being
  folded into the pointwise identity for `D₀`, `D₁`, and so already covers every nonzero rational
  function once such a pair is exhibited.
* `degree_sub_invariant_of_linearEquiv_of_isAlgebraic` -- the algebraic-case instance of the above,
  with `D₀ = D₁ = EffectiveCartierDivisor.empty C.W`: for `r` algebraic over `k`, adding the empty
  divisor to `E₁`, `E₂` changes nothing, so `deg E₁ - deg E₂` is trivially invariant. Together with
  `Curves.degree_sum_divisorOfZeros_sub_degree_sum_divisorOfPoles` (the `r` transcendental case,
  with `D₀ = divisorOfZeros`, `D₁ = divisorOfPoles`), this shows that
  `degree_sub_invariant_of_linearEquiv` covers **every** nonzero rational function on a regular
  proper curve: the invariance of the degree of a formal difference of effective Cartier divisors
  under linear equivalence.

## Not done

Assembling a single closed statement that also *constructs* the pair `(D₀, D₁)` uniformly (rather
than case-splitting on transcendence) would need an ideal-sheaf construction of the divisor of a
section on a possibly non-affine open; that gap is recorded in `CartierDivisorDegree.lean` and is
not addressed here.
-/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.Curves

variable {k : Type u} [Field k]

/-! ## The order of vanishing of a rational function algebraic over `k` -/

/-- **The `k`-algebra structure on the function field of a regular proper curve** induced by the
structure morphism `C.f`, used only to state `IsAlgebraic k r`/`Transcendental k r` for a rational
function `r : C.W.functionField`. This is the same construction `(RationalFunction.kFunctionField
C.f).hom.toAlgebra` used locally (as a `let`, not an instance) in
`IntersectionTheory.ProperCurveDegreeUnconditional.injective_eval₂_inv`; it is registered as a
file-local instance here so that later statements can be phrased with Mathlib's `IsAlgebraic`. -/
noncomputable local instance functionFieldAlgebra (C : RegularProperCurve k) :
    Algebra k C.W.functionField :=
  (RationalFunction.kFunctionField C.f).hom.toAlgebra

/-- **Mathlib's `aeval` for `functionFieldAlgebra` agrees with the repository's
`Polynomial.eval₂RingHom (RationalFunction.kFunctionField C.f).hom`.** -/
theorem aeval_eq_eval₂RingHom (C : RegularProperCurve k) (r : C.W.functionField)
    (p : Polynomial k) :
    Polynomial.aeval r p =
      Polynomial.eval₂RingHom (RationalFunction.kFunctionField C.f).hom r p := by
  rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]
  rfl

/-- **A rational function algebraic over `k` (Mathlib's `IsAlgebraic`) fails the repository's
transcendence test.** The bridge from Mathlib's `IsAlgebraic`/`Transcendental` API to the
`Function.Injective (Polynomial.eval₂RingHom (kFunctionField f).hom r)` formulation used throughout
`IntersectionTheory.ProperCurveDegree*`. -/
theorem not_injective_eval₂_of_isAlgebraic (C : RegularProperCurve k) {r : C.W.functionField}
    (halg : IsAlgebraic k r) :
    ¬ Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField C.f).hom r) := by
  rw [isAlgebraic_iff_not_injective] at halg
  refine fun hinj => halg (fun p q hpq => hinj ?_)
  rw [← aeval_eq_eval₂RingHom C r p, ← aeval_eq_eval₂RingHom C r q]
  exact hpq

/-- **The order of vanishing of a rational function algebraic over `k` is zero at every point of a
regular proper curve.** `r` is a root of a monic polynomial over `k`
(`exists_monic_of_not_injective`), hence lies in every valuation subring of `C.W` together with its
inverse (`mem_regularLocus_inf_of_monic`), hence is a unit at every point, hence has order of
vanishing zero there (`ord_eq_zero_of_mem_regularLocus_inf`). This is the hypothesis needed to treat
the algebraic case of the invariance of the degree under linear equivalence: `r` contributes the
*empty* divisor of zeros and of poles. -/
theorem ord_eq_zero_of_isAlgebraic (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (halg : IsAlgebraic k r)
    (x : C.W) : C.W.ord r x = 0 := by
  obtain ⟨p, hp, hpr⟩ :=
    IntersectionTheory.ProperCurveDegree.exists_monic_of_not_injective C.f r
      (not_injective_eval₂_of_isAlgebraic C halg)
  exact IntersectionTheory.ProperCurveDegree.ord_eq_zero_of_mem_regularLocus_inf r
    (IntersectionTheory.ProperCurveDegree.mem_regularLocus_inf_of_monic C.f C.valuationRing_stalk
      r p hp hpr x)

/-! ## The empty effective Cartier divisor -/

/-- The support of the empty effective Cartier divisor is empty. -/
theorem support_empty_eq_empty (X : Scheme.{u}) :
    ((EffectiveCartierDivisor.empty X).support : Set X) = ∅ := by
  change ((⊤ : X.IdealSheafData).support : Set X) = ∅
  rw [Scheme.IdealSheafData.support_top]
  simp

/-- The empty effective Cartier divisor has multiplicity zero at every point. -/
theorem multiplicity_empty (X : Scheme.{u}) (x : X) :
    (EffectiveCartierDivisor.empty X).multiplicity x = 0 :=
  EffectiveCartierDivisor.multiplicity_eq_zero_of_notMem_support _ x
    (by rw [support_empty_eq_empty]; exact Set.notMem_empty x)

/-- The empty effective Cartier divisor has a (trivially) well-defined degree. -/
theorem hasFiniteDegree_empty (X : Scheme.{u}) :
    (EffectiveCartierDivisor.empty X).HasFiniteDegree where
  finite_multiplicity x hx :=
    absurd hx (by rw [support_empty_eq_empty]; exact Set.notMem_empty x)
  locallyFinite_support x :=
    ⟨Set.univ, Filter.univ_mem, by
      rw [Set.univ_inter, support_empty_eq_empty]; exact Set.finite_empty⟩

/-! ## The assembled invariance of the degree under linear equivalence -/

/-- **Invariance of the degree of a formal difference of effective Cartier divisors under adding a
pair of divisors `D₀`, `D₁` whose multiplicities differ, pointwise, by the order of vanishing of a
rational function `r`.** This is `degree_eq_of_multiplicity_sub_eq_ord` combined with additivity of
the degree (`EffectiveCartierDivisor.degree_add`): no affineness hypothesis on the domain of
definition of `r`, and no case distinction between `r` transcendental or algebraic over `k`, is
needed at this level of generality. Specialising `D₀ := divisorOfZeros C hr hU₀`,
`D₁ := divisorOfPoles C hr hU₁` (using `multiplicity_divisorOfZeros_sub_divisorOfPoles`) recovers
`degree_sum_divisorOfZeros_sub_degree_sum_divisorOfPoles`, the `r` transcendental case; specialising
`D₀ := D₁ := EffectiveCartierDivisor.empty C.W` (using `ord_eq_zero_of_isAlgebraic`) gives
`degree_sub_invariant_of_linearEquiv_of_isAlgebraic`, the `r` algebraic case. -/
theorem degree_sub_invariant_of_linearEquiv (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] (r : C.W.functionField)
    (D₀ D₁ : EffectiveCartierDivisor C.W) (hD₀ : D₀.HasFiniteDegree) (hD₁ : D₁.HasFiniteDegree)
    (hD : ∀ x : C.W, ((D₀.multiplicity x).toNat : ℤ) - ((D₁.multiplicity x).toNat : ℤ) =
      C.W.ord r x)
    (E₁ E₂ : EffectiveCartierDivisor C.W) (h₁ : E₁.HasFiniteDegree) (h₂ : E₂.HasFiniteDegree) :
    (E₁.sum D₀).degree C.f (h₁.sum hD₀) - (E₂.sum D₁).degree C.f (h₂.sum hD₁) =
      E₁.degree C.f h₁ - E₂.degree C.f h₂ := by
  rw [EffectiveCartierDivisor.degree_add C.f E₁ D₀ h₁ hD₀,
    EffectiveCartierDivisor.degree_add C.f E₂ D₁ h₂ hD₁,
    degree_eq_of_multiplicity_sub_eq_ord C r D₀ D₁ hD₀ hD₁ hD]
  ring

/-- **The algebraic case of `degree_sub_invariant_of_linearEquiv`.** For `r` algebraic over `k`,
adding the empty divisor to `E₁` and to `E₂` does not change `deg E₁ - deg E₂` -- as it must not,
since `div r = 0` identically in this case (`ord_eq_zero_of_isAlgebraic`). Together with
`degree_sum_divisorOfZeros_sub_degree_sum_divisorOfPoles` (the transcendental case), this shows
that the degree of a formal difference of effective Cartier divisors on a regular proper curve is
invariant under linear equivalence for **every** nonzero rational function `r` on the curve. -/
theorem degree_sub_invariant_of_linearEquiv_of_isAlgebraic (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (halg : IsAlgebraic k r)
    (E₁ E₂ : EffectiveCartierDivisor C.W) (h₁ : E₁.HasFiniteDegree) (h₂ : E₂.HasFiniteDegree) :
    (E₁.sum (EffectiveCartierDivisor.empty C.W)).degree C.f
          (h₁.sum (hasFiniteDegree_empty C.W)) -
        (E₂.sum (EffectiveCartierDivisor.empty C.W)).degree C.f
          (h₂.sum (hasFiniteDegree_empty C.W)) =
      E₁.degree C.f h₁ - E₂.degree C.f h₂ :=
  degree_sub_invariant_of_linearEquiv C r _ _ (hasFiniteDegree_empty C.W)
    (hasFiniteDegree_empty C.W)
    (fun x => by
      simp only [multiplicity_empty, ENat.toNat_zero, Nat.cast_zero, sub_zero]
      exact (ord_eq_zero_of_isAlgebraic C halg x).symm)
    E₁ E₂ h₁ h₂

end GromovWitten.AlgebraicGeometry.Curves
