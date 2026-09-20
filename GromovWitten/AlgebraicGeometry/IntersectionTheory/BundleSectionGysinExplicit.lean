/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleSectionGysinIdentity
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyInjective

/-!
# Explicit finite-sum form of the Gysin map of a constant section

The affine theory of the Gysin map `i_c^* : Z(Spec R[T]) → Z(Spec R)` of the constant section
`T = c` is developed in `BundleSectionGysin.lean` and `BundleSectionGysinIdentity.lean`, where
the main identity is stated as a `finsum` over all points of `Spec R[T]` and the conclusion of
the injectivity argument is a *membership* in `totalRationalRelations`.  The globalisation of
that argument to a scheme with a globally trivialised bundle needs the same results in a more
explicit shape: finite sums over the support of a cycle, and each summand displayed as the
divisor of a concrete generator `sectionGenerator c V …` on the base.  This file repackages the
existing results in that form; no new mathematics is proved here.

## Contents

* `VectorBundle.sectionGysin_eq_finsetSum` and `VectorBundle.sectionGysin_apply`: the defining
  `finsum` of `sectionGysin` as a finite sum over the (finite) support of the cycle, and its
  value at a point of the base.
* `VectorBundle.sectionGeneratorDivisor`: the divisor on the base of the generator attached to a
  point `V` of `Spec R[T]` lying on the section and a polynomial `a ∉ V`, extended by zero; it
  is always a rational-equivalence relation (`VectorBundle.sectionGeneratorDivisor_mem`).
* `VectorBundle.support_divisor_sectionPoly`: every point `V` in the support of the divisor of
  `T - c` on `V(P)` satisfies `P < V`, `T - c ∈ V` and, in good position, `a ∉ V`.
* `VectorBundle.sectionGysin_elementGenerator_eq_finsetSum`: the explicit formula
  `i_c^* (div_{V(P)} a) = ∑_{V ∈ S} m_V • (sectionGenerator c V …).divisor dimX`, where `S` is
  the support of the divisor of `T - c` on `V(P)` and `m_V` its multiplicity at `V`.
* `VectorBundle.exists_sectionGysin_generator_eq_sub`: the same for an arbitrary generator of
  the relations on the total space, together with the finite set of proper ideals which the
  translate `T - c` has to avoid for the formula to hold.
* `VectorBundle.subsingleton_badConstants`, `VectorBundle.exists_good_constant` and
  `VectorBundle.exists_good_constant_family`: over an infinite field `k` acting on the
  coefficient rings, a single constant `c ∈ k` can be chosen whose translate `T - c` avoids any
  prescribed finite family of proper ideals, in any finite family of `k`-algebras.
* `VectorBundle.mvSectionGysin` and `VectorBundle.mvSectionGysin_pullbackBundle`: the same Gysin
  map read on `Spec (MvPolynomial PUnit R)`, the shape in which the charts of a globally
  trivialised line bundle present themselves, with the corresponding transport of
  `totalRationalRelations`.

## Hypotheses taken as arguments

As in `BundleSectionGysinIdentity.lean`, the dimension formula for prime quotients of `R[T]` is
carried as the explicit hypothesis
`hdim : ∀ P' : Ideal (Polynomial R), P'.IsPrime → HasDimensionFormula (Polynomial R ⧸ P')`;
it is supplied by `HasUniversalDimensionFormula.polynomial` whenever the universal dimension
formula is available for `R` (e.g. for the sections of a scheme of finite type over a field, by
`hasUniversalDimensionFormula_sections`).  The symmetric local identity `LocalOrdSymmetry` is
*not* a hypothesis: it is discharged with the proved `VectorBundle.localOrdSymmetry`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace VectorBundle

/-! ## The Gysin map as a finite sum -/

section FiniteSum

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (c : R)
  (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))

/-- The Gysin map of the section is a finite sum over the support of the cycle: only the points
of the support contribute to the defining `finsum`. -/
theorem sectionGysin_eq_finsetSum (z : AlgebraicCycle (Spec (CommRingCat.of (Polynomial R))) ℚ) :
    sectionGysin c dimE z =
      ∑ V ∈ (AlgebraicCycle.finite_support z).toFinset,
        (z : ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V • sectionGysinTerm c dimE V := by
  classical
  change (∑ᶠ V, (z : ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V •
    sectionGysinTerm c dimE V) = _
  refine finsum_eq_sum_of_support_subset _ ?_
  intro V hV
  rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
  intro hz
  refine hV ?_
  change (z : ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V • sectionGysinTerm c dimE V = 0
  rw [hz, zero_smul]

/-- The value at a point of the base of the Gysin image of a cycle: the finite sum of the
multiplicities of the cycle times the values of the corresponding Gysin summands. -/
theorem sectionGysin_apply_finsetSum
    (z : AlgebraicCycle (Spec (CommRingCat.of (Polynomial R))) ℚ)
    (x : ↥(Spec (CommRingCat.of R))) :
    (sectionGysin c dimE z : ↥(Spec (CommRingCat.of R)) → ℚ) x =
      ∑ V ∈ (AlgebraicCycle.finite_support z).toFinset,
        (z : ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V *
          (sectionGysinTerm c dimE V : ↥(Spec (CommRingCat.of R)) → ℚ) x := by
  classical
  rw [sectionGysin_eq_finsetSum c dimE z]
  rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun V _ ↦ ?_
  rw [Function.locallyFinsuppWithin.coe_rational_smul]
  simp [smul_eq_mul]

end FiniteSum

/-! ## The generators on the base appearing in the Gysin image -/

section Generators

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (c : R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))

open scoped Classical in
/-- The divisor on the base of the generator attached to a point `V` of `Spec R[T]` which lies
on the section and to a polynomial `a` not vanishing identically on `V(V)`, extended by zero in
all other cases.  This is the total function whose values are the summands of the explicit
Gysin formula `sectionGysin_elementGenerator_eq_finsetSum`. -/
noncomputable def sectionGeneratorDivisor (a : Polynomial R)
    (V : ↥(Spec (CommRingCat.of (Polynomial R)))) : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ :=
  if h : sectionPoly c ∈ (V : PrimeSpectrum (Polynomial R)).asIdeal ∧
      a ∉ (V : PrimeSpectrum (Polynomial R)).asIdeal then
    (@sectionGenerator R _ _ c (V : PrimeSpectrum (Polynomial R)).asIdeal
      (V : PrimeSpectrum (Polynomial R)).isPrime h.1 a h.2).divisor dimX
  else 0

/-- On a point of the section where `a` does not vanish identically, `sectionGeneratorDivisor`
is the divisor of the corresponding generator of the base. -/
theorem sectionGeneratorDivisor_of_mem (a : Polynomial R)
    (V : ↥(Spec (CommRingCat.of (Polynomial R))))
    (hs : sectionPoly c ∈ (V : PrimeSpectrum (Polynomial R)).asIdeal)
    (ha : a ∉ (V : PrimeSpectrum (Polynomial R)).asIdeal) :
    sectionGeneratorDivisor c dimX a V =
      (@sectionGenerator R _ _ c (V : PrimeSpectrum (Polynomial R)).asIdeal
        (V : PrimeSpectrum (Polynomial R)).isPrime hs a ha).divisor dimX := by
  classical
  rw [sectionGeneratorDivisor, dif_pos ⟨hs, ha⟩]

/-- Every value of `sectionGeneratorDivisor` is a rational-equivalence relation on the base:
it is either zero or the divisor of a generator. -/
theorem sectionGeneratorDivisor_mem (a : Polynomial R)
    (V : ↥(Spec (CommRingCat.of (Polynomial R)))) :
    sectionGeneratorDivisor c dimX a V ∈ totalRationalRelations (Spec (CommRingCat.of R)) dimX := by
  classical
  by_cases h : sectionPoly c ∈ (V : PrimeSpectrum (Polynomial R)).asIdeal ∧
      a ∉ (V : PrimeSpectrum (Polynomial R)).asIdeal
  · rw [sectionGeneratorDivisor_of_mem c dimX a V h.1 h.2]
    exact Submodule.subset_span ⟨_, rfl⟩
  · rw [sectionGeneratorDivisor, dif_neg h]
    exact Submodule.zero_mem _

/-- At a point lying on the section, the general Gysin summand of `a` is the divisor of the
corresponding generator on the base (both sides vanish when `a` vanishes identically there). -/
theorem sectionGysinTermOf_eq_sectionGeneratorDivisor (a : Polynomial R)
    (V : ↥(Spec (CommRingCat.of (Polynomial R))))
    (hs : sectionPoly c ∈ (V : PrimeSpectrum (Polynomial R)).asIdeal) :
    sectionGysinTermOf c dimE a V = sectionGeneratorDivisor c dimX a V := by
  classical
  by_cases ha : a ∈ (V : PrimeSpectrum (Polynomial R)).asIdeal
  · rw [sectionGysinTermOf, dif_neg (by simpa using ha), sectionGeneratorDivisor,
      dif_neg (by simp [ha])]
  · rw [sectionGysinTermOf_of_notMem c dimE a V ha,
      sectionGeneratorDivisor_of_mem c dimX a V hs ha,
      @sectionRestrict_elementGenerator_divisor R _ _ c
        (V : PrimeSpectrum (Polynomial R)).asIdeal
        (V : PrimeSpectrum (Polynomial R)).isPrime hs a ha dimX dimE]

end Generators

/-! ## The explicit Gysin image of a principal divisor -/

section Explicit

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (c : R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))

/-- The support of the divisor of `T - c` on a subvariety `V(P)` not contained in the section,
together with the consequence of the good-position hypothesis: every such point is a prime
strictly above `P`, contains `T - c`, and does not contain `a`. -/
theorem support_divisor_sectionPoly (P : Ideal (Polynomial R)) [P.IsPrime]
    (hP : sectionPoly c ∉ P) (a : Polynomial R)
    (hgood : ∀ Q : Ideal (Polynomial R), Q.IsPrime → P < Q → sectionPoly c ∈ Q →
      (∀ Q' : Ideal (Polynomial R), Q'.IsPrime → P ≤ Q' → Q' < Q → sectionPoly c ∉ Q') →
      a ∉ Q)
    (V : ↥(Spec (CommRingCat.of (Polynomial R))))
    (hV : ((elementGenerator P (sectionPoly c) hP).divisor dimE :
      ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V ≠ 0) :
    P < (V : PrimeSpectrum (Polynomial R)).asIdeal ∧
      sectionPoly c ∈ (V : PrimeSpectrum (Polynomial R)).asIdeal ∧
      a ∉ (V : PrimeSpectrum (Polynomial R)).asIdeal := by
  obtain ⟨hlt, hmem, hmin⟩ := divisor_sectionPoly_support c dimE P hP V hV
  exact ⟨hlt, hmem, hgood _ (V : PrimeSpectrum (Polynomial R)).isPrime hlt hmem hmin⟩

/-- **The explicit Gysin image of a principal divisor.**  For `a` in good position with respect
to the section `T = c`, the Gysin image of the divisor of `a` on the subvariety `V(P)` is the
finite sum, over the components `V` of the intersection `V(P) ∩ {T = c}`, of the multiplicity of
`V` in the divisor of `T - c` on `V(P)` times the divisor on the base of the generator
`(V, a mod V)`.  This is `sectionGysin_elementGenerator_eq_finsum` with the `finsum` turned into
a `Finset` sum and each summand identified with a concrete generator of the base. -/
theorem sectionGysin_elementGenerator_eq_finsetSum
    (hdim : ∀ P' : Ideal (Polynomial R), P'.IsPrime → HasDimensionFormula (Polynomial R ⧸ P'))
    (P : Ideal (Polynomial R)) [P.IsPrime] (hP : sectionPoly c ∉ P)
    (a : Polynomial R) (ha : a ∉ P)
    (hgood : ∀ Q : Ideal (Polynomial R), Q.IsPrime → P < Q → sectionPoly c ∈ Q →
      (∀ Q' : Ideal (Polynomial R), Q'.IsPrime → P ≤ Q' → Q' < Q → sectionPoly c ∉ Q') →
      a ∉ Q) :
    sectionGysin c dimE ((elementGenerator P a ha).divisor dimE) =
      ∑ V ∈ (AlgebraicCycle.finite_support
          ((elementGenerator P (sectionPoly c) hP).divisor dimE)).toFinset,
        ((elementGenerator P (sectionPoly c) hP).divisor dimE :
            ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V •
          sectionGeneratorDivisor c dimX a V := by
  classical
  rw [sectionGysin_elementGenerator_eq_finsum localOrdSymmetry hdim c dimE P hP a ha hgood]
  have hsub : (Function.support fun V ↦
      ((elementGenerator P (sectionPoly c) hP).divisor dimE :
        ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V • sectionGysinTermOf c dimE a V) ⊆
      ((AlgebraicCycle.finite_support
        ((elementGenerator P (sectionPoly c) hP).divisor dimE)).toFinset : Set _) := by
    intro V hV
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro hz
    refine hV ?_
    change ((elementGenerator P (sectionPoly c) hP).divisor dimE :
      ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V • sectionGysinTermOf c dimE a V = 0
    rw [hz, zero_smul]
  rw [finsum_eq_sum_of_support_subset _ hsub]
  refine Finset.sum_congr rfl fun V hV ↦ ?_
  have hne : ((elementGenerator P (sectionPoly c) hP).divisor dimE :
      ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V ≠ 0 := by
    have := Set.Finite.mem_toFinset _ |>.1 hV
    exact this
  obtain ⟨-, hs, -⟩ := support_divisor_sectionPoly c dimE P hP a hgood V hne
  rw [sectionGysinTermOf_eq_sectionGeneratorDivisor c dimX dimE a V hs]

/-- **The explicit Gysin image of an arbitrary generator.**  To every generator `g` of the
rational-equivalence relations on the total space is attached a finite set `T` of proper ideals
of `R[T]`, depending only on `g`, such that for every constant `c` whose translate `T - c`
avoids `T` the Gysin image of the divisor of `g` is a difference of two finite rational
combinations of divisors of generators of the base, each of them of the shape
`sectionGenerator c V …` for a prime `V` containing `T - c`.  The set `T` consists of the prime
`P` carrying `g` and of the minimal primes over `P + (a)` and `P + (b)`, where `a`, `b` are the
two polynomials representing the rational function of `g`. -/
theorem exists_sectionGysin_generator_eq_sub
    (hdim : ∀ P' : Ideal (Polynomial R), P'.IsPrime → HasDimensionFormula (Polynomial R ⧸ P'))
    (g : RationalFunctionGenerator (Spec (CommRingCat.of (Polynomial R)))) :
    ∃ T : Set (Ideal (Polynomial R)), T.Finite ∧ (∀ Q ∈ T, Q ≠ ⊤) ∧
      ∀ c : R, (∀ Q ∈ T, sectionPoly c ∉ Q) →
        ∃ (a b : Polynomial R) (S₁ S₂ : Finset ↥(Spec (CommRingCat.of (Polynomial R))))
          (m₁ m₂ : ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ),
          (∀ V ∈ S₁, sectionPoly c ∈ (V : PrimeSpectrum (Polynomial R)).asIdeal ∧
            a ∉ (V : PrimeSpectrum (Polynomial R)).asIdeal) ∧
          (∀ V ∈ S₂, sectionPoly c ∈ (V : PrimeSpectrum (Polynomial R)).asIdeal ∧
            b ∉ (V : PrimeSpectrum (Polynomial R)).asIdeal) ∧
          sectionGysin c dimE (g.divisor dimE) =
            (∑ V ∈ S₁, m₁ V • sectionGeneratorDivisor c dimX a V) -
              ∑ V ∈ S₂, m₂ V • sectionGeneratorDivisor c dimX b V := by
  classical
  obtain ⟨P, hP, a, b, ha, hb, hdivsub⟩ := exists_generator_eq_elementGenerator_sub dimE g
  have _ : P.IsPrime := hP
  refine ⟨insert P ((P ⊔ Ideal.span {a}).minimalPrimes ∪ (P ⊔ Ideal.span {b}).minimalPrimes),
    Set.Finite.insert _ ((Ideal.finite_minimalPrimes_of_isNoetherianRing (Polynomial R) _).union
      (Ideal.finite_minimalPrimes_of_isNoetherianRing (Polynomial R) _)), ?_, ?_⟩
  · rintro Q (rfl | h | h)
    · exact hP.ne_top
    · exact h.isPrime.ne_top
    · exact h.isPrime.ne_top
  · intro c hc
    have hsP : sectionPoly c ∉ P := hc P (Set.mem_insert _ _)
    have hgoodA := hgood_of_avoid c P hsP a ha fun Q hQ ↦
      hc Q (Set.mem_insert_of_mem _ (Or.inl hQ))
    have hgoodB := hgood_of_avoid c P hsP b hb fun Q hQ ↦
      hc Q (Set.mem_insert_of_mem _ (Or.inr hQ))
    refine ⟨a, b, (AlgebraicCycle.finite_support
        ((elementGenerator P (sectionPoly c) hsP).divisor dimE)).toFinset,
      (AlgebraicCycle.finite_support
        ((elementGenerator P (sectionPoly c) hsP).divisor dimE)).toFinset,
      ((elementGenerator P (sectionPoly c) hsP).divisor dimE :
        ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ),
      ((elementGenerator P (sectionPoly c) hsP).divisor dimE :
        ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ), ?_, ?_, ?_⟩
    · intro V hV
      obtain ⟨-, hs, hna⟩ := support_divisor_sectionPoly c dimE P hsP a hgoodA V
        ((Set.Finite.mem_toFinset _).1 hV)
      exact ⟨hs, hna⟩
    · intro V hV
      obtain ⟨-, hs, hnb⟩ := support_divisor_sectionPoly c dimE P hsP b hgoodB V
        ((Set.Finite.mem_toFinset _).1 hV)
      exact ⟨hs, hnb⟩
    · rw [hdivsub, map_sub,
        sectionGysin_elementGenerator_eq_finsetSum c dimX dimE hdim P hsP a ha hgoodA,
        sectionGysin_elementGenerator_eq_finsetSum c dimX dimE hdim P hsP b hb hgoodB]

end Explicit

/-! ## Choosing one constant from an infinite field -/

section Constants

variable {R : Type u} [CommRing R] {k : Type u} [Field k] [Algebra k R]

omit [Algebra k R] in
/-- A proper ideal of `R[T]` contains the translate `T - c` for at most one constant `c` coming
from a field acting on `R`: the difference of two such translates is the image of a nonzero
element of the field, hence a unit. -/
theorem subsingleton_badConstants {A : Type u} [CommRing A] [Algebra k A]
    (Q : Ideal (Polynomial A)) (hQ : Q ≠ ⊤) :
    {c : k | sectionPoly (algebraMap k A c) ∈ Q}.Subsingleton := by
  intro x hx y hy
  by_contra hne
  have h1 : sectionPoly (algebraMap k A x) - sectionPoly (algebraMap k A y) ∈ Q :=
    Q.sub_mem hx hy
  have h2 : sectionPoly (algebraMap k A x) - sectionPoly (algebraMap k A y) =
      Polynomial.C (algebraMap k A (y - x)) := by
    simp only [sectionPoly, map_sub]
    ring
  have hyx : (y - x) ≠ 0 := sub_ne_zero_of_ne fun h ↦ hne h.symm
  have h3 : IsUnit (algebraMap k A (y - x)) := (IsUnit.mk0 (y - x) hyx).map (algebraMap k A)
  rw [h2] at h1
  exact hQ (Q.eq_top_of_isUnit_mem h1 (h3.map Polynomial.C))

omit [Algebra k R] in
/-- Over an infinite field acting on a finite family of rings, one constant `c` gives translates
`T - c` avoiding all the ideals of a prescribed finite family of proper ideals, in each ring of
the family: each ideal excludes at most one value of `c`. -/
theorem exists_good_constant_family [Infinite k] {J : Type*} [Finite J] (A : J → Type u)
    [∀ j, CommRing (A j)] [∀ j, Algebra k (A j)] (T : ∀ j, Set (Ideal (Polynomial (A j))))
    (hTfin : ∀ j, (T j).Finite) (hTne : ∀ j, ∀ Q ∈ T j, Q ≠ ⊤) :
    ∃ c : k, ∀ j, ∀ Q ∈ T j, sectionPoly (algebraMap k (A j) c) ∉ Q := by
  classical
  have hbad : (⋃ j : J, ⋃ Q ∈ T j, {c : k | sectionPoly (algebraMap k (A j) c) ∈ Q}).Finite := by
    refine Set.finite_iUnion fun j ↦ (hTfin j).biUnion fun Q hQ ↦ ?_
    exact Set.Subsingleton.finite (subsingleton_badConstants Q (hTne j Q hQ))
  obtain ⟨c, hc⟩ := (hbad.infinite_compl).nonempty
  refine ⟨c, fun j Q hQ hmem ↦ hc ?_⟩
  exact Set.mem_iUnion.2 ⟨j, Set.mem_biUnion hQ hmem⟩

/-- Over an infinite field acting on `R`, one constant `c ∈ k` gives a translate `T - c` lying
in none of a prescribed finite family of proper ideals of `R[T]`.  This is the field version of
`exists_good_translate`, with the constant chosen in the field rather than in `R`. -/
theorem exists_good_constant [Infinite k] (T : Set (Ideal (Polynomial R))) (hTfin : T.Finite)
    (hTne : ∀ Q ∈ T, Q ≠ ⊤) : ∃ c : k, ∀ Q ∈ T, sectionPoly (algebraMap k R c) ∉ Q := by
  obtain ⟨c, hc⟩ := exists_good_constant_family (k := k) (J := PUnit.{1}) (fun _ ↦ R)
    (fun _ ↦ T) (fun _ ↦ hTfin) fun _ ↦ hTne
  exact ⟨c, hc PUnit.unit⟩

end Constants

/-! ## The Gysin map on the chart `Spec (MvPolynomial PUnit R)` -/

section MvPolynomial

variable {R : Type u} [CommRing R]

/-- The isomorphism `Spec R[T] ⟶ Spec (MvPolynomial PUnit R)` identifying the univariate
polynomial ring with the multivariate polynomial ring on a one-element index type, in which the
charts of a globally trivialised line bundle present themselves. -/
noncomputable abbrev mvSectionSpecMap (R : Type u) [CommRing R] :
    Spec (CommRingCat.of (Polynomial R)) ⟶
      Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} R)) :=
  Spec.map (CommRingCat.ofHom (polyTrivialization R).symm.toRingHom)

variable [IsNoetherianRing R]

/-- The Gysin map of the constant section `T = c`, read on the chart
`Spec (MvPolynomial PUnit R)`: restrict along the identification with `Spec R[T]` and apply
`sectionGysin`. -/
noncomputable def mvSectionGysin (c : R)
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R)))) :
    AlgebraicCycle (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} R))) ℚ →ₗ[ℚ]
      AlgebraicCycle (Spec (CommRingCat.of R)) ℚ :=
  (sectionGysin c dimE).comp (AlgebraicCycle.pullbackOpenLinear (mvSectionSpecMap R))

omit [IsNoetherianRing R] in
/-- The flat pullback of a cycle along the trivial bundle in its `MvPolynomial PUnit` form
restricts, along the identification with `Spec R[T]`, to its univariate form. -/
theorem pullbackOpen_mvSectionSpecMap_pullbackBundle
    (w : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) :
    AlgebraicCycle.pullbackOpen (mvSectionSpecMap R)
        (AlgebraicCycle.pullbackBundle
          (AlgEquiv.refl (R := R) (A₁ := MvPolynomial PUnit.{u + 1} R)) w) =
      AlgebraicCycle.pullbackBundle (polyTrivialization R) w := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  exact (AlgebraicCycle.pullbackBundle_algEquiv (polyTrivialization R).symm
    (AlgEquiv.refl (R := R) (A₁ := MvPolynomial PUnit.{u + 1} R)) (polyTrivialization R) w q).symm

/-- The Gysin map of the constant section is a one-sided inverse of the flat pullback, in the
`MvPolynomial PUnit` form of the trivial line bundle. -/
theorem mvSectionGysin_pullbackBundle (c : R)
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))
    (w : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) :
    mvSectionGysin c dimE (AlgebraicCycle.pullbackBundle
      (AlgEquiv.refl (R := R) (A₁ := MvPolynomial PUnit.{u + 1} R)) w) = w := by
  change sectionGysin c dimE (AlgebraicCycle.pullbackOpen (mvSectionSpecMap R) _) = w
  rw [pullbackOpen_mvSectionSpecMap_pullbackBundle w, sectionGysin_pullbackBundle c dimE w]

omit [IsNoetherianRing R] in
/-- Rational-equivalence relations on the chart `Spec (MvPolynomial PUnit R)` restrict to
rational-equivalence relations on `Spec R[T]` along the identification of the two. -/
theorem pullbackOpen_mvSectionSpecMap_mem
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))
    (dimE' : DimensionFunction (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} R))))
    (z : AlgebraicCycle (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} R))) ℚ)
    (hz : z ∈ totalRationalRelations
      (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} R))) dimE') :
    AlgebraicCycle.pullbackOpen (mvSectionSpecMap R) z ∈
      totalRationalRelations (Spec (CommRingCat.of (Polynomial R))) dimE :=
  totalRationalRelations_pullbackOpen_of_isIso
    (specIsoOfAlgEquiv (polyTrivialization R).symm) dimE dimE' ⟨z, hz, rfl⟩

end MvPolynomial

end VectorBundle

end GromovWitten.AlgebraicGeometry.IntersectionTheory
