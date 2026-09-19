/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackChow
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalizationExact

/-!
# Homotopy invariance for an affine vector bundle: surjectivity of the flat pullback

This file proves Fulton, *Intersection Theory*, Proposition 1.9 for a trivialised affine vector
bundle `π : E = Spec A → X = Spec R` with `A ≃ₐ[R] MvPolynomial ι R`, `ι` finite and `R`
Noetherian: the flat pullback `π^*` is *surjective* on dimension-graded rational Chow groups.
The zero-section Gysin map `0^!` is then the inverse of `π^*`, under the explicit remaining
hypothesis that `π^*` is injective.

## The two hypotheses

* `VectorBundle.RankOneKey` is the rank-one core of the argument (a rational function on
  `π⁻¹(W)` whose principal divisor cuts out a given subvariety `V ⊊ π⁻¹(W)` with multiplicity
  one and is supported over `W`).  It is proved in
  `IntersectionTheory/BundleHomotopyRankOne.lean` as `VectorBundle.exists_rankOne_generator`;
  it is carried here as an explicit hypothesis only so that the two files stay independent.
* `PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE` is homogeneity of principal
  divisors on the *total* space.  It is the same hypothesis under which the localisation
  sequence of `IntersectionTheory/LocalizationExact.lean` is proved, and it is genuinely needed
  in this generality because `totalRationalRelations` is defined without a grading.

## The cycle-level formulation

The index `i + (Nat.card ι : ℤ)` of the target rational-equivalence system occurs in a *type*,
so an induction on the rank cannot be run at the level of Chow groups.  The statement is
therefore first proved at the level of cycles with a free integer rank parameter:

* `VectorBundle.pullbackRange e dimX dimE d` is the submodule of cycles on `E` that are
  rationally equivalent to the flat pullback of a cycle concentrated in dimension `d` on `X`;
* `VectorBundle.BundleSurjective e dimX dimE r` says that every cycle on `E` concentrated in
  some dimension `j` lies in `pullbackRange e dimX dimE (j - r)`.

Three structural lemmas drive the induction:
`VectorBundle.bundleSurjective_of_algEquiv` (invariance under an isomorphism of coordinate
algebras), `VectorBundle.pullbackBundle_tower` (the flat pullback along a tower
`R → R' → A` is the composition of the two flat pullbacks) and
`VectorBundle.baseDimension` (the certified dimension grading of the base read off from that of
the total space, certified by `VectorBundle.coheight_bundlePrime`).  Homogeneity descends along
the bundle by `VectorBundle.principalDivisorsHomogeneous_base`, whose input is
`VectorBundle.exists_generator_pullbackBundle_divisor`: the flat pullback of a principal-divisor
generator is again a principal-divisor generator.

## The induction

* `VectorBundle.bundleSurjective_of_isEmpty`: rank zero, where the projection is an isomorphism.
* `VectorBundle.bundleSurjective_polynomial`: rank one for `A = Polynomial R`, by Noetherian
  induction on the image of the base point of a subvariety (well-foundedness of strict reverse
  inclusion of primes) using `RankOneKey` and homogeneity.
* `VectorBundle.bundleSurjective_of_card`: any finite rank, by induction on `Nat.card ι`, the
  step factoring `MvPolynomial ι R` as `Polynomial (MvPolynomial ι' R)`
  (`MvPolynomial.optionEquivLeft`).

## The results

* `VectorBundle.chowPullbackBundle_surjective`: `π^* : A_i(X) → A_{i+r}(E)` is surjective;
* `VectorBundle.exists_pullback_eq` and `VectorBundle.chowQuotientEquiv`:
  `A_i(X) ⧸ ker π^* ≃ₗ[ℚ] A_{i+r}(E)`;
* `VectorBundle.zeroSectionGysinEquiv`, with `zeroSectionGysinEquiv_pullback`,
  `pullback_zeroSectionGysinEquiv` and `eq_zeroSectionGysinEquiv_of_pullback_eq`: the
  zero-section Gysin map, **under the explicit hypothesis that `π^*` is injective**.
  Injectivity is the other half of homotopy invariance (Fulton, Theorem 3.3(a)); its proof
  needs Chern classes of vector bundles, which this development does not have, so it is not
  attempted here and remains an input.

The name `zeroSectionGysin` is already used in `IntersectionTheory/ChernClasses.lean` for the
rank-zero retraction statement, hence the name `zeroSectionGysinEquiv` here.
-/
open CategoryTheory AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## Single-point cycles and finite support on a quasi-compact scheme -/

namespace AlgebraicCycle

variable {X : Scheme.{u}}

/-- On a quasi-compact scheme the locally finite support of a cycle is finite. -/
theorem finite_support [CompactSpace X] (z : AlgebraicCycle X ℚ) :
    (Function.support (z : X → ℚ)).Finite := by
  have h := Function.locallyFinsupp.locallyFiniteSupport z
  have h2 := h.finite_inter_support_of_isCompact (isCompact_univ (X := X))
  simpa using h2

open scoped Classical in
/-- The rational cycle with coefficient one at a single point and zero elsewhere. -/
noncomputable def singlePoint (x : X) : AlgebraicCycle X ℚ where
  toFun y := if y = x then 1 else 0
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' _ _ := by
    refine ⟨Set.univ, Filter.univ_mem, (Set.finite_singleton x).subset ?_⟩
    rintro y ⟨-, hy⟩
    by_contra hne
    exact hy (if_neg hne)

open scoped Classical in
@[simp]
theorem singlePoint_apply (x y : X) :
    (singlePoint x : X → ℚ) y = if y = x then 1 else 0 :=
  rfl

/-- The coefficient of a single-point cycle at its own point is one. -/
theorem singlePoint_self (x : X) : (singlePoint x : X → ℚ) x = 1 := by
  classical
  simp

/-- A single-point cycle vanishes away from its point. -/
theorem singlePoint_of_ne {x y : X} (h : y ≠ x) : (singlePoint x : X → ℚ) y = 0 := by
  classical
  simp [h]

/-- A cycle on a quasi-compact scheme belongs to any submodule containing the single-point
cycles of the points of its support.  This is the finite decomposition `z = ∑ z(x) • [x]`. -/
theorem mem_of_forall_singlePoint [CompactSpace X] (M : Submodule ℚ (AlgebraicCycle X ℚ))
    (z : AlgebraicCycle X ℚ)
    (h : ∀ x : X, (z : X → ℚ) x ≠ 0 → singlePoint x ∈ M) : z ∈ M := by
  classical
  have hfin := finite_support z
  have hz : z = ∑ x ∈ hfin.toFinset, (z : X → ℚ) x • singlePoint x := by
    apply Function.locallyFinsuppWithin.coe_injective
    funext y
    dsimp only
    rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    have hterm : ∀ x : X,
        (((z : X → ℚ) x • singlePoint x : AlgebraicCycle X ℚ) : X → ℚ) y =
          (z : X → ℚ) x * (if y = x then 1 else 0) := by
      intro x
      rw [Function.locallyFinsuppWithin.coe_rational_smul]
      simp only [Pi.smul_apply, singlePoint_apply, smul_eq_mul]
    simp only [hterm]
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb
      rw [if_neg (fun hcon : y = b ↦ hb hcon.symm), mul_zero]
    · intro hy
      have hzy : (z : X → ℚ) y = 0 := by
        by_contra hne
        exact hy (by simpa using hne)
      rw [hzy, zero_mul]
  rw [hz]
  refine Submodule.sum_mem _ fun x hx ↦ Submodule.smul_mem _ _ (h x ?_)
  simpa using hx

end AlgebraicCycle

namespace VectorBundle

/-! ## The rank-one key lemma, taken as a hypothesis -/

/-- The rank-one key lemma (Fulton, Prop. 1.9 for a trivial line bundle), proved in
`IntersectionTheory/BundleHomotopyRankOne.lean` as `VectorBundle.exists_rankOne_generator`;
taken as an explicit hypothesis here so that the two files can be developed independently. -/
def RankOneKey : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))
    (P : ↥(Spec (CommRingCat.of (Polynomial R))))
    (_hP : P.asIdeal ≠ (P.asIdeal.comap (Polynomial.C : R →+* Polynomial R)).map Polynomial.C),
    ∃ g : RationalFunctionGenerator (Spec (CommRingCat.of (Polynomial R))),
      (∀ x, g.divisor dimE x ≠ 0 →
        P.asIdeal.comap (Polynomial.C : R →+* Polynomial R) ≤ x.asIdeal.comap Polynomial.C) ∧
      g.divisor dimE P = 1 ∧
      ∀ Q, Q ≠ P → Q.asIdeal.comap (Polynomial.C : R →+* Polynomial R) =
          P.asIdeal.comap Polynomial.C → g.divisor dimE Q = 0

/-! ## The cycle-level formulation of surjectivity -/

section Range

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} (e : A ≃ₐ[R] MvPolynomial ι R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of A)))

/-- The cycles on the total space which are rationally equivalent to the flat pullback of a
cycle concentrated in dimension `d` on the base.  Surjectivity of the Chow pullback says that
this submodule contains all cycles of the appropriate dimension. -/
def pullbackRange (d : ℤ) : Submodule ℚ (AlgebraicCycle (Spec (CommRingCat.of A)) ℚ) where
  carrier := {z | ∃ w : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ,
    (∀ x, dimX x ≠ d → (w : _ → ℚ) x = 0) ∧
      z - AlgebraicCycle.pullbackBundle e w ∈
        totalRationalRelations (Spec (CommRingCat.of A)) dimE}
  zero_mem' := by
    refine ⟨0, fun x _ ↦ rfl, ?_⟩
    have h0 : AlgebraicCycle.pullbackBundle e (0 : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ)
        = 0 := map_zero (AlgebraicCycle.pullbackBundleLinear e)
    rw [h0, sub_zero]
    exact Submodule.zero_mem _
  add_mem' := by
    rintro a b ⟨wa, hwa, hra⟩ ⟨wb, hwb, hrb⟩
    refine ⟨wa + wb, ?_, ?_⟩
    · intro x hx
      have : ((wa + wb : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) : _ → ℚ) x =
          (wa : _ → ℚ) x + (wb : _ → ℚ) x := by simp
      rw [this, hwa x hx, hwb x hx, add_zero]
    · have hadd : AlgebraicCycle.pullbackBundle e (wa + wb) =
          AlgebraicCycle.pullbackBundle e wa + AlgebraicCycle.pullbackBundle e wb :=
        AlgebraicCycle.pullbackBundle_add e wa wb
      rw [hadd]
      have : a + b - (AlgebraicCycle.pullbackBundle e wa + AlgebraicCycle.pullbackBundle e wb) =
          (a - AlgebraicCycle.pullbackBundle e wa) + (b - AlgebraicCycle.pullbackBundle e wb) := by
        abel
      rw [this]
      exact Submodule.add_mem _ hra hrb
  smul_mem' := by
    rintro c a ⟨wa, hwa, hra⟩
    refine ⟨c • wa, ?_, ?_⟩
    · intro x hx
      have : ((c • wa : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) : _ → ℚ) x =
          c * (wa : _ → ℚ) x := by
        rw [Function.locallyFinsuppWithin.coe_rational_smul]; rfl
      rw [this, hwa x hx, mul_zero]
    · have hsm : AlgebraicCycle.pullbackBundle e (c • wa) =
          c • AlgebraicCycle.pullbackBundle e wa :=
        AlgebraicCycle.pullbackBundle_smul e c wa
      rw [hsm, ← smul_sub]
      exact Submodule.smul_mem _ c hra

theorem mem_pullbackRange_iff (d : ℤ) (z : AlgebraicCycle (Spec (CommRingCat.of A)) ℚ) :
    z ∈ pullbackRange e dimX dimE d ↔
      ∃ w : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ,
        (∀ x, dimX x ≠ d → (w : _ → ℚ) x = 0) ∧
          z - AlgebraicCycle.pullbackBundle e w ∈
            totalRationalRelations (Spec (CommRingCat.of A)) dimE :=
  Iff.rfl

/-- Surjectivity of the flat pullback at the level of cycles: every cycle on the total space
concentrated in some dimension `j` is rationally equivalent to the pullback of a cycle
concentrated in dimension `j - r` on the base, where `r` is the rank of the bundle. -/
def BundleSurjective (r : ℤ) : Prop :=
  ∀ (j : ℤ) (z : AlgebraicCycle (Spec (CommRingCat.of A)) ℚ),
    (∀ q, dimE q ≠ j → (z : _ → ℚ) q = 0) → z ∈ pullbackRange e dimX dimE (j - r)

end Range

/-! ## Invariance of the cycle-level statement under isomorphism of bundles -/

section Transfer

variable {R : Type u} [CommRing R] {A A' : Type u} [CommRing A] [Algebra R A]
  [CommRing A'] [Algebra R A'] {ι ι' : Type u}

/-- The cycle-level surjectivity statement is invariant under an isomorphism of the coordinate
algebras of two affine vector bundles over the same base. -/
theorem bundleSurjective_of_algEquiv (φ : A ≃ₐ[R] A')
    (e : A ≃ₐ[R] MvPolynomial ι R) (e' : A' ≃ₐ[R] MvPolynomial ι' R)
    (dimX : DimensionFunction (Spec (CommRingCat.of R)))
    (dimE : DimensionFunction (Spec (CommRingCat.of A)))
    (dimE' : DimensionFunction (Spec (CommRingCat.of A'))) (r : ℤ)
    (h : BundleSurjective e dimX dimE r) : BundleSurjective e' dimX dimE' r := by
  intro j z' hz'
  have hiso : IsIso (Spec.map (CommRingCat.ofHom φ.toRingHom)) := isIso_specMap_algEquiv φ
  let ε : Spec (CommRingCat.of A') ≅ Spec (CommRingCat.of A) := specIsoOfAlgEquiv φ
  have hinv : IsIso ε.inv := ⟨ε.hom, ε.inv_hom_id, ε.hom_inv_id⟩
  have hhom : IsIso ε.hom := ⟨ε.inv, ε.hom_inv_id, ε.inv_hom_id⟩
  set z : AlgebraicCycle (Spec (CommRingCat.of A)) ℚ :=
    AlgebraicCycle.pullbackOpen ε.inv z' with hzdef
  have hround : ∀ q : ↥(Spec (CommRingCat.of A')), ε.inv.base (ε.hom.base q) = q := by
    intro q
    change (ε.hom ≫ ε.inv).base q = q
    rw [ε.hom_inv_id]
    rfl
  have hz : ∀ q, dimE q ≠ j → (z : _ → ℚ) q = 0 := by
    intro q hq
    refine hz' (ε.inv.base q) ?_
    rw [← DimensionFunction.apply_eq_of_isClosedImmersion dimE dimE' ε.inv q]
    exact hq
  obtain ⟨w, hw, hrel⟩ := h j z hz
  refine ⟨w, hw, ?_⟩
  have hkey : AlgebraicCycle.pullbackOpen ε.hom
      (z - AlgebraicCycle.pullbackBundle e w) = z' - AlgebraicCycle.pullbackBundle e' w := by
    apply Function.locallyFinsuppWithin.coe_injective
    funext q
    dsimp only
    have h1 : (AlgebraicCycle.pullbackOpen ε.hom
        (z - AlgebraicCycle.pullbackBundle e w) : _ → ℚ) q =
        (z : _ → ℚ) (ε.hom.base q) -
          (AlgebraicCycle.pullbackBundle e w : _ → ℚ) (ε.hom.base q) := by
      simp
    rw [h1]
    have h2 : (z : _ → ℚ) (ε.hom.base q) = (z' : _ → ℚ) q := by
      rw [hzdef]
      change (z' : _ → ℚ) (ε.inv.base (ε.hom.base q)) = _
      rw [hround q]
    have h3 : (AlgebraicCycle.pullbackBundle e' w : _ → ℚ) q =
        (AlgebraicCycle.pullbackBundle e w : _ → ℚ) (ε.hom.base q) :=
      AlgebraicCycle.pullbackBundle_algEquiv φ e e' w q
    rw [h2, ← h3]
    simp
  rw [← hkey]
  exact totalRationalRelations_pullbackOpen_of_isIso ε dimE' dimE
    ⟨z - AlgebraicCycle.pullbackBundle e w, hrel, rfl⟩

end Transfer

/-! ## Composition of bundle pullbacks along a tower -/

section Tower

variable {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
  [Algebra R R'] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
  {ι ι₁ ι₂ : Type u}

/-- The generic point of the preimage of a point of the base computed in two steps along a tower
of trivialised affine vector bundles agrees with the one computed in one step. -/
theorem bundlePrime_tower (e : A ≃ₐ[R] MvPolynomial ι R) (e₁ : A ≃ₐ[R'] MvPolynomial ι₁ R')
    (e₂ : R' ≃ₐ[R] MvPolynomial ι₂ R) (p : PrimeSpectrum R) :
    bundlePrime e₁ (bundlePrime e₂ p) = bundlePrime e p := by
  apply PrimeSpectrum.ext
  change Ideal.map (algebraMap R' A) (Ideal.map (algebraMap R R') p.asIdeal) =
    Ideal.map (algebraMap R A) p.asIdeal
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R R' A]

/-- Flat pullback of cycles along a tower of trivialised affine vector bundles is the composition
of the two flat pullbacks. -/
theorem pullbackBundle_tower (e : A ≃ₐ[R] MvPolynomial ι R) (e₁ : A ≃ₐ[R'] MvPolynomial ι₁ R')
    (e₂ : R' ≃ₐ[R] MvPolynomial ι₂ R) (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) :
    AlgebraicCycle.pullbackBundle e c =
      AlgebraicCycle.pullbackBundle e₁ (AlgebraicCycle.pullbackBundle e₂ c) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  dsimp only
  by_cases hq : q ∈ Set.range (bundlePoint e)
  · obtain ⟨p, rfl⟩ := hq
    have hb : bundlePoint e p = bundlePoint e₁ (bundlePoint e₂ p) :=
      (bundlePrime_tower e e₁ e₂ p).symm
    rw [AlgebraicCycle.pullbackBundle_apply_bundlePoint, hb,
      AlgebraicCycle.pullbackBundle_apply_bundlePoint,
      AlgebraicCycle.pullbackBundle_apply_bundlePoint]
  · rw [AlgebraicCycle.pullbackBundle_eq_zero_of_notMem e c hq]
    by_cases hq1 : q ∈ Set.range (bundlePoint e₁)
    · obtain ⟨y, rfl⟩ := hq1
      rw [AlgebraicCycle.pullbackBundle_apply_bundlePoint]
      by_cases hq2 : y ∈ Set.range (bundlePoint e₂)
      · obtain ⟨p, rfl⟩ := hq2
        exact absurd ⟨p, (bundlePrime_tower e e₁ e₂ p).symm⟩ hq
      · exact (AlgebraicCycle.pullbackBundle_eq_zero_of_notMem e₂ c hq2).symm
    · rw [AlgebraicCycle.pullbackBundle_eq_zero_of_notMem e₁ _ hq1]

end Tower

/-! ## The dimension grading of the base induced by that of the total space -/

section BaseDimension

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} [Finite ι] (e : A ≃ₐ[R] MvPolynomial ι R)
  (dimE : DimensionFunction (Spec (CommRingCat.of A)))

/-- The certified dimension grading of the base of a trivialised affine vector bundle, obtained
from that of the total space by subtracting the rank.  Its certificate is the proved dimension
formula `VectorBundle.coheight_bundlePrime`. -/
noncomputable def baseDimension : DimensionFunction (Spec (CommRingCat.of R)) where
  toFun x := dimE (bundlePoint e x) - (Nat.card ι : ℤ)
  nonnegative x := by
    have h1 : Order.coheight (bundlePrime e x) =
        Order.coheight (show PrimeSpectrum R from x) + (Nat.card ι : ℕ∞) :=
      coheight_bundlePrime e x
    have h2 : Order.coheight (bundlePrime e x) =
        (Int.toNat (dimE (bundlePoint e x)) : ℕ∞) :=
      coheight_eq_dimension A dimE (bundlePrime e x)
    rw [h2] at h1
    have h3 : (Nat.card ι : ℕ∞) ≤ (Int.toNat (dimE (bundlePoint e x)) : ℕ∞) := by
      rw [h1]; exact le_add_self
    have h4 : Nat.card ι ≤ Int.toNat (dimE (bundlePoint e x)) := by exact_mod_cast h3
    have h5 := dimE.nonnegative (bundlePoint e x)
    change 0 ≤ dimE.toFun (bundlePoint e x) - (Nat.card ι : ℤ)
    omega
  height_eq x := by
    have h0 : Order.height (show ↥(Spec (CommRingCat.of R)) from x) =
        Order.coheight (show PrimeSpectrum R from x) := (coheight_eq_height R x).symm
    have h1 : Order.coheight (bundlePrime e x) =
        Order.coheight (show PrimeSpectrum R from x) + (Nat.card ι : ℕ∞) :=
      coheight_bundlePrime e x
    have h2 : Order.coheight (bundlePrime e x) =
        (Int.toNat (dimE (bundlePoint e x)) : ℕ∞) :=
      coheight_eq_dimension A dimE (bundlePrime e x)
    rw [h2] at h1
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Order.coheight (show PrimeSpectrum R from x) = (k : ℕ∞) := by
      refine (ENat.ne_top_iff_exists.1 ?_).imp fun k hk ↦ hk.symm
      intro htop
      rw [htop, top_add] at h1
      exact ENat.natCast_ne_top _ h1
    rw [hk] at h1
    have h6 : Int.toNat (dimE (bundlePoint e x)) = k + Nat.card ι := by exact_mod_cast h1
    have h7 := dimE.nonnegative (bundlePoint e x)
    rw [h0, hk]
    have h8 : Int.toNat (dimE.toFun (bundlePoint e x) - (Nat.card ι : ℤ)) = k := by
      omega
    rw [h8]

@[simp]
theorem baseDimension_apply (x : ↥(Spec (CommRingCat.of R))) :
    baseDimension e dimE x = dimE (bundlePoint e x) - (Nat.card ι : ℤ) :=
  rfl

end BaseDimension

/-! ## Homogeneity of principal divisors descends along the bundle -/

section Homogeneity

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} [Finite ι] (e : A ≃ₐ[R] MvPolynomial ι R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of A)))

/-- The flat pullback along an affine vector bundle of the principal divisor of a rational
function on an integral closed subscheme of the base is again an actual principal divisor on the
total space, namely that of the pulled-back function on the preimage subvariety. -/
theorem exists_generator_pullbackBundle_divisor
    (g : RationalFunctionGenerator (Spec (CommRingCat.of R))) :
    ∃ g' : RationalFunctionGenerator (Spec (CommRingCat.of A)),
      AlgebraicCycle.pullbackBundle e (g.divisor dimX) = g'.divisor dimE := by
  obtain ⟨p, εiso, hfac⟩ :=
    _root_.AlgebraicGeometry.IsClosedImmersion.Spec_iff.1 g.subspace.isClosedImmersion
  have hint : _root_.AlgebraicGeometry.IsIntegral (Spec (CommRingCat.of (R ⧸ p))) :=
    _root_.AlgebraicGeometry.IsIntegral.of_isIso εiso.hom
  have hdom : IsDomain (R ⧸ p) :=
    (_root_.AlgebraicGeometry.affine_isIntegral_iff (CommRingCat.of (R ⧸ p))).1 hint
  have hp : p.IsPrime := (Ideal.Quotient.isDomain_iff_prime p).1 hdom
  have hdominant :
      _root_.AlgebraicGeometry.IsDominant
        (GradedCone.projection (R ⧸ p) (MvPolynomial ι (R ⧸ p))) :=
    isDominant_projection (quotTrivialization ι p)
  set f' : (Spec (CommRingCat.of (R ⧸ p))).functionFieldˣ :=
    Units.map (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap εiso.inv).toMonoidHom
      g.function with hf'
  have h1 : g.divisor dimX =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (εiso.hom ≫ quotImmersion p)
        (fun x ↦ (dimX : _ → ℤ) ((εiso.hom ≫ quotImmersion p).base x)) (dimX : _ → ℤ)
        (g.subspace.scheme.principalCycle (g.function : _)) :=
    AlgebraicCycle.map_congr_hom hfac (dimX : _ → ℤ) _
  have h2 := AlgebraicCycle.map_comp_of_isClosedImmersion εiso.hom (quotImmersion p)
    ((DimensionFunction.comapClosedImmersion (quotImmersion p) dimX : _ → ℤ))
    (dimX : _ → ℤ) (g.subspace.scheme.principalCycle (g.function : _))
  have h3 := map_isIso_principalCycle εiso
    (DimensionFunction.comapClosedImmersion (quotImmersion p) dimX)
    (g.function : g.subspace.scheme.functionField)
  rw [h3] at h2
  have h4 : g.divisor dimX =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (quotImmersion p)
        (fun z ↦ (dimX : _ → ℤ) ((quotImmersion p).base z)) (dimX : _ → ℤ)
        ((Spec (CommRingCat.of (R ⧸ p))).principalCycle (f' : _)) := h1.trans h2.symm
  have h5 := pullbackBundle_map_quotImmersion e p (dimX : _ → ℤ) (dimE : _ → ℤ)
    ((Spec (CommRingCat.of (R ⧸ p))).principalCycle (f' : _))
  have h6 := pullbackBundle_principalCycle (quotTrivialization ι p) (f' : _)
  rw [h6] at h5
  refine ⟨⟨{ scheme := Spec (CommRingCat.of (MvPolynomial ι (R ⧸ p)))
             inclusion := quotBundleImmersion e p },
      Units.map (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap
        (GradedCone.projection (R ⧸ p) (MvPolynomial ι (R ⧸ p)))).toMonoidHom f'⟩, ?_⟩
  rw [h4, h5]
  rfl

include e in
/-- Homogeneity of principal divisors descends from the total space of a trivialised affine
vector bundle to its base: the pullback of a principal divisor is a principal divisor, and the
pullback shifts every dimension by the rank. -/
theorem principalDivisorsHomogeneous_base
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE) :
    PrincipalDivisorsHomogeneous (Spec (CommRingCat.of R)) dimX := by
  intro g
  obtain ⟨g', hg'⟩ := exists_generator_pullbackBundle_divisor e dimX dimE g
  obtain ⟨d, hd⟩ := hhom g'
  refine ⟨d - (Nat.card ι : ℤ), ?_⟩
  intro x hx
  have hval : g'.divisor dimE (bundlePoint e x) = g.divisor dimX x := by
    rw [← hg']
    exact AlgebraicCycle.pullbackBundle_apply_bundlePoint e _ x
  have hdim : dimE (bundlePoint e x) = d := hd _ (by rw [hval]; exact hx)
  have hshift : dimE (bundlePoint e x) = dimX x + (Nat.card ι : ℤ) :=
    dimension_bundlePoint e dimX dimE x
  omega

end Homogeneity

/-! ## Homogeneity of principal divisors is invariant under isomorphism -/

/-- Homogeneity of principal divisors transports along an isomorphism of schemes. -/
theorem principalDivisorsHomogeneous_of_isIso {X Y : Scheme.{u}} (ε : X ≅ Y)
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y)
    (h : PrincipalDivisorsHomogeneous Y dimY) : PrincipalDivisorsHomogeneous X dimX := by
  intro g
  obtain ⟨d, hd⟩ := h (g.closedImage ε.hom)
  refine ⟨d, ?_⟩
  intro x hx
  have hw : (dimX : X → ℤ) = fun a ↦ (dimY : Y → ℤ) (ε.hom.base a) :=
    funext fun a ↦ DimensionFunction.apply_eq_of_isClosedImmersion dimX dimY ε.hom a
  have hmap := g.map_divisor_closedImmersion ε.hom dimX dimY
  have hpt := AlgebraicCycle.map_closedImmersion_apply_image ε.hom (dimY : Y → ℤ)
    (g.divisor dimX) x
  rw [← hw] at hpt
  rw [hmap] at hpt
  have hne : (g.closedImage ε.hom).divisor dimY (ε.hom.base x) ≠ 0 := by rw [hpt]; exact hx
  have := hd _ hne
  rw [DimensionFunction.apply_eq_of_isClosedImmersion dimX dimY ε.hom x]
  exact this

/-! ## The rank-zero case -/

section RankZero

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} [IsEmpty ι] (e : A ≃ₐ[R] MvPolynomial ι R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of A)))

include e in
/-- A rank-zero affine vector bundle has bijective flat pullback on cycles: its projection is an
isomorphism of schemes. -/
theorem bundleSurjective_of_isEmpty : BundleSurjective e dimX dimE 0 := by
  intro j z hz
  set ε : A →ₐ[R] R := (e.trans (MvPolynomial.isEmptyAlgEquiv R ι)).toAlgHom with hε
  have hiso : IsIso (zeroSection ε) := isIso_zeroSection_of_isEmpty ε e
  refine ⟨AlgebraicCycle.pullbackOpen (zeroSection ε) z, ?_, ?_⟩
  · intro x hx
    change (z : _ → ℚ) ((zeroSection ε).base x) = 0
    refine hz _ ?_
    rw [← DimensionFunction.apply_eq_of_isClosedImmersion dimX dimE (zeroSection ε) x]
    rw [sub_zero] at hx
    exact hx
  · have heq : AlgebraicCycle.pullbackBundle e
        (AlgebraicCycle.pullbackOpen (zeroSection ε) z) = z := by
      apply Function.locallyFinsuppWithin.coe_injective
      funext q
      dsimp only
      rw [AlgebraicCycle.pullbackBundle_apply_of_isEmpty e]
      change (z : _ → ℚ) ((zeroSection ε).base ((GradedCone.projection R A).base q)) = _
      have hcomp : (GradedCone.projection R A) ≫ zeroSection ε = 𝟙 _ :=
        projection_comp_zeroSection_of_isEmpty ε e
      have : (zeroSection ε).base ((GradedCone.projection R A).base q) = q :=
        congrArg (fun f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) ↦ f.base q) hcomp
      rw [this]
    rw [heq, sub_self]
    exact Submodule.zero_mem _

end RankZero


/-! ## The rank-one case -/

section RankOne

/-- The standard trivialisation of the trivial line bundle `Spec R[X] → Spec R`. -/
noncomputable def polyTrivialization (R : Type u) [CommRing R] :
    Polynomial R ≃ₐ[R] MvPolynomial (PUnit.{u + 1}) R :=
  (MvPolynomial.uniqueAlgEquiv R PUnit.{u + 1}).symm

/-- The trivial line bundle has rank one. -/
theorem card_pUnit : Nat.card (PUnit.{u + 1}) = 1 := by simp

section SinglePoint

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} (e : A ≃ₐ[R] MvPolynomial ι R)

/-- The flat pullback of a single-point cycle is the single-point cycle at the generic point of
the preimage. -/
theorem pullbackBundle_singlePoint (x : ↥(Spec (CommRingCat.of R))) :
    AlgebraicCycle.pullbackBundle e (AlgebraicCycle.singlePoint x) =
      AlgebraicCycle.singlePoint (bundlePoint e x) := by
  classical
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  dsimp only
  by_cases hq : q ∈ Set.range (bundlePoint e)
  · obtain ⟨p, rfl⟩ := hq
    rw [AlgebraicCycle.pullbackBundle_apply_bundlePoint, AlgebraicCycle.singlePoint_apply,
      AlgebraicCycle.singlePoint_apply]
    by_cases hp : p = x
    · rw [if_pos hp, if_pos (congrArg (bundlePoint e) hp)]
    · rw [if_neg hp, if_neg fun hcon ↦ hp (bundlePoint_injective e hcon)]
  · rw [AlgebraicCycle.pullbackBundle_eq_zero_of_notMem e _ hq,
      AlgebraicCycle.singlePoint_apply, if_neg fun hcon ↦ hq ⟨x, hcon.symm⟩]

end SinglePoint

/-- Fulton, *Intersection Theory*, Proposition 1.9 for the trivial line bundle
`Spec R[X] → Spec R` over a Noetherian ring, at the level of cycles: every cycle on the total
space is rationally equivalent to the flat pullback of a cycle of one dimension less on the base.

The proof is a Noetherian induction on the image `W` of the base point of a subvariety `V` of the
total space: either `V` is the whole preimage of `W`, and then `[V] = π^*[W]`, or the rank-one key
lemma `hkey` produces a rational function on `π⁻¹(closure W)` whose principal divisor has
coefficient one at `V` and coefficients supported over points strictly inside `closure W`, to
which the induction hypothesis applies.  Homogeneity of principal divisors (`hhom`) is what
guarantees that the correction divisor lives in a single dimension. -/
theorem bundleSurjective_polynomial (hkey : RankOneKey.{u}) (R : Type u) [CommRing R]
    [IsNoetherianRing R]
    (dimX : DimensionFunction (Spec (CommRingCat.of R)))
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of (Polynomial R))) dimE) :
    BundleSurjective (polyTrivialization R) dimX dimE 1 := by
  classical
  set e := polyTrivialization R with he
  have hC : (algebraMap R (Polynomial R) : R →+* Polynomial R) = Polynomial.C :=
    Polynomial.algebraMap_eq
  have hgt : WellFounded (fun a b : Ideal R ↦ a > b) := IsWellFounded.wf
  have hwf : WellFounded (fun a b : PrimeSpectrum R ↦ a.asIdeal > b.asIdeal) :=
    InvImage.wf (fun a : PrimeSpectrum R ↦ a.asIdeal) hgt
  have hdimBP : ∀ x : ↥(Spec (CommRingCat.of R)), dimE (bundlePoint e x) = dimX x + 1 := by
    intro x
    have h := dimension_bundlePoint e dimX dimE x
    rw [card_pUnit] at h
    simpa using h
  have main : ∀ W : ↥(Spec (CommRingCat.of R)),
      ∀ V : ↥(Spec (CommRingCat.of (Polynomial R))),
        PrimeSpectrum.comap (algebraMap R (Polynomial R)) V = W →
        AlgebraicCycle.singlePoint V ∈ pullbackRange e dimX dimE (dimE V - 1) := by
    intro W
    refine hwf.induction (C := fun W ↦ ∀ V : ↥(Spec (CommRingCat.of (Polynomial R))),
      PrimeSpectrum.comap (algebraMap R (Polynomial R)) V = W →
      AlgebraicCycle.singlePoint V ∈ pullbackRange e dimX dimE (dimE V - 1)) W ?_
    clear W
    intro W IH V hV
    have hbase : (bundlePoint e W).asIdeal =
        Ideal.map (algebraMap R (Polynomial R)) W.asIdeal := rfl
    by_cases hcase : V = bundlePoint e W
    · refine ⟨AlgebraicCycle.singlePoint (X := Spec (CommRingCat.of R)) W, ?_, ?_⟩
      · intro x hx
        by_cases hxW : x = W
        · refine absurd ?_ hx
          rw [hxW, hcase, hdimBP W]
          ring
        · exact AlgebraicCycle.singlePoint_of_ne hxW
      · rw [pullbackBundle_singlePoint e (show ↥(Spec (CommRingCat.of R)) from W), ← hcase,
          sub_self]
        exact Submodule.zero_mem _
    · have hWid : V.asIdeal.comap (Polynomial.C : R →+* Polynomial R) = W.asIdeal := by
        rw [← hC]
        exact congrArg PrimeSpectrum.asIdeal hV
      have hP : V.asIdeal ≠
          (V.asIdeal.comap (Polynomial.C : R →+* Polynomial R)).map Polynomial.C := by
        rw [hWid]
        intro hcon
        refine hcase (PrimeSpectrum.ext ?_)
        rw [hbase, hC]
        exact hcon
      obtain ⟨g, hsupp, hone, hzero⟩ := hkey R dimE V hP
      obtain ⟨d, hd⟩ := hhom g
      have hDrel : g.divisor dimE ∈
          totalRationalRelations (Spec (CommRingCat.of (Polynomial R))) dimE :=
        Submodule.subset_span ⟨g, rfl⟩
      have hdV : d = dimE V := (hd V (by rw [hone]; norm_num)).symm
      have hsub : ∀ Q : ↥(Spec (CommRingCat.of (Polynomial R))),
          ((AlgebraicCycle.singlePoint V - g.divisor dimE :
            AlgebraicCycle (Spec (CommRingCat.of (Polynomial R))) ℚ) : _ → ℚ) Q =
            (AlgebraicCycle.singlePoint V : _ → ℚ) Q - (g.divisor dimE : _ → ℚ) Q := by
        intro Q
        simp
      have hu : (AlgebraicCycle.singlePoint V - g.divisor dimE) ∈
          pullbackRange e dimX dimE (dimE V - 1) := by
        refine AlgebraicCycle.mem_of_forall_singlePoint _ _ ?_
        intro Q hQ
        have hQV : Q ≠ V := by
          intro hQeq
          refine hQ ?_
          rw [hsub Q, hQeq, AlgebraicCycle.singlePoint_self, hone, sub_self]
        have hDQ : (g.divisor dimE : _ → ℚ) Q ≠ 0 := by
          intro h0
          refine hQ ?_
          rw [hsub Q, AlgebraicCycle.singlePoint_of_ne hQV, h0, sub_self]
        have hQdim : dimE Q = dimE V := by rw [← hdV]; exact hd Q hDQ
        have h1 : W.asIdeal ≤ Q.asIdeal.comap (Polynomial.C : R →+* Polynomial R) := by
          have h := hsupp Q hDQ
          rwa [hWid] at h
        have h2 : Q.asIdeal.comap (Polynomial.C : R →+* Polynomial R) ≠ W.asIdeal := by
          intro hcon
          exact hDQ (hzero Q hQV (by rw [hcon, hWid]))
        have hlt : (PrimeSpectrum.comap (algebraMap R (Polynomial R)) Q).asIdeal > W.asIdeal := by
          have hQid : (PrimeSpectrum.comap (algebraMap R (Polynomial R)) Q).asIdeal =
              Q.asIdeal.comap (Polynomial.C : R →+* Polynomial R) := by rw [← hC]; rfl
          rw [hQid]
          exact lt_of_le_of_ne h1 (Ne.symm h2)
        have hIH := IH _ hlt Q rfl
        rwa [hQdim] at hIH
      obtain ⟨w, hw, hrel⟩ := hu
      refine ⟨w, hw, ?_⟩
      have hsplit : AlgebraicCycle.singlePoint V - AlgebraicCycle.pullbackBundle e w =
          (AlgebraicCycle.singlePoint V - g.divisor dimE -
            AlgebraicCycle.pullbackBundle e w) + g.divisor dimE := by
        abel
      rw [hsplit]
      exact Submodule.add_mem _ hrel hDrel
  intro j z hz
  refine AlgebraicCycle.mem_of_forall_singlePoint _ z ?_
  intro V hV
  have hdV : dimE V = j := by
    by_contra hcon
    exact hV (hz V hcon)
  have h := main (PrimeSpectrum.comap (algebraMap R (Polynomial R)) V) V rfl
  rwa [hdV] at h

end RankOne


/-! ## Induction on the rank -/

section Induction

/-- A nonempty finite index type of cardinality `n + 1` splits off one variable. -/
theorem exists_option_equiv (ι : Type u) [Finite ι] (n : ℕ) (h : Nat.card ι = n + 1) :
    ∃ (ι' : Type u) (_ : Finite ι') (_ : ι ≃ Option ι'), Nat.card ι' = n := by
  classical
  have hne : Nonempty ι := (Nat.card_pos_iff.1 (by omega)).1
  obtain ⟨a⟩ := hne
  refine ⟨{x : ι // x ≠ a}, inferInstance, (Equiv.optionSubtypeNe a).symm, ?_⟩
  have h1 : Nat.card (Option {x : ι // x ≠ a}) = Nat.card ι :=
    Nat.card_congr (Equiv.optionSubtypeNe a)
  have h2 : Nat.card (Option {x : ι // x ≠ a}) = Nat.card {x : ι // x ≠ a} + 1 := by
    have _ : Fintype {x : ι // x ≠ a} := Fintype.ofFinite _
    simp [Nat.card_eq_fintype_card, Fintype.card_option]
  omega

/-- Fulton, *Intersection Theory*, Proposition 1.9 at the level of cycles, for a trivialised
affine vector bundle of any finite rank over a Noetherian base.  The proof is an induction on the
rank: rank zero is `bundleSurjective_of_isEmpty`, and the inductive step factors the bundle as a
trivial line bundle over a bundle of one rank less (`MvPolynomial.optionEquivLeft`), composes the
two flat pullbacks (`pullbackBundle_tower`) and transports the result along the isomorphism of
coordinate algebras (`bundleSurjective_of_algEquiv`).  The homogeneity hypothesis on the total
space descends to the intermediate base by `principalDivisorsHomogeneous_base`. -/
theorem bundleSurjective_of_card (hkey : RankOneKey.{u}) (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (A : Type u) [CommRing A] [Algebra R A]
      (ι : Type u) [Finite ι] (e : A ≃ₐ[R] MvPolynomial ι R)
      (dimX : DimensionFunction (Spec (CommRingCat.of R)))
      (dimE : DimensionFunction (Spec (CommRingCat.of A))),
      Nat.card ι = n → PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE →
        BundleSurjective e dimX dimE (n : ℤ) := by
  induction n with
  | zero =>
      intro R _ _ A _ _ ι _ e dimX dimE hcard _
      have hempty : IsEmpty ι := by
        rcases Nat.card_eq_zero.1 hcard with h | h
        · exact h
        · exact absurd h (not_infinite_iff_finite.2 ‹Finite ι›)
      have := bundleSurjective_of_isEmpty (ι := ι) e dimX dimE
      simpa using this
  | succ n IH =>
      intro R _ _ A _ _ ι _ e dimX dimE hcard hhom
      obtain ⟨ι', hfin', eqv, hcard'⟩ := exists_option_equiv ι n hcard
      have _ : Finite ι' := hfin'
      -- the intermediate base and the concrete total space
      let R' : Type u := MvPolynomial ι' R
      let A₂ : Type u := Polynomial R'
      let φ : A₂ ≃ₐ[R] A :=
        (((MvPolynomial.optionEquivLeft R ι').symm.trans
          (MvPolynomial.renameEquiv R eqv.symm)).trans e.symm)
      let eA : A₂ ≃ₐ[R] MvPolynomial ι R := φ.trans e
      have hisoφ : IsIso (Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) :=
        isIso_specMap_algEquiv φ.symm
      let dimE₂ : DimensionFunction (Spec (CommRingCat.of A₂)) :=
        DimensionFunction.comapClosedImmersion
          (Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) dimE
      have hhom₂ : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A₂)) dimE₂ :=
        principalDivisorsHomogeneous_of_isIso (specIsoOfAlgEquiv φ.symm) dimE₂ dimE hhom
      let e₁ : A₂ ≃ₐ[R'] MvPolynomial (PUnit.{u + 1}) R' := polyTrivialization R'
      let dimX' : DimensionFunction (Spec (CommRingCat.of R')) := baseDimension e₁ dimE₂
      have hhomX' : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of R')) dimX' :=
        principalDivisorsHomogeneous_base e₁ dimX' dimE₂ hhom₂
      have h1 : BundleSurjective e₁ dimX' dimE₂ 1 :=
        bundleSurjective_polynomial hkey R' dimX' dimE₂ hhom₂
      have h2 : BundleSurjective (AlgEquiv.refl : R' ≃ₐ[R] MvPolynomial ι' R) dimX dimX' (n : ℤ) :=
        IH R R' ι' AlgEquiv.refl dimX dimX' hcard' hhomX'
      -- compose the two flat pullbacks on the concrete model
      have hcomp : BundleSurjective eA dimX dimE₂ ((n : ℤ) + 1) := by
        intro j z hz
        obtain ⟨w₁, hw₁, hrel₁⟩ := h1 j z hz
        obtain ⟨w, hw, hrel⟩ := h2 (j - 1) w₁ hw₁
        refine ⟨w, ?_, ?_⟩
        · intro x hx
          refine hw x ?_
          intro hcon
          exact hx (by omega)
        · have htower : AlgebraicCycle.pullbackBundle eA w =
              AlgebraicCycle.pullbackBundle e₁
                (AlgebraicCycle.pullbackBundle (AlgEquiv.refl : R' ≃ₐ[R] MvPolynomial ι' R) w) :=
            pullbackBundle_tower eA e₁ AlgEquiv.refl w
          have hlin : AlgebraicCycle.pullbackBundle e₁
              (w₁ - AlgebraicCycle.pullbackBundle (AlgEquiv.refl : R' ≃ₐ[R] MvPolynomial ι' R) w) =
              AlgebraicCycle.pullbackBundle e₁ w₁ -
                AlgebraicCycle.pullbackBundle e₁
                  (AlgebraicCycle.pullbackBundle
                    (AlgEquiv.refl : R' ≃ₐ[R] MvPolynomial ι' R) w) :=
            map_sub (AlgebraicCycle.pullbackBundleLinear e₁) _ _
          have hmem : AlgebraicCycle.pullbackBundle e₁
              (w₁ - AlgebraicCycle.pullbackBundle (AlgEquiv.refl : R' ≃ₐ[R] MvPolynomial ι' R) w)
              ∈ totalRationalRelations (Spec (CommRingCat.of A₂)) dimE₂ :=
            totalRationalRelations_pullbackBundle e₁ dimX' dimE₂ ⟨_, hrel, rfl⟩
          have hsplit : z - AlgebraicCycle.pullbackBundle eA w =
              (z - AlgebraicCycle.pullbackBundle e₁ w₁) +
                AlgebraicCycle.pullbackBundle e₁
                  (w₁ - AlgebraicCycle.pullbackBundle
                    (AlgEquiv.refl : R' ≃ₐ[R] MvPolynomial ι' R) w) := by
            rw [htower, hlin]
            abel
          rw [hsplit]
          exact Submodule.add_mem _ hrel₁ hmem
      have hfinal := bundleSurjective_of_algEquiv φ eA e dimX dimE₂ dimE ((n : ℤ) + 1) hcomp
      have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      exact hfinal

end Induction

/-! ## Surjectivity of the Chow pullback -/

section Surjectivity

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} [Finite ι] (e : A ≃ₐ[R] MvPolynomial ι R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of A))) (i : ℤ)
  (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
  (RE : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimE (i + (Nat.card ι : ℤ)))

/-- **Fulton, *Intersection Theory*, Proposition 1.9.**  The flat pullback along a trivialised
affine vector bundle of finite rank over a Noetherian ring is surjective on dimension-graded
rational Chow groups.

Two hypotheses are carried: `hkey` is the rank-one key lemma, proved in
`IntersectionTheory/BundleHomotopyRankOne.lean` (it is a hypothesis here only to keep the two
files independent), and `hhom` is homogeneity of principal divisors on the total space, the same
hypothesis under which the localisation sequence of `IntersectionTheory/LocalizationExact.lean`
is proved; it is genuinely needed in this generality, because `totalRationalRelations` is defined
without a grading. -/
theorem chowPullbackBundle_surjective (hkey : RankOneKey.{u})
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE) :
    Function.Surjective (chowPullbackBundle e dimX dimE i RX RE) := by
  have hsurj : BundleSurjective e dimX dimE (Nat.card ι : ℤ) :=
    bundleSurjective_of_card hkey (Nat.card ι) R A ι e dimX dimE rfl hhom
  intro y
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective RE.relations y
  have hz2 : ∀ q, dimE q ≠ i + (Nat.card ι : ℤ) →
      ((z : cyclesOfDimension (Spec (CommRingCat.of A)) dimE (i + (Nat.card ι : ℤ))) :
        AlgebraicCycle (Spec (CommRingCat.of A)) ℚ) q = 0 := z.2
  obtain ⟨w, hw, hrel⟩ := hsurj (i + (Nat.card ι : ℤ)) (z : AlgebraicCycle _ ℚ) hz2
  have hw' : ∀ x, dimX x ≠ i → (w : _ → ℚ) x = 0 := by
    intro x hx
    refine hw x ?_
    intro hcon
    exact hx (by omega)
  refine ⟨RX.quotientMap ⟨w, hw'⟩, ?_⟩
  have hmem : cyclesOfDimension.flatPullbackBundle e dimX dimE i ⟨w, hw'⟩ - z ∈ RE.relations := by
    cases RE
    have hneg : AlgebraicCycle.pullbackBundle e w - (z : AlgebraicCycle _ ℚ) =
        -((z : AlgebraicCycle _ ℚ) - AlgebraicCycle.pullbackBundle e w) := by abel
    change AlgebraicCycle.pullbackBundle e w - (z : AlgebraicCycle _ ℚ) ∈
      totalRationalRelations (Spec (CommRingCat.of A)) dimE
    rw [hneg]
    exact Submodule.neg_mem _ hrel
  rw [chowPullbackBundle_quotientMap]
  exact (Submodule.Quotient.eq _).2 hmem

/-- Every rational Chow class on the total space of a trivialised affine vector bundle is the
flat pullback of a class on the base. -/
theorem exists_pullback_eq (hkey : RankOneKey.{u})
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE)
    (β : RE.ChowGroup) :
    ∃ α : RX.ChowGroup, chowPullbackBundle e dimX dimE i RX RE α = β :=
  chowPullbackBundle_surjective e dimX dimE i RX RE hkey hhom β

/-- The first isomorphism theorem for the flat pullback along an affine vector bundle: the Chow
group of the total space is the Chow group of the base modulo the kernel of `π^*`.  Full homotopy
invariance is the statement that this kernel vanishes; that is *not* proved here (see
`zeroSectionGysinEquiv`). -/
noncomputable def chowQuotientEquiv (hkey : RankOneKey.{u})
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE) :
    (RX.ChowGroup ⧸ LinearMap.ker (chowPullbackBundle e dimX dimE i RX RE)) ≃ₗ[ℚ]
      RE.ChowGroup :=
  LinearMap.quotKerEquivOfSurjective _
    (chowPullbackBundle_surjective e dimX dimE i RX RE hkey hhom)

/-- The zero-section Gysin map `0^!` of a trivialised affine vector bundle: the inverse of the
flat pullback `π^*`.

Surjectivity of `π^*` is proved (`chowPullbackBundle_surjective`); **injectivity is an explicit
hypothesis** `hinj`.  Injectivity is the remaining half of homotopy invariance (Fulton, Theorem
3.3(a)); its proof needs Chern classes of vector bundles, which are not available in this
development, so it is not attempted here. -/
noncomputable def zeroSectionGysinEquiv (hkey : RankOneKey.{u})
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE)
    (hinj : Function.Injective (chowPullbackBundle e dimX dimE i RX RE)) :
    RE.ChowGroup ≃ₗ[ℚ] RX.ChowGroup :=
  (LinearEquiv.ofBijective (chowPullbackBundle e dimX dimE i RX RE)
    ⟨hinj, chowPullbackBundle_surjective e dimX dimE i RX RE hkey hhom⟩).symm

/-- The zero-section Gysin map undoes the flat pullback: `0^!(π^* α) = α`. -/
@[simp]
theorem zeroSectionGysinEquiv_pullback (hkey : RankOneKey.{u})
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE)
    (hinj : Function.Injective (chowPullbackBundle e dimX dimE i RX RE))
    (α : RX.ChowGroup) :
    zeroSectionGysinEquiv e dimX dimE i RX RE hkey hhom hinj
        (chowPullbackBundle e dimX dimE i RX RE α) = α :=
  (LinearEquiv.ofBijective (chowPullbackBundle e dimX dimE i RX RE)
    ⟨hinj, chowPullbackBundle_surjective e dimX dimE i RX RE hkey hhom⟩).symm_apply_apply α

/-- The flat pullback undoes the zero-section Gysin map: `π^* (0^! β) = β`. -/
@[simp]
theorem pullback_zeroSectionGysinEquiv (hkey : RankOneKey.{u})
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE)
    (hinj : Function.Injective (chowPullbackBundle e dimX dimE i RX RE))
    (β : RE.ChowGroup) :
    chowPullbackBundle e dimX dimE i RX RE
        (zeroSectionGysinEquiv e dimX dimE i RX RE hkey hhom hinj β) = β :=
  (LinearEquiv.ofBijective (chowPullbackBundle e dimX dimE i RX RE)
    ⟨hinj, chowPullbackBundle_surjective e dimX dimE i RX RE hkey hhom⟩).apply_symm_apply β

/-- The class pulling back to a given class on the total space is unique once `π^*` is
injective. -/
theorem eq_zeroSectionGysinEquiv_of_pullback_eq (hkey : RankOneKey.{u})
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE)
    (hinj : Function.Injective (chowPullbackBundle e dimX dimE i RX RE))
    (α : RX.ChowGroup) (β : RE.ChowGroup)
    (hαβ : chowPullbackBundle e dimX dimE i RX RE α = β) :
    α = zeroSectionGysinEquiv e dimX dimE i RX RE hkey hhom hinj β := by
  subst hαβ
  exact (zeroSectionGysinEquiv_pullback e dimX dimE i RX RE hkey hhom hinj α).symm

end Surjectivity

end VectorBundle

end GromovWitten.AlgebraicGeometry.IntersectionTheory
