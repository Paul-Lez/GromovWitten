/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.StackGysin
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroupLocalization
import GromovWitten.AlgebraicGeometry.Cones.Graded
import GromovWitten.Algebra.FiniteTypeKrullDimension
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Flat pullback along an affine vector bundle, and zero-section Gysin input

Let `R` be a Noetherian ring and let `E = Spec A → Spec R = X` be an affine vector bundle of
rank `r`: an `R`-algebra `A` together with an `R`-algebra isomorphism `A ≃ₐ[R] MvPolynomial ι R`
for a finite index type `ι` with `Nat.card ι = r`.  The vector bundle `Spec Sym(F)` of a finite
free module `F` constructed in `Cones/Graded.lean` is of this form
(`VectorBundle.symTrivialization`).

This file constructs the flat pullback of dimension-graded rational cycles along such a bundle,
with the dimension shift `i ↦ i + r` *proved* rather than assumed, and everything about the zero
section and about isomorphism invariance that does not need the still-missing comparison of
principal divisors.

## The preimage of a subvariety and its dimension

* `VectorBundle.isPrime_map_C`, `VectorBundle.comap_C_map_C`: the extension `p · R[ι]` of a prime
  is prime and contracts back to `p`.
* `VectorBundle.bundlePrime`: the generic point of the preimage `π⁻¹(closure x)`, namely the
  extended ideal `p · A`.  It is proved prime (`VectorBundle.isPrime_map_algebraMap`), proved to
  lie over `p` (`VectorBundle.comap_bundlePrime`), injective in `p`, and proved independent of the
  chosen trivialization (`VectorBundle.bundlePrime_congr`).
* `VectorBundle.coheight_polyPrime`, `VectorBundle.coheight_bundlePrime`: the dimension of the
  preimage of a subvariety is the dimension of the subvariety plus `r`.  This is Mathlib's Krull
  dimension of a polynomial ring over a Noetherian ring applied to `R ⧸ p`.
* `VectorBundle.specOrderIso`, `VectorBundle.coheight_eq_dimension`: the specialization order on
  the points of `Spec R` used by `DimensionFunction` is the dual of the inclusion order on primes,
  so the certified grading of `Spec R` computes coheights.
* `VectorBundle.dimension_bundlePoint`: consequently, for the certified `DimensionFunction`
  gradings of `Spec R` and `Spec A`, `dim_E (bundlePoint x) = dim_X x + r`.

## The flat pullback

* `AlgebraicCycle.pullbackBundle`: the flat pullback of a rational algebraic cycle, supported on
  the generic points of the preimages with all multiplicities one; proved locally finite, rational
  linear (`AlgebraicCycle.pullbackBundleLinear`) and injective.
* `cyclesOfDimension.flatPullbackBundle`: the same map on dimension-graded cycles, with the proved
  grading `Z_i(X) →ₗ[ℚ] Z_{i+r}(E)`, and proved injective.
* `VectorBundle.symFlatPullback`: its instance for the bundle `Spec Sym(F)` of a finite free
  module, whose rank is `Module.finrank R F` (`VectorBundle.card_chooseBasisIndex`).

## Isomorphism invariance

* `VectorBundle.specIsoOfAlgEquiv`: an isomorphism of coordinate algebras induces an isomorphism,
  hence an open immersion, of total spaces; `VectorBundle.dimension_comap_algEquiv` shows the two
  certified gradings agree along it.
* `AlgebraicCycle.pullbackBundle_algEquiv` and
  `cyclesOfDimension.flatPullbackOpen_flatPullbackBundle`: the flat pullback is invariant under
  isomorphism of bundles, on cycles and on graded cycles.
* `VectorBundle.chowEquivOfAlgEquiv`: an isomorphism of coordinate algebras induces an isomorphism
  of rational Chow groups, the two flat pullbacks along the mutually inverse open immersions being
  proved mutually inverse.

## The zero section

* `VectorBundle.zeroSection` (the vertex section of `Cones/Graded.lean`) is proved to be a closed
  immersion (`VectorBundle.isClosedImmersion_vertexSection`, since an `R`-algebra map to `R` is
  automatically surjective) and a section of the projection, and therefore induces
  `VectorBundle.zeroSectionPushforward : A_i(X) →ₗ[ℚ] A_i(E)`.
* `cyclesOfDimension.flatPullbackOpen_properPushforward` and
  `RationalEquivalenceSystem.DescendingMap.openImmersionPullback_pushforward_eq_id`:
  for a closed immersion which is also an open immersion, flat pullback is a retraction of the
  pushforward.  `VectorBundle.zeroSectionGysin` specializes this to the zero section.

## The rank-zero case

For `ι` empty the structure map `R → A` is proved surjective, every point of `E` is proved to be
the generic point of the preimage of its image (`VectorBundle.bundlePoint_surjective_of_isEmpty`),
the pullback is proved to be the existing flat pullback along the projection
(`AlgebraicCycle.pullbackBundle_eq_pullbackOpen_of_isEmpty`), the projection and the zero section
are proved to be mutually inverse isomorphisms (`VectorBundle.isIso_projection_of_isEmpty`,
`VectorBundle.isIso_zeroSection_of_isEmpty`), and the grading shift is `0`.  So the positive-rank
construction restricts to the rank-zero identity of `Gysin.lean`, and `zeroSectionGysin` becomes
the self-intersection formula in the case where the top Chern class is `1`.

## What is not here

The descent of `flatPullbackBundle` to rational equivalence, hence the map `A_i(X) → A_{i+r}(E)`,
is *not* proved, and neither are homotopy invariance, the zero-section Gysin inverse in positive
rank, Chern classes, the projective bundle formula or the Whitney sum formula, all of which rest
on it.  What is missing is exactly one comparison: for an integral closed subscheme `Z ⊆ Spec R`
and `f` in its function field, `π^* div(f)` must be identified with the principal divisor of `f`
on `Z ×_X E`.  That needs the order-of-vanishing comparison for the flat local extension
`𝒪_{Z,z} → 𝒪_{Z ×_X E, π⁻¹ z}`, whose maximal ideal is the extended one but whose residue
extension is transcendental; the existing
`Ring.ord_algebraMap_of_flat_formallyUnramified_local` of `ChowGroup.lean` assumes formal
unramifiedness and so does not apply, and Mathlib has no length formula for a flat local extension
with `m_A · B = m_B` and arbitrary residue extension.  It also needs the base change
`Z ×_X E` of an abstract `IntegralClosedSubscheme` to be identified with `Spec (Γ(Z) ⊗_R A)`,
for which the repository has no affine-closed-immersion presentation lemma.
-/

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

namespace VectorBundle

/-! ## Extension of a prime ideal to a polynomial algebra -/

section CommRing

variable {R : Type u} [CommRing R] {ι : Type u}

/-- The extension of a prime ideal to a multivariate polynomial ring is prime: the quotient is
the polynomial ring over the quotient domain. -/
theorem isPrime_map_C (p : Ideal R) [p.IsPrime] :
    (Ideal.map (MvPolynomial.C (σ := ι)) p).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact MulEquiv.isDomain _
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) p).symm.toRingEquiv.toMulEquiv

/-- Contracting the extension of an ideal of `R` to `R[ι]` returns the ideal: the constant
coefficient is a retraction of the inclusion of constants. -/
theorem comap_C_map_C (p : Ideal R) :
    Ideal.comap (MvPolynomial.C (σ := ι)) (Ideal.map MvPolynomial.C p) = p := by
  refine le_antisymm ?_ Ideal.le_comap_map
  have h : Ideal.map (MvPolynomial.C (σ := ι)) p ≤
      Ideal.comap (MvPolynomial.constantCoeff (σ := ι) (R := R)) p :=
    Ideal.map_le_iff_le_comap.2 fun a ha => by simpa using ha
  intro x hx
  simpa using h hx

/-- The point of `Spec R[ι]` given by the extension of a prime of `R`. -/
noncomputable def polyPrime (p : PrimeSpectrum R) : PrimeSpectrum (MvPolynomial ι R) :=
  ⟨Ideal.map MvPolynomial.C p.asIdeal, isPrime_map_C p.asIdeal⟩

@[simp]
theorem polyPrime_asIdeal (p : PrimeSpectrum R) :
    (polyPrime (ι := ι) p).asIdeal = Ideal.map MvPolynomial.C p.asIdeal :=
  rfl

variable [Finite ι]

/-- The dimension of the closure of the extended prime exceeds that of the closure of `p` by the
rank.  This is Mathlib's computation of the Krull dimension of a polynomial ring over a
Noetherian ring, applied to the Noetherian domain `R ⧸ p`. -/
theorem coheight_polyPrime [IsNoetherianRing R] (p : PrimeSpectrum R) :
    Order.coheight (polyPrime (ι := ι) p) = Order.coheight p + (Nat.card ι : ℕ∞) := by
  have h1 := GromovWitten.Algebra.PrimeSpectrum.coheight_eq_ringKrullDim_quotient
    (polyPrime (ι := ι) p)
  have h2 := GromovWitten.Algebra.PrimeSpectrum.coheight_eq_ringKrullDim_quotient p
  have h3 : ringKrullDim (MvPolynomial ι R ⧸ (polyPrime (ι := ι) p).asIdeal) =
      ringKrullDim (R ⧸ p.asIdeal) + (Nat.card ι : ℕ∞) := by
    rw [polyPrime_asIdeal, ← ringKrullDim_eq_of_ringEquiv
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) p.asIdeal).toRingEquiv]
    exact MvPolynomial.ringKrullDim_of_isNoetherianRing
  rw [h3, ← h2] at h1
  have hcast : ((Order.coheight (polyPrime (ι := ι) p) : ℕ∞) : WithBot ℕ∞) =
      ((Order.coheight p + (Nat.card ι : ℕ∞) : ℕ∞) : WithBot ℕ∞) := by
    rw [h1]
    push_cast
    rfl
  exact_mod_cast hcast

end CommRing

/-- The coheight of a prime is invariant under contraction along a ring isomorphism. -/
theorem coheight_comap_ringEquiv {A B : Type u} [CommRing A] [CommRing B] (f : A ≃+* B)
    (P : PrimeSpectrum B) :
    Order.coheight (PrimeSpectrum.comap f.toRingHom P) = Order.coheight P := by
  rw [RingEquiv.toRingHom_eq_coe]
  simpa using Order.coheight_orderIso (PrimeSpectrum.comapEquiv f.symm) P

/-! ## The generic point of the preimage of a subvariety -/

section Trivialized

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} (e : A ≃ₐ[R] MvPolynomial ι R)

/-- For a trivialized bundle the extended ideal `p · A` is the contraction of the extended ideal
of the polynomial algebra along the trivialization. -/
theorem map_algebraMap_eq_comap (p : PrimeSpectrum R) :
    Ideal.map (algebraMap R A) p.asIdeal =
      Ideal.comap (e.toRingEquiv : A ≃+* MvPolynomial ι R).toRingHom
        (polyPrime (ι := ι) p).asIdeal := by
  have hcomap : Ideal.comap (e.toRingEquiv : A ≃+* MvPolynomial ι R).toRingHom
      (polyPrime (ι := ι) p).asIdeal =
      Ideal.map ((e.toRingEquiv : A ≃+* MvPolynomial ι R).symm :
        MvPolynomial ι R →+* A) (polyPrime (ι := ι) p).asIdeal :=
    (Ideal.map_symm (e.toRingEquiv : A ≃+* MvPolynomial ι R)).symm
  rw [hcomap, polyPrime_asIdeal, Ideal.map_map]
  congr 1
  refine RingHom.ext fun r => ?_
  have hr : (e.symm) ((algebraMap R (MvPolynomial ι R)) r) = algebraMap R A r :=
    e.symm.commutes r
  simp [MvPolynomial.algebraMap_eq, hr.symm]

include e in
/-- The extension of a prime of the base to the coordinate algebra of a trivialized vector
bundle is prime. -/
theorem isPrime_map_algebraMap (p : PrimeSpectrum R) :
    (Ideal.map (algebraMap R A) p.asIdeal).IsPrime := by
  rw [map_algebraMap_eq_comap e]
  exact Ideal.IsPrime.comap _

/-- The generic point of the preimage `π⁻¹(closure p)` of the closure of a point of the base:
the prime `p · A`.  Its underlying ideal does not mention the trivialization, so the point is
canonical (`bundlePrime_congr`). -/
def bundlePrime (p : PrimeSpectrum R) : PrimeSpectrum A :=
  ⟨Ideal.map (algebraMap R A) p.asIdeal, isPrime_map_algebraMap e p⟩

@[simp]
theorem bundlePrime_asIdeal (p : PrimeSpectrum R) :
    (bundlePrime e p).asIdeal = Ideal.map (algebraMap R A) p.asIdeal :=
  rfl

/-- The generic point of the preimage is independent of the chosen trivialization. -/
theorem bundlePrime_congr {ι' : Type u} (e' : A ≃ₐ[R] MvPolynomial ι' R) (p : PrimeSpectrum R) :
    bundlePrime e p = bundlePrime e' p :=
  PrimeSpectrum.ext rfl

/-- The generic point of the preimage lies over the given point of the base. -/
@[simp]
theorem comap_bundlePrime (p : PrimeSpectrum R) :
    PrimeSpectrum.comap (algebraMap R A) (bundlePrime e p) = p := by
  have h : bundlePrime e p =
      PrimeSpectrum.comap (e.toRingEquiv : A ≃+* MvPolynomial ι R).toRingHom
        (polyPrime (ι := ι) p) :=
    PrimeSpectrum.ext (map_algebraMap_eq_comap e p)
  rw [h, ← PrimeSpectrum.comap_comp_apply]
  have hcomp : ((e.toRingEquiv : A ≃+* MvPolynomial ι R).toRingHom).comp (algebraMap R A) =
      algebraMap R (MvPolynomial ι R) := RingHom.ext fun r => e.commutes r
  rw [hcomp]
  exact PrimeSpectrum.ext (comap_C_map_C p.asIdeal)

/-- Distinct points of the base have distinct preimage generic points. -/
theorem bundlePrime_injective : Function.Injective (bundlePrime e) := fun p q h => by
  rw [← comap_bundlePrime e p, ← comap_bundlePrime e q, h]

variable [Finite ι]

/-- The dimension of the preimage of a subvariety exceeds the dimension of the subvariety by the
rank of the bundle. -/
theorem coheight_bundlePrime [IsNoetherianRing R] (p : PrimeSpectrum R) :
    Order.coheight (bundlePrime e p) = Order.coheight p + (Nat.card ι : ℕ∞) := by
  have h : bundlePrime e p =
      PrimeSpectrum.comap (e.toRingEquiv : A ≃+* MvPolynomial ι R).toRingHom
        (polyPrime (ι := ι) p) :=
    PrimeSpectrum.ext (map_algebraMap_eq_comap e p)
  rw [h, coheight_comap_ringEquiv (e.toRingEquiv : A ≃+* MvPolynomial ι R)]
  exact coheight_polyPrime p

end Trivialized

/-! ## The specialization order on an affine scheme -/

section SpecOrder

variable (R : Type u) [CommRing R]

/-- The specialization order on the points of `Spec R` is the order dual of the inclusion order
on prime ideals. -/
def specOrderIso : ↥(Spec (CommRingCat.of R)) ≃o (PrimeSpectrum R)ᵒᵈ where
  toFun x := OrderDual.toDual (x : PrimeSpectrum R)
  invFun x := (OrderDual.ofDual x : PrimeSpectrum R)
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {a b} := PrimeSpectrum.le_iff_specializes b a

/-- The dimension of the closure of a point of `Spec R`, measured by the height in the
specialization order used by `DimensionFunction`, is the coheight of the corresponding prime in
the inclusion order. -/
theorem coheight_eq_height (x : PrimeSpectrum R) :
    Order.coheight x = @Order.height ↥(Spec (CommRingCat.of R)) _ x :=
  Order.height_orderIso (specOrderIso R) x

/-- The certified dimension grading of `Spec R` computes the coheight of a prime. -/
theorem coheight_eq_dimension (dim : DimensionFunction (Spec (CommRingCat.of R)))
    (x : PrimeSpectrum R) :
    Order.coheight x = (Int.toNat (dim x) : ℕ∞) :=
  (coheight_eq_height R x).trans (dim.height_eq x)

end SpecOrder

/-! ## The bundle projection on points, and the dimension shift -/

section Projection

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} (e : A ≃ₐ[R] MvPolynomial ι R)

/-- The projection of an affine vector bundle acts on points by contraction of primes. -/
@[simp]
theorem projection_base (q : ↥(Spec (CommRingCat.of A))) :
    (GradedCone.projection R A).base q = PrimeSpectrum.comap (algebraMap R A) q :=
  rfl

/-- The generic point of the preimage of a point of the base, as a point of the total space. -/
noncomputable def bundlePoint (x : ↥(Spec (CommRingCat.of R))) :
    ↥(Spec (CommRingCat.of A)) :=
  bundlePrime e x

@[simp]
theorem projection_base_bundlePoint (x : ↥(Spec (CommRingCat.of R))) :
    (GradedCone.projection R A).base (bundlePoint e x) = x :=
  comap_bundlePrime e x

theorem bundlePoint_injective : Function.Injective (bundlePoint e) :=
  bundlePrime_injective e

/-- The certified dimension grading of the total space of a rank-`r` affine vector bundle
exceeds that of the base by `r` on the generic point of every preimage.  Both sides are read off
from the two `DimensionFunction` certificates, and the shift itself is the proved polynomial
Krull-dimension formula. -/
theorem dimension_bundlePoint [Finite ι] [IsNoetherianRing R]
    (dimX : DimensionFunction (Spec (CommRingCat.of R)))
    (dimE : DimensionFunction (Spec (CommRingCat.of A)))
    (x : ↥(Spec (CommRingCat.of R))) :
    dimE (bundlePoint e x) = dimX x + (Nat.card ι : ℤ) := by
  have hE : Order.coheight (bundlePrime e x) =
      (Int.toNat (dimE (bundlePoint e x)) : ℕ∞) :=
    coheight_eq_dimension A dimE (bundlePrime e x)
  have hX : Order.coheight (show PrimeSpectrum R from x) = (Int.toNat (dimX x) : ℕ∞) :=
    coheight_eq_dimension R dimX x
  have hco : Order.coheight (bundlePrime e x) =
      Order.coheight (show PrimeSpectrum R from x) + (Nat.card ι : ℕ∞) :=
    coheight_bundlePrime e x
  rw [hE, hX] at hco
  have hnat : Int.toNat (dimE (bundlePoint e x)) = Int.toNat (dimX x) + Nat.card ι := by
    exact_mod_cast hco
  have hE0 := dimE.nonnegative (bundlePoint e x)
  have hX0 := dimX.nonnegative x
  omega

end Projection

end VectorBundle

/-! ## Flat pullback of rational cycles along an affine vector bundle -/


namespace AlgebraicCycle

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} (e : A ≃ₐ[R] MvPolynomial ι R)

open scoped Classical in
/-- The coefficient function of the flat pullback of a cycle along an affine vector bundle:
the preimage of an integral closed subscheme is integral, so the pullback is supported on the
generic points of the preimages and every multiplicity is one. -/
noncomputable def pullbackBundleFun (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) :
    ↥(Spec (CommRingCat.of A)) → ℚ :=
  fun q => if q = VectorBundle.bundlePoint e ((GradedCone.projection R A).base q) then
    c ((GradedCone.projection R A).base q) else 0

@[simp]
theorem pullbackBundleFun_apply_bundlePoint
    (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) (x : ↥(Spec (CommRingCat.of R))) :
    pullbackBundleFun e c (VectorBundle.bundlePoint e x) = c x := by
  have h : (GradedCone.projection R A).base (VectorBundle.bundlePoint e x) = x :=
    VectorBundle.projection_base_bundlePoint e x
  simp only [pullbackBundleFun, h, if_pos]

theorem pullbackBundleFun_eq_zero_of_notMem
    (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) {q : ↥(Spec (CommRingCat.of A))}
    (hq : q ∉ Set.range (VectorBundle.bundlePoint e)) :
    pullbackBundleFun e c q = 0 := by
  rw [pullbackBundleFun]
  exact if_neg fun h => hq ⟨(GradedCone.projection R A).base q, h.symm⟩

theorem support_pullbackBundleFun_subset (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) :
    Function.support (pullbackBundleFun e c) ⊆ Set.range (VectorBundle.bundlePoint e) := by
  intro q hq
  by_contra hmem
  exact hq (pullbackBundleFun_eq_zero_of_notMem e c hmem)

/-- Flat pullback of a rational algebraic cycle along an affine vector bundle.  Local finiteness
holds because the projection is injective on the support of the pullback, with image inside the
support of the original cycle. -/
noncomputable def pullbackBundle (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) :
    AlgebraicCycle (Spec (CommRingCat.of A)) ℚ where
  toFun := pullbackBundleFun e c
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' q _ := by
    obtain ⟨t, ht, hfinite⟩ := c.supportLocallyFiniteWithinDomain
      ((GradedCone.projection R A).base q) (by trivial)
    refine ⟨(GradedCone.projection R A).base ⁻¹' t,
      (GradedCone.projection R A).continuous.continuousAt.preimage_mem_nhds ht, ?_⟩
    have hsub : (GradedCone.projection R A).base ''
        ((GradedCone.projection R A).base ⁻¹' t ∩ Function.support (pullbackBundleFun e c)) ⊆
        t ∩ Function.support (c : ↥(Spec (CommRingCat.of R)) → ℚ) := by
      rintro y ⟨z, hz, rfl⟩
      obtain ⟨w, rfl⟩ := support_pullbackBundleFun_subset e c hz.2
      have hval := hz.2
      rw [Function.mem_support, pullbackBundleFun_apply_bundlePoint] at hval
      have h1 : (GradedCone.projection R A).base (VectorBundle.bundlePoint e w) = w :=
        VectorBundle.projection_base_bundlePoint e w
      have ht' : w ∈ t := by
        rw [← h1]
        exact hz.1
      rw [h1]
      exact ⟨ht', hval⟩
    have hinj : Set.InjOn (GradedCone.projection R A).base
        ((GradedCone.projection R A).base ⁻¹' t ∩ Function.support (pullbackBundleFun e c)) := by
      rintro a ha b hb hab
      obtain ⟨a', rfl⟩ := support_pullbackBundleFun_subset e c ha.2
      obtain ⟨b', rfl⟩ := support_pullbackBundleFun_subset e c hb.2
      rw [VectorBundle.projection_base_bundlePoint,
        VectorBundle.projection_base_bundlePoint] at hab
      rw [hab]
    exact Set.Finite.of_finite_image (hfinite.subset hsub) hinj

@[simp]
theorem pullbackBundle_apply (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ)
    (q : ↥(Spec (CommRingCat.of A))) :
    pullbackBundle e c q = pullbackBundleFun e c q :=
  rfl

/-- The pullback of a cycle has the original coefficient at the generic point of the preimage. -/
theorem pullbackBundle_apply_bundlePoint (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ)
    (x : ↥(Spec (CommRingCat.of R))) :
    pullbackBundle e c (VectorBundle.bundlePoint e x) = c x :=
  pullbackBundleFun_apply_bundlePoint e c x

/-- The pullback of a cycle vanishes away from the generic points of the preimages. -/
theorem pullbackBundle_eq_zero_of_notMem (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ)
    {q : ↥(Spec (CommRingCat.of A))} (hq : q ∉ Set.range (VectorBundle.bundlePoint e)) :
    pullbackBundle e c q = 0 :=
  pullbackBundleFun_eq_zero_of_notMem e c hq

/-- Flat pullback along an affine vector bundle is additive. -/
theorem pullbackBundle_add (c d : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) :
    pullbackBundle e (c + d) = pullbackBundle e c + pullbackBundle e d := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  by_cases h : q ∈ Set.range (VectorBundle.bundlePoint e)
  · obtain ⟨x, rfl⟩ := h
    simp
  · have h0 : ∀ z : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ,
        pullbackBundleFun e z q = 0 := fun z => pullbackBundleFun_eq_zero_of_notMem e z h
    simp [h0]

/-- Flat pullback along an affine vector bundle commutes with rational scalars. -/
theorem pullbackBundle_smul (a : ℚ) (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) :
    pullbackBundle e (a • c) = a • pullbackBundle e c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  by_cases h : q ∈ Set.range (VectorBundle.bundlePoint e)
  · obtain ⟨x, rfl⟩ := h
    simp
  · have h0 : ∀ z : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ,
        pullbackBundleFun e z q = 0 := fun z => pullbackBundleFun_eq_zero_of_notMem e z h
    simp [h0]

/-- Flat pullback along an affine vector bundle, bundled with its proved rational linearity. -/
noncomputable def pullbackBundleLinear :
    AlgebraicCycle (Spec (CommRingCat.of R)) ℚ →ₗ[ℚ]
      AlgebraicCycle (Spec (CommRingCat.of A)) ℚ where
  toFun := pullbackBundle e
  map_add' := pullbackBundle_add e
  map_smul' := pullbackBundle_smul e

@[simp]
theorem pullbackBundleLinear_apply (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) :
    pullbackBundleLinear e c = pullbackBundle e c :=
  rfl

/-- Flat pullback along an affine vector bundle is injective: the original coefficients are
recovered at the generic points of the preimages. -/
theorem pullbackBundle_injective : Function.Injective (pullbackBundle e) := by
  intro c d h
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  have hx := congrArg (fun z : AlgebraicCycle (Spec (CommRingCat.of A)) ℚ =>
    z (VectorBundle.bundlePoint e x)) h
  simpa using hx

end AlgebraicCycle

/-! ## Flat pullback of dimension-graded cycles -/

namespace cyclesOfDimension

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} [Finite ι] (e : A ≃ₐ[R] MvPolynomial ι R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of A))) (i : ℤ)

/-- Flat pullback of dimension-graded rational cycles along a rank-`r` affine vector bundle.
The grading shift `i ↦ i + r` is not an assumption: it is forced by the proved polynomial
Krull-dimension formula `VectorBundle.dimension_bundlePoint`. -/
noncomputable def flatPullbackBundle :
    cyclesOfDimension (Spec (CommRingCat.of R)) dimX i →ₗ[ℚ]
      cyclesOfDimension (Spec (CommRingCat.of A)) dimE (i + (Nat.card ι : ℤ)) where
  toFun c := ⟨AlgebraicCycle.pullbackBundle e c.1, by
    intro q hq
    by_contra hne
    have hsupp : q ∈ Function.support (AlgebraicCycle.pullbackBundleFun e c.1) := hne
    obtain ⟨x, rfl⟩ := AlgebraicCycle.support_pullbackBundleFun_subset e c.1 hsupp
    have hval : (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) x ≠ 0 := by
      rw [← AlgebraicCycle.pullbackBundle_apply_bundlePoint e c.1 x]
      exact hne
    have hdx : dimX x = i := by
      by_contra hcon
      exact hval (c.2 x hcon)
    refine hq ?_
    rw [VectorBundle.dimension_bundlePoint e dimX dimE x, hdx]⟩
  map_add' c d := Subtype.ext (AlgebraicCycle.pullbackBundle_add e c.1 d.1)
  map_smul' a c := Subtype.ext (AlgebraicCycle.pullbackBundle_smul e a c.1)

@[simp]
theorem flatPullbackBundle_apply
    (c : cyclesOfDimension (Spec (CommRingCat.of R)) dimX i)
    (q : ↥(Spec (CommRingCat.of A))) :
    ((flatPullbackBundle e dimX dimE i c :
        cyclesOfDimension (Spec (CommRingCat.of A)) dimE (i + (Nat.card ι : ℤ))) :
          AlgebraicCycle (Spec (CommRingCat.of A)) ℚ) q =
      AlgebraicCycle.pullbackBundle e (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) q :=
  rfl

/-- The graded flat pullback restores the original coefficient at the generic point of each
preimage. -/
@[simp]
theorem flatPullbackBundle_apply_bundlePoint
    (c : cyclesOfDimension (Spec (CommRingCat.of R)) dimX i)
    (x : ↥(Spec (CommRingCat.of R))) :
    ((flatPullbackBundle e dimX dimE i c :
        cyclesOfDimension (Spec (CommRingCat.of A)) dimE (i + (Nat.card ι : ℤ))) :
          AlgebraicCycle (Spec (CommRingCat.of A)) ℚ) (VectorBundle.bundlePoint e x) =
      (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) x :=
  AlgebraicCycle.pullbackBundle_apply_bundlePoint e _ x

/-- The graded flat pullback along an affine vector bundle is injective. -/
theorem flatPullbackBundle_injective :
    Function.Injective (flatPullbackBundle e dimX dimE i) := by
  intro c d h
  apply Subtype.ext
  exact AlgebraicCycle.pullbackBundle_injective e (congrArg Subtype.val h)

end cyclesOfDimension


/-! ## Isomorphisms of affine bundles -/

namespace VectorBundle

section AlgEquiv

variable {R : Type u} [CommRing R] {A A' : Type u} [CommRing A] [Algebra R A]
  [CommRing A'] [Algebra R A']

/-- The scheme isomorphism of total spaces induced by an isomorphism of coordinate algebras. -/
noncomputable def specIsoOfAlgEquiv (φ : A ≃ₐ[R] A') :
    Spec (CommRingCat.of A') ≅ Spec (CommRingCat.of A) where
  hom := Spec.map (CommRingCat.ofHom φ.toRingHom)
  inv := Spec.map (CommRingCat.ofHom φ.symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => by simp)
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => by simp)

instance isIso_specMap_algEquiv (φ : A ≃ₐ[R] A') :
    IsIso (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
  ⟨(specIsoOfAlgEquiv φ).inv, (specIsoOfAlgEquiv φ).hom_inv_id, (specIsoOfAlgEquiv φ).inv_hom_id⟩

@[simp]
theorem specMap_algEquiv_base (φ : A ≃ₐ[R] A') (q : ↥(Spec (CommRingCat.of A'))) :
    (Spec.map (CommRingCat.ofHom φ.toRingHom)).base q =
      PrimeSpectrum.comap φ.toRingHom q :=
  rfl

/-- Contraction of the extended ideal along an isomorphism of `R`-algebras is the extended
ideal. -/
theorem comap_map_algebraMap (φ : A ≃ₐ[R] A') (I : Ideal R) :
    Ideal.comap φ.toRingHom (Ideal.map (algebraMap R A') I) =
      Ideal.map (algebraMap R A) I := by
  have hcomap : Ideal.comap (φ.toRingEquiv : A ≃+* A').toRingHom
      (Ideal.map (algebraMap R A') I) =
      Ideal.map ((φ.toRingEquiv : A ≃+* A').symm : A' →+* A)
        (Ideal.map (algebraMap R A') I) :=
    (Ideal.map_symm (φ.toRingEquiv : A ≃+* A')).symm
  rw [hcomap, Ideal.map_map]
  congr 1
  exact RingHom.ext fun r => φ.symm.commutes r

/-- Contraction along a ring isomorphism is injective on prime spectra. -/
theorem comap_ringEquiv_injective {B C : Type u} [CommRing B] [CommRing C] (f : B ≃+* C) :
    Function.Injective (PrimeSpectrum.comap f.toRingHom) := by
  intro P Q h
  apply PrimeSpectrum.ext
  have h' : Ideal.comap f.toRingHom P.asIdeal = Ideal.comap f.toRingHom Q.asIdeal :=
    congrArg PrimeSpectrum.asIdeal h
  have h'' := congrArg (Ideal.map f.toRingHom) h'
  have hsurj : Function.Surjective (f.toRingHom : B →+* C) := f.surjective
  rwa [Ideal.map_comap_of_surjective _ hsurj, Ideal.map_comap_of_surjective _ hsurj] at h''

variable {ι ι' : Type u}

/-- The generic points of the preimages match up under an isomorphism of bundles. -/
theorem comap_bundlePrime_algEquiv (e : A ≃ₐ[R] MvPolynomial ι R)
    (e' : A' ≃ₐ[R] MvPolynomial ι' R) (φ : A ≃ₐ[R] A') (p : PrimeSpectrum R) :
    PrimeSpectrum.comap φ.toRingHom (bundlePrime e' p) = bundlePrime e p :=
  PrimeSpectrum.ext (comap_map_algebraMap φ p.asIdeal)

/-- Two certified dimension gradings on isomorphic affine schemes agree. -/
theorem dimension_comap_algEquiv (φ : A ≃ₐ[R] A')
    (dimE : DimensionFunction (Spec (CommRingCat.of A)))
    (dimE' : DimensionFunction (Spec (CommRingCat.of A')))
    (u : ↥(Spec (CommRingCat.of A'))) :
    dimE' u = dimE ((Spec.map (CommRingCat.ofHom φ.toRingHom)).base u) := by
  have h1 : Order.coheight (show PrimeSpectrum A' from u) = (Int.toNat (dimE' u) : ℕ∞) :=
    coheight_eq_dimension A' dimE' u
  have h2 : Order.coheight (PrimeSpectrum.comap φ.toRingHom u) =
      (Int.toNat (dimE (PrimeSpectrum.comap φ.toRingHom u)) : ℕ∞) :=
    coheight_eq_dimension A dimE _
  have h3 : Order.coheight (PrimeSpectrum.comap (φ.toRingEquiv : A ≃+* A').toRingHom u) =
      Order.coheight (show PrimeSpectrum A' from u) :=
    coheight_comap_ringEquiv (φ.toRingEquiv : A ≃+* A') u
  rw [h2, h1] at h3
  have hnat : Int.toNat (dimE (PrimeSpectrum.comap φ.toRingHom u)) = Int.toNat (dimE' u) := by
    exact_mod_cast h3
  have hE := dimE.nonnegative (PrimeSpectrum.comap φ.toRingHom u)
  have hE' := dimE'.nonnegative u
  change dimE'.toFun u = dimE.toFun (PrimeSpectrum.comap φ.toRingHom u)
  omega

end AlgEquiv

/-! ## The zero section -/

section ZeroSection

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

/-- The zero section of an affine cone determined by an augmentation of its coordinate algebra
is a closed immersion, because an `R`-algebra map to `R` is automatically surjective. -/
instance isClosedImmersion_vertexSection (ε : A →ₐ[R] R) :
    IsClosedImmersion (GradedCone.vertexSection ε) :=
  GradedCone.isClosedImmersion_of_surjective ε fun r => ⟨algebraMap R A r, ε.commutes r⟩

/-- The zero section of an affine vector bundle, determined by the augmentation of its
coordinate algebra. -/
noncomputable abbrev zeroSection (ε : A →ₐ[R] R) :
    Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A) :=
  GradedCone.vertexSection ε

/-- The zero section is a section of the bundle projection. -/
theorem zeroSection_comp_projection (ε : A →ₐ[R] R) :
    zeroSection ε ≫ GradedCone.projection R A = 𝟙 _ :=
  GradedCone.vertexSection_comp_projection ε

@[simp]
theorem projection_base_zeroSection_base (ε : A →ₐ[R] R) (x : ↥(Spec (CommRingCat.of R))) :
    (GradedCone.projection R A).base ((zeroSection ε).base x) = x := by
  have h := zeroSection_comp_projection ε
  have := congrArg (fun f : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R) => f.base x) h
  exact this

/-- Pushforward of rational Chow classes along the zero section of an affine vector bundle.  It
preserves the dimension grading because the zero section is a closed immersion. -/
noncomputable def zeroSectionPushforward (ε : A →ₐ[R] R)
    {dimX : DimensionFunction (Spec (CommRingCat.of R))}
    {dimE : DimensionFunction (Spec (CommRingCat.of A))} {i : ℤ}
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
    (RE : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimE i) :
    RX.ChowGroup →ₗ[ℚ] RE.ChowGroup :=
  RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward RX (zeroSection ε) RE

@[simp]
theorem zeroSectionPushforward_quotientMap (ε : A →ₐ[R] R)
    {dimX : DimensionFunction (Spec (CommRingCat.of R))}
    {dimE : DimensionFunction (Spec (CommRingCat.of A))} {i : ℤ}
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
    (RE : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimE i)
    (z : cyclesOfDimension (Spec (CommRingCat.of R)) dimX i) :
    zeroSectionPushforward ε RX RE (RX.quotientMap z) =
      RE.quotientMap (cyclesOfDimension.properPushforward (zeroSection ε) z) :=
  rfl

end ZeroSection

/-! ## The rank-zero bundle -/

section RankZero

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} [IsEmpty ι] (e : A ≃ₐ[R] MvPolynomial ι R)

include e in
/-- A rank-zero affine vector bundle has the base as its total space: the structure map is
surjective. -/
theorem surjective_algebraMap_of_isEmpty : Function.Surjective (algebraMap R A) := by
  intro a
  refine ⟨(e.trans (MvPolynomial.isEmptyAlgEquiv R ι)) a, ?_⟩
  have h : ∀ r : R, algebraMap R A r =
      (e.trans (MvPolynomial.isEmptyAlgEquiv R ι)).symm r := fun r =>
    ((e.trans (MvPolynomial.isEmptyAlgEquiv R ι)).symm.commutes r).symm
  rw [h, AlgEquiv.symm_apply_apply]

/-- In rank zero every point of the total space is the generic point of the preimage of its
image, so the rank-zero flat pullback is the pullback along the isomorphism `E ≅ X`. -/
theorem bundlePoint_projection_base_of_isEmpty (q : ↥(Spec (CommRingCat.of A))) :
    bundlePoint e ((GradedCone.projection R A).base q) = q :=
  PrimeSpectrum.ext
    (Ideal.map_comap_of_surjective _ (surjective_algebraMap_of_isEmpty e) q.asIdeal)

theorem bundlePoint_surjective_of_isEmpty : Function.Surjective (bundlePoint e) :=
  fun q => ⟨(GradedCone.projection R A).base q, bundlePoint_projection_base_of_isEmpty e q⟩

@[simp]
theorem card_eq_zero_of_isEmpty : Nat.card ι = 0 := by
  simp

end RankZero

/-! ## The vector bundle of a finite free module -/

section SymmetricAlgebra

variable (R : Type u) [CommRing R] (F : Type u) [AddCommGroup F] [Module R F]
  [Module.Free R F] [Module.Finite R F]

/-- The canonical trivialization of the affine vector bundle `Spec Sym(F)` of a finite free
module, given by an arbitrary choice of basis. -/
noncomputable def symTrivialization :
    SymmetricAlgebra R F ≃ₐ[R] MvPolynomial (Module.Free.ChooseBasisIndex R F) R :=
  SymmetricAlgebra.equivMvPolynomial (Module.Free.chooseBasis R F)

/-- The rank of the vector bundle `Spec Sym(F)` is the rank of `F`. -/
theorem card_chooseBasisIndex [StrongRankCondition R] :
    Nat.card (Module.Free.ChooseBasisIndex R F) = Module.finrank R F := by
  rw [Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]

end SymmetricAlgebra

end VectorBundle


/-! ## Invariance under isomorphism of bundles, and the rank-zero case -/

namespace AlgebraicCycle

variable {R : Type u} [CommRing R] {A A' : Type u} [CommRing A] [Algebra R A]
  [CommRing A'] [Algebra R A'] {ι ι' : Type u}

/-- The flat pullback along an affine vector bundle is invariant under isomorphism of bundles:
transporting along an isomorphism of coordinate algebras carries one bundle pullback to the
other.  In particular it does not depend on the chosen trivialization. -/
theorem pullbackBundle_algEquiv (φ : A ≃ₐ[R] A') (e : A ≃ₐ[R] MvPolynomial ι R)
    (e' : A' ≃ₐ[R] MvPolynomial ι' R) (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ)
    (q : ↥(Spec (CommRingCat.of A'))) :
    pullbackBundle e' c q =
      pullbackBundle e c ((Spec.map (CommRingCat.ofHom φ.toRingHom)).base q) := by
  by_cases h : q ∈ Set.range (VectorBundle.bundlePoint e')
  · obtain ⟨x, rfl⟩ := h
    have hmap : (Spec.map (CommRingCat.ofHom φ.toRingHom)).base
        (VectorBundle.bundlePoint e' x) = VectorBundle.bundlePoint e x :=
      VectorBundle.comap_bundlePrime_algEquiv e e' φ x
    rw [pullbackBundle_apply_bundlePoint, hmap, pullbackBundle_apply_bundlePoint]
  · have hnot : (Spec.map (CommRingCat.ofHom φ.toRingHom)).base q ∉
        Set.range (VectorBundle.bundlePoint e) := by
      rintro ⟨x, hx⟩
      refine h ⟨x, ?_⟩
      have h1 : PrimeSpectrum.comap φ.toRingHom (VectorBundle.bundlePoint e' x) =
          VectorBundle.bundlePoint e x :=
        VectorBundle.comap_bundlePrime_algEquiv e e' φ x
      have h2 : PrimeSpectrum.comap φ.toRingHom (VectorBundle.bundlePoint e' x) =
          PrimeSpectrum.comap φ.toRingHom q := by
        rw [h1]
        exact hx
      exact VectorBundle.comap_ringEquiv_injective (φ.toRingEquiv : A ≃+* A') h2
    rw [pullbackBundle_eq_zero_of_notMem e' c h, pullbackBundle_eq_zero_of_notMem e c hnot]

variable {ι : Type u} [IsEmpty ι] (e : A ≃ₐ[R] MvPolynomial ι R)

/-- In rank zero the flat pullback along the bundle is composition with the projection, that is,
exactly the formula defining the existing flat pullback `AlgebraicCycle.pullbackOpen` along the
projection, which is then an isomorphism.  So the positive-rank construction restricts to the
rank-zero identity. -/
theorem pullbackBundle_apply_of_isEmpty (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ)
    (q : ↥(Spec (CommRingCat.of A))) :
    pullbackBundle e c q = c ((GradedCone.projection R A).base q) := by
  conv_lhs => rw [← VectorBundle.bundlePoint_projection_base_of_isEmpty e q]
  rw [pullbackBundle_apply_bundlePoint]

/-- In rank zero the bundle pullback is the flat pullback along the projection, which is an
isomorphism of schemes. -/
theorem pullbackBundle_eq_pullbackOpen_of_isEmpty
    [IsOpenImmersion (GradedCone.projection R A)]
    (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) :
    pullbackBundle e c = pullbackOpen (GradedCone.projection R A) c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  exact pullbackBundle_apply_of_isEmpty e c q

end AlgebraicCycle

namespace VectorBundle

section RankZeroIso

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} [IsEmpty ι] (e : A ≃ₐ[R] MvPolynomial ι R)

include e in
/-- The projection of a rank-zero affine vector bundle is an isomorphism of schemes. -/
theorem isIso_projection_of_isEmpty : IsIso (GradedCone.projection R A) := by
  have hcomm : ∀ r : R,
      (e.trans (MvPolynomial.isEmptyAlgEquiv R ι)).symm.toRingHom r = algebraMap R A r :=
    fun r => (e.trans (MvPolynomial.isEmptyAlgEquiv R ι)).symm.commutes r
  have hmap : GradedCone.projection R A =
      Spec.map (CommRingCat.ofHom
        (e.trans (MvPolynomial.isEmptyAlgEquiv R ι)).symm.toRingHom) := by
    rw [GradedCone.projection]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun r => (hcomm r).symm)
  rw [hmap]
  infer_instance

end RankZeroIso

/-! ## Chow groups are invariant under isomorphism of bundles -/

section ChowIso

variable {R : Type u} [CommRing R] {A A' : Type u} [CommRing A] [Algebra R A]
  [CommRing A'] [Algebra R A'] (φ : A ≃ₐ[R] A')
  {dimE : DimensionFunction (Spec (CommRingCat.of A))}
  {dimE' : DimensionFunction (Spec (CommRingCat.of A'))} {i : ℤ}
  (RE : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimE i)
  (RE' : RationalEquivalenceSystem (Spec (CommRingCat.of A')) dimE' i)

private theorem flatPullbackOpen_roundTrip
    (z : cyclesOfDimension (Spec (CommRingCat.of A')) dimE' i) :
    cyclesOfDimension.flatPullbackOpen (Spec.map (CommRingCat.ofHom φ.toRingHom))
        (dimension_comap_algEquiv φ dimE dimE')
        (cyclesOfDimension.flatPullbackOpen
          (Spec.map (CommRingCat.ofHom φ.symm.toRingHom))
          (dimension_comap_algEquiv φ.symm dimE' dimE) z) = z := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  have hid : (Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫
      (Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) = 𝟙 _ :=
    (specIsoOfAlgEquiv φ).hom_inv_id
  have hq : (Spec.map (CommRingCat.ofHom φ.symm.toRingHom)).base
      ((Spec.map (CommRingCat.ofHom φ.toRingHom)).base q) = q :=
    congrArg (fun f : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A') => f.base q) hid
  change (z : AlgebraicCycle (Spec (CommRingCat.of A')) ℚ)
    ((Spec.map (CommRingCat.ofHom φ.symm.toRingHom)).base
      ((Spec.map (CommRingCat.ofHom φ.toRingHom)).base q)) =
    (z : AlgebraicCycle (Spec (CommRingCat.of A')) ℚ) q
  rw [hq]

private theorem flatPullbackOpen_roundTrip'
    (z : cyclesOfDimension (Spec (CommRingCat.of A)) dimE i) :
    cyclesOfDimension.flatPullbackOpen (Spec.map (CommRingCat.ofHom φ.symm.toRingHom))
        (dimension_comap_algEquiv φ.symm dimE' dimE)
        (cyclesOfDimension.flatPullbackOpen
          (Spec.map (CommRingCat.ofHom φ.toRingHom))
          (dimension_comap_algEquiv φ dimE dimE') z) = z := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  have hid : (Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) ≫
      (Spec.map (CommRingCat.ofHom φ.toRingHom)) = 𝟙 _ :=
    (specIsoOfAlgEquiv φ).inv_hom_id
  have hq : (Spec.map (CommRingCat.ofHom φ.toRingHom)).base
      ((Spec.map (CommRingCat.ofHom φ.symm.toRingHom)).base q) = q :=
    congrArg (fun f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) => f.base q) hid
  change (z : AlgebraicCycle (Spec (CommRingCat.of A)) ℚ)
    ((Spec.map (CommRingCat.ofHom φ.toRingHom)).base
      ((Spec.map (CommRingCat.ofHom φ.symm.toRingHom)).base q)) =
    (z : AlgebraicCycle (Spec (CommRingCat.of A)) ℚ) q
  rw [hq]

/-- An isomorphism of the coordinate algebras of two affine vector bundles induces an
isomorphism of their dimension-graded rational Chow groups: the flat pullbacks along the two
mutually inverse open immersions are proved to be mutually inverse.  This is invariance of the
theory under isomorphism of bundles. -/
noncomputable def chowEquivOfAlgEquiv : RE.ChowGroup ≃ₗ[ℚ] RE'.ChowGroup :=
  LinearEquiv.ofLinearMap
    (RationalEquivalenceSystem.DescendingMap.openImmersionPullback RE
      (Spec.map (CommRingCat.ofHom φ.toRingHom))
      (dimension_comap_algEquiv φ dimE dimE') RE')
    (RationalEquivalenceSystem.DescendingMap.openImmersionPullback RE'
      (Spec.map (CommRingCat.ofHom φ.symm.toRingHom))
      (dimension_comap_algEquiv φ.symm dimE' dimE) RE)
    (by
      apply LinearMap.ext
      rintro ⟨z⟩
      exact congrArg (fun w => RE'.quotientMap w) (flatPullbackOpen_roundTrip φ z))
    (by
      apply LinearMap.ext
      rintro ⟨z⟩
      exact congrArg (fun w => RE.quotientMap w) (flatPullbackOpen_roundTrip' φ z))


end ChowIso

end VectorBundle


/-! ## The Gysin map of a clopen immersion, and the rank-zero zero-section Gysin map -/

namespace cyclesOfDimension

variable {X Y : Scheme.{u}} {dimX : DimensionFunction X} {dimY : DimensionFunction Y} {i : ℤ}

/-- Flat pullback along a closed immersion which is also an open immersion undoes its
residue-degree pushforward.  This is the self-intersection formula in the case where the normal
bundle has rank zero, so that its top Chern class is `1`. -/
theorem flatPullbackOpen_properPushforward (s : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsClosedImmersion s]
    [_root_.AlgebraicGeometry.IsOpenImmersion s]
    (hdim : ∀ x, dimX x = dimY (s.base x)) (z : cyclesOfDimension X dimX i) :
    flatPullbackOpen s hdim (properPushforward s z) = z := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  have hw : (dimX : X → ℤ) = fun a => dimY (s.base a) := funext hdim
  have key := AlgebraicCycle.map_closedImmersion_apply_image s (dimY : Y → ℤ)
    (z : AlgebraicCycle X ℚ) x
  rw [← hw] at key
  exact key

end cyclesOfDimension

namespace RationalEquivalenceSystem

namespace DescendingMap

variable {X Y : Scheme.{u}} {dimX : DimensionFunction X} {dimY : DimensionFunction Y} {i : ℤ}

/-- The Gysin map of a closed immersion which is also an open immersion: flat pullback is a
retraction of the Chow pushforward. -/
theorem openImmersionPullback_pushforward_eq_id
    (RX : RationalEquivalenceSystem X dimX i) (RY : RationalEquivalenceSystem Y dimY i)
    (s : X ⟶ Y) [_root_.AlgebraicGeometry.IsClosedImmersion s]
    [_root_.AlgebraicGeometry.IsOpenImmersion s]
    (hdim : ∀ x, dimX x = dimY (s.base x)) :
    (openImmersionPullback RY s hdim RX).comp (closedImmersionPushforward RX s RY) =
      LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨z⟩
  exact congrArg (fun w => RX.quotientMap w)
    (cyclesOfDimension.flatPullbackOpen_properPushforward s hdim z)

end DescendingMap

end RationalEquivalenceSystem

namespace VectorBundle

section RankZeroGysin

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  (ε : A →ₐ[R] R)

open RationalEquivalenceSystem.DescendingMap in
/-- The zero-section Gysin map of an affine vector bundle whose zero section is also an open
immersion: flat pullback along the zero section is a retraction of the zero-section pushforward.
This is the self-intersection formula in the case where the top Chern class of the bundle is
`1`, and the rank-zero bundle satisfies its hypothesis by `isIso_zeroSection_of_isEmpty`. -/
theorem zeroSectionGysin [IsOpenImmersion (zeroSection ε)]
    {dimX : DimensionFunction (Spec (CommRingCat.of R))}
    {dimE : DimensionFunction (Spec (CommRingCat.of A))} {i : ℤ}
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
    (RE : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimE i) :
    (openImmersionPullback RE (zeroSection ε)
        (fun x => DimensionFunction.apply_eq_of_isClosedImmersion dimX dimE
          (zeroSection ε) x) RX).comp
      (zeroSectionPushforward ε RX RE) = LinearMap.id :=
  openImmersionPullback_pushforward_eq_id RX RE (zeroSection ε) _

variable {ι : Type u} [IsEmpty ι] (e : A ≃ₐ[R] MvPolynomial ι R)

include e in
/-- In rank zero the zero section is a two-sided inverse of the projection. -/
theorem projection_comp_zeroSection_of_isEmpty :
    GradedCone.projection R A ≫ zeroSection ε = 𝟙 _ := by
  have := isIso_projection_of_isEmpty e
  have h : zeroSection ε = inv (GradedCone.projection R A) := by
    rw [← Category.comp_id (zeroSection ε),
      ← IsIso.hom_inv_id (GradedCone.projection R A), ← Category.assoc,
      zeroSection_comp_projection, Category.id_comp]
  rw [h, IsIso.hom_inv_id]

include e in
/-- In rank zero the zero section is an isomorphism, hence an open immersion as well as a closed
immersion, so `zeroSectionGysin` applies and the zero-section Gysin map is a genuine inverse. -/
theorem isIso_zeroSection_of_isEmpty : IsIso (zeroSection ε) := by
  refine ⟨GradedCone.projection R A, ?_, ?_⟩
  · exact zeroSection_comp_projection ε
  · exact projection_comp_zeroSection_of_isEmpty ε e

end RankZeroGysin

/-! ## The affine vector bundle of a finite free module -/

section SymBundle

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (F : Type u) [AddCommGroup F]
  [Module R F] [Module.Free R F] [Module.Finite R F]
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of (SymmetricAlgebra R F)))) (i : ℤ)

/-- Flat pullback of dimension-graded rational cycles along the affine vector bundle
`Spec Sym(F) → Spec R` of a finite free module `F`, with the proved dimension shift by the rank
of `F`. -/
noncomputable def symFlatPullback :
    cyclesOfDimension (Spec (CommRingCat.of R)) dimX i →ₗ[ℚ]
      cyclesOfDimension (Spec (CommRingCat.of (SymmetricAlgebra R F))) dimE
        (i + (Nat.card (Module.Free.ChooseBasisIndex R F) : ℤ)) :=
  cyclesOfDimension.flatPullbackBundle (symTrivialization R F) dimX dimE i

omit [IsNoetherianRing R] in
/-- The bundle `Spec Sym(F)` has rank `finrank R F`, so the pullback shifts dimension by the
rank of `F`. -/
theorem symFlatPullback_grading [StrongRankCondition R] :
    i + (Nat.card (Module.Free.ChooseBasisIndex R F) : ℤ) = i + (Module.finrank R F : ℤ) := by
  rw [card_chooseBasisIndex]

/-- The flat pullback along `Spec Sym(F)` is injective. -/
theorem symFlatPullback_injective :
    Function.Injective (symFlatPullback R F dimX dimE i) :=
  cyclesOfDimension.flatPullbackBundle_injective _ _ _ _

end SymBundle

end VectorBundle


/-! ## Invariance of the graded pullback under isomorphism of bundles -/

namespace cyclesOfDimension

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {A A' : Type u} [CommRing A] [Algebra R A]
  [CommRing A'] [Algebra R A'] {ι : Type u} [Finite ι]
  (φ : A ≃ₐ[R] A') (e : A ≃ₐ[R] MvPolynomial ι R) (e' : A' ≃ₐ[R] MvPolynomial ι R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of A)))
  (dimE' : DimensionFunction (Spec (CommRingCat.of A'))) (i : ℤ)

/-- Invariance of the graded flat pullback under an isomorphism of affine vector bundles: the
pullback to one total space, restricted along the induced isomorphism, is the pullback to the
other total space. -/
theorem flatPullbackOpen_flatPullbackBundle
    (c : cyclesOfDimension (Spec (CommRingCat.of R)) dimX i) :
    flatPullbackOpen (Spec.map (CommRingCat.ofHom φ.toRingHom))
        (VectorBundle.dimension_comap_algEquiv φ dimE dimE')
        (flatPullbackBundle e dimX dimE i c) =
      flatPullbackBundle e' dimX dimE' i c := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  exact (AlgebraicCycle.pullbackBundle_algEquiv φ e e'
    (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) q).symm

end cyclesOfDimension

end GromovWitten.AlgebraicGeometry.IntersectionTheory
