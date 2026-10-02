/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.EtalePullback
import GromovWitten.AlgebraicGeometry.IntersectionTheory.PointOrder
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleInjectiveRelation
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackDescent
import GromovWitten.Algebra.ReducedOrderSum

/-!
# Etale pullback of point-generator divisors

Let `s : R ⟶ U` be an etale morphism of locally Noetherian schemes with Noetherian underlying
spaces, and let `dimU`, `dimR` be dimension functions with `dimR r = dimU (s r)` which both
increase by exactly one along covering relations (`CovByDimension`).  For a point `w : U` and a
unit `g ∈ κ(w)ˣ`, the etale pullback of the principal divisor of `g` on the closure of `w` is
the sum, over the (finite) fibre of `s` over `w`, of the principal divisors of the images
`g ↑ w' ∈ κ(w')ˣ` on the closures of the points `w'` of the fibre.

The proof compares coefficients at a point `x'` of `R`.  The only nontrivial case is
`w ⤳ s x'` with `dimU w = dimU (s x') + 1`.  There, with `O = 𝒪_{U,s x'}`, `O' = 𝒪_{R,x'}` and
`p ⊆ O` the prime of `w`, the ring `B = O' ⧸ p O'` is a flat, unramified local extension of the
one-dimensional local domain `A = O ⧸ p` with `m_A B = m_B`, so the length order of an element
of `A` is unchanged in `B`; `B` is reduced (it embeds into its generic fibre, which is formally
unramified over the field `Frac A`), has Krull dimension at most one, and its minimal primes
are exactly the primes of the points of the fibre over `w` that specialise to `x'` (going down
for flat maps, and discreteness of etale fibres).  The order of a nonzerodivisor of a reduced
one-dimensional Noetherian local ring is the sum of its orders modulo the minimal primes
(`GromovWitten.Algebra` file `ReducedOrderSum.lean`), which gives the formula.

## Main results

* `fibre_finite_of_etale`: the fibres of an etale morphism with quasi-compact source are
  finite.
* `pullbackUnit s w' g`: the image of `g ∈ κ(s w')ˣ` in `κ(w')ˣ`; `pullbackUnitOver s w w'`:
  the same map `κ(w)ˣ →* κ(w')ˣ` for `s w' = w` (transported along `s w' = w`), and `1`
  otherwise.
* `pullbackEtale_divisor_pointGenerator`: the etale pullback of the divisor of
  `pointGenerator w g` is `∑ w' ∈ (s ⁻¹' {w}), div (pointGenerator w' (g ↑ w'))`.
* `pullbackEtale_sum_divisor_pointGenerator`: the same for a finite sum of point-generator
  divisors.
* Auxiliary results (namespace `EtalePointDivisor`): `isReduced_quotient_map`,
  `ord_quotient_map`, `mem_minimalPrimes_iff`, `krullDimLE_one_fibre`, and the local identity
  `pointOrd_eq_sum_fibre`.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace IsLocalRing

open scoped TensorProduct

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## Fibres and residue fields along an etale morphism -/

section Fibre

variable {R U : Scheme.{u}} (s : R ⟶ U)

/-- **Fibres of an etale morphism out of a quasi-compact scheme are finite.** -/
theorem fibre_finite_of_etale [Etale s] [CompactSpace R] (w : U) :
    (s.base ⁻¹' {w}).Finite := by
  choose V hxV hV using fun x : R ↦
    AlgebraicCycle.exists_isOpen_finite_inter_preimage_of_etale s x (Set.finite_singleton w)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set R))
    (fun x ↦ (V x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxV x⟩)
  refine (t.finite_toSet.biUnion fun x _ ↦ hV x).subset ?_
  intro r hr
  obtain ⟨x, hx, hrx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ r))
  exact Set.mem_iUnion₂.2 ⟨x, hx, hrx, hr⟩

/-- The image of a unit of `κ(s w')` in `κ(w')` under the residue field map of `s`. -/
noncomputable def pullbackUnit (w' : R) (g : (U.residueField (s.base w'))ˣ) :
    (R.residueField w')ˣ :=
  Units.map (s.residueFieldMap w').hom.toMonoidHom g

/-- The value of `pullbackUnit` is the image under the residue field map. -/
@[simp]
theorem pullbackUnit_val (w' : R) (g : (U.residueField (s.base w'))ˣ) :
    (pullbackUnit s w' g : R.residueField w') = s.residueFieldMap w' (g : U.residueField _) :=
  rfl

/-- `pullbackUnit` is multiplicative. -/
theorem pullbackUnit_mul (w' : R) (g h : (U.residueField (s.base w'))ˣ) :
    pullbackUnit s w' (g * h) = pullbackUnit s w' g * pullbackUnit s w' h :=
  map_mul _ _ _

open Classical in
/-- The pullback `g ↑ w'` of a unit `g` of `κ(w)` to a point `w'` of `R`: the image of `g`
under `κ(w) = κ(s w') → κ(w')` when `s w' = w`, and the junk value `1` otherwise. -/
noncomputable def pullbackUnitOver (w : U) (w' : R) :
    (U.residueField w)ˣ →* (R.residueField w')ˣ :=
  if h : s.base w' = w then
    (Units.map (s.residueFieldMap w').hom.toMonoidHom).comp
      (Units.map (U.residueFieldCongr h.symm).hom.hom.toMonoidHom)
  else 1

/-- Over the image point, `pullbackUnitOver` is `pullbackUnit`. -/
theorem pullbackUnitOver_self (w' : R) (g : (U.residueField (s.base w'))ˣ) :
    pullbackUnitOver s (s.base w') w' g = pullbackUnit s w' g := by
  rw [pullbackUnitOver, dif_pos rfl]
  ext
  simp [pullbackUnit]

/-- Compatibility of `pointStalkMap` with the stalk and residue field maps of a morphism. -/
theorem residueFieldMap_pointStalkMap_etale {y x' : R} (h : y ⤳ x') (hs : s.base y ⤳ s.base x')
    (t : U.presheaf.stalk (s.base x')) :
    s.residueFieldMap y (pointStalkMap hs t) = pointStalkMap h (s.stalkMap x' t) := by
  rw [pointStalkMap_apply, pointStalkMap_apply,
    ← Scheme.Hom.stalkSpecializes_stalkMap_apply]
  exact congrArg (fun φ : U.presheaf.stalk (s.base y) ⟶ R.residueField y ↦
    φ.hom (U.presheaf.stalkSpecializes hs t)) (Scheme.residue_residueFieldMap s y)

/-- The pullback of the image of `t ∈ 𝒪_{U,s x'}` in `κ(w)` to a point `w'` of the fibre over
`w` with `w' ⤳ x'` is the image of `s^♯ t ∈ 𝒪_{R,x'}` in `κ(w')`. -/
theorem pullbackUnitOver_val_pointStalkMap {w : U} {w' x' : R} (e : s.base w' = w)
    (hwx : w ⤳ s.base x') (h : w' ⤳ x') (u : (U.residueField w)ˣ)
    (t : U.presheaf.stalk (s.base x')) (hu : (u : U.residueField w) = pointStalkMap hwx t) :
    (pullbackUnitOver s w w' u : R.residueField w') = pointStalkMap h (s.stalkMap x' t) := by
  subst e
  rw [pullbackUnitOver_self, pullbackUnit_val, hu]
  exact residueFieldMap_pointStalkMap_etale s h hwx t

/-- The prime of `𝒪_{R,x'}` of a generization `y` of `x'` pulls back to the prime of
`𝒪_{U,s x'}` of `s y`. -/
theorem comap_ker_pointStalkMap {y x' : R} (h : y ⤳ x') (hs : s.base y ⤳ s.base x') :
    (RingHom.ker (pointStalkMap h)).comap (s.stalkMap x').hom =
      RingHom.ker (pointStalkMap hs) := by
  ext t
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  rw [← residueFieldMap_pointStalkMap_etale s h hs]
  exact map_eq_zero_iff _ (s.residueFieldMap y).hom.injective

end Fibre

namespace EtalePointDivisor

/-! ## Commutative algebra of the quotient of a flat unramified local extension -/

section Algebra

variable {O O' : Type*} [CommRing O] [CommRing O'] [Algebra O O'] (p : Ideal O)

/-- Flatness is inherited by the reduction modulo an ideal of the base. -/
theorem flat_quotient_map [Module.Flat O O'] :
    Module.Flat (O ⧸ p) (O' ⧸ p.map (algebraMap O O')) :=
  Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor O' p).toLinearEquiv

variable (O') [IsLocalRing O] [IsLocalRing O'] [IsLocalHom (algebraMap O O')]

/-- For a local extension, a proper ideal of the base generates an ideal contained in the
maximal ideal. -/
theorem map_le_maximalIdeal (hp : p ≠ ⊤) :
    p.map (algebraMap O O') ≤ maximalIdeal O' := by
  exact (Ideal.map_mono (le_maximalIdeal hp)).trans
    (((local_hom_TFAE (algebraMap O O')).out 0 2 rfl rfl).mp inferInstance)

/-- The reduction of a local extension modulo a proper ideal of the base is nonzero. -/
theorem nontrivial_quotient_map (hp : p ≠ ⊤) :
    Nontrivial (O' ⧸ p.map (algebraMap O O')) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal O').ne_top (map_le_maximalIdeal O' p hp))

/-- The reduction of a local extension modulo a proper ideal of the base is local. -/
theorem isLocalRing_quotient_map (hp : p ≠ ⊤) :
    IsLocalRing (O' ⧸ p.map (algebraMap O O')) :=
  have := nontrivial_quotient_map O' p hp
  .of_surjective' _ Ideal.Quotient.mk_surjective

/-- Reduction modulo an ideal of the base preserves locality of the extension. -/
theorem isLocalHom_quotient_map (hp : p ≠ ⊤) :
    IsLocalHom (algebraMap (O ⧸ p) (O' ⧸ p.map (algebraMap O O'))) := by
  have := nontrivial_quotient_map O' p hp
  have : IsLocalHom (Ideal.Quotient.mk (p.map (algebraMap O O'))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h : IsUnit (Ideal.Quotient.mk (p.map (algebraMap O O')) (algebraMap O O' o)) := ha
  exact (isUnit_of_map_unit _ _ (isUnit_of_map_unit _ _ h)).map _

variable [p.IsPrime] [Algebra.FormallyUnramified O O'] [Algebra.EssFiniteType O O']

/-- For a formally unramified, essentially finite type local extension, the maximal ideal of
the reduction modulo a prime `p` of the base generates the maximal ideal of the reduction. -/
theorem map_maximalIdeal_quotient_map :
    letI := isLocalRing_quotient_map O' p (Ideal.IsPrime.ne_top ‹_›)
    letI : IsLocalRing (O ⧸ p) := .of_surjective' _ Ideal.Quotient.mk_surjective
    (maximalIdeal (O ⧸ p)).map (algebraMap (O ⧸ p) (O' ⧸ p.map (algebraMap O O'))) =
      maximalIdeal (O' ⧸ p.map (algebraMap O O')) := by
  let _ := isLocalRing_quotient_map O' p (Ideal.IsPrime.ne_top ‹_›)
  let _ : IsLocalRing (O ⧸ p) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have := isLocalHom_quotient_map O' p (Ideal.IsPrime.ne_top ‹_›)
  exact Algebra.FormallyUnramified.map_maximalIdeal

/-- The length order is preserved by the reduction modulo a prime `p` of the base of a flat,
formally unramified, essentially finite type local extension. -/
theorem ord_quotient_map [Module.Flat O O'] (o : O) :
    Ring.ord (O' ⧸ p.map (algebraMap O O'))
        (Ideal.Quotient.mk (p.map (algebraMap O O')) (algebraMap O O' o)) =
      Ring.ord (O ⧸ p) (Ideal.Quotient.mk p o) := by
  let _ := isLocalRing_quotient_map O' p (Ideal.IsPrime.ne_top ‹_›)
  let _ : IsLocalRing (O ⧸ p) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have := isLocalHom_quotient_map O' p (Ideal.IsPrime.ne_top ‹_›)
  have := flat_quotient_map (O' := O') p
  exact Ring.ord_algebraMap_of_flat_local_of_map_maximalIdeal
    (map_maximalIdeal_quotient_map O' p) (Ideal.Quotient.mk p o)

omit [IsLocalRing O] [IsLocalRing O'] [IsLocalHom (algebraMap O O')] in
/-- The reduction modulo a prime `p` of the base of a flat, formally unramified, essentially
finite type extension is reduced: it embeds into its generic fibre, which is formally unramified
and essentially of finite type over the field `Frac (O ⧸ p)`. -/
theorem isReduced_quotient_map [Module.Flat O O'] :
    IsReduced (O' ⧸ p.map (algebraMap O O')) := by
  set A := O ⧸ p
  set B := O' ⧸ p.map (algebraMap O O')
  let K := FractionRing A
  have := flat_quotient_map (O' := O') p
  have : IsReduced (K ⊗[A] B) := Algebra.FormallyUnramified.isReduced_of_field K _
  refine isReduced_of_injective (Algebra.TensorProduct.includeRight (R := A) (A := K)
    (B := B)).toRingHom ?_
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := B)
    (Algebra.linearMap A K) (IsFractionRing.injective A K)
  have : ⇑(Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B)) =
      (LinearMap.rTensor B (Algebra.linearMap A K)) ∘ (TensorProduct.lid A B).symm := by
    ext b
    simp
  change Function.Injective (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B))
  rw [this]
  exact hinj.comp (TensorProduct.lid A B).symm.injective

end Algebra

/-! ## Primes of the local ring of the preimage of the closure of a point -/

section LocalPrimes

variable {R U : Scheme.{u}} (s : R ⟶ U) {w : U} {x' : R} (hwx : w ⤳ s.base x')

/-- The extension `p 𝒪_{R,x'}` of the prime `p ⊆ 𝒪_{U,s x'}` of a generization `w` of `s x'`:
the quotient `𝒪_{R,x'} ⧸ p 𝒪_{R,x'}` is the local ring at `x'` of the scheme-theoretic preimage
of the closure of `w`. -/
noncomputable abbrev fibreIdeal : Ideal (R.presheaf.stalk x') :=
  (RingHom.ker (pointStalkMap hwx)).map (s.stalkMap x').hom

/-- The prime of `𝒪_{R,x'} ⧸ p 𝒪_{R,x'}` attached to a generization `y` of `x'`. -/
noncomputable abbrev fibrePrime {y : R} (hy : y ⤳ x') :
    Ideal (R.presheaf.stalk x' ⧸ fibreIdeal s hwx) :=
  (RingHom.ker (pointStalkMap hy)).map (Ideal.Quotient.mk (fibreIdeal s hwx))

/-- The prime of a generization `y` of `x'` contains `p 𝒪_{R,x'}` iff `w ⤳ s y`. -/
theorem fibreIdeal_le_iff {y : R} (hy : y ⤳ x') :
    fibreIdeal s hwx ≤ RingHom.ker (pointStalkMap hy) ↔ w ⤳ s.base y := by
  rw [Ideal.map_le_iff_le_comap, comap_ker_pointStalkMap s hy (s.base.hom.map_specializes hy)]
  exact ker_pointStalkMap_le_iff hwx _

/-- The ideal `fibrePrime` of a generization `y` of `x'` with `w ⤳ s y` is prime. -/
theorem isPrime_fibrePrime {y : R} (hy : y ⤳ x') (hwy : w ⤳ s.base y) :
    (fibrePrime s hwx hy).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact (fibreIdeal_le_iff s hwx hy).2 hwy)

/-- The preimage of `fibrePrime s hwx hy` in `𝒪_{R,x'}` is the prime of `y`. -/
theorem comap_fibrePrime {y : R} (hy : y ⤳ x') (hwy : w ⤳ s.base y) :
    (fibrePrime s hwx hy).comap (Ideal.Quotient.mk _) = RingHom.ker (pointStalkMap hy) :=
  Ideal.comap_map_mk ((fibreIdeal_le_iff s hwx hy).2 hwy)

/-- Inclusions of the primes `fibrePrime` reflect specialisation. -/
theorem specializes_of_fibrePrime_le {y₁ y₂ : R} (hy₁ : y₁ ⤳ x') (hy₂ : y₂ ⤳ x')
    (hw₁ : w ⤳ s.base y₁) (hw₂ : w ⤳ s.base y₂)
    (hle : fibrePrime s hwx hy₁ ≤ fibrePrime s hwx hy₂) : y₁ ⤳ y₂ := by
  have := Ideal.comap_mono (f := Ideal.Quotient.mk (fibreIdeal s hwx)) hle
  rw [comap_fibrePrime s hwx hy₁ hw₁, comap_fibrePrime s hwx hy₂ hw₂] at this
  exact (ker_pointStalkMap_le_iff hy₁ hy₂).1 this

/-- Every prime of `𝒪_{R,x'} ⧸ p 𝒪_{R,x'}` is the prime of a generization `y` of `x'` with
`w ⤳ s y`. -/
theorem exists_fibrePrime_eq (q : Ideal (R.presheaf.stalk x' ⧸ fibreIdeal s hwx))
    [q.IsPrime] : ∃ (y : R) (hy : y ⤳ x'), w ⤳ s.base y ∧ q = fibrePrime s hwx hy := by
  obtain ⟨y, hy, hP⟩ := exists_ker_pointStalkMap_eq (q.comap (Ideal.Quotient.mk _))
  have hle : fibreIdeal s hwx ≤ RingHom.ker (pointStalkMap hy) := by
    rw [hP]
    intro a ha
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact q.zero_mem
  refine ⟨y, hy, (fibreIdeal_le_iff s hwx hy).1 hle, ?_⟩
  rw [fibrePrime, hP, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

include hwx in
/-- **Going down along the flat stalk map.**  A generization `y` of `x'` with `w ⤳ s y` has a
generization `y'` lying over `w`. -/
theorem exists_specializes_eq [Flat s] {y : R} (hy : y ⤳ x') (hwy : w ⤳ s.base y) :
    ∃ (y' : R) (_ : y' ⤳ x'), y' ⤳ y ∧ s.base y' = w := by
  have hgen := RingHom.Flat.generalizingMap_comap (Flat.stalkMap s x')
  let P : PrimeSpectrum (R.presheaf.stalk x') := ⟨RingHom.ker (pointStalkMap hy), inferInstance⟩
  let e : PrimeSpectrum (U.presheaf.stalk (s.base x')) :=
    ⟨RingHom.ker (pointStalkMap hwx), inferInstance⟩
  have hcomap : (PrimeSpectrum.comap (s.stalkMap x').hom P).asIdeal =
      RingHom.ker (pointStalkMap (s.base.hom.map_specializes hy)) :=
    comap_ker_pointStalkMap s hy _
  have he : e ⤳ PrimeSpectrum.comap (s.stalkMap x').hom P := by
    rw [← PrimeSpectrum.le_iff_specializes]
    change RingHom.ker (pointStalkMap hwx) ≤ _
    rw [hcomap]
    exact (ker_pointStalkMap_le_iff hwx _).2 hwy
  obtain ⟨P', hP'P, hP'e⟩ := hgen he
  obtain ⟨y', hy', hy'P⟩ := exists_ker_pointStalkMap_eq P'.asIdeal
  refine ⟨y', hy', ?_, ?_⟩
  · rw [← ker_pointStalkMap_le_iff hy' hy, hy'P]
    exact (PrimeSpectrum.le_iff_specializes _ _).2 hP'P
  · have h1 : RingHom.ker (pointStalkMap (s.base.hom.map_specializes hy')) =
        RingHom.ker (pointStalkMap hwx) := by
      rw [← comap_ker_pointStalkMap s hy', hy'P]
      exact congrArg PrimeSpectrum.asIdeal hP'e
    have h2 := (ker_pointStalkMap_le_iff _ hwx).1 h1.le
    have h3 := (ker_pointStalkMap_le_iff hwx _).1 h1.ge
    exact (h2.antisymm h3).eq

/-- **Minimal primes of `𝒪_{R,x'} ⧸ p 𝒪_{R,x'}`** are exactly the primes of the generizations
of `x'` lying over `w`. -/
theorem mem_minimalPrimes_iff [Etale s] (q : Ideal (R.presheaf.stalk x' ⧸ fibreIdeal s hwx)) :
    q ∈ minimalPrimes _ ↔ ∃ (y : R) (hy : y ⤳ x'), s.base y = w ∧ q = fibrePrime s hwx hy := by
  constructor
  · intro hq
    have : q.IsPrime := hq.1.1
    obtain ⟨y, hy, hwy, rfl⟩ := exists_fibrePrime_eq s hwx q
    obtain ⟨y', hy', hy'y, hy'w⟩ := exists_specializes_eq s hwx hy hwy
    have hw' : w ⤳ s.base y' := hy'w ▸ specializes_rfl
    have hp' := isPrime_fibrePrime s hwx hy' hw'
    have hle : fibrePrime s hwx hy' ≤ fibrePrime s hwx hy :=
      Ideal.map_mono ((ker_pointStalkMap_le_iff hy' hy).2 hy'y)
    exact ⟨y', hy', hy'w, le_antisymm (hq.2 ⟨hp', bot_le⟩ hle) hle⟩
  · rintro ⟨y, hy, rfl, rfl⟩
    have hwy : s.base y ⤳ s.base y := specializes_rfl
    refine ⟨⟨isPrime_fibrePrime s hwx hy hwy, bot_le⟩, fun q' hq' hle ↦ ?_⟩
    have : q'.IsPrime := hq'.1
    obtain ⟨y'', hy'', hwy'', rfl⟩ := exists_fibrePrime_eq s hwx q'
    have h1 := specializes_of_fibrePrime_le s hwx hy'' hy hwy'' hwy hle
    have h2 : s.base y'' = s.base y :=
      ((s.base.hom.map_specializes h1).antisymm hwy'').eq
    obtain rfl := Curves.eq_of_specializes_of_etale s h1 h2
    exact le_rfl

/-- Distinct points give distinct primes `fibrePrime`. -/
theorem fibrePrime_injective {y₁ y₂ : R} (hy₁ : y₁ ⤳ x') (hy₂ : y₂ ⤳ x')
    (hw₁ : w ⤳ s.base y₁) (hw₂ : w ⤳ s.base y₂)
    (h : fibrePrime s hwx hy₁ = fibrePrime s hwx hy₂) : y₁ = y₂ :=
  ((specializes_of_fibrePrime_le s hwx hy₁ hy₂ hw₁ hw₂ h.le).antisymm
    (specializes_of_fibrePrime_le s hwx hy₂ hy₁ hw₂ hw₁ h.ge)).eq

/-- The quotient of `𝒪_{R,x'} ⧸ p 𝒪_{R,x'}` by the prime of `y` is the point stalk of
`y ⤳ x'`. -/
noncomputable def fibrePrimeQuotientEquiv {y : R} (hy : y ⤳ x') (hwy : w ⤳ s.base y) :
    (R.presheaf.stalk x' ⧸ fibreIdeal s hwx) ⧸ fibrePrime s hwx hy ≃+* pointStalk hy :=
  DoubleQuot.quotQuotEquivQuotOfLE ((fibreIdeal_le_iff s hwx hy).2 hwy)

/-- `fibrePrimeQuotientEquiv` on the class of an element of `𝒪_{R,x'}`. -/
theorem fibrePrimeQuotientEquiv_mk {y : R} (hy : y ⤳ x') (hwy : w ⤳ s.base y)
    (a : R.presheaf.stalk x') :
    fibrePrimeQuotientEquiv s hwx hy hwy (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a)) =
      Ideal.Quotient.mk _ a :=
  DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk a _

/-- A point between the two ends of a covering pair in the specialisation order of a scheme is
one of the two ends. -/
theorem eq_or_eq_of_covBy {X : Scheme.{u}} {a b c : X} (h : a ⋖ b) (hac : a ≤ c) (hcb : c ≤ b) :
    c = a ∨ c = b := by
  by_cases hbc : b ≤ c
  · exact Or.inr ((show b ⤳ c from hcb).antisymm (show c ⤳ b from hbc)).eq.symm
  · have hlt : c < b := lt_of_le_not_ge hcb hbc
    have hca : c ≤ a := by
      by_contra hca
      exact h.2 (lt_of_le_not_ge hac hca) hlt
    exact Or.inl ((show c ⤳ a from hac).antisymm (show a ⤳ c from hca)).eq

/-- If `s x'` is covered by `w`, every prime of `𝒪_{R,x'} ⧸ p 𝒪_{R,x'}` is minimal or
maximal, so this ring has Krull dimension at most one. -/
theorem krullDimLE_one_fibre [Etale s] (hcov : s.base x' ⋖ w) :
    Ring.KrullDimLE 1 (R.presheaf.stalk x' ⧸ fibreIdeal s hwx) := by
  refine Ring.KrullDimLE.mk₁ fun q hq ↦ ?_
  obtain ⟨y, hy, hwy, rfl⟩ := exists_fibrePrime_eq s hwx q
  have hle1 : s.base x' ≤ s.base y := s.base.hom.map_specializes hy
  rcases eq_or_eq_of_covBy hcov hle1 hwy with h | h
  · right
    obtain rfl := Curves.eq_of_specializes_of_etale s hy h
    have hfield : IsField (pointStalk hy) := isField_pointStalk_refl y
    exact Ideal.Quotient.maximal_of_isField _
      ((fibrePrimeQuotientEquiv s hwx hy hwy).toMulEquiv.isField hfield)
  · exact Or.inl ((mem_minimalPrimes_iff s hwx _).2 ⟨y, hy, h, rfl⟩)

end LocalPrimes

/-! ## Orders along point stalks -/

section PointOrdStalk

/-- `pointOrd` of the image of an element of the stalk is its length order in the point
stalk. -/
theorem pointOrd_mk0_pointStalkMap {X : Scheme.{u}} [IsLocallyNoetherian X] {a b : X}
    (h : a ⤳ b) (hd : ringKrullDim (pointStalk h) = 1) (t : X.presheaf.stalk b)
    (ht : pointStalkMap h t ≠ 0) :
    pointOrd h (Units.mk0 _ ht) =
      ((Ring.ord (pointStalk h) (Ideal.Quotient.mk _ t)).toNat : ℤ) := by
  have := krullDimLE_one_pointStalk_of_eq_one hd
  have hne : (Ideal.Quotient.mk (RingHom.ker (pointStalkMap h)) t) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker]
  have hnz := mem_nonZeroDivisors_of_ne_zero hne
  apply Multiplicative.ofAdd.injective
  apply WithZero.coe_injective (α := Multiplicative ℤ)
  rw [pointOrd_of_eq_one hd]
  change Ring.ordFrac (pointStalk h)
    (algebraMap (pointStalk h) (X.residueField a) (Ideal.Quotient.mk _ t)) = _
  rw [Ring.ordFrac_eq_ord (pointStalk h) hne, Ring.ordMonoidWithZeroHom_eq_coe _ hnz
    (ENat.natCast_toNat (Ring.ord_ne_top hnz)).symm]

end PointOrdStalk

/-! ## The local identity -/

section LocalIdentity

variable {R U : Scheme.{u}} (s : R ⟶ U) [Etale s] [IsLocallyNoetherian U]
  [IsLocallyNoetherian R] {w : U} {x' : R}

open Classical in
/-- **The local identity behind the etale pullback of a point divisor.**  Let `w ⤳ s x'` with
`s x'` covered by `w`, and let `t ∈ 𝒪_{U,s x'}` have nonzero image in `κ(w)`.  Then the order of
`t` along the closure of `w` at `s x'` is the sum, over the points `y` of the fibre `F` of `s`
over `w` which specialise to `x'`, of the order of the pulled back function along the closure of
`y` at `x'`. -/
theorem pointOrd_eq_sum_fibre (F : Finset R) (hF : ∀ y, y ∈ F ↔ s.base y = w)
    (hwx : w ⤳ s.base x') (hcov : s.base x' ⋖ w) (hd : ringKrullDim (pointStalk hwx) = 1)
    (hd' : ∀ (y : R) (hy : y ⤳ x'), s.base y = w → ringKrullDim (pointStalk hy) = 1)
    (t : U.presheaf.stalk (s.base x')) (ht : pointStalkMap hwx t ≠ 0) :
    (pointOrd hwx (Units.mk0 _ ht) : ℚ) =
      ∑ y ∈ F, if hy : y ⤳ x' then
        (pointOrd hy (pullbackUnitOver s w y (Units.mk0 _ ht)) : ℚ) else 0 := by
  classical
  let O := U.presheaf.stalk (s.base x')
  let O' := R.presheaf.stalk x'
  let _ : Algebra O O' := (s.stalkMap x').hom.toAlgebra
  have : Module.Flat O O' := Flat.stalkMap s x'
  have : Algebra.FormallyUnramified O O' := FormallyUnramified.stalkMap s x'
  have : Algebra.EssFiniteType O O' := LocallyOfFiniteType.stalkMap s x'
  have : IsLocalHom (algebraMap O O') := inferInstanceAs (IsLocalHom (s.stalkMap x').hom)
  let p := RingHom.ker (pointStalkMap hwx)
  let _ : IsLocalRing (O' ⧸ fibreIdeal s hwx) :=
    isLocalRing_quotient_map O' p (Ideal.IsPrime.ne_top inferInstance)
  have : IsReduced (O' ⧸ fibreIdeal s hwx) := isReduced_quotient_map (O' := O') p
  have : Ring.KrullDimLE 1 (O' ⧸ fibreIdeal s hwx) := krullDimLE_one_fibre s hwx hcov
  set g : O' ⧸ fibreIdeal s hwx := Ideal.Quotient.mk (fibreIdeal s hwx) (s.stalkMap x' t)
    with hg_def
  have hval : ∀ (y : R) (hy : y ⤳ x'), s.base y = w →
      pointStalkMap hy (s.stalkMap x' t) ≠ 0 := by
    intro y hy e hz
    rw [← pullbackUnitOver_val_pointStalkMap s e hwx hy (Units.mk0 _ ht) t rfl] at hz
    exact (Units.ne_zero _ hz).elim
  have hg : ∀ q ∈ minimalPrimes (O' ⧸ fibreIdeal s hwx), g ∉ q := by
    intro q hq hgq
    obtain ⟨y, hy, e, rfl⟩ := (mem_minimalPrimes_iff s hwx q).1 hq
    have hwy : w ⤳ s.base y := e ▸ specializes_rfl
    have := Ideal.mem_comap.2 hgq
    rw [comap_fibrePrime s hwx hy hwy, RingHom.mem_ker] at this
    exact hval y hy e this
  have key := GromovWitten.Algebra.reducedOrd_toNat_eq_sum_minimalPrimes g hg
  have hord : Ring.ord (O' ⧸ fibreIdeal s hwx) g = Ring.ord (pointStalk hwx)
      (Ideal.Quotient.mk _ t) := ord_quotient_map O' p t
  rw [pointOrd_mk0_pointStalkMap hwx hd t ht, ← hord, key]
  have hfilter : (∑ y ∈ F, if hy : y ⤳ x' then
        (pointOrd hy (pullbackUnitOver s w y (Units.mk0 _ ht)) : ℚ) else 0) =
      ∑ y ∈ F.filter (· ⤳ x'), if hy : y ⤳ x' then
        (pointOrd hy (pullbackUnitOver s w y (Units.mk0 _ ht)) : ℚ) else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    split_ifs <;> rfl
  rw [hfilter]
  push_cast
  symm
  refine Finset.sum_bij (fun y hy ↦ fibrePrime s hwx (Finset.mem_filter.1 hy).2) ?_ ?_ ?_ ?_
  · intro y hy
    rw [Set.Finite.mem_toFinset, mem_minimalPrimes_iff s hwx]
    exact ⟨y, _, (hF y).1 (Finset.mem_filter.1 hy).1, rfl⟩
  · intro y₁ hy₁ y₂ hy₂ h
    have e₁ := (hF y₁).1 (Finset.mem_filter.1 hy₁).1
    have e₂ := (hF y₂).1 (Finset.mem_filter.1 hy₂).1
    exact fibrePrime_injective s hwx _ _ (e₁ ▸ specializes_rfl) (e₂ ▸ specializes_rfl) h
  · intro q hq
    rw [Set.Finite.mem_toFinset, mem_minimalPrimes_iff s hwx] at hq
    obtain ⟨y, hy, e, rfl⟩ := hq
    exact ⟨y, Finset.mem_filter.2 ⟨(hF y).2 e, hy⟩, rfl⟩
  · intro y hyF
    obtain ⟨hyF', hy⟩ := Finset.mem_filter.1 hyF
    have e := (hF y).1 hyF'
    have hwy : w ⤳ s.base y := e ▸ specializes_rfl
    rw [dif_pos hy]
    have hunit : pullbackUnitOver s w y (Units.mk0 _ ht) = Units.mk0 _ (hval y hy e) :=
      Units.ext (pullbackUnitOver_val_pointStalkMap s e hwx hy _ t rfl)
    rw [hunit, pointOrd_mk0_pointStalkMap hy (hd' y hy e), ← LocalOrdSymmetry.ord_ringEquiv
      (fibrePrimeQuotientEquiv s hwx hy hwy), hg_def, fibrePrimeQuotientEquiv_mk]
    push_cast
    rfl

end LocalIdentity

end EtalePointDivisor

/-! ## The etale pullback of a point-generator divisor -/

section Main

open LineBundleInjective EtalePointDivisor

variable {R U : Scheme.{u}} (s : R ⟶ U) [Etale s] [IsLocallyNoetherian U]
  [IsLocallyNoetherian R] [NoetherianSpace U] [NoetherianSpace R]

omit [Etale s] [IsLocallyNoetherian U] [NoetherianSpace U] [NoetherianSpace R] in
open Classical in
/-- The sum over the fibre is additive in the unit. -/
theorem sum_fibre_pointOrd_mul_inv (F : Finset R) (w : U) (x' : R)
    (u v : (U.residueField w)ˣ) :
    (∑ y ∈ F, if hy : y ⤳ x' then
        (pointOrd hy (pullbackUnitOver s w y (u * v⁻¹)) : ℚ) else 0) =
      (∑ y ∈ F, if hy : y ⤳ x' then (pointOrd hy (pullbackUnitOver s w y u) : ℚ) else 0) -
        ∑ y ∈ F, if hy : y ⤳ x' then (pointOrd hy (pullbackUnitOver s w y v) : ℚ) else 0 := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  split_ifs with hy
  · rw [map_mul, map_inv, pointOrd_mul, pointOrd_inv]
    push_cast
    ring
  · simp

/-- **Etale pullback of a point-generator divisor (Blueprint S2).**  For an etale morphism
`s : R ⟶ U` of locally Noetherian schemes with Noetherian underlying spaces, dimension functions
with `dimR r = dimU (s r)`, both satisfying `CovByDimension`, a point `w : U` and a unit
`g ∈ κ(w)ˣ`, the etale pullback of the divisor of `pointGenerator w g` is the sum, over the
finite fibre of `s` over `w`, of the divisors of the pulled back units `g ↑ w'`. -/
theorem pullbackEtale_divisor_pointGenerator (dimU : DimensionFunction U)
    (dimR : DimensionFunction R) (hdim : ∀ r, dimR r = dimU (s.base r))
    (hcovU : HomogeneityLocal.CovByDimension dimU) (hcovR : HomogeneityLocal.CovByDimension dimR)
    (w : U) (g : (U.residueField w)ˣ) :
    AlgebraicCycle.pullbackEtale s ((pointGenerator w g).divisor dimU) =
      ∑ w' ∈ (fibre_finite_of_etale s w).toFinset,
        (pointGenerator w' (pullbackUnitOver s w w' g)).divisor dimR := by
  classical
  apply Function.locallyFinsuppWithin.coe_injective
  funext x'
  beta_reduce
  rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    AlgebraicCycle.pullbackEtale_apply]
  set F := (fibre_finite_of_etale s w).toFinset
  have hF : ∀ y, y ∈ F ↔ s.base y = w := by simp [F]
  have hterm : ∀ y ∈ F, ((pointGenerator y (pullbackUnitOver s w y g)).divisor dimR : R → ℚ) x' =
      if hy : y ⤳ x' then (pointOrd hy (pullbackUnitOver s w y g) : ℚ) else 0 := by
    intro y _
    split_ifs with hy
    · exact divisor_pointGenerator_apply dimR y _ hy
    · exact divisor_pointGenerator_apply_eq_zero dimR y _ x' hy
  rw [Finset.sum_congr rfl hterm]
  by_cases hwx : w ⤳ s.base x'
  swap
  · rw [divisor_pointGenerator_apply_eq_zero dimU w g _ hwx]
    symm
    refine Finset.sum_eq_zero fun y hyF ↦ dif_neg fun hy ↦ hwx ?_
    have := s.base.hom.map_specializes hy
    rwa [(hF y).1 hyF] at this
  rw [divisor_pointGenerator_apply dimU w g hwx]
  by_cases hd : dimU w = dimU (s.base x') + 1
  swap
  · rw [pointOrd_eq_zero_of_dim_ne dimU hcovU hwx hd]
    symm
    refine Finset.sum_eq_zero fun y hyF ↦ ?_
    split_ifs with hy
    · rw [pointOrd_eq_zero_of_dim_ne dimR hcovR hy (by rw [hdim, hdim, (hF y).1 hyF]; exact hd)]
      simp
    · rfl
  have hcov := covBy_of_dim_eq_add_one dimU hwx hd
  have hd1 := ringKrullDim_pointStalk_eq_one_of_dim_eq dimU hwx hd
  have hd' : ∀ (y : R) (hy : y ⤳ x'), s.base y = w → ringKrullDim (pointStalk hy) = 1 :=
    fun y hy e ↦ ringKrullDim_pointStalk_eq_one_of_dim_eq dimR hy
      (by rw [hdim, hdim, e]; exact hd)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := pointStalk hwx)
    (g : U.residueField w)
  obtain ⟨ta, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨tb, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hb0 : pointStalkMap hwx tb ≠ 0 := by
    rw [← pointStalk_algebraMap_mk]
    exact (map_ne_zero_iff _ (pointStalk_algebraMap_injective hwx)).2
      (nonZeroDivisors.ne_zero hb)
  have ha0 : pointStalkMap hwx ta ≠ 0 := by
    intro h0
    rw [pointStalk_algebraMap_mk, h0, zero_div] at hab
    exact g.ne_zero hab.symm
  have hg : g = Units.mk0 _ ha0 * (Units.mk0 _ hb0)⁻¹ := by
    ext
    rw [← hab, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0,
      div_eq_mul_inv, pointStalk_algebraMap_mk, pointStalk_algebraMap_mk]
  rw [hg, sum_fibre_pointOrd_mul_inv, pointOrd_mul, pointOrd_inv,
    ← pointOrd_eq_sum_fibre s F hF hwx hcov hd1 hd' ta ha0,
    ← pointOrd_eq_sum_fibre s F hF hwx hcov hd1 hd' tb hb0]
  push_cast
  ring

/-- **Etale pullback of a finite sum of point-generator divisors.**  For a finite set `S` of
points of `U` and a unit `v w ∈ κ(w)ˣ` for every `w`, the etale pullback of
`∑ w ∈ S, div (pointGenerator w (v w))` is the sum, over the (finite) preimage of `S`, of the
divisors of the pulled back units. -/
theorem pullbackEtale_sum_divisor_pointGenerator (dimU : DimensionFunction U)
    (dimR : DimensionFunction R) (hdim : ∀ r, dimR r = dimU (s.base r))
    (hcovU : HomogeneityLocal.CovByDimension dimU) (hcovR : HomogeneityLocal.CovByDimension dimR)
    (S : Finset U) (v : ∀ w : U, (U.residueField w)ˣ) :
    AlgebraicCycle.pullbackEtale s (∑ w ∈ S, (pointGenerator w (v w)).divisor dimU) =
      ∑ w' ∈ (S.finite_toSet.preimage' fun w _ ↦ fibre_finite_of_etale s w).toFinset,
        (pointGenerator w' (pullbackUnit s w' (v (s.base w')))).divisor dimR := by
  classical
  have h1 : AlgebraicCycle.pullbackEtale s (∑ w ∈ S, (pointGenerator w (v w)).divisor dimU) =
      ∑ w ∈ S, AlgebraicCycle.pullbackEtale s ((pointGenerator w (v w)).divisor dimU) :=
    map_sum (AlgebraicCycle.pullbackEtaleLinear s) _ S
  rw [h1, Finset.sum_congr rfl fun w _ ↦
    pullbackEtale_divisor_pointGenerator s dimU dimR hdim hcovU hcovR w (v w)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := s.base) (t := S) (fun x hx ↦ by simpa using hx)]
  refine Finset.sum_congr rfl fun w hw ↦ Finset.sum_congr ?_ fun w' hw' ↦ ?_
  · ext w'
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
      Finset.mem_filter, Finset.mem_coe]
    constructor
    · rintro rfl
      exact ⟨hw, rfl⟩
    · exact fun h ↦ h.2
  · have e : s.base w' = w := (by simpa using hw' : s.base w' ∈ S ∧ s.base w' = w).2
    subst e
    rw [pullbackUnitOver_self]

end Main

end GromovWitten.AlgebraicGeometry.IntersectionTheory
