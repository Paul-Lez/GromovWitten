/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroup
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FlatPullbackMultiplicity
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Weighted inverse image of cycles for finite affine maps

For a finite algebra `R → S`, this file constructs a weighted inverse image of an algebraic
cycle on `Spec R`, with the actual ramification multiplicity at every prime `q` of `S`:

`q ↦ c (q.comap R) * q.ramificationIdx R`.

The coefficient is obtained from the local length definition of `ramificationIdx`; it is not a
caller-supplied weight.  Finite morphisms have finite fibres, which gives local finiteness of the
resulting cycle.  This raw coefficient construction does not require flatness.  For finite flat
maps it is the cycle formula underlying flat pullback; functoriality, dimension grading, and
descent to Chow groups require further proofs.  The proper pushforward comparison also needs
the residue-degree comparison between scheme residue fields and `Ideal.inertiaDeg`.
-/

open CategoryTheory TopologicalSpace Topology
open scoped AlgebraicGeometry
open _root_.AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace AlgebraicCycle

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Flat R S]

/-- The affine scheme map induced by the displayed algebra map. -/
noncomputable def specFiniteMap :
    Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

instance specFiniteMap_isFinite : IsFinite (specFiniteMap (R := R) (S := S)) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The weighted inverse image of an affine cycle along a finite map, using the actual
ramification index (local fibre length).  This formula underlies finite flat pullback, but its
construction as an ungraded cycle needs only finiteness. -/
noncomputable def pullbackFiniteFlat (c : AlgebraicCycle
    (Spec (CommRingCat.of R)) ℚ) : AlgebraicCycle
    (Spec (CommRingCat.of S)) ℚ where
  toFun q := c (PrimeSpectrum.comap (algebraMap R S) q) *
    (q.asIdeal.ramificationIdx R : ℚ)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' q _ := by
    let f := specFiniteMap (R := R) (S := S)
    obtain ⟨t, ht, hfinite⟩ := c.supportLocallyFiniteWithinDomain (f.base q) (by trivial)
    have hpre : (f.base ⁻¹' (t ∩ c.support)).Finite := f.finite_preimage hfinite
    refine ⟨f.base ⁻¹' t, f.continuous.continuousAt.preimage_mem_nhds ht, ?_⟩
    refine hpre.subset ?_
    rintro z ⟨hzT, hz⟩
    refine ⟨hzT, ?_⟩
    have hcoeff : c (PrimeSpectrum.comap (algebraMap R S) z) *
        (z.asIdeal.ramificationIdx R : ℚ) ≠ 0 := by
      change c (PrimeSpectrum.comap (algebraMap R S) z) *
        (z.asIdeal.ramificationIdx R : ℚ) ≠ 0 at hz
      exact hz
    exact (mul_ne_zero_iff.mp hcoeff).1

omit [Module.Flat R S] in
/-- The finite weighted inverse image is additive. -/
theorem pullbackFiniteFlat_add (c d : AlgebraicCycle
    (Spec (CommRingCat.of R)) ℚ) :
    pullbackFiniteFlat (R := R) (S := S) (c + d) =
      pullbackFiniteFlat c + pullbackFiniteFlat d := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  change (c (PrimeSpectrum.comap (algebraMap R S) q) +
      d (PrimeSpectrum.comap (algebraMap R S) q)) *
      (q.asIdeal.ramificationIdx R : ℚ) = _
  simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  change (c (PrimeSpectrum.comap (algebraMap R S) q) +
      d (PrimeSpectrum.comap (algebraMap R S) q)) *
      (q.asIdeal.ramificationIdx R : ℚ) =
    (c (PrimeSpectrum.comap (algebraMap R S) q) *
        (q.asIdeal.ramificationIdx R : ℚ)) +
      (d (PrimeSpectrum.comap (algebraMap R S) q) *
        (q.asIdeal.ramificationIdx R : ℚ))
  rw [add_mul]

omit [Module.Flat R S] in
/-- The finite weighted inverse image commutes with rational scalars. -/
theorem pullbackFiniteFlat_smul (a : ℚ) (c : AlgebraicCycle
    (Spec (CommRingCat.of R)) ℚ) :
    pullbackFiniteFlat (R := R) (S := S) (a • c) =
      a • pullbackFiniteFlat c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  change (a * c (PrimeSpectrum.comap (algebraMap R S) q)) *
      (q.asIdeal.ramificationIdx R : ℚ) = _
  simp only [Function.locallyFinsuppWithin.coe_rational_smul, Pi.smul_apply, smul_eq_mul]
  change (a * c (PrimeSpectrum.comap (algebraMap R S) q)) *
      (q.asIdeal.ramificationIdx R : ℚ) =
    a * (c (PrimeSpectrum.comap (algebraMap R S) q) *
      (q.asIdeal.ramificationIdx R : ℚ))
  ring

omit [Module.Flat R S] in
/-- A finite affine map unramified at every prime has coefficient-one weighted inverse image. -/
theorem pullbackFiniteFlat_eq_coefficientOne_of_unramified
    [Algebra.EssFiniteType R S]
    (hu : ∀ q : PrimeSpectrum S, Algebra.IsUnramifiedAt R q.asIdeal) (c : AlgebraicCycle
      (Spec (CommRingCat.of R)) ℚ) :
    pullbackFiniteFlat (R := R) (S := S) c q =
      c (PrimeSpectrum.comap (algebraMap R S) q) := by
  let _ : q.asIdeal.IsPrime := q.isPrime
  let _ : Algebra.IsUnramifiedAt R q.asIdeal := hu q
  change c (PrimeSpectrum.comap (algebraMap R S) q) *
    (q.asIdeal.ramificationIdx R : ℚ) = _
  rw [Ideal.ramificationIdx_eq_one q.asIdeal R]
  simp

end AlgebraicCycle

end GromovWitten.AlgebraicGeometry.IntersectionTheory
