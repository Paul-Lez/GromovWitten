/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.FiniteFlatPullback
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia

/-!
# Dimension grading for finite affine pullback

Finite affine maps preserve the dimension of point closures: incomparability
gives one height inequality, and specialization lifting gives the other. Thus
the ramification-weighted cycle map preserves certified dimension gradings.

This construction already makes sense for finite algebras. Flat functoriality
and descent to rational equivalence are separate assertions.
-/

open CategoryTheory TopologicalSpace Topology
open scoped AlgebraicGeometry
open _root_.AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace AlgebraicCycle

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S]

noncomputable def finiteFlatMap :
    Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  specFiniteMap (R := R) (S := S)

instance finiteFlatMap_isFinite : IsFinite (finiteFlatMap (R := R) (S := S)) := by
  dsimp [finiteFlatMap]
  infer_instance

attribute [local instance] specializationOrder in
lemma finiteFlatMap_strictMono :
    StrictMono (finiteFlatMap (R := R) (S := S)).base := by
  intro q q' hqq'
  let : q.asIdeal.IsPrime := q.isPrime
  let : q'.asIdeal.IsPrime := q'.isPrime
  have hp : q' ⤳ q := hqq'.le
  have hi : q'.asIdeal ≤ q.asIdeal :=
    (PrimeSpectrum.asIdeal_le_asIdeal q' q).mpr
      ((PrimeSpectrum.le_iff_specializes q' q).mpr hp)
  refine lt_of_le_of_ne (hp.map (finiteFlatMap (R := R) (S := S)).continuous) ?_
  intro hh
  apply hqq'.ne
  apply PrimeSpectrum.ext
  apply Eq.symm
  apply Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) q'.asIdeal q.asIdeal hi
  change PrimeSpectrum.comap (algebraMap R S) q =
    PrimeSpectrum.comap (algebraMap R S) q' at hh
  exact (congrArg PrimeSpectrum.asIdeal hh).symm

end AlgebraicCycle

attribute [local instance] specializationOrder in
theorem DimensionFunction.apply_eq_of_finiteFlatMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (dimensionR : DimensionFunction (Spec (CommRingCat.of R)))
    (dimensionS : DimensionFunction (Spec (CommRingCat.of S)))
    (q : Spec (CommRingCat.of S)) :
    dimensionS q = dimensionR ((AlgebraicCycle.finiteFlatMap (R := R) (S := S)).base q) := by
  have h₁ : Order.height q ≤
      Order.height ((AlgebraicCycle.finiteFlatMap (R := R) (S := S)).base q) :=
    Order.height_le_height_apply_of_strictMono _
      (AlgebraicCycle.finiteFlatMap_strictMono (R := R) (S := S)) q
  have h₂ : Order.height ((AlgebraicCycle.finiteFlatMap (R := R) (S := S)).base q) ≤
      Order.height q :=
    height_image_le_of_specializing
      (AlgebraicCycle.finiteFlatMap (R := R) (S := S))
      (AlgebraicCycle.finiteFlatMap (R := R) (S := S)).isClosedMap.specializingMap q
  have hheight : Order.height q =
      Order.height ((AlgebraicCycle.finiteFlatMap (R := R) (S := S)).base q) :=
    le_antisymm h₁ h₂
  have hcast : (Int.toNat (dimensionS q) : ℕ∞) =
      (Int.toNat (dimensionR ((AlgebraicCycle.finiteFlatMap (R := R) (S := S)).base q)) : ℕ∞) := by
    rw [← dimensionS.height_eq, ← dimensionR.height_eq, hheight]
  have hnat : Int.toNat (dimensionS q) =
      Int.toNat (dimensionR ((AlgebraicCycle.finiteFlatMap (R := R) (S := S)).base q)) :=
    ENat.natCast_inj.mp hcast
  rw [← Int.toNat_of_nonneg (dimensionS.nonnegative q),
    ← Int.toNat_of_nonneg (dimensionR.nonnegative _)]
  exact congrArg Int.ofNat hnat

namespace AlgebraicCycle

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S]

/-- The dimension-graded ramification-weighted inverse image of a rational cycle. The coefficient
is the actual ramification index from `pullbackFiniteFlat`; the grading uses the finite-map height
comparison above and therefore does not require a caller-supplied compatibility witness. -/
noncomputable def finiteFlatPullback
    (dimensionR : DimensionFunction (Spec (CommRingCat.of R)))
    (dimensionS : DimensionFunction (Spec (CommRingCat.of S))) (i : ℤ) :
    cyclesOfDimension (Spec (CommRingCat.of R)) dimensionR i →ₗ[ℚ]
      cyclesOfDimension (Spec (CommRingCat.of S)) dimensionS i where
  toFun c := ⟨pullbackFiniteFlat c.1, by
    intro q hq
    have hdim := DimensionFunction.apply_eq_of_finiteFlatMap dimensionR dimensionS q
    have hc := c.2 (PrimeSpectrum.comap (algebraMap R S) q) (by
      intro heq
      apply hq
      rw [hdim]
      exact heq)
    change c.1 (PrimeSpectrum.comap (algebraMap R S) q) *
      (q.asIdeal.ramificationIdx R : ℚ) = 0
    rw [hc, zero_mul]⟩
  map_add' c d := by
    apply Subtype.ext
    exact pullbackFiniteFlat_add c.1 d.1
  map_smul' a c := by
    apply Subtype.ext
    exact pullbackFiniteFlat_smul a c.1

@[simp]
theorem finiteFlatPullback_apply
    (dimensionR : DimensionFunction (Spec (CommRingCat.of R)))
    (dimensionS : DimensionFunction (Spec (CommRingCat.of S))) (i : ℤ)
    (c : cyclesOfDimension (Spec (CommRingCat.of R)) dimensionR i)
    (q : Spec (CommRingCat.of S)) :
    ((finiteFlatPullback dimensionR dimensionS i c :
      cyclesOfDimension (Spec (CommRingCat.of S)) dimensionS i) :
        _root_.AlgebraicGeometry.AlgebraicCycle (Spec (CommRingCat.of S)) ℚ) q =
      c.1 (PrimeSpectrum.comap (algebraMap R S) q) *
        (q.asIdeal.ramificationIdx R : ℚ) :=
  rfl

end AlgebraicCycle

end GromovWitten.AlgebraicGeometry.IntersectionTheory
