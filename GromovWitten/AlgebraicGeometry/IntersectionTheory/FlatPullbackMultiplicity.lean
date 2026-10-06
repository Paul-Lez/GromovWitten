/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroup
import Mathlib.RingTheory.LocalRing.Length

/-!
# Flat pullback multiplicities

This file records the local algebra underlying flat pullback of cycles.  If `A → B` is a flat
local map, the fibre over the closed point has the scheme-theoretic multiplicity
`ℓ_B(B / m_A B)`.  The length base-change theorem, together with the actual quotient/tensor
equivalence, gives the order formula

`ord_B(a) = ord_A(a) * ℓ_B(B / m_A B)`.

The same multiplicity is transitive for a second flat local map.  The statements below are local
and do not encode a geometric divisor or pullback as structure data; they are intended as the
input for a scheme-level construction once the relevant finite-flat hypotheses are available.
-/

open CategoryTheory

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## The local flat order formula -/

namespace Ring

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]

/-- The order of an element after a flat local base change is its old order multiplied by the
length of the actual scheme-theoretic closed fibre.  The proof uses the genuine tensor/quotient
equivalence and `IsLocalRing.length_baseChange`; no multiplicity formula is assumed. -/
theorem ord_algebraMap_of_flat_local (a : A) :
    Ring.ord B (algebraMap A B a) = Ring.ord A a *
      Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) := by
  unfold Ring.ord
  let I : Ideal A := Ideal.span ({a} : Set A)
  have hmap : I.map (algebraMap A B) =
      Ideal.span ({algebraMap A B a} : Set B) := by
    rw [Ideal.map_span]
    simp
  rw [← hmap]
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq]
  rw [IsLocalRing.length_baseChange A B (A ⧸ I)]

/-- For a nonzero element of a flat local extension of one-dimensional Noetherian domains, the
zero-preserving multiplicative order has the same fibre-length factor. -/
theorem ordMonoidWithZeroHom_algebraMap_of_flat_local
    [IsDomain A] [IsDomain B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Ring.KrullDimLE 1 A] [Ring.KrullDimLE 1 B] (a : A) (ha : a ≠ 0) :
    Ring.ordMonoidWithZeroHom B (algebraMap A B a) =
      (ENat.recTopCoe 0 (fun n => WithZero.coe (Multiplicative.ofAdd (n : ℤ)))
        (Ring.ord A a * Module.length B
          (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)))) := by
  have hmap : algebraMap A B a ≠ 0 := by
    let _ : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    simpa using (FaithfulSMul.algebraMap_injective A B).ne ha
  rw [Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero hmap)]
  rw [ord_algebraMap_of_flat_local]

/-! ## Fraction-field orders -/

/-- A local flat map scales the order of a nonzero fraction by the length of the closed fibre.
The order takes values in `WithZero (Multiplicative ℤ)`, so this scaling is expressed by raising
to the fibre-length power.  The explicit finite-length hypothesis ensures that `ENat.toNat`
records the actual length. -/
theorem ordFrac_algebraMap_of_flat_local
    [IsDomain A] [IsDomain B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Ring.KrullDimLE 1 A] [Ring.KrullDimLE 1 B]
    {K L : Type u} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (hfinite : Module.length B
      (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) ≠ ⊤)
    (q : K) (hq : q ≠ 0) :
    Ring.ordFrac B (algebraMap K L q) =
      Ring.ordFrac A q ^ ENat.toNat (Module.length B
        (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B))) := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hmlen : Module.length B
      (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) = m := hm.symm
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) q
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp at hq
  have hb0 : b ≠ 0 := by
    simpa [mem_nonZeroDivisors_iff_ne_zero] using hb
  let _ : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hma : algebraMap A B a ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective A B).ne ha
  have hmb : algebraMap A B b ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective A B).ne hb0
  simp only [map_div₀]
  rw [show algebraMap K L (algebraMap A K a) =
      algebraMap B L (algebraMap A B a) by
        rw [← IsScalarTower.algebraMap_apply A K L,
          ← IsScalarTower.algebraMap_apply A B L],
    show algebraMap K L (algebraMap A K b) =
      algebraMap B L (algebraMap A B b) by
        rw [← IsScalarTower.algebraMap_apply A K L,
          ← IsScalarTower.algebraMap_apply A B L]]
  rw [Ring.ordFrac_eq_ord B hma, Ring.ordFrac_eq_ord B hmb,
    Ring.ordFrac_eq_ord A ha, Ring.ordFrac_eq_ord A hb0]
  rw [ordMonoidWithZeroHom_algebraMap_of_flat_local _ ha,
    ordMonoidWithZeroHom_algebraMap_of_flat_local _ hb0]
  have horda : Ring.ord A a ≠ ⊤ :=
    Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha)
  have hordb : Ring.ord A b ≠ ⊤ :=
    Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hb0)
  obtain ⟨na, hna⟩ := ENat.ne_top_iff_exists.mp horda
  obtain ⟨nb, hnb⟩ := ENat.ne_top_iff_exists.mp hordb
  rw [Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero ha),
    Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero hb0), ← hna, ← hnb,
    hmlen]
  rw [← ENat.natCast_mul, ← ENat.natCast_mul]
  simp only [ENat.recTopCoe_natCast, ENat.toNat_natCast]
  conv_lhs => rw [← WithZero.coe_div]
  conv_rhs => rw [← WithZero.coe_div, ← WithZero.coe_pow]
  apply WithZero.coe_inj.mpr
  conv_lhs => rw [← ofAdd_sub]
  conv_rhs => rw [← ofAdd_sub, ← ofAdd_nsmul]
  apply (Multiplicative.ofAdd).injective
  push_cast
  ring_nf

end Ring

/-! ## Transitivity of fibre multiplicity -/

namespace FlatPullbackMultiplicity

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
  [Algebra A B] [Algebra B C] [Algebra A C]
  [IsScalarTower A B C] [IsLocalHom (algebraMap B C)] [Module.Flat B C]

/-- The scheme-theoretic multiplicity of the closed fibre of a flat local ring map. -/
noncomputable def fibreLength (A B : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] : ℕ∞ :=
  Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B))

/-- A formally unramified essentially finite-type local map has reduced closed fibre, so its
scheme-theoretic fibre multiplicity is one.  This is the local length statement behind the
coefficient-one etale pullback. -/
theorem fibreLength_eq_one_of_formallyUnramified
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] :
    fibreLength A B = 1 := by
  unfold fibreLength
  rw [Algebra.FormallyUnramified.map_maximalIdeal]
  have hresidue : Module.length B (B ⧸ IsLocalRing.maximalIdeal B) = 1 := by
    rw [Module.length_eq_one_iff]
    rw [isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (S := B ⧸ IsLocalRing.maximalIdeal B) Ideal.Quotient.mk_surjective]
    let _ := Ideal.Quotient.field (IsLocalRing.maximalIdeal B)
    exact instIsSimpleModule _
  exact hresidue

/-- Fibre multiplicities compose for two flat local maps.  The left side is identified with the
base-changed quotient by the actual quotient/tensor equivalence, and then `length_baseChange`
computes the product. -/
theorem fibreLength_comp :
    fibreLength A C = fibreLength A B * fibreLength B C := by
  unfold fibreLength
  let I : Ideal A := IsLocalRing.maximalIdeal A
  let J : Ideal B := I.map (algebraMap A B)
  have hmap : J.map (algebraMap B C) =
      I.map (algebraMap A C) := by
    simp [J, I, Ideal.map_map, ← IsScalarTower.algebraMap_eq A B C]
  rw [← hmap]
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot C J).toLinearEquiv.length_eq]
  rw [IsLocalRing.length_baseChange B C (B ⧸ J)]

end FlatPullbackMultiplicity

end GromovWitten.AlgebraicGeometry.IntersectionTheory
