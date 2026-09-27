/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.FractionRing
import GromovWitten.AlgebraicGeometry.IntersectionTheory.HomogeneityLocal

/-!
# Point stalks

For a specialization `w ⤳ v` in a scheme `X` (i.e. `v ∈ closure {w}`), the local ring of the
reduced closure of `w` at `v` is `𝒪_{X,v} ⧸ 𝔭_w`, where `𝔭_w` is the prime of `𝒪_{X,v}`
corresponding to `w`. This file defines it canonically, without charts, as
`pointStalk h := 𝒪_{X,v} ⧸ ker (pointStalkMap h)`, where
`pointStalkMap h : 𝒪_{X,v} → 𝒪_{X,w} → κ(w)` is the specialization map followed by the residue
map, and develops its basic theory.

## Main results

* `pointStalk h`: a local domain (Noetherian if `X` is locally Noetherian) with an embedding into
  `κ(w)`; `IsFractionRing (pointStalk h) (X.residueField w)`.
* `pointStalkResidueEquiv h : ResidueField (pointStalk h) ≃+* X.residueField v`, compatible with
  the residue maps (`pointStalkResidueEquiv_residue_mk`).
* `pointStalkReflEquiv w : pointStalk (specializes_refl w) ≃+* X.residueField w`,
  `maximalIdeal_pointStalk_refl`, and `residueFieldGenericPointEquiv` (`κ` of the generic point
  of an integral scheme is its function field).
* For `w ⤳ v ⤳ Q`: the prime `pointStalkPrime hwv hvQ` of `pointStalk (w ⤳ Q)`,
  `pointStalkQuotientEquiv : pointStalk (w ⤳ Q) ⧸ pointStalkPrime hwv hvQ ≃+* pointStalk (v ⤳ Q)`,
  the algebra `pointStalkAlgebra hwv hvQ` (a def, not an instance) with
  `pointStalk_isScalarTower` and `pointStalk_isLocalization` (`pointStalk (w ⤳ v)` is the
  localization at `pointStalkPrime hwv hvQ`), and the residue-field compatibility square
  `pointStalkResidue_comm`.
* The prime correspondence `pointStalkPrimeOrderIso hwQ : Set.Icc Q w ≃o
  (PrimeSpectrum (pointStalk hwQ))ᵒᵈ` (specialization order, where `x ≤ y ↔ y ⤳ x`), with
  `pointStalkPrime_le_iff`, `pointStalkPrime_injective`, `exists_pointStalkPrime_eq`.
* Dimensions: for a `DimensionFunction` `dim` with `HomogeneityLocal.CovByDimension dim`,
  `ringKrullDim_pointStalk : ringKrullDim (pointStalk h) = (dim w - dim v).toNat` and
  `height_pointStalkPrime : (pointStalkPrime hwv hvQ).height = (dim w - dim v).toNat`, and
  `height_pointStalkPrime_eq_one_iff`.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace IsLocalRing

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

variable {X : Scheme.{u}}

section Basic

variable {w v : X}

/-- For a specialization `w ⤳ v`, the composite `𝒪_{X,v} → 𝒪_{X,w} → κ(w)` of the
specialization map of stalks with the residue map at `w`. -/
noncomputable def pointStalkMap (h : w ⤳ v) : X.presheaf.stalk v →+* X.residueField w :=
  (X.residue w).hom.comp (X.presheaf.stalkSpecializes h).hom

/-- Unfolding `pointStalkMap` on an element. -/
theorem pointStalkMap_apply (h : w ⤳ v) (t : X.presheaf.stalk v) :
    pointStalkMap h t = X.residue w (X.presheaf.stalkSpecializes h t) := rfl

/-- The local ring at `v` of the reduced closure of `w`, for a specialization `w ⤳ v`:
the quotient of `𝒪_{X,v}` by the kernel of `pointStalkMap h`, i.e. by the prime of `𝒪_{X,v}`
corresponding to `w`. -/
abbrev pointStalk (h : w ⤳ v) : Type u :=
  X.presheaf.stalk v ⧸ RingHom.ker (pointStalkMap h)

/-- The kernel of `pointStalkMap h` is prime, since `κ(w)` is a field. -/
instance (h : w ⤳ v) : (RingHom.ker (pointStalkMap h)).IsPrime :=
  RingHom.ker_isPrime _

/-- The point stalk is local, being a nonzero quotient of the local ring `𝒪_{X,v}`. -/
instance (h : w ⤳ v) : IsLocalRing (pointStalk h) :=
  .of_surjective' _ Ideal.Quotient.mk_surjective

example (h : w ⤳ v) : IsDomain (pointStalk h) := inferInstance

example [IsLocallyNoetherian X] (h : w ⤳ v) : IsNoetherianRing (pointStalk h) := inferInstance

/-- The embedding of the point stalk `pointStalk h` into the residue field `κ(w)`, induced by
`pointStalkMap h`. -/
noncomputable instance (h : w ⤳ v) : Algebra (pointStalk h) (X.residueField w) :=
  (pointStalkMap h).kerLift.toAlgebra

/-- The embedding `pointStalk h → κ(w)` on the class of `t : 𝒪_{X,v}` is `pointStalkMap h t`. -/
theorem pointStalk_algebraMap_mk (h : w ⤳ v) (t : X.presheaf.stalk v) :
    algebraMap (pointStalk h) (X.residueField w) (Ideal.Quotient.mk _ t) = pointStalkMap h t :=
  rfl

/-- The embedding `pointStalk h → κ(w)` is injective. -/
theorem pointStalk_algebraMap_injective (h : w ⤳ v) :
    Function.Injective (algebraMap (pointStalk h) (X.residueField w)) :=
  RingHom.kerLift_injective _

/-- The point stalk acts faithfully on `κ(w)`, since the embedding is injective. -/
instance (h : w ⤳ v) : FaithfulSMul (pointStalk h) (X.residueField w) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (pointStalk_algebraMap_injective h)

/-- Every element of the stalk at `w` is a fraction of images of elements of the stalk at a
specialization `v` of `w`, with unit denominator. -/
theorem exists_mul_stalkSpecializes_eq (h : w ⤳ v) (y : X.presheaf.stalk w) :
    ∃ a s : X.presheaf.stalk v, IsUnit (X.presheaf.stalkSpecializes h s) ∧
      y * X.presheaf.stalkSpecializes h s = X.presheaf.stalkSpecializes h a := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hvU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ v) isOpen_univ
  have hwU : w ∈ U := h.mem_open U.2 hvU
  let _ := X.presheaf.algebra_section_stalk ⟨w, hwU⟩
  have hloc := hU.isLocalization_stalk ⟨w, hwU⟩
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (hU.primeIdealOf ⟨w, hwU⟩).asIdeal.primeCompl y
  refine ⟨X.presheaf.germ U v hvU a, X.presheaf.germ U v hvU s, ?_, ?_⟩
  · have := IsLocalization.map_units (X.presheaf.stalk w)
      (M := (hU.primeIdealOf ⟨w, hwU⟩).asIdeal.primeCompl) s
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    exact this
  · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      TopCat.Presheaf.germ_stalkSpecializes]
    exact hs

/-- **`κ(w)` is the fraction field of `pointStalk h`.** Every element of `κ(w)` is
`pointStalkMap h a / pointStalkMap h s` with `pointStalkMap h s ≠ 0`, by
`exists_mul_stalkSpecializes_eq`. -/
instance (h : w ⤳ v) : IsFractionRing (pointStalk h) (X.residueField w) := by
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨y, rfl⟩ := X.residue_surjective w z
  obtain ⟨a, s, hs, hys⟩ := exists_mul_stalkSpecializes_eq h y
  refine ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ s, ?_⟩
  rw [pointStalk_algebraMap_mk, pointStalk_algebraMap_mk, pointStalkMap_apply,
    pointStalkMap_apply, ← hys, map_mul]
  have : X.residue w (X.presheaf.stalkSpecializes h s) ≠ 0 := by
    intro h0
    exact (hs.map (X.residue w).hom).ne_zero h0
  field_simp

/-- The quotient map `𝒪_{X,v} → pointStalk h` is a local homomorphism. -/
instance (h : w ⤳ v) :
    IsLocalHom (Ideal.Quotient.mk (RingHom.ker (pointStalkMap h))) :=
  .of_surjective _ Ideal.Quotient.mk_surjective

/-- The residue field of the point stalk `pointStalk h` (for `w ⤳ v`) is the residue field
`κ(v)`: the quotient map `𝒪_{X,v} → pointStalk h` is a surjective local homomorphism, so it
induces an isomorphism of residue fields. -/
noncomputable def pointStalkResidueEquiv (h : w ⤳ v) :
    ResidueField (pointStalk h) ≃+* X.residueField v :=
  (RingEquiv.ofBijective (ResidueField.map (Ideal.Quotient.mk (RingHom.ker (pointStalkMap h))))
    ⟨RingHom.injective _, by
      intro z
      obtain ⟨x, rfl⟩ := residue_surjective z
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨residue _ t, ResidueField.map_residue _ t⟩⟩).symm

/-- `pointStalkResidueEquiv h` sends the residue of the class of `t : 𝒪_{X,v}` to the residue
`X.residue v t`. -/
theorem pointStalkResidueEquiv_residue_mk (h : w ⤳ v) (t : X.presheaf.stalk v) :
    pointStalkResidueEquiv h (residue _ (Ideal.Quotient.mk _ t)) = X.residue v t := by
  exact (RingEquiv.symm_apply_eq _).mpr (ResidueField.map_residue _ t).symm

end Basic

section Refl

variable (w : X)

/-- For the trivial specialization, `pointStalkMap` is the residue map. -/
theorem pointStalkMap_refl :
    pointStalkMap (specializes_refl w) = (X.residue w).hom := by
  ext t
  simp [pointStalkMap_apply]

/-- For the trivial specialization `w ⤳ w`, the point stalk is the residue field `κ(w)`: the
embedding `pointStalk (specializes_refl w) → κ(w)` is bijective. -/
noncomputable def pointStalkReflEquiv :
    pointStalk (specializes_refl w) ≃+* X.residueField w :=
  RingEquiv.ofBijective (algebraMap (pointStalk (specializes_refl w)) (X.residueField w))
    ⟨pointStalk_algebraMap_injective _, by
      intro z
      obtain ⟨t, rfl⟩ := X.residue_surjective w z
      refine ⟨Ideal.Quotient.mk _ t, ?_⟩
      rw [pointStalk_algebraMap_mk, pointStalkMap_refl]⟩

/-- `pointStalkReflEquiv` is the embedding `pointStalk (specializes_refl w) → κ(w)`. -/
theorem pointStalkReflEquiv_apply (x : pointStalk (specializes_refl w)) :
    pointStalkReflEquiv w x = algebraMap _ (X.residueField w) x := rfl

/-- The point stalk of the trivial specialization is a field. -/
theorem isField_pointStalk_refl : IsField (pointStalk (specializes_refl w)) :=
  (pointStalkReflEquiv w).toMulEquiv.isField (Field.toIsField _)

/-- The point stalk of the trivial specialization has zero maximal ideal. -/
theorem maximalIdeal_pointStalk_refl : maximalIdeal (pointStalk (specializes_refl w)) = ⊥ :=
  IsLocalRing.isField_iff_maximalIdeal_eq.mp (isField_pointStalk_refl w)

/-- On an integral scheme, the residue field at the generic point is the function field: the
residue map of the stalk at the generic point (a field) is bijective. -/
noncomputable def residueFieldGenericPointEquiv (X : Scheme.{u}) [IsIntegral X] :
    X.residueField (genericPoint X) ≃+* X.functionField :=
  (RingEquiv.ofBijective (X.residue (genericPoint X)).hom
    ⟨RingHom.injective _, X.residue_surjective _⟩).symm

/-- `residueFieldGenericPointEquiv X` inverts the residue map at the generic point. -/
theorem residueFieldGenericPointEquiv_residue (X : Scheme.{u}) [IsIntegral X]
    (t : X.functionField) :
    residueFieldGenericPointEquiv X (X.residue (genericPoint X) t) = t := by
  rw [residueFieldGenericPointEquiv, RingEquiv.symm_apply_eq]
  rfl

end Refl

section Transitivity

variable {w v Q : X}

/-- For `w ⤳ v ⤳ Q`, `pointStalkMap (w ⤳ Q)` factors through the specialization map
`𝒪_{X,Q} → 𝒪_{X,v}` and `pointStalkMap (w ⤳ v)`. -/
theorem pointStalkMap_trans (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    pointStalkMap (hwv.trans hvQ) =
      (pointStalkMap hwv).comp (X.presheaf.stalkSpecializes hvQ).hom := by
  ext t
  change X.residue w (X.presheaf.stalkSpecializes (hwv.trans hvQ) t) =
    X.residue w (X.presheaf.stalkSpecializes hwv (X.presheaf.stalkSpecializes hvQ t))
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply]

/-- For `w ⤳ v ⤳ Q`, the kernel of `pointStalkMap (w ⤳ Q)` is the preimage of the kernel of
`pointStalkMap (w ⤳ v)` under the specialization map `𝒪_{X,Q} → 𝒪_{X,v}`. -/
theorem ker_pointStalkMap_trans (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    RingHom.ker (pointStalkMap (hwv.trans hvQ)) =
      (RingHom.ker (pointStalkMap hwv)).comap (X.presheaf.stalkSpecializes hvQ).hom := by
  rw [pointStalkMap_trans, RingHom.comap_ker]

/-- `pointStalkMap h t` vanishes iff the image of `t` in `𝒪_{X,w}` is not a unit. -/
theorem pointStalkMap_eq_zero_iff (h : w ⤳ v) (t : X.presheaf.stalk v) :
    pointStalkMap h t = 0 ↔ ¬ IsUnit (X.presheaf.stalkSpecializes h t) := by
  rw [pointStalkMap_apply]
  change IsLocalRing.residue _ _ = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- For `w ⤳ v ⤳ Q`, the prime of `w` in `𝒪_{X,Q}` is contained in the prime of `v`. -/
theorem ker_pointStalkMap_le (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    RingHom.ker (pointStalkMap (hwv.trans hvQ)) ≤ RingHom.ker (pointStalkMap hvQ) := by
  intro t ht
  rw [RingHom.mem_ker, pointStalkMap_eq_zero_iff] at ht ⊢
  intro hu
  apply ht
  rw [← TopCat.Presheaf.stalkSpecializes_comp_apply _ hwv hvQ]
  exact hu.map _

/-- For `w ⤳ v ⤳ Q`, the surjection `pointStalk (w ⤳ Q) → pointStalk (v ⤳ Q)` of quotients of
`𝒪_{X,Q}`. -/
noncomputable def pointStalkFactor (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    pointStalk (hwv.trans hvQ) →+* pointStalk hvQ :=
  Ideal.Quotient.factor (ker_pointStalkMap_le hwv hvQ)

/-- `pointStalkFactor` on the class of `t : 𝒪_{X,Q}`. -/
theorem pointStalkFactor_mk (hwv : w ⤳ v) (hvQ : v ⤳ Q) (t : X.presheaf.stalk Q) :
    pointStalkFactor hwv hvQ (Ideal.Quotient.mk _ t) = Ideal.Quotient.mk _ t := rfl

/-- `pointStalkFactor` is surjective. -/
theorem pointStalkFactor_surjective (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    Function.Surjective (pointStalkFactor hwv hvQ) :=
  Ideal.Quotient.factor_surjective _

/-- For `w ⤳ v ⤳ Q`, the prime ideal of `pointStalk (w ⤳ Q)` corresponding to `v`: the image of
the kernel of `pointStalkMap hvQ : 𝒪_{X,Q} → κ(v)`. -/
noncomputable def pointStalkPrime (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    Ideal (pointStalk (hwv.trans hvQ)) :=
  (RingHom.ker (pointStalkMap hvQ)).map (Ideal.Quotient.mk _)

/-- `pointStalkPrime hwv hvQ` is the kernel of `pointStalkFactor hwv hvQ`. -/
theorem pointStalkPrime_eq_ker (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    pointStalkPrime hwv hvQ = RingHom.ker (pointStalkFactor hwv hvQ) := by
  rw [pointStalkPrime, ← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective
    (RingHom.ker (pointStalkFactor hwv hvQ)), RingHom.comap_ker, pointStalkFactor,
    Ideal.Quotient.factor_comp_mk, Ideal.mk_ker]

/-- The class of `t : 𝒪_{X,Q}` lies in `pointStalkPrime hwv hvQ` iff `pointStalkMap hvQ t = 0`. -/
theorem mk_mem_pointStalkPrime_iff (hwv : w ⤳ v) (hvQ : v ⤳ Q) (t : X.presheaf.stalk Q) :
    Ideal.Quotient.mk _ t ∈ pointStalkPrime hwv hvQ ↔ pointStalkMap hvQ t = 0 := by
  rw [pointStalkPrime_eq_ker, RingHom.mem_ker, pointStalkFactor_mk,
    Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker]

/-- `pointStalkPrime hwv hvQ` is a prime ideal. -/
instance (hwv : w ⤳ v) (hvQ : v ⤳ Q) : (pointStalkPrime hwv hvQ).IsPrime := by
  rw [pointStalkPrime_eq_ker]
  exact RingHom.ker_isPrime _

/-- The quotient of `pointStalk (w ⤳ Q)` by the prime of `v` is `pointStalk (v ⤳ Q)`. -/
noncomputable def pointStalkQuotientEquiv (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    pointStalk (hwv.trans hvQ) ⧸ pointStalkPrime hwv hvQ ≃+* pointStalk hvQ :=
  (Ideal.quotEquivOfEq (pointStalkPrime_eq_ker hwv hvQ)).trans
    (RingHom.quotientKerEquivOfSurjective (pointStalkFactor_surjective hwv hvQ))

/-- `pointStalkQuotientEquiv` on the class of `x` is `pointStalkFactor hwv hvQ x`. -/
theorem pointStalkQuotientEquiv_mk (hwv : w ⤳ v) (hvQ : v ⤳ Q) (x : pointStalk (hwv.trans hvQ)) :
    pointStalkQuotientEquiv hwv hvQ (Ideal.Quotient.mk _ x) = pointStalkFactor hwv hvQ x := rfl

/-- For `w ⤳ v ⤳ Q`, the ring map `pointStalk (w ⤳ Q) → pointStalk (w ⤳ v)` induced by the
specialization map `𝒪_{X,Q} → 𝒪_{X,v}`. -/
noncomputable def pointStalkSpecializes (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    pointStalk (hwv.trans hvQ) →+* pointStalk hwv :=
  Ideal.quotientMap _ (X.presheaf.stalkSpecializes hvQ).hom (ker_pointStalkMap_trans hwv hvQ).le

/-- `pointStalkSpecializes` on the class of `t : 𝒪_{X,Q}`. -/
theorem pointStalkSpecializes_mk (hwv : w ⤳ v) (hvQ : v ⤳ Q) (t : X.presheaf.stalk Q) :
    pointStalkSpecializes hwv hvQ (Ideal.Quotient.mk _ t) =
      Ideal.Quotient.mk _ (X.presheaf.stalkSpecializes hvQ t) := rfl

/-- The algebra structure on `pointStalk (w ⤳ v)` over `pointStalk (w ⤳ Q)` given by
`pointStalkSpecializes`. It is not an instance, since `hvQ` cannot be inferred. -/
@[instance_reducible]
noncomputable def pointStalkAlgebra (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    Algebra (pointStalk (hwv.trans hvQ)) (pointStalk hwv) :=
  (pointStalkSpecializes hwv hvQ).toAlgebra

/-- The maps `pointStalk (w ⤳ Q) → pointStalk (w ⤳ v) → κ(w)` and
`pointStalk (w ⤳ Q) → κ(w)` agree. -/
theorem algebraMap_comp_pointStalkSpecializes (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    (algebraMap (pointStalk hwv) (X.residueField w)).comp (pointStalkSpecializes hwv hvQ) =
      algebraMap (pointStalk (hwv.trans hvQ)) (X.residueField w) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun t ↦ ?_)
  simp only [RingHom.comp_apply, pointStalkSpecializes_mk, pointStalk_algebraMap_mk]
  rw [pointStalkMap_trans hwv hvQ]
  rfl

/-- `pointStalkSpecializes` is injective. -/
theorem pointStalkSpecializes_injective (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    Function.Injective (pointStalkSpecializes hwv hvQ) := by
  intro x y hxy
  apply pointStalk_algebraMap_injective (hwv.trans hvQ)
  rw [← algebraMap_comp_pointStalkSpecializes hwv hvQ, RingHom.comp_apply, RingHom.comp_apply,
    hxy]

/-- The scalar tower `pointStalk (w ⤳ Q) → pointStalk (w ⤳ v) → κ(w)`. -/
theorem pointStalk_isScalarTower (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    letI := pointStalkAlgebra hwv hvQ
    IsScalarTower (pointStalk (hwv.trans hvQ)) (pointStalk hwv) (X.residueField w) := by
  let _ := pointStalkAlgebra hwv hvQ
  exact IsScalarTower.of_algebraMap_eq' (algebraMap_comp_pointStalkSpecializes hwv hvQ).symm

/-- **Localization.** For `w ⤳ v ⤳ Q`, `pointStalk (w ⤳ v)` is the localization of
`pointStalk (w ⤳ Q)` at the prime `pointStalkPrime hwv hvQ` (with the algebra structure
`pointStalkAlgebra hwv hvQ`). -/
theorem pointStalk_isLocalization (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    letI := pointStalkAlgebra hwv hvQ
    IsLocalization.AtPrime (pointStalk hwv) (pointStalkPrime hwv hvQ) := by
  let _ := pointStalkAlgebra hwv hvQ
  have hunit : ∀ t : X.presheaf.stalk Q, Ideal.Quotient.mk _ t ∉ pointStalkPrime hwv hvQ →
      IsUnit (X.presheaf.stalkSpecializes hvQ t) := by
    intro t ht
    rw [mk_mem_pointStalkPrime_iff, pointStalkMap_eq_zero_iff, not_not] at ht
    exact ht
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (hunit t hx).map (Ideal.Quotient.mk _)
  · intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, s, hs, hys⟩ := exists_mul_stalkSpecializes_eq hvQ y
    refine ⟨⟨Ideal.Quotient.mk _ a, ⟨Ideal.Quotient.mk _ s, ?_⟩⟩, ?_⟩
    · change Ideal.Quotient.mk _ s ∉ pointStalkPrime hwv hvQ
      rw [mk_mem_pointStalkPrime_iff, pointStalkMap_eq_zero_iff, not_not]
      exact hs
    · change _ * pointStalkSpecializes hwv hvQ _ = pointStalkSpecializes hwv hvQ _
      rw [pointStalkSpecializes_mk, pointStalkSpecializes_mk, ← map_mul, hys]
  · intro x y hxy
    exact ⟨1, by rw [pointStalkSpecializes_injective hwv hvQ hxy]⟩

/-- For `w ⤳ v ⤳ Q`, the map from `pointStalk (w ⤳ Q) ⧸ pointStalkPrime hwv hvQ` to the residue
field of the localization `pointStalk (w ⤳ v)`. -/
noncomputable def pointStalkQuotientToResidueField (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    pointStalk (hwv.trans hvQ) ⧸ pointStalkPrime hwv hvQ →+* ResidueField (pointStalk hwv) :=
  Ideal.Quotient.lift _ ((residue _).comp (pointStalkSpecializes hwv hvQ)) (by
    intro x hx
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [mk_mem_pointStalkPrime_iff, pointStalkMap_eq_zero_iff] at hx
    rw [RingHom.comp_apply, residue_eq_zero_iff, pointStalkSpecializes_mk, mem_maximalIdeal,
      mem_nonunits_iff]
    exact fun hu ↦ hx (hu.of_map _))

/-- `pointStalkQuotientToResidueField` on the class of `x`. -/
theorem pointStalkQuotientToResidueField_mk (hwv : w ⤳ v) (hvQ : v ⤳ Q)
    (x : pointStalk (hwv.trans hvQ)) :
    pointStalkQuotientToResidueField hwv hvQ (Ideal.Quotient.mk _ x) =
      residue _ (pointStalkSpecializes hwv hvQ x) := rfl

/-- **Compatibility of residue fields.** The two maps
`pointStalk (w ⤳ Q) ⧸ pointStalkPrime hwv hvQ → κ(v)`, one through the residue field of the
localization `pointStalk (w ⤳ v)` and `pointStalkResidueEquiv`, the other through
`pointStalkQuotientEquiv` and the fraction field embedding `pointStalk (v ⤳ Q) → κ(v)`,
agree. -/
theorem pointStalkResidue_comm (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    (pointStalkResidueEquiv hwv).toRingHom.comp (pointStalkQuotientToResidueField hwv hvQ) =
      (algebraMap (pointStalk hvQ) (X.residueField v)).comp
        (pointStalkQuotientEquiv hwv hvQ).toRingHom := by
  refine Ideal.Quotient.ringHom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun t ↦ ?_))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    pointStalkQuotientToResidueField_mk, pointStalkSpecializes_mk,
    pointStalkResidueEquiv_residue_mk, pointStalkQuotientEquiv_mk, pointStalkFactor_mk,
    pointStalk_algebraMap_mk, pointStalkMap_apply]

end Transitivity

section Correspondence

variable {w Q : X}

/-- For `y ⤳ Q`, the point of `Spec 𝒪_{X,Q}` given by the closed point of `Spec 𝒪_{X,y}` maps to
`y` under `X.fromSpecStalk Q`. -/
theorem fromSpecStalk_SpecMap_stalkSpecializes_closedPoint {y : X} (h : y ⤳ Q) :
    X.fromSpecStalk Q
      (Spec.map (X.presheaf.stalkSpecializes h) (closedPoint (X.presheaf.stalk y))) = y := by
  have := Scheme.fromSpecStalk_closedPoint (X := X) (x := y)
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h] at this
  exact this

/-- For `y ⤳ Q`, the prime of `𝒪_{X,Q}` given by the closed point of `Spec 𝒪_{X,y}` is the
kernel of `pointStalkMap h`. -/
theorem asIdeal_SpecMap_stalkSpecializes_closedPoint {y : X} (h : y ⤳ Q) :
    (Spec.map (X.presheaf.stalkSpecializes h) (closedPoint (X.presheaf.stalk y))).asIdeal =
      RingHom.ker (pointStalkMap h) := by
  change Ideal.comap (X.presheaf.stalkSpecializes h).hom (maximalIdeal _) = _
  rw [pointStalkMap, ← RingHom.comap_ker]
  change _ = Ideal.comap _ (RingHom.ker (IsLocalRing.residue _))
  rw [IsLocalRing.ker_residue]

/-- For two generizations `y₁, y₂` of `Q`, the primes `ker (𝒪_{X,Q} → κ(yᵢ))` satisfy
`ker₁ ≤ ker₂` iff `y₁ ⤳ y₂`. -/
theorem ker_pointStalkMap_le_iff {y₁ y₂ : X} (h₁ : y₁ ⤳ Q) (h₂ : y₂ ⤳ Q) :
    RingHom.ker (pointStalkMap h₁) ≤ RingHom.ker (pointStalkMap h₂) ↔ y₁ ⤳ y₂ := by
  have key := (X.fromSpecStalk Q).isEmbedding.isInducing.specializes_iff
    (x := Spec.map (X.presheaf.stalkSpecializes h₁) (closedPoint (X.presheaf.stalk y₁)))
    (y := Spec.map (X.presheaf.stalkSpecializes h₂) (closedPoint (X.presheaf.stalk y₂)))
  rw [fromSpecStalk_SpecMap_stalkSpecializes_closedPoint h₁,
    fromSpecStalk_SpecMap_stalkSpecializes_closedPoint h₂] at key
  rw [← asIdeal_SpecMap_stalkSpecializes_closedPoint h₁,
    ← asIdeal_SpecMap_stalkSpecializes_closedPoint h₂, key]
  exact PrimeSpectrum.le_iff_specializes _ _

/-- Every prime ideal of `𝒪_{X,Q}` is `ker (𝒪_{X,Q} → κ(y))` for some generization `y` of
`Q`. -/
theorem exists_ker_pointStalkMap_eq (p : Ideal (X.presheaf.stalk Q)) [p.IsPrime] :
    ∃ (y : X) (h : y ⤳ Q), RingHom.ker (pointStalkMap h) = p := by
  let pt : Spec (X.presheaf.stalk Q) := (⟨p, inferInstance⟩ : PrimeSpectrum _)
  have hy : X.fromSpecStalk Q pt ⤳ Q := by
    have : X.fromSpecStalk Q pt ∈ Set.range (X.fromSpecStalk Q) := Set.mem_range_self pt
    rwa [Scheme.range_fromSpecStalk] at this
  refine ⟨_, hy, ?_⟩
  rw [← asIdeal_SpecMap_stalkSpecializes_closedPoint hy,
    (X.fromSpecStalk Q).isEmbedding.injective
      (fromSpecStalk_SpecMap_stalkSpecializes_closedPoint hy)]

/-- The preimage of `pointStalkPrime hwv hvQ` in `𝒪_{X,Q}` is the kernel of `pointStalkMap hvQ`. -/
theorem comap_mk_pointStalkPrime {v : X} (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    (pointStalkPrime hwv hvQ).comap (Ideal.Quotient.mk _) = RingHom.ker (pointStalkMap hvQ) := by
  ext t
  rw [Ideal.mem_comap, mk_mem_pointStalkPrime_iff, RingHom.mem_ker]

/-- The prime correspondence is order-preserving and order-reflecting: for `w ⤳ vᵢ ⤳ Q`,
`pointStalkPrime hwv₁ hv₁Q ≤ pointStalkPrime hwv₂ hv₂Q` iff `v₁ ⤳ v₂`. -/
theorem pointStalkPrime_le_iff {v₁ v₂ : X} (hwv₁ : w ⤳ v₁) (hv₁Q : v₁ ⤳ Q) (hwv₂ : w ⤳ v₂)
    (hv₂Q : v₂ ⤳ Q) :
    pointStalkPrime hwv₁ hv₁Q ≤ pointStalkPrime hwv₂ hv₂Q ↔ v₁ ⤳ v₂ := by
  rw [← ker_pointStalkMap_le_iff hv₁Q hv₂Q]
  constructor
  · intro hle
    rw [← comap_mk_pointStalkPrime hwv₁ hv₁Q, ← comap_mk_pointStalkPrime hwv₂ hv₂Q]
    exact Ideal.comap_mono hle
  · intro hle
    exact Ideal.map_mono hle

/-- `v ↦ pointStalkPrime hwv hvQ` is injective. -/
theorem pointStalkPrime_injective {v₁ v₂ : X} (hwv₁ : w ⤳ v₁) (hv₁Q : v₁ ⤳ Q) (hwv₂ : w ⤳ v₂)
    (hv₂Q : v₂ ⤳ Q) (h : pointStalkPrime hwv₁ hv₁Q = pointStalkPrime hwv₂ hv₂Q) : v₁ = v₂ :=
  ((pointStalkPrime_le_iff hwv₁ hv₁Q hwv₂ hv₂Q).mp h.le).antisymm
    ((pointStalkPrime_le_iff hwv₂ hv₂Q hwv₁ hv₁Q).mp h.ge) |>.eq

/-- Every prime ideal of `pointStalk (w ⤳ Q)` is `pointStalkPrime hwv hvQ` for some `v` with
`w ⤳ v ⤳ Q`. -/
theorem exists_pointStalkPrime_eq (hwQ : w ⤳ Q) (p : Ideal (pointStalk hwQ)) [p.IsPrime] :
    ∃ (v : X) (hwv : w ⤳ v) (hvQ : v ⤳ Q), pointStalkPrime hwv hvQ = p := by
  obtain ⟨v, hvQ, hv⟩ := exists_ker_pointStalkMap_eq (p.comap (Ideal.Quotient.mk _))
  have hwv : w ⤳ v := by
    rw [← ker_pointStalkMap_le_iff hwQ hvQ, hv]
    intro t ht
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ht]
    exact p.zero_mem
  refine ⟨v, hwv, hvQ, ?_⟩
  rw [pointStalkPrime, hv, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

/-- **The prime correspondence.** For `w ⤳ Q`, the points `v` with `w ⤳ v ⤳ Q` (the interval
`[Q, w]` of the specialization order, where `x ≤ y ↔ y ⤳ x`) are order-anti-isomorphic to the
prime spectrum of `pointStalk (w ⤳ Q)`, via `v ↦ pointStalkPrime hwv hvQ`. -/
noncomputable def pointStalkPrimeOrderIso (hwQ : w ⤳ Q) :
    Set.Icc Q w ≃o (PrimeSpectrum (pointStalk hwQ))ᵒᵈ where
  toEquiv := Equiv.ofBijective
    (fun v ↦ OrderDual.toDual (⟨pointStalkPrime v.2.2 v.2.1, inferInstance⟩ : PrimeSpectrum _))
    ⟨fun v₁ v₂ h ↦ Subtype.ext (pointStalkPrime_injective v₁.2.2 v₁.2.1 v₂.2.2 v₂.2.1
        (congrArg (fun p ↦ (OrderDual.ofDual p).asIdeal) h)),
      fun p ↦ by
        obtain ⟨v, hwv, hvQ, hv⟩ := exists_pointStalkPrime_eq hwQ (OrderDual.ofDual p).asIdeal
        exact ⟨⟨v, hvQ, hwv⟩, by
          apply OrderDual.ofDual.injective
          exact PrimeSpectrum.ext hv⟩⟩
  map_rel_iff' {v₁ v₂} := by
    change pointStalkPrime v₂.2.2 v₂.2.1 ≤ pointStalkPrime v₁.2.2 v₁.2.1 ↔ v₂.1 ⤳ v₁.1
    exact pointStalkPrime_le_iff _ _ _ _

/-- The underlying ideal of `pointStalkPrimeOrderIso hwQ v` is `pointStalkPrime`. -/
theorem pointStalkPrimeOrderIso_apply (hwQ : w ⤳ Q) (v : Set.Icc Q w) :
    (OrderDual.ofDual (pointStalkPrimeOrderIso hwQ v)).asIdeal = pointStalkPrime v.2.2 v.2.1 :=
  rfl

/-- Membership in the interval `Set.Icc Q w` of the specialization order of `X` (where
`x ≤ y ↔ y ⤳ x`). -/
theorem pointStalk_mem_Icc_iff {v : X} : v ∈ Set.Icc Q w ↔ v ⤳ Q ∧ w ⤳ v := Iff.rfl

end Correspondence

/-! ### Order-theoretic auxiliaries: chains under a grading that is additive along covers -/

section OrderAux

variable {α : Type*} [Preorder α] (f : α → ℤ)
  (hheight : ∀ x, Order.height x = ((f x).toNat : ℕ∞)) (hnn : ∀ x, 0 ≤ f x)

include hheight hnn

private theorem pointStalk_aux_strictMono {x y : α} (hxy : x < y) : f x < f y := by
  have := Order.height_strictMono hxy (by rw [hheight]; exact ENat.natCast_lt_top _)
  rw [hheight, hheight, Nat.cast_lt] at this
  have := hnn x
  have := hnn y
  omega

private theorem pointStalk_aux_mono {x y : α} (hxy : x ≤ y) : f x ≤ f y := by
  have := Order.height_mono hxy
  rw [hheight, hheight, Nat.cast_le] at this
  have := hnn x
  have := hnn y
  omega

variable (hcov : ∀ x y : α, x ⋖ y → f x + 1 = f y)

include hcov in
private theorem pointStalk_aux_exists_series (n : ℕ) :
    ∀ a b : α, a ≤ b → f b = f a + n →
      ∃ p : LTSeries α, p.head = a ∧ p.last ≤ b ∧ p.length = n := by
  induction n with
  | zero => exact fun a _ hab _ ↦ ⟨RelSeries.singleton _ a, rfl, hab, rfl⟩
  | succ n ih =>
    classical
    intro a b hab hfb
    have hlt : a < b := by
      refine lt_of_le_not_ge hab fun hba ↦ ?_
      have := pointStalk_aux_mono f hheight hnn hba
      omega
    have hex : ∃ m : ℕ, ∃ y : α, a < y ∧ y ≤ b ∧ (f y).toNat = m := ⟨_, b, hlt, le_rfl, rfl⟩
    obtain ⟨y, hay, hyb, hy⟩ := Nat.find_spec hex
    have hcovy : a ⋖ y := by
      refine ⟨hay, fun z haz hzy ↦ ?_⟩
      have hmin := Nat.find_min' hex ⟨z, haz, hzy.le.trans hyb, rfl⟩
      have := pointStalk_aux_strictMono f hheight hnn hzy
      have := hnn z
      omega
    have hfy := hcov a y hcovy
    obtain ⟨p, hp0, hp1, hp2⟩ := ih y b hyb (by omega)
    refine ⟨p.cons a (by rw [hp0]; exact hay), by simp, by simpa using hp1, by simp [hp2]⟩

include hcov in
private theorem pointStalk_aux_krullDim_Icc {a b : α} (hab : a ≤ b) :
    Order.krullDim (Set.Icc a b) = (((f b - f a).toNat : ℕ) : WithBot ℕ∞) := by
  apply le_antisymm
  · refine iSup_le fun p ↦ ?_
    have hmono : StrictMono (fun x : Set.Icc a b ↦ f x) :=
      fun x y hxy ↦ pointStalk_aux_strictMono f hheight hnn hxy
    have h1 : f p.head + p.length ≤ f p.last := (p.map _ hmono).head_add_length_le_int
    have h2 := pointStalk_aux_mono f hheight hnn p.head.2.1
    have h3 := pointStalk_aux_mono f hheight hnn p.last.2.2
    have : p.length ≤ (f b - f a).toNat := by omega
    exact_mod_cast this
  · obtain ⟨p, hp0, hp1, hp2⟩ :=
      pointStalk_aux_exists_series f hheight hnn hcov (f b - f a).toNat a b hab
        (by have := pointStalk_aux_mono f hheight hnn hab; omega)
    let q : LTSeries (Set.Icc a b) := LTSeries.mk p.length
      (fun i ↦ ⟨p i, hp0 ▸ p.head_le i, (p.monotone (Fin.le_last i)).trans hp1⟩)
      (fun i j hij ↦ p.strictMono hij)
    have := Order.LTSeries.length_le_krullDim q
    rwa [show q.length = p.length from rfl, hp2] at this

end OrderAux

section Dimension

variable {w v Q : X} (dim : DimensionFunction X)

/-- A dimension function does not increase under specialization: `w ⤳ v` gives
`dim v ≤ dim w`. -/
theorem dimensionFunction_le_of_specializes (h : w ⤳ v) : dim v ≤ dim w :=
  pointStalk_aux_mono dim dim.height_eq dim.nonnegative h

variable (hcov : HomogeneityLocal.CovByDimension dim)
include hcov

/-- **Krull dimension of a point stalk.** If the dimension function `dim` increases by exactly
one along every covering relation of the specialization order, then for `w ⤳ v` the ring
`pointStalk h` has Krull dimension `dim w - dim v`. -/
theorem ringKrullDim_pointStalk (h : w ⤳ v) :
    ringKrullDim (pointStalk h) = (((dim w - dim v).toNat : ℕ) : WithBot ℕ∞) := by
  change Order.krullDim (PrimeSpectrum _) = _
  rw [← Order.krullDim_orderDual, ← Order.krullDim_eq_of_orderIso (pointStalkPrimeOrderIso h),
    pointStalk_aux_krullDim_Icc dim dim.height_eq dim.nonnegative hcov (h : v ≤ w)]

/-- **Height of the prime of an intermediate point.** Under `hcov`, for `w ⤳ v ⤳ Q` the prime
`pointStalkPrime hwv hvQ` of `pointStalk (w ⤳ Q)` has height `dim w - dim v`. -/
theorem height_pointStalkPrime (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    (pointStalkPrime hwv hvQ).height = (((dim w - dim v).toNat : ℕ) : ℕ∞) := by
  let _ := pointStalkAlgebra hwv hvQ
  have := pointStalk_isLocalization hwv hvQ
  have h := IsLocalization.AtPrime.ringKrullDim_eq_height (pointStalkPrime hwv hvQ)
    (pointStalk hwv)
  rw [ringKrullDim_pointStalk dim hcov hwv] at h
  exact_mod_cast h.symm

/-- Under `hcov`, for `w ⤳ v ⤳ Q` the prime `pointStalkPrime hwv hvQ` has height one iff
`dim w = dim v + 1`. -/
theorem height_pointStalkPrime_eq_one_iff (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    (pointStalkPrime hwv hvQ).height = 1 ↔ dim w = dim v + 1 := by
  rw [height_pointStalkPrime dim hcov hwv hvQ]
  have := dimensionFunction_le_of_specializes dim hwv
  constructor
  · intro h1
    have : (dim w - dim v).toNat = 1 := by exact_mod_cast h1
    omega
  · intro h1
    have : (dim w - dim v).toNat = 1 := by omega
    rw [this]
    rfl

end Dimension

end GromovWitten.AlgebraicGeometry.IntersectionTheory
