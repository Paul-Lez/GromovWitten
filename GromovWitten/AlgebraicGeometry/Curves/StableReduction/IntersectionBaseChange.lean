/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.StalkIntersection
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Flat base change for local intersection lengths

The intersection quotient is identified with an actual tensor product quotient before the
length theorem for flat local extensions is used.  Consequently all equalities below retain
the `ℕ∞` value `⊤` when the relevant quotient has infinite length.
-/

open CategoryTheory
open TopologicalSpace
open _root_.AlgebraicGeometry
open TensorProduct

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]

/-! ## Flat base change of the intersection multiplicity -/

/-- Flat local base change of the actual ideal-intersection quotient.  The proof first transports
the quotient through Mathlib's canonical quotient/tensor equivalence, after identifying the
extension of a sum with the sum of the extensions, and only then applies the local length
base-change theorem. -/
theorem idealIntersectionMultiplicity_baseChange (I J : Ideal A) :
    idealIntersectionMultiplicity
        (I.map (algebraMap A B)) (J.map (algebraMap A B)) =
      idealIntersectionMultiplicity I J *
        Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) := by
  unfold idealIntersectionMultiplicity
  rw [← Ideal.map_sup]
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (I ⊔ J)).toLinearEquiv.length_eq]
  exact IsLocalRing.length_baseChange A B (A ⧸ (I ⊔ J))

omit [Module.Flat A B] in
/-- Restriction of the base-changed intersection quotient to the base ring is weighted by the
length of the residue-field extension.  This is a genuine statement about the quotient by the
extended ideals, rather than an abbreviation for the multiplicity formula. -/
theorem intersectionQuotient_length_restrictScalars (I J : Ideal A) :
    Module.length A
        (B ⧸ (I.map (algebraMap A B) ⊔ J.map (algebraMap A B))) =
      idealIntersectionMultiplicity
          (I.map (algebraMap A B)) (J.map (algebraMap A B)) *
        Module.length (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
  exact IsLocalRing.length_restrictScalars A B
    (B ⧸ (I.map (algebraMap A B) ⊔ J.map (algebraMap A B)))

omit [Module.Flat A B] in
/-- If the residue extension is finite as a module, its length in the restriction formula is its
usual vector-space dimension. -/
theorem intersectionQuotient_length_restrictScalars_finrank (I J : Ideal A)
    [Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
    Module.length A
        (B ⧸ (I.map (algebraMap A B) ⊔ J.map (algebraMap A B))) =
      idealIntersectionMultiplicity
          (I.map (algebraMap A B)) (J.map (algebraMap A B)) *
        Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
  rw [intersectionQuotient_length_restrictScalars]
  rw [Module.length_eq_finrank]

/-! ## The length-one closed-fibre specialization -/

private theorem length_quotient_maximalIdeal_eq_one (R : Type u) [CommRing R] [IsLocalRing R] :
    Module.length R (R ⧸ IsLocalRing.maximalIdeal R) = 1 := by
  rw [Module.length_eq_one_iff,
    isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (S := R ⧸ IsLocalRing.maximalIdeal R) Ideal.Quotient.mk_surjective]
  let _ := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  infer_instance

/-- When the extended maximal ideal is the maximal ideal of `B`, flat base change preserves the
local intersection multiplicity. -/
theorem idealIntersectionMultiplicity_baseChange_of_map_maximalIdeal_eq
    (I J : Ideal A)
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B) :
    idealIntersectionMultiplicity
        (I.map (algebraMap A B)) (J.map (algebraMap A B)) =
      idealIntersectionMultiplicity I J := by
  rw [idealIntersectionMultiplicity_baseChange, hmax,
    length_quotient_maximalIdeal_eq_one, mul_one]

/-! ## Stalks of inverse-image ideal sheaves -/

/-- The stalk ideal of a scheme-theoretic inverse image is the extension of the original stalk
ideal along the stalk map.  The proof uses an affine chart subordinate to the inverse image and
the naturality equation for germs, so this is an equality of the actual ideals in the two stalks. -/
theorem stalkIdeal_comap (X Y : Scheme.{u}) (I : Y.IdealSheafData) (f : X ⟶ Y) (x : X) :
    stalkIdeal (I.comap f) x =
      (stalkIdeal I (f x)).map (f.stalkMap x).hom := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hfxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVpre⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ U from hfxU) (f ⁻¹ᵁ U).2
  change V ≤ f ⁻¹ᵁ U at hVpre
  rw [stalkIdeal_eq_map (I.comap f) x ⟨V, hV⟩ hxV,
    stalkIdeal_eq_map I (f x) ⟨U, hU⟩ hfxU,
    idealSheaf_comap_ideal I f ⟨U, hU⟩ ⟨V, hV⟩ hVpre]
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  apply congrArg CommRingCat.Hom.hom
  simp only [Scheme.Hom.appLE]
  rw [Category.assoc, X.presheaf.germ_res (homOfLE hVpre) x hxV,
    Scheme.Hom.germ_stalkMap]

/-- Flat base change of a scheme-theoretic local intersection is the ring-theoretic formula at
the corresponding stalks.  The stalk comap identity above supplies the two extended ideals. -/
theorem idealSheafIntersectionMultiplicity_flat_baseChange
    (X Y : Scheme.{u}) (I J : Y.IdealSheafData) (f : X ⟶ Y) (x : X)
    (hf : (f.stalkMap x).hom.Flat) :
    idealSheafIntersectionMultiplicity (I.comap f) (J.comap f) x =
      idealSheafIntersectionMultiplicity I J (f x) *
        Module.length (X.presheaf.stalk x)
          (X.presheaf.stalk x ⧸
            (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom) := by
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let j : A →+* B := (f.stalkMap x).hom
  let _ : Algebra A B := j.toAlgebra
  let _ : IsLocalHom (algebraMap A B) := by
    change IsLocalHom j
    infer_instance
  let _ : Module.Flat A B := hf
  have h_alg : algebraMap A B = (f.stalkMap x).hom := rfl
  rw [idealSheafIntersectionMultiplicity, idealSheafIntersectionMultiplicity,
    stalkIdeal_comap, stalkIdeal_comap]
  rw [← h_alg]
  simpa [idealIntersectionMultiplicity, A, B, j, h_alg] using
    (idealIntersectionMultiplicity_baseChange
      (A := A) (B := B) (stalkIdeal I (f x)) (stalkIdeal J (f x)))

/-- When the extended maximal ideal equals the maximal ideal of the source stalk, flat
pullback preserves the local intersection multiplicity itself. -/
theorem idealSheafIntersectionMultiplicity_flat_baseChange_of_map_maximalIdeal_eq
    (X Y : Scheme.{u}) (I J : Y.IdealSheafData) (f : X ⟶ Y) (x : X)
    (hf : (f.stalkMap x).hom.Flat)
    (hmax : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    idealSheafIntersectionMultiplicity (I.comap f) (J.comap f) x =
      idealSheafIntersectionMultiplicity I J (f x) := by
  rw [idealSheafIntersectionMultiplicity_flat_baseChange X Y I J f x hf,
    hmax, length_quotient_maximalIdeal_eq_one, mul_one]

end
end GromovWitten.AlgebraicGeometry.Curves.StableReduction
