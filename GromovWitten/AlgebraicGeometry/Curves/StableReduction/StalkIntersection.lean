/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalIntersection
import GromovWitten.AlgebraicGeometry.Curves.CartierDivisors
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Scheme-theoretic local intersections of ideal sheaves

The affine ideals in `Scheme.IdealSheafData` have a canonical common image in every stalk.
This file records that image and defines the local intersection length as the length of the
quotient by the sum of the two stalk ideals.  No finiteness of the length is built into the
definition; it remains a value in `ℕ∞`.
-/

open CategoryTheory
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

variable {X : Scheme.{u}}

private noncomputable def affineOpenAt (x : X) : X.affineOpens :=
  Classical.choose (show ∃ U : X.affineOpens, x ∈ U.1 from by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨U, hU⟩, hxU⟩)

private theorem mem_affineOpenAt (x : X) : x ∈ (affineOpenAt x).1 :=
  Classical.choose_spec (show ∃ U : X.affineOpens, x ∈ U.1 from by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨U, hU⟩, hxU⟩)

/-- The image in `𝒪_{X,x}` of the ideal on an affine neighbourhood of `x`. -/
noncomputable def stalkIdeal (I : X.IdealSheafData) (x : X) :
    Ideal (X.presheaf.stalk x) :=
  (I.ideal (affineOpenAt x)).map
    (X.presheaf.germ (affineOpenAt x).1 x (mem_affineOpenAt x)).hom

theorem stalkIdeal_eq_map (I : X.IdealSheafData) (x : X)
    (U : X.affineOpens) (hxU : x ∈ U.1) :
    stalkIdeal I x = (I.ideal U).map (X.presheaf.germ U.1 x hxU).hom := by
  let A := affineOpenAt x
  let hA : x ∈ A.1 := mem_affineOpenAt x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWA⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ A.1 ⊓ U.1 from ⟨hA, hxU⟩)
      (A.1 ⊓ U.1).2
  let W' : X.affineOpens := ⟨W, hW⟩
  have hWA' : W' ≤ A := hWA.trans inf_le_left
  have hWU' : W' ≤ U := hWA.trans inf_le_right
  have hIA : (I.ideal A).map (X.presheaf.map (homOfLE hWA').op).hom = I.ideal W' :=
    I.map_ideal hWA'
  have hIU : (I.ideal U).map (X.presheaf.map (homOfLE hWU').op).hom = I.ideal W' :=
    I.map_ideal hWU'
  have hcompA : X.presheaf.map (homOfLE hWA').op ≫
      X.presheaf.germ W'.1 x hxW = X.presheaf.germ A.1 x hA :=
    X.presheaf.germ_res (homOfLE hWA') x hxW
  have hcompU : X.presheaf.map (homOfLE hWU').op ≫
      X.presheaf.germ W'.1 x hxW = X.presheaf.germ U.1 x hxU :=
    X.presheaf.germ_res (homOfLE hWU') x hxW
  rw [stalkIdeal]
  calc
    (I.ideal A).map (X.presheaf.germ A.1 x hA).hom =
        ((I.ideal A).map (X.presheaf.map (homOfLE hWA').op).hom).map
          (X.presheaf.germ W'.1 x hxW).hom := by
      rw [Ideal.map_map]
      rw [← CommRingCat.hom_comp]
      rw [congrArg CommRingCat.Hom.hom hcompA]
    _ = (I.ideal W').map (X.presheaf.germ W'.1 x hxW).hom := by rw [hIA]
    _ = ((I.ideal U).map (X.presheaf.map (homOfLE hWU').op).hom).map
          (X.presheaf.germ W'.1 x hxW).hom := by rw [hIU]
    _ = (I.ideal U).map (X.presheaf.germ U.1 x hxU).hom := by
      rw [Ideal.map_map]
      rw [← CommRingCat.hom_comp]
      rw [congrArg CommRingCat.Hom.hom hcompU]

@[simp]
theorem stalkIdeal_top (x : X) : stalkIdeal (⊤ : X.IdealSheafData) x = ⊤ := by
  rw [stalkIdeal]
  exact Ideal.map_top _

@[simp]
theorem stalkIdeal_bot (x : X) : stalkIdeal (⊥ : X.IdealSheafData) x = ⊥ := by
  rw [stalkIdeal]
  simp

/-- The scheme-theoretic local intersection length of two ideal sheaves at a point. -/
noncomputable def idealSheafIntersectionMultiplicity
    (I J : X.IdealSheafData) (x : X) : ℕ∞ :=
  Module.length (X.presheaf.stalk x)
    (X.presheaf.stalk x ⧸ (stalkIdeal I x ⊔ stalkIdeal J x))

theorem idealSheafIntersectionMultiplicity_eq_chart
    (I J : X.IdealSheafData) (x : X) (U : X.affineOpens) (hxU : x ∈ U.1) :
    idealSheafIntersectionMultiplicity I J x =
      Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸
          ((I.ideal U).map (X.presheaf.germ U.1 x hxU).hom ⊔
            (J.ideal U).map (X.presheaf.germ U.1 x hxU).hom)) := by
  rw [idealSheafIntersectionMultiplicity, stalkIdeal_eq_map I x U hxU,
    stalkIdeal_eq_map J x U hxU]

@[simp]
theorem idealSheafIntersectionMultiplicity_comm
    (I J : X.IdealSheafData) (x : X) :
    idealSheafIntersectionMultiplicity I J x = idealSheafIntersectionMultiplicity J I x := by
  rw [idealSheafIntersectionMultiplicity, idealSheafIntersectionMultiplicity, sup_comm]

theorem idealSheafIntersectionMultiplicity_eq_idealIntersectionMultiplicity
    (I J : X.IdealSheafData) (x : X) :
    idealSheafIntersectionMultiplicity I J x =
      idealIntersectionMultiplicity (stalkIdeal I x) (stalkIdeal J x) := rfl

theorem stalkIdeal_mul (I J : X.IdealSheafData) (x : X) :
    stalkIdeal (I * J) x = stalkIdeal I x * stalkIdeal J x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [stalkIdeal_eq_map (I * J) x ⟨U, hU⟩ hxU,
    stalkIdeal_eq_map I x ⟨U, hU⟩ hxU, stalkIdeal_eq_map J x ⟨U, hU⟩ hxU]
  rw [Scheme.IdealSheafData.ideal_mul]
  simp only [Pi.mul_apply, Ideal.map_mul]

theorem stalkIdeal_sup (I J : X.IdealSheafData) (x : X) :
    stalkIdeal (I ⊔ J) x = stalkIdeal I x ⊔ stalkIdeal J x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [stalkIdeal_eq_map (I ⊔ J) x ⟨U, hU⟩ hxU,
    stalkIdeal_eq_map I x ⟨U, hU⟩ hxU, stalkIdeal_eq_map J x ⟨U, hU⟩ hxU]
  rw [Scheme.IdealSheafData.ideal_sup]
  exact Ideal.map_sup _ _ _

theorem stalkIdeal_pow (I : X.IdealSheafData) (x : X) (n : ℕ) :
    stalkIdeal (I ^ n) x = stalkIdeal I x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, stalkIdeal_mul, ih, pow_succ]

theorem stalkIdeal_eq_top_of_not_mem_support (I : X.IdealSheafData) {x : X}
    (hx : x ∉ I.support) : stalkIdeal I x = ⊤ := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hxZ : x ∉ X.zeroLocus (U := U) (I.ideal ⟨U, hU⟩) := by
    intro hxZ
    exact hx ((I.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).2 hxZ)
  rw [stalkIdeal_eq_map I x ⟨U, hU⟩ hxU]
  obtain ⟨f, hf, hxf⟩ : ∃ f : Γ(X, U), f ∈ I.ideal ⟨U, hU⟩ ∧ x ∈ X.basicOpen f := by
    by_contra h
    apply hxZ
    rw [Scheme.mem_zeroLocus_iff]
    intro f hf
    by_contra hxf'
    exact h ⟨f, hf, hxf'⟩
  exact ((I.ideal ⟨U, hU⟩).map (X.presheaf.germ U x hxU).hom).eq_top_of_isUnit_mem
    (Ideal.mem_map_of_mem _ hf) ((X.mem_basicOpen f x hxU).mp hxf)

theorem idealSheafIntersectionMultiplicity_eq_zero_of_not_mem_support
    (I J : X.IdealSheafData) {x : X}
    (hx : x ∉ I.support ∨ x ∉ J.support) :
    idealSheafIntersectionMultiplicity I J x = 0 := by
  rcases hx with hxI | hxJ
  · rw [idealSheafIntersectionMultiplicity, stalkIdeal_eq_top_of_not_mem_support I hxI,
      top_sup_eq, Module.length_eq_zero]
  · rw [idealSheafIntersectionMultiplicity, stalkIdeal_eq_top_of_not_mem_support J hxJ,
      sup_top_eq, Module.length_eq_zero]

/-- Local intersection multiplicity for effective Cartier divisors, using their intrinsic ideal
sheaves. -/
noncomputable def effectiveCartierIntersectionMultiplicity
    (D E : Curves.EffectiveCartierDivisor X) (x : X) : ℕ∞ :=
  idealSheafIntersectionMultiplicity D.idealSheaf E.idealSheaf x

@[simp]
theorem effectiveCartierIntersectionMultiplicity_comm
    (D E : Curves.EffectiveCartierDivisor X) (x : X) :
    effectiveCartierIntersectionMultiplicity D E x =
      effectiveCartierIntersectionMultiplicity E D x := by
  exact idealSheafIntersectionMultiplicity_comm D.idealSheaf E.idealSheaf x

theorem effectiveCartierIntersectionMultiplicity_eq_local
    (D E : Curves.EffectiveCartierDivisor X) (x : X)
    (U : X.affineOpens) (hxU : x ∈ U.1)
    (r s : Γ(X, U.1))
    (hDr : D.idealSheaf.ideal U = Ideal.span {r})
    (hEs : E.idealSheaf.ideal U = Ideal.span {s}) :
    effectiveCartierIntersectionMultiplicity D E x =
      localIntersectionMultiplicity
        (X.presheaf.germ U.1 x hxU r) (X.presheaf.germ U.1 x hxU s) := by
  rw [effectiveCartierIntersectionMultiplicity,
    idealSheafIntersectionMultiplicity_eq_chart D.idealSheaf E.idealSheaf x U hxU,
    hDr, hEs, Ideal.map_span, Ideal.map_span]
  have hr : (⇑(CommRingCat.Hom.hom (X.presheaf.germ U.1 x hxU)) ''
      ({r} : Set Γ(X, U.1))) =
      {(X.presheaf.germ U.1 x hxU).hom r} := Set.image_singleton
  have hs : (⇑(CommRingCat.Hom.hom (X.presheaf.germ U.1 x hxU)) ''
      ({s} : Set Γ(X, U.1))) =
      {(X.presheaf.germ U.1 x hxU).hom s} := Set.image_singleton
  rw [hr, hs]
  rfl

theorem idealSheafIntersectionMultiplicity_top_left
    (I : X.IdealSheafData) (x : X) :
    idealSheafIntersectionMultiplicity (⊤ : X.IdealSheafData) I x = 0 := by
  rw [idealSheafIntersectionMultiplicity, stalkIdeal_top, top_sup_eq]
  rw [Module.length_eq_zero]

theorem idealSheafIntersectionMultiplicity_top_right
    (I : X.IdealSheafData) (x : X) :
    idealSheafIntersectionMultiplicity I (⊤ : X.IdealSheafData) x = 0 := by
  rw [idealSheafIntersectionMultiplicity, stalkIdeal_top, sup_top_eq]
  rw [Module.length_eq_zero]

end
end GromovWitten.AlgebraicGeometry.Curves.StableReduction
