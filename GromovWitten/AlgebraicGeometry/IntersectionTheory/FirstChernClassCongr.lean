/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.FirstChernClassGeneral

/-!
# First Chern classes of line bundles with the same residue transition units

Two Čech line bundles `L₁`, `L₂` on a scheme `X` have the same first Chern class as soon as
there is a map of index sets `φ : L₁.J → L₂.J` with `L₂.U (φ a) = L₁.U a` such that, at every
point `x` of an overlap `U a ⊓ U a'`, the residue classes in `κ(x)` of the transition units
`L₂.g (φ a) (φ a')` and `L₁.g a a'` agree.  (No surjectivity of `φ` is needed: the charts of
`L₂` outside the image of `φ` are never used.)

The proof compares the divisors of the frame sections `⟨a₀, _, 1⟩` of `L₁` and `⟨φ a₀, _, 1⟩`
of `L₂` along `pointSubscheme x`, whose coefficients are the `pointOrd`s of the residue classes
of the transition units (`LineBundleData.divisor_frame_apply`).

## Main results

* `c1Cycle_congr`: the cycle-level first Chern classes `c1Cycle L₁ dim i` and
  `c1Cycle L₂ dim i` agree.
* `firstChernClass_congr`, `firstChernClassOfField_congr`: the same for the first Chern classes
  on Chow groups.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open LineBundleInjective

universe u

section Cycle

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [NoetherianSpace X]

/-- **Congruence of cycle-level first Chern classes.**  If `φ : L₁.J → L₂.J` matches the charts
(`L₂.U (φ a) = L₁.U a`) and the residue classes of the transition units at every point of every
overlap, then `c1Cycle L₁ dim i = c1Cycle L₂ dim i`. -/
theorem c1Cycle_congr (L₁ L₂ : LineBundleData X) (φ : L₁.J → L₂.J)
    (hU : ∀ a, (L₂.U (φ a) : X.Opens) = L₁.U a)
    (hg : ∀ (a a' : L₁.J) (x : X) (hx : x ∈ (L₁.U a : X.Opens) ⊓ (L₁.U a' : X.Opens))
      (hx' : x ∈ (L₂.U (φ a) : X.Opens) ⊓ (L₂.U (φ a') : X.Opens)),
      sectionResidueUnit hx' (L₂.g (φ a) (φ a')) = sectionResidueUnit hx (L₁.g a a'))
    {dim : DimensionFunction X} (hcov : HomogeneityLocal.CovByDimension dim) (i : ℤ) :
    c1Cycle L₁ dim i = c1Cycle L₂ dim i := by
  apply c1Cycle_ext
  intro x
  by_cases hx : dim x = i + 1
  · rw [cyclesOfDimension.pointProj_eq_point hx]
    obtain ⟨a₀, ha₀⟩ := L₁.covers x
    have ha₀' : x ∈ (L₂.U (φ a₀) : X.Opens) := by rw [hU]; exact ha₀
    have hj₁ : (pointSubscheme x).eta ∈ (L₁.U a₀ : X.Opens) :=
      eta_pointSubscheme_mem (specializes_refl x) ha₀
    have hj₂ : (pointSubscheme x).eta ∈ (L₂.U (φ a₀) : X.Opens) :=
      eta_pointSubscheme_mem (specializes_refl x) ha₀'
    rw [c1Cycle_single hcov hx ⟨a₀, hj₁, 1⟩, c1Cycle_single hcov hx ⟨φ a₀, hj₂, 1⟩]
    congr 1
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro Q
    by_cases hxQ : x ⤳ Q
    · obtain ⟨a', ha'⟩ := L₁.covers Q
      have hQ' : Q ∈ (L₂.U (φ a') : X.Opens) := by rw [hU]; exact ha'
      have hx1 : x ∈ (L₁.U a' : X.Opens) ⊓ (L₁.U a₀ : X.Opens) :=
        ⟨hxQ.mem_open (L₁.U a').1.2 ha', ha₀⟩
      have hx2 : x ∈ (L₂.U (φ a') : X.Opens) ⊓ (L₂.U (φ a₀) : X.Opens) :=
        ⟨hxQ.mem_open (L₂.U (φ a')).1.2 hQ', ha₀'⟩
      rw [LineBundleData.divisor_frame_apply L₁ dim x a₀ a' hj₁ hxQ ha' hx1,
        LineBundleData.divisor_frame_apply L₂ dim x (φ a₀) (φ a') hj₂ hxQ hQ' hx2,
        hg a' a₀ x hx1 hx2]
    · rw [LineBundleData.RationalSection.divisor_apply_eq_zero_of_not_specializes _ _ hxQ,
        LineBundleData.RationalSection.divisor_apply_eq_zero_of_not_specializes _ _ hxQ]
  · rw [cyclesOfDimension.pointProj_eq_zero_of_ne hx, map_zero, map_zero]

/-- **Congruence of first Chern classes on Chow groups** (`firstChernClass`), under the
hypotheses of `c1Cycle_congr`. -/
theorem firstChernClass_congr (hU₀ : ∀ x : X, VectorBundle.UnitDifferences (X.presheaf.stalk x))
    {dim : DimensionFunction X} (hcov : HomogeneityLocal.CovByDimension dim)
    (L₁ L₂ : LineBundleData X) (φ : L₁.J → L₂.J)
    (hU : ∀ a, (L₂.U (φ a) : X.Opens) = L₁.U a)
    (hg : ∀ (a a' : L₁.J) (x : X) (hx : x ∈ (L₁.U a : X.Opens) ⊓ (L₁.U a' : X.Opens))
      (hx' : x ∈ (L₂.U (φ a) : X.Opens) ⊓ (L₂.U (φ a') : X.Opens)),
      sectionResidueUnit hx' (L₂.g (φ a) (φ a')) = sectionResidueUnit hx (L₁.g a a'))
    (i : ℤ) :
    firstChernClass hU₀ hcov L₁ i = firstChernClass hU₀ hcov L₂ i := by
  apply LinearMap.ext
  intro α
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  change firstChernClass hU₀ hcov L₁ i ((chowSystem dim (i + 1)).quotientMap a) =
    firstChernClass hU₀ hcov L₂ i ((chowSystem dim (i + 1)).quotientMap a)
  rw [firstChernClass_quotientMap, firstChernClass_quotientMap, c1Cycle_congr L₁ L₂ φ hU hg hcov]

end Cycle

section Field

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [NoetherianSpace X]

/-- **Congruence of first Chern classes over an infinite field** (`firstChernClassOfField`),
under the hypotheses of `c1Cycle_congr`. -/
theorem firstChernClassOfField_congr (L₁ L₂ : LineBundleData X) (φ : L₁.J → L₂.J)
    (hU : ∀ a, (L₂.U (φ a) : X.Opens) = L₁.U a)
    (hg : ∀ (a a' : L₁.J) (x : X) (hx : x ∈ (L₁.U a : X.Opens) ⊓ (L₁.U a' : X.Opens))
      (hx' : x ∈ (L₂.U (φ a) : X.Opens) ⊓ (L₂.U (φ a') : X.Opens)),
      sectionResidueUnit hx' (L₂.g (φ a) (φ a')) = sectionResidueUnit hx (L₁.g a a'))
    (i : ℤ) :
    firstChernClassOfField f L₁ i = firstChernClassOfField f L₂ i :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  firstChernClass_congr (unitDifferences_stalk_of_infinite f)
    (covByDimension_finiteTypeDimension f) L₁ L₂ φ hU hg i

end Field

end GromovWitten.AlgebraicGeometry.IntersectionTheory
