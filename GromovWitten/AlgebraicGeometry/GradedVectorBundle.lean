/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.VectorBundleTrivial
import GromovWitten.AlgebraicGeometry.PolynomialRelativeProj

/-!
# Graded vector bundle data

A vector bundle `E → X` carries, over every affine open `U` of `X` (not just the trivialising
charts), an intrinsic grading of its algebra of functions `𝓔.bundle.algebra.ring U` by the
`MvPolynomial`-degree one would see in a trivialisation: the symmetric algebra `Sym(E^∨)` is
graded, and the grading is compatible with every restriction map.  This file packages that
extra structure as `GradedBundleData X ι`, derives from it the `GradedAlgebraData X` consumed by
`RelativeProj.relativeProj` (used by the projective completion `P(E ⊕ 1)` of round G3), and
constructs the trivial example.

## Main declarations

* `GradedBundleData X ι` — a `BundleData X ι` together with a grading of `bundle.algebra.ring U`
  for every affine open `U`, graded transition maps which are graded base changes along the
  restriction maps, a degree-zero identification with the base section ring, a finite-type
  hypothesis over every affine open, compatibility of the grading with the chart
  trivialisations (`triv_graded`), and compatibility of the augmentation with the degree-zero
  projection (`augmentation_eq`).
* `GradedBundleData.gradedMap` — the transition maps, packaged as graded ring homomorphisms.
* `GradedBundleData.toGradedAlgebraData` — the underlying `GradedAlgebraData X`, forgetting the
  bundle chart data; this is the input to `RelativeProj.relativeProj`.
* `GradedBundleData.trivial X ι` — the trivial graded bundle `X × 𝔸^ι`, graded by total degree
  in the polynomial coordinates (needs `[Finite ι]`, for the finite-type hypothesis).
* `GradedBundleData.finiteType_degreeZero` — finite type transported from the section ring to
  the (isomorphic) degree-zero part of the grading.

## Design note

Both `bundle.algebra.isPushout` (an axiom of `AlgebraData`, inherited through `bundle`) and
`isGradedBaseChange` are independent hypotheses of `GradedBundleData`: the former is the
*ungraded* base-change condition used by `BundleData`/`RelativeSpec`, the latter the *graded*
base-change condition used by `RelativeProj`.  We have **not** derived one from the other here:
`IsGradedBaseChangeAlong` unpacks to a degreewise bijectivity statement
(`GradedHomOver.IsBaseChange`), and while the ring-level pushout square should in principle be
recoverable from the degreewise statement by summing over degrees (an element of the tensor
product `(bundle.algebra.ring V) ⊗ Γ(X,U)` decomposes as a finite sum of its homogeneous pieces,
each of which is handled by `isGradedBaseChange`), no such summation lemma currently exists in
the repository for a general `ℕ`-indexed internally-graded module (as opposed to the `Submodule`
level comparison already present in `IsGradedBaseChangeAlong`), and reconstructing it was out of
scope for this file; we therefore keep both hypotheses as independent data, exactly as the task
allows.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace

namespace GromovWitten.AlgebraicGeometry

open ProjBaseChange GlobalBlowup

universe u

noncomputable section

/-- The data of a *graded* vector bundle of rank `ι` over a scheme `X`: a `BundleData X ι`
together with an intrinsic grading of its algebra of functions over *every* affine open of `X`
(not just the trivialising charts), compatible with the transition maps, the chart
trivialisations and the augmentation. -/
structure GradedBundleData (X : Scheme.{u}) (ι : Type u) where
  /-- The underlying vector bundle data. -/
  bundle : VectorBundleTotalSpace.BundleData X ι
  /-- The grading of the algebra of functions over every affine open. -/
  grading : ∀ U : X.affineOpens, ℕ → Submodule Γ(X, U.1) (bundle.algebra.ring U)
  [gradedAlgebra : ∀ U, GradedAlgebra (grading U)]
  /-- The transition maps respect the grading. -/
  map_mem : ∀ {U V : X.affineOpens} (h : U ≤ V) {n : ℕ} {x : bundle.algebra.ring V},
    x ∈ grading V n → bundle.algebra.map h x ∈ grading U n
  /-- The transition maps, viewed as graded ring homomorphisms (`gradedMap`), are base changes
  along the restriction maps of section rings. -/
  isGradedBaseChange : ∀ {U V : X.affineOpens} (h : U ≤ V),
    IsGradedBaseChangeAlong (res X h) (grading V) (grading U)
      (⟨bundle.algebra.map h, fun {_ _} hx => map_mem h hx⟩ : grading V →+*ᵍ grading U)
  /-- The degree-zero part of the grading is the section ring. -/
  degreeZero : ∀ U, Function.Bijective (algebraMap Γ(X, U.1) (grading U 0))
  /-- The algebra of functions is of finite type over the section ring on every affine open.
  This is **not** automatic from the chart data: the trivialisations only control the charts
  themselves, not an arbitrary affine open of `X`, so it is recorded as an extra hypothesis. -/
  finiteType : ∀ U, Algebra.FiniteType Γ(X, U.1) (bundle.algebra.ring U)
  /-- The grading is compatible with the chart trivialisations: in chart coordinates it is the
  grading of `MvPolynomial ι Γ(X, chart j)` by total degree. -/
  triv_graded : ∀ (j : bundle.J) (n : ℕ),
    (grading (bundle.chart j) n).map (bundle.triv j).toLinearMap =
      MvPolynomial.homogeneousSubmodule ι Γ(X, (bundle.chart j).1) n
  /-- The augmentation (zero section) is the degree-zero projection, read in `Γ(X, U)` through
  the identification `degreeZero`. -/
  augmentation_eq : ∀ (U : X.affineOpens) (x : bundle.algebra.ring U),
    bundle.augmentation.app U x =
      (Equiv.ofBijective (algebraMap Γ(X, U.1) (grading U 0)) (degreeZero U)).symm
        (GradedRing.projZeroRingHom' (grading U) x)

attribute [instance] GradedBundleData.gradedAlgebra

namespace GradedBundleData

variable {X : Scheme.{u}} {ι : Type u}

/-- The transition maps of a graded bundle, packaged as graded ring homomorphisms. -/
def gradedMap (𝓔 : GradedBundleData X ι) {U V : X.affineOpens} (h : U ≤ V) :
    𝓔.grading V →+*ᵍ 𝓔.grading U :=
  ⟨𝓔.bundle.algebra.map h, fun {_ _} hx => 𝓔.map_mem h hx⟩

@[simp]
theorem gradedMap_apply (𝓔 : GradedBundleData X ι) {U V : X.affineOpens} (h : U ≤ V)
    (x : 𝓔.bundle.algebra.ring V) : 𝓔.gradedMap h x = 𝓔.bundle.algebra.map h x := rfl

theorem isGradedBaseChange' (𝓔 : GradedBundleData X ι) {U V : X.affineOpens} (h : U ≤ V) :
    IsGradedBaseChangeAlong (res X h) (𝓔.grading V) (𝓔.grading U) (𝓔.gradedMap h) :=
  𝓔.isGradedBaseChange h

/-- The underlying `GradedAlgebraData X`: a graded bundle gives a quasi-coherent graded algebra
on `X`, forgetting the bundle chart data.  This is the input to `RelativeProj.relativeProj` used
to build the projective completion of the bundle. -/
def toGradedAlgebraData (𝓔 : GradedBundleData X ι) : GradedAlgebraData X where
  ring U := 𝓔.bundle.algebra.ring U
  commRing _ := inferInstance
  algebra _ := inferInstance
  grading U := 𝓔.grading U
  gradedAlgebra U := 𝓔.gradedAlgebra U
  map h := 𝓔.gradedMap h
  map_id U := by
    apply GradedRingHom.ext
    intro x
    change 𝓔.bundle.algebra.map (le_refl U) x = x
    rw [𝓔.bundle.algebra.map_id]
    rfl
  map_comp hUV hVW := by
    apply GradedRingHom.ext
    intro x
    change 𝓔.bundle.algebra.map (hUV.trans hVW) x =
      𝓔.bundle.algebra.map hUV (𝓔.bundle.algebra.map hVW x)
    rw [𝓔.bundle.algebra.map_comp]
    rfl
  isBaseChange h := 𝓔.isGradedBaseChange h

@[simp]
theorem toGradedAlgebraData_ring (𝓔 : GradedBundleData X ι) (U : X.affineOpens) :
    (𝓔.toGradedAlgebraData).ring U = 𝓔.bundle.algebra.ring U := rfl

@[simp]
theorem toGradedAlgebraData_grading (𝓔 : GradedBundleData X ι) (U : X.affineOpens) :
    (𝓔.toGradedAlgebraData).grading U = 𝓔.grading U := rfl

/-- Finite type transports from the section ring to the (isomorphic, via `degreeZero`)
degree-zero part of the grading. -/
theorem finiteType_degreeZero (𝓔 : GradedBundleData X ι) (U : X.affineOpens) :
    Algebra.FiniteType (𝓔.grading U 0) (𝓔.bundle.algebra.ring U) := by
  have hft : Algebra.FiniteType Γ(X, U.1) (𝓔.bundle.algebra.ring U) := 𝓔.finiteType U
  have hst : IsScalarTower Γ(X, U.1) (𝓔.grading U 0) (𝓔.bundle.algebra.ring U) :=
    IsScalarTower.of_algebraMap_eq (R := Γ(X, U.1)) (S := 𝓔.grading U 0)
      (A := 𝓔.bundle.algebra.ring U) (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType Γ(X, U.1) (𝓔.grading U 0)
    (𝓔.bundle.algebra.ring U)

end GradedBundleData

/-! ### The trivial graded vector bundle -/

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The degree-zero projection of a polynomial, read back in the coefficient ring through the
identification of the degree-zero submodule with that ring, agrees with evaluation at the
origin.  Stated for a plain `MvPolynomial`, with no reference to `BundleData`, so that the proof
is not derailed by the semireducible unfolding of `(trivialData X ι).algebra.ring U`. -/
private theorem trivial_augmentation_eq {X : Scheme.{u}} (ι : Type u) (U : X.affineOpens)
    (p : MvPolynomial ι Γ(X, U.1)) :
    MvPolynomial.aeval (fun _ => (0 : Γ(X, U.1))) p =
      (Equiv.ofBijective (algebraMap Γ(X, U.1) (MvPolynomial.homogeneousSubmodule ι Γ(X, U.1) 0))
          (PolynomialRelativeProj.degreeZero ι X U)).symm
        (GradedRing.projZeroRingHom' (MvPolynomial.homogeneousSubmodule ι Γ(X, U.1)) p) := by
  have hdeg : Function.Bijective
      (algebraMap Γ(X, U.1) (MvPolynomial.homogeneousSubmodule ι Γ(X, U.1) 0)) :=
    PolynomialRelativeProj.degreeZero ι X U
  change MvPolynomial.aeval (fun _ => (0 : Γ(X, U.1))) p =
    (Equiv.ofBijective (algebraMap Γ(X, U.1) (MvPolynomial.homogeneousSubmodule ι Γ(X, U.1) 0))
        hdeg).symm (GradedRing.projZeroRingHom' (MvPolynomial.homogeneousSubmodule ι Γ(X, U.1)) p)
  rw [Equiv.eq_symm_apply]
  apply Subtype.ext
  change (algebraMap Γ(X, U.1) (MvPolynomial.homogeneousSubmodule ι Γ(X, U.1) 0)
      (MvPolynomial.aeval (fun _ => (0 : Γ(X, U.1))) p) : MvPolynomial ι Γ(X, U.1)) =
    (GradedRing.projZeroRingHom' (MvPolynomial.homogeneousSubmodule ι Γ(X, U.1)) p :
      MvPolynomial ι Γ(X, U.1))
  rw [SetLike.GradeZero.coe_algebraMap, GradedRing.coe_projZeroRingHom'_apply,
    GradedRing.projZeroRingHom_apply]
  change _ = (MvPolynomial.decomposition.decompose' p 0 : MvPolynomial ι Γ(X, U.1))
  rw [MvPolynomial.decomposition.decompose'_apply, MvPolynomial.homogeneousComponent_zero,
    ← MvPolynomial.constantCoeff_eq, MvPolynomial.aeval_zero']
  simp

/-- The trivial graded vector bundle `X × 𝔸^ι`, graded by total degree in the polynomial
coordinates of the (identity) trivialisation.  The hypothesis `[Finite ι]` is needed for
`finiteType`: a polynomial ring in infinitely many variables is not of finite type over its
coefficient ring, so this is a genuine (and necessary) extra hypothesis on top of the brief's
literal signature `GradedBundleData.trivial X ι`; without it the structure's `finiteType` field
cannot be filled. -/
def GradedBundleData.trivial (X : Scheme.{u}) (ι : Type u) [Finite ι] : GradedBundleData X ι where
  bundle := VectorBundleTotalSpace.trivialData X ι
  grading U n := MvPolynomial.homogeneousSubmodule ι Γ(X, U.1) n
  gradedAlgebra _ := MvPolynomial.gradedAlgebra
  map_mem := fun {_ _} h {_ _} hx =>
    GradedRingHom.map_mem (PolynomialRelativeProj.coefficientMap ι (res X h)) hx
  isGradedBaseChange h := PolynomialRelativeProj.coefficientMap_isBaseChange ι (res X h)
  degreeZero U := PolynomialRelativeProj.degreeZero ι X U
  finiteType U := by
    change Algebra.FiniteType Γ(X, U.1) (MvPolynomial ι Γ(X, U.1))
    infer_instance
  triv_graded j n := by
    let e : MvPolynomial ι Γ(X, j.1) ≃ₐ[Γ(X, j.1)] MvPolynomial ι Γ(X, j.1) := AlgEquiv.refl
    have hid : e.toLinearMap = LinearMap.id := rfl
    change (MvPolynomial.homogeneousSubmodule ι Γ(X, j.1) n).map e.toLinearMap = _
    rw [hid, Submodule.map_id]
    rfl
  augmentation_eq U p := trivial_augmentation_eq ι U p

end

end GromovWitten.AlgebraicGeometry
