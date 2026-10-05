/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.ProjectiveCompletion
import GromovWitten.AlgebraicGeometry.RelativeSpecPolynomial

/-!
# The graded vector bundle `E ⊕ 1`

For a graded vector bundle `E = Spec_X 𝒜` of rank `ι` (`GradedBundleData X ι`), the
homogenisation `𝒜[t]` (`deg t = 1`) is the algebra of functions of the bundle `E ⊕ 𝔸¹` of rank
`Option ι`, the new coordinate being `t = x_none`.  This file packages it as a graded bundle
`GradedBundleData.extend 𝓔 : GradedBundleData X (Option ι)` whose underlying graded algebra
data is *definitionally* the homogenisation `𝓔.homogData`.  Consequently the relative `Proj` of
`𝓔.extend` is the projective completion `P(E ⊕ 1)` of `𝓔`, the projective completion of
`𝓔.extend` is `P((E ⊕ 1) ⊕ 1)`, and the embedding at infinity of `𝓔.extend` is a closed
immersion `P(E ⊕ 1) ⟶ P((E ⊕ 1) ⊕ 1)` over `X`.

## Main results

* `GradedBundleData.extendBundle`: the bundle data of `E ⊕ 𝔸¹`, with zero section
  `extendAugmentation` and chart trivialisations `extendTriv`.
* `GradedBundleData.extend`: the graded bundle `E ⊕ 1`, with algebra of functions
  `𝓔.bundle.algebra.polynomial` (`(𝒜 U)[t]` over every affine open `U`), the zero section
  `t ↦ 0` followed by the zero section of `E`, the same charts as `𝓔`, the chart
  trivialisations `(𝒜 U)[t] ≅ Γ(U)[x_k][t] ≅ Γ(U)[x_i : i ∈ Option ι]` (`t ↦ x_none`), and the
  grading of the homogenisation.
* `GradedBundleData.extend_toGradedAlgebraData`: `𝓔.extend.toGradedAlgebraData = 𝓔.homogData`
  (by `rfl`).
* `GradedBundleData.extend_triv_apply`: the chart trivialisations of `𝓔.extend` are the graded
  chart identifications `𝓔.chartGraded j` of `P(E ⊕ 1)`.
* `GradedBundleData.extend_relativeProj`:
  `relativeProj X 𝓔.extend.toGradedAlgebraData = 𝓔.projectiveCompletion` (by `rfl`).
* `GradedBundleData.hyperplaneEmbedding : 𝓔.projectiveCompletion ⟶
  𝓔.extend.projectiveCompletion`, the embedding at infinity of `𝓔.extend`; it is a closed
  immersion (`isClosedImmersion_hyperplaneEmbedding`) over `X`
  (`hyperplaneEmbedding_toBase`).
* `GradedBundleData.extendProj : 𝓔.extend.bundle.totalSpace ⟶ 𝓔.bundle.totalSpace`, the
  projection `E ⊕ 𝔸¹ → E` induced by the coefficient inclusion `𝒜 → 𝒜[t]`, over `X`
  (`extendProj_proj`), sending the zero section to the zero section (`zeroSection_extendProj`).
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

open GromovWitten.Algebra RelativeProj VectorBundleTotalSpace ProjBaseChange GlobalBlowup

universe u

noncomputable section

namespace GradedBundleData

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : GradedBundleData X ι)

/-! ### The bundle data of `E ⊕ 1` -/

/-- Evaluation at the origin after the chart identification
`A[t] ≅ R[x_k : k ∈ ι][t] ≅ R[x_i : i ∈ Option ι]` is `t ↦ 0` followed by the augmentation of
`A`, provided the augmentation of `A` is evaluation at the origin in the chart. -/
private theorem extendAugmentation_aux {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (aug : A →ₐ[R] R) (e : A ≃ₐ[R] MvPolynomial ι R)
    (he : ∀ a, aug a = MvPolynomial.aeval (fun _ ↦ (0 : R)) (e a)) (p : Polynomial A) :
    Polynomial.eval₂ (aug : A →+* R) 0 p =
      MvPolynomial.aeval (fun _ ↦ (0 : R))
        ((MvPolynomial.optionEquivLeft R ι).symm
          (Polynomial.map (e : A →+* MvPolynomial ι R) p)) := by
  have hC : ∀ q : MvPolynomial ι R, MvPolynomial.aeval (fun _ ↦ (0 : R))
      ((MvPolynomial.optionEquivLeft R ι).symm (Polynomial.C q)) =
        MvPolynomial.aeval (fun _ ↦ (0 : R)) q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp [map_mul, hp]
  induction p using Polynomial.induction_on with
  | C a => rw [Polynomial.eval₂_C, Polynomial.map_C, hC]; exact he a
  | add p q hp hq => rw [Polynomial.eval₂_add, hp, hq, Polynomial.map_add, map_add, map_add]
  | monomial n a _ => simp

/-- The zero section of `E ⊕ 1` on functions: `t ↦ 0`, followed by the zero section of `E`. -/
def extendAugmentation :
    RelativeSpec.Hom X (structureData X) 𝓔.bundle.algebra.polynomial where
  app U := Polynomial.eval₂AlgHom (𝓔.bundle.augmentation.app U) 0
    (fun _ ↦ Commute.zero_right _)
  naturality {U V} h := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · change Polynomial.eval₂ _ 0 (Polynomial.map (𝓔.bundle.algebra.map h) (Polynomial.C a)) =
        res X h (Polynomial.eval₂ _ 0 (Polynomial.C a))
      erw [Polynomial.map_C, Polynomial.eval₂_C, Polynomial.eval₂_C]
      exact congrArg (fun f ↦ f a) (𝓔.bundle.augmentation.naturality h)
    · change Polynomial.eval₂ _ 0 (Polynomial.map (𝓔.bundle.algebra.map h) Polynomial.X) =
        res X h (Polynomial.eval₂ _ 0 Polynomial.X)
      erw [Polynomial.map_X, Polynomial.eval₂_X, Polynomial.eval₂_X, map_zero]

/-- The chart trivialisations of `E ⊕ 1`: apply the trivialisation of `E` coefficientwise and
identify `Γ(U)[x_k : k ∈ ι][t]` with `Γ(U)[x_i : i ∈ Option ι]`, `t ↦ x_none`. -/
def extendTriv (j : 𝓔.bundle.J) :
    Polynomial (𝓔.bundle.algebra.ring (𝓔.bundle.chart j)) ≃ₐ[Γ(X, (𝓔.bundle.chart j).1)]
      MvPolynomial (Option ι) Γ(X, (𝓔.bundle.chart j).1) :=
  (Polynomial.mapAlgEquiv (𝓔.bundle.triv j)).trans
    (homogEquivOption Γ(X, (𝓔.bundle.chart j).1) ι)

/-- The bundle data of `E ⊕ 1`. -/
def extendBundle : BundleData X (Option ι) where
  algebra := 𝓔.bundle.algebra.polynomial
  augmentation := 𝓔.extendAugmentation
  J := 𝓔.bundle.J
  chart := 𝓔.bundle.chart
  iSup_chart := 𝓔.bundle.iSup_chart
  triv := 𝓔.extendTriv
  augmentation_triv j a := by
    exact extendAugmentation_aux (𝓔.bundle.augmentation.app _) (𝓔.bundle.triv j)
      (𝓔.bundle.augmentation_triv j) a

/-! ### The graded bundle `E ⊕ 1` -/

/-- For the homogenisation `𝒜[t]` of a graded algebra, the degree-zero projection of `x`, read
in `R` through `R ≅ (𝒜[t])₀`, is the degree-zero projection of the constant coefficient
`x(0)`, read in `R` through `R ≅ 𝒜₀`. -/
private theorem extend_augmentation_eq_aux {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜] (h0 : Function.Bijective (algebraMap R (𝒜 0)))
    (aug : S →+* R)
    (haug : ∀ s, aug s = (Equiv.ofBijective _ h0).symm (GradedRing.projZeroRingHom' 𝒜 s))
    (x : Polynomial S) :
    Polynomial.eval₂ aug 0 x =
      (Equiv.ofBijective (algebraMap R (homog 𝒜 0)) (bijective_algebraMap_homog_zero h0)).symm
        (GradedRing.projZeroRingHom' (homog 𝒜) x) := by
  rw [Equiv.eq_symm_apply, Equiv.ofBijective_apply]
  apply Subtype.ext
  rw [SetLike.GradeZero.coe_algebraMap, GradedRing.coe_projZeroRingHom'_apply,
    GradedRing.projZeroRingHom_apply, Polynomial.eval₂_at_zero, haug,
    Polynomial.algebraMap_apply]
  set y := DirectSum.decompose (homog 𝒜) x 0 with hy
  have hdeg : (y : Polynomial S) = Polynomial.C ((y : Polynomial S).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp (natDegree_le_of_mem_homog y.2))
  have hcoeff : (y : Polynomial S).coeff 0 = (DirectSum.decompose 𝒜 (x.coeff 0) 0 : S) := by
    have := GradedRingHom.map_directSumDecompose (homog 𝒜) 𝒜 (evalZeroGraded 𝒜) (x := x) (i := 0)
    rw [hy]
    exact this
  rw [hdeg, hcoeff]
  congr 1
  exact congrArg Subtype.val ((Equiv.ofBijective _ h0).apply_symm_apply _)

/-- The graded bundle `E ⊕ 1` of rank `Option ι` (the new coordinate `t = x_none`): bundle data
`extendBundle`, graded by the homogenisation of the grading of `E` (`deg t = 1`). -/
def extend : GradedBundleData X (Option ι) where
  bundle := 𝓔.extendBundle
  grading U := 𝓔.homogData.grading U
  gradedAlgebra U := 𝓔.homogData.gradedAlgebra U
  map_mem := fun {_ _} h {_ _} hx => (𝓔.homogData.map h).map_mem hx
  isGradedBaseChange h := 𝓔.homogData.isBaseChange h
  degreeZero U := bijective_algebraMap_homog_zero (𝒜 := 𝓔.grading U) (𝓔.degreeZero U)
  finiteType U := by
    have h : Algebra.FiniteType Γ(X, U.1) (𝓔.bundle.algebra.ring U) := 𝓔.finiteType U
    change Algebra.FiniteType Γ(X, U.1) (Polynomial (𝓔.bundle.algebra.ring U))
    exact h.trans inferInstance
  triv_graded j n := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (𝓔.chartGraded j).map_mem hp
    · intro hq
      exact ⟨𝓔.chartGradedInv j q, (𝓔.chartGradedInv j).map_mem hq,
        GradedRingHom.congr_fun (𝓔.chartGraded_comp_chartGradedInv j) q⟩
  augmentation_eq U x :=
    extend_augmentation_eq_aux (𝓔.grading U) (𝓔.degreeZero U)
      (𝓔.bundle.augmentation.app U).toRingHom
      (𝓔.augmentation_eq U) x

/-- The underlying graded algebra data of `E ⊕ 1` is the homogenisation `𝒜[t]` of that of `E`;
this holds by definition. -/
theorem extend_toGradedAlgebraData : 𝓔.extend.toGradedAlgebraData = 𝓔.homogData := rfl

/-- The relative `Proj` of `E ⊕ 1` is the projective completion `P(E ⊕ 1)` of `E`; this holds
by definition. -/
theorem extend_relativeProj :
    relativeProj X 𝓔.extend.toGradedAlgebraData = 𝓔.projectiveCompletion := rfl

/-- The algebra of functions of `E ⊕ 1` is `𝒜[t]`; this holds by definition. -/
theorem extend_bundle_algebra : 𝓔.extend.bundle.algebra = 𝓔.bundle.algebra.polynomial := rfl

/-- The charts of `E ⊕ 1` are those of `E`; this holds by definition. -/
theorem extend_bundle_chart : 𝓔.extend.bundle.chart = 𝓔.bundle.chart := rfl

/-- The chart trivialisations of `E ⊕ 1` are the graded chart identifications `chartGraded` of
the projective completion `P(E ⊕ 1)` (so `t ↦ x_none`, `x_k ↦ x_(some k)`); this holds by
definition. -/
theorem extend_triv_apply (j : 𝓔.bundle.J)
    (p : Polynomial (𝓔.bundle.algebra.ring (𝓔.bundle.chart j))) :
    𝓔.extend.bundle.triv j p = 𝓔.chartGraded j p := rfl

/-! ### The hyperplane at infinity `P(E ⊕ 1) ⊂ P((E ⊕ 1) ⊕ 1)` -/

/-- The embedding at infinity of `E ⊕ 1`, `P(E ⊕ 1) ⟶ P((E ⊕ 1) ⊕ 1)`: the embedding
`𝓔.extend.infinityDivisor`, whose source `relativeProj X 𝓔.extend.toGradedAlgebraData` is by
definition `𝓔.projectiveCompletion` (`extend_relativeProj`). -/
def hyperplaneEmbedding : 𝓔.projectiveCompletion ⟶ 𝓔.extend.projectiveCompletion :=
  𝓔.extend.infinityDivisor

/-- The hyperplane embedding is a closed immersion. -/
instance isClosedImmersion_hyperplaneEmbedding : IsClosedImmersion 𝓔.hyperplaneEmbedding :=
  𝓔.extend.isClosedImmersion_infinityDivisor

/-- The hyperplane embedding lies over `X`. -/
@[reassoc (attr := simp)]
theorem hyperplaneEmbedding_toBase :
    𝓔.hyperplaneEmbedding ≫ 𝓔.extend.completionToBase = 𝓔.completionToBase :=
  𝓔.extend.infinityDivisor_toBase

/-! ### The projection `E ⊕ 𝔸¹ → E` -/

/-- The projection `E ⊕ 𝔸¹ → E` of total spaces, induced by the coefficient inclusion
`𝒜 → 𝒜[t]`. -/
def extendProj : 𝓔.extend.bundle.totalSpace ⟶ 𝓔.bundle.totalSpace :=
  𝓔.bundle.algebra.polynomialProjection

/-- The projection `E ⊕ 𝔸¹ → E` lies over `X`. -/
@[reassoc (attr := simp)]
theorem extendProj_proj : 𝓔.extendProj ≫ 𝓔.bundle.proj = 𝓔.extend.bundle.proj :=
  𝓔.bundle.algebra.polynomialInclusion.map_toBase

/-- The projection `E ⊕ 𝔸¹ → E` maps the zero section to the zero section. -/
@[reassoc (attr := simp)]
theorem zeroSection_extendProj :
    𝓔.extend.bundle.zeroSection ≫ 𝓔.extendProj = 𝓔.bundle.zeroSection := by
  have h : 𝓔.extendAugmentation.comp 𝓔.bundle.algebra.polynomialInclusion =
      𝓔.bundle.augmentation := by
    ext U a
    exact Polynomial.eval₂_C _ _
  change ((baseIso X).inv ≫ 𝓔.extendAugmentation.map) ≫
    𝓔.bundle.algebra.polynomialInclusion.map = (baseIso X).inv ≫ 𝓔.bundle.augmentation.map
  rw [Category.assoc, ← RelativeSpec.Hom.map_comp, h]

end GradedBundleData

end

end GromovWitten.AlgebraicGeometry
