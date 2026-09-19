/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeAbsolute

/-!
# The obstruction-theory property of the absolute datum

Let `R = MvPolynomial (σ ⊕ τ) k` with `σ`, `τ` finite, let `I : Ideal R` and let
`φ : E ⟶ relConormalComplex I` be a datum relative to the base `Y = 𝔸^τ`, as in
`VirtualFundamentalClass/RelativeAbsolute.lean`.  That file builds the absolute datum
`absHom φ : absComplex φ ⟶ conormalComplex k R I` and identifies its resolved cone and its
virtual class with the relative ones.  Here we prove that the two data are obstruction theories
at the same time:

* `isObstructionTheory_absHom_iff`:
  `PicardCriteria.IsObstructionTheory (absHom φ) ↔ PicardCriteria.IsObstructionTheory φ`.

Both directions are element computations with the decomposition `Tangent I ≅ (σ → R/I) × (τ → R/I)`
of `Cones/NormalConeAction.lean`.  Writing `d = E.differential`, `d_σ` for the differential of
`relConormalComplex I` and `d_τ = tauPart ∘ conormalMap`, the absolute complex has differential
`x ↦ (d x, d_τ (φ⁰ x))` and the absolute chain map is `(u, w) ↦ sigmaLift (φ¹ u) + tauLift w`,
so the `σ`- and `τ`-blocks of `H⁰` and `H⁻¹` can be compared one at a time.

## Main declarations

* `surjective_kernelMap_iff`, `surjective_cokernelMap_iff`, `injective_cokernelMap_iff`:
  the element form of the two conditions of `PicardCriteria.IsObstructionTheory` for an arbitrary
  chain map of two-term complexes.
* `sigmaPart_sigmaLift`, `tauPart_tauLift`, `sigmaPart_tauLift`, `tauPart_sigmaLift`: the four
  projection identities of the coordinate decomposition of a tangent vector.
* `surjective_kernelMap_absHom`, `surjective_cokernelMap_absHom`, `injective_cokernelMap_absHom`:
  the three conditions for `absHom φ`, deduced from the relative ones.
* `isObstructionTheory_absHom`, `isObstructionTheory_of_absHom`, `isObstructionTheory_absHom_iff`:
  the two directions and the equivalence.
* `isObstructionTheory_absHom_and_virtualClassAt`: the Chow-level corollary, combining the
  equivalence with `virtualClassAt_absHom` of `RelativeAbsolute.lean`.
-/

universe u

-- The coordinate ring of the resolved cone is a tensor product whose left factor is a quotient
-- of a Rees algebra; synthesising `CommRing` for it needs one more level of pending instance
-- problems than the default.
set_option maxSynthPendingDepth 5

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeAbsolute

open scoped TensorProduct
open NormalConeAction NormalSheafPicard
open NormalSheafPicard.AffineIntrinsicNormalSheaf

/-! ## The two conditions of an obstruction theory, in elements -/

section Elements

variable {S : Type u} [CommRing S] {C D : LinearTwoTermComplex S}

/-- **Surjectivity of `H⁻¹(f)` in elements**: every cycle of the target is the image of a cycle
of the source. -/
theorem surjective_kernelMap_iff {f : LinearTwoTermComplex.Hom C D} :
    Function.Surjective f.kernelMap ↔
      ∀ y : D.degreeZero, D.differential y = 0 →
        ∃ x : C.degreeZero, C.differential x = 0 ∧ f.degreeZero x = y := by
  constructor
  · intro h y hy
    obtain ⟨x, hx⟩ := h ⟨y, LinearMap.mem_ker.mpr hy⟩
    exact ⟨(x : C.degreeZero), LinearMap.mem_ker.mp x.2, congrArg Subtype.val hx⟩
  · intro h y
    obtain ⟨x, hx0, hx⟩ := h (y : D.degreeZero) (LinearMap.mem_ker.mp y.2)
    exact ⟨⟨x, LinearMap.mem_ker.mpr hx0⟩, Subtype.ext hx⟩

/-- **Surjectivity of `H⁰(f)` in elements**: every element of the target in degree one is the sum
of an image and a boundary. -/
theorem surjective_cokernelMap_iff {f : LinearTwoTermComplex.Hom C D} :
    Function.Surjective f.cokernelMap ↔
      ∀ a : D.degreeOne, ∃ (u : C.degreeOne) (y : D.degreeZero),
        a = f.degreeOne u + D.differential y := by
  constructor
  · intro h a
    obtain ⟨z, hz⟩ := h (Submodule.Quotient.mk a)
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [LinearTwoTermComplex.Hom.cokernelMap, Submodule.mapQ_apply,
      Submodule.Quotient.eq] at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨u, -y, by rw [map_neg, hy]; abel⟩
  · intro h z
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨u, y, hy⟩ := h a
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    rw [LinearTwoTermComplex.Hom.cokernelMap, Submodule.mapQ_apply, Submodule.Quotient.eq]
    exact ⟨-y, by rw [map_neg, hy]; abel⟩

/-- **Injectivity of `H⁰(f)` in elements**: an element of the source in degree one whose image is
a boundary is itself a boundary. -/
theorem injective_cokernelMap_iff {f : LinearTwoTermComplex.Hom C D} :
    Function.Injective f.cokernelMap ↔
      ∀ (u : C.degreeOne) (y : D.degreeZero), f.degreeOne u = D.differential y →
        ∃ x : C.degreeZero, u = C.differential x := by
  constructor
  · intro h u y hu
    have hz : f.cokernelMap (Submodule.Quotient.mk u) = f.cokernelMap 0 := by
      rw [map_zero, LinearTwoTermComplex.Hom.cokernelMap, Submodule.mapQ_apply, hu,
        Submodule.Quotient.mk_eq_zero]
      exact ⟨y, rfl⟩
    have hu0 := h hz
    rw [Submodule.Quotient.mk_eq_zero] at hu0
    obtain ⟨x, hx⟩ := hu0
    exact ⟨x, hx.symm⟩
  · intro h
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [LinearTwoTermComplex.Hom.cokernelMap, Submodule.mapQ_apply,
      Submodule.Quotient.mk_eq_zero] at hz
    obtain ⟨y, hy⟩ := hz
    obtain ⟨x, hx⟩ := h u y hy.symm
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨x, hx.symm⟩

end Elements

/-! ## The projections of the coordinate decomposition of a tangent vector -/

variable {k : Type u} [CommRing k] {σ τ : Type u}
variable (I : Ideal (MvPolynomial (σ ⊕ τ) k))

section SigmaProjection

variable [Fintype σ]

/-- The `σ`-coordinates of a tangent vector with prescribed `σ`-coordinates. -/
@[simp]
theorem sigmaPart_sigmaLift (f : σ → Base I) : sigmaPart I (sigmaLift I f) = f := by
  funext s
  rw [sigmaPart_apply, sigmaLift_apply]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single s]
  · rw [Finsupp.single_eq_same, mul_one]
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne' (fun h => hb (Sum.inl_injective h)), mul_zero]
  · intro hs
    exact absurd (Finset.mem_univ s) hs

/-- A tangent vector with prescribed `σ`-coordinates has vanishing `τ`-coordinates. -/
@[simp]
theorem tauPart_sigmaLift (f : σ → Base I) : tauPart I (sigmaLift I f) = 0 := by
  funext t
  rw [tauPart_apply, sigmaLift_apply]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, smul_eq_mul, Pi.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Finsupp.single_eq_of_ne (by simp), mul_zero]

end SigmaProjection

section TauProjection

variable [Fintype τ]

/-- The `τ`-coordinates of a tangent vector with prescribed `τ`-coordinates. -/
@[simp]
theorem tauPart_tauLift (f : τ → Base I) : tauPart I (tauLift I f) = f := by
  funext t
  rw [tauPart_apply, tauLift_apply]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single t]
  · rw [Finsupp.single_eq_same, mul_one]
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne' (fun h => hb (Sum.inr_injective h)), mul_zero]
  · intro ht
    exact absurd (Finset.mem_univ t) ht

/-- A tangent vector with prescribed `τ`-coordinates has vanishing `σ`-coordinates. -/
@[simp]
theorem sigmaPart_tauLift (f : τ → Base I) : sigmaPart I (tauLift I f) = 0 := by
  funext s
  rw [sigmaPart_apply, tauLift_apply]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, smul_eq_mul, Pi.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Finsupp.single_eq_of_ne (by simp), mul_zero]

end TauProjection

/-- The differential of the relative conormal complex is the `σ`-block of the conormal
differential. -/
theorem relConormalComplex_differential_apply (y : I.Cotangent) :
    (relConormalComplex I).differential y =
      sigmaPart I ((conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).differential y) :=
  rfl

section Main

variable [Fintype σ] [Fintype τ]

/-- **The coordinate decomposition of a tangent vector**, as a criterion. -/
theorem sigmaLift_add_tauLift_eq_iff (a : σ → Base I) (w : τ → Base I) (v : Tangent I) :
    sigmaLift I a + tauLift I w = v ↔ a = sigmaPart I v ∧ w = tauPart I v := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← h, map_add, sigmaPart_sigmaLift, sigmaPart_tauLift, add_zero]
    · rw [← h, map_add, tauPart_sigmaLift, tauPart_tauLift, zero_add]
  · rintro ⟨rfl, rfl⟩
    exact sigmaLift_sigmaPart_add_tauLift_tauPart I v

/-- The conormal differential is the sum of its `σ`- and `τ`-blocks. -/
theorem conormalMap_decomp (y : I.Cotangent) :
    (conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).differential y =
      sigmaLift I ((relConormalComplex I).differential y) +
        tauLift I (tauPart I ((conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).differential y)) :=
  (sigmaLift_sigmaPart_add_tauLift_tauPart I _).symm

variable {I}
variable {E : LinearTwoTermComplex (Base I)}
variable (φ : LinearTwoTermComplex.Hom E (relConormalComplex I))

omit [Fintype σ] [Fintype τ] in
/-- The differential of the absolute complex in coordinates. -/
theorem absComplex_differential_apply (x : E.degreeZero) :
    (absComplex φ).differential x =
      (E.differential x,
        tauPart I ((conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).differential
          (φ.degreeZero x))) :=
  rfl

/-- The value of the absolute chain map, translated by a tangent vector, in coordinates. -/
theorem absHomOne_add (u : E.degreeOne) (w : τ → Base I) (q : Tangent I) :
    absHomOne φ (u, w) + q =
      sigmaLift I (φ.degreeOne u + sigmaPart I q) + tauLift I (w + tauPart I q) := by
  rw [absHomOne_apply, map_add, map_add]
  conv_lhs => rw [← sigmaLift_sigmaPart_add_tauLift_tauPart I q]
  abel

/-! ## From the relative to the absolute obstruction theory -/

/-- **`H⁻¹` of the absolute datum is surjective** as soon as `H⁻¹(φ)` is: a conormal class killed
by the full conormal differential is killed by its `σ`-block, and the lift produced by `φ` has
vanishing `τ`-block by construction. -/
theorem surjective_kernelMap_absHom (h : Function.Surjective φ.kernelMap) :
    Function.Surjective (absHom φ).kernelMap := by
  rw [surjective_kernelMap_iff] at h ⊢
  intro y hy
  have hσ : (relConormalComplex I).differential y = 0 := by
    rw [relConormalComplex_differential_apply, hy, map_zero]
  obtain ⟨x, hx0, hx⟩ := h y hσ
  refine ⟨x, ?_, hx⟩
  rw [absComplex_differential_apply, hx0, hx, hy, map_zero]
  rfl

/-- **`H⁰` of the absolute datum is surjective** as soon as `H⁰(φ)` is: the `σ`-block of a tangent
vector is corrected by `φ`, and the `τ`-block by the tautological `τ`-directions. -/
theorem surjective_cokernelMap_absHom (h : Function.Surjective φ.cokernelMap) :
    Function.Surjective (absHom φ).cokernelMap := by
  rw [surjective_cokernelMap_iff] at h ⊢
  intro v
  obtain ⟨u, y, hy⟩ := h (sigmaPart I v)
  refine ⟨(u, tauPart I v -
    tauPart I ((conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).differential y)), y, ?_⟩
  rw [absHom_degreeOne, absHomOne_add, sub_add_cancel, ← relConormalComplex_differential_apply,
    ← hy, sigmaLift_sigmaPart_add_tauLift_tauPart]

/-- **`H⁰` of the absolute datum is injective** as soon as `H⁰(φ)` is injective and `H⁻¹(φ)` is
surjective.  The `σ`-block gives a lift `u = d x'` of the degree-one class; correcting `x'` by a
cycle produced by `H⁻¹(φ)` makes the `τ`-block match as well. -/
theorem injective_cokernelMap_absHom (hinj : Function.Injective φ.cokernelMap)
    (hker : Function.Surjective φ.kernelMap) :
    Function.Injective (absHom φ).cokernelMap := by
  rw [injective_cokernelMap_iff] at hinj ⊢
  rw [surjective_kernelMap_iff] at hker
  rintro ⟨u, w⟩ y hy
  rw [absHom_degreeOne, absHomOne_apply, sigmaLift_add_tauLift_eq_iff] at hy
  obtain ⟨hu, hw⟩ := hy
  obtain ⟨x', hx'⟩ := hinj u y (by rw [hu, relConormalComplex_differential_apply])
  have hzero : (relConormalComplex I).differential (y - φ.degreeZero x') = 0 := by
    rw [map_sub, ← φ.comm x', ← hx', hu, relConormalComplex_differential_apply, sub_self]
  obtain ⟨x'', hx''0, hx''⟩ := hker (y - φ.degreeZero x') hzero
  refine ⟨x' + x'', ?_⟩
  have h1 : E.differential (x' + x'') = u := by rw [map_add, hx''0, add_zero, hx']
  have h2 : φ.degreeZero (x' + x'') = y := by rw [map_add, hx'']; abel
  rw [absComplex_differential_apply, h1, h2, ← hw]

/-- **A relative obstruction theory gives an absolute one.** -/
theorem isObstructionTheory_absHom (h : PicardCriteria.IsObstructionTheory φ) :
    PicardCriteria.IsObstructionTheory (absHom φ) where
  bijective_cokernelMap :=
    ⟨injective_cokernelMap_absHom φ h.bijective_cokernelMap.1 h.surjective_kernelMap,
      surjective_cokernelMap_absHom φ h.bijective_cokernelMap.2⟩
  surjective_kernelMap := surjective_kernelMap_absHom φ h.surjective_kernelMap

/-! ## From the absolute back to the relative obstruction theory -/

/-- **An absolute obstruction theory comes from a relative one.**  Surjectivity and injectivity of
`H⁰(φ)` are read off from the `σ`-block; for the surjectivity of `H⁻¹(φ)` one first uses the
injectivity of `H⁰(absHom φ)` on the element `(0, d_τ y)`, which is a boundary because the
`σ`-block of `y` vanishes. -/
theorem isObstructionTheory_of_absHom (h : PicardCriteria.IsObstructionTheory (absHom φ)) :
    PicardCriteria.IsObstructionTheory φ := by
  have hcosurj : Function.Surjective φ.cokernelMap := by
    rw [surjective_cokernelMap_iff]
    intro a
    obtain ⟨⟨u, w⟩, y, hy⟩ :=
      surjective_cokernelMap_iff.mp h.bijective_cokernelMap.2 (sigmaLift I a)
    rw [absHom_degreeOne, absHomOne_apply] at hy
    have h2 := congrArg (sigmaPart I) hy
    rw [sigmaPart_sigmaLift, map_add, map_add, sigmaPart_sigmaLift, sigmaPart_tauLift,
      add_zero] at h2
    exact ⟨u, y, by rw [relConormalComplex_differential_apply]; exact h2⟩
  have hcoinj : Function.Injective φ.cokernelMap := by
    rw [injective_cokernelMap_iff]
    intro u y hu
    have habs : (absHom φ).degreeOne
        (u, tauPart I ((conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).differential y)) =
        (conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).differential y := by
      rw [absHom_degreeOne, absHomOne_apply, hu, relConormalComplex_differential_apply,
        sigmaLift_sigmaPart_add_tauLift_tauPart]
    obtain ⟨x, hx⟩ := injective_cokernelMap_iff.mp h.bijective_cokernelMap.1 _ y habs
    exact ⟨x, congrArg Prod.fst hx⟩
  refine ⟨⟨hcoinj, hcosurj⟩, ?_⟩
  rw [surjective_kernelMap_iff]
  intro y hy
  have habs : (absHom φ).degreeOne
      ((0 : E.degreeOne),
        tauPart I ((conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).differential y)) =
      (conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).differential y := by
    rw [absHom_degreeOne, absHomOne_apply, map_zero, map_zero, zero_add]
    conv_rhs => rw [conormalMap_decomp]
    rw [hy, map_zero, zero_add]
  obtain ⟨x, hx⟩ := injective_cokernelMap_iff.mp h.bijective_cokernelMap.1 _ y habs
  have hx0 : E.differential x = 0 := (congrArg Prod.fst hx).symm
  have hx1 : tauPart I ((conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).differential
      (φ.degreeZero x)) =
      tauPart I ((conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).differential y) :=
    (congrArg Prod.snd hx).symm
  have hcyc : (conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).differential
      (y - φ.degreeZero x) = 0 := by
    have e1 : (relConormalComplex I).differential (y - φ.degreeZero x) = 0 := by
      rw [map_sub, hy, ← φ.comm x, hx0, map_zero, sub_zero]
    have e2 : tauPart I ((conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).differential
        (y - φ.degreeZero x)) = 0 := by
      rw [map_sub, map_sub, hx1, sub_self]
    rw [conormalMap_decomp, e1, e2, map_zero, map_zero, add_zero]
  obtain ⟨x', hx'0, hx'⟩ :=
    surjective_kernelMap_iff.mp h.surjective_kernelMap (y - φ.degreeZero x) hcyc
  have hx'e : E.differential x' = 0 := congrArg Prod.fst hx'0
  have hx'2 : φ.degreeZero x' = y - φ.degreeZero x := hx'
  refine ⟨x + x', by rw [map_add, hx0, hx'e, add_zero], ?_⟩
  rw [map_add, hx'2]
  abel

/-- **The absolute datum is an obstruction theory exactly when the relative one is.**  This is the
affine model of Behrend–Fantechi's comparison of relative and absolute obstruction theories over
the smooth base `Y = 𝔸^τ`. -/
theorem isObstructionTheory_absHom_iff :
    PicardCriteria.IsObstructionTheory (absHom φ) ↔ PicardCriteria.IsObstructionTheory φ :=
  ⟨isObstructionTheory_of_absHom φ, isObstructionTheory_absHom φ⟩

/-! ## The Chow-level corollary -/

section Cycle

open IntersectionTheory

variable [IsNoetherianRing k]
variable [Module.Free (Base I) E.degreeZero] [Module.Finite (Base I) E.degreeZero]
variable {ι : Type u} [Finite ι]
variable (e : ResolvedCone.bundleRing (absHom φ) ≃ₐ[Base I] MvPolynomial ι (Base I))
variable (dimX : DimensionFunction (_root_.AlgebraicGeometry.Spec (CommRingCat.of (Base I))))
variable (dimE : DimensionFunction (ResolvedCone.bundleSpace (absHom φ))) (i : ℤ)
variable (RX : RationalEquivalenceSystem
  (_root_.AlgebraicGeometry.Spec (CommRingCat.of (Base I))) dimX i)
variable (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace (absHom φ)) dimE
  (i + (Nat.card ι : ℤ)))

/-- **A relative obstruction theory produces an absolute obstruction theory whose virtual class is
the relative virtual class.**  This combines `isObstructionTheory_absHom` with
`virtualClassAt_absHom` of `VirtualFundamentalClass/RelativeAbsolute.lean`. -/
theorem isObstructionTheory_absHom_and_virtualClassAt
    (h : PicardCriteria.IsObstructionTheory φ)
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace (absHom φ)) dimE)
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE i RX RE)) :
    PicardCriteria.IsObstructionTheory (absHom φ) ∧
      VirtualClass.virtualClassAt (absHom φ) e dimX dimE i RX RE hhom hinj =
        relativeVirtualClass φ e dimX dimE i RX RE hhom hinj :=
  ⟨isObstructionTheory_absHom φ h, virtualClassAt_absHom φ e dimX dimE i RX RE hhom hinj⟩

end Cycle

end Main

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeAbsolute
