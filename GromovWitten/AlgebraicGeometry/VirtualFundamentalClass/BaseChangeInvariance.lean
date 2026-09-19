/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.BaseChangeConeIdeal
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.DegreeOneSummand
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.IndependenceAcyclic
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackBaseChange

/-!
# The virtual class is compatible with the base change `X × 𝔸^τ → X`

This file is the Layer-8 assembly, in the affine polynomial model, of Behrend–Fantechi's
Proposition 7.2 for the smooth projection `X × 𝔸^τ → X`.  The notation is that of
`VirtualFundamentalClass/BaseChangeCone.lean` and `BaseChangeConeIdeal.lean`: `k` is a Noetherian
commutative ring, `σ`, `τ` are finite, `R = k[x_σ]`, `A' = k[y_τ]`, `R' = A'[x_σ]`, `I ⊆ R`,
`I' = I·R'`, `B = R/I`, `B' = R'/I'`, `φ : E ⟶ conormalComplex k R I` is an affine obstruction
datum with `E⁻¹` free and finite over `B`, and `ψ = baseChangeHom τ I φ` is its base change,
an obstruction datum over `A'` on `X' = Spec B' = X × 𝔸^τ`.

## Contents

* `polyBundleAlgEquiv`: `BaseChangeCone.polyBundleRingEquiv` as an isomorphism of `B`-algebras
  `Sym_{B'}(B' ⊗_B E⁻¹) ≃ₐ[B] (Sym_B E⁻¹)[y_τ]`, and the induced isomorphisms of schemes
  `bundleSpaceIsoPoly : E₁' ≅ E₁ × 𝔸^τ`, `coneSchemeIsoPoly : C(E) × 𝔸^τ ≅ C(E)'`.
* `trivializationBaseChange`: the trivialisation of the bundle `E₁'` induced by a trivialisation
  `e` of `E₁`, with the *same* index type (hence the same rank), together with the two
  trivialisations `totalTrivializationBaseChange`, `PullbackBaseChange.totalTrivialization` of
  `E₁'` and of `E₁ × 𝔸^τ` as bundles over `X`.
* `bundleImm_comp_specPolyBundle`: the commuting square of closed immersions
  `C(E) × 𝔸^τ ↪ E₁ × 𝔸^τ` and `C(E)' ↪ E₁'`, the scheme-level form of
  `BaseChangeCone.ringEquiv_comp_mk`.
* **Cycle level** (`flatPullbackOpen_flatPullbackBundle_resolvedConeCycleAt`): the resolved-cone
  cycle of `ψ` is, through `bundleSpaceIsoPoly`, the flat pullback of the resolved-cone cycle of
  `φ` along the trivial bundle `E₁ × 𝔸^τ → E₁`.
* **Chow level** (`chowPullbackBundle_baseChange_square`): flat pullback along the bundle `E₁' → X'`
  composed with flat pullback along `X' → X` agrees with flat pullback along `E₁ × 𝔸^τ → E₁`
  composed with flat pullback along `E₁ → X`, transported by `bundleSpaceIsoPoly`.
* **Main theorem** `virtualClassAt_baseChangeHom`: for every degree `i` and compatible
  rational-equivalence systems,
  `virtualClassAt ψ (trivializationBaseChange τ I φ e) dimX' dimE' (i + rk τ) RX' RE' hhom' hinj'
  = chowPullbackBundle (baseAlgEquiv τ I) dimX dimX' i RX RX'
  (virtualClassAt φ e dimX dimE i RX RE hhom hinj)`,
  and its relative form `relativeVirtualClassAt_baseChangeHom`, which reads the left-hand side as
  the relative virtual class of `ψ` in relative dimension `Nat.card τ`
  (`DegreeOneSummand.relativeVirtualClassAt`); by `virtualDimension_baseChangeHom` the degree
  `virtualDimension ψ` occurring there is `virtualDimension φ`.

All the dimension functions are arbitrary (certified dimension gradings on isomorphic affine
schemes automatically agree, `VectorBundle.dimension_comap_algEquiv`), and the
`RationalEquivalenceSystem`s are canonical; the only hypotheses are the homogeneity and
injectivity inputs `hhom`, `hinj` of `VectorBundle.zeroSectionGysin'` itself.
-/

universe u

open scoped TensorProduct

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.BaseChangeInvariance

open IntersectionTheory hiding Scheme AlgebraicCycle
open IntersectionTheory.VectorBundle
open NormalSheafPicard.AffineIntrinsicNormalSheaf
open VirtualClass BaseChangeCone

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {k : Type u} [CommRing k] [IsNoetherianRing k] {σ : Type u} [Finite σ]
variable (τ : Type u) [Finite τ] (I : Ideal (MvPolynomial σ k))
variable {E : LinearTwoTermComplex (MvPolynomial σ k ⧸ I)}
variable [Module.Free (MvPolynomial σ k ⧸ I) E.degreeZero]
variable [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))

/-- **The coordinate ring of the base-changed bundle `E₁'`**, as a `B`-algebra: the ring
isomorphism `BaseChangeCone.polyBundleRingEquiv` is an isomorphism of algebras over the base
`B = R ⧸ I` of the original obstruction datum. -/
noncomputable def polyBundleAlgEquiv :
    ResolvedCone.bundleRing (baseChangeHom τ I φ) ≃ₐ[MvPolynomial σ k ⧸ I]
      MvPolynomial τ (ResolvedCone.bundleRing φ) :=
  { polyBundleRingEquiv τ I φ with
    commutes' := by
      intro b
      rw [IsScalarTower.algebraMap_apply (MvPolynomial σ k ⧸ I) (baseExt τ I)
        (ResolvedCone.bundleRing (baseChangeHom τ I φ))]
      change polyBundleRingEquiv τ I φ _ = _
      rw [polyBundleRingEquiv_algebraMap, baseRingEquiv_algebraMap]
      rw [IsScalarTower.algebraMap_apply (MvPolynomial σ k ⧸ I) (ResolvedCone.bundleRing φ)
        (MvPolynomial τ (ResolvedCone.bundleRing φ))]
      simp [MvPolynomial.algebraMap_eq] }

variable {ι : Type u} [Finite ι]
  (e : ResolvedCone.bundleRing φ ≃ₐ[MvPolynomial σ k ⧸ I]
    MvPolynomial ι (MvPolynomial σ k ⧸ I))

/-- The trivialisation of the base-changed bundle `E₁'` over `X' = Spec B'` induced by a
trivialisation `e` of `E₁` over `X = Spec B`.  The index type, hence the rank, is unchanged. -/
noncomputable def trivializationBaseChange :
    ResolvedCone.bundleRing (baseChangeHom τ I φ) ≃ₐ[baseExt τ I]
      MvPolynomial ι (baseExt τ I) :=
  (bundleRingEquiv τ I φ).trans
    ((Algebra.TensorProduct.congr
        (AlgEquiv.refl (R := baseExt τ I) (A₁ := baseExt τ I)) e).trans
      (MvPolynomial.algebraTensorAlgEquiv (MvPolynomial σ k ⧸ I) (baseExt τ I)))

/-- The trivialisation of `E₁'` as a bundle of rank `rk ι + rk τ` over the *original* base
`X = Spec B`, obtained from `trivializationBaseChange` and `BaseChangeCone.baseAlgEquiv`. -/
noncomputable def totalTrivializationBaseChange :
    ResolvedCone.bundleRing (baseChangeHom τ I φ) ≃ₐ[MvPolynomial σ k ⧸ I]
      MvPolynomial (ι ⊕ τ) (MvPolynomial σ k ⧸ I) :=
  ((trivializationBaseChange τ I φ e).restrictScalars (MvPolynomial σ k ⧸ I)).trans
    ((MvPolynomial.mapAlgEquiv ι (baseAlgEquiv τ I)).trans
      (MvPolynomial.sumAlgEquiv (MvPolynomial σ k ⧸ I) ι τ).symm)

/-- `B'` is nontrivial as soon as `B` is, since `B' ≃ B[y_τ]`. -/
instance nontrivialBaseExt [Nontrivial (MvPolynomial σ k ⧸ I)] : Nontrivial (baseExt τ I) :=
  (baseRingEquiv τ I).toEquiv.nontrivial

omit [IsNoetherianRing k] [Finite σ] [Finite τ]
  [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero] in
/-- **The base change does not change the virtual dimension**: the two terms of `E` are
replaced by their base changes to `B'`, whose ranks are unchanged. -/
theorem virtualDimension_baseChangeHom [Nontrivial (MvPolynomial σ k ⧸ I)]
    [Module.Free (MvPolynomial σ k ⧸ I) E.degreeOne] :
    virtualDimension (baseChangeHom τ I φ) = virtualDimension φ := by
  have h0 : Module.finrank (baseExt τ I) (E.baseChange (baseExt τ I)).degreeZero =
      Module.finrank (MvPolynomial σ k ⧸ I) E.degreeZero :=
    Module.finrank_baseChange
  have h1 : Module.finrank (baseExt τ I) (E.baseChange (baseExt τ I)).degreeOne =
      Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne :=
    Module.finrank_baseChange
  change ((_ : ℕ) : ℤ) - (_ : ℕ) = ((_ : ℕ) : ℤ) - (_ : ℕ)
  rw [h0, h1]

/-! ## The square of closed immersions -/

/-- **The base-changed bundle is the trivial `𝔸^τ`-bundle over `E₁`**: the isomorphism of
schemes `E₁' ≅ E₁ × 𝔸^τ` induced by `polyBundleAlgEquiv`. -/
noncomputable def bundleSpaceIsoPoly :
    ResolvedCone.bundleSpace (baseChangeHom τ I φ) ≅
      Spec (CommRingCat.of (MvPolynomial τ (ResolvedCone.bundleRing φ))) :=
  (specIsoOfAlgEquiv (polyBundleAlgEquiv τ I φ)).symm

omit [IsNoetherianRing k] [Finite σ] [Finite τ] [Module.Free (MvPolynomial σ k ⧸ I) E.degreeZero]
  [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero] in
/-- The inverse of `bundleSpaceIsoPoly` is `Spec` of `polyBundleAlgEquiv`. -/
theorem bundleSpaceIsoPoly_inv :
    (bundleSpaceIsoPoly τ I φ).inv =
      Spec.map (CommRingCat.ofHom (polyBundleAlgEquiv τ I φ).toRingHom) := rfl

omit [IsNoetherianRing k] [Finite σ] [Finite τ] [Module.Free (MvPolynomial σ k ⧸ I) E.degreeZero]
  [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero] in
/-- `bundleSpaceIsoPoly` is `Spec` of the inverse of `polyBundleAlgEquiv`. -/
theorem bundleSpaceIsoPoly_hom :
    (bundleSpaceIsoPoly τ I φ).hom =
      Spec.map (CommRingCat.ofHom (polyBundleAlgEquiv τ I φ).symm.toRingHom) := rfl

/-- **The base-changed resolved cone is the trivial `𝔸^τ`-bundle over `C(E)`**: the
isomorphism of schemes `C(E) × 𝔸^τ ≅ C(E)'` induced by `BaseChangeCone.ringEquiv`. -/
noncomputable def coneSchemeIsoPoly :
    Spec (CommRingCat.of (MvPolynomial τ (ResolvedCone.ring φ))) ≅
      ResolvedCone.scheme (baseChangeHom τ I φ) where
  hom := Spec.map (CommRingCat.ofHom (ringEquiv τ I φ).toRingHom)
  inv := Spec.map (CommRingCat.ofHom (ringEquiv τ I φ).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => by simp)
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => by simp)

omit [IsNoetherianRing k] [Finite σ] [Finite τ] [Module.Free (MvPolynomial σ k ⧸ I) E.degreeZero]
  [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero] in
/-- `coneSchemeIsoPoly` is `Spec` of `BaseChangeCone.ringEquiv`. -/
theorem coneSchemeIsoPoly_hom :
    (coneSchemeIsoPoly τ I φ).hom =
      Spec.map (CommRingCat.ofHom (ringEquiv τ I φ).toRingHom) := rfl

omit [IsNoetherianRing k] [Finite σ] [Finite τ] [Module.Free (MvPolynomial σ k ⧸ I) E.degreeZero]
  [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero] in
/-- **The commuting square of closed immersions** `C(E) × 𝔸^τ ↪ E₁ × 𝔸^τ` and
`C(E)' ↪ E₁'`: the scheme-level form of `BaseChangeCone.ringEquiv_comp_mk`. -/
theorem bundleImm_comp_specPolyBundle :
    PullbackBaseChange.bundleImm (ResolvedCone.ideal φ) (τ := τ) ≫ (bundleSpaceIsoPoly τ I φ).inv =
      (coneSchemeIsoPoly τ I φ).hom ≫ ResolvedCone.toBundle (baseChangeHom τ I φ) := by
  rw [coneSchemeIsoPoly_hom, bundleSpaceIsoPoly_inv, ResolvedCone.toBundle, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (ringEquiv_comp_mk τ I φ).symm

variable (dimE' : DimensionFunction (ResolvedCone.bundleSpace (baseChangeHom τ I φ)))
  (dimEp : DimensionFunction
    (Spec (CommRingCat.of (MvPolynomial τ (ResolvedCone.bundleRing φ)))))

/-- The pushforward of the fundamental cycle of `C(E) × 𝔸^τ` along the closed immersion into
`E₁ × 𝔸^τ`, transported along `bundleSpaceIsoPoly`, is the pushforward of the fundamental cycle
of `C(E)'` along `C(E)' ↪ E₁'`. -/
theorem map_specPolyBundle_map_bundleImm :
    AlgebraicCycle.map (bundleSpaceIsoPoly τ I φ).inv dimEp dimE'
        (AlgebraicCycle.map (PullbackBaseChange.bundleImm (ResolvedCone.ideal φ) (τ := τ))
          (dimEp.comapClosedImmersion
            (PullbackBaseChange.bundleImm (ResolvedCone.ideal φ) (τ := τ))) dimEp
          (Spec (CommRingCat.of (MvPolynomial τ (ResolvedCone.ring φ)))).fundamentalCycle) =
      AlgebraicCycle.map (ResolvedCone.toBundle (baseChangeHom τ I φ))
        (coneDimension (baseChangeHom τ I φ) dimE') dimE'
        (ResolvedCone.scheme (baseChangeHom τ I φ)).fundamentalCycle := by
  have hiso : IsIso (coneSchemeIsoPoly τ I φ).hom := inferInstance
  rw [← map_comp_closedImmersion, map_congr_hom (bundleImm_comp_specPolyBundle τ I φ),
    map_comp_closedImmersion _ _ _ (coneDimension (baseChangeHom τ I φ) dimE') _]
  exact congrArg
    (AlgebraicCycle.map (ResolvedCone.toBundle (baseChangeHom τ I φ))
      (coneDimension (baseChangeHom τ I φ) dimE') dimE')
    (map_fundamentalCycle_of_isIso (coneSchemeIsoPoly τ I φ) _ _)

/-- **The resolved-cone cycle of the base change, before grading**: the flat pullback of the
pushforward of the fundamental cycle of `C(E)` along the trivial bundle `E₁ × 𝔸^τ → E₁`,
restricted along `bundleSpaceIsoPoly`, is the pushforward of the fundamental cycle of `C(E)'`.
The fundamental-cycle input is `VirtualClass.pullbackBundle_fundamentalCycle` and the
base-change square is `PullbackBaseChange.pullbackBundle_map_baseImm_fundamentalCycle`. -/
theorem pullbackOpen_pullbackBundle_map_toBundle
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) :
    AlgebraicCycle.pullbackOpen (bundleSpaceIsoPoly τ I φ).hom
        (AlgebraicCycle.pullbackBundle
          (PullbackBaseChange.trivialBundle (ResolvedCone.bundleRing φ) τ)
          (AlgebraicCycle.map (ResolvedCone.toBundle φ) (coneDimension φ dimE) dimE
            (ResolvedCone.scheme φ).fundamentalCycle)) =
      AlgebraicCycle.map (ResolvedCone.toBundle (baseChangeHom τ I φ))
        (coneDimension (baseChangeHom τ I φ) dimE') dimE'
        (ResolvedCone.scheme (baseChangeHom τ I φ)).fundamentalCycle := by
  have dimEp : DimensionFunction
      (Spec (CommRingCat.of (MvPolynomial τ (ResolvedCone.bundleRing φ)))) :=
    DimensionFunction.comapClosedImmersion (bundleSpaceIsoPoly τ I φ).inv dimE'
  rw [AlgebraicCycle.pullbackOpen_eq_map_of_isIso (bundleSpaceIsoPoly τ I φ) dimE' dimEp,
    ← map_specPolyBundle_map_bundleImm τ I φ dimE' dimEp]
  exact congrArg (AlgebraicCycle.map (bundleSpaceIsoPoly τ I φ).inv dimEp dimE')
    (PullbackBaseChange.pullbackBundle_map_baseImm_fundamentalCycle (ResolvedCone.ideal φ)
      dimE dimEp (pullbackBundle_fundamentalCycle _))

/-- **The resolved-cone cycle is compatible with the base change `X × 𝔸^τ → X`**: in every
degree `d`, the flat pullback of `[C(E)] ∈ Z_d(E₁)` along the trivial bundle `E₁ × 𝔸^τ → E₁`
is, through the isomorphism `bundleSpaceIsoPoly`, the resolved-cone cycle
`[C(E)'] ∈ Z_{d + rk τ}(E₁')` of the base-changed obstruction datum. -/
theorem flatPullbackOpen_flatPullbackBundle_resolvedConeCycleAt
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) (d : ℤ) :
    cyclesOfDimension.flatPullbackOpen (bundleSpaceIsoPoly τ I φ).hom
        (VectorBundle.dimension_comap_algEquiv (polyBundleAlgEquiv τ I φ).symm dimEp dimE')
        (cyclesOfDimension.flatPullbackBundle
          (PullbackBaseChange.trivialBundle (ResolvedCone.bundleRing φ) τ) dimE dimEp d
          (resolvedConeCycleAt φ dimE d)) =
      resolvedConeCycleAt (baseChangeHom τ I φ) dimE' (d + (Nat.card τ : ℤ)) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext u
  have hval : (AlgebraicCycle.map (ResolvedCone.toBundle (baseChangeHom τ I φ))
        (coneDimension (baseChangeHom τ I φ) dimE') dimE'
        (ResolvedCone.scheme (baseChangeHom τ I φ)).fundamentalCycle) u =
      AlgebraicCycle.pullbackBundle
        (PullbackBaseChange.trivialBundle (ResolvedCone.bundleRing φ) τ)
        (AlgebraicCycle.map (ResolvedCone.toBundle φ) (coneDimension φ dimE) dimE
          (ResolvedCone.scheme φ).fundamentalCycle)
        ((bundleSpaceIsoPoly τ I φ).hom.base u) := by
    rw [← pullbackOpen_pullbackBundle_map_toBundle τ I φ dimE' dimE]
    exact AlgebraicCycle.pullbackOpen_apply _ _ u
  change AlgebraicCycle.pullbackBundle
      (PullbackBaseChange.trivialBundle (ResolvedCone.bundleRing φ) τ)
      (resolvedConeCycleAt φ dimE d : AlgebraicCycle (ResolvedCone.bundleSpace φ) ℚ)
      ((bundleSpaceIsoPoly τ I φ).hom.base u) =
    (resolvedConeCycleAt (baseChangeHom τ I φ) dimE' (d + (Nat.card τ : ℤ)) :
      AlgebraicCycle (ResolvedCone.bundleSpace (baseChangeHom τ I φ)) ℚ) u
  by_cases hq : (bundleSpaceIsoPoly τ I φ).hom.base u ∈
      Set.range (VectorBundle.bundlePoint
        (PullbackBaseChange.trivialBundle (ResolvedCone.bundleRing φ) τ))
  · obtain ⟨x, hx⟩ := hq
    have hdimu : dimE' u = dimE x + (Nat.card τ : ℤ) := by
      rw [VectorBundle.dimension_comap_algEquiv (polyBundleAlgEquiv τ I φ).symm dimEp dimE' u]
      change dimEp ((bundleSpaceIsoPoly τ I φ).hom.base u) = _
      rw [← hx]
      exact VectorBundle.dimension_bundlePoint _ dimE dimEp x
    rw [← hx, AlgebraicCycle.pullbackBundle_apply_bundlePoint, resolvedConeCycleAt_apply,
      resolvedConeCycleAt_apply, hdimu]
    simp only [add_left_inj]
    by_cases hd : dimE x = d
    · rw [if_pos hd, if_pos hd, hval, ← hx, AlgebraicCycle.pullbackBundle_apply_bundlePoint]
    · rw [if_neg hd, if_neg hd]
  · rw [AlgebraicCycle.pullbackBundle_eq_zero_of_notMem _ _ hq, resolvedConeCycleAt_apply, hval,
      AlgebraicCycle.pullbackBundle_eq_zero_of_notMem _ _ hq, ite_self]

omit [IsNoetherianRing k] [Finite σ] [Finite τ] [Module.Free (MvPolynomial σ k ⧸ I) E.degreeZero]
  [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero] [Finite ι] in
/-- **The cycle-level base-change square for the two bundle pullbacks**: pulling back a cycle
of `X` first to `X' = X × 𝔸^τ` and then to `E₁'` is the same as pulling it back first to `E₁`
and then to `E₁ × 𝔸^τ ≅ E₁'`.  Both composites are the pullback along the bundle `E₁' → X`. -/
theorem pullbackBundle_baseChange_square
    (z : AlgebraicCycle (Spec (CommRingCat.of (MvPolynomial σ k ⧸ I))) ℚ) :
    AlgebraicCycle.pullbackBundle (trivializationBaseChange τ I φ e)
        (AlgebraicCycle.pullbackBundle (R := MvPolynomial σ k ⧸ I) (A := baseExt τ I)
          (baseAlgEquiv τ I) z) =
      AlgebraicCycle.pullbackOpen (bundleSpaceIsoPoly τ I φ).hom
        (AlgebraicCycle.pullbackBundle
          (PullbackBaseChange.trivialBundle (ResolvedCone.bundleRing φ) τ)
          (AlgebraicCycle.pullbackBundle e z)) := by
  rw [← pullbackBundle_tower (R := MvPolynomial σ k ⧸ I) (R' := baseExt τ I)
      (A := ResolvedCone.bundleRing (baseChangeHom τ I φ))
      (totalTrivializationBaseChange τ I φ e) (trivializationBaseChange τ I φ e)
      (baseAlgEquiv τ I) z,
    ← pullbackBundle_tower (R := MvPolynomial σ k ⧸ I) (R' := ResolvedCone.bundleRing φ)
      (A := MvPolynomial τ (ResolvedCone.bundleRing φ))
      (PullbackBaseChange.totalTrivialization τ e)
      (PullbackBaseChange.trivialBundle (ResolvedCone.bundleRing φ) τ) e z]
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  exact (AlgebraicCycle.pullbackBundle_algEquiv (polyBundleAlgEquiv τ I φ).symm
      (PullbackBaseChange.totalTrivialization τ e)
      (totalTrivializationBaseChange τ I φ e) z q).trans
    (AlgebraicCycle.pullbackOpen_apply _ _ q).symm

omit [IsNoetherianRing k] [Finite σ] [Finite τ] [Module.Free (MvPolynomial σ k ⧸ I) E.degreeZero]
  [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero] [Finite ι] in
/-- The two degree shifts `rk ι` and `rk τ` commute. -/
theorem degree_add_swap (i : ℤ) :
    i + (Nat.card ι : ℤ) + (Nat.card τ : ℤ) = i + (Nat.card τ : ℤ) + (Nat.card ι : ℤ) := by
  ring

/-- The Chow-group isomorphism induced by an isomorphism of bundles is induced by the flat
pullback of graded cycles. -/
theorem chowEquivOfAlgEquiv_quotientMap {R A A' : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing A'] [Algebra R A'] (ε : A ≃ₐ[R] A')
    {dA : DimensionFunction (Spec (CommRingCat.of A))}
    {dA' : DimensionFunction (Spec (CommRingCat.of A'))} {j : ℤ}
    (RA : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dA j)
    (RA' : RationalEquivalenceSystem (Spec (CommRingCat.of A')) dA' j)
    (z : cyclesOfDimension (Spec (CommRingCat.of A)) dA j) :
    chowEquivOfAlgEquiv ε RA RA' (RA.quotientMap z) =
      RA'.quotientMap (cyclesOfDimension.flatPullbackOpen
        (Spec.map (CommRingCat.ofHom ε.toRingHom))
        (VectorBundle.dimension_comap_algEquiv ε dA dA') z) := rfl

variable (dimX : DimensionFunction (Spec (CommRingCat.of (MvPolynomial σ k ⧸ I))))
  (dimX' : DimensionFunction (Spec (CommRingCat.of (baseExt τ I))))
  (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) (i : ℤ)
  (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (MvPolynomial σ k ⧸ I))) dimX i)
  (RX' : RationalEquivalenceSystem (Spec (CommRingCat.of (baseExt τ I))) dimX'
    (i + (Nat.card τ : ℤ)))
  (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card ι : ℤ)))
  (RE' : RationalEquivalenceSystem (ResolvedCone.bundleSpace (baseChangeHom τ I φ)) dimE'
    (i + (Nat.card τ : ℤ) + (Nat.card ι : ℤ)))
  (REp : RationalEquivalenceSystem
    (Spec (CommRingCat.of (MvPolynomial τ (ResolvedCone.bundleRing φ)))) dimEp
    (i + (Nat.card ι : ℤ) + (Nat.card τ : ℤ)))
  (RE₂ : RationalEquivalenceSystem (ResolvedCone.bundleSpace (baseChangeHom τ I φ)) dimE'
    (i + (Nat.card ι : ℤ) + (Nat.card τ : ℤ)))

/-- **The Chow-level base-change square for the two bundle pullbacks**, the descent of
`pullbackBundle_baseChange_square` through rational equivalence. -/
theorem chowPullbackBundle_baseChange_square (α : RX.ChowGroup) :
    chowPullbackBundle (trivializationBaseChange τ I φ e) dimX' dimE' (i + (Nat.card τ : ℤ))
        RX' RE' (chowPullbackBundle (R := MvPolynomial σ k ⧸ I) (A := baseExt τ I)
          (baseAlgEquiv τ I) dimX dimX' i RX RX' α) =
      PullbackBaseChange.chowDegreeCongr (degree_add_swap τ (ι := ι) i) RE₂ RE'
        (chowEquivOfAlgEquiv (polyBundleAlgEquiv τ I φ).symm REp RE₂
          (chowPullbackBundle (PullbackBaseChange.trivialBundle (ResolvedCone.bundleRing φ) τ)
            dimE dimEp (i + (Nat.card ι : ℤ)) RE REp
            (chowPullbackBundle e dimX dimE i RX RE α))) := by
  obtain ⟨z, rfl⟩ := RX.relations.mkQ_surjective α
  rw [chowPullbackBundle_quotientMap, chowPullbackBundle_quotientMap,
    chowPullbackBundle_quotientMap, chowPullbackBundle_quotientMap,
    chowEquivOfAlgEquiv_quotientMap, PullbackBaseChange.chowDegreeCongr_quotientMap]
  refine congrArg RE'.quotientMap (Subtype.ext ?_)
  simp only [PullbackBaseChange.cyclesDegreeCongr_coe]
  exact pullbackBundle_baseChange_square τ I φ e z.1

omit [Finite ι] in
/-- The resolved-cone cycle in two equal degrees, transported by `cyclesDegreeCongr`. -/
theorem cyclesDegreeCongr_resolvedConeCycleAt {d d' : ℤ} (h : d = d') :
    PullbackBaseChange.cyclesDegreeCongr h
        (resolvedConeCycleAt (baseChangeHom τ I φ) dimE' d) =
      resolvedConeCycleAt (baseChangeHom τ I φ) dimE' d' := by
  subst h
  exact Subtype.ext (PullbackBaseChange.cyclesDegreeCongr_coe rfl _)

omit [Finite ι] in
/-- **The resolved-cone class is compatible with the base change `X × 𝔸^τ → X`**: the Chow-level
form of `flatPullbackOpen_flatPullbackBundle_resolvedConeCycleAt`. -/
theorem chowDegreeCongr_chowEquivOfAlgEquiv_resolvedConeClassAt :
    PullbackBaseChange.chowDegreeCongr (degree_add_swap τ (ι := ι) i) RE₂ RE'
        (chowEquivOfAlgEquiv (polyBundleAlgEquiv τ I φ).symm REp RE₂
          (chowPullbackBundle (PullbackBaseChange.trivialBundle (ResolvedCone.bundleRing φ) τ)
            dimE dimEp (i + (Nat.card ι : ℤ)) RE REp (resolvedConeClassAt φ dimE i RE))) =
      resolvedConeClassAt (baseChangeHom τ I φ) dimE' (i + (Nat.card τ : ℤ)) RE' := by
  rw [resolvedConeClassAt, chowPullbackBundle_quotientMap, chowEquivOfAlgEquiv_quotientMap,
    PullbackBaseChange.chowDegreeCongr_quotientMap]
  refine congrArg RE'.quotientMap (Eq.trans (congrArg
    (⇑(PullbackBaseChange.cyclesDegreeCongr (degree_add_swap τ (ι := ι) i)))
    (flatPullbackOpen_flatPullbackBundle_resolvedConeCycleAt τ I φ dimE' dimEp dimE
      (i + (Nat.card ι : ℤ)))) ?_)
  exact cyclesDegreeCongr_resolvedConeCycleAt τ I φ dimE' _

/-- **The virtual class is compatible with the base change `X × 𝔸^τ → X`**
(Behrend–Fantechi, Proposition 7.2, for the smooth projection `X × 𝔸^τ → X`, in the affine
model): the virtual class of the base-changed obstruction datum `ψ = baseChangeHom τ I φ`,
computed in the induced trivialisation and in the degree `i + rk τ`, is the flat pullback of the
virtual class of `φ` along the trivial bundle `X' = X × 𝔸^τ → X`. -/
theorem virtualClassAt_baseChangeHom
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (chowPullbackBundle e dimX dimE i RX RE))
    (hhom' : PrincipalDivisorsHomogeneous
      (ResolvedCone.bundleSpace (baseChangeHom τ I φ)) dimE')
    (hinj' : Function.Injective (chowPullbackBundle (trivializationBaseChange τ I φ e)
      dimX' dimE' (i + (Nat.card τ : ℤ)) RX' RE')) :
    virtualClassAt (baseChangeHom τ I φ) (trivializationBaseChange τ I φ e) dimX' dimE'
        (i + (Nat.card τ : ℤ)) RX' RE' hhom' hinj' =
      chowPullbackBundle (R := MvPolynomial σ k ⧸ I) (A := baseExt τ I) (baseAlgEquiv τ I)
        dimX dimX' i RX RX' (virtualClassAt φ e dimX dimE i RX RE hhom hinj) := by
  have dimEq : DimensionFunction
      (Spec (CommRingCat.of (MvPolynomial τ (ResolvedCone.bundleRing φ)))) :=
    DimensionFunction.comapClosedImmersion (bundleSpaceIsoPoly τ I φ).inv dimE'
  apply hinj'
  rw [chowPullbackBundle_virtualClassAt,
    chowPullbackBundle_baseChange_square (dimEp := dimEq)
      (REp := RationalEquivalenceSystem.canonical)
      (RE₂ := RationalEquivalenceSystem.canonical),
    chowPullbackBundle_virtualClassAt]
  exact (chowDegreeCongr_chowEquivOfAlgEquiv_resolvedConeClassAt (τ := τ) (I := I) (φ := φ)
    (dimE' := dimE') (dimEp := dimEq) (dimE := dimE) (i := i) (RE := RE) (RE' := RE')
    (REp := RationalEquivalenceSystem.canonical)
    (RE₂ := RationalEquivalenceSystem.canonical)).symm

/-- **The relative form of `virtualClassAt_baseChangeHom`**: in the canonical degree
`virtualDimension ψ` the left-hand side is the relative virtual class of `ψ` in relative
dimension `Nat.card τ` in the sense of `DegreeOneSummand.relativeVirtualClassAt`.  By
`virtualDimension_baseChangeHom` the degree `virtualDimension ψ` is `virtualDimension φ`, so the
right-hand side is the flat pullback of the virtual class of `φ` in its own canonical degree. -/
theorem relativeVirtualClassAt_baseChangeHom
    (RXv : RationalEquivalenceSystem (Spec (CommRingCat.of (MvPolynomial σ k ⧸ I))) dimX
      (virtualDimension (baseChangeHom τ I φ)))
    (RXv' : RationalEquivalenceSystem (Spec (CommRingCat.of (baseExt τ I))) dimX'
      (virtualDimension (baseChangeHom τ I φ) + (Nat.card τ : ℤ)))
    (REv : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
      (virtualDimension (baseChangeHom τ I φ) + (Nat.card ι : ℤ)))
    (REv' : RationalEquivalenceSystem (ResolvedCone.bundleSpace (baseChangeHom τ I φ)) dimE'
      (virtualDimension (baseChangeHom τ I φ) + (Nat.card τ : ℤ) + (Nat.card ι : ℤ)))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (chowPullbackBundle e dimX dimE
      (virtualDimension (baseChangeHom τ I φ)) RXv REv))
    (hhom' : PrincipalDivisorsHomogeneous
      (ResolvedCone.bundleSpace (baseChangeHom τ I φ)) dimE')
    (hinj' : Function.Injective (chowPullbackBundle (trivializationBaseChange τ I φ e)
      dimX' dimE' (virtualDimension (baseChangeHom τ I φ) + (Nat.card τ : ℤ)) RXv' REv')) :
    DegreeOneSummand.relativeVirtualClassAt (baseChangeHom τ I φ)
        (trivializationBaseChange τ I φ e) dimX' dimE' (Nat.card τ) RXv' REv' hhom' hinj' =
      chowPullbackBundle (R := MvPolynomial σ k ⧸ I) (A := baseExt τ I) (baseAlgEquiv τ I)
        dimX dimX' (virtualDimension (baseChangeHom τ I φ)) RXv RXv'
        (virtualClassAt φ e dimX dimE (virtualDimension (baseChangeHom τ I φ)) RXv REv
          hhom hinj) :=
  virtualClassAt_baseChangeHom τ I φ e dimE' dimX dimX' dimE _ RXv RXv' REv REv'
    hhom hinj hhom' hinj'

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.BaseChangeInvariance
