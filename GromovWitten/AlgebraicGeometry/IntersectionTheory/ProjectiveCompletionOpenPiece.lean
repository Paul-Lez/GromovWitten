/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.GradedVectorBundleExtend
import GromovWitten.AlgebraicGeometry.RelativeSpecAffineHom
import GromovWitten.AlgebraicGeometry.VectorBundleTrivial
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProjectiveBundleSegre
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackGlobalChow

/-!
# The open piece `E ⊂ P(E ⊕ 1)` and the tower `E ⊕ 1 → E → X`

Let `𝓔 : GradedBundleData X ι` be a graded vector bundle with total space `E`, projective
completion `P = P(E ⊕ 1)` and charts `𝓔.completionCharts` of `q : P → X`.

* **The open piece.**  The open embedding `𝓔.bundleOpenEmbedding : E ⟶ P` sends the generic
  point of the fibre of `E` over `x` to the generic point of the fibre of `P` over `x`, and the
  restriction to `E` of the charted flat pullback `q^*` along `P → X` is the flat pullback `p^*`
  along `E → X`, on rational Chow groups.  Since the localisation sequence is stated for the
  inclusion `V.ι` of an open subscheme `V`, the same compatibility is also given for
  `V := 𝓔.bundleOpenEmbedding.opensRange`, transported along `E ≅ V`.
* **The tower.**  The projection `π := 𝓔.extendProj : F := E ⊕ 1 ⟶ E` has affine charts
  `extendCharts 𝓔 : AffineCharts π PUnit` (the pieces of `F` over the affine opens
  `E|_{U_j}` of `E`, `U_j` the trivialising opens of `𝓔`).  The flat pullback along `F → X` is
  the composite of the flat pullback along `E → X` and the charted pullback along `π`.

## Main results

* `bundleOpenEmbedding_bundlePoint`: `E → P` maps the generic fibre point of `E` over `x` to the
  generic fibre point `fibrePoint 𝓔.completionCharts x` of `P`.
* `pullbackOpen_opensRange_pullbackCharted`: cycle-level restriction of `q^*` to the open
  subscheme `V = range (E → P)` (the restriction to `E` itself is the existing
  `GradedBundleData.pullbackOpen_bundleOpenEmbedding_pullbackCharted`).
* `openImmersionPullback_bundleOpenEmbedding_chowPullbackCharted`: on rational Chow groups,
  restriction along `E → P` after `q^*` is `p^*` (`chowPullbackBundleGlobal`), for arbitrary
  dimension functions and rational-equivalence systems.
* `openImmersionPullback_opensRange_chowPullbackCharted` and
  `openImmersionPullback_opensRange_chowPullbackCharted_eq_zero`: the same along `V.ι`
  (transported along `V ≅ E`), and the vanishing of the restriction of `q^* α` to `V` when
  `p^* α = 0`; `openImmersionPullback_opensRange_chowPullbackCharted_eq_zero_finiteType` is the
  latter for the canonical dimension functions over a field.
* `affineι_eq_gammaHom_fromSpec`: the affine chart of a relative `Spec` over `U` is
  `Spec Γ(toBase ⁻¹ U) ⟶ Spec_X 𝒜` up to `RelativeSpec.gammaHom`.
* `extendCharts : AffineCharts 𝓔.extendProj PUnit`, with `fibrePoint_extendCharts_bundlePoint`
  (generic fibre points in the tower) and `dimensionFunction_fibrePoint_extendCharts` (the
  dimension shift along `π` for the canonical dimension functions over a field).
* `pullbackCharted_extendCharts_pullbackBundle`: `π^* ∘ p_E^* = p_F^*` on cycles.
* `chowPullbackBundleGlobal_extend`: `p_F^* = π^* ∘ p_E^*` on rational Chow groups (up to the
  degree cast `i + r + 1 = i + (r + 1)`), and `chowPullbackBundleGlobal_extend_eq_zero_of_eq_zero`
  (with the `_finiteType` version for the canonical dimension functions over a field).
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)
open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
open RationalEquivalenceSystem.DescendingMap ChartedOverSubscheme FiniteTypeDimension

/-! ## The open piece `E ⊂ P(E ⊕ 1)` -/

section OpenPiece

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : GradedBundleData X ι)

/-- The open embedding `E ⟶ P(E ⊕ 1)` maps the generic point of the fibre of `E` over `x` to
the generic point of the fibre of `P(E ⊕ 1)` over `x`. -/
theorem bundleOpenEmbedding_bundlePoint (x : X) :
    𝓔.bundleOpenEmbedding.base (BundlePullbackGlobal.bundlePoint 𝓔.bundle x) =
      AffineCharts.fibrePoint 𝓔.completionCharts x :=
  (𝓔.fibrePoint_completionCharts x).symm

/-- The open embedding `E ⟶ P(E ⊕ 1)` followed by the inverse of its corestriction to its range
`V` is the inclusion `V.ι` of the range. -/
theorem bundleOpenEmbedding_isoOpensRange_inv_base (v : 𝓔.bundleOpenEmbedding.opensRange) :
    𝓔.bundleOpenEmbedding.base (𝓔.bundleOpenEmbedding.isoOpensRange.inv.base v) =
      𝓔.bundleOpenEmbedding.opensRange.ι.base v := by
  rw [← Scheme.Hom.isoOpensRange_inv_comp 𝓔.bundleOpenEmbedding]
  rfl

/-- Cycle level, in the form used by the localisation sequence: the restriction of the charted
flat pullback along `P(E ⊕ 1) → X` to the open subscheme `V = range (E → P(E ⊕ 1))` is the
flat pullback along `E → X`, transported to `V` along `V ≅ E`. -/
theorem pullbackOpen_opensRange_pullbackCharted (c : AlgebraicCycle X ℚ) :
    AlgebraicCycle.pullbackOpen 𝓔.bundleOpenEmbedding.opensRange.ι
        (AffineCharts.pullbackCharted 𝓔.completionCharts c) =
      AlgebraicCycle.pullbackOpen 𝓔.bundleOpenEmbedding.isoOpensRange.inv
        (BundlePullbackGlobal.pullbackBundle 𝓔.bundle c) := by
  rw [← GradedBundleData.pullbackOpen_bundleOpenEmbedding_pullbackCharted]
  apply Function.locallyFinsuppWithin.coe_injective
  funext v
  change AffineCharts.pullbackCharted 𝓔.completionCharts c
      (𝓔.bundleOpenEmbedding.opensRange.ι.base v) =
    AffineCharts.pullbackCharted 𝓔.completionCharts c
      (𝓔.bundleOpenEmbedding.base (𝓔.bundleOpenEmbedding.isoOpensRange.inv.base v))
  exact congrArg _ (bundleOpenEmbedding_isoOpensRange_inv_base 𝓔 v).symm

variable [Finite ι] (dimX : DimensionFunction X)
  (dimP : DimensionFunction 𝓔.projectiveCompletion)
  (dimE : DimensionFunction 𝓔.bundle.totalSpace)
  (hshift : ∀ x, dimP (AffineCharts.fibrePoint 𝓔.completionCharts x) =
    dimX x + (Nat.card ι : ℤ))
  (hE : ∀ x, dimE (BundlePullbackGlobal.bundlePoint 𝓔.bundle x) = dimX x + (Nat.card ι : ℤ))
  (i : ℤ) (RX : RationalEquivalenceSystem X dimX i)
  (RP : RationalEquivalenceSystem 𝓔.projectiveCompletion dimP (i + (Nat.card ι : ℤ)))
  (RE : RationalEquivalenceSystem 𝓔.bundle.totalSpace dimE (i + (Nat.card ι : ℤ)))

/-- **Restriction of `q^*` to the open piece.**  On rational Chow groups, the charted flat
pullback `A_i(X) → A_{i+r}(P(E ⊕ 1))` followed by the restriction to the open subscheme
`E ⊂ P(E ⊕ 1)` is the flat pullback `A_i(X) → A_{i+r}(E)` along the bundle.  The dimension
functions are arbitrary, subject to the compatibility `hdim` along `E → P(E ⊕ 1)`. -/
theorem openImmersionPullback_bundleOpenEmbedding_chowPullbackCharted
    (hdim : ∀ e, dimE e = dimP (𝓔.bundleOpenEmbedding.base e)) (α : RX.ChowGroup) :
    openImmersionPullback RP 𝓔.bundleOpenEmbedding hdim RE
        (chowPullbackCharted 𝓔.completionCharts dimX dimP hshift i RX RP α) =
      BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.bundle dimX dimE hE i RX RE α := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ α
  refine congrArg RE.quotientMap (Subtype.ext ?_)
  exact GradedBundleData.pullbackOpen_bundleOpenEmbedding_pullbackCharted 𝓔 z.1

/-- **Restriction of `q^*` to the open piece, in the form of the localisation sequence.**  With
`V := range (E → P(E ⊕ 1))`, the restriction along `V.ι` of the charted flat pullback is the flat
pullback along `E → X` transported along the isomorphism `V ≅ E`. -/
theorem openImmersionPullback_opensRange_chowPullbackCharted
    {dimV : DimensionFunction 𝓔.bundleOpenEmbedding.opensRange.toScheme}
    (hV : ∀ v, dimV v = dimP (𝓔.bundleOpenEmbedding.opensRange.ι.base v))
    (hVE : ∀ v, dimV v = dimE (𝓔.bundleOpenEmbedding.isoOpensRange.inv.base v))
    (RV : RationalEquivalenceSystem 𝓔.bundleOpenEmbedding.opensRange.toScheme dimV
      (i + (Nat.card ι : ℤ))) (α : RX.ChowGroup) :
    openImmersionPullback RP 𝓔.bundleOpenEmbedding.opensRange.ι hV RV
        (chowPullbackCharted 𝓔.completionCharts dimX dimP hshift i RX RP α) =
      openImmersionPullback RE 𝓔.bundleOpenEmbedding.isoOpensRange.inv hVE RV
        (BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.bundle dimX dimE hE i RX RE α) := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ α
  refine congrArg RV.quotientMap (Subtype.ext ?_)
  exact pullbackOpen_opensRange_pullbackCharted 𝓔 z.1

/-- If the flat pullback of `α` along `E → X` vanishes, then so does the restriction of the
charted flat pullback `q^* α` to the open subscheme `V = range (E → P(E ⊕ 1))`. -/
theorem openImmersionPullback_opensRange_chowPullbackCharted_eq_zero
    {dimV : DimensionFunction 𝓔.bundleOpenEmbedding.opensRange.toScheme}
    (hV : ∀ v, dimV v = dimP (𝓔.bundleOpenEmbedding.opensRange.ι.base v))
    (hVE : ∀ v, dimV v = dimE (𝓔.bundleOpenEmbedding.isoOpensRange.inv.base v))
    (RV : RationalEquivalenceSystem 𝓔.bundleOpenEmbedding.opensRange.toScheme dimV
      (i + (Nat.card ι : ℤ))) (α : RX.ChowGroup)
    (h : BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.bundle dimX dimE hE i RX RE α = 0) :
    openImmersionPullback RP 𝓔.bundleOpenEmbedding.opensRange.ι hV RV
        (chowPullbackCharted 𝓔.completionCharts dimX dimP hshift i RX RP α) = 0 := by
  rw [openImmersionPullback_opensRange_chowPullbackCharted 𝓔 dimX dimP dimE hshift hE i RX RP
    RE hV hVE RV α, h, map_zero]

end OpenPiece

/-! ## The open piece with the canonical dimension functions -/

section OpenPieceFiniteType

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] {ι : Type u} [Finite ι] (𝓔 : GradedBundleData X ι)

/-- The canonical dimension function of `E` is the restriction of that of `P(E ⊕ 1)`. -/
theorem dimensionFunction_bundleOpenEmbedding (e : 𝓔.bundle.totalSpace) :
    dimensionFunction (𝓔.bundle.proj ≫ f) e =
      dimensionFunction (𝓔.completionToBase ≫ f) (𝓔.bundleOpenEmbedding.base e) := by
  rw [← dimensionFunction_comp (𝓔.completionToBase ≫ f) 𝓔.bundleOpenEmbedding]
  exact GradedBundleData.dimensionFunction_congr_hom
    (g := 𝓔.bundle.proj ≫ f) (g' := 𝓔.bundleOpenEmbedding ≫ 𝓔.completionToBase ≫ f)
    (by rw [← Category.assoc, GradedBundleData.bundleOpenEmbedding_toBase]) e

omit [Finite ι] in
/-- The canonical dimension function of `V = range (E → P(E ⊕ 1))` is the restriction of that of
`P(E ⊕ 1)`. -/
theorem dimensionFunction_opensRange_bundleOpenEmbedding
    (v : 𝓔.bundleOpenEmbedding.opensRange.toScheme) :
    dimensionFunction (𝓔.bundleOpenEmbedding.opensRange.ι ≫ 𝓔.completionToBase ≫ f) v =
      dimensionFunction (𝓔.completionToBase ≫ f) (𝓔.bundleOpenEmbedding.opensRange.ι.base v) :=
  dimensionFunction_comp _ _ v

/-- The canonical dimension function of `V = range (E → P(E ⊕ 1))` corresponds to that of `E`
under `V ≅ E`. -/
theorem dimensionFunction_opensRange_isoOpensRange_inv
    (v : 𝓔.bundleOpenEmbedding.opensRange.toScheme) :
    dimensionFunction (𝓔.bundleOpenEmbedding.opensRange.ι ≫ 𝓔.completionToBase ≫ f) v =
      dimensionFunction (𝓔.bundle.proj ≫ f) (𝓔.bundleOpenEmbedding.isoOpensRange.inv.base v) := by
  rw [dimensionFunction_opensRange_bundleOpenEmbedding, dimensionFunction_bundleOpenEmbedding]
  exact congrArg _ (bundleOpenEmbedding_isoOpensRange_inv_base 𝓔 v).symm

/-- **The open piece over a field.**  With the canonical dimension functions and Chow groups, if
`p^* α = 0` on `E` then the restriction of `q^* α` to `V = range (E → P(E ⊕ 1))` vanishes.  This
is the input of the localisation sequence along `V.ι`. -/
theorem openImmersionPullback_opensRange_chowPullbackCharted_eq_zero_finiteType (i : ℤ)
    (α : (chowSystem (dimensionFunction f) i).ChowGroup)
    (h : BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.bundle (dimensionFunction f)
      (dimensionFunction (𝓔.bundle.proj ≫ f)) (dimensionFunction_bundlePoint f 𝓔.bundle) i
      (chowSystem (dimensionFunction f) i)
      (chowSystem (dimensionFunction (𝓔.bundle.proj ≫ f)) (i + (Nat.card ι : ℤ))) α = 0) :
    openImmersionPullback (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f))
        (i + (Nat.card ι : ℤ))) 𝓔.bundleOpenEmbedding.opensRange.ι
        (dimensionFunction_opensRange_bundleOpenEmbedding f 𝓔)
        (chowSystem (dimensionFunction
          (𝓔.bundleOpenEmbedding.opensRange.ι ≫ 𝓔.completionToBase ≫ f))
          (i + (Nat.card ι : ℤ)))
        (chowPullbackCharted 𝓔.completionCharts (dimensionFunction f)
          (dimensionFunction (𝓔.completionToBase ≫ f))
          (𝓔.dimensionFunction_fibrePoint_completionCharts f) i
          (chowSystem (dimensionFunction f) i)
          (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) (i + (Nat.card ι : ℤ))) α) =
      0 :=
  openImmersionPullback_opensRange_chowPullbackCharted_eq_zero 𝓔 _ _ _ _
    (dimensionFunction_bundlePoint f 𝓔.bundle) i _ _ _ _
    (dimensionFunction_opensRange_isoOpensRange_inv f 𝓔) _ α h

end OpenPieceFiniteType

/-! ## Sections of a relative `Spec` over an affine open -/

section Gamma

variable {X : Scheme.{u}} (𝒜 : AlgebraData X) (U : X.affineOpens)

/-- The affine chart `Spec (𝒜.ring U) ⟶ Spec_X 𝒜` over an affine open `U` of `X` is the canonical
morphism `Spec Γ(W) ⟶ Spec_X 𝒜` of the affine open `W = toBase ⁻¹ U`, precomposed with the
identification `𝒜.ring U ≅ Γ(W)` (`RelativeSpec.gammaHom`). -/
theorem affineι_eq_gammaHom_fromSpec
    (hW : IsAffineOpen (RelativeSpec.toBase X 𝒜 ⁻¹ᵁ U.1)) :
    RelativeSpec.affineι X 𝒜 U = Spec.map (RelativeSpec.gammaHom X 𝒜 U) ≫ hW.fromSpec := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (RelativeSpec.affineι X 𝒜 U) hW
    (isAffineOpen_top _) (RelativeSpec.affineι_preimage_toBase_preimage X 𝒜 U).ge
  rw [IsAffineOpen.fromSpec_top, Iso.eq_inv_comp, Scheme.isoSpec_Spec_hom] at h
  rw [← h, RelativeSpec.gammaHom, Spec.map_comp, Category.assoc]

end Gamma

/-! ## The tower `E ⊕ 1 → E → X` -/

section Tower

/- The total space of `𝓔.extend` is, by definition but not reducibly, the relative `Spec` of the
polynomial extension `𝒜[t]`, and `𝒜[t].ring U` is, by definition but not reducibly,
`Polynomial (𝒜.ring U)`; as in `BundleHomotopyInjectiveGlobal.lean`, the unifier is told not to
respect transparency in this section. -/
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : GradedBundleData X ι)

/-- The affine open `E|_{U_j}` of the total space `E` lying over the `j`-th trivialising open
`U_j` of the bundle. -/
noncomputable abbrev extendChartBase (j : 𝓔.bundle.J) : 𝓔.bundle.totalSpace.affineOpens :=
  ⟨RelativeSpec.toBase X 𝓔.bundle.algebra ⁻¹ᵁ (𝓔.bundle.chart j).1,
    (𝓔.bundle.chart j).2.preimage _⟩

/-- The coordinate ring of `E ⊕ 1` over `U_j`, `(𝒜 U_j)[t]`, is the polynomial ring in one
variable over the sections of `E` over `E|_{U_j}`. -/
noncomputable def extendChartEquiv (j : 𝓔.bundle.J) :
    𝓔.bundle.algebra.polynomial.ring (𝓔.bundle.chart j) ≃+*
      MvPolynomial PUnit.{u + 1} Γ(𝓔.bundle.totalSpace, (extendChartBase 𝓔 j).1) :=
  (Polynomial.mapEquiv (RelativeSpec.ringEquivGamma X 𝓔.bundle.algebra (𝓔.bundle.chart j))).trans
    (MvPolynomial.uniqueAlgEquiv (R := Γ(𝓔.bundle.totalSpace, (extendChartBase 𝓔 j).1))
      PUnit.{u + 1}).symm.toRingEquiv

/-- `extendChartEquiv` sends a constant to the constant given by `ringEquivGamma`. -/
theorem extendChartEquiv_C (j : 𝓔.bundle.J) (a : 𝓔.bundle.algebra.ring (𝓔.bundle.chart j)) :
    extendChartEquiv 𝓔 j (Polynomial.C a) =
      MvPolynomial.C (RelativeSpec.ringEquivGamma X 𝓔.bundle.algebra (𝓔.bundle.chart j) a) := by
  change (MvPolynomial.uniqueAlgEquiv (R := Γ(𝓔.bundle.totalSpace, (extendChartBase 𝓔 j).1))
      PUnit.{u + 1}).symm (Polynomial.map
        (RelativeSpec.ringEquivGamma X 𝓔.bundle.algebra (𝓔.bundle.chart j) : _ →+* _)
        (Polynomial.C a)) = _
  rw [Polynomial.map_C]
  change (MvPolynomial.uniqueAlgEquiv _ PUnit.{u + 1}).symm
    (algebraMap _ (Polynomial _) _) = _
  rw [AlgEquiv.commutes]
  rfl

/-- The chart of `E ⊕ 1` over `E|_{U_j}`: the affine line over `E|_{U_j}`. -/
noncomputable def extendChartι (j : 𝓔.bundle.J) :
    Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1}
      Γ(𝓔.bundle.totalSpace, (extendChartBase 𝓔 j).1))) ⟶ 𝓔.extend.bundle.totalSpace :=
  Spec.map (CommRingCat.ofHom (extendChartEquiv 𝓔 j).toRingHom) ≫
    RelativeSpec.affineι X 𝓔.bundle.algebra.polynomial (𝓔.bundle.chart j)

/-- The affine chart of `E ⊕ 1 = Spec_X (𝒜[t])` over `U_j` is an open immersion (stated with the
codomain written as the total space of `𝓔.extend`). -/
theorem isOpenImmersion_affineι_extend (j : 𝓔.bundle.J) :
    IsOpenImmersion (RelativeSpec.affineι X 𝓔.bundle.algebra.polynomial (𝓔.bundle.chart j) :
      _ ⟶ 𝓔.extend.bundle.totalSpace) :=
  RelativeSpec.affineι_isOpenImmersion _ _ _

/-- The chart `extendChartι j` of `E ⊕ 1` is an open immersion. -/
instance isOpenImmersion_extendChartι (j : 𝓔.bundle.J) : IsOpenImmersion (extendChartι 𝓔 j) := by
  have : IsIso (CommRingCat.ofHom (extendChartEquiv 𝓔 j).toRingHom) :=
    (extendChartEquiv 𝓔 j).toCommRingCatIso.isIso_hom
  have := isOpenImmersion_affineι_extend 𝓔 j
  unfold extendChartι
  infer_instance

/-- The chart `extendChartι j` of `E ⊕ 1` is the preimage of `U_j`. -/
theorem opensRange_extendChartι (j : 𝓔.bundle.J) :
    (extendChartι 𝓔 j).opensRange = 𝓔.extend.bundle.proj ⁻¹ᵁ (𝓔.bundle.chart j).1 := by
  have : IsIso (CommRingCat.ofHom (extendChartEquiv 𝓔 j).toRingHom) :=
    (extendChartEquiv 𝓔 j).toCommRingCatIso.isIso_hom
  have := isOpenImmersion_affineι_extend 𝓔 j
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (opensRange_affineι X 𝓔.bundle.algebra.polynomial (𝓔.bundle.chart j))

/-- A point of `E ⊕ 1` lies in the chart `extendChartι j` iff its image in `E` lies in
`E|_{U_j}`. -/
theorem mem_range_extendChartι_iff (j : 𝓔.bundle.J) (p : 𝓔.extend.bundle.totalSpace) :
    p ∈ Set.range (extendChartι 𝓔 j).base ↔
      𝓔.extendProj.base p ∈ (extendChartBase 𝓔 j).1 := by
  have h : p ∈ (extendChartι 𝓔 j).opensRange ↔
      p ∈ 𝓔.extend.bundle.proj ⁻¹ᵁ (𝓔.bundle.chart j).1 := by
    rw [opensRange_extendChartι]
  refine h.trans ?_
  change 𝓔.extend.bundle.proj.base p ∈ (𝓔.bundle.chart j).1 ↔
    𝓔.bundle.proj.base (𝓔.extendProj.base p) ∈ (𝓔.bundle.chart j).1
  rw [← GradedBundleData.extendProj_proj]
  rfl

/-- The projection `E ⊕ 1 → E` is surjective on points. -/
theorem extendProj_surjective : Function.Surjective 𝓔.extendProj.base := by
  intro e
  obtain ⟨j, he⟩ : ∃ j, e ∈ RelativeSpec.toBase X 𝓔.bundle.algebra ⁻¹ᵁ (𝓔.bundle.chart j).1 :=
    ⟨_, BundlePullbackGlobal.mem_chart_chartIndex 𝓔.bundle (𝓔.bundle.proj.base e)⟩
  rw [← opensRange_affineι] at he
  obtain ⟨y, rfl⟩ := he
  refine ⟨(RelativeSpec.affineι X 𝓔.bundle.algebra.polynomial (𝓔.bundle.chart j)).base
    ((Spec.map (CommRingCat.ofHom (R := 𝓔.bundle.algebra.polynomial.ring (𝓔.bundle.chart j))
      (Polynomial.evalRingHom 0))).base y), ?_⟩
  have h1 := 𝓔.bundle.algebra.polynomialProjection_affineι (𝓔.bundle.chart j)
  have h2 : (Spec.map (CommRingCat.ofHom
      (R := 𝓔.bundle.algebra.polynomial.ring (𝓔.bundle.chart j)) (Polynomial.evalRingHom 0))) ≫
      Spec.map (CommRingCat.ofHom (S := 𝓔.bundle.algebra.polynomial.ring (𝓔.bundle.chart j))
        Polynomial.C) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
    exact Polynomial.eval_C
  have h3 : (Spec.map (CommRingCat.ofHom
      (R := 𝓔.bundle.algebra.polynomial.ring (𝓔.bundle.chart j)) (Polynomial.evalRingHom 0))) ≫
      RelativeSpec.affineι X 𝓔.bundle.algebra.polynomial (𝓔.bundle.chart j) ≫
        𝓔.bundle.algebra.polynomialProjection =
      RelativeSpec.affineι X 𝓔.bundle.algebra (𝓔.bundle.chart j) := by
    rw [h1, ← Category.assoc, h2, Category.id_comp]
  exact congrArg (fun g ↦ g.base y) h3

/-- **The affine charts of the tower `E ⊕ 1 → E`.**  Over the affine open `E|_{U_j}` of `E`
(`U_j` a trivialising open of the bundle), `E ⊕ 1` is the affine line
`Spec Γ(E|_{U_j})[t]`. -/
noncomputable def extendCharts : AffineCharts 𝓔.extendProj PUnit.{u + 1} where
  J := 𝓔.bundle.J
  base := extendChartBase 𝓔
  iSup_base := by
    change ⨆ j, 𝓔.bundle.proj ⁻¹ᵁ (𝓔.bundle.chart j).1 = ⊤
    exact 𝓔.bundle.proj.iSup_preimage_eq_top 𝓔.bundle.iSup_chart
  chartι := extendChartι 𝓔
  chartι_comp j := by
    rw [extendChartι, Category.assoc]
    change Spec.map _ ≫ (RelativeSpec.affineι X 𝓔.bundle.algebra.polynomial (𝓔.bundle.chart j) ≫
      𝓔.bundle.algebra.polynomialProjection) = _
    rw [𝓔.bundle.algebra.polynomialProjection_affineι,
      affineι_eq_gammaHom_fromSpec _ _ (extendChartBase 𝓔 j).2, IsAffineOpen.fromSpec,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
    change extendChartEquiv 𝓔 j (Polynomial.C (RelativeSpec.gammaHom X 𝓔.bundle.algebra
      (𝓔.bundle.chart j) a)) = MvPolynomial.C a
    rw [extendChartEquiv_C, RelativeSpec.ringEquivGamma_gammaHom]
  exists_mem_range p := by
    refine ⟨BundlePullbackGlobal.chartIndex 𝓔.bundle (𝓔.bundle.proj.base (𝓔.extendProj.base p)),
      (mem_range_extendChartι_iff 𝓔 _ p).2 ?_⟩
    exact BundlePullbackGlobal.mem_chart_chartIndex 𝓔.bundle _
  meets j j' e he he' := by
    obtain ⟨p, rfl⟩ := extendProj_surjective 𝓔 e
    exact ⟨p, rfl, (mem_range_extendChartι_iff 𝓔 j p).2 he,
      (mem_range_extendChartι_iff 𝓔 j' p).2 he'⟩

/-- The generic point of the fibre of `E ⊕ 1 → E` over the generic point of the fibre of
`E → X` over `x` is the generic point of the fibre of `E ⊕ 1 → X` over `x`. -/
theorem fibrePoint_extendCharts_bundlePoint (x : X) :
    AffineCharts.fibrePoint (extendCharts 𝓔) (BundlePullbackGlobal.bundlePoint 𝓔.bundle x) =
      BundlePullbackGlobal.bundlePoint 𝓔.extend.bundle x := by
  have hproj : ∀ p : 𝓔.extend.bundle.totalSpace,
      𝓔.extend.bundle.proj.base p = 𝓔.bundle.proj.base (𝓔.extendProj.base p) := fun p ↦
    (congrArg (fun g : 𝓔.extend.bundle.totalSpace ⟶ X ↦ g.base p) 𝓔.extendProj_proj).symm
  set e := BundlePullbackGlobal.bundlePoint 𝓔.bundle x
  set b := BundlePullbackGlobal.bundlePoint 𝓔.extend.bundle x
  have h₁ : b ⤳ AffineCharts.fibrePoint (extendCharts 𝓔) e :=
    VectorBundleTotalSpace.bundlePoint_specializes 𝓔.extend.bundle x _ (by
      rw [hproj, AffineCharts.q_fibrePoint, BundlePullbackGlobal.proj_bundlePoint])
  have h₂ : AffineCharts.fibrePoint (extendCharts 𝓔) e ⤳ b := by
    refine AffineCharts.fibrePoint_specializes (extendCharts 𝓔) ?_
    exact VectorBundleTotalSpace.bundlePoint_specializes 𝓔.bundle x _ (by
      rw [← hproj, BundlePullbackGlobal.proj_bundlePoint])
  exact (h₂.antisymm h₁).eq

/-- **The tower on cycles.**  The charted flat pullback along `E ⊕ 1 → E` of the flat pullback
along `E → X` is the flat pullback along `E ⊕ 1 → X`. -/
theorem pullbackCharted_extendCharts_pullbackBundle (w : AlgebraicCycle X ℚ) :
    AffineCharts.pullbackCharted (extendCharts 𝓔)
        (BundlePullbackGlobal.pullbackBundle 𝓔.bundle w) =
      BundlePullbackGlobal.pullbackBundle 𝓔.extend.bundle w := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext p
  change AffineCharts.pullbackCharted (extendCharts 𝓔)
      (BundlePullbackGlobal.pullbackBundle 𝓔.bundle w) p =
    BundlePullbackGlobal.pullbackBundle 𝓔.extend.bundle w p
  by_cases hp : p ∈ Set.range (BundlePullbackGlobal.bundlePoint 𝓔.extend.bundle)
  · obtain ⟨x, rfl⟩ := hp
    rw [← fibrePoint_extendCharts_bundlePoint, AffineCharts.pullbackCharted_apply_fibrePoint,
      BundlePullbackGlobal.pullbackBundle_apply_bundlePoint, fibrePoint_extendCharts_bundlePoint,
      BundlePullbackGlobal.pullbackBundle_apply_bundlePoint]
  · rw [BundlePullbackGlobal.pullbackBundle_eq_zero_of_notMem _ _ hp]
    by_cases hp' : p ∈ Set.range (AffineCharts.fibrePoint (extendCharts 𝓔))
    · obtain ⟨e, rfl⟩ := hp'
      rw [AffineCharts.pullbackCharted_apply_fibrePoint]
      refine BundlePullbackGlobal.pullbackBundle_eq_zero_of_notMem _ _ ?_
      rintro ⟨x, rfl⟩
      exact hp ⟨x, (fibrePoint_extendCharts_bundlePoint 𝓔 x).symm⟩
    · exact AffineCharts.pullbackCharted_eq_zero_of_notMem _ _ hp'

/-- **The dimension shift along `E ⊕ 1 → E`** for the canonical dimension functions over a field:
the generic point of the fibre over `e` has dimension `dim e + 1`. -/
theorem dimensionFunction_fibrePoint_extendCharts {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [Finite ι]
    (e : 𝓔.bundle.totalSpace) :
    dimensionFunction (𝓔.extend.bundle.proj ≫ f) (AffineCharts.fibrePoint (extendCharts 𝓔) e) =
      dimensionFunction (𝓔.bundle.proj ≫ f) e + (Nat.card PUnit.{u + 1} : ℤ) := by
  set j := BundlePullbackGlobal.chartIndex 𝓔.bundle (𝓔.bundle.proj.base e)
  have hj : e ∈ ((extendCharts 𝓔).base j).1 :=
    BundlePullbackGlobal.mem_chart_chartIndex 𝓔.bundle _
  have _ := isNoetherianRing_sections (𝓔.bundle.proj ≫ f) ((extendCharts 𝓔).base j).1
    ((extendCharts 𝓔).base j).2
  exact AffineCharts.dimension_fibrePoint_chart (extendCharts 𝓔) j
    (dimensionFunction (𝓔.bundle.proj ≫ f)) (dimensionFunction (𝓔.extend.bundle.proj ≫ f))
    (dimensionFunction (((isAffineOpen _ ((extendCharts 𝓔).base j)).isoSpec.inv ≫
      ((extendCharts 𝓔).base j).1.ι) ≫ 𝓔.bundle.proj ≫ f))
    (dimensionFunction ((extendCharts 𝓔).chartι j ≫ 𝓔.extend.bundle.proj ≫ f))
    (fun y ↦ dimensionFunction_comp _ _ y) (fun q ↦ dimensionFunction_comp _ _ q) ⟨e, hj⟩

variable [Finite ι] (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.bundle.totalSpace)
  (dimF : DimensionFunction 𝓔.extend.bundle.totalSpace)
  (hE : ∀ x, dimE (BundlePullbackGlobal.bundlePoint 𝓔.bundle x) = dimX x + (Nat.card ι : ℤ))
  (hF : ∀ x, dimF (BundlePullbackGlobal.bundlePoint 𝓔.extend.bundle x) =
    dimX x + (Nat.card (Option ι) : ℤ))
  (hπ : ∀ e, dimF (AffineCharts.fibrePoint (extendCharts 𝓔) e) =
    dimE e + (Nat.card PUnit.{u + 1} : ℤ))
  (i : ℤ)

/-- The degree bookkeeping of the tower: `i + r + 1 = i + (r + 1)`. -/
theorem extendCharts_degree_eq :
    i + (Nat.card ι : ℤ) + (Nat.card PUnit.{u + 1} : ℤ) = i + (Nat.card (Option ι) : ℤ) := by
  rw [Finite.card_option, Nat.card_unique (α := PUnit.{u + 1})]
  push_cast
  ring

/-- **The tower on rational Chow groups.**  The flat pullback `A_i(X) → A_{i+r+1}(E ⊕ 1)` along
`E ⊕ 1 → X` is the charted flat pullback along `E ⊕ 1 → E` after the flat pullback
`A_i(X) → A_{i+r}(E)` along `E → X`, up to the degree cast `i + r + 1 = i + (r + 1)`. -/
theorem chowPullbackBundleGlobal_extend (α : (chowSystem dimX i).ChowGroup) :
    BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.extend.bundle dimX dimF hF i
        (chowSystem dimX i) (chowSystem dimF (i + (Nat.card (Option ι) : ℤ))) α =
      chowCast (extendCharts_degree_eq (ι := ι) i)
        (chowPullbackCharted (extendCharts 𝓔) dimE dimF hπ (i + (Nat.card ι : ℤ))
          (chowSystem dimE (i + (Nat.card ι : ℤ)))
          (chowSystem dimF (i + (Nat.card ι : ℤ) + (Nat.card PUnit.{u + 1} : ℤ)))
          (BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.bundle dimX dimE hE i
            (chowSystem dimX i) (chowSystem dimE (i + (Nat.card ι : ℤ))) α)) := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ α
  change _ = chowCast (extendCharts_degree_eq (ι := ι) i)
    ((chowSystem dimF _).quotientMap (AffineCharts.flatPullbackCharted (extendCharts 𝓔) dimE
      dimF hπ _ (BundlePullbackGlobal.flatPullbackBundleGlobal 𝓔.bundle dimX dimE hE i z)))
  rw [chowCast_quotientMap]
  refine congrArg (chowSystem dimF _).quotientMap (Subtype.ext ?_)
  exact (pullbackCharted_extendCharts_pullbackBundle 𝓔 z.1).symm

include hπ in
/-- If the flat pullback of `α` along `E → X` vanishes, so does its flat pullback along
`E ⊕ 1 → X`. -/
theorem chowPullbackBundleGlobal_extend_eq_zero_of_eq_zero (α : (chowSystem dimX i).ChowGroup)
    (h : BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.bundle dimX dimE hE i
      (chowSystem dimX i) (chowSystem dimE (i + (Nat.card ι : ℤ))) α = 0) :
    BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.extend.bundle dimX dimF hF i
        (chowSystem dimX i) (chowSystem dimF (i + (Nat.card (Option ι) : ℤ))) α = 0 := by
  rw [chowPullbackBundleGlobal_extend 𝓔 dimX dimE dimF hE hF hπ i α, h, map_zero, map_zero]

/-- **The tower over a field**, with the canonical dimension functions and Chow groups: if the
flat pullback of `α` along `E → X` vanishes, so does its flat pullback along `E ⊕ 1 → X`. -/
theorem chowPullbackBundleGlobal_extend_eq_zero_of_eq_zero_finiteType {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (i : ℤ)
    (α : (chowSystem (dimensionFunction f) i).ChowGroup)
    (h : BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.bundle (dimensionFunction f)
      (dimensionFunction (𝓔.bundle.proj ≫ f)) (dimensionFunction_bundlePoint f 𝓔.bundle) i
      (chowSystem (dimensionFunction f) i)
      (chowSystem (dimensionFunction (𝓔.bundle.proj ≫ f)) (i + (Nat.card ι : ℤ))) α = 0) :
    BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.extend.bundle (dimensionFunction f)
        (dimensionFunction (𝓔.extend.bundle.proj ≫ f))
        (dimensionFunction_bundlePoint f 𝓔.extend.bundle) i (chowSystem (dimensionFunction f) i)
        (chowSystem (dimensionFunction (𝓔.extend.bundle.proj ≫ f))
          (i + (Nat.card (Option ι) : ℤ))) α = 0 :=
  chowPullbackBundleGlobal_extend_eq_zero_of_eq_zero 𝓔 _ _ _ _ _
    (dimensionFunction_fibrePoint_extendCharts 𝓔 f) i α h

end Tower

end GromovWitten.AlgebraicGeometry.IntersectionTheory
