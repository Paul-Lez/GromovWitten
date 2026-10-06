/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.GradedVectorBundleExtend
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProjectiveBundleSegre
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FirstChernClassCongr

/-!
# The hyperplane embedding `P(E ⊕ 1) ↪ P((E ⊕ 1) ⊕ 1)`

For a graded vector bundle `𝓔 : GradedBundleData X ι` with projective completion
`P := P(E ⊕ 1)`, the graded bundle `𝓔.extend` (`E ⊕ 1`, of rank `Option ι`) has projective
completion `P' := P((E ⊕ 1) ⊕ 1)`, and the embedding at infinity of `𝓔.extend` is the closed
immersion `j := 𝓔.hyperplaneEmbedding : P ⟶ P'` over `X` (`GradedVectorBundleExtend.lean`).
This file proves the two facts about `j` used in Fulton's proof of Theorem 3.3(a):

* `j` sends the generic fibre point of `P` over `x` to the generic point of the hyperplane at
  infinity of `P'` over `x`, hence `j_* q^* α = c₁(O_{P'}(1)) ∩ q'^* α` on Chow groups;
* `j^* O_{P'}(1) = O_P(1)` on first Chern classes.  Concretely, on the standard cover of `P'`
  by the charts `D₊(x_(j, s'))`, `s' : Option (Option ι)`, the charts `D₊(x_(j, some s))` pull
  back to the charts `D₊(x_(j, s))` of `P` (`hyperplaneEmbedding_preimage_tautOpen`), and the
  transition units `x_(j', some s') / x_(j, some s)` restrict to the transition units
  `x_(j', s') / x_(j, s)` (`restrict_tautological_g`): over the affine open `U_j ∩ U_{j'}` of
  `X`, `j` is `Proj` of the graded surjection `(𝒜[t])[t'] → 𝒜[t]`, `t' ↦ 0`, which sends the
  homogeneous coordinate `x_(some s)` of `𝓔.extend` to the coordinate `x_s` of `𝓔`
  (`evalZeroGraded_extend_homogCoord_some`).  The comparison of first Chern classes then follows
  from the generic congruence lemma `firstChernClassOfField_congr`
  (`IntersectionTheory/FirstChernClassCongr.lean`).

## Main results

* `sectionsToRing_appLE`: reading a section pulled back along a morphism `g : P ⟶ P'` through an
  affine chart `ψ` with `ψ ≫ g = Spec.map α ≫ ψ'` is reading it through `ψ'` followed by `α`.
* `IntersectionTheory.AffineCharts.flatPullbackCharted_point`: the charted flat pullback of a
  point cycle `[x]` is the point cycle of the generic fibre point over `x`.
* `GradedBundleData.hyperplaneEmbedding_fibrePoint`:
  `j (fibrePoint_P x) = hyperPoint_{P'} x`.
* `GradedBundleData.closedImmersionPushforward_chowPullbackCharted_point`,
  `GradedBundleData.closedImmersionPushforward_chowPullbackCharted`:
  `j_* (q^* α) = c₁(O_{P'}(1)) ∩ (q'^* α)` for `α ∈ A_i(X)` (`X` locally of finite type over an
  infinite field with Noetherian underlying space, canonical dimension functions).
* `GradedBundleData.evalZeroGraded_extend_homogCoord_some`,
  `GradedBundleData.hyperplaneEmbedding_preimage_tautOpen`,
  `GradedBundleData.overlapChart_comp_hyperplaneEmbedding`,
  `GradedBundleData.restrict_tautological_g`,
  `GradedBundleData.sectionResidueUnit_restrict_tautological_g`: the charts and transition
  units of `O_{P'}(1)` restricted along `j` are those of `O_P(1)`.
* `GradedBundleData.firstChernClassOfField_tautological_restrict_hyperplaneEmbedding`,
  `GradedBundleData.c1Iter_restrict_hyperplaneEmbedding`: `j^* O_{P'}(1) = O_P(1)` on (iterated)
  first Chern classes.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace HomogeneousLocalization

namespace GromovWitten.AlgebraicGeometry

open GromovWitten.Algebra MvPolynomial IntersectionTheory RelativeProj

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Sections through affine charts along a morphism -/

/-- `sectionsToRing` is compatible with pulling back sections along a morphism `g : P ⟶ P'`
covered by `Spec.map α` on affine charts: if `ψ ≫ g = Spec.map α ≫ ψ'`, then pulling a section
over `O' ⊇ ψ'(Spec A')` back along `g` to `O ⊇ ψ(Spec A)` and reading it through `ψ` is reading
it through `ψ'` followed by `α`.  (The case `g = 𝟙` is `sectionsToRing_res`.) -/
theorem sectionsToRing_appLE {P P' : Scheme.{u}} {A A' : CommRingCat.{u}}
    (ψ : Spec A ⟶ P) (ψ' : Spec A' ⟶ P') [IsOpenImmersion ψ] [IsOpenImmersion ψ']
    (g : P ⟶ P') (α : A' ⟶ A) (hψ : ψ ≫ g = Spec.map α ≫ ψ')
    {O : P.Opens} {O' : P'.Opens} (hO : ψ.opensRange ≤ O) (hO' : ψ'.opensRange ≤ O')
    (h : O ≤ g ⁻¹ᵁ O') (s : Γ(P', O')) :
    sectionsToRing ψ O hO (g.appLE O' O h s) = α.hom (sectionsToRing ψ' O' hO' s) := by
  have hc : ∀ (χ : Spec A ⟶ P') (hχ : ⊤ ≤ χ ⁻¹ᵁ O'), χ = Spec.map α ≫ ψ' →
      χ.appLE O' ⊤ hχ =
        (Spec.map α ≫ ψ').appLE O' ⊤ (fun x _ ↦ hO' ⟨(Spec.map α).base x, rfl⟩) := by
    rintro χ hχ rfl
    rfl
  change (g.appLE O' O h ≫ ψ.appLE O ⊤ _ ≫ (Scheme.ΓSpecIso A).hom).hom s =
    ((ψ'.appLE O' ⊤ _ ≫ (Scheme.ΓSpecIso A').hom) ≫ α).hom s
  congr 1
  rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE, hc _ _ hψ, Category.assoc,
    ← Scheme.ΓSpecIso_naturality, ← Category.assoc]
  congr 2

/-! ### Charted pullback of a point -/

namespace IntersectionTheory.AffineCharts

variable {P X : Scheme.{u}} {q : P ⟶ X} {ι : Type u} [Finite ι] (𝒞 : AffineCharts q ι)

/-- The charted flat pullback of the point cycle `[x]` is the point cycle of the generic fibre
point over `x`. -/
theorem flatPullbackCharted_point (dimX : DimensionFunction X) (dimP : DimensionFunction P)
    (hshift : ∀ x, dimP (fibrePoint 𝒞 x) = dimX x + (Nat.card ι : ℤ)) {i : ℤ} (x : X)
    (hx : dimX x = i) :
    𝒞.flatPullbackCharted dimX dimP hshift i (cyclesOfDimension.point x hx) =
      cyclesOfDimension.point (fibrePoint 𝒞 x) (by rw [hshift, hx]) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro p
  rw [flatPullbackCharted_apply]
  by_cases hp : p ∈ Set.range (fibrePoint 𝒞)
  · obtain ⟨y, rfl⟩ := hp
    rw [pullbackCharted_apply_fibrePoint]
    by_cases hyx : y = x
    · subst hyx
      rw [cyclesOfDimension.point_apply_self, cyclesOfDimension.point_apply_self]
    · rw [cyclesOfDimension.point_apply_of_ne x y hx hyx,
        cyclesOfDimension.point_apply_of_ne _ _ _ (fun h ↦ hyx (fibrePoint_injective 𝒞 h))]
  · rw [pullbackCharted_eq_zero_of_notMem 𝒞 _ hp,
      cyclesOfDimension.point_apply_of_ne _ _ _ (fun h ↦ hp ⟨x, h.symm⟩)]

end IntersectionTheory.AffineCharts

namespace GradedBundleData

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : GradedBundleData X ι)

/-! ### The image of the generic fibre point -/

/-- `hyperplaneEmbedding` lies over `X`, on points. -/
theorem hyperplaneEmbedding_base_completionToBase (p : 𝓔.projectiveCompletion) :
    𝓔.extend.completionToBase.base (𝓔.hyperplaneEmbedding.base p) =
      𝓔.completionToBase.base p := by
  rw [← Scheme.Hom.comp_apply, hyperplaneEmbedding_toBase]

/-- **The hyperplane embedding sends the generic fibre point of `P(E ⊕ 1)` over `x` to the
generic point of the hyperplane at infinity of `P((E ⊕ 1) ⊕ 1)` over `x`.** -/
theorem hyperplaneEmbedding_fibrePoint (x : X) :
    𝓔.hyperplaneEmbedding.base (AffineCharts.fibrePoint 𝓔.completionCharts x) =
      𝓔.extend.hyperPoint x := by
  obtain ⟨p, hp⟩ := 𝓔.extend.hyperPoint_mem_range_infinityDivisor x
  have hqp : 𝓔.completionToBase.base p = x := by
    rw [← 𝓔.hyperplaneEmbedding_base_completionToBase p]
    change 𝓔.extend.completionToBase.base (𝓔.extend.infinityDivisor.base p) = x
    rw [hp, completionToBase_hyperPoint]
  refine 𝓔.extend.hyperPoint_eq_of_specializes ?_ ?_ ?_
  · rw [range_bundleOpenEmbedding]
    exact fun h ↦ h ⟨_, rfl⟩
  · rw [hyperplaneEmbedding_base_completionToBase, AffineCharts.q_fibrePoint]
  · have h : AffineCharts.fibrePoint 𝓔.completionCharts x ⤳ p :=
      AffineCharts.fibrePoint_specializes _ (by rw [hqp])
    have := 𝓔.hyperplaneEmbedding.base.hom.map_specializes h
    rwa [show 𝓔.hyperplaneEmbedding.base p = 𝓔.extend.hyperPoint x from hp] at this

/-! ### The homogeneous coordinates under `t ↦ 0` -/

set_option backward.isDefEq.respectTransparency false in
/-- Killing the new variable `x_none` of `P((E ⊕ 1) ⊕ 1)` sends the homogeneous coordinate
`x_(some s)` of `𝓔.extend` to the homogeneous coordinate `x_s` of `𝓔`. -/
theorem evalZeroGraded_extend_homogCoord_some (j : 𝓔.bundle.J) (s : Option ι) :
    evalZeroGraded (𝓔.homogData.grading (𝓔.bundle.chart j))
        (𝓔.extend.homogCoord j (some s)) = 𝓔.homogCoord j s := by
  have h1 : (homogEquivOption Γ(X, (𝓔.bundle.chart j).1) (Option ι)).symm
      (MvPolynomial.X (some s)) = Polynomial.C (MvPolynomial.X s) := by
    change MvPolynomial.optionEquivLeft _ _ (MvPolynomial.X (some s)) = _
    rw [optionEquivLeft_X_some]
  have h2 : (𝓔.extendTriv j).symm (MvPolynomial.X s) = 𝓔.homogCoord j s := by
    rw [AlgEquiv.symm_apply_eq]
    exact (GradedRingHom.congr_fun (𝓔.chartGraded_comp_chartGradedInv j)
      (MvPolynomial.X s)).symm
  change Polynomial.constantCoeff
    (Polynomial.map (𝓔.extendTriv j).symm.toRingEquiv.toRingHom
      ((homogEquivOption Γ(X, (𝓔.bundle.chart j).1) (Option ι)).symm
        (MvPolynomial.X (some s)))) = _
  rw [h1, Polynomial.map_C, Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]
  exact h2


set_option backward.isDefEq.respectTransparency false in
/-- Killing `x_none` sends the restricted coordinate `x_(some s)|_V` of `𝓔.extend` to the
restricted coordinate `x_s|_V` of `𝓔`. -/
theorem evalZeroGraded_extend_homogCoordAt (a : 𝓔.TautIndex) (V : X.affineOpens)
    (h : V ≤ 𝓔.bundle.chart a.1) :
    evalZeroGraded (𝓔.homogData.grading V) (𝓔.extend.homogCoordAt (a.1, some a.2) V h) =
      𝓔.homogCoordAt a V h := by
  change ((evalZeroGraded (𝓔.homogData.grading V)).comp (homogMap (𝓔.homogData.map h)))
    (𝓔.extend.homogCoord a.1 (some a.2)) = _
  rw [evalZeroGraded_comp_homogMap]
  change 𝓔.homogData.map h (evalZeroGraded (𝓔.homogData.grading (𝓔.bundle.chart a.1))
    (𝓔.extend.homogCoord a.1 (some a.2))) = _
  rw [evalZeroGraded_extend_homogCoord_some]
  rfl

/-! ### The hyperplane embedding on the affine pieces and the charts -/

/-- On the affine piece over `U`, the hyperplane embedding is `Proj.map` of `t ↦ 0`. -/
theorem hyperplaneEmbedding_affineι (U : X.affineOpens) (y : Proj (𝓔.homogData.grading U)) :
    𝓔.hyperplaneEmbedding.base (affineι X 𝓔.homogData U y) =
      (affineι X 𝓔.homogData.homogenisation U).base
        (Proj.map (𝓔.homogData.evalZeroHom.app U)
          (𝓔.homogData.evalZeroHom.irrelevant_le U) y) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun g : Proj (𝓔.homogData.grading U) ⟶ 𝓔.extend.projectiveCompletion ↦ g.base y)
    (Hom.affineι_map 𝓔.homogData.evalZeroHom U)

set_option backward.isDefEq.respectTransparency false in
/-- For a point `y` of the affine piece of `P(E ⊕ 1)` over `U_j`, its image in
`P((E ⊕ 1) ⊕ 1)` lies in the chart `D₊(x_(some s))` iff `y` lies in the chart `D₊(x_s)`. -/
theorem hyperplaneEmbedding_affineι_mem_range_tautChart_iff (j : 𝓔.bundle.J) (s : Option ι)
    (y : Proj (𝓔.homogData.grading (𝓔.bundle.chart j))) :
    𝓔.hyperplaneEmbedding.base (affineι X 𝓔.homogData (𝓔.bundle.chart j) y) ∈
        Set.range (𝓔.extend.tautChart (j, some s)).base ↔
      (affineι X 𝓔.homogData (𝓔.bundle.chart j)).base y ∈
        Set.range (𝓔.tautChart (j, s)).base := by
  have h2 := affineι_mem_range_awayChart_iff 𝓔.extend.homogData (𝓔.bundle.chart j)
    (Proj.map (𝓔.homogData.evalZeroHom.app (𝓔.bundle.chart j))
      (𝓔.homogData.evalZeroHom.irrelevant_le (𝓔.bundle.chart j)) y)
    (𝓔.extend.homogCoord j (some s)) (𝓔.extend.homogCoord_mem j (some s)) one_pos
  have h3 := affineι_mem_range_awayChart_iff 𝓔.homogData (𝓔.bundle.chart j) y
    (𝓔.homogCoord j s) (𝓔.homogCoord_mem j s) one_pos
  rw [hyperplaneEmbedding_affineι]
  refine h2.trans (Iff.trans ?_ h3.symm)
  change evalZeroGraded (𝓔.homogData.grading (𝓔.bundle.chart j))
    (𝓔.extend.homogCoord j (some s)) ∉ y.asHomogeneousIdeal ↔ _
  rw [evalZeroGraded_extend_homogCoord_some]

set_option backward.isDefEq.respectTransparency false in
/-- **The charts of `O(1)` restrict correctly**: the preimage under the hyperplane embedding of
the chart `D₊(x_(some s))` of `P((E ⊕ 1) ⊕ 1)` over `U_j` is the chart `D₊(x_s)` of `P(E ⊕ 1)`. -/
theorem hyperplaneEmbedding_preimage_tautOpen (j : 𝓔.bundle.J) (s : Option ι) :
    𝓔.hyperplaneEmbedding ⁻¹ᵁ
        (𝓔.extend.tautOpen (j, some s) : 𝓔.extend.projectiveCompletion.Opens) =
      (𝓔.tautOpen (j, s) : 𝓔.projectiveCompletion.Opens) := by
  ext p
  change 𝓔.hyperplaneEmbedding.base p ∈ Set.range (𝓔.extend.tautChart (j, some s)).base ↔
    p ∈ Set.range (𝓔.tautChart (j, s)).base
  have hU : p ∈ Set.range (affineι X 𝓔.homogData (𝓔.bundle.chart j)).base ↔
      𝓔.completionToBase.base p ∈ (𝓔.bundle.chart j).1 := by
    rw [range_affineι]
    exact Iff.rfl
  constructor
  · intro hp
    have hp' : 𝓔.hyperplaneEmbedding.base p ∈
        Set.range (affineι X 𝓔.extend.homogData (𝓔.bundle.chart j)).base :=
      range_awayChart_subset _ _ _ _ _ hp
    rw [range_affineι] at hp'
    change 𝓔.extend.completionToBase.base (𝓔.hyperplaneEmbedding.base p) ∈
      (𝓔.bundle.chart j).1 at hp'
    rw [hyperplaneEmbedding_base_completionToBase, ← hU] at hp'
    obtain ⟨y, rfl⟩ := hp'
    exact (𝓔.hyperplaneEmbedding_affineι_mem_range_tautChart_iff j s y).mp hp
  · intro hp
    obtain ⟨y, rfl⟩ := range_awayChart_subset _ _ _ _ _ hp
    exact (𝓔.hyperplaneEmbedding_affineι_mem_range_tautChart_iff j s y).mpr hp

/-! ### The transition units of `O(1)` under the hyperplane embedding -/

variable (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))

/-- The chart index `(j, some s)` of `P((E ⊕ 1) ⊕ 1)` attached to the chart index `(j, s)` of
`P(E ⊕ 1)`. -/
abbrev extendIndex (a : 𝓔.TautIndex) : 𝓔.extend.TautIndex := (a.1, some a.2)

set_option backward.isDefEq.respectTransparency false in
/-- Killing `x_none` sends `x_(some a) x_(some b)` to `x_a x_b`. -/
theorem evalZeroGraded_extend_overlapElem (a b : 𝓔.TautIndex) :
    evalZeroGraded (𝓔.homogData.grading (𝓔.overlapBase hX a b))
        (𝓔.extend.overlapElem hX (𝓔.extendIndex a) (𝓔.extendIndex b)) =
      𝓔.overlapElem hX a b := by
  change evalZeroGraded _
    (𝓔.extend.homogCoordAt (a.1, some a.2) (𝓔.overlapBase hX a b) (𝓔.overlapBase_le_left hX a b) *
      𝓔.extend.homogCoordAt (b.1, some b.2) (𝓔.overlapBase hX a b)
        (𝓔.overlapBase_le_right hX a b)) = _
  rw [map_mul]
  exact congrArg₂ (· * ·)
    (𝓔.evalZeroGraded_extend_homogCoordAt a (𝓔.overlapBase hX a b) (𝓔.overlapBase_le_left hX a b))
    (𝓔.evalZeroGraded_extend_homogCoordAt b (𝓔.overlapBase hX a b)
      (𝓔.overlapBase_le_right hX a b))

set_option backward.isDefEq.respectTransparency false in
/-- **The overlap charts under the hyperplane embedding**: `D₊(x_a x_b) ⊆ P(E ⊕ 1)` maps to
`D₊(x_(some a) x_(some b)) ⊆ P((E ⊕ 1) ⊕ 1)` through the homogeneous localisation of
`t ↦ 0`. -/
theorem overlapChart_comp_hyperplaneEmbedding (a b : 𝓔.TautIndex) :
    𝓔.overlapChart hX a b ≫ 𝓔.hyperplaneEmbedding =
      Spec.map (CommRingCat.ofHom (awayMapOfEq
        (evalZeroGraded (𝓔.homogData.grading (𝓔.overlapBase hX a b)))
        (𝓔.extend.overlapElem hX (𝓔.extendIndex a) (𝓔.extendIndex b)) (𝓔.overlapElem hX a b)
        (𝓔.evalZeroGraded_extend_overlapElem hX a b))) ≫
        𝓔.extend.overlapChart hX (𝓔.extendIndex a) (𝓔.extendIndex b) := by
  change (Proj.awayι _ _ (𝓔.overlapElem_mem hX a b) _ ≫ affineι X 𝓔.homogData _) ≫
    𝓔.homogData.evalZeroHom.map =
      _ ≫ (Proj.awayι _ _ _ _ ≫ affineι X 𝓔.homogData.homogenisation _)
  have key := awayι_comp_projMap_of_eq (𝓔.homogData.evalZeroHom.app (𝓔.overlapBase hX a b))
    (𝓔.homogData.evalZeroHom.irrelevant_le _) (by norm_num)
    (𝓔.extend.overlapElem hX (𝓔.extendIndex a) (𝓔.extendIndex b))
    (𝓔.extend.overlapElem_mem hX (𝓔.extendIndex a) (𝓔.extendIndex b)) (𝓔.overlapElem hX a b)
    (𝓔.evalZeroGraded_extend_overlapElem hX a b) (𝓔.overlapElem_mem hX a b)
  rw [Category.assoc, Hom.affineι_map, ← Category.assoc, key, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The chart `(j, some s)` of the restriction of `O(1)` along the hyperplane embedding is the
chart `(j, s)` of `O(1)` on `P(E ⊕ 1)`. -/
theorem restrict_tautological_U (a : 𝓔.TautIndex) :
    (((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding).U (𝓔.extendIndex a) :
        𝓔.projectiveCompletion.Opens) =
      ((𝓔.tautological hX).U a : 𝓔.projectiveCompletion.Opens) :=
  𝓔.hyperplaneEmbedding_preimage_tautOpen a.1 a.2

/-- The overlap of two charts of the restriction of `O(1)` along the hyperplane embedding is
contained in (in fact equal to) the overlap of the corresponding charts of `O(1)`. -/
theorem restrict_tautological_inf_le (a b : 𝓔.TautIndex) :
    (((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding).U (𝓔.extendIndex a) :
        𝓔.projectiveCompletion.Opens) ⊓
      (((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding).U (𝓔.extendIndex b) :
        𝓔.projectiveCompletion.Opens) ≤
    ((𝓔.tautological hX).U a : 𝓔.projectiveCompletion.Opens) ⊓
      ((𝓔.tautological hX).U b : 𝓔.projectiveCompletion.Opens) := by
  rw [restrict_tautological_U, restrict_tautological_U]

set_option backward.isDefEq.respectTransparency false in
/-- **The transition units of `O(1)` restrict correctly**: the transition unit of the restriction
of `O_{P((E ⊕ 1) ⊕ 1)}(1)` along the hyperplane embedding between the charts `(j, some s)` and
`(j', some s')` is the transition unit `x_(j', s') / x_(j, s)` of `O_{P(E ⊕ 1)}(1)`. -/
theorem restrict_tautological_g (a b : 𝓔.TautIndex) :
    ((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding).g (𝓔.extendIndex a)
        (𝓔.extendIndex b) =
      resUnit (𝓔.restrict_tautological_inf_le hX a b) ((𝓔.tautological hX).g a b) := by
  set ψ := 𝓔.overlapChart hX a b
  set ψ' := 𝓔.extend.overlapChart hX (𝓔.extendIndex a) (𝓔.extendIndex b)
  have hO : ψ.opensRange =
      (((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding).U (𝓔.extendIndex a) :
        𝓔.projectiveCompletion.Opens) ⊓
      (((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding).U (𝓔.extendIndex b) :
        𝓔.projectiveCompletion.Opens) := by
    rw [restrict_tautological_U, restrict_tautological_U]
    exact 𝓔.opensRange_overlapChart hX a b
  have hL : sectionsToRing ψ _ hO.le
      (((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding).g (𝓔.extendIndex a)
        (𝓔.extendIndex b)).val =
      (CommRingCat.ofHom (awayMapOfEq
        (evalZeroGraded (𝓔.homogData.grading (𝓔.overlapBase hX a b)))
        (𝓔.extend.overlapElem hX (𝓔.extendIndex a) (𝓔.extendIndex b)) (𝓔.overlapElem hX a b)
        (𝓔.evalZeroGraded_extend_overlapElem hX a b))).hom
        (sectionsToRing ψ' _ (𝓔.extend.opensRange_overlapChart hX _ _).le
          ((𝓔.extend.tautological hX).g (𝓔.extendIndex a) (𝓔.extendIndex b)).val) :=
    sectionsToRing_appLE ψ ψ' 𝓔.hyperplaneEmbedding _
      (𝓔.overlapChart_comp_hyperplaneEmbedding hX a b) hO.le
      (𝓔.extend.opensRange_overlapChart hX _ _).le
      (LineBundleData.inf_preimage_le_preimage_inf 𝓔.hyperplaneEmbedding _ _) _
  have hR : sectionsToRing ψ _ hO.le
      (resUnit (𝓔.restrict_tautological_inf_le hX a b) ((𝓔.tautological hX).g a b)).val =
      sectionsToRing ψ _ (𝓔.opensRange_overlapChart hX a b).le ((𝓔.tautological hX).g a b).val :=
    sectionsToRing_res ψ ψ (𝟙 _) (by rw [Spec.map_id, Category.id_comp])
      (𝓔.opensRange_overlapChart hX a b).le hO.le (𝓔.restrict_tautological_inf_le hX a b) _
  apply Units.ext
  apply (sectionsToRing_bijective ψ _ hO).injective
  rw [hL, hR, 𝓔.extend.tautological_g hX (𝓔.extendIndex a) (𝓔.extendIndex b),
    𝓔.tautological_g hX a b]
  change awayMapOfEq (evalZeroGraded (𝓔.homogData.grading (𝓔.overlapBase hX a b)))
    (𝓔.extend.overlapElem hX (𝓔.extendIndex a) (𝓔.extendIndex b)) (𝓔.overlapElem hX a b)
    (𝓔.evalZeroGraded_extend_overlapElem hX a b) (Away.mk _ _ 1 _ _) = _
  refine (awayMapOfEq_mk _ _ _ _ (𝓔.extend.overlapElem_mem hX _ _) (𝓔.overlapElem_mem hX a b)
    1 _ _).trans ?_
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, Away.val_mk]
  congr 1
  rw [map_pow]
  congr 1
  exact 𝓔.evalZeroGraded_extend_homogCoordAt b (𝓔.overlapBase hX a b)
    (𝓔.overlapBase_le_right hX a b)

/-- The residue classes of the transition units of the restriction of `O(1)` along the
hyperplane embedding agree with those of `O(1)` on `P(E ⊕ 1)`. -/
theorem sectionResidueUnit_restrict_tautological_g (a b : 𝓔.TautIndex)
    (p : 𝓔.projectiveCompletion)
    (hp : p ∈ ((𝓔.tautological hX).U a : 𝓔.projectiveCompletion.Opens) ⊓
      ((𝓔.tautological hX).U b : 𝓔.projectiveCompletion.Opens))
    (hp' : p ∈ (((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding).U
        (𝓔.extendIndex a) : 𝓔.projectiveCompletion.Opens) ⊓
      (((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding).U (𝓔.extendIndex b) :
        𝓔.projectiveCompletion.Opens)) :
    sectionResidueUnit hp' (((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding).g
        (𝓔.extendIndex a) (𝓔.extendIndex b)) =
      sectionResidueUnit hp ((𝓔.tautological hX).g a b) := by
  rw [restrict_tautological_g, sectionResidueUnit_resUnit]

/-! ### `j^* O(1) = O(1)` on first Chern classes -/

section Chern

variable {k : Type u} [Field k] [Infinite k] (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [NoetherianSpace X]

/-- **`j^* O_{P((E ⊕ 1) ⊕ 1)}(1) = O_{P(E ⊕ 1)}(1)` on first Chern classes**: the first Chern
class of the restriction of the tautological bundle of `P((E ⊕ 1) ⊕ 1)` along the hyperplane
embedding is the first Chern class of the tautological bundle of `P(E ⊕ 1)`. -/
theorem firstChernClassOfField_tautological_restrict_hyperplaneEmbedding (i : ℤ) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    firstChernClassOfField (𝓔.completionToBase ≫ f)
        ((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding) i =
      firstChernClassOfField (𝓔.completionToBase ≫ f) (𝓔.tautological hX) i := by
  have := 𝓔.noetherianSpace_projectiveCompletion f
  exact (firstChernClassOfField_congr (𝓔.completionToBase ≫ f) (𝓔.tautological hX)
    ((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding) 𝓔.extendIndex
    (𝓔.restrict_tautological_U hX) (𝓔.sectionResidueUnit_restrict_tautological_g hX) i).symm

/-- **Iterated first Chern classes of `j^* O(1)` and `O(1)` agree.** -/
theorem c1Iter_restrict_hyperplaneEmbedding (m : ℕ) (i : ℤ) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    c1Iter (𝓔.completionToBase ≫ f)
        ((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding) m i =
      c1Iter (𝓔.completionToBase ≫ f) (𝓔.tautological hX) m i := by
  have := 𝓔.noetherianSpace_projectiveCompletion f
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
    rw [c1Iter_succ, c1Iter_succ, ih,
      firstChernClassOfField_tautological_restrict_hyperplaneEmbedding]

end Chern

/-! ### `j_* q^* = c₁(O(1)) ∩ q'^*` -/

section Pushforward

open RationalEquivalenceSystem.DescendingMap FiniteTypeDimension ChartedOverSubscheme

variable {k : Type u} [Field k] [Infinite k] (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [NoetherianSpace X] [Finite ι]

omit hX [Infinite k] [NoetherianSpace X] [Finite ι] in
/-- The pushforward along the hyperplane embedding of the generic fibre point of `P(E ⊕ 1)` over
`x` is the generic hyperplane point of `P((E ⊕ 1) ⊕ 1)` over `x`, on cycles. -/
theorem properPushforward_hyperplaneEmbedding_point {i : ℤ} (x : X)
    (hx : dimensionFunction (𝓔.completionToBase ≫ f)
      (AffineCharts.fibrePoint 𝓔.completionCharts x) = i) :
    cyclesOfDimension.properPushforward
        (dimensionY := dimensionFunction (𝓔.extend.completionToBase ≫ f))
        𝓔.hyperplaneEmbedding
        (cyclesOfDimension.point (AffineCharts.fibrePoint 𝓔.completionCharts x) hx) =
      cyclesOfDimension.point (𝓔.extend.hyperPoint x)
        (by
          rw [← hyperplaneEmbedding_fibrePoint, ← hx]
          exact (DimensionFunction.apply_eq_of_isClosedImmersion _ _ 𝓔.hyperplaneEmbedding
            _).symm) := by
  rw [properPushforward_point_of_isClosedImmersion,
    cyclesOfDimension.point_congr (𝓔.hyperplaneEmbedding_fibrePoint x)]

/-- **`j_* q^*[x] = c₁(O(1)) ∩ q'^*[x]`** for the class of a point `x` of dimension `i`: the
pushforward along the hyperplane embedding `j : P(E ⊕ 1) ⟶ P((E ⊕ 1) ⊕ 1)` of the pullback of
`[x]` to `P(E ⊕ 1)` is the first Chern class of `O(1)` capped with the pullback of `[x]` to
`P((E ⊕ 1) ⊕ 1)`. -/
theorem closedImmersionPushforward_chowPullbackCharted_point {i : ℤ} (x : X)
    (hx : dimensionFunction f x = i) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    haveI := 𝓔.extend.noetherianSpace_projectiveCompletion f
    closedImmersionPushforward
        (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) (i + Nat.card ι))
        𝓔.hyperplaneEmbedding
        (chowSystem (dimensionFunction (𝓔.extend.completionToBase ≫ f)) (i + Nat.card ι))
        (chowPullbackCharted 𝓔.completionCharts (dimensionFunction f)
          (dimensionFunction (𝓔.completionToBase ≫ f))
          (𝓔.dimensionFunction_fibrePoint_completionCharts f) i (chowSystem _ i)
          (chowSystem _ (i + Nat.card ι))
          ((chowSystem (dimensionFunction f) i).quotientMap (cyclesOfDimension.point x hx))) =
      firstChernClassOfField (𝓔.extend.completionToBase ≫ f) (𝓔.extend.tautological hX)
        (i + Nat.card ι)
        (chowCast (by rw [Finite.card_option]; push_cast; ring)
          (chowPullbackCharted 𝓔.extend.completionCharts (dimensionFunction f)
            (dimensionFunction (𝓔.extend.completionToBase ≫ f))
            (𝓔.extend.dimensionFunction_fibrePoint_completionCharts f) i (chowSystem _ i)
            (chowSystem _ (i + Nat.card (Option ι)))
            ((chowSystem (dimensionFunction f) i).quotientMap
              (cyclesOfDimension.point x hx)))) := by
  have := 𝓔.noetherianSpace_projectiveCompletion f
  have := 𝓔.extend.noetherianSpace_projectiveCompletion f
  rw [chowPullbackCharted_quotientMap, chowPullbackCharted_quotientMap,
    AffineCharts.flatPullbackCharted_point, AffineCharts.flatPullbackCharted_point,
    closedImmersionPushforward_quotientMap, properPushforward_hyperplaneEmbedding_point,
    chowCast_quotientMap, cyclesCast_point]
  have hdeg : dimensionFunction f x + (Nat.card (Option ι) : ℤ) - 1 = i + Nat.card ι := by
    rw [hx, Finite.card_option]; push_cast; ring
  change _ = firstChernClassOfField (𝓔.extend.completionToBase ≫ f) (𝓔.extend.tautological hX)
    (i + Nat.card ι) (chowCast rfl ((chowSystem _ _).quotientMap
      (cyclesOfDimension.point (AffineCharts.fibrePoint 𝓔.extend.completionCharts x) _)))
  rw [firstChernClassOfField_chowCast _ _ hdeg rfl, chowCast_quotientMap, cyclesCast_point,
    𝓔.extend.firstChernClassOfField_tautological_fibrePoint hX f x, chowCast_quotientMap,
    cyclesCast_point]

/-- **`j_* q^* α = c₁(O(1)) ∩ q'^* α`** (Fulton, §3.3): the pushforward along the hyperplane
embedding `j : P(E ⊕ 1) ⟶ P((E ⊕ 1) ⊕ 1)` of the pullback of a class `α ∈ A_i(X)` to
`P(E ⊕ 1)` is the first Chern class of `O(1)` capped with the pullback of `α` to
`P((E ⊕ 1) ⊕ 1)`. -/
theorem closedImmersionPushforward_chowPullbackCharted (i : ℤ)
    (α : (chowSystem (dimensionFunction f) i).ChowGroup) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    haveI := 𝓔.extend.noetherianSpace_projectiveCompletion f
    closedImmersionPushforward
        (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) (i + Nat.card ι))
        𝓔.hyperplaneEmbedding
        (chowSystem (dimensionFunction (𝓔.extend.completionToBase ≫ f)) (i + Nat.card ι))
        (chowPullbackCharted 𝓔.completionCharts (dimensionFunction f)
          (dimensionFunction (𝓔.completionToBase ≫ f))
          (𝓔.dimensionFunction_fibrePoint_completionCharts f) i (chowSystem _ i)
          (chowSystem _ (i + Nat.card ι)) α) =
      firstChernClassOfField (𝓔.extend.completionToBase ≫ f) (𝓔.extend.tautological hX)
        (i + Nat.card ι)
        (chowCast (by rw [Finite.card_option]; push_cast; ring)
          (chowPullbackCharted 𝓔.extend.completionCharts (dimensionFunction f)
            (dimensionFunction (𝓔.extend.completionToBase ≫ f))
            (𝓔.extend.dimensionFunction_fibrePoint_completionCharts f) i (chowSystem _ i)
            (chowSystem _ (i + Nat.card (Option ι))) α)) := by
  have := 𝓔.noetherianSpace_projectiveCompletion f
  have := 𝓔.extend.noetherianSpace_projectiveCompletion f
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  change (closedImmersionPushforward _ 𝓔.hyperplaneEmbedding _ ∘ₗ
      (chowPullbackCharted 𝓔.completionCharts (dimensionFunction f)
        (dimensionFunction (𝓔.completionToBase ≫ f))
        (𝓔.dimensionFunction_fibrePoint_completionCharts f) i (chowSystem _ i)
        (chowSystem _ (i + Nat.card ι)) ∘ₗ (chowSystem (dimensionFunction f) i).quotientMap)) z =
    (firstChernClassOfField (𝓔.extend.completionToBase ≫ f) (𝓔.extend.tautological hX)
      (i + Nat.card ι) ∘ₗ ((chowCast (by rw [Finite.card_option]; push_cast; ring)).toLinearMap ∘ₗ
      (chowPullbackCharted 𝓔.extend.completionCharts (dimensionFunction f)
        (dimensionFunction (𝓔.extend.completionToBase ≫ f))
        (𝓔.extend.dimensionFunction_fibrePoint_completionCharts f) i (chowSystem _ i)
        (chowSystem _ (i + Nat.card (Option ι))) ∘ₗ
          (chowSystem (dimensionFunction f) i).quotientMap))) z
  refine LinearMap.congr_fun (LinearMap.ext fun w ↦ ?_) z
  rw [cyclesOfDimension.eq_sum_pointProj w, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [map_smul, map_smul]
  congr 1
  by_cases hx : dimensionFunction f x = i
  · rw [cyclesOfDimension.pointProj_eq_point hx]
    exact 𝓔.closedImmersionPushforward_chowPullbackCharted_point hX f x hx
  · rw [cyclesOfDimension.pointProj_eq_zero_of_ne hx, map_zero, map_zero]

end Pushforward

end GradedBundleData

end

end GromovWitten.AlgebraicGeometry
