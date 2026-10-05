/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChartPointOrder
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FirstChernClassGeneral
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroupLocalization
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleRestrict

/-!
# Pullback of line bundle data and `c₁` under open restriction

For a morphism of schemes `ψ : Y' ⟶ Y` and Čech line bundle data `L` on `Y`, this file defines
the pulled back line bundle data `L.pullback ψ` on `Y'`: its charts are the affine opens `W` of
`Y'` contained in some `ψ⁻¹(U a)`, and its transition units are the pullbacks along `ψ`
(`Scheme.Hom.appLE`) of those of `L`.  For an open immersion `ψ` it proves that the first Chern
class commutes with restriction to `Y'`, first at the cycle level and then on Chow groups over
an infinite field.

The comparison is pointwise: for a point `x' : Y'`, the divisor of the frame section (coordinate
`1` in a chart) of `L` along `pointSubscheme (ψ x')` restricts to the divisor of the
corresponding frame section of `L.pullback ψ` along `pointSubscheme x'`.  Both coefficients are
computed by `LineBundleData.divisor_frame_apply` as `pointOrd`s of residues of transition units,
which agree by the open-immersion invariance of `pointOrd` (`pointOrd_openImmersion`,
`ChartPointOrder.lean`).

## Main results

* `LineBundleData.pullback` — pullback of line bundle data along any morphism, with
  `pullback_U`, `pullback_g` and `sectionResidueUnit_pullback_g` (residues of the pulled back
  transition units are the images of the original residues under `ψ.residueFieldMap`).
* `pullbackOpen_divisor_frame` — for an open immersion, the divisor of a frame section restricts
  to the divisor of the pulled back frame section.
* `openImmersionPullback_comp_c1Cycle` — cycle-level compatibility of `c1Cycle` with open
  restriction, for dimension functions with `dim' = dim ∘ ψ` satisfying `CovByDimension`.
* `openImmersionPullback_firstChernClassOfField` — over an infinite field,
  `(c₁(L) ∩ β)|_{Y'} = c₁(L.pullback ψ) ∩ (β|_{Y'})` on Chow groups with the canonical dimension
  functions.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace LineBundleData

variable {Y' Y : Scheme.{u}}

/-- The chart index type of the pullback of `L` along `ψ`: pairs of a chart `a` of `L` and an
affine open of `Y'` contained in `ψ⁻¹(U a)`. -/
abbrev PullbackIndex (L : LineBundleData Y) (ψ : Y' ⟶ Y) : Type u :=
  {aW : L.J × Y'.affineOpens // (aW.2 : Y'.Opens) ≤ ψ ⁻¹ᵁ (L.U aW.1 : Y.Opens)}

/-- The overlap of two charts of the pullback lies in the preimage of the overlap of the
underlying charts. -/
lemma pullbackIndex_inf_le (L : LineBundleData Y) (ψ : Y' ⟶ Y) (aW bW : L.PullbackIndex ψ) :
    (aW.1.2 : Y'.Opens) ⊓ (bW.1.2 : Y'.Opens) ≤
      ψ ⁻¹ᵁ ((L.U aW.1.1 : Y.Opens) ⊓ (L.U bW.1.1 : Y.Opens)) := by
  rw [Scheme.Hom.preimage_inf]
  exact inf_le_inf aW.2 bW.2

/-- The pullback of line bundle data along an arbitrary morphism of schemes `ψ : Y' ⟶ Y`: the
charts are the affine opens `W` of `Y'` inside some `ψ⁻¹(U a)`, and the transition unit of two
such charts is the pullback along `ψ` of the transition unit of the underlying charts of `L`. -/
noncomputable def pullback (L : LineBundleData Y) (ψ : Y' ⟶ Y) : LineBundleData Y' where
  J := L.PullbackIndex ψ
  U aW := aW.1.2
  covers y := by
    obtain ⟨a, ha⟩ := L.covers (ψ.base y)
    obtain ⟨W, hW, hyW, hWle⟩ := Opens.isBasis_iff_nbhd.mp Y'.isBasis_affineOpens
      (show y ∈ ψ ⁻¹ᵁ (L.U a : Y.Opens) from ha)
    exact ⟨⟨(a, ⟨W, hW⟩), hWle⟩, hyW⟩
  g aW bW := pullUnit ψ (pullbackIndex_inf_le L ψ aW bW) (L.g aW.1.1 bW.1.1)
  g_self aW := by
    rw [L.g_self]
    exact pullUnit_one ψ _
  g_cocycle aW bW cW := by
    have hT : (aW.1.2 : Y'.Opens) ⊓ (bW.1.2 : Y'.Opens) ⊓ (cW.1.2 : Y'.Opens) ≤
        ψ ⁻¹ᵁ ((L.U aW.1.1 : Y.Opens) ⊓ (L.U bW.1.1 : Y.Opens) ⊓ (L.U cW.1.1 : Y.Opens)) := by
      rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf]
      exact inf_le_inf (inf_le_inf aW.2 bW.2) cW.2
    rw [resUnit_pullUnit, resUnit_pullUnit, resUnit_pullUnit,
      ← pullUnit_resUnit ψ hT inf_le_left,
      ← pullUnit_resUnit ψ hT (inf_le_inf inf_le_right le_rfl),
      ← pullUnit_resUnit ψ hT (inf_le_inf inf_le_left le_rfl), ← pullUnit_mul, L.g_cocycle]

@[simp]
lemma pullback_J (L : LineBundleData Y) (ψ : Y' ⟶ Y) :
    (L.pullback ψ).J = L.PullbackIndex ψ := rfl

@[simp]
lemma pullback_U (L : LineBundleData Y) (ψ : Y' ⟶ Y) (aW : L.PullbackIndex ψ) :
    (L.pullback ψ).U aW = aW.1.2 := rfl

lemma pullback_g (L : LineBundleData Y) (ψ : Y' ⟶ Y) (aW bW : L.PullbackIndex ψ) :
    (L.pullback ψ).g aW bW = pullUnit ψ (pullbackIndex_inf_le L ψ aW bW) (L.g aW.1.1 bW.1.1) :=
  rfl

/-- The residue at a point `y` of a transition unit of the pullback is the image, under the
residue field map `κ(ψ y) → κ(y)`, of the residue at `ψ y` of the original transition unit. -/
theorem sectionResidueUnit_pullback_g (L : LineBundleData Y) (ψ : Y' ⟶ Y)
    (aW bW : L.PullbackIndex ψ) {y : Y'}
    (hy : y ∈ ((L.pullback ψ).U aW : Y'.Opens) ⊓ ((L.pullback ψ).U bW : Y'.Opens)) :
    sectionResidueUnit hy ((L.pullback ψ).g aW bW) =
      Units.map (ψ.residueFieldMap y).hom.toMonoidHom
        (sectionResidueUnit (U := (L.U aW.1.1 : Y.Opens) ⊓ (L.U bW.1.1 : Y.Opens))
          ⟨aW.2 hy.1, bW.2 hy.2⟩ (L.g aW.1.1 bW.1.1)) := by
  apply Units.ext
  have hy' : y ∈ (aW.1.2 : Y'.Opens) ⊓ (bW.1.2 : Y'.Opens) := hy
  change Y'.residue y (Y'.presheaf.germ ((aW.1.2 : Y'.Opens) ⊓ (bW.1.2 : Y'.Opens)) y hy'
    ((ψ.appLE ((L.U aW.1.1 : Y.Opens) ⊓ (L.U bW.1.1 : Y.Opens))
      ((aW.1.2 : Y'.Opens) ⊓ (bW.1.2 : Y'.Opens))
      (by
        rw [Scheme.Hom.preimage_inf]
        exact inf_le_inf aW.2 bW.2)).hom
      ((L.g aW.1.1 bW.1.1 : Γ(Y, (L.U aW.1.1 : Y.Opens) ⊓ (L.U bW.1.1 : Y.Opens)))))) =
    (ψ.residueFieldMap y).hom (Y.residue (ψ.base y)
      (Y.presheaf.germ ((L.U aW.1.1 : Y.Opens) ⊓ (L.U bW.1.1 : Y.Opens)) (ψ.base y)
        ⟨aW.2 hy'.1, bW.2 hy'.2⟩
        (L.g aW.1.1 bW.1.1 : Γ(Y, (L.U aW.1.1 : Y.Opens) ⊓ (L.U bW.1.1 : Y.Opens)))))
  rw [← CommRingCat.comp_apply (Y.residue _), Scheme.residue_residueFieldMap,
    CommRingCat.comp_apply]
  refine congrArg (Y'.residue y).hom ?_
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply ψ _ y _ _).symm
  exact Y'.presheaf.germ_res_apply (homOfLE _) y hy' _

end LineBundleData

/-! ## Divisors of frame sections under open restriction -/

section Restrict

variable {Y' Y : Scheme.{u}}

open LineBundleInjective

/-- **Divisors of frame sections restrict along open immersions** (blueprint A3, frame form).
Let `ψ : Y' ⟶ Y` be an open immersion, `x' : Y'`, and `aW` a chart of `L.pullback ψ` (an affine
open of `Y'` inside `ψ⁻¹(U a)`) containing `x'`.  The restriction along `ψ` of the divisor of the
rational section of `L` along `pointSubscheme (ψ x')` with coordinate `1` in the chart `a` is the
divisor of the rational section of `L.pullback ψ` along `pointSubscheme x'` with coordinate `1`
in the chart `aW`.  (No compatibility of the dimension functions is needed: the coefficients of
these divisors do not depend on them.) -/
theorem pullbackOpen_divisor_frame [IsLocallyNoetherian Y] [NoetherianSpace Y]
    [IsLocallyNoetherian Y'] [NoetherianSpace Y'] (L : LineBundleData Y) (ψ : Y' ⟶ Y)
    [IsOpenImmersion ψ] (dim : DimensionFunction Y) (dim' : DimensionFunction Y') (x' : Y')
    (aW : L.PullbackIndex ψ)
    (hj : (pointSubscheme (ψ.base x')).eta ∈ (L.U aW.1.1 : Y.Opens))
    (hj' : (pointSubscheme x').eta ∈ ((L.pullback ψ).U aW : Y'.Opens)) :
    AlgebraicCycle.pullbackOpen ψ
        ((⟨aW.1.1, hj, 1⟩ : L.RationalSection (pointSubscheme (ψ.base x'))).divisor dim) =
      (⟨aW, hj', 1⟩ : (L.pullback ψ).RationalSection (pointSubscheme x')).divisor dim' := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext Q'
  change ((⟨aW.1.1, hj, 1⟩ : L.RationalSection (pointSubscheme (ψ.base x'))).divisor dim :
    Y → ℚ) (ψ.base Q') =
    ((⟨aW, hj', 1⟩ : (L.pullback ψ).RationalSection (pointSubscheme x')).divisor dim' :
      Y' → ℚ) Q'
  have hx' : (pointSubscheme x').genericPointImage = x' := genericPointImage_pointSubscheme x'
  by_cases h' : x' ⤳ Q'
  · have h : ψ.base x' ⤳ ψ.base Q' := h'.map ψ.continuous
    obtain ⟨b, hb⟩ := L.covers (ψ.base Q')
    obtain ⟨W', hW', hQW', hW'le⟩ := Opens.isBasis_iff_nbhd.mp Y'.isBasis_affineOpens
      (show Q' ∈ ψ ⁻¹ᵁ (L.U b : Y.Opens) from hb)
    let bW : L.PullbackIndex ψ := ⟨(b, ⟨W', hW'⟩), hW'le⟩
    have hxa' : x' ∈ (aW.1.2 : Y'.Opens) := by
      rw [← hx']
      exact hj'
    have hxW' : x' ∈ W' := h'.mem_open W'.isOpen hQW'
    rw [L.divisor_frame_apply dim (ψ.base x') aW.1.1 b hj h hb ⟨hW'le hxW', aW.2 hxa'⟩,
      (L.pullback ψ).divisor_frame_apply dim' x' aW bW hj' h' hQW' ⟨hxW', hxa'⟩]
    have e := L.sectionResidueUnit_pullback_g ψ bW aW (y := x') ⟨hxW', hxa'⟩
    refine congrArg (fun z : ℤ ↦ (z : ℚ)) ?_
    exact (pointOrd_openImmersion ψ h' h _).trans (congrArg (pointOrd h') e.symm)
  · have h : ¬ ψ.base x' ⤳ ψ.base Q' := fun h ↦
      h' (ψ.isOpenEmbedding.isInducing.specializes_iff.mp h)
    rw [LineBundleData.RationalSection.divisor_apply_eq_zero_of_not_specializes _ _ h,
      LineBundleData.RationalSection.divisor_apply_eq_zero_of_not_specializes _ _ h']

end Restrict

/-! ## `c₁` commutes with open restriction -/

section Field

open LineBundleInjective RationalEquivalenceSystem.DescendingMap FiniteTypeDimension

/-- The source of an open immersion into a Noetherian space is a Noetherian space. -/
theorem noetherianSpace_of_isOpenImmersion {Y' Y : Scheme.{u}} (ψ : Y' ⟶ Y) [IsOpenImmersion ψ]
    [NoetherianSpace Y] : NoetherianSpace Y' :=
  ψ.isOpenEmbedding.isInducing.noetherianSpace

/-- **`c₁` commutes with open restriction, cycle level.**  Let `ψ : Y' ⟶ Y` be an open immersion
of locally Noetherian schemes with Noetherian underlying spaces, and `dim`, `dim'` dimension
functions with `dim' = dim ∘ ψ` satisfying `CovByDimension`.  Then for every line bundle `L` on
`Y`, restricting `c1Cycle L dim i` to `Y'` (on Chow classes) agrees with `c1Cycle` of the pulled
back line bundle `L.pullback ψ` applied to the restricted cycle. -/
theorem openImmersionPullback_comp_c1Cycle {Y' Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [NoetherianSpace Y] [IsLocallyNoetherian Y'] [NoetherianSpace Y'] (ψ : Y' ⟶ Y)
    [IsOpenImmersion ψ] (L : LineBundleData Y) {dim : DimensionFunction Y}
    {dim' : DimensionFunction Y'} (hdim : ∀ y, dim' y = dim (ψ.base y))
    (hcov : HomogeneityLocal.CovByDimension dim) (hcov' : HomogeneityLocal.CovByDimension dim')
    (i : ℤ) :
    (openImmersionPullback (chowSystem dim i) ψ hdim (chowSystem dim' i)).comp
        (c1Cycle L dim i) =
      (c1Cycle (L.pullback ψ) dim' i).comp (cyclesOfDimension.flatPullbackOpen ψ hdim) := by
  apply c1Cycle_ext
  intro x
  simp only [LinearMap.comp_apply]
  by_cases hx : dim x = i + 1
  · rw [cyclesOfDimension.pointProj_eq_point hx]
    obtain ⟨a, ha⟩ := L.covers x
    have hj : (pointSubscheme x).eta ∈ (L.U a : Y.Opens) := by
      change (pointSubscheme x).genericPointImage ∈ _
      rw [genericPointImage_pointSubscheme]
      exact ha
    rw [c1Cycle_single hcov hx ⟨a, hj, 1⟩, openImmersionPullback_quotientMap]
    by_cases hxr : x ∈ Set.range ψ.base
    · obtain ⟨x', rfl⟩ := hxr
      have hx' : dim' x' = i + 1 := (hdim x').trans hx
      have hpt : cyclesOfDimension.flatPullbackOpen ψ hdim
          (cyclesOfDimension.point (ψ.base x') hx) = cyclesOfDimension.point x' hx' := by
        apply Subtype.ext
        apply Function.locallyFinsuppWithin.coe_injective
        funext Q'
        change (cyclesOfDimension.point (ψ.base x') hx : AlgebraicCycle Y ℚ) (ψ.base Q') =
          (cyclesOfDimension.point x' hx' : AlgebraicCycle Y' ℚ) Q'
        by_cases hQ : Q' = x'
        · subst hQ
          rw [cyclesOfDimension.point_apply_self, cyclesOfDimension.point_apply_self]
        · rw [cyclesOfDimension.point_apply_of_ne _ _ _
            (fun h ↦ hQ (ψ.isOpenEmbedding.injective h)),
            cyclesOfDimension.point_apply_of_ne _ _ _ hQ]
      obtain ⟨W, hW, hxW, hWle⟩ := Opens.isBasis_iff_nbhd.mp Y'.isBasis_affineOpens
        (show x' ∈ ψ ⁻¹ᵁ (L.U a : Y.Opens) from ha)
      let aW : L.PullbackIndex ψ := ⟨(a, ⟨W, hW⟩), hWle⟩
      have hj' : (pointSubscheme x').eta ∈ ((L.pullback ψ).U aW : Y'.Opens) := by
        change (pointSubscheme x').genericPointImage ∈ W
        rw [genericPointImage_pointSubscheme]
        exact hxW
      rw [hpt, c1Cycle_single hcov' hx' ⟨aW, hj', 1⟩]
      congr 1
      apply Subtype.ext
      exact pullbackOpen_divisor_frame L ψ _ _ x' aW hj hj'
    · have hpt : cyclesOfDimension.flatPullbackOpen ψ hdim
          (cyclesOfDimension.point x hx) = 0 := by
        apply Subtype.ext
        apply Function.locallyFinsuppWithin.coe_injective
        funext Q'
        change (cyclesOfDimension.point x hx : AlgebraicCycle Y ℚ) (ψ.base Q') = 0
        exact cyclesOfDimension.point_apply_of_ne _ _ _ (fun h ↦ hxr ⟨Q', h⟩)
      rw [hpt, map_zero]
      refine (congrArg _ ?_).trans (map_zero _)
      apply Subtype.ext
      apply Function.locallyFinsuppWithin.coe_injective
      funext Q'
      change ((⟨a, hj, 1⟩ : L.RationalSection (pointSubscheme x)).divisor dim :
        Y → ℚ) (ψ.base Q') = 0
      exact LineBundleData.RationalSection.divisor_apply_eq_zero_of_not_specializes _ _
        (fun h ↦ hxr (h.mem_open ψ.isOpenEmbedding.isOpen_range ⟨Q', rfl⟩))
  · rw [cyclesOfDimension.pointProj_eq_zero_of_ne hx, map_zero, map_zero, map_zero, map_zero]

variable {k : Type u} [Field k] [Infinite k] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [NoetherianSpace Y] {Y' : Scheme.{u}} (ψ : Y' ⟶ Y)
  [IsOpenImmersion ψ]

/-- **The first Chern class commutes with restriction to an open subscheme** (blueprint A4).
For `Y` locally of finite type over an infinite field `k` with Noetherian underlying space, an
open immersion `ψ : Y' ⟶ Y` (with `Y'` given the canonical dimension function of `ψ ≫ f`) and a
line bundle `L` on `Y`: restricting `c₁(L) ∩ β` to `Y'` is `c₁(L.pullback ψ) ∩ (β|_{Y'})`, for
every `β ∈ A_{i+1}(Y)`. -/
theorem openImmersionPullback_firstChernClassOfField [NoetherianSpace Y'] (L : LineBundleData Y)
    (i : ℤ) (β : (haveI := LocallyOfFiniteType.isLocallyNoetherian f
      chowSystem (dimensionFunction f) (i + 1)).ChowGroup) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian f
    haveI := LocallyOfFiniteType.isLocallyNoetherian (ψ ≫ f)
    openImmersionPullback (chowSystem (dimensionFunction f) i) ψ
        (fun y ↦ dimensionFunction_comp f ψ y) (chowSystem (dimensionFunction (ψ ≫ f)) i)
        (firstChernClassOfField f L i β) =
      firstChernClassOfField (ψ ≫ f) (L.pullback ψ) i
        (openImmersionPullback (chowSystem (dimensionFunction f) (i + 1)) ψ
          (fun y ↦ dimensionFunction_comp f ψ y)
          (chowSystem (dimensionFunction (ψ ≫ f)) (i + 1)) β) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := LocallyOfFiniteType.isLocallyNoetherian (ψ ≫ f)
  obtain ⟨α, rfl⟩ := Submodule.mkQ_surjective _ β
  have hdim : ∀ y, dimensionFunction (ψ ≫ f) y = dimensionFunction f (ψ.base y) :=
    fun y ↦ dimensionFunction_comp f ψ y
  unfold firstChernClassOfField
  rw [firstChernClass_quotientMap, openImmersionPullback_quotientMap,
    firstChernClass_quotientMap]
  exact LinearMap.congr_fun (openImmersionPullback_comp_c1Cycle ψ L hdim
    (covByDimension_finiteTypeDimension f) (covByDimension_finiteTypeDimension (ψ ≫ f)) i) α

end Field

end GromovWitten.AlgebraicGeometry.IntersectionTheory
