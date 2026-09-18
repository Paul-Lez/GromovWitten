/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroupLocalization

/-!
# Exactness of the localization sequence in the middle

`ChowGroupLocalization.lean` constructs the flat pullback `A_i(X) → A_i(U)` along an open
immersion, proves that it is surjective, and proves that its composite with the pushforward
`A_i(Y) → A_i(X)` along a closed immersion with image in the complement of `U` vanishes.  This
file supplies the remaining exactness statement in the middle (Fulton, *Intersection Theory*,
Proposition 1.8): every dimension-`i` class restricting to zero on `U` comes from the complement.

## Main results

* `AlgebraicCycle.pullbackClosed` and `AlgebraicCycle.map_pullbackClosed`: a rational cycle
  vanishing off the image of a closed immersion is the pushforward of its restriction;
  `cyclesOfDimension.properPushforward_pullbackClosed` is the dimension-graded form.  This is the
  step "cycles supported on `Y` come from `Y`", proved unconditionally.
* `IntegralClosedSubscheme.closureIn`: the closure in `X` of an integral closed subscheme of an
  open subscheme `V`, constructed as the scheme-theoretic image of `Z → V → X`.  It is an
  integral closed subscheme (`isIntegral_image`, `isLocallyNoetherian_image`) and `Z` is exactly
  its trace on `V` (`isIso_traceLift`, `isOpenImmersion_toImage`, `mem_range_toImage`).
* `RationalFunctionGenerator.closureIn` and `pullbackOpen_divisor_closureIn`: the closure of a
  principal-divisor generator, whose principal divisor restricts to the given one on `V`.
* `totalRationalRelations_le_map_pullbackOpen`: on a Noetherian scheme every principal-divisor
  relation on an open subscheme is the restriction of a relation on the ambient scheme.  This is
  the closure step of Fulton's proof, proved unconditionally.
* `RationalEquivalenceSystem.DescendingMap.ker_openImmersionPullback_le_range` and its Noetherian
  and homogeneous specialisations: exactness in the middle of the localization sequence.
* `RationalEquivalenceSystem.DescendingMap.ker_openImmersionPullback_eq_range_of_homogeneous`:
  the exactness statement as an equality of the kernel and the image.
* `RationalEquivalenceSystem.DescendingMap.openImmersionPullback_bijective_of_forall_ne`: if the
  closed complement carries no point in dimension `i`, restriction is an isomorphism of rational
  Chow groups.

## The remaining input: gradedness of the span of principal divisors

`ChowGroup.lean` deliberately defines `totalRationalRelations` as the span of *all* principal
divisors without any grading assumption, because the principal divisor of a rational function on
an integral closed subscheme `W` is concentrated in the single dimension `dim W - 1` only when
`W` is catenary and equidimensional; Mathlib has no such statement for general schemes, and the
repository consistently avoids assuming it.  Exactness in the middle needs the dimension-`i` part
of a relation to be a relation again, because the class of the difference `α - γ` of a graded
cycle and a relation has to be represented by a graded cycle.  This is the hypothesis

* `hproject : ∀ c ∈ totalRationalRelations X dimensionX, project c ∈ totalRationalRelations X
  dimensionX`

of `ker_openImmersionPullback_le_range`.  It is implied by the geometric homogeneity statement
`PrincipalDivisorsHomogeneous X dimensionX` (every principal divisor is concentrated in one
dimension), see `project_mem_totalRationalRelations_of_homogeneous`; the theorems ending in
`_of_homogeneous` take that form of the hypothesis.  Everything else in this file, in particular
the closure construction, is proved unconditionally.
-/
open CategoryTheory TopologicalSpace Topology Order

open scoped AlgebraicGeometry


namespace AlgebraicGeometry.Scheme

universe u

/-! ## Closed immersions with dense image, and function fields of open immersions -/

/-- A closed immersion into a reduced scheme whose image is dense is an isomorphism.  The kernel
ideal sheaf has full support, and on a reduced scheme the only such ideal sheaf is zero. -/
lemma isIso_of_isClosedImmersion_of_denseRange {A B : Scheme.{u}} (u : A ⟶ B)
    [IsClosedImmersion u] [IsReduced B] (hu : DenseRange u.base) : IsIso u := by
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot, ← IdealSheafData.support_eq_top_iff]
  apply SetLike.ext'
  rw [Hom.support_ker]
  simp [hu.closure_range]

/-- The function-field map of a dominant open immersion of integral schemes is bijective: it is
the stalk map at the generic point, which is an isomorphism for an open immersion. -/
lemma bijective_dominantFunctionFieldMap_of_isOpenImmersion {A B : Scheme.{u}}
    [IsIntegral A] [IsIntegral B] (f : A ⟶ B) [IsOpenImmersion f] [IsDominant f] :
    Function.Bijective (dominantFunctionFieldMap f) := by
  have hiso : IsIso ((eqToHom (congrArg (fun z ↦ B.presheaf.stalk z)
      (map_genericPoint_of_isDominant f).symm) :
      B.presheaf.stalk (genericPoint B) ⟶
        B.presheaf.stalk (f.base (genericPoint A))) ≫ f.stalkMap (genericPoint A)) :=
    IsIso.comp_isIso' inferInstance inferInstance
  exact (ConcreteCategory.bijective_of_isIso _)

/-- The canonical function-field isomorphism of a dominant open immersion of integral
schemes. -/
noncomputable def dominantFunctionFieldEquiv {A B : Scheme.{u}}
    [IsIntegral A] [IsIntegral B] (f : A ⟶ B) [IsOpenImmersion f] [IsDominant f] :
    B.functionField ≃+* A.functionField :=
  RingEquiv.ofBijective (dominantFunctionFieldMap f)
    (bijective_dominantFunctionFieldMap_of_isOpenImmersion f)

@[simp]
lemma dominantFunctionFieldEquiv_apply {A B : Scheme.{u}}
    [IsIntegral A] [IsIntegral B] (f : A ⟶ B) [IsOpenImmersion f] [IsDominant f]
    (q : B.functionField) :
    dominantFunctionFieldEquiv f q = dominantFunctionFieldMap f q :=
  rfl

/-! ## The scheme-theoretic image as a closed subscheme -/

section Image

variable {A X : Scheme.{u}} (f : A ⟶ X) [QuasiCompact f]

/-- The scheme-theoretic image of a quasi-compact morphism from a reduced scheme is reduced: on
every affine open of the target its ring of sections is the quotient by an actual kernel. -/
lemma isReduced_image [IsReduced A] : IsReduced f.image := by
  have hcov : ∀ U : X.affineOpens,
      IsReduced (Spec (CommRingCat.of (Γ(X, U.1) ⧸ f.ker.ideal U))) := by
    intro U
    have hq : _root_.IsReduced (CommRingCat.of (Γ(X, U.1) ⧸ f.ker.ideal U)) := by
      dsimp
      refine (Ideal.isRadical_iff_quotient_reduced _).mp ?_
      rw [Scheme.Hom.ker_apply]
      rintro x ⟨n, hn⟩
      rw [RingHom.mem_ker] at hn ⊢
      have hnil : IsNilpotent ((f.app U.1).hom x) := ⟨n, by rw [← map_pow]; exact hn⟩
      exact hnil.eq_zero
    infer_instance
  have hcov' : ∀ U, IsReduced (f.ker.subschemeCover.openCover.X U) := hcov
  exact IsReduced.of_openCover _ f.ker.subschemeCover.openCover

omit [QuasiCompact f] in
/-- The scheme-theoretic image of a morphism into a locally Noetherian scheme is locally
Noetherian. -/
lemma isLocallyNoetherian_image [IsLocallyNoetherian X] : IsLocallyNoetherian f.image := by
  have hcov : ∀ U : X.affineOpens,
      IsLocallyNoetherian (Spec (CommRingCat.of (Γ(X, U.1) ⧸ f.ker.ideal U))) := by
    intro U
    have h : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    have hq : IsNoetherianRing (CommRingCat.of (Γ(X, U.1) ⧸ f.ker.ideal U)) := by
      dsimp
      infer_instance
    infer_instance
  have hcov' : ∀ U, IsLocallyNoetherian (f.ker.subschemeCover.openCover.X U) := hcov
  exact (isLocallyNoetherian_iff_openCover f.ker.subschemeCover.openCover).mpr hcov'

/-- The scheme-theoretic image of a quasi-compact morphism from an irreducible scheme is
irreducible: the morphism to the image has dense range. -/
lemma irreducibleSpace_image [IrreducibleSpace A] : IrreducibleSpace f.image := by
  rw [irreducibleSpace_def]
  have h : IsIrreducible (Set.range f.toImage.base) := by
    have h0 := (IrreducibleSpace.isIrreducible_univ A).image f.toImage.base
      f.toImage.continuous.continuousOn
    rwa [Set.image_univ] at h0
  have hclosed := h.closure
  rw [f.toImage.denseRange.closure_range] at hclosed
  rwa [Set.top_eq_univ]

end Image

end AlgebraicGeometry.Scheme

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

namespace AlgebraicCycle

variable {W X : Scheme.{u}}

/-! ## Restriction of cycles along a closed immersion -/

/-- Restriction of a rational algebraic cycle along a closed immersion: the coefficient function
is composed with the closed embedding.  Local finiteness is inherited because the embedding is
continuous and injective. -/
noncomputable def pullbackClosed (f : W ⟶ X)
    [_root_.AlgebraicGeometry.IsClosedImmersion f] (c : AlgebraicCycle X ℚ) :
    AlgebraicCycle W ℚ where
  toFun w := c (f.base w)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' w _ := by
    obtain ⟨t, ht, hfinite⟩ := c.supportLocallyFiniteWithinDomain (f.base w) (by trivial)
    refine ⟨f.base ⁻¹' t, f.continuous.continuousAt.preimage_mem_nhds ht, ?_⟩
    apply Set.Finite.of_finite_image (f := f.base) (hfinite.subset ?_)
    · exact f.isClosedEmbedding.injective.injOn
    · rintro y ⟨z, hz, rfl⟩
      exact ⟨hz.1, hz.2⟩

@[simp]
lemma pullbackClosed_apply (f : W ⟶ X) [_root_.AlgebraicGeometry.IsClosedImmersion f]
    (c : AlgebraicCycle X ℚ) (w : W) : pullbackClosed f c w = c (f.base w) :=
  rfl

/-- A rational cycle which vanishes outside the image of a closed immersion is the
residue-degree pushforward of its restriction.  Both the statement and the proof use the
pulled-back weight, for which all pushforward multiplicities are one. -/
lemma map_pullbackClosed (f : W ⟶ X) [_root_.AlgebraicGeometry.IsClosedImmersion f]
    (wX : X → ℤ) (c : AlgebraicCycle X ℚ)
    (hc : ∀ x, x ∉ Set.range f.base → c x = 0) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map f (fun w ↦ wX (f.base w)) wX
      (pullbackClosed f c) = c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  by_cases hx : x ∈ Set.range f.base
  · obtain ⟨w, rfl⟩ := hx
    exact map_closedImmersion_apply_image f wX (pullbackClosed f c) w
  · exact (map_closedImmersion_apply_of_not_mem_range f wX _ x hx).trans (hc x hx).symm

end AlgebraicCycle

/-! ## The dimension-graded restriction along a closed immersion -/

namespace cyclesOfDimension

variable {W X : Scheme.{u}} {dimensionW : DimensionFunction W}
  {dimensionX : DimensionFunction X} {i : ℤ}

/-- Restriction of a dimension-graded rational cycle along a closed immersion.  No hypothesis is
needed: a closed immersion preserves the certified dimension of every point. -/
noncomputable def pullbackClosed (f : W ⟶ X)
    [_root_.AlgebraicGeometry.IsClosedImmersion f] (z : cyclesOfDimension X dimensionX i) :
    cyclesOfDimension W dimensionW i :=
  ⟨AlgebraicCycle.pullbackClosed f z.1, by
    intro w hw
    refine z.2 (f.base w) ?_
    rw [← DimensionFunction.apply_eq_of_isClosedImmersion dimensionW dimensionX f w]
    exact hw⟩

@[simp]
lemma pullbackClosed_apply (f : W ⟶ X) [_root_.AlgebraicGeometry.IsClosedImmersion f]
    (z : cyclesOfDimension X dimensionX i) (w : W) :
    ((pullbackClosed (dimensionW := dimensionW) f z : cyclesOfDimension W dimensionW i) :
        AlgebraicCycle W ℚ) w = (z : AlgebraicCycle X ℚ) (f.base w) :=
  rfl

/-- A dimension-graded cycle vanishing outside a closed subscheme is the proper pushforward of
its restriction to that closed subscheme. -/
theorem properPushforward_pullbackClosed (f : W ⟶ X)
    [_root_.AlgebraicGeometry.IsClosedImmersion f] (z : cyclesOfDimension X dimensionX i)
    (hz : ∀ x, x ∉ Set.range f.base → (z : AlgebraicCycle X ℚ) x = 0) :
    properPushforward (dimension := dimensionW) (dimensionY := dimensionX) (i := i) f
      (pullbackClosed f z) = z := by
  apply Subtype.ext
  change _root_.AlgebraicGeometry.AlgebraicCycle.map f dimensionW dimensionX
    (AlgebraicCycle.pullbackClosed f z.1) = z.1
  have hw : (dimensionW : W → ℤ) = fun w ↦ (dimensionX : X → ℤ) (f.base w) := by
    funext w
    exact DimensionFunction.apply_eq_of_isClosedImmersion dimensionW dimensionX f w
  rw [hw]
  exact AlgebraicCycle.map_pullbackClosed f dimensionX z.1 hz

end cyclesOfDimension

/-! ## Elementary properties of the dimension-`i` projection -/

namespace cyclesOfDimension

variable {X : Scheme.{u}} {dimensionX : DimensionFunction X} {i : ℤ}

/-- Projecting a cycle which is already concentrated in dimension `i` changes nothing. -/
@[simp]
theorem project_coe (z : cyclesOfDimension X dimensionX i) :
    project (dimension := dimensionX) (i := i) (z : AlgebraicCycle X ℚ) = z := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  simp only [project_apply]
  by_cases hx : dimensionX x = i
  · rw [if_pos hx]
  · rw [if_neg hx, z.2 x hx]

/-- The dimension-`i` projection is additive. -/
theorem project_add (c d : AlgebraicCycle X ℚ) :
    (project (dimension := dimensionX) (i := i) (c + d) : AlgebraicCycle X ℚ) =
      (project (dimension := dimensionX) (i := i) c : AlgebraicCycle X ℚ) +
        (project (dimension := dimensionX) (i := i) d : AlgebraicCycle X ℚ) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  by_cases hx : dimensionX x = i <;> simp [project_apply, hx]

/-- The dimension-`i` projection commutes with rational scalars. -/
theorem project_smul (q : ℚ) (c : AlgebraicCycle X ℚ) :
    (project (dimension := dimensionX) (i := i) (q • c) : AlgebraicCycle X ℚ) =
      q • (project (dimension := dimensionX) (i := i) c : AlgebraicCycle X ℚ) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  by_cases hx : dimensionX x = i <;> simp [project_apply, hx]

/-- The dimension-`i` projection of the zero cycle vanishes. -/
@[simp]
theorem project_zero :
    (project (dimension := dimensionX) (i := i) 0 : AlgebraicCycle X ℚ) = 0 := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  by_cases hx : dimensionX x = i <;> simp [project_apply, hx]

end cyclesOfDimension

/-! ## Homogeneity of principal divisors -/

/-- All principal divisors on `X` are homogeneous for the certified dimension grading: the
divisor of every rational function on every integral closed subscheme is concentrated in a single
dimension.  For a catenary equidimensional scheme this is the usual statement that a Weil divisor
on an integral closed subscheme `W` lives in dimension `dim W - 1`; Mathlib has no such statement
for general schemes, which is why `totalRationalRelations` is defined without a grading. -/
def PrincipalDivisorsHomogeneous (X : Scheme.{u}) (dimension : DimensionFunction X) : Prop :=
  ∀ g : RationalFunctionGenerator X, ∃ d : ℤ,
    ∀ x : X, g.divisor dimension x ≠ 0 → dimension x = d

/-- If all principal divisors are homogeneous then the canonical span of principal divisors is
graded: the dimension-`i` part of a relation is again a relation. -/
theorem project_mem_totalRationalRelations_of_homogeneous {X : Scheme.{u}}
    {dimension : DimensionFunction X} {i : ℤ}
    (hhom : PrincipalDivisorsHomogeneous X dimension)
    (c : AlgebraicCycle X ℚ) (hc : c ∈ totalRationalRelations X dimension) :
    (cyclesOfDimension.project (dimension := dimension) (i := i) c : AlgebraicCycle X ℚ) ∈
      totalRationalRelations X dimension := by
  induction hc using Submodule.span_induction with
  | mem d hd =>
      obtain ⟨g, rfl⟩ := hd
      obtain ⟨e, he⟩ := hhom g
      by_cases hei : e = i
      · have hproj : (cyclesOfDimension.project (dimension := dimension) (i := i)
            (g.divisor dimension) : AlgebraicCycle X ℚ) = g.divisor dimension := by
          apply Function.locallyFinsuppWithin.coe_injective
          funext x
          simp only [cyclesOfDimension.project_apply]
          by_cases hx : dimension x = i
          · rw [if_pos hx]
          · rw [if_neg hx]
            by_contra hne
            exact hx ((he x fun h ↦ hne h.symm).trans hei)
        rw [hproj]
        exact Submodule.subset_span (Set.mem_range_self g)
      · have hproj : (cyclesOfDimension.project (dimension := dimension) (i := i)
            (g.divisor dimension) : AlgebraicCycle X ℚ) = 0 := by
          apply Function.locallyFinsuppWithin.coe_injective
          funext x
          simp only [cyclesOfDimension.project_apply]
          by_cases hx : dimension x = i
          · rw [if_pos hx]
            by_contra hne
            exact hei ((he x hne).symm.trans hx)
          · rw [if_neg hx]
            rfl
        rw [hproj]
        exact Submodule.zero_mem _
  | zero =>
      rw [cyclesOfDimension.project_zero]
      exact Submodule.zero_mem _
  | add c d _ _ hc hd =>
      rw [cyclesOfDimension.project_add]
      exact Submodule.add_mem _ hc hd
  | smul q c _ hc =>
      rw [cyclesOfDimension.project_smul]
      exact Submodule.smul_mem _ q hc


/-! ## The closure of an integral closed subscheme of an open subscheme -/

/-- On a Noetherian scheme the inclusion of an open subscheme is quasi-compact: every subset of a
Noetherian space is compact. -/
instance quasiCompact_opens_ι {X : Scheme.{u}} [NoetherianSpace X] (V : X.Opens) :
    _root_.AlgebraicGeometry.QuasiCompact V.ι := by
  constructor
  intro U _ _
  have hnoeth : NoetherianSpace V.toScheme := NoetherianSpace.set _
  exact NoetherianSpace.isCompact _

namespace IntegralClosedSubscheme

variable {X : Scheme.{u}} (V : X.Opens) (Z : IntegralClosedSubscheme V.toScheme)

/-- The canonical morphism from `Z` to the scheme-theoretic image of `Z → V → X` lands over
`V`. -/
lemma range_toImage_subset :
    Set.range ((Z.inclusion ≫ V.ι).toImage).base ⊆
      Set.range ((Z.inclusion ≫ V.ι).imageι ⁻¹ᵁ V).ι.base := by
  rintro _ ⟨a, rfl⟩
  rw [_root_.AlgebraicGeometry.Scheme.Opens.range_ι]
  change (Z.inclusion ≫ V.ι).imageι.base ((Z.inclusion ≫ V.ι).toImage.base a) ∈ V
  rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply,
    _root_.AlgebraicGeometry.Scheme.Hom.toImage_imageι,
    _root_.AlgebraicGeometry.Scheme.Hom.comp_apply]
  exact (Z.inclusion.base a).2

/-- The comparison morphism from `Z` to the trace on `V` of the scheme-theoretic image. -/
noncomputable def traceLift :
    Z.scheme ⟶ ((Z.inclusion ≫ V.ι).imageι ⁻¹ᵁ V).toScheme :=
  _root_.AlgebraicGeometry.IsOpenImmersion.lift _ _ (range_toImage_subset V Z)

/-- The comparison morphism composed with the open immersion is the canonical morphism to the
scheme-theoretic image. -/
@[reassoc (attr := simp)]
lemma traceLift_fac :
    traceLift V Z ≫ ((Z.inclusion ≫ V.ι).imageι ⁻¹ᵁ V).ι = (Z.inclusion ≫ V.ι).toImage :=
  _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _

variable [_root_.AlgebraicGeometry.QuasiCompact (Z.inclusion ≫ V.ι)]

/-- The scheme-theoretic image of `Z → V → X` is integral: it is reduced because `Z` is, and
irreducible because `Z` has dense image in it. -/
instance isIntegral_image :
    _root_.AlgebraicGeometry.IsIntegral ((Z.inclusion ≫ V.ι).image) :=
  have _h1 : _root_.AlgebraicGeometry.IsReduced ((Z.inclusion ≫ V.ι).image) :=
    _root_.AlgebraicGeometry.Scheme.isReduced_image _
  have _h2 : IrreducibleSpace ((Z.inclusion ≫ V.ι).image) :=
    _root_.AlgebraicGeometry.Scheme.irreducibleSpace_image _
  _root_.AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced _

/-- The scheme-theoretic image of `Z → V → X` is locally Noetherian when `X` is. -/
instance isLocallyNoetherian_image
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X] :
    _root_.AlgebraicGeometry.IsLocallyNoetherian ((Z.inclusion ≫ V.ι).image) :=
  _root_.AlgebraicGeometry.Scheme.isLocallyNoetherian_image _

/-- The closure in `X` of an integral closed subscheme of an open subscheme `V`: the
scheme-theoretic image of the composite `Z → V → X`.  It is an integral closed subscheme of `X`
whose underlying closed set is the closure of the image of `Z`. -/
noncomputable def closureIn [_root_.AlgebraicGeometry.IsLocallyNoetherian X] :
    IntegralClosedSubscheme X where
  scheme := (Z.inclusion ≫ V.ι).image
  inclusion := (Z.inclusion ≫ V.ι).imageι

/-- The underlying scheme of the closure is the scheme-theoretic image. -/
@[simp]
lemma closureIn_scheme [_root_.AlgebraicGeometry.IsLocallyNoetherian X] :
    (Z.closureIn V).scheme = (Z.inclusion ≫ V.ι).image :=
  rfl

/-- The closed immersion of the closure is the one of the scheme-theoretic image. -/
@[simp]
lemma closureIn_inclusion [_root_.AlgebraicGeometry.IsLocallyNoetherian X] :
    (Z.closureIn V).inclusion = (Z.inclusion ≫ V.ι).imageι :=
  rfl

/-- The comparison morphism is an isomorphism: it is a closed immersion with dense image into a
reduced scheme.  This is the statement that `Z` is the trace on `V` of its closure. -/
instance isIso_traceLift : IsIso (traceLift V Z) := by
  have hcomp : traceLift V Z ≫ ((Z.inclusion ≫ V.ι).imageι ∣_ V) = Z.inclusion := by
    rw [← cancel_mono V.ι, Category.assoc, _root_.AlgebraicGeometry.morphismRestrict_ι,
      ← Category.assoc, traceLift_fac, _root_.AlgebraicGeometry.Scheme.Hom.toImage_imageι]
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
      (traceLift V Z ≫ ((Z.inclusion ≫ V.ι).imageι ∣_ V)) := by
    rw [hcomp]
    infer_instance
  have h2 : _root_.AlgebraicGeometry.IsClosedImmersion (traceLift V Z) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.of_comp_isClosedImmersion _
      ((Z.inclusion ≫ V.ι).imageι ∣_ V)
  have hdense : DenseRange (traceLift V Z).base := by
    rw [denseRange_iff_closure_range,
      ((Z.inclusion ≫ V.ι).imageι ⁻¹ᵁ V).ι.isEmbedding.isInducing.closure_eq_preimage_closure_image]
    have himg : ((Z.inclusion ≫ V.ι).imageι ⁻¹ᵁ V).ι.base '' Set.range (traceLift V Z).base =
        Set.range ((Z.inclusion ≫ V.ι).toImage).base := by
      rw [← Set.range_comp, ← traceLift_fac V Z]
      rfl
    rw [himg, ((Z.inclusion ≫ V.ι).toImage).denseRange.closure_range, Set.preimage_univ]
  exact _root_.AlgebraicGeometry.Scheme.isIso_of_isClosedImmersion_of_denseRange _ hdense

/-- The canonical morphism from `Z` to its closure is an open immersion. -/
instance isOpenImmersion_toImage :
    _root_.AlgebraicGeometry.IsOpenImmersion ((Z.inclusion ≫ V.ι).toImage) := by
  rw [← traceLift_fac V Z]
  infer_instance

/-- Every point of the closure of `Z` lying over `V` is in the image of `Z`. -/
lemma mem_range_toImage (y : (Z.inclusion ≫ V.ι).image)
    (hy : (Z.inclusion ≫ V.ι).imageι.base y ∈ V) :
    y ∈ Set.range ((Z.inclusion ≫ V.ι).toImage).base := by
  have hsurj : Function.Surjective (traceLift V Z).base := fun t ↦
    ⟨(inv (traceLift V Z)).base t, by
      rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl⟩
  obtain ⟨z, hz⟩ := hsurj ⟨y, hy⟩
  refine ⟨z, ?_⟩
  rw [← traceLift_fac V Z, _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, hz]
  rfl

end IntegralClosedSubscheme

namespace RationalFunctionGenerator

/-! ### Comparison of principal divisors along a closure -/

variable {X : Scheme.{u}} (V : X.Opens)

/-- Flat pullback to an open subscheme carries the principal divisor of a generator `G` on `X` to
the principal divisor of a generator `g` on `V`, provided that the integral closed subscheme of
`g` is identified with the trace on `V` of the one of `G` by an open immersion `w` which is
dominant, compatible with the two closed immersions, and surjective over `V`, and provided that
the two rational functions correspond under `w`.  This is the geometric content of the closure
step in Fulton's proof of exactness of the localization sequence. -/
theorem pullbackOpen_divisor_of_closure (G : RationalFunctionGenerator X)
    (g : RationalFunctionGenerator V.toScheme)
    (w : g.subspace.scheme ⟶ G.subspace.scheme)
    [_root_.AlgebraicGeometry.IsOpenImmersion w] [_root_.AlgebraicGeometry.IsDominant w]
    (hfac : w ≫ G.subspace.inclusion = g.subspace.inclusion ≫ V.ι)
    (hsurj : ∀ y : G.subspace.scheme, G.subspace.inclusion.base y ∈ V →
      y ∈ Set.range w.base)
    (hfun : _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap w
        (G.function : G.subspace.scheme.functionField) =
      (g.function : g.subspace.scheme.functionField))
    (dimensionX : DimensionFunction X) (dimensionV : DimensionFunction V.toScheme) :
    AlgebraicCycle.pullbackOpen V.ι (G.divisor dimensionX) = g.divisor dimensionV := by
  have hpt : ∀ z : g.subspace.scheme,
      V.ι.base (g.subspace.inclusion.base z) = G.subspace.inclusion.base (w.base z) :=
    fun z ↦ congrArg (fun m : g.subspace.scheme ⟶ X ↦ m.base z) hfac.symm
  apply Function.locallyFinsuppWithin.ext
  intro v
  rw [AlgebraicCycle.pullbackOpen_apply]
  unfold divisor IntegralClosedSubscheme.pushforward
  by_cases hv : v ∈ Set.range g.subspace.inclusion.base
  · obtain ⟨z, rfl⟩ := hv
    rw [hpt z, AlgebraicCycle.map_closedImmersion_apply_image,
      AlgebraicCycle.map_closedImmersion_apply_image,
      _root_.AlgebraicGeometry.Scheme.principalCycle_apply,
      _root_.AlgebraicGeometry.Scheme.principalCycle_apply, ← hfun,
      _root_.AlgebraicGeometry.Scheme.ord_dominantFunctionFieldMap_of_isOpenImmersion w z]
  · have hnot : V.ι.base v ∉ Set.range G.subspace.inclusion.base := by
      rintro ⟨y, hy⟩
      have hyV : G.subspace.inclusion.base y ∈ V := by
        rw [hy]
        exact v.2
      obtain ⟨z, hz⟩ := hsurj y hyV
      refine hv ⟨z, ?_⟩
      apply V.ι.isOpenEmbedding.injective
      rw [hpt z, hz, hy]
    rw [AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range _ _ _ _ hnot,
      AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range _ _ _ _ hv]

variable (g : RationalFunctionGenerator V.toScheme)
  [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
  [_root_.AlgebraicGeometry.QuasiCompact (g.subspace.inclusion ≫ V.ι)]

/-- The closure in `X` of a principal-divisor generator on an open subscheme: the closure of its
integral closed subscheme, together with the rational function transported along the canonical
function-field isomorphism of the dominant open immersion from `Z` into its closure. -/
noncomputable def closureIn : RationalFunctionGenerator X where
  subspace := g.subspace.closureIn V
  function := Units.map
    (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldEquiv
        ((g.subspace.inclusion ≫ V.ι).toImage)).symm.toRingHom.toMonoidHom g.function

/-- The integral closed subscheme of the closure of a generator is the closure of its integral
closed subscheme. -/
@[simp]
lemma closureIn_subspace : (g.closureIn V).subspace = g.subspace.closureIn V :=
  rfl

/-- The rational function of the closure of a generator restricts to the original rational
function. -/
lemma dominantFunctionFieldMap_closureIn_function :
    _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap
        ((g.subspace.inclusion ≫ V.ι).toImage)
        ((g.closureIn V).function : (g.closureIn V).subspace.scheme.functionField) =
      (g.function : g.subspace.scheme.functionField) :=
  RingEquiv.apply_symm_apply
    (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldEquiv
      ((g.subspace.inclusion ≫ V.ι).toImage)) _

/-- Flat pullback to an open subscheme carries the principal divisor of the closure of a
generator to the principal divisor of the generator. -/
theorem pullbackOpen_divisor_closureIn
    (dimensionX : DimensionFunction X) (dimensionV : DimensionFunction V.toScheme) :
    AlgebraicCycle.pullbackOpen V.ι ((g.closureIn V).divisor dimensionX) =
      g.divisor dimensionV := by
  have hoi : @_root_.AlgebraicGeometry.IsOpenImmersion g.subspace.scheme
      (g.closureIn V).subspace.scheme ((g.subspace.inclusion ≫ V.ι).toImage) :=
    IntegralClosedSubscheme.isOpenImmersion_toImage V g.subspace
  have hdom : @_root_.AlgebraicGeometry.IsDominant g.subspace.scheme
      (g.closureIn V).subspace.scheme ((g.subspace.inclusion ≫ V.ι).toImage) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsDominant
      ((g.subspace.inclusion ≫ V.ι).toImage))
  exact pullbackOpen_divisor_of_closure V (g.closureIn V) g
    ((g.subspace.inclusion ≫ V.ι).toImage)
    (_root_.AlgebraicGeometry.Scheme.Hom.toImage_imageι _)
    (fun y hy ↦ IntegralClosedSubscheme.mem_range_toImage V g.subspace y hy)
    (dominantFunctionFieldMap_closureIn_function V g) dimensionX dimensionV

end RationalFunctionGenerator

/-- Every principal-divisor relation on an open subscheme of a Noetherian scheme is the
restriction of a principal-divisor relation on the ambient scheme.  This is the closure step of
Fulton's proof, and it is the hypothesis `hrestrict` of the exactness theorem. -/
theorem totalRationalRelations_le_map_pullbackOpen {X : Scheme.{u}} [NoetherianSpace X]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X] (V : X.Opens)
    (dimensionX : DimensionFunction X) (dimensionV : DimensionFunction V.toScheme) :
    totalRationalRelations V.toScheme dimensionV ≤
      Submodule.map (AlgebraicCycle.pullbackOpenLinear V.ι)
        (totalRationalRelations X dimensionX) := by
  rw [totalRationalRelations, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  exact ⟨(g.closureIn V).divisor dimensionX, Submodule.subset_span (Set.mem_range_self _),
    g.pullbackOpen_divisor_closureIn V dimensionX dimensionV⟩

/-! ## Exactness of the localization sequence in the middle -/

namespace RationalEquivalenceSystem

namespace DescendingMap

variable {X : Scheme.{u}} {dimensionX : DimensionFunction X} {i : ℤ}

/-- Exactness of the localization sequence at `A_i(X)`: every dimension-`i` rational Chow class
whose restriction to the open subscheme `V` vanishes is pushed forward from a closed subscheme
covering the complement of `V`.

The two hypotheses are the geometric inputs discussed in the module docstring: `hrestrict` says
that every principal-divisor relation on `V` extends to a relation on `X` (proved below for a
Noetherian `X`), and `hproject` says that the canonical span of principal divisors is graded (it
follows from homogeneity of principal divisors, see
`project_mem_totalRationalRelations_of_homogeneous`). -/
theorem ker_openImmersionPullback_le_range
    (R : RationalEquivalenceSystem X dimensionX i) (V : X.Opens)
    {dimensionV : DimensionFunction V.toScheme}
    (S : RationalEquivalenceSystem V.toScheme dimensionV i)
    (hdim : ∀ v, dimensionV v = dimensionX (V.ι.base v))
    {W : Scheme.{u}} {dimensionW : DimensionFunction W}
    (Q : RationalEquivalenceSystem W dimensionW i)
    (f : W ⟶ X) [_root_.AlgebraicGeometry.IsClosedImmersion f]
    (hrange : ∀ x : X, x ∉ V → x ∈ Set.range f.base)
    (hrestrict : totalRationalRelations V.toScheme dimensionV ≤
      Submodule.map (AlgebraicCycle.pullbackOpenLinear V.ι)
        (totalRationalRelations X dimensionX))
    (hproject : ∀ c ∈ totalRationalRelations X dimensionX,
      (cyclesOfDimension.project (dimension := dimensionX) (i := i) c : AlgebraicCycle X ℚ) ∈
        totalRationalRelations X dimensionX) :
    LinearMap.ker (openImmersionPullback R V.ι hdim S) ≤
      LinearMap.range (closedImmersionPushforward Q f R) := by
  rintro ⟨z⟩ hc
  have hc' : S.quotientMap (cyclesOfDimension.flatPullbackOpen V.ι hdim z) = 0 := hc
  have hmem : AlgebraicCycle.pullbackOpen V.ι (z : AlgebraicCycle X ℚ) ∈
      totalRationalRelations V.toScheme dimensionV := by
    have h0 : cyclesOfDimension.flatPullbackOpen (i := i) V.ι hdim z ∈ S.relations :=
      (Submodule.Quotient.mk_eq_zero _).mp hc'
    cases S
    exact h0
  obtain ⟨γ, hγmem, hγeq⟩ := hrestrict hmem
  have hδ : ∀ x : X, x ∉ Set.range f.base →
      ((z - cyclesOfDimension.project (dimension := dimensionX) (i := i) γ :
        cyclesOfDimension X dimensionX i) : AlgebraicCycle X ℚ) x = 0 := by
    intro x hx
    have hxV : x ∈ V := by
      by_contra h
      exact hx (hrange x h)
    have hval : γ x = (z : AlgebraicCycle X ℚ) x := by
      have hcongr : AlgebraicCycle.pullbackOpen V.ι γ (⟨x, hxV⟩ : V.toScheme) =
          AlgebraicCycle.pullbackOpen V.ι (z : AlgebraicCycle X ℚ) (⟨x, hxV⟩ : V.toScheme) :=
        congrArg (fun c : AlgebraicCycle V.toScheme ℚ ↦ c (⟨x, hxV⟩ : V.toScheme)) hγeq
      exact hcongr
    have hcoe : ((z - cyclesOfDimension.project (dimension := dimensionX) (i := i) γ :
          cyclesOfDimension X dimensionX i) : AlgebraicCycle X ℚ) x =
        (z : AlgebraicCycle X ℚ) x -
          (cyclesOfDimension.project (dimension := dimensionX) (i := i) γ :
            AlgebraicCycle X ℚ) x := by
      simp
    rw [hcoe]
    simp only [cyclesOfDimension.project_apply]
    by_cases hd : dimensionX x = i
    · rw [if_pos hd, hval, sub_self]
    · rw [if_neg hd, sub_zero]
      exact z.2 x hd
  have hzero : R.quotientMap
      (cyclesOfDimension.project (dimension := dimensionX) (i := i) γ) = 0 := by
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    cases R
    exact hproject γ hγmem
  have hfinal : closedImmersionPushforward Q f R
      (Q.quotientMap (cyclesOfDimension.pullbackClosed (dimensionW := dimensionW) f
        (z - cyclesOfDimension.project (dimension := dimensionX) (i := i) γ))) =
      R.quotientMap z := by
    change R.quotientMap (cyclesOfDimension.properPushforward f
      (cyclesOfDimension.pullbackClosed f
        (z - cyclesOfDimension.project (dimension := dimensionX) (i := i) γ))) =
      R.quotientMap z
    rw [cyclesOfDimension.properPushforward_pullbackClosed f _ hδ, map_sub, hzero, sub_zero]
  exact LinearMap.mem_range.mpr ⟨_, hfinal⟩

section Consequences

variable [NoetherianSpace X] [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
  (R : RationalEquivalenceSystem X dimensionX i) (V : X.Opens)
  {dimensionV : DimensionFunction V.toScheme}
  (S : RationalEquivalenceSystem V.toScheme dimensionV i)
  (hdim : ∀ v, dimensionV v = dimensionX (V.ι.base v))
  {W : Scheme.{u}} {dimensionW : DimensionFunction W}
  (Q : RationalEquivalenceSystem W dimensionW i)
  (f : W ⟶ X) [_root_.AlgebraicGeometry.IsClosedImmersion f]

/-- Exactness in the middle of the localization sequence over a Noetherian scheme.  The closure
step is proved here (`totalRationalRelations_le_map_pullbackOpen`), so the only remaining input is
that the canonical span of principal divisors is graded. -/
theorem ker_openImmersionPullback_le_range_of_noetherian
    (hrange : ∀ x : X, x ∉ V → x ∈ Set.range f.base)
    (hproject : ∀ c ∈ totalRationalRelations X dimensionX,
      (cyclesOfDimension.project (dimension := dimensionX) (i := i) c : AlgebraicCycle X ℚ) ∈
        totalRationalRelations X dimensionX) :
    LinearMap.ker (openImmersionPullback R V.ι hdim S) ≤
      LinearMap.range (closedImmersionPushforward Q f R) :=
  ker_openImmersionPullback_le_range R V S hdim Q f hrange
    (totalRationalRelations_le_map_pullbackOpen V dimensionX dimensionV) hproject

/-- Exactness in the middle of the localization sequence over a Noetherian scheme all of whose
principal divisors are homogeneous. -/
theorem ker_openImmersionPullback_le_range_of_homogeneous
    (hrange : ∀ x : X, x ∉ V → x ∈ Set.range f.base)
    (hhom : PrincipalDivisorsHomogeneous X dimensionX) :
    LinearMap.ker (openImmersionPullback R V.ι hdim S) ≤
      LinearMap.range (closedImmersionPushforward Q f R) :=
  ker_openImmersionPullback_le_range_of_noetherian R V S hdim Q f hrange
    fun c hc ↦ project_mem_totalRationalRelations_of_homogeneous hhom c hc

/-- The localization sequence `A_i(Y) → A_i(X) → A_i(U) → 0` is exact at `A_i(X)`: the kernel of
restriction to the open subscheme is exactly the image of the pushforward from a closed subscheme
covering the complement. -/
theorem ker_openImmersionPullback_eq_range_of_homogeneous
    (hrange : ∀ x : X, x ∉ V → x ∈ Set.range f.base)
    (hdisjoint : ∀ w, f.base w ∉ V)
    (hhom : PrincipalDivisorsHomogeneous X dimensionX) :
    LinearMap.ker (openImmersionPullback R V.ι hdim S) =
      LinearMap.range (closedImmersionPushforward Q f R) := by
  refine le_antisymm
    (ker_openImmersionPullback_le_range_of_homogeneous R V S hdim Q f hrange hhom) ?_
  rintro c ⟨d, rfl⟩
  have hz := LinearMap.congr_fun
    (openImmersionPullback_comp_closedImmersionPushforward R V Q S f hdisjoint hdim) d
  simpa using hz

omit [NoetherianSpace X] [_root_.AlgebraicGeometry.IsLocallyNoetherian X] in
/-- Every rational Chow class pushed forward from a closed subscheme with no points in dimension
`i` vanishes. -/
theorem closedImmersionPushforward_eq_zero_of_forall_ne
    (hdimW : ∀ w : W, dimensionW w ≠ i) (d : Q.ChowGroup) :
    closedImmersionPushforward Q f R d = 0 := by
  have hzero : ∀ z : cyclesOfDimension W dimensionW i, z = 0 := by
    intro z
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro w
    exact z.2 w (hdimW w)
  induction d using Submodule.Quotient.induction_on with
  | H z =>
      have hq : Q.quotientMap z = 0 := by
        rw [hzero z]
        exact map_zero _
      have hfin : closedImmersionPushforward Q f R (Q.quotientMap z) = 0 := by
        rw [hq]
        exact map_zero _
      exact hfin

include Q in
/-- If the closed complement of `V` has no points in dimension `i`, restriction of rational Chow
classes to `V` is an isomorphism in dimension `i`. -/
theorem openImmersionPullback_bijective_of_forall_ne
    (hrange : ∀ x : X, x ∉ V → x ∈ Set.range f.base)
    (hhom : PrincipalDivisorsHomogeneous X dimensionX)
    (hdimW : ∀ w : W, dimensionW w ≠ i) :
    Function.Bijective (openImmersionPullback R V.ι hdim S) := by
  refine ⟨?_, openImmersionPullback_surjective R V hdim S⟩
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro c hc
  obtain ⟨d, rfl⟩ := LinearMap.mem_range.mp
    (ker_openImmersionPullback_le_range_of_homogeneous R V S hdim Q f hrange hhom hc)
  exact Submodule.mem_bot _ |>.mpr
    (closedImmersionPushforward_eq_zero_of_forall_ne R Q f hdimW d)

end Consequences

end DescendingMap

end RationalEquivalenceSystem

end GromovWitten.AlgebraicGeometry.IntersectionTheory
