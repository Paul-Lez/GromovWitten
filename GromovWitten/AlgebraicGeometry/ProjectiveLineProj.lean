/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.ProjectiveLineRing
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChernClasses
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FiniteTypeDimension
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# The projective line over `ℤ` and over a base scheme

Let `ℤ' = ULift ℤ` and let `ℙ¹_ℤ = Proj ℤ'[X₀, X₁]` (Mathlib's `Proj` of the polynomial grading
of `ProjectiveLineRing.lean`). For a scheme `S` we set `ℙ¹_S = S ×_ℤ ℙ¹_ℤ`, the pullback of the two
terminal morphisms, with projections `pr S : ℙ¹_S ⟶ S` and `prP S : ℙ¹_S ⟶ ℙ¹_ℤ`. The two standard
charts `D₊(Xᵢ) ≅ Spec ℤ'[T]` of `ℙ¹_ℤ` give, after base change, two open immersions
`affineChart i S : 𝔸¹_S ⟶ ℙ¹_S` from Mathlib's affine line `𝔸(PUnit; S)`.

## Main results

* `isProper_terminal_from`: `ℙ¹_ℤ` is proper over the terminal scheme `Spec ℤ'`.
* `chart`, `chart_range_sup`: the two standard affine charts of `ℙ¹_ℤ` cover it.
* `P1S`, `pr`, `prP`, `P1S.map`: the relative projective line, its projections and its
  functoriality in the base; `isProper_pr` and friends: `ℙ¹_S ⟶ S` is proper, separated, locally
  of finite type and quasi-compact.
* `affineChart`, `isPullback_affineChart`, `affineChart_opensRange`, `affineChart_range_sup`,
  `affineChart_map`: the affine charts are open immersions, base changes of the charts of
  `ℙ¹_ℤ`, cover `ℙ¹_S` and are natural in `S`.
* `affineChart_preimage_basicOpen`: the first chart meets the second one exactly in the basic
  open set of the coordinate of `𝔸¹_S`.
* `irreducibleSpace_of_isOpen_of_isIrreducible`: a space covered by two irreducible open sets
  with nonempty intersection is irreducible.
* `isIntegral_P1S`, `isLocallyNoetherian_P1S`, `isDominant_affineChart`,
  `affineChart_genericPoint`: `ℙ¹_S` is integral (resp. locally Noetherian) when `S` is, and the
  first affine chart maps the generic point to the generic point.
* `coordFn`, `dominantFunctionFieldMap_affineChart_coordFn`, `coordFn_ne_zero`: the coordinate
  rational function of `ℙ¹_S`, characterised by its restriction to the first affine chart.
* `dimensionFunction_genericPoint_affineSpace`: for `S` integral and locally of finite type over a
  field `k`, the generic point of `𝔸¹_S` has dimension `dim S + 1`.
-/

-- Concrete `Spec R` / section-ring carriers only unify with the generic scheme instances at
-- default transparency; this option is what Mathlib's own affine-scheme API uses.
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry Topology TopologicalSpace HomogeneousLocalization

noncomputable section

namespace GromovWitten.AlgebraicGeometry.P1

/-! ### The projective line over `ℤ` -/

/-- The projective line `ℙ¹ = Proj ℤ[X₀, X₁]` over `ℤ' = ULift ℤ`. -/
abbrev scheme : Scheme.{u} := Proj grading.{u}

/-- `Spec` of the degree-zero part of the grading is a terminal scheme. -/
noncomputable def isTerminalSpecGradeZero :
    IsTerminal (Spec (CommRingCat.of (grading.{u} 0))) :=
  specULiftZIsTerminal.ofIso (Scheme.Spec.mapIso gradeZeroEquiv.toCommRingCatIso.op).symm

/-- The structure map of `Spec` of the degree-zero part to the terminal scheme is an
isomorphism. -/
instance : IsIso (terminal.from (Spec (CommRingCat.of (grading.{u} 0)))) :=
  isIso_of_isTerminal isTerminalSpecGradeZero terminalIsTerminal _

/-- The terminal morphism of `ℙ¹` factors through `Proj.toSpecZero`. -/
theorem terminal_from_eq :
    terminal.from scheme.{u} = Proj.toSpecZero grading ≫ terminal.from _ :=
  (terminal.comp_from _).symm

/-- **`ℙ¹_ℤ` is proper** (over the terminal scheme `Spec ℤ'`). -/
instance isProper_terminal_from : IsProper (terminal.from scheme.{u}) := by
  rw [terminal_from_eq]; infer_instance

/-- The standard affine chart `Spec ℤ'[X₀,X₁]_(Xᵢ) ⟶ ℙ¹`. -/
noncomputable def chart (i : Fin 2) : Spec (CommRingCat.of (Away grading.{u} (X i))) ⟶ scheme :=
  Proj.awayι grading (X i) (X_mem i) Nat.one_pos

/-- The standard charts are open immersions. -/
instance (i : Fin 2) : IsOpenImmersion (chart.{u} i) := by
  unfold chart; infer_instance

/-- The `i`-th chart has image the basic open set `D₊(Xᵢ)`. -/
theorem opensRange_chart (i : Fin 2) :
    (chart.{u} i).opensRange = Proj.basicOpen grading (X i) :=
  Proj.opensRange_awayι _ _ _ _

/-- The two standard charts cover `ℙ¹`. -/
theorem chart_range_sup : (chart.{u} 0).opensRange ⊔ (chart 1).opensRange = ⊤ := by
  rw [opensRange_chart, opensRange_chart, ← Proj.iSup_basicOpen_eq_top grading X
    irrelevant_le_span_X]
  refine le_antisymm (sup_le (le_iSup (fun i ↦ Proj.basicOpen grading (X i)) 0)
    (le_iSup (fun i ↦ Proj.basicOpen grading (X i)) 1)) (iSup_le fun i ↦ ?_)
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

/-! ### The projective line over a base -/

/-- The projective line `ℙ¹_S = S ×_ℤ ℙ¹_ℤ` over a scheme `S`. -/
abbrev P1S (S : Scheme.{u}) : Scheme.{u} := pullback (terminal.from S) (terminal.from scheme.{u})

/-- The projection `ℙ¹_S ⟶ S`. -/
abbrev pr (S : Scheme.{u}) : P1S S ⟶ S := pullback.fst _ _

/-- The projection `ℙ¹_S ⟶ ℙ¹_ℤ`. -/
abbrev prP (S : Scheme.{u}) : P1S S ⟶ scheme.{u} := pullback.snd _ _

/-- `ℙ¹_S ⟶ S` is proper (base change of `ℙ¹_ℤ ⟶ Spec ℤ'`). -/
instance isProper_pr (S : Scheme.{u}) : IsProper (pr S) := inferInstance

/-- `ℙ¹_S ⟶ S` is separated. -/
instance isSeparated_pr (S : Scheme.{u}) : IsSeparated (pr S) := inferInstance

/-- `ℙ¹_S ⟶ S` is locally of finite type. -/
instance locallyOfFiniteType_pr (S : Scheme.{u}) : LocallyOfFiniteType (pr S) := inferInstance

/-- `ℙ¹_S ⟶ S` is quasi-compact. -/
instance quasiCompact_pr (S : Scheme.{u}) : QuasiCompact (pr S) := inferInstance

/-- Functoriality of `ℙ¹_S` in the base `S`. -/
def P1S.map {S S' : Scheme.{u}} (f : S ⟶ S') : P1S S ⟶ P1S S' :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (terminal.hom_ext _ _) (by simp)

/-- `P1S.map` lies over the base morphism. -/
@[reassoc (attr := simp)]
theorem P1S.map_pr {S S' : Scheme.{u}} (f : S ⟶ S') : P1S.map f ≫ pr S' = pr S ≫ f :=
  pullback.lift_fst _ _ _

/-- `P1S.map` commutes with the projections to `ℙ¹_ℤ`. -/
@[reassoc (attr := simp)]
theorem P1S.map_prP {S S' : Scheme.{u}} (f : S ⟶ S') : P1S.map f ≫ prP S' = prP S :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- `P1S.map` preserves identities. -/
@[simp]
theorem P1S.map_id (S : Scheme.{u}) : P1S.map (𝟙 S) = 𝟙 (P1S S) :=
  pullback.hom_ext (by simp) (by simp)

/-- `P1S.map` preserves composition. -/
@[simp]
theorem P1S.map_comp {S S' S'' : Scheme.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
    P1S.map (f ≫ g) = P1S.map f ≫ P1S.map g :=
  pullback.hom_ext (by simp) (by simp)

/-! ### The affine charts of `ℙ¹_S` -/

/-- The identification `Spec ℤ'[T] ≅ Spec ℤ'[X₀,X₁]_(Xᵢ)` (`T ↦ Xⱼ / Xᵢ`). -/
def chartPolyIso (i : Fin 2) :
    Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))) ≅
      Spec (CommRingCat.of (Away grading.{u} (X i))) :=
  Scheme.Spec.mapIso (awayEquivPoly i).toCommRingCatIso.op

/-- The `i`-th standard chart of `ℙ¹_ℤ`, read on the affine line `Spec ℤ'[T]`. -/
def chartPoly (i : Fin 2) :
    Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))) ⟶ scheme.{u} :=
  (chartPolyIso i).hom ≫ chart i

/-- The charts `Spec ℤ'[T] ⟶ ℙ¹` are open immersions. -/
instance (i : Fin 2) : IsOpenImmersion (chartPoly.{u} i) := by
  unfold chartPoly; infer_instance

/-- The image of `chartPoly i` is `D₊(Xᵢ)`. -/
theorem opensRange_chartPoly (i : Fin 2) :
    (chartPoly.{u} i).opensRange = Proj.basicOpen grading (X i) := by
  change ((chartPolyIso i).hom ≫ chart i).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, opensRange_chart]

/-- The `i`-th standard affine chart `𝔸¹_S ⟶ ℙ¹_S`. -/
def affineChart (i : Fin 2) (S : Scheme.{u}) : 𝔸(PUnit; S) ⟶ P1S S :=
  pullback.map _ _ _ _ (𝟙 S) (chartPoly i) (𝟙 _) (terminal.hom_ext _ _) (terminal.hom_ext _ _)

/-- The affine charts lie over `S`. -/
@[reassoc (attr := simp)]
theorem affineChart_pr (i : Fin 2) (S : Scheme.{u}) :
    affineChart i S ≫ pr S = 𝔸(PUnit; S) ↘ S :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The affine charts are compatible with the charts of `ℙ¹_ℤ`. -/
@[reassoc (attr := simp)]
theorem affineChart_prP (i : Fin 2) (S : Scheme.{u}) :
    affineChart i S ≫ prP S = AffineSpace.toSpecMvPoly PUnit S ≫ chartPoly i :=
  pullback.lift_snd _ _ _

/-- The affine chart `𝔸¹_S ⟶ ℙ¹_S` is the base change of `chartPoly i` along
`ℙ¹_S ⟶ ℙ¹_ℤ`. -/
theorem isPullback_affineChart (i : Fin 2) (S : Scheme.{u}) :
    IsPullback (affineChart i S) (AffineSpace.toSpecMvPoly PUnit S) (prP S) (chartPoly i) := by
  refine IsPullback.of_right ?_ (affineChart_prP i S) (IsPullback.of_hasPullback _ _)
  rw [affineChart_pr, terminal.comp_from]
  exact IsPullback.of_hasPullback _ _

/-- The affine charts are open immersions. -/
instance (i : Fin 2) (S : Scheme.{u}) : IsOpenImmersion (affineChart i S) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_affineChart i S).flip inferInstance

/-- The `i`-th affine chart has image the preimage of `D₊(Xᵢ)`. -/
theorem affineChart_opensRange (i : Fin 2) (S : Scheme.{u}) :
    (affineChart i S).opensRange = (prP S) ⁻¹ᵁ (Proj.basicOpen grading (X i)) := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (isPullback_affineChart i S).flip ⊤
  rw [← Scheme.Hom.image_top_eq_opensRange, ← opensRange_chartPoly, ←
    Scheme.Hom.image_top_eq_opensRange]
  simpa using h

/-- The two affine charts cover `ℙ¹_S`. -/
theorem affineChart_range_sup (S : Scheme.{u}) :
    (affineChart 0 S).opensRange ⊔ (affineChart 1 S).opensRange = ⊤ := by
  rw [affineChart_opensRange, affineChart_opensRange, ← opensRange_chart, ← opensRange_chart,
    ← Scheme.Hom.preimage_sup, chart_range_sup, Scheme.Hom.preimage_top]

/-- The affine charts are natural in the base. -/
@[reassoc]
theorem affineChart_map (i : Fin 2) {S S' : Scheme.{u}} (f : S ⟶ S') :
    affineChart i S ≫ P1S.map f = AffineSpace.map PUnit f ≫ affineChart i S' := by
  apply pullback.hom_ext
  · simp only [Category.assoc, P1S.map_pr, affineChart_pr_assoc, affineChart_pr,
      AffineSpace.map_over]
  · simp only [Category.assoc, P1S.map_prP, affineChart_prP, AffineSpace.map_toSpecMvPoly_assoc]

/-! ### The overlap of the two charts -/

/-- The coordinate `t 0 = X₁ / X₀` is Mathlib's localisation element of `D₊(X₀) ∩ D₊(X₁)`. -/
theorem t_zero_eq_isLocalizationElem :
    t.{u} 0 = Away.isLocalizationElem (X_mem 0) (X_mem 1) := by
  apply HomogeneousLocalization.val_injective
  rw [t_val, Away.val_mk]
  simp only [other, pow_one]
  congr 1
  exact Subtype.ext (pow_one _)

/-- The second chart meets the first one in the locus where the coordinate `T = X₁ / X₀` of
`Spec ℤ'[T]` is invertible. -/
theorem chartPoly_preimage_basicOpen :
    chartPoly.{u} 0 ⁻¹ᵁ Proj.basicOpen grading (X 1) =
      (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv (MvPolynomial.X PUnit.unit)) := by
  have h : chart.{u} 0 ⁻¹ᵁ Proj.basicOpen grading (X 1) =
      (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv (t 0)) := by
    rw [basicOpen_eq_of_affine, t_zero_eq_isLocalizationElem]
    exact Proj.awayι_preimage_basicOpen (𝒜 := grading) (X_mem 0) Nat.one_pos (X_mem 1)
      Nat.one_pos
  change (chartPolyIso 0).hom ⁻¹ᵁ (chart 0 ⁻¹ᵁ Proj.basicOpen grading (X 1)) = _
  rw [h, Scheme.preimage_basicOpen_top]
  congr 1
  rw [chartPolyIso, Scheme.Spec.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  congr 1
  exact awayEquivPoly_t 0

/-- On `𝔸¹_S`, the locus where the first affine chart meets the second one is the basic open
set of the coordinate. -/
theorem affineChart_preimage_basicOpen (S : Scheme.{u}) :
    affineChart 0 S ⁻¹ᵁ prP S ⁻¹ᵁ Proj.basicOpen grading (X 1) =
      (𝔸(PUnit; S)).basicOpen (AffineSpace.coord S PUnit.unit) := by
  rw [← Scheme.Hom.comp_preimage, affineChart_prP, Scheme.Hom.comp_preimage,
    chartPoly_preimage_basicOpen, Scheme.preimage_basicOpen_top]
  rfl

/-- The coordinate of `𝔸¹_S` is nonzero as soon as `Γ(S, ⊤)` is nontrivial: it maps to `1`
along the section `S ⟶ 𝔸¹_S` at the point `1`. -/
theorem coord_ne_zero (S : Scheme.{u}) [Nontrivial Γ(S, ⊤)] :
    AffineSpace.coord S PUnit.unit ≠ 0 := by
  intro h
  have h1 := AffineSpace.homOfVector_appTop_coord (𝟙 S) (fun _ ↦ (1 : Γ(S, ⊤))) PUnit.unit
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-! ### Integrality -/

/-- A space covered by two irreducible open subsets with nonempty intersection is
irreducible. -/
theorem irreducibleSpace_of_isOpen_of_isIrreducible {T : Type*} [TopologicalSpace T]
    {U V : Set T} (hU : IsOpen U) (hU' : IsIrreducible U) (hV' : IsIrreducible V)
    (hUV : U ∪ V = Set.univ) (hne : (U ∩ V).Nonempty) : IrreducibleSpace T := by
  have h2 : V ⊆ closure (V ∩ U) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hV'.isPreirreducible hU
      (by rwa [Set.inter_comm])
  have h3 : closure U = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hUV]
    exact Set.union_subset subset_closure (h2.trans (closure_mono Set.inter_subset_right))
  rw [irreducibleSpace_def, Set.top_eq_univ, ← h3]
  exact isIrreducible_iff_closure.mpr hU'

/-- Every point of `ℙ¹_S` lies in one of the two affine charts. -/
theorem exists_affineChart_eq (S : Scheme.{u}) (x : P1S S) :
    ∃ (i : Fin 2) (y : 𝔸(PUnit; S)), affineChart i S y = x := by
  have hx : x ∈ (affineChart 0 S).opensRange ⊔ (affineChart 1 S).opensRange := by
    rw [affineChart_range_sup]; trivial
  rcases Opens.mem_sup.mp hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact ⟨0, y, hy⟩
  · exact ⟨1, y, hy⟩

/-- `ℙ¹_S` is reduced when `S` is: its stalks are stalks of `𝔸¹_S`. -/
instance isReduced_P1S (S : Scheme.{u}) [IsReduced S] : IsReduced (P1S S) := by
  have : ∀ x : P1S S, _root_.IsReduced ((P1S S).presheaf.stalk x) := by
    intro x
    obtain ⟨i, y, rfl⟩ := exists_affineChart_eq S x
    exact isReduced_of_injective ((affineChart i S).stalkMap y).hom
      (ConcreteCategory.bijective_of_isIso _).1
  exact isReduced_of_isReduced_stalk _

/-- The image of an affine chart is irreducible when `S` is. -/
theorem isIrreducible_range_affineChart (i : Fin 2) (S : Scheme.{u}) [IrreducibleSpace S] :
    IsIrreducible (Set.range (affineChart i S)) := by
  rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _
    (affineChart i S).continuous.continuousOn

/-- The generic point of the first affine chart lies in the second one. -/
theorem affineChart_genericPoint_mem (S : Scheme.{u}) [IsIntegral S] :
    affineChart 0 S (genericPoint 𝔸(PUnit; S)) ∈ (affineChart 1 S).opensRange := by
  rw [affineChart_opensRange]
  change genericPoint _ ∈ affineChart 0 S ⁻¹ᵁ prP S ⁻¹ᵁ Proj.basicOpen grading (X 1)
  rw [affineChart_preimage_basicOpen]
  refine ((genericPoint_spec _).mem_open_set_iff (Opens.isOpen _)).mpr ?_
  rw [Set.univ_inter, Set.nonempty_iff_ne_empty, ne_eq, ← Opens.coe_bot, SetLike.coe_set_eq,
    _root_.AlgebraicGeometry.basicOpen_eq_bot_iff]
  exact coord_ne_zero S

/-- `ℙ¹_S` is irreducible when `S` is integral: the two irreducible chart images meet. -/
instance irreducibleSpace_P1S (S : Scheme.{u}) [IsIntegral S] : IrreducibleSpace (P1S S) := by
  refine irreducibleSpace_of_isOpen_of_isIrreducible (affineChart 0 S).isOpenEmbedding.isOpen_range
    (isIrreducible_range_affineChart 0 S)
    (isIrreducible_range_affineChart 1 S) ?_ ⟨_, ⟨_, rfl⟩, affineChart_genericPoint_mem S⟩
  have h := congrArg (fun U : (P1S S).Opens ↦ (U : Set (P1S S))) (affineChart_range_sup S)
  simpa using h

/-- **`ℙ¹_S` is integral** when `S` is. -/
instance isIntegral_P1S (S : Scheme.{u}) [IsIntegral S] : IsIntegral (P1S S) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- `ℙ¹_S` is locally Noetherian when `S` is. -/
instance isLocallyNoetherian_P1S (S : Scheme.{u}) [IsLocallyNoetherian S] :
    IsLocallyNoetherian (P1S S) :=
  LocallyOfFiniteType.isLocallyNoetherian (pr S)

/-- For `S` integral, the affine charts (nonempty open immersions) are dominant. -/
instance isDominant_affineChart (i : Fin 2) (S : Scheme.{u}) [IsIntegral S] :
    IsDominant (affineChart i S) :=
  ⟨(affineChart i S).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

/-- The first affine chart maps the generic point of `𝔸¹_S` to the generic point of
`ℙ¹_S`. -/
theorem affineChart_genericPoint (S : Scheme.{u}) [IsIntegral S] :
    affineChart 0 S (genericPoint 𝔸(PUnit; S)) = genericPoint (P1S S) :=
  genericPoint_eq_of_isOpenImmersion _

/-! ### The coordinate function -/

/-- The function-field map of a dominant open immersion of integral schemes is bijective: it is
the stalk map at the generic point, an isomorphism for an open immersion. -/
theorem dominantFunctionFieldMap_bijective_of_isOpenImmersion {A B : Scheme.{u}}
    [IsIntegral A] [IsIntegral B] (f : A ⟶ B) [IsOpenImmersion f] [IsDominant f] :
    Function.Bijective (Scheme.dominantFunctionFieldMap f) := by
  have hiso : IsIso ((eqToHom (congrArg (fun z ↦ B.presheaf.stalk z)
      (Scheme.map_genericPoint_of_isDominant f).symm) :
      B.presheaf.stalk (genericPoint B) ⟶
        B.presheaf.stalk (f.base (genericPoint A))) ≫ f.stalkMap (genericPoint A)) :=
    IsIso.comp_isIso' inferInstance inferInstance
  exact ConcreteCategory.bijective_of_isIso _

/-- The top open of a nonempty scheme is nonempty (needed for `germToFunctionField ⊤`). -/
instance nonempty_top_opens {X : Scheme.{u}} [Nonempty X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.arbitrary X, trivial⟩⟩

/-- The function field of `ℙ¹_S` is identified with that of the first affine chart `𝔸¹_S`. -/
def functionFieldEquiv (S : Scheme.{u}) [IsIntegral S] :
    (P1S S).functionField ≃+* (𝔸(PUnit; S)).functionField :=
  RingEquiv.ofBijective _ (dominantFunctionFieldMap_bijective_of_isOpenImmersion (affineChart 0 S))

/-- The coordinate rational function `t = X₁ / X₀` on `ℙ¹_S`, for `S` integral. -/
def coordFn (S : Scheme.{u}) [IsIntegral S] : (P1S S).functionField :=
  (functionFieldEquiv S).symm
    ((𝔸(PUnit; S)).germToFunctionField ⊤ (AffineSpace.coord S PUnit.unit))

/-- The coordinate function of `ℙ¹_S` restricts on the first affine chart to the coordinate of
`𝔸¹_S`. -/
theorem dominantFunctionFieldMap_affineChart_coordFn (S : Scheme.{u}) [IsIntegral S] :
    Scheme.dominantFunctionFieldMap (affineChart 0 S) (coordFn S) =
      (𝔸(PUnit; S)).germToFunctionField ⊤ (AffineSpace.coord S PUnit.unit) :=
  (functionFieldEquiv S).apply_symm_apply _

/-- The coordinate function of `ℙ¹_S` is nonzero. -/
theorem coordFn_ne_zero (S : Scheme.{u}) [IsIntegral S] : coordFn S ≠ 0 := by
  intro h
  have h1 := dominantFunctionFieldMap_affineChart_coordFn S
  rw [h, map_zero, eq_comm, ← map_zero ((𝔸(PUnit; S)).germToFunctionField ⊤).hom] at h1
  exact coord_ne_zero S (Scheme.germToFunctionField_injective _ _ h1)

/-! ### The dimension of the affine line -/

section Dimension

variable {k : Type u} [Field k] (S : Scheme.{u}) (sS : S ⟶ Spec (CommRingCat.of k))

/-- `ℙ¹_S` is locally of finite type over `k` when `S` is. -/
instance locallyOfFiniteType_pr_comp [LocallyOfFiniteType sS] :
    LocallyOfFiniteType (pr S ≫ sS) := inferInstance

/-- `𝔸¹_S` is locally of finite type over `k` when `S` is. -/
instance locallyOfFiniteType_affineSpace_comp [LocallyOfFiniteType sS] :
    LocallyOfFiniteType (𝔸(PUnit; S) ↘ S ≫ sS) := inferInstance

/-- **The dimension of the affine line.**  Over an integral scheme `S` locally of finite type
over a field, the generic point of `𝔸¹_S` has dimension one more than the generic point of
`S`. -/
theorem dimensionFunction_genericPoint_affineSpace [IsIntegral S] [LocallyOfFiniteType sS] :
    IntersectionTheory.FiniteTypeDimension.dimensionFunction (𝔸(PUnit; S) ↘ S ≫ sS)
        (genericPoint 𝔸(PUnit; S)) =
      IntersectionTheory.FiniteTypeDimension.dimensionFunction sS (genericPoint S) + 1 := by
  obtain ⟨U, hU, hx, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := genericPoint S) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨_, hx⟩⟩
  have _ : IsNoetherianRing Γ(S, U) :=
    IntersectionTheory.FiniteTypeDimension.isNoetherianRing_sections sS U hU
  let J : Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} Γ(S, U))) ⟶ 𝔸(PUnit; S) :=
    (AffineSpace.SpecIso PUnit Γ(S, U)).inv ≫ AffineSpace.map PUnit hU.fromSpec
  have _ : IsOpenImmersion (AffineSpace.map PUnit.{u + 1} hU.fromSpec) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
      (AffineSpace.isPullback_map hU.fromSpec).flip inferInstance
  have _ : IsOpenImmersion J := by dsimp only [J]; infer_instance
  have key := IntersectionTheory.VectorBundle.dimension_bundlePoint
    (e := AlgEquiv.refl (R := Γ(S, U)) (A₁ := MvPolynomial PUnit.{u + 1} Γ(S, U)))
    (IntersectionTheory.FiniteTypeDimension.dimensionFunction (hU.fromSpec ≫ sS))
    (IntersectionTheory.FiniteTypeDimension.dimensionFunction (J ≫ 𝔸(PUnit; S) ↘ S ≫ sS))
    (genericPoint (Spec Γ(S, U)))
  have hgen : IntersectionTheory.VectorBundle.bundlePoint
      (AlgEquiv.refl (R := Γ(S, U)) (A₁ := MvPolynomial PUnit.{u + 1} Γ(S, U)))
      (genericPoint (Spec Γ(S, U))) = genericPoint (Spec (.of (MvPolynomial PUnit Γ(S, U)))) := by
    rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    simp [IntersectionTheory.VectorBundle.bundlePoint]
  rw [hgen, IntersectionTheory.FiniteTypeDimension.dimensionFunction_comp _ J,
    IntersectionTheory.FiniteTypeDimension.dimensionFunction_comp sS hU.fromSpec,
    genericPoint_eq_of_isOpenImmersion, genericPoint_eq_of_isOpenImmersion] at key
  simpa using key

end Dimension

end GromovWitten.AlgebraicGeometry.P1

end
