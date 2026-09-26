/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The projective line over a field

placeholder
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.ProjectiveLine

noncomputable section

variable (k : Type u) [Field k]

/-- The coordinate ring `k[t, t⁻¹]` of the overlap of the two standard charts of `ℙ¹_k`. -/
abbrev overlapRing : Type u := Localization.Away (Polynomial.X : Polynomial k)

instance : IsDomain (overlapRing k) :=
  IsLocalization.isDomain_localization (M := Submonoid.powers (Polynomial.X : Polynomial k))
    (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero)

/-- The inverse `t⁻¹` of the coordinate in `k[t, t⁻¹]`. -/
def tInv : overlapRing k := IsLocalization.Away.invSelf (Polynomial.X : Polynomial k)

/-- `t * t⁻¹ = 1` in `k[t, t⁻¹]`. -/
lemma algebraMap_X_mul_tInv :
    algebraMap (Polynomial k) (overlapRing k) Polynomial.X * tInv k = 1 :=
  IsLocalization.Away.mul_invSelf _

/-- `t⁻¹` is a unit of `k[t, t⁻¹]`. -/
lemma isUnit_tInv : IsUnit (tInv k) :=
  ⟨⟨tInv k, algebraMap (Polynomial k) (overlapRing k) Polynomial.X,
    (mul_comm _ _).trans (algebraMap_X_mul_tInv k), algebraMap_X_mul_tInv k⟩, rfl⟩

/-- The `k`-algebra map `k[s] → k[t, t⁻¹]` sending the coordinate `s` to `t⁻¹`.  It exhibits
`k[t, t⁻¹]` as the localization of the second chart away from its coordinate, and is the
transition map of the standard atlas of `ℙ¹_k`. -/
def flipHom : Polynomial k →+* overlapRing k :=
  Polynomial.eval₂RingHom ((algebraMap (Polynomial k) (overlapRing k)).comp Polynomial.C) (tInv k)

@[simp] lemma flipHom_X : flipHom k Polynomial.X = tInv k := by simp [flipHom]

@[simp] lemma flipHom_C (a : k) :
    flipHom k (Polynomial.C a) = algebraMap (Polynomial k) (overlapRing k) (Polynomial.C a) := by
  simp [flipHom]

/-- The transition automorphism `t ↦ t⁻¹` of `k[t, t⁻¹]`, as a ring homomorphism. -/
def flipRingHom : overlapRing k →+* overlapRing k :=
  IsLocalization.Away.lift (S := overlapRing k) (Polynomial.X : Polynomial k)
    (g := flipHom k) (by simpa using isUnit_tInv k)

@[simp] lemma flipRingHom_algebraMap (p : Polynomial k) :
    flipRingHom k (algebraMap (Polynomial k) (overlapRing k) p) = flipHom k p :=
  IsLocalization.Away.lift_eq _ _ _

/-- The transition automorphism inverts the coordinate. -/
lemma flipRingHom_tInv :
    flipRingHom k (tInv k) = algebraMap (Polynomial k) (overlapRing k) Polynomial.X := by
  have h1 : flipRingHom k (algebraMap (Polynomial k) (overlapRing k) Polynomial.X) *
      flipRingHom k (tInv k) = 1 := by
    rw [← map_mul, algebraMap_X_mul_tInv, map_one]
  rw [flipRingHom_algebraMap, flipHom_X] at h1
  have h2 := algebraMap_X_mul_tInv k
  calc flipRingHom k (tInv k)
      = (algebraMap (Polynomial k) (overlapRing k) Polynomial.X * tInv k) *
          flipRingHom k (tInv k) := by rw [h2, one_mul]
    _ = algebraMap (Polynomial k) (overlapRing k) Polynomial.X *
          (tInv k * flipRingHom k (tInv k)) := by ring
    _ = algebraMap (Polynomial k) (overlapRing k) Polynomial.X := by rw [h1, mul_one]

/-- The transition automorphism is an involution. -/
lemma flipRingHom_involutive (x : overlapRing k) : flipRingHom k (flipRingHom k x) = x := by
  have h : (flipRingHom k).comp (flipRingHom k) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial k))
    apply Polynomial.ringHom_ext
    · intro a; simp
    · simp [flipRingHom_tInv]
  exact congrArg (fun f => f x) h ▸ rfl

/-- The transition automorphism `t ↦ t⁻¹` of `k[t, t⁻¹]`, as a ring isomorphism. -/
def flipRingEquiv : overlapRing k ≃+* overlapRing k :=
  RingEquiv.ofRingHom (flipRingHom k) (flipRingHom k)
    (RingHom.ext fun x => flipRingHom_involutive k x)
    (RingHom.ext fun x => flipRingHom_involutive k x)

instance isIso_ofHom_flipRingHom : IsIso (CommRingCat.ofHom (flipRingHom k)) := by
  refine (ConcreteCategory.isIso_iff_bijective (C := CommRingCat) _).mpr ?_
  exact Function.Involutive.bijective (flipRingHom_involutive k)

/-- The standard chart `𝔸¹_k = Spec k[t]` of `ℙ¹_k`. -/
abbrev chart : Scheme.{u} := Spec (CommRingCat.of (Polynomial k))

/-- The overlap `Spec k[t, t⁻¹]` of the two standard charts of `ℙ¹_k`. -/
abbrev overlap : Scheme.{u} := Spec (CommRingCat.of (overlapRing k))

/-- The inclusion of the overlap into the first chart, `Spec k[t,t⁻¹] ⟶ Spec k[t]`. -/
abbrev overlapToChartZero : overlap k ⟶ chart k :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (overlapRing k)))

/-- The inclusion of the overlap into the second chart, `Spec k[t,t⁻¹] ⟶ Spec k[s]`,
induced by `s ↦ t⁻¹`. -/
abbrev overlapToChartOne : overlap k ⟶ chart k :=
  Spec.map (CommRingCat.ofHom (flipHom k))

/-- The second inclusion of the overlap differs from the first by the transition automorphism. -/
lemma overlapToChartOne_eq :
    overlapToChartOne k =
      Spec.map (CommRingCat.ofHom (flipRingHom k)) ≫ overlapToChartZero k := by
  have h : (flipRingHom k).comp (algebraMap (Polynomial k) (overlapRing k)) = flipHom k :=
    IsLocalization.Away.lift_comp _ _
  rw [overlapToChartZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

instance : IsOpenImmersion (overlapToChartOne k) := by
  rw [overlapToChartOne_eq]
  infer_instance

/-- The two inclusions of the overlap have the same image, the basic open set `D(t)`. -/
lemma range_overlapToChartOne :
    Set.range (overlapToChartOne k).base = Set.range (overlapToChartZero k).base := by
  rw [overlapToChartOne_eq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr, Set.image_univ]
  exact (Scheme.homeoOfIso (asIso (Spec.map (CommRingCat.ofHom (flipRingHom k))))).surjective

/-- The span diagram whose colimit is `ℙ¹_k`: two copies of `𝔸¹_k` glued along `Spec k[t,t⁻¹]`. -/
abbrev diagram : WidePushoutShape (Fin 2) ⥤ Scheme.{u} :=
  WidePushoutShape.wideSpan (overlap k) (fun _ => chart k)
    (fun i => if i = 0 then overlapToChartZero k else overlapToChartOne k)

instance instIsOpenImmersionArrow (i : Fin 2) :
    IsOpenImmersion (if i = 0 then overlapToChartZero k else overlapToChartOne k) := by
  by_cases h : i = 0
  · rw [if_pos h]; infer_instance
  · rw [if_neg h]; infer_instance

instance instIsOpenImmersionDiagramMap :
    ∀ {i j : WidePushoutShape (Fin 2)} (f : i ⟶ j), IsOpenImmersion ((diagram k).map f) := by
  intro i j f
  cases f with
  | id X => exact inferInstanceAs (IsOpenImmersion (𝟙 _))
  | init j => exact instIsOpenImmersionArrow k j

/-- **The projective line over `k`**, as the gluing of two copies of the affine line along
`Spec k[t, t⁻¹]`. -/
abbrev scheme : Scheme.{u} := colimit (diagram k)

/-- The first standard chart of `ℙ¹_k`, an open immersion `Spec k[t] ⟶ ℙ¹_k`. -/
abbrev chartZero : chart k ⟶ scheme k := colimit.ι (diagram k) (some 0)

/-- The second standard chart of `ℙ¹_k`, an open immersion `Spec k[s] ⟶ ℙ¹_k`. -/
abbrev chartOne : chart k ⟶ scheme k := colimit.ι (diagram k) (some 1)

/-- The gluing map of the overlap into `ℙ¹_k`, i.e. the restriction of either chart to the
overlap.  Stated with `overlap k` as its source (rather than `(diagram k).obj none`) so that
instance search and rewriting work. -/
abbrev overlapι : overlap k ⟶ scheme k := colimit.ι (diagram k) none

/-- The two charts of `ℙ¹_k` cover it. -/
lemma mem_range_chart (x : scheme k) :
    x ∈ Set.range (chartZero k).base ∪ Set.range (chartOne k).base := by
  obtain ⟨i, xi, hxi⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram k) x
  match i with
  | none =>
    refine Or.inl ⟨(diagram k).map (WidePushoutShape.Hom.init 0) xi, ?_⟩
    have h : (colimit.ι (diagram k) (some 0)).base
        (((diagram k).map (WidePushoutShape.Hom.init (0 : Fin 2))).base xi) =
        (colimit.ι (diagram k) none).base xi := by
      rw [← Scheme.Hom.comp_apply, colimit.w]
    exact h.trans hxi
  | some 0 => exact Or.inl ⟨xi, hxi⟩
  | some 1 => exact Or.inr ⟨xi, hxi⟩

instance instCompactSpaceObj (i : WidePushoutShape (Fin 2)) :
    CompactSpace ((diagram k).obj i) := by
  match i with
  | none => exact inferInstanceAs (CompactSpace (overlap k))
  | some _ => exact inferInstanceAs (CompactSpace (chart k))

instance : CompactSpace (scheme k) := by
  constructor
  have h : (Set.univ : Set (scheme k)) =
      Set.range (chartZero k).base ∪ Set.range (chartOne k).base :=
    (Set.eq_univ_of_forall (mem_range_chart k)).symm
  rw [h]
  refine IsCompact.union ?_ ?_ <;>
    exact Set.image_univ (f := _) ▸ (CompactSpace.isCompact_univ).image (by continuity)

instance instIsReducedObj (i : WidePushoutShape (Fin 2)) : IsReduced ((diagram k).obj i) := by
  match i with
  | none => exact inferInstanceAs (IsReduced (overlap k))
  | some _ => exact inferInstanceAs (IsReduced (chart k))

instance : IsReduced (scheme k) := by
  have h : ∀ i, IsReduced ((Scheme.IsLocallyDirected.openCover (diagram k)).X i) := fun i =>
    instIsReducedObj k i
  exact IsReduced.of_openCover _ (Scheme.IsLocallyDirected.openCover (diagram k))

/-! ## Integrality -/

/-- The image in `ℙ¹_k` of the generic point of the first chart; the generic point of `ℙ¹_k`. -/
def genericPt : scheme k := (chartZero k).base (genericPoint (chart k))

lemma map_init_zero :
    (diagram k).map (WidePushoutShape.Hom.init (0 : Fin 2)) = overlapToChartZero k := rfl

lemma map_init_one :
    (diagram k).map (WidePushoutShape.Hom.init (1 : Fin 2)) = overlapToChartOne k := rfl

/-- The first chart restricted to the overlap is the gluing map of the overlap. -/
lemma overlapToChartZero_comp :
    overlapToChartZero k ≫ chartZero k = overlapι k := by
  rw [← map_init_zero k]
  exact colimit.w (diagram k) _

/-- The second chart restricted to the overlap is the gluing map of the overlap. -/
lemma overlapToChartOne_comp :
    overlapToChartOne k ≫ chartOne k = overlapι k := by
  rw [← map_init_one k]
  exact colimit.w (diagram k) _

/-- Both charts send the generic point of `𝔸¹_k` to the generic point of `ℙ¹_k`. -/
lemma chartOne_genericPoint :
    (chartOne k).base (genericPoint (chart k)) = genericPt k := by
  have h0 : (overlapToChartZero k).base (genericPoint (overlap k)) = genericPoint (chart k) :=
    _root_.AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion (overlapToChartZero k)
  have h1 : (overlapToChartOne k).base (genericPoint (overlap k)) = genericPoint (chart k) :=
    _root_.AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion (overlapToChartOne k)
  have e0 : (chartZero k).base ((overlapToChartZero k).base (genericPoint (overlap k)))
      = (overlapι k).base (genericPoint (overlap k)) := by
    rw [← Scheme.Hom.comp_apply, overlapToChartZero_comp]
  have e1 : (chartOne k).base ((overlapToChartOne k).base (genericPoint (overlap k)))
      = (overlapι k).base (genericPoint (overlap k)) := by
    rw [← Scheme.Hom.comp_apply, overlapToChartOne_comp]
  calc (chartOne k).base (genericPoint (chart k))
      = (chartOne k).base ((overlapToChartOne k).base (genericPoint (overlap k))) := by rw [h1]
    _ = (overlapι k).base (genericPoint (overlap k)) := e1
    _ = (chartZero k).base ((overlapToChartZero k).base (genericPoint (overlap k))) := e0.symm
    _ = genericPt k := by rw [h0]; rfl

/-- Every point in the image of a chart lies in the closure of the generic point. -/
lemma mem_closure_genericPt (j : chart k ⟶ scheme k)
    (hj : j.base (genericPoint (chart k)) = genericPt k) (y : chart k) :
    j.base y ∈ closure {genericPt k} := by
  have hgp : closure {genericPoint (chart k)} = Set.univ := genericPoint_spec (chart k)
  have h2 : j.base '' closure {genericPoint (chart k)} ⊆ closure {genericPt k} := by
    rw [← hj, ← Set.image_singleton]
    exact image_closure_subset_closure_image j.continuous
  exact h2 ⟨y, by rw [hgp]; trivial, rfl⟩

/-- `ℙ¹_k` is the closure of its generic point. -/
lemma closure_genericPt : closure {genericPt k} = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  rcases mem_range_chart k x with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact hy ▸ mem_closure_genericPt k (chartZero k) rfl y
  · exact hy ▸ mem_closure_genericPt k (chartOne k) (chartOne_genericPoint k) y

instance : IrreducibleSpace (scheme k) := by
  rw [irreducibleSpace_def]
  have h : IsIrreducible (closure {genericPt k}) := isIrreducible_singleton.closure
  rw [closure_genericPt] at h
  exact h

instance : IsIntegral (scheme k) := isIntegral_of_irreducibleSpace_of_isReduced _

/-! ## The structure morphism to `Spec k` -/

/-- `k[t]` is generated by `t` as a `k`-algebra. -/
lemma adjoin_X_eq_top : Algebra.adjoin k ({Polynomial.X} : Set (Polynomial k)) = ⊤ := by
  refine le_antisymm le_top ?_
  intro p hp
  clear hp
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.algebraMap_eq]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a)
      (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton k Polynomial.X) n)

instance : Algebra.FiniteType k (Polynomial k) :=
  ⟨⟨{Polynomial.X}, by rw [Finset.coe_singleton]; exact adjoin_X_eq_top k⟩⟩

/-- The `k`-algebra structure map of the overlap ring `k[t,t⁻¹]`. -/
def kToOverlapRing : k →+* overlapRing k :=
  (algebraMap (Polynomial k) (overlapRing k)).comp (algebraMap k (Polynomial k))

/-- The structure morphism `𝔸¹_k ⟶ Spec k` of a chart. -/
abbrev chartToSpecK : chart k ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))

/-- Both transition maps are compatible with the structure morphisms to `Spec k`. -/
lemma arrow_comp_chartToSpecK (j : Fin 2) :
    (diagram k).map (WidePushoutShape.Hom.init j) ≫ chartToSpecK k =
      Spec.map (CommRingCat.ofHom (kToOverlapRing k)) := by
  have h : ∀ φ : Polynomial k →+* overlapRing k,
      φ.comp (algebraMap k (Polynomial k)) = kToOverlapRing k →
      Spec.map (CommRingCat.ofHom φ) ≫ chartToSpecK k =
        Spec.map (CommRingCat.ofHom (kToOverlapRing k)) := by
    intro φ hφ
    rw [chartToSpecK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have harr : (diagram k).map (WidePushoutShape.Hom.init j) =
      if j = 0 then overlapToChartZero k else overlapToChartOne k := rfl
  rw [harr]
  by_cases hj : j = 0
  · rw [if_pos hj]
    exact h _ rfl
  · rw [if_neg hj]
    refine h _ (RingHom.ext fun a => ?_)
    rw [RingHom.comp_apply, Polynomial.algebraMap_eq, flipHom_C]
    rfl

/-- The cocone over the atlas diagram with vertex `Spec k`. -/
def toSpecKCocone : Cocone (diagram k) :=
  WidePushoutShape.mkCocone (Spec.map (CommRingCat.ofHom (kToOverlapRing k)))
    (fun _ => chartToSpecK k) (arrow_comp_chartToSpecK k)

/-- **The structure morphism `ℙ¹_k ⟶ Spec k`.** -/
def structureMap : scheme k ⟶ Spec (CommRingCat.of k) :=
  colimit.desc (diagram k) (toSpecKCocone k)

@[simp] lemma chartZero_comp_structureMap :
    chartZero k ≫ structureMap k = chartToSpecK k :=
  colimit.ι_desc (toSpecKCocone k) (some 0)

@[simp] lemma chartOne_comp_structureMap :
    chartOne k ≫ structureMap k = chartToSpecK k :=
  colimit.ι_desc (toSpecKCocone k) (some 1)

instance instLOFTChartToSpecK : LocallyOfFiniteType (chartToSpecK k) := by
  rw [chartToSpecK, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType),
    CommRingCat.hom_ofHom]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

instance instLOFTOverlapToSpecK :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (kToOverlapRing k))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom]
  exact RingHom.FiniteType.comp (RingHom.finiteType_algebraMap.mpr inferInstance)
    (RingHom.finiteType_algebraMap.mpr inferInstance)

instance : LocallyOfFiniteType (structureMap k) := by
  let _ := HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @LocallyOfFiniteType) (Q := RingHom.FiniteType)
  rw [IsZariskiLocalAtSource.iff_of_openCover
    (P := @LocallyOfFiniteType) (Scheme.IsLocallyDirected.openCover (diagram k))]
  intro i
  have h : (Scheme.IsLocallyDirected.openCover (diagram k)).f i ≫ structureMap k =
      (toSpecKCocone k).ι.app i := colimit.ι_desc (toSpecKCocone k) i
  rw [h]
  match i with
  | none =>
    exact inferInstanceAs (LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (kToOverlapRing k))))
  | some _ => exact inferInstanceAs (LocallyOfFiniteType (chartToSpecK k))

instance : IsLocallyNoetherian (scheme k) :=
  LocallyOfFiniteType.isLocallyNoetherian (structureMap k)

instance instNonemptyDiagramObj (i : WidePushoutShape (Fin 2)) :
    Nonempty ((diagram k).obj i) := by
  match i with
  | none => exact inferInstanceAs (Nonempty (overlap k))
  | some _ => exact inferInstanceAs (Nonempty (chart k))

-- Mathlib's instance `IsOpenImmersion (colimit.ι F i)` is itself stated under this option.
set_option backward.isDefEq.respectTransparency.types false in
instance : IsOpenImmersion (chartZero k) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (diagram k) (some 0)))

set_option backward.isDefEq.respectTransparency.types false in
instance : IsOpenImmersion (chartOne k) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (diagram k) (some 1)))

set_option backward.isDefEq.respectTransparency.types false in
instance instIsOpenImmersionOverlapι : IsOpenImmersion (overlapι k) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (diagram k) none))

/-! ## The point at infinity -/

/-- `t` generates a prime ideal of `k[t]`. -/
instance : (Ideal.span {(Polynomial.X : Polynomial k)}).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

/-- The origin `t = 0` of a chart, as a point of `Spec k[t]`. -/
def origin : chart k := ⟨Ideal.span {(Polynomial.X : Polynomial k)}, inferInstance⟩

/-- **The point at infinity of `ℙ¹_k`**: the origin of the second chart. -/
def infty : scheme k := (chartOne k).base (origin k)

/-- The image of the overlap in the first chart is the basic open set `D(t)`. -/
lemma range_overlapToChartZero :
    Set.range (overlapToChartZero k).base =
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) :
        Set (PrimeSpectrum (Polynomial k))) := by
  have h := Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (Polynomial k))
    (Polynomial.X : Polynomial k)
  exact congrArg (fun U : (chart k).Opens => (U : Set (chart k))) h

/-- The origin does not lie in the overlap. -/
lemma origin_notMem_range_overlapToChartZero :
    origin k ∉ Set.range (overlapToChartZero k).base := by
  rw [range_overlapToChartZero]
  intro h
  exact (PrimeSpectrum.mem_basicOpen _ _).mp h (Ideal.mem_span_singleton_self _)

/-- Points of a chart other than the origin lie in the overlap. -/
lemma mem_range_overlapToChartZero_of_ne (y : chart k) (hy : y ≠ origin k) :
    y ∈ Set.range (overlapToChartZero k).base := by
  rw [range_overlapToChartZero]
  have hX : (Polynomial.X : Polynomial k) ∉ y.asIdeal := by
    intro hmem
    refine hy (PrimeSpectrum.ext ?_)
    have hmax : (Ideal.span {(Polynomial.X : Polynomial k)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
    exact (hmax.eq_of_le y.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hmem)).symm
  exact (PrimeSpectrum.mem_basicOpen _ _).mpr hX

/-- Points of the second chart other than its origin lie in the overlap. -/
lemma mem_range_overlapToChartOne_of_ne (y : chart k) (hy : y ≠ origin k) :
    y ∈ Set.range (overlapToChartOne k).base := by
  rw [range_overlapToChartOne]
  exact mem_range_overlapToChartZero_of_ne k y hy

/-- The gluing map of the overlap factors through the first chart. -/
lemma mem_range_chartZero_of_mem_range_overlap (z : overlap k) :
    (overlapι k).base z ∈ Set.range (chartZero k).base := by
  refine ⟨(overlapToChartZero k).base z, ?_⟩
  rw [← Scheme.Hom.comp_apply, overlapToChartZero_comp]

/-- **The first chart of `ℙ¹_k` is exactly the complement of the point at infinity.** -/
lemma range_chartZero_eq_compl_infty :
    Set.range (chartZero k).base = {infty k}ᶜ := by
  apply Set.eq_of_subset_of_subset
  · intro x hx hmem
    rw [Set.mem_singleton_iff] at hmem
    obtain ⟨y, hy⟩ := hx
    have heq : (chartOne k).base (origin k) = (chartZero k).base y := by
      rw [hy]
      exact hmem.symm
    obtain ⟨l, fi, fj, z, hzi, hzj⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := diagram k)).mp heq
    cases fj with
    | id X => cases fi
    | init b =>
      cases fi with
      | init a =>
        refine origin_notMem_range_overlapToChartZero k ?_
        rw [← hzi, ← range_overlapToChartOne, map_init_one]
        exact ⟨z, rfl⟩
  · intro x hx
    rcases mem_range_chart k x with h | ⟨y, hy⟩
    · exact h
    · have hyne : y ≠ origin k := by
        intro hy'
        exact hx (by rw [Set.mem_singleton_iff, ← hy, hy']; rfl)
      obtain ⟨z, hz⟩ := mem_range_overlapToChartOne_of_ne k y hyne
      have h1 : (chartOne k).base ((overlapToChartOne k).base z)
          = (overlapι k).base z := by
        rw [← Scheme.Hom.comp_apply, overlapToChartOne_comp]
      have h2 : (overlapι k).base z = x := by rw [← h1, hz, hy]
      rw [← h2]
      exact mem_range_chartZero_of_mem_range_overlap k z

end

end GromovWitten.AlgebraicGeometry.ProjectiveLine
