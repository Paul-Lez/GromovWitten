/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperCurveDegreeTranscendental

/-!
# `deg (div r) = 0` on a regular proper curve, unconditionally

This file constructs the `ChartPresentation` which is the last remaining hypothesis of
`ProperCurveDegree.RegularProperCurve.degreeCycle_principalCycle_eq_zero`, and deduces the
unconditional statement

* `RegularProperCurve.degreeCycle_principalCycle_eq_zero'` :
  `degreeCycle X.f (X.W.principalCycle r) = 0` for every nonzero rational function `r` on a
  regular proper curve `X`.

The presentation is the obvious one: the two chart rings are the rings of sections
`Γ(W, regularLocus r)` and `Γ(W, regularLocus r⁻¹)` themselves, with the `k`-algebra structures of
`RationalFunction.kSection` and the elements `regularSection r`, `regularSection r⁻¹`.  What has to
be provided is the list of ring-theoretic properties of these two rings and the comparison of the
two fibre dimensions:

* both rings are `k[t]`-algebras via `RationalFunction.toChartHom` (`t` acting as the section
  representing `r`, resp. `r⁻¹`), module-finite over `k[t]` by
  `ProperCurveDegree.finite_toChartHom`, and the structure map is injective by
  `ProperCurveDegree.injective_toChartHom_regularSection`;
* hence they are Noetherian, of finite type over `k`, integral over `k[t]`, and of Krull dimension
  at most one, the last by `krullDimLE_one_of_moduleFinite` below: a module-finite extension of a
  principal ideal domain has Krull dimension at most that of the base, because a nonzero prime
  contracts to a nonzero prime (`Ideal.IsIntegral.comap_ne_bot`) and lies over a maximal ideal
  (`Ideal.IsIntegral.isMaximal_of_isMaximal_comap`);
* the localisations of the two rings away from `t` are both the ring of sections over the
  intersection of the two domains of definition (`ProperCurveDegree.basicOpen_regularSection_inv`,
  `IsAffineOpen.isLocalization_basicOpen`), and the two images of `t` there are mutually inverse
  (`RationalFunction.ChartPair.res_mul_res`), so the comparison follows from
  `ProperCurveDegree.finrank_eq_of_isLocalizationAway`.

## Main declarations

* `krullDimLE_one_of_moduleFinite` — a module-finite algebra over a principal ideal domain which is
  a domain has Krull dimension at most one.
* `injective_eval₂_inv` — the inverse of a transcendental rational function is transcendental.
* `resRingEquiv` — the restriction isomorphism between the sections over two equal open subsets.
* `ProperCurveDegree.chartPresentation` — the chart presentation of the two domains of definition
  of a rational function whose associated morphism to `ℙ¹_k` and the one associated to its inverse
  are finite.
* `RegularProperCurve.chartPresentation`, `RegularProperCurve.degreeCycle_principalCycle_eq_zero'`
  — the unconditional vanishing of the degree of a principal divisor on a regular proper curve, and
  `RegularProperCurve.degreeCycle_principalCycle_units_eq_zero`, its form for a unit of the function
  field.
* `RegularProperCurve.degreeCycle_divisor_eq` — the degree of a generator of
  `totalRationalRelations` equals the degree of the corresponding principal divisor computed on its
  integral closed subscheme.  Together with the previous item this reduces the well-definedness of
  the degree map on the Chow group of zero-cycles of a regular proper curve to the statement that
  every integral closed subscheme of a curve is either the curve itself or a (zero-dimensional)
  point, which is not proved here.

-/

universe u

open CategoryTheory AlgebraicGeometry Topology

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## Krull dimension of a module-finite extension of a principal ideal domain -/

/-- **A domain which is module-finite over a principal ideal domain has Krull dimension at most
one.**  A nonzero prime `I` contracts to a nonzero prime of the base, which is maximal because the
base has dimension at most one, and then `I` itself is maximal by going up. -/
theorem krullDimLE_one_of_moduleFinite (R B : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B] :
    Ring.KrullDimLE 1 B := by
  refine Ring.KrullDimLE.mk₁' fun I hIne hprime => ?_
  have _ := hprime
  have hne : I.comap (algebraMap R B) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot R hIne
  have hp : (I.comap (algebraMap R B)).IsPrime := Ideal.IsPrime.comap _
  have _ := hp
  exact Ideal.IsIntegral.isMaximal_of_isMaximal_comap I
    (Ideal.isMaximal_of_isPrime_of_ne_bot _ hne)

/-! ## Transcendence of the inverse of a rational function -/

/-- **If a rational function is transcendental over the base field, so is its inverse.**
Transcendence is expressed, as everywhere in this development, as injectivity of the evaluation
map `k[t] ⟶ K(W)`. -/
theorem injective_eval₂_inv {k : Type u} [Field k] {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] (f : W ⟶ Spec (CommRingCat.of k))
    (r : W.functionField)
    (htr : Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField f).hom r)) :
    Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField f).hom r⁻¹) := by
  let _ : Algebra k W.functionField := (RationalFunction.kFunctionField f).hom.toAlgebra
  have h1 : Transcendental k r := by
    rw [transcendental_iff_injective]
    exact htr
  have h2 : Transcendental k r⁻¹ := fun hal => h1 (IsAlgebraic.inv_iff.mp hal)
  rw [transcendental_iff_injective] at h2
  exact h2

/-! ## The restriction isomorphism between two equal open subsets -/

/-- **The restriction isomorphism between the rings of sections over two equal open subsets** of a
scheme. -/
noncomputable def resRingEquiv {W : Scheme.{u}} {U V : W.Opens} (h : U = V) :
    Γ(W, U) ≃+* Γ(W, V) :=
  (W.presheaf.mapIso (eqToIso (congrArg Opposite.op h))).commRingCatIsoToRingEquiv

/-- `resRingEquiv` is the restriction map. -/
@[simp] lemma resRingEquiv_apply {W : Scheme.{u}} {U V : W.Opens} (h : U = V) (s : Γ(W, U)) :
    resRingEquiv h s = (W.presheaf.map (homOfLE h.ge).op) s := by
  subst h
  simp [resRingEquiv]
  rfl

/-- Restriction maps of the structure sheaf compose. -/
lemma map_map_apply {W : Scheme.{u}} {U V Z : W.Opens} (h₁ : V ≤ U) (h₂ : Z ≤ V) (s : Γ(W, U)) :
    (W.presheaf.map (homOfLE h₂).op) ((W.presheaf.map (homOfLE h₁).op) s)
      = (W.presheaf.map (homOfLE (h₂.trans h₁)).op) s := by
  rw [← ConcreteCategory.comp_apply, ← W.presheaf.map_comp]
  rfl

/-- The `k`-algebra structures on the rings of sections are compatible with restriction. -/
lemma kSection_res_apply {k : Type u} [Field k] {W : Scheme.{u}}
    (f : W ⟶ Spec (CommRingCat.of k)) {U V : W.Opens} (h : V ≤ U) (a : k) :
    (W.presheaf.map (homOfLE h).op) ((RationalFunction.kSection f U).hom a)
      = (RationalFunction.kSection f V).hom a := by
  have h2 := congrArg (fun g : CommRingCat.of k ⟶ Γ(W, V) => g.hom a)
    (RationalFunction.kSection_res f h)
  simpa using h2

namespace ProperCurveDegree

open ProjectiveLine

variable {k : Type u} [Field k] {W : Scheme.{u}} [_root_.AlgebraicGeometry.IsIntegral W]
  (f : W ⟶ Spec (CommRingCat.of k))
  (hv : ∀ x : W, ValuationRing (W.presheaf.stalk x)) (r : W.functionField)

include hv in
/-- **The chart presentation of the two domains of definition of a rational function** `r` whose
associated morphism `W ⟶ ℙ¹_k`, and the one associated to `r⁻¹`, are finite.  The two chart rings
are the rings of sections themselves. -/
noncomputable def chartPresentation (hr : r ≠ 0)
    (htr : Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField f).hom r))
    (hfin : IsFinite (RationalFunction.toProjectiveLine f hv r hr))
    (hfin' : IsFinite (RationalFunction.toProjectiveLine f hv r⁻¹ (inv_ne_zero hr))) :
    ChartPresentation f r := by
  have hr' : r⁻¹ ≠ 0 := inv_ne_zero hr
  have htr' := injective_eval₂_inv f r htr
  have hU₀ : IsAffineOpen (Scheme.regularLocus r) :=
    isAffineOpen_regularLocus_of_isFinite f hv r hr hfin
  have hU₁ : IsAffineOpen (Scheme.regularLocus r⁻¹) :=
    isAffineOpen_regularLocus_of_isFinite f hv r⁻¹ hr' hfin'
  have _ : Nonempty ↥(Scheme.regularLocus r) := ⟨⟨_, Scheme.genericPoint_mem_regularLocus r⟩⟩
  have _ : Nonempty ↥(Scheme.regularLocus r⁻¹) := ⟨⟨_, Scheme.genericPoint_mem_regularLocus r⁻¹⟩⟩
  have _ : IsDomain ↥Γ(W, Scheme.regularLocus r) :=
    _root_.AlgebraicGeometry.IsIntegral.component_integral _
  have _ : IsDomain ↥Γ(W, Scheme.regularLocus r⁻¹) :=
    _root_.AlgebraicGeometry.IsIntegral.component_integral _
  let _ : Algebra k ↥Γ(W, Scheme.regularLocus r) :=
    (RationalFunction.kSection f (Scheme.regularLocus r)).hom.toAlgebra
  let _ : Algebra k ↥Γ(W, Scheme.regularLocus r⁻¹) :=
    (RationalFunction.kSection f (Scheme.regularLocus r⁻¹)).hom.toAlgebra
  let _ : Algebra (Polynomial k) ↥Γ(W, Scheme.regularLocus r) :=
    (RationalFunction.toChartHom f (Scheme.regularLocus r)
      (Scheme.regularSection r)).hom.toAlgebra
  let _ : Algebra (Polynomial k) ↥Γ(W, Scheme.regularLocus r⁻¹) :=
    (RationalFunction.toChartHom f (Scheme.regularLocus r⁻¹)
      (Scheme.regularSection r⁻¹)).hom.toAlgebra
  have _ : IsScalarTower k (Polynomial k) ↥Γ(W, Scheme.regularLocus r) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    have h2 := congrArg (fun g : CommRingCat.of k ⟶ Γ(W, Scheme.regularLocus r) => g.hom a)
      (RationalFunction.algebraMap_comp_toChartHom f (Scheme.regularLocus r)
        (Scheme.regularSection r))
    exact h2.symm
  have _ : IsScalarTower k (Polynomial k) ↥Γ(W, Scheme.regularLocus r⁻¹) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    have h2 := congrArg (fun g : CommRingCat.of k ⟶ Γ(W, Scheme.regularLocus r⁻¹) => g.hom a)
      (RationalFunction.algebraMap_comp_toChartHom f (Scheme.regularLocus r⁻¹)
        (Scheme.regularSection r⁻¹))
    exact h2.symm
  have _ : Module.Finite (Polynomial k) ↥Γ(W, Scheme.regularLocus r) :=
    finite_toChartHom f hv r hr hfin hU₀
  have _ : Module.Finite (Polynomial k) ↥Γ(W, Scheme.regularLocus r⁻¹) :=
    finite_toChartHom f hv r⁻¹ hr' hfin' hU₁
  have _ : Algebra.FiniteType k ↥Γ(W, Scheme.regularLocus r) :=
    Algebra.FiniteType.trans (S := Polynomial k) inferInstance inferInstance
  have _ : Algebra.FiniteType k ↥Γ(W, Scheme.regularLocus r⁻¹) :=
    Algebra.FiniteType.trans (S := Polynomial k) inferInstance inferInstance
  have _ : IsNoetherianRing ↥Γ(W, Scheme.regularLocus r) :=
    Algebra.FiniteType.isNoetherianRing k _
  have _ : IsNoetherianRing ↥Γ(W, Scheme.regularLocus r⁻¹) :=
    Algebra.FiniteType.isNoetherianRing k _
  have _ : Ring.KrullDimLE 1 ↥Γ(W, Scheme.regularLocus r) :=
    krullDimLE_one_of_moduleFinite (Polynomial k) _
  have _ : Ring.KrullDimLE 1 ↥Γ(W, Scheme.regularLocus r⁻¹) :=
    krullDimLE_one_of_moduleFinite (Polynomial k) _
  have hinj₀ : Function.Injective
      (algebraMap (Polynomial k) ↥Γ(W, Scheme.regularLocus r)) :=
    injective_toChartHom_regularSection f r htr
  have hinj₁ : Function.Injective
      (algebraMap (Polynomial k) ↥Γ(W, Scheme.regularLocus r⁻¹)) :=
    injective_toChartHom_regularSection f r⁻¹ htr'
  have hX₀ : algebraMap (Polynomial k) ↥Γ(W, Scheme.regularLocus r) Polynomial.X
      = Scheme.regularSection r := by
    simp [RingHom.algebraMap_toAlgebra, RationalFunction.toChartHom]
  have hX₁ : algebraMap (Polynomial k) ↥Γ(W, Scheme.regularLocus r⁻¹) Polynomial.X
      = Scheme.regularSection r⁻¹ := by
    simp [RingHom.algebraMap_toAlgebra, RationalFunction.toChartHom]
  have _ : IsLocalization.Away
      (algebraMap (Polynomial k) ↥Γ(W, Scheme.regularLocus r) Polynomial.X)
      ↥Γ(W, W.basicOpen (Scheme.regularSection r)) := by
    rw [hX₀]
    exact hU₀.isLocalization_basicOpen _
  have _ : IsLocalization.Away
      (algebraMap (Polynomial k) ↥Γ(W, Scheme.regularLocus r⁻¹) Polynomial.X)
      ↥Γ(W, W.basicOpen (Scheme.regularSection r⁻¹)) := by
    rw [hX₁]
    exact hU₁.isLocalization_basicOpen _
  have hbo : W.basicOpen (Scheme.regularSection r) = W.basicOpen (Scheme.regularSection r⁻¹) :=
    (basicOpen_regularSection_inv hv r hr).symm
  have ea₀ : ∀ x : Γ(W, Scheme.regularLocus r), algebraMap ↥Γ(W, Scheme.regularLocus r)
      ↥Γ(W, W.basicOpen (Scheme.regularSection r)) x
      = W.presheaf.map (homOfLE (W.basicOpen_le (Scheme.regularSection r))).op x := fun _ => rfl
  have ea₁ : ∀ x : Γ(W, Scheme.regularLocus r⁻¹), algebraMap ↥Γ(W, Scheme.regularLocus r⁻¹)
      ↥Γ(W, W.basicOpen (Scheme.regularSection r⁻¹)) x
      = W.presheaf.map (homOfLE (W.basicOpen_le (Scheme.regularSection r⁻¹))).op x := fun _ => rfl
  have hZ₀ : W.basicOpen (Scheme.regularSection r⁻¹) ≤ Scheme.regularLocus r :=
    hbo.ge.trans (W.basicOpen_le (Scheme.regularSection r))
  have hZ₁ : W.basicOpen (Scheme.regularSection r⁻¹) ≤ Scheme.regularLocus r⁻¹ :=
    W.basicOpen_le (Scheme.regularSection r⁻¹)
  have hgen : genericPoint W ∈ W.basicOpen (Scheme.regularSection r⁻¹) :=
    le_of_eq ((inf_regularLocus_eq_basicOpen hv r hr).trans hbo)
      ⟨Scheme.genericPoint_mem_regularLocus r, Scheme.genericPoint_mem_regularLocus r⁻¹⟩
  have hmul : W.presheaf.map (homOfLE hZ₀).op (Scheme.regularSection r) *
      W.presheaf.map (homOfLE hZ₁).op (Scheme.regularSection r⁻¹) = 1 :=
    (RationalFunction.chartPairOfValuationRing hv r).res_mul_res hr hZ₀ hZ₁ hgen
  have hΦX : (resRingEquiv hbo) (algebraMap ↥Γ(W, Scheme.regularLocus r)
        ↥Γ(W, W.basicOpen (Scheme.regularSection r))
        (algebraMap (Polynomial k) ↥Γ(W, Scheme.regularLocus r) Polynomial.X)) *
      algebraMap ↥Γ(W, Scheme.regularLocus r⁻¹)
        ↥Γ(W, W.basicOpen (Scheme.regularSection r⁻¹))
        (algebraMap (Polynomial k) ↥Γ(W, Scheme.regularLocus r⁻¹) Polynomial.X) = 1 := by
    rw [hX₀, hX₁, ea₀, ea₁, resRingEquiv_apply, map_map_apply]
    exact hmul
  have hΦC : ∀ a : k, (resRingEquiv hbo) (algebraMap ↥Γ(W, Scheme.regularLocus r)
        ↥Γ(W, W.basicOpen (Scheme.regularSection r))
        (algebraMap (Polynomial k) ↥Γ(W, Scheme.regularLocus r) (Polynomial.C a)))
      = algebraMap ↥Γ(W, Scheme.regularLocus r⁻¹)
        ↥Γ(W, W.basicOpen (Scheme.regularSection r⁻¹))
        (algebraMap (Polynomial k) ↥Γ(W, Scheme.regularLocus r⁻¹) (Polynomial.C a)) := by
    intro a
    have hC₀ : algebraMap (Polynomial k) ↥Γ(W, Scheme.regularLocus r) (Polynomial.C a)
        = (RationalFunction.kSection f (Scheme.regularLocus r)).hom a := by
      simp [RingHom.algebraMap_toAlgebra, RationalFunction.toChartHom]
    have hC₁ : algebraMap (Polynomial k) ↥Γ(W, Scheme.regularLocus r⁻¹) (Polynomial.C a)
        = (RationalFunction.kSection f (Scheme.regularLocus r⁻¹)).hom a := by
      simp [RingHom.algebraMap_toAlgebra, RationalFunction.toChartHom]
    rw [hC₀, hC₁, ea₀, ea₁, resRingEquiv_apply, map_map_apply, kSection_res_apply,
      kSection_res_apply]
  have hrank : Module.finrank k (↥Γ(W, Scheme.regularLocus r) ⧸
        Ideal.span {Scheme.regularSection r})
      = Module.finrank k (↥Γ(W, Scheme.regularLocus r⁻¹) ⧸
        Ideal.span {Scheme.regularSection r⁻¹}) := by
    rw [← hX₀, ← hX₁, finrank_quotient_span_eq_finrank_of_injective _ hinj₀,
      finrank_quotient_span_eq_finrank_of_injective _ hinj₁]
    exact finrank_eq_of_isLocalizationAway _ _ _ _ hinj₀ hinj₁ (resRingEquiv hbo) hΦX hΦC
  exact
    { B₀ := ↥Γ(W, Scheme.regularLocus r)
      B₁ := ↥Γ(W, Scheme.regularLocus r⁻¹)
      e₀ := Iso.refl _
      e₁ := Iso.refl _
      he₀ := by
        rw [Iso.refl_hom, Category.comp_id]
        rfl
      he₁ := by
        rw [Iso.refl_hom, Category.comp_id]
        rfl
      b₀ := Scheme.regularSection r
      b₁ := Scheme.regularSection r⁻¹
      hb₀ := regularSection_ne_zero r hr
      hb₁ := regularSection_ne_zero r⁻¹ hr'
      hbe₀ := rfl
      hbe₁ := rfl
      hrank := hrank }

namespace RegularProperCurve

variable (X : _root_.GromovWitten.AlgebraicGeometry.RegularProperCurve k)

/-- **The chart presentation of the two domains of definition of a rational function
transcendental over `k` on a regular proper curve.**  Both morphisms to `ℙ¹_k` are finite because
both `r` and `r⁻¹` are transcendental over `k`. -/
noncomputable def chartPresentation (r : X.W.functionField) (hr : r ≠ 0)
    (htr : Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField X.f).hom r)) :
    ChartPresentation X.f r :=
  ProperCurveDegree.chartPresentation X.f X.valuationRing_stalk r hr htr
    (isFinite_toProjectiveLine X r hr htr)
    (isFinite_toProjectiveLine X r⁻¹ (inv_ne_zero hr) (injective_eval₂_inv X.f r htr))

/-- **The degree of a principal divisor on a regular proper curve vanishes.**  This is the
unconditional form of `degreeCycle_principalCycle_eq_zero`: the chart presentation which the latter
takes as a hypothesis is now constructed in `chartPresentation`. -/
theorem degreeCycle_principalCycle_eq_zero' (r : X.W.functionField) (hr : r ≠ 0) :
    have _ := X.isNoetherian
    ZeroCycleDegree.degreeCycle X.f (X.W.principalCycle r) = 0 :=
  degreeCycle_principalCycle_eq_zero X r hr fun htr => chartPresentation X r hr htr

/-- **The degree of the principal divisor of a unit of the function field of a regular proper curve
vanishes.**  This is the shape in which the vanishing enters the Chow group of zero-cycles: the
rational function of a `RationalFunctionGenerator` is a unit of the function field of its integral
closed subscheme. -/
theorem degreeCycle_principalCycle_units_eq_zero (u : X.W.functionFieldˣ) :
    have _ := X.isNoetherian
    ZeroCycleDegree.degreeCycle X.f (X.W.principalCycle (u : X.W.functionField)) = 0 :=
  degreeCycle_principalCycle_eq_zero' X (u : X.W.functionField) u.ne_zero

/-- **The degree of a generator of the rational relations is the degree of the corresponding
principal divisor computed on its integral closed subscheme.**  This reduces the well-definedness
of the degree map on the Chow group of zero-cycles of a regular proper curve to the vanishing of
the degree of a principal divisor on each integral closed subscheme of the curve, the curve itself
being covered by `degreeCycle_principalCycle_eq_zero'`. -/
theorem degreeCycle_divisor_eq (dimension : DimensionFunction X.W)
    (g : RationalFunctionGenerator X.W) :
    have _ := X.isNoetherian
    have _ : CompactSpace ↥g.subspace.scheme :=
      Topology.IsClosedEmbedding.compactSpace (h := X.isNoetherian.toCompactSpace)
        g.subspace.inclusion.isClosedEmbedding
    ZeroCycleDegree.degreeCycle X.f (g.divisor dimension) =
      ZeroCycleDegree.degreeCycle (g.subspace.inclusion ≫ X.f)
        (g.subspace.scheme.principalCycle (g.function : g.subspace.scheme.functionField)) := by
  intro _ _
  exact NormPushforward.degreeCycle_map_eq X.f g.subspace.inclusion _ _ _ fun _ _ => rfl

end RegularProperCurve

end ProperCurveDegree

end GromovWitten.AlgebraicGeometry.IntersectionTheory
