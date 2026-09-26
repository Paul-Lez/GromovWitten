/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperCurveDegree
import GromovWitten.AlgebraicGeometry.Curves.ProperCurveTopology

/-!
# The degree of a principal divisor on a regular proper curve

This file completes the proof that the degree of a principal divisor on a regular proper curve
over a field `k` vanishes, starting from the reduction of
`IntersectionTheory/ProperCurveDegree.lean`.

The argument splits according to whether the rational function `r` is algebraic or transcendental
over `k`.

## The algebraic case

If `r` is algebraic over `k` then `r` and `r⁻¹` both lie in every local ring of `W`: the local
ring `𝒪_{W,x}` is a valuation ring, so one of `r`, `r⁻¹` lies in it, and the other one is then
obtained from `IsIntegral.inv_mem` (a `k`-subalgebra of a field containing an element integral
over `k` contains its inverse).  Hence `r` is a unit at every point, the principal cycle of `r`
vanishes identically, and so does its degree.

## The transcendental case

If `r` is transcendental over `k` then the morphism `p : W ⟶ ℙ¹_k` of
`RationalFunction.toProjectiveLine` is finite, the two domains of definition of `r` and `r⁻¹` are
the preimages of the two standard charts of `ℙ¹_k` and hence affine, and the two partial degrees of
`div r` over them are the `k`-dimensions of the two chart fibres, both equal to `[K(W) : k(t)]`.
This file supplies everything except the identification of the preimages of the two charts with the
two domains of definition and the comparison of the two chart dimensions: the degree of `div r`
vanishes as soon as the two domains of definition are affine with equal chart dimension
(`degreeCycle_principalCycle_eq_zero_of_isAffineOpen`).

## Main declarations

* `kStalk`, `algebraMap_kStalk` — the `k`-algebra structure on a local ring of `W` induced by the
  structure morphism, and its compatibility with the one on the function field.
* `exists_algebraMap_eq_and_exists_algebraMap_eq_inv` — the key algebraic fact: an element of a
  field `K`, algebraic over a field `k` which maps into a valuation subring `O` with fraction
  field `K`, lies in `O` together with its inverse.
* `mem_regularLocus_inf_of_monic` — a rational function algebraic over `k` is regular, together
  with its inverse, at every point.
* `principalCycle_eq_zero_of_monic`, `degreeCycle_principalCycle_eq_zero_of_monic`,
  `RegularProperCurve.degreeCycle_principalCycle_eq_zero_of_monic` — the algebraic case of the main
  theorem, unconditionally.
* `exists_monic_of_not_injective`, `degreeCycle_principalCycle_eq_zero_of_not_injective`,
  `RegularProperCurve.degreeCycle_principalCycle_eq_zero_of_not_injective` — the algebraic
  branch of the case split, phrased with the negation of the transcendence hypothesis of
  `RationalFunction.isFinite_toProjectiveLine`.
* `fromSpec_comp_structureMap` — the canonical open immersion `Spec Γ(W, U) ⟶ W` of an affine open
  is a morphism of `k`-schemes.
* `dominantFunctionFieldMap_germ`, `dominantFunctionFieldMap_fromSpec_germ` — the function-field
  pullback of the rational function determined by a section is the rational function determined by
  the pulled-back section; for `Spec Γ(W, U) ⟶ W` it is the image of the section in the fraction
  field of `Γ(W, U)`.
* `finsum_eq_finrank_of_isAffineOpen` — the partial degree of `div σ` over an affine open `U` is
  `dim_k (Γ(W, U) ⧸ (σ))`.
* `degreeCycle_principalCycle_eq_zero_of_isAffineOpen`,
  `RegularProperCurve.degreeCycle_principalCycle_eq_zero_of_isAffineOpen` — the degree of a
  principal divisor vanishes as soon as the two domains of definition are affine with equal chart
  dimension.
* `isAffineOpen_preimage_chart`, `regularLocus_le_preimage_chartZero` — first steps towards the
  remaining bridge: the preimage of a standard chart of `ℙ¹_k` under a finite morphism is affine
  and contains the domain of definition of `r`.

-/

universe u

open CategoryTheory AlgebraicGeometry Topology

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperCurveDegree

variable {k : Type u} [Field k]

/-! ## The `k`-algebra structure on the local rings -/

/-- The `k`-algebra structure on the local ring of `W` at `x` induced by the structure morphism
`f : W ⟶ Spec k`: it is the composition of `k → Γ(W, ⊤)` with the germ map at `x`. -/
noncomputable def kStalk {W : Scheme.{u}} (f : W ⟶ Spec (CommRingCat.of k)) (x : W) :
    CommRingCat.of k ⟶ W.presheaf.stalk x :=
  RationalFunction.kSection f ⊤ ≫ W.presheaf.germ ⊤ x trivial

/-- The `k`-algebra structure on `𝒪_{W,x}` is compatible with the one on the function field:
composing `k → 𝒪_{W,x}` with `𝒪_{W,x} → K(W)` gives `k → K(W)`. -/
theorem algebraMap_kStalk {W : Scheme.{u}} [_root_.AlgebraicGeometry.IsIntegral W]
    (f : W ⟶ Spec (CommRingCat.of k)) (x : W) (c : k) :
    algebraMap (W.presheaf.stalk x) W.functionField ((kStalk f x).hom c) =
      (RationalFunction.kFunctionField f).hom c := by
  have h : genericPoint W ⤳ x := (genericPoint_spec W).specializes trivial
  have key : W.presheaf.germ ⊤ x trivial ≫ W.presheaf.stalkSpecializes h =
      W.presheaf.germ ⊤ (genericPoint W) trivial :=
    W.presheaf.germ_stalkSpecializes (U := ⊤) (y := x) trivial h
  have key2 := congrArg (fun g : Γ(W, ⊤) ⟶ W.functionField =>
      g.hom ((RationalFunction.kSection f ⊤).hom c)) key
  simp only [ConcreteCategory.comp_apply] at key2
  simpa only [kStalk, RationalFunction.kFunctionField, ConcreteCategory.comp_apply,
    RingHom.algebraMap_toAlgebra] using key2

/-! ## The algebraic case -/

/-- **An element of a field which is algebraic over a subfield contained in a valuation subring is
a unit of that valuation ring.**  Concretely: `O` is a valuation ring with fraction field `K`,
`ψ : k → O` makes `O` a `k`-algebra, and `r : K` is a root of a monic polynomial `p` over `k`.
Then both `r` and `r⁻¹` lie in the image of `O`. -/
theorem exists_algebraMap_eq_and_exists_algebraMap_eq_inv
    {K O : Type u} [Field K] [CommRing O] [IsDomain O] [ValuationRing O] [Algebra O K]
    [IsFractionRing O K] (ψ : k →+* O) (r : K)
    (p : Polynomial k) (hp : p.Monic)
    (hpr : Polynomial.eval₂ ((algebraMap O K).comp ψ) r p = 0) :
    (∃ o : O, algebraMap O K o = r) ∧ ∃ o : O, algebraMap O K o = r⁻¹ := by
  let _ : Algebra k O := ψ.toAlgebra
  let _ : Algebra k K := ((algebraMap O K).comp ψ).toAlgebra
  have hmapk : (algebraMap k K) = (algebraMap O K).comp ψ := rfl
  let _ : IsScalarTower k O K := IsScalarTower.of_algebraMap_eq' hmapk
  have hint : IsIntegral k r := ⟨p, hp, by rw [hmapk]; exact hpr⟩
  set A : Subalgebra k K := (IsScalarTower.toAlgHom k O K).range with hA
  have hmemA : ∀ y : K, y ∈ A ↔ ∃ o : O, algebraMap O K o = y := by
    intro y
    rw [hA]
    exact ⟨fun ⟨o, ho⟩ => ⟨o, ho⟩, fun ⟨o, ho⟩ => ⟨o, ho⟩⟩
  have hboth : r ∈ A ∧ r⁻¹ ∈ A := by
    rcases ValuationRing.isInteger_or_isInteger O r with ⟨o, ho⟩ | ⟨o, ho⟩
    · exact ⟨(hmemA r).mpr ⟨o, ho⟩, hint.inv_mem ((hmemA r).mpr ⟨o, ho⟩)⟩
    · have h1 : r⁻¹ ∈ A := (hmemA r⁻¹).mpr ⟨o, ho⟩
      exact ⟨hint.mem_of_inv_mem h1, h1⟩
  exact ⟨(hmemA r).mp hboth.1, (hmemA r⁻¹).mp hboth.2⟩


/-- **A rational function which is a root of a monic polynomial over `k` is regular, together with
its inverse, at every point** of a scheme all of whose local rings are valuation rings. -/
theorem mem_regularLocus_inf_of_monic {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] (f : W ⟶ Spec (CommRingCat.of k))
    (hv : ∀ x : W, ValuationRing (W.presheaf.stalk x)) (r : W.functionField)
    (p : Polynomial k) (hp : p.Monic)
    (hpr : Polynomial.eval₂ (RationalFunction.kFunctionField f).hom r p = 0) (x : W) :
    x ∈ Scheme.regularLocus r ⊓ Scheme.regularLocus r⁻¹ := by
  have hvx := hv x
  have hcomp : ((algebraMap (W.presheaf.stalk x) W.functionField).comp (kStalk f x).hom) =
      (RationalFunction.kFunctionField f).hom :=
    RingHom.ext fun c => algebraMap_kStalk f x c
  obtain ⟨h0, h1⟩ := exists_algebraMap_eq_and_exists_algebraMap_eq_inv
    (K := W.functionField) (O := W.presheaf.stalk x) (kStalk f x).hom r p hp
    (by rw [hcomp]; exact hpr)
  exact ⟨Scheme.mem_regularLocus_iff.mpr h0, Scheme.mem_regularLocus_iff.mpr h1⟩

/-- **The principal cycle of a rational function algebraic over `k` vanishes identically**: such a
function is a unit in every local ring, so its order of vanishing is zero everywhere. -/
theorem principalCycle_eq_zero_of_monic {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    (f : W ⟶ Spec (CommRingCat.of k))
    (hv : ∀ x : W, ValuationRing (W.presheaf.stalk x)) (r : W.functionField)
    (p : Polynomial k) (hp : p.Monic)
    (hpr : Polynomial.eval₂ (RationalFunction.kFunctionField f).hom r p = 0) :
    W.principalCycle r = 0 := by
  refine Function.locallyFinsuppWithin.coe_injective (funext fun x => ?_)
  have hx := mem_regularLocus_inf_of_monic f hv r p hp hpr x
  simp only [Scheme.principalCycle_apply, ord_eq_zero_of_mem_regularLocus_inf r hx]
  rfl

/-- **The degree of the principal divisor of a rational function algebraic over `k` vanishes.**
This is the easy case of the main theorem: the divisor itself is zero. -/
theorem degreeCycle_principalCycle_eq_zero_of_monic {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    [CompactSpace W] (f : W ⟶ Spec (CommRingCat.of k))
    (hv : ∀ x : W, ValuationRing (W.presheaf.stalk x)) (r : W.functionField)
    (p : Polynomial k) (hp : p.Monic)
    (hpr : Polynomial.eval₂ (RationalFunction.kFunctionField f).hom r p = 0) :
    ZeroCycleDegree.degreeCycle f (W.principalCycle r) = 0 := by
  rw [principalCycle_eq_zero_of_monic f hv r p hp hpr, map_zero]

/-- **A rational function which is not transcendental over `k` is a root of a monic polynomial.**
Dividing by the leading coefficient turns any nonzero polynomial relation into a monic one. -/
theorem exists_monic_of_not_injective {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] (f : W ⟶ Spec (CommRingCat.of k))
    (r : W.functionField)
    (htr : ¬ Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField f).hom r)) :
    ∃ p : Polynomial k, p.Monic ∧
      Polynomial.eval₂ (RationalFunction.kFunctionField f).hom r p = 0 := by
  rw [injective_iff_map_eq_zero] at htr
  push Not at htr
  obtain ⟨q, hq0, hqne⟩ := htr
  refine ⟨q * Polynomial.C (q.leadingCoeff)⁻¹, Polynomial.monic_mul_leadingCoeff_inv hqne, ?_⟩
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C]
  simp only [Polynomial.coe_eval₂RingHom] at hq0
  rw [hq0, zero_mul]

/-! ## Affine charts from affine open subsets -/

section Charts

/-- **An affine open of a `k`-scheme is an affine `k`-scheme.**  Composing the canonical open
immersion `Spec Γ(W, U) ⟶ W` with the structure morphism gives the morphism of affine schemes
induced by the `k`-algebra structure `k → Γ(W, U)` of `RationalFunction.kSection`. -/
theorem fromSpec_comp_structureMap {W : Scheme.{u}} (f : W ⟶ Spec (CommRingCat.of k))
    {U : W.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ f = Spec.map (RationalFunction.kSection f U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of k))) hU
    le_top, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- The transport of a germ along the canonical identification of the stalks at two equal
points. -/
private lemma eqToHom_germ_apply {Y : Scheme.{u}} {a b : Y} (e : b = a) (U : Y.Opens)
    (ha : a ∈ U) (hb : b ∈ U) (σ : Γ(Y, U)) :
    (eqToHom (congrArg (fun z => Y.presheaf.stalk z) e.symm) :
        Y.presheaf.stalk a ⟶ Y.presheaf.stalk b).hom (Y.presheaf.germ U a ha σ) =
      Y.presheaf.germ U b hb σ := by
  subst e
  simp

/-- **The function-field pullback of a germ is the germ of the pulled-back section.**  For a
dominant morphism `g : X ⟶ Y` of integral schemes and a section `σ` on an open `U` containing the
generic point of `Y`, the function-field pullback of the rational function determined by `σ` is the
rational function determined by `g.app U σ`. -/
theorem dominantFunctionFieldMap_germ {X Y : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral X] [_root_.AlgebraicGeometry.IsIntegral Y]
    (g : X ⟶ Y) [IsDominant g] (U : Y.Opens) (hU : genericPoint Y ∈ U) (σ : Γ(Y, U))
    (hU' : genericPoint X ∈ g ⁻¹ᵁ U) :
    Scheme.dominantFunctionFieldMap g (Y.presheaf.germ U (genericPoint Y) hU σ) =
      X.presheaf.germ (g ⁻¹ᵁ U) (genericPoint X) hU' ((g.app U).hom σ) := by
  have e : g.base (genericPoint X) = genericPoint Y :=
    Scheme.map_genericPoint_of_isDominant g
  have he : g.base (genericPoint X) ∈ U := by rw [e]; exact hU
  change (g.stalkMap (genericPoint X)).hom
    ((eqToHom (congrArg (fun z => Y.presheaf.stalk z) e.symm)).hom _) = _
  rw [eqToHom_germ_apply e U hU he σ]
  exact Scheme.Hom.germ_stalkMap_apply g U (genericPoint X) he σ

/-- **A rational function regular on an affine open, read in the coordinate ring.**  For `U` an
affine open of an integral scheme containing the generic point and `σ ∈ Γ(W, U)`, the function-field
pullback along `Spec Γ(W, U) ⟶ W` of the rational function determined by `σ` is the image of `σ` in
the fraction field of `Γ(W, U)`. -/
theorem dominantFunctionFieldMap_fromSpec_germ {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] {U : W.Opens} (hU : IsAffineOpen U)
    (hgen : genericPoint W ∈ U) (σ : Γ(W, U)) :
    have _ : Nonempty U := ⟨⟨genericPoint W, hgen⟩⟩
    have _ : IsDomain Γ(W, U) := _root_.AlgebraicGeometry.IsIntegral.component_integral U
    have _ : IsDominant hU.fromSpec := Scheme.isDominant_of_isOpenImmersion hU.fromSpec
    Scheme.dominantFunctionFieldMap hU.fromSpec
        (W.presheaf.germ U (genericPoint W) hgen σ) =
      algebraMap Γ(W, U) (Spec Γ(W, U)).functionField σ := by
  intro _ _ _
  have hpre : hU.fromSpec ⁻¹ᵁ U = ⊤ := hU.fromSpec_preimage_self
  have hU' : genericPoint (Spec Γ(W, U)) ∈ hU.fromSpec ⁻¹ᵁ U := by rw [hpre]; trivial
  rw [dominantFunctionFieldMap_germ hU.fromSpec U hgen σ hU', IsAffineOpen.fromSpec_app_self,
    ConcreteCategory.comp_apply,
    (Spec Γ(W, U)).presheaf.germ_res_apply (eqToHom hpre) _ hU']
  exact (StructureSheaf.algebraMap_germ_apply (R := Γ(W, U)) ⊤
    (genericPoint (Spec Γ(W, U))) trivial σ).symm

end Charts

/-! ## The partial degree over an affine open -/

section AffineOpen

/-- **The partial degree of a principal divisor over an affine open, computed in the coordinate
ring.**  Let `U` be an affine open of the integral scheme `W` containing the generic point and
`σ ∈ Γ(W, U)`, and identify `Γ(W, U)` with a finite-type `k`-algebra `B` by a ring isomorphism `e`
compatible with the two `k`-algebra structures (`he`) and carrying `b : B` to `σ` (`hbe`).  Then
the partial degree `∑_{x ∈ U} ord_x(σ)·[κ(x):k]` of the rational function determined by `σ` equals
`dim_k (B ⧸ (b))`. -/
theorem finsum_eq_finrank_of_isAffineOpen {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    (f : W ⟶ Spec (CommRingCat.of k)) {U : W.Opens} (hU : IsAffineOpen U)
    (hgen : genericPoint W ∈ U) (σ : Γ(W, U))
    {B : Type u} [CommRing B] [Algebra k B] [IsDomain B] [Ring.KrullDimLE 1 B]
    [Algebra.FiniteType k B] [IsNoetherianRing B]
    (e : CommRingCat.of B ≅ Γ(W, U))
    (he : CommRingCat.ofHom (algebraMap k B) ≫ e.hom = RationalFunction.kSection f U)
    (b : B) (hb : b ≠ 0) (hbe : e.hom.hom b = σ) :
    (∑ᶠ x ∈ (U : Set W),
        (W.ord (W.presheaf.germ U (genericPoint W) hgen σ) x : ℚ) *
          (ZeroCycleDegree.residueDegree f x : ℚ)) =
      (Module.finrank k (B ⧸ Ideal.span {b}) : ℚ) := by
  have hnetop : Nonempty U := ⟨⟨genericPoint W, hgen⟩⟩
  have hdom : IsDomain Γ(W, U) := _root_.AlgebraicGeometry.IsIntegral.component_integral U
  have hiso : IsIso (Spec.map e.inv) := inferInstance
  have hdomfs : IsDominant hU.fromSpec := Scheme.isDominant_of_isOpenImmersion hU.fromSpec
  have hoi : IsOpenImmersion (Spec.map e.inv ≫ hU.fromSpec) := inferInstance
  have hdomj : IsDominant (Spec.map e.inv ≫ hU.fromSpec) :=
    Scheme.isDominant_of_isOpenImmersion _
  have hrange : Set.range (Spec.map e.inv ≫ hU.fromSpec).base = (U : Set W) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr (Spec.map e.inv).surjective, Set.image_univ, hU.range_fromSpec]
  have hjf : (Spec.map e.inv ≫ hU.fromSpec) ≫ f =
      AffineDegreeScheme.structureMorphism (k := k) (A := B) := by
    rw [Category.assoc, fromSpec_comp_structureMap f hU, ← Spec.map_comp,
      AffineDegreeScheme.structureMorphism, ← he, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  have hbr : Scheme.dominantFunctionFieldMap (Spec.map e.inv ≫ hU.fromSpec)
      (W.presheaf.germ U (genericPoint W) hgen σ) =
      (VectorBundle.functionFieldUnit (CommRingCat.of B) b hb :
        (Spec (CommRingCat.of B)).functionField) := by
    rw [Scheme.dominantFunctionFieldMap_comp' (Spec.map e.inv) hU.fromSpec _ rfl]
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [dominantFunctionFieldMap_fromSpec_germ hU hgen σ,
      Scheme.dominantFunctionFieldMap_Spec_map_algebraMap e.inv σ,
      VectorBundle.functionFieldUnit_val]
    congr 1
    rw [← hbe, ← ConcreteCategory.comp_apply, e.hom_inv_id]
    rfl
  rw [← hrange, finsum_eq_finrank_of_openImmersion f (Spec.map e.inv ≫ hU.fromSpec) hjf
    (W.presheaf.germ U (genericPoint W) hgen σ) b hb hbr]

end AffineOpen

/-! ## The degree of a principal divisor from affine domains of definition -/

/-- **The degree of a principal divisor on a curve vanishes as soon as the two domains of
definition are affine with equal chart dimension.**  Here `W` is an integral `k`-scheme all of whose
local rings are valuation rings (e.g. a regular curve), `r` is a rational function, the two domains
of definition `Scheme.regularLocus r` and `Scheme.regularLocus r⁻¹` are affine (`hU₀`, `hU₁`) with
coordinate rings identified with finite-type `k`-algebras `B₀`, `B₁` by `e₀`, `e₁` (compatibly with
the `k`-structures, `he₀`, `he₁`), and `bᵢ` corresponds to the canonical regular function
representing `r` (resp. `r⁻¹`).  If the two chart dimensions `dim_k (Bᵢ ⧸ (bᵢ))` agree then
`deg (div r) = 0`.  This is `degreeCycle_principalCycle_eq_zero_of_affineCharts` with the chart
morphisms produced from the affineness of the domains of definition. -/
theorem degreeCycle_principalCycle_eq_zero_of_isAffineOpen {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    [CompactSpace W] (f : W ⟶ Spec (CommRingCat.of k)) (r : W.functionField)
    (hv : ∀ x : W, ValuationRing (W.presheaf.stalk x))
    (hU₀ : IsAffineOpen (Scheme.regularLocus r))
    (hU₁ : IsAffineOpen (Scheme.regularLocus r⁻¹))
    {B₀ B₁ : Type u} [CommRing B₀] [Algebra k B₀] [IsDomain B₀] [Ring.KrullDimLE 1 B₀]
    [Algebra.FiniteType k B₀] [IsNoetherianRing B₀]
    [CommRing B₁] [Algebra k B₁] [IsDomain B₁] [Ring.KrullDimLE 1 B₁]
    [Algebra.FiniteType k B₁] [IsNoetherianRing B₁]
    (e₀ : CommRingCat.of B₀ ≅ Γ(W, Scheme.regularLocus r))
    (e₁ : CommRingCat.of B₁ ≅ Γ(W, Scheme.regularLocus r⁻¹))
    (he₀ : CommRingCat.ofHom (algebraMap k B₀) ≫ e₀.hom =
      RationalFunction.kSection f (Scheme.regularLocus r))
    (he₁ : CommRingCat.ofHom (algebraMap k B₁) ≫ e₁.hom =
      RationalFunction.kSection f (Scheme.regularLocus r⁻¹))
    (b₀ : B₀) (hb₀ : b₀ ≠ 0) (b₁ : B₁) (hb₁ : b₁ ≠ 0)
    (hbe₀ : e₀.hom.hom b₀ = Scheme.regularSection r)
    (hbe₁ : e₁.hom.hom b₁ = Scheme.regularSection r⁻¹)
    (hrank : Module.finrank k (B₀ ⧸ Ideal.span {b₀}) =
      Module.finrank k (B₁ ⧸ Ideal.span {b₁})) :
    ZeroCycleDegree.degreeCycle f (W.principalCycle r) = 0 := by
  refine degreeCycle_principalCycle_eq_zero_of_finsum_eq f r hv ?_
  have h0 := finsum_eq_finrank_of_isAffineOpen f hU₀ (Scheme.genericPoint_mem_regularLocus r)
    (Scheme.regularSection r) e₀ he₀ b₀ hb₀ hbe₀
  have h1 := finsum_eq_finrank_of_isAffineOpen f hU₁ (Scheme.genericPoint_mem_regularLocus r⁻¹)
    (Scheme.regularSection r⁻¹) e₁ he₁ b₁ hb₁ hbe₁
  rw [Scheme.germ_regularSection r] at h0
  rw [Scheme.germ_regularSection r⁻¹] at h1
  rw [h0, h1, hrank]

/-! ## Specialisation to a regular proper curve -/

namespace RegularProperCurve

variable (X : _root_.GromovWitten.AlgebraicGeometry.RegularProperCurve k)

/-- **The degree of the principal divisor of a rational function algebraic over `k` on a regular
proper curve vanishes** — indeed the divisor itself vanishes, `r` being a unit at every point. -/
theorem degreeCycle_principalCycle_eq_zero_of_monic (r : X.W.functionField)
    (p : Polynomial k) (hp : p.Monic)
    (hpr : Polynomial.eval₂ (RationalFunction.kFunctionField X.f).hom r p = 0) :
    have _ := X.isNoetherian
    ZeroCycleDegree.degreeCycle X.f (X.W.principalCycle r) = 0 := by
  intro _
  exact ProperCurveDegree.degreeCycle_principalCycle_eq_zero_of_monic
    X.f X.valuationRing_stalk r p hp hpr

/-- **Fulton's `killsGradedDivisor` for a regular proper curve, given the affine chart data.**
The degree of the principal divisor of a nonzero rational function `r` on a regular proper curve
vanishes, provided the two domains of definition `Scheme.regularLocus r` and
`Scheme.regularLocus r⁻¹` are affine with coordinate rings `B₀`, `B₁` (identified by `e₀`, `e₁`
compatibly with the `k`-structures) of equal chart dimension `dim_k (Bᵢ ⧸ (bᵢ))`.  For `r`
transcendental over `k` this data comes from finiteness of the morphism
`RationalFunction.toProjectiveLine X.f X.valuationRing_stalk r hr : W ⟶ ℙ¹_k`, the two domains of
definition being the preimages of the two standard charts; for `r` algebraic over `k` no data is
needed, see `degreeCycle_principalCycle_eq_zero_of_monic`. -/
theorem degreeCycle_principalCycle_eq_zero_of_isAffineOpen (r : X.W.functionField)
    (hU₀ : IsAffineOpen (Scheme.regularLocus r))
    (hU₁ : IsAffineOpen (Scheme.regularLocus r⁻¹))
    {B₀ B₁ : Type u} [CommRing B₀] [Algebra k B₀] [IsDomain B₀] [Ring.KrullDimLE 1 B₀]
    [Algebra.FiniteType k B₀] [IsNoetherianRing B₀]
    [CommRing B₁] [Algebra k B₁] [IsDomain B₁] [Ring.KrullDimLE 1 B₁]
    [Algebra.FiniteType k B₁] [IsNoetherianRing B₁]
    (e₀ : CommRingCat.of B₀ ≅ Γ(X.W, Scheme.regularLocus r))
    (e₁ : CommRingCat.of B₁ ≅ Γ(X.W, Scheme.regularLocus r⁻¹))
    (he₀ : CommRingCat.ofHom (algebraMap k B₀) ≫ e₀.hom =
      RationalFunction.kSection X.f (Scheme.regularLocus r))
    (he₁ : CommRingCat.ofHom (algebraMap k B₁) ≫ e₁.hom =
      RationalFunction.kSection X.f (Scheme.regularLocus r⁻¹))
    (b₀ : B₀) (hb₀ : b₀ ≠ 0) (b₁ : B₁) (hb₁ : b₁ ≠ 0)
    (hbe₀ : e₀.hom.hom b₀ = Scheme.regularSection r)
    (hbe₁ : e₁.hom.hom b₁ = Scheme.regularSection r⁻¹)
    (hrank : Module.finrank k (B₀ ⧸ Ideal.span {b₀}) =
      Module.finrank k (B₁ ⧸ Ideal.span {b₁})) :
    have _ := X.isNoetherian
    ZeroCycleDegree.degreeCycle X.f (X.W.principalCycle r) = 0 := by
  intro _
  exact ProperCurveDegree.degreeCycle_principalCycle_eq_zero_of_isAffineOpen
    X.f r
    X.valuationRing_stalk hU₀ hU₁
    e₀ e₁ he₀ he₁ b₀ hb₀ b₁ hb₁ hbe₀ hbe₁ hrank

end RegularProperCurve

/-! ## The chart preimages of the morphism to the projective line -/

section ProjectiveLineCharts

open ProjectiveLine

/-- **The preimage of a standard chart of `ℙ¹_k` under a finite morphism is an affine open.**
Finite morphisms are affine (`IsFinite` extends `IsAffineHom`) and the standard charts of `ℙ¹_k` are
affine opens, being the ranges of open immersions from `Spec k[t]`. -/
theorem isAffineOpen_preimage_chart {W : Scheme.{u}} (p : W ⟶ ProjectiveLine.scheme k)
    [IsFinite p] (j : ProjectiveLine.chart k ⟶ ProjectiveLine.scheme k) [IsOpenImmersion j] :
    IsAffineOpen (p ⁻¹ᵁ j.opensRange) :=
  (isAffineOpen_opensRange j).preimage p

/-- **The domain of definition of `r` is contained in the preimage of the first standard chart.**
On `Scheme.regularLocus r` the morphism to `ℙ¹_k` factors through the first chart
(`RationalFunction.ι_toProjectiveLine`). -/
theorem regularLocus_le_preimage_chartZero {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] (f : W ⟶ Spec (CommRingCat.of k))
    (hv : ∀ x : W, ValuationRing (W.presheaf.stalk x)) (r : W.functionField) (hr : r ≠ 0) :
    Scheme.regularLocus r ≤
      RationalFunction.toProjectiveLine f hv r hr ⁻¹ᵁ (chartZero k).opensRange := by
  intro x hx
  have h := congrArg (fun g : (Scheme.regularLocus r).toScheme ⟶ ProjectiveLine.scheme k =>
    g.base ⟨x, hx⟩) (RationalFunction.ι_toProjectiveLine f hv r hr)
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp] at h
  exact ⟨_, h.symm⟩

end ProjectiveLineCharts

/-! ## The algebraic case of the case split -/

/-- **The degree of the principal divisor of a rational function which is not transcendental over
`k` vanishes.**  This is the algebraic branch of the case split in the proof of
"the degree of a principal divisor on a proper curve vanishes": the hypothesis is the negation of
the transcendence hypothesis `htr` of `RationalFunction.isFinite_toProjectiveLine`. -/
theorem degreeCycle_principalCycle_eq_zero_of_not_injective {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    [CompactSpace W] (f : W ⟶ Spec (CommRingCat.of k))
    (hv : ∀ x : W, ValuationRing (W.presheaf.stalk x)) (r : W.functionField)
    (htr : ¬ Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField f).hom r)) :
    ZeroCycleDegree.degreeCycle f (W.principalCycle r) = 0 := by
  obtain ⟨p, hp, hpr⟩ := exists_monic_of_not_injective f r htr
  exact degreeCycle_principalCycle_eq_zero_of_monic f hv r p hp hpr

namespace RegularProperCurve

/-- **The regular proper curve form of `degreeCycle_principalCycle_eq_zero_of_not_injective`.** -/
theorem degreeCycle_principalCycle_eq_zero_of_not_injective
    (X : _root_.GromovWitten.AlgebraicGeometry.RegularProperCurve k) (r : X.W.functionField)
    (htr : ¬ Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField X.f).hom r)) :
    have _ := X.isNoetherian
    ZeroCycleDegree.degreeCycle X.f (X.W.principalCycle r) = 0 := by
  intro _
  exact ProperCurveDegree.degreeCycle_principalCycle_eq_zero_of_not_injective
    X.f X.valuationRing_stalk r htr

end RegularProperCurve

end GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperCurveDegree
