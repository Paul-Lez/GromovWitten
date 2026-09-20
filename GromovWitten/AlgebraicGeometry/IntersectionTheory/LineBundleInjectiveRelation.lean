/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleInjectiveGysin
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyInjectiveGlobal

/-!
# The global relation produced by the Gysin map of a constant section

`IntersectionTheory/LineBundleInjectiveGlobal.lean` reduced the injectivity of the flat pullback
along the trivial line bundle `E = Y × 𝔸¹` to the statement that the global Gysin map
`LineBundleInjective.globalGysin fk c dimE` of the constant section `t = c` sends a principal
divisor of `E` into `totalRationalRelations Y`, and
`IntersectionTheory/LineBundleInjectiveGysin.lean` supplied the residue-field bookkeeping needed
to identify the chart-wise Gysin summands.  This file assembles the two into the global relation
and proves the rank-one injectivity theorem.

## Main declarations

* `LineBundleInjective.specChartRatio_eq_of_refinement` — the general chart comparison of the
  ratio of two ring elements in the residue field of the ambient scheme, through a common
  refinement of two affine charts.
* `LineBundleInjective.specChartRatio_base_eq` — the base-level instance of that comparison, for
  the ratio of the evaluations `a(c)`, `b(c)` at a point of the base lying on the section
  `t = c` under a specialisation of the generic point of the subvariety of a generator.
* `LineBundleInjective.divisor_pointGenerator_sub` and
  `LineBundleInjective.divisor_openGenerator_sectionGenerator` — the divisor of a Gysin summand,
  transported to the base, is the divisor of the canonical generator attached to the base point
  of the component and to the class of the polynomial there; differences of such divisors are
  the canonical generator of the ratio.
* `LineBundleInjective.globalGysin_divisor_mem_of_data` — the global relation: for a constant in
  general position on a finite affine cover, the Gysin image of a principal divisor of the total
  space is the finite sum, over the points of the base lying on the intersection of the
  subvariety with the section, of the divisors of canonical point generators.
* `LineBundleInjective.exists_good_constant_globalGysin` — the choice of one such constant for
  finitely many generators, over an infinite field.
* `LineBundleInjective.pullbackBundle_injective_rankOne` and
  `LineBundleInjective.rankOneInjective` — the rank-one injectivity theorem, and
  `LineBundleInjective.pullbackBundle_trivialData_injective`,
  `LineBundleInjective.pullbackBundle_injective_of_globalTrivialisation`,
  `LineBundleInjective.chowPullbackBundleGlobal_injective` — the corollaries of
  `IntersectionTheory/BundleHomotopyInjectiveGlobal.lean` with the hypothesis
  `BundlePullbackGlobal.RankOneInjective` discharged.

-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)

namespace LineBundleInjective

/-! ## Comparing two charts through a common refinement -/

section Refinement

variable {X : Scheme.{u}} [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The ratio of two ring elements read on an affine chart only depends on the point, not on the
proofs that the two elements are invertible there, and it is transported along an equality of
points by the residue-field congruence. -/
theorem specChartRatio_congr {B : CommRingCat.{u}} (V : X.Opens) (e : Spec B ≅ V.toScheme)
    {x x' : ↥(Spec B)} (hxx' : x = x') (a b : B)
    (ha : a ∉ (x : PrimeSpectrum B).asIdeal) (hb : b ∉ (x : PrimeSpectrum B).asIdeal)
    (ha' : a ∉ (x' : PrimeSpectrum B).asIdeal) (hb' : b ∉ (x' : PrimeSpectrum B).asIdeal) :
    specChartRatio V e x' a b ha' hb' =
      Units.map (X.residueFieldCongr
          (congrArg (openInclusion V e).base hxx')).hom.hom.toMonoidHom
        (specChartRatio V e x a b ha hb) := by
  subst hxx'
  rfl

/-- **Chart independence of a ratio through a common refinement.**  If two affine charts of `X`
are both refined by a third one, in which the two pairs of elements satisfy the cross relation at
the chosen point, then the two ratios agree in the residue field of `X`. -/
theorem specChartRatio_eq_of_refinement {B B' C : CommRingCat.{u}}
    (V : X.Opens) (e : Spec B ≅ V.toScheme) (V' : X.Opens) (e' : Spec B' ≅ V'.toScheme)
    (V'' : X.Opens) (e'' : Spec C ≅ V''.toScheme) (φ : B ⟶ C) (φ' : B' ⟶ C)
    (hφ : Spec.map φ ≫ openInclusion V e = openInclusion V'' e'')
    (hφ' : Spec.map φ' ≫ openInclusion V' e' = openInclusion V'' e'')
    {x : ↥(Spec B)} {x' : ↥(Spec B')} (x'' : ↥(Spec C))
    (hx : (Spec.map φ).base x'' = x) (hx' : (Spec.map φ').base x'' = x')
    (a b : B) (a' b' : B')
    (ha : a ∉ (x : PrimeSpectrum B).asIdeal) (hb : b ∉ (x : PrimeSpectrum B).asIdeal)
    (ha' : a' ∉ (x' : PrimeSpectrum B').asIdeal) (hb' : b' ∉ (x' : PrimeSpectrum B').asIdeal)
    (hcross : φ a * φ' b' - φ' a' * φ b ∈ (x'' : PrimeSpectrum C).asIdeal)
    (hy : (openInclusion V' e').base x' = (openInclusion V e).base x) :
    Units.map (X.residueFieldCongr hy).hom.hom.toMonoidHom
        (specChartRatio V' e' x' a' b' ha' hb') = specChartRatio V e x a b ha hb := by
  subst hx
  subst hx'
  have hyy : (openInclusion V e).base ((Spec.map φ).base x'') =
      (openInclusion V'' e'').base x'' :=
    congrArg (fun m : Spec C ⟶ X ↦ m.base x'') hφ
  have hyy' : (openInclusion V' e').base ((Spec.map φ').base x'') =
      (openInclusion V'' e'').base x'' :=
    congrArg (fun m : Spec C ⟶ X ↦ m.base x'') hφ'
  have e1 := specChartRatio_comp V e V'' e'' φ hφ x'' a b ha hb ha hb hyy
  have e1' := specChartRatio_comp V' e' V'' e'' φ' hφ' x'' a' b' ha' hb' ha' hb' hyy'
  have hEq : specChartRatio V'' e'' x'' (φ a) (φ b) ha hb =
      specChartRatio V'' e'' x'' (φ' a') (φ' b') ha' hb' :=
    (specChartRatio_eq_iff V'' e'' x'' _ _ _ _ ha hb ha' hb').2 hcross
  rw [e1, e1'] at hEq
  have h5 := congrArg (Units.map ((X.residueFieldCongr hyy.symm)).hom.hom.toMonoidHom) hEq
  rw [units_map_residueFieldCongr_trans, units_map_residueFieldCongr_trans] at h5
  exact h5.symm

end Refinement

/-! ## Evaluation of polynomials along a restriction map -/

section EvalRestriction

/-- Evaluating the image of a polynomial under a coefficient ring homomorphism at the image of
the constant is the image of the evaluation. -/
theorem eval_mapRingHom {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (a : A)
    (p : Polynomial A) :
    Polynomial.eval (φ a) (Polynomial.mapRingHom φ p) = φ (Polynomial.eval a p) := by
  rw [Polynomial.coe_mapRingHom, Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-- A polynomial not vanishing identically on a component of the section does not vanish at the
base point of that component. -/
theorem eval_notMem_basePoint {R : Type u} [CommRing R] (c : R)
    (V : ↥(Spec (CommRingCat.of (Polynomial R))))
    (hsV : VectorBundle.sectionPoly c ∈ (V : PrimeSpectrum (Polynomial R)).asIdeal)
    (a : Polynomial R) (ha : a ∉ (V : PrimeSpectrum (Polynomial R)).asIdeal) :
    Polynomial.eval c a ∉
      ((VectorBundle.basePoint c V hsV : ↥(Spec (CommRingCat.of R))) :
        PrimeSpectrum R).asIdeal := by
  intro h
  have h3 : a ∈ ((VectorBundle.sectionPoint c (VectorBundle.basePoint c V hsV) :
      ↥(Spec (CommRingCat.of (Polynomial R)))) : PrimeSpectrum (Polynomial R)).asIdeal := h
  rw [VectorBundle.sectionPoint_basePoint] at h3
  exact ha h3

end EvalRestriction

/-! ## The ratio of the evaluations at the base point of a component -/

section BaseChartRatio

variable {Y : Scheme.{u}} {k : Type u} [Field k] (fk : Y ⟶ Spec (CommRingCat.of k)) (c : k)

/-- Evaluating the restriction of a polynomial at the restricted constant is the restriction of
the evaluation. -/
theorem eval_coordMap {U W : Y.affineOpens} (h : W ≤ U) (p : Polynomial Γ(Y, U.1)) :
    Polynomial.eval (chartConst fk c W) (Polynomial.mapRingHom (GlobalBlowup.res Y h) p) =
      GlobalBlowup.res Y h (Polynomial.eval (chartConst fk c U) p) := by
  have hc : GlobalBlowup.res Y h (chartConst fk c U) = chartConst fk c W :=
    res_structureMap fk h c
  rw [← hc]
  exact eval_mapRingHom (GlobalBlowup.res Y h) (chartConst fk c U) p

/-- A point of a smaller univariate chart lying over a component of the section is itself a
component of the section. -/
theorem coordPoly_mem_of_map {U W : Y.affineOpens} (h : W ≤ U)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (VW : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, W.1)))))
    (hVW : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (GlobalBlowup.res Y h)))).base VW = V)
    (hsV : coordPoly fk c U ∈ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal) :
    coordPoly fk c W ∈ (VW : PrimeSpectrum (Polynomial Γ(Y, W.1))).asIdeal := by
  rw [← mapRingHom_coordPoly fk c h]
  rw [← hVW] at hsV
  exact hsV

/-- The square relating the constant sections of two nested univariate charts. -/
theorem specMap_res_comp_sectionMap {U W : Y.affineOpens} (h : W ≤ U) :
    Spec.map (CommRingCat.ofHom (GlobalBlowup.res Y h)) ≫
        VectorBundle.sectionMap (chartConst fk c U) =
      VectorBundle.sectionMap (chartConst fk c W) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y h))) := by
  rw [VectorBundle.sectionMap, VectorBundle.sectionMap, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  refine congrArg Spec.map (congrArg CommRingCat.ofHom (RingHom.ext fun p ↦ ?_))
  exact (eval_coordMap fk c h p).symm

/-- The base point of a component of the section computed on a smaller chart restricts to the
base point computed on the bigger chart. -/
theorem specMap_res_basePoint {U W : Y.affineOpens} (h : W ≤ U)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (VW : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, W.1)))))
    (hsV : coordPoly fk c U ∈ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hsW : coordPoly fk c W ∈ (VW : PrimeSpectrum (Polynomial Γ(Y, W.1))).asIdeal)
    (hVW : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (GlobalBlowup.res Y h)))).base VW = V) :
    (Spec.map (CommRingCat.ofHom (GlobalBlowup.res Y h))).base
        (VectorBundle.basePoint (chartConst fk c W) VW hsW) =
      VectorBundle.basePoint (chartConst fk c U) V hsV := by
  refine VectorBundle.sectionPoint_injective (chartConst fk c U) ?_
  have hsq := congrArg (fun m : Spec (CommRingCat.of Γ(Y, W.1)) ⟶
      Spec (CommRingCat.of (Polynomial Γ(Y, U.1))) ↦
        m.base (VectorBundle.basePoint (chartConst fk c W) VW hsW))
    (specMap_res_comp_sectionMap fk c h)
  refine hsq.trans ?_
  change (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y h)))).base
      (VectorBundle.sectionPoint (chartConst fk c W)
        (VectorBundle.basePoint (chartConst fk c W) VW hsW)) = _
  rw [VectorBundle.sectionPoint_basePoint, hVW, VectorBundle.sectionPoint_basePoint]

/-- The constant section is injective on points. -/
theorem sectionMap_base_injective :
    Function.Injective (sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base := by
  intro y y' hyy'
  have h := congrArg (trivialData Y PUnit.{u + 1}).proj.base hyy'
  rwa [proj_sectionMap_base fk c, proj_sectionMap_base fk c] at h

variable [_root_.AlgebraicGeometry.IsLocallyNoetherian Y] [NoetherianSpace Y]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)] [NoetherianSpace (lineSpace Y)]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian Y] [NoetherianSpace Y]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- The constant section carries the base point of a component of the section to that
component. -/
theorem sectionMap_base_chartInclusion_basePoint (U : Y.affineOpens)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hsV : coordPoly fk c U ∈ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal) :
    (sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base
        ((chartInclusion U).base (VectorBundle.basePoint (chartConst fk c U) V hsV)) =
      (polyChartMap U).base V := by
  have hsq := congrArg (fun m : Spec (CommRingCat.of Γ(Y, U.1)) ⟶ lineSpace Y ↦
      m.base (VectorBundle.basePoint (chartConst fk c U) V hsV))
    (chartInclusion_comp_sectionMap fk c U)
  refine hsq.trans ?_
  change (polyChartMap U).base (VectorBundle.sectionPoint (chartConst fk c U)
    (VectorBundle.basePoint (chartConst fk c U) V hsV)) = _
  rw [VectorBundle.sectionPoint_basePoint]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian Y] [NoetherianSpace Y]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- Two components of the section with the same image in the total space have the same base
point in the base. -/
theorem chartInclusion_basePoint_eq {U U' : Y.affineOpens}
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (V' : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U'.1)))))
    (hsV : coordPoly fk c U ∈ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hsV' : coordPoly fk c U' ∈ (V' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (hq : (openInclusion (polyOpens U') (polyIso U')).base V' =
      (openInclusion (polyOpens U) (polyIso U)).base V) :
    (chartInclusion U').base (VectorBundle.basePoint (chartConst fk c U') V' hsV') =
      (chartInclusion U).base (VectorBundle.basePoint (chartConst fk c U) V hsV) := by
  refine sectionMap_base_injective fk c ?_
  rw [sectionMap_base_chartInclusion_basePoint fk c U' V' hsV',
    sectionMap_base_chartInclusion_basePoint fk c U V hsV]
  rw [openInclusion_polyIso, openInclusion_polyIso] at hq
  exact hq

/-- The point of the base attached to a component of the section, computed from a point of the
chart. -/
theorem basePoint_sectionPoint {R : Type u} [CommRing R] (cR : R)
    (x : ↥(Spec (CommRingCat.of R)))
    (hs : VectorBundle.sectionPoly cR ∈
      ((VectorBundle.sectionPoint cR x : ↥(Spec (CommRingCat.of (Polynomial R)))) :
        PrimeSpectrum (Polynomial R)).asIdeal) :
    VectorBundle.basePoint cR (VectorBundle.sectionPoint cR x) hs = x := by
  refine VectorBundle.sectionPoint_injective cR ?_
  rw [VectorBundle.sectionPoint_basePoint]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian Y] [NoetherianSpace Y]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- The constant section read on a chart: the image of a point of the chart under the affine
section is the image of its image in the base under the global section. -/
theorem polyChartMap_sectionPoint (U : Y.affineOpens)
    (y : ↥(Spec (CommRingCat.of Γ(Y, U.1)))) :
    (polyChartMap U).base (VectorBundle.sectionPoint (chartConst fk c U) y) =
      (sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base ((chartInclusion U).base y) :=
  (congrArg (fun m : Spec (CommRingCat.of Γ(Y, U.1)) ⟶ lineSpace Y ↦ m.base y)
    (chartInclusion_comp_sectionMap fk c U)).symm

/-- **The base-level chart independence of the ratio.**  If two pairs of polynomials read on two
univariate charts represent the same rational function at the generic point `p` of the subvariety
of a generator, then their evaluations at the constant `c` have the same ratio in the residue
field of the base at any point `z` of the base which lies on the section under a specialisation
of `p`, computed on either chart. -/
theorem specChartRatio_base_eq {U U' : Y.affineOpens}
    (p : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (p' : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U'.1)))))
    (y : ↥(Spec (CommRingCat.of Γ(Y, U.1)))) (y' : ↥(Spec (CommRingCat.of Γ(Y, U'.1))))
    (a b : Polynomial Γ(Y, U.1)) (a' b' : Polynomial Γ(Y, U'.1))
    (hap : a ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hbp : b ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hap' : a' ∉ (p' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (hbp' : b' ∉ (p' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (hay : Polynomial.eval (chartConst fk c U) a ∉ (y : PrimeSpectrum Γ(Y, U.1)).asIdeal)
    (hby : Polynomial.eval (chartConst fk c U) b ∉ (y : PrimeSpectrum Γ(Y, U.1)).asIdeal)
    (hay' : Polynomial.eval (chartConst fk c U') a' ∉ (y' : PrimeSpectrum Γ(Y, U'.1)).asIdeal)
    (hby' : Polynomial.eval (chartConst fk c U') b' ∉ (y' : PrimeSpectrum Γ(Y, U'.1)).asIdeal)
    (hspec : (openInclusion (polyOpens U) (polyIso U)).base p ⤳
      (sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base ((chartInclusion U).base y))
    (hξ : (openInclusion (polyOpens U') (polyIso U')).base p' =
      (openInclusion (polyOpens U) (polyIso U)).base p)
    (hzz' : (chartInclusion U').base y' = (chartInclusion U).base y)
    (hrat : Units.map ((lineSpace Y).residueFieldCongr hξ).hom.hom.toMonoidHom
        (specChartRatio (polyOpens U') (polyIso U') p' a' b' hap' hbp') =
      specChartRatio (polyOpens U) (polyIso U) p a b hap hbp) :
    Units.map (Y.residueFieldCongr hzz').hom.hom.toMonoidHom
        (specChartRatio U'.1 (isAffineOpen Y U').isoSpec.symm y'
          (Polynomial.eval (chartConst fk c U') a')
          (Polynomial.eval (chartConst fk c U') b') hay' hby') =
      specChartRatio U.1 (isAffineOpen Y U).isoSpec.symm y
        (Polynomial.eval (chartConst fk c U) a)
        (Polynomial.eval (chartConst fk c U) b) hay hby := by
  have hsV : coordPoly fk c U ∈
      ((VectorBundle.sectionPoint (chartConst fk c U) y :
        ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
        PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal :=
    VectorBundle.sectionPoly_mem_sectionPoint (chartConst fk c U) y
  have hsV' : coordPoly fk c U' ∈
      ((VectorBundle.sectionPoint (chartConst fk c U') y' :
        ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U'.1))))) :
        PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal :=
    VectorBundle.sectionPoly_mem_sectionPoint (chartConst fk c U') y'
  have hq : (openInclusion (polyOpens U') (polyIso U')).base
        (VectorBundle.sectionPoint (chartConst fk c U') y') =
      (openInclusion (polyOpens U) (polyIso U)).base
        (VectorBundle.sectionPoint (chartConst fk c U) y) := by
    rw [openInclusion_polyIso, openInclusion_polyIso, polyChartMap_sectionPoint,
      polyChartMap_sectionPoint, hzz']
  have hspec2 : (openInclusion (polyOpens U) (polyIso U)).base p ⤳
      (openInclusion (polyOpens U) (polyIso U)).base
        (VectorBundle.sectionPoint (chartConst fk c U) y) := by
    have h := hspec
    rw [openInclusion_polyIso] at h
    rw [openInclusion_polyIso, polyChartMap_sectionPoint]
    exact h
  obtain ⟨W, hWU, hWU', VW, hVWU, hVWU', hinclV, hcross⟩ :=
    exists_refinement_crossMem p (VectorBundle.sectionPoint (chartConst fk c U) y) p'
      (VectorBundle.sectionPoint (chartConst fk c U') y') a b a' b' hap hbp hap' hbp'
      hay hby hay' hby' hspec2 hξ hq hrat
  have hsW : coordPoly fk c W ∈ (VW : PrimeSpectrum (Polynomial Γ(Y, W.1))).asIdeal :=
    coordPoly_mem_of_map fk c hWU _ VW hVWU hsV
  refine specChartRatio_eq_of_refinement U.1 (isAffineOpen Y U).isoSpec.symm
    U'.1 (isAffineOpen Y U').isoSpec.symm W.1 (isAffineOpen Y W).isoSpec.symm
    (CommRingCat.ofHom (GlobalBlowup.res Y hWU)) (CommRingCat.ofHom (GlobalBlowup.res Y hWU'))
    (chartInclusion_comp hWU) (chartInclusion_comp hWU')
    (VectorBundle.basePoint (chartConst fk c W) VW hsW)
    ((specMap_res_basePoint fk c hWU _ VW hsV hsW hVWU).trans
      (basePoint_sectionPoint (chartConst fk c U) y hsV))
    ((specMap_res_basePoint fk c hWU' _ VW hsV' hsW hVWU').trans
      (basePoint_sectionPoint (chartConst fk c U') y' hsV'))
    _ _ _ _ _ _ _ _ ?_ _
  have h3 : (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU))) a *
        (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU'))) b' -
      (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU'))) a' *
        (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU))) b ∈
      ((VectorBundle.sectionPoint (chartConst fk c W)
          (VectorBundle.basePoint (chartConst fk c W) VW hsW) :
        ↥(Spec (CommRingCat.of (Polynomial Γ(Y, W.1))))) :
        PrimeSpectrum (Polynomial Γ(Y, W.1))).asIdeal := by
    rw [VectorBundle.sectionPoint_basePoint]
    exact hcross
  have h4 : Polynomial.eval (chartConst fk c W)
      ((Polynomial.mapRingHom (GlobalBlowup.res Y hWU)) a *
          (Polynomial.mapRingHom (GlobalBlowup.res Y hWU')) b' -
        (Polynomial.mapRingHom (GlobalBlowup.res Y hWU')) a' *
          (Polynomial.mapRingHom (GlobalBlowup.res Y hWU)) b) ∈
      ((VectorBundle.basePoint (chartConst fk c W) VW hsW :
        ↥(Spec (CommRingCat.of Γ(Y, W.1)))) : PrimeSpectrum Γ(Y, W.1)).asIdeal := h3
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
    eval_coordMap fk c hWU a, eval_coordMap fk c hWU' b',
    eval_coordMap fk c hWU' a', eval_coordMap fk c hWU b] at h4
  exact h4

end BaseChartRatio

/-! ## The difference of two point generators -/

section PointArith

variable {X : Scheme.{u}} [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]
  (dim : DimensionFunction X)

/-- The canonical generator attached to the unit `1` has trivial divisor. -/
theorem divisor_pointGenerator_one (x : X) :
    (pointGenerator x (1 : (X.residueField x)ˣ)).divisor dim = 0 := by
  have h : pointGenerator x (1 : (X.residueField x)ˣ) =
      RationalFunctionGenerator.mk (pointSubscheme x) 1 :=
    congrArg (RationalFunctionGenerator.mk (pointSubscheme x)) (map_one _)
  rw [h]
  exact divisor_one dim _

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] dim in
/-- Transport of a unit along the trivial equality of points is the identity. -/
theorem units_map_residueFieldCongr_rfl (x : X) (w : (X.residueField x)ˣ) :
    Units.map (X.residueFieldCongr (rfl : x = x)).hom.hom.toMonoidHom w = w := rfl

/-- **The difference of two canonical point generators at the same point** is the canonical
generator of the ratio of the two units. -/
theorem divisor_pointGenerator_sub (x : X) (u v : (X.residueField x)ˣ) :
    (pointGenerator x u).divisor dim - (pointGenerator x v).divisor dim =
      (pointGenerator x (u / v)).divisor dim := by
  have hres : ∀ w : (X.residueField x)ˣ,
      Units.map (X.residueFieldCongr
          (genericPointImage_pointSubscheme x)).hom.hom.toMonoidHom
        (RationalFunctionGenerator.mk (pointSubscheme x)
          (Units.map ((pointFieldEquiv x).symm.toMonoidHom) w)).residueFunction = w :=
    fun w ↦ residueFunction_pointGenerator x w
  have hcond : Units.map (X.residueFieldCongr
        (rfl : (pointSubscheme x).genericPointImage =
          (pointSubscheme x).genericPointImage)).hom.hom.toMonoidHom
        (RationalFunctionGenerator.mk (pointSubscheme x)
          (Units.map ((pointFieldEquiv x).symm.toMonoidHom) u)).residueFunction *
      (RationalFunctionGenerator.mk (pointSubscheme x)
        (Units.map ((pointFieldEquiv x).symm.toMonoidHom)
          (1 : (X.residueField x)ˣ))).residueFunction =
      (RationalFunctionGenerator.mk (pointSubscheme x)
          (Units.map ((pointFieldEquiv x).symm.toMonoidHom) (u / v))).residueFunction *
        Units.map (X.residueFieldCongr
          (rfl : (pointSubscheme x).genericPointImage =
            (pointSubscheme x).genericPointImage)).hom.hom.toMonoidHom
          (RationalFunctionGenerator.mk (pointSubscheme x)
            (Units.map ((pointFieldEquiv x).symm.toMonoidHom) v)).residueFunction := by
    rw [units_map_residueFieldCongr_rfl, units_map_residueFieldCongr_rfl]
    refine units_map_residueFieldCongr_injective (genericPointImage_pointSubscheme x) ?_
    rw [map_mul, map_mul, hres u, hres v, hres (u / v), hres 1, mul_one]
    exact (div_mul_cancel u v).symm
  have key : (pointGenerator x u).divisor dim - (pointGenerator x v).divisor dim =
      (pointGenerator x (u / v)).divisor dim -
        (pointGenerator x (1 : (X.residueField x)ˣ)).divisor dim :=
    RationalFunctionGenerator.divisor_sub_eq_of_residueFunction_mul_eq dim
      (pointSubscheme x) (pointSubscheme x) rfl _ _ _ _ hcond
  rw [divisor_pointGenerator_one dim x, sub_zero] at key
  exact key

/-- **The divisor of a generator transported from a chart is a canonical point generator**: it
only depends on the image of the generic point of the generator and on the class of its rational
function there, read through the chart. -/
theorem divisor_openGenerator_eq_pointGenerator {W : Scheme.{u}} (V : X.Opens)
    (e : W ≅ V.toScheme) (g : RationalFunctionGenerator W) {x : W}
    (hgp : g.subspace.genericPointImage = x) (w : (W.residueField x)ˣ)
    (hres : Units.map (W.residueFieldCongr hgp).hom.hom.toMonoidHom g.residueFunction = w) :
    (openGenerator V e g).divisor dim =
      (pointGenerator ((openInclusion V e).base x) (openUnit V e x w)).divisor dim := by
  refine divisor_openGenerator_eq_of V e dim g _
    ((congrArg (openInclusion V e).base hgp).trans
      (genericPointImage_pointGenerator _ _).symm) ?_
  refine units_map_residueFieldCongr_injective (genericPointImage_pointGenerator _ _) ?_
  rw [units_map_residueFieldCongr_trans, residueFunction_pointGenerator,
    openResidueUnit_eq_openUnit, ← openUnit_congr V e hgp g.residueFunction, hres]

end PointArith

/-! ## The Gysin summand of a chart as a global point generator -/

section GysinSummand

variable {Y : Scheme.{u}} {k : Type u} [Field k] (fk : Y ⟶ Spec (CommRingCat.of k)) (c : k)
  [_root_.AlgebraicGeometry.IsLocallyNoetherian Y] [NoetherianSpace Y]

/-- **The divisor of a Gysin summand, transported to the base.**  The generator produced on the
chart `Spec Γ(Y, U)` by a component `V` of the intersection of a subvariety with the section
`t = c` and a polynomial `a` has, once transported to `Y`, the divisor of the canonical
generator attached to the base point of `V` and to the class of `a(c)` there. -/
theorem divisor_openGenerator_sectionGenerator (U : Y.affineOpens)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hsV : coordPoly fk c U ∈ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (a : Polynomial Γ(Y, U.1)) (haV : a ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (dimY : DimensionFunction Y) :
    (openGenerator U.1 (isAffineOpen Y U).isoSpec.symm
        (@VectorBundle.sectionGenerator _ _ _ (chartConst fk c U)
          (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
          (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).isPrime hsV a haV)).divisor dimY =
      (pointGenerator ((chartInclusion U).base (VectorBundle.basePoint (chartConst fk c U) V hsV))
        (specChartUnit U.1 (isAffineOpen Y U).isoSpec.symm
          (VectorBundle.basePoint (chartConst fk c U) V hsV)
          (Polynomial.eval (chartConst fk c U) a)
          (eval_notMem_basePoint _ V hsV a haV))).divisor dimY := by
  refine divisor_openGenerator_eq_pointGenerator dimY U.1 (isAffineOpen Y U).isoSpec.symm
    (@VectorBundle.sectionGenerator _ _ _ (chartConst fk c U)
      (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
      (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).isPrime hsV a haV)
    (VectorBundle.genericPointImage_sectionGenerator_eq_basePoint (chartConst fk c U)
      (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal hsV a haV)
    (specResidueUnit (CommRingCat.of Γ(Y, U.1))
      (VectorBundle.basePoint (chartConst fk c U) V hsV)
      (Polynomial.eval (chartConst fk c U) a) (eval_notMem_basePoint _ V hsV a haV)) ?_
  rw [VectorBundle.residueFunction_sectionGenerator]
  exact units_map_residueFieldCongr_specResidueUnit (CommRingCat.of Γ(Y, U.1)) _ _ _ _

/-- The difference of the two Gysin summands of a component, transported to the base, is the
divisor of the canonical generator attached to the base point of the component and to the ratio
of the two evaluations. -/
theorem divisor_openGenerator_sectionGenerator_sub (U : Y.affineOpens)
    (V : ↑(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hsV : coordPoly fk c U ∈ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (a b : Polynomial Γ(Y, U.1))
    (haV : a ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hbV : b ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (dimY : DimensionFunction Y) :
    (openGenerator U.1 (isAffineOpen Y U).isoSpec.symm
        (@VectorBundle.sectionGenerator _ _ _ (chartConst fk c U)
          (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
          (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).isPrime hsV a haV)).divisor dimY -
      (openGenerator U.1 (isAffineOpen Y U).isoSpec.symm
        (@VectorBundle.sectionGenerator _ _ _ (chartConst fk c U)
          (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
          (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).isPrime hsV b hbV)).divisor dimY =
      (pointGenerator ((chartInclusion U).base (VectorBundle.basePoint (chartConst fk c U) V hsV))
        (specChartRatio U.1 (isAffineOpen Y U).isoSpec.symm
          (VectorBundle.basePoint (chartConst fk c U) V hsV)
          (Polynomial.eval (chartConst fk c U) a) (Polynomial.eval (chartConst fk c U) b)
          (eval_notMem_basePoint _ V hsV a haV)
          (eval_notMem_basePoint _ V hsV b hbV))).divisor dimY := by
  rw [divisor_openGenerator_sectionGenerator fk c U V hsV a haV dimY,
    divisor_openGenerator_sectionGenerator fk c U V hsV b hbV dimY,
    divisor_pointGenerator_sub]
  rfl

/-- The value at a point of the chart of a Gysin summand, computed on the base. -/
theorem sectionGeneratorDivisor_apply (U : Y.affineOpens)
    (V : ↑(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hsV : coordPoly fk c U ∈ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (a : Polynomial Γ(Y, U.1))
    (haV : a ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (dimXU : DimensionFunction (Spec (CommRingCat.of Γ(Y, U.1))))
    (dimY : DimensionFunction Y) (dimU : DimensionFunction U.1.toScheme)
    (y : ↑(Spec (CommRingCat.of Γ(Y, U.1)))) :
    (VectorBundle.sectionGeneratorDivisor (chartConst fk c U) dimXU a V :
        ↑(Spec (CommRingCat.of Γ(Y, U.1))) → ℚ) y =
      ((openGenerator U.1 (isAffineOpen Y U).isoSpec.symm
          (@VectorBundle.sectionGenerator _ _ _ (chartConst fk c U)
            (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
            (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).isPrime hsV a haV)).divisor dimY :
        Y → ℚ) ((chartInclusion U).base y) := by
  rw [VectorBundle.sectionGeneratorDivisor_of_mem (chartConst fk c U) dimXU a V hsV haV,
    ← pullbackOpen_divisor_openGenerator U.1 (isAffineOpen Y U).isoSpec.symm dimY dimU dimXU
      (@VectorBundle.sectionGenerator _ _ _ (chartConst fk c U)
        (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
        (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).isPrime hsV a haV)]
  rfl

end GysinSummand

/-! ## Auxiliary facts for the assembly of the global relation -/

section AssemblyAux

/-- The point of the spectrum of the sections over an affine chart corresponding to a point of
the base lying in that chart. -/
noncomputable def chartPoint {X : Scheme.{u}} (U : X.affineOpens) (z : X) (hz : z ∈ U.1) :
    ↥(Spec (CommRingCat.of Γ(X, U.1))) :=
  (isAffineOpen X U).isoSpec.hom.base (⟨z, hz⟩ : U.1.toScheme)

/-- The chart inclusion sends `chartPoint` back to the point it came from. -/
theorem chartInclusion_chartPoint {X : Scheme.{u}} (U : X.affineOpens) (z : X) (hz : z ∈ U.1) :
    (chartInclusion U).base (chartPoint U z hz) = z :=
  congrArg (fun w : U.1.toScheme ↦ U.1.ι.base w)
    (isoInv_isoHom_base (isAffineOpen X U).isoSpec (⟨z, hz⟩ : U.1.toScheme))

/-- The flat pullback along an open immersion only depends on the morphism. -/
theorem pullbackOpen_congr {A B : Scheme.{u}} (f f' : A ⟶ B)
    [_root_.AlgebraicGeometry.IsOpenImmersion f] [_root_.AlgebraicGeometry.IsOpenImmersion f']
    (h : f = f') (z : AlgebraicCycle B ℚ) :
    AlgebraicCycle.pullbackOpen f z = AlgebraicCycle.pullbackOpen f' z := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [AlgebraicCycle.pullbackOpen_apply, AlgebraicCycle.pullbackOpen_apply, h]

/-- `chartPoint` inverts the chart inclusion. -/
theorem chartPoint_chartInclusion {X : Scheme.{u}} (U : X.affineOpens)
    (w : ↥(Spec (CommRingCat.of Γ(X, U.1))))
    (hz : (chartInclusion U).base w ∈ U.1) :
    chartPoint U ((chartInclusion U).base w) hz = w := by
  refine (chartInclusion U).isOpenEmbedding.injective ?_
  rw [chartInclusion_chartPoint]

variable {X : Scheme.{u}} [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]

/-- A canonical point divisor vanishes outside the closure of its point. -/
theorem divisor_pointGenerator_apply_eq_zero (dim : DimensionFunction X) (z : X)
    (r : (X.residueField z)ˣ) (y : X) (h : ¬ z ⤳ y) :
    ((pointGenerator z r).divisor dim : X → ℚ) y = 0 := by
  refine divisor_apply_eq_zero_of_not_specializes dim _ y ?_
  rw [genericPointImage_pointGenerator]
  exact h

end AssemblyAux

section AssemblyChart

variable {Y : Scheme.{u}} {k : Type u} [Field k] (fk : Y ⟶ Spec (CommRingCat.of k)) (c : k)
  [_root_.AlgebraicGeometry.IsLocallyNoetherian Y]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)] [NoetherianSpace (lineSpace Y)]
  (dimE : DimensionFunction (lineSpace Y))

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian Y]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- A principal divisor of the total space restricts to zero on a chart which does not meet the
closure of the generic point of its subvariety. -/
theorem pullbackOpen_divisor_eq_zero_of_notMem (U : Y.affineOpens)
    (g : RationalFunctionGenerator (lineSpace Y))
    (hmem : g.subspace.genericPointImage ∉ polyOpens U) :
    AlgebraicCycle.pullbackOpen (polyChartMap U) (g.divisor dimE) = 0 := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [AlgebraicCycle.pullbackOpen_apply]
  refine divisor_apply_eq_zero_of_not_specializes dimE g _ fun hsp ↦ hmem ?_
  refine hsp.mem_open (polyOpens U).isOpen ?_
  exact ⟨y, (openInclusion_polyIso U).symm ▸ rfl⟩

/-- The multiplicity of a component of the intersection with the section in the coordinate
divisor, read on a chart. -/
theorem coordDivisor_apply_polyChartMap (U : Y.affineOpens)
    (p : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hp : coordPoly fk c U ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (dimChart : DimensionFunction (Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (dimPoly : DimensionFunction (polyOpens U).toScheme)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
    (coordDivisor fk c dimE U p hp : lineSpace Y → ℚ) ((polyChartMap U).base V) =
      ((coordGenerator fk c U p hp).divisor dimChart :
        ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) → ℚ) V := by
  have h : ((AlgebraicCycle.pullbackOpen (openInclusion (polyOpens U) (polyIso U))
        (coordDivisor fk c dimE U p hp) :
      AlgebraicCycle (Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) ℚ) :
      ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) → ℚ) V =
      ((coordGenerator fk c U p hp).divisor dimChart :
        ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) → ℚ) V :=
    congrArg
      (fun z : AlgebraicCycle (Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) ℚ ↦
        (z : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) → ℚ) V)
      (pullbackOpen_coordDivisor fk c dimE U dimChart dimPoly p hp)
  rw [← h, AlgebraicCycle.pullbackOpen_apply, openInclusion_polyIso]

end AssemblyChart

/-! ## The global relation -/

section Assembly

variable {Y : Scheme.{u}} {k : Type u} [Field k] (fk : Y ⟶ Spec (CommRingCat.of k)) (c : k)
  [_root_.AlgebraicGeometry.IsLocallyNoetherian Y] [NoetherianSpace Y]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)] [NoetherianSpace (lineSpace Y)]
  [LocallyOfFiniteType fk]

/-- The canonical dimension function of an affine chart of the base. -/
noncomputable abbrev baseChartDim (U : Y.affineOpens) :
    DimensionFunction (Spec (CommRingCat.of Γ(Y, U.1))) :=
  FiniteTypeDimension.dimensionFunction (chartInclusion U ≫ fk)

/-- The canonical dimension function of an affine open of the base. -/
noncomputable abbrev opensDim (U : Y.affineOpens) : DimensionFunction U.1.toScheme :=
  FiniteTypeDimension.dimensionFunction (U.1.ι ≫ fk)

/-- **The global relation produced by the Gysin map of the constant section.**  Given, on every
univariate chart whose opens contains the generic point of the subvariety of `g`, a normal form
of the restriction of the divisor of `g` with a chart-independent ratio, and a constant `c` in
general position on every chart of a finite affine cover, the Gysin image of the divisor of `g`
is a finite rational combination of divisors of canonical point generators of the base, hence a
rational-equivalence relation. -/
theorem globalGysin_divisor_mem_of_data [CompactSpace Y]
    (dimE : DimensionFunction (lineSpace Y))
    (g : RationalFunctionGenerator (lineSpace Y))
    (pp : ∀ U : Y.affineOpens, g.subspace.genericPointImage ∈ polyOpens U →
      ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (aa bb : ∀ U : Y.affineOpens, g.subspace.genericPointImage ∈ polyOpens U →
      Polynomial Γ(Y, U.1))
    (hpp : ∀ (U : Y.affineOpens) (h : g.subspace.genericPointImage ∈ polyOpens U),
      (openInclusion (polyOpens U) (polyIso U)).base (pp U h) = g.subspace.genericPointImage)
    (haa : ∀ (U : Y.affineOpens) (h : g.subspace.genericPointImage ∈ polyOpens U),
      aa U h ∉ ((pp U h : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
        PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hbb : ∀ (U : Y.affineOpens) (h : g.subspace.genericPointImage ∈ polyOpens U),
      bb U h ∉ ((pp U h : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
        PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hdiv : ∀ (U : Y.affineOpens) (h : g.subspace.genericPointImage ∈ polyOpens U),
      AlgebraicCycle.pullbackOpen (openInclusion (polyOpens U) (polyIso U)) (g.divisor dimE) =
        (VectorBundle.elementGenerator
            ((pp U h : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
              PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal (aa U h)
            (haa U h)).divisor (chartDim fk U) -
          (VectorBundle.elementGenerator
            ((pp U h : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
              PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal (bb U h)
            (hbb U h)).divisor (chartDim fk U))
    (hrat : ∀ (U : Y.affineOpens) (h : g.subspace.genericPointImage ∈ polyOpens U),
      specChartRatio (polyOpens U) (polyIso U) (pp U h) (aa U h) (bb U h) (haa U h) (hbb U h) =
        Units.map ((lineSpace Y).residueFieldCongr (hpp U h).symm).hom.hom.toMonoidHom
          g.residueFunction)
    (𝒰 : Finset Y.affineOpens) (hcov : ∀ z : Y, ∃ U ∈ 𝒰, z ∈ U.1)
    (hcP : ∀ U ∈ 𝒰, ∀ h : g.subspace.genericPointImage ∈ polyOpens U,
      coordPoly fk c U ∉ ((pp U h : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
        PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hcA : ∀ U ∈ 𝒰, ∀ h : g.subspace.genericPointImage ∈ polyOpens U,
      ∀ Q ∈ (((pp U h : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
          PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal ⊔ Ideal.span {aa U h}).minimalPrimes,
        coordPoly fk c U ∉ Q)
    (hcB : ∀ U ∈ 𝒰, ∀ h : g.subspace.genericPointImage ∈ polyOpens U,
      ∀ Q ∈ (((pp U h : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
          PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal ⊔ Ideal.span {bb U h}).minimalPrimes,
        coordPoly fk c U ∉ Q) :
    globalGysin fk c dimE (g.divisor dimE) ∈
      totalRationalRelations Y (FiniteTypeDimension.dimensionFunction fk) := by
  classical
  have _ : CompactSpace (lineSpace Y) := compactSpace_lineSpace
  obtain ⟨U₀, hU₀mem, hU₀⟩ := hcov ((trivialData Y PUnit.{u + 1}).proj.base
    g.subspace.genericPointImage)
  have hη₀ : g.subspace.genericPointImage ∈ polyOpens U₀ := (mem_polyOpens_iff U₀ _).2 hU₀
  set Dg : AlgebraicCycle (lineSpace Y) ℚ :=
    coordDivisor fk c dimE U₀ (pp U₀ hη₀) (hcP U₀ hU₀mem hη₀) with hDgdef
  have hDgeq : ∀ (U : Y.affineOpens) (hU : U ∈ 𝒰)
      (h : g.subspace.genericPointImage ∈ polyOpens U),
      coordDivisor fk c dimE U (pp U h) (hcP U hU h) = Dg := by
    intro U hU h
    rw [hDgdef]
    refine coordDivisor_eq fk c dimE (pp U₀ hη₀) (pp U h) _ _ ?_
    rw [hpp U h, hpp U₀ hη₀]
  have hDgspec : ∀ q : lineSpace Y, (Dg : lineSpace Y → ℚ) q ≠ 0 →
      g.subspace.genericPointImage ⤳ q := by
    intro q hq
    by_contra hns
    refine hq ?_
    rw [hDgdef]
    simp only [coordDivisor]
    refine divisor_pointGenerator_apply_eq_zero dimE _ _ q ?_
    rw [hpp U₀ hη₀]
    exact hns
  have hDgfin : (Function.support (Dg : lineSpace Y → ℚ)).Finite :=
    AlgebraicCycle.finite_support Dg
  set Z : Finset Y := Finset.preimage hDgfin.toFinset
    (sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base
    (Function.Injective.injOn (sectionMap_base_injective fk c)) with hZdef
  have hmemZ : ∀ z : Y, z ∈ Z ↔ (Dg : lineSpace Y → ℚ)
      ((sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base z) ≠ 0 := by
    intro z
    rw [hZdef, Finset.mem_preimage, Set.Finite.mem_toFinset, Function.mem_support]
  set Pred : ∀ z : Y, (Y.residueField z)ˣ → Prop := fun z r ↦
    ∀ (U : Y.affineOpens), U ∈ 𝒰 → ∀ (h : g.subspace.genericPointImage ∈ polyOpens U)
      (y : ↥(Spec (CommRingCat.of Γ(Y, U.1)))) (hy : (chartInclusion U).base y = z)
      (ha : Polynomial.eval (chartConst fk c U) (aa U h) ∉
        (y : PrimeSpectrum Γ(Y, U.1)).asIdeal)
      (hb : Polynomial.eval (chartConst fk c U) (bb U h) ∉
        (y : PrimeSpectrum Γ(Y, U.1)).asIdeal),
      Units.map (Y.residueFieldCongr hy).hom.hom.toMonoidHom
          (specChartRatio U.1 (isAffineOpen Y U).isoSpec.symm y
            (Polynomial.eval (chartConst fk c U) (aa U h))
            (Polynomial.eval (chartConst fk c U) (bb U h)) ha hb) = r with hPreddef
  obtain ⟨ratio, hratio⟩ : ∃ ratio : ∀ z : Y, (Y.residueField z)ˣ,
      ∀ z : Y, (∃ r, Pred z r) → Pred z (ratio z) := by
    refine ⟨fun z ↦ if h : ∃ r : (Y.residueField z)ˣ, Pred z r then h.choose else 1, ?_⟩
    intro z hex
    simp only [dif_pos hex]
    exact hex.choose_spec
  have hexists : ∀ (z : Y), g.subspace.genericPointImage ⤳
        (sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base z →
      ∀ (U₁ : Y.affineOpens), U₁ ∈ 𝒰 →
      ∀ (h₁ : g.subspace.genericPointImage ∈ polyOpens U₁)
        (y₁ : ↥(Spec (CommRingCat.of Γ(Y, U₁.1))))
        (hy₁ : (chartInclusion U₁).base y₁ = z)
        (ha₁ : Polynomial.eval (chartConst fk c U₁) (aa U₁ h₁) ∉
          (y₁ : PrimeSpectrum Γ(Y, U₁.1)).asIdeal)
        (hb₁ : Polynomial.eval (chartConst fk c U₁) (bb U₁ h₁) ∉
          (y₁ : PrimeSpectrum Γ(Y, U₁.1)).asIdeal),
      Pred z (Units.map (Y.residueFieldCongr hy₁).hom.hom.toMonoidHom
        (specChartRatio U₁.1 (isAffineOpen Y U₁).isoSpec.symm y₁
          (Polynomial.eval (chartConst fk c U₁) (aa U₁ h₁))
          (Polynomial.eval (chartConst fk c U₁) (bb U₁ h₁)) ha₁ hb₁)) := by
    intro z hsp U₁ hU₁ h₁ y₁ hy₁ ha₁ hb₁
    simp only [hPreddef]
    intro U hU h y hy ha hb
    have hzz' : (chartInclusion U).base y = (chartInclusion U₁).base y₁ := by rw [hy, hy₁]
    have key := specChartRatio_base_eq fk c (pp U₁ h₁) (pp U h) y₁ y
      (aa U₁ h₁) (bb U₁ h₁) (aa U h) (bb U h)
      (haa U₁ h₁) (hbb U₁ h₁) (haa U h) (hbb U h) ha₁ hb₁ ha hb
      (by rw [hpp U₁ h₁, hy₁]; exact hsp)
      (by rw [hpp U h, hpp U₁ h₁])
      hzz'
      (by rw [hrat U h, hrat U₁ h₁, units_map_residueFieldCongr_trans])
    have h2 := congrArg (Units.map (Y.residueFieldCongr hy₁).hom.hom.toMonoidHom) key
    rw [units_map_residueFieldCongr_trans] at h2
    exact h2
  have hρmem : (∑ z ∈ Z, (Dg : lineSpace Y → ℚ)
        ((sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base z) •
      (pointGenerator z (ratio z)).divisor (FiniteTypeDimension.dimensionFunction fk)) ∈
      totalRationalRelations Y (FiniteTypeDimension.dimensionFunction fk) :=
    Submodule.sum_mem _ fun z _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  refine Eq.mpr (congrArg (fun t : AlgebraicCycle Y ℚ ↦ t ∈ totalRationalRelations Y
    (FiniteTypeDimension.dimensionFunction fk)) ?_) hρmem
  apply Function.locallyFinsuppWithin.ext
  intro y₀
  obtain ⟨U, hU𝒰, hyU⟩ := hcov y₀
  obtain ⟨y, rfl⟩ : ∃ y, (chartInclusion U).base y = y₀ :=
    ⟨chartPoint U y₀ hyU, chartInclusion_chartPoint U y₀ hyU⟩
  have hRHS : ((∑ z ∈ Z, (Dg : lineSpace Y → ℚ)
          ((sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base z) •
        (pointGenerator z (ratio z)).divisor (FiniteTypeDimension.dimensionFunction fk) :
        AlgebraicCycle Y ℚ) : Y → ℚ) ((chartInclusion U).base y) =
      ∑ z ∈ Z, (Dg : lineSpace Y → ℚ)
          ((sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base z) *
        (((pointGenerator z (ratio z)).divisor
          (FiniteTypeDimension.dimensionFunction fk) : Y → ℚ) ((chartInclusion U).base y)) := by
    rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [Function.locallyFinsuppWithin.coe_rational_smul]
    simp [smul_eq_mul]
  rw [globalGysin_apply, hRHS]
  by_cases hη : g.subspace.genericPointImage ∈ polyOpens U
  · have hP : coordPoly fk c U ∉ ((pp U hη : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
        PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal := hcP U hU𝒰 hη
    have hgoodA := VectorBundle.hgood_of_avoid (chartConst fk c U)
      ((pp U hη : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
        PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal hP (aa U hη) (haa U hη) (hcA U hU𝒰 hη)
    have hgoodB := VectorBundle.hgood_of_avoid (chartConst fk c U)
      ((pp U hη : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
        PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal hP (bb U hη) (hbb U hη) (hcB U hU𝒰 hη)
    have hdimU : ∀ P' : Ideal (Polynomial Γ(Y, U.1)), P'.IsPrime →
        GromovWitten.AlgebraicGeometry.HasDimensionFormula (Polynomial Γ(Y, U.1) ⧸ P') :=
      (FiniteTypeDimension.hasUniversalDimensionFormula_sections fk U.1 U.2).polynomial
    have hdiv' := (pullbackOpen_congr (openInclusion (polyOpens U) (polyIso U))
      (polyChartMap U) (openInclusion_polyIso U) (g.divisor dimE)).symm.trans (hdiv U hη)
    rw [hdiv', map_sub,
      VectorBundle.sectionGysin_elementGenerator_eq_finsetSum (chartConst fk c U)
        (baseChartDim fk U) (chartDim fk U) hdimU
        ((pp U hη : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
          PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal hP (aa U hη) (haa U hη) hgoodA,
      VectorBundle.sectionGysin_elementGenerator_eq_finsetSum (chartConst fk c U)
        (baseChartDim fk U) (chartDim fk U) hdimU
        ((pp U hη : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
          PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal hP (bb U hη) (hbb U hη) hgoodB,
      Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply,
      Function.locallyFinsuppWithin.coe_sum, Function.locallyFinsuppWithin.coe_sum,
      Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]
    set D0 : AlgebraicCycle (Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) ℚ :=
      (VectorBundle.elementGenerator
        ((pp U hη : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
          PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
        (VectorBundle.sectionPoly (chartConst fk c U)) hP).divisor (chartDim fk U) with hD0
    set S : Finset ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) :=
      (AlgebraicCycle.finite_support D0).toFinset with hSdef
    have hmemS : ∀ V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))),
        V ∈ S ↔ (D0 : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) → ℚ) V ≠ 0 := by
      intro V
      rw [hSdef, Set.Finite.mem_toFinset, Function.mem_support]
    have hsuppA : ∀ V ∈ S,
        ((pp U hη : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1))))) :
            PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal <
          (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal ∧
        VectorBundle.sectionPoly (chartConst fk c U) ∈
          (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal ∧
        aa U hη ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal := fun V hV ↦
      VectorBundle.support_divisor_sectionPoly (chartConst fk c U) (chartDim fk U) _ hP
        (aa U hη) hgoodA V ((hmemS V).1 hV)
    have hsuppB : ∀ V ∈ S, bb U hη ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal :=
      fun V hV ↦ (VectorBundle.support_divisor_sectionPoly (chartConst fk c U) (chartDim fk U)
        _ hP (bb U hη) hgoodB V ((hmemS V).1 hV)).2.2
    have hmult : ∀ V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))),
        (Dg : lineSpace Y → ℚ) ((polyChartMap U).base V) =
          (D0 : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) → ℚ) V := by
      intro V
      rw [← hDgeq U hU𝒰 hη, coordDivisor_apply_polyChartMap fk c dimE U (pp U hη)
        (hcP U hU𝒰 hη) (chartDim fk U) (polyOpensDim fk U) V, hD0]
      rfl
    refine Eq.trans ?_ (Finset.sum_subset (Finset.filter_subset (fun z ↦ z ∈ U.1) Z) ?_)
    · refine Finset.sum_bij'
        (fun V hV ↦ (chartInclusion U).base
          (VectorBundle.basePoint (chartConst fk c U) V (hsuppA V hV).2.1))
        (fun z hz ↦ VectorBundle.sectionPoint (chartConst fk c U)
          (chartPoint U z (Finset.mem_filter.1 hz).2)) ?_ ?_ ?_ ?_ ?_
      · intro V hV
        refine Finset.mem_filter.2 ⟨(hmemZ _).2 ?_, mem_chartInclusion_base U _⟩
        rw [sectionMap_base_chartInclusion_basePoint fk c U V (hsuppA V hV).2.1, hmult V]
        exact (hmemS V).1 hV
      · intro z hz
        refine (hmemS _).2 ?_
        rw [← hmult, polyChartMap_sectionPoint fk c U, chartInclusion_chartPoint]
        exact (hmemZ z).1 (Finset.mem_filter.1 hz).1
      · intro V hV
        rw [chartPoint_chartInclusion U (VectorBundle.basePoint (chartConst fk c U) V
          (hsuppA V hV).2.1), VectorBundle.sectionPoint_basePoint]
      · intro z hz
        rw [basePoint_sectionPoint (chartConst fk c U) (chartPoint U z
          (Finset.mem_filter.1 hz).2), chartInclusion_chartPoint]
      · intro V hV
        obtain ⟨hlt, hsV, haV⟩ := hsuppA V hV
        have hbV := hsuppB V hV
        have hspecV : g.subspace.genericPointImage ⤳
            (sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base
              ((chartInclusion U).base (VectorBundle.basePoint (chartConst fk c U) V hsV)) := by
          rw [sectionMap_base_chartInclusion_basePoint fk c U V hsV, ← hpp U hη,
            openInclusion_polyIso]
          exact ((PrimeSpectrum.le_iff_specializes _ _).1 hlt.le).map (polyChartMap U).continuous
        have hra : Polynomial.eval (chartConst fk c U) (aa U hη) ∉
            ((VectorBundle.basePoint (chartConst fk c U) V hsV :
              ↥(Spec (CommRingCat.of Γ(Y, U.1)))) : PrimeSpectrum Γ(Y, U.1)).asIdeal :=
          eval_notMem_basePoint _ V hsV (aa U hη) haV
        have hrb : Polynomial.eval (chartConst fk c U) (bb U hη) ∉
            ((VectorBundle.basePoint (chartConst fk c U) V hsV :
              ↥(Spec (CommRingCat.of Γ(Y, U.1)))) : PrimeSpectrum Γ(Y, U.1)).asIdeal :=
          eval_notMem_basePoint _ V hsV (bb U hη) hbV
        have hPz := hratio ((chartInclusion U).base
          (VectorBundle.basePoint (chartConst fk c U) V hsV))
          ⟨_, hexists _ hspecV U hU𝒰 hη (VectorBundle.basePoint (chartConst fk c U) V hsV)
            rfl hra hrb⟩
        simp only [hPreddef] at hPz
        have hratV := hPz U hU𝒰 hη (VectorBundle.basePoint (chartConst fk c U) V hsV)
          rfl hra hrb
        rw [units_map_residueFieldCongr_rfl] at hratV
        rw [Function.locallyFinsuppWithin.coe_rational_smul,
          Function.locallyFinsuppWithin.coe_rational_smul]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [sectionGeneratorDivisor_apply fk c U V hsV (aa U hη) haV (baseChartDim fk U)
            (FiniteTypeDimension.dimensionFunction fk) (opensDim fk U) y,
          sectionGeneratorDivisor_apply fk c U V hsV (bb U hη) hbV (baseChartDim fk U)
            (FiniteTypeDimension.dimensionFunction fk) (opensDim fk U) y,
          ← mul_sub, sectionMap_base_chartInclusion_basePoint fk c U V hsV, hmult V, ← hratV]
        congr 1
        exact congrArg (fun t : AlgebraicCycle Y ℚ ↦ (t : Y → ℚ) ((chartInclusion U).base y))
          (divisor_openGenerator_sectionGenerator_sub fk c U V hsV (aa U hη) (bb U hη) haV hbV
            (FiniteTypeDimension.dimensionFunction fk))
    · intro z hz hznot
      have hns : ¬ z ⤳ (chartInclusion U).base y := by
        intro hsp
        exact hznot (Finset.mem_filter.2 ⟨hz, hsp.mem_open U.1.isOpen hyU⟩)
      rw [divisor_pointGenerator_apply_eq_zero _ z (ratio z) _ hns, mul_zero]
  · rw [pullbackOpen_divisor_eq_zero_of_notMem dimE U g hη, map_zero]
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
    refine (Finset.sum_eq_zero fun z hz ↦ ?_).symm
    have hns : ¬ z ⤳ (chartInclusion U).base y := by
      intro hsp
      have hzU : z ∈ U.1 := hsp.mem_open U.1.isOpen hyU
      refine hη ?_
      have hq : (sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base z ∈ polyOpens U := by
        rw [mem_polyOpens_iff, proj_sectionMap_base]
        exact hzU
      exact (hDgspec _ ((hmemZ z).1 hz)).mem_open (polyOpens U).isOpen hq
    rw [divisor_pointGenerator_apply_eq_zero _ z (ratio z) _ hns, mul_zero]

/-- **Choice of a constant in general position for finitely many generators.**  Over an infinite
field and for a compact base, one constant `c ∈ k` makes the Gysin image of the divisor of each
of finitely many generators of the total space a rational-equivalence relation on the base. -/
theorem exists_good_constant_globalGysin [Infinite k] [CompactSpace Y]
    (dimE : DimensionFunction (lineSpace Y)) {n : ℕ}
    (G : Fin n → RationalFunctionGenerator (lineSpace Y)) :
    ∃ c : k, ∀ i : Fin n, globalGysin fk c dimE ((G i).divisor dimE) ∈
      totalRationalRelations Y (FiniteTypeDimension.dimensionFunction fk) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ : ∃ 𝒰 : Finset Y.affineOpens, ∀ z : Y, ∃ U ∈ 𝒰, z ∈ U.1 := by
    have hcover : (Set.univ : Set Y) ⊆ ⋃ U : Y.affineOpens, (U.1 : Set Y) := by
      intro z _
      obtain ⟨U, hU⟩ := exists_affineOpen_mem z
      exact Set.mem_iUnion.2 ⟨U, hU⟩
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
      (fun U : Y.affineOpens ↦ (U.1 : Set Y)) (fun U ↦ U.1.isOpen) hcover
    refine ⟨t, fun z ↦ ?_⟩
    obtain ⟨U, hUt, hz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
    exact ⟨U, hUt, hz⟩
  have hdata : ∀ (i : Fin n) (U : Y.affineOpens),
      (G i).subspace.genericPointImage ∈ polyOpens U →
      ∃ (p : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
        (hp : (openInclusion (polyOpens U) (polyIso U)).base p =
          (G i).subspace.genericPointImage)
        (a b : Polynomial Γ(Y, U.1))
        (ha : a ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
        (hb : b ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal),
        AlgebraicCycle.pullbackOpen (openInclusion (polyOpens U) (polyIso U))
            ((G i).divisor dimE) =
            (VectorBundle.elementGenerator
              (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal a ha).divisor (chartDim fk U) -
              (VectorBundle.elementGenerator
                (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal b hb).divisor
                (chartDim fk U) ∧
          specChartRatio (polyOpens U) (polyIso U) p a b ha hb =
            Units.map ((lineSpace Y).residueFieldCongr hp.symm).hom.hom.toMonoidHom
              (G i).residueFunction :=
    fun i U h ↦ exists_polyChart_normalForm (G i) dimE U (chartDim fk U) (polyOpensDim fk U) h
  choose pp hpp aa bb haa hbb hmain using hdata
  let halg : ∀ j : Fin n × {U : Y.affineOpens // U ∈ 𝒰},
      Algebra k Γ(Y, (j.2.1).1) := fun j ↦ FiniteTypeDimension.sectionsAlgebra fk (j.2.1).1
  set T : ∀ j : Fin n × {U : Y.affineOpens // U ∈ 𝒰},
      Set (Ideal (Polynomial Γ(Y, (j.2.1).1))) := fun j ↦
    if h : (G j.1).subspace.genericPointImage ∈ polyOpens j.2.1 then
      insert ((pp j.1 j.2.1 h : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, (j.2.1).1))))) :
          PrimeSpectrum (Polynomial Γ(Y, (j.2.1).1))).asIdeal
        ((((pp j.1 j.2.1 h : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, (j.2.1).1))))) :
              PrimeSpectrum (Polynomial Γ(Y, (j.2.1).1))).asIdeal ⊔
            Ideal.span {aa j.1 j.2.1 h}).minimalPrimes ∪
          (((pp j.1 j.2.1 h : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, (j.2.1).1))))) :
              PrimeSpectrum (Polynomial Γ(Y, (j.2.1).1))).asIdeal ⊔
            Ideal.span {bb j.1 j.2.1 h}).minimalPrimes)
    else ∅ with hTdef
  have hTfin : ∀ j, (T j).Finite := by
    intro j
    simp only [hTdef]
    by_cases h : (G j.1).subspace.genericPointImage ∈ polyOpens j.2.1
    · rw [dif_pos h]
      exact Set.Finite.insert _ ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).union
        (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _))
    · rw [dif_neg h]
      exact Set.finite_empty
  have hTne : ∀ j, ∀ Q ∈ T j, Q ≠ ⊤ := by
    intro j Q hQ
    simp only [hTdef] at hQ
    by_cases h : (G j.1).subspace.genericPointImage ∈ polyOpens j.2.1
    · rw [dif_pos h] at hQ
      rcases hQ with rfl | hQ | hQ
      · exact ((pp j.1 j.2.1 h : ↥(Spec (CommRingCat.of
          (Polynomial Γ(Y, (j.2.1).1))))) : PrimeSpectrum _).isPrime.ne_top
      · exact hQ.1.1.ne_top
      · exact hQ.1.1.ne_top
    · rw [dif_neg h] at hQ
      exact absurd hQ (Set.notMem_empty Q)
  obtain ⟨c, hc⟩ := VectorBundle.exists_good_constant_family (k := k)
    (fun j : Fin n × {U : Y.affineOpens // U ∈ 𝒰} ↦ Γ(Y, (j.2.1).1)) T hTfin hTne
  refine ⟨c, fun i ↦ ?_⟩
  refine globalGysin_divisor_mem_of_data fk c dimE (G i) (pp i) (aa i) (bb i) (hpp i) (haa i)
    (hbb i) (fun U h ↦ (hmain i U h).1) (fun U h ↦ (hmain i U h).2) 𝒰 h𝒰 ?_ ?_ ?_
  · intro U hU h
    exact hc (i, ⟨U, hU⟩) _ (by simp only [hTdef, dif_pos h]; exact Set.mem_insert _ _)
  · intro U hU h Q hQ
    exact hc (i, ⟨U, hU⟩) Q
      (by simp only [hTdef, dif_pos h]; exact Set.mem_insert_of_mem _ (Or.inl hQ))
  · intro U hU h Q hQ
    exact hc (i, ⟨U, hU⟩) Q
      (by simp only [hTdef, dif_pos h]; exact Set.mem_insert_of_mem _ (Or.inr hQ))

end Assembly

/-! ## The rank-one injectivity theorem and its consequences -/

section RankOne

variable {k : Type u} [Field k] [Infinite k] {Y : Scheme.{u}}

/-- **Injectivity of the flat pullback along the trivial line bundle.**  For a compact scheme
locally of finite type over an infinite field, a cycle whose pullback to `Y × 𝔸¹` is a rational
equivalence relation is itself a rational equivalence relation. -/
theorem pullbackBundle_injective_rankOne (f : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [CompactSpace Y] (w : AlgebraicCycle Y ℚ)
    (hw : BundlePullbackGlobal.pullbackBundle (trivialData Y PUnit.{u + 1}) w ∈
      totalRationalRelations (trivialData Y PUnit.{u + 1}).totalSpace
        (FiniteTypeDimension.dimensionFunction ((trivialData Y PUnit.{u + 1}).proj ≫ f))) :
    w ∈ totalRationalRelations Y (FiniteTypeDimension.dimensionFunction f) := by
  classical
  have _ := isLocallyNoetherian_base f
  have _ : NoetherianSpace Y := inferInstance
  have _ := isLocallyNoetherian_lineSpace f
  have _ := noetherianSpace_lineSpace f
  obtain ⟨n, qs, gs, hsum⟩ := Submodule.mem_span_set'.1 hw
  choose G hG using fun i : Fin n ↦ (gs i).2
  obtain ⟨c, hc⟩ := exists_good_constant_globalGysin f
    (FiniteTypeDimension.dimensionFunction ((trivialData Y PUnit.{u + 1}).proj ≫ f)) G
  have hlin : globalGysin f c
        (FiniteTypeDimension.dimensionFunction ((trivialData Y PUnit.{u + 1}).proj ≫ f))
        (∑ i : Fin n, qs i • ((gs i : AlgebraicCycle (lineSpace Y) ℚ))) =
      ∑ i : Fin n, qs i • globalGysin f c
        (FiniteTypeDimension.dimensionFunction ((trivialData Y PUnit.{u + 1}).proj ≫ f))
        ((gs i : AlgebraicCycle (lineSpace Y) ℚ)) := by
    have h := map_sum (globalGysinLinear f c
        (FiniteTypeDimension.dimensionFunction ((trivialData Y PUnit.{u + 1}).proj ≫ f)))
      (fun i : Fin n ↦ qs i • ((gs i : AlgebraicCycle (lineSpace Y) ℚ))) Finset.univ
    simp only [map_smul] at h
    exact h
  have hkey : w = ∑ i : Fin n, qs i • globalGysin f c
      (FiniteTypeDimension.dimensionFunction ((trivialData Y PUnit.{u + 1}).proj ≫ f))
      ((G i).divisor
        (FiniteTypeDimension.dimensionFunction ((trivialData Y PUnit.{u + 1}).proj ≫ f))) := by
    rw [← globalGysin_pullbackBundle f c
      (FiniteTypeDimension.dimensionFunction ((trivialData Y PUnit.{u + 1}).proj ≫ f)) w,
      ← hsum, hlin]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hGi : (G i).divisor
        (FiniteTypeDimension.dimensionFunction ((trivialData Y PUnit.{u + 1}).proj ≫ f)) =
        (gs i : AlgebraicCycle (lineSpace Y) ℚ) := hG i
    rw [hGi]
  rw [hkey]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (hc i)

/-- **The rank-one injectivity statement of `BundleHomotopyInjectiveGlobal.lean` holds over any
infinite field.** -/
theorem rankOneInjective (k : Type u) [Field k] [Infinite k] :
    BundlePullbackGlobal.RankOneInjective k :=
  fun _ f _ _ w hw ↦ pullbackBundle_injective_rankOne f w hw

end RankOne

section Corollaries

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [CompactSpace X]
  {ι : Type u} [Finite ι]

/-- **Injectivity of the flat pullback along a trivial bundle of any finite rank.** -/
theorem pullbackBundle_trivialData_injective (w : AlgebraicCycle X ℚ)
    (hw : BundlePullbackGlobal.pullbackBundle (trivialData X ι) w ∈
      totalRationalRelations (trivialData X ι).totalSpace
        (FiniteTypeDimension.dimensionFunction ((trivialData X ι).proj ≫ f))) :
    w ∈ totalRationalRelations X (FiniteTypeDimension.dimensionFunction f) :=
  BundlePullbackGlobal.pullbackBundle_trivialData_injective (rankOneInjective k) f w hw

/-- **Injectivity of the flat pullback along a globally trivialisable vector bundle.** -/
theorem pullbackBundle_injective_of_globalTrivialisation {𝓔 : BundleData X ι}
    (t : GlobalTrivialisation 𝓔) (w : AlgebraicCycle X ℚ)
    (hw : BundlePullbackGlobal.pullbackBundle 𝓔 w ∈
      totalRationalRelations 𝓔.totalSpace
        (FiniteTypeDimension.dimensionFunction (𝓔.proj ≫ f))) :
    w ∈ totalRationalRelations X (FiniteTypeDimension.dimensionFunction f) :=
  BundlePullbackGlobal.pullbackBundle_injective_of_globalTrivialisation (rankOneInjective k)
    f t w hw

/-- **Injectivity of the flat pullback on Chow groups** for a globally trivialisable bundle. -/
theorem chowPullbackBundleGlobal_injective {𝓔 : BundleData X ι}
    (t : GlobalTrivialisation 𝓔) (i : ℤ)
    (RX : RationalEquivalenceSystem X (FiniteTypeDimension.dimensionFunction f) i)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace
      (FiniteTypeDimension.dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ))) :
    Function.Injective (BundleOverSubscheme.chowPullbackBundleGlobal 𝓔
      (FiniteTypeDimension.dimensionFunction f)
      (FiniteTypeDimension.dimensionFunction (𝓔.proj ≫ f))
      (FiniteTypeDimension.dimensionFunction_bundlePoint f 𝓔) i RX RE) :=
  BundlePullbackGlobal.chowPullbackBundleGlobal_injective (rankOneInjective k) f t i RX RE

end Corollaries

end LineBundleInjective

end GromovWitten.AlgebraicGeometry.IntersectionTheory
