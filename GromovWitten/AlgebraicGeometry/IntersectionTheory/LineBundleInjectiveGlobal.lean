/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleInjective

/-!
# The global Gysin map of the constant section of the trivial line bundle

`IntersectionTheory/LineBundleInjective.lean` proved the injectivity of the flat pullback along
a globally trivial bundle when one trivialising chart already covers the base, and supplied the
normal form `divisor_pointGenerator` of a principal divisor together with the chart independence
`divisor_chartGenerator_eq`.  This file continues that work: it constructs the **global** Gysin
map of the constant section `t = c` of the trivial line bundle `E = Y × 𝔸¹` over an arbitrary
scheme `Y` over a field, and shows that it inverts the flat pullback.

The construction glues the affine section Gysin maps `VectorBundle.sectionGysin` of the charts
`Spec (Polynomial Γ(Y, U))` of `E` (`CycleGluing.glue`).  The compatibility of the charts is the
main content: the value of an affine Gysin summand at a point of the base is the value at the
corresponding point of the section of the divisor on `E` of the coordinate `t - c` on the closure
of a point of `E` (`sectionGysinTerm_eq_coordDivisor`), and that divisor does not depend on the
chart it is computed in (`coordDivisor_eq`).  The latter rests on the chart independence of the
class of `t - c` in the residue field of `E` at a point (`coordUnit_eq`), which is proved by
passing to a common affine refinement of two charts.

What is **not** proved here is that the global Gysin map carries a principal divisor of `E` into
the span of the principal divisors of `Y`; this is the only missing step of the multi-chart
injectivity theorem, and it is carried as the explicit hypothesis `hgysin` of
`pullbackBundle_injective_of_gysin`.

## Main declarations

* `LineBundleInjective.openGenerator V e g`, `openResidueUnit`, `divisor_openGenerator_eq`,
  `pullbackOpen_divisor_openGenerator` — the transport of a generator to `X` from a chart
  presented by an isomorphism `e : W ≅ V.toScheme`, generalising `chartGenerator` from the
  affine charts of `X` to arbitrary ones;
* `LineBundleInjective.openUnit`, `openUnit_comp`, `residueFieldMap_specResidueUnit`,
  `openUnit_specResidueUnit_comp` — residue classes read on a chart and their behaviour under a
  refinement of charts;
* `LineBundleInjective.polyChartMap U` — the chart `Spec (Polynomial Γ(Y, U)) ⟶ E` of the total
  space, with `polyChartMap_comp` and `polyOpens_eq`;
* `LineBundleInjective.coordUnit`, `coordUnit_eq` — the class of `t - c` in the residue field of
  `E` at a point of a chart, and its chart independence;
* `LineBundleInjective.coordDivisor`, `coordDivisor_eq`, `sectionGysinTerm_eq_coordDivisor`,
  `sectionGysinTerm_chart_eq` — the divisor of `t - c` on the closure of a point of `E` and the
  chart independence of the affine Gysin summands;
* `LineBundleInjective.sectionGysin_apply_le`, `sectionGysin_apply_congr` — the affine Gysin
  maps of two charts agree at corresponding points;
* `LineBundleInjective.globalGysin`, `globalGysinLinear`, `globalGysin_apply` — the global Gysin
  map and its chart formula;
* `LineBundleInjective.globalGysin_pullbackBundle` — the global Gysin map inverts the flat
  pullback along the trivial line bundle;
* `LineBundleInjective.pullbackBundle_injective_of_gysin` — injectivity of the flat pullback,
  modulo the Gysin image of a principal divisor;
* `LineBundleInjective.isLocallyNoetherian_base`, `isLocallyNoetherian_lineSpace`,
  `compactSpace_lineSpace`, `noetherianSpace_lineSpace` — the standing hypotheses in the
  finite-type case.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)

namespace LineBundleInjective

/-! ## Generators transported from an arbitrary chart -/

section OpenGenerator

variable {X W : Scheme.{u}} [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]
  (V : X.Opens) (e : W ≅ V.toScheme)

/-- The open immersion of a chart of `X` into `X`: a scheme `W` isomorphic to an open subscheme
`V` of `X`. -/
noncomputable abbrev openInclusion : W ⟶ X := e.hom ≫ V.ι

/-- The transport to `X` of a principal-divisor generator living on a chart: first along the
chart isomorphism `W ≅ V`, then by taking the closure in `X`. -/
noncomputable def openGenerator (g : RationalFunctionGenerator W) :
    RationalFunctionGenerator X :=
  (g.transportIso e).closureIn V

/-- The generic point of a generator transported from a chart is the image of the generic point
of the generator. -/
theorem genericPointImage_openGenerator (g : RationalFunctionGenerator W) :
    (openGenerator V e g).subspace.genericPointImage =
      (openInclusion V e).base g.subspace.genericPointImage := by
  rw [openGenerator, RationalFunctionGenerator.genericPointImage_closureIn]
  rfl

/-- The residue function of a generator transported from a chart, read through the residue field
map of the chart inclusion. -/
theorem residueFunction_openGenerator (g : RationalFunctionGenerator W) :
    Units.map ((openInclusion V e).residueFieldMap
          g.subspace.genericPointImage).hom.toMonoidHom
        (Units.map (X.residueFieldCongr
            (genericPointImage_openGenerator V e g)).hom.hom.toMonoidHom
          (openGenerator V e g).residueFunction) =
      g.residueFunction := by
  refine Units.ext ?_
  rw [Units.coe_map, Units.coe_map]
  have hcomp : ∀ z : X.residueField ((openInclusion V e).base g.subspace.genericPointImage),
      ((openInclusion V e).residueFieldMap g.subspace.genericPointImage).hom z =
        (e.hom.residueFieldMap g.subspace.genericPointImage).hom
          ((V.ι.residueFieldMap (e.hom.base g.subspace.genericPointImage)).hom z) := by
    intro z
    rw [_root_.AlgebraicGeometry.Scheme.residueFieldMap_comp]
    rfl
  refine (hcomp _).trans (Eq.trans (congrArg (fun t ↦
      (e.hom.residueFieldMap g.subspace.genericPointImage).hom t)
    (RationalFunctionGenerator.residueFunction_closureIn V (g.transportIso e)).symm) ?_)
  exact RationalFunctionGenerator.residueFieldMap_residueFunction_closedImage g e.hom

/-- **The chart-independent datum of a generator living on a chart**: the class of its rational
function in the residue field of `X` at the image of its generic point. -/
noncomputable def openResidueUnit (g : RationalFunctionGenerator W) :
    (X.residueField ((openInclusion V e).base g.subspace.genericPointImage))ˣ :=
  Units.map (X.residueFieldCongr
      (genericPointImage_openGenerator V e g)).hom.hom.toMonoidHom
    (openGenerator V e g).residueFunction

/-- `openResidueUnit` is determined by the data on the chart: it maps to the residue function of
the generator under the (isomorphic) residue field map of the chart inclusion. -/
theorem residueFieldMap_openResidueUnit (g : RationalFunctionGenerator W) :
    Units.map ((openInclusion V e).residueFieldMap
        g.subspace.genericPointImage).hom.toMonoidHom (openResidueUnit V e g) =
      g.residueFunction :=
  residueFunction_openGenerator V e g

/-- **Normal form of the divisor of a generator transported from a chart**: it is the divisor of
the canonical generator attached to the image of its generic point and to its residue class
there. -/
theorem divisor_openGenerator (dim : DimensionFunction X) (g : RationalFunctionGenerator W) :
    (openGenerator V e g).divisor dim =
      (pointGenerator ((openInclusion V e).base g.subspace.genericPointImage)
        (openResidueUnit V e g)).divisor dim := by
  rw [openResidueUnit, divisor_pointGenerator_congr dim
    (genericPointImage_openGenerator V e g) (openGenerator V e g).residueFunction,
    divisor_pointGenerator]

/-- Flat pullback along a composite of open immersions. -/
theorem pullbackOpen_comp {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C)
    [_root_.AlgebraicGeometry.IsOpenImmersion p] [_root_.AlgebraicGeometry.IsOpenImmersion q]
    (z : AlgebraicCycle C ℚ) :
    AlgebraicCycle.pullbackOpen (p ≫ q) z =
      AlgebraicCycle.pullbackOpen p (AlgebraicCycle.pullbackOpen q z) := by
  apply Function.locallyFinsuppWithin.ext
  intro a
  rfl

/-- The restriction to the chart of the divisor of a transported generator is the divisor of the
generator. -/
theorem pullbackOpen_divisor_openGenerator (dimX : DimensionFunction X)
    (dimV : DimensionFunction V.toScheme) (dimW : DimensionFunction W)
    (g : RationalFunctionGenerator W) :
    AlgebraicCycle.pullbackOpen (openInclusion V e) ((openGenerator V e g).divisor dimX) =
      g.divisor dimW := by
  rw [pullbackOpen_comp, openGenerator,
    RationalFunctionGenerator.pullbackOpen_divisor_closureIn V (g.transportIso e) dimX dimV,
    RationalFunctionGenerator.pullbackOpen_divisor_transportIso e g dimW dimV]

end OpenGenerator

/-- **Chart independence.**  Two generators living on two charts have the same divisor on `X` as
soon as the images of their generic points agree and their residue classes at that common point
agree. -/
theorem divisor_openGenerator_eq {X W W' : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]
    (dim : DimensionFunction X) (V : X.Opens) (e : W ≅ V.toScheme)
    (V' : X.Opens) (e' : W' ≅ V'.toScheme)
    (g : RationalFunctionGenerator W) (g' : RationalFunctionGenerator W')
    (hy : (openInclusion V' e').base g'.subspace.genericPointImage =
      (openInclusion V e).base g.subspace.genericPointImage)
    (hu : Units.map (X.residueFieldCongr hy).hom.hom.toMonoidHom (openResidueUnit V' e' g') =
      openResidueUnit V e g) :
    (openGenerator V' e' g').divisor dim = (openGenerator V e g).divisor dim := by
  rw [divisor_openGenerator V' e' dim g', divisor_openGenerator V e dim g, ← hu,
    divisor_pointGenerator_congr dim hy (openResidueUnit V' e' g')]

/-! ## Residue classes read on a chart -/

section OpenUnit

variable {X W : Scheme.{u}} [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]
  (V : X.Opens) (e : W ≅ V.toScheme)

/-- The class in the residue field of `X` at `(openInclusion V e).base x` of a unit of the
residue field of the chart at `x`.  The residue field map of an open immersion is an
isomorphism, so this is well defined. -/
noncomputable def openUnit (x : W) (u : (W.residueField x)ˣ) :
    (X.residueField ((openInclusion V e).base x))ˣ :=
  Units.map (CategoryTheory.inv ((openInclusion V e).residueFieldMap x)).hom.toMonoidHom u

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- `openUnit` is a section of the residue field map of the chart inclusion. -/
@[simp]
theorem residueFieldMap_openUnit (x : W) (u : (W.residueField x)ˣ) :
    Units.map ((openInclusion V e).residueFieldMap x).hom.toMonoidHom (openUnit V e x u) = u := by
  refine Units.ext ?_
  rw [Units.coe_map, openUnit, Units.coe_map]
  change (CategoryTheory.inv ((openInclusion V e).residueFieldMap x) ≫
    (openInclusion V e).residueFieldMap x).hom _ = _
  rw [CategoryTheory.IsIso.inv_hom_id]
  rfl

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The residue field map of the chart inclusion is injective, being a homomorphism of fields. -/
theorem injective_residueFieldMap_openInclusion (x : W) :
    Function.Injective ((openInclusion V e).residueFieldMap x).hom :=
  ((openInclusion V e).residueFieldMap x).hom.injective

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- A unit of the residue field of `X` at a point of a chart is determined by its image in the
residue field of the chart. -/
theorem openUnit_eq_of_residueFieldMap_eq (x : W) (u : (W.residueField x)ˣ)
    (v : (X.residueField ((openInclusion V e).base x))ˣ)
    (hv : Units.map ((openInclusion V e).residueFieldMap x).hom.toMonoidHom v = u) :
    v = openUnit V e x u := by
  refine Units.ext (injective_residueFieldMap_openInclusion V e x ?_)
  have h : ((openInclusion V e).residueFieldMap x).hom (v : X.residueField _) = (u : _) :=
    congrArg Units.val hv
  have h2 : ((openInclusion V e).residueFieldMap x).hom
      ((openUnit V e x u : X.residueField _)) = (u : _) :=
    congrArg Units.val (residueFieldMap_openUnit V e x u)
  rw [h, h2]

/-- `openResidueUnit` is the class of the residue function of the generator. -/
theorem openResidueUnit_eq_openUnit (g : RationalFunctionGenerator W) :
    openResidueUnit V e g =
      openUnit V e g.subspace.genericPointImage g.residueFunction :=
  openUnit_eq_of_residueFieldMap_eq V e _ _ _ (residueFieldMap_openResidueUnit V e g)

end OpenUnit

/-- **Refinement of charts.**  If a chart `W'` maps into a chart `W` compatibly with the two
inclusions into `X`, the class in the residue field of `X` of a unit read on `W` agrees with the
class of its image on `W'`. -/
theorem openUnit_comp {X W W' : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]
    (V : X.Opens) (e : W ≅ V.toScheme) (V' : X.Opens) (e' : W' ≅ V'.toScheme)
    (ψ : W' ⟶ W) (hψ : ψ ≫ openInclusion V e = openInclusion V' e') (x' : W')
    (u : (W.residueField (ψ.base x'))ˣ)
    (hy : (openInclusion V e).base (ψ.base x') = (openInclusion V' e').base x') :
    openUnit V' e' x' (Units.map (ψ.residueFieldMap x').hom.toMonoidHom u) =
      Units.map (X.residueFieldCongr hy).hom.hom.toMonoidHom
        (openUnit V e (ψ.base x') u) := by
  refine (openUnit_eq_of_residueFieldMap_eq V' e' x' _ _ ?_).symm
  refine Units.ext ?_
  rw [Units.coe_map, Units.coe_map, Units.coe_map]
  have hkey : (X.residueFieldCongr hy).hom ≫ (openInclusion V' e').residueFieldMap x' =
      (openInclusion V e).residueFieldMap (ψ.base x') ≫ ψ.residueFieldMap x' := by
    rw [← _root_.AlgebraicGeometry.Scheme.residueFieldMap_comp,
      _root_.AlgebraicGeometry.Scheme.Hom.residueFieldMap_congr hψ x']
    rfl
  have happ := ConcreteCategory.congr_hom hkey
    ((openUnit V e (ψ.base x') u : X.residueField ((openInclusion V e).base (ψ.base x'))))
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at happ
  exact happ.trans (congrArg (fun t ↦ (ψ.residueFieldMap x').hom t)
    (congrArg Units.val (residueFieldMap_openUnit V e (ψ.base x') u)))

/-! ## Residue classes of ring elements on an affine chart -/

/-- The residue field map of `Spec.map φ` sends the class of `b` to the class of `φ b`. -/
theorem residueFieldMap_specResidueUnit {B B' : CommRingCat.{u}} (φ : B ⟶ B')
    (x' : ↥(Spec B')) (b : B)
    (hb : b ∉ ((((Spec.map φ).base x' : ↥(Spec B))) : PrimeSpectrum B).asIdeal)
    (hb' : φ b ∉ ((x' : PrimeSpectrum B')).asIdeal) :
    Units.map ((Spec.map φ).residueFieldMap x').hom.toMonoidHom
        (specResidueUnit B ((Spec.map φ).base x') b hb) =
      specResidueUnit B' x' (φ b) hb' := by
  refine Units.ext ?_
  rw [Units.coe_map, specResidueUnit_val_eq_residue, specResidueUnit_val_eq_residue]
  change ((Spec.map φ).residueFieldMap x') _ = _
  rw [residue_residueFieldMap_apply, stalkMap_spec_algebraMap]

/-- **The class of a ring element read on two comparable affine charts.**  If `Spec φ` maps the
chart `Spec B'` into the chart `Spec B` compatibly with the inclusions into `X`, then the class
of `φ b` computed on `Spec B'` is the class of `b` computed on `Spec B`. -/
theorem openUnit_specResidueUnit_comp {X : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]
    {B B' : CommRingCat.{u}} (Vb : X.Opens) (e : Spec B ≅ Vb.toScheme)
    (Vb' : X.Opens) (e' : Spec B' ≅ Vb'.toScheme) (φ : B ⟶ B')
    (hφ : Spec.map φ ≫ openInclusion Vb e = openInclusion Vb' e') (x' : ↥(Spec B')) (b : B)
    (hb : b ∉ ((((Spec.map φ).base x' : ↥(Spec B))) : PrimeSpectrum B).asIdeal)
    (hb' : φ b ∉ ((x' : PrimeSpectrum B')).asIdeal)
    (hy : (openInclusion Vb e).base ((Spec.map φ).base x') =
      (openInclusion Vb' e').base x') :
    openUnit Vb' e' x' (specResidueUnit B' x' (φ b) hb') =
      Units.map (X.residueFieldCongr hy).hom.hom.toMonoidHom
        (openUnit Vb e ((Spec.map φ).base x') (specResidueUnit B _ b hb)) := by
  rw [← residueFieldMap_specResidueUnit φ x' b hb hb']
  exact openUnit_comp Vb e Vb' e' (Spec.map φ) hφ x' _ hy

/-! ## Affine charts of the base -/

section BaseChart

variable {X : Scheme.{u}}

/-- The affine charts of a scheme are compatible with the restriction maps of the structure
sheaf. -/
theorem specMap_res_comp_isoSpec_inv {U V : X.affineOpens} (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (GlobalBlowup.res X h)) ≫ (isAffineOpen X V).isoSpec.inv =
      (isAffineOpen X U).isoSpec.inv ≫ X.homOfLE (h : U.1 ≤ V.1) := by
  rw [← cancel_mono V.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι]
  exact (isAffineOpen X V).map_fromSpec (isAffineOpen X U) (homOfLE (h : U.1 ≤ V.1)).op

/-- The inclusions of the affine charts of a scheme are compatible with the restriction maps. -/
theorem chartInclusion_comp {U V : X.affineOpens} (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (GlobalBlowup.res X h)) ≫ chartInclusion V = chartInclusion U := by
  rw [chartInclusion, chartInclusion, ← Category.assoc, specMap_res_comp_isoSpec_inv h,
    Category.assoc, Scheme.homOfLE_ι]

/-- The affine chart of a scheme over `U`, presented as an open subscheme. -/
theorem openInclusion_isoSpec_symm (U : X.affineOpens) :
    openInclusion U.1 (isAffineOpen X U).isoSpec.symm = chartInclusion U := rfl

end BaseChart

/-! ## The univariate charts of the trivial line bundle -/

section LineBundle

variable {Y : Scheme.{u}}

/-- The comparison of the `PUnit`-indexed and the univariate polynomial ring is natural in the
coefficient ring. -/
theorem polyMap_uniqueAlgEquiv {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    (Polynomial.mapRingHom g).comp (VectorBundle.polyTrivialization A).symm.toRingHom =
      ((VectorBundle.polyTrivialization B).symm.toRingHom).comp (MvPolynomial.map g) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp [VectorBundle.polyTrivialization]
  · simp [VectorBundle.polyTrivialization]

/-- The trivialising chart of the total space of the trivial line bundle over an affine open,
written as the spectrum of a univariate polynomial ring. -/
noncomputable def polyChartMap (U : Y.affineOpens) :
    Spec (CommRingCat.of (Polynomial Γ(Y, U.1))) ⟶ (trivialData Y PUnit.{u + 1}).totalSpace :=
  VectorBundle.mvSectionSpecMap Γ(Y, U.1) ≫ (trivialData Y PUnit.{u + 1}).chartι U

/-- The univariate chart is the affine chart composed with the comparison of polynomial rings. -/
theorem polyChartMap_eq (U : Y.affineOpens) :
    polyChartMap U =
      VectorBundle.mvSectionSpecMap Γ(Y, U.1) ≫ (trivialData Y PUnit.{u + 1}).chartι U := rfl

instance isOpenImmersion_polyChartMap (U : Y.affineOpens) :
    _root_.AlgebraicGeometry.IsOpenImmersion (polyChartMap U) := by
  rw [polyChartMap]
  infer_instance

/-- The affine charts of a relative `Spec` are compatible with the transition maps. -/
theorem specMap_map_affineι {X : Scheme.{u}} (𝒜 : AlgebraData X) {U V : X.affineOpens}
    (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (𝒜.map h)) ≫ RelativeSpec.affineι X 𝒜 V =
      RelativeSpec.affineι X 𝒜 U :=
  Limits.colimit.w (RelativeSpec.gluingData X 𝒜).functor (homOfLE h)

/-- The trivialising charts of the trivial bundle are compatible with the restriction maps of
the base. -/
theorem specMap_map_chartι {X : Scheme.{u}} {ι : Type u} {U V : X.affineOpens} (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (GlobalBlowup.res X h))) ≫
        (trivialData X ι).chartι V =
      (trivialData X ι).chartι U := by
  rw [trivialData_chartι, trivialData_chartι]
  exact specMap_map_affineι (trivialAlgebraData X ι) h

/-- The univariate charts of the total space of the trivial line bundle are compatible with the
restriction maps of the base. -/
theorem polyChartMap_comp {U V : Y.affineOpens} (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y h))) ≫
        polyChartMap V =
      polyChartMap U := by
  have hring : CommRingCat.ofHom
        ((VectorBundle.polyTrivialization Γ(Y, V.1)).symm.toRingHom) ≫
        CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y h)) =
      CommRingCat.ofHom (MvPolynomial.map (GlobalBlowup.res Y h)) ≫
        CommRingCat.ofHom ((VectorBundle.polyTrivialization Γ(Y, U.1)).symm.toRingHom) :=
    CommRingCat.hom_ext (RingHom.ext fun p ↦
      RingHom.congr_fun (polyMap_uniqueAlgEquiv (GlobalBlowup.res Y h)) p)
  rw [polyChartMap, polyChartMap, VectorBundle.mvSectionSpecMap,
    VectorBundle.mvSectionSpecMap, ← specMap_map_chartι (ι := PUnit.{u + 1}) h,
    ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp, hring]

/-- The total space of the trivial line bundle over `Y`. -/
noncomputable abbrev lineSpace (Y : Scheme.{u}) : Scheme.{u} :=
  (trivialData Y PUnit.{u + 1}).totalSpace

/-- The open subscheme of the total space covered by the univariate chart over `U`. -/
noncomputable abbrev polyOpens (U : Y.affineOpens) : (lineSpace Y).Opens :=
  (polyChartMap U).opensRange

/-- The univariate chart of the total space, as an isomorphism onto its open image. -/
noncomputable abbrev polyIso (U : Y.affineOpens) :
    Spec (CommRingCat.of (Polynomial Γ(Y, U.1))) ≅ (polyOpens U).toScheme :=
  (polyChartMap U).isoOpensRange

/-- The chart inclusion attached to the univariate chart is the chart map itself. -/
theorem openInclusion_polyIso (U : Y.affineOpens) :
    openInclusion (polyOpens U) (polyIso U) = polyChartMap U :=
  (polyChartMap U).isoOpensRange_hom_ι

/-- The univariate chart of the total space covers the preimage of the affine open. -/
theorem polyOpens_eq (U : Y.affineOpens) :
    polyOpens U = (trivialData Y PUnit.{u + 1}).proj ⁻¹ᵁ U.1 := by
  have h : (VectorBundle.mvSectionSpecMap Γ(Y, U.1) ≫
      (trivialData Y PUnit.{u + 1}).chartι U).opensRange =
      (trivialData Y PUnit.{u + 1}).proj ⁻¹ᵁ U.1 := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, BundleData.opensRange_chartι,
      trivialData_chart]
  exact h

/-- A point of the total space lies in the univariate chart over `U` exactly when its image in
the base does. -/
theorem mem_polyOpens_iff (U : Y.affineOpens) (q : lineSpace Y) :
    q ∈ polyOpens U ↔ (trivialData Y PUnit.{u + 1}).proj.base q ∈ U.1 := by
  rw [polyOpens_eq]
  rfl

/-- Transport of a unit of a residue field along a composite equality of points. -/
theorem units_map_residueFieldCongr_trans {X : Scheme.{u}} {a b d : X} (h₁ : a = b) (h₂ : b = d)
    (u : (X.residueField a)ˣ) :
    Units.map (X.residueFieldCongr h₂).hom.hom.toMonoidHom
        (Units.map (X.residueFieldCongr h₁).hom.hom.toMonoidHom u) =
      Units.map (X.residueFieldCongr (h₁.trans h₂)).hom.hom.toMonoidHom u := by
  subst h₁
  subst h₂
  rfl

/-- Transport of units along an equality of points is injective. -/
theorem units_map_residueFieldCongr_injective {X : Scheme.{u}} {a b : X} (h : a = b) :
    Function.Injective
      (Units.map (X.residueFieldCongr h).hom.hom.toMonoidHom :
        (X.residueField a)ˣ → (X.residueField b)ˣ) := by
  subst h
  intro x y hxy
  exact hxy

end LineBundle

/-! ## The coordinate of the trivial line bundle -/

section Coordinate

variable {Y : Scheme.{u}} {k : Type u} [Field k] (fk : Y ⟶ Spec (CommRingCat.of k)) (c : k)
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)] [NoetherianSpace (lineSpace Y)]

/-- The constant `c` read as a section over an affine open of the base. -/
noncomputable abbrev chartConst (U : Y.affineOpens) : Γ(Y, U.1) :=
  FiniteTypeDimension.structureMap fk U.1 c

/-- The coordinate `t - c` of the trivial line bundle, read on the univariate chart over `U`. -/
noncomputable abbrev coordPoly (U : Y.affineOpens) : Polynomial Γ(Y, U.1) :=
  VectorBundle.sectionPoly (chartConst fk c U)

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- The coordinate is compatible with the restriction maps of the base. -/
theorem mapRingHom_coordPoly {U V : Y.affineOpens} (h : U ≤ V) :
    Polynomial.mapRingHom (GlobalBlowup.res Y h) (coordPoly fk c V) = coordPoly fk c U := by
  simp [VectorBundle.sectionPoly, res_structureMap]

/-- The class of the coordinate `t - c` in the residue field of the total space at a point of a
chart which does not lie on the section. -/
noncomputable def coordUnit (U : Y.affineOpens)
    (p : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hp : coordPoly fk c U ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal) :
    ((lineSpace Y).residueField ((openInclusion (polyOpens U) (polyIso U)).base p))ˣ :=
  openUnit (polyOpens U) (polyIso U) p
    (specResidueUnit (CommRingCat.of (Polynomial Γ(Y, U.1))) p (coordPoly fk c U) hp)

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- The class of an element of a ring in a residue field depends only on the element. -/
theorem specResidueUnit_congr (B : CommRingCat.{u}) (x : ↥(Spec B)) {b b' : B} (hbb' : b = b')
    (hb : b ∉ ((x : PrimeSpectrum B)).asIdeal) (hb' : b' ∉ ((x : PrimeSpectrum B)).asIdeal) :
    specResidueUnit B x b hb = specResidueUnit B x b' hb' := by
  subst hbb'
  rfl

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- The chart inclusions of the univariate charts are compatible with the restriction maps. -/
theorem openInclusion_polyIso_comp {U V : Y.affineOpens} (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y h))) ≫
        openInclusion (polyOpens V) (polyIso V) =
      openInclusion (polyOpens U) (polyIso U) := by
  rw [openInclusion_polyIso, openInclusion_polyIso]
  exact polyChartMap_comp h

/-- **The coordinate class computed on a smaller chart.**  The class of `t - c` at a point of the
total space does not change when it is computed on a smaller trivialising chart. -/
theorem coordUnit_le {U V : Y.affineOpens} (h : U ≤ V)
    (p : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hp : coordPoly fk c U ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hpV : coordPoly fk c V ∉
      ((((Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (GlobalBlowup.res Y h)))).base p :
        ↥(Spec (CommRingCat.of (Polynomial Γ(Y, V.1))))) :
          PrimeSpectrum (Polynomial Γ(Y, V.1)))).asIdeal)
    (hy : (openInclusion (polyOpens V) (polyIso V)).base
        ((Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (GlobalBlowup.res Y h)))).base p) =
      (openInclusion (polyOpens U) (polyIso U)).base p) :
    coordUnit fk c U p hp =
      Units.map ((lineSpace Y).residueFieldCongr hy).hom.hom.toMonoidHom
        (coordUnit fk c V _ hpV) := by
  have hp2 : (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y h)))
      (coordPoly fk c V) ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal := by
    rw [show (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y h)))
        (coordPoly fk c V) = coordPoly fk c U from mapRingHom_coordPoly fk c h]
    exact hp
  have hres := residueFieldMap_specResidueUnit
    (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y h))) p
    (coordPoly fk c V) hpV hp2
  rw [specResidueUnit_congr (CommRingCat.of (Polynomial Γ(Y, U.1))) p
    (show (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y h)))
        (coordPoly fk c V) = coordPoly fk c U from mapRingHom_coordPoly fk c h) hp2 hp] at hres
  have hcomp := openUnit_comp (polyOpens V) (polyIso V) (polyOpens U) (polyIso U)
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y h))))
    (openInclusion_polyIso_comp h) p
    (specResidueUnit (CommRingCat.of (Polynomial Γ(Y, V.1))) _ (coordPoly fk c V) hpV) hy
  rw [hres] at hcomp
  exact hcomp

/-- **Chart independence of the coordinate class.**  The class of `t - c` in the residue field of
the total space at a point does not depend on the trivialising chart used to compute it. -/
theorem coordUnit_eq {U U' : Y.affineOpens}
    (p : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (p' : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U'.1)))))
    (hp : coordPoly fk c U ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hp' : coordPoly fk c U' ∉ (p' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (hq : (openInclusion (polyOpens U') (polyIso U')).base p' =
      (openInclusion (polyOpens U) (polyIso U)).base p) :
    Units.map ((lineSpace Y).residueFieldCongr hq).hom.hom.toMonoidHom
        (coordUnit fk c U' p' hp') =
      coordUnit fk c U p hp := by
  have hqU : (openInclusion (polyOpens U) (polyIso U)).base p ∈ polyOpens U := by
    refine ⟨p, ?_⟩
    rw [openInclusion_polyIso]
  have hqU' : (openInclusion (polyOpens U) (polyIso U)).base p ∈ polyOpens U' := by
    rw [← hq]
    refine ⟨p', ?_⟩
    rw [openInclusion_polyIso]
  rw [mem_polyOpens_iff] at hqU hqU'
  obtain ⟨W, hWaff, hyW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
    Y.isBasis_affineOpens (show (trivialData Y PUnit.{u + 1}).proj.base
      ((openInclusion (polyOpens U) (polyIso U)).base p) ∈ U.1 ⊓ U'.1 from ⟨hqU, hqU'⟩)
  have hWU : (⟨W, hWaff⟩ : Y.affineOpens) ≤ U := (le_trans hWle inf_le_left : W ≤ U.1)
  have hWU' : (⟨W, hWaff⟩ : Y.affineOpens) ≤ U' := (le_trans hWle inf_le_right : W ≤ U'.1)
  have hmem : (openInclusion (polyOpens U) (polyIso U)).base p ∈
      polyOpens (⟨W, hWaff⟩ : Y.affineOpens) := by
    rw [mem_polyOpens_iff]
    exact hyW
  obtain ⟨pW, hpW⟩ := hmem
  have hinclW : (openInclusion (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
      (polyIso (⟨W, hWaff⟩ : Y.affineOpens))).base pW =
      (openInclusion (polyOpens U) (polyIso U)).base p := by
    rw [openInclusion_polyIso]
    exact hpW
  have hbase : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (GlobalBlowup.res Y hWU)))).base pW = p := by
    refine (openInclusion (polyOpens U) (polyIso U)).isOpenEmbedding.injective ?_
    have := congrArg (fun m : Spec (CommRingCat.of (Polynomial Γ(Y, W))) ⟶ lineSpace Y ↦ m.base pW)
      (openInclusion_polyIso_comp (V := U) hWU)
    exact this.trans hinclW
  have hbase' : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (GlobalBlowup.res Y hWU')))).base pW = p' := by
    refine (openInclusion (polyOpens U') (polyIso U')).isOpenEmbedding.injective ?_
    have := congrArg (fun m : Spec (CommRingCat.of (Polynomial Γ(Y, W))) ⟶ lineSpace Y ↦ m.base pW)
      (openInclusion_polyIso_comp (V := U') hWU')
    rw [hq]
    exact this.trans hinclW
  have hpWmem : coordPoly fk c (⟨W, hWaff⟩ : Y.affineOpens) ∉
      (pW : PrimeSpectrum (Polynomial Γ(Y, W))).asIdeal := by
    rw [← mapRingHom_coordPoly fk c hWU]
    rw [← hbase] at hp
    exact hp
  subst hbase
  subst hbase'
  have hy1 := hinclW.symm
  have hy2 := hq.trans hinclW.symm
  have h1 := coordUnit_le fk c hWU pW hpWmem hp hy1
  have h2 := coordUnit_le fk c hWU' pW hpWmem hp' hy2
  refine units_map_residueFieldCongr_injective hy1 ?_
  rw [units_map_residueFieldCongr_trans, ← h1]
  exact h2.symm

/-! ## Transport lemmas for residue classes -/

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- The class of a ring element transported along an equality of points. -/
theorem units_map_residueFieldCongr_specResidueUnit (B : CommRingCat.{u}) {x x' : ↥(Spec B)}
    (h : x = x') (b : B) (hb : b ∉ ((x : PrimeSpectrum B)).asIdeal)
    (hb' : b ∉ ((x' : PrimeSpectrum B)).asIdeal) :
    Units.map ((Spec B).residueFieldCongr h).hom.hom.toMonoidHom (specResidueUnit B x b hb) =
      specResidueUnit B x' b hb' := by
  subst h
  rfl

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- The residue field map of a morphism commutes with the transport along an equality of
points. -/
theorem units_map_residueFieldMap_congr {X W : Scheme.{u}} (j : W ⟶ X) {x x' : W} (h : x = x')
    (u : (X.residueField (j.base x))ˣ) :
    Units.map (j.residueFieldMap x').hom.toMonoidHom
        (Units.map (X.residueFieldCongr (congrArg j.base h)).hom.hom.toMonoidHom u) =
      Units.map (W.residueFieldCongr h).hom.hom.toMonoidHom
        (Units.map (j.residueFieldMap x).hom.toMonoidHom u) := by
  subst h
  rfl

end Coordinate

/-! ## The divisor of the coordinate on the closure of a point -/

section CoordDivisor

variable {Y : Scheme.{u}} {k : Type u} [Field k] (fk : Y ⟶ Spec (CommRingCat.of k)) (c : k)
  [_root_.AlgebraicGeometry.IsLocallyNoetherian Y]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)] [NoetherianSpace (lineSpace Y)]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- The sections over an affine open of a locally Noetherian scheme form a Noetherian ring. -/
instance isNoetherianRing_sections_affine (U : Y.affineOpens) : IsNoetherianRing Γ(Y, U.1) :=
  _root_.AlgebraicGeometry.IsLocallyNoetherian.component_noetherian U

/-- The generator of the divisor of `t - c` on the closure of a point of a chart. -/
noncomputable def coordGenerator (U : Y.affineOpens)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hV : coordPoly fk c U ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal) :
    RationalFunctionGenerator (Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) :=
  @VectorBundle.elementGenerator Γ(Y, U.1) _ (isNoetherianRing_sections_affine U)
    (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
    (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).isPrime (coordPoly fk c U) hV

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- `coordGenerator` is the affine generator of the coordinate on the closure of the point. -/
theorem coordGenerator_eq (U : Y.affineOpens)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hV : coordPoly fk c U ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal) :
    coordGenerator fk c U V hV =
      @VectorBundle.elementGenerator Γ(Y, U.1) _ (isNoetherianRing_sections_affine U)
        (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
        (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).isPrime (coordPoly fk c U) hV := rfl

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- The generic point of the subspace of `coordGenerator` is the given point. -/
theorem genericPointImage_coordGenerator (U : Y.affineOpens)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hV : coordPoly fk c U ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal) :
    (coordGenerator fk c U V hV).subspace.genericPointImage = V := by
  have h := @VectorBundle.genericPointImage_elementGenerator Γ(Y, U.1) _
    (isNoetherianRing_sections_affine U) (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
    (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).isPrime (coordPoly fk c U) hV
  exact PrimeSpectrum.ext h

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- The coordinate does not vanish at the generic point of `coordGenerator`. -/
theorem notMem_genericPointImage_coordGenerator (U : Y.affineOpens)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hV : coordPoly fk c U ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal) :
    coordPoly fk c U ∉ ((((coordGenerator fk c U V hV).subspace.genericPointImage :
      ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))) :
        PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal :=
  @VectorBundle.notMem_genericPointImage_elementGenerator Γ(Y, U.1) _
    (isNoetherianRing_sections_affine U) (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
    (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).isPrime (coordPoly fk c U) hV

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- The residue function of `coordGenerator` is the class of the coordinate. -/
theorem residueFunction_coordGenerator (U : Y.affineOpens)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hV : coordPoly fk c U ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal) :
    (coordGenerator fk c U V hV).residueFunction =
      specResidueUnit (CommRingCat.of (Polynomial Γ(Y, U.1)))
        (coordGenerator fk c U V hV).subspace.genericPointImage (coordPoly fk c U)
        (notMem_genericPointImage_coordGenerator fk c U V hV) :=
  @VectorBundle.residueFunction_elementGenerator Γ(Y, U.1) _
    (isNoetherianRing_sections_affine U) (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
    (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).isPrime (coordPoly fk c U) hV

/-- The class of the coordinate at the generic point of `coordGenerator` is `coordUnit`. -/
theorem openResidueUnit_coordGenerator (U : Y.affineOpens)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hV : coordPoly fk c U ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal) :
    Units.map ((lineSpace Y).residueFieldCongr
        (congrArg (openInclusion (polyOpens U) (polyIso U)).base
          (genericPointImage_coordGenerator fk c U V hV))).hom.hom.toMonoidHom
      (openResidueUnit (polyOpens U) (polyIso U) (coordGenerator fk c U V hV)) =
      coordUnit fk c U V hV := by
  have _ := isNoetherianRing_sections_affine (Y := Y) U
  change _ = openUnit (polyOpens U) (polyIso U) V
    (specResidueUnit (CommRingCat.of (Polynomial Γ(Y, U.1))) V (coordPoly fk c U) hV)
  refine openUnit_eq_of_residueFieldMap_eq (polyOpens U) (polyIso U) V _ _ ?_
  rw [units_map_residueFieldMap_congr, residueFieldMap_openResidueUnit,
    residueFunction_coordGenerator,
    units_map_residueFieldCongr_specResidueUnit]
  exact genericPointImage_coordGenerator fk c U V hV

variable (dimE : DimensionFunction (lineSpace Y))

/-- **The divisor on the total space of the coordinate `t - c`** on the closure of a point of a
chart which does not lie on the section. -/
noncomputable def coordDivisor (U : Y.affineOpens)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hV : coordPoly fk c U ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal) :
    AlgebraicCycle (lineSpace Y) ℚ :=
  (pointGenerator ((openInclusion (polyOpens U) (polyIso U)).base V)
    (coordUnit fk c U V hV)).divisor dimE

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian Y] in
/-- **Chart independence of the coordinate divisor.** -/
theorem coordDivisor_eq {U U' : Y.affineOpens}
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (V' : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U'.1)))))
    (hV : coordPoly fk c U ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hV' : coordPoly fk c U' ∉ (V' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (hq : (openInclusion (polyOpens U') (polyIso U')).base V' =
      (openInclusion (polyOpens U) (polyIso U)).base V) :
    coordDivisor fk c dimE U' V' hV' = coordDivisor fk c dimE U V hV := by
  rw [coordDivisor, coordDivisor, ← coordUnit_eq fk c V V' hV hV' hq,
    divisor_pointGenerator_congr dimE hq (coordUnit fk c U' V' hV')]

/-- The coordinate divisor is the divisor on the total space of the transported affine
coordinate generator. -/
theorem coordDivisor_eq_divisor (U : Y.affineOpens)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hV : coordPoly fk c U ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal) :
    coordDivisor fk c dimE U V hV =
      (openGenerator (polyOpens U) (polyIso U) (coordGenerator fk c U V hV)).divisor dimE := by
  rw [coordDivisor, ← openResidueUnit_coordGenerator fk c U V hV,
    divisor_pointGenerator_congr dimE
      (congrArg (openInclusion (polyOpens U) (polyIso U)).base
        (genericPointImage_coordGenerator fk c U V hV))
      (openResidueUnit (polyOpens U) (polyIso U) (coordGenerator fk c U V hV)),
    divisor_openGenerator]

/-- The restriction of the coordinate divisor to a chart is the affine divisor of `t - c`. -/
theorem pullbackOpen_coordDivisor (U : Y.affineOpens)
    (dimChart : DimensionFunction (Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (dimPoly : DimensionFunction (polyOpens U).toScheme)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hV : coordPoly fk c U ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal) :
    AlgebraicCycle.pullbackOpen (openInclusion (polyOpens U) (polyIso U))
        (coordDivisor fk c dimE U V hV) =
      (coordGenerator fk c U V hV).divisor dimChart := by
  rw [coordDivisor_eq_divisor, pullbackOpen_divisor_openGenerator _ _ dimE dimPoly dimChart]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian Y]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- Evaluation at a constant through the comparison of the `PUnit`-indexed and the univariate
polynomial ring is evaluation of the multivariable polynomial at that constant. -/
theorem evalRingHom_comp_polyTrivialization_symm {A : Type u} [CommRing A] (a : A) :
    (Polynomial.evalRingHom a).comp (VectorBundle.polyTrivialization A).symm.toRingHom =
      (MvPolynomial.aeval (R := A) fun _ : PUnit.{u + 1} ↦ a).toRingHom := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp [VectorBundle.polyTrivialization]
  · simp [VectorBundle.polyTrivialization]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian Y]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- **The constant section read on a univariate chart.**  Over an affine open of the base the
global constant section of the trivial line bundle is the affine constant section of
`Spec (Polynomial Γ(Y, U))`. -/
theorem chartInclusion_comp_sectionMap (U : Y.affineOpens) :
    chartInclusion U ≫ sectionMap fk PUnit.{u + 1} (fun _ ↦ c) =
      VectorBundle.sectionMap (chartConst fk c U) ≫ polyChartMap U := by
  have h1 : VectorBundle.sectionMap (chartConst fk c U) ≫ polyChartMap U =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := Γ(Y, U.1))
          fun _ : PUnit.{u + 1} ↦ chartConst fk c U).toRingHom) ≫
        (trivialData Y PUnit.{u + 1}).chartι U := by
    rw [VectorBundle.sectionMap, polyChartMap_eq, VectorBundle.mvSectionSpecMap,
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      evalRingHom_comp_polyTrivialization_symm]
  rw [h1, chartInclusion, Category.assoc, trivialData_chartι]
  exact sectionMap_chart fk PUnit.{u + 1} (fun _ ↦ c) U

variable [LocallyOfFiniteType fk]

/-- The canonical dimension function of a univariate chart of the total space. -/
noncomputable abbrev chartDim (U : Y.affineOpens) :
    DimensionFunction (Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) :=
  FiniteTypeDimension.dimensionFunction
    (polyChartMap U ≫ (trivialData Y PUnit.{u + 1}).proj ≫ fk)

/-- The canonical dimension function of the open subscheme covered by a univariate chart. -/
noncomputable abbrev polyOpensDim (U : Y.affineOpens) :
    DimensionFunction (polyOpens U).toScheme :=
  FiniteTypeDimension.dimensionFunction
    ((polyOpens U).ι ≫ (trivialData Y PUnit.{u + 1}).proj ≫ fk)

/-- **The Gysin summand of a chart is the global coordinate divisor read along the section.**
This is the statement which makes the affine section Gysin map glue. -/
theorem sectionGysinTerm_eq_coordDivisor (U : Y.affineOpens)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (hV : coordPoly fk c U ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (y : ↥(Spec (CommRingCat.of Γ(Y, U.1)))) :
    (@VectorBundle.sectionGysinTerm Γ(Y, U.1) _ (isNoetherianRing_sections_affine U)
        (chartConst fk c U) (chartDim fk U) V :
        ↥(Spec (CommRingCat.of Γ(Y, U.1))) → ℚ) y =
      (coordDivisor fk c dimE U V hV : lineSpace Y → ℚ)
        ((sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base ((chartInclusion U).base y)) := by
  have _ := isNoetherianRing_sections_affine (Y := Y) U
  rw [VectorBundle.sectionGysinTerm_of_notMem _ _ _ hV, VectorBundle.sectionRestrict_apply]
  have hdiv : (@VectorBundle.sectionDivisor Γ(Y, U.1) _ (isNoetherianRing_sections_affine U)
      (chartConst fk c U) (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
      (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).isPrime hV).divisor (chartDim fk U) =
      AlgebraicCycle.pullbackOpen (openInclusion (polyOpens U) (polyIso U))
        (coordDivisor fk c dimE U V hV) :=
    (pullbackOpen_coordDivisor fk c dimE U (chartDim fk U) (polyOpensDim fk U) V hV).symm
  rw [hdiv, AlgebraicCycle.pullbackOpen_apply, openInclusion_polyIso]
  have hpt : (polyChartMap U).base
      (VectorBundle.sectionPoint (chartConst fk c U) y) =
      (sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base ((chartInclusion U).base y) := by
    have := congrArg (fun m : Spec (CommRingCat.of Γ(Y, U.1)) ⟶ lineSpace Y ↦ m.base y)
      (chartInclusion_comp_sectionMap fk c U)
    exact this.symm
  rw [hpt]

include dimE in
/-- **Chart independence of the Gysin summand.**  Two charts give the same Gysin summand at
corresponding points. -/
theorem sectionGysinTerm_chart_eq {U U' : Y.affineOpens}
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (V' : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U'.1)))))
    (hV : coordPoly fk c U ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hV' : coordPoly fk c U' ∉ (V' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (hq : (openInclusion (polyOpens U') (polyIso U')).base V' =
      (openInclusion (polyOpens U) (polyIso U)).base V)
    (y : ↥(Spec (CommRingCat.of Γ(Y, U.1)))) (y' : ↥(Spec (CommRingCat.of Γ(Y, U'.1))))
    (hyy' : (chartInclusion U').base y' = (chartInclusion U).base y) :
    (@VectorBundle.sectionGysinTerm Γ(Y, U.1) _ (isNoetherianRing_sections_affine U)
        (chartConst fk c U) (chartDim fk U) V :
        ↥(Spec (CommRingCat.of Γ(Y, U.1))) → ℚ) y =
      (@VectorBundle.sectionGysinTerm Γ(Y, U'.1) _ (isNoetherianRing_sections_affine U')
        (chartConst fk c U') (chartDim fk U') V' :
        ↥(Spec (CommRingCat.of Γ(Y, U'.1))) → ℚ) y' := by
  rw [sectionGysinTerm_eq_coordDivisor fk c dimE U V hV y,
    sectionGysinTerm_eq_coordDivisor fk c dimE U' V' hV' y',
    coordDivisor_eq fk c dimE V V' hV hV' hq, hyy']

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian Y]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] [LocallyOfFiniteType fk] in
/-- The projection sends the constant section of a point back to that point. -/
theorem proj_sectionMap_base (y : Y) :
    (trivialData Y PUnit.{u + 1}).proj.base
      ((sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base y) = y := by
  have h := congrArg (fun m : Y ⟶ Y ↦ m.base y) (sectionMap_proj fk PUnit.{u + 1} (fun _ ↦ c))
  exact h

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] in
/-- **Localisation of the Gysin summands.**  A point of a chart whose image in the total space
does not lie over a smaller chart contributes nothing at the points of that smaller chart. -/
theorem sectionGysinTerm_eq_zero_of_notMem (U W : Y.affineOpens)
    (V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (y : ↥(Spec (CommRingCat.of Γ(Y, U.1))))
    (hy : (chartInclusion U).base y ∈ W.1)
    (hV : (polyChartMap U).base V ∉ polyOpens W) :
    (VectorBundle.sectionGysinTerm (chartConst fk c U) (chartDim fk U) V :
      ↥(Spec (CommRingCat.of Γ(Y, U.1))) → ℚ) y = 0 := by
  by_cases hmem : coordPoly fk c U ∈ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal
  · rw [VectorBundle.sectionGysinTerm_of_mem _ _ _ hmem]
    rfl
  · rw [VectorBundle.sectionGysinTerm_of_notMem _ _ _ hmem, VectorBundle.sectionRestrict_apply]
    refine VectorBundle.elementGenerator_divisor_apply_of_not_le _ _ hmem _ _ fun hle ↦ hV ?_
    have hspec : (V : PrimeSpectrum (Polynomial Γ(Y, U.1))) ⤳
        (VectorBundle.sectionPoint (chartConst fk c U) y : PrimeSpectrum (Polynomial Γ(Y, U.1))) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 hle
    have hmap := hspec.map (polyChartMap U).continuous
    refine hmap.mem_open (polyOpens W).isOpen ?_
    have hpt : (polyChartMap U).base (VectorBundle.sectionPoint (chartConst fk c U) y) =
        (sectionMap fk PUnit.{u + 1} (fun _ ↦ c)).base ((chartInclusion U).base y) := by
      have := congrArg (fun m : Spec (CommRingCat.of Γ(Y, U.1)) ⟶ lineSpace Y ↦ m.base y)
        (chartInclusion_comp_sectionMap fk c U)
      exact this.symm
    have hgoal : (polyChartMap U).base (VectorBundle.sectionPoint (chartConst fk c U) y) ∈
        polyOpens W := by
      rw [hpt, mem_polyOpens_iff, proj_sectionMap_base]
      exact hy
    exact hgoal

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] [LocallyOfFiniteType fk] in
/-- A point of an affine chart of `X` maps into that chart. -/
theorem mem_chartInclusion_base {X : Scheme.{u}} (U : X.affineOpens)
    (y : ↥(Spec (CommRingCat.of Γ(X, U.1)))) : (chartInclusion U).base y ∈ U.1 :=
  ((isAffineOpen X U).isoSpec.inv.base y).2

include dimE in
/-- **Restriction of the chart Gysin map to a smaller chart.**  The value of the affine section
Gysin map of the chart over `U` at a point coming from a smaller chart `W` is computed by the
chart over `W`. -/
theorem sectionGysin_apply_le {U W : Y.affineOpens} (h : W ≤ U)
    (z : AlgebraicCycle (lineSpace Y) ℚ)
    (yW : ↥(Spec (CommRingCat.of Γ(Y, W.1)))) :
    (VectorBundle.sectionGysin (chartConst fk c U) (chartDim fk U)
        (AlgebraicCycle.pullbackOpen (polyChartMap U) z) :
        ↥(Spec (CommRingCat.of Γ(Y, U.1))) → ℚ)
      ((Spec.map (CommRingCat.ofHom (GlobalBlowup.res Y h))).base yW) =
      (VectorBundle.sectionGysin (chartConst fk c W) (chartDim fk W)
        (AlgebraicCycle.pullbackOpen (polyChartMap W) z) :
        ↥(Spec (CommRingCat.of Γ(Y, W.1))) → ℚ) yW := by
  classical
  have hψchart : Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y h))) ≫
      polyChartMap U = polyChartMap W := polyChartMap_comp h
  have hψpt : ∀ V' : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, W.1)))),
      (polyChartMap U).base ((Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (GlobalBlowup.res Y h)))).base V') =
        (polyChartMap W).base V' := fun V' ↦
    congrArg (fun m : Spec (CommRingCat.of (Polynomial Γ(Y, W.1))) ⟶ lineSpace Y ↦ m.base V')
      hψchart
  have hchart : (chartInclusion U).base
      ((Spec.map (CommRingCat.ofHom (GlobalBlowup.res Y h))).base yW) =
      (chartInclusion W).base yW :=
    congrArg (fun m : Spec (CommRingCat.of Γ(Y, W.1)) ⟶ Y ↦ m.base yW) (chartInclusion_comp h)
  have hmemW : ∀ V' : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, W.1)))),
      (coordPoly fk c U ∈ ((((Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (GlobalBlowup.res Y h)))).base V' :
        ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))) :
          PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal) ↔
      coordPoly fk c W ∈ (V' : PrimeSpectrum (Polynomial Γ(Y, W.1))).asIdeal := by
    intro V'
    rw [← mapRingHom_coordPoly fk c h]
    exact Ideal.mem_comap
  have hz : ∀ V' : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, W.1)))),
      (AlgebraicCycle.pullbackOpen (polyChartMap W) z :
          ↥(Spec (CommRingCat.of (Polynomial Γ(Y, W.1)))) → ℚ) V' =
        (AlgebraicCycle.pullbackOpen (polyChartMap U) z :
          ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) → ℚ)
          ((Spec.map (CommRingCat.ofHom
            (Polynomial.mapRingHom (GlobalBlowup.res Y h)))).base V') := by
    intro V'
    rw [AlgebraicCycle.pullbackOpen_apply, AlgebraicCycle.pullbackOpen_apply, hψpt]
  have hT : ∀ V' : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, W.1)))),
      (VectorBundle.sectionGysinTerm (chartConst fk c W) (chartDim fk W) V' :
          ↥(Spec (CommRingCat.of Γ(Y, W.1))) → ℚ) yW =
        (VectorBundle.sectionGysinTerm (chartConst fk c U) (chartDim fk U)
            ((Spec.map (CommRingCat.ofHom
              (Polynomial.mapRingHom (GlobalBlowup.res Y h)))).base V') :
          ↥(Spec (CommRingCat.of Γ(Y, U.1))) → ℚ)
          ((Spec.map (CommRingCat.ofHom (GlobalBlowup.res Y h))).base yW) := by
    intro V'
    by_cases hmem : coordPoly fk c W ∈ (V' : PrimeSpectrum (Polynomial Γ(Y, W.1))).asIdeal
    · rw [VectorBundle.sectionGysinTerm_of_mem _ _ _ hmem,
        VectorBundle.sectionGysinTerm_of_mem _ _ _ ((hmemW V').2 hmem)]
      exact rfl
    · have hq : (openInclusion (polyOpens W) (polyIso W)).base V' =
          (openInclusion (polyOpens U) (polyIso U)).base
            ((Spec.map (CommRingCat.ofHom
              (Polynomial.mapRingHom (GlobalBlowup.res Y h)))).base V') := by
        rw [openInclusion_polyIso, openInclusion_polyIso, hψpt]
      exact (sectionGysinTerm_chart_eq fk c dimE _ V' (fun hc ↦ hmem ((hmemW V').1 hc)) hmem hq
        _ yW hchart.symm).symm
  rw [VectorBundle.sectionGysin_apply_finsetSum, VectorBundle.sectionGysin_apply_finsetSum]
  have hzero : ∀ V ∈ (AlgebraicCycle.finite_support
        (AlgebraicCycle.pullbackOpen (polyChartMap U) z)).toFinset,
      V ∉ ((AlgebraicCycle.finite_support
        (AlgebraicCycle.pullbackOpen (polyChartMap U) z)).toFinset.filter
        fun V ↦ (polyChartMap U).base V ∈ polyOpens W) →
      (AlgebraicCycle.pullbackOpen (polyChartMap U) z :
          ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))) → ℚ) V *
        (VectorBundle.sectionGysinTerm (chartConst fk c U) (chartDim fk U) V :
          ↥(Spec (CommRingCat.of Γ(Y, U.1))) → ℚ)
          ((Spec.map (CommRingCat.ofHom (GlobalBlowup.res Y h))).base yW) = 0 := by
    intro V hV hVnot
    have hnot : (polyChartMap U).base V ∉ polyOpens W := by
      intro hcon
      exact hVnot (Finset.mem_filter.2 ⟨hV, hcon⟩)
    have hy2 : (chartInclusion U).base
        ((Spec.map (CommRingCat.ofHom (GlobalBlowup.res Y h))).base yW) ∈ W.1 := by
      rw [hchart]
      exact mem_chartInclusion_base W yW
    rw [sectionGysinTerm_eq_zero_of_notMem fk c U W V _ hy2 hnot, mul_zero]
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hzero]
  refine (Finset.sum_bij (fun V' _ ↦ (Spec.map (CommRingCat.ofHom
    (Polynomial.mapRingHom (GlobalBlowup.res Y h)))).base V') ?_ ?_ ?_ ?_).symm
  · intro V' hV'
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hV'
    refine Finset.mem_filter.2 ⟨?_, ?_⟩
    · rw [Set.Finite.mem_toFinset, Function.mem_support, ← hz V']
      exact hV'
    · rw [hψpt]
      exact ⟨V', rfl⟩
  · intro V₁ h₁ V₂ h₂ hV
    refine (polyChartMap W).isOpenEmbedding.injective ?_
    rw [← hψpt, ← hψpt, hV]
  · intro V hV
    obtain ⟨V', hV'⟩ : (polyChartMap U).base V ∈ polyOpens W := (Finset.mem_filter.1 hV).2
    refine ⟨V', ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset, Function.mem_support, hz V']
      have hVeq : (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (GlobalBlowup.res Y h)))).base V' = V := by
        refine (polyChartMap U).isOpenEmbedding.injective ?_
        rw [hψpt]
        exact hV'
      rw [hVeq]
      have := (Finset.mem_filter.1 hV).1
      rw [Set.Finite.mem_toFinset, Function.mem_support] at this
      exact this
    · refine (polyChartMap U).isOpenEmbedding.injective ?_
      rw [hψpt]
      exact hV'
  · intro V' hV'
    rw [hz V', hT V']

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian Y]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)]
  [NoetherianSpace (lineSpace Y)] [LocallyOfFiniteType fk] in
/-- The affine chart of `X` over `U` covers `U`. -/
theorem opensRange_chartInclusion {X : Scheme.{u}} (U : X.affineOpens) :
    (chartInclusion U).opensRange = U.1 := by
  have h : ((isAffineOpen X U).isoSpec.inv ≫ U.1.ι).opensRange = U.1 := by
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    exact U.1.opensRange_ι
  exact h

include dimE in
/-- **Compatibility of the chart Gysin maps.**  Two affine charts of the base compute the same
Gysin value at points with the same image in `Y`. -/
theorem sectionGysin_apply_congr {U U' : Y.affineOpens}
    (z : AlgebraicCycle (lineSpace Y) ℚ)
    (y : ↥(Spec (CommRingCat.of Γ(Y, U.1)))) (y' : ↥(Spec (CommRingCat.of Γ(Y, U'.1))))
    (hyy' : (chartInclusion U').base y' = (chartInclusion U).base y) :
    (VectorBundle.sectionGysin (chartConst fk c U) (chartDim fk U)
        (AlgebraicCycle.pullbackOpen (polyChartMap U) z) :
        ↥(Spec (CommRingCat.of Γ(Y, U.1))) → ℚ) y =
      (VectorBundle.sectionGysin (chartConst fk c U') (chartDim fk U')
        (AlgebraicCycle.pullbackOpen (polyChartMap U') z) :
        ↥(Spec (CommRingCat.of Γ(Y, U'.1))) → ℚ) y' := by
  obtain ⟨W, hWaff, hxW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
    Y.isBasis_affineOpens (show (chartInclusion U).base y ∈ U.1 ⊓ U'.1 from
      ⟨mem_chartInclusion_base U y, hyy' ▸ mem_chartInclusion_base U' y'⟩)
  have hWU : (⟨W, hWaff⟩ : Y.affineOpens) ≤ U := (le_trans hWle inf_le_left : W ≤ U.1)
  have hWU' : (⟨W, hWaff⟩ : Y.affineOpens) ≤ U' := (le_trans hWle inf_le_right : W ≤ U'.1)
  obtain ⟨yW, hyW⟩ : (chartInclusion U).base y ∈
      (chartInclusion (⟨W, hWaff⟩ : Y.affineOpens)).opensRange := by
    rw [opensRange_chartInclusion]
    exact hxW
  have hres : (Spec.map (CommRingCat.ofHom (GlobalBlowup.res Y hWU))).base yW = y := by
    refine (chartInclusion U).isOpenEmbedding.injective ?_
    have := congrArg (fun m : Spec (CommRingCat.of Γ(Y, W)) ⟶ Y ↦ m.base yW)
      (chartInclusion_comp hWU)
    exact this.trans hyW
  have hres' : (Spec.map (CommRingCat.ofHom (GlobalBlowup.res Y hWU'))).base yW = y' := by
    refine (chartInclusion U').isOpenEmbedding.injective ?_
    have := congrArg (fun m : Spec (CommRingCat.of Γ(Y, W)) ⟶ Y ↦ m.base yW)
      (chartInclusion_comp hWU')
    rw [hyy']
    exact this.trans hyW
  rw [← hres, ← hres', sectionGysin_apply_le fk c dimE hWU z yW,
    sectionGysin_apply_le fk c dimE hWU' z yW]

/-- The Gysin image of a cycle on the total space, computed on an affine chart of the base. -/
noncomputable def localGysin (U : Y.affineOpens) (z : AlgebraicCycle (lineSpace Y) ℚ) :
    AlgebraicCycle U.1.toScheme ℚ :=
  AlgebraicCycle.pullbackOpen (isAffineOpen Y U).isoSpec.hom
    (VectorBundle.sectionGysin (chartConst fk c U) (chartDim fk U)
      (AlgebraicCycle.pullbackOpen (polyChartMap U) z))

include dimE in
/-- The chart-wise Gysin images form a compatible family. -/
theorem localGysin_compatible (z : AlgebraicCycle (lineSpace Y) ℚ) :
    CycleGluing.Compatible (U := fun U : Y.affineOpens ↦ U.1)
      fun U ↦ localGysin fk c U z := by
  intro U U' x x' hxx'
  have hbase : ∀ (V : Y.affineOpens) (v : V.1.toScheme),
      (chartInclusion V).base ((isAffineOpen Y V).isoSpec.hom.base v) = V.1.ι.base v := by
    intro V v
    change V.1.ι.base ((isAffineOpen Y V).isoSpec.inv.base
      ((isAffineOpen Y V).isoSpec.hom.base v)) = _
    rw [isoInv_isoHom_base]
  exact sectionGysin_apply_congr fk c dimE z _ _
    (by rw [hbase U' x', hbase U x, hxx'])

include dimE in
/-- **The global Gysin map of the constant section `t = c`** at the level of cycles. -/
noncomputable def globalGysin (z : AlgebraicCycle (lineSpace Y) ℚ) : AlgebraicCycle Y ℚ :=
  CycleGluing.glue (U := fun U : Y.affineOpens ↦ U.1) (iSup_affineOpens_eq_top Y)
    (fun U ↦ localGysin fk c U z) (localGysin_compatible fk c dimE z)

include dimE in
/-- The global Gysin map restricts to the chart-wise Gysin images. -/
theorem pullbackOpen_globalGysin (z : AlgebraicCycle (lineSpace Y) ℚ) (U : Y.affineOpens) :
    AlgebraicCycle.pullbackOpen U.1.ι (globalGysin fk c dimE z) = localGysin fk c U z :=
  CycleGluing.pullbackOpen_glue _ _ _ U

include dimE in
/-- The value of the global Gysin map at a point, computed on any affine chart containing it. -/
theorem globalGysin_apply (z : AlgebraicCycle (lineSpace Y) ℚ) (U : Y.affineOpens)
    (y : ↥(Spec (CommRingCat.of Γ(Y, U.1)))) :
    (globalGysin fk c dimE z : Y → ℚ) ((chartInclusion U).base y) =
      (VectorBundle.sectionGysin (chartConst fk c U) (chartDim fk U)
        (AlgebraicCycle.pullbackOpen (polyChartMap U) z) :
        ↥(Spec (CommRingCat.of Γ(Y, U.1))) → ℚ) y := by
  have hx : (chartInclusion U).base y ∈ U.1 := mem_chartInclusion_base U y
  have key : (globalGysin fk c dimE z : Y → ℚ) ((chartInclusion U).base y) =
      (localGysin fk c U z : U.1.toScheme → ℚ) ⟨(chartInclusion U).base y, hx⟩ :=
    congrArg (fun t : AlgebraicCycle U.1.toScheme ℚ ↦
      (t : U.1.toScheme → ℚ) ⟨(chartInclusion U).base y, hx⟩)
      (pullbackOpen_globalGysin fk c dimE z U)
  have key2 : (localGysin fk c U z : U.1.toScheme → ℚ) ⟨(chartInclusion U).base y, hx⟩ =
      (VectorBundle.sectionGysin (chartConst fk c U) (chartDim fk U)
          (AlgebraicCycle.pullbackOpen (polyChartMap U) z) :
          ↥(Spec (CommRingCat.of Γ(Y, U.1))) → ℚ)
        ((isAffineOpen Y U).isoSpec.hom.base
          (⟨(chartInclusion U).base y, hx⟩ : U.1.toScheme)) := rfl
  have hpteq : (isAffineOpen Y U).isoSpec.hom.base
      (⟨(chartInclusion U).base y, hx⟩ : U.1.toScheme) = y := by
    refine (chartInclusion U).isOpenEmbedding.injective ?_
    exact congrArg (fun w : U.1.toScheme ↦ U.1.ι.base w)
      (isoInv_isoHom_base (isAffineOpen Y U).isoSpec ⟨(chartInclusion U).base y, hx⟩)
  rw [key, key2, hpteq]

include dimE in
/-- **The global Gysin map of the constant section inverts the flat pullback along the trivial
line bundle**, at the level of cycles. -/
theorem globalGysin_pullbackBundle (w : AlgebraicCycle Y ℚ) :
    globalGysin fk c dimE
        (BundlePullbackGlobal.pullbackBundle (trivialData Y PUnit.{u + 1}) w) = w := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  obtain ⟨U, hU⟩ := exists_affineOpen_mem y
  obtain ⟨yU, hyU⟩ : y ∈ (chartInclusion U).opensRange := by
    rw [opensRange_chartInclusion]
    exact hU
  rw [← hyU, globalGysin_apply]
  have h1 : AlgebraicCycle.pullbackOpen (polyChartMap U)
      (BundlePullbackGlobal.pullbackBundle (trivialData Y PUnit.{u + 1}) w) =
      AlgebraicCycle.pullbackBundle (VectorBundle.polyTrivialization Γ(Y, U.1))
        (AlgebraicCycle.pullbackOpen (chartInclusion U) w) := by
    have h0 : AlgebraicCycle.pullbackOpen (polyChartMap U)
        (BundlePullbackGlobal.pullbackBundle (trivialData Y PUnit.{u + 1}) w) =
        AlgebraicCycle.pullbackOpen (VectorBundle.mvSectionSpecMap Γ(Y, U.1))
          (AlgebraicCycle.pullbackOpen ((trivialData Y PUnit.{u + 1}).chartι U)
            (BundlePullbackGlobal.pullbackBundle (trivialData Y PUnit.{u + 1}) w)) := by
      apply Function.locallyFinsuppWithin.ext
      intro a
      rfl
    rw [h0, BundlePullbackGlobal.pullbackOpen_chartι_pullbackBundle,
      VectorBundle.pullbackOpen_mvSectionSpecMap_pullbackBundle]
    rfl
  rw [h1, VectorBundle.sectionGysin_pullbackBundle]
  rfl

include dimE in
/-- The global Gysin map is additive. -/
theorem globalGysin_add (z z' : AlgebraicCycle (lineSpace Y) ℚ) :
    globalGysin fk c dimE (z + z') = globalGysin fk c dimE z + globalGysin fk c dimE z' := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  obtain ⟨U, hU⟩ := exists_affineOpen_mem y
  obtain ⟨yU, hyU⟩ : y ∈ (chartInclusion U).opensRange := by
    rw [opensRange_chartInclusion]
    exact hU
  rw [← hyU, globalGysin_apply, AlgebraicCycle.pullbackOpen_add, map_add]
  rw [show ((globalGysin fk c dimE z + globalGysin fk c dimE z' : AlgebraicCycle Y ℚ) :
      Y → ℚ) ((chartInclusion U).base yU) =
      (globalGysin fk c dimE z : Y → ℚ) ((chartInclusion U).base yU) +
        (globalGysin fk c dimE z' : Y → ℚ) ((chartInclusion U).base yU) by simp,
    globalGysin_apply, globalGysin_apply]
  simp

include dimE in
/-- The global Gysin map is homogeneous. -/
theorem globalGysin_smul (q : ℚ) (z : AlgebraicCycle (lineSpace Y) ℚ) :
    globalGysin fk c dimE (q • z) = q • globalGysin fk c dimE z := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  obtain ⟨U, hU⟩ := exists_affineOpen_mem y
  obtain ⟨yU, hyU⟩ : y ∈ (chartInclusion U).opensRange := by
    rw [opensRange_chartInclusion]
    exact hU
  have hpb : AlgebraicCycle.pullbackOpen (polyChartMap U) (q • z) =
      q • AlgebraicCycle.pullbackOpen (polyChartMap U) z :=
    (AlgebraicCycle.pullbackOpenLinear (polyChartMap U)).map_smul q z
  rw [← hyU, globalGysin_apply, hpb, map_smul]
  rw [show ((q • globalGysin fk c dimE z : AlgebraicCycle Y ℚ) : Y → ℚ)
      ((chartInclusion U).base yU) =
      q * (globalGysin fk c dimE z : Y → ℚ) ((chartInclusion U).base yU) by
        rw [Function.locallyFinsuppWithin.coe_rational_smul]; rfl,
    globalGysin_apply]
  rw [Function.locallyFinsuppWithin.coe_rational_smul]
  rfl

include dimE in
/-- **The global Gysin map of the constant section `t = c`**, as a linear map on cycles. -/
noncomputable def globalGysinLinear :
    AlgebraicCycle (lineSpace Y) ℚ →ₗ[ℚ] AlgebraicCycle Y ℚ where
  toFun := globalGysin fk c dimE
  map_add' := globalGysin_add fk c dimE
  map_smul' q z := globalGysin_smul fk c dimE q z

include dimE in
/-- **Injectivity of the flat pullback along the trivial line bundle, modulo the Gysin image of
a principal divisor.**  The hypothesis `hgysin` says that the global Gysin map of the constant
section `t = c` carries principal divisors of the total space into the span of principal divisors
of the base; it is the only thing missing for the unconditional multi-chart theorem, and it holds
for a constant `c` in general position (see the module docstring). -/
theorem pullbackBundle_injective_of_gysin
    (hgysin : ∀ g : RationalFunctionGenerator (lineSpace Y),
      globalGysin fk c dimE (g.divisor dimE) ∈
        totalRationalRelations Y (FiniteTypeDimension.dimensionFunction fk))
    (w : AlgebraicCycle Y ℚ)
    (hw : BundlePullbackGlobal.pullbackBundle (trivialData Y PUnit.{u + 1}) w ∈
      totalRationalRelations (lineSpace Y) dimE) :
    w ∈ totalRationalRelations Y (FiniteTypeDimension.dimensionFunction fk) := by
  have hmap : Submodule.map (globalGysinLinear fk c dimE)
      (totalRationalRelations (lineSpace Y) dimE) ≤
      totalRationalRelations Y (FiniteTypeDimension.dimensionFunction fk) := by
    rw [totalRationalRelations, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact hgysin g
  have hmem := hmap ⟨_, hw, rfl⟩
  rwa [show (globalGysinLinear fk c dimE)
      (BundlePullbackGlobal.pullbackBundle (trivialData Y PUnit.{u + 1}) w) = w from
    globalGysin_pullbackBundle fk c dimE w] at hmem

end CoordDivisor



/-! ## Discharging the standing hypotheses in the finite-type case -/

section FiniteType

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- A scheme locally of finite type over a field is locally Noetherian. -/
theorem isLocallyNoetherian_base (fk : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fk] :
    _root_.AlgebraicGeometry.IsLocallyNoetherian Y :=
  BundlePullbackGlobal.isLocallyNoetherian_of_locallyOfFiniteType fk
    (trivialData Y PUnit.{u + 1})

/-- The total space of the trivial line bundle over a scheme locally of finite type over a field
is locally Noetherian. -/
theorem isLocallyNoetherian_lineSpace (fk : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType fk] :
    _root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y) :=
  BundlePullbackGlobal.isLocallyNoetherian_of_locallyOfFiniteType
    ((trivialData Y PUnit.{u + 1}).proj ≫ fk) (trivialData (lineSpace Y) PUnit.{u + 1})

/-- The total space of the trivial line bundle over a compact scheme is compact. -/
theorem compactSpace_lineSpace [CompactSpace Y] : CompactSpace (lineSpace Y) :=
  QuasiCompact.compactSpace_of_compactSpace ((trivialData Y PUnit.{u + 1}).proj)

/-- The total space of the trivial line bundle over a compact scheme locally of finite type over
a field is a Noetherian space. -/
theorem noetherianSpace_lineSpace (fk : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fk]
    [CompactSpace Y] : NoetherianSpace (lineSpace Y) :=
  have _ := isLocallyNoetherian_lineSpace fk
  have _ := compactSpace_lineSpace (Y := Y)
  inferInstance

end FiniteType

end LineBundleInjective

end GromovWitten.AlgebraicGeometry.IntersectionTheory
