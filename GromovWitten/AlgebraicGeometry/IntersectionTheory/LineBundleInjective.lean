/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VectorBundleTrivial
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyGlobal
import GromovWitten.AlgebraicGeometry.IntersectionTheory.GeneratorInvarianceAffine
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleSectionGysinExplicit

/-!
# Injectivity of the flat pullback along a globally trivial vector bundle

Round 15 proved that the flat pullback `π^* : Z_*(Spec R) → Z_*(Spec (MvPolynomial ι R))`
is injective modulo rational equivalence (`VectorBundle.bundleInjective_of_universal`).  This
file starts the globalisation of that statement to a scheme `Y` locally of finite type over an
infinite field `k`, for a vector bundle `𝓔 : BundleData Y ι` of finite rank.

The part which is complete here is the **single chart** case: if one trivialising chart of `𝓔`
covers the whole of `Y` — in particular if `Y` is affine and `𝓔` is the trivial bundle
`trivialData Y ι` — then the global flat pullback `BundlePullbackGlobal.pullbackBundle 𝓔` is
injective modulo the canonical span of principal divisors.  The proof transports the affine
statement along the two isomorphisms `Spec Γ(Y, ⊤) ≅ Y` and
`Spec (MvPolynomial ι Γ(Y, ⊤)) ≅ 𝓔.totalSpace` given by the chart.

The genuinely global case (several charts) additionally needs a chart-independent description of
the generators produced by the affine section Gysin map.  The infrastructure for that is the
second half of this file: the *normal form* `divisor_pointGenerator` of a principal divisor —
every generator has the same divisor as the canonical generator attached to the pair consisting
of the generic point of its subspace and the class of its rational function in the residue field
of that point — and its consequence `divisor_chartGenerator_eq`, which says that a generator
transported to `X` from an affine chart has a divisor depending only on that pair, hence not on
the chart it was built on.

## Main declarations

* `LineBundleInjective.isIso_chartε`, `LineBundleInjective.isIso_chartι` — a trivialising chart
  whose affine open is `⊤` identifies `Spec Γ(Y, ⊤)` with `Y` and `Spec (MvPolynomial ι Γ(Y, ⊤))`
  with the total space;
* `LineBundleInjective.pullbackBundle_injective_chart` — injectivity of the flat pullback for a
  bundle with such a chart;
* `LineBundleInjective.pullbackBundle_injective_affine` — the same for the trivial bundle over an
  affine base;
* `LineBundleInjective.pointSubscheme x` — an integral closed subscheme of a Noetherian scheme
  whose generic point is a prescribed point `x` (`genericPointImage_pointSubscheme`);
* `LineBundleInjective.pointGenerator x u` — the generator attached to a point `x` and a unit `u`
  of its residue field, with `residueFunction_pointGenerator` and the normal form
  `LineBundleInjective.divisor_pointGenerator`;
* `LineBundleInjective.chartGenerator U g` — the transport to `X` of a generator on the affine
  chart `Spec Γ(X, U)`, with `genericPointImage_chartGenerator`,
  `residueFunction_chartGenerator`, the normal form `divisor_chartGenerator` and the chart
  independence `divisor_chartGenerator_eq`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)

namespace LineBundleInjective

section Chart

variable {Y : Scheme.{u}} {ι : Type u} (𝓔 : BundleData Y ι)

/-- A trivialising chart of a bundle whose affine open is the whole space identifies
`Spec Γ(Y, ⊤)` with `Y`. -/
theorem isIso_chartε (j : 𝓔.J) (hj : (𝓔.chart j).1 = ⊤) :
    IsIso (BundlePullbackGlobal.chartε 𝓔 j) := by
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
  refine TopologicalSpace.Opens.ext ?_
  change Set.range (BundlePullbackGlobal.chartε 𝓔 j).base = _
  rw [BundlePullbackGlobal.range_chartε, hj]

/-- A trivialising chart of a bundle whose affine open is the whole space identifies
`Spec (MvPolynomial ι Γ(Y, ⊤))` with the total space of the bundle. -/
theorem isIso_chartι (j : 𝓔.J) (hj : (𝓔.chart j).1 = ⊤) : IsIso (𝓔.chartι j) := by
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
  rw [BundleData.opensRange_chartι, hj]
  rfl

end Chart

section Affine

variable {k : Type u} [Field k] [Infinite k] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {ι : Type u} [Finite ι] (𝓔 : BundleData Y ι)

/-- **Injectivity of the global flat pullback for a bundle with a single trivialising chart.**
If one chart of `𝓔` is defined over the whole of `Y`, the affine injectivity theorem of round 15
transports to `Y` along the two isomorphisms of `isIso_chartε` and `isIso_chartι`.  No
trivialisation data beyond the chart is used. -/
theorem pullbackBundle_injective_chart (j : 𝓔.J) (hj : (𝓔.chart j).1 = ⊤)
    (w : AlgebraicCycle Y ℚ)
    (hw : BundlePullbackGlobal.pullbackBundle 𝓔 w ∈
      totalRationalRelations 𝓔.totalSpace (FiniteTypeDimension.dimensionFunction (𝓔.proj ≫ f))) :
    w ∈ totalRationalRelations Y (FiniteTypeDimension.dimensionFunction f) := by
  classical
  have hε := isIso_chartε 𝓔 j hj
  have hι := isIso_chartι 𝓔 j hj
  set ε : Spec (CommRingCat.of Γ(Y, (𝓔.chart j).1)) ≅ Y :=
    asIso (BundlePullbackGlobal.chartε 𝓔 j) with hεdef
  set δ : Spec (CommRingCat.of (MvPolynomial ι Γ(Y, (𝓔.chart j).1))) ≅ 𝓔.totalSpace :=
    asIso (𝓔.chartι j) with hδdef
  set dimA := FiniteTypeDimension.dimensionFunction (BundlePullbackGlobal.chartε 𝓔 j ≫ f)
    with hdimA
  set dimP := FiniteTypeDimension.dimensionFunction (𝓔.chartι j ≫ 𝓔.proj ≫ f) with hdimP
  have h1 : AlgebraicCycle.pullbackOpen (𝓔.chartι j)
      (BundlePullbackGlobal.pullbackBundle 𝓔 w) ∈
        totalRationalRelations _ dimP := by
    rw [← totalRationalRelations_map_pullbackOpenLinear δ dimP
      (FiniteTypeDimension.dimensionFunction (𝓔.proj ≫ f))]
    exact ⟨_, hw, rfl⟩
  rw [BundlePullbackGlobal.pullbackOpen_chartι_pullbackBundle] at h1
  by_cases hnt : Nontrivial Γ(Y, (𝓔.chart j).1)
  · have _ : IsNoetherianRing Γ(Y, (𝓔.chart j).1) :=
      FiniteTypeDimension.isNoetherianRing_sections f _ (𝓔.chart j).2
    have _ : Algebra k Γ(Y, (𝓔.chart j).1) := FiniteTypeDimension.sectionsAlgebra f _
    have hunit : VectorBundle.UnitDifferences Γ(Y, (𝓔.chart j).1) :=
      VectorBundle.unitDifferences_of_field k _
    have hdimU : VectorBundle.HasUniversalDimensionFormula Γ(Y, (𝓔.chart j).1) :=
      FiniteTypeDimension.hasUniversalDimensionFormula_sections f _ (𝓔.chart j).2
    have h2 := VectorBundle.bundleInjective_of_universal
      (AlgEquiv.refl (R := Γ(Y, (𝓔.chart j).1))
        (A₁ := MvPolynomial ι Γ(Y, (𝓔.chart j).1))) dimA dimP hunit hdimU _ h1
    rw [← totalRationalRelations_map_pullbackOpenLinear ε dimA
      (FiniteTypeDimension.dimensionFunction f)] at h2
    obtain ⟨ρ, hρ, hρw⟩ := h2
    have hwρ : w = ρ := by
      have h3 := pullbackOpen_hom_inv ε.symm w
      have h4 := pullbackOpen_hom_inv ε.symm ρ
      simp only [Iso.symm_hom, Iso.symm_inv] at h3 h4
      rw [← h3, ← h4]
      exact congrArg _ hρw.symm
    rw [hwρ]
    exact hρ
  · rw [not_nontrivial_iff_subsingleton] at hnt
    have _ : IsEmpty ↥(Spec (CommRingCat.of Γ(Y, (𝓔.chart j).1))) :=
      inferInstanceAs (IsEmpty (PrimeSpectrum Γ(Y, (𝓔.chart j).1)))
    have hYempty : IsEmpty Y := Function.isEmpty ε.inv.base
    have hw0 : w = 0 := by
      apply Function.locallyFinsuppWithin.coe_injective
      funext x
      exact hYempty.elim x
    rw [hw0]
    exact Submodule.zero_mem _

/-- **Injectivity of the global flat pullback for the trivial bundle over an affine base.** -/
theorem pullbackBundle_injective_affine [IsAffine Y] (w : AlgebraicCycle Y ℚ)
    (hw : BundlePullbackGlobal.pullbackBundle (trivialData Y ι) w ∈
      totalRationalRelations (trivialData Y ι).totalSpace
        (FiniteTypeDimension.dimensionFunction ((trivialData Y ι).proj ≫ f))) :
    w ∈ totalRationalRelations Y (FiniteTypeDimension.dimensionFunction f) :=
  pullbackBundle_injective_chart f (trivialData Y ι)
    (⟨⊤, isAffineOpen_top Y⟩ : (trivialData Y ι).J) rfl w hw

end Affine

/-! ## The normal form of a principal-divisor generator

By Task T0's `RationalFunctionGenerator.divisor_eq_of_residueFunction_eq` the divisor of a
generator only depends on the pair `(ξ, u)` consisting of the image `ξ` in `X` of the generic
point of its subspace and the class `u` of its rational function in the residue field `κ(ξ)`.
This section realises *every* such pair by a canonical generator `pointGenerator ξ u`, so that
generators built on different affine charts can be compared by comparing the corresponding
pairs.  The integral closed subscheme with prescribed generic point is the closure in `X` of the
reduced closed subscheme `V(𝔭)` of an affine chart around `ξ`. -/

section PointGenerator

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The quotient of a Noetherian ring by an ideal is Noetherian, in the shape instance search
needs for the coordinate ring of a closed subscheme of `Spec A`. -/
instance isNoetherianRing_quotientOf (p : Ideal A) :
    IsNoetherianRing ↥(CommRingCat.of (A ⧸ p)) :=
  inferInstanceAs (IsNoetherianRing (A ⧸ p))

/-- The quotient of a ring by a prime ideal is a domain, in the shape instance search needs. -/
instance isDomain_quotientOf (p : Ideal A) [p.IsPrime] :
    IsDomain ↥(CommRingCat.of (A ⧸ p)) :=
  inferInstanceAs (IsDomain (A ⧸ p))

/-- The integral closed subscheme `V(p) ⊆ Spec A` cut out by a prime ideal of a Noetherian
ring. -/
noncomputable def specSubscheme (p : Ideal A) [p.IsPrime] :
    IntegralClosedSubscheme (Spec (CommRingCat.of A)) where
  scheme := Spec (CommRingCat.of (A ⧸ p))
  inclusion := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p))
  isClosedImmersion :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The generic point of the subvariety `V(p)` of `Spec A` is the point `p`. -/
theorem genericPointImage_specSubscheme (p : Ideal A) [p.IsPrime] :
    (((specSubscheme p).genericPointImage : ↥(Spec (CommRingCat.of A))) :
      PrimeSpectrum A).asIdeal = p := by
  have h : (((specSubscheme p).genericPointImage : ↥(Spec (CommRingCat.of A))) :
      PrimeSpectrum A).asIdeal =
      Ideal.comap (Ideal.Quotient.mk p)
        ((genericPoint (Spec (CommRingCat.of (A ⧸ p))) : PrimeSpectrum (A ⧸ p)).asIdeal) := rfl
  rw [h, genericPoint_asIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

variable {X : Scheme.{u}}

/-- The inverse of an isomorphism of schemes undoes it on points. -/
theorem isoInv_isoHom_base {W Z : Scheme.{u}} (e : W ≅ Z) (w : W) :
    e.inv.base (e.hom.base w) = w := by
  have h : (e.hom ≫ e.inv).base w = (𝟙 W : W ⟶ W).base w := by rw [e.hom_inv_id]
  exact h

/-- The generic point of a subscheme transported along an isomorphism of ambient schemes. -/
theorem genericPointImage_transportIso {W W' : Scheme.{u}} (e : W ≅ W')
    (Z : IntegralClosedSubscheme W) :
    (Z.transportIso e).genericPointImage = e.hom.base Z.genericPointImage := rfl

/-- The generic point of the closure in `X` of an integral closed subscheme of an open
subscheme. -/
theorem genericPointImage_closureIn [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
    (U : X.Opens) (Z : IntegralClosedSubscheme U.toScheme)
    [_root_.AlgebraicGeometry.QuasiCompact (Z.inclusion ≫ U.ι)] :
    (Z.closureIn U).genericPointImage = U.ι.base Z.genericPointImage :=
  RationalFunctionGenerator.genericPointImage_closureIn U ⟨Z, 1⟩

/-- Every point of a scheme lies in an affine open. -/
theorem exists_affineOpen_mem (x : X) : ∃ U : X.affineOpens, x ∈ U.1 := by
  have h : x ∈ (⊤ : X.Opens) := trivial
  rw [← iSup_affineOpens_eq_top X] at h
  simpa using h

/-- A chosen affine open containing a given point. -/
noncomputable def pointChart (x : X) : X.affineOpens := (exists_affineOpen_mem x).choose

/-- The chosen affine chart around a point contains it. -/
theorem mem_pointChart (x : X) : x ∈ (pointChart x).1 := (exists_affineOpen_mem x).choose_spec

variable [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]

/-- The sections over an affine chart of a locally Noetherian scheme form a Noetherian ring. -/
instance isNoetherianRing_pointChart (x : X) : IsNoetherianRing Γ(X, (pointChart x).1) :=
  IsLocallyNoetherian.component_noetherian (pointChart x)

/-- The prime ideal of `Γ(X, U)` corresponding to a point of its affine chart. -/
noncomputable def pointPrime (x : X) : Ideal Γ(X, (pointChart x).1) :=
  ((((isAffineOpen X (pointChart x)).isoSpec.hom.base
    (⟨x, mem_pointChart x⟩ : (pointChart x).1.toScheme) :
      ↥(Spec (CommRingCat.of Γ(X, (pointChart x).1)))) :
      PrimeSpectrum Γ(X, (pointChart x).1))).asIdeal

/-- The ideal `pointPrime x` is prime. -/
instance isPrime_pointPrime (x : X) : (pointPrime x).IsPrime :=
  PrimeSpectrum.isPrime _

/-- **An integral closed subscheme with prescribed generic point**: the closure in `X` of the
reduced subvariety `V(𝔭)` of the chosen affine chart around `x`. -/
noncomputable def pointSubscheme (x : X) : IntegralClosedSubscheme X :=
  ((specSubscheme (pointPrime x)).transportIso
    (isAffineOpen X (pointChart x)).isoSpec.symm).closureIn (pointChart x).1

/-- The generic point of `pointSubscheme x` is `x`. -/
theorem genericPointImage_pointSubscheme (x : X) : (pointSubscheme x).genericPointImage = x := by
  have h0 : ((specSubscheme (pointPrime x)).genericPointImage :
      ↥(Spec (CommRingCat.of Γ(X, (pointChart x).1)))) =
      (isAffineOpen X (pointChart x)).isoSpec.hom.base
        (⟨x, mem_pointChart x⟩ : (pointChart x).1.toScheme) :=
    PrimeSpectrum.ext (genericPointImage_specSubscheme (pointPrime x))
  have h1 : ((specSubscheme (pointPrime x)).transportIso
      (isAffineOpen X (pointChart x)).isoSpec.symm).genericPointImage =
      (⟨x, mem_pointChart x⟩ : (pointChart x).1.toScheme) := by
    rw [genericPointImage_transportIso, h0, Iso.symm_hom]
    exact isoInv_isoHom_base _ _
  rw [pointSubscheme, genericPointImage_closureIn, h1]
  rfl

/-- The canonical isomorphism between the function field of `pointSubscheme x` and the residue
field of `x`. -/
noncomputable def pointFieldEquiv (x : X) :
    (pointSubscheme x).scheme.functionField ≃+* X.residueField x :=
  (pointSubscheme x).functionFieldEquivResidueField.trans
    (X.residueFieldCongr (genericPointImage_pointSubscheme x)).commRingCatIsoToRingEquiv

/-- **The canonical generator attached to a point and a unit of its residue field.** -/
noncomputable def pointGenerator (x : X) (u : (X.residueField x)ˣ) :
    RationalFunctionGenerator X where
  subspace := pointSubscheme x
  function := Units.map (pointFieldEquiv x).symm.toMonoidHom u

/-- The generic point of the subspace of `pointGenerator x u` is `x`. -/
theorem genericPointImage_pointGenerator (x : X) (u : (X.residueField x)ˣ) :
    (pointGenerator x u).subspace.genericPointImage = x :=
  genericPointImage_pointSubscheme x

/-- The residue function of `pointGenerator x u` is `u`, transported along the identification of
the generic point of `pointSubscheme x` with `x`. -/
theorem residueFunction_pointGenerator (x : X) (u : (X.residueField x)ˣ) :
    Units.map (X.residueFieldCongr
        (genericPointImage_pointGenerator x u)).hom.hom.toMonoidHom
      (pointGenerator x u).residueFunction = u := by
  refine Units.ext ?_
  rw [Units.coe_map, RationalFunctionGenerator.residueFunction_val]
  exact (pointFieldEquiv x).apply_symm_apply (u : X.residueField x)

/-- **Normal form of a principal divisor.**  Every generator has the same divisor as the
canonical generator attached to the generic point of its subspace and to the class of its
rational function in the residue field of that point.  Together with
`residueFunction_pointGenerator` this reduces the comparison of two generators to the comparison
of the pairs `(generic point, residue class of the function)`. -/
theorem divisor_pointGenerator (dim : DimensionFunction X) (g : RationalFunctionGenerator X) :
    (pointGenerator g.subspace.genericPointImage g.residueFunction).divisor dim =
      g.divisor dim :=
  RationalFunctionGenerator.divisor_eq_of_residueFunction_eq dim _ g
    (genericPointImage_pointGenerator _ _) (residueFunction_pointGenerator _ _)

end PointGenerator

/-! ## Generators transported from an affine chart

The generators produced by the affine section Gysin map live on a chart `Spec Γ(X, U)`; the
global relation is assembled from their transports to `X`.  This section records the two pieces
of data which, by `divisor_pointGenerator`, determine the divisor of such a transport: its
generic point and its residue function. -/

section ChartGenerator

variable {X : Scheme.{u}} [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]

/-- A generator transported along an isomorphism of the ambient scheme is its image under the
closed immersion given by that isomorphism. -/
theorem transportIso_eq_closedImage {W W' : Scheme.{u}} (e : W ≅ W')
    (g : RationalFunctionGenerator W) :
    g.transportIso e = g.closedImage e.hom := rfl

/-- The open immersion of an affine chart of `X` into `X`. -/
noncomputable abbrev chartInclusion (U : X.affineOpens) :
    Spec (CommRingCat.of Γ(X, U.1)) ⟶ X :=
  (isAffineOpen X U).isoSpec.inv ≫ U.1.ι

/-- The transport to `X` of a principal-divisor generator living on an affine chart: first along
the chart isomorphism `Spec Γ(X, U) ≅ U`, then by taking the closure in `X`. -/
noncomputable def chartGenerator (U : X.affineOpens)
    (g : RationalFunctionGenerator (Spec (CommRingCat.of Γ(X, U.1)))) :
    RationalFunctionGenerator X :=
  (g.transportIso (isAffineOpen X U).isoSpec.symm).closureIn U.1

/-- The generic point of a generator transported from an affine chart is the image of the
generic point of the generator. -/
theorem genericPointImage_chartGenerator (U : X.affineOpens)
    (g : RationalFunctionGenerator (Spec (CommRingCat.of Γ(X, U.1)))) :
    (chartGenerator U g).subspace.genericPointImage =
      (chartInclusion U).base g.subspace.genericPointImage := by
  rw [chartGenerator, RationalFunctionGenerator.genericPointImage_closureIn]
  rfl

/-- The residue function of a generator transported from an affine chart, read through the
residue field map of the chart inclusion. -/
theorem residueFunction_chartGenerator (U : X.affineOpens)
    (g : RationalFunctionGenerator (Spec (CommRingCat.of Γ(X, U.1)))) :
    Units.map ((chartInclusion U).residueFieldMap
          g.subspace.genericPointImage).hom.toMonoidHom
        (Units.map (X.residueFieldCongr
            (genericPointImage_chartGenerator U g)).hom.hom.toMonoidHom
          (chartGenerator U g).residueFunction) =
      g.residueFunction := by
  refine Units.ext ?_
  rw [Units.coe_map, Units.coe_map]
  have hcomp : ∀ z : X.residueField ((chartInclusion U).base g.subspace.genericPointImage),
      ((chartInclusion U).residueFieldMap g.subspace.genericPointImage).hom z =
        (((isAffineOpen X U).isoSpec.inv).residueFieldMap
            g.subspace.genericPointImage).hom
          ((U.1.ι.residueFieldMap
            (((isAffineOpen X U).isoSpec.inv).base g.subspace.genericPointImage)).hom z) := by
    intro z
    rw [_root_.AlgebraicGeometry.Scheme.residueFieldMap_comp]
    rfl
  refine (hcomp _).trans (Eq.trans (congrArg (fun t ↦
      (((isAffineOpen X U).isoSpec.inv).residueFieldMap
        g.subspace.genericPointImage).hom t)
    (RationalFunctionGenerator.residueFunction_closureIn U.1
      (g.transportIso (isAffineOpen X U).isoSpec.symm)).symm) ?_)
  exact RationalFunctionGenerator.residueFieldMap_residueFunction_closedImage g
    (isAffineOpen X U).isoSpec.inv

/-- **The chart-independent datum of a generator living on an affine chart**: the class of its
rational function in the residue field of `X` at the image of its generic point. -/
noncomputable def chartResidueUnit (U : X.affineOpens)
    (g : RationalFunctionGenerator (Spec (CommRingCat.of Γ(X, U.1)))) :
    (X.residueField ((chartInclusion U).base g.subspace.genericPointImage))ˣ :=
  Units.map (X.residueFieldCongr
      (genericPointImage_chartGenerator U g)).hom.hom.toMonoidHom
    (chartGenerator U g).residueFunction

/-- `chartResidueUnit` is determined by the affine data: it maps to the residue function of the
generator under the (isomorphic) residue field map of the chart inclusion. -/
theorem residueFieldMap_chartResidueUnit (U : X.affineOpens)
    (g : RationalFunctionGenerator (Spec (CommRingCat.of Γ(X, U.1)))) :
    Units.map ((chartInclusion U).residueFieldMap
        g.subspace.genericPointImage).hom.toMonoidHom (chartResidueUnit U g) =
      g.residueFunction :=
  residueFunction_chartGenerator U g

/-- The divisor of a canonical point generator only depends on the point and on the residue
class, transported along an equality of points. -/
theorem divisor_pointGenerator_congr (dim : DimensionFunction X) {x x' : X} (h : x = x')
    (u : (X.residueField x)ˣ) :
    (pointGenerator x' (Units.map (X.residueFieldCongr h).hom.hom.toMonoidHom u)).divisor dim =
      (pointGenerator x u).divisor dim := by
  subst h
  simp

/-- **Normal form of the divisor of a generator transported from an affine chart**: it is the
divisor of the canonical generator attached to the image of its generic point and to its residue
class there.  In particular it depends on neither the chart nor the generator, only on these two
pieces of data. -/
theorem divisor_chartGenerator (dim : DimensionFunction X) (U : X.affineOpens)
    (g : RationalFunctionGenerator (Spec (CommRingCat.of Γ(X, U.1)))) :
    (chartGenerator U g).divisor dim =
      (pointGenerator ((chartInclusion U).base g.subspace.genericPointImage)
        (chartResidueUnit U g)).divisor dim := by
  rw [chartResidueUnit, divisor_pointGenerator_congr dim
    (genericPointImage_chartGenerator U g) (chartGenerator U g).residueFunction,
    divisor_pointGenerator]

/-- **Chart independence.**  Two generators living on two affine charts have the same divisor on
`X` as soon as the images of their generic points agree and their residue classes at that common
point agree. -/
theorem divisor_chartGenerator_eq (dim : DimensionFunction X) (U U' : X.affineOpens)
    (g : RationalFunctionGenerator (Spec (CommRingCat.of Γ(X, U.1))))
    (g' : RationalFunctionGenerator (Spec (CommRingCat.of Γ(X, U'.1))))
    (hy : (chartInclusion U').base g'.subspace.genericPointImage =
      (chartInclusion U).base g.subspace.genericPointImage)
    (hu : Units.map (X.residueFieldCongr hy).hom.hom.toMonoidHom (chartResidueUnit U' g') =
      chartResidueUnit U g) :
    (chartGenerator U' g').divisor dim = (chartGenerator U g).divisor dim := by
  rw [divisor_chartGenerator dim U' g', divisor_chartGenerator dim U g, ← hu,
    divisor_pointGenerator_congr dim hy (chartResidueUnit U' g')]

end ChartGenerator

end LineBundleInjective

end GromovWitten.AlgebraicGeometry.IntersectionTheory
