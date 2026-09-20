/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleInjectiveGlobal
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyInjectiveGlobal

/-!
# The Gysin image of a principal divisor of the trivial line bundle

`IntersectionTheory/LineBundleInjectiveGlobal.lean` built the global Gysin map
`LineBundleInjective.globalGysin fk c dimE` of the constant section `t = c` of the trivial line
bundle `E = Y × 𝔸¹` and reduced the multi-chart injectivity theorem to the single hypothesis
`hgysin` of `pullbackBundle_injective_of_gysin`: that the Gysin image of a principal divisor of
`E` lies in `totalRationalRelations Y`.  This file supplies the ingredients for that hypothesis
which concern the *rational function* of a generator, as opposed to its support: the affine
normal form of a principal divisor keeping track of the residue classes, the arithmetic of
residue classes read on affine charts, the normal form of a principal divisor of `E` on a
univariate chart, and the chart independence of the ratio of two polynomials representing the
rational function of a generator at a specialisation of its generic point.

The remaining step of `hgysin`, namely the assembly of the global relation as a finite sum of
divisors of `pointGenerator`s over the points of the intersection of the subvariety of the
generator with the section `t = c`, is **not** carried out here; see the "Open items" of the
report and `<scratchpad>/progress/T2c.md`.

## Main declarations

* `LineBundleInjective.exists_elementGenerator_sub_residue` — the affine normal form of a
  principal divisor on `Spec A[T]` keeping track of the residue classes: the two polynomials
  `a`, `b` representing the rational function of the generator satisfy `[a] = f · [b]` in the
  residue field at the generic point of the subspace of the generator.  Its converse
  `divisor_eq_sub_elementGenerator` produces the divisor identity from the residue relation.
* `LineBundleInjective.specResidueUnit_mul`, `specResidueUnit_eq_iff_sub_mem`,
  `specResidueUnit_cross_iff` — the arithmetic of the classes `specResidueUnit` of elements of a
  ring in the residue field of `Spec` at a prime.
* `LineBundleInjective.specChartUnit`, `specChartRatio`, `specChartRatio_eq_iff`,
  `specChartUnit_comp`, `specChartRatio_comp` — the same classes read in the residue field of an
  ambient scheme through an affine chart, and their behaviour under a refinement of charts.
* `LineBundleInjective.divisor_openGenerator_eq_of`, `exists_chartGenerator` — a generator whose
  generic point lies in a chart is represented by a generator of that chart.
* `LineBundleInjective.divisor_apply_eq_zero_of_not_specializes` — a principal divisor is
  supported on the closure of the generic point of its subspace.
* `LineBundleInjective.exists_polyChart_normalForm` — the normal form of a principal divisor of
  the total space on a univariate chart, together with the identification of the ratio of the
  two polynomials with the residue function of the generator.
* `LineBundleInjective.exists_refinement_crossMem`, `specChartRatio_poly_eq` — the chart
  independence of that ratio at a specialisation of the generic point, proved by passing to a
  common affine refinement of the two charts.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)

namespace LineBundleInjective

/-! ## The affine normal form with the residue relation -/

section AffineNormalForm

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The prime ideal of `A[T]` corresponding to the generic point of the subspace of a
principal-divisor generator on `Spec A[T]`. -/
noncomputable abbrev genericPrime
    (g : RationalFunctionGenerator (Spec (CommRingCat.of (Polynomial A)))) :
    Ideal (Polynomial A) :=
  ((g.subspace.genericPointImage : ↥(Spec (CommRingCat.of (Polynomial A)))) :
    PrimeSpectrum (Polynomial A)).asIdeal

/-- The residue function of a generator built from a polynomial on `V(P)`, in the form used
below. -/
theorem residueFunction_mk_elementFunction (P : Ideal (Polynomial A)) [P.IsPrime]
    (a : Polynomial A) (ha : a ∉ P)
    (ha' : a ∉ (((VectorBundle.quotientSubscheme P).genericPointImage :
      ↥(Spec (CommRingCat.of (Polynomial A)))) : PrimeSpectrum (Polynomial A)).asIdeal) :
    (RationalFunctionGenerator.mk (VectorBundle.quotientSubscheme P)
        (VectorBundle.elementFunction P a ha)).residueFunction =
      specResidueUnit (CommRingCat.of (Polynomial A))
        (VectorBundle.quotientSubscheme P).genericPointImage a ha' :=
  VectorBundle.residueFunction_elementGenerator P a ha

/-- The principal divisor of the constant function `1` vanishes. -/
theorem divisor_one {X : Scheme.{u}} (dim : DimensionFunction X)
    (V : IntegralClosedSubscheme X) :
    (RationalFunctionGenerator.mk V (1 : V.scheme.functionFieldˣ)).divisor dim = 0 := by
  have h : (RationalFunctionGenerator.mk V (1 : V.scheme.functionFieldˣ)).divisor dim =
      V.pushforward dim (V.scheme.principalCycle (1 : V.scheme.functionField)) := rfl
  rw [h, _root_.AlgebraicGeometry.Scheme.principalCycle_one]
  exact (AlgebraicCycle.mapLinear V.inclusion
    (fun z ↦ (dim : _ → ℤ) (V.inclusion.base z)) (dim : _ → ℤ)).map_zero

/-- The residue function of a generator is the residue function of its own data. -/
theorem residueFunction_mk_self {X : Scheme.{u}} (g : RationalFunctionGenerator X) :
    (RationalFunctionGenerator.mk g.subspace g.function).residueFunction =
      g.residueFunction := rfl

/-- The residue function of the constant function `1` is `1`. -/
theorem residueFunction_one {X : Scheme.{u}} (V : IntegralClosedSubscheme X) :
    (RationalFunctionGenerator.mk V (1 : V.scheme.functionFieldˣ)).residueFunction = 1 :=
  map_one _

/-- **From the residue relation to the divisor identity.**  If the classes of two polynomials
`a`, `b` at the generic point of the subspace of a generator `g` are related by
`[a] = g.residueFunction · [b]`, then the divisor of `g` is the difference of the divisors of
`a` and `b` on the subvariety `V(P)`, `P` the prime of that generic point. -/
theorem divisor_eq_sub_elementGenerator
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial A))))
    (g : RationalFunctionGenerator (Spec (CommRingCat.of (Polynomial A))))
    (a b : Polynomial A) (ha : a ∉ genericPrime g) (hb : b ∉ genericPrime g)
    (hrel : specResidueUnit (CommRingCat.of (Polynomial A))
          g.subspace.genericPointImage a ha =
        g.residueFunction *
          specResidueUnit (CommRingCat.of (Polynomial A))
            g.subspace.genericPointImage b hb) :
    g.divisor dimE =
      (VectorBundle.elementGenerator (genericPrime g) a ha).divisor dimE -
        (VectorBundle.elementGenerator (genericPrime g) b hb).divisor dimE := by
  have hxi : g.subspace.genericPointImage =
      (VectorBundle.quotientSubscheme (genericPrime g)).genericPointImage :=
    (PrimeSpectrum.ext (VectorBundle.genericPointImage_quotientSubscheme _)).symm
  have ha' : a ∉ (((VectorBundle.quotientSubscheme (genericPrime g)).genericPointImage :
      ↥(Spec (CommRingCat.of (Polynomial A)))) : PrimeSpectrum (Polynomial A)).asIdeal := by
    rw [VectorBundle.genericPointImage_quotientSubscheme]
    exact ha
  have hb' : b ∉ (((VectorBundle.quotientSubscheme (genericPrime g)).genericPointImage :
      ↥(Spec (CommRingCat.of (Polynomial A)))) : PrimeSpectrum (Polynomial A)).asIdeal := by
    rw [VectorBundle.genericPointImage_quotientSubscheme]
    exact hb
  have hcross : Units.map ((Spec (CommRingCat.of (Polynomial A))).residueFieldCongr
          hxi).hom.hom.toMonoidHom
        (RationalFunctionGenerator.mk g.subspace g.function).residueFunction *
        (RationalFunctionGenerator.mk (VectorBundle.quotientSubscheme (genericPrime g))
          (VectorBundle.elementFunction (genericPrime g) b hb)).residueFunction =
      (RationalFunctionGenerator.mk (VectorBundle.quotientSubscheme (genericPrime g))
          (VectorBundle.elementFunction (genericPrime g) a ha)).residueFunction *
        Units.map ((Spec (CommRingCat.of (Polynomial A))).residueFieldCongr
          hxi).hom.hom.toMonoidHom
          (RationalFunctionGenerator.mk g.subspace
            (1 : g.subspace.scheme.functionFieldˣ)).residueFunction := by
    rw [residueFunction_mk_self, residueFunction_one, map_one, mul_one,
      residueFunction_mk_elementFunction (genericPrime g) a ha ha',
      residueFunction_mk_elementFunction (genericPrime g) b hb hb',
      ← units_map_residueFieldCongr_specResidueUnit (CommRingCat.of (Polynomial A)) hxi a ha ha',
      ← units_map_residueFieldCongr_specResidueUnit (CommRingCat.of (Polynomial A)) hxi b hb hb',
      ← map_mul, ← hrel]
  have hmain := RationalFunctionGenerator.divisor_sub_eq_of_residueFunction_mul_eq dimE
    g.subspace (VectorBundle.quotientSubscheme (genericPrime g)) hxi g.function 1
    (VectorBundle.elementFunction (genericPrime g) a ha)
    (VectorBundle.elementFunction (genericPrime g) b hb) hcross
  rw [divisor_one, sub_zero] at hmain
  exact hmain

/-- **Affine normal form of a principal divisor, with the residue relation.**  Every principal
divisor on the total space `Spec A[T]` of the trivial line bundle over `Spec A` is the difference
of the divisors of two polynomials `a`, `b` on the closure of the generic point `ξ` of the
subspace of the generator, and the classes of `a` and `b` in the residue field at `ξ` are related
by the rational function of the generator: `[a] = f · [b]`.  This refines
`VectorBundle.exists_generator_eq_elementGenerator_sub`, which records only the divisor
identity. -/
theorem exists_elementGenerator_sub_residue
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial A))))
    (g : RationalFunctionGenerator (Spec (CommRingCat.of (Polynomial A)))) :
    ∃ (a b : Polynomial A) (ha : a ∉ genericPrime g) (hb : b ∉ genericPrime g),
      specResidueUnit (CommRingCat.of (Polynomial A)) g.subspace.genericPointImage a ha =
          g.residueFunction *
            specResidueUnit (CommRingCat.of (Polynomial A))
              g.subspace.genericPointImage b hb ∧
        g.divisor dimE =
          (VectorBundle.elementGenerator (genericPrime g) a ha).divisor dimE -
            (VectorBundle.elementGenerator (genericPrime g) b hb).divisor dimE := by
  classical
  have hvmap : Units.map (specResidueFieldIso (CommRingCat.of (Polynomial A))
        g.subspace.genericPointImage).inv.hom.toMonoidHom
      (Units.map (specResidueFieldIso (CommRingCat.of (Polynomial A))
        g.subspace.genericPointImage).hom.hom.toMonoidHom g.residueFunction) =
      g.residueFunction := by
    refine Units.ext ?_
    rw [Units.coe_map, Units.coe_map]
    exact Iso.hom_inv_id_apply
      (specResidueFieldIso (CommRingCat.of (Polynomial A)) g.subspace.genericPointImage)
      (g.residueFunction :
        (Spec (CommRingCat.of (Polynomial A))).residueField g.subspace.genericPointImage)
  obtain ⟨abar, bbar, hbbar, hab⟩ :=
    IsFractionRing.div_surjective (A := Polynomial A ⧸ genericPrime g)
      (K := (genericPrime g).ResidueField)
      ((Units.map (specResidueFieldIso (CommRingCat.of (Polynomial A))
        g.subspace.genericPointImage).hom.hom.toMonoidHom g.residueFunction :
          (genericPrime g).ResidueField))
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bbar
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective abar
  have hbP : b ∉ genericPrime g := fun hmem ↦
    nonZeroDivisors.ne_zero hbbar (Ideal.Quotient.eq_zero_iff_mem.2 hmem)
  have hbne : algebraMap (Polynomial A) (genericPrime g).ResidueField b ≠ 0 :=
    fun h ↦ hbP (Ideal.algebraMap_residueField_eq_zero.1 h)
  rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk,
    div_eq_iff hbne] at hab
  have haP : a ∉ genericPrime g := by
    intro hmem
    rw [Ideal.algebraMap_residueField_eq_zero.2 hmem] at hab
    exact mul_ne_zero (Units.ne_zero _) hbne hab.symm
  have hrel0 : residueUnit (genericPrime g) a haP =
      Units.map (specResidueFieldIso (CommRingCat.of (Polynomial A))
          g.subspace.genericPointImage).hom.hom.toMonoidHom g.residueFunction *
        residueUnit (genericPrime g) b hbP :=
    Units.ext hab
  have hrel : specResidueUnit (CommRingCat.of (Polynomial A))
        g.subspace.genericPointImage a haP =
      g.residueFunction *
        specResidueUnit (CommRingCat.of (Polynomial A))
          g.subspace.genericPointImage b hbP := by
    have hmapped := congrArg (Units.map (specResidueFieldIso (CommRingCat.of (Polynomial A))
      g.subspace.genericPointImage).inv.hom.toMonoidHom) hrel0
    rw [map_mul, hvmap] at hmapped
    exact hmapped
  exact ⟨a, b, haP, hbP, hrel, divisor_eq_sub_elementGenerator dimE g a b haP hbP hrel⟩

end AffineNormalForm

/-! ## Arithmetic of residue classes on an affine scheme -/

section SpecResidueArith

/-- The class of a product is the product of the classes. -/
theorem specResidueUnit_mul (B : CommRingCat.{u}) (x : ↥(Spec B)) (a b : B)
    (ha : a ∉ (x : PrimeSpectrum B).asIdeal) (hb : b ∉ (x : PrimeSpectrum B).asIdeal)
    (hab : a * b ∉ (x : PrimeSpectrum B).asIdeal) :
    specResidueUnit B x (a * b) hab = specResidueUnit B x a ha * specResidueUnit B x b hb := by
  refine Units.ext ?_
  rw [Units.val_mul, specResidueUnit_val, specResidueUnit_val, specResidueUnit_val, map_mul,
    map_mul]

/-- Two classes agree exactly when the difference of the elements lies in the prime. -/
theorem specResidueUnit_eq_iff_sub_mem (B : CommRingCat.{u}) (x : ↥(Spec B)) (a b : B)
    (ha : a ∉ (x : PrimeSpectrum B).asIdeal) (hb : b ∉ (x : PrimeSpectrum B).asIdeal) :
    specResidueUnit B x a ha = specResidueUnit B x b hb ↔
      a - b ∈ (x : PrimeSpectrum B).asIdeal := by
  rw [← Ideal.algebraMap_residueField_eq_zero
    (I := (x : PrimeSpectrum B).asIdeal) (x := a - b), map_sub, sub_eq_zero]
  constructor
  · intro h
    have hv : (specResidueFieldIso B x).inv
          (algebraMap (B : Type u) (x : PrimeSpectrum B).asIdeal.ResidueField a) =
        (specResidueFieldIso B x).inv
          (algebraMap (B : Type u) (x : PrimeSpectrum B).asIdeal.ResidueField b) := by
      rw [← specResidueUnit_val B x a ha, ← specResidueUnit_val B x b hb, h]
    have h2 := congrArg (fun t ↦ (specResidueFieldIso B x).hom t) hv
    rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at h2
    exact h2
  · intro h
    refine Units.ext ?_
    rw [specResidueUnit_val, specResidueUnit_val, h]

/-- The cross relation between four classes at a point, read as a membership. -/
theorem specResidueUnit_cross_iff (B : CommRingCat.{u}) (x : ↥(Spec B)) (a b a' b' : B)
    (ha : a ∉ (x : PrimeSpectrum B).asIdeal) (hb : b ∉ (x : PrimeSpectrum B).asIdeal)
    (ha' : a' ∉ (x : PrimeSpectrum B).asIdeal) (hb' : b' ∉ (x : PrimeSpectrum B).asIdeal) :
    specResidueUnit B x a ha * specResidueUnit B x b' hb' =
        specResidueUnit B x a' ha' * specResidueUnit B x b hb ↔
      a * b' - a' * b ∈ (x : PrimeSpectrum B).asIdeal := by
  have hab : a * b' ∉ (x : PrimeSpectrum B).asIdeal := fun h ↦
    ((x : PrimeSpectrum B).isPrime.mem_or_mem h).elim ha hb'
  have hab' : a' * b ∉ (x : PrimeSpectrum B).asIdeal := fun h ↦
    ((x : PrimeSpectrum B).isPrime.mem_or_mem h).elim ha' hb
  rw [← specResidueUnit_mul B x a b' ha hb' hab, ← specResidueUnit_mul B x a' b ha' hb hab',
    specResidueUnit_eq_iff_sub_mem]

end SpecResidueArith

/-! ## Residue classes of ring elements read on an affine chart -/

section SpecChartUnit

variable {X : Scheme.{u}} [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]
  {B : CommRingCat.{u}} (V : X.Opens) (e : Spec B ≅ V.toScheme)

/-- The class in the residue field of `X` at a point of an affine chart of an element of the
coordinate ring of that chart. -/
noncomputable def specChartUnit (x : ↥(Spec B)) (b : B)
    (hb : b ∉ (x : PrimeSpectrum B).asIdeal) :
    (X.residueField ((openInclusion V e).base x))ˣ :=
  openUnit V e x (specResidueUnit B x b hb)

/-- The class of the ratio of two elements of the coordinate ring of an affine chart, in the
residue field of `X`. -/
noncomputable def specChartRatio (x : ↥(Spec B)) (a b : B)
    (ha : a ∉ (x : PrimeSpectrum B).asIdeal) (hb : b ∉ (x : PrimeSpectrum B).asIdeal) :
    (X.residueField ((openInclusion V e).base x))ˣ :=
  specChartUnit V e x a ha / specChartUnit V e x b hb

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The class of a product is the product of the classes. -/
theorem specChartUnit_mul (x : ↥(Spec B)) (a b : B)
    (ha : a ∉ (x : PrimeSpectrum B).asIdeal) (hb : b ∉ (x : PrimeSpectrum B).asIdeal)
    (hab : a * b ∉ (x : PrimeSpectrum B).asIdeal) :
    specChartUnit V e x (a * b) hab = specChartUnit V e x a ha * specChartUnit V e x b hb := by
  rw [specChartUnit, specChartUnit, specChartUnit, specResidueUnit_mul B x a b ha hb hab,
    openUnit, openUnit, openUnit, map_mul]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- **The ratio of two chart classes is determined by the cross relation**: two pairs give the
same ratio at a point exactly when the difference of the cross products lies in the prime of
that point. -/
theorem specChartRatio_eq_iff (x : ↥(Spec B)) (a b a' b' : B)
    (ha : a ∉ (x : PrimeSpectrum B).asIdeal) (hb : b ∉ (x : PrimeSpectrum B).asIdeal)
    (ha' : a' ∉ (x : PrimeSpectrum B).asIdeal) (hb' : b' ∉ (x : PrimeSpectrum B).asIdeal) :
    specChartRatio V e x a b ha hb = specChartRatio V e x a' b' ha' hb' ↔
      a * b' - a' * b ∈ (x : PrimeSpectrum B).asIdeal := by
  rw [← specResidueUnit_cross_iff B x a b a' b' ha hb ha' hb', specChartRatio, specChartRatio,
    div_eq_div_iff_mul_eq_mul]
  constructor
  · intro h
    have h2 := congrArg (Units.map ((openInclusion V e).residueFieldMap x).hom.toMonoidHom) h
    rw [map_mul, map_mul, specChartUnit, specChartUnit, specChartUnit, specChartUnit,
      residueFieldMap_openUnit, residueFieldMap_openUnit, residueFieldMap_openUnit,
      residueFieldMap_openUnit] at h2
    exact h2
  · intro h
    rw [specChartUnit, specChartUnit, specChartUnit, specChartUnit, openUnit, openUnit, openUnit,
      openUnit, ← map_mul, ← map_mul]
    exact congrArg _ h

end SpecChartUnit

/-- **The class of a ring element computed on a smaller chart.**  This is
`openUnit_specResidueUnit_comp` read through `specChartUnit`. -/
theorem specChartUnit_comp {X : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]
    {B B' : CommRingCat.{u}} (V : X.Opens) (e : Spec B ≅ V.toScheme) (V' : X.Opens)
    (e' : Spec B' ≅ V'.toScheme) (φ : B ⟶ B')
    (hφ : Spec.map φ ≫ openInclusion V e = openInclusion V' e') (x' : ↥(Spec B')) (b : B)
    (hb : b ∉ ((((Spec.map φ).base x' : ↥(Spec B))) : PrimeSpectrum B).asIdeal)
    (hb' : φ b ∉ ((x' : PrimeSpectrum B')).asIdeal)
    (hy : (openInclusion V e).base ((Spec.map φ).base x') = (openInclusion V' e').base x') :
    specChartUnit V' e' x' (φ b) hb' =
      Units.map (X.residueFieldCongr hy).hom.hom.toMonoidHom
        (specChartUnit V e ((Spec.map φ).base x') b hb) :=
  openUnit_specResidueUnit_comp V e V' e' φ hφ x' b hb hb' hy

/-- **The ratio of two ring elements computed on a smaller chart.** -/
theorem specChartRatio_comp {X : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]
    {B B' : CommRingCat.{u}} (V : X.Opens) (e : Spec B ≅ V.toScheme) (V' : X.Opens)
    (e' : Spec B' ≅ V'.toScheme) (φ : B ⟶ B')
    (hφ : Spec.map φ ≫ openInclusion V e = openInclusion V' e') (x' : ↥(Spec B')) (a b : B)
    (ha : a ∉ ((((Spec.map φ).base x' : ↥(Spec B))) : PrimeSpectrum B).asIdeal)
    (hb : b ∉ ((((Spec.map φ).base x' : ↥(Spec B))) : PrimeSpectrum B).asIdeal)
    (ha' : φ a ∉ ((x' : PrimeSpectrum B')).asIdeal)
    (hb' : φ b ∉ ((x' : PrimeSpectrum B')).asIdeal)
    (hy : (openInclusion V e).base ((Spec.map φ).base x') = (openInclusion V' e').base x') :
    specChartRatio V' e' x' (φ a) (φ b) ha' hb' =
      Units.map (X.residueFieldCongr hy).hom.hom.toMonoidHom
        (specChartRatio V e ((Spec.map φ).base x') a b ha hb) := by
  rw [specChartRatio, specChartRatio, specChartUnit_comp V e V' e' φ hφ x' a ha ha' hy,
    specChartUnit_comp V e V' e' φ hφ x' b hb hb' hy, ← map_div]

/-! ## Chart normal form of a generator -/

section ChartNormalForm

variable {X W : Scheme.{u}} [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]
  (V : X.Opens) (e : W ≅ V.toScheme)

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- `openUnit` inverts the residue field map of the chart inclusion. -/
theorem openUnit_residueFieldMap (x : W) (w : (X.residueField ((openInclusion V e).base x))ˣ) :
    openUnit V e x (Units.map ((openInclusion V e).residueFieldMap x).hom.toMonoidHom w) = w :=
  (openUnit_eq_of_residueFieldMap_eq V e x _ w rfl).symm

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- Transport of `openUnit` along an equality of points of the chart. -/
theorem openUnit_congr {x x' : W} (h : x = x') (u : (W.residueField x)ˣ) :
    openUnit V e x' (Units.map (W.residueFieldCongr h).hom.hom.toMonoidHom u) =
      Units.map (X.residueFieldCongr
        (congrArg (openInclusion V e).base h)).hom.hom.toMonoidHom (openUnit V e x u) := by
  subst h
  rfl

/-- **Criterion for a chart generator to represent a generator of the ambient scheme.** -/
theorem divisor_openGenerator_eq_of (dim : DimensionFunction X)
    (g' : RationalFunctionGenerator W) (g : RationalFunctionGenerator X)
    (hy : (openInclusion V e).base g'.subspace.genericPointImage =
      g.subspace.genericPointImage)
    (hu : Units.map (X.residueFieldCongr hy).hom.hom.toMonoidHom (openResidueUnit V e g') =
      g.residueFunction) :
    (openGenerator V e g').divisor dim = g.divisor dim := by
  rw [divisor_openGenerator, ← divisor_pointGenerator_congr dim hy (openResidueUnit V e g'), hu,
    divisor_pointGenerator]

variable [_root_.AlgebraicGeometry.IsLocallyNoetherian W] [NoetherianSpace W]

/-- **Every generator whose generic point lies in a chart is represented by a generator of that
chart**, with the same residue class at the common generic point. -/
theorem exists_chartGenerator (g : RationalFunctionGenerator X)
    (hmem : g.subspace.genericPointImage ∈ Set.range (openInclusion V e).base) :
    ∃ (g' : RationalFunctionGenerator W)
      (hy : (openInclusion V e).base g'.subspace.genericPointImage =
        g.subspace.genericPointImage),
      Units.map (X.residueFieldCongr hy).hom.hom.toMonoidHom (openResidueUnit V e g') =
        g.residueFunction := by
  obtain ⟨p, hp⟩ := hmem
  set w : (X.residueField ((openInclusion V e).base p))ˣ :=
    Units.map (X.residueFieldCongr hp.symm).hom.hom.toMonoidHom g.residueFunction with hw
  set v : (W.residueField p)ˣ :=
    Units.map ((openInclusion V e).residueFieldMap p).hom.toMonoidHom w with hv
  have hgp : (pointGenerator p v).subspace.genericPointImage = p :=
    genericPointImage_pointGenerator p v
  refine ⟨pointGenerator p v, (congrArg (openInclusion V e).base hgp).trans hp, ?_⟩
  have h1 : openUnit V e p v =
      Units.map (X.residueFieldCongr
        (congrArg (openInclusion V e).base hgp)).hom.hom.toMonoidHom
          (openResidueUnit V e (pointGenerator p v)) := by
    rw [openResidueUnit_eq_openUnit, ← openUnit_congr V e hgp (pointGenerator p v).residueFunction,
      residueFunction_pointGenerator]
  have h2 : openUnit V e p v = w := by
    rw [hv, openUnit_residueFieldMap]
  have h3 := h1.symm.trans h2
  have h4 := congrArg (Units.map (X.residueFieldCongr hp).hom.hom.toMonoidHom) h3
  rw [hw, units_map_residueFieldCongr_trans, units_map_residueFieldCongr_trans] at h4
  rw [h4]
  rfl

end ChartNormalForm

/-! ## Support of a principal divisor -/

section Support

/-- **A principal divisor is supported on the closure of the generic point of its subspace.**
It vanishes at every point which is not a specialisation of that generic point. -/
theorem divisor_apply_eq_zero_of_not_specializes {X : Scheme.{u}} (dim : DimensionFunction X)
    (g : RationalFunctionGenerator X) (y : X)
    (hy : ¬ g.subspace.genericPointImage ⤳ y) :
    (g.divisor dim : X → ℚ) y = 0 := by
  classical
  have hopen : IsOpen ((closure {g.subspace.genericPointImage})ᶜ) :=
    isClosed_closure.isOpen_compl
  set U : X.Opens := ⟨(closure {g.subspace.genericPointImage})ᶜ, hopen⟩ with hUdef
  have hyU : y ∈ U := fun hmem ↦ hy (specializes_iff_mem_closure.2 hmem)
  have hempty : IsEmpty (g.subspace.inclusion ⁻¹ᵁ U) := by
    constructor
    rintro ⟨w, hw⟩
    have _ := g.subspace.isIntegral
    have hspec : g.subspace.genericPointImage ⤳ g.subspace.inclusion.base w :=
      (genericPoint_specializes w).map g.subspace.inclusion.continuous
    exact hw (specializes_iff_mem_closure.1 hspec)
  have h0 := @RationalFunctionGenerator.pullbackOpen_divisor_eq_zero X g U hempty dim
  have h1 := congrArg (fun t : AlgebraicCycle U.toScheme ℚ ↦
    (t : ↥(U.toScheme) → ℚ) (⟨y, hyU⟩ : ↥(U.toScheme))) h0
  exact h1

end Support

/-! ## Normal form of a principal divisor of the total space on a univariate chart -/

section LineChartNormalForm

variable {Y : Scheme.{u}} [_root_.AlgebraicGeometry.IsLocallyNoetherian Y]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)] [NoetherianSpace (lineSpace Y)]

/-- **Chart normal form of a principal divisor of the total space.**  If the generic point of a
generator `g` of the total space of the trivial line bundle lies in the univariate chart over
`U`, then the restriction of its divisor to that chart is the difference of the divisors of two
polynomials on the subvariety cut out by the generic point, and the ratio of the classes of
those two polynomials in the residue field of the total space at the generic point is the
residue function of `g`. -/
theorem exists_polyChart_normalForm (g : RationalFunctionGenerator (lineSpace Y))
    (dimE : DimensionFunction (lineSpace Y)) (U : Y.affineOpens)
    (dimU : DimensionFunction (Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (dimV : DimensionFunction (polyOpens U).toScheme)
    (hmem : g.subspace.genericPointImage ∈ polyOpens U) :
    ∃ (p : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
      (hp : (openInclusion (polyOpens U) (polyIso U)).base p =
        g.subspace.genericPointImage)
      (a b : Polynomial Γ(Y, U.1))
      (ha : a ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
      (hb : b ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal),
      AlgebraicCycle.pullbackOpen (openInclusion (polyOpens U) (polyIso U)) (g.divisor dimE) =
          (VectorBundle.elementGenerator
              (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal a ha).divisor dimU -
            (VectorBundle.elementGenerator
              (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal b hb).divisor dimU ∧
        specChartRatio (polyOpens U) (polyIso U) p a b ha hb =
          Units.map ((lineSpace Y).residueFieldCongr hp.symm).hom.hom.toMonoidHom
            g.residueFunction := by
  obtain ⟨p0, hp0⟩ := hmem
  have hrange : g.subspace.genericPointImage ∈
      Set.range (openInclusion (polyOpens U) (polyIso U)).base := by
    rw [openInclusion_polyIso]
    exact ⟨p0, hp0⟩
  obtain ⟨g', hy, hu⟩ := exists_chartGenerator (polyOpens U) (polyIso U) g hrange
  obtain ⟨a, b, ha, hb, hrel, hdiv⟩ := exists_elementGenerator_sub_residue dimU g'
  refine ⟨g'.subspace.genericPointImage, hy, a, b, ha, hb, ?_, ?_⟩
  · refine Eq.trans ?_ hdiv
    rw [← divisor_openGenerator_eq_of (polyOpens U) (polyIso U) dimE g' g hy hu]
    exact pullbackOpen_divisor_openGenerator (polyOpens U) (polyIso U) dimE dimV dimU g'
  · have hr : specChartRatio (polyOpens U) (polyIso U) g'.subspace.genericPointImage a b ha hb =
        openUnit (polyOpens U) (polyIso U) g'.subspace.genericPointImage g'.residueFunction := by
      rw [specChartRatio, specChartUnit, specChartUnit, hrel, openUnit, openUnit, openUnit,
        map_mul, mul_div_cancel_right]
    have h2 := congrArg (Units.map
      (((lineSpace Y).residueFieldCongr hy.symm)).hom.hom.toMonoidHom) hu
    rw [units_map_residueFieldCongr_trans] at h2
    rw [hr, ← openResidueUnit_eq_openUnit]
    exact h2

end LineChartNormalForm

/-! ## Chart independence of the ratio at a specialisation -/

section CrossChart

variable {Y : Scheme.{u}}
  [_root_.AlgebraicGeometry.IsLocallyNoetherian (lineSpace Y)] [NoetherianSpace (lineSpace Y)]

/-- **Chart independence of the ratio of two polynomials representing a rational function.**
Two pairs of polynomials read on two univariate charts of the total space, whose ratios agree in
the residue field at a point `ξ`, have the same ratio at every specialisation `q` of `ξ` at which
all four polynomials are invertible. -/
theorem specChartRatio_poly_eq {U U' : Y.affineOpens}
    (p V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (p' V' : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U'.1)))))
    (a b : Polynomial Γ(Y, U.1)) (a' b' : Polynomial Γ(Y, U'.1))
    (hap : a ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hbp : b ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hap' : a' ∉ (p' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (hbp' : b' ∉ (p' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (haV : a ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hbV : b ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (haV' : a' ∉ (V' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (hbV' : b' ∉ (V' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (hspec : (openInclusion (polyOpens U) (polyIso U)).base p ⤳
      (openInclusion (polyOpens U) (polyIso U)).base V)
    (hξ : (openInclusion (polyOpens U') (polyIso U')).base p' =
      (openInclusion (polyOpens U) (polyIso U)).base p)
    (hq : (openInclusion (polyOpens U') (polyIso U')).base V' =
      (openInclusion (polyOpens U) (polyIso U)).base V)
    (hrat : Units.map ((lineSpace Y).residueFieldCongr hξ).hom.hom.toMonoidHom
        (specChartRatio (polyOpens U') (polyIso U') p' a' b' hap' hbp') =
      specChartRatio (polyOpens U) (polyIso U) p a b hap hbp) :
    Units.map ((lineSpace Y).residueFieldCongr hq).hom.hom.toMonoidHom
        (specChartRatio (polyOpens U') (polyIso U') V' a' b' haV' hbV') =
      specChartRatio (polyOpens U) (polyIso U) V a b haV hbV := by
  classical
  have hqUmem : (openInclusion (polyOpens U) (polyIso U)).base V ∈ polyOpens U :=
    ⟨V, by rw [openInclusion_polyIso]⟩
  have hqU'mem : (openInclusion (polyOpens U) (polyIso U)).base V ∈ polyOpens U' := by
    rw [← hq]
    exact ⟨V', by rw [openInclusion_polyIso]⟩
  rw [mem_polyOpens_iff] at hqUmem hqU'mem
  obtain ⟨W, hWaff, hyW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
    Y.isBasis_affineOpens (show (trivialData Y PUnit.{u + 1}).proj.base
      ((openInclusion (polyOpens U) (polyIso U)).base V) ∈ U.1 ⊓ U'.1 from ⟨hqUmem, hqU'mem⟩)
  have hWU : (⟨W, hWaff⟩ : Y.affineOpens) ≤ U := (le_trans hWle inf_le_left : W ≤ U.1)
  have hWU' : (⟨W, hWaff⟩ : Y.affineOpens) ≤ U' := (le_trans hWle inf_le_right : W ≤ U'.1)
  have hmemq : (openInclusion (polyOpens U) (polyIso U)).base V ∈
      polyOpens (⟨W, hWaff⟩ : Y.affineOpens) := by
    rw [mem_polyOpens_iff]
    exact hyW
  have hmemp : (openInclusion (polyOpens U) (polyIso U)).base p ∈
      polyOpens (⟨W, hWaff⟩ : Y.affineOpens) :=
    hspec.mem_open (polyOpens (⟨W, hWaff⟩ : Y.affineOpens)).2 hmemq
  obtain ⟨VW, hVW⟩ := hmemq
  obtain ⟨pW, hpW⟩ := hmemp
  have hinclV : (openInclusion (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
      (polyIso (⟨W, hWaff⟩ : Y.affineOpens))).base VW =
      (openInclusion (polyOpens U) (polyIso U)).base V := by
    rw [openInclusion_polyIso]
    exact hVW
  have hinclP : (openInclusion (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
      (polyIso (⟨W, hWaff⟩ : Y.affineOpens))).base pW =
      (openInclusion (polyOpens U) (polyIso U)).base p := by
    rw [openInclusion_polyIso]
    exact hpW
  have hVbase : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (GlobalBlowup.res Y hWU)))).base VW = V := by
    refine (openInclusion (polyOpens U) (polyIso U)).isOpenEmbedding.injective ?_
    have h := congrArg
      (fun m : Spec (CommRingCat.of (Polynomial Γ(Y, W))) ⟶ lineSpace Y ↦ m.base VW)
      (openInclusion_polyIso_comp (V := U) hWU)
    exact h.trans hinclV
  have hVbase' : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (GlobalBlowup.res Y hWU')))).base VW = V' := by
    refine (openInclusion (polyOpens U') (polyIso U')).isOpenEmbedding.injective ?_
    have h := congrArg
      (fun m : Spec (CommRingCat.of (Polynomial Γ(Y, W))) ⟶ lineSpace Y ↦ m.base VW)
      (openInclusion_polyIso_comp (V := U') hWU')
    rw [hq]
    exact h.trans hinclV
  have hPbase : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (GlobalBlowup.res Y hWU)))).base pW = p := by
    refine (openInclusion (polyOpens U) (polyIso U)).isOpenEmbedding.injective ?_
    have h := congrArg
      (fun m : Spec (CommRingCat.of (Polynomial Γ(Y, W))) ⟶ lineSpace Y ↦ m.base pW)
      (openInclusion_polyIso_comp (V := U) hWU)
    exact h.trans hinclP
  have hPbase' : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (GlobalBlowup.res Y hWU')))).base pW = p' := by
    refine (openInclusion (polyOpens U') (polyIso U')).isOpenEmbedding.injective ?_
    have h := congrArg
      (fun m : Spec (CommRingCat.of (Polynomial Γ(Y, W))) ⟶ lineSpace Y ↦ m.base pW)
      (openInclusion_polyIso_comp (V := U') hWU')
    rw [hξ]
    exact h.trans hinclP
  subst hVbase
  subst hVbase'
  subst hPbase
  subst hPbase'
  have hle : (pW : PrimeSpectrum (Polynomial Γ(Y, W))).asIdeal ≤
      (VW : PrimeSpectrum (Polynomial Γ(Y, W))).asIdeal := by
    have hsW : pW ⤳ VW := by
      refine (Topology.IsInducing.specializes_iff
        (openInclusion (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
          (polyIso (⟨W, hWaff⟩ : Y.affineOpens))).isOpenEmbedding.isInducing).1 ?_
      rw [hinclP, hinclV]
      exact hspec
    exact (PrimeSpectrum.le_iff_specializes pW VW).2 hsW
  have e1 := specChartRatio_comp (polyOpens U) (polyIso U)
    (polyOpens (⟨W, hWaff⟩ : Y.affineOpens)) (polyIso (⟨W, hWaff⟩ : Y.affineOpens))
    (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU)))
    (openInclusion_polyIso_comp hWU) VW a b haV hbV haV hbV hinclV.symm
  have e1' := specChartRatio_comp (polyOpens U') (polyIso U')
    (polyOpens (⟨W, hWaff⟩ : Y.affineOpens)) (polyIso (⟨W, hWaff⟩ : Y.affineOpens))
    (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU')))
    (openInclusion_polyIso_comp hWU') VW a' b' haV' hbV' haV' hbV' (hq.trans hinclV.symm)
  have e2 := specChartRatio_comp (polyOpens U) (polyIso U)
    (polyOpens (⟨W, hWaff⟩ : Y.affineOpens)) (polyIso (⟨W, hWaff⟩ : Y.affineOpens))
    (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU)))
    (openInclusion_polyIso_comp hWU) pW a b hap hbp hap hbp hinclP.symm
  have e2' := specChartRatio_comp (polyOpens U') (polyIso U')
    (polyOpens (⟨W, hWaff⟩ : Y.affineOpens)) (polyIso (⟨W, hWaff⟩ : Y.affineOpens))
    (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU')))
    (openInclusion_polyIso_comp hWU') pW a' b' hap' hbp' hap' hbp' (hξ.trans hinclP.symm)
  have hpEq : specChartRatio (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
        (polyIso (⟨W, hWaff⟩ : Y.affineOpens)) pW
        ((CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU))) a)
        ((CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU))) b) hap hbp =
      specChartRatio (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
        (polyIso (⟨W, hWaff⟩ : Y.affineOpens)) pW
        ((CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU'))) a')
        ((CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU'))) b') hap' hbp' := by
    rw [e2, e2', ← hrat, units_map_residueFieldCongr_trans]
  have hmem := (specChartRatio_eq_iff (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
    (polyIso (⟨W, hWaff⟩ : Y.affineOpens)) pW _ _ _ _ hap hbp hap' hbp').1 hpEq
  have hVEq := (specChartRatio_eq_iff (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
    (polyIso (⟨W, hWaff⟩ : Y.affineOpens)) VW _ _ _ _ haV hbV haV' hbV').2 (hle hmem)
  rw [e1, e1'] at hVEq
  have h5 := congrArg (Units.map (((lineSpace Y).residueFieldCongr
    hinclV)).hom.hom.toMonoidHom) hVEq
  rw [units_map_residueFieldCongr_trans, units_map_residueFieldCongr_trans] at h5
  exact h5.symm

/-- **The cross relation on a common refinement of two univariate charts.**  Two pairs of
polynomials read on two univariate charts of the total space, whose ratios agree in the residue
field at a point `ξ`, satisfy the cross relation at every specialisation `q` of `ξ`, after
restriction to a common affine refinement of the two charts. -/
theorem exists_refinement_crossMem {U U' : Y.affineOpens}
    (p V : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U.1)))))
    (p' V' : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, U'.1)))))
    (a b : Polynomial Γ(Y, U.1)) (a' b' : Polynomial Γ(Y, U'.1))
    (hap : a ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hbp : b ∉ (p : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hap' : a' ∉ (p' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (hbp' : b' ∉ (p' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (haV : a ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (hbV : b ∉ (V : PrimeSpectrum (Polynomial Γ(Y, U.1))).asIdeal)
    (haV' : a' ∉ (V' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (hbV' : b' ∉ (V' : PrimeSpectrum (Polynomial Γ(Y, U'.1))).asIdeal)
    (hspec : (openInclusion (polyOpens U) (polyIso U)).base p ⤳
      (openInclusion (polyOpens U) (polyIso U)).base V)
    (hξ : (openInclusion (polyOpens U') (polyIso U')).base p' =
      (openInclusion (polyOpens U) (polyIso U)).base p)
    (hq : (openInclusion (polyOpens U') (polyIso U')).base V' =
      (openInclusion (polyOpens U) (polyIso U)).base V)
    (hrat : Units.map ((lineSpace Y).residueFieldCongr hξ).hom.hom.toMonoidHom
        (specChartRatio (polyOpens U') (polyIso U') p' a' b' hap' hbp') =
      specChartRatio (polyOpens U) (polyIso U) p a b hap hbp) :
    ∃ (W : Y.affineOpens) (hWU : W ≤ U) (hWU' : W ≤ U')
      (VW : ↥(Spec (CommRingCat.of (Polynomial Γ(Y, W.1))))),
      (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (GlobalBlowup.res Y hWU)))).base VW = V ∧
        (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (GlobalBlowup.res Y hWU')))).base VW = V' ∧
        (openInclusion (polyOpens W) (polyIso W)).base VW =
          (openInclusion (polyOpens U) (polyIso U)).base V ∧
        (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU))) a *
              (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU'))) b' -
            (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU'))) a' *
              (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU))) b ∈
          (VW : PrimeSpectrum (Polynomial Γ(Y, W.1))).asIdeal := by
  classical
  have hqUmem : (openInclusion (polyOpens U) (polyIso U)).base V ∈ polyOpens U :=
    ⟨V, by rw [openInclusion_polyIso]⟩
  have hqU'mem : (openInclusion (polyOpens U) (polyIso U)).base V ∈ polyOpens U' := by
    rw [← hq]
    exact ⟨V', by rw [openInclusion_polyIso]⟩
  rw [mem_polyOpens_iff] at hqUmem hqU'mem
  obtain ⟨W, hWaff, hyW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
    Y.isBasis_affineOpens (show (trivialData Y PUnit.{u + 1}).proj.base
      ((openInclusion (polyOpens U) (polyIso U)).base V) ∈ U.1 ⊓ U'.1 from ⟨hqUmem, hqU'mem⟩)
  have hWU : (⟨W, hWaff⟩ : Y.affineOpens) ≤ U := (le_trans hWle inf_le_left : W ≤ U.1)
  have hWU' : (⟨W, hWaff⟩ : Y.affineOpens) ≤ U' := (le_trans hWle inf_le_right : W ≤ U'.1)
  have hmemq : (openInclusion (polyOpens U) (polyIso U)).base V ∈
      polyOpens (⟨W, hWaff⟩ : Y.affineOpens) := by
    rw [mem_polyOpens_iff]
    exact hyW
  have hmemp : (openInclusion (polyOpens U) (polyIso U)).base p ∈
      polyOpens (⟨W, hWaff⟩ : Y.affineOpens) :=
    hspec.mem_open (polyOpens (⟨W, hWaff⟩ : Y.affineOpens)).2 hmemq
  obtain ⟨VW, hVW⟩ := hmemq
  obtain ⟨pW, hpW⟩ := hmemp
  have hinclV : (openInclusion (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
      (polyIso (⟨W, hWaff⟩ : Y.affineOpens))).base VW =
      (openInclusion (polyOpens U) (polyIso U)).base V := by
    rw [openInclusion_polyIso]
    exact hVW
  have hinclP : (openInclusion (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
      (polyIso (⟨W, hWaff⟩ : Y.affineOpens))).base pW =
      (openInclusion (polyOpens U) (polyIso U)).base p := by
    rw [openInclusion_polyIso]
    exact hpW
  have hVbase : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (GlobalBlowup.res Y hWU)))).base VW = V := by
    refine (openInclusion (polyOpens U) (polyIso U)).isOpenEmbedding.injective ?_
    have h := congrArg
      (fun m : Spec (CommRingCat.of (Polynomial Γ(Y, W))) ⟶ lineSpace Y ↦ m.base VW)
      (openInclusion_polyIso_comp (V := U) hWU)
    exact h.trans hinclV
  have hVbase' : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (GlobalBlowup.res Y hWU')))).base VW = V' := by
    refine (openInclusion (polyOpens U') (polyIso U')).isOpenEmbedding.injective ?_
    have h := congrArg
      (fun m : Spec (CommRingCat.of (Polynomial Γ(Y, W))) ⟶ lineSpace Y ↦ m.base VW)
      (openInclusion_polyIso_comp (V := U') hWU')
    rw [hq]
    exact h.trans hinclV
  have hPbase : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (GlobalBlowup.res Y hWU)))).base pW = p := by
    refine (openInclusion (polyOpens U) (polyIso U)).isOpenEmbedding.injective ?_
    have h := congrArg
      (fun m : Spec (CommRingCat.of (Polynomial Γ(Y, W))) ⟶ lineSpace Y ↦ m.base pW)
      (openInclusion_polyIso_comp (V := U) hWU)
    exact h.trans hinclP
  have hPbase' : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (GlobalBlowup.res Y hWU')))).base pW = p' := by
    refine (openInclusion (polyOpens U') (polyIso U')).isOpenEmbedding.injective ?_
    have h := congrArg
      (fun m : Spec (CommRingCat.of (Polynomial Γ(Y, W))) ⟶ lineSpace Y ↦ m.base pW)
      (openInclusion_polyIso_comp (V := U') hWU')
    rw [hξ]
    exact h.trans hinclP
  subst hVbase
  subst hVbase'
  subst hPbase
  subst hPbase'
  have hle : (pW : PrimeSpectrum (Polynomial Γ(Y, W))).asIdeal ≤
      (VW : PrimeSpectrum (Polynomial Γ(Y, W))).asIdeal := by
    have hsW : pW ⤳ VW := by
      refine (Topology.IsInducing.specializes_iff
        (openInclusion (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
          (polyIso (⟨W, hWaff⟩ : Y.affineOpens))).isOpenEmbedding.isInducing).1 ?_
      rw [hinclP, hinclV]
      exact hspec
    exact (PrimeSpectrum.le_iff_specializes pW VW).2 hsW
  have e2 := specChartRatio_comp (polyOpens U) (polyIso U)
    (polyOpens (⟨W, hWaff⟩ : Y.affineOpens)) (polyIso (⟨W, hWaff⟩ : Y.affineOpens))
    (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU)))
    (openInclusion_polyIso_comp hWU) pW a b hap hbp hap hbp hinclP.symm
  have e2' := specChartRatio_comp (polyOpens U') (polyIso U')
    (polyOpens (⟨W, hWaff⟩ : Y.affineOpens)) (polyIso (⟨W, hWaff⟩ : Y.affineOpens))
    (CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU')))
    (openInclusion_polyIso_comp hWU') pW a' b' hap' hbp' hap' hbp' (hξ.trans hinclP.symm)
  have hpEq : specChartRatio (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
        (polyIso (⟨W, hWaff⟩ : Y.affineOpens)) pW
        ((CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU))) a)
        ((CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU))) b) hap hbp =
      specChartRatio (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
        (polyIso (⟨W, hWaff⟩ : Y.affineOpens)) pW
        ((CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU'))) a')
        ((CommRingCat.ofHom (Polynomial.mapRingHom (GlobalBlowup.res Y hWU'))) b') hap' hbp' := by
    rw [e2, e2', ← hrat, units_map_residueFieldCongr_trans]
  have hmemCross := (specChartRatio_eq_iff (polyOpens (⟨W, hWaff⟩ : Y.affineOpens))
    (polyIso (⟨W, hWaff⟩ : Y.affineOpens)) pW _ _ _ _ hap hbp hap' hbp').1 hpEq
  exact ⟨⟨W, hWaff⟩, hWU, hWU', VW, rfl, rfl, hinclV, hle hmemCross⟩

end CrossChart

end LineBundleInjective

end GromovWitten.AlgebraicGeometry.IntersectionTheory
