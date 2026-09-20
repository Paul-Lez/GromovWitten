/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.GeneratorInvariance

/-!
# Residue functions of the affine generators

`GeneratorInvariance.lean` shows that the principal divisor of a `RationalFunctionGenerator X`
depends only on the image `genericPointImage` of the generic point of its subscheme and on the
class `residueFunction` of its rational function in the residue field of `X` at that point.  This
file computes `residueFunction` for the two affine generators of `BundleSectionGysin.lean` and
derives the comparison of differences of principal divisors that the global rank-one argument
consumes.

## Main results

* `residue_algebraMap_stalk_spec`, `stalkMap_spec_algebraMap`: the two affine bookkeeping lemmas
  identifying germs of global sections with Mathlib's residue field `Ideal.ResidueField`.
* `specResidueUnit`: the class of a ring element at a point of `Spec B` where it does not vanish,
  as a unit of the residue field of `Spec B` at that point.
* `VectorBundle.residueFunction_elementGenerator`: the residue function of
  `elementGenerator P a ha` is the class of `a` at the point `P` of `Spec R[T]`.
* `VectorBundle.residueFunction_sectionGenerator`: the residue function of
  `sectionGenerator c Q hQ a ha` is the class of `a(c)` at the base point of `Q` in `Spec R`.
* `RationalFunctionGenerator.divisor_sub_eq_of_residueFunction_mul_eq`: two differences of
  principal divisors built from two integral closed subschemes with the same generic point image
  agree as soon as the four residue classes satisfy the cross relation `a · b' = a' · b`.
* `RationalFunctionGenerator.residueFieldMap_residueFunction_closedImage`: compatibility of
  `residueFunction` with `closedImage` along a closed immersion.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## Residue fields of affine schemes -/

section SpecResidue

/-- Mathlib's identification of the residue field of `Spec B` at a point with the residue field
of the corresponding prime ideal of `B`. -/
noncomputable abbrev specResidueFieldIso (B : CommRingCat.{u}) (x : ↥(Spec B)) :
    (Spec B).residueField x ≅
      CommRingCat.of ((x : PrimeSpectrum B).asIdeal.ResidueField) :=
  _root_.AlgebraicGeometry.Scheme.Spec.residueFieldIso B x

/-- The germ at `x` of a global section `b` of `Spec B` has residue the class of `b` in the
residue field of the prime ideal corresponding to `x`. -/
theorem residue_algebraMap_stalk_spec (B : CommRingCat.{u}) (x : ↥(Spec B)) (b : B) :
    (Spec B).residue x (algebraMap B ((Spec B).presheaf.stalk x) b) =
      (specResidueFieldIso B x).inv
        (algebraMap B (x : PrimeSpectrum B).asIdeal.ResidueField b) := by
  have h := ConcreteCategory.congr_hom
    (_root_.AlgebraicGeometry.Scheme.Spec.algebraMap_residueFieldIso_inv B x) b
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply] at h
  have hg : algebraMap B ((Spec B).presheaf.stalk x) b =
      (Spec B).presheaf.germ ⊤ x (Opens.mem_top _)
        ((_root_.AlgebraicGeometry.Scheme.ΓSpecIso B).inv b) :=
    (StructureSheaf.algebraMap_germ_apply (R := B) ⊤ _ (Opens.mem_top _) b).symm
  exact (congrArg _ hg).trans h.symm

/-- The stalk map of `Spec.map f` sends the germ of a global section `b` to the germ of `f b`. -/
theorem stalkMap_spec_algebraMap {B C : CommRingCat.{u}} (f : B ⟶ C) (x : ↥(Spec C)) (b : B) :
    (Spec.map f).stalkMap x
        (algebraMap B ((Spec B).presheaf.stalk ((Spec.map f).base x)) b) =
      algebraMap C ((Spec C).presheaf.stalk x) (f b) := by
  have h1 : algebraMap B ((Spec B).presheaf.stalk ((Spec.map f).base x)) b =
      (Spec B).presheaf.germ ⊤ ((Spec.map f).base x) (Opens.mem_top _)
        ((_root_.AlgebraicGeometry.Scheme.ΓSpecIso B).inv b) :=
    (StructureSheaf.algebraMap_germ_apply (R := B) ⊤ _ (Opens.mem_top _) b).symm
  have h2 : algebraMap C ((Spec C).presheaf.stalk x) (f b) =
      (Spec C).presheaf.germ ⊤ x (Opens.mem_top _)
        ((_root_.AlgebraicGeometry.Scheme.ΓSpecIso C).inv (f b)) :=
    (StructureSheaf.algebraMap_germ_apply (R := C) ⊤ _ (Opens.mem_top _) (f b)).symm
  have h3 := ConcreteCategory.congr_hom
    (_root_.AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality f) b
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h3
  rw [h1, h2, _root_.AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply, h3]
  rfl

/-- The class of an element outside a prime ideal, as a unit of the residue field. -/
noncomputable def residueUnit {B : Type u} [CommRing B] (P : Ideal B) [P.IsPrime] (a : B)
    (ha : a ∉ P) : (P.ResidueField)ˣ :=
  Units.mk0 (algebraMap B P.ResidueField a)
    fun h ↦ ha (Ideal.algebraMap_residueField_eq_zero.1 h)

/-- The underlying element of `residueUnit`. -/
@[simp]
theorem residueUnit_val {B : Type u} [CommRing B] (P : Ideal B) [P.IsPrime] (a : B)
    (ha : a ∉ P) : (residueUnit P a ha : P.ResidueField) = algebraMap B P.ResidueField a :=
  rfl

/-- The class at a point of `Spec B` of a ring element which does not vanish there, as a unit of
the residue field of `Spec B` at that point. -/
noncomputable def specResidueUnit (B : CommRingCat.{u}) (x : ↥(Spec B)) (b : B)
    (hb : b ∉ (x : PrimeSpectrum B).asIdeal) : ((Spec B).residueField x)ˣ :=
  Units.map (specResidueFieldIso B x).inv.hom.toMonoidHom
    (residueUnit (x : PrimeSpectrum B).asIdeal b hb)

/-- The underlying element of `specResidueUnit`, in terms of Mathlib's residue field. -/
theorem specResidueUnit_val (B : CommRingCat.{u}) (x : ↥(Spec B)) (b : B)
    (hb : b ∉ (x : PrimeSpectrum B).asIdeal) :
    (specResidueUnit B x b hb : (Spec B).residueField x) =
      (specResidueFieldIso B x).inv
        (algebraMap B (x : PrimeSpectrum B).asIdeal.ResidueField b) := rfl

/-- The underlying element of `specResidueUnit`, in terms of the germ of `b` in the stalk. -/
theorem specResidueUnit_val_eq_residue (B : CommRingCat.{u}) (x : ↥(Spec B)) (b : B)
    (hb : b ∉ (x : PrimeSpectrum B).asIdeal) :
    (specResidueUnit B x b hb : (Spec B).residueField x) =
      (Spec B).residue x (algebraMap B ((Spec B).presheaf.stalk x) b) :=
  ((residue_algebraMap_stalk_spec B x b).trans (specResidueUnit_val B x b hb).symm).symm

end SpecResidue

/-! ## The residue function of the affine generators -/

namespace VectorBundle

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The polynomial `a` does not lie in the prime corresponding to the generic point of
`V(P)`. -/
theorem notMem_genericPointImage_elementGenerator (P : Ideal (Polynomial R)) [P.IsPrime]
    (a : Polynomial R) (ha : a ∉ P) :
    a ∉ (((elementGenerator P a ha).subspace.genericPointImage :
      ↥(Spec (CommRingCat.of (Polynomial R)))) : PrimeSpectrum (Polynomial R)).asIdeal := by
  rw [genericPointImage_elementGenerator P a ha]
  exact ha

/-- The residue function of `elementGenerator P a ha` is the class of the polynomial `a` in the
residue field of `Spec R[T]` at the point `P`. -/
theorem residueFunction_elementGenerator (P : Ideal (Polynomial R)) [P.IsPrime]
    (a : Polynomial R) (ha : a ∉ P) :
    (elementGenerator P a ha).residueFunction =
      specResidueUnit (CommRingCat.of (Polynomial R))
        (elementGenerator P a ha).subspace.genericPointImage a
        (notMem_genericPointImage_elementGenerator P a ha) := by
  refine Units.ext ?_
  rw [RationalFunctionGenerator.residueFunction_val, specResidueUnit_val_eq_residue,
    ← IntegralClosedSubscheme.stalkMap_functionFieldIso]
  exact congrArg _ ((functionFieldUnit_val (CommRingCat.of (Polynomial R ⧸ P))
      (Ideal.Quotient.mk P a) (quotientMk_ne_zero P a ha)).trans
    (stalkMap_spec_algebraMap (CommRingCat.ofHom (Ideal.Quotient.mk P))
      (genericPoint (Spec (CommRingCat.of (Polynomial R ⧸ P)))) a).symm)

variable (c : R)

omit [IsNoetherianRing R] in
/-- The class of `a` modulo a prime containing `T - c` is the class of the constant `a(c)`. -/
theorem sectionQuotientHom_eval (Q : Ideal (Polynomial R)) (hQ : sectionPoly c ∈ Q)
    (a : Polynomial R) :
    sectionQuotientHom (R := R) Q (Polynomial.eval c a) = Ideal.Quotient.mk Q a :=
  congrArg (fun h : Polynomial R →+* Polynomial R ⧸ Q ↦ h a)
    (sectionQuotientHom_comp_evalRingHom c Q hQ)

omit [IsNoetherianRing R] in
/-- A polynomial lies in a prime containing `T - c` exactly when its value at `c` lies in the
contraction of that prime to the constants. -/
theorem eval_mem_comap_iff (Q : Ideal (Polynomial R)) (hQ : sectionPoly c ∈ Q)
    (a : Polynomial R) :
    Polynomial.eval c a ∈ Q.comap (Polynomial.C : R →+* Polynomial R) ↔ a ∈ Q := by
  have hkey : Ideal.Quotient.mk Q (Polynomial.C (Polynomial.eval c a)) =
      Ideal.Quotient.mk Q a := sectionQuotientHom_eval c Q hQ a
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem, hkey]

/-- The value `a(c)` does not lie in the prime corresponding to the generic point of the
subvariety of a `sectionGenerator`. -/
theorem notMem_genericPointImage_sectionGenerator (Q : Ideal (Polynomial R)) [Q.IsPrime]
    (hQ : sectionPoly c ∈ Q) (a : Polynomial R) (ha : a ∉ Q) :
    Polynomial.eval c a ∉ (((sectionGenerator c Q hQ a ha).subspace.genericPointImage :
      ↥(Spec (CommRingCat.of R))) : PrimeSpectrum R).asIdeal := by
  rw [genericPointImage_sectionGenerator c Q hQ a ha]
  exact fun h ↦ ha ((eval_mem_comap_iff c Q hQ a).1 h)

/-- The residue function of `sectionGenerator c Q hQ a ha` is the class of `a(c)` in the residue
field of `Spec R` at the base point of `Q`. -/
theorem residueFunction_sectionGenerator (Q : Ideal (Polynomial R)) [Q.IsPrime]
    (hQ : sectionPoly c ∈ Q) (a : Polynomial R) (ha : a ∉ Q) :
    (sectionGenerator c Q hQ a ha).residueFunction =
      specResidueUnit (CommRingCat.of R)
        (sectionGenerator c Q hQ a ha).subspace.genericPointImage (Polynomial.eval c a)
        (notMem_genericPointImage_sectionGenerator c Q hQ a ha) := by
  refine Units.ext ?_
  rw [RationalFunctionGenerator.residueFunction_val, specResidueUnit_val_eq_residue,
    ← IntegralClosedSubscheme.stalkMap_functionFieldIso]
  have key := stalkMap_spec_algebraMap (CommRingCat.ofHom (sectionQuotientHom (R := R) Q))
    (genericPoint (Spec (CommRingCat.of (Polynomial R ⧸ Q)))) (Polynomial.eval c a)
  rw [show (CommRingCat.ofHom (sectionQuotientHom (R := R) Q)) (Polynomial.eval c a) =
      Ideal.Quotient.mk Q a from sectionQuotientHom_eval c Q hQ a] at key
  exact congrArg _ ((functionFieldUnit_val (CommRingCat.of (Polynomial R ⧸ Q))
    (Ideal.Quotient.mk Q a) (quotientMk_ne_zero Q a ha)).trans key.symm)

end VectorBundle

/-! ## Differences of principal divisors -/

namespace RationalFunctionGenerator

variable {X : Scheme.{u}}

/-- `residueFunction` is multiplicative in the rational function. -/
theorem residueFunction_mul (V : IntegralClosedSubscheme X) (f f' : V.scheme.functionFieldˣ) :
    (RationalFunctionGenerator.mk V (f * f')).residueFunction =
      (RationalFunctionGenerator.mk V f).residueFunction *
        (RationalFunctionGenerator.mk V f').residueFunction :=
  map_mul (Units.map V.functionFieldEquivResidueField.toMonoidHom) f f'

/-- `residueFunction` takes inverses to inverses. -/
theorem residueFunction_inv (V : IntegralClosedSubscheme X) (f : V.scheme.functionFieldˣ) :
    (RationalFunctionGenerator.mk V f⁻¹).residueFunction =
      ((RationalFunctionGenerator.mk V f).residueFunction)⁻¹ :=
  map_inv (Units.map V.functionFieldEquivResidueField.toMonoidHom) f

/-- A difference of two principal divisors on a fixed subvariety is the principal divisor of the
quotient of the two rational functions. -/
theorem divisor_sub (dim : DimensionFunction X) (V : IntegralClosedSubscheme X)
    (f f' : V.scheme.functionFieldˣ) :
    (RationalFunctionGenerator.mk V f).divisor dim -
        (RationalFunctionGenerator.mk V f').divisor dim =
      (RationalFunctionGenerator.mk V (f * f'⁻¹)).divisor dim := by
  rw [divisor_mul, divisor_inv]
  abel

/-- The comparison that the global rank-one argument needs: two differences of principal divisors
built from two integral closed subschemes with the same generic point image agree as soon as the
residue classes of the four rational functions satisfy the cross relation `a · b' = a' · b`. -/
theorem divisor_sub_eq_of_residueFunction_mul_eq (dim : DimensionFunction X)
    (V V' : IntegralClosedSubscheme X) (hξ : V.genericPointImage = V'.genericPointImage)
    (a b : V.scheme.functionFieldˣ) (a' b' : V'.scheme.functionFieldˣ)
    (h : Units.map (X.residueFieldCongr hξ).hom.hom.toMonoidHom
            (RationalFunctionGenerator.mk V a).residueFunction *
          (RationalFunctionGenerator.mk V' b').residueFunction =
        (RationalFunctionGenerator.mk V' a').residueFunction *
          Units.map (X.residueFieldCongr hξ).hom.hom.toMonoidHom
            (RationalFunctionGenerator.mk V b).residueFunction) :
    (RationalFunctionGenerator.mk V a).divisor dim -
        (RationalFunctionGenerator.mk V b).divisor dim =
      (RationalFunctionGenerator.mk V' a').divisor dim -
        (RationalFunctionGenerator.mk V' b').divisor dim := by
  rw [divisor_sub, divisor_sub]
  refine divisor_eq_of_residueFunction_eq dim _ _ hξ ?_
  rw [residueFunction_mul, residueFunction_inv, residueFunction_mul, residueFunction_inv,
    map_mul, map_inv, mul_inv_eq_iff_eq_mul, mul_assoc,
    mul_comm _ (Units.map (X.residueFieldCongr hξ).hom.hom.toMonoidHom
      (RationalFunctionGenerator.mk V b).residueFunction),
    ← mul_assoc, ← h, mul_assoc, mul_inv_cancel, mul_one]

/-- The residue function of the closed image of a generator along a closed immersion `f`
corresponds to the residue function of the generator under the residue field map of `f`. -/
theorem residueFieldMap_residueFunction_closedImage {Y : Scheme.{u}}
    (g : RationalFunctionGenerator X) (f : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsClosedImmersion f] :
    (f.residueFieldMap g.subspace.genericPointImage)
        ((g.closedImage f).residueFunction :
          Y.residueField (g.closedImage f).subspace.genericPointImage) =
      (g.residueFunction : X.residueField g.subspace.genericPointImage) := by
  obtain ⟨b, hb⟩ := (g.subspace.closedImage f).inclusion.stalkMap_surjective
    (genericPoint g.subspace.scheme) (g.function : g.subspace.scheme.functionField)
  have hcomp : (g.subspace.closedImage f).inclusion.stalkMap (genericPoint g.subspace.scheme) b =
      g.subspace.inclusion.stalkMap (genericPoint g.subspace.scheme)
        (f.stalkMap g.subspace.genericPointImage b) := by
    change ((g.subspace.inclusion ≫ f).stalkMap (genericPoint g.subspace.scheme)) b = _
    rw [_root_.AlgebraicGeometry.Scheme.Hom.stalkMap_comp]
    rfl
  have h2 : (g.function : g.subspace.scheme.functionField) =
      g.subspace.inclusion.stalkMap (genericPoint g.subspace.scheme)
        (f.stalkMap g.subspace.genericPointImage b) := hb.symm.trans hcomp
  have hL : (f.residueFieldMap g.subspace.genericPointImage)
        ((g.closedImage f).subspace.functionFieldIso.hom
          ((g.closedImage f).function : (g.closedImage f).subspace.scheme.functionField)) =
      X.residue g.subspace.genericPointImage
        (f.stalkMap g.subspace.genericPointImage b) := by
    rw [show ((g.closedImage f).function : (g.closedImage f).subspace.scheme.functionField) =
      (g.subspace.closedImage f).inclusion.stalkMap (genericPoint g.subspace.scheme) b from hb.symm]
    refine Eq.trans ?_ (residue_residueFieldMap_apply f g.subspace.genericPointImage b)
    exact congrArg _
      (IntegralClosedSubscheme.stalkMap_functionFieldIso (g.subspace.closedImage f) b)
  rw [residueFunction_val, residueFunction_val, hL, h2]
  exact (IntegralClosedSubscheme.stalkMap_functionFieldIso g.subspace _).symm

/-- Unit form of `residueFieldMap_residueFunction_closedImage`. -/
theorem units_map_residueFunction_closedImage {Y : Scheme.{u}}
    (g : RationalFunctionGenerator X) (f : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsClosedImmersion f] :
    Units.map (f.residueFieldMap g.subspace.genericPointImage).hom.toMonoidHom
        (g.closedImage f).residueFunction =
      g.residueFunction :=
  Units.ext (residueFieldMap_residueFunction_closedImage g f)

end RationalFunctionGenerator

end GromovWitten.AlgebraicGeometry.IntersectionTheory
