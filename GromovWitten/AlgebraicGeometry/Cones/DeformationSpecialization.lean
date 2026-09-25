/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Cones.DeformationSpaceGeometry
import GromovWitten.AlgebraicGeometry.Curves.CartierDivisors

/-!
# Quotient deformations and the input for specialization

Let `P` be the ideal of a closed subscheme of `Spec R`, and put
`B = R ⧸ P`.  The coefficientwise Laurent map induces the actual comparison

`R[It,t⁻¹] ⟶ B[(IB)t,t⁻¹]`.

The map is surjective, including when `P` is prime and the closed subscheme is
integral.  Its kernel is recorded coefficientwise; this is the correct kernel
without a flatness or Tor-independence hypothesis.  Passing to the parameter
quotients gives the closed immersion of the special normal cones, while
inverting the parameter gives the map on the generic trivial families.
-/

open CategoryTheory Limits AlgebraicGeometry LaurentPolynomial
open scoped TensorProduct

namespace GromovWitten
namespace AlgebraicGeometry

universe u

noncomputable section

namespace AffineDeformationSpace

section Quotient

variable (R : Type u) [CommRing R] (I : Ideal R) (P : Ideal R)

local notation "q" => (Ideal.Quotient.mk P : R →+* (R ⧸ P))

/-- The extended Rees algebra of the closed subscheme cut out by `P`. -/
abbrev quotientExtendedRees : Type u :=
  extendedRees (R ⧸ P) (I.map q)

/-- The coefficientwise comparison map for the deformation of the closed subscheme. -/
def quotientExtendedReesHom : extendedRees R I →+* quotientExtendedRees R I P :=
  reesBaseChangeHom R I (R ⧸ P)

@[simp]
theorem quotientExtendedReesHom_coe (f : extendedRees R I) :
    ((quotientExtendedReesHom R I P f : quotientExtendedRees R I P) :
        (R ⧸ P)[T;T⁻¹]) = mapLaurent q (f : R[T;T⁻¹]) :=
  rfl

@[simp]
theorem quotientExtendedReesHom_C_mul_T (a : R) (n : ℤ)
    (ha : a ∈ I ^ n.toNat) :
    quotientExtendedReesHom R I P
        ⟨LaurentPolynomial.C a * T n, isExtendedRees_C_mul_T R I ha⟩ =
      ⟨LaurentPolynomial.C (q a) * T n,
        isExtendedRees_C_mul_T (R ⧸ P) (I.map q)
          (by
            rw [← Ideal.map_pow]
            exact Ideal.mem_map_of_mem q ha)⟩ := by
  apply Subtype.ext
  rw [quotientExtendedReesHom_coe, mapLaurent_C_mul_T]

/-- The quotient comparison map is onto.  Its factorization through the tensor product
uses surjectivity of the coefficient quotient and of the canonical Rees tensor map. -/
theorem quotientExtendedReesHom_surjective :
    Function.Surjective (quotientExtendedReesHom R I P) := by
  have hleft : Function.Surjective
      (Algebra.TensorProduct.includeLeft :
        extendedRees R I →ₐ[R] (extendedRees R I) ⊗[R] (R ⧸ P)) :=
    Algebra.TensorProduct.includeLeft_surjective R (extendedRees R I) Ideal.Quotient.mk_surjective
  intro y
  obtain ⟨z, hz⟩ := reesTensorMap_surjective R I (R ⧸ P) y
  obtain ⟨x, rfl⟩ := hleft z
  refine ⟨x, ?_⟩
  rw [← hz]
  apply Subtype.ext
  change mapLaurent q (x : R[T;T⁻¹]) = _
  rw [coe_reesTensorMap]
  change mapLaurent q (x : R[T;T⁻¹]) =
    reesTensorToLaurent R I (R ⧸ P) (x ⊗ₜ[R] 1)
  rw [reesTensorToLaurent_tmul]
  simp

/-- Exact kernel description for the deformation of a quotient: an extended-Rees element
vanishes precisely when every Laurent coefficient lies in `P`. -/
theorem quotientExtendedReesHom_mem_ker_iff (f : extendedRees R I) :
    f ∈ RingHom.ker (quotientExtendedReesHom R I P) ↔
      ∀ n : ℤ, (f : R[T;T⁻¹]).coeff n ∈ P := by
  constructor
  · intro hf n
    have hzero : mapLaurent q (f : R[T;T⁻¹]) = 0 := by
      have := congrArg Subtype.val hf
      exact this
    have hc := congrArg (fun z : (R ⧸ P)[T;T⁻¹] ↦ z.coeff n) hzero
    rw [coeff_mapLaurent] at hc
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hc)
  · intro hf
    apply RingHom.mem_ker.mpr
    apply Subtype.ext
    change mapLaurent q (f : R[T;T⁻¹]) = 0
    apply AddMonoidAlgebra.ext
    ext n
    change (mapLaurent q (f : R[T;T⁻¹])).coeff n = 0
    rw [coeff_mapLaurent]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hf n)

@[simp]
theorem quotientExtendedReesHom_parameter :
    quotientExtendedReesHom R I P (parameter R I) =
      parameter (R ⧸ P) (I.map q) := by
  apply Subtype.ext
  change mapLaurent q (T (-1)) = T (-1)
  calc
    mapLaurent q (T (-1)) =
        mapLaurent q (LaurentPolynomial.C (1 : R) * T (-1)) := by simp
    _ = LaurentPolynomial.C (q 1) * T (-1) := mapLaurent_C_mul_T q 1 (-1)
    _ = T (-1) := by simp

/-- The map induced by the quotient comparison on the special fibres. -/
def quotientSpecialFibreMap :
    specialFibreRing R I →+* specialFibreRing (R ⧸ P) (I.map q) :=
  Ideal.quotientMap (parameterIdeal (R ⧸ P) (I.map q))
    (quotientExtendedReesHom R I P) (by
      rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      change quotientExtendedReesHom R I P (parameter R I) ∈
        parameterIdeal (R ⧸ P) (I.map q)
      rw [quotientExtendedReesHom_parameter]
      exact Ideal.mem_span_singleton_self _)

@[simp]
theorem quotientSpecialFibreMap_mk (f : extendedRees R I) :
    quotientSpecialFibreMap R I P (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (quotientExtendedReesHom R I P f) := by
  exact Ideal.quotientMap_mk

/-- The induced map on special fibres is onto. -/
theorem quotientSpecialFibreMap_surjective :
    Function.Surjective (quotientSpecialFibreMap R I P) := by
  apply Ideal.quotientMap_surjective
  exact quotientExtendedReesHom_surjective R I P

theorem quotientSpecialFibreMap_comp_mk :
    (quotientSpecialFibreMap R I P).comp (Ideal.Quotient.mk (parameterIdeal R I)) =
      (Ideal.Quotient.mk (parameterIdeal (R ⧸ P) (I.map q))).comp
        (quotientExtendedReesHom R I P) := by
  exact Ideal.quotientMap_comp_mk _

/-! ### The actual deformation and normal-cone maps -/

/-- The closed immersion of the deformation of `Spec (R ⧸ P)` into the deformation of `Spec R`.
The map is the spectrum of the coefficientwise extended-Rees quotient map. -/
def quotientDeformationMap :
    space (R ⧸ P) (I.map q) ⟶ space R I :=
  Spec.map (CommRingCat.ofHom (quotientExtendedReesHom R I P))

instance quotientDeformationMap_isClosedImmersion :
    IsClosedImmersion (quotientDeformationMap R I P) :=
  IsClosedImmersion.spec_of_surjective _ (quotientExtendedReesHom_surjective R I P)

/-- The closed immersion of the special fibre of the quotient deformation. -/
def quotientSpecialFibreSchemeMap :
    specialFibre (R ⧸ P) (I.map q) ⟶ specialFibre R I :=
  Spec.map (CommRingCat.ofHom (quotientSpecialFibreMap R I P))

instance quotientSpecialFibreSchemeMap_isClosedImmersion :
    IsClosedImmersion (quotientSpecialFibreSchemeMap R I P) :=
  IsClosedImmersion.spec_of_surjective _ (quotientSpecialFibreMap_surjective R I P)

/-- The normal-cone map obtained from the actual special-fibre quotient maps. -/
def quotientNormalConeMap :
    AffineNormalCone.scheme (R ⧸ P) (I.map q) ⟶ AffineNormalCone.scheme R I :=
  (normalConeIsoSpecialFibre (R ⧸ P) (I.map q)).hom ≫
    quotientSpecialFibreSchemeMap R I P ≫
    (normalConeIsoSpecialFibre R I).inv

instance quotientNormalConeMap_isClosedImmersion :
    IsClosedImmersion (quotientNormalConeMap R I P) := by
  unfold quotientNormalConeMap
  infer_instance

theorem quotientNormalConeMap_comp_normalConeι :
    quotientNormalConeMap R I P ≫ normalConeι R I =
      normalConeι (R ⧸ P) (I.map q) ≫ quotientDeformationMap R I P := by
  unfold quotientNormalConeMap normalConeι quotientSpecialFibreSchemeMap quotientDeformationMap
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  unfold specialFibreι
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, quotientSpecialFibreMap_comp_mk]

/-! ### Generic fibre and Cartier parameter -/

/-- The map on the generic trivial families `Spec (R ⧸ P)[t,t⁻¹] → Spec R[t,t⁻¹]`. -/
def quotientGenericFibreMap :
    genericFibre (R ⧸ P) ⟶ genericFibre R :=
  Spec.map (CommRingCat.ofHom (mapLaurent q))

theorem quotientGenericFibreMap_comp_genericFibreι :
    quotientGenericFibreMap R P ≫ genericFibreι R I =
      genericFibreι (R ⧸ P) (I.map q) ≫ quotientDeformationMap R I P := by
  unfold quotientGenericFibreMap genericFibreι quotientDeformationMap
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 1

/-- The global parameter equation on the affine deformation space. -/
def parameterSection :
    Γ(space R I, ⊤) :=
  (Scheme.ΓSpecIso (.of (extendedRees R I))).inv (parameter R I)

theorem parameterSection_isRegular : IsRegular (parameterSection R I) := by
  apply Curves.isRegular_map_of_flat
    (Scheme.ΓSpecIso (.of (extendedRees R I))).inv.hom
  · exact RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of (extendedRees R I))).inv)
  · apply (Commute.isRegular_iff (fun _ ↦ Commute.all _ _)).2
    intro b hb
    apply (parameter_isSMulRegular R I)

/-- The special fibre is packaged as a genuine effective Cartier divisor, using the regular
parameter of the extended Rees algebra. -/
def specialFibreCartierDivisor :
    Curves.EffectiveCartierDivisor (space R I) :=
  Curves.EffectiveCartierDivisor.ofGlobalEquation (space R I)
    (parameterSection R I) (parameterSection_isRegular R I)

@[simp]
theorem specialFibreCartierDivisor_ideal_top :
    (specialFibreCartierDivisor R I).idealSheaf.ideal
        ⟨⊤, isAffineOpen_top (space R I)⟩ =
      Ideal.span {parameterSection R I} := by
  exact Curves.EffectiveCartierDivisor.ofGlobalEquation_ideal_top _ _ _

/-- The ideal of the actual special-fibre immersion is generated by the parameter section. -/
theorem specialFibreι_ker_appTop :
    RingHom.ker (specialFibreι R I).appTop.hom = Ideal.span {parameterSection R I} := by
  let e := Scheme.ΓSpecIso (.of (extendedRees R I))
  let e₀ := Scheme.ΓSpecIso (.of (specialFibreRing R I))
  let parameterQuotient := CommRingCat.ofHom (Ideal.Quotient.mk (parameterIdeal R I))
  have hnat : parameterQuotient ≫ e₀.inv = e.inv ≫ (specialFibreι R I).appTop :=
    Scheme.ΓSpecIso_inv_naturality parameterQuotient
  have happ : (specialFibreι R I).appTop = e.hom ≫ parameterQuotient ≫ e₀.inv := by
    rw [← cancel_epi e.inv]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hnat.symm
  have hr := congrArg CommRingCat.Hom.hom happ
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at hr
  rw [hr]
  change RingHom.ker (e₀.commRingCatIsoToRingEquiv.symm.toRingHom.comp
    (parameterQuotient.hom.comp e.hom.hom)) = _
  rw [RingHom.ker_equiv_comp, ← RingHom.comap_ker]
  change Ideal.comap e.commRingCatIsoToRingEquiv.toRingHom (RingHom.ker parameterQuotient.hom) = _
  have hq : RingHom.ker parameterQuotient.hom = parameterIdeal R I := by
    ext z
    exact Ideal.Quotient.eq_zero_iff_mem
  calc
    _ = Ideal.map e.commRingCatIsoToRingEquiv.symm.toRingHom
        (RingHom.ker parameterQuotient.hom) :=
      (Ideal.map_symm e.commRingCatIsoToRingEquiv).symm
    _ = _ := by
      rw [hq, Ideal.map_span, Set.image_singleton]
      rfl

/-- The kernel ideal sheaf agrees with the constructed Cartier divisor, not just its support. -/
theorem specialFibreι_ker :
    (specialFibreι R I).ker = (specialFibreCartierDivisor R I).idealSheaf := by
  rw [Scheme.ker_of_isAffine, specialFibreι_ker_appTop]
  rfl

/-- The special fibre is the closed subscheme of the actual parameter Cartier divisor. -/
def specialFibreCartierIso :
    specialFibre R I ≅ (specialFibreCartierDivisor R I).subscheme :=
  Curves.EffectiveCartierDivisor.closedImmersionSubschemeIsoOfKerEq
    (specialFibreι R I) (specialFibreCartierDivisor R I).idealSheaf
    (specialFibreι_ker R I)

@[reassoc (attr := simp)]
theorem specialFibreCartierIso_hom_ι :
    (specialFibreCartierIso R I).hom ≫ (specialFibreCartierDivisor R I).ι =
      specialFibreι R I :=
  Curves.EffectiveCartierDivisor.closedImmersionSubschemeIsoOfKerEq_hom_subschemeι
    (specialFibreι R I) (specialFibreCartierDivisor R I).idealSheaf
    (specialFibreι_ker R I)

end Quotient

end AffineDeformationSpace

end

end AlgebraicGeometry
end GromovWitten
