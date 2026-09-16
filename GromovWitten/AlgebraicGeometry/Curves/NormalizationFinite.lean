/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Curves.Normalization
import GromovWitten.AlgebraicGeometry.NormalizationConductor
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.FieldTheory.Perfect

/-!
# Finiteness of normalization

This file proves that the normalization morphism `Normalization.toCurve X` of an integral scheme
`X` is a *finite* morphism, whenever `X` is locally of finite type over a field of characteristic
zero.  No finiteness supplier structure is used: the result is proved from Noether normalization
and the finiteness of integral closures in finite separable extensions.

## Ring-theoretic core

* `module_finite_integralClosure_fractionRing`: if a domain `A` is a finite module over a
  Noetherian integrally closed domain `R` and the induced extension of fraction fields is
  separable, then the integral closure of `A` in its fraction field is a finite `A`-module.
  This is the general statement; separability of the function-field extension is exactly the
  hypothesis under which Mathlib's trace-form argument (`IsIntegralClosure.finite`) applies, and
  it is genuinely needed for that argument.
* `module_finite_integralClosure_of_charZero`: **finiteness of normalization**, ring version.
  For a domain `A` of finite type over a field `k` of characteristic zero, the integral closure of
  `A` in its fraction field is a finite `A`-module.  Characteristic zero enters only to guarantee
  separability of the extension of the fraction field of a Noether normalization; the
  characteristic-`p` case would additionally require a separating transcendence basis.

## Scheme-level statements

* `isFinite_fromNormalization`: a relative normalization is finite as soon as all the integral
  closures computing it on affine opens are finite modules.
* `module_finite_functionField`: for an integral scheme locally of finite type over a field of
  characteristic zero, the integral closure of the sections on an affine open in the function
  field is a finite module.
* `isFinite_toCurve`: **finiteness of normalization**.  For an integral scheme `X` locally of
  finite type over a field of characteristic zero, `Normalization.toCurve X` is a finite morphism.
* `isIntegrallyClosed_sections`: the sections of the normalization over the preimage of a nonempty
  affine open are integrally closed, i.e. the normalization is normal.
* `conductor_ne_bot`, `sourceIdeal_ne_bot`: the conductor of a ring in its normalization is a
  nonzero ideal as soon as the normalization is module-finite, so the conductor short exact
  sequence of `NormalizationConductor` is supported on a proper closed subscheme.
* `conductor_shortExact_of_charZero`: the combination of the short exact conductor sequence with
  the nonvanishing of both conductor ideals, in the characteristic-zero finite-type case.

## Not proved here

Finiteness of the singular and branch schemes, étaleness of the branch scheme over a separable
residue field, and the construction of a single finite separable extension splitting all branches
are not addressed: they require a scheme-theoretic singular locus and dimension theory for curves,
neither of which exists in this repository or in Mathlib yet.
-/

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

noncomputable section

namespace Normalization

/-! ### Finiteness of integral closures -/

section RingTheory

/-- An isomorphism of algebras restricts to an isomorphism of integral closures. -/
def integralClosureAlgEquiv {A K L : Type u} [CommRing A] [CommRing K] [CommRing L] [Algebra A K]
    [Algebra A L] (e : K ≃ₐ[A] L) : integralClosure A K ≃ₐ[A] integralClosure A L :=
  (Subalgebra.equivMapOfInjective (integralClosure A K) (e : K →ₐ[A] L) e.injective).trans
    (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv e))

/-- Module-finiteness of an integral closure is invariant under isomorphisms of the ambient
algebra. -/
theorem module_finite_integralClosure_of_algEquiv {A K L : Type u} [CommRing A] [CommRing K]
    [CommRing L] [Algebra A K] [Algebra A L] (e : K ≃ₐ[A] L)
    [Module.Finite A (integralClosure A K)] :
    Module.Finite A (integralClosure A L) :=
  Module.Finite.equiv (integralClosureAlgEquiv e).toLinearEquiv

/-- The integral closure of a domain in its fraction field is integrally closed: the
normalization is normal. -/
theorem isIntegrallyClosed_integralClosure (A K : Type u) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] : IsIntegrallyClosed (integralClosure A K) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension (R := A) (K := K) (L := K)

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- If a domain `A` is a finite module over a Noetherian integrally closed domain `R`, and the
extension of fraction fields `Frac R ⊆ Frac A` is separable, then the integral closure of `A` in
its fraction field is a finite `A`-module.

This is the finiteness of normalization in its general (separable) form: the separability
hypothesis is what makes the trace form nondegenerate, and it cannot be dropped without a
different argument. -/
theorem module_finite_integralClosure_fractionRing (R A : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing A] [IsDomain A] [Algebra R A]
    [Module.Finite R A] [FaithfulSMul R A]
    [Algebra.IsSeparable (FractionRing R) (FractionRing A)] :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  have : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  -- the integral closure of `A` in `Frac A` is also the integral closure of `R`
  have hic : IsIntegralClosure (integralClosure A (FractionRing A)) R (FractionRing A) := by
    refine ⟨Subtype.val_injective, fun {x} ↦ ⟨fun hx ↦ ⟨⟨x, hx.tower_top⟩, rfl⟩, ?_⟩⟩
    rintro ⟨y, rfl⟩
    exact isIntegral_trans _ y.2
  have : Module.Finite R (integralClosure A (FractionRing A)) :=
    IsIntegralClosure.finite R (FractionRing R) (FractionRing A) _
  exact Module.Finite.of_restrictScalars_finite R A _

/-- **Finiteness of normalization**, ring version.  For a domain `A` of finite type over a field
of characteristic zero, the integral closure of `A` in its fraction field is a finite
`A`-module. -/
theorem module_finite_integralClosure_of_charZero (k A : Type u) [Field k] [CharZero k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  -- a Noether normalization `k[X₁, …, X_s] ↪ A`
  let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : IsIntegrallyClosed (MvPolynomial (Fin s) k) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  exact module_finite_integralClosure_fractionRing (MvPolynomial (Fin s) k) A

/-- **Finiteness of normalization** for an arbitrary fraction field. -/
theorem module_finite_integralClosure_of_charZero' (k A K : Type u) [Field k] [CharZero k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra A K]
    [IsFractionRing A K] :
    Module.Finite A (integralClosure A K) := by
  have := module_finite_integralClosure_of_charZero k A
  exact module_finite_integralClosure_of_algEquiv (FractionRing.algEquiv A K)

/-- The conductor of a domain in its integral closure is a nonzero ideal whenever that integral
closure is a finite module: a common denominator for finitely many module generators multiplies
the whole integral closure into the ring. -/
theorem exists_ne_zero_mem_sourceIdeal (A K : Type u) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Module.Finite A (integralClosure A K)] :
    ∃ a : A, a ≠ 0 ∧ a ∈ NormalizationConductor.sourceIdeal A K := by
  classical
  obtain ⟨T, hT⟩ := ‹Module.Finite A (integralClosure A K)›
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) T
    (fun t : integralClosure A K ↦ (t : K))
  refine ⟨(b : A), nonZeroDivisors.ne_zero b.2, ?_⟩
  -- the elements multiplied into `A` by `b` form a submodule containing the generators
  set N : Submodule A (integralClosure A K) :=
    (LinearMap.range (Algebra.linearMap A (integralClosure A K))).comap
      (LinearMap.mulLeft A (algebraMap A (integralClosure A K) (b : A)))
  have hTN : (T : Set (integralClosure A K)) ⊆ (N : Set (integralClosure A K)) := by
    intro t ht
    obtain ⟨x, hx⟩ := hb t ht
    refine ⟨x, ?_⟩
    apply Subtype.ext
    have hx' : algebraMap A K x = (b : A) • (t : K) := hx
    simpa [Algebra.smul_def] using hx'
  have hle : (⊤ : Submodule A (integralClosure A K)) ≤ N := by
    rw [← hT]
    exact Submodule.span_le.mpr hTN
  intro c
  obtain ⟨x, hx⟩ := hle (Submodule.mem_top (x := c))
  exact ⟨x, hx⟩

/-- The conductor ideal of the normalization is nonzero for a finite integral closure. -/
theorem sourceIdeal_ne_bot (A K : Type u) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Module.Finite A (integralClosure A K)] :
    NormalizationConductor.sourceIdeal A K ≠ ⊥ := by
  obtain ⟨a, ha, hmem⟩ := exists_ne_zero_mem_sourceIdeal A K
  intro h
  rw [h, Ideal.mem_bot] at hmem
  exact ha hmem

/-- The conductor ideal inside the normalization is nonzero for a finite integral closure. -/
theorem conductor_ne_bot (A K : Type u) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Module.Finite A (integralClosure A K)] :
    NormalizationConductor.ideal A K ≠ ⊥ := by
  obtain ⟨a, ha, hmem⟩ := exists_ne_zero_mem_sourceIdeal A K
  intro h
  have hmem' : algebraMap A (integralClosure A K) a ∈ NormalizationConductor.ideal A K := hmem
  rw [h, Ideal.mem_bot] at hmem'
  refine ha (IsFractionRing.injective A K ?_)
  have : ((algebraMap A (integralClosure A K) a : integralClosure A K) : K) = algebraMap A K a :=
    rfl
  rw [← this, hmem']
  simp

/-- The map from a domain to its integral closure in a fraction field is injective. -/
theorem algebraMap_integralClosure_injective (A K : Type u) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] :
    Function.Injective (algebraMap A (integralClosure A K)) := by
  intro x y hxy
  refine IsFractionRing.injective A K ?_
  have hx : ((algebraMap A (integralClosure A K) x : integralClosure A K) : K) =
      algebraMap A K x := rfl
  have hy : ((algebraMap A (integralClosure A K) y : integralClosure A K) : K) =
      algebraMap A K y := rfl
  rw [← hx, ← hy, hxy]

/-- **The conductor sequence of a normalization in characteristic zero.**  For a domain `A` of
finite type over a field of characteristic zero with fraction field `K`, the conductor square
sequence `0 → A → B × A/I → B/J → 0` of `A` inside its normalization `B = integralClosure A K`
is short exact, and both conductor ideals are nonzero, so the sequence is concentrated on a
proper closed subscheme of `Spec A`. -/
theorem conductor_shortExact_of_charZero (k A K : Type u) [Field k] [CharZero k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra A K]
    [IsFractionRing A K] :
    (Function.Injective
        (RingHomConductor.diagonal (algebraMap A (integralClosure A K))) ∧
      Function.Exact
          (RingHomConductor.diagonal (algebraMap A (integralClosure A K)))
          (RingHomConductor.difference (algebraMap A (integralClosure A K))) ∧
        Function.Surjective
          (RingHomConductor.difference (algebraMap A (integralClosure A K)))) ∧
      NormalizationConductor.ideal A K ≠ ⊥ ∧
        NormalizationConductor.sourceIdeal A K ≠ ⊥ := by
  have := module_finite_integralClosure_of_charZero' k A K
  exact ⟨NormalizationConductor.shortExact A K (algebraMap_integralClosure_injective A K),
    conductor_ne_bot A K, sourceIdeal_ne_bot A K⟩

end RingTheory

/-! ### Finiteness of the normalization morphism -/

section Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The generic point of an integral scheme lies in every nonempty open. -/
theorem genericPoint_mem_of_nonempty (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- The function-field point meets every nonempty open in the whole of `Spec` of the function
field. -/
theorem preimage_genericPointMap_eq_top (U : X.Opens) [Nonempty U] :
    genericPointMap X ⁻¹ᵁ U = ⊤ := by
  apply TopologicalSpace.Opens.ext
  apply Set.eq_univ_of_forall
  intro s
  change (genericPointMap X).base s ∈ U
  have hmem : (genericPointMap X).base s ∈
      Set.range (X.fromSpecStalk (genericPoint X)).base := ⟨s, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hmem
  exact hmem.mem_open U.isOpen (genericPoint_mem_of_nonempty X U)

/-- The sections of the function-field point over the preimage of a nonempty open are the
function field. -/
def genericSectionsIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, genericPointMap X ⁻¹ᵁ U) ≅ X.functionField :=
  (Spec X.functionField).presheaf.mapIso
      (eqToIso (preimage_genericPointMap_eq_top X U).symm).op ≪≫
    Scheme.ΓSpecIso X.functionField

/-- Under the identification of `genericSectionsIso`, the structure map of the function-field
point is the germ map into the function field. -/
theorem genericPointMap_app_genericSectionsIso (U : X.Opens) [Nonempty U] :
    (genericPointMap X).app U ≫ (genericSectionsIso X U).hom =
      X.presheaf.germ U (genericPoint X) (genericPoint_mem_of_nonempty X U) := by
  change (X.fromSpecStalk (genericPoint X)).app U ≫ _ = _
  rw [Scheme.fromSpecStalk_app (genericPoint_mem_of_nonempty X U)]
  have h1 : (Spec X.functionField).presheaf.map (homOfLE le_top).op ≫
      (Spec X.functionField).presheaf.map
        (eqToHom (preimage_genericPointMap_eq_top X U).symm).op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp]
    convert (Spec X.functionField).presheaf.map_id _
    exact Subsingleton.elim _ _
  simp only [genericSectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    Category.assoc]
  rw [reassoc_of% h1]
  simp

/-- The function field is isomorphic, as an algebra over the sections on a nonempty open `U`, to
the sections of the function-field point over the preimage of `U`. -/
def functionFieldAlgEquiv (U : X.Opens) [Nonempty U] :
    letI := ((genericPointMap X).app U).hom.toAlgebra
    X.functionField ≃ₐ[Γ(X, U)] Γ(Spec X.functionField, genericPointMap X ⁻¹ᵁ U) :=
  letI := ((genericPointMap X).app U).hom.toAlgebra
  { (genericSectionsIso X U).symm.commRingCatIsoToRingEquiv with
    commutes' := fun a ↦ by
      have h := congrArg (fun φ : Γ(X, U) ⟶ X.functionField ↦ φ.hom a)
        (genericPointMap_app_genericSectionsIso X U)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
      change (genericSectionsIso X U).inv.hom _ = _
      rw [show (algebraMap Γ(X, U) X.functionField) a =
        (X.presheaf.germ U (genericPoint X) (genericPoint_mem_of_nonempty X U)).hom a from rfl,
        ← h]
      change ((genericSectionsIso X U).hom ≫ (genericSectionsIso X U).inv).hom _ = _
      simp
      rfl }

/-- **Normality of the normalization.**  The sections of the normalization over the preimage of a
nonempty affine open are an integrally closed domain, namely the integral closure of the sections
of `X` in the function field. -/
theorem isIntegrallyClosed_sections (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(scheme X, toCurve X ⁻¹ᵁ U) := by
  let _ := ((genericPointMap X).app U).hom.toAlgebra
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have h1 : IsIntegrallyClosed (integralClosure Γ(X, U) X.functionField) :=
    isIntegrallyClosed_integralClosure Γ(X, U) X.functionField
  have h2 : IsIntegrallyClosed
      (integralClosure Γ(X, U) Γ(Spec X.functionField, genericPointMap X ⁻¹ᵁ U)) :=
    IsIntegrallyClosed.of_equiv
      (integralClosureAlgEquiv (functionFieldAlgEquiv X U)).toRingEquiv
  exact IsIntegrallyClosed.of_equiv
    ((genericPointMap X).normalizationObjIso hU).symm.commRingCatIsoToRingEquiv

set_option backward.isDefEq.respectTransparency false in
/-- A relative normalization is a finite morphism as soon as all the integral closures computing
it over affine opens are finite modules. -/
theorem isFinite_fromNormalization {Y Z : Scheme.{u}} (f : Y ⟶ Z) [QuasiCompact f]
    [QuasiSeparated f]
    (H : ∀ U : Z.affineOpens, letI := (f.app U.1).hom.toAlgebra
      Module.Finite Γ(Z, U.1) (integralClosure Γ(Z, U.1) Γ(Y, f ⁻¹ᵁ U.1))) :
    IsFinite f.fromNormalization := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _
    (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (f.fromNormalization ⁻¹ᵁ U).ι
      (f.normalizationOpenCover.f U)
      (by simpa using congr($(f.fromNormalization_preimage U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _ U.2.isoSpec.hom]
  have : (f.normalizationDiagramMap.app (.op U)).hom.Finite := by
    let := (f.app U).hom.toAlgebra
    change (algebraMap Γ(Z, U) (integralClosure Γ(Z, U) Γ(Y, f ⁻¹ᵁ U))).Finite
    rw [RingHom.finite_algebraMap]
    exact H U
  convert! (IsFinite.SpecMap_iff _).mpr this
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, Scheme.Hom.ι_fromNormalization]

variable (k : Type u) [Field k] [CharZero k]

/-- On a nonempty affine open of an integral scheme locally of finite type over a field of
characteristic zero, the integral closure in the function field is a finite module. -/
theorem module_finite_functionField (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (U : X.affineOpens) [Nonempty U.1] :
    Module.Finite Γ(X, U.1) (integralClosure Γ(X, U.1) X.functionField) := by
  let _ : Algebra k Γ(X, U.1) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U.1 le_top).hom.toAlgebra
  have hft : Algebra.FiniteType k Γ(X, U.1) := by
    change RingHom.FiniteType _
    rw [CommRingCat.hom_comp]
    refine RingHom.FiniteType.comp ?_ ?_
    · exact HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_›
        ⟨⊤, isAffineOpen_top _⟩ U le_top
    · exact RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso (CommRingCat.of k)).inv).surjective
  have : IsFractionRing Γ(X, U.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  exact module_finite_integralClosure_of_charZero' k Γ(X, U.1) X.functionField

/-- **Finiteness of normalization.**  The normalization morphism of an integral scheme that is
locally of finite type over a field of characteristic zero is a finite morphism. -/
theorem isFinite_toCurve (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    IsFinite (toCurve X) := by
  apply isFinite_fromNormalization
  intro U
  let _ : Algebra Γ(X, U.1) Γ(Spec X.functionField, genericPointMap X ⁻¹ᵁ U.1) :=
    ((genericPointMap X).app U.1).hom.toAlgebra
  change Module.Finite Γ(X, U.1) (integralClosure Γ(X, U.1) _)
  rcases (U.1 : Set X).eq_empty_or_nonempty with h | h
  · -- an empty affine open has the zero ring as sections
    have hU : U.1 = ⊥ := SetLike.ext' h
    have hsub : Subsingleton Γ(X, U.1) := hU ▸ inferInstance
    have := Module.subsingleton Γ(X, U.1)
      (integralClosure Γ(X, U.1) Γ(Spec X.functionField, genericPointMap X ⁻¹ᵁ U.1))
    exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩
  · have : Nonempty U.1 := h.to_subtype
    have := module_finite_functionField X k f U
    exact module_finite_integralClosure_of_algEquiv (functionFieldAlgEquiv X U.1)

/-- The normalization morphism of an integral scheme locally of finite type over a field of
characteristic zero is affine, being finite. -/
theorem isAffineHom_toCurve (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    IsAffineHom (toCurve X) :=
  have := isFinite_toCurve X k f
  inferInstance

/-- The normalization morphism of an integral scheme locally of finite type over a field of
characteristic zero is locally of finite type, being finite. -/
theorem locallyOfFiniteType_toCurve (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] : LocallyOfFiniteType (toCurve X) :=
  have := isFinite_toCurve X k f
  inferInstance

end Scheme

end Normalization

end

end GromovWitten.AlgebraicGeometry.Curves
