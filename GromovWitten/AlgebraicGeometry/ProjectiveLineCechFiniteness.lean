/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.LaurentCechIntersection
import GromovWitten.Algebra.PolynomialLocalizationKernel
import GromovWitten.AlgebraicGeometry.ProjectiveLineSections

/-!
# Finiteness of the standard projective-line Čech differential

The two chart restrictions are treated as actual maps on section modules.  The
results here establish finite kernel and finite cokernel over the base ring
under finite-presentation and quasi-coherence hypotheses.
-/

open CategoryTheory AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.ProjectiveLine
open scoped LaurentPolynomial
open LaurentPolynomial
open Polynomial
universe u
noncomputable section

namespace GromovWitten.AlgebraicGeometry.ProjectiveLine

variable (R : Type u) [CommRing R]

/-- Chart sections viewed as modules over the base ring. -/
abbrev chartSectionsBase (M : (scheme R).Modules) (b : Bool) : ModuleCat R :=
  (ModuleCat.restrictScalars (algebraMap R (Polynomial R))).obj (chartSections R M b)

/-- Overlap sections viewed as modules over the base ring. -/
abbrev overlapSectionsBase (M : (scheme R).Modules) : ModuleCat R :=
  (ModuleCat.restrictScalars (algebraMap R (overlapRing R))).obj (overlapSections R M)

local instance (P : ModuleCat (Polynomial R)) : Module R P :=
  Module.compHom P (algebraMap R (Polynomial R))

local instance (P : ModuleCat (Polynomial R)) : IsScalarTower R (Polynomial R) P :=
  IsScalarTower.of_compHom R (Polynomial R) P

local instance (Q : ModuleCat (overlapRing R)) : Module R Q :=
  Module.compHom Q (algebraMap R (overlapRing R))

local instance (Q : ModuleCat (overlapRing R)) : Module R[T;T⁻¹] Q :=
  Module.compHom Q (overlapLaurentEquiv R).symm.toRingHom

local instance : IsScalarTower R (Polynomial R) R[T;T⁻¹] :=
  IsScalarTower.of_algebraMap_eq fun r => by
    rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.algebraMap_eq,
      Polynomial.toLaurent_C, LaurentPolynomial.C_eq_algebraMap]

lemma overlapSectionsBase_isScalarTower (M : (scheme R).Modules) :
    IsScalarTower R R[T;T⁻¹] (overlapSections R M) := by
  constructor
  intro r t x
  change (overlapLaurentEquiv R).symm (r • t) • x =
    (algebraMap R (overlapRing R) r) • ((overlapLaurentEquiv R).symm t • x)
  rw [Algebra.smul_def, map_mul, mul_smul]
  congr 1
  exact (AlgEquiv.restrictScalars R (overlapLaurentEquiv R).symm).commutes r

private def restrictionBaseMap (P : ModuleCat (Polynomial R)) (Q : ModuleCat (overlapRing R))
    (χ : Polynomial R →+* overlapRing R)
    (hc : ∀ r : R, χ (Polynomial.C r) = algebraMap R (overlapRing R) r)
    (f : P ⟶ (ModuleCat.restrictScalars χ).obj Q) : P →ₗ[R] Q where
  toFun := f
  map_add' := f.hom.map_add
  map_smul' := by
    intro r x
    change f ((algebraMap R (Polynomial R) r) • x) =
      (algebraMap R (overlapRing R) r) • f x
    rw [f.hom.map_smul]
    change χ (Polynomial.C r) • f x = (algebraMap R (overlapRing R) r) • f x
    rw [hc]

private lemma restrictionBaseMap_intertwines_X
    (P : ModuleCat (Polynomial R)) (Q : ModuleCat (overlapRing R))
    (χ : Polynomial R →+* overlapRing R)
    (hc : ∀ r : R, χ (Polynomial.C r) = algebraMap R (overlapRing R) r)
    (f : P ⟶ (ModuleCat.restrictScalars χ).obj Q) (ε : ℤ)
    (hX : overlapLaurentEquiv R (χ Polynomial.X) = T ε) (x : P) :
    restrictionBaseMap R P Q χ hc f ((Polynomial.X : Polynomial R) • x) =
      (T ε : R[T;T⁻¹]) • restrictionBaseMap R P Q χ hc f x := by
  change f ((Polynomial.X : Polynomial R) • x) =
    (overlapLaurentEquiv R).symm (T ε) • f x
  rw [f.hom.map_smul]
  change χ Polynomial.X • f x = (overlapLaurentEquiv R).symm (T ε) • f x
  congr 1
  apply (overlapLaurentEquiv R).injective
  rw [hX, AlgEquiv.apply_symm_apply]

private lemma restrictionBaseMap_clears_denominators
    (P : ModuleCat (Polynomial R)) (Q : ModuleCat (overlapRing R))
    (χ : Polynomial R →+* overlapRing R)
    (hc : ∀ r : R, χ (Polynomial.C r) = algebraMap R (overlapRing R) r)
    (f : P ⟶ (ModuleCat.restrictScalars χ).obj Q) (ε : ℤ)
    (hX : overlapLaurentEquiv R (χ Polynomial.X) = T ε)
    [IsLocalizedModule (.powers (Polynomial.X : Polynomial R)) f.hom] (x : Q) :
    ∃ n : ℕ, (T ((n : ℤ) * ε) : R[T;T⁻¹]) • x ∈
      (restrictionBaseMap R P Q χ hc f).range := by
  obtain ⟨⟨p, s⟩, hs⟩ := IsLocalizedModule.surj
    (.powers (Polynomial.X : Polynomial R)) f.hom x
  obtain ⟨n, hn⟩ := s.property
  refine ⟨n, p, ?_⟩
  have he : (overlapLaurentEquiv R).symm (T ((n : ℤ) * ε)) =
      χ (Polynomial.X ^ n) := by
    apply (overlapLaurentEquiv R).injective
    rw [AlgEquiv.apply_symm_apply, map_pow, map_pow, hX, T_pow]
  change f p = (overlapLaurentEquiv R).symm (T ((n : ℤ) * ε)) • x
  rw [he]
  change χ (s : Polynomial R) • x = f p at hs
  rw [← hn] at hs
  exact hs.symm

lemma chartZero_c_eq_algebraMap (r : R) :
    (algebraMap (Polynomial R) (overlapRing R)) (Polynomial.C r) =
      algebraMap R (overlapRing R) r := by
  change (algebraMap (Polynomial R) (overlapRing R))
      ((algebraMap R (Polynomial R)) r) = _
  exact (IsScalarTower.algebraMap_apply R (Polynomial R) (overlapRing R) r).symm

lemma chartOne_c_eq_algebraMap (r : R) :
    flipHom R (Polynomial.C r) = algebraMap R (overlapRing R) r := by
  rw [flipHom_C]
  exact chartZero_c_eq_algebraMap R r

/-- The first chart restriction, made linear over the base ring. -/
def chartZeroRestrictionLinear (M : (scheme R).Modules) :
    (chartSections R M false : Type u) →ₗ[R] overlapSections R M :=
  restrictionBaseMap R (chartSections R M false) (overlapSections R M)
    (algebraMap (Polynomial R) (overlapRing R)) (chartZero_c_eq_algebraMap R)
    (chartZeroRestrictionMap R M)

/-- The second chart restriction, made linear over the base ring. -/
def chartOneRestrictionLinear (M : (scheme R).Modules) :
    (chartSections R M true : Type u) →ₗ[R] overlapSections R M :=
  restrictionBaseMap R (chartSections R M true) (overlapSections R M)
    (flipHom R) (chartOne_c_eq_algebraMap R)
    (chartOneRestrictionMap R M)

private lemma restrictionBaseMap_finite_ker [IsNoetherianRing R]
    (P : ModuleCat (Polynomial R)) (Q : ModuleCat (overlapRing R))
    [Module.Finite (Polynomial R) P]
    (χ : Polynomial R →+* overlapRing R)
    (hc : ∀ r : R, χ (Polynomial.C r) = algebraMap R (overlapRing R) r)
    (f : P ⟶ (ModuleCat.restrictScalars χ).obj Q)
    [IsLocalizedModule (.powers (Polynomial.X : Polynomial R)) f.hom] :
    Module.Finite R (restrictionBaseMap R P Q χ hc f).ker := by
  have : Module.Finite R f.hom.ker := f.hom.finite_ker_of_polynomial_localization
  let e : f.hom.ker ≃ₗ[R] (restrictionBaseMap R P Q χ hc f).ker :=
    LinearEquiv.refl R _
  exact Module.Finite.equiv e

lemma chartZeroRestrictionLinear_intertwines_X
    (M : (scheme R).Modules) (x : chartSections R M false) :
    chartZeroRestrictionLinear R M ((Polynomial.X : Polynomial R) • x) =
      (T 1 : R[T;T⁻¹]) • chartZeroRestrictionLinear R M x := by
  exact restrictionBaseMap_intertwines_X R (chartSections R M false)
    (overlapSections R M) (algebraMap (Polynomial R) (overlapRing R))
    (chartZero_c_eq_algebraMap R) (chartZeroRestrictionMap R M) 1
    (overlapLaurentEquiv_algebraMap_X R) x

lemma chartOneRestrictionLinear_intertwines_X
    (M : (scheme R).Modules) (x : chartSections R M true) :
    chartOneRestrictionLinear R M ((Polynomial.X : Polynomial R) • x) =
      (T (-1) : R[T;T⁻¹]) • chartOneRestrictionLinear R M x := by
  exact restrictionBaseMap_intertwines_X R (chartSections R M true)
    (overlapSections R M) (flipHom R) (chartOne_c_eq_algebraMap R)
    (chartOneRestrictionMap R M) (-1) (overlapLaurentEquiv_flipHom_X R) x

/-- The two chart restrictions form the standard projective-line Čech differential. -/
def projectiveLineCechDifferential (M : (scheme R).Modules) :
    (chartSections R M false × chartSections R M true) →ₗ[R]
      overlapSections R M :=
  (chartZeroRestrictionLinear R M).comp
      (LinearMap.fst R (chartSections R M false) (chartSections R M true)) -
    (chartOneRestrictionLinear R M).comp
      (LinearMap.snd R (chartSections R M false) (chartSections R M true))

/-- The first chart restriction has finite base-ring kernel. -/
lemma chartZeroRestrictionLinear_finite_ker
    [IsNoetherianRing R] {M : (scheme R).Modules}
    [M.IsQuasicoherent] [M.IsFinitePresentation] :
    Module.Finite R (chartZeroRestrictionLinear R M).ker := by
  have : Module.FinitePresentation (Polynomial R)
      (chartSections R M false : Type u) := chartSections_isFinitePresentation R false
  let : Module.Finite (Polynomial R) (chartSections R M false : Type u) := inferInstance
  let : IsLocalizedModule (.powers (Polynomial.X : Polynomial R))
      (chartZeroRestrictionMap R M).hom :=
    chartZeroRestrictionMap_isLocalizedModule R
  exact restrictionBaseMap_finite_ker R (chartSections R M false)
    (overlapSections R M) (algebraMap (Polynomial R) (overlapRing R))
    (chartZero_c_eq_algebraMap R) (chartZeroRestrictionMap R M)

/-- The second chart restriction has finite base-ring kernel. -/
lemma chartOneRestrictionLinear_finite_ker
    [IsNoetherianRing R] {M : (scheme R).Modules}
    [M.IsQuasicoherent] [M.IsFinitePresentation] :
    Module.Finite R (chartOneRestrictionLinear R M).ker := by
  have : Module.FinitePresentation (Polynomial R)
      (chartSections R M true : Type u) := chartSections_isFinitePresentation R true
  let : Module.Finite (Polynomial R) (chartSections R M true : Type u) := inferInstance
  let : IsLocalizedModule (.powers (Polynomial.X : Polynomial R))
      (chartOneRestrictionMap R M).hom :=
    chartOneRestrictionMap_isLocalizedModule R
  exact restrictionBaseMap_finite_ker R (chartSections R M true)
    (overlapSections R M) (flipHom R) (chartOne_c_eq_algebraMap R)
    (chartOneRestrictionMap R M)

/-- The kernel of the projective-line Čech differential is finite over the base ring. -/
lemma projectiveLineCechDifferential_ker_finite
    [IsNoetherianRing R] {M : (scheme R).Modules}
    [M.IsQuasicoherent] [M.IsFinitePresentation] :
    Module.Finite R (projectiveLineCechDifferential R M).ker := by
  let : IsScalarTower R R[T;T⁻¹] (overlapSections R M) :=
    overlapSectionsBase_isScalarTower R M
  have : Module.FinitePresentation (Polynomial R)
      (chartSections R M false : Type u) := chartSections_isFinitePresentation R false
  have : Module.FinitePresentation (Polynomial R)
      (chartSections R M true : Type u) := chartSections_isFinitePresentation R true
  let : Module.Finite (Polynomial R) (chartSections R M false : Type u) := inferInstance
  let : Module.Finite (Polynomial R) (chartSections R M true : Type u) := inferInstance
  let : Module.Finite R (chartZeroRestrictionLinear R M).ker :=
    chartZeroRestrictionLinear_finite_ker R
  let : Module.Finite R (chartOneRestrictionLinear R M).ker :=
    chartOneRestrictionLinear_finite_ker R
  let : Module.Finite R
      ((chartZeroRestrictionLinear R M).range ⊓
        (chartOneRestrictionLinear R M).range :
        Submodule R (overlapSections R M)) := by
    let : IsLocalizedModule (.powers (Polynomial.X : Polynomial R))
        (chartZeroRestrictionMap R M).hom :=
      chartZeroRestrictionMap_isLocalizedModule R
    let : IsLocalizedModule (.powers (Polynomial.X : Polynomial R))
        (chartOneRestrictionMap R M).hom :=
      chartOneRestrictionMap_isLocalizedModule R
    apply LinearMap.finite_range_inf_of_laurent_localization
      (chartZeroRestrictionLinear R M) (chartOneRestrictionLinear R M)
    · intro x
      exact chartZeroRestrictionLinear_intertwines_X R M x
    · intro x
      exact chartOneRestrictionLinear_intertwines_X R M x
    · intro x
      obtain ⟨n, p, hp⟩ := restrictionBaseMap_clears_denominators R
        (chartSections R M false) (overlapSections R M)
        (algebraMap (Polynomial R) (overlapRing R))
        (chartZero_c_eq_algebraMap R) (chartZeroRestrictionMap R M) 1
        (overlapLaurentEquiv_algebraMap_X R) x
      refine ⟨n, p, ?_⟩
      change (restrictionBaseMap R (chartSections R M false)
        (overlapSections R M) (algebraMap (Polynomial R) (overlapRing R))
        (chartZero_c_eq_algebraMap R) (chartZeroRestrictionMap R M)) p = _
      simpa only [mul_one] using hp
    · intro x
      obtain ⟨n, p, hp⟩ := restrictionBaseMap_clears_denominators R
        (chartSections R M true) (overlapSections R M)
        (flipHom R) (chartOne_c_eq_algebraMap R) (chartOneRestrictionMap R M)
        (-1) (overlapLaurentEquiv_flipHom_X R) x
      refine ⟨n, p, ?_⟩
      change (restrictionBaseMap R (chartSections R M true)
        (overlapSections R M) (flipHom R) (chartOne_c_eq_algebraMap R)
        (chartOneRestrictionMap R M)) p = _
      simpa only [mul_neg, mul_one] using hp
  exact LinearMap.finite_ker_sub_fst_snd_of_finite_ker_of_finite_range_inf
    (chartZeroRestrictionLinear R M) (chartOneRestrictionLinear R M)

/-- The Laurent overlap sections are finite over the Laurent coordinate ring. -/
lemma overlapSectionsBase_finite_laurent
    [IsNoetherianRing R] {M : (scheme R).Modules}
    [M.IsFinitePresentation] :
    Module.Finite R[T;T⁻¹] (overlapSections R M) := by
  have : Module.FinitePresentation (overlapRing R)
      (overlapSections R M : Type u) := overlapSections_isFinitePresentation R
  let : Module.Finite (overlapRing R) (overlapSections R M : Type u) := inferInstance
  let f : (overlapSections R M) →ₛₗ[(overlapLaurentEquiv R).toRingHom]
      (overlapSections R M) :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change a • x = (overlapLaurentEquiv R).symm (overlapLaurentEquiv R a) • x
        rw [AlgEquiv.symm_apply_apply] }
  exact Module.Finite.of_surjective f Function.surjective_id

/-- The cokernel of the projective-line Čech differential is finite over the base ring. -/
lemma projectiveLineCechDifferential_range_quotient_finite
    [IsNoetherianRing R] {M : (scheme R).Modules}
    [M.IsQuasicoherent] [M.IsFinitePresentation] :
    Module.Finite R
      ((overlapSections R M) ⧸
        (projectiveLineCechDifferential R M).range) := by
  let : IsScalarTower R R[T;T⁻¹] (overlapSections R M) :=
    overlapSectionsBase_isScalarTower R M
  let : Module.Finite R[T;T⁻¹] (overlapSections R M) :=
    overlapSectionsBase_finite_laurent R
  let : IsLocalizedModule (.powers (Polynomial.X : Polynomial R))
      (chartZeroRestrictionMap R M).hom :=
    chartZeroRestrictionMap_isLocalizedModule R
  let : IsLocalizedModule (.powers (Polynomial.X : Polynomial R))
      (chartOneRestrictionMap R M).hom :=
    chartOneRestrictionMap_isLocalizedModule R
  let z := chartZeroRestrictionLinear R M
  let o := chartOneRestrictionLinear R M
  have hrange : (projectiveLineCechDifferential R M).range = z.range ⊔ o.range := by
    have hd : projectiveLineCechDifferential R M = z.coprod (-o) := by
      apply LinearMap.ext
      rintro ⟨x, y⟩
      simp [projectiveLineCechDifferential, z, o, LinearMap.coprod_apply,
        sub_eq_add_neg]
    rw [hd, LinearMap.range_coprod, LinearMap.range_neg]
  rw [hrange]
  apply GromovWitten.Algebra.finiteLaurentCechQuotient z.range o.range
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨(X : Polynomial R) • y, chartZeroRestrictionLinear_intertwines_X R M y⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨(X : Polynomial R) • y, chartOneRestrictionLinear_intertwines_X R M y⟩
  · intro x
    obtain ⟨n, p, hp⟩ := restrictionBaseMap_clears_denominators R
      (chartSections R M false) (overlapSections R M)
      (algebraMap (Polynomial R) (overlapRing R))
      (chartZero_c_eq_algebraMap R) (chartZeroRestrictionMap R M) 1
      (overlapLaurentEquiv_algebraMap_X R) x
    refine ⟨n, p, ?_⟩
    change (restrictionBaseMap R (chartSections R M false)
      (overlapSections R M) (algebraMap (Polynomial R) (overlapRing R))
      (chartZero_c_eq_algebraMap R) (chartZeroRestrictionMap R M)) p = _
    simpa only [mul_one] using hp
  · intro x
    obtain ⟨n, p, hp⟩ := restrictionBaseMap_clears_denominators R
      (chartSections R M true) (overlapSections R M)
      (flipHom R) (chartOne_c_eq_algebraMap R) (chartOneRestrictionMap R M)
      (-1) (overlapLaurentEquiv_flipHom_X R) x
    refine ⟨n, p, ?_⟩
    change (restrictionBaseMap R (chartSections R M true)
      (overlapSections R M) (flipHom R) (chartOne_c_eq_algebraMap R)
      (chartOneRestrictionMap R M)) p = _
    simpa only [mul_neg, mul_one] using hp

end GromovWitten.AlgebraicGeometry.ProjectiveLine
