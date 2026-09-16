/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Blowups from the graded Rees algebra

Mathlib defines the Rees algebra as a subalgebra of `R[X]`, but does not yet equip it with
its natural grading.  This file supplies that grading and uses Mathlib's projective spectrum
to construct the affine blowup of an ideal.
-/

open Polynomial
open CategoryTheory
open TopologicalSpace
open scoped DirectSum

universe u

namespace AlgebraicGeometry
namespace ReesBlowup

variable {R : Type u} [CommRing R]

/-- The degree-`n` part `I^n t^n` of the Rees algebra. -/
def grade (I : Ideal R) (n : ℕ) : AddSubgroup (reesAlgebra I) where
  carrier := {f | (f : R[X]) = monomial n ((f : R[X]).coeff n)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change ((f : reesAlgebra I) : R[X]) + g =
      monomial n ((((f : reesAlgebra I) : R[X]) + g).coeff n)
    ext m
    rw [coeff_add, hf, hg]
    simp [coeff_monomial]
  neg_mem' := by
    intro f hf
    change -((f : reesAlgebra I) : R[X]) =
      monomial n ((-((f : reesAlgebra I) : R[X])).coeff n)
    ext m
    rw [coeff_neg, hf]
    simp [coeff_monomial]

/-- The homogeneous component of a Rees-algebra element. -/
noncomputable def component (I : Ideal R) (f : reesAlgebra I) (n : ℕ) : grade I n :=
  ⟨⟨monomial n ((f : R[X]).coeff n), reesAlgebra.monomial_mem.mpr
      (((mem_reesAlgebra_iff I (f : R[X])).mp f.property) n)⟩, by
        ext m
        simp [coeff_monomial]⟩

@[simp]
theorem component_coe (I : Ideal R) (f : reesAlgebra I) (n : ℕ) :
    ((component I f n : reesAlgebra I) : R[X]) = monomial n ((f : R[X]).coeff n) :=
  rfl

/-- The finitely supported family of homogeneous components of a Rees-algebra element. -/
noncomputable def decomposeFun (I : Ideal R) (f : reesAlgebra I) :
    (⨁ n : ℕ, grade I n) :=
  DirectSum.mk (fun n : ℕ ↦ grade I n) (f : R[X]).support
    (fun n ↦ component I f n)

@[simp]
theorem decomposeFun_apply (I : Ideal R) (f : reesAlgebra I) (n : ℕ) :
    decomposeFun I f n = component I f n := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  by_cases hn : n ∈ (f : R[X]).support
  · exact congr_arg (fun x : grade I n ↦ ((x : reesAlgebra I) : R[X]))
      (DirectSum.mk_apply_of_mem hn)
  · unfold decomposeFun
    rw [DirectSum.mk_apply_of_notMem hn]
    have hcoeff : (f : R[X]).coeff n = 0 := by
      simpa only [mem_support_iff, not_not] using hn
    simp [component, hcoeff]

/-- Additive decomposition of a Rees-algebra element into its homogeneous monomials. -/
noncomputable def decomposeAddHom (I : Ideal R) :
    reesAlgebra I →+ (⨁ n : ℕ, grade I n) where
  toFun := decomposeFun I
  map_zero' := by
    apply DFinsupp.ext
    intro n
    rw [decomposeFun_apply]
    apply Subtype.ext
    apply Subtype.ext
    simp [component]
  map_add' f g := by
    apply DFinsupp.ext
    intro n
    rw [decomposeFun_apply]
    rw [DFinsupp.add_apply, decomposeFun_apply, decomposeFun_apply]
    apply Subtype.ext
    apply Subtype.ext
    ext m
    simp [component, coeff_monomial]

theorem coe_decomposeAddHom_component (I : Ideal R) (f : reesAlgebra I) (n : ℕ) :
    (((decomposeAddHom I f) n : grade I n) : reesAlgebra I) = component I f n := by
  exact congr_arg Subtype.val (decomposeFun_apply I f n)

theorem recompose_decomposeAddHom (I : Ideal R) :
    (DirectSum.coeAddMonoidHom (grade I)).comp (decomposeAddHom I) = AddMonoidHom.id _ := by
  classical
  apply AddMonoidHom.ext
  intro f
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
  apply Subtype.ext
  have hs : (decomposeAddHom I f).support = (f : R[X]).support := by
    ext n
    rw [DFinsupp.mem_support_iff, mem_support_iff]
    have hz : (decomposeAddHom I f) n = 0 ↔ (f : R[X]).coeff n = 0 := by
      rw [show (decomposeAddHom I f) n = component I f n from decomposeFun_apply I f n]
      constructor
      · intro h
        have h' := congr_arg
          (fun x : grade I n ↦ (((x : reesAlgebra I) : R[X]).coeff n)) h
        simpa [component] using h'
      · intro h
        apply Subtype.ext
        apply Subtype.ext
        simp [component, h]
    exact not_congr hz
  rw [DFinsupp.sum, hs]
  rw [AddSubmonoidClass.coe_finsetSum]
  simp_rw [coe_decomposeAddHom_component, component_coe]
  exact (as_sum_support (f : R[X])).symm

theorem decomposeAddHom_recompose (I : Ideal R) :
    (decomposeAddHom I).comp (DirectSum.coeAddMonoidHom (grade I)) = AddMonoidHom.id _ := by
  apply DirectSum.addHom_ext'
  intro n
  apply AddMonoidHom.ext
  intro f
  simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
    AddMonoidHom.id_apply]
  apply DFinsupp.ext
  intro m
  change decomposeFun I (f : reesAlgebra I) m =
    (DirectSum.of (fun i : ℕ ↦ grade I i) n f) m
  rw [decomposeFun_apply]
  apply Subtype.ext
  apply Subtype.ext
  rw [component_coe, f.property]
  by_cases hmn : n = m
  · subst m
    rw [DirectSum.of_eq_same]
    simpa using f.property.symm
  · have hzero : (DirectSum.of (fun i : ℕ ↦ grade I i) n f) m = 0 :=
      DirectSum.of_eq_of_ne _ _ _ (fun h ↦ hmn h.symm)
    rw [hzero]
    rw [@coeff_monomial_of_ne R _ m n ((f : R[X]).coeff n) (fun h ↦ hmn h.symm)]
    simp

noncomputable instance decomposition (I : Ideal R) :
    DirectSum.Decomposition (grade I) :=
  DirectSum.Decomposition.ofAddHom (grade I) (decomposeAddHom I)
    (recompose_decomposeAddHom I) (decomposeAddHom_recompose I)

instance gradedMonoid (I : Ideal R) : SetLike.GradedMonoid (grade I) where
  one_mem := by
    change ((1 : reesAlgebra I) : R[X]) = monomial 0 (((1 : reesAlgebra I) : R[X]).coeff 0)
    simp
  mul_mem i j f g hf hg := by
    change ((f : reesAlgebra I) : R[X]) =
      monomial i (((f : reesAlgebra I) : R[X]).coeff i) at hf
    change ((g : reesAlgebra I) : R[X]) =
      monomial j (((g : reesAlgebra I) : R[X]).coeff j) at hg
    change ((f * g : reesAlgebra I) : R[X]) =
      monomial (i + j) (((f * g : reesAlgebra I) : R[X]).coeff (i + j))
    rw [Subalgebra.coe_mul, hf, hg, monomial_mul_monomial]
    simp

/-- The Rees algebra with its natural internal grading. -/
noncomputable instance gradedRing (I : Ideal R) : GradedRing (grade I) where
  toGradedMonoid := gradedMonoid I
  toDecomposition := decomposition I

/-! ## Functoriality under coefficient-ring maps -/

section ReesMap

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- Applying a ring map coefficientwise sends the Rees algebra of `I` to the Rees algebra of
the extended ideal. -/
noncomputable def reesMap (I : Ideal A) (f : A →+* B) :
    reesAlgebra I →+* reesAlgebra (I.map f) :=
  ((Polynomial.mapRingHom f).comp (reesAlgebra I).val.toRingHom).codRestrict
    (reesAlgebra (I.map f)) (by
      intro p
      rw [mem_reesAlgebra_iff]
      intro n
      change ((p : A[X]).map f).coeff n ∈ (I.map f) ^ n
      rw [coeff_map, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem f
        (((mem_reesAlgebra_iff I (p : A[X])).mp p.property) n))

@[simp]
theorem reesMap_coe (I : Ideal A) (f : A →+* B) (p : reesAlgebra I) :
    (reesMap I f p : B[X]) = (p : A[X]).map f :=
  rfl

/-- Coefficientwise extension of Rees algebras is injective when the coefficient map is. -/
theorem reesMap_injective (I : Ideal A) (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (reesMap I f) := by
  intro p q h
  apply Subtype.ext
  apply Polynomial.map_injective f hf
  exact congrArg Subtype.val h

/-- Coefficientwise extension preserves every homogeneous degree. -/
theorem reesMap_mem_grade (I : Ideal A) (f : A →+* B) (n : ℕ)
    (p : reesAlgebra I) (hp : p ∈ grade I n) :
    reesMap I f p ∈ grade (I.map f) n := by
  change (p : A[X]).map f = monomial n (((p : A[X]).map f).coeff n)
  change (p : A[X]) = monomial n ((p : A[X]).coeff n) at hp
  rw [hp, map_monomial, coeff_monomial]
  simp

/-- The coefficientwise Rees map as a graded ring homomorphism. -/
noncomputable def gradedMap (I : Ideal A) (f : A →+* B) :
    grade I →+*ᵍ grade (I.map f) where
  toRingHom := reesMap I f
  map_mem := reesMap_mem_grade I f _ _

end ReesMap

/-- The affine blowup of `Spec R` along `I`, constructed as `Proj (⨁ I^n t^n)`. -/
noncomputable abbrev scheme (I : Ideal R) : Scheme := Proj (grade I)

/-- The degree-zero part of the Rees algebra is canonically the base ring. -/
noncomputable def zeroEquiv (I : Ideal R) : grade I 0 ≃+* R where
  toFun f := ((f : reesAlgebra I) : R[X]).coeff 0
  invFun r := component I (algebraMap R (reesAlgebra I) r) 0
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    rw [component_coe]
    simpa using f.property.symm
  right_inv r := by simp [component]
  map_mul' f g := by simp
  map_add' f g := by simp

/-- Over a Noetherian base, the Rees algebra is finite type over its degree-zero part.  The
proof transports Mathlib's finite-generation theorem over `R` through `zeroEquiv`. -/
noncomputable instance finiteTypeOverZero (I : Ideal R) [IsNoetherianRing R] :
    Algebra.FiniteType (grade I 0) (reesAlgebra I) := by
  rw [← RingHom.finiteType_algebraMap]
  let e : R →+* grade I 0 := (zeroEquiv I).symm
  let j : grade I 0 →+* reesAlgebra I := algebraMap _ _
  have hcomp : j.comp e = algebraMap R (reesAlgebra I) := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    simp [j, e, zeroEquiv, component]
  apply RingHom.FiniteType.of_comp_finiteType (f := e) (g := j)
  rw [hcomp]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The blowup projection to the affine base. -/
noncomputable def projection (I : Ideal R) : scheme I ⟶ Spec (.of R) :=
  Proj.toSpecZero (grade I) ≫
    Spec.map (CommRingCat.ofHom (zeroEquiv I).symm.toRingHom)

/-- The affine Rees blowup projection over a Noetherian ring is proper. -/
noncomputable instance projection_isProper (I : Ideal R) [IsNoetherianRing R] :
    IsProper (projection I) := by
  let _ : IsIso (CommRingCat.ofHom (zeroEquiv I).symm.toRingHom) := by
    change IsIso (zeroEquiv I).toCommRingCatIso.inv
    infer_instance
  let _ : IsIso (Spec.map (CommRingCat.ofHom (zeroEquiv I).symm.toRingHom)) := by
    infer_instance
  unfold projection
  infer_instance

/-- The homogeneous degree-one Rees element `r t` associated to `r ∈ I`. -/
noncomputable def generator (I : Ideal R) (r : I) : reesAlgebra I :=
  ⟨monomial 1 r.1, reesAlgebra.monomial_mem.mpr (by simpa only [pow_one] using r.2)⟩

theorem generator_mem_grade_one (I : Ideal R) (r : I) : generator I r ∈ grade I 1 := by
  change monomial 1 r.1 = monomial 1 ((monomial 1 r.1).coeff 1)
  simp

/-- A Rees monomial, defined to be zero if its coefficient does not lie in the corresponding
ideal power.  This proof-independent definition is convenient for induction on ideal powers. -/
noncomputable def homogeneousMonomial (I : Ideal R) (n : ℕ) (a : R) : reesAlgebra I :=
  by
    classical
    exact if ha : a ∈ I ^ n then
      ⟨monomial n a, reesAlgebra.monomial_mem.mpr ha⟩ else 0

@[simp]
theorem homogeneousMonomial_coe (I : Ideal R) (n : ℕ) (a : R) (ha : a ∈ I ^ n) :
    (homogeneousMonomial I n a : R[X]) = monomial n a := by
  simp [homogeneousMonomial, ha]

/-- Every positive-degree Rees monomial belongs to the ideal generated by the degree-one
elements `r t`, `r ∈ I`. -/
theorem homogeneousMonomial_mem_span_generators (I : Ideal R) (n : ℕ) (hn : 0 < n)
    (a : R) (ha : a ∈ I ^ n) :
    homogeneousMonomial I n a ∈ Ideal.span (Set.range (generator I)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ'] at ha
  have hresult : a ∈ I ^ (n + 1) ∧
      homogeneousMonomial I (n + 1) a ∈ Ideal.span (Set.range (generator I)) :=
    Submodule.smul_induction_on ha (p := fun a ↦ a ∈ I ^ (n + 1) ∧
      homogeneousMonomial I (n + 1) a ∈ Ideal.span (Set.range (generator I))) (by
      intro r hr s hs
      change r * s ∈ I ^ (n + 1) ∧
        homogeneousMonomial I (n + 1) (r * s) ∈ Ideal.span (Set.range (generator I))
      have hrs : r * s ∈ I ^ (n + 1) := by
        rw [pow_succ]
        simpa [mul_comm] using Ideal.mul_mem_mul hs hr
      refine ⟨hrs, ?_⟩
      have hgen : generator I ⟨r, hr⟩ ∈ Ideal.span (Set.range (generator I)) :=
        Ideal.subset_span ⟨⟨r, hr⟩, rfl⟩
      have hmul := (Ideal.span (Set.range (generator I))).mul_mem_right
        (homogeneousMonomial I n s) hgen
      convert hmul using 1
      apply Subtype.ext
      rw [homogeneousMonomial_coe I (n + 1) (r * s) hrs,
        Subalgebra.coe_mul, homogeneousMonomial_coe I n s hs]
      change monomial (n + 1) (r * s) = monomial 1 r * monomial n s
      rw [monomial_mul_monomial]
      rw [Nat.add_comm n 1]) (by
      intro x y hx hy
      have hxy := Ideal.add_mem (I ^ (n + 1)) hx.1 hy.1
      refine ⟨hxy, ?_⟩
      convert (Ideal.span (Set.range (generator I))).add_mem hx.2 hy.2 using 1
      apply Subtype.ext
      rw [homogeneousMonomial_coe I (n + 1) (x + y) hxy,
        Subalgebra.coe_add, homogeneousMonomial_coe I (n + 1) x hx.1,
        homogeneousMonomial_coe I (n + 1) y hy.1]
      simp)
  exact hresult.2

/-- The positive-degree irrelevant ideal is generated by the degree-one elements `r t`. -/
theorem irrelevant_le_span_generators (I : Ideal R) :
    (HomogeneousIdeal.irrelevant (grade I)).toIdeal ≤
      Ideal.span (Set.range (generator I)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn f hf
  have hcoeff : ((f : reesAlgebra I) : R[X]).coeff n ∈ I ^ n :=
    ((mem_reesAlgebra_iff I ((f : reesAlgebra I) : R[X])).mp
      (f : reesAlgebra I).property) n
  have hm := homogeneousMonomial_mem_span_generators I n hn _ hcoeff
  have heq : (f : reesAlgebra I) = homogeneousMonomial I n ((f : R[X]).coeff n) := by
    apply Subtype.ext
    rw [homogeneousMonomial_coe I n _ hcoeff]
    exact hf
  rw [heq]
  exact hm

section ReesMap

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- Extension of coefficients maps the source irrelevant ideal onto enough degree-one elements
to contain the irrelevant ideal of the extended Rees algebra.  This is the hypothesis required
by functoriality of `Proj`. -/
theorem irrelevant_le_map_gradedMap (I : Ideal A) (f : A →+* B) :
    HomogeneousIdeal.irrelevant (grade (I.map f)) ≤
      (HomogeneousIdeal.irrelevant (grade I)).map (gradedMap I f) := by
  change (HomogeneousIdeal.irrelevant (grade (I.map f))).toIdeal ≤
    ((HomogeneousIdeal.irrelevant (grade I)).map (gradedMap I f)).toIdeal
  refine (irrelevant_le_span_generators (I.map f)).trans ?_
  rw [Ideal.span_le]
  intro z hz
  obtain ⟨r, rfl⟩ := hz
  change generator (I.map f) r ∈
    (HomogeneousIdeal.irrelevant (grade I)).toIdeal.map (gradedMap I f)
  have hr : r.1 ∈ I.map f := r.property
  change r.1 ∈ Ideal.span (f '' (I : Set A)) at hr
  refine Submodule.span_induction
    (p := fun x hx ↦ generator (I.map f) ⟨x, hx⟩ ∈
      (HomogeneousIdeal.irrelevant (grade I)).toIdeal.map (gradedMap I f)) ?_ ?_ ?_ ?_ hr
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    have hmem := HomogeneousIdeal.mem_irrelevant_of_mem (grade I) (by omega)
      (generator_mem_grade_one I ⟨a, ha⟩)
    convert Ideal.mem_map_of_mem (gradedMap I f) hmem using 1
    apply Subtype.ext
    simp [gradedMap, reesMap, generator]
  · convert Ideal.zero_mem _ using 1
    apply Subtype.ext
    simp [generator]
  · intro x y hx hy ihx ihy
    convert Ideal.add_mem _ ihx ihy using 1
    apply Subtype.ext
    simp [generator]
  · intro b x hx ih
    have hmul := ((HomogeneousIdeal.irrelevant (grade I)).toIdeal.map
      (gradedMap I f)).mul_mem_left
        (algebraMap B (reesAlgebra (I.map f)) b) ih
    convert hmul using 1
    apply Subtype.ext
    ext n
    simp [generator, coeff_monomial]

end ReesMap

/-! ## Flat base change for the Rees algebra -/

section FlatBaseChange

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Coefficient extension as an algebra morphism. -/
noncomputable def reesMapAlg (I : Ideal A) :
    reesAlgebra I →ₐ[A] reesAlgebra (I.map (algebraMap A B)) where
  toFun := reesMap I (algebraMap A B)
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' a := by
    apply Subtype.ext
    simp [reesMap, Polynomial.algebraMap_apply]

@[simp]
theorem reesMapAlg_apply (I : Ideal A) (x : reesAlgebra I) :
    reesMapAlg (B := B) I x = reesMap I (algebraMap A B) x := rfl

/-- The canonical scalar-extension map for Rees algebras. -/
noncomputable def reesBaseChangeMap (I : Ideal A) :
    reesAlgebra I ⊗[A] B →ₐ[A] reesAlgebra (I.map (algebraMap A B)) :=
  Algebra.TensorProduct.lift (R := A) (S := A)
    (reesMapAlg (B := B) I)
    (IsScalarTower.toAlgHom A B (reesAlgebra (I.map (algebraMap A B))))
    (fun _ _ ↦ Commute.all _ _)

@[simp]
theorem reesBaseChangeMap_tmul (I : Ideal A) (x : reesAlgebra I) (b : B) :
    reesBaseChangeMap (B := B) I (x ⊗ₜ b) =
      algebraMap B (reesAlgebra (I.map (algebraMap A B))) b *
        reesMap I (algebraMap A B) x := by
  simp [reesBaseChangeMap, mul_comm]

/-- The same canonical scalar-extension map, with its natural `B`-algebra structure exposed. -/
noncomputable def reesBaseChangeMapB (I : Ideal A) :
    reesAlgebra I ⊗[A] B →ₐ[B] reesAlgebra (I.map (algebraMap A B)) :=
  (Algebra.TensorProduct.lift (R := A) (S := B)
    (Algebra.ofId B (reesAlgebra (I.map (algebraMap A B))))
    (reesMapAlg (B := B) I)
    (fun _ _ ↦ Commute.all _ _)).comp
      (Algebra.TensorProduct.commRight A B (reesAlgebra I)).symm.toAlgHom

@[simp]
theorem reesBaseChangeMapB_tmul (I : Ideal A) (x : reesAlgebra I) (b : B) :
    reesBaseChangeMapB (B := B) I (x ⊗ₜ b) =
      algebraMap B (reesAlgebra (I.map (algebraMap A B))) b *
        reesMap I (algebraMap A B) x := by
  simp [reesBaseChangeMapB]

/-- The `A`- and `B`-algebra presentations of the Rees base-change map have the same
underlying function. -/
theorem reesBaseChangeMapB_apply (I : Ideal A) (z : reesAlgebra I ⊗[A] B) :
    reesBaseChangeMapB (B := B) I z = reesBaseChangeMap (B := B) I z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => rw [reesBaseChangeMapB_tmul, reesBaseChangeMap_tmul]
  | add x y hx hy => simp [hx, hy]

theorem reesBaseChangeMap_homogeneousMonomial_mem_range (I : Ideal A)
    (n : ℕ) (b : B) (hb : b ∈ (I.map (algebraMap A B)) ^ n) :
    homogeneousMonomial (I.map (algebraMap A B)) n b ∈
      (reesBaseChangeMap (B := B) I).range := by
  rw [← Ideal.map_pow] at hb
  refine Submodule.span_induction
    (p := fun b hb ↦ homogeneousMonomial (I.map (algebraMap A B)) n b ∈
      (reesBaseChangeMap (B := B) I).range) ?_ ?_ ?_ ?_ hb
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := hb
    have haT : algebraMap A B a ∈ (I.map (algebraMap A B)) ^ n := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem (algebraMap A B) ha
    refine ⟨homogeneousMonomial I n a ⊗ₜ[A] (1 : B), ?_⟩
    calc
      (reesBaseChangeMap (B := B) I).toRingHom
          (homogeneousMonomial I n a ⊗ₜ[A] (1 : B)) =
          algebraMap B (reesAlgebra (I.map (algebraMap A B))) 1 *
            reesMap I (algebraMap A B) (homogeneousMonomial I n a) := by
        exact reesBaseChangeMap_tmul I _ _
      _ = homogeneousMonomial (I.map (algebraMap A B)) n (algebraMap A B a) := by
        apply Subtype.ext
        simp only [map_one, one_mul, reesMap_coe]
        rw [homogeneousMonomial_coe I n a ha,
          homogeneousMonomial_coe (I.map (algebraMap A B)) n (algebraMap A B a) haT]
        exact Polynomial.map_monomial (algebraMap A B)
  · refine ⟨0, ?_⟩
    rw [map_zero]
    apply Subtype.ext
    simp [homogeneousMonomial]
  · intro x y hx hy hx' hy'
    have hxT : x ∈ (I.map (algebraMap A B)) ^ n := by
      rwa [← Ideal.map_pow]
    have hyT : y ∈ (I.map (algebraMap A B)) ^ n := by
      rwa [← Ideal.map_pow]
    obtain ⟨x', hx'⟩ := hx'
    obtain ⟨y', hy'⟩ := hy'
    refine ⟨x' + y', ?_⟩
    rw [map_add, hx', hy']
    apply Subtype.ext
    rw [Subalgebra.coe_add,
      homogeneousMonomial_coe _ n x hxT,
      homogeneousMonomial_coe _ n y hyT,
      homogeneousMonomial_coe _ n (x + y) (Ideal.add_mem _ hxT hyT)]
    simp
  · intro c x hx hx'
    have hxT : x ∈ (I.map (algebraMap A B)) ^ n := by
      rwa [← Ideal.map_pow]
    obtain ⟨x', hx'⟩ := hx'
    refine ⟨(1 ⊗ₜ[A] c) * x', ?_⟩
    rw [map_mul, hx']
    have hone := reesBaseChangeMap_tmul (B := B) I (1 : reesAlgebra I) c
    have hone' : (reesBaseChangeMap (B := B) I).toRingHom (1 ⊗ₜ[A] c) =
        algebraMap B (reesAlgebra (I.map (algebraMap A B))) c := by
      exact hone.trans (by simp)
    rw [hone']
    apply Subtype.ext
    rw [Subalgebra.coe_mul,
      homogeneousMonomial_coe _ n x hxT,
      homogeneousMonomial_coe _ n (c • x) (((I.map (algebraMap A B)) ^ n).smul_mem c hxT)]
    simp [smul_eq_mul]

/-- Scalar extension surjects onto the Rees algebra of the extended ideal, without a flatness
hypothesis. -/
theorem reesBaseChangeMap_surjective (I : Ideal A) :
    Function.Surjective (reesBaseChangeMap (B := B) I) := by
  intro p
  change p ∈ (reesBaseChangeMap (B := B) I).range
  have hp : p = ∑ n ∈ (p : B[X]).support,
      homogeneousMonomial (I.map (algebraMap A B)) n ((p : B[X]).coeff n) := by
    apply Subtype.ext
    change (p : B[X]) =
      (reesAlgebra (I.map (algebraMap A B))).val
        (∑ n ∈ (p : B[X]).support,
          homogeneousMonomial (I.map (algebraMap A B)) n ((p : B[X]).coeff n))
    rw [map_sum]
    change (p : B[X]) = ∑ n ∈ (p : B[X]).support,
      (homogeneousMonomial (I.map (algebraMap A B)) n ((p : B[X]).coeff n) : B[X])
    simp_rw [homogeneousMonomial_coe _ _ _
      (((mem_reesAlgebra_iff _ (p : B[X])).mp p.property) _)]
    exact (p : B[X]).as_sum_support
  rw [hp]
  apply Subalgebra.sum_mem
  intro n hn
  have hc : (p : B[X]).coeff n ∈ (I.map (algebraMap A B)) ^ n :=
    ((mem_reesAlgebra_iff _ (p : B[X])).mp p.property) n
  exact reesBaseChangeMap_homogeneousMonomial_mem_range I n _ hc

/-- Polynomial scalar extension, as an `A`-linear equivalence. -/
noncomputable def polynomialBaseChangeLinearEquiv :
    B ⊗[A] A[X] ≃ₗ[A] B[X] :=
  (LinearEquiv.lTensor B
      (MvPolynomial.uniqueAlgEquiv A Unit).symm.toLinearEquiv).trans
    ((MvPolynomial.algebraTensorAlgEquiv (σ := Unit) A B).toLinearEquiv.restrictScalars A) |>.trans
      ((MvPolynomial.uniqueAlgEquiv B Unit).toLinearEquiv.restrictScalars A)

@[simp]
theorem polynomialBaseChangeLinearEquiv_tmul (b : B) (p : A[X]) :
    polynomialBaseChangeLinearEquiv (A := A) (B := B) (b ⊗ₜ[A] p) =
      b • p.map (algebraMap A B) := by
  simp only [polynomialBaseChangeLinearEquiv, AlgEquiv.toLinearEquiv_symm,
    LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul, AlgEquiv.coe_symm_toLinearEquiv,
    MvPolynomial.uniqueAlgEquiv_symm_apply, PUnit.default_eq_unit,
    LinearEquiv.restrictScalars_apply, AlgEquiv.toLinearEquiv_apply,
    MvPolynomial.algebraTensorAlgEquiv_tmul, map_smul,
    MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_map]
  rw [← MvPolynomial.uniqueAlgEquiv_symm_apply A Unit p]
  rw [MvPolynomial.eval₂_uniqueAlgEquiv_symm]
  rfl

/-- The scalar extension of the inclusion `Rees(I) ⊆ A[X]`, followed by polynomial base
change. -/
noncomputable def reesTensorPolynomialMap (I : Ideal A) :
    reesAlgebra I ⊗[A] B →ₗ[A] B[X] :=
  (polynomialBaseChangeLinearEquiv (A := A) (B := B)).toLinearMap.comp
    ((LinearMap.lTensor B (reesAlgebra I).val.toLinearMap).comp
      (Algebra.TensorProduct.comm A (reesAlgebra I) B).toLinearEquiv.toLinearMap)

@[simp]
theorem reesTensorPolynomialMap_tmul (I : Ideal A) (x : reesAlgebra I) (b : B) :
    reesTensorPolynomialMap (B := B) I (x ⊗ₜ[A] b) =
      b • (x : A[X]).map (algebraMap A B) := by
  simp [reesTensorPolynomialMap]

/-- The tensor-product Rees map agrees with scalar extension inside the ambient polynomial
ring. -/
theorem reesTensorPolynomialMap_eq (I : Ideal A) (z : reesAlgebra I ⊗[A] B) :
    reesTensorPolynomialMap (B := B) I z =
      (reesBaseChangeMap (B := B) I z : B[X]) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
      rw [reesTensorPolynomialMap_tmul, reesBaseChangeMap_tmul]
      simp [reesMap_coe, Polynomial.smul_eq_C_mul, mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- Flatness makes the ambient scalar-extension map injective. -/
theorem reesTensorPolynomialMap_injective (I : Ideal A) [Module.Flat A B] :
    Function.Injective (reesTensorPolynomialMap (B := B) I) := by
  have hval : Function.Injective (reesAlgebra I).val.toLinearMap := Subtype.val_injective
  have htensor : Function.Injective (LinearMap.lTensor B (reesAlgebra I).val.toLinearMap) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hval
  exact (polynomialBaseChangeLinearEquiv (A := A) (B := B)).injective.comp
    (htensor.comp (Algebra.TensorProduct.comm A (reesAlgebra I) B).injective)

/-- The canonical Rees scalar-extension map is injective under flatness. -/
theorem reesBaseChangeMap_injective (I : Ideal A) [Module.Flat A B] :
    Function.Injective (reesBaseChangeMap (B := B) I) := by
  intro x y hxy
  apply reesTensorPolynomialMap_injective (B := B) I
  rw [reesTensorPolynomialMap_eq, reesTensorPolynomialMap_eq, hxy]

/-- Under flatness, the natural `B`-algebra form of the Rees base-change map is bijective. -/
theorem reesBaseChangeMapB_bijective (I : Ideal A) [Module.Flat A B] :
    Function.Bijective (reesBaseChangeMapB (B := B) I) := by
  constructor
  · intro x y hxy
    apply reesBaseChangeMap_injective (B := B) I
    rw [← reesBaseChangeMapB_apply I x, ← reesBaseChangeMapB_apply I y, hxy]
  · intro y
    obtain ⟨x, hx⟩ := reesBaseChangeMap_surjective (B := B) I y
    exact ⟨x, (reesBaseChangeMapB_apply I x).trans hx⟩

/-- Rees algebras commute with arbitrary flat scalar extension. -/
noncomputable def reesBaseChangeEquiv (I : Ideal A) [Module.Flat A B] :
    reesAlgebra I ⊗[A] B ≃ₐ[A] reesAlgebra (I.map (algebraMap A B)) :=
  AlgEquiv.ofBijective (reesBaseChangeMap (B := B) I)
    ⟨reesBaseChangeMap_injective I, reesBaseChangeMap_surjective I⟩

/-- Rees algebras commute with arbitrary flat scalar extension as `B`-algebras. -/
noncomputable def reesBaseChangeEquivB (I : Ideal A) [Module.Flat A B] :
    reesAlgebra I ⊗[A] B ≃ₐ[B] reesAlgebra (I.map (algebraMap A B)) :=
  AlgEquiv.ofBijective (reesBaseChangeMapB (B := B) I)
    (reesBaseChangeMapB_bijective I)

end FlatBaseChange

section SchemeMap

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Functoriality of the affine Rees blowup under extension of its coefficient ring.  The source
is the blowup of the extended ideal; identifying this morphism with the scheme-theoretic base
change requires the still-separate Rees base-change isomorphism. -/
noncomputable def schemeMap (I : Ideal A) (f : A →+* B) :
    scheme (I.map f) ⟶ scheme I :=
  Proj.map (gradedMap I f) (irrelevant_le_map_gradedMap I f)

@[simp]
theorem schemeMap_preimage_basicOpen (I : Ideal A) (f : A →+* B)
    (p : reesAlgebra I) :
    schemeMap I f ⁻¹ᵁ Proj.basicOpen (grade I) p =
      Proj.basicOpen (grade (I.map f)) (reesMap I f p) :=
  rfl

/-- A degree-one Rees generator maps to the corresponding generator of the extended ideal. -/
theorem reesMap_generator (I : Ideal A) (f : A →+* B) (r : I) :
    reesMap I f (generator I r) =
      generator (I.map f) ⟨f r.1, Ideal.mem_map_of_mem f r.2⟩ := by
  apply Subtype.ext
  simp [generator]

@[simp]
theorem schemeMap_preimage_generator_basicOpen (I : Ideal A) (f : A →+* B)
    (r : I) :
    schemeMap I f ⁻¹ᵁ Proj.basicOpen (grade I) (generator I r) =
      Proj.basicOpen (grade (I.map f))
        (generator (I.map f) ⟨f r.1, Ideal.mem_map_of_mem f r.2⟩) := by
  rw [schemeMap_preimage_basicOpen, reesMap_generator]

end SchemeMap

/-- Degree-one Rees generators attached to a chosen family spanning the centre ideal. -/
noncomputable def generatorOfFamily {ι : Type*} (I : Ideal R) (s : ι → R)
    (hI : I = Ideal.span (Set.range s)) (i : ι) : reesAlgebra I :=
  generator I ⟨s i, hI.symm ▸ Ideal.subset_span ⟨i, rfl⟩⟩

theorem generatorOfFamily_mem_grade_one {ι : Type*} (I : Ideal R) (s : ι → R)
    (hI : I = Ideal.span (Set.range s)) (i : ι) :
    generatorOfFamily I s hI i ∈ grade I 1 :=
  generator_mem_grade_one I _

/-- If `s` spans `I`, then the corresponding finite or infinite family `sᵢ t` already
generates the irrelevant ideal of the Rees algebra. -/
theorem irrelevant_le_span_generatorOfFamily {ι : Type*} (I : Ideal R) (s : ι → R)
    (hI : I = Ideal.span (Set.range s)) :
    (HomogeneousIdeal.irrelevant (grade I)).toIdeal ≤
      Ideal.span (Set.range (generatorOfFamily I s hI)) := by
  refine (irrelevant_le_span_generators I).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨r, rfl⟩
  have hr : r.1 ∈ Ideal.span (Set.range s) := hI ▸ r.2
  have hspan : generator I ⟨r.1, hI.symm ▸ hr⟩ ∈
      Ideal.span (Set.range (generatorOfFamily I s hI)) := by
    refine Submodule.span_induction
      (p := fun x hx ↦ generator I ⟨x, hI.symm ▸ hx⟩ ∈
        Ideal.span (Set.range (generatorOfFamily I s hI))) ?_ ?_ ?_ ?_ hr
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      apply Ideal.subset_span
      refine ⟨i, ?_⟩
      apply Subtype.ext
      rfl
    · convert (Ideal.span (Set.range (generatorOfFamily I s hI))).zero_mem using 1
      apply Subtype.ext
      simp [generator]
    · intro x y hxmem hymem hx hy
      convert (Ideal.span (Set.range (generatorOfFamily I s hI))).add_mem hx hy using 1
      apply Subtype.ext
      simp [generator]
    · intro a x hxmem hx
      have hmul := (Ideal.span (Set.range (generatorOfFamily I s hI))).mul_mem_left
        (algebraMap R (reesAlgebra I) a) hx
      convert hmul using 1
      apply Subtype.ext
      ext n
      simp [generator, coeff_monomial]
  have heq : generator I r = generator I ⟨r.1, hI.symm ▸ hr⟩ := by
    apply Subtype.ext
    rfl
  rw [heq]
  exact hspan

/-- The standard affine chart of the blowup on which `r t` does not vanish. -/
noncomputable abbrev chart (I : Ideal R) (r : I) : Scheme :=
  Spec (.of (HomogeneousLocalization.Away (grade I) (generator I r)))

/-- The standard chart is canonically an open subscheme of the Rees `Proj`. -/
noncomputable def chartMap (I : Ideal R) (r : I) : chart I r ⟶ scheme I :=
  Proj.awayι (grade I) (generator I r) (generator_mem_grade_one I r) (by omega)

instance chartMap_isOpenImmersion (I : Ideal R) (r : I) :
    IsOpenImmersion (chartMap I r) := by
  change IsOpenImmersion
    (Proj.awayι (grade I) (generator I r) (generator_mem_grade_one I r) (by omega))
  infer_instance

/-- The image of the standard affine chart is the projective basic open `D₊(r t)`. -/
theorem chartMap_opensRange (I : Ideal R) (r : I) :
    (chartMap I r).opensRange = Proj.basicOpen (grade I) (generator I r) :=
  Proj.opensRange_awayι (grade I) (generator I r) (generator_mem_grade_one I r) (by omega)

/-- The canonical affine cover by degree-positive homogeneous localization charts. -/
noncomputable def affineOpenCover (I : Ideal R) : (scheme I).AffineOpenCover :=
  Proj.affineOpenCover (grade I)

/-- The affine cover indexed just by the degree-one elements of the centre ideal. -/
noncomputable def generatorAffineOpenCover (I : Ideal R) : (scheme I).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (grade I) (generator I)
    (m := fun _ ↦ 1) (generator_mem_grade_one I) (fun _ ↦ by omega)
    (irrelevant_le_span_generators I)

/-- An affine blowup cover indexed by any chosen family spanning the centre ideal. -/
noncomputable def affineOpenCoverOfSpan {ι : Type*} (I : Ideal R) (s : ι → R)
    (hI : I = Ideal.span (Set.range s)) : (scheme I).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (grade I) (generatorOfFamily I s hI)
    (m := fun _ ↦ 1) (generatorOfFamily_mem_grade_one I s hI) (fun _ ↦ by omega)
    (irrelevant_le_span_generatorOfFamily I s hI)

/-! ## The universal map from a principalized chart -/

section PrincipalizedChart

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- If the image of `I` is generated by `p`, every element of `Iⁿ` has a chosen quotient by
`pⁿ`.  The quotient becomes unique as soon as `p` is regular; existence alone is enough for
the construction below. -/
noncomputable def principalCoefficient (I : Ideal A) (f : A →+* B) (p : B)
    (hI : I.map f = Ideal.span {p}) (n : ℕ) (a : A) (ha : a ∈ I ^ n) : B := by
  have hm : f a ∈ (I ^ n).map f := Ideal.mem_map_of_mem f ha
  rw [Ideal.map_pow, hI, Ideal.span_singleton_pow] at hm
  exact Classical.choose (Ideal.mem_span_singleton'.mp hm)

theorem principalCoefficient_spec (I : Ideal A) (f : A →+* B) (p : B)
    (hI : I.map f = Ideal.span {p}) (n : ℕ) (a : A) (ha : a ∈ I ^ n) :
    principalCoefficient I f p hI n a ha * p ^ n = f a := by
  exact Classical.choose_spec (Ideal.mem_span_singleton'.mp (by
    have hm : f a ∈ (I ^ n).map f := Ideal.mem_map_of_mem f ha
    rwa [Ideal.map_pow, hI, Ideal.span_singleton_pow] at hm))

/-- Evaluation at `t = 1` after applying a ring map to the coefficients of a Rees polynomial. -/
noncomputable def reesEval (I : Ideal A) (f : A →+* B) : reesAlgebra I →+* B :=
  (Polynomial.eval₂RingHom f 1).comp (reesAlgebra I).val.toRingHom

@[simp]
theorem reesEval_generator (I : Ideal A) (f : A →+* B) (r : I) :
    reesEval I f (generator I r) = f r.1 := by
  simp [reesEval, generator]

/-- The degree-zero Rees chart maps canonically to the ordinary localization at the image of
its distinguished generator. -/
noncomputable def chartLocalizationMap (I : Ideal A) (f : A →+* B) (r : I) :
    HomogeneousLocalization.Away (grade I) (generator I r) →+*
      Localization.Away (f r.1) :=
  (IsLocalization.map (Localization.Away (f r.1)) (reesEval I f) (by
    change Submonoid.powers (generator I r) ≤
      (Submonoid.powers (f r.1)).comap (reesEval I f)
    intro z hz
    obtain ⟨n, rfl⟩ := hz
    change reesEval I f (generator I r ^ n) ∈ Submonoid.powers (f r.1)
    rw [map_pow, reesEval_generator]
    exact ⟨n, rfl⟩)).comp
      (algebraMap _ (Localization.Away (generator I r)))

theorem chartLocalizationMap_mk (I : Ideal A) (f : A →+* B) (r : I)
    (n : ℕ) (a : reesAlgebra I) (ha : a ∈ grade I n) :
    chartLocalizationMap I f r
        (HomogeneousLocalization.Away.mk (grade I) (generator_mem_grade_one I r) n a
          (by simpa using ha)) =
      Localization.mk (reesEval I f a)
        (⟨(f r.1) ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (f r.1)) := by
  rw [chartLocalizationMap, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk']
  rw [IsLocalization.map_mk']
  rw [← Localization.mk_eq_mk'_apply]
  congr 1
  apply Subtype.ext
  simp

theorem chartLocalizationMap_mem_range (I : Ideal A) (f : A →+* B) (r : I)
    (hI : I.map f = Ideal.span {f r.1})
    (z : HomogeneousLocalization.Away (grade I) (generator I r)) :
    chartLocalizationMap I f r z ∈
      Set.range (algebraMap B (Localization.Away (f r.1))) := by
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grade I) (generator_mem_grade_one I r) z
  have ha' : a ∈ grade I n := by
    convert ha using 1
    simp
  have hhom : ((a : reesAlgebra I) : A[X]) =
      monomial n (((a : reesAlgebra I) : A[X]).coeff n) := by
    exact ha'
  have hcoeff : ((a : A[X]).coeff n) ∈ I ^ n :=
    ((mem_reesAlgebra_iff I (a : A[X])).mp a.property) n
  let b := principalCoefficient I f (f r.1) hI n ((a : A[X]).coeff n) hcoeff
  refine ⟨b, ?_⟩
  rw [chartLocalizationMap_mk I f r n a ha']
  rw [show reesEval I f a = f ((a : A[X]).coeff n) by
    change Polynomial.eval₂ f 1 (a : A[X]) = _
    rw [hhom]
    simp]
  symm
  rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_iff_eq_mul]
  have heq := congrArg (algebraMap B (Localization.Away (f r.1)))
    (principalCoefficient_spec I f (f r.1) hI n ((a : A[X]).coeff n) hcoeff).symm
  simpa only [map_mul, map_pow] using heq

/-- The map from a homogeneous Rees chart to the corresponding ordinary localization is
injective when the coefficient map is injective and the chosen chart generator stays regular. -/
theorem chartLocalizationMap_injective (I : Ideal A) (f : A →+* B) (r : I)
    (hf : Function.Injective f) (hp : IsRegular (f r.1)) :
    Function.Injective (chartLocalizationMap I f r) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grade I) (generator_mem_grade_one I r) z
  have ha' : a ∈ grade I n := by
    convert ha using 1
    simp
  rw [chartLocalizationMap_mk I f r n a ha'] at hz
  rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff] at hz
  obtain ⟨m, hm⟩ := hz
  have hregular : IsRegular (m.1 : B) := by
    obtain ⟨j, hj⟩ := m.2
    rw [← hj]
    exact hp.pow j
  have heval : reesEval I f a = 0 := by
    apply hregular.left
    simpa using hm
  have hhom : ((a : reesAlgebra I) : A[X]) =
      monomial n (((a : reesAlgebra I) : A[X]).coeff n) := ha'
  have hcoeff : f (((a : reesAlgebra I) : A[X]).coeff n) = 0 := by
    change Polynomial.eval₂ f 1 (a : A[X]) = 0 at heval
    rw [hhom] at heval
    simpa using heval
  have hcoeffzero : ((a : reesAlgebra I) : A[X]).coeff n = 0 := by
    apply hf
    simpa using hcoeff
  have hazero : a = 0 := by
    apply Subtype.ext
    rw [hhom, hcoeffzero]
    simp
  subst a
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero]
  change Localization.mk (0 : reesAlgebra I) _ = 0
  rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
  exact ⟨1, by simp⟩

theorem powers_le_nonZeroDivisors_of_isRegular (p : B) (hp : IsRegular p) :
    Submonoid.powers p ≤ nonZeroDivisors B := by
  intro z hz
  obtain ⟨n, rfl⟩ := hz
  exact (hp.pow n).mem_nonZeroDivisors

/-- The underlying chosen lift from a Rees chart to a ring in which the centre is principal. -/
noncomputable def chartLiftFun (I : Ideal A) (f : A →+* B) (r : I)
    (hI : I.map f = Ideal.span {f r.1})
    (z : HomogeneousLocalization.Away (grade I) (generator I r)) : B :=
  Classical.choose (chartLocalizationMap_mem_range I f r hI z)

theorem chartLiftFun_spec (I : Ideal A) (f : A →+* B) (r : I)
    (hI : I.map f = Ideal.span {f r.1})
    (z : HomogeneousLocalization.Away (grade I) (generator I r)) :
    algebraMap B (Localization.Away (f r.1)) (chartLiftFun I f r hI z) =
      chartLocalizationMap I f r z :=
  Classical.choose_spec (chartLocalizationMap_mem_range I f r hI z)

/-- Universal ring map from the Rees chart associated to `r` to a principalization of `I`.
Regularity of the chosen generator makes the descent from `B[(f r)⁻¹]` to `B` unique. -/
noncomputable def chartLift (I : Ideal A) (f : A →+* B) (r : I)
    (hp : IsRegular (f r.1)) (hI : I.map f = Ideal.span {f r.1}) :
    HomogeneousLocalization.Away (grade I) (generator I r) →+* B where
  toFun := chartLiftFun I f r hI
  map_one' := by
    apply IsLocalization.injective (Localization.Away (f r.1))
      (powers_le_nonZeroDivisors_of_isRegular (f r.1) hp)
    calc
      algebraMap B (Localization.Away (f r.1)) (chartLiftFun I f r hI 1) =
          chartLocalizationMap I f r 1 := chartLiftFun_spec I f r hI 1
      _ = 1 := (chartLocalizationMap I f r).map_one
      _ = algebraMap B (Localization.Away (f r.1)) 1 :=
        (map_one (algebraMap B (Localization.Away (f r.1)))).symm
  map_mul' x y := by
    apply IsLocalization.injective (Localization.Away (f r.1))
      (powers_le_nonZeroDivisors_of_isRegular (f r.1) hp)
    calc
      algebraMap B (Localization.Away (f r.1)) (chartLiftFun I f r hI (x * y)) =
          chartLocalizationMap I f r (x * y) := chartLiftFun_spec I f r hI (x * y)
      _ = chartLocalizationMap I f r x * chartLocalizationMap I f r y :=
        (chartLocalizationMap I f r).map_mul x y
      _ = algebraMap B (Localization.Away (f r.1)) (chartLiftFun I f r hI x) *
          algebraMap B (Localization.Away (f r.1)) (chartLiftFun I f r hI y) := by
        rw [chartLiftFun_spec, chartLiftFun_spec]
      _ = algebraMap B (Localization.Away (f r.1))
          (chartLiftFun I f r hI x * chartLiftFun I f r hI y) :=
        (map_mul (algebraMap B (Localization.Away (f r.1))) _ _).symm
  map_zero' := by
    apply IsLocalization.injective (Localization.Away (f r.1))
      (powers_le_nonZeroDivisors_of_isRegular (f r.1) hp)
    calc
      algebraMap B (Localization.Away (f r.1)) (chartLiftFun I f r hI 0) =
          chartLocalizationMap I f r 0 := chartLiftFun_spec I f r hI 0
      _ = 0 := (chartLocalizationMap I f r).map_zero
      _ = algebraMap B (Localization.Away (f r.1)) 0 :=
        (map_zero (algebraMap B (Localization.Away (f r.1)))).symm
  map_add' x y := by
    apply IsLocalization.injective (Localization.Away (f r.1))
      (powers_le_nonZeroDivisors_of_isRegular (f r.1) hp)
    calc
      algebraMap B (Localization.Away (f r.1)) (chartLiftFun I f r hI (x + y)) =
          chartLocalizationMap I f r (x + y) := chartLiftFun_spec I f r hI (x + y)
      _ = chartLocalizationMap I f r x + chartLocalizationMap I f r y :=
        (chartLocalizationMap I f r).map_add x y
      _ = algebraMap B (Localization.Away (f r.1)) (chartLiftFun I f r hI x) +
          algebraMap B (Localization.Away (f r.1)) (chartLiftFun I f r hI y) := by
        rw [chartLiftFun_spec, chartLiftFun_spec]
      _ = algebraMap B (Localization.Away (f r.1))
          (chartLiftFun I f r hI x + chartLiftFun I f r hI y) :=
        (map_add (algebraMap B (Localization.Away (f r.1))) _ _).symm

@[simp]
theorem algebraMap_chartLift (I : Ideal A) (f : A →+* B) (r : I)
    (hp : IsRegular (f r.1)) (hI : I.map f = Ideal.span {f r.1})
    (z : HomogeneousLocalization.Away (grade I) (generator I r)) :
    algebraMap B (Localization.Away (f r.1)) (chartLift I f r hp hI z) =
      chartLocalizationMap I f r z :=
  chartLiftFun_spec I f r hI z

/-- The universal map to a principalized chart is injective when the original coefficient map
is injective. -/
theorem chartLift_injective (I : Ideal A) (f : A →+* B) (r : I)
    (hf : Function.Injective f) (hp : IsRegular (f r.1))
    (hI : I.map f = Ideal.span {f r.1}) :
    Function.Injective (chartLift I f r hp hI) := by
  intro x y hxy
  apply chartLocalizationMap_injective I f r hf hp
  rw [← algebraMap_chartLift I f r hp hI,
    ← algebraMap_chartLift I f r hp hI, hxy]

/-- On a represented homogeneous fraction, `chartLift` is the quotient of its coefficient by
the corresponding power of the principal generator. -/
theorem chartLift_mk (I : Ideal A) (f : A →+* B) (r : I)
    (hp : IsRegular (f r.1)) (hI : I.map f = Ideal.span {f r.1})
    (n : ℕ) (a : reesAlgebra I) (ha : a ∈ grade I n) :
    chartLift I f r hp hI
        (HomogeneousLocalization.Away.mk (grade I)
          (generator_mem_grade_one I r) n a (by simpa using ha)) =
      principalCoefficient I f (f r.1) hI n
        ((a : A[X]).coeff n)
        (((mem_reesAlgebra_iff I (a : A[X])).mp a.property) n) := by
  let c := ((a : A[X]).coeff n)
  let hc : c ∈ I ^ n := ((mem_reesAlgebra_iff I (a : A[X])).mp a.property) n
  apply IsLocalization.injective (Localization.Away (f r.1))
    (powers_le_nonZeroDivisors_of_isRegular (f r.1) hp)
  rw [algebraMap_chartLift]
  rw [chartLocalizationMap_mk I f r n a ha]
  have hhom : (a : A[X]) = monomial n ((a : A[X]).coeff n) := ha
  rw [show reesEval I f a = f c by
    change Polynomial.eval₂ f 1 (a : A[X]) = _
    rw [hhom]
    simp [c]]
  rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_iff_eq_mul]
  have heq := congrArg (algebraMap B (Localization.Away (f r.1)))
    (principalCoefficient_spec I f (f r.1) hI n c hc)
  simpa only [map_mul, map_pow] using heq.symm

/-- The structure map from the affine base ring to a standard Rees chart. -/
noncomputable def baseRingHom (I : Ideal A) (r : I) :
    A →+* HomogeneousLocalization.Away (grade I) (generator I r) :=
  (HomogeneousLocalization.fromZeroRingHom (grade I)
    (Submonoid.powers (generator I r))).comp (zeroEquiv I).symm.toRingHom

/-- A base-ring element regarded as a degree-zero function on a standard Rees chart. -/
noncomputable def baseElement (I : Ideal A) (r : I) (a : A) :
    HomogeneousLocalization.Away (grade I) (generator I r) :=
  HomogeneousLocalization.Away.mk (grade I)
    (generator_mem_grade_one I r) 0
    (algebraMap A (reesAlgebra I) a) (by
      change ((algebraMap A (reesAlgebra I) a : reesAlgebra I) : A[X]) =
      monomial 0 ((((algebraMap A (reesAlgebra I) a : reesAlgebra I) : A[X]).coeff 0))
      simp)

@[simp]
theorem baseRingHom_apply (I : Ideal A) (r : I) (a : A) :
    baseRingHom I r a = baseElement I r a := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk
      (component I (algebraMap A (reesAlgebra I) a) 0 : reesAlgebra I) _ =
    Localization.mk (algebraMap A (reesAlgebra I) a) _
  congr 1
  apply Subtype.ext
  simp [component]

/-- On a standard Rees chart, the blowup projection is induced by the base-ring inclusion. -/
theorem chartMap_projection (I : Ideal A) (r : I) :
    chartMap I r ≫ projection I =
      Spec.map (CommRingCat.ofHom (baseRingHom I r)) := by
  rw [chartMap, projection, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

@[simp]
theorem chartLift_baseElement (I : Ideal A) (f : A →+* B) (r : I)
    (hp : IsRegular (f r.1)) (hI : I.map f = Ideal.span {f r.1}) (a : A) :
    chartLift I f r hp hI (baseElement I r a) = f a := by
  have hbase : (algebraMap A (reesAlgebra I) a : reesAlgebra I) ∈ grade I 0 := by
    change ((algebraMap A (reesAlgebra I) a : reesAlgebra I) : A[X]) =
      monomial 0 ((((algebraMap A (reesAlgebra I) a : reesAlgebra I) : A[X]).coeff 0))
    simp
  rw [baseElement, chartLift_mk I f r hp hI 0 _ hbase]
  have hspec := principalCoefficient_spec I f (f r.1) hI 0
    (((algebraMap A (reesAlgebra I) a : reesAlgebra I) : A[X]).coeff 0)
    (((mem_reesAlgebra_iff I
      ((algebraMap A (reesAlgebra I) a : reesAlgebra I) : A[X])).mp
        (algebraMap A (reesAlgebra I) a : reesAlgebra I).property) 0)
  simpa using hspec

@[simp]
theorem chartLift_baseRingHom (I : Ideal A) (f : A →+* B) (r : I)
    (hp : IsRegular (f r.1)) (hI : I.map f = Ideal.span {f r.1}) (a : A) :
    chartLift I f r hp hI (baseRingHom I r a) = f a := by
  rw [baseRingHom_apply, chartLift_baseElement]

/-- The degree-zero ratio `(s t)/(r t)` on the standard chart indexed by `r`. -/
noncomputable def ratioElement (I : Ideal A) (r s : I) :
    HomogeneousLocalization.Away (grade I) (generator I r) :=
  HomogeneousLocalization.Away.mk (grade I)
    (generator_mem_grade_one I r) 1 (generator I s)
    (by simpa using generator_mem_grade_one I s)

@[simp]
theorem chartLift_ratioElement (I : Ideal A) (f : A →+* B) (r s : I)
    (hp : IsRegular (f r.1)) (hI : I.map f = Ideal.span {f r.1}) (q : B)
    (hq : q * f r.1 = f s.1) :
    chartLift I f r hp hI (ratioElement I r s) = q := by
  have hgen : generator I s ∈ grade I 1 := generator_mem_grade_one I s
  rw [ratioElement, chartLift_mk I f r hp hI 1 _ hgen]
  apply hp.right
  calc
    principalCoefficient I f (f r.1) hI 1
          (((generator I s : reesAlgebra I) : A[X]).coeff 1) _ * f r.1 =
        f s.1 := by
      simpa [generator] using
        principalCoefficient_spec I f (f r.1) hI 1
          (((generator I s : reesAlgebra I) : A[X]).coeff 1)
          (((mem_reesAlgebra_iff I
            ((generator I s : reesAlgebra I) : A[X])).mp
              (generator I s).property) 1)
    _ = q * f r.1 := hq.symm

/-- Multiplying the ratio `(s t)/(r t)` by the base function `r` recovers the base
function `s`. -/
theorem baseElement_mul_ratioElement (I : Ideal A) (r s : I) :
    baseElement I r r.1 * ratioElement I r s = baseElement I r s.1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, baseElement, ratioElement,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_mul]
  simp_rw [Localization.mk_eq_mk'_apply]
  rw [IsLocalization.mk'_eq_iff_eq]
  simp only [pow_zero, pow_one, Submonoid.coe_mul, one_mul]
  congr 1
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_mul]
  change C r.1 * monomial 1 s.1 = monomial 1 r.1 * C s.1
  simp [mul_comm]

/-- A product of two chart ratios is a base function whenever the corresponding cross-multiplied
identity holds in the base ring. -/
theorem ratioElement_mul_ratioElement_eq_baseElement (I : Ideal A) (r s t : I) (a : A)
    (h : s.1 * t.1 = r.1 ^ 2 * a) :
    ratioElement I r s * ratioElement I r t = baseElement I r a := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, ratioElement, baseElement,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_mul]
  simp_rw [Localization.mk_eq_mk'_apply]
  rw [IsLocalization.mk'_eq_iff_eq]
  simp only [pow_zero, pow_one, Submonoid.coe_mul, one_mul]
  congr 1
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_mul]
  change monomial 1 s.1 * monomial 1 t.1 =
    (monomial 1 r.1 * monomial 1 r.1) * C a
  simp only [monomial_mul_monomial, one_add_one_eq_two, monomial_mul_C]
  rw [h]
  simp [pow_two]

/-! ## The base principal open inside a Rees blowup -/

/-- On the standard chart indexed by `r`, the chart-to-`A[r⁻¹]` map sends every base
function to its ordinary localization. -/
@[simp]
theorem chartLocalizationMap_id_baseElement (I : Ideal A) (r : I) (a : A) :
    chartLocalizationMap I (RingHom.id A) r (baseElement I r a) =
      algebraMap A (Localization.Away r.1) a := by
  have hbase : (algebraMap A (reesAlgebra I) a : reesAlgebra I) ∈ grade I 0 := by
    change C a = monomial 0 ((C a).coeff 0)
    simp
  rw [baseElement, chartLocalizationMap_mk I (RingHom.id A) r 0 _ hbase]
  rw [show reesEval I (RingHom.id A) (algebraMap A (reesAlgebra I) a) = a by
    simp [reesEval]]
  rw [Localization.mk_eq_mk'_apply]
  apply (IsLocalization.mk'_eq_iff_eq_mul).mpr
  simp

/-- Further inverting the base function `r` on the standard `r t` chart gives exactly the
ordinary localization `A[r⁻¹]`.  This is the ring-level complement theorem and does not
require `r` to be regular. -/
theorem chartLocalizationMap_id_isLocalization (I : Ideal A) (r : I) :
    letI := (chartLocalizationMap I (RingHom.id A) r).toAlgebra
    IsLocalization.Away (baseElement I r r.1) (Localization.Away r.1) := by
  let _ := (chartLocalizationMap I (RingHom.id A) r).toAlgebra
  apply IsLocalization.Away.mk
  · change IsUnit (chartLocalizationMap I (RingHom.id A) r (baseElement I r r.1))
    rw [chartLocalizationMap_id_baseElement]
    exact IsLocalization.Away.algebraMap_isUnit r.1
  · intro z
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj r.1 z
    refine ⟨n, baseElement I r a, ?_⟩
    change z * chartLocalizationMap I (RingHom.id A) r (baseElement I r r.1) ^ n =
      chartLocalizationMap I (RingHom.id A) r (baseElement I r a)
    simpa only [chartLocalizationMap_id_baseElement, map_pow] using ha
  · intro x y hxy
    obtain ⟨n, a, ha, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (grade I) (generator_mem_grade_one I r) x
    obtain ⟨m, b, hb, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (grade I) (generator_mem_grade_one I r) y
    have ha' : a ∈ grade I n := by
      convert ha using 1
      simp
    have hb' : b ∈ grade I m := by
      convert hb using 1
      simp
    change chartLocalizationMap I (RingHom.id A) r
        (HomogeneousLocalization.Away.mk (grade I)
          (generator_mem_grade_one I r) n a ha) =
      chartLocalizationMap I (RingHom.id A) r
        (HomogeneousLocalization.Away.mk (grade I)
          (generator_mem_grade_one I r) m b hb) at hxy
    rw [chartLocalizationMap_mk I (RingHom.id A) r n a ha',
      chartLocalizationMap_mk I (RingHom.id A) r m b hb'] at hxy
    have hae : reesEval I (RingHom.id A) a = (a : A[X]).coeff n := by
      change Polynomial.eval₂ (RingHom.id A) 1 (a : A[X]) = _
      rw [show (a : A[X]) = monomial n ((a : A[X]).coeff n) from ha']
      simp
    have hbe : reesEval I (RingHom.id A) b = (b : A[X]).coeff m := by
      change Polynomial.eval₂ (RingHom.id A) 1 (b : A[X]) = _
      rw [show (b : A[X]) = monomial m ((b : A[X]).coeff m) from hb']
      simp
    rw [hae, hbe] at hxy
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hxy
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := hxy
    refine ⟨k, ?_⟩
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
      HomogeneousLocalization.Away.val_mk, baseElement]
    simp only [Localization.mk_pow, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow]
    apply Subtype.ext
    simp only [pow_zero, one_pow, one_mul, Subalgebra.coe_mul]
    change (generator I r : A[X]) ^ m * (C r.1 ^ k * (a : A[X])) =
      (generator I r : A[X]) ^ n * (C r.1 ^ k * (b : A[X]))
    rw [show (a : A[X]) = monomial n ((a : A[X]).coeff n) from ha',
      show (b : A[X]) = monomial m ((b : A[X]).coeff m) from hb']
    rw [← C_pow]
    simp only [generator, Subtype.coe_mk, monomial_pow, ← monomial_zero_left,
      monomial_mul_monomial]
    rw [one_mul, zero_add, one_mul, zero_add, Nat.add_comm m n]
    congr 1
    simpa [mul_assoc, mul_comm, mul_left_comm] using hk

/-- The pullback of the center ideal to every standard Rees chart is principal, generated by
the base equation of that chart's distinguished element. -/
theorem map_baseRingHom_eq_span_baseElement (I : Ideal A) (r : I) :
    I.map (baseRingHom I r) = Ideal.span {baseElement I r r.1} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change baseRingHom I r a ∈ Ideal.span {baseElement I r r.1}
    rw [baseRingHom_apply, ← baseElement_mul_ratioElement I r ⟨a, ha⟩]
    exact Ideal.mul_mem_right (ratioElement I r ⟨a, ha⟩) _
      (Ideal.subset_span (Set.mem_singleton _))
  · rw [Ideal.span_le]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    rw [← baseRingHom_apply]
    exact Ideal.mem_map_of_mem (baseRingHom I r) r.2

/-- If the chart generator is regular on the base, its equation for the exceptional locus
remains regular on the standard Rees chart. -/
theorem baseElement_isRegular (I : Ideal A) (r : I) (hr : IsRegular r.1) :
    IsRegular (baseElement I r r.1) := by
  have hinj : Function.Injective (chartLocalizationMap I (RingHom.id A) r) :=
    chartLocalizationMap_injective I (RingHom.id A) r (fun _ _ h ↦ h) hr
  apply (Commute.isRegular_iff (Commute.all _)).mpr
  intro x y hxy
  apply hinj
  have hmap := congrArg (chartLocalizationMap I (RingHom.id A) r) hxy
  simp only [map_mul, chartLocalizationMap_id_baseElement] at hmap
  exact (IsLocalization.Away.algebraMap_isUnit r.1).mul_left_cancel hmap

/-- Pulling a base principal open back to a standard Rees chart gives the principal open
of the corresponding base function on that chart. -/
@[simp]
theorem chartMap_preimage_projection_basicOpen (I : Ideal A) (s : I) (a : A) :
    chartMap I s ⁻¹ᵁ (projection I ⁻¹ᵁ PrimeSpectrum.basicOpen a) =
      PrimeSpectrum.basicOpen (baseElement I s a) := by
  change (chartMap I s ≫ projection I) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen a : (Spec (.of A)).Opens) = _
  rw [chartMap_projection,
    AlgebraicGeometry.SpecMap_preimage_basicOpen]
  exact congrArg PrimeSpectrum.basicOpen (baseRingHom_apply I s a)

/-- Pulling the range of one standard Rees chart back to another gives the principal
open of their degree-zero ratio. -/
@[simp]
theorem chartMap_preimage_chartMap_opensRange (I : Ideal A) (s r : I) :
    chartMap I s ⁻¹ᵁ (chartMap I r).opensRange =
      PrimeSpectrum.basicOpen (ratioElement I s r) := by
  rw [chartMap_opensRange]
  change Proj.awayι (grade I) (generator I s) (generator_mem_grade_one I s) (by omega)
      ⁻¹ᵁ Proj.basicOpen (grade I) (generator I r) = _
  rw [Proj.awayι_preimage_basicOpen (grade I)
    (generator_mem_grade_one I s) (by omega)
    (generator_mem_grade_one I r) (by omega)]
  congr 2
  simp only [HomogeneousLocalization.Away.isLocalizationElem, ratioElement,
    pow_one]

/-- On every standard chart, the pullback of the base open `D(r)` is contained in the
overlap with the `r t` chart. -/
theorem chartMap_preimage_projection_basicOpen_le_chartRange
    (I : Ideal A) (s r : I) :
    chartMap I s ⁻¹ᵁ (projection I ⁻¹ᵁ PrimeSpectrum.basicOpen r.1) ≤
      chartMap I s ⁻¹ᵁ (chartMap I r).opensRange := by
  rw [chartMap_preimage_projection_basicOpen,
    chartMap_preimage_chartMap_opensRange]
  rw [← baseElement_mul_ratioElement I s r,
    PrimeSpectrum.basicOpen_mul]
  exact inf_le_right

/-- Above the base principal open `D(r)`, every point of the blowup lies in the
standard Rees chart `D₊(r t)`. -/
theorem projection_preimage_basicOpen_le_chartMap_opensRange
    (I : Ideal A) (r : I) :
    projection I ⁻¹ᵁ PrimeSpectrum.basicOpen r.1 ≤
      (chartMap I r).opensRange := by
  have hcover : ⨆ s : I, (chartMap I s).opensRange = ⊤ := by
    simpa only [chartMap_opensRange] using
      Proj.iSup_basicOpen_eq_top (grade I) (generator I)
        (irrelevant_le_span_generators I)
  let U : (scheme I).Opens :=
    projection I ⁻¹ᵁ PrimeSpectrum.basicOpen r.1
  change U ≤ (chartMap I r).opensRange
  calc
    U = ⊤ ⊓ U := (top_inf_eq U).symm
    _ = (⨆ s : I, (chartMap I s).opensRange) ⊓ U := by rw [hcover]
    _ = ⨆ s : I, (chartMap I s).opensRange ⊓ U :=
      iSup_inf_eq (fun s : I ↦ (chartMap I s).opensRange) U
    _ ≤ (chartMap I r).opensRange := by
      apply iSup_le
      intro s
      rw [← (chartMap I s).image_preimage_eq_opensRange_inf U]
      exact ((chartMap I s).image_mono
        (chartMap_preimage_projection_basicOpen_le_chartRange I s r)).trans
          ((chartMap I s).image_preimage_le (chartMap I r).opensRange)

@[simp]
theorem chartLocalizationMap_id_baseRingHom (I : Ideal A) (r : I) (a : A) :
    chartLocalizationMap I (RingHom.id A) r (baseRingHom I r a) =
      algebraMap A (Localization.Away r.1) a := by
  rw [baseRingHom_apply, chartLocalizationMap_id_baseElement]

/-- The base principal open `Spec A[r⁻¹]` as an open subscheme of the affine Rees blowup.
Its image lies in the standard chart `D₊(r t)`. -/
noncomputable def principalOpenMap (I : Ideal A) (r : I) :
    Spec (.of (Localization.Away r.1)) ⟶ scheme I :=
  Spec.map (CommRingCat.ofHom (chartLocalizationMap I (RingHom.id A) r)) ≫
    chartMap I r

/-- The map from the base principal open to the standard `r t` chart is itself an open
immersion. -/
noncomputable instance principalOpenChartMap_isOpenImmersion (I : Ideal A) (r : I) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (chartLocalizationMap I (RingHom.id A) r))) := by
  let _ := (chartLocalizationMap I (RingHom.id A) r).toAlgebra
  let _ : IsLocalization.Away (baseElement I r r.1) (Localization.Away r.1) :=
    chartLocalizationMap_id_isLocalization I r
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (HomogeneousLocalization.Away (grade I) (generator I r))
      (Localization.Away r.1))))
  exact IsOpenImmersion.of_isLocalization (baseElement I r r.1)

noncomputable instance principalOpenMap_isOpenImmersion (I : Ideal A) (r : I) :
    IsOpenImmersion (principalOpenMap I r) := by
  unfold principalOpenMap
  infer_instance

/-- The localization map onto the base principal open has image the corresponding
principal open inside the standard Rees chart. -/
theorem principalOpenChartMap_opensRange (I : Ideal A) (r : I) :
    (Spec.map (CommRingCat.ofHom
      (chartLocalizationMap I (RingHom.id A) r))).opensRange =
        PrimeSpectrum.basicOpen (baseElement I r r.1) := by
  let _ := (chartLocalizationMap I (RingHom.id A) r).toAlgebra
  let _ : IsLocalization.Away (baseElement I r r.1) (Localization.Away r.1) :=
    chartLocalizationMap_id_isLocalization I r
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (HomogeneousLocalization.Away (grade I) (generator I r))
        (Localization.Away r.1)))) :=
    IsOpenImmersion.of_isLocalization (baseElement I r r.1)
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (HomogeneousLocalization.Away (grade I) (generator I r))
      (Localization.Away r.1)))).opensRange = _
  exact TopologicalSpace.Opens.ext <|
    PrimeSpectrum.localization_away_comap_range
      (Localization.Away r.1) (baseElement I r r.1)

/-- The base principal open inside the affine Rees blowup is exactly the full inverse
image of that principal open under the blowup projection. -/
theorem principalOpenMap_opensRange (I : Ideal A) (r : I) :
    (principalOpenMap I r).opensRange =
      projection I ⁻¹ᵁ PrimeSpectrum.basicOpen r.1 := by
  let U : (scheme I).Opens :=
    projection I ⁻¹ᵁ PrimeSpectrum.basicOpen r.1
  change (Spec.map (CommRingCat.ofHom
      (chartLocalizationMap I (RingHom.id A) r)) ≫ chartMap I r).opensRange = U
  rw [Scheme.Hom.opensRange_comp,
    principalOpenChartMap_opensRange]
  rw [← chartMap_preimage_projection_basicOpen]
  rw [(chartMap I r).image_preimage_eq_opensRange_inf]
  exact inf_eq_right.mpr (projection_preimage_basicOpen_le_chartMap_opensRange I r)

/-- On the principal-open copy inside the blowup, the blowup projection is the ordinary
principal-open immersion into the affine base. -/
theorem principalOpenMap_projection (I : Ideal A) (r : I) :
    principalOpenMap I r ≫ projection I =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r.1))) := by
  rw [principalOpenMap, Category.assoc, chartMap_projection, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact chartLocalizationMap_id_baseRingHom I r a

/-- The affine complement square formed by the blowup projection and the ordinary
principal-open immersion is cartesian. -/
theorem principalOpenMap_isPullback (I : Ideal A) (r : I) :
    IsPullback (𝟙 (Spec (.of (Localization.Away r.1)))) (principalOpenMap I r)
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r.1))))
      (projection I) := by
  apply IsOpenImmersion.isPullback
  · simpa using principalOpenMap_projection I r
  · have hj :
        (Spec.map (CommRingCat.ofHom
          (algebraMap A (Localization.Away r.1)))).opensRange =
            PrimeSpectrum.basicOpen r.1 := by
        exact TopologicalSpace.Opens.ext <|
          PrimeSpectrum.localization_away_comap_range
            (Localization.Away r.1) r.1
    exact (congrArg (fun U ↦ projection I ⁻¹ᵁ U) hj).trans
      (principalOpenMap_opensRange I r).symm

/-- The open complement of the affine center, written as the union of its principal opens. -/
noncomputable def baseComplement (I : Ideal A) : (Spec (.of A)).Opens :=
  ⨆ r : I, PrimeSpectrum.basicOpen r.1

/-- The blowup projection restricts to an isomorphism over each principal open in the
complement of the center. -/
theorem projection_restrict_basicOpen_isIso (I : Ideal A) (r : I) :
    IsIso (projection I ∣_ (PrimeSpectrum.basicOpen r.1 : (Spec (.of A)).Opens)) := by
  let j : Spec (.of (Localization.Away r.1)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r.1)))
  have hj : j.opensRange =
      (PrimeSpectrum.basicOpen r.1 : (Spec (.of A)).Opens) := by
    exact TopologicalSpace.Opens.ext <|
      PrimeSpectrum.localization_away_comap_range (Localization.Away r.1) r.1
  have hpb : IsPullback (principalOpenMap I r)
      (𝟙 (Spec (.of (Localization.Away r.1)))) (projection I) j := by
    exact (principalOpenMap_isPullback I r).flip
  let e := hpb.isoOverPullback
  have he : e.hom.left ≫ Limits.pullback.snd (projection I) j =
      𝟙 (Spec (.of (Localization.Away r.1))) := by
    simp [e]
  let _ : IsIso e.hom.left := by
    change IsIso ((Over.forget _).map e.hom)
    infer_instance
  let _ : IsIso (e.hom.left ≫ Limits.pullback.snd (projection I) j) := by
    exact he ▸ (inferInstance : IsIso
      (𝟙 (Spec (.of (Localization.Away r.1)))))
  let _ : IsIso (Limits.pullback.snd (projection I) j) :=
    IsIso.of_isIso_comp_left e.hom.left (Limits.pullback.snd (projection I) j)
  rw [← MorphismProperty.isomorphisms.iff]
  rw [← hj]
  exact (MorphismProperty.arrow_mk_iso_iff
    (MorphismProperty.isomorphisms Scheme)
      (morphismRestrictOpensRange (projection I) j)).mpr (by
        rw [MorphismProperty.isomorphisms.iff]
        infer_instance)

/-- The affine Rees blowup projection is an isomorphism over the whole complement of its
center. -/
theorem projection_restrict_baseComplement_isIso (I : Ideal A) :
    IsIso (projection I ∣_ baseComplement I) := by
  let U : (Spec (.of A)).Opens := baseComplement I
  let W : I → (Spec (.of A)).Opens := fun r ↦
    (PrimeSpectrum.basicOpen r.1 : (Spec (.of A)).Opens)
  let V : I → U.toScheme.Opens := fun r ↦ U.ι ⁻¹ᵁ W r
  have hcover : ⨆ r : I, V r = ⊤ := by
    calc
      ⨆ r : I, V r = U.ι ⁻¹ᵁ (⨆ r : I, W r) :=
        (U.ι.preimage_iSup W).symm
      _ = U.ι ⁻¹ᵁ U := by rfl
      _ = ⊤ := by
        simpa only [Scheme.Opens.opensRange_ι] using U.ι.preimage_opensRange
  rw [← MorphismProperty.isomorphisms.iff]
  apply IsZariskiLocalAtTarget.of_iSup_eq_top V hcover
  intro r
  have himage : U.ι ''ᵁ V r =
      (PrimeSpectrum.basicOpen r.1 : (Spec (.of A)).Opens) := by
    change U.ι ''ᵁ V r = W r
    have hpre : U.ι ''ᵁ V r = U.ι.opensRange ⊓ W r :=
      U.ι.image_preimage_eq_opensRange_inf (W r)
    have hrange : U.ι.opensRange = U := Scheme.Opens.opensRange_ι U
    have hle : W r ≤ U := by
      change (PrimeSpectrum.basicOpen r.1 : (Spec (.of A)).Opens) ≤
        baseComplement I
      exact le_iSup (fun s : I ↦
        (PrimeSpectrum.basicOpen s.1 : (Spec (.of A)).Opens)) r
    calc
      U.ι ''ᵁ V r = U.ι.opensRange ⊓ W r := hpre
      _ = U ⊓ W r := congrArg (fun Z ↦ Z ⊓ W r) hrange
      _ = W r := inf_eq_right.mpr hle
  let e := morphismRestrictRestrict (projection I) U (V r) ≪≫
    morphismRestrictEq (projection I) himage
  exact (MorphismProperty.arrow_mk_iso_iff
    (MorphismProperty.isomorphisms Scheme) e).mpr (by
      rw [MorphismProperty.isomorphisms.iff]
      exact projection_restrict_basicOpen_isIso I r)

/-! ## The scheme-theoretic exceptional locus -/

/-- The affine center as a closed subscheme. -/
noncomputable abbrev center (I : Ideal A) : Scheme := Spec (.of (A ⧸ I))

/-- The closed immersion of the center into the affine base. -/
noncomputable def centerι (I : Ideal A) : center I ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

instance centerι_isClosedImmersion (I : Ideal A) : IsClosedImmersion (centerι I) := by
  apply IsClosedImmersion.spec_of_surjective
  exact Ideal.Quotient.mk_surjective

/-- The exceptional subscheme is the scheme-theoretic inverse image of the center. -/
noncomputable abbrev exceptional (I : Ideal A) : Scheme :=
  Limits.pullback (projection I) (centerι I)

/-- The exceptional subscheme as a closed subscheme of the blowup. -/
noncomputable def exceptionalι (I : Ideal A) : exceptional I ⟶ scheme I :=
  Limits.pullback.fst (projection I) (centerι I)

instance exceptionalι_isClosedImmersion (I : Ideal A) :
    IsClosedImmersion (exceptionalι I) := by
  unfold exceptionalι
  infer_instance

/-- Projection from the exceptional subscheme to the center. -/
noncomputable def exceptionalToCenter (I : Ideal A) : exceptional I ⟶ center I :=
  Limits.pullback.snd (projection I) (centerι I)

@[reassoc]
theorem exceptional_square (I : Ideal A) :
    exceptionalι I ≫ projection I = exceptionalToCenter I ≫ centerι I := by
  exact Limits.pullback.condition

/-- The exceptional subscheme is the cartesian inverse image of the center. -/
theorem exceptional_isPullback (I : Ideal A) :
    IsPullback (exceptionalι I) (exceptionalToCenter I)
      (projection I) (centerι I) :=
  IsPullback.of_hasPullback _ _

/-- Set-theoretically, the exceptional subscheme is exactly the inverse image of the center. -/
theorem exceptionalι_range (I : Ideal A) :
    Set.range (exceptionalι I) =
      (projection I) ⁻¹' Set.range (centerι I) := by
  unfold exceptionalι
  exact Scheme.Pullback.range_fst _ _

/-! ## Scheme-theoretic and reduced strict transforms -/

/-- The inverse image in the blowup of the open complement of the center. -/
noncomputable def blowupComplement (I : Ideal A) : (scheme I).Opens :=
  projection I ⁻¹ᵁ baseComplement I

/-- The ideal of the inverse image of a closed subscheme over the complement of the center. -/
noncomputable def strictTransformOpenPartIdeal (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) : (blowupComplement I).toScheme.IdealSheafData :=
  J.comap ((blowupComplement I).ι ≫ projection I)

/-- The ideal of the scheme-theoretic closure in the blowup of the inverse image away from the
center.  The `IdealSheafData.map` construction is the kernel of the composite of the open-part
closed immersion with the open immersion into the blowup, so it retains nilpotent structure. -/
noncomputable def strictTransformIdeal (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) : (scheme I).IdealSheafData :=
  (strictTransformOpenPartIdeal I J).map (blowupComplement I).ι

/-- The scheme-theoretic strict transform as a closed subscheme of the blowup. -/
noncomputable abbrev strictTransform (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) : Scheme :=
  (strictTransformIdeal I J).subscheme

/-- The closed immersion of the scheme-theoretic strict transform into the blowup. -/
noncomputable def strictTransformι (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) : strictTransform I J ⟶ scheme I :=
  (strictTransformIdeal I J).subschemeι

instance strictTransformι_isClosedImmersion (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) :
    IsClosedImmersion (strictTransformι I J) := by
  unfold strictTransformι
  infer_instance

/-- The open part whose scheme-theoretic closure is the strict transform. -/
noncomputable abbrev strictTransformOpenPart (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) : Scheme :=
  (strictTransformOpenPartIdeal I J).subscheme

/-- The canonical map from the open inverse-image part into its scheme-theoretic closure. -/
noncomputable def strictTransformOpenMap (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) :
    strictTransformOpenPart I J ⟶ strictTransform I J :=
  Scheme.IdealSheafData.subschemeMap
    (strictTransformOpenPartIdeal I J) (strictTransformIdeal I J)
    (blowupComplement I).ι le_rfl

@[reassoc (attr := simp)]
theorem strictTransformOpenMap_comp_ι (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) :
    strictTransformOpenMap I J ≫ strictTransformι I J =
      (strictTransformOpenPartIdeal I J).subschemeι ≫ (blowupComplement I).ι := by
  exact Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- Universal property of the scheme-theoretic closure: an ideal on the blowup cuts out a
closed subscheme through which the open part factors exactly when its restriction is contained
in the open-part ideal. -/
theorem strictTransformIdeal_le_iff (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) (K : (scheme I).IdealSheafData) :
    K ≤ strictTransformIdeal I J ↔
      K.comap (blowupComplement I).ι ≤ strictTransformOpenPartIdeal I J := by
  exact Scheme.IdealSheafData.le_map_iff_comap_le

/-- Restricting the schematic closure back to the complement maps into the original open-part
closed subscheme. -/
theorem strictTransformIdeal_comap_le (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) :
    (strictTransformIdeal I J).comap (blowupComplement I).ι ≤
      strictTransformOpenPartIdeal I J := by
  exact Scheme.IdealSheafData.comap_map_le _ _

/-- The topological closure in the blowup of the inverse image of a closed subscheme away from
the blowup center. -/
noncomputable def reducedStrictTransformSupport (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) : Closeds (scheme I) :=
  .closure ((projection I) ⁻¹'
    ((J.support : Set (Spec (.of A))) ∩ (baseComplement I : Set (Spec (.of A)))))

/-- The reduced ideal sheaf defining the reduced strict transform. -/
noncomputable def reducedStrictTransformIdeal (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) : (scheme I).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (reducedStrictTransformSupport I J)

/-- The reduced strict transform as a closed subscheme of the blowup. -/
noncomputable abbrev reducedStrictTransform (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) : Scheme :=
  (reducedStrictTransformIdeal I J).subscheme

/-- The closed immersion of the reduced strict transform into the blowup. -/
noncomputable def reducedStrictTransformι (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) : reducedStrictTransform I J ⟶ scheme I :=
  (reducedStrictTransformIdeal I J).subschemeι

instance reducedStrictTransformι_isClosedImmersion (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) :
    IsClosedImmersion (reducedStrictTransformι I J) := by
  unfold reducedStrictTransformι
  infer_instance

@[simp]
theorem reducedStrictTransformIdeal_support (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) :
    ((reducedStrictTransformIdeal I J).support : Set (scheme I)) =
      closure ((projection I) ⁻¹'
        ((J.support : Set (Spec (.of A))) ∩
          (baseComplement I : Set (Spec (.of A))))) := by
  exact Scheme.IdealSheafData.coe_support_vanishingIdeal _

@[simp]
theorem reducedStrictTransformι_range (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) :
    Set.range (reducedStrictTransformι I J) =
      closure ((projection I) ⁻¹'
        ((J.support : Set (Spec (.of A))) ∩
          (baseComplement I : Set (Spec (.of A))))) := by
  change Set.range ((reducedStrictTransformIdeal I J).subschemeι) = _
  rw [Scheme.IdealSheafData.range_subschemeι, reducedStrictTransformIdeal_support]

/-- Away from the center, the reduced strict transform has exactly the inverse-image support of
the original closed subscheme. -/
theorem reducedStrictTransform_support_inter_complement (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) :
    ((reducedStrictTransformIdeal I J).support : Set (scheme I)) ∩
        (projection I) ⁻¹' (baseComplement I : Set (Spec (.of A))) =
      (projection I) ⁻¹' (J.support : Set (Spec (.of A))) ∩
        (projection I) ⁻¹' (baseComplement I : Set (Spec (.of A))) := by
  rw [reducedStrictTransformIdeal_support]
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨?_, hx.2⟩
    have hclosure :
        closure ((projection I) ⁻¹'
          ((J.support : Set (Spec (.of A))) ∩
            (baseComplement I : Set (Spec (.of A))))) ⊆
          (projection I) ⁻¹' (J.support : Set (Spec (.of A))) :=
      closure_minimal (fun y hy ↦ hy.1)
        (J.support.isClosed.preimage (projection I).continuous)
    exact hclosure hx.1
  · intro x hx
    refine ⟨subset_closure ?_, hx.2⟩
    exact ⟨hx.1, hx.2⟩

/-- The reduced strict-transform support is the smallest closed subset containing the inverse
image of the original subscheme away from the center. -/
theorem reducedStrictTransformSupport_le_iff (I : Ideal A)
    (J : (Spec (.of A)).IdealSheafData) (W : Closeds (scheme I)) :
    reducedStrictTransformSupport I J ≤ W ↔
      (projection I) ⁻¹'
        ((J.support : Set (Spec (.of A))) ∩
          (baseComplement I : Set (Spec (.of A)))) ⊆ (W : Set (scheme I)) := by
  exact TopologicalSpace.Closeds.closure_le

end PrincipalizedChart

/-! ## The blowup away from the centre

The unit ideal is the affine local model for the complement of a centre.  Its Rees blowup is
already the base scheme.  This is the algebraic core of the usual statement that a blowup is
an isomorphism away from its centre; a relative complement theorem additionally requires the
localization/base-change comparison for Rees algebras.
-/

/-- The element `1` regarded as a generator of the unit ideal. -/
noncomputable def topGenerator : (⊤ : Ideal R) := ⟨1, trivial⟩

theorem topGenerator_isRegular :
    IsRegular ((RingHom.id R) (topGenerator : (⊤ : Ideal R)).1) := by
  simpa [topGenerator] using (isRegular_one : IsRegular (1 : R))

theorem top_map_id_eq_span_generator :
    (⊤ : Ideal R).map (RingHom.id R) =
      Ideal.span {RingHom.id R (topGenerator : (⊤ : Ideal R)).1} := by
  simp [topGenerator]

/-- The base-ring map to the unique standard chart of the unit-ideal blowup is bijective. -/
theorem topChart_baseRingHom_bijective :
    Function.Bijective (baseRingHom (⊤ : Ideal R) topGenerator) := by
  let lift := chartLift (⊤ : Ideal R) (RingHom.id R) topGenerator
    topGenerator_isRegular top_map_id_eq_span_generator
  constructor
  · intro x y hxy
    have h := congrArg lift hxy
    simpa [lift] using h
  · intro z
    refine ⟨lift z, ?_⟩
    apply chartLift_injective (⊤ : Ideal R) (RingHom.id R) topGenerator
      (fun _ _ h ↦ h) topGenerator_isRegular top_map_id_eq_span_generator
    simp [lift]

/-- The coordinate ring of the unique standard chart of the unit-ideal blowup is the base
ring itself. -/
noncomputable def topChartEquiv :
    R ≃+* HomogeneousLocalization.Away (grade (⊤ : Ideal R))
      (generator (⊤ : Ideal R) topGenerator) :=
  RingEquiv.ofBijective (baseRingHom (⊤ : Ideal R) topGenerator)
    topChart_baseRingHom_bijective

/-- The standard chart indexed by `1` covers the Proj of the unit-ideal Rees algebra. -/
theorem top_basicOpen_eq_top :
    Proj.basicOpen (grade (⊤ : Ideal R))
      (generator (⊤ : Ideal R) topGenerator) = ⊤ := by
  let s : Unit → R := fun _ ↦ 1
  have hI : (⊤ : Ideal R) = Ideal.span (Set.range s) := by
    simp [s]
  have hcover := Proj.iSup_basicOpen_eq_top (grade (⊤ : Ideal R))
    (generatorOfFamily (⊤ : Ideal R) s hI)
    (irrelevant_le_span_generatorOfFamily (⊤ : Ideal R) s hI)
  apply top_unique
  rw [← hcover]
  apply iSup_le
  intro i
  have hi : i = () := Subsingleton.elim _ _
  subst i
  apply le_of_eq
  congr 2

noncomputable instance chartMap_top_isIso :
    IsIso (chartMap (⊤ : Ideal R) (topGenerator : (⊤ : Ideal R))) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [chartMap_opensRange]
  exact top_basicOpen_eq_top

/-- Blowing up the unit ideal does not change an affine scheme. -/
noncomputable instance projection_top_isIso : IsIso (projection (⊤ : Ideal R)) := by
  let _ : IsIso (CommRingCat.ofHom
      (baseRingHom (⊤ : Ideal R) (topGenerator : (⊤ : Ideal R)))) := by
    change IsIso (topChartEquiv (R := R)).toCommRingCatIso.hom
    infer_instance
  let _ : IsIso (Spec.map (CommRingCat.ofHom
      (baseRingHom (⊤ : Ideal R) (topGenerator : (⊤ : Ideal R))))) := by
    infer_instance
  exact IsIso.of_isIso_fac_left (chartMap_projection (⊤ : Ideal R) topGenerator)

end ReesBlowup
end AlgebraicGeometry
