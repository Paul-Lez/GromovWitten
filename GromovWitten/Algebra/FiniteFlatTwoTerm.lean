/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.TensorKernel
import GromovWitten.Algebra.ModuleCatScalarExtension
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite flat two-term replacements

Let `d : A →ₗ[R] B` have flat source and target, finite kernel and finite cokernel,
where `R` is Noetherian.  This file constructs a finite free module `P`, a lift
`q : P →ₗ[R] B` of a finite set of cokernel generators, and the finite projective
kernel `K` of `(a, p) ↦ d a - q p`.  The resulting projections give a two-term
replacement of `d`; comparison and tensor compatibility are recorded separately.
-/

open TensorProduct
noncomputable section

namespace LinearMap

universe u v w

variable {R : Type u} [CommRing R]
variable {A : Type v} [AddCommGroup A] [Module R A]
variable {B : Type w} [AddCommGroup B] [Module R B]

section

/-- The surjection whose kernel is the first term of the replacement. -/
def finiteFlatTwoTermMap (d : A →ₗ[R] B) {n : ℕ}
    (q : (Fin n → R) →ₗ[R] B) : (A × (Fin n → R)) →ₗ[R] B where
  toFun x := d x.1 - q x.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' r x := by
    simp [Prod.smul_fst, Prod.smul_snd, smul_sub]

@[simp]
lemma finiteFlatTwoTermMap_apply (d : A →ₗ[R] B) {n : ℕ}
    (q : (Fin n → R) →ₗ[R] B) (x : A × (Fin n → R)) :
    finiteFlatTwoTermMap d q x = d x.1 - q x.2 :=
  rfl

/-- The first projection from the kernel term to the original source. -/
def finiteFlatTwoTermLeft (d : A →ₗ[R] B) {n : ℕ}
    (q : (Fin n → R) →ₗ[R] B) :
    LinearMap.ker (finiteFlatTwoTermMap d q) →ₗ[R] A :=
  (LinearMap.fst R A (Fin n → R)).comp (LinearMap.ker (finiteFlatTwoTermMap d q)).subtype

/-- The second projection from the kernel term to the finite free term. -/
def finiteFlatTwoTermDifferential (d : A →ₗ[R] B) {n : ℕ}
    (q : (Fin n → R) →ₗ[R] B) :
    LinearMap.ker (finiteFlatTwoTermMap d q) →ₗ[R] (Fin n → R) :=
  (LinearMap.snd R A (Fin n → R)).comp (LinearMap.ker (finiteFlatTwoTermMap d q)).subtype

@[simp]
lemma finiteFlatTwoTermLeft_apply (d : A →ₗ[R] B) {n : ℕ}
    (q : (Fin n → R) →ₗ[R] B) (x : LinearMap.ker (finiteFlatTwoTermMap d q)) :
    finiteFlatTwoTermLeft d q x = (x : A × (Fin n → R)).1 :=
  rfl

@[simp]
lemma finiteFlatTwoTermDifferential_apply (d : A →ₗ[R] B) {n : ℕ}
    (q : (Fin n → R) →ₗ[R] B) (x : LinearMap.ker (finiteFlatTwoTermMap d q)) :
    finiteFlatTwoTermDifferential d q x = (x : A × (Fin n → R)).2 :=
  rfl

lemma finiteFlatTwoTerm_comm (d : A →ₗ[R] B) {n : ℕ}
    (q : (Fin n → R) →ₗ[R] B) :
    d.comp (finiteFlatTwoTermLeft d q) = q.comp (finiteFlatTwoTermDifferential d q) := by
  ext x
  have hx := x.property
  exact sub_eq_zero.mp hx

private lemma flat_ker_of_surjective_of_flat
    {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : N →ₗ[R] P) (hf : Function.Surjective f)
    (g : M →ₗ[R] N) (hg : Function.Injective g) (h : Function.Exact g f)
    [Module.Flat R N] [Module.Flat R P] : Module.Flat R M := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ i hi
  have hiN : Function.Injective (i.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap i hi
  have hig : Function.Injective (g.lTensor X) :=
    LinearMap.lTensor_injective_of_exact_of_flat f hf g hg h X
  intro x y hxy
  apply hig
  apply hiN
  have hcomm : (i.rTensor N).comp (g.lTensor X) =
      (g.lTensor Y).comp (i.rTensor M) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply, hxy]
  exact (LinearMap.congr_fun hcomm y).symm

private lemma flat_prod_of_flat
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Flat R M] [Module.Flat R N] :
    Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ f hf
  let eX := TensorProduct.prodRight R R X M N
  let eY := TensorProduct.prodRight R R Y M N
  have hmap : eY.toLinearMap.comp (f.rTensor (M × N)) =
      ((f.rTensor M).prodMap (f.rTensor N)).comp eX.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
    | tmul x z => rfl
  intro x y hxy
  have hxy' : (eY.toLinearMap.comp (f.rTensor (M × N))) x =
      (eY.toLinearMap.comp (f.rTensor (M × N))) y := congrArg eY hxy
  rw [hmap] at hxy'
  apply eX.injective
  apply Prod.ext
  · apply Module.Flat.rTensor_preserves_injective_linearMap f hf
    exact congrArg Prod.fst hxy'
  · apply Module.Flat.rTensor_preserves_injective_linearMap f hf
    exact congrArg Prod.snd hxy'

private lemma finite_ker_of_finite_coker_lift
    (d : A →ₗ[R] B) {n : ℕ} (q : (Fin n → R) →ₗ[R] B)
    [IsNoetherianRing R]
    [Module.Finite R (LinearMap.ker d)] : Module.Finite R
      (LinearMap.ker (finiteFlatTwoTermMap d q)) := by
  let K := LinearMap.ker (finiteFlatTwoTermMap d q)
  let f : LinearMap.ker d →ₗ[R] K :=
    { toFun := fun a => ⟨(a, 0), by
          change d (a : A) - q (0 : Fin n → R) = 0
          rw [a.property, map_zero, sub_zero]⟩
      map_add' := by intro a b; ext <;> simp
      map_smul' := by intro r a; ext <;> simp }
  let p : K →ₗ[R] (Fin n → R) := finiteFlatTwoTermDifferential d q
  let g : K →ₗ[R] LinearMap.range p := p.rangeRestrict
  have hg : Function.Surjective g := p.surjective_rangeRestrict
  have hfg : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    ext x
    constructor
    · intro hx
      have hx' : p x = 0 := by
        exact congrArg Subtype.val hx
      have hx2 : (x : A × (Fin n → R)).2 = 0 := by
        simpa [p, finiteFlatTwoTermDifferential] using hx'
      have hxE : d (x : A × (Fin n → R)).1 -
          q (x : A × (Fin n → R)).2 = 0 := x.property
      rw [hx2, map_zero, sub_zero] at hxE
      let a : LinearMap.ker d := ⟨(x : A × (Fin n → R)).1, hxE⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      ext <;> simp [f, a, hx2]
    · rintro ⟨a, rfl⟩
      apply Subtype.ext
      change p ⟨(a, 0), _⟩ = 0
      simp [p, finiteFlatTwoTermDifferential]
  have hfinite_range : Module.Finite R (LinearMap.range p) := inferInstance
  exact Module.Finite.of_exact hfg hg

section Construction

variable (d : A →ₗ[R] B)
variable [Module.Flat R A] [Module.Flat R B]
variable [Module.Finite R (LinearMap.ker d)]
variable [Module.Finite R (B ⧸ LinearMap.range d)]

omit [Module.Flat R A] [Module.Flat R B] [Module.Finite R (LinearMap.ker d)] in
/-- A finite free cover of the cokernel can be lifted to a map into `B`. -/
theorem exists_finiteFlatTwoTerm_cover :
    ∃ (n : ℕ) (q : (Fin n → R) →ₗ[R] B),
      Function.Surjective ((LinearMap.range d).mkQ.comp q) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R (B ⧸ LinearMap.range d)
  let c : B →ₗ[R] (B ⧸ LinearMap.range d) := (LinearMap.range d).mkQ
  obtain ⟨q, hq⟩ := Module.projective_lifting_property c f
    (Submodule.mkQ_surjective (LinearMap.range d))
  exact ⟨n, q, hq ▸ hf⟩

omit [Module.Flat R A] [Module.Flat R B] [Module.Finite R (LinearMap.ker d)]
  [Module.Finite R (B ⧸ LinearMap.range d)] in
/-- The lifted cokernel cover makes the kernel map onto `B`. -/
theorem finiteFlatTwoTerm_surjective_of_cover {n : ℕ}
    (q : (Fin n → R) →ₗ[R] B)
    (hq : Function.Surjective ((LinearMap.range d).mkQ.comp q)) :
    Function.Surjective (finiteFlatTwoTermMap d q) := by
  intro y
  obtain ⟨p, hp⟩ := hq ((LinearMap.range d).mkQ y)
  change (LinearMap.range d).mkQ (q p) = (LinearMap.range d).mkQ y at hp
  have hzero : (LinearMap.range d).mkQ (y - q p) = 0 := by
    rw [map_sub, hp, sub_self]
  have hmem : y - q p ∈ LinearMap.range d := by
    rw [← Submodule.ker_mkQ (LinearMap.range d)]
    exact LinearMap.mem_ker.mp hzero
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hmem
  refine ⟨(a, -p), ?_⟩
  simp [finiteFlatTwoTermMap, ha]

/-- Tensoring the kernel term with any module identifies it with the new kernel. -/
private def finiteFlatTwoTerm_tensor_kernel_equiv {n : ℕ}
    (q : (Fin n → R) →ₗ[R] B)
    (hq : Function.Surjective ((LinearMap.range d).mkQ.comp q))
    {T : Type*} [AddCommGroup T] [Module R T] :
    T ⊗[R] LinearMap.ker (finiteFlatTwoTermMap d q) ≃ₗ[R]
      LinearMap.ker ((finiteFlatTwoTermMap d q).lTensor T) := by
  exact (finiteFlatTwoTermMap d q).kerLTensorEquivOfSurjective
    (finiteFlatTwoTerm_surjective_of_cover d q hq) T |>.symm

section Noetherian

variable [IsNoetherianRing R]

omit [Module.Finite R (B ⧸ LinearMap.range d)] in
/-- The kernel term of the lifted cover is flat and finite projective. -/
theorem finiteFlatTwoTerm_kernel_properties {n : ℕ}
    (q : (Fin n → R) →ₗ[R] B)
    (hq : Function.Surjective ((LinearMap.range d).mkQ.comp q)) :
    Module.Flat R (LinearMap.ker (finiteFlatTwoTermMap d q)) ∧
      Module.Finite R (LinearMap.ker (finiteFlatTwoTermMap d q)) ∧
      Module.Projective R (LinearMap.ker (finiteFlatTwoTermMap d q)) := by
  let e := finiteFlatTwoTermMap d q
  have he : Function.Surjective e := finiteFlatTwoTerm_surjective_of_cover d q hq
  let K := LinearMap.ker e
  have hflat : Module.Flat R K := by
    let _ : Module.Flat R (Fin n → R) := Module.Flat.of_free
    let _ : Module.Flat R (A × (Fin n → R)) := flat_prod_of_flat
    exact flat_ker_of_surjective_of_flat e he K.subtype
      K.injective_subtype (LinearMap.exact_subtype_ker_map e)
  have hfinite : Module.Finite R K := finite_ker_of_finite_coker_lift d q
  let _ : Module.Flat R K := hflat
  let _ : Module.Finite R K := hfinite
  have hfp : Module.FinitePresentation R K := Module.finitePresentation_of_finite R K
  let _ : Module.FinitePresentation R K := hfp
  have hproj : Module.Projective R K := Module.Flat.projective_of_finitePresentation
  exact ⟨hflat, hfinite, hproj⟩

/-- Existence of the finite flat two-term replacement data. -/
theorem exists_finiteFlatTwoTerm :
    ∃ (n : ℕ) (q : (Fin n → R) →ₗ[R] B),
      Function.Surjective ((LinearMap.range d).mkQ.comp q) ∧
      Module.Flat R (LinearMap.ker (finiteFlatTwoTermMap d q)) ∧
      Module.Finite R (LinearMap.ker (finiteFlatTwoTermMap d q)) ∧
      Module.Projective R (LinearMap.ker (finiteFlatTwoTermMap d q)) := by
  obtain ⟨n, q, hq⟩ := exists_finiteFlatTwoTerm_cover d
  obtain ⟨hflat, hfinite, hproj⟩ := finiteFlatTwoTerm_kernel_properties d q hq
  exact ⟨n, q, hq, hflat, hfinite, hproj⟩

end Noetherian

end Construction

end

end LinearMap

open CategoryTheory Limits

namespace LinearMap

universe t

section Comparison

attribute [local instance] ModuleCat.hasKernels_moduleCat
attribute [local instance] ModuleCat.hasCokernels_moduleCat

variable {S X Y : Type t} [CommRing S]
variable [AddCommGroup X] [Module S X]
variable [AddCommGroup Y] [Module S Y]

/-- The replacement square is a pullback of `q` and `d`. -/
theorem finiteFlatTwoTerm_isPullback (d : X →ₗ[S] Y) {n : ℕ}
    (q : (Fin n → S) →ₗ[S] Y) :
    IsPullback (ModuleCat.ofHom (finiteFlatTwoTermDifferential d q))
      (ModuleCat.ofHom (finiteFlatTwoTermLeft d q))
      (ModuleCat.ofHom q) (ModuleCat.ofHom d) := by
  apply IsPullback.mk'
  · apply ModuleCat.hom_ext_iff.mpr
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      (finiteFlatTwoTerm_comm d q).symm
  · intro T φ φ' h₁ h₂
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · have h := congrArg (fun f => f x) (ModuleCat.hom_ext_iff.mp h₂)
      exact h
    · have h := congrArg (fun f => f x) (ModuleCat.hom_ext_iff.mp h₁)
      exact h
  · intro T a b hab
    let l : T →ₗ[S] LinearMap.ker (finiteFlatTwoTermMap d q) :=
      ((b.hom).prod (a.hom)).codRestrict _ (by
        intro x
        change d (b.hom x) - q (a.hom x) = 0
        rw [sub_eq_zero]
        exact (congrArg (fun f => f x) (ModuleCat.hom_ext_iff.mp hab)).symm)
    refine ⟨ModuleCat.ofHom l, ?_, ?_⟩
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl

/-- The pullback square gives the canonical isomorphism on kernels. -/
theorem finiteFlatTwoTerm_kernel_map_isIso (d : X →ₗ[S] Y) {n : ℕ}
    (q : (Fin n → S) →ₗ[S] Y) :
    IsIso (kernel.map (ModuleCat.ofHom (finiteFlatTwoTermDifferential d q))
      (ModuleCat.ofHom d) (ModuleCat.ofHom (finiteFlatTwoTermLeft d q))
      (ModuleCat.ofHom q) (finiteFlatTwoTerm_isPullback d q).w) := by
  exact isIso_kernel_map_of_isPullback (finiteFlatTwoTerm_isPullback d q)

/-- The surjective replacement square is also a pushout. -/
theorem finiteFlatTwoTerm_isPushout (d : X →ₗ[S] Y) {n : ℕ}
    (q : (Fin n → S) →ₗ[S] Y)
    (hq : Function.Surjective ((LinearMap.range d).mkQ.comp q)) :
    IsPushout (ModuleCat.ofHom (finiteFlatTwoTermDifferential d q))
      (ModuleCat.ofHom (finiteFlatTwoTermLeft d q))
      (ModuleCat.ofHom q) (ModuleCat.ofHom d) := by
  let e := finiteFlatTwoTermMap d q
  have he : Function.Surjective e := finiteFlatTwoTerm_surjective_of_cover d q hq
  apply IsPushout.mk'
  · apply ModuleCat.hom_ext_iff.mpr
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      (finiteFlatTwoTerm_comm d q).symm
  · intro T φ φ' h₁ h₂
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := he y
    change φ.hom (d z.1 - q z.2) = φ'.hom (d z.1 - q z.2)
    rw [map_sub, map_sub]
    have hd := congrArg (fun f => f z.1) (ModuleCat.hom_ext_iff.mp h₂)
    have hd' : φ.hom (d z.1) = φ'.hom (d z.1) := by
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] using hd
    have hq' := congrArg (fun f => f z.2) (ModuleCat.hom_ext_iff.mp h₁)
    have hq'' : φ.hom (q z.2) = φ'.hom (q z.2) := by
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] using hq'
    rw [hd', hq'']
  · intro T a b hab
    let h : (X × (Fin n → S)) →ₗ[S] T :=
      LinearMap.coprod b.hom (-a.hom)
    have hker : e.ker ≤ LinearMap.ker h := by
      intro x hx
      change h x = 0
      simp only [h, LinearMap.coprod_apply]
      change b.hom x.1 + -(a.hom x.2) = 0
      rw [← sub_eq_add_neg, sub_eq_zero]
      have hab' := congrArg (fun f => f ⟨x, hx⟩) (ModuleCat.hom_ext_iff.mp hab)
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        finiteFlatTwoTermLeft_apply, finiteFlatTwoTermDifferential_apply] using hab'.symm
    let δ : Y →ₗ[S] T :=
      (e.ker.liftQ h hker).comp (e.quotKerEquivOfSurjective he).symm.toLinearMap
    refine ⟨ModuleCat.ofHom δ, ?_, ?_⟩
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro p
      change δ (q p) = a.hom p
      change (e.ker.liftQ h hker)
        ((e.quotKerEquivOfSurjective he).symm (q p)) = a.hom p
      have hz : (e.quotKerEquivOfSurjective he).symm (q p) =
          Submodule.Quotient.mk (0, -p) := by
        calc
          _ = (e.quotKerEquivOfSurjective he).symm (e (0, -p)) := by
            congr 1
            simp [e, finiteFlatTwoTermMap]
          _ = _ := LinearMap.quotKerEquivOfSurjective_symm_apply e he (0, -p)
      rw [hz]
      simp [h]
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change δ (d x) = b.hom x
      change (e.ker.liftQ h hker)
        ((e.quotKerEquivOfSurjective he).symm (d x)) = b.hom x
      have hz : (e.quotKerEquivOfSurjective he).symm (d x) =
          Submodule.Quotient.mk (x, 0) := by
        calc
          _ = (e.quotKerEquivOfSurjective he).symm (e (x, 0)) := by
            congr 1
            simp [e, finiteFlatTwoTermMap]
          _ = _ := LinearMap.quotKerEquivOfSurjective_symm_apply e he (x, 0)
      rw [hz]
      simp [h]

/-- The pushout square gives the canonical isomorphism on cokernels. -/
theorem finiteFlatTwoTerm_cokernel_map_isIso (d : X →ₗ[S] Y) {n : ℕ}
    (q : (Fin n → S) →ₗ[S] Y)
    (hq : Function.Surjective ((LinearMap.range d).mkQ.comp q)) :
    IsIso (cokernel.map (ModuleCat.ofHom (finiteFlatTwoTermDifferential d q))
      (ModuleCat.ofHom d) (ModuleCat.ofHom (finiteFlatTwoTermLeft d q))
      (ModuleCat.ofHom q) (finiteFlatTwoTerm_isPullback d q).w) := by
  exact isIso_cokernel_map_of_isPushout (finiteFlatTwoTerm_isPushout d q hq)

end Comparison

section BaseChange

universe b

attribute [local instance] ModuleCat.hasKernels_moduleCat
attribute [local instance] ModuleCat.hasCokernels_moduleCat

variable {R T X Y : Type b} [CommRing R] [CommRing T]
variable [AddCommGroup X] [Module R X]
variable [AddCommGroup Y] [Module R Y]

/-- Scalar extension preserves the replacement pushout and its cokernel comparison. -/
theorem finiteFlatTwoTerm_extendScalars_cokernel_map_isIso
    (φ : R →+* T) (d : X →ₗ[R] Y) {n : ℕ}
    (q : (Fin n → R) →ₗ[R] Y)
    (hq : Function.Surjective ((LinearMap.range d).mkQ.comp q)) :
    IsIso (cokernel.map
      ((ModuleCat.extendScalars φ).map
        (ModuleCat.ofHom (finiteFlatTwoTermDifferential d q)))
      ((ModuleCat.extendScalars φ).map (ModuleCat.ofHom d))
      ((ModuleCat.extendScalars φ).map
        (ModuleCat.ofHom (finiteFlatTwoTermLeft d q)))
      ((ModuleCat.extendScalars φ).map (ModuleCat.ofHom q))
      ((finiteFlatTwoTerm_isPushout d q hq).map (ModuleCat.extendScalars φ)).w) := by
  exact isIso_cokernel_map_of_isPushout
    ((finiteFlatTwoTerm_isPushout d q hq).map (ModuleCat.extendScalars φ))

end BaseChange

section TensorBaseChange

universe c

attribute [local instance] ModuleCat.hasKernels_moduleCat
attribute [local instance] ModuleCat.hasCokernels_moduleCat

variable {R T X Y : Type c} [CommRing R] [CommRing T] [Algebra R T]
variable [AddCommGroup X] [Module R X]
variable [AddCommGroup Y] [Module R Y] [Module.Flat R Y]

/-- Tensoring the replacement square remains a pullback when its target is flat. -/
theorem finiteFlatTwoTerm_tensor_isPullback (d : X →ₗ[R] Y) {n : ℕ}
    (q : (Fin n → R) →ₗ[R] Y)
    (hq : Function.Surjective ((LinearMap.range d).mkQ.comp q)) :
    IsPullback
      (ModuleCat.ofHom (AlgebraTensorModule.lTensor T T
        (finiteFlatTwoTermDifferential d q)))
      (ModuleCat.ofHom (AlgebraTensorModule.lTensor T T
        (finiteFlatTwoTermLeft d q)))
      (ModuleCat.ofHom (AlgebraTensorModule.lTensor T T q))
      (ModuleCat.ofHom (AlgebraTensorModule.lTensor T T d)) := by
  let e := finiteFlatTwoTermMap d q
  let p := finiteFlatTwoTermDifferential d q
  let l := finiteFlatTwoTermLeft d q
  let et : T ⊗[R] LinearMap.ker e ≃ₗ[T]
      LinearMap.ker (AlgebraTensorModule.lTensor T T e) := by
    apply LinearEquiv.ofBijective (LinearMap.tensorKer T T e)
    have he : Function.Surjective e := finiteFlatTwoTerm_surjective_of_cover d q hq
    have hcoker : Module.Flat R (Y ⧸ e.range) := by
      rw [LinearMap.range_eq_top.mpr he]
      exact Module.Flat.of_free
    exact LinearMap.tensorKer_bijective_of_target_flat_of_cokernel_flat e
  have hprod :
      (TensorProduct.prodRight R T T X (Fin n → R)).toLinearMap.comp
          (AlgebraTensorModule.lTensor T T
            (LinearMap.ker (finiteFlatTwoTermMap d q)).subtype) =
        LinearMap.prod (AlgebraTensorModule.lTensor T T (finiteFlatTwoTermLeft d q))
          (AlgebraTensorModule.lTensor T T (finiteFlatTwoTermDifferential d q)) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | add z₁ z₂ hz₁ hz₂ =>
      rw [map_add, map_add, hz₁, hz₂]
    | tmul s x =>
      change (s ⊗ₜ[R] (x : X × (Fin n → R)).1,
          s ⊗ₜ[R] (x : X × (Fin n → R)).2) =
        (s ⊗ₜ[R] finiteFlatTwoTermLeft d q x,
          s ⊗ₜ[R] finiteFlatTwoTermDifferential d q x)
      rfl
  have heprod :
      (AlgebraTensorModule.lTensor T T e) =
        (LinearMap.coprod (AlgebraTensorModule.lTensor T T d)
          (-(AlgebraTensorModule.lTensor T T q))).comp
          (TensorProduct.prodRight R T T X (Fin n → R)).toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | add z₁ z₂ hz₁ hz₂ =>
      rw [map_add, map_add, hz₁, hz₂]
    | tmul s x =>
      change s ⊗ₜ[R] (d x.1 - q x.2) =
        s ⊗ₜ[R] d x.1 + -(s ⊗ₜ[R] q x.2)
      rw [tmul_sub]
      simp only [sub_eq_add_neg]
  have hprod_apply (x : T ⊗[R] LinearMap.ker e) :
      (TensorProduct.prodRight R T T X (Fin n → R))
          ((AlgebraTensorModule.lTensor T T
            (LinearMap.ker e).subtype) x) =
        ((AlgebraTensorModule.lTensor T T (finiteFlatTwoTermLeft d q)) x,
          (AlgebraTensorModule.lTensor T T
            (finiteFlatTwoTermDifferential d q)) x) := by
    simpa only [e, LinearMap.comp_apply, LinearMap.prod_apply, Function.prod_apply,
      LinearEquiv.coe_toLinearMap] using LinearMap.congr_fun hprod x
  have hprod_apply_R (x : T ⊗[R] LinearMap.ker e) :
      (TensorProduct.prodRight R T T X (Fin n → R))
          ((LinearMap.lTensor T (LinearMap.ker e).subtype) x) =
        ((LinearMap.lTensor T (finiteFlatTwoTermLeft d q)) x,
          (LinearMap.lTensor T
            (finiteFlatTwoTermDifferential d q)) x) := by
    simpa only [AlgebraTensorModule.coe_lTensor] using hprod_apply x
  apply IsPullback.mk'
  · apply ModuleCat.hom_ext_iff.mpr
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      AlgebraTensorModule.lTensor_comp] using
      congrArg (fun f => AlgebraTensorModule.lTensor T T f)
        (finiteFlatTwoTerm_comm d q).symm
  · intro U φ φ' h₁ h₂
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply et.injective
    apply Subtype.ext
    change (LinearMap.tensorKer T T e (φ.hom z)).val =
      (LinearMap.tensorKer T T e (φ'.hom z)).val
    rw [LinearMap.tensorKer_coe, LinearMap.tensorKer_coe]
    apply (TensorProduct.prodRight R T T X (Fin n → R)).injective
    rw [hprod_apply_R, hprod_apply_R]
    apply Prod.ext
    · exact congrArg (fun f => f z) (ModuleCat.hom_ext_iff.mp h₂)
    · exact congrArg (fun f => f z) (ModuleCat.hom_ext_iff.mp h₁)
  · intro U a b hab
    let v : U →ₗ[T] T ⊗[R] (X × (Fin n → R)) :=
      (TensorProduct.prodRight R T T X (Fin n → R)).symm.toLinearMap.comp
        (b.hom.prod a.hom)
    have hv : ∀ z, (AlgebraTensorModule.lTensor T T e) (v z) = 0 := by
      intro z
      rw [heprod]
      simp only [LinearMap.comp_apply, LinearMap.coprod_apply]
      have hvprod :
          (TensorProduct.prodRight R T T X (Fin n → R)) (v z) =
            (b.hom z, a.hom z) := by
        simp [v]
      change (AlgebraTensorModule.lTensor T T d)
          ((TensorProduct.prodRight R T T X (Fin n → R)) (v z)).1 +
        (-(AlgebraTensorModule.lTensor T T q))
          ((TensorProduct.prodRight R T T X (Fin n → R)) (v z)).2 = 0
      rw [hvprod]
      simp only [LinearMap.neg_apply]
      rw [← sub_eq_add_neg, sub_eq_zero]
      have hab' := congrArg (fun f => f z) (ModuleCat.hom_ext_iff.mp hab)
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] using
        hab'.symm
    let v' : U →ₗ[T]
        LinearMap.ker (AlgebraTensorModule.lTensor T T e) :=
      v.codRestrict _ hv
    let lift : U →ₗ[T] T ⊗[R] LinearMap.ker e :=
      et.symm.toLinearMap.comp v'
    have hlift (z : U) :
        (LinearMap.lTensor T (LinearMap.ker e).subtype) (lift z) = v z := by
      have hz := congrArg Subtype.val (et.apply_symm_apply (v' z))
      change (LinearMap.tensorKer T T e (lift z)).val = (v' z).val at hz
      rw [LinearMap.tensorKer_coe] at hz
      calc
        (LinearMap.lTensor T (LinearMap.ker e).subtype) (lift z) =
            (v' z).val := hz
        _ = v z := by
          change ((v.codRestrict _ hv) z).val = v z
          exact LinearMap.codRestrict_apply _ _ _
    refine ⟨ModuleCat.ofHom lift, ?_, ?_⟩
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      have hz := congrArg Prod.snd (hprod_apply_R (lift z))
      rw [hlift z] at hz
      have hvprod :
          (TensorProduct.prodRight R T T X (Fin n → R)) (v z) =
            (b.hom z, a.hom z) := by
        simp [v]
      rw [hvprod] at hz
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        AlgebraTensorModule.coe_lTensor] using hz.symm
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      have hz := congrArg Prod.fst (hprod_apply_R (lift z))
      rw [hlift z] at hz
      have hvprod :
          (TensorProduct.prodRight R T T X (Fin n → R)) (v z) =
            (b.hom z, a.hom z) := by
        simp [v]
      rw [hvprod] at hz
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        AlgebraTensorModule.coe_lTensor] using hz.symm

/-- Tensoring the replacement square gives the canonical isomorphism on kernels. -/
theorem finiteFlatTwoTerm_tensor_kernel_map_isIso (d : X →ₗ[R] Y) {n : ℕ}
    (q : (Fin n → R) →ₗ[R] Y)
    (hq : Function.Surjective ((LinearMap.range d).mkQ.comp q)) :
    IsIso (kernel.map
      (ModuleCat.ofHom (AlgebraTensorModule.lTensor T T
        (finiteFlatTwoTermDifferential d q)))
      (ModuleCat.ofHom (AlgebraTensorModule.lTensor T T d))
      (ModuleCat.ofHom (AlgebraTensorModule.lTensor T T
        (finiteFlatTwoTermLeft d q)))
      (ModuleCat.ofHom (AlgebraTensorModule.lTensor T T q))
      (finiteFlatTwoTerm_tensor_isPullback d q hq).w) := by
  exact isIso_kernel_map_of_isPullback
    (finiteFlatTwoTerm_tensor_isPullback d q hq)

end TensorBaseChange

section ExtendScalarsPullback

universe s

attribute [local instance] ModuleCat.hasKernels_moduleCat
attribute [local instance] ModuleCat.hasCokernels_moduleCat

variable {R T X Y : Type s} [CommRing R] [CommRing T]
variable [AddCommGroup X] [Module R X]
variable [AddCommGroup Y] [Module R Y] [Module.Flat R Y]

/-- Scalar extension identifies the replacement pullback with its tensor square. -/
theorem finiteFlatTwoTerm_extendScalars_isPullback
    (φ : R →+* T) (d : X →ₗ[R] Y) {n : ℕ}
    (q : (Fin n → R) →ₗ[R] Y)
    (hq : Function.Surjective ((LinearMap.range d).mkQ.comp q)) :
    IsPullback
      ((ModuleCat.extendScalars φ).map
        (ModuleCat.ofHom (finiteFlatTwoTermDifferential d q)))
      ((ModuleCat.extendScalars φ).map
        (ModuleCat.ofHom (finiteFlatTwoTermLeft d q)))
      ((ModuleCat.extendScalars φ).map (ModuleCat.ofHom q))
      ((ModuleCat.extendScalars φ).map (ModuleCat.ofHom d)) := by
  let _ : Algebra R T := φ.toAlgebra
  have hφ : algebraMap R T = φ := by
    ext r
    rfl
  rw [← hφ]
  have hnat_inv {M N : ModuleCat.{s} R} (f : M ⟶ N) :
      ModuleCat.ofHom (AlgebraTensorModule.lTensor T T f.hom) ≫
          (ModuleCat.extendScalarsAlgebraIso (C := T) N).inv =
        (ModuleCat.extendScalarsAlgebraIso (C := T) M).inv ≫
          (ModuleCat.extendScalars (algebraMap R T)).map f := by
    apply (cancel_mono
      (ModuleCat.extendScalarsAlgebraIso (C := T) N).hom).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id, ModuleCat.extendScalarsAlgebraIso_naturality]
  apply IsPullback.of_iso (finiteFlatTwoTerm_tensor_isPullback d q hq)
    ((ModuleCat.extendScalarsAlgebraIso (C := T)
      (ModuleCat.of R (LinearMap.ker (finiteFlatTwoTermMap d q)))).symm)
    ((ModuleCat.extendScalarsAlgebraIso (C := T)
      (ModuleCat.of R (Fin n → R))).symm)
    ((ModuleCat.extendScalarsAlgebraIso (C := T)
      (ModuleCat.of R X)).symm)
    ((ModuleCat.extendScalarsAlgebraIso (C := T)
      (ModuleCat.of R Y)).symm)
  · exact hnat_inv (ModuleCat.ofHom (finiteFlatTwoTermDifferential d q))
  · exact hnat_inv (ModuleCat.ofHom (finiteFlatTwoTermLeft d q))
  · exact hnat_inv (ModuleCat.ofHom q)
  · exact hnat_inv (ModuleCat.ofHom d)

/-- Scalar extension gives the canonical kernel comparison for the replacement. -/
theorem finiteFlatTwoTerm_extendScalars_kernel_map_isIso
    (φ : R →+* T) (d : X →ₗ[R] Y) {n : ℕ}
    (q : (Fin n → R) →ₗ[R] Y)
    (hq : Function.Surjective ((LinearMap.range d).mkQ.comp q)) :
    IsIso (kernel.map
      ((ModuleCat.extendScalars φ).map
        (ModuleCat.ofHom (finiteFlatTwoTermDifferential d q)))
      ((ModuleCat.extendScalars φ).map (ModuleCat.ofHom d))
      ((ModuleCat.extendScalars φ).map
        (ModuleCat.ofHom (finiteFlatTwoTermLeft d q)))
      ((ModuleCat.extendScalars φ).map (ModuleCat.ofHom q))
      (finiteFlatTwoTerm_extendScalars_isPullback φ d q hq).w) := by
  exact isIso_kernel_map_of_isPullback
    (finiteFlatTwoTerm_extendScalars_isPullback φ d q hq)

end ExtendScalarsPullback

end LinearMap
