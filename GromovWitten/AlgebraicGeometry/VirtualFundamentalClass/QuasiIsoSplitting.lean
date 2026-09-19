/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Independence
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Exact.Basic

/-!
# Splitting a quasi-isomorphism of two-term complexes

Let `S` be a commutative ring and let `f : E ⟶ F` be a map of two-term complexes of `S`-modules
(`degreeZero` is the term in degree `-1`, `degreeOne` the term in degree `0`).  This file proves
the purely algebraic statement that, if `f` is a quasi-isomorphism and `F.degreeOne` is a
projective `S`-module, then

`F ⊕ [E⁰ = E⁰] ≅ E ⊕ [F⁰ = F⁰]`

as two-term complexes, where `[M = M]` denotes the acyclic complex `acyclicComplex S M`.

The construction proceeds through the *extension* `extend f : E ⟶ F ⊕ [E⁰ = E⁰]`,
`x ↦ (f x, d x)`, and the *cokernel map* `cokernelMap f : F⁻¹ × E⁰ → F⁰`,
`(y, e) ↦ d_F y - f⁰ e`.  The main exactness statement `exact_extend_cokernelMap` says that

`0 ⟶ E⁻¹ ⟶ F⁻¹ ⊕ E⁰ ⟶ F⁰ ⟶ 0`

is a short exact sequence; projectivity of `F⁰` provides a section `chosenSection f hf`, hence a
retraction `retraction f hf` onto `E⁻¹`, and the isomorphism `iso f hf` together with its explicit
inverse `isoInv f hf`.

The last group of results is the degree-zero homotopy formula `coprod_comp_iso_degreeZero`: if
`φ : E ⟶ L` and `ψ : F ⟶ L` satisfy `ψ⁻¹ ∘ f⁻¹ = φ⁻¹`, then `(φ⁻¹ ⊕ 0) ∘ (iso f hf)⁻¹` differs
from `ψ⁻¹ ⊕ 0` by the degree-zero part of an explicit chain homotopy `homotopy f hf ψ`.

## Deviation from the naive formula

The map `iso f hf` is *not* the naive `(y', e) ↦ (e, y' - f⁰ e)` in degree zero: that map fails
to commute with the differentials.  The correct formula, recorded in `iso_degreeOne_apply`, is

`(iso f hf).degreeOne (y', e) = (e - sectionSnd f hf (y' - f⁰ e), y' - f⁰ e)`,

where `sectionSnd f hf` is the `E⁰`-component of the chosen section.  It agrees with the naive
formula exactly on the image of the differential of `F ⊕ [E⁰ = E⁰]` twisted by the section, and
this correction is what makes `iso f hf` a chain map.
-/

namespace GromovWitten.AlgebraicGeometry

open GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.VirtualClass

universe u

namespace LinearTwoTermComplex.QuasiIsoSplitting

variable {S : Type u} [CommRing S] {E F : LinearTwoTermComplex S}

/-- Two chain maps of two-term complexes agreeing in both degrees are equal. -/
theorem hom_ext {a b : Hom E F} (h0 : a.degreeZero = b.degreeZero)
    (h1 : a.degreeOne = b.degreeOne) : a = b := by
  obtain ⟨a0, a1, ha⟩ := a
  obtain ⟨b0, b1, hb⟩ := b
  simp only at h0 h1
  subst h0
  subst h1
  rfl

/-! ## The extension of a chain map and its cokernel map -/

variable (f : Hom E F)

/-- **The extension of a chain map** `f : E ⟶ F` to a chain map
`E ⟶ F ⊕ [E⁰ = E⁰]`, given by `x ↦ (f⁻¹ x, d_E x)` in degree `-1` and `e ↦ (f⁰ e, e)` in
degree `0`. -/
def extend : Hom E (F.sum (acyclicComplex S E.degreeOne)) where
  degreeZero := LinearMap.prod f.degreeZero E.differential
  degreeOne := LinearMap.prod f.degreeOne LinearMap.id
  comm x := by
    change (f.degreeOne (E.differential x), E.differential x) =
      (F.differential (f.degreeZero x), E.differential x)
    rw [f.comm]

@[simp]
theorem extend_degreeZero_apply (x : E.degreeZero) :
    (extend f).degreeZero x = (f.degreeZero x, E.differential x) :=
  rfl

@[simp]
theorem extend_degreeOne_apply (e : E.degreeOne) :
    (extend f).degreeOne e = (f.degreeOne e, e) :=
  rfl

/-- **The cokernel map of the extension in degree `-1`**: the surjection
`F⁻¹ × E⁰ → F⁰`, `(y, e) ↦ d_F y - f⁰ e`. -/
def cokernelMap : (F.sum (acyclicComplex S E.degreeOne)).degreeZero →ₗ[S] F.degreeOne :=
  F.differential.comp (LinearMap.fst S F.degreeZero E.degreeOne) -
    f.degreeOne.comp (LinearMap.snd S F.degreeZero E.degreeOne)

@[simp]
theorem cokernelMap_apply (v : (F.sum (acyclicComplex S E.degreeOne)).degreeZero) :
    cokernelMap f v = F.differential v.1 - f.degreeOne v.2 :=
  rfl

/-- **The cokernel map of the extension in degree `0`**: the surjection
`F⁰ × E⁰ → F⁰`, `(y', e) ↦ y' - f⁰ e`. -/
def cokernelMapOne : (F.sum (acyclicComplex S E.degreeOne)).degreeOne →ₗ[S] F.degreeOne :=
  LinearMap.fst S F.degreeOne E.degreeOne -
    f.degreeOne.comp (LinearMap.snd S F.degreeOne E.degreeOne)

@[simp]
theorem cokernelMapOne_apply (v : (F.sum (acyclicComplex S E.degreeOne)).degreeOne) :
    cokernelMapOne f v = v.1 - f.degreeOne v.2 :=
  rfl

/-- The degree-zero and degree-one cokernel maps are compatible with the differential. -/
theorem cokernelMapOne_differential (v : (F.sum (acyclicComplex S E.degreeOne)).degreeZero) :
    cokernelMapOne f ((F.sum (acyclicComplex S E.degreeOne)).differential v) = cokernelMap f v :=
  rfl

/-- The composite of the extension with the cokernel map vanishes. -/
@[simp]
theorem cokernelMap_extend (x : E.degreeZero) :
    cokernelMap f ((extend f).degreeZero x) = 0 := by
  change F.differential (f.degreeZero x) - f.degreeOne (E.differential x) = 0
  rw [f.comm, sub_self]

/-! ## Exactness under a quasi-isomorphism -/

/-- If `f` is a quasi-isomorphism then the extension is injective in degree `-1`. -/
theorem extend_degreeZero_injective (hf : f.IsQuasiIsomorphism) :
    Function.Injective (extend f).degreeZero := by
  have key : ∀ x : E.degreeZero, (extend f).degreeZero x = 0 → x = 0 := by
    intro x hx
    have hx2 : E.differential x = 0 := congrArg Prod.snd hx
    have hx1 : f.degreeZero x = 0 := congrArg Prod.fst hx
    have hker : f.kernelMap ⟨x, hx2⟩ = f.kernelMap 0 := by
      rw [map_zero]
      exact Subtype.ext hx1
    exact congrArg Subtype.val (hf.1.1 hker)
  intro x y hxy
  have h : (extend f).degreeZero (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.1 (key _ h)

/-- If `f` is a quasi-isomorphism then the degree `-1` cokernel map is surjective. -/
theorem cokernelMap_surjective (hf : f.IsQuasiIsomorphism) :
    Function.Surjective (cokernelMap f) := by
  intro z
  obtain ⟨c, hc⟩ := hf.2.2 (Submodule.Quotient.mk (-z))
  obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  have hc' : (Submodule.Quotient.mk (f.degreeOne e) :
      F.degreeOne ⧸ (LinearMap.range F.differential)) = Submodule.Quotient.mk (-z) := hc
  obtain ⟨y, hy⟩ := (Submodule.Quotient.eq _).1 hc'
  refine ⟨(y, e), ?_⟩
  change F.differential y - f.degreeOne e = z
  rw [hy]
  abel

/-- **Exactness of the extension sequence**: for a quasi-isomorphism `f`, the sequence
`E⁻¹ ⟶ F⁻¹ × E⁰ ⟶ F⁰` is exact. -/
theorem exact_extend_cokernelMap (hf : f.IsQuasiIsomorphism) :
    Function.Exact (extend f).degreeZero (cokernelMap f) := by
  intro v
  constructor
  · intro hv
    have hv' : F.differential v.1 = f.degreeOne v.2 := sub_eq_zero.1 hv
    have hq : f.cokernelMap (Submodule.Quotient.mk v.2) = 0 := by
      change (Submodule.Quotient.mk (f.degreeOne v.2) :
        F.degreeOne ⧸ (LinearMap.range F.differential)) = 0
      rw [← hv']
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨v.1, rfl⟩
    have h0 : (Submodule.Quotient.mk v.2 :
        E.degreeOne ⧸ (LinearMap.range E.differential)) = 0 := by
      refine hf.2.1 ?_
      rw [hq, map_zero]
    obtain ⟨x₀, hx₀⟩ := (Submodule.Quotient.mk_eq_zero _).1 h0
    have hker : F.differential (v.1 - f.degreeZero x₀) = 0 := by
      rw [map_sub, hv', ← f.comm, hx₀, sub_self]
    obtain ⟨x₁, hx₁⟩ := hf.1.2 ⟨v.1 - f.degreeZero x₀, hker⟩
    have hx₁' : f.degreeZero x₁.1 = v.1 - f.degreeZero x₀ := congrArg Subtype.val hx₁
    have hx₁d : E.differential x₁.1 = 0 := x₁.2
    refine ⟨x₀ + x₁.1, ?_⟩
    change (f.degreeZero (x₀ + x₁.1), E.differential (x₀ + x₁.1)) = v
    rw [map_add, map_add, hx₁', hx₁d, hx₀, add_zero]
    have hfin : f.degreeZero x₀ + (v.1 - f.degreeZero x₀) = v.1 := by abel
    rw [hfin]
  · rintro ⟨x, rfl⟩
    exact cokernelMap_extend f x

/-! ## Quasi-isomorphisms from degreewise bijections -/

/-- A chain map which is bijective in both degrees is a quasi-isomorphism. -/
theorem isQuasiIsomorphism_of_bijective {g : Hom E F} (h0 : Function.Bijective g.degreeZero)
    (h1 : Function.Bijective g.degreeOne) : g.IsQuasiIsomorphism := by
  constructor
  · constructor
    · intro a b hab
      exact Subtype.ext (h0.1 (congrArg Subtype.val hab))
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := h0.2 y
      have hx : E.differential x = 0 := by
        refine h1.1 ?_
        rw [map_zero, g.comm]
        exact hy
      exact ⟨⟨x, hx⟩, rfl⟩
  · constructor
    · refine (injective_iff_map_eq_zero _).2 ?_
      intro c hc
      obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      have hc' : (Submodule.Quotient.mk (g.degreeOne e) :
          F.degreeOne ⧸ (LinearMap.range F.differential)) = 0 := hc
      obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).1 hc'
      obtain ⟨x, rfl⟩ := h0.2 y
      refine (Submodule.Quotient.mk_eq_zero _).2 ⟨x, ?_⟩
      refine h1.1 ?_
      rw [g.comm]
      exact hy
    · intro c
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      obtain ⟨e, rfl⟩ := h1.2 y
      exact ⟨Submodule.Quotient.mk e, rfl⟩

/-! ## The chosen splitting of the extension sequence -/

section Projective

variable [Module.Projective S F.degreeOne]

/-- **A chosen section of the degree `-1` cokernel map**, produced by projectivity of `F⁰`. -/
noncomputable def chosenSection (hf : f.IsQuasiIsomorphism) :
    F.degreeOne →ₗ[S] (F.sum (acyclicComplex S E.degreeOne)).degreeZero :=
  (Module.projective_lifting_property (cokernelMap f) LinearMap.id
    (cokernelMap_surjective f hf)).choose

/-- The chosen section is a section of the degree `-1` cokernel map. -/
@[simp]
theorem cokernelMap_chosenSection (hf : f.IsQuasiIsomorphism) (z : F.degreeOne) :
    cokernelMap f (chosenSection f hf z) = z :=
  DFunLike.congr_fun (Module.projective_lifting_property (cokernelMap f) LinearMap.id
    (cokernelMap_surjective f hf)).choose_spec z

/-- The `F⁻¹`-component of the chosen section. -/
noncomputable def sectionFst (hf : f.IsQuasiIsomorphism) : F.degreeOne →ₗ[S] F.degreeZero :=
  (LinearMap.fst S F.degreeZero E.degreeOne).comp (chosenSection f hf)

/-- The `E⁰`-component of the chosen section. -/
noncomputable def sectionSnd (hf : f.IsQuasiIsomorphism) : F.degreeOne →ₗ[S] E.degreeOne :=
  (LinearMap.snd S F.degreeZero E.degreeOne).comp (chosenSection f hf)

/-- The chosen section written in components. -/
theorem chosenSection_eq (hf : f.IsQuasiIsomorphism) (z : F.degreeOne) :
    chosenSection f hf z = (sectionFst f hf z, sectionSnd f hf z) :=
  rfl

/-- The section property of `chosenSection`, written in components. -/
theorem sectionFst_sub_sectionSnd (hf : f.IsQuasiIsomorphism) (z : F.degreeOne) :
    F.differential (sectionFst f hf z) - f.degreeOne (sectionSnd f hf z) = z :=
  cokernelMap_chosenSection f hf z

/-- The section property of `chosenSection`, solved for the `F⁻¹`-component. -/
theorem differential_sectionFst (hf : f.IsQuasiIsomorphism) (z : F.degreeOne) :
    F.differential (sectionFst f hf z) = z + f.degreeOne (sectionSnd f hf z) :=
  sub_eq_iff_eq_add.1 (sectionFst_sub_sectionSnd f hf z)

/-- **The retraction** of the extension `E⁻¹ ⟶ F⁻¹ × E⁰` determined by the chosen section. -/
noncomputable def retraction (hf : f.IsQuasiIsomorphism) :
    (F.sum (acyclicComplex S E.degreeOne)).degreeZero →ₗ[S] E.degreeZero :=
  (LinearEquiv.ofInjective (extend f).degreeZero
      (extend_degreeZero_injective f hf)).symm.toLinearMap.comp
    (LinearMap.codRestrict (LinearMap.range (extend f).degreeZero)
      (LinearMap.id - (chosenSection f hf).comp (cokernelMap f))
      (fun v => (exact_extend_cokernelMap f hf _).1 (by
        change cokernelMap f (v - chosenSection f hf (cokernelMap f v)) = 0
        rw [map_sub, cokernelMap_chosenSection, sub_self])))

/-- **The splitting identity**: the extension of the retraction is the given element minus the
chosen section of its image. -/
theorem extend_retraction (hf : f.IsQuasiIsomorphism)
    (v : (F.sum (acyclicComplex S E.degreeOne)).degreeZero) :
    (extend f).degreeZero (retraction f hf v) = v - chosenSection f hf (cokernelMap f v) := by
  have hmem : v - chosenSection f hf (cokernelMap f v) ∈
      LinearMap.range (extend f).degreeZero := by
    refine (exact_extend_cokernelMap f hf _).1 ?_
    rw [map_sub, cokernelMap_chosenSection, sub_self]
  exact LinearEquiv.ofInjective_symm_apply (f := (extend f).degreeZero)
    (h := extend_degreeZero_injective f hf) (x := ⟨_, hmem⟩)

/-- The retraction is a left inverse of the extension. -/
@[simp]
theorem retraction_extend (hf : f.IsQuasiIsomorphism) (x : E.degreeZero) :
    retraction f hf ((extend f).degreeZero x) = x := by
  refine extend_degreeZero_injective f hf ?_
  rw [extend_retraction, cokernelMap_extend, map_zero, sub_zero]

/-- The retraction kills the chosen section. -/
@[simp]
theorem retraction_chosenSection (hf : f.IsQuasiIsomorphism) (z : F.degreeOne) :
    retraction f hf (chosenSection f hf z) = 0 := by
  refine extend_degreeZero_injective f hf ?_
  rw [extend_retraction, cokernelMap_chosenSection, sub_self, map_zero]

/-! ## The isomorphism `F ⊕ [E⁰ = E⁰] ≅ E ⊕ [F⁰ = F⁰]` -/

/-- **The isomorphism of two-term complexes** `F ⊕ [E⁰ = E⁰] ⟶ E ⊕ [F⁰ = F⁰]` attached to a
quasi-isomorphism `f : E ⟶ F` with `F⁰` projective. -/
noncomputable def iso (hf : f.IsQuasiIsomorphism) :
    Hom (F.sum (acyclicComplex S E.degreeOne)) (E.sum (acyclicComplex S F.degreeOne)) where
  degreeZero := LinearMap.prod (retraction f hf) (cokernelMap f)
  degreeOne :=
    LinearMap.prod
      (LinearMap.snd S F.degreeOne E.degreeOne - (sectionSnd f hf).comp (cokernelMapOne f))
      (cokernelMapOne f)
  comm v := by
    have h : E.differential (retraction f hf v) =
        v.2 - sectionSnd f hf (cokernelMap f v) :=
      congrArg Prod.snd (extend_retraction f hf v)
    change (v.2 - sectionSnd f hf (cokernelMap f v), cokernelMap f v) =
      (E.differential (retraction f hf v), cokernelMap f v)
    rw [h]

@[simp]
theorem iso_degreeZero_apply (hf : f.IsQuasiIsomorphism)
    (v : (F.sum (acyclicComplex S E.degreeOne)).degreeZero) :
    (iso f hf).degreeZero v = (retraction f hf v, cokernelMap f v) :=
  rfl

@[simp]
theorem iso_degreeOne_apply (hf : f.IsQuasiIsomorphism)
    (w : (F.sum (acyclicComplex S E.degreeOne)).degreeOne) :
    (iso f hf).degreeOne w =
      (w.2 - sectionSnd f hf (w.1 - f.degreeOne w.2), w.1 - f.degreeOne w.2) :=
  rfl

/-- The `E⁰`-component of the inverse isomorphism in degree `0`. -/
noncomputable def isoInvSnd (hf : f.IsQuasiIsomorphism) :
    (E.sum (acyclicComplex S F.degreeOne)).degreeOne →ₗ[S] E.degreeOne :=
  LinearMap.fst S E.degreeOne F.degreeOne +
    (sectionSnd f hf).comp (LinearMap.snd S E.degreeOne F.degreeOne)

/-- **The inverse isomorphism** `E ⊕ [F⁰ = F⁰] ⟶ F ⊕ [E⁰ = E⁰]`. -/
noncomputable def isoInv (hf : f.IsQuasiIsomorphism) :
    Hom (E.sum (acyclicComplex S F.degreeOne)) (F.sum (acyclicComplex S E.degreeOne)) where
  degreeZero := (extend f).degreeZero.comp (LinearMap.fst S E.degreeZero F.degreeOne) +
    (chosenSection f hf).comp (LinearMap.snd S E.degreeZero F.degreeOne)
  degreeOne :=
    LinearMap.prod
      (LinearMap.snd S E.degreeOne F.degreeOne + f.degreeOne.comp (isoInvSnd f hf))
      (isoInvSnd f hf)
  comm u := by
    have h1 : u.2 + f.degreeOne (E.differential u.1 + sectionSnd f hf u.2) =
        F.differential (f.degreeZero u.1 + sectionFst f hf u.2) := by
      rw [map_add, map_add, f.comm, differential_sectionFst]
      abel
    change (u.2 + f.degreeOne (E.differential u.1 + sectionSnd f hf u.2),
        E.differential u.1 + sectionSnd f hf u.2) =
      (F.differential (f.degreeZero u.1 + sectionFst f hf u.2),
        E.differential u.1 + sectionSnd f hf u.2)
    rw [h1]

@[simp]
theorem isoInv_degreeZero_apply (hf : f.IsQuasiIsomorphism)
    (u : (E.sum (acyclicComplex S F.degreeOne)).degreeZero) :
    (isoInv f hf).degreeZero u = (extend f).degreeZero u.1 + chosenSection f hf u.2 :=
  rfl

@[simp]
theorem isoInv_degreeOne_apply (hf : f.IsQuasiIsomorphism)
    (u : (E.sum (acyclicComplex S F.degreeOne)).degreeOne) :
    (isoInv f hf).degreeOne u =
      (u.2 + f.degreeOne (u.1 + sectionSnd f hf u.2), u.1 + sectionSnd f hf u.2) :=
  rfl

/-- `isoInv` is a left inverse of `iso` in degree `-1`. -/
theorem isoInv_iso_degreeZero (hf : f.IsQuasiIsomorphism)
    (v : (F.sum (acyclicComplex S E.degreeOne)).degreeZero) :
    (isoInv f hf).degreeZero ((iso f hf).degreeZero v) = v := by
  change (extend f).degreeZero (retraction f hf v) + chosenSection f hf (cokernelMap f v) = v
  rw [extend_retraction]
  abel

/-- `isoInv` is a left inverse of `iso` in degree `0`. -/
theorem isoInv_iso_degreeOne (hf : f.IsQuasiIsomorphism)
    (w : (F.sum (acyclicComplex S E.degreeOne)).degreeOne) :
    (isoInv f hf).degreeOne ((iso f hf).degreeOne w) = w := by
  have h2 : w.2 - sectionSnd f hf (w.1 - f.degreeOne w.2)
      + sectionSnd f hf (w.1 - f.degreeOne w.2) = w.2 := by abel
  have h3 : w.1 - f.degreeOne w.2 + f.degreeOne w.2 = w.1 := by abel
  change (w.1 - f.degreeOne w.2 + f.degreeOne (w.2 - sectionSnd f hf (w.1 - f.degreeOne w.2)
      + sectionSnd f hf (w.1 - f.degreeOne w.2)),
    w.2 - sectionSnd f hf (w.1 - f.degreeOne w.2)
      + sectionSnd f hf (w.1 - f.degreeOne w.2)) = w
  rw [h2, h3]

/-- `isoInv` is a right inverse of `iso` in degree `-1`. -/
theorem iso_isoInv_degreeZero (hf : f.IsQuasiIsomorphism)
    (u : (E.sum (acyclicComplex S F.degreeOne)).degreeZero) :
    (iso f hf).degreeZero ((isoInv f hf).degreeZero u) = u := by
  have hq : cokernelMap f ((isoInv f hf).degreeZero u) = u.2 := by
    change cokernelMap f ((extend f).degreeZero u.1 + chosenSection f hf u.2) = u.2
    rw [map_add, cokernelMap_extend, cokernelMap_chosenSection, zero_add]
  have hr : retraction f hf ((isoInv f hf).degreeZero u) = u.1 := by
    refine extend_degreeZero_injective f hf ?_
    rw [extend_retraction, hq]
    change (extend f).degreeZero u.1 + chosenSection f hf u.2 - chosenSection f hf u.2 =
      (extend f).degreeZero u.1
    abel
  change (retraction f hf ((isoInv f hf).degreeZero u),
    cokernelMap f ((isoInv f hf).degreeZero u)) = u
  rw [hq, hr]

/-- `isoInv` is a right inverse of `iso` in degree `0`. -/
theorem iso_isoInv_degreeOne (hf : f.IsQuasiIsomorphism)
    (u : (E.sum (acyclicComplex S F.degreeOne)).degreeOne) :
    (iso f hf).degreeOne ((isoInv f hf).degreeOne u) = u := by
  have hz : u.2 + f.degreeOne (u.1 + sectionSnd f hf u.2)
      - f.degreeOne (u.1 + sectionSnd f hf u.2) = u.2 := by abel
  have h2 : u.1 + sectionSnd f hf u.2 - sectionSnd f hf u.2 = u.1 := by abel
  change (u.1 + sectionSnd f hf u.2
      - sectionSnd f hf (u.2 + f.degreeOne (u.1 + sectionSnd f hf u.2)
        - f.degreeOne (u.1 + sectionSnd f hf u.2)),
    u.2 + f.degreeOne (u.1 + sectionSnd f hf u.2)
      - f.degreeOne (u.1 + sectionSnd f hf u.2)) = u
  rw [hz, h2]

/-- `isoInv` is a left inverse of `iso` as a chain map. -/
theorem isoInv_comp_iso (hf : f.IsQuasiIsomorphism) :
    (isoInv f hf).comp (iso f hf) = Hom.id (F.sum (acyclicComplex S E.degreeOne)) :=
  hom_ext (LinearMap.ext fun v => isoInv_iso_degreeZero f hf v)
    (LinearMap.ext fun w => isoInv_iso_degreeOne f hf w)

/-- `isoInv` is a right inverse of `iso` as a chain map. -/
theorem iso_comp_isoInv (hf : f.IsQuasiIsomorphism) :
    (iso f hf).comp (isoInv f hf) = Hom.id (E.sum (acyclicComplex S F.degreeOne)) :=
  hom_ext (LinearMap.ext fun u => iso_isoInv_degreeZero f hf u)
    (LinearMap.ext fun u => iso_isoInv_degreeOne f hf u)

/-- `iso f hf` is bijective in degree `-1`. -/
theorem iso_degreeZero_bijective (hf : f.IsQuasiIsomorphism) :
    Function.Bijective (iso f hf).degreeZero :=
  Function.bijective_iff_has_inverse.2
    ⟨(isoInv f hf).degreeZero, isoInv_iso_degreeZero f hf, iso_isoInv_degreeZero f hf⟩

/-- `iso f hf` is bijective in degree `0`. -/
theorem iso_degreeOne_bijective (hf : f.IsQuasiIsomorphism) :
    Function.Bijective (iso f hf).degreeOne :=
  Function.bijective_iff_has_inverse.2
    ⟨(isoInv f hf).degreeOne, isoInv_iso_degreeOne f hf, iso_isoInv_degreeOne f hf⟩

/-- `iso f hf` sends the image of the extension to `E⁻¹ ⊕ 0`. -/
@[simp]
theorem iso_degreeZero_extend (hf : f.IsQuasiIsomorphism) (x : E.degreeZero) :
    (iso f hf).degreeZero ((extend f).degreeZero x) = (x, 0) := by
  change (retraction f hf ((extend f).degreeZero x),
    cokernelMap f ((extend f).degreeZero x)) = (x, 0)
  rw [retraction_extend, cokernelMap_extend]

/-- `iso f hf` sends the chosen section to `0 ⊕ F⁰`. -/
@[simp]
theorem iso_degreeZero_chosenSection (hf : f.IsQuasiIsomorphism) (z : F.degreeOne) :
    (iso f hf).degreeZero (chosenSection f hf z) = (0, z) := by
  change (retraction f hf (chosenSection f hf z), cokernelMap f (chosenSection f hf z)) = (0, z)
  rw [retraction_chosenSection, cokernelMap_chosenSection]

/-- `iso f hf` is a quasi-isomorphism. -/
theorem iso_isQuasiIsomorphism (hf : f.IsQuasiIsomorphism) : (iso f hf).IsQuasiIsomorphism :=
  isQuasiIsomorphism_of_bijective (iso_degreeZero_bijective f hf) (iso_degreeOne_bijective f hf)

/-- `isoInv f hf` is a quasi-isomorphism. -/
theorem isoInv_isQuasiIsomorphism (hf : f.IsQuasiIsomorphism) :
    (isoInv f hf).IsQuasiIsomorphism :=
  isQuasiIsomorphism_of_bijective
    (Function.bijective_iff_has_inverse.2
      ⟨(iso f hf).degreeZero, iso_isoInv_degreeZero f hf, isoInv_iso_degreeZero f hf⟩)
    (Function.bijective_iff_has_inverse.2
      ⟨(iso f hf).degreeOne, iso_isoInv_degreeOne f hf, isoInv_iso_degreeOne f hf⟩)

/-! ## The degree-zero homotopy formula -/

variable {L : LinearTwoTermComplex S}

/-- **The chain homotopy** correcting `φ ⊕ 0` after transport along `iso f hf`. -/
noncomputable def homotopy (hf : f.IsQuasiIsomorphism) (ψ : Hom F L) :
    (F.sum (acyclicComplex S E.degreeOne)).degreeOne →ₗ[S] L.degreeZero :=
  -(ψ.degreeZero.comp ((sectionFst f hf).comp (cokernelMapOne f)))

@[simp]
theorem homotopy_apply (hf : f.IsQuasiIsomorphism) (ψ : Hom F L)
    (w : (F.sum (acyclicComplex S E.degreeOne)).degreeOne) :
    homotopy f hf ψ w = -ψ.degreeZero (sectionFst f hf (w.1 - f.degreeOne w.2)) :=
  rfl

/-- **The degree-zero homotopy formula.**  If `ψ⁻¹ ∘ f⁻¹ = φ⁻¹` then transporting `φ ⊕ 0` along
`iso f hf` gives `ψ ⊕ 0` up to the explicit degree-zero chain homotopy `homotopy f hf ψ`. -/
theorem coprod_comp_iso_degreeZero (hf : f.IsQuasiIsomorphism) {φ : Hom E L} {ψ : Hom F L}
    (hcomp : ψ.degreeZero.comp f.degreeZero = φ.degreeZero) :
    (LinearMap.coprod φ.degreeZero 0).comp (iso f hf).degreeZero =
      LinearMap.coprod ψ.degreeZero 0 +
        (homotopy f hf ψ).comp (F.sum (acyclicComplex S E.degreeOne)).differential := by
  refine LinearMap.ext fun v => ?_
  have h1 : f.degreeZero (retraction f hf v) = v.1 - sectionFst f hf (cokernelMap f v) :=
    congrArg Prod.fst (extend_retraction f hf v)
  have h2 : φ.degreeZero (retraction f hf v) =
      ψ.degreeZero (f.degreeZero (retraction f hf v)) :=
    (DFunLike.congr_fun hcomp (retraction f hf v)).symm
  change φ.degreeZero (retraction f hf v) + (0 : L.degreeZero) =
    ψ.degreeZero v.1 + (0 : L.degreeZero) +
      -ψ.degreeZero (sectionFst f hf (cokernelMap f v))
  rw [h2, h1, map_sub]
  abel

end Projective

/-! ## Freeness and finiteness of the terms of a direct sum

The terms of `E.sum E'` are products of the terms of `E` and `E'`, so these instances are
inherited from `Module.Free.prod` and `Module.Finite.prod`.  They are restated here in the
form in which the sums `F ⊕ [E⁰ = E⁰]` and `E ⊕ [F⁰ = F⁰]` occur above, so that instance search
succeeds directly on the two-term-complex projections. -/

section FreeFinite

variable (E F)

/-- The degree `-1` term of a direct sum of two-term complexes is free. -/
instance free_sum_degreeZero [Module.Free S E.degreeZero] [Module.Free S F.degreeZero] :
    Module.Free S (E.sum F).degreeZero :=
  Module.Free.prod S E.degreeZero F.degreeZero

/-- The degree `0` term of a direct sum of two-term complexes is free. -/
instance free_sum_degreeOne [Module.Free S E.degreeOne] [Module.Free S F.degreeOne] :
    Module.Free S (E.sum F).degreeOne :=
  Module.Free.prod S E.degreeOne F.degreeOne

/-- The degree `-1` term of a direct sum of two-term complexes is finitely generated. -/
instance finite_sum_degreeZero [Module.Finite S E.degreeZero] [Module.Finite S F.degreeZero] :
    Module.Finite S (E.sum F).degreeZero :=
  Module.Finite.prod

/-- The degree `0` term of a direct sum of two-term complexes is finitely generated. -/
instance finite_sum_degreeOne [Module.Finite S E.degreeOne] [Module.Finite S F.degreeOne] :
    Module.Finite S (E.sum F).degreeOne :=
  Module.Finite.prod

end FreeFinite

end LinearTwoTermComplex.QuasiIsoSplitting

end GromovWitten.AlgebraicGeometry
