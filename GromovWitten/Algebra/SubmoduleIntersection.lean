/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of intersections after a linear map

Over a Noetherian ring, finite intersection data upstairs and finite kernel
quotient data control the intersection of the two images.  The proof uses the
connecting difference map from the fibre product of the two submodules; it is
an algebraic finiteness statement and makes no geometric claim.
-/

noncomputable section

universe u v w z

variable {R : Type u} [CommRing R]
  {P : Type v} [AddCommGroup P] [Module R P]
  {C : Type w} [AddCommGroup C] [Module R C]
  {D : Type z} [AddCommGroup D] [Module R D]

private theorem finite_image_kernel (c : P →ₗ[R] C) (hc : Function.Surjective c)
    (d : P →ₗ[R] D) [Module.Finite R d.range] [Module.Finite R (d.ker.map c)] :
    Module.Finite R C := by
  have : Module.Finite R (P ⧸ d.ker) :=
    Module.Finite.of_surjective d.quotKerEquivRange.symm.toLinearMap
      d.quotKerEquivRange.symm.surjective
  let q : (P ⧸ d.ker) →ₗ[R] (C ⧸ d.ker.map c) :=
    d.ker.mapQ (d.ker.map c) c (Submodule.le_comap_map c d.ker)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨y, rfl⟩ := (d.ker.map c).mkQ_surjective y
    obtain ⟨x, rfl⟩ := hc y
    exact ⟨d.ker.mkQ x, rfl⟩
  have : Module.Finite R (C ⧸ d.ker.map c) := Module.Finite.of_surjective q hq
  exact Module.Finite.of_submodule_quotient (d.ker.map c)

variable {S : Type v} [AddCommGroup S] [Module R S]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- If `A ∩ B` is finite and the quotient of `ker q` by the contributions from
`A ∩ ker q` and `B ∩ ker q` is finite, then `q(A) ∩ q(B)` is finite. -/
theorem Submodule.finite_inf_map_of_finite_inf_of_finite_ker_quotient
    [IsNoetherianRing R] (q : S →ₗ[R] N) (A B : Submodule R S)
    [Module.Finite R (A ⊓ B : Submodule R S)]
    [Module.Finite R (q.ker ⧸
      (A.comap q.ker.subtype ⊔ B.comap q.ker.subtype))] :
    Module.Finite R (A.map q ⊓ B.map q : Submodule R N) := by
  let C := A.map q ⊓ B.map q
  let f : A × B →ₗ[R] N :=
    (q.comp A.subtype).comp (LinearMap.fst R A B) -
      (q.comp B.subtype).comp (LinearMap.snd R A B)
  let P := f.ker
  have hp (x : P) : q (x.1.1 : S) = q (x.1.2 : S) := sub_eq_zero.mp x.property
  let c : P →ₗ[R] C :=
    { toFun := fun x => ⟨q (x.1.1 : S),
        ⟨⟨x.1.1, x.1.1.property, rfl⟩, ⟨x.1.2, x.1.2.property, (hp x).symm⟩⟩⟩
      map_add' := by intro x y; apply Subtype.ext; exact q.map_add _ _
      map_smul' := by intro a x; apply Subtype.ext; exact q.map_smul a _ }
  have hc : Function.Surjective c := by
    intro z
    obtain ⟨a, ha, hqa⟩ := z.property.1
    obtain ⟨b, hb, hqb⟩ := z.property.2
    refine ⟨⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩, ?_⟩
    · change q a - q b = 0
      rw [hqa, hqb, sub_self]
    · exact Subtype.ext hqa
  let K := q.ker
  let L : Submodule R K := A.comap K.subtype ⊔ B.comap K.subtype
  let delta : P →ₗ[R] K :=
    { toFun := fun x => ⟨(x.1.1 : S) - (x.1.2 : S), by
        rw [LinearMap.mem_ker, map_sub, hp, sub_self]⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change (_ + _) - (_ + _) = (_ - _) + (_ - _)
        abel
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact (smul_sub a (x.1.1 : S) (x.1.2 : S)).symm }
  let d : P →ₗ[R] (K ⧸ L) := L.mkQ.comp delta
  let u : (A ⊓ B : Submodule R S) →ₗ[R] C :=
    { toFun := fun x => ⟨q x, ⟨⟨x, x.property.1, rfl⟩, ⟨x, x.property.2, rfl⟩⟩⟩
      map_add' := by intro x y; apply Subtype.ext; exact q.map_add _ _
      map_smul' := by intro a x; apply Subtype.ext; exact q.map_smul a _ }
  have hu : Module.Finite R u.range :=
    Module.Finite.of_surjective u.rangeRestrict u.surjective_rangeRestrict
  have hle : d.ker.map c ≤ u.range := by
    rintro z ⟨x, hx, rfl⟩
    have hx' : delta x ∈ L := (Submodule.Quotient.mk_eq_zero L).mp hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx'
    have ha' : (a : S) ∈ A := ha
    have hb' : (b : S) ∈ B := hb
    have he : (a : S) + (b : S) = (x.1.1 : S) - (x.1.2 : S) :=
      congrArg Subtype.val hab
    have hz : (x.1.1 : S) - a = (x.1.2 : S) + b := by
      apply sub_eq_iff_eq_add.mpr
      calc
        (x.1.1 : S) = ((a : S) + b) + x.1.2 := (eq_sub_iff_add_eq.mp he).symm
        _ = ((x.1.2 : S) + b) + a := by abel
    refine ⟨⟨(x.1.1 : S) - a, A.sub_mem x.1.1.property ha', ?_⟩, ?_⟩
    · rw [hz]
      exact B.add_mem x.1.2.property hb'
    · apply Subtype.ext
      change q ((x.1.1 : S) - a) = q (x.1.1 : S)
      rw [map_sub, a.property, sub_zero]
  have : Module.Finite R (d.ker.map c) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have : Module.Finite R d.range := inferInstance
  exact finite_image_kernel c hc d

/-- The kernel of the difference map from a product is finite when both individual
kernels and the intersection of the two ranges are finite. -/
theorem LinearMap.finite_ker_sub_fst_snd_of_finite_ker_of_finite_range_inf
    {P₁ : Type v} [AddCommGroup P₁] [Module R P₁]
    {P₂ : Type w} [AddCommGroup P₂] [Module R P₂]
    {N₁ : Type z} [AddCommGroup N₁] [Module R N₁]
    (f : P₁ →ₗ[R] N₁) (g : P₂ →ₗ[R] N₁)
    [Module.Finite R f.ker] [Module.Finite R g.ker]
    [Module.Finite R (f.range ⊓ g.range : Submodule R N₁)] :
    Module.Finite R ((f.comp (LinearMap.fst R P₁ P₂) -
      g.comp (LinearMap.snd R P₁ P₂)).ker) := by
  let d := f.comp (LinearMap.fst R P₁ P₂) - g.comp (LinearMap.snd R P₁ P₂)
  let K := d.ker
  let C := f.range ⊓ g.range
  have hk (x : K) : f x.1.1 = g x.1.2 := sub_eq_zero.mp x.property
  let c : K →ₗ[R] C :=
    { toFun := fun x => ⟨f x.1.1, ⟨⟨x.1.1, rfl⟩, ⟨x.1.2, (hk x).symm⟩⟩⟩
      map_add' := by intro x y; apply Subtype.ext; exact f.map_add _ _
      map_smul' := by intro a x; apply Subtype.ext; exact f.map_smul a _ }
  have hc : Function.Surjective c := by
    intro z
    obtain ⟨a, ha⟩ := z.property.1
    obtain ⟨b, hb⟩ := z.property.2
    refine ⟨⟨(a, b), ?_⟩, ?_⟩
    · change f a - g b = 0
      rw [ha, hb, sub_self]
    · exact Subtype.ext ha
  let i : f.ker × g.ker →ₗ[R] K :=
    { toFun := fun x => ⟨(x.1, x.2), by
        change f (x.1 : P₁) - g (x.2 : P₂) = 0
        rw [x.1.property, x.2.property, sub_self]⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hi : Function.Exact i c := by
    rw [LinearMap.exact_iff]
    ext x
    constructor
    · intro hx
      have hf : f x.1.1 = 0 := congrArg Subtype.val hx
      have hg : g x.1.2 = 0 := (hk x).symm.trans hf
      exact ⟨(⟨x.1.1, hf⟩, ⟨x.1.2, hg⟩), rfl⟩
    · rintro ⟨x, rfl⟩
      exact Subtype.ext x.1.property
  exact Module.Finite.of_exact hi hc
