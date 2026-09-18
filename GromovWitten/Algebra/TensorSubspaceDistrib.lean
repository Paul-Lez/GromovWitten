/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Tensor products of subspaces form a distributive lattice

For vector spaces `V`, `W` over a field `k` and subspaces `A ≤ V`, `B ≤ W`, write
`A ⊗' B := range (A.subtype ⊗ B.subtype) ≤ V ⊗[k] W` (`tensorSub`).  The main result is

`tensorSub_top_inf_top_tensorSub : (A ⊗' ⊤) ⊓ (⊤ ⊗' B) = A ⊗' B`,

the distributivity input needed to compute the associated graded ring of a product
(`GromovWitten/AlgebraicGeometry/Cones/NormalConeProduct.lean`).

## Method

Over a field every subspace `A ≤ V` is the range of an idempotent endomorphism `e` of `V`
(`Submodule.projection` along a complement, which exists by `Submodule.exists_isCompl`).  For
such an `e` and a corresponding `f` for `B`,

* `range (e ⊗ f) = A ⊗' B` (`range_tensorMap`, valid over any commutative ring), and
* `e ⊗ f` is again idempotent (`isIdempotentElem_tensorMap`),

so membership in `A ⊗' B` is the fixed-point condition `(e ⊗ f) x = x`
(`mem_tensorSub_iff_of_range_eq`).  The lemma then follows from the identity
`(e ⊗ 1) ∘ (1 ⊗ f) = e ⊗ f` and idempotency, with no choice of bases and no coordinates.

## Main results

* `tensorSub`, `mem_tensorSub_iff_of_range_eq`, `range_tensorMap`.
* `tensorSub_top_inf_top_tensorSub`: the distributivity lemma over a field.
* `mem_tensorSub_iff`: its elementwise form, `x ∈ A ⊗' B ↔ x ∈ A ⊗' ⊤ ∧ x ∈ ⊤ ⊗' B`.

Everything is unconditional; only `tensorSub_top_inf_top_tensorSub` and its corollaries need `k`
to be a field.  Not proved here: the version for two families of subspaces on each side, which
also needs `(A₁ ⊓ A₂) ⊗' ⊤ = A₁ ⊗' ⊤ ⊓ A₂ ⊗' ⊤` (flatness of the second factor), and hence the
filtration statement `J^n/J^{n+1} ≅ ⊕_{a+b=n} (I^a/I^{a+1}) ⊗ (I'^b/I'^{b+1})`.
-/

open scoped TensorProduct

namespace GromovWitten.Algebra

universe u v

section CommRing

variable {k : Type u} [CommRing k] {V W : Type v} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- The image of `A ⊗[k] B` inside `V ⊗[k] W`, for subspaces `A ≤ V` and `B ≤ W`. -/
def tensorSub (A : Submodule k V) (B : Submodule k W) : Submodule k (V ⊗[k] W) :=
  LinearMap.range (TensorProduct.map A.subtype B.subtype)

/-- Elementary tensors of elements of `A` and `B` lie in `A ⊗' B`. -/
theorem tmul_mem_tensorSub {A : Submodule k V} {B : Submodule k W} {a : V} {b : W}
    (ha : a ∈ A) (hb : b ∈ B) : a ⊗ₜ[k] b ∈ tensorSub A B :=
  ⟨(⟨a, ha⟩ : A) ⊗ₜ[k] (⟨b, hb⟩ : B), rfl⟩

/-- `A ⊗' B` is monotone in both arguments. -/
theorem tensorSub_mono {A₁ A₂ : Submodule k V} {B₁ B₂ : Submodule k W} (hA : A₁ ≤ A₂)
    (hB : B₁ ≤ B₂) : tensorSub A₁ B₁ ≤ tensorSub A₂ B₂ := by
  rw [tensorSub, LinearMap.range_le_iff_comap, eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact tmul_mem_tensorSub (hA a.2) (hB b.2)
  | add x y hx hy =>
    rw [Submodule.mem_comap, map_add]
    exact Submodule.add_mem _ hx hy

/-- If `e` and `f` have ranges `A` and `B`, then `e ⊗ f` has range `A ⊗' B`. -/
theorem range_tensorMap {A : Submodule k V} {B : Submodule k W} {e : V →ₗ[k] V} {f : W →ₗ[k] W}
    (hA : LinearMap.range e = A) (hB : LinearMap.range f = B) :
    LinearMap.range (TensorProduct.map e f) = tensorSub A B := by
  subst hA
  subst hB
  have key : TensorProduct.map (LinearMap.range e).subtype (LinearMap.range f).subtype ∘ₗ
      TensorProduct.map e.rangeRestrict f.rangeRestrict = TensorProduct.map e f := by
    rw [← TensorProduct.map_comp]
    congr 1
  rw [← key, LinearMap.range_comp, LinearMap.range_eq_top.mpr
    (TensorProduct.map_surjective (LinearMap.surjective_rangeRestrict e)
      (LinearMap.surjective_rangeRestrict f)),
    Submodule.map_top, tensorSub]

/-- A tensor product of idempotent endomorphisms is idempotent. -/
theorem isIdempotentElem_tensorMap {e : V →ₗ[k] V} {f : W →ₗ[k] W} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) : IsIdempotentElem (TensorProduct.map e f) := by
  have he' : e ∘ₗ e = e := he
  have hf' : f ∘ₗ f = f := hf
  change TensorProduct.map e f ∘ₗ TensorProduct.map e f = TensorProduct.map e f
  rw [← TensorProduct.map_comp, he', hf']

/-- Membership in `A ⊗' B` is the fixed-point condition for `e ⊗ f`, for any idempotents `e`, `f`
with ranges `A` and `B`. -/
theorem mem_tensorSub_iff_of_range_eq {A : Submodule k V} {B : Submodule k W} {e : V →ₗ[k] V}
    {f : W →ₗ[k] W} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hA : LinearMap.range e = A) (hB : LinearMap.range f = B) (x : V ⊗[k] W) :
    x ∈ tensorSub A B ↔ TensorProduct.map e f x = x := by
  rw [← range_tensorMap hA hB]
  exact LinearMap.IsIdempotentElem.mem_range_iff (isIdempotentElem_tensorMap he hf)

end CommRing

section Field

variable {k : Type u} [Field k] {V W : Type v} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- Over a field, every subspace is the range of an idempotent endomorphism. -/
theorem exists_isIdempotentElem_range_eq (A : Submodule k V) :
    ∃ e : V →ₗ[k] V, IsIdempotentElem e ∧ LinearMap.range e = A := by
  obtain ⟨A', hA'⟩ := A.exists_isCompl
  exact ⟨A.projection A' hA', Submodule.isIdempotentElem_projection hA',
    Submodule.range_projection hA'⟩

/-- **Distributivity of tensor products of subspaces over a field.**
`(A ⊗ W) ⊓ (V ⊗ B) = A ⊗ B` inside `V ⊗[k] W`. -/
theorem tensorSub_top_inf_top_tensorSub (A : Submodule k V) (B : Submodule k W) :
    tensorSub A (⊤ : Submodule k W) ⊓ tensorSub (⊤ : Submodule k V) B = tensorSub A B := by
  obtain ⟨e, he, hAe⟩ := exists_isIdempotentElem_range_eq A
  obtain ⟨f, hf, hBf⟩ := exists_isIdempotentElem_range_eq B
  have hidV : IsIdempotentElem (LinearMap.id : V →ₗ[k] V) := by
    change (LinearMap.id : V →ₗ[k] V) ∘ₗ LinearMap.id = LinearMap.id
    rw [LinearMap.id_comp]
  have hidW : IsIdempotentElem (LinearMap.id : W →ₗ[k] W) := by
    change (LinearMap.id : W →ₗ[k] W) ∘ₗ LinearMap.id = LinearMap.id
    rw [LinearMap.id_comp]
  have he' : e ∘ₗ e = e := he
  have hf' : f ∘ₗ f = f := hf
  have hsplit : TensorProduct.map e (LinearMap.id : W →ₗ[k] W) ∘ₗ
      TensorProduct.map (LinearMap.id : V →ₗ[k] V) f = TensorProduct.map e f := by
    rw [← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]
  have hleft : TensorProduct.map e (LinearMap.id : W →ₗ[k] W) ∘ₗ TensorProduct.map e f
      = TensorProduct.map e f := by
    rw [← TensorProduct.map_comp, he', LinearMap.id_comp]
  have hright : TensorProduct.map (LinearMap.id : V →ₗ[k] V) f ∘ₗ TensorProduct.map e f
      = TensorProduct.map e f := by
    rw [← TensorProduct.map_comp, hf', LinearMap.id_comp]
  ext x
  rw [Submodule.mem_inf,
    mem_tensorSub_iff_of_range_eq he hidW hAe LinearMap.range_id x,
    mem_tensorSub_iff_of_range_eq hidV hf LinearMap.range_id hBf x,
    mem_tensorSub_iff_of_range_eq he hf hAe hBf x]
  constructor
  · rintro ⟨h1, h2⟩
    have := congrArg (TensorProduct.map e (LinearMap.id : W →ₗ[k] W)) h2
    rw [← LinearMap.comp_apply, hsplit, h1] at this
    exact this
  · intro h
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← h]
      rw [← LinearMap.comp_apply, hleft, h]
    · conv_lhs => rw [← h]
      rw [← LinearMap.comp_apply, hright, h]

/-- The special case of `tensorSub_top_inf_top_tensorSub` in which the right-hand subspace is the
same on both sides. -/
theorem tensorSub_inf_tensorSub_left (A : Submodule k V) (B : Submodule k W) :
    tensorSub A (⊤ : Submodule k W) ⊓ tensorSub (⊤ : Submodule k V) B ⊓ tensorSub A B
      = tensorSub A B := by
  rw [tensorSub_top_inf_top_tensorSub, inf_idem]

/-- `A ⊗' B` is contained in `A ⊗' ⊤` and in `⊤ ⊗' B`. -/
theorem tensorSub_le_tensorSub_top (A : Submodule k V) (B : Submodule k W) :
    tensorSub A B ≤ tensorSub A (⊤ : Submodule k W) :=
  tensorSub_mono le_rfl le_top

/-- `A ⊗' B` is contained in `⊤ ⊗' B`. -/
theorem tensorSub_le_top_tensorSub (A : Submodule k V) (B : Submodule k W) :
    tensorSub A B ≤ tensorSub (⊤ : Submodule k V) B :=
  tensorSub_mono le_top le_rfl

/-- The two-sided form of the distributivity lemma: an element of `V ⊗[k] W` lies in `A ⊗' B`
exactly when it lies in `A ⊗' ⊤` and in `⊤ ⊗' B`. -/
theorem mem_tensorSub_iff (A : Submodule k V) (B : Submodule k W) (x : V ⊗[k] W) :
    x ∈ tensorSub A B ↔
      x ∈ tensorSub A (⊤ : Submodule k W) ∧ x ∈ tensorSub (⊤ : Submodule k V) B := by
  rw [← Submodule.mem_inf, tensorSub_top_inf_top_tensorSub]

end Field

end GromovWitten.Algebra
