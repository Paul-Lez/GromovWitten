/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5
-/

import GromovWitten.AlgebraicGeometry.ObstructionTheory.AffineObstructionCone

/-!
# External direct sums of obstruction theories over a product of affine schemes

For `k`-algebras `S`, `S'`, the affine scheme `Spec (S ⊗[k] S') = Spec S ×_{Spec k} Spec S'` is
the product of `Spec S` and `Spec S'`.  In the affine, two-term model of
`Cones/Picard.lean`/`Cones/CriteriaBundle.lean` the cotangent complex of a product is the
external direct sum of the pullbacks of the two factors' cotangent complexes,
`L_{X×Y} ≅ pr_X^*L_X ⊕ pr_Y^*L_Y`; this file constructs that external sum in the affine model
and proves that an external sum of obstruction theories is again an obstruction theory.

Everything here is an unconditional consequence of results already proved in
`ObstructionTheory/AffineObstructionCone.lean`:

* `LinearTwoTermComplex.baseChange` (degreewise `R' ⊗[R] -`, for *any* `R`-algebra `R'`,
  `AffineObstructionCone.lean:747`) realises the pullback `pr_X^*`;
* `LinearTwoTermComplex.sum` (degreewise product, `AffineObstructionCone.lean:721`) realises the
  direct sum `⊕`;
* `PicardCriteria.IsObstructionTheory.baseChange` (`AffineObstructionCone.lean:1078`) and
  `PicardCriteria.isObstructionTheory_sum_iff`/`IsObstructionTheory.sum`
  (`AffineObstructionCone.lean:972,1025`) say that both operations preserve being an obstruction
  theory.

Composing base change (twice, along `S → S ⊗[k] S'` and `S' → S ⊗[k] S'`) with the external sum
gives the external sum over the product ring.

## Main results

* `PicardCriteria.externalSum k E E' : LinearTwoTermComplex (S ⊗[k] S')`: the external sum
  `(E.baseChange (S ⊗[k] S')).sum (E'.baseChange (S ⊗[k] S'))` of two two-term complexes `E`,
  `E'` over `k`-algebras `S`, `S'`.
* `PicardCriteria.isPerfectTwoTerm_externalSum`, `PicardCriteria.virtualRank_externalSum`: the
  external sum of two perfect two-term complexes is perfect, with virtual rank the sum of the
  virtual ranks (`virtualRank E + virtualRank E'`); this rests on
  `PicardCriteria.virtualRank_baseChange`, base change of *any* algebra map preserving the
  virtual rank of a perfect two-term complex.
* `PicardCriteria.virtualRank_dualPoints_externalSum`: the vector-bundle-stack rank of the
  external sum, over every test algebra `B` of `S ⊗[k] S'`, is `-(virtualRank E + virtualRank E')`
  — the rank-additivity statement for the fibres of `h¹/h⁰((E ⊞ E')ᵛ)`, combining
  `PicardCriteria.virtualRank_dualPoints` with `virtualRank_externalSum`.
* `PicardCriteria.homExternalSum`, `PicardCriteria.isObstructionTheory_externalSum`: the external
  sum of two chain maps `φ : Hom E L`, `φ' : Hom E' L'`, and the fact that if both are obstruction
  theories then so is their external sum
  `homExternalSum k φ φ' : Hom (externalSum k E E') (externalSum k L L')`.
* `PicardCriteria.isObstructionTheory_of_iso_sum`: the degenerate/split case of triangle
  compatibility.  If `E` is chain-homotopy-equivalent to an external sum `F.sum G` — the affine
  model of a *split* distinguished triangle `F ⟶ E ⟶ G ⟶ F[1]` with zero connecting map — and
  `φ_F`, `φ_G` are obstruction theories, then transporting their sum along the homotopy
  equivalence gives an obstruction theory for `E`.

## What is not done

* **The identification with the conormal complex of an actual product.** `externalSum k E E'`
  lands in `LinearTwoTermComplex (S ⊗[k] S')` for *arbitrary* two-term complexes `E`, `E'`; it is
  not identified here with `conormalComplex k (R ⊗[k] R') (I ⊞ I')` for the actual conormal
  complex of the ideal `I ⊞ I' = I.map (Algebra.TensorProduct.includeLeft) ⊔
  I'.map (Algebra.TensorProduct.includeRight)` of a product of local embeddings `Spec S ↪ Spec R`,
  `Spec S' ↪ Spec R'` (`S = R ⧸ I`, `S' = R' ⧸ I'`, matching
  `Cones/NormalConeProduct.lean`/`AffineNormalConeProduct.productIdeal`).  That identification
  needs two further facts, neither of which is available, in the repository or in Mathlib, in the
  generality required:
  - the ideal identity `(I ⊞ I').Cotangent ≃ (I.Cotangent ⊗[S] (S ⊗[k] S')) ×
    ((S ⊗[k] S') ⊗[S'] I'.Cotangent)`.  `Cones/NormalConeProduct.lean` proves the *ring* version
    of this (`AffineNormalConeProduct.grTensorToGr`) only up to an explicit, unproved injectivity
    hypothesis in general, and only its surjectivity and degree-one compatibility
    (`grTensorToGr_degreeOne_left/right`) without extracting the degree-one graded piece as a
    module isomorphism; `Cones/NormalSheafProduct.lean` proves the analogous statement for the
    *normal sheaf ring* `nsTensorToNs`, but only over a field `k` and again without isolating the
    cotangent-module identity from the ring-level one;
  - the Kähler-differential Leibniz identity `Ω[(R ⊗[k] R')⁄k] ≃ ((R ⊗[k] R') ⊗[R] Ω[R⁄k]) ×
    ((R ⊗[k] R') ⊗[R'] Ω[R'⁄k])`.  `Mathlib.RingTheory.Kaehler.TensorProduct` only computes
    `Ω[B⁄S]` for `B` a pushout `S ⊗[k] A` *relative to one of the two factors* `S`
    (`KaehlerDifferential.tensorKaehlerEquiv`/`tensorKaehlerEquivBase`); it does not compute
    `Ω[B⁄k]` relative to the common base, which is what is needed here.  Even the polynomial-ring
    special case `R = k[x_σ]`, `R' = k[x_τ]` suggested as a fallback needs a compatibility lemma
    between `KaehlerDifferential.D` and the currying isomorphism
    `MvPolynomial.sumRingEquiv : MvPolynomial (σ ⊕ τ) k ≃+* MvPolynomial σ (MvPolynomial τ k)`
    that is not already available; this was attempted and found to require genuinely new
    Kähler-differential infrastructure, not a one-file gluing of existing lemmas, so it is left
    undone here (see also `Cones/NormalConeProduct.lean`'s own remark that the corresponding
    normal-*sheaf* statement, as opposed to the normal-*cone* statement, "is not proved here").
* **General (non-split) distinguished triangles.** `isObstructionTheory_of_iso_sum` only handles
  the case of a *degenerate* triangle (an isomorphism to a direct sum, zero connecting map).  The
  general case needs a snake/five-lemma argument through the long exact cohomology sequence
  (`HomologySequence.lean`), matching the retired `CompatibleTransitivity` structure of
  `ObstructionTheory/Properties.lean`; this is genuine new homological algebra, not attempted
  here.
* **Pullback along a general morphism.** Only the two base-change operations already proved in
  `AffineObstructionCone.lean`/`VirtualFundamentalClass/BaseChangeObstruction.lean` (arbitrary
  algebra base change, and the specific comparisons for localisation and for `Spec B × 𝔸^τ`) are
  used; pullback of an obstruction theory along a general morphism of affine schemes is not
  addressed.
* **The geometric statement over a genuine product `X × Y` of schemes or stacks** beyond
  `Spec S × Spec S'` is not addressed.
-/

open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry

namespace PicardCriteria

open LinearTwoTermComplex

universe u

-- Register the algebra structure on the **right** tensor factor of `S ⊗[k] S'` as a local
-- instance.  `Algebra.TensorProduct.leftAlgebra` already gives `Algebra S (S ⊗[k] S')` as a
-- genuine instance; the symmetric statement `Algebra S' (S ⊗[k] S')` is only an `abbrev` in
-- Mathlib (this is the repo's own noted pitfall: "`Algebra B (S ⊗[A] B)` is not an instance, only
-- the left factor"), so it has to be turned on explicitly to base-change *both* factors of an
-- external sum to the tensor product.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ## External sums of two-term complexes over a tensor product of base rings -/

section ExternalSum

variable (k : Type u) [CommRing k] {S S' : Type u} [CommRing S] [Algebra k S] [CommRing S']
  [Algebra k S']

/-- **The external direct sum of two two-term complexes along a common base `k`.**

For a two-term complex `E` over a `k`-algebra `S` and a two-term complex `E'` over a `k`-algebra
`S'`, `externalSum k E E'` is the two-term complex over `S ⊗[k] S'` obtained by base-changing each
factor to the tensor product and taking the (already existing) external direct sum
`LinearTwoTermComplex.sum`.  This models the cotangent complex of a product
`Spec S × Spec S' = Spec (S ⊗[k] S')` of affine `k`-schemes, `L_{X×Y} ≅ pr_X^*L_X ⊕ pr_Y^*L_Y`,
with `LinearTwoTermComplex.baseChange` playing the role of `pr_X^*`/`pr_Y^*`. -/
noncomputable abbrev externalSum (E : LinearTwoTermComplex S) (E' : LinearTwoTermComplex S') :
    LinearTwoTermComplex (S ⊗[k] S') :=
  (E.baseChange (S ⊗[k] S')).sum (E'.baseChange (S ⊗[k] S'))

/-- Base change of any perfect (finite free) two-term complex along any algebra map preserves
finite-freeness. -/
theorem isPerfectTwoTerm_baseChange {T : Type u} [CommRing T] [Algebra S T]
    {E : LinearTwoTermComplex S} (h : IsPerfectTwoTerm E) : IsPerfectTwoTerm (E.baseChange T) := by
  have h1 := h.free_degreeZero
  have h2 := h.finite_degreeZero
  have h3 := h.free_degreeOne
  have h4 := h.finite_degreeOne
  exact
    { free_degreeZero := inferInstance
      finite_degreeZero := inferInstance
      free_degreeOne := inferInstance
      finite_degreeOne := inferInstance }

/-- **Base change along any algebra map preserves the virtual rank of a perfect two-term
complex.**  Base change of a finite free module has the same rank
(`Module.finrank_baseChange`); no flatness or finiteness of the base change map itself is
needed. -/
theorem virtualRank_baseChange {T : Type u} [CommRing T] [Algebra S T] [Nontrivial S]
    [Nontrivial T] {E : LinearTwoTermComplex S} (h : IsPerfectTwoTerm E) :
    virtualRank (E.baseChange T) = virtualRank E := by
  have h1 := h.free_degreeZero
  have h3 := h.free_degreeOne
  have key : ((Module.finrank T (T ⊗[S] E.degreeOne) : ℤ) -
      (Module.finrank T (T ⊗[S] E.degreeZero) : ℤ)) =
      ((Module.finrank S E.degreeOne : ℤ) - (Module.finrank S E.degreeZero : ℤ)) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange]
  exact key

/-- **The external sum of two perfect two-term complexes is perfect.** -/
theorem isPerfectTwoTerm_externalSum {E : LinearTwoTermComplex S} {E' : LinearTwoTermComplex S'}
    (h : IsPerfectTwoTerm E) (h' : IsPerfectTwoTerm E') :
    IsPerfectTwoTerm (externalSum k E E') :=
  (isPerfectTwoTerm_baseChange h).sum (isPerfectTwoTerm_baseChange h')

/-- **Virtual ranks add under external sums over a tensor product of base rings.** -/
theorem virtualRank_externalSum [Nontrivial S] [Nontrivial S'] [Nontrivial (S ⊗[k] S')]
    {E : LinearTwoTermComplex S} {E' : LinearTwoTermComplex S'} (h : IsPerfectTwoTerm E)
    (h' : IsPerfectTwoTerm E') :
    virtualRank (externalSum k E E') = virtualRank E + virtualRank E' := by
  have key := virtualRank_sum (isPerfectTwoTerm_baseChange (T := S ⊗[k] S') h)
    (isPerfectTwoTerm_baseChange (T := S ⊗[k] S') h')
  rw [virtualRank_baseChange h, virtualRank_baseChange h'] at key
  exact key

/-- **The vector-bundle-stack rank of an external sum.**  Over every test algebra `B` of the
product ring `S ⊗[k] S'`, the fibre `h¹/h⁰((E ⊞ E')ᵛ)(B)` is again a finite free two-term complex
(`isFiniteFreeComplex_dualPoints`), of rank `-(virtualRank E + virtualRank E')`: rank additivity
for the target of an external sum of obstruction theories. -/
theorem virtualRank_dualPoints_externalSum [Nontrivial S] [Nontrivial S']
    [Nontrivial (S ⊗[k] S')] {E : LinearTwoTermComplex S} {E' : LinearTwoTermComplex S'}
    (h : IsPerfectTwoTerm E) (h' : IsPerfectTwoTerm E') (B : Type u) [CommRing B]
    [Algebra (S ⊗[k] S') B] [Nontrivial B] :
    virtualRank (dualPoints (externalSum k E E') B) = -(virtualRank E + virtualRank E') := by
  have key := virtualRank_dualPoints (isPerfectTwoTerm_externalSum k h h') B
  rw [virtualRank_externalSum k h h'] at key
  exact key

/-- **The external direct sum of two chain maps over a tensor product of base rings.** -/
noncomputable abbrev homExternalSum {E L : LinearTwoTermComplex S} {E' L' : LinearTwoTermComplex S'}
    (φ : Hom E L) (φ' : Hom E' L') : Hom (externalSum k E E') (externalSum k L L') :=
  (φ.baseChange (S ⊗[k] S')).sum (φ'.baseChange (S ⊗[k] S'))

/-- **The external sum of two obstruction theories over a tensor product of base rings is an
obstruction theory.**

For `φ : E ⟶ L` over `S` and `φ' : E' ⟶ L'` over `S'`, both obstruction theories, the external
sum `homExternalSum k φ φ' : externalSum k E E' ⟶ externalSum k L L'` is an obstruction theory
over `S ⊗[k] S'`.  This is `IsObstructionTheory.baseChange` — unconditional along *any* algebra
map — applied to each factor, followed by `IsObstructionTheory.sum`. -/
theorem isObstructionTheory_externalSum {E L : LinearTwoTermComplex S}
    {E' L' : LinearTwoTermComplex S'} {φ : Hom E L} {φ' : Hom E' L'} (h : IsObstructionTheory φ)
    (h' : IsObstructionTheory φ') : IsObstructionTheory (homExternalSum k φ φ') :=
  (h.baseChange (S ⊗[k] S')).sum (h'.baseChange (S ⊗[k] S'))

end ExternalSum

/-! ## The degenerate (split) case of triangle compatibility -/

section SplitTriangle

variable {R : Type u} [CommRing R]

/-- **The split (degenerate) triangle case of triangle compatibility for obstruction theories.**

If `E` is chain-homotopy-equivalent to the external sum `F.sum G` of two two-term complexes — the
affine, two-term model of a *split* distinguished triangle `F ⟶ E ⟶ G ⟶ F[1]` with zero
connecting map — and `φ_F : Hom F L`, `φ_G : Hom G L'` are both obstruction theories, then the
transport of their external sum along the homotopy equivalence is an obstruction theory for `E`.
This reuses `IsObstructionTheory.sum` (the sum `φ_F.sum φ_G` is an obstruction theory for
`F.sum G`) and `IsObstructionTheory.homotopyEquivalence_comp` (transport along a chain homotopy
equivalence of the source).  The general case of an arbitrary distinguished triangle, with a
possibly nonzero connecting map, is not addressed: see the module docstring. -/
theorem isObstructionTheory_of_iso_sum {F G L L' : LinearTwoTermComplex R} {φF : Hom F L}
    {φG : Hom G L'} (hF : IsObstructionTheory φF) (hG : IsObstructionTheory φG)
    {E : LinearTwoTermComplex R} (e : HomotopyEquivalence E (F.sum G)) :
    IsObstructionTheory ((φF.sum φG).comp e.hom) :=
  (hF.sum hG).homotopyEquivalence_comp e

end SplitTriangle

end PicardCriteria

end GromovWitten.AlgebraicGeometry
