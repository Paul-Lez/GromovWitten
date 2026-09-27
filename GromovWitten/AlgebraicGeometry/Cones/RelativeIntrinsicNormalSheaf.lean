/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.Cones.NormalSheafPicard
import GromovWitten.AlgebraicGeometry.Cones.EmbeddingIndependence
import GromovWitten.AlgebraicGeometry.Cones.PicardBaseChange
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The relative intrinsic normal sheaf and flat base change

For a tower of rings `B → M → M ⧸ I` (a local embedding `U = Spec (M ⧸ I) ↪ M = Spec M` over the
base `Spec B`), `Cones/NormalSheafPicard.lean` already builds the affine intrinsic normal sheaf
`AffineIntrinsicNormalSheaf.conormalComplex B M I : LinearTwoTermComplex (M ⧸ I)` for an
*arbitrary* commutative ring `B` and proves it is `h¹/h⁰` of the dual of the conormal complex.
That construction is already "relative over `B`"; this file only has to name it as such, record
its comparison with the field-extension theory of `Cones/ConormalBaseChange.lean` and the
polynomial-presentation independence of `Cones/EmbeddingIndependence.lean`, and prove the
substantive new content: **flat base change of the whole relative conormal complex** — and hence
of the relative intrinsic normal sheaf — along an arbitrary ring map `B → B'` with `B'` flat over
`B`, not merely along a field extension and not merely for polynomial ambient rings.

## Contents

* `relativeConormalComplex B M I`: the relative conormal complex of `Spec (M ⧸ I) ⊆ Spec M`
  over `Spec B`, literally `AffineIntrinsicNormalSheaf.conormalComplex B M I`.
* `relativeIntrinsicNormalSheafEquiv`: the relative intrinsic normal sheaf `[N_{U/M}/T_M|_U]` is
  `h¹/h⁰` of the dual of `relativeConormalComplex`, over every test algebra — a re-export of
  `normalSheafQuotientEquivDualPoints` under the relative name.
* `relative_over_field_eq_absolute`: the relative conormal complex over a base `B` is
  *definitionally* the object used by the field-restricted theory (purity in
  `Cones/NormalConeDimension.lean`, base change in `Cones/ConormalBaseChange.lean`): setting
  `B := k` a field recovers `AffineIntrinsicNormalSheaf.conormalComplex k R I` verbatim, since
  `relativeConormalComplex` is *defined* to be that object for an arbitrary base ring.
* `relativeEmbeddingIndependence`: chart independence over `B` for the polynomial-presentation
  model of `Cones/EmbeddingIndependence.lean`. Its base ring `A` was already arbitrary there, so
  the relative statement is *already* the general one: setting `A := B` needs no new proof.
* `relativeKaehlerBaseChange`: **flat (in fact unconditional) base change of the ambient Kähler
  differentials**, `Ω[M'⁄B'] ≅ M' ⊗_M Ω[M⁄B]` for `M' := B' ⊗[B] M`, via
  `KaehlerDifferential.tensorKaehlerEquiv`.
* `relativeConormalBaseChange`: **flat base change of the conormal module**,
  `B' ⊗[B] (I/I²) ≅ I'/I'²` for `I' := I.map (M → M')`, given `Module.Flat B B'`, via
  `Ideal.tensorCotangentEquiv`.
* `relativeQuotientBaseChangeEquiv`: the target ring of the base-changed presentation,
  `B' ⊗[B] (M ⧸ I) ≅ M' ⧸ I'`, via `Algebra.TensorProduct.tensorQuotientEquiv`.
* `relativeConormalBaseChangeMap`, `relativeConormalBaseChangeLinearEquiv`: the degree-zero
  comparison `(M' ⧸ I') ⊗[M ⧸ I] (I/I²) → I'/I'²`, linear over the quotient ring `M' ⧸ I'` (not
  merely over `B'`), and the proof that it is **bijective** for `B'` flat over `B`.
* `relativeKaehlerDegreeOneEquiv`: the degree-one comparison
  `(M' ⧸ I') ⊗[M ⧸ I] ((M ⧸ I) ⊗[M] Ω[M⁄B]) ≃ (M' ⧸ I') ⊗[M'] Ω[M'⁄B']`, unconditionally.
* `relativeConormalComplexBaseChange`: **flat base change of the relative conormal complex** — a
  `LinearTwoTermComplex.HomotopyEquivalence` (indeed an isomorphism of complexes, with zero
  homotopies) between `(relativeConormalComplex B M I).baseChange (M' ⧸ I')` and
  `relativeConormalComplex B' M' I'`.
* `relativeNormalSheafBaseChangeEquiv`: **the relative intrinsic normal sheaf is invariant under
  flat base change**, over every test algebra — the affine model of the base-change compatibility
  of `N_{U/B}` used by the virtual fundamental class.
* `relativeDualPointsBaseChangeEquiv`: the same invariance in the `h¹/h⁰` form, for the
  Picard-groupoid criteria of `Cones/PicardBaseChange.lean`.

## The key technical point

`Ideal.Cotangent` equips `I.Cotangent` with a `Module S` structure for every `S` with
`Algebra S M`, and derives `IsScalarTower S S'` only for *intermediate rings* `S'` carrying an
`Algebra S' M`. The residue ring `M ⧸ I` is not such an intermediate ring, so the tower
`IsScalarTower B (M ⧸ I) I.Cotangent` — exactly what is needed to cancel the base change in
`(M' ⧸ I') ⊗[M ⧸ I] (I/I²)` — is missing from Mathlib, and it is *not* a `rfl`-lemma (an earlier
pass mistook this for an unresolvable instance diamond). It is supplied here by
`isScalarTower_quotient_cotangent`, which composes the two derived towers
`IsScalarTower B M I.Cotangent` and `IsScalarTower M (M ⧸ I) I.Cotangent` propositionally. With it
in place, the cancellation is `Algebra.IsPushout.cancelBaseChange`, applied to the pushout square
`relativeQuotientIsPushout` extracted from `relativeQuotientBaseChangeEquiv`.

## What is not done here

Purity of the relative intrinsic normal cone over a smooth base, and the globalisation of the
above from the affine model `B → M → M ⧸ I` to a morphism of algebraic stacks, remain out of
scope. Chart independence (`relativeEmbeddingIndependence`) is only available for the
polynomial-presentation model of `Cones/EmbeddingIndependence.lean`, not for the general ambient
ring `M` used in the rest of this file.
-/

open CategoryTheory

open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry

open ConeQuotient ConeRefinement

universe u

/-! ## The relative conormal complex and intrinsic normal sheaf -/

section RelativeApi

variable (B M : Type u) [CommRing B] [CommRing M] [Algebra B M] (I : Ideal M)

/-- **The relative conormal complex** of the local embedding `U = Spec (M ⧸ I) ↪ M = Spec M`
over the base `Spec B`: the two-term complex `[I/I² → (M/I) ⊗_M Ω[M⁄B]]` of
`AffineIntrinsicNormalSheaf.conormalComplex`, viewed as depending on an arbitrary base ring `B`
(not merely a field or `ℤ`). -/
noncomputable abbrev relativeConormalComplex : LinearTwoTermComplex (M ⧸ I) :=
  NormalSheafPicard.AffineIntrinsicNormalSheaf.conormalComplex B M I

variable (Bb : Type u) [CommRing Bb] [Algebra (M ⧸ I) Bb]

/-- **The relative intrinsic normal sheaf.** Over every test algebra `Bb`, the quotient
groupoid `[N_{U/M}/T_M|_U](Bb)` of the affine normal sheaf is equivalent to the fibre of
`h¹/h⁰` of the dual of `relativeConormalComplex`. This is
`normalSheafQuotientEquivDualPoints` under the relative name. -/
noncomputable def relativeIntrinsicNormalSheafEquiv :
    QuotientGroupoid (AffineNormalCone.normalSheafTangentAction B M I) Bb ≌
      (PicardCriteria.dualPoints (relativeConormalComplex B M I) Bb).quotient :=
  NormalSheafPicard.AffineIntrinsicNormalSheaf.normalSheafQuotientEquivDualPoints B M I Bb

/-- **Relative over a field is definitionally absolute.** `relativeConormalComplex` is *defined*
to be `AffineIntrinsicNormalSheaf.conormalComplex B M I` for an arbitrary base ring `B`; in
particular, when `B = k` is the field of the absolute theory
(`Cones/NormalConeDimension.lean`, `Cones/ConormalBaseChange.lean`), the relative and absolute
conormal complexes agree on the nose. -/
theorem relative_over_field_eq_absolute :
    relativeConormalComplex B M I =
      NormalSheafPicard.AffineIntrinsicNormalSheaf.conormalComplex B M I :=
  rfl

end RelativeApi

/-! ## Chart independence over the base `B` -/

section EmbeddingIndependence

/-- **Chart independence over the relative base `B`.**
`EmbeddingIndependence.presentationEquivalence` already quantifies over an *arbitrary* base ring
(called `A` there), so setting `A := B` gives chart independence over our relative base with no
adaptation: for two polynomial presentations
`π : B[x_σ] ↠ S`, `π' : B[x_σ'] ↠ S` of the same `B`-algebra `S`, with lifts `h, k` of the
generators in both directions, the quotient groupoids `ConeGroupoid (presIdeal π) Bb` and
`ConeGroupoid (presIdeal π') Bb` are equivalent for every test algebra `Bb`. This is the affine
polynomial-presentation model of `Cones/RefinementQuotient.lean`; it is *not* the general
`relativeConormalComplex`/`AffineIntrinsicNormalSheaf` model above (arbitrary ambient ring `M`),
which does not yet have its own embedding-independence theorem. -/
noncomputable def relativeEmbeddingIndependence {B : Type u} [CommRing B] {σ σ' S : Type u}
    [CommRing S] [Algebra B S] {π : MvPolynomial σ B →ₐ[B] S} {π' : MvPolynomial σ' B →ₐ[B] S}
    {h : σ' → MvPolynomial σ B} {k : σ → MvPolynomial σ' B}
    (hh : ∀ t, π (h t) = π' (MvPolynomial.X t)) (hk : ∀ i, π' (k i) = π (MvPolynomial.X i))
    (Bb : Type u) [CommRing Bb] :
    ConeGroupoid (EmbeddingIndependence.presIdeal π) Bb ≌
      ConeGroupoid (EmbeddingIndependence.presIdeal π') Bb :=
  EmbeddingIndependence.presentationEquivalence hh hk Bb

end EmbeddingIndependence

/-! ## Flat base change: the ambient ring and its Kähler differentials -/

section KaehlerBaseChange

variable (B M B' : Type u) [CommRing B] [CommRing M] [Algebra B M] [CommRing B'] [Algebra B B']

/-- **The base-changed ambient ring** `M' := B' ⊗[B] M` of `Spec M` along `Spec B' → Spec B`. -/
noncomputable abbrev baseChangeAmbient : Type u := B' ⊗[B] M

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Flat base change of the ambient Kähler differentials.** For `M' := B' ⊗[B] M`, the
`M'`-module of relative differentials of `M'` over `B'` is the base change of `Ω[M⁄B]`:
`Ω[M'⁄B'] ≅ M' ⊗_M Ω[M⁄B]`. Unlike the conormal module below, this holds *unconditionally*, with
no flatness hypothesis on `B'`: Kähler differentials always commute with base change. This is
`KaehlerDifferential.tensorKaehlerEquiv` (`Mathlib/RingTheory/Kaehler/TensorProduct.lean`)
specialised to the pushout square `B → M`, `B → B' → M'`. -/
noncomputable def relativeKaehlerBaseChange :
    baseChangeAmbient B M B' ⊗[M] Ω[M⁄B] ≃ₗ[baseChangeAmbient B M B']
      Ω[baseChangeAmbient B M B'⁄B'] :=
  KaehlerDifferential.tensorKaehlerEquiv B B' M (baseChangeAmbient B M B')

end KaehlerBaseChange

/-! ## Flat base change: the conormal module -/

section ConormalBaseChange

variable (B M B' : Type u) [CommRing B] [CommRing M] [Algebra B M] [CommRing B'] [Algebra B B']
  [Module.Flat B B'] (I : Ideal M)

/-- **The extended ideal** `I' := I · M'` of `I` along the base change `M → M' = B' ⊗[B] M`. -/
noncomputable abbrev baseChangeIdeal : Ideal (baseChangeAmbient B M B') :=
  I.map (Algebra.TensorProduct.includeRight.toRingHom : M →+* baseChangeAmbient B M B')

/-- **Flat base change of the conormal module.** For `B'` flat over `B`, extension of the ideal
`I` along `M → M' = B' ⊗[B] M` commutes with forming the conormal module `I/I²`:
`B' ⊗[B] (I/I²) ≅ I'/I'²` for `I' := I.map (M → M')`. This is `Ideal.tensorCotangentEquiv`
(`Mathlib/RingTheory/Ideal/CotangentBaseChange.lean`), which combines right-exactness of the
tensor product with the injectivity of `I ⊗[B] B' → M ⊗[B] B'` supplied by flatness of `B'`. -/
noncomputable def relativeConormalBaseChange :
    B' ⊗[B] I.Cotangent ≃ₗ[B'] (baseChangeIdeal B M B' I).Cotangent :=
  Ideal.tensorCotangentEquiv B B' I

/-- **The base-changed quotient ring.** `M' ⧸ I'` is the base change `B' ⊗[B] (M ⧸ I)` of the
target `M ⧸ I` of the original presentation: extension of ideals along a base change commutes
with forming the quotient, unconditionally (no flatness needed here, unlike the conormal module
above). This is `Algebra.TensorProduct.tensorQuotientEquiv`
(`Mathlib/RingTheory/TensorProduct/Quotient.lean`). -/
noncomputable def relativeQuotientBaseChangeEquiv :
    B' ⊗[B] (M ⧸ I) ≃ₐ[B'] baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I :=
  Algebra.TensorProduct.tensorQuotientEquiv (R := B) B' M B' I

end ConormalBaseChange

/-! ## A missing scalar tower for conormal modules -/

section CotangentScalarTower

/-- **The base ring acts on `J/J²` through the residue ring.** For an `A`-algebra `R` and an ideal
`J ≤ R`, the `A`-action on the conormal module `J/J²` — coming from `Ideal.Cotangent`'s generic
`Algebra A R`-parametrised module structure — factors through `R ⧸ J`.

This scalar tower is missing from Mathlib: `Ideal.Cotangent` derives `IsScalarTower A A'` only for
*intermediate rings* `A'` with `Algebra A' R`, and `R ⧸ J` is not such a ring. It is *not* a
`rfl`-lemma; the proof composes the two derived towers `IsScalarTower A R J.Cotangent` and
`IsScalarTower R (R ⧸ J) J.Cotangent`. It is the instance whose absence blocked the base-change
comparison below in an earlier pass. -/
theorem isScalarTower_quotient_cotangent (A R : Type*) [CommRing A] [CommRing R] [Algebra A R]
    (J : Ideal R) : IsScalarTower A (R ⧸ J) J.Cotangent :=
  IsScalarTower.of_algebraMap_smul fun a y => by
    rw [IsScalarTower.algebraMap_apply A R (R ⧸ J), IsScalarTower.algebraMap_smul,
      IsScalarTower.algebraMap_smul]

end CotangentScalarTower

/-! ## The assembled base-change isomorphism of conormal complexes -/

section Assembly

variable (B M B' : Type u) [CommRing B] [CommRing M] [Algebra B M] [CommRing B'] [Algebra B B']
  [Module.Flat B B'] (I : Ideal M)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The induced map on quotient rings.** `M ⧸ I → M' ⧸ I'`, induced by `M → M'` since `I` maps
into `I'` by construction of `I' := I.map (M → M')`. This is the ring map along which
`relativeConormalComplex B' M' I'` becomes a `LinearTwoTermComplex.baseChange` of
`relativeConormalComplex B M I`. -/
noncomputable def relativeQuotientMap :
    (M ⧸ I) →+* baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I :=
  Ideal.quotientMap (baseChangeIdeal B M B' I)
    (Algebra.TensorProduct.includeRight.toRingHom : M →+* baseChangeAmbient B M B')
    Ideal.le_comap_map

/-- The base-changed quotient ring is an algebra over the original one, via
`relativeQuotientMap`. -/
@[instance_reducible]
noncomputable def relativeQuotientAlgebra :
    Algebra (M ⧸ I) (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) :=
  (relativeQuotientMap B M B' I).toAlgebra

attribute [local instance] relativeQuotientAlgebra

/-- **The conormal comparison map, over the ambient ring `M`.** The functorial map `I/I² → I'/I'²`
of conormal modules induced by `M → M'`, `M`-linear (`Ideal.mapCotangent`). -/
noncomputable def relativeConormalMapAmbient :
    I.Cotangent →ₗ[M] (baseChangeIdeal B M B' I).Cotangent :=
  Ideal.mapCotangent I (baseChangeIdeal B M B' I) (Algebra.ofId M (baseChangeAmbient B M B'))
    Ideal.le_comap_map

/-- **The conormal comparison map, over the quotient ring `M ⧸ I`.** Since `M ⧸ I → M' ⧸ I'` is
surjective, the `M`-linear map `relativeConormalMapAmbient` is automatically linear over the
quotient ring, by `LinearMap.extendScalarsOfSurjective`. -/
@[instance_reducible]
noncomputable def relativeConormalModule :
    Module (M ⧸ I) (baseChangeIdeal B M B' I).Cotangent :=
  Module.compHom _ (relativeQuotientMap B M B' I)

attribute [local instance] relativeConormalModule

instance relativeConormalTower :
    IsScalarTower M (M ⧸ I) (baseChangeIdeal B M B' I).Cotangent :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

noncomputable def relativeConormalMap :
    I.Cotangent →ₗ[M ⧸ I] (baseChangeIdeal B M B' I).Cotangent :=
  (relativeConormalMapAmbient B M B' I).extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective (I := I))

/-- Compatibility of the `M ⧸ I`-action on `(baseChangeIdeal B M B' I).Cotangent` (via
`relativeConormalModule`) with its own `M' ⧸ I'`-module structure, needed to state
`relativeConormalBaseChangeMap` as an `(M' ⧸ I')`-linear base change. -/
instance relativeConormalQuotientTower :
    IsScalarTower (M ⧸ I) (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I)
      (baseChangeIdeal B M B' I).Cotangent :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- **The degree-zero comparison map of the base-changed conormal complex.** The `(M' ⧸ I')`-linear
map `(M' ⧸ I') ⊗[M ⧸ I] (I/I²) → I'/I'²` obtained by base-changing `relativeConormalMap` along
`M ⧸ I → M' ⧸ I'`. This is the degree-zero component of the chain map
`relativeConormalBaseChangeHom`, and it is **bijective** when `B'` is flat over `B`
(`relativeConormalBaseChangeMap_bijective`, packaged as
`relativeConormalBaseChangeLinearEquiv`). -/
noncomputable def relativeConormalBaseChangeMap :
    (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) ⊗[M ⧸ I] I.Cotangent →ₗ[
      baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I] (baseChangeIdeal B M B' I).Cotangent :=
  LinearMap.liftBaseChange _ (relativeConormalMap B M B' I)

/-- **The quotient ring comparison, linear over `M ⧸ I`.** `relativeQuotientBaseChangeEquiv` is a
`B'`-algebra isomorphism `B' ⊗[B] (M ⧸ I) ≃ M' ⧸ I'`; this repackages the same underlying
bijection as an `(M ⧸ I)`-linear equivalence, using that it intertwines the algebra maps out of
`M ⧸ I` on both sides (checked directly from the defining formulas of
`Algebra.TensorProduct.tensorQuotientEquiv`). This is the key extra input, beyond
`relativeConormalBaseChange` and `relativeKaehlerBaseChange`, needed to assemble the base-change
isomorphism of two-term complexes: it lets the (`B'`-linear) degree-zero and degree-one
comparisons be re-expressed as tensoring over `M ⧸ I`, matching
`LinearTwoTermComplex.baseChange`. -/
noncomputable def relativeQuotientBaseChangeLinearEquiv :
    B' ⊗[B] (M ⧸ I) ≃ₗ[M ⧸ I] (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) :=
  AddEquiv.toLinearEquiv (relativeQuotientBaseChangeEquiv B M B' I).toAddEquiv (fun c x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul b y =>
      obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective y
      change relativeQuotientBaseChangeEquiv B M B' I
          (Ideal.Quotient.mk I m • b ⊗ₜ[B] Ideal.Quotient.mk I n) =
        relativeQuotientMap B M B' I (Ideal.Quotient.mk I m) •
          relativeQuotientBaseChangeEquiv B M B' I (b ⊗ₜ[B] Ideal.Quotient.mk I n)
      simp only [Algebra.smul_def]
      rw [map_mul]
      congr 1)

attribute [local instance] isScalarTower_quotient_cotangent

omit [Module.Flat B B'] in
/-- **The base ring `B` acts on `M' ⧸ I'` through `M ⧸ I`.** The two structure maps
`B → M → M ⧸ I → M' ⧸ I'` and `B → M' → M' ⧸ I'` agree, because
`1 ⊗ₜ algebraMap B M b = algebraMap B M' b` in `M' = B' ⊗[B] M`. -/
theorem relativeQuotientTower : IsScalarTower B (M ⧸ I)
    (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) :=
  IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B M (M ⧸ I)]
    change algebraMap B (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) b =
      relativeQuotientMap B M B' I (Ideal.Quotient.mk I (algebraMap B M b))
    rw [relativeQuotientMap, Ideal.quotientMap_mk, ← Ideal.Quotient.mk_algebraMap]
    congr 1
    exact (Algebra.TensorProduct.includeRight.commutes b).symm

attribute [local instance] relativeQuotientTower

omit [Module.Flat B B'] in
/-- **`M' ⧸ I'` is the base change of `M ⧸ I` along `B → B'`**, as a pushout square of rings
```
B   →  B'
↓      ↓
M ⧸ I → M' ⧸ I'
```
This is `relativeQuotientBaseChangeEquiv` recorded as an `Algebra.IsPushout` instance, which is
the form required by the cancellation equivalence `Algebra.IsPushout.cancelBaseChange`. -/
theorem relativeQuotientIsPushout : Algebra.IsPushout B B' (M ⧸ I)
    (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) :=
  Algebra.IsPushout.of_equiv (relativeQuotientBaseChangeEquiv B M B' I) (by ext c; rfl)

attribute [local instance] relativeQuotientIsPushout

/-- **Cancelling the base change in the source of the comparison map.** Since `M' ⧸ I'` is the
base change `B' ⊗[B] (M ⧸ I)`, tensoring `I/I²` up to `M' ⧸ I'` over `M ⧸ I` is the same as
tensoring it up to `B'` over `B`:
`(M' ⧸ I') ⊗[M ⧸ I] (I/I²) ≃ₗ[B'] B' ⊗[B] (I/I²)`.
This is `Algebra.IsPushout.cancelBaseChange`, which needs exactly the scalar tower
`isScalarTower_quotient_cotangent B M I` on `I/I²` and the pushout square
`relativeQuotientIsPushout`. -/
noncomputable def relativeConormalCancelBaseChange :
    (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) ⊗[M ⧸ I] I.Cotangent ≃ₗ[B']
      B' ⊗[B] I.Cotangent :=
  Algebra.IsPushout.cancelBaseChange B B' (M ⧸ I)
    (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) I.Cotangent

/-- The flat base-change equivalence `relativeConormalBaseChange` on a pure tensor: it sends
`b' ⊗ y` to `b' • (image of y)`, the image being taken along the functorial conormal map
`relativeConormalMapAmbient`. -/
theorem relativeConormalBaseChange_tmul (b' : B') (y : I.Cotangent) :
    relativeConormalBaseChange B M B' I (b' ⊗ₜ[B] y) =
      b' • relativeConormalMapAmbient B M B' I y := by
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective I y
  rfl

/-- **The comparison map matches the flat base-change equivalence**, after cancelling the base
change in the source: `relativeConormalBaseChangeMap ∘ relativeConormalCancelBaseChange.symm =
relativeConormalBaseChange`. Both sides are additive and agree on pure tensors `b' ⊗ y`, where
they both give `b' • (image of y)`; the linearity discrepancy (`M' ⧸ I'` versus `B'`) is absorbed
by the scalar tower `isScalarTower_quotient_cotangent B' (baseChangeAmbient B M B') _`. -/
theorem relativeConormalBaseChangeMap_cancel_symm (z : B' ⊗[B] I.Cotangent) :
    relativeConormalBaseChangeMap B M B' I
        ((relativeConormalCancelBaseChange B M B' I).symm z) =
      relativeConormalBaseChange B M B' I z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b' y =>
    rw [relativeConormalCancelBaseChange, Algebra.IsPushout.cancelBaseChange_symm_tmul,
      relativeConormalBaseChangeMap, LinearMap.liftBaseChange_tmul,
      relativeConormalBaseChange_tmul, IsScalarTower.algebraMap_smul]
    rfl

/-- `relativeConormalBaseChangeMap` factors as the cancellation equivalence followed by the flat
base-change equivalence. -/
theorem relativeConormalBaseChangeMap_apply
    (u : (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) ⊗[M ⧸ I] I.Cotangent) :
    relativeConormalBaseChangeMap B M B' I u =
      relativeConormalBaseChange B M B' I (relativeConormalCancelBaseChange B M B' I u) := by
  have h := relativeConormalBaseChangeMap_cancel_symm B M B' I
    (relativeConormalCancelBaseChange B M B' I u)
  rwa [LinearEquiv.symm_apply_apply] at h

/-- **Bijectivity of the degree-zero comparison map.** For `B'` flat over `B`, the
`(M' ⧸ I')`-linear map `(M' ⧸ I') ⊗[M ⧸ I] (I/I²) → I'/I'²` is bijective: by
`relativeConormalBaseChangeMap_apply` it is the composite of the two bijections
`relativeConormalCancelBaseChange` and `relativeConormalBaseChange`. -/
theorem relativeConormalBaseChangeMap_bijective :
    Function.Bijective (relativeConormalBaseChangeMap B M B' I) := by
  have h : (relativeConormalBaseChangeMap B M B' I : _ → _) =
      (relativeConormalBaseChange B M B' I) ∘ (relativeConormalCancelBaseChange B M B' I) :=
    funext (relativeConormalBaseChangeMap_apply B M B' I)
  rw [h]
  exact (relativeConormalBaseChange B M B' I).bijective.comp
    (relativeConormalCancelBaseChange B M B' I).bijective

/-- **Flat base change of the conormal module, in the form needed for the conormal complex.**
For `B'` flat over `B`, the degree-zero term of the base-changed relative conormal complex is the
base change of the degree-zero term:
`(M' ⧸ I') ⊗[M ⧸ I] (I/I²) ≃ₗ[M' ⧸ I'] I'/I'²`.
Unlike `relativeConormalBaseChange`, this is linear over the *quotient* ring `M' ⧸ I'`, which is
the ring over which the relative conormal complex `relativeConormalComplex B' M' I'` lives, so
this is the degree-zero half of the base-change isomorphism of two-term complexes. -/
noncomputable def relativeConormalBaseChangeLinearEquiv :
    (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) ⊗[M ⧸ I] I.Cotangent ≃ₗ[
      baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I]
      (baseChangeIdeal B M B' I).Cotangent :=
  LinearEquiv.ofBijective (relativeConormalBaseChangeMap B M B' I)
    (relativeConormalBaseChangeMap_bijective B M B' I)

omit [Module.Flat B B'] in
/-- **The ambient ring `M` acts on `M' ⧸ I'` through `M ⧸ I`.** Both structure maps send `m` to
the class of `1 ⊗ₜ m`, so this holds definitionally. -/
theorem relativeQuotientTowerAmbient : IsScalarTower M (M ⧸ I)
    (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] relativeQuotientTowerAmbient

/-- **The degree-one comparison of the base-changed conormal complex.** The degree-one term of
`relativeConormalComplex B M I` is the restricted cotangent bundle `(M ⧸ I) ⊗[M] Ω[M⁄B]`, so the
degree-one term of its base change along `M ⧸ I → M' ⧸ I'` is
`(M' ⧸ I') ⊗[M ⧸ I] ((M ⧸ I) ⊗[M] Ω[M⁄B])`; the degree-one term of
`relativeConormalComplex B' M' I'` is `(M' ⧸ I') ⊗[M'] Ω[M'⁄B']`. They are identified by
cancelling the intermediate base changes (`TensorProduct.AlgebraTensorModule.cancelBaseChange`,
twice) and applying `relativeKaehlerBaseChange : M' ⊗[M] Ω[M⁄B] ≃ₗ[M'] Ω[M'⁄B']`. No flatness is
needed: Kähler differentials always commute with base change. -/
noncomputable def relativeKaehlerDegreeOneEquiv :
    (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) ⊗[M ⧸ I]
        ((M ⧸ I) ⊗[M] Ω[M⁄B]) ≃ₗ[baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I]
      (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) ⊗[baseChangeAmbient B M B']
        Ω[baseChangeAmbient B M B'⁄B'] :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange M (M ⧸ I)
      (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I)
      (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) Ω[M⁄B] ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange M (baseChangeAmbient B M B')
      (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I)
      (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) Ω[M⁄B]).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) _)
      (relativeKaehlerBaseChange B M B')

omit [Module.Flat B B'] in
/-- **The two comparison maps commute with the conormal differentials.** Both sides send the
generator `t ⊗ [y]`, for `y ∈ I`, to `t ⊗ d(1 ⊗ y)` in `(M' ⧸ I') ⊗[M'] Ω[M'⁄B']`. This is the
compatibility that turns `relativeConormalBaseChangeMap` and `relativeKaehlerDegreeOneEquiv` into
a chain map of two-term complexes. -/
theorem relativeConormalBaseChange_comm
    (x : (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) ⊗[M ⧸ I] I.Cotangent) :
    relativeKaehlerDegreeOneEquiv B M B' I
        (LinearMap.baseChange (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I)
          (AffineNormalCone.conormalMap B M I) x) =
      AffineNormalCone.conormalMap B' (baseChangeAmbient B M B') (baseChangeIdeal B M B' I)
        (relativeConormalBaseChangeMap B M B' I x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul t c =>
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective I c
    rw [LinearMap.baseChange_tmul, AffineNormalCone.conormalMap_toCotangent,
      relativeConormalBaseChangeMap, LinearMap.liftBaseChange_tmul, map_smul]
    have hr : relativeConormalMap B M B' I (I.toCotangent y) =
        (baseChangeIdeal B M B' I).toCotangent
          ⟨1 ⊗ₜ (y : M), Ideal.mem_map_of_mem _ y.2⟩ := rfl
    rw [hr, AffineNormalCone.conormalMap_toCotangent, relativeKaehlerDegreeOneEquiv]
    simp only [LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
      relativeKaehlerBaseChange, KaehlerDifferential.tensorKaehlerEquiv_tmul_D,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl

/-- **The comparison chain map** from the base change of the relative conormal complex of
`I ⊆ M` along `M ⧸ I → M' ⧸ I'` to the relative conormal complex of `I' ⊆ M'` over `B'`. -/
noncomputable def relativeConormalBaseChangeHom :
    LinearTwoTermComplex.Hom
      ((relativeConormalComplex B M I).baseChange
        (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I))
      (relativeConormalComplex B' (baseChangeAmbient B M B') (baseChangeIdeal B M B' I)) where
  degreeZero := relativeConormalBaseChangeMap B M B' I
  degreeOne := (relativeKaehlerDegreeOneEquiv B M B' I).toLinearMap
  comm x := relativeConormalBaseChange_comm B M B' I x

/-- The inverse comparison chain map, using that both comparisons are bijective (degree zero by
`relativeConormalBaseChangeMap_bijective`, which is where flatness of `B'` enters). -/
noncomputable def relativeConormalBaseChangeInv :
    LinearTwoTermComplex.Hom
      (relativeConormalComplex B' (baseChangeAmbient B M B') (baseChangeIdeal B M B' I))
      ((relativeConormalComplex B M I).baseChange
        (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I)) where
  degreeZero := (relativeConormalBaseChangeLinearEquiv B M B' I).symm.toLinearMap
  degreeOne := (relativeKaehlerDegreeOneEquiv B M B' I).symm.toLinearMap
  comm y := by
    have hx : relativeConormalBaseChangeMap B M B' I
        ((relativeConormalBaseChangeLinearEquiv B M B' I).symm y) = y :=
      (relativeConormalBaseChangeLinearEquiv B M B' I).apply_symm_apply y
    have hcomm := relativeConormalBaseChange_comm B M B' I
      ((relativeConormalBaseChangeLinearEquiv B M B' I).symm y)
    rw [hx] at hcomm
    change (relativeKaehlerDegreeOneEquiv B M B' I).symm
        (AffineNormalCone.conormalMap B' (baseChangeAmbient B M B')
          (baseChangeIdeal B M B' I) y) = _
    rw [← hcomm]
    exact (relativeKaehlerDegreeOneEquiv B M B' I).symm_apply_apply _

/-- **Flat base change of the relative conormal complex.** For a ring map `B → B'` with `B'` flat
over `B`, an ambient `B`-algebra `M` and an ideal `I ≤ M`, put `M' := B' ⊗[B] M` and
`I' := I · M'`. Then the degreewise base change of `relativeConormalComplex B M I` along
`M ⧸ I → M' ⧸ I'` is isomorphic — hence chain-homotopy equivalent, with zero homotopies — to
`relativeConormalComplex B' M' I'`:
`(relativeConormalComplex B M I).baseChange (M' ⧸ I') ≃ relativeConormalComplex B' M' I'`.
In degree zero this is flat base change of the conormal module `I/I²`
(`relativeConormalBaseChangeLinearEquiv`, where flatness is used), in degree one the unconditional
base change of the Kähler differentials (`relativeKaehlerDegreeOneEquiv`), and the two are
compatible with the conormal differential by `relativeConormalBaseChange_comm`.

This is the general-ambient-ring, arbitrary-flat-base analogue of
`ConormalBaseChange.conormalBaseChange`, which only covers polynomial ambient rings and a base
*field* extension. -/
noncomputable def relativeConormalComplexBaseChange :
    LinearTwoTermComplex.HomotopyEquivalence
      ((relativeConormalComplex B M I).baseChange
        (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I))
      (relativeConormalComplex B' (baseChangeAmbient B M B') (baseChangeIdeal B M B' I)) where
  hom := relativeConormalBaseChangeHom B M B' I
  inv := relativeConormalBaseChangeInv B M B' I
  unit :=
    { homotopy := 0
      degreeZero x := by
        refine ((relativeConormalBaseChangeLinearEquiv B M B' I).symm_apply_apply x).trans ?_
        exact (NormalSheafPicard.add_eq_of_eq_zero_degreeZero _ _ rfl).symm
      degreeOne x :=
        ((relativeKaehlerDegreeOneEquiv B M B' I).symm_apply_apply x).trans
          (NormalSheafPicard.add_eq_of_eq_zero_degreeOne _ _ (map_zero _)).symm }
  counit :=
    { homotopy := 0
      degreeZero y := by
        refine ((relativeConormalBaseChangeLinearEquiv B M B' I).apply_symm_apply y).symm.trans ?_
        exact (NormalSheafPicard.add_eq_of_eq_zero_degreeZero
          (E := relativeConormalComplex B' (baseChangeAmbient B M B')
            (baseChangeIdeal B M B' I)) _ _ rfl).symm
      degreeOne y :=
        ((relativeKaehlerDegreeOneEquiv B M B' I).apply_symm_apply y).symm.trans
          (NormalSheafPicard.add_eq_of_eq_zero_degreeOne
            (E := relativeConormalComplex B' (baseChangeAmbient B M B')
              (baseChangeIdeal B M B' I)) _ _ (map_zero _)).symm }

omit [Module.Flat B B'] in
/-- The base ring `B` acts on `M' = B' ⊗[B] M` through `M`: `algebraMap B B' b ⊗ₜ 1 =
1 ⊗ₜ algebraMap B M b`. -/
theorem relativeAmbientTower : IsScalarTower B M (baseChangeAmbient B M B') :=
  IsScalarTower.of_algebraMap_eq fun b =>
    (Algebra.TensorProduct.includeRight.commutes b).symm

attribute [local instance] relativeAmbientTower

/-- **The relative intrinsic normal sheaf is invariant under flat base change.** For `B'` flat
over `B`, `M' := B' ⊗[B] M` and `I' := I · M'`, the quotient groupoid
`[N_{U'/M'} / T_{M'/B'}|_{U'}](Bb)` of the base-changed presentation is equivalent, over every
test algebra `Bb` (an `M' ⧸ I'`-algebra which is compatibly an `M ⧸ I`-algebra), to
`[N_{U/M} / T_{M/B}|_U](Bb)`.

This discharges the `compare` hypothesis of
`NormalSheafPicard.AffineIntrinsicNormalSheaf.normalSheafBaseChangeEquiv` with
`relativeConormalComplexBaseChange`, and is the affine model of the statement that the intrinsic
normal sheaf of `U → Spec B` is compatible with flat base change of the base. -/
noncomputable def relativeNormalSheafBaseChangeEquiv (Bb : Type u) [CommRing Bb]
    [Algebra (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) Bb] [Algebra (M ⧸ I) Bb]
    [IsScalarTower (M ⧸ I) (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) Bb] :
    QuotientGroupoid (AffineNormalCone.normalSheafTangentAction B'
        (baseChangeAmbient B M B') (baseChangeIdeal B M B' I)) Bb ≌
      QuotientGroupoid (AffineNormalCone.normalSheafTangentAction B M I) Bb :=
  NormalSheafPicard.AffineIntrinsicNormalSheaf.normalSheafBaseChangeEquiv I
    (baseChangeIdeal B M B' I) Bb (relativeConormalComplexBaseChange B M B' I)

omit [Module.Flat B B'] in
/-- The degree-zero comparison map on a pure tensor: `u ⊗ [x] ↦ u · [1 ⊗ x]`. -/
@[simp]
theorem relativeConormalBaseChangeMap_tmul
    (u : baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) (y : I.Cotangent) :
    relativeConormalBaseChangeMap B M B' I (u ⊗ₜ[M ⧸ I] y) =
      u • relativeConormalMap B M B' I y :=
  rfl

/-- The underlying map of `relativeConormalBaseChangeLinearEquiv` is
`relativeConormalBaseChangeMap`. -/
@[simp]
theorem relativeConormalBaseChangeLinearEquiv_apply
    (u : (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) ⊗[M ⧸ I] I.Cotangent) :
    relativeConormalBaseChangeLinearEquiv B M B' I u =
      relativeConormalBaseChangeMap B M B' I u :=
  rfl

/-- **`h¹/h⁰` of the relative conormal complex is invariant under flat base change.** Over every
test algebra `Bb`, the fibre of `h¹/h⁰` of the dual of `relativeConormalComplex B' M' I'` is
equivalent to the fibre of `h¹/h⁰` of the dual of `relativeConormalComplex B M I`. This is
`relativeNormalSheafBaseChangeEquiv` transported through
`relativeIntrinsicNormalSheafEquiv`/`normalSheafQuotientEquivDualPoints`, and is the form in which
the base-change compatibility is consumed by the Picard-groupoid criteria of
`Cones/PicardBaseChange.lean`. -/
noncomputable def relativeDualPointsBaseChangeEquiv (Bb : Type u) [CommRing Bb]
    [Algebra (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) Bb] [Algebra (M ⧸ I) Bb]
    [IsScalarTower (M ⧸ I) (baseChangeAmbient B M B' ⧸ baseChangeIdeal B M B' I) Bb] :
    (PicardCriteria.dualPoints (relativeConormalComplex B' (baseChangeAmbient B M B')
        (baseChangeIdeal B M B' I)) Bb).quotient ≌
      (PicardCriteria.dualPoints (relativeConormalComplex B M I) Bb).quotient :=
  (PicardCriteria.dualQuotientEquivalence Bb
      (relativeConormalComplexBaseChange B M B' I)).trans
    (PicardCriteria.dualPointsBaseChangeEquiv (relativeConormalComplex B M I) Bb)

end Assembly

end GromovWitten.AlgebraicGeometry
