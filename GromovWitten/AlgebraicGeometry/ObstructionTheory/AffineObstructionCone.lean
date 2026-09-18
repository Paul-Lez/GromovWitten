/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.ObstructionTheory.AffineCriterion
import GromovWitten.AlgebraicGeometry.ObstructionTheory.Perfect
import GromovWitten.AlgebraicGeometry.Cones.NormalSheafPicard
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Obstruction cones, perfectness, sums and base change in the affine two-term model

`ObstructionTheory/AffineCriterion.lean` proves the Behrend–Fantechi criterion
(`PicardCriteria.isObstructionTheory_iff_forall_isCohomologicalMono`) for a chain map
`φ : E ⟶ L` of two-term complexes, and attaches to an abstract cone `ι` inside `h¹/h⁰(Lᵛ)(B)`
its image `PicardCriteria.obstructionConeFunctor φ B ι` in `h¹/h⁰(Eᵛ)(B)`.  This file
instantiates that abstract cone with the honest affine cone quotients of `Cones/Quotient.lean`,
compares the two-term notion of an obstruction theory with the derived-category definition of
`ObstructionTheory/Basic.lean`, and proves the stability of the notion under direct sums and
arbitrary base change.

## The obstruction cone

`PicardCriteria.obstructionCone φ h B` is the composite

`[C/T](B) ⟶ [N/T](B) ≅ h¹/h⁰([N → F]ᵛ)(B) ⟶ h¹/h⁰(Eᵛ)(B)`

of the functor induced by an equivariant closed immersion `C ↪ N` of cones acted on by the same
vector bundle `T = Spec Sym F` (`ConeQuotient.quotientFunctor`), the strict comparison
`NormalSheafPicard.bundleQuotientEquivDualPoints` of the quotient groupoid of a bundle
translation action with the Picard groupoid of the complex of `B`-points of the dual, and the
closed immersion of cone stacks attached to the obstruction theory `φ`.  In the intended
application `N = N_{U/M}` is the affine normal sheaf of an ideal `I ⊆ R`, `T = T_M|_U`, and
`[N/T]` is the affine intrinsic normal sheaf
`NormalSheafPicard.AffineIntrinsicNormalSheaf.normalSheafQuotientEquivDualPoints`, identified
with `h¹/h⁰(L^∨)` for the presentation cotangent complex by
`NormalSheafPicard.AffineIntrinsicNormalSheaf.normalSheafQuotientEquivPresentation`; `C` is the
affine normal cone `C_{U/M}` with the tangent translation action of `Cones/ConeTranslation.lean`.

"The obstruction cone is a *closed* subcone-stack of `h¹/h⁰(Eᵛ)`" means, fibrewise over every
affine test scheme `Spec B`, that the functor is fully faithful and injective on isomorphism
classes: no arrows and no isomorphism classes are created or collapsed.  This is
`PicardCriteria.obstructionConeFullyFaithful` and
`PicardCriteria.obstructionCone_injective_isoClass`.

## Main results

* `PicardCriteria.quotientFunctorFullyFaithfulOfSurjective`: an equivariant *closed immersion*
  of cones with the same acting bundle (that is, a surjective map of coordinate rings) induces a
  fully faithful functor of quotient groupoids.
* `PicardCriteria.obstructionCone`, `obstructionConeFullyFaithful`,
  `obstructionCone_injective_isoClass`, `obstructionCone_naturality`,
  `obstructionCone_comp_homotopyEquivalence`: the obstruction cone and its properties.
* `PicardCriteria.normalSheafObstructionCone`,
  `PicardCriteria.affineNormalSheafObstructionCone` and
  `PicardCriteria.presentationObstructionCone`: the unconditional instantiations with the whole
  normal sheaf `[N/T]`, with the affine intrinsic normal sheaf of `I ⊆ R`, and with an
  obstruction theory on the two-term cotangent complex of the presentation `R → R/I`.
* `PicardCriteria.isIso_homologyMap_zero_iff`,
  `PicardCriteria.epi_homologyMap_negOne_iff`,
  `PicardCriteria.isObstructionTheory_iff_derived` and
  `PicardCriteria.derivedObstructionTheory`: the comparison with
  `DerivedObstructionTheory.ObstructionTheory`.  The cohomology of `E.toCochainComplex` in
  degrees `-1` and `0` is identified with `PicardCriteria.h0` and `PicardCriteria.h1` by an
  explicit `ShortComplex.LeftHomologyMapData`, so that `H⁰(φ)` iso and `H⁻¹(φ)` epi in the
  derived category are literally `φ.cokernelMap` bijective and `φ.kernelMap` surjective.
* `PicardCriteria.IsPerfectTwoTerm`, `PicardCriteria.isFiniteFreeComplex_dualPoints`,
  `PicardCriteria.virtualRank_dualPoints`: in the two-term model perfectness is finite freeness
  of the two terms, and it implies that every fibre `h¹/h⁰(Eᵛ)(B)` is the Picard groupoid of a
  two-term complex of finite free `B`-modules, that is, a vector-bundle stack, of rank
  `-virtualRank E`.
* `LinearTwoTermComplex.sum`, `PicardCriteria.isObstructionTheory_sum_iff`: the external direct
  sum of two obstruction theories is an obstruction theory, and conversely.
* `LinearTwoTermComplex.baseChange`, `PicardCriteria.IsObstructionTheory.baseChange`: the base
  change of an obstruction theory along *any* `R`-algebra `R'` is an obstruction theory.  No
  flatness is needed: `PicardCriteria.isObstructionTheory_iff_exact_cone` shows that being an
  obstruction theory is exactly right exactness of the mapping-cone sequence
  `E⁻¹ → L⁻¹ ⊕ E⁰ → L⁰ → 0`, which is preserved by every tensor product.
* `CotangentComplex.PerfectComplex.GlobalTwoTermResolution.sum` and
  `CotangentComplex.PerfectComplex.nonempty_globalTwoTermResolution_biprod`: having a global
  two-term resolution by finite free modules is stable under biproducts in the derived category.

## What is not done here

The tangent translation action on the affine normal cone of `Cones/ConeTranslation.lean` is
built in the polynomial model, as a coaction `gr_I(R) →ₐ MvPolynomial σ (gr_I(R))`, and is not
packaged as a `ConeQuotient.ConeAction`; consequently the obstruction cone of the *normal cone*
(as opposed to the normal sheaf) is available here only after such a packaging, through the
hypotheses of `PicardCriteria.obstructionCone`, which are stated for an arbitrary cone with an
equivariant closed immersion into the normal sheaf.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

namespace PicardCriteria

universe u v

open LinearTwoTermComplex

/-! ## Closed immersions of cone quotients -/

section ConeImmersion

open ConeQuotient

variable {R S S' F : Type u} [CommRing R] [CommRing S] [Algebra R S] [CommRing S']
  [Algebra R S'] [AddCommGroup F] [Module R F] {Ac : ConeAction R S F}
  {Ac' : ConeAction R S' F} {ψ : S →ₐ[R] S'}

/-- **A closed immersion of cones induces a fully faithful functor of quotient groupoids.**

If `ψ : S →ₐ[R] S'` is a surjective map of coordinate rings — that is, `Spec S' → Spec S` is a
closed immersion — which is equivariant for actions of the *same* vector bundle
`Spec Sym F` on both cones, then over every test algebra `B` the induced functor
`[Spec S'/Spec Sym F](B) ⥤ [Spec S/Spec Sym F](B)` is fully faithful.  Faithfulness holds
because an arrow of either quotient groupoid *is* its translating `B`-point of the bundle;
fullness holds because `ψ` is surjective, so two `B`-points of `Spec S'` that become equal after
composing with `ψ` are equal. -/
noncomputable def quotientFunctorFullyFaithfulOfSurjective
    (h : IsEquivariant Ac Ac' ψ LinearMap.id) (hψ : Function.Surjective ψ)
    (B : Type u) [CommRing B] [Algebra R B] :
    (quotientFunctor h B).FullyFaithful where
  preimage {x y} f :=
    { val := f.val
      translate_eq := by
        have hcomp := translate_comp h x.point f.val
        rw [LinearMap.comp_id] at hcomp
        refine AlgHom.ext fun s => ?_
        obtain ⟨t, rfl⟩ := hψ s
        exact congrArg (fun z : S →ₐ[R] B => z t) (hcomp.trans f.translate_eq) }
  map_preimage _ := QuotientGroupoid.Hom.ext (LinearMap.comp_id _)
  preimage_map _ := QuotientGroupoid.Hom.ext (LinearMap.comp_id _)

end ConeImmersion

/-! ## The obstruction cone -/

section ObstructionCone

open ConeQuotient NormalSheafPicard

variable {A N F S : Type u} [CommRing A] [AddCommGroup N] [Module A N] [AddCommGroup F]
  [Module A F] [CommRing S] [Algebra A S] {d : N →ₗ[A] F} {Ac : ConeAction A S F}
  {ψ : SymmetricAlgebra A N →ₐ[A] S} {E : LinearTwoTermComplex A}

/-- **A closed subcone of the normal sheaf, read inside `h¹/h⁰([N → F]ᵛ)`.**

An equivariant morphism from the cone `Spec S` with its action of `Spec Sym F` to the bundle
`Spec Sym N` with the translation action along `d : N →ₗ[A] F` gives, over every test algebra
`B`, a functor from `[Spec S/Spec Sym F](B)` to the fibre of `h¹/h⁰` of the dual of
`[N → F]`. -/
noncomputable def coneToDualPoints (h : IsEquivariant (bundleTranslationAction d) Ac ψ
    LinearMap.id) (B : Type u) [CommRing B] [Algebra A B] :
    QuotientGroupoid Ac B ⥤ (dualPoints (dualComplexOf d) B).quotient :=
  quotientFunctor h B ⋙ toDualPoints d B

/-- The comparison of a closed subcone with `h¹/h⁰` of the dual is fully faithful. -/
noncomputable def coneToDualPointsFullyFaithful
    (h : IsEquivariant (bundleTranslationAction d) Ac ψ LinearMap.id)
    (hψ : Function.Surjective ψ) (B : Type u) [CommRing B] [Algebra A B] :
    (coneToDualPoints h B).FullyFaithful :=
  (quotientFunctorFullyFaithfulOfSurjective h hψ B).comp
    (bundleQuotientEquivDualPoints d B).fullyFaithfulFunctor

/-- **The obstruction cone of a closed subcone of the normal sheaf.**

Given an obstruction theory `φ : E ⟶ [N → F]` in the two-term model and an equivariant closed
immersion of a cone `Spec S` into the normal sheaf `Spec Sym N`, this is the composite functor

`[Spec S/Spec Sym F](B) ⟶ h¹/h⁰([N → F]ᵛ)(B) ⟶ h¹/h⁰(Eᵛ)(B)`.

In the intended application the source is the affine intrinsic normal cone and the target is
the vector-bundle stack `h¹/h⁰(Eᵛ)` of the obstruction theory. -/
noncomputable def obstructionCone (φ : Hom E (dualComplexOf d))
    (h : IsEquivariant (bundleTranslationAction d) Ac ψ LinearMap.id)
    (B : Type u) [CommRing B] [Algebra A B] :
    QuotientGroupoid Ac B ⥤ (dualPoints E B).quotient :=
  obstructionConeFunctor φ B (coneToDualPoints h B)

/-- The obstruction cone is the composite of the comparison with `h¹/h⁰` of the dual and the
closed immersion of cone stacks attached to `φ`. -/
theorem obstructionCone_eq (φ : Hom E (dualComplexOf d))
    (h : IsEquivariant (bundleTranslationAction d) Ac ψ LinearMap.id)
    (B : Type u) [CommRing B] [Algebra A B] :
    obstructionCone φ h B = coneToDualPoints h B ⋙ (dualHom φ B).quotientFunctor :=
  rfl

/-- **The obstruction cone is a closed immersion, first half: it is fully faithful.**

Over every test algebra the obstruction cone neither creates nor collapses arrows; in
particular it is injective on the automorphism groups, which are the stabilisers of the cone
action. -/
noncomputable def obstructionConeFullyFaithful {φ : Hom E (dualComplexOf d)}
    (hφ : IsObstructionTheory φ) (h : IsEquivariant (bundleTranslationAction d) Ac ψ
      LinearMap.id) (hψ : Function.Surjective ψ) (B : Type u) [CommRing B] [Algebra A B] :
    (obstructionCone φ h B).FullyFaithful :=
  obstructionConeFunctorFullyFaithful hφ B (coneToDualPointsFullyFaithful h hψ B)

/-- **The obstruction cone is a closed immersion, second half: it is injective on isomorphism
classes.**  Two `B`-points of the cone with isomorphic images in `h¹/h⁰(Eᵛ)(B)` are already
isomorphic in the cone quotient. -/
theorem obstructionCone_injective_isoClass {φ : Hom E (dualComplexOf d)}
    (hφ : IsObstructionTheory φ)
    (h : IsEquivariant (bundleTranslationAction d) Ac ψ LinearMap.id)
    (hψ : Function.Surjective ψ) (B : Type u) [CommRing B] [Algebra A B]
    {c c' : QuotientGroupoid Ac B}
    (hiso : Nonempty ((obstructionCone φ h B).obj c ≅ (obstructionCone φ h B).obj c')) :
    Nonempty (c ≅ c') :=
  obstructionConeFunctor_injective_isoClass hφ B (coneToDualPointsFullyFaithful h hψ B) hiso

/-- **The obstruction cone is natural in the test algebra.**  Reindexing the cone quotient along
`g : B →ₐ[A] B'` and then taking the obstruction cone is the same as taking the obstruction cone
and then reindexing the fibre of `h¹/h⁰(Eᵛ)`; so the obstruction cones assemble into a morphism
of prestacks on the affine objects of the big site. -/
theorem obstructionCone_naturality (φ : Hom E (dualComplexOf d))
    (h : IsEquivariant (bundleTranslationAction d) Ac ψ LinearMap.id)
    (B B' : Type u) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B']
    (g : B →ₐ[A] B') :
    obstructionCone φ h B ⋙ dualPointsMap E B B' g =
      QuotientGroupoid.mapQuotient Ac g ⋙ obstructionCone φ h B' :=
  calc obstructionCone φ h B ⋙ dualPointsMap E B B' g
      = quotientFunctor h B ⋙ (toDualPoints d B ⋙
        ((dualHom φ B).quotientFunctor ⋙ dualPointsMap E B B' g)) := rfl
    _ = quotientFunctor h B ⋙ (toDualPoints d B ⋙
        (dualPointsMap (dualComplexOf d) B B' g ⋙ (dualHom φ B').quotientFunctor)) := by
      rw [dualHom_quotientFunctor_naturality]
    _ = quotientFunctor h B ⋙ ((toDualPoints d B ⋙ dualPointsMap (dualComplexOf d) B B' g) ⋙
        (dualHom φ B').quotientFunctor) := rfl
    _ = quotientFunctor h B ⋙ ((QuotientGroupoid.mapQuotient (bundleTranslationAction d) g ⋙
        toDualPoints d B') ⋙ (dualHom φ B').quotientFunctor) := by
      rw [← toDualPoints_naturality]
    _ = (quotientFunctor h B ⋙ QuotientGroupoid.mapQuotient (bundleTranslationAction d) g) ⋙
        (toDualPoints d B' ⋙ (dualHom φ B').quotientFunctor) := rfl
    _ = (QuotientGroupoid.mapQuotient Ac g ⋙ quotientFunctor h B') ⋙
        (toDualPoints d B' ⋙ (dualHom φ B').quotientFunctor) := by
      rw [quotientFunctor_comp_mapQuotient]
    _ = QuotientGroupoid.mapQuotient Ac g ⋙ obstructionCone φ h B' := rfl

/-- **Invariance of the obstruction cone under homotopy equivalence of the source.**  Replacing
`E` by a chain homotopy equivalent complex `E'` changes the obstruction cone by the equivalence
`PicardCriteria.dualQuotientEquivalence` of the fibres, so the obstruction cone is an invariant
of the homotopy class of the obstruction theory. -/
theorem obstructionCone_comp_homotopyEquivalence {E' : LinearTwoTermComplex A}
    (φ : Hom E (dualComplexOf d)) (e : HomotopyEquivalence E' E)
    (h : IsEquivariant (bundleTranslationAction d) Ac ψ LinearMap.id)
    (B : Type u) [CommRing B] [Algebra A B] :
    obstructionCone (φ.comp e.hom) h B =
      obstructionCone φ h B ⋙ (dualQuotientEquivalence B e).functor :=
  rfl

/-! ### The whole normal sheaf as its own obstruction cone -/

/-- **The obstruction cone of the full normal sheaf.**  Taking the closed immersion to be the
identity of `Spec Sym N` gives, unconditionally, the morphism of cone stacks
`[N/T](B) ⟶ h¹/h⁰(Eᵛ)(B)` attached to an obstruction theory `φ : E ⟶ [N → F]`. -/
noncomputable def normalSheafObstructionCone (φ : Hom E (dualComplexOf d)) (B : Type u)
    [CommRing B] [Algebra A B] :
    QuotientGroupoid (bundleTranslationAction d) B ⥤ (dualPoints E B).quotient :=
  obstructionCone φ (isEquivariant_id (bundleTranslationAction d)) B

/-- The obstruction cone of the full normal sheaf is fully faithful. -/
noncomputable def normalSheafObstructionConeFullyFaithful {φ : Hom E (dualComplexOf d)}
    (hφ : IsObstructionTheory φ) (B : Type u) [CommRing B] [Algebra A B] :
    (normalSheafObstructionCone φ B).FullyFaithful :=
  obstructionConeFullyFaithful hφ _ (fun s => ⟨s, rfl⟩) B

/-- The obstruction cone of the full normal sheaf is injective on isomorphism classes. -/
theorem normalSheafObstructionCone_injective_isoClass {φ : Hom E (dualComplexOf d)}
    (hφ : IsObstructionTheory φ) (B : Type u) [CommRing B] [Algebra A B]
    {c c' : QuotientGroupoid (bundleTranslationAction d) B}
    (hiso : Nonempty ((normalSheafObstructionCone φ B).obj c
      ≅ (normalSheafObstructionCone φ B).obj c')) :
    Nonempty (c ≅ c') :=
  obstructionCone_injective_isoClass hφ _ (fun s => ⟨s, rfl⟩) B hiso

end ObstructionCone

/-! ### The affine intrinsic normal sheaf -/

/-! ### Reversing a chain homotopy equivalence -/

section Symm

variable {R : Type u} [CommRing R] {E F : LinearTwoTermComplex R}

/-- A chain homotopy can be reversed: the reverse homotopy is the negative of the given one. -/
def chainHomotopySymm {f g : Hom E F} (H : ChainHomotopy f g) : ChainHomotopy g f where
  homotopy := -H.homotopy
  degreeZero x := by
    rw [LinearMap.neg_apply, H.degreeZero x]
    abel
  degreeOne x := by
    rw [LinearMap.neg_apply, map_neg, H.degreeOne x]
    abel

/-- A chain homotopy equivalence can be reversed. -/
def homotopyEquivalenceSymm (e : HomotopyEquivalence E F) : HomotopyEquivalence F E where
  hom := e.inv
  inv := e.hom
  unit := chainHomotopySymm e.counit
  counit := chainHomotopySymm e.unit

end Symm

section AffineIntrinsic

open ConeQuotient NormalSheafPicard NormalSheafPicard.AffineIntrinsicNormalSheaf

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] (I : Ideal R)
  {E : LinearTwoTermComplex (R ⧸ I)}

/-- **The obstruction cone of the affine intrinsic normal sheaf.**  For an obstruction theory
`φ : E ⟶ [I/I² → (R/I) ⊗ Ω[R⁄k]]` this is the morphism of cone stacks

`[N_{U/M}/T_M|_U](B) ⟶ h¹/h⁰(Eᵛ)(B)`

over every test algebra `B`.  Through
`NormalSheafPicard.AffineIntrinsicNormalSheaf.normalSheafQuotientEquivPresentation` its source
is the fibre of `h¹/h⁰(L^∨)` for the two-term cotangent complex of the presentation
`R → R/I`. -/
noncomputable def affineNormalSheafObstructionCone (φ : Hom E (conormalComplex k R I))
    (B : Type u) [CommRing B] [Algebra (R ⧸ I) B] :
    QuotientGroupoid (AffineNormalCone.normalSheafTangentAction k R I) B ⥤
      (dualPoints E B).quotient :=
  normalSheafObstructionCone φ B

/-- The obstruction cone of the affine intrinsic normal sheaf is fully faithful: it is a closed
immersion of cone stacks fibrewise. -/
noncomputable def affineNormalSheafObstructionConeFullyFaithful
    {φ : Hom E (conormalComplex k R I)} (hφ : IsObstructionTheory φ) (B : Type u) [CommRing B]
    [Algebra (R ⧸ I) B] : (affineNormalSheafObstructionCone k R I φ B).FullyFaithful :=
  normalSheafObstructionConeFullyFaithful hφ B

/-- The obstruction cone of the affine intrinsic normal sheaf is injective on isomorphism
classes. -/
theorem affineNormalSheafObstructionCone_injective_isoClass
    {φ : Hom E (conormalComplex k R I)} (hφ : IsObstructionTheory φ) (B : Type u) [CommRing B]
    [Algebra (R ⧸ I) B]
    {c c' : QuotientGroupoid (AffineNormalCone.normalSheafTangentAction k R I) B}
    (hiso : Nonempty ((affineNormalSheafObstructionCone k R I φ B).obj c
      ≅ (affineNormalSheafObstructionCone k R I φ B).obj c')) :
    Nonempty (c ≅ c') :=
  normalSheafObstructionCone_injective_isoClass hφ B hiso

/-! #### The presentation cotangent complex -/

/-- The obstruction theory on the conormal complex attached to one on the two-term cotangent
complex of the presentation `R → R/I`, through the chain homotopy equivalence
`NormalSheafPicard.AffineIntrinsicNormalSheaf.conormalHomotopyEquivalence`. -/
noncomputable def ofPresentation
    (φ : Hom E (CotangentComplex.AffinePresentation.twoTerm k (R ⧸ I)
      (quotientExtension k R I))) : Hom E (conormalComplex k R I) :=
  (homotopyEquivalenceSymm (conormalHomotopyEquivalence k R I)).hom.comp φ

/-- An obstruction theory on the presentation complex is an obstruction theory on the conormal
complex. -/
theorem isObstructionTheory_ofPresentation
    {φ : Hom E (CotangentComplex.AffinePresentation.twoTerm k (R ⧸ I)
      (quotientExtension k R I))} (hφ : IsObstructionTheory φ) :
    IsObstructionTheory (ofPresentation k R I φ) :=
  hφ.comp_homotopyEquivalence (homotopyEquivalenceSymm (conormalHomotopyEquivalence k R I))

/-- **The obstruction cone of an obstruction theory on the presentation cotangent complex.**

For `φ : E ⟶ L` with `L` the two-term cotangent complex of the presentation `R → R/I`, whose
`h¹/h⁰(L^∨)` is the affine intrinsic normal sheaf by
`NormalSheafPicard.AffineIntrinsicNormalSheaf.normalSheafQuotientEquivPresentation`, this is the
morphism of cone stacks `[N_{U/M}/T_M|_U](B) ⟶ h¹/h⁰(Eᵛ)(B)`. -/
noncomputable def presentationObstructionCone
    (φ : Hom E (CotangentComplex.AffinePresentation.twoTerm k (R ⧸ I)
      (quotientExtension k R I))) (B : Type u) [CommRing B] [Algebra (R ⧸ I) B] :
    QuotientGroupoid (AffineNormalCone.normalSheafTangentAction k R I) B ⥤
      (dualPoints E B).quotient :=
  affineNormalSheafObstructionCone k R I (ofPresentation k R I φ) B

/-- The obstruction cone of an obstruction theory on the presentation complex is fully
faithful. -/
noncomputable def presentationObstructionConeFullyFaithful
    {φ : Hom E (CotangentComplex.AffinePresentation.twoTerm k (R ⧸ I)
      (quotientExtension k R I))} (hφ : IsObstructionTheory φ) (B : Type u) [CommRing B]
    [Algebra (R ⧸ I) B] : (presentationObstructionCone k R I φ B).FullyFaithful :=
  affineNormalSheafObstructionConeFullyFaithful k R I
    (isObstructionTheory_ofPresentation k R I hφ) B

/-- The obstruction cone of an obstruction theory on the presentation complex is injective on
isomorphism classes. -/
theorem presentationObstructionCone_injective_isoClass
    {φ : Hom E (CotangentComplex.AffinePresentation.twoTerm k (R ⧸ I)
      (quotientExtension k R I))} (hφ : IsObstructionTheory φ) (B : Type u) [CommRing B]
    [Algebra (R ⧸ I) B]
    {c c' : QuotientGroupoid (AffineNormalCone.normalSheafTangentAction k R I) B}
    (hiso : Nonempty ((presentationObstructionCone k R I φ B).obj c
      ≅ (presentationObstructionCone k R I φ B).obj c')) :
    Nonempty (c ≅ c') :=
  affineNormalSheafObstructionCone_injective_isoClass k R I
    (isObstructionTheory_ofPresentation k R I hφ) B hiso

end AffineIntrinsic

/-! ## Comparison with the derived-category definition -/

section Derived

open CategoryTheory.Limits

variable {R : Type u} [CommRing R] {E L : LinearTwoTermComplex R}

/-- Transport of invertibility across a commuting square with invertible vertical maps. -/
theorem isIso_iff_of_square {C : Type*} [Category C] {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (a : X ≅ X') (b : Y ≅ Y') (h : f ≫ b.hom = a.hom ≫ f') : IsIso f ↔ IsIso f' := by
  constructor
  · intro hf
    have hf' : f' = a.inv ≫ f ≫ b.hom := by
      rw [h, ← Category.assoc, a.inv_hom_id, Category.id_comp]
    rw [hf']
    infer_instance
  · intro hf
    have hff : f = (a.hom ≫ f') ≫ b.inv := by
      rw [← h, Category.assoc, b.hom_inv_id, Category.comp_id]
    rw [hff]
    infer_instance

/-- Transport of epimorphy across a commuting square with invertible vertical maps. -/
theorem epi_iff_of_square {C : Type*} [Category C] {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (a : X ≅ X') (b : Y ≅ Y') (h : f ≫ b.hom = a.hom ≫ f') : Epi f ↔ Epi f' := by
  constructor
  · intro hf
    have hf' : f' = a.inv ≫ f ≫ b.hom := by
      rw [h, ← Category.assoc, a.inv_hom_id, Category.id_comp]
    rw [hf']
    infer_instance
  · intro hf
    have hff : f = (a.hom ≫ f') ≫ b.inv := by
      rw [← h, Category.assoc, b.hom_inv_id, Category.comp_id]
    rw [hff]
    infer_instance

/-! ### The cochain map attached to a chain map of two-term complexes -/

/-- The degree-`i` component of the cochain map realising a chain map of two-term complexes:
`φ⁻¹` in degree `-1`, `φ⁰` in degree `0` and zero in every other degree. -/
noncomputable def cochainMap (φ : Hom E L) (i : ℤ) :
    E.toCochainComplex.X i ⟶ L.toCochainComplex.X i := by
  by_cases h1 : i = -1
  · subst h1
    exact ModuleCat.ofHom φ.degreeZero
  · by_cases h0 : i = 0
    · subst h0
      exact ModuleCat.ofHom φ.degreeOne
    · exact 0

@[simp]
theorem cochainMap_negOne (φ : Hom E L) :
    cochainMap φ (-1) = ModuleCat.ofHom φ.degreeZero :=
  rfl

@[simp]
theorem cochainMap_zero (φ : Hom E L) :
    cochainMap φ 0 = ModuleCat.ofHom φ.degreeOne :=
  rfl

/-- **The cochain realisation of a chain map of two-term complexes.** -/
noncomputable def toCochainComplexHom (φ : Hom E L) :
    E.toCochainComplex ⟶ L.toCochainComplex where
  f := cochainMap φ
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases h1 : i = -1
    · subst h1
      obtain rfl : j = 0 := by omega
      simp only [cochainMap_negOne, cochainMap_zero, toCochainComplex_d_negOne_zero]
      exact ModuleCat.hom_ext (LinearMap.ext fun x => (φ.comm x).symm)
    · by_cases h0 : i = 0
      · subst h0
        obtain rfl : j = 1 := by omega
        rw [(L.toCochainComplex_X_isZero 1 (by norm_num) (by norm_num)).eq_of_tgt
            (L.toCochainComplex.d 0 1) 0,
          (E.toCochainComplex_X_isZero 1 (by norm_num) (by norm_num)).eq_of_tgt
            (E.toCochainComplex.d 0 1) 0, comp_zero, zero_comp]
      · rw [(E.toCochainComplex_X_isZero i h1 h0).eq_of_src (cochainMap φ i) 0,
          (E.toCochainComplex_X_isZero i h1 h0).eq_of_src (E.toCochainComplex.d i j) 0,
          zero_comp, zero_comp]

@[simp]
theorem toCochainComplexHom_f (φ : Hom E L) (i : ℤ) :
    (toCochainComplexHom φ).f i = cochainMap φ i :=
  rfl

/-! ### Identification of the cohomology in degrees `-1` and `0` -/

/-- In the short complex computing degree-`0` cohomology the second map vanishes: the complex
has nothing in degree `1`. -/
theorem sc'_zero_g (E : LinearTwoTermComplex R) : (E.toCochainComplex.sc' (-1) 0 1).g = 0 :=
  (E.toCochainComplex_X_isZero 1 (by norm_num) (by norm_num)).eq_of_tgt _ _

/-- In the short complex computing degree-`-1` cohomology the first map vanishes: the complex
has nothing in degree `-2`. -/
theorem sc'_negOne_f (E : LinearTwoTermComplex R) :
    (E.toCochainComplex.sc' (-2) (-1) 0).f = 0 :=
  (E.toCochainComplex_X_isZero (-2) (by norm_num) (by norm_num)).eq_of_src _ _

/-- The explicit left homology data computing degree-`0` cohomology as the cokernel `h¹(E)` of
the differential. -/
noncomputable def leftHomologyDataZero (E : LinearTwoTermComplex R) :
    (E.toCochainComplex.sc' (-1) 0 1).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork _ (sc'_zero_g E)
    (ModuleCat.cokernelCocone _) (ModuleCat.cokernelIsColimit _)

/-- The explicit left homology data computing degree-`-1` cohomology as the kernel `h⁰(E)` of
the differential. -/
noncomputable def leftHomologyDataNegOne (E : LinearTwoTermComplex R) :
    (E.toCochainComplex.sc' (-2) (-1) 0).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofIsLimitKernelFork _ (sc'_negOne_f E)
    (ModuleCat.kernelCone _) (ModuleCat.kernelIsLimit _)

/-- The map on degree-`0` cohomology induced by a chain map is `H⁰(φ) = φ.cokernelMap`. -/
noncomputable def leftHomologyMapDataZero (φ : Hom E L) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℤ)
        (-1) 0 1).map (toCochainComplexHom φ)) (leftHomologyDataZero E) (leftHomologyDataZero L) :=
  ShortComplex.LeftHomologyMapData.ofIsColimitCokernelCofork _ (sc'_zero_g E) _
    (ModuleCat.cokernelIsColimit _) (sc'_zero_g L) _ (ModuleCat.cokernelIsColimit _)
    (ModuleCat.ofHom φ.cokernelMap) (ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- The map on degree-`-1` cohomology induced by a chain map is `H⁻¹(φ) = φ.kernelMap`. -/
noncomputable def leftHomologyMapDataNegOne (φ : Hom E L) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℤ)
        (-2) (-1) 0).map (toCochainComplexHom φ)) (leftHomologyDataNegOne E)
      (leftHomologyDataNegOne L) :=
  ShortComplex.LeftHomologyMapData.ofIsLimitKernelFork _ (sc'_negOne_f E) _
    (ModuleCat.kernelIsLimit _) (sc'_negOne_f L) _ (ModuleCat.kernelIsLimit _)
    (ModuleCat.ofHom φ.kernelMap) (ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- The comparison of degree-`0` cohomology with the homology of the short complex in the
explicit degrees `(-1, 0, 1)`. -/
noncomputable def scIsoZero (E : LinearTwoTermComplex R) :
    E.toCochainComplex.homology 0 ≅ (E.toCochainComplex.sc' (-1) 0 1).homology :=
  (HomologicalComplex.homologyFunctorIso' (ModuleCat.{u} R) (ComplexShape.up ℤ) (-1) 0 1
    ((ComplexShape.up ℤ).prev_eq' (by norm_num))
    ((ComplexShape.up ℤ).next_eq' (by norm_num))).app E.toCochainComplex

/-- The comparison of degree-`-1` cohomology with the homology of the short complex in the
explicit degrees `(-2, -1, 0)`. -/
noncomputable def scIsoNegOne (E : LinearTwoTermComplex R) :
    E.toCochainComplex.homology (-1) ≅ (E.toCochainComplex.sc' (-2) (-1) 0).homology :=
  (HomologicalComplex.homologyFunctorIso' (ModuleCat.{u} R) (ComplexShape.up ℤ) (-2) (-1) 0
    ((ComplexShape.up ℤ).prev_eq' (by norm_num))
    ((ComplexShape.up ℤ).next_eq' (by norm_num))).app E.toCochainComplex

/-- Naturality of the degree-`0` comparison with the short complex. -/
theorem scIsoZero_naturality (φ : Hom E L) :
    HomologicalComplex.homologyMap (toCochainComplexHom φ) 0 ≫ (scIsoZero L).hom =
      (scIsoZero E).hom ≫ ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℤ)
          (-1) 0 1).map (toCochainComplexHom φ)) :=
  (HomologicalComplex.homologyFunctorIso' (ModuleCat.{u} R) (ComplexShape.up ℤ) (-1) 0 1
    ((ComplexShape.up ℤ).prev_eq' (by norm_num))
    ((ComplexShape.up ℤ).next_eq' (by norm_num))).hom.naturality (toCochainComplexHom φ)

/-- Naturality of the degree-`-1` comparison with the short complex. -/
theorem scIsoNegOne_naturality (φ : Hom E L) :
    HomologicalComplex.homologyMap (toCochainComplexHom φ) (-1) ≫ (scIsoNegOne L).hom =
      (scIsoNegOne E).hom ≫ ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℤ)
          (-2) (-1) 0).map (toCochainComplexHom φ)) :=
  (HomologicalComplex.homologyFunctorIso' (ModuleCat.{u} R) (ComplexShape.up ℤ) (-2) (-1) 0
    ((ComplexShape.up ℤ).prev_eq' (by norm_num))
    ((ComplexShape.up ℤ).next_eq' (by norm_num))).hom.naturality (toCochainComplexHom φ)

/-- **Degree-`0` cohomology of the cochain realisation is `h¹`.** -/
noncomputable def homologyIsoZero (E : LinearTwoTermComplex R) :
    E.toCochainComplex.homology 0 ≅ ModuleCat.of R (h1 E) :=
  scIsoZero E ≪≫ (leftHomologyDataZero E).homologyIso

/-- **Degree-`-1` cohomology of the cochain realisation is `h⁰`.** -/
noncomputable def homologyIsoNegOne (E : LinearTwoTermComplex R) :
    E.toCochainComplex.homology (-1) ≅ ModuleCat.of R (h0 E) :=
  scIsoNegOne E ≪≫ (leftHomologyDataNegOne E).homologyIso

/-- The degree-`0` comparison isomorphism, unfolded as a composite. -/
theorem homologyIsoZero_hom (E : LinearTwoTermComplex R) :
    (homologyIsoZero E).hom = (scIsoZero E).hom ≫ (leftHomologyDataZero E).homologyIso.hom :=
  rfl

/-- The degree-`-1` comparison isomorphism, unfolded as a composite. -/
theorem homologyIsoNegOne_hom (E : LinearTwoTermComplex R) :
    (homologyIsoNegOne E).hom =
      (scIsoNegOne E).hom ≫ (leftHomologyDataNegOne E).homologyIso.hom :=
  rfl

/-- The identification of degree-`0` cohomology with `h¹` is compatible with chain maps. -/
theorem homologyMap_zero_comm (φ : Hom E L) :
    HomologicalComplex.homologyMap (toCochainComplexHom φ) 0 ≫ (homologyIsoZero L).hom =
      (homologyIsoZero E).hom ≫ ModuleCat.ofHom φ.cokernelMap := by
  have key : HomologicalComplex.homologyMap (toCochainComplexHom φ) 0 ≫
      (scIsoZero L).hom ≫ (leftHomologyDataZero L).homologyIso.hom =
      ((scIsoZero E).hom ≫ (leftHomologyDataZero E).homologyIso.hom) ≫
        (leftHomologyMapDataZero φ).φH := by
    rw [← Category.assoc, scIsoZero_naturality, Category.assoc,
      (leftHomologyMapDataZero φ).homologyMap_comm, ← Category.assoc]
  exact key

/-- The identification of degree-`-1` cohomology with `h⁰` is compatible with chain maps. -/
theorem homologyMap_negOne_comm (φ : Hom E L) :
    HomologicalComplex.homologyMap (toCochainComplexHom φ) (-1) ≫ (homologyIsoNegOne L).hom =
      (homologyIsoNegOne E).hom ≫ ModuleCat.ofHom φ.kernelMap := by
  have key : HomologicalComplex.homologyMap (toCochainComplexHom φ) (-1) ≫
      (scIsoNegOne L).hom ≫ (leftHomologyDataNegOne L).homologyIso.hom =
      ((scIsoNegOne E).hom ≫ (leftHomologyDataNegOne E).homologyIso.hom) ≫
        (leftHomologyMapDataNegOne φ).φH := by
    rw [← Category.assoc, scIsoNegOne_naturality, Category.assoc,
      (leftHomologyMapDataNegOne φ).homologyMap_comm, ← Category.assoc]
  exact key

/-- **`H⁰` of the cochain realisation is an isomorphism exactly when `φ.cokernelMap` is
bijective.** -/
theorem isIso_homologyMap_zero_iff (φ : Hom E L) :
    IsIso (HomologicalComplex.homologyMap (toCochainComplexHom φ) 0) ↔
      Function.Bijective φ.cokernelMap := by
  rw [isIso_iff_of_square (homologyIsoZero E) (homologyIsoZero L) (homologyMap_zero_comm φ),
    ConcreteCategory.isIso_iff_bijective]
  rfl

/-- **`H⁻¹` of the cochain realisation is an epimorphism exactly when `φ.kernelMap` is
surjective.** -/
theorem epi_homologyMap_negOne_iff (φ : Hom E L) :
    Epi (HomologicalComplex.homologyMap (toCochainComplexHom φ) (-1)) ↔
      Function.Surjective φ.kernelMap := by
  rw [epi_iff_of_square (homologyIsoNegOne E) (homologyIsoNegOne L) (homologyMap_negOne_comm φ),
    ModuleCat.epi_iff_surjective]
  rfl

/-! ### The derived obstruction theory -/

section DerivedCategoryComparison

attribute [local instance] HasDerivedCategory.standard

/-- The object of the derived category of `R`-modules represented by a two-term complex. -/
noncomputable def derivedObject (E : LinearTwoTermComplex R) :
    DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Q.obj E.toCochainComplex

/-- The morphism of the derived category represented by a chain map of two-term complexes. -/
noncomputable def derivedMap (φ : Hom E L) : derivedObject E ⟶ derivedObject L :=
  DerivedCategory.Q.map (toCochainComplexHom φ)

/-- **`H⁰` in the derived category is `φ.cokernelMap`.** -/
theorem isIso_cohomologyMap_zero_iff (φ : Hom E L) :
    IsIso (DerivedObstructionTheory.cohomologyMap 0 (derivedMap φ)) ↔
      Function.Bijective φ.cokernelMap := by
  rw [← isIso_homologyMap_zero_iff φ]
  exact isIso_iff_of_square
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) 0).app E.toCochainComplex)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) 0).app L.toCochainComplex)
    (DerivedCategory.homologyFunctorFactors_hom_naturality (toCochainComplexHom φ) 0)

/-- **`H⁻¹` in the derived category is `φ.kernelMap`.** -/
theorem epi_cohomologyMap_negOne_iff (φ : Hom E L) :
    Epi (DerivedObstructionTheory.cohomologyMap (-1) (derivedMap φ)) ↔
      Function.Surjective φ.kernelMap := by
  rw [← epi_homologyMap_negOne_iff φ]
  exact epi_iff_of_square
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (-1)).app E.toCochainComplex)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (-1)).app L.toCochainComplex)
    (DerivedCategory.homologyFunctorFactors_hom_naturality (toCochainComplexHom φ) (-1))

/-- **The two-term notion of an obstruction theory is the derived-category notion.**

A chain map `φ : E ⟶ L` of two-term complexes satisfies `PicardCriteria.IsObstructionTheory`
exactly when the induced morphism of the derived category of `R`-modules satisfies the
Behrend–Fantechi conditions of `DerivedObstructionTheory.ObstructionTheory`: `H⁰` an isomorphism
and `H⁻¹` an epimorphism. -/
theorem isObstructionTheory_iff_derived (φ : Hom E L) :
    IsObstructionTheory φ ↔
      (IsIso (DerivedObstructionTheory.cohomologyMap 0 (derivedMap φ)) ∧
        Epi (DerivedObstructionTheory.cohomologyMap (-1) (derivedMap φ))) := by
  rw [isIso_cohomologyMap_zero_iff, epi_cohomologyMap_negOne_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **From the two-term model to the derived definition.** -/
noncomputable def derivedObstructionTheory {φ : Hom E L} (h : IsObstructionTheory φ) :
    DerivedObstructionTheory.ObstructionTheory (derivedObject L) where
  E := derivedObject E
  φ := derivedMap φ
  h0_isIso := ((isObstructionTheory_iff_derived φ).1 h).1
  hNegOne_epi := ((isObstructionTheory_iff_derived φ).1 h).2

/-- **From the derived definition back to the two-term model.** -/
theorem isObstructionTheory_of_derived {φ : Hom E L}
    (hiso : IsIso (DerivedObstructionTheory.cohomologyMap 0 (derivedMap φ)))
    (hepi : Epi (DerivedObstructionTheory.cohomologyMap (-1) (derivedMap φ))) :
    IsObstructionTheory φ :=
  (isObstructionTheory_iff_derived φ).2 ⟨hiso, hepi⟩

end DerivedCategoryComparison

end Derived

end PicardCriteria

/-! ## External direct sums and base change of two-term complexes -/

namespace LinearTwoTermComplex

open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R]

/-- **The external direct sum of two two-term complexes**, degreewise the product. -/
abbrev sum (E E' : LinearTwoTermComplex R) : LinearTwoTermComplex R where
  degreeZero := E.degreeZero × E'.degreeZero
  degreeOne := E.degreeOne × E'.degreeOne
  differential := E.differential.prodMap E'.differential

theorem sum_differential (E E' : LinearTwoTermComplex R) :
    (E.sum E').differential = E.differential.prodMap E'.differential :=
  rfl

/-- **The direct sum of two chain maps.** -/
abbrev Hom.sum {E E' L L' : LinearTwoTermComplex R} (φ : Hom E L) (φ' : Hom E' L') :
    Hom (E.sum E') (L.sum L') where
  degreeZero := φ.degreeZero.prodMap φ'.degreeZero
  degreeOne := φ.degreeOne.prodMap φ'.degreeOne
  comm x := Prod.ext (φ.comm x.1) (φ'.comm x.2)

theorem Hom.sum_degreeZero {E E' L L' : LinearTwoTermComplex R} (φ : Hom E L) (φ' : Hom E' L') :
    (φ.sum φ').degreeZero = φ.degreeZero.prodMap φ'.degreeZero :=
  rfl

theorem Hom.sum_degreeOne {E E' L L' : LinearTwoTermComplex R} (φ : Hom E L) (φ' : Hom E' L') :
    (φ.sum φ').degreeOne = φ.degreeOne.prodMap φ'.degreeOne :=
  rfl

/-- **The base change of a two-term complex along an `R`-algebra `R'`**, degreewise
`R' ⊗[R] -`. -/
abbrev baseChange (E : LinearTwoTermComplex R) (R' : Type u) [CommRing R'] [Algebra R R'] :
    LinearTwoTermComplex R' where
  degreeZero := R' ⊗[R] E.degreeZero
  degreeOne := R' ⊗[R] E.degreeOne
  differential := LinearMap.baseChange R' E.differential

theorem baseChange_differential (E : LinearTwoTermComplex R) (R' : Type u) [CommRing R']
    [Algebra R R'] :
    (E.baseChange R').differential = LinearMap.baseChange R' E.differential :=
  rfl

/-- The commuting square of a chain map is preserved by base change. -/
theorem baseChange_comm {E L : LinearTwoTermComplex R} (φ : Hom E L) (R' : Type u) [CommRing R']
    [Algebra R R'] (x : R' ⊗[R] E.degreeZero) :
    LinearMap.baseChange R' φ.degreeOne (LinearMap.baseChange R' E.differential x) =
      LinearMap.baseChange R' L.differential (LinearMap.baseChange R' φ.degreeZero x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => simp [φ.comm m]
  | add x y hx hy => simp [hx, hy]

/-- **The base change of a chain map.** -/
abbrev Hom.baseChange {E L : LinearTwoTermComplex R} (φ : Hom E L) (R' : Type u) [CommRing R']
    [Algebra R R'] : Hom (E.baseChange R') (L.baseChange R') where
  degreeZero := LinearMap.baseChange R' φ.degreeZero
  degreeOne := LinearMap.baseChange R' φ.degreeOne
  comm x := baseChange_comm φ R' x

theorem Hom.baseChange_degreeZero {E L : LinearTwoTermComplex R} (φ : Hom E L) (R' : Type u)
    [CommRing R'] [Algebra R R'] :
    (φ.baseChange R').degreeZero = LinearMap.baseChange R' φ.degreeZero :=
  rfl

theorem Hom.baseChange_degreeOne {E L : LinearTwoTermComplex R} (φ : Hom E L) (R' : Type u)
    [CommRing R'] [Algebra R R'] :
    (φ.baseChange R').degreeOne = LinearMap.baseChange R' φ.degreeOne :=
  rfl

end LinearTwoTermComplex

namespace PicardCriteria

universe u

open LinearTwoTermComplex

/-! ## Perfect obstruction theories and vector-bundle stacks -/

section Perfect

variable {R : Type u} [CommRing R]

/-- **Perfectness in the affine two-term model.**  A two-term complex is perfect exactly when
both of its terms are finite free; there is no further amplitude condition, since the complex
is concentrated in degrees `-1` and `0` by construction.  This is
`PicardCriteria.IsFiniteFreeComplex` of `Cones/CriteriaBundle.lean`, named here for the
obstruction-theory layer. -/
abbrev IsPerfectTwoTerm (E : LinearTwoTermComplex R) : Prop := IsFiniteFreeComplex E

/-- **The fibres of `h¹/h⁰(Eᵛ)` are vector-bundle stacks.**

If `E` is perfect then, over every test algebra `B`, the two-term complex of `B`-points of the
dual, `[Hom_R(E¹, B) → Hom_R(E⁰, B)]`, again has finite free terms.  Its Picard groupoid — the
fibre of `h¹/h⁰(Eᵛ)` over `Spec B` — is therefore the translation groupoid of a two-term complex
of vector bundles on `Spec B`, which is what it means for `h¹/h⁰(Eᵛ)` to be a vector-bundle
stack. -/
theorem isFiniteFreeComplex_dualPoints {E : LinearTwoTermComplex R} (h : IsPerfectTwoTerm E)
    (B : Type u) [CommRing B] [Algebra R B] : IsFiniteFreeComplex (dualPoints E B) := by
  have h1 := h.free_degreeZero
  have h2 := h.finite_degreeZero
  have h3 := h.free_degreeOne
  have h4 := h.finite_degreeOne
  exact
    { free_degreeZero := Module.Free.linearMap R B E.degreeOne B
      finite_degreeZero := Module.Finite.linearMap R B E.degreeOne B
      free_degreeOne := Module.Free.linearMap R B E.degreeZero B
      finite_degreeOne := Module.Finite.linearMap R B E.degreeZero B }

/-- **The virtual rank of the dual fibre.**  The vector-bundle stack `h¹/h⁰(Eᵛ)(B)` has rank
`-virtualRank E`: dualising exchanges the two terms. -/
theorem virtualRank_dualPoints [Nontrivial R] {E : LinearTwoTermComplex R}
    (h : IsPerfectTwoTerm E) (B : Type u) [CommRing B] [Algebra R B] [Nontrivial B] :
    virtualRank (dualPoints E B) = -virtualRank E := by
  have h1 := h.free_degreeZero
  have h2 := h.finite_degreeZero
  have h3 := h.free_degreeOne
  have h4 := h.finite_degreeOne
  have e1 : Module.finrank B (E.degreeZero →ₗ[R] B) = Module.finrank R E.degreeZero := by
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
  have e2 : Module.finrank B (E.degreeOne →ₗ[R] B) = Module.finrank R E.degreeOne := by
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
  have key : ((Module.finrank B (E.degreeZero →ₗ[R] B) : ℤ)
      - (Module.finrank B (E.degreeOne →ₗ[R] B) : ℤ))
      = -((Module.finrank R E.degreeOne : ℤ) - (Module.finrank R E.degreeZero : ℤ)) := by
    rw [e1, e2]
    ring
  exact key

/-- The virtual rank of a perfect two-term complex is invariant under chain homotopy
equivalence, so the virtual rank of a perfect obstruction theory is an invariant of its
homotopy class. -/
theorem IsPerfectTwoTerm.virtualRank_eq [Nontrivial R] {E E' : LinearTwoTermComplex R}
    (h : IsPerfectTwoTerm E) (h' : IsPerfectTwoTerm E') (e : HomotopyEquivalence E E') :
    virtualRank E = virtualRank E' :=
  virtualRank_eq_of_homotopyEquivalence h h' e

/-- Perfectness is stable under external direct sums. -/
theorem IsPerfectTwoTerm.sum {E E' : LinearTwoTermComplex R} (h : IsPerfectTwoTerm E)
    (h' : IsPerfectTwoTerm E') : IsPerfectTwoTerm (E.sum E') := by
  have h1 := h.free_degreeZero
  have h2 := h.finite_degreeZero
  have h3 := h.free_degreeOne
  have h4 := h.finite_degreeOne
  have h1' := h'.free_degreeZero
  have h2' := h'.finite_degreeZero
  have h3' := h'.free_degreeOne
  have h4' := h'.finite_degreeOne
  exact
    { free_degreeZero := Module.Free.prod R E.degreeZero E'.degreeZero
      finite_degreeZero := Module.Finite.prod
      free_degreeOne := Module.Free.prod R E.degreeOne E'.degreeOne
      finite_degreeOne := Module.Finite.prod }

/-- **Virtual ranks add under external direct sums.** -/
theorem virtualRank_sum [Nontrivial R] {E E' : LinearTwoTermComplex R} (h : IsPerfectTwoTerm E)
    (h' : IsPerfectTwoTerm E') :
    virtualRank (E.sum E') = virtualRank E + virtualRank E' := by
  have h1 := h.free_degreeZero
  have h2 := h.finite_degreeZero
  have h3 := h.free_degreeOne
  have h4 := h.finite_degreeOne
  have h1' := h'.free_degreeZero
  have h2' := h'.finite_degreeZero
  have h3' := h'.free_degreeOne
  have h4' := h'.finite_degreeOne
  have key : ((Module.finrank R (E.degreeOne × E'.degreeOne) : ℤ)
      - (Module.finrank R (E.degreeZero × E'.degreeZero) : ℤ))
      = ((Module.finrank R E.degreeOne : ℤ) - (Module.finrank R E.degreeZero : ℤ))
        + ((Module.finrank R E'.degreeOne : ℤ) - (Module.finrank R E'.degreeZero : ℤ)) := by
    rw [Module.finrank_prod, Module.finrank_prod]
    push_cast
    ring
  exact key

end Perfect

/-! ## Right exactness of the mapping-cone sequence -/

section ConeExactness

variable {R : Type u} [CommRing R] {E L : LinearTwoTermComplex R}

/-- An obstruction theory makes the mapping-cone sequence `E⁻¹ → L⁻¹ ⊕ E⁰ → L⁰ → 0` right
exact. -/
theorem IsObstructionTheory.exact_cone {φ : Hom E L} (h : IsObstructionTheory φ) :
    Function.Surjective (coneBeta φ) ∧ Function.Exact (coneAlpha φ) (coneBeta φ) :=
  ⟨coneBeta_surjective φ h.bijective_cokernelMap.2,
    LinearMap.exact_iff.2 (ker_coneBeta φ h.surjective_kernelMap h.bijective_cokernelMap.1)⟩

/-- Right exactness of the mapping-cone sequence makes `φ` an obstruction theory. -/
theorem isObstructionTheory_of_exact_cone {φ : Hom E L}
    (hsurj : Function.Surjective (coneBeta φ))
    (hexact : Function.Exact (coneAlpha φ) (coneBeta φ)) : IsObstructionTheory φ := by
  have hker : LinearMap.ker (coneBeta φ) = LinearMap.range (coneAlpha φ) :=
    LinearMap.exact_iff.1 hexact
  refine ⟨⟨?_, ?_⟩, surjective_kernelMap_of_ker_coneBeta (le_of_eq hker)⟩
  · refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
    obtain ⟨x, rfl⟩ := h1mk_surjective p
    rw [cokernelMap_h1mk, h1mk_eq_zero_iff] at hp
    obtain ⟨a, ha⟩ := hp
    have hmem : ((-a, x) : L.degreeZero × E.degreeOne) ∈ LinearMap.ker (coneBeta φ) := by
      rw [LinearMap.mem_ker, coneBeta_apply, map_neg, ha]
      abel
    rw [hker] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hsnd := congrArg Prod.snd hy
    rw [coneAlpha_apply] at hsnd
    rw [h1mk_eq_zero_iff]
    exact ⟨-y, by rw [map_neg]; exact hsnd⟩
  · intro q
    obtain ⟨b, rfl⟩ := h1mk_surjective q
    obtain ⟨m, hm⟩ := hsurj b
    rw [coneBeta_apply] at hm
    have hz : h1mk L (φ.degreeOne m.2 - b) = 0 :=
      (h1mk_eq_zero_iff _).2 ⟨-m.1, by rw [map_neg, ← hm]; abel⟩
    rw [h1mk_sub, sub_eq_zero] at hz
    exact ⟨h1mk E m.2, by rw [cokernelMap_h1mk]; exact hz⟩

/-- **Being an obstruction theory is right exactness of the mapping-cone sequence.**

`φ : E ⟶ L` is an obstruction theory exactly when

`E⁻¹ → L⁻¹ ⊕ E⁰ → L⁰ → 0`

is exact.  This reformulation is what makes the notion stable under arbitrary base change:
tensor products are right exact. -/
theorem isObstructionTheory_iff_exact_cone (φ : Hom E L) :
    IsObstructionTheory φ ↔
      (Function.Surjective (coneBeta φ) ∧ Function.Exact (coneAlpha φ) (coneBeta φ)) :=
  ⟨IsObstructionTheory.exact_cone, fun h => isObstructionTheory_of_exact_cone h.1 h.2⟩

end ConeExactness

/-! ## External sums of obstruction theories -/

section Sum

variable {R : Type u} [CommRing R] {E E' L L' : LinearTwoTermComplex R}

/-- The second map of the mapping-cone sequence of a direct sum is the product of the two
mapping-cone maps. -/
theorem coneBeta_sum (φ : Hom E L) (φ' : Hom E' L') (a : L.degreeZero) (a' : L'.degreeZero)
    (x : E.degreeOne) (x' : E'.degreeOne) :
    coneBeta (φ.sum φ') ((a, a'), (x, x')) = (coneBeta φ (a, x), coneBeta φ' (a', x')) :=
  rfl

/-- The first map of the mapping-cone sequence of a direct sum is the product of the two
mapping-cone maps, up to the shuffle of the two product factors. -/
theorem coneAlpha_sum (φ : Hom E L) (φ' : Hom E' L') (y : E.degreeZero) (y' : E'.degreeZero) :
    coneAlpha (φ.sum φ') (y, y') =
      (((coneAlpha φ y).1, (coneAlpha φ' y').1), ((coneAlpha φ y).2, (coneAlpha φ' y').2)) :=
  rfl

/-- **The external direct sum of two obstruction theories is an obstruction theory, and
conversely.** -/
theorem isObstructionTheory_sum_iff (φ : Hom E L) (φ' : Hom E' L') :
    IsObstructionTheory (φ.sum φ') ↔ (IsObstructionTheory φ ∧ IsObstructionTheory φ') := by
  simp only [isObstructionTheory_iff_exact_cone]
  constructor
  · rintro ⟨hsurj, hexact⟩
    refine ⟨⟨fun y => ?_, fun z => ?_⟩, ⟨fun y => ?_, fun z => ?_⟩⟩
    · obtain ⟨⟨⟨a, a'⟩, ⟨x, x'⟩⟩, hm⟩ := hsurj (y, 0)
      rw [coneBeta_sum] at hm
      exact ⟨(a, x), congrArg Prod.fst hm⟩
    · obtain ⟨a, x⟩ := z
      refine ⟨fun hz => ?_, ?_⟩
      · have hz' : coneBeta (φ.sum φ') ((a, 0), (x, 0)) = 0 := by
          rw [coneBeta_sum, hz, coneBeta_apply]
          simp only [map_zero, add_zero]
          rfl
        obtain ⟨⟨y, y'⟩, hy⟩ := (hexact _).1 hz'
        rw [coneAlpha_sum] at hy
        exact ⟨y, Prod.ext (congrArg (fun w => Prod.fst w.1) hy)
          (congrArg (fun w => Prod.fst w.2) hy)⟩
      · rintro ⟨y, hy⟩
        exact hy ▸ coneBeta_coneAlpha φ y
    · obtain ⟨⟨⟨a, a'⟩, ⟨x, x'⟩⟩, hm⟩ := hsurj (0, y)
      rw [coneBeta_sum] at hm
      exact ⟨(a', x'), congrArg Prod.snd hm⟩
    · obtain ⟨a', x'⟩ := z
      refine ⟨fun hz => ?_, ?_⟩
      · have hz' : coneBeta (φ.sum φ') ((0, a'), (0, x')) = 0 := by
          rw [coneBeta_sum, hz, coneBeta_apply]
          simp only [map_zero, add_zero]
          rfl
        obtain ⟨⟨y, y'⟩, hy⟩ := (hexact _).1 hz'
        rw [coneAlpha_sum] at hy
        exact ⟨y', Prod.ext (congrArg (fun w => Prod.snd w.1) hy)
          (congrArg (fun w => Prod.snd w.2) hy)⟩
      · rintro ⟨y, hy⟩
        exact hy ▸ coneBeta_coneAlpha φ' y
  · rintro ⟨⟨hs, he⟩, ⟨hs', he'⟩⟩
    refine ⟨fun y => ?_, fun z => ?_⟩
    · obtain ⟨b, b'⟩ := y
      obtain ⟨⟨a, x⟩, hm⟩ := hs b
      obtain ⟨⟨a', x'⟩, hm'⟩ := hs' b'
      exact ⟨((a, a'), (x, x')), by rw [coneBeta_sum, hm, hm']⟩
    · obtain ⟨⟨a, a'⟩, ⟨x, x'⟩⟩ := z
      refine ⟨fun hz => ?_, ?_⟩
      · rw [coneBeta_sum] at hz
        obtain ⟨y, hy⟩ := (he (a, x)).1 (congrArg Prod.fst hz)
        obtain ⟨y', hy'⟩ := (he' (a', x')).1 (congrArg Prod.snd hz)
        refine ⟨(y, y'), ?_⟩
        rw [coneAlpha_sum, hy, hy']
      · rintro ⟨y, hy⟩
        exact hy ▸ coneBeta_coneAlpha (φ.sum φ') y

/-- The external direct sum of two obstruction theories is an obstruction theory. -/
theorem IsObstructionTheory.sum {φ : Hom E L} {φ' : Hom E' L'} (h : IsObstructionTheory φ)
    (h' : IsObstructionTheory φ') : IsObstructionTheory (φ.sum φ') :=
  (isObstructionTheory_sum_iff φ φ').2 ⟨h, h'⟩

end Sum

/-! ## Base change of obstruction theories -/

section BaseChange

open scoped TensorProduct

variable {R : Type u} [CommRing R] {E L : LinearTwoTermComplex R} (R' : Type u) [CommRing R']
  [Algebra R R']

/-- The first map of the base-changed mapping-cone sequence is the base change of the first map,
through the distributivity of tensor products over products. -/
theorem coneAlpha_baseChange (φ : Hom E L) (z : R' ⊗[R] E.degreeZero) :
    coneAlpha (φ.baseChange R') z =
      TensorProduct.prodRight R R' R' L.degreeZero E.degreeOne
        (LinearMap.lTensor R' (coneAlpha φ) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    have hval : coneAlpha (φ.baseChange R') (r ⊗ₜ[R] x) =
        (LinearMap.baseChange R' φ.degreeZero (r ⊗ₜ[R] x),
          -LinearMap.baseChange R' E.differential (r ⊗ₜ[R] x)) := rfl
    rw [hval]
    simp [TensorProduct.tmul_neg]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The second map of the base-changed mapping-cone sequence is the base change of the second
map, through the distributivity of tensor products over products. -/
theorem coneBeta_baseChange (φ : Hom E L) (z : R' ⊗[R] (L.degreeZero × E.degreeOne)) :
    coneBeta (φ.baseChange R')
        (TensorProduct.prodRight R R' R' L.degreeZero E.degreeOne z) =
      LinearMap.lTensor R' (coneBeta φ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    have hval : coneBeta (φ.baseChange R') (r ⊗ₜ[R] x.1, r ⊗ₜ[R] x.2) =
        LinearMap.baseChange R' L.differential (r ⊗ₜ[R] x.1) +
          LinearMap.baseChange R' φ.degreeOne (r ⊗ₜ[R] x.2) := rfl
    simp only [TensorProduct.prodRight_tmul, hval, LinearMap.baseChange_tmul,
      LinearMap.lTensor_tmul, coneBeta_apply, TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Base change of an obstruction theory is an obstruction theory.**

For *every* `R`-algebra `R'` — no flatness is required — the degreewise base change
`R' ⊗[R] φ` of an obstruction theory is an obstruction theory over `R'`.  The reason is
`PicardCriteria.isObstructionTheory_iff_exact_cone`: being an obstruction theory is right
exactness of the mapping-cone sequence, and tensor products are right exact. -/
theorem IsObstructionTheory.baseChange {φ : Hom E L} (h : IsObstructionTheory φ) :
    IsObstructionTheory (φ.baseChange R') := by
  obtain ⟨hsurj, hexact⟩ := h.exact_cone
  have hT : Function.Exact (LinearMap.lTensor R' (coneAlpha φ))
      (LinearMap.lTensor R' (coneBeta φ)) := _root_.lTensor_exact R' hexact hsurj
  refine isObstructionTheory_of_exact_cone (fun z => ?_) (fun z => ?_)
  · obtain ⟨w, hw⟩ := LinearMap.lTensor_surjective R' hsurj z
    exact ⟨TensorProduct.prodRight R R' R' L.degreeZero E.degreeOne w,
      (coneBeta_baseChange R' φ w).trans hw⟩
  · constructor
    · intro hz
      have hz' : LinearMap.lTensor R' (coneBeta φ)
          ((TensorProduct.prodRight R R' R' L.degreeZero E.degreeOne).symm z) = 0 := by
        rw [← coneBeta_baseChange R' φ, LinearEquiv.apply_symm_apply]
        exact hz
      obtain ⟨w, hw⟩ := (hT _).1 hz'
      refine ⟨w, ?_⟩
      rw [coneAlpha_baseChange, hw, LinearEquiv.apply_symm_apply]
    · rintro ⟨w, rfl⟩
      rw [coneAlpha_baseChange, coneBeta_baseChange]
      exact (hT _).2 ⟨w, rfl⟩

end BaseChange

end PicardCriteria

/-! ## Direct sums of global two-term resolutions -/

namespace CotangentComplex.PerfectComplex

open CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R]

attribute [local instance] HasDerivedCategory.standard

/-- The binary biproduct of two zero module objects is a zero object. -/
theorem isZero_biprod {M N : ModuleCat.{u} R} (hM : IsZero M) (hN : IsZero N) :
    IsZero (M ⊞ N) := by
  rw [IsZero.iff_id_eq_zero, ← biprod.total, hM.eq_of_tgt biprod.fst 0,
    hN.eq_of_tgt biprod.snd 0, zero_comp, zero_comp, add_zero]

/-- **The localisation functor to the derived category preserves binary biproducts.**  It is
additive, so the matrix `(Q(fst), Q(snd))` is an isomorphism with inverse `(Q(inl), Q(inr))`. -/
noncomputable def qMapBiprod (K K' : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj (K ⊞ K') ≅
      DerivedCategory.Q.obj K ⊞ DerivedCategory.Q.obj K' where
  hom := biprod.lift (DerivedCategory.Q.map biprod.fst) (DerivedCategory.Q.map biprod.snd)
  inv := biprod.desc (DerivedCategory.Q.map biprod.inl) (DerivedCategory.Q.map biprod.inr)
  hom_inv_id := by
    rw [biprod.lift_desc, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add,
      biprod.total, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [← Functor.map_comp]

/-- **The direct sum of two global two-term resolutions.**

The biproduct of the two resolving complexes is again concentrated in degrees `-1` and `0` with
finite free terms, and its image in the derived category is the biproduct of the two derived
objects, because `DerivedCategory.Q` is additive.  This is the stability of "has a global
two-term resolution" under biproducts. -/
noncomputable def GlobalTwoTermResolution.sum {E F : DerivedCategory (ModuleCat.{u} R)}
    (P : GlobalTwoTermResolution E) (P' : GlobalTwoTermResolution F) :
    GlobalTwoTermResolution (E ⊞ F) where
  complex := P.complex ⊞ P'.complex
  supported i hi :=
    (isZero_biprod (P.supported i hi) (P'.supported i hi)).of_iso
      (HomologicalComplex.biprodXIso _ _ i)
  finiteFree i :=
    ((P.finiteFree i).biprod (P'.finiteFree i)).of_iso
      (HomologicalComplex.biprodXIso _ _ i).symm
  iso := qMapBiprod P.complex P'.complex ≪≫ biprod.mapIso P.iso P'.iso

/-- **"Has a global two-term resolution" is stable under biproducts.** -/
theorem nonempty_globalTwoTermResolution_biprod {E F : DerivedCategory (ModuleCat.{u} R)}
    (hE : Nonempty (GlobalTwoTermResolution E)) (hF : Nonempty (GlobalTwoTermResolution F)) :
    Nonempty (GlobalTwoTermResolution (E ⊞ F)) :=
  ⟨hE.some.sum hF.some⟩

end CotangentComplex.PerfectComplex

end GromovWitten.AlgebraicGeometry
