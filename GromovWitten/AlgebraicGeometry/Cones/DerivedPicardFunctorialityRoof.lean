/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.DerivedPicardFunctoriality
import GromovWitten.AlgebraicGeometry.Cones.DerivedTruncationRoof

/-!
# Functoriality of `h¹/h⁰` for projectivity-free representatives

`Cones/DerivedPicardFunctoriality.lean` builds, for a derived morphism `f : E ⟶ E'` and a choice
of *K-projective* global two-term resolutions `F` of `E` and `F'` of `E'`, an induced functor
`picardMap f : F.picard ⥤ F'.picard` on Picard groupoids, together with identity/composition
coherence up to natural isomorphism.  `Cones/DerivedTruncationRoof.lean` shows that `h¹/h⁰` may
also be computed from an arbitrary (possibly non-projective) `TruncRep` of a derived object, and
that any two such representatives of the *same* object have equivalent Picard groupoids, via the
calculus of fractions rather than K-projectivity.

This file transports the functoriality of `picardMap` along the roof-based identification of
`Cones/DerivedTruncationRoof.lean`: given `TruncRep`s `K` of `E` and `K'` of `E'`, together with a
*chosen* auxiliary K-projective global two-term resolution `P` of `E` and `P'` of `E'`, every
derived morphism `f : E ⟶ E'` induces a functor `K.picard ⥤ K'.picard`, satisfying the same kind
of identity/composition coherence as `picardMap`, and specializing to an equivalence when `f` is
an isomorphism.

## Main declarations

* `TruncRep.truncEquiv`: the (non-canonically chosen) equivalence `P.picard ≌ K.picard` between
  the Picard groupoid of a K-projective global two-term resolution `P` of `E` and that of an
  arbitrary truncation representative `K` of `E`, extracted from the `Nonempty` statement
  `GlobalTwoTermResolution.nonempty_picardEquivalence_truncRep`.
* `TruncRep.picardMapRoof`: the induced functor `K.picard ⥤ K'.picard` attached to a derived
  morphism `f : E ⟶ E'` and a choice of auxiliary resolutions `P` of `E`, `P'` of `E'`, obtained
  by composing `(truncEquiv K P).inverse`, `GlobalTwoTermResolution.picardMap f` and
  `(truncEquiv K' P').functor`.
* `TruncRep.picardMapRoof_id`, `TruncRep.picardMapRoof_comp`: the functor induced by the identity
  is naturally isomorphic to the identity functor, and the functor induced by a composite is
  naturally isomorphic to the composite of the induced functors (for a *fixed* choice of the
  auxiliary resolutions), built from `GlobalTwoTermResolution.picardMap_id`/`picardMap_comp` and
  the unit/counit isomorphisms of `truncEquiv`.
* `TruncRep.picardMapRoofEquivOfIso`, instance `TruncRep.picardMapRoof_isEquivalence_of_iso`: when
  `f` is an isomorphism, `picardMapRoof f.hom` is promoted to an honest equivalence of Picard
  groupoids, by composing `(truncEquiv K P).symm`, `GlobalTwoTermResolution.picardEquivOfIso f`
  and `truncEquiv K' P'`.
* `TruncRep.nonempty_picardEquivalence_of_picardMapRoof`: specializing `picardMapRoofEquivOfIso`
  to `f = Iso.refl E` recovers the conclusion of `TruncRep.nonempty_picardEquivalence` (the
  projectivity-free resolution independence of `Cones/DerivedTruncationRoof.lean`), through a
  different route: an auxiliary K-projective resolution and `picardMap`, rather than a roof of
  quasi-isomorphisms and the calculus of fractions.

## What is not proved

* `picardMapRoof` is only defined relative to a *chosen* auxiliary K-projective global two-term
  resolution `P` of `E` (and likewise `P'` of `E'`), supplied as explicit data: no existence
  theorem producing such a `P` from an arbitrary `TruncRep` (or from an arbitrary object of the
  derived category) is available in this repository, and proving one in general would require
  free-resolution theory for modules over an arbitrary commutative ring, which is out of scope
  here. This mirrors the convention already used for `GlobalTwoTermResolution` itself, whose
  resolving complex is always "the chosen" complex, never produced by an existence theorem
  internal to `Cones/DerivedPicard.lean`.
* Even for a fixed choice of `P`, `P'`, the functor `picardMapRoof` further depends on the
  arbitrarily chosen witness `truncEquiv K P` (a `Classical.choice` of a `Nonempty` statement),
  and hence, exactly as for `picardMap_id`/`picardMap_comp` in `DerivedPicardFunctoriality.lean`,
  the coherence isomorphisms `picardMapRoof_id`/`picardMapRoof_comp` are well defined only up to
  further natural isomorphism, not on the nose; no pentagon/unit coherence statement comparing
  different choices of `P`, `P'` or of the `truncEquiv` witnesses is attempted.
* `nonempty_picardEquivalence_of_picardMapRoof` only records that `picardMapRoofEquivOfIso`
  witnesses the same `Nonempty` statement as `TruncRep.nonempty_picardEquivalence`; the two
  constructions (one through an auxiliary K-projective resolution and `picardMap`, the other
  through a roof of quasi-isomorphisms and the calculus of fractions) are not compared at the
  level of an explicit natural isomorphism of functors, which would require unwinding both
  constructions to genuine chain-level data.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

attribute [local instance] HasDerivedCategory.standard

open CotangentComplex.PerfectComplex

namespace TruncRep

variable {E E' E'' : DerivedCategory (ModuleCat.{u} R)}

/-! ## Identifying a truncation representative with a chosen K-projective resolution -/

/-- **A chosen equivalence between the Picard groupoid of an auxiliary K-projective global
two-term resolution and that of an arbitrary truncation representative of the same object.**
Extracted from the `Nonempty` statement
`GlobalTwoTermResolution.nonempty_picardEquivalence_truncRep`; not canonical (see the module
docstring). -/
noncomputable def truncEquiv (K : TruncRep E) (P : GlobalTwoTermResolution E) :
    P.picard ≌ K.picard :=
  Classical.choice (P.nonempty_picardEquivalence_truncRep K)

/-! ## The induced functor on Picard groupoids of arbitrary representatives -/

/-- **The functor induced on Picard groupoids of arbitrary truncation representatives by a
derived morphism**, relative to a chosen auxiliary K-projective global two-term resolution `P`
of `E` and `P'` of `E'`: the composite of `(truncEquiv K P).inverse`,
`GlobalTwoTermResolution.picardMap f` and `(truncEquiv K' P').functor`. -/
noncomputable def picardMapRoof (K : TruncRep E) (K' : TruncRep E')
    (P : GlobalTwoTermResolution E) (P' : GlobalTwoTermResolution E') (f : E ⟶ E') :
    K.picard ⥤ K'.picard :=
  (truncEquiv K P).inverse ⋙ GlobalTwoTermResolution.picardMap (F := P) (F' := P') f ⋙
    (truncEquiv K' P').functor

/-- **Identity coherence.**  The functor induced by the identity derived morphism is naturally
isomorphic to the identity functor of the Picard groupoid, for a fixed choice of auxiliary
resolution `P`. -/
noncomputable def picardMapRoof_id (K : TruncRep E) (P : GlobalTwoTermResolution E) :
    picardMapRoof K K P P (𝟙 E) ≅ 𝟭 K.picard :=
  Functor.isoWhiskerLeft (truncEquiv K P).inverse
      (Functor.isoWhiskerRight (GlobalTwoTermResolution.picardMap_id P) (truncEquiv K P).functor) ≪≫
    Functor.isoWhiskerLeft (truncEquiv K P).inverse (Functor.leftUnitor (truncEquiv K P).functor) ≪≫
    (truncEquiv K P).counitIso

/-- **Composition coherence.**  The functor induced by a composite derived morphism `f ≫ g` is
naturally isomorphic to the composite of the induced functors, for a fixed choice of the
auxiliary resolutions `P`, `P'`, `P''`. -/
noncomputable def picardMapRoof_comp (K : TruncRep E) (K' : TruncRep E') (K'' : TruncRep E'')
    (P : GlobalTwoTermResolution E) (P' : GlobalTwoTermResolution E')
    (P'' : GlobalTwoTermResolution E'') (f : E ⟶ E') (g : E' ⟶ E'') :
    picardMapRoof K K'' P P'' (f ≫ g) ≅
      picardMapRoof K K' P P' f ⋙ picardMapRoof K' K'' P' P'' g :=
  Functor.isoWhiskerLeft (truncEquiv K P).inverse
      (Functor.isoWhiskerRight
        (GlobalTwoTermResolution.picardMap_comp (F := P) (F' := P') (F'' := P'') f g)
        (truncEquiv K'' P'').functor) ≪≫
    Functor.isoWhiskerLeft (truncEquiv K P).inverse
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (GlobalTwoTermResolution.picardMap (F := P) (F' := P') f)
          ((Functor.leftUnitor (GlobalTwoTermResolution.picardMap (F := P') (F' := P'') g)).symm ≪≫
            Functor.isoWhiskerRight (truncEquiv K' P').unitIso
              (GlobalTwoTermResolution.picardMap (F := P') (F' := P'') g)))
        (truncEquiv K'' P'').functor)

/-! ## Compatibility with isomorphisms -/

/-- **When `f` is an isomorphism, `picardMapRoof f.hom` is promoted to an equivalence.**  Built
by composing `(truncEquiv K P).symm`, `GlobalTwoTermResolution.picardEquivOfIso f` and
`truncEquiv K' P'`; its forward functor agrees with `picardMapRoof f.hom`
(`picardMapRoof_isEquivalence_of_iso`). -/
noncomputable def picardMapRoofEquivOfIso (K : TruncRep E) (K' : TruncRep E')
    (P : GlobalTwoTermResolution E) (P' : GlobalTwoTermResolution E') (f : E ≅ E') :
    K.picard ≌ K'.picard :=
  (truncEquiv K P).symm.trans
    ((GlobalTwoTermResolution.picardEquivOfIso (F := P) (F' := P') f).trans (truncEquiv K' P'))

/-- The equivalence `picardMapRoofEquivOfIso` has forward functor `picardMapRoof f.hom`, so
`picardMapRoof f.hom` is an equivalence of categories whenever `f` is an isomorphism of the
derived category. -/
instance picardMapRoof_isEquivalence_of_iso (K : TruncRep E) (K' : TruncRep E')
    (P : GlobalTwoTermResolution E) (P' : GlobalTwoTermResolution E') (f : E ≅ E') :
    (picardMapRoof K K' P P' f.hom).IsEquivalence :=
  (picardMapRoofEquivOfIso K K' P P' f).isEquivalence_functor

/-- **Recovering resolution independence from `picardMapRoof`.**  Specializing
`picardMapRoofEquivOfIso` to the identity isomorphism of `E` gives an equivalence witnessing the
same `Nonempty` statement as `TruncRep.nonempty_picardEquivalence`, through an auxiliary
K-projective resolution rather than through the roof of quasi-isomorphisms of
`Cones/DerivedTruncationRoof.lean`. -/
theorem nonempty_picardEquivalence_of_picardMapRoof (K K' : TruncRep E)
    (P : GlobalTwoTermResolution E) : Nonempty (K.picard ≌ K'.picard) :=
  ⟨picardMapRoofEquivOfIso K K' P P (Iso.refl E)⟩

end TruncRep

end GromovWitten.AlgebraicGeometry
