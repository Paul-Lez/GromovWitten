/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.Cones.ConeQuotientStack
import GromovWitten.AlgebraicGeometry.Cones.SmoothAmbientEtaleConeAction

/-!
# The cone stack of a formally-étale chart

`Cones/ConeQuotientStack.lean` builds, for an abstract base ring `R`, an abstract graded cone
ring `S` and a free `R`-module `F`, a `ConeStack (ConeQuotient.coneBaseStack R)
canonicalFppfScalarRings` out of any `ConeQuotient.ConeAction R S F`, an `R`-basis of `F` and a
vertex augmentation of `S` (`ConeQuotient.coneQuotientStack`). Until now this had only ever been
instantiated at the single, unlocalised presentation of `Cones/NormalConeAction.lean`
(`NormalConeAction.normalConeAction`/`tangentBasis`, the "polynomial model"). What is new here is
the *first* instantiation of `ConeQuotient.coneQuotientStack` at the generality of
`Cones/SmoothAmbientEtaleConeAction.lean`: for **every** formally-étale `Amb A σ`-algebra `R` (an
arbitrary chart of the ambient `𝔸^σ_A`, not just the tautological one) and every ideal `J ⊆ R`,
`EtaleConeAction.etaleNormalConeAction A σ R J`/`EtaleConeAction.tangentBasis A σ R J` together
with the unconditional vertex law `GradedCone.isConeVertex_normalConeCoactionQuot R J` assemble
into a cone stack over `Spec (R/J)` (`etaleChartConeStack`). Specialising at the *tautological*
chart `R = Amb A σ` recovers `coneQuotientStack` applied to `NormalConeAction.normalConeAction`
(by the pre-existing `EtaleConeAction.etaleNormalConeAction_eq`/`tangentBasis_eq`), so
`tautologicalChartConeStack` below is definitionally that one-chart construction, packaged at
the base `X = Spec (A[σ]/I)` itself.

## Main declarations

* `etaleChartConeStack A σ R J`: the cone stack, over `Spec (R/J)`, attached to *any*
  formally-étale chart `R` of the ambient `Amb A σ` and any ideal `J ⊆ R`.
* `tautologicalChartConeStack I`: `etaleChartConeStack` specialised at the tautological chart
  `R = Amb A σ` (no localisation), i.e. `ConeQuotient.coneQuotientStack` in the étale-chart
  generality, packaged as a cone stack over `X = Spec (A[σ]/I)` itself.

## What is not here

This file does **not** glue the intrinsic cone over a cover of local embeddings of `X` as a cone
stack (the remaining content of issue `#61`). Doing so needs base change of a `ConeStack` along a
scheme morphism (to compare `etaleChartConeStack` of a genuinely localised chart, whose base is
only a flat/étale piece of `X`, against a stack over all of `X`), and `Cones/Stack.lean` has no
such operation: its "Retired provisional cone-stack base change" comment (just above
`ClosedConeSubstack`) explains why an earlier attempt at exactly this was withdrawn as incomplete.
Nor does this file relate `etaleChartConeStack`'s fibres to the Type-valued groupoids of
`Cones/IntrinsicConeGluingCover.lean` (`ConeCover.intrinsicConeCover`/`AlgConeGroupoid`): that
needs triviality of vector-bundle-group torsors over affine test schemes, which is not proved
anywhere in `Cones/`. No comparison lemma between two *different* non-tautological charts is
given either: `Cones/SmoothAmbientEtaleConeAction.lean` supplies no composition/transport lemma
relating `etaleNormalConeAction`/`tangentBasis` at two distinct formally-étale `R`, `R'` (its only
comparison result, `etaleNormalConeAction_eq`/`tangentBasis_eq`, is specifically between a chart
`R` and the tautological chart `R = Amb A σ`, not between two arbitrary charts), so no such lemma
is stated here.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

namespace EtaleChartConeStack

universe u

noncomputable section

variable {A : Type u} [CommRing A] {σ : Type u}

/-- **The cone stack of a formally-étale chart.** For any formally-étale `Amb A σ`-algebra `R`
(compatibly an `A`-algebra) and any ideal `J ⊆ R`, the local model `[C_{U/M_R}/T_{M_R}|_U]` of
`Cones/SmoothAmbientEtaleConeAction.lean` assembles, via `ConeQuotient.coneQuotientStack`, into a
cone stack over `Spec (R/J)`. -/
def etaleChartConeStack (A : Type u) [CommRing A] (σ : Type u) (R : Type u) [CommRing R]
    [Algebra (MvPolynomial σ A) R] [Algebra.FormallyEtale (MvPolynomial σ A) R] [Algebra A R]
    [IsScalarTower A (MvPolynomial σ A) R] (J : Ideal R) :
    ConeStack (ConeQuotient.coneBaseStack (R ⧸ J)) canonicalFppfScalarRings.{u} :=
  ConeQuotient.coneQuotientStack (EtaleConeAction.etaleNormalConeAction A σ R J)
    (EtaleConeAction.tangentBasis A σ R J)
    (GradedCone.isConeVertex_normalConeCoactionQuot R J)

/-- **The cone stack of the tautological chart.** `etaleChartConeStack` specialised at
`R = Amb A σ` (no localisation): the affine normal cone `gr_I(Amb A σ)` already lives over the
whole closed subscheme `X = Spec (A[σ]/I)`, so this is `ConeQuotient.coneQuotientStack` in the
étale-chart generality, packaged as a cone stack over `X` itself. By
`EtaleConeAction.etaleNormalConeAction_eq`/`EtaleConeAction.tangentBasis_eq` it agrees, as a
term, with feeding `NormalConeAction.normalConeAction`/`NormalConeAction.tangentBasis` (the
polynomial model of `Cones/NormalConeAction.lean`) into `ConeQuotient.coneQuotientStack` directly.
Gluing this over a cover of local embeddings of `X` into a single cone stack (the remaining
content of issue `#61`) is **not** done here: see the module docstring. -/
def tautologicalChartConeStack (I : Ideal (MvPolynomial σ A)) :
    ConeStack (ConeQuotient.coneBaseStack (MvPolynomial σ A ⧸ I))
      canonicalFppfScalarRings.{u} :=
  etaleChartConeStack A σ (MvPolynomial σ A) I

end

end EtaleChartConeStack

end GromovWitten.AlgebraicGeometry
