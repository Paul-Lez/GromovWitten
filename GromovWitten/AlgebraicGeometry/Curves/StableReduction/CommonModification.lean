/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ModelBlowup

/-!
# A common scheme dominating two modifications of a model

Given two proper modifications `f : ModelModification M P` and `g : ModelModification N P` of
models of the same curve to a common target `P`, this file constructs the fibre product
`M.total ×_{P.total} N.total`, together with its structure map to `Spec R` and the properness of
both projections.

This scheme is **not** shown to be a `Model` here: unlike properness (stable under base change)
and quasi-compactness/finite presentation (also stable under base change, though not needed for
the deliverables below), flatness over `R` genuinely fails for the naive fibre product in general.
The special fibre of `M.total ×_{P.total} N.total` can pick up extra `R`-torsion components (for
instance when `M` and `N` blow up different centres of the same node of `P`, the fibre product
contains components entirely contained in the special fibre, i.e. `R`-torsion, unlike a model's
total space).  The standard fix -- taking the scheme-theoretic closure of the diagonal generic
fibre inside the fibre product, i.e. the flat/torsion-free part -- would repair this, but no
"closure model" construction exists yet in this repository (`grep`ping the whole `AlgebraicGeometry`
tree for scheme-theoretic-closure machinery turns up nothing), so it is not attempted here.

The identification of the generic fibre of the fibre product with the common curve `C` is also
left open: informally, since `f` and `g` are modifications, restricting `f.hom.hom` and
`g.hom.hom` to generic fibres gives isomorphisms onto the generic fibre of `P`, and base change of
an isomorphism is again an isomorphism, so restricting either projection of the fibre product to
generic fibres should again be an isomorphism, identifying the generic fibre of the fibre product
with that of `M` (equivalently of `N`), hence with `C`.  Formalizing this needs an "iterated
pullback" identity (the generic fibre of a fibre product is the fibre product, over the generic
fibre of `P`, of the generic fibres of `M` and `N`) together with the fact that pulling back an
isomorphism stays an isomorphism; assembling the relevant `IsPullback`pasting lemmas
(`pullbackLeftPullbackSndIso`or equivalent) into this precise statement was not completed here and
is the remaining gap.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

namespace ModelModification

variable {M N P : Model R K C toK} (f : ModelModification M P) (g : ModelModification N P)

/-- The fibre product of the total spaces of two modifications of a common target `P`: a scheme
dominating both `M.total` and `N.total`, though not (yet) shown to underlie a `Model` -- see the
module docstring for the flatness gap. -/
abbrev commonTotal : Scheme.{u} := pullback f.hom.hom g.hom.hom

/-- The structure map of the common scheme to the base DVR, computed through `M`. -/
def commonToBase : commonTotal f g ⟶ Spec (.of R) :=
  pullback.fst f.hom.hom g.hom.hom ≫ M.toBase

/-- The structure map computed through `M` agrees with the one computed through `N`: both
modifications commute with the models' structure maps to `Spec R`, so the two composites with
`pullback.condition` agree. -/
theorem commonToBase_eq_snd :
    commonToBase f g = pullback.snd f.hom.hom g.hom.hom ≫ N.toBase := by
  change pullback.fst f.hom.hom g.hom.hom ≫ M.toBase =
      pullback.snd f.hom.hom g.hom.hom ≫ N.toBase
  rw [← f.hom.over_base, ← g.hom.over_base, ← Category.assoc, ← Category.assoc,
    pullback.condition]

/-- The first projection of the common scheme onto `M.total` is proper: it is the base change,
along `f.hom.hom`, of the proper morphism `g.hom.hom`. -/
instance isProper_fst : _root_.AlgebraicGeometry.IsProper (pullback.fst f.hom.hom g.hom.hom) := by
  have : _root_.AlgebraicGeometry.IsProper g.hom.hom := g.proper
  infer_instance

/-- The second projection of the common scheme onto `N.total` is proper: it is the base change,
along `g.hom.hom`, of the proper morphism `f.hom.hom`. -/
instance isProper_snd : _root_.AlgebraicGeometry.IsProper (pullback.snd f.hom.hom g.hom.hom) := by
  have : _root_.AlgebraicGeometry.IsProper f.hom.hom := f.proper
  infer_instance

/-- The structure map of the common scheme to `Spec R` is proper whenever `M` (equivalently `N`,
via `commonToBase_eq_snd`) is proper: it factors as the proper first projection followed by the
proper structure map of `M`. -/
instance isProper_commonToBase [M.IsProper] :
    _root_.AlgebraicGeometry.IsProper (commonToBase f g) := by
  have : _root_.AlgebraicGeometry.IsProper M.toBase := ‹M.IsProper›
  unfold commonToBase
  infer_instance

end ModelModification

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
