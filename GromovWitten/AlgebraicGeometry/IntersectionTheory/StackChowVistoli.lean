/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroupLocalization
import GromovWitten.AlgebraicGeometry.Stacks.AtlasRefinement
import GromovWitten.AlgebraicGeometry.Stacks.Inertia

/-!
# Vistoli-style rational cycle groups of a stack presented by an atlas

Let `X` be an algebraic stack with a scheme atlas `U → X` and let `R = U ×_X U ⇉ U` be the
associated presentation groupoid, with its source and target maps `s, t : R ⟶ U`.  Vistoli's
rational Chow theory computes cycles on `X` as cycles on `U` which *descend*, that is which have
the same flat pullback under `s` and under `t`, and then divides by rational equivalence on `U`.

This file constructs that group for the part of the presentation which the currently available
flat-pullback theory can actually see.

## What is constructed

* `invariantCycles p q`, the equalizer of an arbitrary pair of linear maps on dimension-graded
  rational cycles.  Nothing geometric is assumed; the geometry enters when `p` and `q` are the two
  flat pullbacks of a groupoid.
* `OpenPresentationGroupoid`, the scheme-level data `R ⇉ U` of a presentation groupoid whose
  source and target are open immersions of relative dimension zero.
* `OpenPresentationGroupoid.cycles`, the invariant (descent) cycles on the atlas, with the
  pointwise characterisation `mem_cycles_iff`, and `OpenPresentationGroupoid.chow`, its quotient
  by rational equivalence on the atlas.
* `OpenPresentationGroupoid.Refinement`, a refinement of presentations, its induced map on
  invariant cycles and on Chow groups, functoriality of that map, and the resulting comparison of
  two presentations through a common refinement.  A refinement whose atlas map is invertible
  induces an isomorphism of Chow groups.
* The identity presentation of a scheme, for which the invariant cycles are all cycles and the
  Vistoli Chow group is canonically the scheme Chow group.
* The rational stabilizer weight `1/|Aut|` of an object of a presentation groupoid, its
  invariance under refinement of atlases, its identification with the automorphisms of the image
  object in the base stack, and the weighted degree of a zero-cycle on an atlas, computed on a
  one-point atlas with constant stabilizer group `Γ` to be `1/|Γ|`.

## What is missing, and why

The one genuinely missing geometric input is **flat pullback of algebraic cycles along a flat
morphism of positive relative dimension**.  Mathlib v4.33.1 has only
`AlgebraicGeometry.AlgebraicCycle.map` (proper pushforward); there is no `AlgebraicCycle.pullback`
for a flat morphism, and `IntersectionTheory/ChowGroupLocalization.lean` constructs it only for
open immersions, where every multiplicity is one and the pullback is literally restriction of the
coefficient function.  Consequently:

* The source and target of the presentation groupoid of a genuine smooth (or etale) atlas are
  smooth surjective, not open immersions, so `OpenPresentationGroupoid` cannot be instantiated at
  the groupoid of `AlgebraicStack.chosenAtlasSelfOverlap` except when that groupoid happens to
  have open-immersion legs (for example the identity atlas of a scheme).  Building the general
  instance needs the flat pullback above together with the relative-dimension shift `i ↦ i + d`.
* Independence of the atlas is proved here only in the form supplied by refinements: a refinement
  induces a map of Chow groups, two presentations with a common refinement are canonically
  compared through it, and an invertible refinement induces an isomorphism.  That the comparison
  map of an arbitrary refinement is an isomorphism is *not* proved: it is exactly the exactness of
  the descent sequence `0 → A(X) → A(U) ⇉ A(R)` for a smooth surjection `U → X`, which needs flat
  pullback along `U → X` itself (unavailable) and the surjectivity of flat pullback along a smooth
  cover (Fulton, *Intersection Theory*, Prop. 1.9 together with descent), also unavailable.
* `BG` is not available as a `DeligneMumfordStack`: `Stacks/QuotientStackClassifying.lean` builds
  `classifyingPrestack G` only as a prestack, since fppf descent for action torsors is open.  The
  degree computation is therefore carried out on an abstract one-point atlas whose stabilizer
  group is a finite group `Γ`, which is precisely the atlas data a presentation of `BΓ` would
  supply; see `pointDegree_pointFundamentalClass` and
  `weightedDegree_fundamentalCycle_of_autEquiv`.
* The weighted degree is defined on cycles, not on Chow classes, except on a one-point atlas
  where rational equivalence is proved trivial in `ChowGroup.lean`.  Making it descend in general
  is the degree theorem `deg div(f) = 0` for a proper curve, whose Mathlib input (the norm along a
  finite extension of function fields, and additivity of `Ring.ord`) is the same missing input
  already recorded in `ChowGroupLocalization.lean` for general proper pushforward.
-/

open CategoryTheory Order

attribute [local instance] specializationOrder

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

/-! ## Invariant cycles for an arbitrary pair of pullbacks -/

section Invariant

variable {U R : Scheme.{u}} {dU : DimensionFunction U} {dR : DimensionFunction R} {i : ℤ}

/-- The cycles on `U` which are invariant for a pair of maps `p q : Z_i(U) → Z_i(R)`, that is the
equalizer of `p` and `q`.  For the two flat pullbacks of a presentation groupoid this is the
Vistoli descent condition: a cycle on the atlas defines a cycle on the stack exactly when its two
pullbacks to the arrow scheme agree. -/
def invariantCycles (p q : cyclesOfDimension U dU i →ₗ[ℚ] cyclesOfDimension R dR i) :
    Submodule ℚ (cyclesOfDimension U dU i) :=
  LinearMap.ker (p - q)

/-- Membership in the invariant cycles is exactly the equality of the two pullbacks. -/
theorem mem_invariantCycles_iff
    {p q : cyclesOfDimension U dU i →ₗ[ℚ] cyclesOfDimension R dR i}
    {z : cyclesOfDimension U dU i} :
    z ∈ invariantCycles p q ↔ p z = q z := by
  rw [invariantCycles, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]

/-- If the two pullbacks coincide then every cycle is invariant. -/
theorem invariantCycles_self (p : cyclesOfDimension U dU i →ₗ[ℚ] cyclesOfDimension R dR i) :
    invariantCycles p p = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ mem_invariantCycles_iff.mpr rfl

end Invariant

/-! ## Presentation groupoids with open-immersion legs -/

/-- The scheme-level data of a presentation groupoid `R ⇉ U` of a stack by an atlas, in the range
in which the available flat-pullback theory applies: the source and target are open immersions of
relative dimension zero for the two certified dimension gradings.  Only the data of the two legs
is recorded; the groupoid unit, inverse and composition are not needed for the cycle groups below
and are constructed for genuine atlases in `Stacks/AtlasRefinement.lean`. -/
structure OpenPresentationGroupoid where
  /-- The atlas scheme `U`. -/
  base : Scheme.{u}
  /-- The arrow scheme `R = U ×_X U`. -/
  arrows : Scheme.{u}
  /-- The certified closure-dimension grading of the atlas. -/
  baseDim : DimensionFunction base
  /-- The certified closure-dimension grading of the arrow scheme. -/
  arrowsDim : DimensionFunction arrows
  /-- The source map `s : R ⟶ U` of the groupoid. -/
  src : arrows ⟶ base
  /-- The target map `t : R ⟶ U` of the groupoid. -/
  tgt : arrows ⟶ base
  /-- The source map is an open immersion; this is the case in which flat pullback of rational
  cycles is constructed. -/
  src_isOpenImmersion : _root_.AlgebraicGeometry.IsOpenImmersion src
  /-- The target map is an open immersion. -/
  tgt_isOpenImmersion : _root_.AlgebraicGeometry.IsOpenImmersion tgt
  /-- The source map has relative dimension zero for the two certified gradings. -/
  src_dim (r : arrows) : arrowsDim r = baseDim (src.base r)
  /-- The target map has relative dimension zero for the two certified gradings. -/
  tgt_dim (r : arrows) : arrowsDim r = baseDim (tgt.base r)

attribute [instance] OpenPresentationGroupoid.src_isOpenImmersion
attribute [instance] OpenPresentationGroupoid.tgt_isOpenImmersion

namespace OpenPresentationGroupoid

variable (G : OpenPresentationGroupoid.{u}) (i : ℤ)

/-- Flat pullback of dimension-graded rational cycles along the source map of the groupoid. -/
noncomputable def srcPullback :
    cyclesOfDimension G.base G.baseDim i →ₗ[ℚ]
      cyclesOfDimension G.arrows G.arrowsDim i :=
  cyclesOfDimension.flatPullbackOpen G.src G.src_dim

/-- Flat pullback of dimension-graded rational cycles along the target map of the groupoid. -/
noncomputable def tgtPullback :
    cyclesOfDimension G.base G.baseDim i →ₗ[ℚ]
      cyclesOfDimension G.arrows G.arrowsDim i :=
  cyclesOfDimension.flatPullbackOpen G.tgt G.tgt_dim

/-- Coefficients of the source pullback of a cycle. -/
@[simp]
theorem srcPullback_apply (z : cyclesOfDimension G.base G.baseDim i) (r : G.arrows) :
    ((G.srcPullback i z : cyclesOfDimension G.arrows G.arrowsDim i) :
        AlgebraicCycle G.arrows ℚ) r =
      (z : AlgebraicCycle G.base ℚ) (G.src.base r) :=
  rfl

/-- Coefficients of the target pullback of a cycle. -/
@[simp]
theorem tgtPullback_apply (z : cyclesOfDimension G.base G.baseDim i) (r : G.arrows) :
    ((G.tgtPullback i z : cyclesOfDimension G.arrows G.arrowsDim i) :
        AlgebraicCycle G.arrows ℚ) r =
      (z : AlgebraicCycle G.base ℚ) (G.tgt.base r) :=
  rfl

/-- **Vistoli cycles of the presentation.**  The dimension-`i` rational cycles on the atlas whose
two flat pullbacks to the arrow scheme agree. -/
noncomputable def cycles : Submodule ℚ (cyclesOfDimension G.base G.baseDim i) :=
  invariantCycles (G.srcPullback i) (G.tgtPullback i)

/-- **Pointwise description of the Vistoli cycles.**  A cycle descends exactly when its
coefficient function is constant along the point relation of the groupoid. -/
theorem mem_cycles_iff {z : cyclesOfDimension G.base G.baseDim i} :
    z ∈ G.cycles i ↔
      ∀ r : G.arrows,
        (z : AlgebraicCycle G.base ℚ) (G.src.base r) =
          (z : AlgebraicCycle G.base ℚ) (G.tgt.base r) := by
  rw [cycles, mem_invariantCycles_iff]
  constructor
  · intro h r
    have hr := congrArg
      (fun w : cyclesOfDimension G.arrows G.arrowsDim i ↦
        (w : AlgebraicCycle G.arrows ℚ) r) h
    simpa using hr
  · intro h
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.coe_injective
    funext r
    exact h r

/-- Rational equivalence on the atlas, restricted to the Vistoli cycles. -/
noncomputable def relations : Submodule ℚ (G.cycles i) :=
  Submodule.comap (G.cycles i).subtype
    (RationalEquivalenceSystem.canonical
      (X := G.base) (dimension := G.baseDim) (i := i)).relations

/-- **The Vistoli rational Chow group of the presentation** in dimension `i`: descent cycles on
the atlas modulo rational equivalence on the atlas. -/
noncomputable abbrev chow := G.cycles i ⧸ G.relations i

/-- The class of a Vistoli cycle in the Vistoli Chow group. -/
noncomputable abbrev quotientMap : G.cycles i →ₗ[ℚ] G.chow i :=
  (G.relations i).mkQ

/-- The Vistoli class of a cycle which is rationally equivalent to zero on the atlas
vanishes. -/
theorem quotientMap_eq_zero_of_mem_relations (z : G.cycles i)
    (hz : (z : cyclesOfDimension G.base G.baseDim i) ∈
      (RationalEquivalenceSystem.canonical
        (X := G.base) (dimension := G.baseDim) (i := i)).relations) :
    G.quotientMap i z = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hz

end OpenPresentationGroupoid

/-! ## The identity presentation of a scheme -/

/-- The identity presentation groupoid of a scheme: the atlas is the scheme itself and both legs
of the groupoid are the identity. -/
noncomputable def identityPresentation (X : Scheme.{u}) (dX : DimensionFunction X) :
    OpenPresentationGroupoid.{u} where
  base := X
  arrows := X
  baseDim := dX
  arrowsDim := dX
  src := 𝟙 X
  tgt := 𝟙 X
  src_isOpenImmersion := inferInstance
  tgt_isOpenImmersion := inferInstance
  src_dim _ := rfl
  tgt_dim _ := rfl

namespace OpenPresentationGroupoid

variable (G : OpenPresentationGroupoid.{u})

/-- When the two legs of the presentation coincide every cycle on the atlas descends. -/
theorem cycles_eq_top_of_src_eq_tgt (h : G.src = G.tgt) (i : ℤ) : G.cycles i = ⊤ :=
  eq_top_iff.mpr fun z _ ↦ (G.mem_cycles_iff i).mpr fun r ↦ by rw [h]

/-- The Vistoli cycles of a presentation with equal legs, identified with all cycles on the
atlas. -/
noncomputable def cyclesTopEquiv (h : G.src = G.tgt) (i : ℤ) :
    G.cycles i ≃ₗ[ℚ] cyclesOfDimension G.base G.baseDim i :=
  (LinearEquiv.ofEq _ _ (G.cycles_eq_top_of_src_eq_tgt h i)).trans Submodule.topEquiv

/-- The identification of Vistoli cycles with all cycles is the inclusion. -/
@[simp]
theorem cyclesTopEquiv_apply (h : G.src = G.tgt) (i : ℤ) (z : G.cycles i) :
    G.cyclesTopEquiv h i z = (z : cyclesOfDimension G.base G.baseDim i) :=
  rfl

/-- Under the identification of Vistoli cycles with all cycles, the Vistoli relations become the
rational equivalence relations of the atlas. -/
theorem map_relations_cyclesTopEquiv (h : G.src = G.tgt) (i : ℤ) :
    Submodule.map
        ((G.cyclesTopEquiv h i : G.cycles i ≃ₗ[ℚ] cyclesOfDimension G.base G.baseDim i) :
          G.cycles i →ₗ[ℚ] cyclesOfDimension G.base G.baseDim i)
        (G.relations i) =
      (RationalEquivalenceSystem.canonical
        (X := G.base) (dimension := G.baseDim) (i := i)).relations := by
  have hcoe :
      ((G.cyclesTopEquiv h i : G.cycles i ≃ₗ[ℚ] cyclesOfDimension G.base G.baseDim i) :
          G.cycles i →ₗ[ℚ] cyclesOfDimension G.base G.baseDim i) =
        (G.cycles i).subtype :=
    LinearMap.ext fun _ ↦ rfl
  rw [hcoe, relations]
  refine Submodule.map_comap_eq_of_surjective ?_ _
  intro z
  refine ⟨⟨z, ?_⟩, rfl⟩
  rw [G.cycles_eq_top_of_src_eq_tgt h i]
  trivial

/-- **A presentation with equal legs computes the scheme Chow group of its atlas.**  In
particular, for the identity presentation of a scheme the Vistoli construction returns the
dimension-graded rational Chow group of that scheme. -/
noncomputable def chowEquivSchemeChow (h : G.src = G.tgt) (i : ℤ) :
    G.chow i ≃ₗ[ℚ]
      (RationalEquivalenceSystem.canonical
        (X := G.base) (dimension := G.baseDim) (i := i)).ChowGroup :=
  Submodule.Quotient.equiv _ _ (G.cyclesTopEquiv h i) (G.map_relations_cyclesTopEquiv h i)

/-- The comparison with the scheme Chow group sends the Vistoli class of a cycle to its ordinary
rational-equivalence class. -/
@[simp]
theorem chowEquivSchemeChow_quotientMap (h : G.src = G.tgt) (i : ℤ) (z : G.cycles i) :
    G.chowEquivSchemeChow h i (G.quotientMap i z) =
      (RationalEquivalenceSystem.canonical
        (X := G.base) (dimension := G.baseDim) (i := i)).quotientMap
        (z : cyclesOfDimension G.base G.baseDim i) :=
  rfl

end OpenPresentationGroupoid

/-- **The Vistoli Chow group of a scheme with its identity atlas is its scheme Chow group.** -/
noncomputable def identityPresentationChowEquiv (X : Scheme.{u}) (dX : DimensionFunction X)
    (i : ℤ) :
    (identityPresentation X dX).chow i ≃ₗ[ℚ]
      (RationalEquivalenceSystem.canonical (X := X) (dimension := dX) (i := i)).ChowGroup :=
  (identityPresentation X dX).chowEquivSchemeChow rfl i

/-! ## Refinements of presentations and independence of the atlas -/

namespace OpenPresentationGroupoid

/-- A refinement of presentation groupoids.  The atlas map `U' ⟶ U` is an open immersion of
relative dimension zero, so rational cycles pull back along it, and it is intertwined with the two
legs by a map of arrow schemes.  For genuine atlases this is the scheme-level shadow of
`StackTwoPullback.RefinementGroupoid.refinementGroupoidMap`. -/
structure Refinement (H G : OpenPresentationGroupoid.{u}) where
  /-- The map of atlas schemes. -/
  onBase : H.base ⟶ G.base
  /-- The compatible map of arrow schemes. -/
  onArrows : H.arrows ⟶ G.arrows
  /-- The atlas map is an open immersion, so rational cycles pull back along it. -/
  onBase_isOpenImmersion : _root_.AlgebraicGeometry.IsOpenImmersion onBase
  /-- The atlas map has relative dimension zero for the two certified gradings. -/
  onBase_dim (u : H.base) : H.baseDim u = G.baseDim (onBase.base u)
  /-- The map of arrow schemes intertwines the two source maps. -/
  src_comm : onArrows ≫ G.src = H.src ≫ onBase
  /-- The map of arrow schemes intertwines the two target maps. -/
  tgt_comm : onArrows ≫ G.tgt = H.tgt ≫ onBase

attribute [instance] Refinement.onBase_isOpenImmersion

namespace Refinement

variable {K H G : OpenPresentationGroupoid.{u}} {i : ℤ}

/-- Every presentation refines itself. -/
def id (G : OpenPresentationGroupoid.{u}) : G.Refinement G where
  onBase := 𝟙 G.base
  onArrows := 𝟙 G.arrows
  onBase_isOpenImmersion := inferInstance
  onBase_dim _ := rfl
  src_comm := by simp
  tgt_comm := by simp

/-- Refinements compose: if `K` refines `H` and `H` refines `G` then `K` refines `G`. -/
noncomputable def trans (g : K.Refinement H) (f : H.Refinement G) : K.Refinement G where
  onBase := g.onBase ≫ f.onBase
  onArrows := g.onArrows ≫ f.onArrows
  onBase_isOpenImmersion := inferInstance
  onBase_dim u := by
    rw [g.onBase_dim u, f.onBase_dim (g.onBase.base u),
      _root_.AlgebraicGeometry.Scheme.Hom.comp_apply]
  src_comm := by
    rw [Category.assoc, f.src_comm, ← Category.assoc, g.src_comm, Category.assoc]
  tgt_comm := by
    rw [Category.assoc, f.tgt_comm, ← Category.assoc, g.tgt_comm, Category.assoc]

/-- Flat pullback of all dimension-graded rational cycles along the atlas map of a refinement. -/
noncomputable def onSchemeCycles (f : H.Refinement G) (i : ℤ) :
    cyclesOfDimension G.base G.baseDim i →ₗ[ℚ] cyclesOfDimension H.base H.baseDim i :=
  cyclesOfDimension.flatPullbackOpen f.onBase f.onBase_dim

/-- Coefficients of the pullback of a cycle along a refinement. -/
@[simp]
theorem onSchemeCycles_apply (f : H.Refinement G) (i : ℤ)
    (z : cyclesOfDimension G.base G.baseDim i) (u : H.base) :
    ((f.onSchemeCycles i z : cyclesOfDimension H.base H.baseDim i) :
        AlgebraicCycle H.base ℚ) u =
      (z : AlgebraicCycle G.base ℚ) (f.onBase.base u) :=
  rfl

/-- **A refinement pulls Vistoli cycles back to Vistoli cycles.**  The two intertwining equations
carry the descent condition on the coarse presentation to the descent condition on the fine
one. -/
theorem mem_cycles (f : H.Refinement G) (i : ℤ) :
    ∀ z ∈ G.cycles i, f.onSchemeCycles i z ∈ H.cycles i := by
  intro z hz
  refine (H.mem_cycles_iff i).mpr fun r ↦ ?_
  have hsrc : f.onBase.base (H.src.base r) = G.src.base (f.onArrows.base r) := by
    rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply,
      ← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, f.src_comm]
  have htgt : f.onBase.base (H.tgt.base r) = G.tgt.base (f.onArrows.base r) := by
    rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply,
      ← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, f.tgt_comm]
  rw [onSchemeCycles_apply, onSchemeCycles_apply, hsrc, htgt]
  exact (G.mem_cycles_iff i).mp hz (f.onArrows.base r)

/-- **The map on Vistoli cycles induced by a refinement of presentations.** -/
noncomputable def onCycles (f : H.Refinement G) (i : ℤ) : G.cycles i →ₗ[ℚ] H.cycles i :=
  LinearMap.restrict (f.onSchemeCycles i) (f.mem_cycles i)

/-- Coefficients of the Vistoli cycle induced by a refinement. -/
@[simp]
theorem onCycles_apply (f : H.Refinement G) (i : ℤ) (z : G.cycles i) (u : H.base) :
    (((f.onCycles i z : H.cycles i) : cyclesOfDimension H.base H.baseDim i) :
        AlgebraicCycle H.base ℚ) u =
      ((z : cyclesOfDimension G.base G.baseDim i) : AlgebraicCycle G.base ℚ)
        (f.onBase.base u) :=
  rfl

/-- Vistoli cycles agree as soon as all their coefficients agree. -/
theorem cycles_ext {z w : H.cycles i}
    (h : ∀ u : H.base,
      ((z : cyclesOfDimension H.base H.baseDim i) : AlgebraicCycle H.base ℚ) u =
        ((w : cyclesOfDimension H.base H.baseDim i) : AlgebraicCycle H.base ℚ) u) :
    z = w := by
  apply Subtype.ext
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext u
  exact h u

/-- The identity refinement induces the identity on Vistoli cycles. -/
@[simp]
theorem onCycles_id (G : OpenPresentationGroupoid.{u}) (i : ℤ) :
    (Refinement.id G).onCycles i = LinearMap.id :=
  LinearMap.ext fun _ ↦ cycles_ext fun _ ↦ rfl

/-- Composition of refinements induces composition of the maps on Vistoli cycles. -/
@[simp]
theorem onCycles_trans (g : K.Refinement H) (f : H.Refinement G) (i : ℤ) :
    (g.trans f).onCycles i = (g.onCycles i).comp (f.onCycles i) := by
  apply LinearMap.ext
  intro z
  refine cycles_ext fun u ↦ ?_
  change ((z : cyclesOfDimension G.base G.baseDim i) : AlgebraicCycle G.base ℚ)
      ((g.onBase ≫ f.onBase).base u) = _
  rw [_root_.AlgebraicGeometry.Scheme.Hom.comp_apply]
  rfl

/-- **A refinement preserves rational equivalence on the atlas.**  This is the open-immersion
flat-pullback descent theorem of `ChowGroupLocalization.lean`. -/
theorem mapsRelations (f : H.Refinement G) (i : ℤ) :
    G.relations i ≤ Submodule.comap (f.onCycles i) (H.relations i) := by
  intro z hz
  exact (RationalEquivalenceSystem.DescendingMap.ofOpenImmersion
    (RationalEquivalenceSystem.canonical
      (X := G.base) (dimension := G.baseDim) (i := i))
    f.onBase f.onBase_dim
    (RationalEquivalenceSystem.canonical
      (X := H.base) (dimension := H.baseDim) (i := i))).maps_relations hz

/-- **The map on Vistoli rational Chow groups induced by a refinement of presentations.** -/
noncomputable def chowMap (f : H.Refinement G) (i : ℤ) : G.chow i →ₗ[ℚ] H.chow i :=
  Submodule.mapQ _ _ (f.onCycles i) (f.mapsRelations i)

/-- The induced map on Chow groups is computed by the induced map on Vistoli cycles. -/
@[simp]
theorem chowMap_quotientMap (f : H.Refinement G) (i : ℤ) (z : G.cycles i) :
    f.chowMap i (G.quotientMap i z) = H.quotientMap i (f.onCycles i z) :=
  rfl

/-- The identity refinement induces the identity on Vistoli Chow groups. -/
@[simp]
theorem chowMap_id (G : OpenPresentationGroupoid.{u}) (i : ℤ) :
    (Refinement.id G).chowMap i = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨z⟩
  change G.quotientMap i ((Refinement.id G).onCycles i z) = G.quotientMap i z
  rw [onCycles_id]
  rfl

/-- Composition of refinements induces composition of the maps on Vistoli Chow groups. -/
@[simp]
theorem chowMap_trans (g : K.Refinement H) (f : H.Refinement G) (i : ℤ) :
    (g.trans f).chowMap i = (g.chowMap i).comp (f.chowMap i) := by
  apply LinearMap.ext
  rintro ⟨z⟩
  change K.quotientMap i ((g.trans f).onCycles i z) = _
  rw [onCycles_trans]
  rfl

/-- Two mutually inverse refinements induce mutually inverse maps on Vistoli cycles. -/
theorem onCycles_comp_onCycles (f : H.Refinement G) (g : G.Refinement H)
    (h : f.onBase ≫ g.onBase = 𝟙 H.base) (i : ℤ) :
    (f.onCycles i).comp (g.onCycles i) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  refine cycles_ext fun u ↦ ?_
  change ((z : cyclesOfDimension H.base H.baseDim i) : AlgebraicCycle H.base ℚ)
      (g.onBase.base (f.onBase.base u)) = _
  rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, h]
  rfl

/-- **An invertible refinement induces an isomorphism of Vistoli rational Chow groups.**  This is
the form of independence of the presentation which the available flat-pullback theory proves. -/
noncomputable def chowEquiv (f : H.Refinement G) (g : G.Refinement H)
    (hfg : f.onBase ≫ g.onBase = 𝟙 H.base) (hgf : g.onBase ≫ f.onBase = 𝟙 G.base) (i : ℤ) :
    G.chow i ≃ₗ[ℚ] H.chow i := by
  refine LinearEquiv.ofLinearMap (f.chowMap i) (g.chowMap i) ?_ ?_
  · apply LinearMap.ext
    rintro ⟨z⟩
    change H.quotientMap i ((f.onCycles i) ((g.onCycles i) z)) = _
    have hz := congrArg (fun m : H.cycles i →ₗ[ℚ] H.cycles i ↦ m z)
      (onCycles_comp_onCycles f g hfg i)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hz
    rw [hz]
    rfl
  · apply LinearMap.ext
    rintro ⟨z⟩
    change G.quotientMap i ((g.onCycles i) ((f.onCycles i) z)) = _
    have hz := congrArg (fun m : G.cycles i →ₗ[ℚ] G.cycles i ↦ m z)
      (onCycles_comp_onCycles g f hgf i)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hz
    rw [hz]
    rfl

end Refinement

end OpenPresentationGroupoid

/-- **Two presentations with a common refinement are canonically comparable.**  Each presentation
maps to the Vistoli Chow group of the common refinement.  These maps are not proved to be
isomorphisms: see the module docstring for the exact missing input. -/
noncomputable def commonRefinementComparison {K G₁ G₂ : OpenPresentationGroupoid.{u}}
    (f₁ : K.Refinement G₁) (f₂ : K.Refinement G₂) (i : ℤ) :
    (G₁.chow i →ₗ[ℚ] K.chow i) × (G₂.chow i →ₗ[ℚ] K.chow i) :=
  (f₁.chowMap i, f₂.chowMap i)

/-- The first comparison map of a common refinement is the map induced by the first leg. -/
@[simp]
theorem commonRefinementComparison_fst {K G₁ G₂ : OpenPresentationGroupoid.{u}}
    (f₁ : K.Refinement G₁) (f₂ : K.Refinement G₂) (i : ℤ) :
    (commonRefinementComparison f₁ f₂ i).1 = f₁.chowMap i :=
  rfl

/-- The second comparison map of a common refinement is the map induced by the second leg. -/
@[simp]
theorem commonRefinementComparison_snd {K G₁ G₂ : OpenPresentationGroupoid.{u}}
    (f₁ : K.Refinement G₁) (f₂ : K.Refinement G₂) (i : ℤ) :
    (commonRefinementComparison f₁ f₂ i).2 = f₂.chowMap i :=
  rfl

/-- **Two presentations with an invertible common refinement have isomorphic Vistoli Chow
groups.** -/
noncomputable def commonRefinementEquiv {K G₁ G₂ : OpenPresentationGroupoid.{u}}
    (f₁ : K.Refinement G₁) (g₁ : G₁.Refinement K) (f₂ : K.Refinement G₂)
    (g₂ : G₂.Refinement K)
    (h₁ : f₁.onBase ≫ g₁.onBase = 𝟙 K.base) (h₁' : g₁.onBase ≫ f₁.onBase = 𝟙 G₁.base)
    (h₂ : f₂.onBase ≫ g₂.onBase = 𝟙 K.base) (h₂' : g₂.onBase ≫ f₂.onBase = 𝟙 G₂.base)
    (i : ℤ) :
    G₁.chow i ≃ₗ[ℚ] G₂.chow i :=
  (f₁.chowEquiv g₁ h₁ h₁' i).trans (f₂.chowEquiv g₂ h₂ h₂' i).symm

/-! ## Stabilizer weights -/

/-- The rational stabilizer weight of a point whose stabilizer has order `n`.  This is the
normalization which forces the first stack Chow theory to be rational rather than integral. -/
def stabilizerWeight (n : ℕ) : ℚ :=
  (n : ℚ)⁻¹

/-- The stabilizer weight of a stabilizer of order `n` is `1/n`. -/
@[simp]
theorem stabilizerWeight_eq_one_div (n : ℕ) : stabilizerWeight n = 1 / (n : ℚ) := by
  rw [stabilizerWeight, one_div]

/-- A trivial stabilizer carries weight one, so the theory restricts to the usual one on
schemes. -/
@[simp]
theorem stabilizerWeight_one : stabilizerWeight 1 = 1 := by
  rw [stabilizerWeight, Nat.cast_one, inv_one]

/-- A nontrivial finite stabilizer carries a strictly positive weight. -/
theorem stabilizerWeight_pos {n : ℕ} (hn : 0 < n) : 0 < stabilizerWeight n := by
  rw [stabilizerWeight, inv_pos]
  exact_mod_cast hn

/-- **Multiplying by the order of the stabilizer removes the stack weight.** -/
theorem cast_mul_stabilizerWeight {n : ℕ} (hn : n ≠ 0) :
    (n : ℚ) * stabilizerWeight n = 1 := by
  rw [stabilizerWeight]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn)

/-- The stabilizer weight of an object of a groupoid: the reciprocal of the number of its
automorphisms.  Applied to an object of `PresentationGroupoid f T` this is `1/|Aut|` for the
automorphism group of its image in the base stack. -/
noncomputable def autWeight {C : Type*} [Category* C] (a : C) : ℚ :=
  stabilizerWeight (Nat.card (a ⟶ a))

/-- Objects with bijective automorphism sets have the same stabilizer weight. -/
theorem autWeight_eq_of_equiv {C D : Type*} [Category* C] [Category* D] {a : C} {b : D}
    (e : (a ⟶ a) ≃ (b ⟶ b)) : autWeight a = autWeight b := by
  rw [autWeight, autWeight, Nat.card_congr e]

/-- An object with no nontrivial automorphisms has weight one. -/
theorem autWeight_eq_one {C : Type*} [Category* C] (a : C) [Subsingleton (a ⟶ a)] :
    autWeight a = 1 := by
  have hcard : Nat.card (a ⟶ a) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨𝟙 a⟩⟩
  rw [autWeight, hcard, stabilizerWeight_one]

/-- An object whose automorphisms are in bijection with a finite group `Γ` has weight
`1/|Γ|`. -/
theorem autWeight_eq_of_group_equiv {C : Type*} [Category* C] (a : C)
    (Γ : Type*) [Group Γ] [Fintype Γ] (e : (a ⟶ a) ≃ Γ) :
    autWeight a = 1 / (Fintype.card Γ : ℚ) := by
  rw [autWeight, Nat.card_congr e, Nat.card_eq_fintype_card, stabilizerWeight_eq_one_div]

section Presentation

variable {X U : FppfStack.{u}} {f : StackHom U X} {T : Scheme.{u}}

/-- **The stabilizer weight of a point of a presentation groupoid is `1/|Aut|` computed in the
base stack.**  No stabilizer arrow is lost by passing to the atlas. -/
theorem autWeight_presentationGroupoid (a : PresentationGroupoid f T) :
    autWeight a =
      stabilizerWeight (Nat.card (Aut ((f.appFunctor T).obj (PresentationGroupoid.back a)))) := by
  rw [autWeight, Nat.card_congr (PresentationGroupoid.autEquiv f a)]

/-- **Stabilizer weights are unchanged by refinement of atlases.**  Conjugation by the refinement
2-cell is a bijection of automorphism groups. -/
theorem autWeight_refinementFunctor {W : FppfStack.{u}} {w : StackHom W X}
    (q : StackHom W U) (e : StackIso2 (Pseudofunctor.StrongTrans.vcomp q f) w)
    (a : PresentationGroupoid w T) :
    autWeight ((PresentationGroupoid.refinementFunctor (f := f) q e T).obj a) = autWeight a :=
  (autWeight_eq_of_equiv (PresentationGroupoid.refinementArrowEquiv q e T a a)).symm

end Presentation

/-! ## The stabilizer-weighted degree of a zero-cycle -/

/-- The stabilizer-weighted degree of a zero-dimensional rational cycle on an atlas, summed over
a finite set containing its support.  Each coefficient is multiplied by the stabilizer weight of
its point, which is the `1/|Aut|` normalization of Vistoli's theory. -/
noncomputable def weightedDegree {U : Scheme.{u}} (dU : DimensionFunction U)
    (order : U → ℕ) (z : cyclesOfDimension U dU 0) (S : Finset U) : ℚ :=
  ∑ x ∈ S, (z : AlgebraicCycle U ℚ) x * stabilizerWeight (order x)

/-- **The weighted degree does not depend on the finite set used to compute it**, provided the set
contains the support of the cycle. -/
theorem weightedDegree_eq_of_support_subset {U : Scheme.{u}} (dU : DimensionFunction U)
    (order : U → ℕ) (z : cyclesOfDimension U dU 0) (S S' : Finset U)
    (hS : ∀ x, (z : AlgebraicCycle U ℚ) x ≠ 0 → x ∈ S)
    (hS' : ∀ x, (z : AlgebraicCycle U ℚ) x ≠ 0 → x ∈ S') :
    weightedDegree dU order z S = weightedDegree dU order z S' := by
  classical
  have hleft : ∑ x ∈ S ∩ S', (z : AlgebraicCycle U ℚ) x * stabilizerWeight (order x) =
      ∑ x ∈ S, (z : AlgebraicCycle U ℚ) x * stabilizerWeight (order x) := by
    refine Finset.sum_subset Finset.inter_subset_left fun x hx hxn ↦ ?_
    have hzero : (z : AlgebraicCycle U ℚ) x = 0 := by
      by_contra hne
      exact hxn (Finset.mem_inter.mpr ⟨hx, hS' x hne⟩)
    rw [hzero, zero_mul]
  have hright : ∑ x ∈ S ∩ S', (z : AlgebraicCycle U ℚ) x * stabilizerWeight (order x) =
      ∑ x ∈ S', (z : AlgebraicCycle U ℚ) x * stabilizerWeight (order x) := by
    refine Finset.sum_subset Finset.inter_subset_right fun x hx hxn ↦ ?_
    have hzero : (z : AlgebraicCycle U ℚ) x = 0 := by
      by_contra hne
      exact hxn (Finset.mem_inter.mpr ⟨hS x hne, hx⟩)
    rw [hzero, zero_mul]
  rw [weightedDegree, weightedDegree, ← hleft, hright]

/-- The weighted degree is additive in the cycle. -/
theorem weightedDegree_add {U : Scheme.{u}} (dU : DimensionFunction U)
    (order : U → ℕ) (z w : cyclesOfDimension U dU 0) (S : Finset U) :
    weightedDegree dU order (z + w) S =
      weightedDegree dU order z S + weightedDegree dU order w S := by
  rw [weightedDegree, weightedDegree, weightedDegree, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  change ((z : AlgebraicCycle U ℚ) x + (w : AlgebraicCycle U ℚ) x) * _ = _
  ring

/-- The weighted degree of the zero cycle vanishes. -/
@[simp]
theorem weightedDegree_zero {U : Scheme.{u}} (dU : DimensionFunction U)
    (order : U → ℕ) (S : Finset U) :
    weightedDegree dU order (0 : cyclesOfDimension U dU 0) S = 0 := by
  rw [weightedDegree]
  exact Finset.sum_eq_zero fun x _ ↦ by change (0 : ℚ) * _ = 0; rw [zero_mul]

/-! ## The one-point presentation and the degree of the fundamental class of `BΓ` -/

/-- The one-point presentation groupoid whose atlas is the spectrum of a field.  For a
classifying stack `BΓ` the arrow scheme is `Γ × Spec k` with both legs equal to the projection;
that projection is finite etale and not an open immersion, so it is replaced here by the
identity groupoid, which imposes the same (vacuous) descent condition because the two legs of a
trivial action coincide. -/
noncomputable def pointPresentation (k : Type u) [Field k] : OpenPresentationGroupoid.{u} :=
  identityPresentation (_root_.AlgebraicGeometry.Spec (.of k)) (DimensionFunction.specField k)

/-- Every cycle on a presentation whose two legs agree descends, whatever the pullback along the
legs is.  This is the reason the one-point presentation above computes the same cycle group as the
groupoid `Γ × Spec k ⇉ Spec k` of `BΓ`. -/
theorem invariantCycles_eq_top_of_eq {U R : Scheme.{u}} {dU : DimensionFunction U}
    {dR : DimensionFunction R} {i : ℤ}
    (p q : cyclesOfDimension U dU i →ₗ[ℚ] cyclesOfDimension R dR i) (h : p = q) :
    invariantCycles p q = ⊤ := by
  rw [h]
  exact invariantCycles_self q

/-- Every cycle on an atlas with a single point descends. -/
theorem OpenPresentationGroupoid.cycles_eq_top_of_subsingleton
    (G : OpenPresentationGroupoid.{u}) [Subsingleton G.base] (i : ℤ) : G.cycles i = ⊤ :=
  eq_top_iff.mpr fun z _ ↦ (G.mem_cycles_iff i).mpr fun r ↦ by
    rw [Subsingleton.elim (G.src.base r) (G.tgt.base r)]

/-- The fundamental Vistoli cycle of the one-point presentation: the unique point with
coefficient one. -/
noncomputable def pointFundamentalCycle (k : Type u) [Field k] :
    (pointPresentation k).cycles 0 :=
  ⟨PointChow.fundamentalCycle k, by
    rw [(pointPresentation k).cycles_eq_top_of_src_eq_tgt rfl 0]
    trivial⟩

/-- The fundamental Vistoli class of the one-point presentation. -/
noncomputable def pointFundamentalClass (k : Type u) [Field k] :
    (pointPresentation k).chow 0 :=
  (pointPresentation k).quotientMap 0 (pointFundamentalCycle k)

/-- **The degree map of the one-point presentation with constant stabilizer order `n`.**  It is
the scheme degree of the class on the atlas, weighted by `1/n`. -/
noncomputable def pointDegree (k : Type u) [Field k] (n : ℕ) :
    (pointPresentation k).chow 0 →ₗ[ℚ] ℚ :=
  (LinearMap.lsmul ℚ ℚ (stabilizerWeight n)).comp
    ((PointChow.chowEquivRat k).toLinearMap.comp
      ((pointPresentation k).chowEquivSchemeChow rfl 0).toLinearMap)

/-- **`deg [BΓ] = 1/|Γ|`.**  The degree of the fundamental class of the one-point presentation
whose stabilizer group is a finite group `Γ` is `1/|Γ|`.  `BΓ` itself is not yet available as a
Deligne--Mumford stack, so the statement is made for the atlas data `Spec k` with constant
stabilizer group `Γ` which such a presentation supplies. -/
theorem pointDegree_pointFundamentalClass (k : Type u) [Field k]
    (Γ : Type*) [Group Γ] [Fintype Γ] :
    pointDegree k (Fintype.card Γ) (pointFundamentalClass k) = 1 / (Fintype.card Γ : ℚ) := by
  have hone : (PointChow.chowEquivRat k)
      (((pointPresentation k).chowEquivSchemeChow rfl 0) (pointFundamentalClass k)) = 1 :=
    PointChow.fundamentalClass_degree_one k
  change stabilizerWeight (Fintype.card Γ) •
    ((PointChow.chowEquivRat k)
      (((pointPresentation k).chowEquivSchemeChow rfl 0) (pointFundamentalClass k))) = _
  rw [hone, smul_eq_mul, mul_one, stabilizerWeight_eq_one_div]

/-- **The stack degree of the fundamental class of `BΓ` is nonzero and becomes one after
multiplication by the order of the stabilizer.** -/
theorem card_mul_pointDegree_pointFundamentalClass (k : Type u) [Field k]
    (Γ : Type*) [Group Γ] [Fintype Γ] :
    (Fintype.card Γ : ℚ) * pointDegree k (Fintype.card Γ) (pointFundamentalClass k) = 1 := by
  rw [pointDegree_pointFundamentalClass k Γ, ← stabilizerWeight_eq_one_div]
  exact cast_mul_stabilizerWeight Fintype.card_ne_zero

/-- **The same degree computed by the weighted sum over the atlas.** -/
theorem weightedDegree_fundamentalCycle (k : Type u) [Field k]
    (Γ : Type*) [Group Γ] [Fintype Γ] :
    weightedDegree (DimensionFunction.specField k) (fun _ ↦ Fintype.card Γ)
        (PointChow.fundamentalCycle k) {default} = 1 / (Fintype.card Γ : ℚ) := by
  rw [weightedDegree, Finset.sum_singleton, PointChow.fundamentalCycle_apply, one_mul,
    stabilizerWeight_eq_one_div]

/-- **The atlas degree of the fundamental class weighted by a genuine stack stabilizer.**  The
stabilizer order is read off from an object of a presentation groupoid, so the weight is the
`1/|Aut|` of the corresponding point of the base stack. -/
theorem weightedDegree_fundamentalCycle_eq_autWeight (k : Type u) [Field k]
    {X U : FppfStack.{u}} {f : StackHom U X} {T : Scheme.{u}}
    (a : PresentationGroupoid f T) :
    weightedDegree (DimensionFunction.specField k) (fun _ ↦ Nat.card (a ⟶ a))
        (PointChow.fundamentalCycle k) {default} = autWeight a := by
  rw [weightedDegree, Finset.sum_singleton, PointChow.fundamentalCycle_apply, one_mul, autWeight]

/-- **The atlas degree of the fundamental class of `BΓ` expressed through the stabilizer of an
object of a presentation groupoid.**  If the automorphism group of the atlas object in the base
stack is the finite group `Γ`, the stabilizer-weighted degree of the fundamental cycle is
`1/|Γ|`. -/
theorem weightedDegree_fundamentalCycle_of_autEquiv (k : Type u) [Field k]
    {X U : FppfStack.{u}} {f : StackHom U X} {T : Scheme.{u}}
    (a : PresentationGroupoid f T) (Γ : Type*) [Group Γ] [Fintype Γ] (e : (a ⟶ a) ≃ Γ) :
    weightedDegree (DimensionFunction.specField k) (fun _ ↦ Nat.card (a ⟶ a))
        (PointChow.fundamentalCycle k) {default} = 1 / (Fintype.card Γ : ℚ) := by
  rw [weightedDegree_fundamentalCycle_eq_autWeight k a, autWeight_eq_of_group_equiv a Γ e]

end GromovWitten.AlgebraicGeometry.IntersectionTheory
