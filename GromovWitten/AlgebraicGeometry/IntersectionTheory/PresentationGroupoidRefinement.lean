/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroupLocalization

/-!
# A generic refinement API for presentation-groupoid Vistoli cycle data

`OpenPresentationGroupoid` (`StackChowVistoli.lean`) and `EtalePresentationGroupoid`
(`EtalePullback.lean`) both package a scheme `base` with an atlas-dimension grading, an arrow
scheme with two legs `src, tgt`, a submodule of "Vistoli" (descent) cycles on `base` for each
dimension `i` characterised pointwise by `mem_cycles_iff`, and the quotient of that submodule by
rational equivalence on `base`.  Both then support the *same* notion of refinement (an atlas
comparison map which is an open immersion, intertwined with the arrow schemes) with the *same*
proofs: nothing in the refinement layer ever uses that the legs `src`/`tgt` are open immersions
(for `OpenPresentationGroupoid`) or merely etale (for `EtalePresentationGroupoid`), only that
`onBase` is an open immersion and that `mem_cycles_iff` holds.

This file factors that common layer out **once**, as `PresentationGroupoidData` (the shared shape:
`base`, `arrows`, `baseDim`, `src`, `tgt`, `cycles`, `mem_cycles_iff`, with `relations`/`chow`/
`quotientMap` derived generically from `base`/`baseDim`/`cycles` alone) and its `Refinement` API
(`id`, `trans`, `onSchemeCycles`, `mem_cycles`, `onCycles`, `mapsRelations`, `chowMap`, `chowEquiv`,
`commonRefinementComparison`, `commonRefinementEquiv`, plus the supporting simp lemmas
`onSchemeCycles_apply`, `onCycles_apply`, `cycles_ext`, `onCycles_id`, `onCycles_trans`,
`chowMap_quotientMap`, `chowMap_id`, `chowMap_trans`, `onCycles_comp_onCycles`).
`StackChowVistoli.lean` and `EtaleAtlasRefinement.lean` each supply a `toData` packaging
(`OpenPresentationGroupoid.toData`, `EtalePresentationGroupoid.toData`) and re-export the public
names (`Refinement`, `id`, `trans`, `onSchemeCycles`, `mem_cycles`, `onCycles`, `mapsRelations`,
`chowMap`, `chowMap_id`, `chowMap_trans`, `chowEquiv`, `commonRefinementComparison`,
`commonRefinementEquiv`) as thin wrappers with the stated types of the concrete groupoids
(`G.chow i`, not `G.toData.chow i`); the auxiliary lemmas (`onSchemeCycles_apply`,
`onCycles_apply`, `cycles_ext`, `onCycles_id`, `onCycles_trans`, `chowMap_quotientMap`,
`onCycles_comp_onCycles`, `commonRefinementComparison_fst`/`_snd`) exist only in the generic
namespace `PresentationGroupoidData.Refinement` and are reached through dot notation.

This file must not import `StackChowVistoli.lean` or `EtalePullback.lean`: both of those import
*it*, so importing either back would be a cycle.
-/

open CategoryTheory Order

attribute [local instance] specializationOrder

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-- The shared shape of a presentation-groupoid's Vistoli cycle data: an atlas `base` with a
certified dimension grading, an arrow scheme `arrows` with two legs `src`, `tgt`, the submodule of
descent (Vistoli) cycles `cycles i` for each dimension `i`, and its pointwise characterisation
`mem_cycles_iff`.  This is exactly the data the refinement API below needs; it says nothing about
how `cycles` was constructed (open-immersion or etale flat pullback) or about `src`/`tgt`
themselves, only that a descent cycle's coefficient function is constant along the point relation
`r ↦ (src r, tgt r)`. -/
structure PresentationGroupoidData where
  /-- The atlas scheme. -/
  base : Scheme.{u}
  /-- The arrow scheme. -/
  arrows : Scheme.{u}
  /-- The certified closure-dimension grading of the atlas. -/
  baseDim : DimensionFunction base
  /-- The source map of the groupoid. -/
  src : arrows ⟶ base
  /-- The target map of the groupoid. -/
  tgt : arrows ⟶ base
  /-- The dimension-`i` Vistoli (descent) cycles on the atlas. -/
  cycles (i : ℤ) : Submodule ℚ (cyclesOfDimension base baseDim i)
  /-- A cycle descends exactly when its coefficient function is constant along the point relation
  of the groupoid. -/
  mem_cycles_iff (i : ℤ) {z : cyclesOfDimension base baseDim i} :
    z ∈ cycles i ↔
      ∀ r : arrows,
        (z : AlgebraicCycle base ℚ) (src.base r) = (z : AlgebraicCycle base ℚ) (tgt.base r)

namespace PresentationGroupoidData

variable (D : PresentationGroupoidData.{u}) (i : ℤ)

/-- Rational equivalence on the atlas, restricted to the Vistoli cycles. -/
noncomputable def relations : Submodule ℚ (D.cycles i) :=
  Submodule.comap (D.cycles i).subtype
    (RationalEquivalenceSystem.canonical
      (X := D.base) (dimension := D.baseDim) (i := i)).relations

/-- **The Vistoli rational Chow group** in dimension `i`: descent cycles on the atlas modulo
rational equivalence on the atlas. -/
noncomputable abbrev chow := D.cycles i ⧸ D.relations i

/-- The class of a Vistoli cycle in the Vistoli Chow group. -/
noncomputable abbrev quotientMap : D.cycles i →ₗ[ℚ] D.chow i :=
  (D.relations i).mkQ

/-- A refinement of presentation-groupoid data.  The atlas map `H.base ⟶ G.base` is an open
immersion of relative dimension zero, so rational cycles pull back along it, and it is intertwined
with the two legs of `H` and `G` by a map of arrow schemes. -/
structure Refinement (H G : PresentationGroupoidData.{u}) where
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

variable {K H G : PresentationGroupoidData.{u}} {i : ℤ}

/-- Every presentation refines itself. -/
def id (G : PresentationGroupoidData.{u}) : G.Refinement G where
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
theorem onCycles_id (G : PresentationGroupoidData.{u}) (i : ℤ) :
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
flat-pullback descent theorem of `ChowGroupLocalization.lean`; it is the only place any geometric
input beyond the abstract `PresentationGroupoidData` shape is used. -/
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
theorem chowMap_id (G : PresentationGroupoidData.{u}) (i : ℤ) :
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
the form of independence of the presentation which the available flat-pullback theory proves: the
atlas comparison map `onBase` must have a two-sided inverse which is again a refinement map. -/
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

/-- **Two presentations with a common refinement are canonically comparable.**  Each presentation
maps to the Vistoli Chow group of the common refinement.  These maps are not proved to be
isomorphisms in general: see the module docstrings of `StackChowVistoli.lean`/
`EtaleAtlasRefinement.lean` for the exact missing input. -/
noncomputable def commonRefinementComparison {K G₁ G₂ : PresentationGroupoidData.{u}}
    (f₁ : K.Refinement G₁) (f₂ : K.Refinement G₂) (i : ℤ) :
    (G₁.chow i →ₗ[ℚ] K.chow i) × (G₂.chow i →ₗ[ℚ] K.chow i) :=
  (f₁.chowMap i, f₂.chowMap i)

/-- The first comparison map of a common refinement is the map induced by the first leg. -/
@[simp]
theorem commonRefinementComparison_fst {K G₁ G₂ : PresentationGroupoidData.{u}}
    (f₁ : K.Refinement G₁) (f₂ : K.Refinement G₂) (i : ℤ) :
    (commonRefinementComparison f₁ f₂ i).1 = f₁.chowMap i :=
  rfl

/-- The second comparison map of a common refinement is the map induced by the second leg. -/
@[simp]
theorem commonRefinementComparison_snd {K G₁ G₂ : PresentationGroupoidData.{u}}
    (f₁ : K.Refinement G₁) (f₂ : K.Refinement G₂) (i : ℤ) :
    (commonRefinementComparison f₁ f₂ i).2 = f₂.chowMap i :=
  rfl

/-- **Two presentations with an invertible common refinement have isomorphic Vistoli Chow
groups.** -/
noncomputable def commonRefinementEquiv {K G₁ G₂ : PresentationGroupoidData.{u}}
    (f₁ : K.Refinement G₁) (g₁ : G₁.Refinement K) (f₂ : K.Refinement G₂)
    (g₂ : G₂.Refinement K)
    (h₁ : f₁.onBase ≫ g₁.onBase = 𝟙 K.base) (h₁' : g₁.onBase ≫ f₁.onBase = 𝟙 G₁.base)
    (h₂ : f₂.onBase ≫ g₂.onBase = 𝟙 K.base) (h₂' : g₂.onBase ≫ f₂.onBase = 𝟙 G₂.base)
    (i : ℤ) :
    G₁.chow i ≃ₗ[ℚ] G₂.chow i :=
  (f₁.chowEquiv g₁ h₁ h₁' i).trans (f₂.chowEquiv g₂ h₂ h₂' i).symm

end PresentationGroupoidData

end GromovWitten.AlgebraicGeometry.IntersectionTheory
