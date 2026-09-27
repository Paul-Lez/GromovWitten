/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.EtalePullback
import GromovWitten.AlgebraicGeometry.IntersectionTheory.PresentationGroupoidRefinement
import GromovWitten.AlgebraicGeometry.Stacks.EtaleSliceLocalSlicing

/-!
# Refinement of etale presentation groupoids and Chow-group comparisons

This file instantiates the refinement API of `OpenPresentationGroupoid`
(`IntersectionTheory/StackChowVistoli.lean`) for `EtalePresentationGroupoid`
(`IntersectionTheory/EtalePullback.lean`): the two legs `src, tgt : arrows ⟶ base` of the source
and target groupoids are only required to be *etale*, but the refinement map
`onBase : H.base ⟶ G.base` comparing a fine presentation `H` to a coarse one `G` is still required
to be an *open immersion*.  This is exactly the range in which descent of rational equivalence is
available (`RationalEquivalenceSystem.DescendingMap.ofOpenImmersion`, `ChowGroupLocalization.lean`).

Every proof of the refinement layer is shared, **once**, with `OpenPresentationGroupoid`: both
structures package the same shape of data (an atlas, an arrow scheme, two legs, the Vistoli
cycles for each dimension and their pointwise description `mem_cycles_iff`) as
`PresentationGroupoidData` (`PresentationGroupoidRefinement.lean`), and the whole refinement API
(`Refinement`, `id`, `trans`, `onSchemeCycles`, `mem_cycles`, `onCycles`, `mapsRelations`,
`chowMap`, `chowMap_id`, `chowMap_trans`, `chowEquiv`, `commonRefinementComparison`,
`commonRefinementEquiv`) is proved there against that abstract shape — it only ever uses `onBase`
being an open immersion and `mem_cycles_iff`, never the etaleness (or openness) of
`G.src`/`G.tgt`/`H.src`/`H.tgt`.  The declarations below (`EtalePresentationGroupoid.toData`,
`.Refinement`, `.Refinement.chowMap`, ...) are thin wrappers around the generic ones with the
stated types of the concrete groupoids (`G.chow i`, not `G.toData.chow i`); the auxiliary lemmas
live only in the generic namespace `PresentationGroupoidData.Refinement`.

## Main declarations

* `EtalePresentationGroupoid.Refinement H G`, a refinement of a coarse presentation `G` by a
  finer one `H`: an open immersion `onBase : H.base ⟶ G.base` of relative dimension zero together
  with a compatible map `onArrows : H.arrows ⟶ G.arrows` of arrow schemes.
* `Refinement.id`, `Refinement.trans`: refinements form a category (reflexivity and transitivity).
* `Refinement.onSchemeCycles`, `Refinement.mem_cycles`, `Refinement.onCycles`: a refinement pulls
  Vistoli (descent) cycles back to Vistoli cycles.
* `Refinement.mapsRelations`, `Refinement.chowMap`: a refinement preserves rational equivalence on
  the atlas (via `DescendingMap.ofOpenImmersion`, the *only* geometric input used here) and hence
  induces a linear map of Vistoli Chow groups `G.chow i →ₗ[ℚ] H.chow i`.
* `Refinement.chowEquiv`, `commonRefinementEquiv`: an *invertible* refinement (mutually inverse
  atlas maps) induces a linear equivalence of Chow groups, and two presentations with a common
  invertible refinement have isomorphic Chow groups.
* `DeligneMumfordStack.etalePresentationSwap`, `DeligneMumfordStack.vistoliChowSwapEquiv`: the
  refinement API instantiated on a genuine Deligne–Mumford stack `X`.  Exchanging which projection
  of the self-overlap `R = U ×_X U` of the chosen etale atlas is called `src` and which is called
  `tgt` produces another `EtalePresentationGroupoid` for the *same* atlas `U`, related to the
  original one by the identity open immersion on `U` together with the scheme-level groupoid
  inverse `StackChart.selfOverlapInv` on `R`; this refinement is invertible (both ways, by the same
  underlying map), so `chowEquiv` gives a canonical linear equivalence of the two Vistoli Chow
  groups of `X`.

## What is not proved here, and why

Genuine atlas independence — comparing `X.vistoliChow` for the *chosen* etale atlas `U` to the
Vistoli Chow group of a **strictly smaller** open `V ⊊ U` that is still an etale-surjective atlas
of `X` — is not proved, and cannot be obtained from `chowEquiv`/`commonRefinementEquiv` as ported
here.  Structurally, `chowEquiv` only ever certifies a linear equivalence when the two atlas
schemes are related by a *pair of mutually inverse* open immersions, i.e. when the atlas map itself
is an isomorphism; a proper open subscheme `V ⊊ U` admits no morphism back from `U`, so no such
pair exists.  This matches the module docstring of `StackChowVistoli.lean`: proving that the
comparison map of an *arbitrary* refinement is an isomorphism needs the exactness of the descent
sequence `0 → A(X) → A(U) ⇉ A(R)` for the smooth surjection `U → X`, which needs flat/etale
pullback along `U → X` itself and the surjectivity of flat pullback along a smooth cover — both
unavailable (the same gap already recorded there and in `EtalePullback.lean`).  No descent of
rational equivalence along an etale (non-open) map is attempted either, per the same gap recorded
in `EtalePullback.lean`.  The `DeligneMumfordStack.etalePresentationSwap` comparison sidesteps this
entirely: it identifies two presentations of the *same* atlas scheme `U`, so its refinement map
`onBase` is literally the identity, which is invertible for free.
-/

open CategoryTheory Order

attribute [local instance] specializationOrder

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace EtalePresentationGroupoid

/-- The data of an etale presentation groupoid packaged for the generic refinement API of
`PresentationGroupoidRefinement.lean`: the same atlas, arrow scheme, legs, Vistoli cycles and
their pointwise characterisation, forgetting only that the legs happen to be etale (which the
refinement layer never uses). -/
noncomputable def toData (G : EtalePresentationGroupoid.{u}) : PresentationGroupoidData.{u} where
  base := G.base
  arrows := G.arrows
  baseDim := G.baseDim
  src := G.src
  tgt := G.tgt
  cycles := G.cycles
  mem_cycles_iff := G.mem_cycles_iff

/-- A refinement of etale presentation groupoids: the generic `PresentationGroupoidData.Refinement`
(`PresentationGroupoidRefinement.lean`) applied to the underlying data `toData`.  The atlas map
`onBase : H.base ⟶ G.base` is an open immersion of relative dimension zero (the two legs of `H`
and `G` are only etale), intertwined with the two legs by a map `onArrows` of arrow schemes; see
`PresentationGroupoidData.Refinement` for the field list and every proof, which is shared
verbatim with `OpenPresentationGroupoid.Refinement` (`StackChowVistoli.lean`). -/
abbrev Refinement (H G : EtalePresentationGroupoid.{u}) :=
  PresentationGroupoidData.Refinement H.toData G.toData

namespace Refinement

variable {K H G : EtalePresentationGroupoid.{u}} {i : ℤ}

/-- Every presentation refines itself. -/
noncomputable def id (G : EtalePresentationGroupoid.{u}) : G.Refinement G :=
  PresentationGroupoidData.Refinement.id G.toData

/-- Refinements compose: if `K` refines `H` and `H` refines `G` then `K` refines `G`. -/
noncomputable def trans (g : K.Refinement H) (f : H.Refinement G) : K.Refinement G :=
  PresentationGroupoidData.Refinement.trans g f

/-- Flat pullback of all dimension-graded rational cycles along the atlas map of a refinement. -/
noncomputable def onSchemeCycles (f : H.Refinement G) (i : ℤ) :
    cyclesOfDimension G.base G.baseDim i →ₗ[ℚ] cyclesOfDimension H.base H.baseDim i :=
  PresentationGroupoidData.Refinement.onSchemeCycles f i

/-- **A refinement pulls Vistoli cycles back to Vistoli cycles.** -/
theorem mem_cycles (f : H.Refinement G) (i : ℤ) :
    ∀ z ∈ G.cycles i, f.onSchemeCycles i z ∈ H.cycles i :=
  PresentationGroupoidData.Refinement.mem_cycles f i

/-- **The map on Vistoli cycles induced by a refinement of presentations.** -/
noncomputable def onCycles (f : H.Refinement G) (i : ℤ) : G.cycles i →ₗ[ℚ] H.cycles i :=
  PresentationGroupoidData.Refinement.onCycles f i

/-- **A refinement preserves rational equivalence on the atlas.** -/
theorem mapsRelations (f : H.Refinement G) (i : ℤ) :
    G.relations i ≤ Submodule.comap (f.onCycles i) (H.relations i) :=
  PresentationGroupoidData.Refinement.mapsRelations f i

/-- **The map on Vistoli rational Chow groups induced by a refinement of presentations.** -/
noncomputable def chowMap (f : H.Refinement G) (i : ℤ) : G.chow i →ₗ[ℚ] H.chow i :=
  PresentationGroupoidData.Refinement.chowMap f i

/-- The identity refinement induces the identity on Vistoli Chow groups. -/
theorem chowMap_id (G : EtalePresentationGroupoid.{u}) (i : ℤ) :
    (Refinement.id G).chowMap i = LinearMap.id :=
  PresentationGroupoidData.Refinement.chowMap_id G.toData i

/-- Composition of refinements induces composition of the maps on Vistoli Chow groups. -/
theorem chowMap_trans (g : K.Refinement H) (f : H.Refinement G) (i : ℤ) :
    (g.trans f).chowMap i = (g.chowMap i).comp (f.chowMap i) :=
  PresentationGroupoidData.Refinement.chowMap_trans g f i

/-- **An invertible refinement induces an isomorphism of Vistoli rational Chow groups.** -/
noncomputable def chowEquiv (f : H.Refinement G) (g : G.Refinement H)
    (hfg : f.onBase ≫ g.onBase = 𝟙 H.base) (hgf : g.onBase ≫ f.onBase = 𝟙 G.base) (i : ℤ) :
    G.chow i ≃ₗ[ℚ] H.chow i :=
  PresentationGroupoidData.Refinement.chowEquiv f g hfg hgf i

end Refinement

/-- **Two presentations with a common refinement are canonically comparable.**  Each presentation
maps to the Vistoli Chow group of the common refinement.  These maps are not proved to be
isomorphisms in general: see the module docstring for the exact missing input. -/
noncomputable def commonRefinementComparison {K G₁ G₂ : EtalePresentationGroupoid.{u}}
    (f₁ : K.Refinement G₁) (f₂ : K.Refinement G₂) (i : ℤ) :
    (G₁.chow i →ₗ[ℚ] K.chow i) × (G₂.chow i →ₗ[ℚ] K.chow i) :=
  PresentationGroupoidData.commonRefinementComparison f₁ f₂ i

/-- **Two presentations with an invertible common refinement have isomorphic Vistoli Chow
groups.** -/
noncomputable def commonRefinementEquiv {K G₁ G₂ : EtalePresentationGroupoid.{u}}
    (f₁ : K.Refinement G₁) (g₁ : G₁.Refinement K) (f₂ : K.Refinement G₂)
    (g₂ : G₂.Refinement K)
    (h₁ : f₁.onBase ≫ g₁.onBase = 𝟙 K.base) (h₁' : g₁.onBase ≫ f₁.onBase = 𝟙 G₁.base)
    (h₂ : f₂.onBase ≫ g₂.onBase = 𝟙 K.base) (h₂' : g₂.onBase ≫ f₂.onBase = 𝟙 G₂.base)
    (i : ℤ) :
    G₁.chow i ≃ₗ[ℚ] G₂.chow i :=
  PresentationGroupoidData.commonRefinementEquiv f₁ g₁ f₂ g₂ h₁ h₁' h₂ h₂' i

end EtalePresentationGroupoid

end GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## Instantiation on a genuine Deligne-Mumford stack -/

namespace GromovWitten.AlgebraicGeometry

namespace DeligneMumfordStack

variable (X : DeligneMumfordStack.{u})

/-- **The self-overlap presentation groupoid of the chosen etale atlas with its two legs
exchanged.**  Same atlas scheme, same arrow scheme, same certified dimension gradings as
`etalePresentation`; only the roles of `src` and `tgt` are swapped, using the *other* projection
of the self-overlap as the source.  Whenever `(baseDim, arrowsDim, hsrc, htgt)` are valid data for
`X.etalePresentation`, the swapped roles `(baseDim, arrowsDim, htgt, hsrc)` are valid data for
this presentation. -/
noncomputable def etalePresentationSwap
    (baseDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlas.scheme)
    (arrowsDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlasSelfOverlap.space)
    (hsrc : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.fst.base r))
    (htgt : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.snd.base r)) :
    IntersectionTheory.EtalePresentationGroupoid.{u} where
  base := X.chosenEtaleAtlas.scheme
  arrows := X.chosenEtaleAtlasSelfOverlap.space
  baseDim := baseDim
  arrowsDim := arrowsDim
  src := X.chosenEtaleAtlasSelfOverlap.snd
  tgt := X.chosenEtaleAtlasSelfOverlap.fst
  src_etale := X.chosenEtaleAtlasSelfOverlap_snd_etale
  tgt_etale := X.chosenEtaleAtlasSelfOverlap_fst_etale
  src_dim := htgt
  tgt_dim := hsrc

/-- **The canonical refinement of the chosen etale presentation by its own leg-swap.**  The atlas
map is the identity on `U = X.chosenEtaleAtlas.scheme` (certainly an open immersion of relative
dimension zero) and the map of arrow schemes is the scheme-level groupoid inverse
`StackChart.selfOverlapInv` of the self-overlap `R = U ×_X U`, which exchanges its two
projections. -/
noncomputable def etalePresentationSwapRefinement
    (baseDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlas.scheme)
    (arrowsDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlasSelfOverlap.space)
    (hsrc : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.fst.base r))
    (htgt : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.snd.base r)) :
    (X.etalePresentationSwap baseDim arrowsDim hsrc htgt).Refinement
      (X.etalePresentation baseDim arrowsDim hsrc htgt) where
  onBase := 𝟙 _
  onArrows := X.chosenEtaleAtlas.selfOverlapInv X.chosenEtaleAtlasSelfOverlap
  onBase_isOpenImmersion :=
    (inferInstance : _root_.AlgebraicGeometry.IsOpenImmersion (𝟙 X.chosenEtaleAtlas.scheme))
  onBase_dim _ := rfl
  src_comm := by
    change X.chosenEtaleAtlas.selfOverlapInv X.chosenEtaleAtlasSelfOverlap ≫
        X.chosenEtaleAtlasSelfOverlap.fst =
      X.chosenEtaleAtlasSelfOverlap.snd ≫ 𝟙 X.chosenEtaleAtlas.scheme
    rw [Category.comp_id]
    exact X.chosenEtaleAtlas.selfOverlapInv_fst X.chosenEtaleAtlasSelfOverlap
  tgt_comm := by
    change X.chosenEtaleAtlas.selfOverlapInv X.chosenEtaleAtlasSelfOverlap ≫
        X.chosenEtaleAtlasSelfOverlap.snd =
      X.chosenEtaleAtlasSelfOverlap.fst ≫ 𝟙 X.chosenEtaleAtlas.scheme
    rw [Category.comp_id]
    exact X.chosenEtaleAtlas.selfOverlapInv_snd X.chosenEtaleAtlasSelfOverlap

/-- **The reverse refinement, of the chosen etale presentation by its own leg-swap.**  The same
identity atlas map and the same scheme-level swap `StackChart.selfOverlapInv`, in the opposite
direction: `selfOverlapInv` exchanges the two projections either way round. -/
noncomputable def etalePresentationSwapRefinement'
    (baseDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlas.scheme)
    (arrowsDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlasSelfOverlap.space)
    (hsrc : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.fst.base r))
    (htgt : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.snd.base r)) :
    (X.etalePresentation baseDim arrowsDim hsrc htgt).Refinement
      (X.etalePresentationSwap baseDim arrowsDim hsrc htgt) where
  onBase := 𝟙 _
  onArrows := X.chosenEtaleAtlas.selfOverlapInv X.chosenEtaleAtlasSelfOverlap
  onBase_isOpenImmersion :=
    (inferInstance : _root_.AlgebraicGeometry.IsOpenImmersion (𝟙 X.chosenEtaleAtlas.scheme))
  onBase_dim _ := rfl
  src_comm := by
    change X.chosenEtaleAtlas.selfOverlapInv X.chosenEtaleAtlasSelfOverlap ≫
        X.chosenEtaleAtlasSelfOverlap.snd =
      X.chosenEtaleAtlasSelfOverlap.fst ≫ 𝟙 X.chosenEtaleAtlas.scheme
    rw [Category.comp_id]
    exact X.chosenEtaleAtlas.selfOverlapInv_snd X.chosenEtaleAtlasSelfOverlap
  tgt_comm := by
    change X.chosenEtaleAtlas.selfOverlapInv X.chosenEtaleAtlasSelfOverlap ≫
        X.chosenEtaleAtlasSelfOverlap.fst =
      X.chosenEtaleAtlasSelfOverlap.snd ≫ 𝟙 X.chosenEtaleAtlas.scheme
    rw [Category.comp_id]
    exact X.chosenEtaleAtlas.selfOverlapInv_fst X.chosenEtaleAtlasSelfOverlap

/-- **The first atlas-independence theorem of #47 for a genuine Deligne–Mumford stack.**
Exchanging the two legs of the presentation groupoid of the chosen etale atlas is an invertible
refinement of the presentation by itself (`etalePresentationSwapRefinement` both ways, via the
identity atlas map), so it induces a canonical linear equivalence of the two Vistoli Chow groups.
Both `vistoliChow` and its swap compute honest invariants of the *same* atlas `U`; the module
docstring explains why comparing `vistoliChow` to the Vistoli Chow group of a genuinely different,
strictly smaller atlas is not attempted. -/
noncomputable def vistoliChowSwapEquiv
    (baseDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlas.scheme)
    (arrowsDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlasSelfOverlap.space)
    (hsrc : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.fst.base r))
    (htgt : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.snd.base r))
    (i : ℤ) :
    X.vistoliChow baseDim arrowsDim hsrc htgt i ≃ₗ[ℚ]
      (X.etalePresentationSwap baseDim arrowsDim hsrc htgt).chow i :=
  (X.etalePresentationSwapRefinement baseDim arrowsDim hsrc htgt).chowEquiv
    (X.etalePresentationSwapRefinement' baseDim arrowsDim hsrc htgt)
    (show (𝟙 X.chosenEtaleAtlas.scheme) ≫ 𝟙 X.chosenEtaleAtlas.scheme = 𝟙 X.chosenEtaleAtlas.scheme
      from Category.comp_id _)
    (show (𝟙 X.chosenEtaleAtlas.scheme) ≫ 𝟙 X.chosenEtaleAtlas.scheme = 𝟙 X.chosenEtaleAtlas.scheme
      from Category.comp_id _) i

end DeligneMumfordStack

end GromovWitten.AlgebraicGeometry
