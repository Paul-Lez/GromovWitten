/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.VistoliRelations
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperPushforwardChow
import GromovWitten.AlgebraicGeometry.Stacks.OverlapSwap
import GromovWitten.AlgebraicGeometry.Stacks.EtaleAtlasDiagonal
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChartGroupoid
import GromovWitten.AlgebraicGeometry.Stacks.DiagonalPresentationTransport

/-!
# Atlas independence of the Vistoli Chow group of a Deligne–Mumford stack

**Atlas independence (GitHub issue #47).** Let `k` be a field. For two étale surjective,
representably quasi-compact charts `A B : StackChart X` of an fppf stack `X`, whose schemes are
compact and locally of finite type over `k`, the genuine Vistoli rational Chow groups computed
from `A` and from `B` are isomorphic. As a corollary, for a Deligne–Mumford stack `𝒳` the Vistoli
Chow group is independent of the choice of such an étale atlas (in particular of the internally
chosen one, `𝒳.chosenEtaleAtlas`).

The proof assembles three pieces:

* `MoritaMap.ofArrowIso` (blueprint D.2.5): an isomorphism `θ` of arrow schemes over a common
  isomorphism `e` of base schemes, compatible with source/target and dimension functions, and
  admitting units, produces a `MoritaMap`.
* `EtalePresentationGroupoid.good_of_locallyOfFiniteType`: a generic sufficient condition for
  `Good` (compactness plus local finite type over `k`).
* `StackChart.commonRefinement`: the common scheme-level refinement `P` of two étale surjective
  charts `A B`, with its two legs étale, surjective and quasi-compact.

combined with task D1's `StackChart.etaleGroupoid`/`isomGroupoid`/`moritaToChart`
(`ChartGroupoid.lean`) and task D2's `StackChart.isomSchemeIso`
(`DiagonalPresentationTransport.lean`) into the chain of three `MoritaMap.vistoliChowEquiv`s
described in blueprint §D.3.

## Main definitions and results

* `MoritaMap.ofArrowIso`: a `MoritaMap` from an isomorphism of arrow schemes over a shared base.
* `EtalePresentationGroupoid.good_of_locallyOfFiniteType`: a sufficient condition for `Good`.
* `StackChart.commonRefinement`: the common refinement scheme of two étale surjective charts.
* `StackChart.vistoliChowEquivOfEtaleCharts` (**Theorem D**): atlas independence for two étale
  surjective charts.
* `DeligneMumfordStack.vistoliChowEquivOfChart` (**Corollary D**): atlas independence for a
  Deligne–Mumford stack, comparing the chosen atlas with any other chart.
* `DeligneMumfordStack.chosenEtaleAtlas_etaleGroupoid_eq`: the new chart groupoid of the chosen
  atlas is literally (by `rfl`) the old `DeligneMumfordStack.etalePresentation` groupoid.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## (D.2.5) Morita map from an isomorphism of arrow schemes over a shared base -/

variable {H G : EtalePresentationGroupoid.{u}}

/-- **Morita map of an isomorphism of groupoids over a common isomorphism of bases.**
Given an isomorphism `e` of the base schemes and an isomorphism `θ` of the arrow schemes
commuting with source and target (via `e`), agreeing dimension functions, and a "unit" self-arrow
at every point of `H.base` along which the two legs of `H` induce the same residue field map,
`e.hom` and `θ.hom` form a `MoritaMap H G`. Applied with `e := Iso.refl P` this proves two
`EtalePresentationGroupoid`s with literally the same base and isomorphic arrow schemes (over the
identity) have equivalent Vistoli Chow groups. -/
noncomputable def MoritaMap.ofArrowIso (e : H.base ≅ G.base) (θ : H.arrows ≅ G.arrows)
    (hsrc : θ.hom ≫ G.src = H.src ≫ e.hom) (htgt : θ.hom ≫ G.tgt = H.tgt ≫ e.hom)
    (hdim : ∀ u : H.base, H.baseDim u = G.baseDim (e.hom.base u))
    (hunit : ∀ u : H.base, ∃ (r : H.arrows) (hs : H.src.base r = u) (ht : H.tgt.base r = u),
      H.src.residueFieldMap r =
        (H.base.residueFieldCongr (hs.trans ht.symm)).hom ≫ H.tgt.residueFieldMap r) :
    MoritaMap H G where
  onBase := e.hom
  onArrows := θ.hom
  onBase_etale := inferInstance
  onBase_dim := hdim
  src_comm := hsrc
  tgt_comm := htgt
  onBase_surjective := e.hom.surjective
  exists_arrow_over_identity u' v' huv := by
    have hinj : u' = v' := e.hom.homeomorph.injective huv
    subst hinj
    obtain ⟨r, hs, ht, hres⟩ := hunit u'
    have hb : e.hom.base (H.src.base r) = e.hom.base (H.tgt.base r) := by rw [hs, ht]
    refine ⟨r, hb, hs, ht, ?_⟩
    change (H.src ≫ e.hom).residueFieldMap r =
        (G.base.residueFieldCongr hb).hom ≫ (H.tgt ≫ e.hom).residueFieldMap r
    rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp, hres,
      ← Category.assoc, Scheme.Hom.residueFieldMap_congr' (hs.trans ht.symm), Category.assoc]
  residue_descent u' a _ := by
    have : IsIso (e.hom.residueFieldMap u') := inferInstance
    obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.residueFieldMap u')).2 a
    exact ⟨b, hb⟩
  full r u' v' hu hv := by
    have hcancel : θ.hom.base (θ.inv.base r) = r := by
      change (θ.inv ≫ θ.hom).base r = r
      rw [θ.inv_hom_id]
      rfl
    refine ⟨θ.inv.base r, ?_, ?_, hcancel⟩
    · have hbase :
          e.hom.base (H.src.base (θ.inv.base r)) = G.src.base (θ.hom.base (θ.inv.base r)) := by
        change (H.src ≫ e.hom).base (θ.inv.base r) = (θ.hom ≫ G.src).base (θ.inv.base r)
        rw [hsrc]
      rw [hcancel] at hbase
      exact e.hom.homeomorph.injective (hbase.trans hu.symm)
    · have hbase :
          e.hom.base (H.tgt.base (θ.inv.base r)) = G.tgt.base (θ.hom.base (θ.inv.base r)) := by
        change (H.tgt ≫ e.hom).base (θ.inv.base r) = (θ.hom ≫ G.tgt).base (θ.inv.base r)
        rw [htgt]
      rw [hcancel] at hbase
      exact e.hom.homeomorph.injective (hbase.trans hv.symm)

/-! ## `Good` from compactness and local finite type over a field -/

/-- **A sufficient condition for `Good`.** If the base and arrow schemes of an étale
presentation groupoid are compact, and both admit a structure map to `Spec k` locally of finite
type, the groupoid satisfies the standing hypotheses of the Vistoli Chow group: local
Noetherianity is `LocallyOfFiniteType.isLocallyNoetherian`, and `CovByDimension` for the
(arbitrary) certified dimension functions `G.baseDim`/`G.arrowsDim` follows from
`covByDimension_of_locallyOfFiniteType`, since any two certified dimension functions of the same
scheme agree. -/
theorem EtalePresentationGroupoid.good_of_locallyOfFiniteType {k : Type u} [Field k]
    {G : EtalePresentationGroupoid.{u}} [CompactSpace G.base] [CompactSpace G.arrows]
    (sBase : G.base ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sBase]
    (sArrows : G.arrows ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sArrows] :
    G.Good where
  compactSpace_base := ‹_›
  compactSpace_arrows := ‹_›
  isLocallyNoetherian_base := LocallyOfFiniteType.isLocallyNoetherian sBase
  isLocallyNoetherian_arrows := LocallyOfFiniteType.isLocallyNoetherian sArrows
  covByDimension_base := covByDimension_of_locallyOfFiniteType sBase G.baseDim
  covByDimension_arrows := covByDimension_of_locallyOfFiniteType sArrows G.arrowsDim

end GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace GromovWitten.AlgebraicGeometry

open IntersectionTheory IntersectionTheory.FiniteTypeDimension
  IntersectionTheory.ProperPushforwardDivisor

namespace StackChart

variable {X : FppfStack.{u}}

/-! ## The common refinement of two étale surjective charts -/

/-- **The common scheme-level refinement of two étale surjective charts.** A scheme `P`
representing the base change of `A` by the tautological object of `B`, chosen from `B`'s
representability clause applied to `A`'s tautological object. -/
noncomputable def commonRefinement (A B : StackChart X) (hB : B.IsEtaleSurjective) :
    B.PullbackPresentation A.scheme A.tautObj :=
  Classical.choice (hB.1 A.scheme A.tautObj)

/-- The first projection `P ⟶ A.scheme` of the common refinement is étale, directly from `B`'s
étale-surjectivity clause. -/
theorem commonRefinement_fst_etale (A B : StackChart X) (hB : B.IsEtaleSurjective) :
    _root_.AlgebraicGeometry.Etale (commonRefinement A B hB).fst :=
  (hB.2 A.scheme A.tautObj (commonRefinement A B hB)).1

/-- The first projection `P ⟶ A.scheme` of the common refinement is surjective. -/
theorem commonRefinement_fst_surjective (A B : StackChart X) (hB : B.IsEtaleSurjective) :
    _root_.AlgebraicGeometry.Surjective (commonRefinement A B hB).fst :=
  (hB.2 A.scheme A.tautObj (commonRefinement A B hB)).2

/-- The first projection `P ⟶ A.scheme` of the common refinement is quasi-compact, from `B`'s
representable quasi-compactness clause. -/
theorem commonRefinement_fst_quasiCompact (A B : StackChart X) (hB : B.IsEtaleSurjective)
    (hBq : B.HasRepresentableProperty @_root_.AlgebraicGeometry.QuasiCompact) :
    _root_.AlgebraicGeometry.QuasiCompact (commonRefinement A B hB).fst :=
  hBq.2 A.scheme A.tautObj (commonRefinement A B hB)

/-- The second projection `P ⟶ B.scheme` of the common refinement is étale: the leg-swapped
presentation is an `A`-presentation of `B`'s tautological object, to which `A`'s
étale-surjectivity clause applies. -/
theorem commonRefinement_snd_etale (A B : StackChart X) (hA : A.IsEtaleSurjective)
    (hB : B.IsEtaleSurjective) :
    _root_.AlgebraicGeometry.Etale (commonRefinement A B hB).snd :=
  (hA.2 B.scheme B.tautObj (PullbackPresentation.swap B A (commonRefinement A B hB))).1

/-- The second projection `P ⟶ B.scheme` of the common refinement is surjective. -/
theorem commonRefinement_snd_surjective (A B : StackChart X) (hA : A.IsEtaleSurjective)
    (hB : B.IsEtaleSurjective) :
    _root_.AlgebraicGeometry.Surjective (commonRefinement A B hB).snd :=
  (hA.2 B.scheme B.tautObj (PullbackPresentation.swap B A (commonRefinement A B hB))).2

/-- The second projection `P ⟶ B.scheme` of the common refinement is quasi-compact, from `A`'s
representable quasi-compactness clause applied to the leg-swapped presentation. -/
theorem commonRefinement_snd_quasiCompact (A B : StackChart X) (hB : B.IsEtaleSurjective)
    (hAq : A.HasRepresentableProperty @_root_.AlgebraicGeometry.QuasiCompact) :
    _root_.AlgebraicGeometry.QuasiCompact (commonRefinement A B hB).snd :=
  hAq.2 B.scheme B.tautObj (PullbackPresentation.swap B A (commonRefinement A B hB))

/-! ## Theorem D: atlas independence for two étale surjective charts -/

variable {k : Type u} [Field k]

/-- **Theorem D (atlas independence).** For two étale surjective, representably quasi-compact
charts `A B` of an fppf stack `X` with compact schemes locally of finite type over a field `k`,
the genuine Vistoli rational Chow groups computed from `A` and from `B` are isomorphic. The proof
goes through the common refinement `P := (commonRefinement A B hB).space`: a Morita map from the
Isom groupoid of `A` over `P` to the chart groupoid of `A` (`StackChart.moritaToChart`), an
isomorphism of the two Isom groupoids over `P` (`MoritaMap.ofArrowIso`, fed by
`StackChart.isomSchemeIso`), and a Morita map from the Isom groupoid of `B` over `P` to the chart
groupoid of `B`. -/
noncomputable def vistoliChowEquivOfEtaleCharts (A B : StackChart X)
    (hA : A.IsEtaleSurjective) (hB : B.IsEtaleSurjective)
    (hAq : A.HasRepresentableProperty @_root_.AlgebraicGeometry.QuasiCompact)
    (hBq : B.HasRepresentableProperty @_root_.AlgebraicGeometry.QuasiCompact)
    [CompactSpace A.scheme] [CompactSpace B.scheme]
    (sA : A.scheme ⟶ Spec (CommRingCat.of k)) (sB : B.scheme ⟶ Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType sA]
    [_root_.AlgebraicGeometry.LocallyOfFiniteType sB] (i : ℤ) :
    A.vistoliChow hA sA i ≃ₗ[ℚ] B.vistoliChow hB sB i := by
  classical
  have hA' := A.isRepresentable_of_isEtaleSurjective hA
  have hB' := B.isRepresentable_of_isEtaleSurjective hB
  set p := commonRefinement A B hB with hp_def
  have hpf_etale : _root_.AlgebraicGeometry.Etale p.fst := commonRefinement_fst_etale A B hB
  have hpf_surj : _root_.AlgebraicGeometry.Surjective p.fst :=
    commonRefinement_fst_surjective A B hB
  have hpf_qc : _root_.AlgebraicGeometry.QuasiCompact p.fst :=
    commonRefinement_fst_quasiCompact A B hB hBq
  have hps_etale : _root_.AlgebraicGeometry.Etale p.snd :=
    commonRefinement_snd_etale A B hA hB
  have hps_surj : _root_.AlgebraicGeometry.Surjective p.snd :=
    commonRefinement_snd_surjective A B hA hB
  have hps_qc : _root_.AlgebraicGeometry.QuasiCompact p.snd :=
    commonRefinement_snd_quasiCompact A B hB hAq
  have hP_compact : CompactSpace p.space :=
    _root_.AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace p.fst
  -- `Good` for the two chart groupoids
  have hAE_good : (A.etaleGroupoid hA sA).Good := by
    have h1 : _root_.AlgebraicGeometry.Etale (A.selfOverlapScheme hA').fst :=
      A.selfOverlapScheme_fst_etale hA' hA
    have h2 : _root_.AlgebraicGeometry.QuasiCompact (A.selfOverlapScheme hA').fst :=
      A.selfOverlapScheme_fst_quasiCompact hA' hAq
    have h3 : CompactSpace (A.selfOverlapScheme hA').space :=
      _root_.AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
        (A.selfOverlapScheme hA').fst
    exact EtalePresentationGroupoid.good_of_locallyOfFiniteType sA
      ((A.selfOverlapScheme hA').fst ≫ sA)
  have hBE_good : (B.etaleGroupoid hB sB).Good := by
    have h1 : _root_.AlgebraicGeometry.Etale (B.selfOverlapScheme hB').fst :=
      B.selfOverlapScheme_fst_etale hB' hB
    have h2 : _root_.AlgebraicGeometry.QuasiCompact (B.selfOverlapScheme hB').fst :=
      B.selfOverlapScheme_fst_quasiCompact hB' hBq
    have h3 : CompactSpace (B.selfOverlapScheme hB').space :=
      _root_.AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
        (B.selfOverlapScheme hB').fst
    exact EtalePresentationGroupoid.good_of_locallyOfFiniteType sB
      ((B.selfOverlapScheme hB').fst ≫ sB)
  -- `Good` for the two Isom groupoids over `P`
  have hAI_good : (A.isomGroupoid hA p.fst sA).Good := by
    have hse : _root_.AlgebraicGeometry.Etale (A.isomSrc hA p.fst) := A.isomSrc_etale hA p.fst
    have hsq : _root_.AlgebraicGeometry.QuasiCompact (A.isomSrc hA p.fst) :=
      A.isomSrc_quasiCompact hA p.fst hAq
    have h1 : CompactSpace (A.isomArrows hA p.fst) :=
      _root_.AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
        (A.isomSrc hA p.fst)
    exact EtalePresentationGroupoid.good_of_locallyOfFiniteType (p.fst ≫ sA)
      (A.isomSrc hA p.fst ≫ p.fst ≫ sA)
  have hBI_good : (B.isomGroupoid hB p.snd sB).Good := by
    have hse : _root_.AlgebraicGeometry.Etale (B.isomSrc hB p.snd) := B.isomSrc_etale hB p.snd
    have hsq : _root_.AlgebraicGeometry.QuasiCompact (B.isomSrc hB p.snd) :=
      B.isomSrc_quasiCompact hB p.snd hBq
    have h1 : CompactSpace (B.isomArrows hB p.snd) :=
      _root_.AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
        (B.isomSrc hB p.snd)
    exact EtalePresentationGroupoid.good_of_locallyOfFiniteType (p.snd ≫ sB)
      (B.isomSrc hB p.snd ≫ p.snd ≫ sB)
  -- the isomorphism of the two Isom groupoids over `P`
  let θ := StackChart.isomSchemeIso hA' hB' p
  have hsrc : θ.hom ≫ B.isomSrc hB p.snd = A.isomSrc hA p.fst :=
    StackChart.isomSchemeIso_hom_map_assoc hA' hB' p prod.fst
  have htgt : θ.hom ≫ B.isomTgt hB p.snd = A.isomTgt hA p.fst :=
    StackChart.isomSchemeIso_hom_map_assoc hA' hB' p prod.snd
  have hdim_eq : dimensionFunction (p.fst ≫ sA) = dimensionFunction (p.snd ≫ sB) :=
    dimensionFunction_eq _ _
  have hdim : ∀ u : p.space, dimensionFunction (p.fst ≫ sA) u =
      dimensionFunction (p.snd ≫ sB) u :=
    fun u ↦ congrArg (fun d : DimensionFunction p.space ↦ d u) hdim_eq
  have hunit : ∀ u : p.space, ∃ (r : A.isomArrows hA p.fst)
      (hs : (A.isomSrc hA p.fst).base r = u) (ht : (A.isomTgt hA p.fst).base r = u),
      (A.isomSrc hA p.fst).residueFieldMap r =
        (p.space.residueFieldCongr (hs.trans ht.symm)).hom ≫
          (A.isomTgt hA p.fst).residueFieldMap r :=
    fun u ↦ ⟨(A.unitW hA p.fst).base u, A.unitW_src_apply hA p.fst u,
      A.unitW_tgt_apply hA p.fst u,
      A.residueFieldMap_unitW_eq hA p.fst u
        ((A.unitW_src_apply hA p.fst u).trans (A.unitW_tgt_apply hA p.fst u).symm)⟩
  have φ : MoritaMap (A.isomGroupoid hA p.fst sA) (B.isomGroupoid hB p.snd sB) :=
    MoritaMap.ofArrowIso (Iso.refl p.space) θ hsrc htgt hdim hunit
  exact ((A.moritaToChart hA p.fst sA).vistoliChowEquiv i hAI_good hAE_good).trans
    (((φ.vistoliChowEquiv i hAI_good hBI_good).symm).trans
      ((B.moritaToChart hB p.snd sB).vistoliChowEquiv i hBI_good hBE_good).symm)

end StackChart

/-! ## Corollary D: atlas independence for a Deligne–Mumford stack -/

namespace DeligneMumfordStack

variable {k : Type u} [Field k]

/-- **Corollary D (atlas independence for a Deligne–Mumford stack).** The Vistoli rational Chow
group computed from the internally chosen étale atlas `𝒳.chosenEtaleAtlas` is isomorphic to the
one computed from any other étale surjective, representably quasi-compact chart `B` with compact
scheme locally of finite type over `k` — the Vistoli Chow group of a Deligne–Mumford stack does
not depend on the choice of such an atlas (GitHub issue #47). -/
noncomputable def vistoliChowEquivOfChart (𝒳 : DeligneMumfordStack.{u})
    (hXq : 𝒳.chosenEtaleAtlas.HasRepresentableProperty @_root_.AlgebraicGeometry.QuasiCompact)
    [CompactSpace 𝒳.chosenEtaleAtlas.scheme]
    (sX : 𝒳.chosenEtaleAtlas.scheme ⟶ Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType sX]
    (B : StackChart 𝒳.toStack) (hB : B.IsEtaleSurjective)
    (hBq : B.HasRepresentableProperty @_root_.AlgebraicGeometry.QuasiCompact)
    [CompactSpace B.scheme] (sB : B.scheme ⟶ Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType sB] (i : ℤ) :
    𝒳.chosenEtaleAtlas.vistoliChow 𝒳.chosenEtaleAtlas_isEtaleSurjective sX i ≃ₗ[ℚ]
      B.vistoliChow hB sB i :=
  StackChart.vistoliChowEquivOfEtaleCharts 𝒳.chosenEtaleAtlas B
    𝒳.chosenEtaleAtlas_isEtaleSurjective hB hXq hBq sX sB i

/-- **The new chart groupoid of the chosen étale atlas is the old `etalePresentation`
groupoid.** Both are built from the same scheme: `X.chosenEtaleAtlasSelfOverlap` and
`X.chosenEtaleAtlas.selfOverlapScheme (X.chosenEtaleAtlas.isRepresentable_of_isEtaleSurjective
X.chosenEtaleAtlas_isEtaleSurjective)` are each `Classical.choice`/`Nonempty.some` of the same
`Nonempty` proposition (the `.1` clause of `HasRepresentableProperty` does not depend on the
morphism property `P`), hence equal by proof irrelevance; consequently the two
`EtalePresentationGroupoid`s agree outright, by `rfl`, once fed the same dimension functions. -/
theorem chosenEtaleAtlas_etaleGroupoid_eq (X : DeligneMumfordStack.{u})
    (sX : X.chosenEtaleAtlas.scheme ⟶ Spec (CommRingCat.of k))
    [_root_.AlgebraicGeometry.LocallyOfFiniteType sX]
    [_root_.AlgebraicGeometry.LocallyOfFiniteType (X.chosenEtaleAtlasSelfOverlap.fst ≫ sX)]
    (hsrc : ∀ r, dimensionFunction (X.chosenEtaleAtlasSelfOverlap.fst ≫ sX) r =
      dimensionFunction sX (X.chosenEtaleAtlasSelfOverlap.fst.base r))
    (htgt : ∀ r, dimensionFunction (X.chosenEtaleAtlasSelfOverlap.fst ≫ sX) r =
      dimensionFunction sX (X.chosenEtaleAtlasSelfOverlap.snd.base r)) :
    X.chosenEtaleAtlas.etaleGroupoid X.chosenEtaleAtlas_isEtaleSurjective sX =
      X.etalePresentation (dimensionFunction sX)
        (dimensionFunction (X.chosenEtaleAtlasSelfOverlap.fst ≫ sX)) hsrc htgt :=
  rfl

end DeligneMumfordStack

end GromovWitten.AlgebraicGeometry
