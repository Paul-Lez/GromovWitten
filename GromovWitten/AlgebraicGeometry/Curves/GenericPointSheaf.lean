/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.DiscreteSpace
import GromovWitten.AlgebraicGeometry.Curves.TotalNormalization
import Mathlib.Topology.Sheaves.Abelian

/-!
# Restriction to the generic points

The natural map to the pushforward from the discrete generic-point scheme has
flasque target. On a Noetherian scheme it is an isomorphism at every generic
stalk. Its kernel and cokernel therefore have vanishing generic stalks, which
is the support reduction used in the dimension-one cohomology bound.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves
variable {X : Scheme.{u}}

/-! ### The generic-point restriction map

The concrete map below is the presheaf pullback/pushforward unit followed by
the sheafification unit on the generic-point source.  Keeping this map
explicit exposes the stalk comparison needed for support arguments without
assuming that the unit is injective on the closed points. -/

noncomputable def genericPointSheafMap (X : Scheme.{u})
    (F : X.toTopCat.Sheaf AddCommGrpCat.{u}) : F ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (genericPointsToScheme X).base).obj
        ((presheafToSheaf (Opens.grothendieckTopology
          (genericPointCoproduct X).toTopCat) AddCommGrpCat).obj
          ((TopCat.Presheaf.pullback AddCommGrpCat
            (genericPointsToScheme X).base).obj F.1)) := by
  apply ObjectProperty.homMk
  exact (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat
      (genericPointsToScheme X).base).unit.app F.1 ≫
    (TopCat.Presheaf.pushforward AddCommGrpCat
      (genericPointsToScheme X).base).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology
        (genericPointCoproduct X).toTopCat)
        ((TopCat.Presheaf.pullback AddCommGrpCat
          (genericPointsToScheme X).base).obj F.1))

/-- The generic-point restriction map is an isomorphism on every generic
point stalk.  The proof factors the stalk map through the presheaf
pullback/stalk comparison and the sheafification stalk comparison. -/
theorem isIso_genericPointSheafMap_stalk [IsNoetherian X]
    (F : X.toTopCat.Sheaf AddCommGrpCat.{u})
    (x : genericPointCoproduct X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat
      ((genericPointsToScheme X).base x)).map
        (genericPointSheafMap X F).1) := by
  let f := (genericPointsToScheme X).base
  let P := (TopCat.Presheaf.pullback AddCommGrpCat f).obj F.1
  let Q : TopCat.Presheaf AddCommGrpCat (genericPointCoproduct X).toTopCat :=
    ((presheafToSheaf (Opens.grothendieckTopology
      (genericPointCoproduct X).toTopCat) AddCommGrpCat).obj P).1
  let t : P ⟶ Q := CategoryTheory.toSheafify
    (Opens.grothendieckTopology (genericPointCoproduct X).toTopCat) P
  let u := (TopCat.Presheaf.pullbackPushforwardAdjunction
    AddCommGrpCat f).unit.app F.1
  have hspP : IsIso (TopCat.Presheaf.stalkPushforward
      AddCommGrpCat f P x) := by
    apply TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      (F := P) (x := x)
    exact (genericPointsToScheme_isPreimmersion X).isEmbedding.isInducing
  have : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat f P x) := hspP
  have hpb : IsIso (TopCat.Presheaf.stalkPullbackHom
      AddCommGrpCat f F.1 x) := by
    exact (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat f F.1 x).isIso_hom
  have hu : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat
      (f x)).map u) := by
    have hcomp : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat
        (f x)).map u ≫ TopCat.Presheaf.stalkPushforward
          AddCommGrpCat f P x) := by
      change IsIso (TopCat.Presheaf.stalkPullbackHom AddCommGrpCat f F.1 x)
      exact hpb
    exact @IsIso.of_isIso_comp_right _ _ _ _ _
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map u)
      (TopCat.Presheaf.stalkPushforward AddCommGrpCat f P x)
      hspP hcomp
  have ht : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map t) := by
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x AddCommGrpCat P
  have hpush : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat
      (f x)).map ((TopCat.Presheaf.pushforward AddCommGrpCat f).map t)) := by
    have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map t) := ht
    have hspQ : IsIso (TopCat.Presheaf.stalkPushforward
        AddCommGrpCat f Q x) := by
      apply TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        (F := Q) (x := x)
      exact (genericPointsToScheme_isPreimmersion X).isEmbedding.isInducing
    have hn : ((TopCat.Presheaf.stalkFunctor AddCommGrpCat
          (f x)).map ((TopCat.Presheaf.pushforward AddCommGrpCat f).map t)) ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat f Q x =
        TopCat.Presheaf.stalkPushforward AddCommGrpCat f P x ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map t) := by
      apply TopCat.Presheaf.stalk_hom_ext
        ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj P)
      intro U hxU
      let mt : P.stalk x ⟶ Q.stalk x :=
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map t
      have h1 := TopCat.Presheaf.stalkFunctor_map_germ U (f x) hxU
        ((TopCat.Presheaf.pushforward AddCommGrpCat f).map t)
      let hxMap : x ∈ (Opens.map f).obj U := (Opens.mem_map).mpr hxU
      have h2 := congrArg (fun k => k ≫
          TopCat.Presheaf.stalkPushforward AddCommGrpCat f Q x) h1
      calc
        _ = (((TopCat.Presheaf.pushforward AddCommGrpCat f).map t).app (op U) ≫
            ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj Q).germ U
              (f x) hxU) ≫ TopCat.Presheaf.stalkPushforward AddCommGrpCat f Q x := by
          exact h2
        _ = ((TopCat.Presheaf.pushforward AddCommGrpCat f).map t).app (op U) ≫
            Q.germ ((Opens.map f).obj U) x hxMap := by
          have hsp := TopCat.Presheaf.stalkPushforward_germ
            AddCommGrpCat f Q U x hxU
          have hsp' := congrArg (fun k =>
            ((TopCat.Presheaf.pushforward AddCommGrpCat f).map t).app (op U) ≫ k) hsp
          simpa only [Category.assoc] using hsp'
        _ = P.germ ((Opens.map f).obj U) x hxMap ≫ mt := by
          have hgm := TopCat.Presheaf.stalkFunctor_map_germ
            ((Opens.map f).obj U) x hxMap t
          change t.app (op ((Opens.map f).obj U)) ≫
              Q.germ ((Opens.map f).obj U) x hxMap = _
          simpa [mt] using hgm.symm
        _ = ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj P).germ U
              (f x) hxU ≫ TopCat.Presheaf.stalkPushforward AddCommGrpCat f P x ≫ mt := by
          symm
          exact TopCat.Presheaf.stalkPushforward_germ_assoc
            AddCommGrpCat f P U x hxU mt
    have hcomp : IsIso (((TopCat.Presheaf.stalkFunctor AddCommGrpCat
        (f x)).map ((TopCat.Presheaf.pushforward AddCommGrpCat f).map t)) ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat f Q x) := by
      rw [hn]
      have : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat f P x) := hspP
      have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map t) := ht
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hspP ht
    exact @IsIso.of_isIso_comp_right _ _ _ _ _
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat f).map t))
      (TopCat.Presheaf.stalkPushforward AddCommGrpCat f Q x)
      hspQ hcomp
  change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map
    (u ≫ (TopCat.Presheaf.pushforward AddCommGrpCat f).map t))
  rw [Functor.map_comp]
  infer_instance

/-- The finite generic-point source used by the curve normalization API has a
flasque pushforward for every abelian sheaf on it. -/
theorem isFlasque_genericPointCoproduct_pushforward (X : Scheme.{u})
    (F : (genericPointCoproduct X).toTopCat.Sheaf AddCommGrpCat.{u}) :
    TopCat.Sheaf.IsFlasque
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (genericPointsToScheme X).base).obj F) := by
  exact isFlasque_pushforward_of_discreteSource
    (genericPointsToScheme X).base F

variable [IsNoetherian X]

/-- The generic restriction map is invertible at any generic point of the scheme. -/
lemma isIso_genericPointSheafMap_stalk_of_mem
    (F : X.toTopCat.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∈ genericPoints X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (genericPointSheafMap X F).1) := by
  let y : GenericPointSet X := ⟨x, hx⟩
  obtain ⟨q, hq⟩ := (genericPointCoproductEquiv X).surjective y
  have hqx : (genericPointsToScheme X).base q = x := by
    rw [← genericPointCoproductEquiv_val, hq]
  rw [← hqx]
  exact isIso_genericPointSheafMap_stalk F q

/-- The kernel of generic restriction has zero generic stalks. -/
lemma genericPointSheafMap_kernel_stalk_isZero
    (F : X.toTopCat.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∈ genericPoints X) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (kernel (genericPointSheafMap X F)).obj) := by
  let K := TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : IsIso (K.map (genericPointSheafMap X F)) :=
    isIso_genericPointSheafMap_stalk_of_mem F x hx
  exact IsZero.of_iso (isZero_kernel_of_mono (K.map (genericPointSheafMap X F)))
    (PreservesKernel.iso K (genericPointSheafMap X F))

/-- The cokernel of generic restriction has zero generic stalks. -/
lemma genericPointSheafMap_cokernel_stalk_isZero
    (F : X.toTopCat.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∈ genericPoints X) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (cokernel (genericPointSheafMap X F)).obj) := by
  let K := TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : IsIso (K.map (genericPointSheafMap X F)) :=
    isIso_genericPointSheafMap_stalk_of_mem F x hx
  exact IsZero.of_iso (isZero_cokernel_of_epi (K.map (genericPointSheafMap X F)))
    (PreservesCokernel.iso K (genericPointSheafMap X F))
end GromovWitten.AlgebraicGeometry.Curves
