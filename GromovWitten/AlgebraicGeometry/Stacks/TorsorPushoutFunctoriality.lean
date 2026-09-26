/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.TorsorPushout

/-!
# Functoriality of the pushout of an fppf torsor

`Stacks/TorsorPushout.lean` constructs, for a homomorphism `r : G ⟶ G'` of group algebraic spaces
and a `G`-torsor `P`, the pushout `G'`-torsor `r_* P`, presented by its universal evaluation
pairing `PushoutTorsor` (a point of `r_* P` is a `G`-equivariant map `P ⟶ G'` through `r`).  Its
docstring records that functoriality of `r_* P` in `P` is not proved.  This file supplies it,
together with the auxiliary comparison theory used to prove it.

## The comparison of two pushout data for the same torsor

The key technical tool is `PushoutTorsor.cmpLocal`: given two `PushoutTorsor r P` structures `A`,
`B` for the *same* torsor `P`, and a point `α` of `A` whose base lifts to the trivialising cover
of `P` through `c`, `cmpLocal A B α c hc` is the point of `B` with the same evaluation as `α`
against the tautological point of `P` at `c`.  This does not depend on the chosen lift
(`cmpLocal_lift_congr`) and is natural (`comp_cmpLocal`), so it glues (via
`GromovWitten.SheafGluing.PartialHom`) to an actual morphism of sheaves `cmpMap A B : A.sheaf ⟶
B.sheaf` computing `cmpLocal` on every lift (`cmpMap_spec`).

Two morphisms out of `A.sheaf` agreeing through `cmpLocal` on the trivialising cover of `P`
already agree everywhere (`PushoutTorsor.hom_ext_of_cmp`, by fppf descent), which gives at once:
that `cmpMap A B` lies over `T` and is `G'`-equivariant (`cmpMap_proj`, `cmpMap_equivariant`),
and that it is inverse to `cmpMap B A` (`cmpMap_hom_inv`, `cmpMap_inv_hom`), assembled into
`PushoutTorsor.compareIso : A.sheaf ≅ B.sheaf`.  This is the **uniqueness of the pushout datum**
flagged as open in `TorsorPushout.lean`, and is the main result of this file.

## Maps of pushout data over a base change

`PushoutTorsor.ev_eq_of_ev_cover_over` is the engine of the whole file: for an equivariant map
`u : P.P ⟶ Q.P` of the total sheaves of two torsors (`PushoutTorsor.IsEquivariantPt`), possibly
over *different* bases, a morphism of pushout data whose evaluation pairing is computed through `u`
at the tautological points of the trivialising cover of `P` computes it through `u` at every point
of `P`.  The proof is fppf descent along the trivialising cover, using that `u` preserves
difference points (`divPt_comp_of_isEquivariantPt`).

## Functoriality in the torsor

`PushoutTorsor.reindexAlong B φ` reindexes a pushout datum `B` for `Q` along a morphism
`φ : P ⟶ Q` of `G`-torsors to a pushout datum for `P` on the same underlying sheaf, and
`PushoutTorsor.pushMap A B φ : A.sheaf ⟶ B.sheaf` is the induced comparison.  It lies over `T`
(`pushMap_proj`), is `G'`-equivariant (`pushMap_equivariant`) and is characterised by its
evaluation pairing: `ev_pushMap` computes it at every point of `P` and `eq_pushMap` is the
corresponding uniqueness statement.  Uniqueness gives `pushMap_id` and `pushMap_comp`, hence
`TorsorPushout.pushoutMap φ r : r_* P ⟶ r_* Q` with `pushoutMap_id`, `pushoutMap_comp` and the
functor `pushoutFunctor r : FppfTorsor G T ⥤ FppfTorsor G' T`.

*Performance note*: every statement about `pushMap` is made with the pushout data `A`, `B`
abstract, and the concrete `pushoutTorsor` is substituted only in `pushoutMap` itself.  Baking the
concrete construction into the reindexed datum instead (as an earlier version of this file did)
makes the kernel unfold the whole descent construction of `pushoutSheaf` on every
definitional-equality check, and times out.

## Functoriality in the homomorphism

`PushoutTorsor.idDatum P : PushoutTorsor (𝟙 G.space.toSheaf) P` exhibits `P` itself as its own
pushout along the identity homomorphism, the evaluation pairing being the difference point
`divPt`.  `PushoutTorsor.compDatum B C` exhibits an iterated pushout as a pushout along the
composite homomorphism, evaluating through the canonical image `PushoutTorsor.unitPt` of a point
of `P` in `s_* P`.  Comparing them with the canonical data through `compareIso` gives
`pushoutIdIso : r_* P ≅ P` for `r = 𝟙 G` and `pushoutCompIso : (s ≫ r)_* P ≅ r_* (s_* P)`.

## Compatibility with base change

`PushoutTorsor.pullbackDatum A b` is the base change of a pushout datum along `b : T' ⟶ T`: a
point of the base change evaluates through the first projections (`pullback_ev_cond`).  Comparing
it with the canonical datum of the base-changed torsor gives
`pushoutPullbackIso : r_* (b^* P) ≅ b^* (r_* P)`.  The comparison is characterised by its
evaluation pairing (`ev_pushoutPullbackFst`, via the relative local-to-global lemma above) and is
natural in the torsor (`pushMap_comp_pushoutPullbackFst`).

## The induced equivariant map at an arbitrary point

`TorsorPushout.comp_targetMap_pt` computes `TorsorPushout.targetMap` (the equivariant map
`r_* P ⟶ U'` induced by an `r`-equivariant `U ⟶ U'`) at an *arbitrary* point of `P` over the same
base point, not only at the tautological points of the trivialising cover.  This is what makes
`targetMap` comparable with the constructions above; it is used in
`Stacks/QuotientStackGroupMaps.lean` to lift `pushoutFunctor` to quotient-stack fibres.

**Not done**: nothing about `r_*` itself; what is missing for the quotient-stack map `[U/G] ⟶
[V/H]` is only the bicategorical bookkeeping of the three coherence laws of a strong transformation,
see `Stacks/QuotientStackGroupMaps.lean`.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

namespace TorsorPushout

universe u

namespace PushoutTorsor

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}
  {r : G.space.toSheaf ⟶ G'.space.toSheaf} {P : FppfTorsor G T}

/-! ### Evaluation at varying points of `P` -/

/-- Evaluation of a point of a pushout datum at two points of `P` over the same base differ by
the image under `r` of the difference point of `P` (inverted). -/
theorem ev_congr_pt (A : PushoutTorsor r P) {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf)
    (p q : fppfYoneda.obj W ⟶ P.P) (hp : α ≫ A.projection = p ≫ P.projection)
    (hq : α ≫ A.projection = q ≫ P.projection) :
    A.ev α p hp = A.ev α q hq * (divPt P p q (hp.symm.trans hq) ≫ r)⁻¹ := by
  have hact : actPt (divPt P p q (hp.symm.trans hq)) q = p := actPt_divPt p q _
  have h' : α ≫ A.projection = actPt (divPt P p q (hp.symm.trans hq)) q ≫ P.projection := by
    rw [hact]; exact hp
  calc A.ev α p hp = A.ev α (actPt (divPt P p q (hp.symm.trans hq)) q) h' :=
        A.ev_congr_right α hact.symm hp h'
    _ = A.ev α q hq * (divPt P p q (hp.symm.trans hq) ≫ r)⁻¹ :=
        A.ev_actPt_right (divPt P p q (hp.symm.trans hq)) α q hq h'

/-! ### The local comparison formula -/

variable (A B : PushoutTorsor r P)

/-- The local comparison of two pushout data for the same torsor `P`: the point of `B` with the
same evaluation as `α` against the tautological point of `P` at a lift `c` of the base of `α`
through the trivialising cover of `P`. -/
noncomputable def cmpLocal {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hc : α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    fppfYoneda.obj W ⟶ B.sheaf :=
  (B.ev_bijective (coverPt c) (A.ev α (coverPt c) (by rw [hc, coverPt_proj]))).choose.1

variable {A B}

/-- The comparison point lies over the same base as `α`. -/
theorem cmpLocal_proj {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hc : α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    cmpLocal A B α c hc ≫ B.projection = coverPt c ≫ P.projection :=
  (B.ev_bijective (coverPt c) (A.ev α (coverPt c) (by rw [hc, coverPt_proj]))).choose.2

/-- The comparison point computes the same evaluation as `α`. -/
theorem ev_cmpLocal {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hc : α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    B.ev (cmpLocal A B α c hc) (coverPt c) (cmpLocal_proj α c hc) =
      A.ev α (coverPt c) (by rw [hc, coverPt_proj]) :=
  (B.ev_bijective (coverPt c) (A.ev α (coverPt c) (by rw [hc, coverPt_proj]))).choose_spec.1

/-- **The comparison does not depend on the chosen lift.** -/
theorem cmpLocal_lift_congr {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf)
    {c c' : W ⟶ P.locallyTrivial.coverScheme}
    (hc : α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hc' : α ≫ A.projection = fppfYoneda.map (c' ≫ P.locallyTrivial.cover)) :
    cmpLocal A B α c' hc' = cmpLocal A B α c hc := by
  have hp : α ≫ A.projection = coverPt c ≫ P.projection := by rw [hc, coverPt_proj]
  have hp' : α ≫ A.projection = coverPt c' ≫ P.projection := by rw [hc', coverPt_proj]
  have hβp' : (cmpLocal A B α c hc) ≫ B.projection = coverPt c' ≫ P.projection :=
    (cmpLocal_proj α c hc).trans (hp.symm.trans hp')
  have hAeq := A.ev_congr_pt α (coverPt c) (coverPt c') hp hp'
  have hBeq := B.ev_congr_pt (cmpLocal A B α c hc) (coverPt c) (coverPt c')
    (cmpLocal_proj α c hc) hβp'
  rw [ev_cmpLocal α c hc] at hBeq
  have hcombine : A.ev α (coverPt c') hp' * (divPt P (coverPt c) (coverPt c') _ ≫ r)⁻¹ =
      B.ev (cmpLocal A B α c hc) (coverPt c') hβp' * (divPt P (coverPt c) (coverPt c') _ ≫ r)⁻¹ :=
    hAeq ▸ hBeq
  have hval : A.ev α (coverPt c') hp' = B.ev (cmpLocal A B α c hc) (coverPt c') hβp' :=
    mul_right_cancel hcombine
  exact B.ev_injective (coverPt c') (cmpLocal_proj α c' hc') hβp'
    ((ev_cmpLocal α c' hc').trans hval)

/-- **The comparison is natural in the test scheme.** -/
theorem comp_cmpLocal {V W : Scheme.{u}} (u : V ⟶ W) (α : fppfYoneda.obj W ⟶ A.sheaf)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hc : α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hc' : (fppfYoneda.map u ≫ α) ≫ A.projection =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover)) :
    fppfYoneda.map u ≫ cmpLocal A B α c hc =
      cmpLocal A B (fppfYoneda.map u ≫ α) (u ≫ c) hc' := by
  have hp' : (fppfYoneda.map u ≫ α) ≫ A.projection = coverPt (u ≫ c) ≫ P.projection := by
    rw [hc', coverPt_proj]
  have hβproj : (fppfYoneda.map u ≫ cmpLocal A B α c hc) ≫ B.projection =
      coverPt (u ≫ c) ≫ P.projection := by
    rw [Category.assoc, cmpLocal_proj α c hc, ← Category.assoc, comp_coverPt]
  have hnatB := B.ev_naturality u (cmpLocal A B α c hc) (coverPt c) (cmpLocal_proj α c hc)
    (by rw [Category.assoc, cmpLocal_proj α c hc, ← Category.assoc])
  have hnatB' : fppfYoneda.map u ≫
      B.ev (cmpLocal A B α c hc) (coverPt c) (cmpLocal_proj α c hc) =
        B.ev (fppfYoneda.map u ≫ cmpLocal A B α c hc) (coverPt (u ≫ c)) hβproj :=
    hnatB.trans (B.ev_congr_right (fppfYoneda.map u ≫ cmpLocal A B α c hc) (comp_coverPt u c) _
      hβproj)
  have hnatA := A.ev_naturality u α (coverPt c) (by rw [hc, coverPt_proj])
    (by simp only [Category.assoc]; rw [hc, coverPt_proj])
  have hnatA' : fppfYoneda.map u ≫ A.ev α (coverPt c) (by rw [hc, coverPt_proj]) =
      A.ev (fppfYoneda.map u ≫ α) (coverPt (u ≫ c)) hp' :=
    hnatA.trans (A.ev_congr_right (fppfYoneda.map u ≫ α) (comp_coverPt u c) _ hp')
  refine B.ev_injective (coverPt (u ≫ c)) hβproj
    (cmpLocal_proj (fppfYoneda.map u ≫ α) (u ≫ c) hc') ?_
  rw [← hnatB', ev_cmpLocal α c hc, hnatA', ev_cmpLocal (fppfYoneda.map u ≫ α) (u ≫ c) hc']

/-! ### Uniqueness by descent along the trivialising cover -/

/-- **Two morphisms out of a pushout datum agreeing on the trivialising cover of `P` agree
everywhere.**  This is the technical heart of the uniqueness of a pushout datum: it lets every
subsequent comparison be checked only on the (canonically presented) fibre over the trivialising
cover. -/
theorem hom_ext_of_cmp {A : PushoutTorsor r P} {S : FppfSheaf.{u}} {φ ψ : A.sheaf ⟶ S}
    (h : ∀ {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf)
      (c : W ⟶ P.locallyTrivial.coverScheme),
      α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover) → α ≫ φ = α ≫ ψ) :
    φ = ψ := by
  apply hom_ext_points
  intro W ω
  set s₀ : W ⟶ T := Scheme.fppfTopology.yonedaEquiv (ω ≫ A.projection) with hs₀def
  have hs : ω ≫ A.projection = fppfYoneda.map s₀ := (fppfYoneda_map_yonedaEquiv _).symm
  have hR : (coverSieve P).pullback s₀ ∈ Scheme.fppfTopology W :=
    Scheme.fppfTopology.pullback_stable s₀ (coverSieve_mem P)
  refine hom_ext_of_sieve_pt (φ := ω ≫ φ) (ψ := ω ≫ ψ) hR ?_
  intro V u hu
  obtain ⟨c, hc0⟩ := exists_factor_of_coverSieve hu
  have hcu : (fppfYoneda.map u ≫ ω) ≫ A.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hs, ← Functor.map_comp, hc0]
  have key := h (fppfYoneda.map u ≫ ω) c hcu
  rw [← Category.assoc, ← Category.assoc]
  exact key

/-! ### Existence of the comparison morphism -/

open GromovWitten.SheafGluing

/-- The comparison only depends on the point (not on the proof it lifts through the cover). -/
theorem cmpLocal_congr_pt {W : Scheme.{u}} {α α' : fppfYoneda.obj W ⟶ A.sheaf} (hαα' : α = α')
    {c : W ⟶ P.locallyTrivial.coverScheme}
    (hc : α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hc' : α' ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    cmpLocal A B α c hc = cmpLocal A B α' c hc' := by
  subst hαα'
  rfl

variable (A B)

/-- The comparison morphism between two pushout data for the same torsor, defined on the sections
whose base lifts to the trivialising cover of `P`. -/
noncomputable def cmpPartial : PartialHom A.projection B.sheaf (coverSieve P) where
  app {W} x :=
    Scheme.fppfTopology.yonedaEquiv (cmpLocal A B
      (Scheme.fppfTopology.yonedaEquiv.symm x.1)
      (exists_factor_of_coverSieve x.2).choose (by
        rw [GrothendieckTopology.yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_map]
        exact congrArg _ (exists_factor_of_coverSieve x.2).choose_spec.symm))
  naturality := by
    intro V W u x
    rw [GrothendieckTopology.yonedaEquiv_naturality]
    refine congrArg _ ?_
    have hres : Scheme.fppfTopology.yonedaEquiv.symm ((SectionsOver.res u x).1) =
        fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1 :=
      (Scheme.fppfTopology.yonedaEquiv_symm_naturality_left u _ x.1).symm
    have hA : (fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1) ≫ A.projection =
        fppfYoneda.map ((u ≫ (exists_factor_of_coverSieve x.2).choose) ≫
          P.locallyTrivial.cover) := by
      rw [Category.assoc, GrothendieckTopology.yonedaEquiv_symm_naturality_right,
        yonedaEquiv_symm_map, ← CategoryTheory.Functor.map_comp]
      refine congrArg _ ?_
      rw [Category.assoc, (exists_factor_of_coverSieve x.2).choose_spec]
      rfl
    have hB : (fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1) ≫ A.projection =
        fppfYoneda.map ((exists_factor_of_coverSieve (SectionsOver.res u x).2).choose ≫
          P.locallyTrivial.cover) := by
      rw [← hres, GrothendieckTopology.yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_map]
      exact congrArg _ (exists_factor_of_coverSieve (SectionsOver.res u x).2).choose_spec.symm
    refine Eq.trans (comp_cmpLocal u (Scheme.fppfTopology.yonedaEquiv.symm x.1)
      (exists_factor_of_coverSieve x.2).choose _ hA) ?_
    refine Eq.trans (cmpLocal_lift_congr _ hA hB).symm ?_
    exact (cmpLocal_congr_pt hres _ hB).symm

/-- **The comparison morphism between two pushout data for the same torsor**, glued from
`cmpLocal` along the trivialising cover of `P`. -/
noncomputable def cmpMap : A.sheaf ⟶ B.sheaf :=
  (cmpPartial A B).glue (coverSieve_mem P)

/-- The comparison morphism computes `cmpLocal` on every point lifting through the trivialising
cover of `P`. -/
theorem cmpMap_spec {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hc : α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    α ≫ cmpMap A B = cmpLocal A B α c hc := by
  have hbe : GromovWitten.SheafGluing.base A.projection
      (Scheme.fppfTopology.yonedaEquiv α) = c ≫ P.locallyTrivial.cover := by
    rw [SheafGluing.base_yonedaEquiv, hc, GrothendieckTopology.yonedaEquiv_yoneda_map]
  have hb : (coverSieve P).arrows
      (GromovWitten.SheafGluing.base A.projection (Scheme.fppfTopology.yonedaEquiv α)) := by
    rw [hbe]
    exact ⟨_, c, P.locallyTrivial.cover, Presieve.singleton.mk, rfl⟩
  have key := (cmpPartial A B).glue_app (coverSieve_mem P)
    (⟨Scheme.fppfTopology.yonedaEquiv α, hb⟩ : SectionsOver A.projection (coverSieve P) W)
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [cmpMap, GrothendieckTopology.yonedaEquiv_comp, key]
  refine congrArg Scheme.fppfTopology.yonedaEquiv ?_
  have hpt : Scheme.fppfTopology.yonedaEquiv.symm
      ((⟨Scheme.fppfTopology.yonedaEquiv α, hb⟩ :
        SectionsOver A.projection (coverSieve P) W).1) = α :=
    Equiv.symm_apply_apply _ _
  have hA : α ≫ A.projection = fppfYoneda.map
      ((exists_factor_of_coverSieve (⟨Scheme.fppfTopology.yonedaEquiv α, hb⟩ :
        SectionsOver A.projection (coverSieve P) W).2).choose ≫ P.locallyTrivial.cover) := by
    rw [hc, hbe.symm]
    exact congrArg _ (exists_factor_of_coverSieve hb).choose_spec.symm
  refine (cmpLocal_congr_pt hpt _ hA).trans ?_
  exact cmpLocal_lift_congr α hc hA

/-! ### The comparison morphism is an isomorphism, lying over `T` and equivariant -/

/-- The comparison lies over `T`. -/
theorem cmpMap_proj : cmpMap A B ≫ B.projection = A.projection := by
  refine hom_ext_of_cmp (fun α c hc => ?_)
  rw [← Category.assoc, cmpMap_spec A B α c hc, cmpLocal_proj α c hc, coverPt_proj, ← hc]

/-- **The comparison is a round trip on the trivialising cover of `P`.** -/
theorem cmpLocal_round_trip {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hc : α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    cmpLocal B A (cmpLocal A B α c hc) c
      ((cmpLocal_proj α c hc).trans (coverPt_proj c)) = α := by
  have hp : α ≫ A.projection = coverPt c ≫ P.projection := by rw [hc, coverPt_proj]
  refine A.ev_injective (coverPt c)
    (cmpLocal_proj (cmpLocal A B α c hc) c ((cmpLocal_proj α c hc).trans (coverPt_proj c))) hp ?_
  rw [ev_cmpLocal (cmpLocal A B α c hc) c ((cmpLocal_proj α c hc).trans (coverPt_proj c)),
    ev_cmpLocal α c hc]

/-- **The comparison morphisms are mutually inverse.** -/
theorem cmpMap_hom_inv : cmpMap A B ≫ cmpMap B A = 𝟙 A.sheaf := by
  refine hom_ext_of_cmp (fun α c hc => ?_)
  rw [← Category.assoc, cmpMap_spec A B α c hc,
    cmpMap_spec B A (cmpLocal A B α c hc) c ((cmpLocal_proj α c hc).trans (coverPt_proj c)),
    cmpLocal_round_trip A B α c hc, Category.comp_id]

theorem cmpMap_inv_hom : cmpMap B A ≫ cmpMap A B = 𝟙 B.sheaf := by
  refine hom_ext_of_cmp (fun β c hc => ?_)
  rw [← Category.assoc, cmpMap_spec B A β c hc,
    cmpMap_spec A B (cmpLocal B A β c hc) c ((cmpLocal_proj β c hc).trans (coverPt_proj c)),
    cmpLocal_round_trip B A β c hc, Category.comp_id]

/-- The comparison is compatible with the action on points. -/
theorem cmpLocal_actPt {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (α : fppfYoneda.obj W ⟶ A.sheaf) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hc : α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hc' : actPt g' α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    cmpLocal A B (actPt g' α) c hc' = actPt g' (cmpLocal A B α c hc) := by
  have hcB : actPt g' (cmpLocal A B α c hc) ≫ B.projection = coverPt c ≫ P.projection := by
    rw [B.actPt_projection]; exact cmpLocal_proj α c hc
  refine B.ev_injective (coverPt c) (cmpLocal_proj (actPt g' α) c hc') hcB ?_
  rw [ev_cmpLocal (actPt g' α) c hc',
    B.ev_actPt g' (cmpLocal A B α c hc) (coverPt c) (cmpLocal_proj α c hc) hcB, ev_cmpLocal α c hc]
  exact A.ev_actPt g' α (coverPt c) (hc.trans (coverPt_proj c).symm)
    (hc'.trans (coverPt_proj c).symm)

/-- **The comparison is equivariant for the action of `G'`, on points.** -/
theorem cmpMap_actPt {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (α : fppfYoneda.obj W ⟶ A.sheaf) :
    actPt g' α ≫ cmpMap A B = actPt g' (α ≫ cmpMap A B) := by
  have hbase : α ≫ A.projection =
      fppfYoneda.map (Scheme.fppfTopology.yonedaEquiv (α ≫ A.projection)) :=
    (fppfYoneda_map_yonedaEquiv _).symm
  refine hom_ext_of_sieve_pt
    (pullback_coverSieve_mem P (Scheme.fppfTopology.yonedaEquiv (α ≫ A.projection)))
    fun V u hu => ?_
  obtain ⟨c, hc⟩ := exists_lift_of_pullback hu
  have hα : (fppfYoneda.map u ≫ α) ≫ A.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hbase, ← Functor.map_comp, hc]
  have hgα : actPt (fppfYoneda.map u ≫ g') (fppfYoneda.map u ≫ α) ≫ A.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [A.actPt_projection]; exact hα
  have hL : fppfYoneda.map u ≫ (actPt g' α ≫ cmpMap A B) =
      cmpLocal A B (actPt (fppfYoneda.map u ≫ g') (fppfYoneda.map u ≫ α)) c hgα := by
    rw [← Category.assoc, comp_actPt, cmpMap_spec A B _ c hgα]
  have hR : fppfYoneda.map u ≫ actPt g' (α ≫ cmpMap A B) =
      actPt (fppfYoneda.map u ≫ g') (cmpLocal A B (fppfYoneda.map u ≫ α) c hα) := by
    rw [comp_actPt, ← Category.assoc, cmpMap_spec A B (fppfYoneda.map u ≫ α) c hα]
  rw [hL, hR, cmpLocal_actPt A B (fppfYoneda.map u ≫ g') (fppfYoneda.map u ≫ α) c hα hgα]

/-- **The comparison is equivariant for the action of `G'`.** -/
theorem cmpMap_equivariant :
    ModObj.smul (M := G'.space.toSheaf) (X := A.sheaf) ≫ cmpMap A B =
      (G'.space.toSheaf ◁ cmpMap A B) ≫ ModObj.smul (M := G'.space.toSheaf) (X := B.sheaf) := by
  refine hom_ext_points fun W ω => ?_
  rw [← Category.assoc, ← Category.assoc, ← lift_comp_fst_snd ω, ConeQuotient.lift_whiskerLeft]
  exact cmpMap_actPt A B (ω ≫ fst _ _) (ω ≫ snd _ _)

/-- **Uniqueness of a pushout datum**: two `PushoutTorsor r P` structures for the same torsor
`P` are canonically isomorphic, compatibly with the projection to `T` and the action of `G'`. -/
noncomputable def compareIso : A.sheaf ≅ B.sheaf where
  hom := cmpMap A B
  inv := cmpMap B A
  hom_inv_id := cmpMap_hom_inv A B
  inv_hom_id := cmpMap_inv_hom A B

end PushoutTorsor

/-! ### Comparison of pushout data along a map of torsors over a base change -/

namespace PushoutTorsor

section Relative

variable {G G' : AlgebraicSpaceGroup.{u}} {T T₂ : Scheme.{u}}
  {r : G.space.toSheaf ⟶ G'.space.toSheaf} {P : FppfTorsor G T} {Q : FppfTorsor G T₂}

/-- Evaluation only depends on the point of the pushout and the point of `P`, not on the proof
that they lie over the same base point. -/
theorem ev_congr (A : PushoutTorsor r P) {W : Scheme.{u}}
    {α β : fppfYoneda.obj W ⟶ A.sheaf} (hαβ : α = β) {p q : fppfYoneda.obj W ⟶ P.P}
    (hpq : p = q) (h : α ≫ A.projection = p ≫ P.projection)
    (h' : β ≫ A.projection = q ≫ P.projection) : A.ev α p h = A.ev β q h' := by
  subst hαβ
  subst hpq
  rfl

/-- `G`-equivariance, on points, of a map between the total sheaves of two torsors, possibly over
different bases. -/
def IsEquivariantPt (u : P.P ⟶ Q.P) : Prop :=
  ∀ ⦃Z : FppfSheaf.{u}⦄ (g : Z ⟶ G.space.toSheaf) (p : Z ⟶ P.P),
    actPt g p ≫ u = actPt g (p ≫ u)

/-- **The difference point of two points of a torsor is preserved by an equivariant map.** -/
theorem divPt_comp_of_isEquivariantPt {u : P.P ⟶ Q.P} (hu : IsEquivariantPt u)
    {Z : FppfSheaf.{u}} (p q : Z ⟶ P.P) (h : p ≫ P.projection = q ≫ P.projection)
    (h' : (p ≫ u) ≫ Q.projection = (q ≫ u) ≫ Q.projection) :
    divPt Q (p ≫ u) (q ≫ u) h' = divPt P p q h :=
  (eq_divPt _ _ h' (divPt P p q h) (by rw [← hu, actPt_divPt])).symm

/-- **From the trivialising cover to all points**, for a map of pushout data over an equivariant
map `u` of the underlying torsors (which may lie over a base change): if the evaluation pairing of
`f` is computed through `u` at the tautological points of the trivialising cover of `P`, then it is
computed through `u` at every point of `P`. -/
theorem ev_eq_of_ev_cover_over (A : PushoutTorsor r P) (B : PushoutTorsor r Q) {u : P.P ⟶ Q.P}
    (hu : IsEquivariantPt u) (f : A.sheaf ⟶ B.sheaf)
    (hbase : ∀ {V : Scheme.{u}} (β : fppfYoneda.obj V ⟶ A.sheaf) (q : fppfYoneda.obj V ⟶ P.P),
      β ≫ A.projection = q ≫ P.projection → (β ≫ f) ≫ B.projection = (q ≫ u) ≫ Q.projection)
    (hloc : ∀ {V : Scheme.{u}} (β : fppfYoneda.obj V ⟶ A.sheaf)
      (c : V ⟶ P.locallyTrivial.coverScheme),
      β ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover) →
      ∀ (h₁ : (β ≫ f) ≫ B.projection = (coverPt c ≫ u) ≫ Q.projection)
        (h₂ : β ≫ A.projection = coverPt c ≫ P.projection),
        B.ev (β ≫ f) (coverPt c ≫ u) h₁ = A.ev β (coverPt c) h₂)
    {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ A.projection = p ≫ P.projection)
    (h' : (α ≫ f) ≫ B.projection = (p ≫ u) ≫ Q.projection) :
    B.ev (α ≫ f) (p ≫ u) h' = A.ev α p h := by
  have hbase0 : α ≫ A.projection =
      fppfYoneda.map (Scheme.fppfTopology.yonedaEquiv (α ≫ A.projection)) :=
    (fppfYoneda_map_yonedaEquiv _).symm
  refine hom_ext_of_sieve_pt
    (pullback_coverSieve_mem P (Scheme.fppfTopology.yonedaEquiv (α ≫ A.projection)))
    fun V w hw => ?_
  obtain ⟨c, hcw⟩ := exists_lift_of_pullback hw
  have hα' : (fppfYoneda.map w ≫ α) ≫ A.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hbase0, ← CategoryTheory.Functor.map_comp, hcw]
  have hp : (fppfYoneda.map w ≫ α) ≫ A.projection =
      (fppfYoneda.map w ≫ p) ≫ P.projection := by
    simp only [Category.assoc]
    rw [h]
  have hq : (fppfYoneda.map w ≫ α) ≫ A.projection = coverPt c ≫ P.projection := by
    rw [hα', coverPt_proj]
  have h₁ : ((fppfYoneda.map w ≫ α) ≫ f) ≫ B.projection =
      ((fppfYoneda.map w ≫ p) ≫ u) ≫ Q.projection := hbase _ _ hp
  have h₂ : ((fppfYoneda.map w ≫ α) ≫ f) ≫ B.projection =
      (coverPt c ≫ u) ≫ Q.projection := hbase _ _ hq
  have hnat : (fppfYoneda.map w ≫ (α ≫ f)) ≫ B.projection =
      (fppfYoneda.map w ≫ (p ≫ u)) ≫ Q.projection := by
    simp only [Category.assoc]
    simpa only [Category.assoc] using h₁
  calc fppfYoneda.map w ≫ B.ev (α ≫ f) (p ≫ u) h'
      = B.ev (fppfYoneda.map w ≫ (α ≫ f)) (fppfYoneda.map w ≫ (p ≫ u)) hnat :=
        B.ev_naturality w (α ≫ f) (p ≫ u) h' hnat
    _ = B.ev ((fppfYoneda.map w ≫ α) ≫ f) ((fppfYoneda.map w ≫ p) ≫ u) h₁ :=
        B.ev_congr (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm hnat h₁
    _ = B.ev ((fppfYoneda.map w ≫ α) ≫ f) (coverPt c ≫ u) h₂ *
          (divPt Q ((fppfYoneda.map w ≫ p) ≫ u) (coverPt c ≫ u) (h₁.symm.trans h₂) ≫ r)⁻¹ :=
        B.ev_congr_pt ((fppfYoneda.map w ≫ α) ≫ f) _ _ h₁ h₂
    _ = A.ev (fppfYoneda.map w ≫ α) (coverPt c) hq *
          (divPt P (fppfYoneda.map w ≫ p) (coverPt c) (hp.symm.trans hq) ≫ r)⁻¹ := by
        rw [hloc (fppfYoneda.map w ≫ α) c hα' h₂ hq]
        exact congrArg (fun x => A.ev (fppfYoneda.map w ≫ α) (coverPt c) hq * (x ≫ r)⁻¹)
          (divPt_comp_of_isEquivariantPt hu (fppfYoneda.map w ≫ p) (coverPt c)
            (hp.symm.trans hq) (h₁.symm.trans h₂))
    _ = A.ev (fppfYoneda.map w ≫ α) (fppfYoneda.map w ≫ p) hp :=
        (A.ev_congr_pt (fppfYoneda.map w ≫ α) _ _ hp hq).symm
    _ = fppfYoneda.map w ≫ A.ev α p h := (A.ev_naturality w α p h hp).symm

end Relative

end PushoutTorsor

/-! ### Functoriality in the torsor -/

namespace PushoutTorsor

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}
  {r : G.space.toSheaf ⟶ G'.space.toSheaf} {P Q R : FppfTorsor G T}

/-- A morphism of torsors over a fixed base is equivariant on points. -/
theorem isEquivariantPt_iso_hom (φ : P ⟶ Q) : IsEquivariantPt φ.iso.hom :=
  fun _ g x => actPt_comp_equivariant φ.iso.hom φ.equivariant g x

/-- **The difference point of two points of a torsor is preserved by a morphism of torsors.** -/
theorem divPt_comp_iso (φ : P ⟶ Q) {Z : FppfSheaf.{u}} (p q : Z ⟶ P.P)
    (h : p ≫ P.projection = q ≫ P.projection)
    (h' : (p ≫ φ.iso.hom) ≫ Q.projection = (q ≫ φ.iso.hom) ≫ Q.projection) :
    divPt Q (p ≫ φ.iso.hom) (q ≫ φ.iso.hom) h' = divPt P p q h :=
  divPt_comp_of_isEquivariantPt (isEquivariantPt_iso_hom φ) p q h h'

/-- **Reindexing a pushout datum along a morphism of torsors.**  A pushout datum `B` for `Q` and
a morphism `φ : P ⟶ Q` of `G`-torsors produce a pushout datum for `P` on the *same* underlying
sheaf `B.sheaf`, whose evaluation pairing is computed through `φ` (`reindexAlong_ev`).  Comparing
it with a pushout datum for `P` (via `cmpMap`) gives the functoriality of the pushout in the
torsor. -/
noncomputable def reindexAlong (B : PushoutTorsor r Q) (φ : P ⟶ Q) : PushoutTorsor r P where
  sheaf := B.sheaf
  action := B.action
  projection := B.projection
  action_over := B.action_over
  ev := fun {_} α p h => B.ev α (p ≫ φ.iso.hom) (by simpa [Category.assoc, φ.over] using h)
  ev_naturality := by
    intro V W u α p h h'
    have e1 : (fppfYoneda.map u ≫ p) ≫ φ.iso.hom = fppfYoneda.map u ≫ (p ≫ φ.iso.hom) := by
      rw [Category.assoc]
    have hQ : α ≫ B.projection = (p ≫ φ.iso.hom) ≫ Q.projection := by
      simpa [Category.assoc, φ.over] using h
    have hQ' : (fppfYoneda.map u ≫ α) ≫ B.projection =
        (fppfYoneda.map u ≫ (p ≫ φ.iso.hom)) ≫ Q.projection := by
      simpa [Category.assoc, φ.over] using h'
    refine (B.ev_naturality u α (p ≫ φ.iso.hom) hQ hQ').trans
      (B.ev_congr_right (fppfYoneda.map u ≫ α) e1.symm hQ' ?_)
    simpa [Category.assoc, φ.over] using h'
  ev_actPt := by
    intro W g' α p h h'
    exact B.ev_actPt g' α (p ≫ φ.iso.hom) (by simpa [Category.assoc, φ.over] using h)
      (by simpa [Category.assoc, φ.over] using h')
  ev_actPt_right := by
    intro W g α p h h'
    have e2 : actPt g p ≫ φ.iso.hom = actPt g (p ≫ φ.iso.hom) :=
      actPt_comp_equivariant φ.iso.hom φ.equivariant g p
    have hQ : α ≫ B.projection = (p ≫ φ.iso.hom) ≫ Q.projection := by
      simpa [Category.assoc, φ.over] using h
    have hQ' : α ≫ B.projection = (actPt g p ≫ φ.iso.hom) ≫ Q.projection := by
      simpa [Category.assoc, φ.over] using h'
    refine (B.ev_congr_right α e2 hQ' ?_).trans (B.ev_actPt_right g α (p ≫ φ.iso.hom) hQ ?_)
    · rw [e2] at hQ'; exact hQ'
    · rw [e2] at hQ'; exact hQ'
  ev_bijective := by
    intro W p g'
    obtain ⟨⟨β, hβ⟩, hβg, hβu⟩ := B.ev_bijective (p ≫ φ.iso.hom) g'
    have hβ' : β ≫ B.projection = p ≫ P.projection := by
      simpa [Category.assoc, φ.over] using hβ
    refine ⟨⟨β, hβ'⟩, hβg, ?_⟩
    intro y hy
    obtain ⟨δ, hδ0⟩ := y
    have hδ0' : δ ≫ B.projection = (p ≫ φ.iso.hom) ≫ Q.projection := by
      simpa [Category.assoc, φ.over] using hδ0
    have hδ' : B.ev δ (p ≫ φ.iso.hom) hδ0' = g' := hy
    have hval : δ = β := congrArg Subtype.val (hβu ⟨δ, hδ0'⟩ hδ')
    exact Subtype.ext hval

/-- The reindexed evaluation pairing is computed through `φ`. -/
theorem reindexAlong_ev (B : PushoutTorsor r Q) (φ : P ⟶ Q) {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ B.sheaf) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ B.projection = p ≫ P.projection) :
    (reindexAlong B φ).ev α p h =
      B.ev α (p ≫ φ.iso.hom) (by rw [Category.assoc, φ.over]; exact h) :=
  rfl

/-! ### The morphism of pushout data induced by a morphism of torsors -/

/-- **The morphism of pushout data induced by a morphism `φ : P ⟶ Q` of `G`-torsors.**  It is
characterised by `ev_pushMap` (its evaluation pairing is computed through `φ`) together with
`eq_pushMap` (uniqueness); no property of any particular construction of the pushout is used. -/
noncomputable def pushMap (A : PushoutTorsor r P) (B : PushoutTorsor r Q) (φ : P ⟶ Q) :
    A.sheaf ⟶ B.sheaf :=
  cmpMap A (reindexAlong B φ)

/-- The induced morphism lies over the base. -/
theorem pushMap_proj (A : PushoutTorsor r P) (B : PushoutTorsor r Q) (φ : P ⟶ Q) :
    pushMap A B φ ≫ B.projection = A.projection :=
  cmpMap_proj A (reindexAlong B φ)

/-- The induced morphism is `G'`-equivariant. -/
theorem pushMap_equivariant (A : PushoutTorsor r P) (B : PushoutTorsor r Q) (φ : P ⟶ Q) :
    ModObj.smul (M := G'.space.toSheaf) (X := A.sheaf) ≫ pushMap A B φ =
      (G'.space.toSheaf ◁ pushMap A B φ) ≫ ModObj.smul (M := G'.space.toSheaf) (X := B.sheaf) :=
  cmpMap_equivariant A (reindexAlong B φ)

/-- **The defining property of the induced morphism, at the tautological points of the
trivialising cover of `P`.** -/
theorem ev_pushMap_cover (A : PushoutTorsor r P) (B : PushoutTorsor r Q) (φ : P ⟶ Q)
    {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hc : α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h : (α ≫ pushMap A B φ) ≫ B.projection = (coverPt c ≫ φ.iso.hom) ≫ Q.projection)
    (h' : α ≫ A.projection = coverPt c ≫ P.projection) :
    B.ev (α ≫ pushMap A B φ) (coverPt c ≫ φ.iso.hom) h = A.ev α (coverPt c) h' := by
  have hspec : α ≫ pushMap A B φ = cmpLocal A (reindexAlong B φ) α c hc :=
    cmpMap_spec A (reindexAlong B φ) α c hc
  have h₂ : cmpLocal A (reindexAlong B φ) α c hc ≫ B.projection =
      (coverPt c ≫ φ.iso.hom) ≫ Q.projection := by
    rw [Category.assoc, φ.over]
    exact cmpLocal_proj α c hc
  exact (B.ev_congr hspec rfl h h₂).trans (ev_cmpLocal (A := A) (B := reindexAlong B φ) α c hc)

/-- **From the trivialising cover to all points**: a morphism over the base whose evaluation
pairing is computed through `φ` at the tautological points of the trivialising cover of `P` has
that property at every point of `P`. -/
theorem ev_eq_of_ev_cover (A : PushoutTorsor r P) (B : PushoutTorsor r Q) (φ : P ⟶ Q)
    (f : A.sheaf ⟶ B.sheaf) (hf : f ≫ B.projection = A.projection)
    (hloc : ∀ {V : Scheme.{u}} (β : fppfYoneda.obj V ⟶ A.sheaf)
      (c : V ⟶ P.locallyTrivial.coverScheme),
      β ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover) →
      ∀ (h₁ : (β ≫ f) ≫ B.projection = (coverPt c ≫ φ.iso.hom) ≫ Q.projection)
        (h₂ : β ≫ A.projection = coverPt c ≫ P.projection),
        B.ev (β ≫ f) (coverPt c ≫ φ.iso.hom) h₁ = A.ev β (coverPt c) h₂)
    {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ A.projection = p ≫ P.projection)
    (h' : (α ≫ f) ≫ B.projection = (p ≫ φ.iso.hom) ≫ Q.projection) :
    B.ev (α ≫ f) (p ≫ φ.iso.hom) h' = A.ev α p h :=
  ev_eq_of_ev_cover_over A B (isEquivariantPt_iso_hom φ) f
    (fun β q hq => by rw [Category.assoc, hf, hq, Category.assoc, φ.over]) hloc α p h h'

/-- **The defining property of the induced morphism**: its evaluation pairing is computed through
`φ`, at every point of `P`. -/
theorem ev_pushMap (A : PushoutTorsor r P) (B : PushoutTorsor r Q) (φ : P ⟶ Q)
    {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ A.projection = p ≫ P.projection)
    (h' : (α ≫ pushMap A B φ) ≫ B.projection = (p ≫ φ.iso.hom) ≫ Q.projection) :
    B.ev (α ≫ pushMap A B φ) (p ≫ φ.iso.hom) h' = A.ev α p h :=
  ev_eq_of_ev_cover A B φ (pushMap A B φ) (pushMap_proj A B φ)
    (fun β c hc h₁ h₂ => ev_pushMap_cover A B φ β c hc h₁ h₂) α p h h'

/-- **Uniqueness of the induced morphism**: a morphism over the base whose evaluation pairing is
computed through `φ` on the trivialising cover of `P` is `pushMap`. -/
theorem eq_pushMap (A : PushoutTorsor r P) (B : PushoutTorsor r Q) (φ : P ⟶ Q)
    (f : A.sheaf ⟶ B.sheaf) (hf : f ≫ B.projection = A.projection)
    (hloc : ∀ {V : Scheme.{u}} (β : fppfYoneda.obj V ⟶ A.sheaf)
      (c : V ⟶ P.locallyTrivial.coverScheme),
      β ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover) →
      ∀ (h₁ : (β ≫ f) ≫ B.projection = (coverPt c ≫ φ.iso.hom) ≫ Q.projection)
        (h₂ : β ≫ A.projection = coverPt c ≫ P.projection),
        B.ev (β ≫ f) (coverPt c ≫ φ.iso.hom) h₁ = A.ev β (coverPt c) h₂) :
    f = pushMap A B φ := by
  refine hom_ext_of_cmp (fun α c hc => ?_)
  have hp : α ≫ A.projection = coverPt c ≫ P.projection := by rw [hc, coverPt_proj]
  have h₁ : (α ≫ f) ≫ B.projection = (coverPt c ≫ φ.iso.hom) ≫ Q.projection := by
    rw [Category.assoc, hf, hp, Category.assoc, φ.over]
  have h₂ : (α ≫ pushMap A B φ) ≫ B.projection = (coverPt c ≫ φ.iso.hom) ≫ Q.projection := by
    rw [Category.assoc, pushMap_proj, hp, Category.assoc, φ.over]
  exact B.ev_injective (coverPt c ≫ φ.iso.hom) h₁ h₂
    ((hloc α c hc h₁ hp).trans (ev_pushMap_cover A B φ α c hc h₂ hp).symm)

/-- The induced morphism only depends on the morphism of torsors. -/
theorem pushMap_congr (A : PushoutTorsor r P) (B : PushoutTorsor r Q) {φ ψ : P ⟶ Q}
    (h : φ = ψ) : pushMap A B φ = pushMap A B ψ := by
  subst h
  rfl

/-- **The pushout of the identity is the identity.** -/
theorem pushMap_id (A : PushoutTorsor r P) : pushMap A A (𝟙 P) = 𝟙 A.sheaf :=
  (eq_pushMap A A (𝟙 P) (𝟙 A.sheaf) (Category.id_comp _) fun β c _ h₁ h₂ =>
    A.ev_congr (Category.comp_id β) (by rw [FppfTorsor.id_iso_hom, Category.comp_id]) h₁ h₂).symm

/-- **The pushout of a composite is the composite of the pushouts.** -/
theorem pushMap_comp (A : PushoutTorsor r P) (B : PushoutTorsor r Q) (C : PushoutTorsor r R)
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    pushMap A B φ ≫ pushMap B C ψ = pushMap A C (φ ≫ ψ) := by
  refine eq_pushMap A C (φ ≫ ψ) (pushMap A B φ ≫ pushMap B C ψ) ?_ ?_
  · rw [Category.assoc, pushMap_proj, pushMap_proj]
  · intro V β c hc h₁ h₂
    have hQ : (β ≫ pushMap A B φ) ≫ B.projection = (coverPt c ≫ φ.iso.hom) ≫ Q.projection := by
      rw [Category.assoc, pushMap_proj, h₂, Category.assoc, φ.over]
    have h₃ : ((β ≫ pushMap A B φ) ≫ pushMap B C ψ) ≫ C.projection =
        ((coverPt c ≫ φ.iso.hom) ≫ ψ.iso.hom) ≫ R.projection := by
      rw [Category.assoc, pushMap_proj, hQ]
      simp only [Category.assoc, ψ.over]
    calc C.ev (β ≫ pushMap A B φ ≫ pushMap B C ψ) (coverPt c ≫ (φ ≫ ψ).iso.hom) h₁
        = C.ev ((β ≫ pushMap A B φ) ≫ pushMap B C ψ)
            ((coverPt c ≫ φ.iso.hom) ≫ ψ.iso.hom) h₃ :=
          C.ev_congr (Category.assoc _ _ _).symm
            (by rw [FppfTorsor.comp_iso_hom, Category.assoc]) h₁ h₃
      _ = B.ev (β ≫ pushMap A B φ) (coverPt c ≫ φ.iso.hom) hQ :=
          ev_pushMap B C ψ (β ≫ pushMap A B φ) (coverPt c ≫ φ.iso.hom) hQ h₃
      _ = A.ev β (coverPt c) h₂ := ev_pushMap_cover A B φ β c hc hQ h₂

/-- **The isomorphism of pushout data induced by a morphism of torsors.**  Every morphism of
`G`-torsors is invertible, so the induced morphism of pushouts is an isomorphism. -/
noncomputable def pushIso (A : PushoutTorsor r P) (B : PushoutTorsor r Q) (φ : P ⟶ Q) :
    A.sheaf ≅ B.sheaf where
  hom := pushMap A B φ
  inv := pushMap B A (Groupoid.inv φ)
  hom_inv_id := by
    rw [pushMap_comp A B A φ (Groupoid.inv φ),
      pushMap_congr A A (Groupoid.comp_inv φ), pushMap_id]
  inv_hom_id := by
    rw [pushMap_comp B A B (Groupoid.inv φ) φ,
      pushMap_congr B B (Groupoid.inv_comp φ), pushMap_id]

/-- The underlying morphism of the induced isomorphism. -/
@[simp]
theorem pushIso_hom (A : PushoutTorsor r P) (B : PushoutTorsor r Q) (φ : P ⟶ Q) :
    (pushIso A B φ).hom = pushMap A B φ :=
  rfl

end PushoutTorsor

/-! ### The pushout functor -/

section Functoriality

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {P Q R : FppfTorsor G T}

/-- **The pushout `r_* -` is functorial in the torsor.**  A morphism `φ : P ⟶ Q` of `G`-torsors
induces a morphism `r_* P ⟶ r_* Q` of the pushout `G'`-torsors. -/
noncomputable def pushoutMap (φ : P ⟶ Q) (r : G.space.toSheaf ⟶ G'.space.toSheaf)
    [IsMonHom r] : pushoutFppfTorsor P r ⟶ pushoutFppfTorsor Q r where
  iso := PushoutTorsor.pushIso (pushoutTorsor P r) (pushoutTorsor Q r) φ
  over := PushoutTorsor.pushMap_proj (pushoutTorsor P r) (pushoutTorsor Q r) φ
  equivariant := PushoutTorsor.pushMap_equivariant (pushoutTorsor P r) (pushoutTorsor Q r) φ

/-- The underlying morphism of sheaves of the induced morphism of pushout torsors. -/
@[simp]
theorem pushoutMap_iso_hom (φ : P ⟶ Q) (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r] :
    (pushoutMap φ r).iso.hom =
      PushoutTorsor.pushMap (pushoutTorsor P r) (pushoutTorsor Q r) φ :=
  rfl

/-- **The pushout preserves identities.** -/
theorem pushoutMap_id (P : FppfTorsor G T) (r : G.space.toSheaf ⟶ G'.space.toSheaf)
    [IsMonHom r] : pushoutMap (𝟙 P) r = 𝟙 (pushoutFppfTorsor P r) := by
  refine FppfTorsor.Hom.ext _ _ ?_
  rw [pushoutMap_iso_hom, FppfTorsor.id_iso_hom]
  exact PushoutTorsor.pushMap_id (pushoutTorsor P r)

/-- **The pushout preserves composition.** -/
theorem pushoutMap_comp (φ : P ⟶ Q) (ψ : Q ⟶ R)
    (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r] :
    pushoutMap (φ ≫ ψ) r = pushoutMap φ r ≫ pushoutMap ψ r := by
  refine FppfTorsor.Hom.ext _ _ ?_
  rw [pushoutMap_iso_hom, FppfTorsor.comp_iso_hom, pushoutMap_iso_hom, pushoutMap_iso_hom]
  exact (PushoutTorsor.pushMap_comp (pushoutTorsor P r) (pushoutTorsor Q r)
    (pushoutTorsor R r) φ ψ).symm

/-- **The pushout functor `r_* : FppfTorsor G T ⥤ FppfTorsor G' T`.** -/
noncomputable def pushoutFunctor (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r] :
    FppfTorsor G T ⥤ FppfTorsor G' T where
  obj P := pushoutFppfTorsor P r
  map φ := pushoutMap φ r
  map_id P := pushoutMap_id P r
  map_comp φ ψ := pushoutMap_comp φ ψ r

/-- The pushout functor on objects. -/
@[simp]
theorem pushoutFunctor_obj (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r]
    (P : FppfTorsor G T) : (pushoutFunctor (T := T) r).obj P = pushoutFppfTorsor P r :=
  rfl

/-- The pushout functor on morphisms. -/
@[simp]
theorem pushoutFunctor_map (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r] (φ : P ⟶ Q) :
    (pushoutFunctor (T := T) r).map φ = pushoutMap φ r :=
  rfl

end Functoriality

/-! ### Functoriality in the homomorphism -/

namespace PushoutTorsor

variable {G H K : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {P : FppfTorsor G T}

/-- **The torsor `P` is its own pushout along the identity homomorphism**: the evaluation pairing
of a point `α` against a point `p` is the difference point `α / p`. -/
noncomputable def idDatum (P : FppfTorsor G T) : PushoutTorsor (𝟙 G.space.toSheaf) P where
  sheaf := P.P
  action := P.action
  projection := P.projection
  action_over := P.action_over
  ev α p h := divPt P α p h
  ev_naturality u α p h h' :=
    comp_divPt (fppfYoneda.map u) α p h (by simpa only [Category.assoc] using h')
  ev_actPt g' α p h h' := divPt_actPt_left g' α p h h'
  ev_actPt_right := by
    intro W g α p h h'
    have hgp : actPt g p ≫ P.projection = p ≫ P.projection := actPt_proj P g p
    have h1 : divPt P (actPt g p) p hgp = g := by
      rw [divPt_actPt_left g p p rfl hgp, divPt_self, mul_one]
    have h2 : divPt P α (actPt g p) h' * divPt P (actPt g p) p hgp = divPt P α p h :=
      divPt_mul α (actPt g p) p h' hgp
    rw [Category.comp_id, ← h2, h1, mul_inv_cancel_right]
  ev_bijective := by
    intro W p g
    refine ⟨⟨actPt g p, actPt_proj P g p⟩, ?_, ?_⟩
    · change divPt P (actPt g p) p (actPt_proj P g p) = g
      rw [divPt_actPt_left g p p rfl (actPt_proj P g p), divPt_self, mul_one]
    · intro y hy
      have hy' : divPt P y.1 p y.2 = g := hy
      refine Subtype.ext ?_
      rw [← hy']
      exact (actPt_divPt y.1 p y.2).symm

/-! ### The unit point of a pushout datum -/

variable {s : G.space.toSheaf ⟶ H.space.toSheaf} {r : H.space.toSheaf ⟶ K.space.toSheaf}

/-- The point of a pushout datum over the base of `p` whose evaluation at `p` is the unit.  It is
the image of `p` under the canonical map `P ⟶ s_* P`. -/
noncomputable def unitPt (B : PushoutTorsor s P) {W : Scheme.{u}}
    (p : fppfYoneda.obj W ⟶ P.P) : fppfYoneda.obj W ⟶ B.sheaf :=
  (B.ev_bijective p 1).choose.1

/-- The unit point lies over the same base point as `p`. -/
theorem unitPt_proj (B : PushoutTorsor s P) {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P) :
    unitPt B p ≫ B.projection = p ≫ P.projection :=
  (B.ev_bijective p 1).choose.2

/-- The evaluation of the unit point at `p` is the unit. -/
theorem ev_unitPt (B : PushoutTorsor s P) {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P) :
    B.ev (unitPt B p) p (unitPt_proj B p) = 1 :=
  (B.ev_bijective p 1).choose_spec.1

/-- **Characterisation of the unit point.** -/
theorem eq_unitPt (B : PushoutTorsor s P) {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (β : fppfYoneda.obj W ⟶ B.sheaf) (hβ : β ≫ B.projection = p ≫ P.projection)
    (h : B.ev β p hβ = 1) : β = unitPt B p :=
  B.ev_injective p hβ (unitPt_proj B p) (h.trans (ev_unitPt B p).symm)

/-- The unit point is natural in the test scheme. -/
theorem comp_unitPt (B : PushoutTorsor s P) {V W : Scheme.{u}} (u : V ⟶ W)
    (p : fppfYoneda.obj W ⟶ P.P) :
    fppfYoneda.map u ≫ unitPt B p = unitPt B (fppfYoneda.map u ≫ p) := by
  have hproj : (fppfYoneda.map u ≫ unitPt B p) ≫ B.projection =
      (fppfYoneda.map u ≫ p) ≫ P.projection := by
    simp only [Category.assoc]
    rw [unitPt_proj]
  refine eq_unitPt B _ _ hproj ?_
  rw [← B.ev_naturality u (unitPt B p) p (unitPt_proj B p) hproj, ev_unitPt, MonObj.comp_one]

/-- The unit point of a translated point is translated through `s`. -/
theorem unitPt_actPt (B : PushoutTorsor s P) {W : Scheme.{u}}
    (g : fppfYoneda.obj W ⟶ G.space.toSheaf) (p : fppfYoneda.obj W ⟶ P.P) :
    unitPt B (actPt g p) = actPt (g ≫ s) (unitPt B p) := by
  have hq : unitPt B p ≫ B.projection = actPt g p ≫ P.projection := by
    rw [unitPt_proj, actPt_proj]
  have hp : actPt (g ≫ s) (unitPt B p) ≫ B.projection = actPt g p ≫ P.projection := by
    rw [B.actPt_projection]
    exact hq
  refine (eq_unitPt B (actPt g p) (actPt (g ≫ s) (unitPt B p)) hp ?_).symm
  rw [B.ev_actPt (g ≫ s) (unitPt B p) (actPt g p) hq hp,
    B.ev_actPt_right g (unitPt B p) p (unitPt_proj B p) hq, ev_unitPt, one_mul, mul_inv_cancel]

/-! ### The iterated pushout -/

/-- **The iterated pushout is a pushout datum for the composite homomorphism.**  If `B` is a
pushout datum for `P` along `s : G ⟶ H` and `C` is a pushout datum for `B` along
`r : H ⟶ K`, then `C` is a pushout datum for `P` along `s ≫ r`, with the evaluation pairing
`ev z p := C.ev z (unitPt B p)`. -/
noncomputable def compDatum (B : PushoutTorsor s P) (C : PushoutTorsor r B.toFppfTorsor) :
    PushoutTorsor (s ≫ r) P where
  sheaf := C.sheaf
  action := C.action
  projection := C.projection
  action_over := C.action_over
  ev := fun {_} z p h => C.ev z (unitPt B p) (h.trans (unitPt_proj B p).symm)
  ev_naturality := by
    intro V W u z p h h'
    have e : (fppfYoneda.map u ≫ unitPt B p) ≫ B.projection =
        (fppfYoneda.map u ≫ p) ≫ P.projection := by
      simp only [Category.assoc]
      rw [unitPt_proj]
    exact (C.ev_naturality u z (unitPt B p) (h.trans (unitPt_proj B p).symm)
      (h'.trans e.symm)).trans
      (C.ev_congr_right _ (comp_unitPt B u p) (h'.trans e.symm)
        (h'.trans (unitPt_proj B (fppfYoneda.map u ≫ p)).symm))
  ev_actPt := by
    intro W k z p h h'
    exact C.ev_actPt k z (unitPt B p) (h.trans (unitPt_proj B p).symm)
      ((C.actPt_projection k z).trans (h.trans (unitPt_proj B p).symm))
  ev_actPt_right := by
    intro W g z p h h'
    have hB : z ≫ C.projection = unitPt B p ≫ B.projection := h.trans (unitPt_proj B p).symm
    have hB' : z ≫ C.projection = actPt (g ≫ s) (unitPt B p) ≫ B.projection :=
      hB.trans (B.actPt_projection (g ≫ s) (unitPt B p)).symm
    refine (C.ev_congr_right z (unitPt_actPt B g p)
      (h'.trans (unitPt_proj B (actPt g p)).symm) hB').trans
      ((C.ev_actPt_right (g ≫ s) z (unitPt B p) hB hB').trans ?_)
    exact congrArg (fun x => C.ev z (unitPt B p) hB * x⁻¹) (Category.assoc g s r)
  ev_bijective := by
    intro W p k
    obtain ⟨⟨z, hz⟩, hzk, huniq⟩ := C.ev_bijective (unitPt B p) k
    refine ⟨⟨z, hz.trans (unitPt_proj B p)⟩, hzk, ?_⟩
    intro y hy
    obtain ⟨δ, hδ⟩ := y
    have hδ' : δ ≫ C.projection = unitPt B p ≫ B.toFppfTorsor.projection :=
      hδ.trans (unitPt_proj B p).symm
    have hδz : δ = z := congrArg Subtype.val (huniq ⟨δ, hδ'⟩ hy)
    exact Subtype.ext hδz

end PushoutTorsor

/-! ### The pushout along the identity and along a composite -/

section HomFunctoriality

variable {G H K : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}

/-- **The pushout along the identity homomorphism is the torsor itself**, as a morphism of
`G`-torsors. -/
noncomputable def pushoutIdHom (P : FppfTorsor G T) :
    pushoutFppfTorsor P (𝟙 G.space.toSheaf) ⟶ P where
  iso := PushoutTorsor.compareIso (pushoutTorsor P (𝟙 G.space.toSheaf)) (PushoutTorsor.idDatum P)
  over := PushoutTorsor.cmpMap_proj (pushoutTorsor P (𝟙 G.space.toSheaf))
    (PushoutTorsor.idDatum P)
  equivariant := PushoutTorsor.cmpMap_equivariant (pushoutTorsor P (𝟙 G.space.toSheaf))
    (PushoutTorsor.idDatum P)

/-- **`(𝟙 G)_* P ≅ P`.**  The pushout of a `G`-torsor along the identity homomorphism of `G` is
the torsor itself. -/
noncomputable def pushoutIdIso (P : FppfTorsor G T) :
    pushoutFppfTorsor P (𝟙 G.space.toSheaf) ≅ P :=
  ⟨pushoutIdHom P, Groupoid.inv (pushoutIdHom P), Groupoid.comp_inv _, Groupoid.inv_comp _⟩

variable (s : G.space.toSheaf ⟶ H.space.toSheaf) [IsMonHom s]
  (r : H.space.toSheaf ⟶ K.space.toSheaf) [IsMonHom r]

/-- **The pushout along a composite is the iterated pushout**, as a morphism of `K`-torsors. -/
noncomputable def pushoutCompHom (P : FppfTorsor G T) :
    pushoutFppfTorsor P (s ≫ r) ⟶ pushoutFppfTorsor (pushoutFppfTorsor P s) r where
  iso := PushoutTorsor.compareIso (pushoutTorsor P (s ≫ r))
    (PushoutTorsor.compDatum (pushoutTorsor P s) (pushoutTorsor (pushoutFppfTorsor P s) r))
  over := PushoutTorsor.cmpMap_proj (pushoutTorsor P (s ≫ r))
    (PushoutTorsor.compDatum (pushoutTorsor P s) (pushoutTorsor (pushoutFppfTorsor P s) r))
  equivariant := PushoutTorsor.cmpMap_equivariant (pushoutTorsor P (s ≫ r))
    (PushoutTorsor.compDatum (pushoutTorsor P s) (pushoutTorsor (pushoutFppfTorsor P s) r))

/-- **`(s ≫ r)_* P ≅ r_* (s_* P)`.**  The pushout along a composite homomorphism is the iterated
pushout. -/
noncomputable def pushoutCompIso (P : FppfTorsor G T) :
    pushoutFppfTorsor P (s ≫ r) ≅ pushoutFppfTorsor (pushoutFppfTorsor P s) r :=
  ⟨pushoutCompHom s r P, Groupoid.inv (pushoutCompHom s r P), Groupoid.comp_inv _,
    Groupoid.inv_comp _⟩

end HomFunctoriality

/-! ### Compatibility of the pushout with base change -/

namespace PushoutTorsor

variable {G G' : AlgebraicSpaceGroup.{u}} {T T' : Scheme.{u}} {P : FppfTorsor G T}
  {r : G.space.toSheaf ⟶ G'.space.toSheaf}

-- The action on a base-changed torsor is not an instance globally; make it one here so that the
-- statements below about points of base-changed torsors elaborate.
attribute [local instance] FppfTorsor.pullbackAction

/-- The first projection of a base-changed torsor is `G`-equivariant, on points. -/
theorem actPt_pullback_fst (X : FppfTorsor G T) (b : T' ⟶ T) {Z : FppfSheaf.{u}}
    (g : Z ⟶ G.space.toSheaf) (α : Z ⟶ (X.pullbackTorsor b).P) :
    actPt g α ≫ Limits.pullback.fst X.projection (fppfYoneda.map b) =
      actPt g (α ≫ Limits.pullback.fst X.projection (fppfYoneda.map b)) :=
  actPt_comp_equivariant (X := (X.pullbackTorsor b).P) (Y := X.P)
    (Limits.pullback.fst X.projection (fppfYoneda.map b)) (FppfTorsor.pullbackSmul_fst X b) g α

/-- Two points of base-changed torsors lying over the same point of the new base have first
projections lying over the same point of the old base. -/
theorem pullback_ev_cond (A : PushoutTorsor r P) (b : T' ⟶ T) {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ (A.toFppfTorsor.pullbackTorsor b).P)
    (p : fppfYoneda.obj W ⟶ (P.pullbackTorsor b).P)
    (h : α ≫ (A.toFppfTorsor.pullbackTorsor b).projection =
      p ≫ (P.pullbackTorsor b).projection) :
    (α ≫ Limits.pullback.fst A.toFppfTorsor.projection (fppfYoneda.map b)) ≫
        A.toFppfTorsor.projection =
      (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ P.projection := by
  rw [Category.assoc, Limits.pullback.condition, Category.assoc, Limits.pullback.condition,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (fun x => x ≫ fppfYoneda.map b) h

/-- **The base change of a pushout datum.**  If `A` is a pushout datum for the `G`-torsor `P`
along `r`, then the base change of `A` along `b : T' ⟶ T` is a pushout datum for the base change
of `P`: a point of `r_* P` over `T'` evaluates at a point of `P` over `T'` through their first
projections. -/
noncomputable def pullbackDatum (A : PushoutTorsor r P) (b : T' ⟶ T) :
    PushoutTorsor r (P.pullbackTorsor b) where
  sheaf := FppfTorsor.pullbackSheaf A.toFppfTorsor b
  action := FppfTorsor.pullbackAction A.toFppfTorsor b
  projection := Limits.pullback.snd A.toFppfTorsor.projection (fppfYoneda.map b)
  action_over := FppfTorsor.pullbackSmul_snd A.toFppfTorsor b
  ev := fun {_} α p h =>
    A.ev (α ≫ Limits.pullback.fst A.toFppfTorsor.projection (fppfYoneda.map b))
      (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) (pullback_ev_cond A b α p h)
  ev_naturality := by
    intro V W u α p h h'
    exact (A.ev_naturality u (α ≫ Limits.pullback.fst A.toFppfTorsor.projection
        (fppfYoneda.map b)) (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))
        (pullback_ev_cond A b α p h) (by
          simp only [Category.assoc]
          exact pullback_ev_cond A b (fppfYoneda.map u ≫ α) (fppfYoneda.map u ≫ p) (by
            simpa only [Category.assoc] using h'))).trans
      (A.ev_congr (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm _
        (pullback_ev_cond A b (fppfYoneda.map u ≫ α) (fppfYoneda.map u ≫ p) h'))
  ev_actPt := by
    intro W g' α p h h'
    refine (A.ev_congr (actPt_pullback_fst A.toFppfTorsor b g' α) rfl
      (pullback_ev_cond A b (actPt g' α) p h') ?_).trans
      (A.ev_actPt g' (α ≫ Limits.pullback.fst A.toFppfTorsor.projection (fppfYoneda.map b))
        (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))
        (pullback_ev_cond A b α p h) ?_)
    · exact (A.actPt_projection g' _).trans (pullback_ev_cond A b α p h)
    · exact (A.actPt_projection g' _).trans (pullback_ev_cond A b α p h)
  ev_actPt_right := by
    intro W g α p h h'
    refine (A.ev_congr rfl (actPt_pullback_fst P b g p)
      (pullback_ev_cond A b α (actPt g p) h') ?_).trans
      (A.ev_actPt_right g (α ≫ Limits.pullback.fst A.toFppfTorsor.projection (fppfYoneda.map b))
        (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))
        (pullback_ev_cond A b α p h) ?_)
    · exact (pullback_ev_cond A b α p h).trans
        (actPt_proj P g (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))).symm
    · exact (pullback_ev_cond A b α p h).trans
        (actPt_proj P g (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))).symm
  ev_bijective := by
    intro W p g'
    obtain ⟨⟨β, hβ⟩, hβg, hβu⟩ :=
      A.ev_bijective (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) g'
    have hcond : β ≫ A.projection =
        (p ≫ Limits.pullback.snd P.projection (fppfYoneda.map b)) ≫ fppfYoneda.map b := by
      rw [hβ, Category.assoc, Limits.pullback.condition, ← Category.assoc]
    refine ⟨⟨Limits.pullback.lift β (p ≫ Limits.pullback.snd P.projection (fppfYoneda.map b))
      hcond, Limits.pullback.lift_snd _ _ _⟩, ?_, ?_⟩
    · exact (A.ev_congr (Limits.pullback.lift_fst _ _ _) rfl _ hβ).trans hβg
    · intro y hy
      obtain ⟨δ, hδ⟩ := y
      have hδβ : δ ≫ Limits.pullback.fst A.toFppfTorsor.projection (fppfYoneda.map b) = β :=
        congrArg Subtype.val (hβu ⟨δ ≫ Limits.pullback.fst A.toFppfTorsor.projection
          (fppfYoneda.map b), pullback_ev_cond A b δ p hδ⟩ hy)
      exact Subtype.ext (Limits.pullback.hom_ext
        (hδβ.trans (Limits.pullback.lift_fst _ _ _).symm)
        (hδ.trans (Limits.pullback.lift_snd _ _ _).symm))

/-- **The pushout commutes with base change.**  The pushout of the base change of `P` is the base
change of the pushout of `P`, as a morphism of `G'`-torsors over `T'`. -/
noncomputable def pushoutPullbackHom (P : FppfTorsor G T)
    (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r] (b : T' ⟶ T) :
    pushoutFppfTorsor (P.pullbackTorsor b) r ⟶ (pushoutFppfTorsor P r).pullbackTorsor b where
  iso := compareIso (pushoutTorsor (P.pullbackTorsor b) r) (pullbackDatum (pushoutTorsor P r) b)
  over := cmpMap_proj (pushoutTorsor (P.pullbackTorsor b) r) (pullbackDatum (pushoutTorsor P r) b)
  equivariant := cmpMap_equivariant (pushoutTorsor (P.pullbackTorsor b) r)
    (pullbackDatum (pushoutTorsor P r) b)

/-- The first projection of a base-changed torsor is `G`-equivariant on points. -/
theorem isEquivariantPt_pullback_fst (X : FppfTorsor G T) (b : T' ⟶ T) :
    IsEquivariantPt (P := X.pullbackTorsor b) (Q := X)
      (Limits.pullback.fst X.projection (fppfYoneda.map b)) :=
  fun _ g α => actPt_pullback_fst X b g α

/-- The base-change comparison of the pushouts, followed by the projection to the pushout over
the original base. -/
noncomputable def pushoutPullbackFst (X : FppfTorsor G T)
    (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r] (b : T' ⟶ T) :
    pushoutSheaf (X.pullbackTorsor b) r ⟶ pushoutSheaf X r :=
  (pushoutPullbackHom X r b).iso.hom ≫
    Limits.pullback.fst (pushoutFppfTorsor X r).projection (fppfYoneda.map b)

/-- The base change of a point of the pushout of a base-changed torsor lies over the expected
base point. -/
theorem pushoutPullbackFst_cond (X : FppfTorsor G T)
    (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r] (b : T' ⟶ T) {W : Scheme.{u}}
    (β : fppfYoneda.obj W ⟶ (pushoutTorsor (X.pullbackTorsor b) r).sheaf)
    (q : fppfYoneda.obj W ⟶ (X.pullbackTorsor b).P)
    (hq : β ≫ (pushoutTorsor (X.pullbackTorsor b) r).projection =
      q ≫ (X.pullbackTorsor b).projection) :
    (β ≫ pushoutPullbackFst X r b) ≫ (pushoutTorsor X r).projection =
      (q ≫ Limits.pullback.fst X.projection (fppfYoneda.map b)) ≫ X.projection := by
  have hY : (β ≫ (pushoutPullbackHom X r b).iso.hom) ≫
      Limits.pullback.snd (pushoutFppfTorsor X r).projection (fppfYoneda.map b) =
      q ≫ (X.pullbackTorsor b).projection :=
    ((Category.assoc β _ _).trans (congrArg (fun x => β ≫ x)
      (cmpMap_proj (pushoutTorsor (X.pullbackTorsor b) r)
        (pullbackDatum (pushoutTorsor X r) b)))).trans hq
  exact (congrArg (fun x => x ≫ (pushoutTorsor X r).projection)
    (Category.assoc β _ _).symm).trans
    (pullback_ev_cond (pushoutTorsor X r) b (β ≫ (pushoutPullbackHom X r b).iso.hom) q hY)

/-- **The base-change comparison computes the evaluation pairing through the first projections**,
at every point of the base-changed torsor.  This is the characterisation of
`pushoutPullbackHom` used to prove its compatibilities. -/
theorem ev_pushoutPullbackFst (X : FppfTorsor G T)
    (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r] (b : T' ⟶ T) {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ (pushoutTorsor (X.pullbackTorsor b) r).sheaf)
    (p : fppfYoneda.obj W ⟶ (X.pullbackTorsor b).P)
    (h : α ≫ (pushoutTorsor (X.pullbackTorsor b) r).projection =
      p ≫ (X.pullbackTorsor b).projection)
    (h' : (α ≫ pushoutPullbackFst X r b) ≫ (pushoutTorsor X r).projection =
      (p ≫ Limits.pullback.fst X.projection (fppfYoneda.map b)) ≫ X.projection) :
    (pushoutTorsor X r).ev (α ≫ pushoutPullbackFst X r b)
        (p ≫ Limits.pullback.fst X.projection (fppfYoneda.map b)) h' =
      (pushoutTorsor (X.pullbackTorsor b) r).ev α p h := by
  refine ev_eq_of_ev_cover_over (pushoutTorsor (X.pullbackTorsor b) r) (pushoutTorsor X r)
    (isEquivariantPt_pullback_fst X b) (pushoutPullbackFst X r b)
    (fun β q hq => pushoutPullbackFst_cond X r b β q hq) (fun β c hc h₁ h₂ => ?_) α p h h'
  have hY : (β ≫ (pushoutPullbackHom X r b).iso.hom) ≫
      Limits.pullback.snd (pushoutFppfTorsor X r).projection (fppfYoneda.map b) =
      coverPt c ≫ (X.pullbackTorsor b).projection :=
    ((Category.assoc β _ _).trans (congrArg (fun x => β ≫ x)
      (cmpMap_proj (pushoutTorsor (X.pullbackTorsor b) r)
        (pullbackDatum (pushoutTorsor X r) b)))).trans h₂
  have hkey : (pullbackDatum (pushoutTorsor X r) b).ev
        (β ≫ (pushoutPullbackHom X r b).iso.hom) (coverPt c) hY =
      (pushoutTorsor (X.pullbackTorsor b) r).ev β (coverPt c) h₂ :=
    ((pullbackDatum (pushoutTorsor X r) b).ev_congr
      (cmpMap_spec (pushoutTorsor (X.pullbackTorsor b) r)
        (pullbackDatum (pushoutTorsor X r) b) β c hc) rfl hY
      (cmpLocal_proj β c hc)).trans (ev_cmpLocal β c hc)
  exact ((pushoutTorsor X r).ev_congr (Category.assoc β _ _).symm rfl h₁
    (pullback_ev_cond (pushoutTorsor X r) b
      (β ≫ (pushoutPullbackHom X r b).iso.hom) (coverPt c) hY)).trans hkey

/-- **The base-change comparison is natural in the torsor.**  If `φ' : b^* P ⟶ b^* Q` is the base
change of a morphism `φ : P ⟶ Q` of `G`-torsors, then the square formed by `φ'`, `φ` and the
base-change comparisons of the pushouts commutes.  Both composites are computed by
`ev_pushoutPullbackFst` and `ev_pushMap` at the tautological points of the trivialising cover of
`b^* P`, where they agree. -/
theorem pushMap_comp_pushoutPullbackFst {P Q : FppfTorsor G T} (φ : P ⟶ Q)
    (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r] (b : T' ⟶ T)
    (φ' : P.pullbackTorsor b ⟶ Q.pullbackTorsor b)
    (hφ' : φ'.iso.hom = FppfTorsor.pullbackMap b φ.iso.hom φ.over) :
    pushMap (pushoutTorsor (P.pullbackTorsor b) r) (pushoutTorsor (Q.pullbackTorsor b) r) φ' ≫
        pushoutPullbackFst Q r b =
      pushoutPullbackFst P r b ≫ pushMap (pushoutTorsor P r) (pushoutTorsor Q r) φ := by
  refine hom_ext_of_cmp (fun α c hc => ?_)
  have hcov : α ≫ (pushoutTorsor (P.pullbackTorsor b) r).projection =
      coverPt c ≫ (P.pullbackTorsor b).projection :=
    hc.trans (coverPt_proj c).symm
  have hP : (α ≫ pushoutPullbackFst P r b) ≫ (pushoutTorsor P r).projection =
      (coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ P.projection :=
    pushoutPullbackFst_cond P r b α (coverPt c) hcov
  have hQ' : (α ≫ pushMap (pushoutTorsor (P.pullbackTorsor b) r)
        (pushoutTorsor (Q.pullbackTorsor b) r) φ') ≫
        (pushoutTorsor (Q.pullbackTorsor b) r).projection =
      (coverPt c ≫ φ'.iso.hom) ≫ (Q.pullbackTorsor b).projection := by
    rw [Category.assoc, pushMap_proj, hcov, Category.assoc, φ'.over]
  have hQ'' : ((α ≫ pushMap (pushoutTorsor (P.pullbackTorsor b) r)
        (pushoutTorsor (Q.pullbackTorsor b) r) φ') ≫ pushoutPullbackFst Q r b) ≫
        (pushoutTorsor Q r).projection =
      ((coverPt c ≫ φ'.iso.hom) ≫
        Limits.pullback.fst Q.projection (fppfYoneda.map b)) ≫ Q.projection :=
    pushoutPullbackFst_cond Q r b _ _ hQ'
  have hR : ((α ≫ pushoutPullbackFst P r b) ≫
        pushMap (pushoutTorsor P r) (pushoutTorsor Q r) φ) ≫ (pushoutTorsor Q r).projection =
      ((coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫
        φ.iso.hom) ≫ Q.projection :=
    (((Category.assoc (α ≫ pushoutPullbackFst P r b) _ _).trans
      (congrArg (fun x => (α ≫ pushoutPullbackFst P r b) ≫ x)
        (pushMap_proj (pushoutTorsor P r) (pushoutTorsor Q r) φ))).trans hP).trans
      ((Category.assoc (coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))
        φ.iso.hom Q.projection).trans (congrArg (fun x =>
          (coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ x) φ.over)).symm
  have hpt : (coverPt c ≫ φ'.iso.hom) ≫
        Limits.pullback.fst Q.projection (fppfYoneda.map b) =
      (coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ φ.iso.hom := by
    rw [hφ', Category.assoc, FppfTorsor.pullbackMap_fst, Category.assoc]
  have hL : (α ≫ (pushMap (pushoutTorsor (P.pullbackTorsor b) r)
        (pushoutTorsor (Q.pullbackTorsor b) r) φ' ≫ pushoutPullbackFst Q r b)) ≫
        (pushoutTorsor Q r).projection =
      ((coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫
        φ.iso.hom) ≫ Q.projection :=
    ((congrArg (fun x => x ≫ (pushoutTorsor Q r).projection)
      (Category.assoc α _ _).symm).trans hQ'').trans
      (congrArg (fun x => x ≫ Q.projection) hpt)
  have hR2 : (α ≫ (pushoutPullbackFst P r b ≫
        pushMap (pushoutTorsor P r) (pushoutTorsor Q r) φ)) ≫ (pushoutTorsor Q r).projection =
      ((coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫
        φ.iso.hom) ≫ Q.projection :=
    (congrArg (fun x => x ≫ (pushoutTorsor Q r).projection)
      (Category.assoc α _ _).symm).trans hR
  have hevL : (pushoutTorsor Q r).ev ((α ≫ pushMap (pushoutTorsor (P.pullbackTorsor b) r)
        (pushoutTorsor (Q.pullbackTorsor b) r) φ') ≫ pushoutPullbackFst Q r b)
        ((coverPt c ≫ φ'.iso.hom) ≫
          Limits.pullback.fst Q.projection (fppfYoneda.map b)) hQ'' =
      (pushoutTorsor (P.pullbackTorsor b) r).ev α (coverPt c) hcov :=
    (ev_pushoutPullbackFst Q r b _ (coverPt c ≫ φ'.iso.hom) hQ' hQ'').trans
      (ev_pushMap_cover (pushoutTorsor (P.pullbackTorsor b) r)
        (pushoutTorsor (Q.pullbackTorsor b) r) φ' α c hc hQ' hcov)
  have hevR : (pushoutTorsor Q r).ev ((α ≫ pushoutPullbackFst P r b) ≫
        pushMap (pushoutTorsor P r) (pushoutTorsor Q r) φ)
        ((coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ φ.iso.hom) hR =
      (pushoutTorsor (P.pullbackTorsor b) r).ev α (coverPt c) hcov :=
    (ev_pushMap (pushoutTorsor P r) (pushoutTorsor Q r) φ (α ≫ pushoutPullbackFst P r b)
      (coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) hP hR).trans
      (ev_pushoutPullbackFst P r b α (coverPt c) hcov hP)
  refine (pushoutTorsor Q r).ev_injective
    ((coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ φ.iso.hom) hL hR2 ?_
  exact (((pushoutTorsor Q r).ev_congr (Category.assoc α _ _).symm hpt.symm hL hQ'').trans
    hevL).trans (hevR.symm.trans
      ((pushoutTorsor Q r).ev_congr (Category.assoc α _ _) rfl hR hR2))

/-- The underlying morphism of sheaves of the base-change comparison. -/
@[simp]
theorem pushoutPullbackHom_iso_hom (P : FppfTorsor G T)
    (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r] (b : T' ⟶ T) :
    (pushoutPullbackHom P r b).iso.hom =
      cmpMap (pushoutTorsor (P.pullbackTorsor b) r) (pullbackDatum (pushoutTorsor P r) b) :=
  rfl

end PushoutTorsor

section BaseChange

variable {G G' : AlgebraicSpaceGroup.{u}} {T T' : Scheme.{u}}

/-- **`r_* (b^* P) ≅ b^* (r_* P)`.**  The pushout of an fppf torsor commutes with base change
along an arbitrary morphism of schemes. -/
noncomputable def pushoutPullbackIso (P : FppfTorsor G T)
    (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r] (b : T' ⟶ T) :
    pushoutFppfTorsor (P.pullbackTorsor b) r ≅ (pushoutFppfTorsor P r).pullbackTorsor b :=
  ⟨PushoutTorsor.pushoutPullbackHom P r b,
    Groupoid.inv (PushoutTorsor.pushoutPullbackHom P r b), Groupoid.comp_inv _,
    Groupoid.inv_comp _⟩

end BaseChange

/-! ### The induced equivariant map at an arbitrary point of the torsor -/

section TargetPoint

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {U : AlgebraicSpaceAction G}
  {U' : AlgebraicSpaceAction G'} (P : ActionTorsor G U T)
  (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r]
  {pt : U.space.toSheaf ⟶ U'.space.toSheaf} (hpt : IsEquivariantOver r pt)

/-- **The induced equivariant map `r_* P ⟶ U'` evaluated at an arbitrary point.**  The local
formula `α ↦ (ev α p) · pt (p)` computing `targetMap` holds at *every* point `p` of `P` over the
same base point, not only at the tautological points of the trivialising cover. -/
theorem comp_targetMap_pt {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor r) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ pushoutProj P.toFppfTorsor r = p ≫ P.projection) :
    α ≫ targetMap P r pt hpt = actPt (evPt P.toFppfTorsor r α p h) (p ≫ P.target ≫ pt) := by
  have hbase : α ≫ pushoutProj P.toFppfTorsor r =
      fppfYoneda.map (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P.toFppfTorsor r)) :=
    (fppfYoneda_map_yonedaEquiv _).symm
  refine hom_ext_of_sieve_pt (pullback_coverSieve_mem P.toFppfTorsor
    (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P.toFppfTorsor r))) fun V u hu => ?_
  obtain ⟨c, hcu⟩ := exists_lift_of_pullback hu
  have hα : (fppfYoneda.map u ≫ α) ≫ pushoutProj P.toFppfTorsor r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hbase, ← CategoryTheory.Functor.map_comp, hcu]
  have hcov : (fppfYoneda.map u ≫ α) ≫ pushoutProj P.toFppfTorsor r =
      coverPt c ≫ P.projection := by rw [hα, coverPt_proj]
  have hp : (fppfYoneda.map u ≫ α) ≫ pushoutProj P.toFppfTorsor r =
      (fppfYoneda.map u ≫ p) ≫ P.projection := by
    simp only [Category.assoc]
    rw [h]
  have hL : fppfYoneda.map u ≫ α ≫ targetMap P r pt hpt =
      actPt (evPt P.toFppfTorsor r (fppfYoneda.map u ≫ α) (coverPt c) hcov)
        (coverPt c ≫ P.target ≫ pt) := by
    rw [← Category.assoc]
    exact comp_targetMap hpt (fppfYoneda.map u ≫ α) c hα
  have hd : actPt (divPt P.toFppfTorsor (fppfYoneda.map u ≫ p) (coverPt c) (hp.symm.trans hcov))
      (coverPt c) = fppfYoneda.map u ≫ p :=
    actPt_divPt _ _ _
  have hev : evPt P.toFppfTorsor r (fppfYoneda.map u ≫ α) (fppfYoneda.map u ≫ p) hp =
      evPt P.toFppfTorsor r (fppfYoneda.map u ≫ α) (coverPt c) hcov *
        (divPt P.toFppfTorsor (fppfYoneda.map u ≫ p) (coverPt c)
          (hp.symm.trans hcov) ≫ r)⁻¹ :=
    (pushoutTorsor P.toFppfTorsor r).ev_congr_pt (fppfYoneda.map u ≫ α) _ _ hp hcov
  have htarget : (fppfYoneda.map u ≫ p) ≫ P.target ≫ pt =
      actPt (divPt P.toFppfTorsor (fppfYoneda.map u ≫ p) (coverPt c)
        (hp.symm.trans hcov) ≫ r) (coverPt c ≫ P.target ≫ pt) := by
    calc (fppfYoneda.map u ≫ p) ≫ P.target ≫ pt
        = actPt (divPt P.toFppfTorsor (fppfYoneda.map u ≫ p) (coverPt c)
            (hp.symm.trans hcov)) (coverPt c) ≫ P.target ≫ pt := by rw [hd]
      _ = actPt (divPt P.toFppfTorsor (fppfYoneda.map u ≫ p) (coverPt c)
            (hp.symm.trans hcov)) (coverPt c ≫ P.target) ≫ pt := by
            rw [← Category.assoc, actPt_comp_target]
      _ = actPt (divPt P.toFppfTorsor (fppfYoneda.map u ≫ p) (coverPt c)
            (hp.symm.trans hcov) ≫ r) ((coverPt c ≫ P.target) ≫ pt) :=
            hpt _ (coverPt c ≫ P.target)
      _ = actPt (divPt P.toFppfTorsor (fppfYoneda.map u ≫ p) (coverPt c)
            (hp.symm.trans hcov) ≫ r) (coverPt c ≫ P.target ≫ pt) := by
            rw [Category.assoc (coverPt c) P.target pt]
  rw [hL, comp_actPt, comp_evPt u α p h hp, ← Category.assoc (fppfYoneda.map u) p
    (P.target ≫ pt), hev, htarget, ← actPt_mul, inv_mul_cancel_right]

end TargetPoint

end TorsorPushout

end GromovWitten.AlgebraicGeometry
