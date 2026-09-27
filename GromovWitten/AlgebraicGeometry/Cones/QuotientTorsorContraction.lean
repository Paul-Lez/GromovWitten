/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.QuotientTorsorStack
import GromovWitten.AlgebraicGeometry.Stacks.TorsorPushoutFunctoriality
import GromovWitten.AlgebraicGeometry.Stacks.QuotientStackGroupMaps
import GromovWitten.AlgebraicGeometry.Stacks.TorsorPushoutRelative

/-!
# The unconditional scalar contraction on `[C/E]`, as a functor

`Cones/QuotientTorsorStack.lean` constructs the scalar contraction of the affine cone quotient
`[C/E]` only on trivialised torsors (`ConeQuotient.coneTwist`), transporting it to the whole
torsor groupoid `ActionTorsor G U T` only under the hypothesis `AllTorsorsTrivial G T`, because
(its own docstring) "the pushout torsor `r_* P` for a general torsor `P` is not constructed".

## The obstruction to the naively expected route, and how it is avoided

A first guess for removing the hypothesis is to package scalar multiplication by
`r : Γ(T, 𝒪)` as an *absolute* homomorphism `scalarHom r : G.space.toSheaf ⟶ G.space.toSheaf` of
the vector bundle group `G = vectorBundleGroup σ` (independent of `T`) and invoke the general
pushout functoriality of `Stacks/TorsorPushoutFunctoriality.lean` and
`Stacks/QuotientStackGroupMaps.lean`.
This is impossible in general: `G.space.toSheaf` is the fppf sheaf represented by the *absolute*
scheme `𝔸^σ`, so by the fppf-Yoneda lemma every sheaf endomorphism `G.space.toSheaf ⟶
G.space.toSheaf` is `fppfYoneda.map` of an honest scheme endomorphism of `𝔸^σ`, natural in *every*
test scheme `S`, not merely in schemes over `T`. Multiplication by a section `r : Γ(T, 𝒪)`
depends on `T` and cannot define such a natural transformation unless `r` comes from a genuinely
global scalar (already handled by `ConeQuotient.scaleRing_algebraMap`): for a general test ring
this is exactly the obstruction recorded in `Stacks/TorsorPushout.lean`'s docstring, and no
`scalarHom r : G ⟶ G` exists.

`Stacks/TorsorPushoutRelative.lean` (already in the repository, from an earlier round) resolves
this correctly: multiplication by `r` is a homomorphism of group objects only *relative to* `T`
(`TorsorPushoutRel.RelMonHom`, a single morphism `G ⊗ y(T) ⟶ G` of fppf sheaves), and its pushout
`TorsorPushoutRel.PushoutTorsorRel` is built with no sheafification and no triviality hypothesis.
It already supplies the *object* map `TorsorPushoutRel.coneContraction`, matching `coneTwist` on
`TrivialPoint` (`TorsorPushoutRel.coneContractionEmbeddingIso`), but stops there: its own
docstring records that "the functoriality of `ρ_*` on arrows of torsors ... is not done".

This file supplies exactly that functoriality, for the *relative* pushout, mirroring the
comparison engine of `Stacks/TorsorPushoutFunctoriality.lean` (`cmpLocal`/`cmpMap`/`compareIso`
for the uniqueness of a pushout datum, then `reindexAlong`/`pushMap` for functoriality in the
torsor) with the absolute homomorphism `r` everywhere replaced by the relative pairing `ρ.pt`.
The torsor-level engine (`TorsorPushout.PushoutTorsor.IsEquivariantPt`,
`divPt_comp_of_isEquivariantPt`, `isEquivariantPt_iso_hom`, `divPt_comp_iso`) does not mention
`r` at all and is reused verbatim.

## Main results

* `TorsorPushoutRel.PushoutTorsorRel.compareIso`: uniqueness of a pushout datum for the relative
  pushout (the relative analogue of `TorsorPushout.PushoutTorsor.compareIso`), from which
  `TorsorPushoutRel.PushoutTorsorRel.pushMap`, `pushMap_id`, `pushMap_comp` and `pushIso` follow
  exactly as in the absolute case.
* `TorsorPushoutRel.pushoutMap_comp_target`, `TorsorPushoutRel.pushoutHom`,
  **`TorsorPushoutRel.pushoutFunctorRel ρ τ : ActionTorsor G U T ⥤ ActionTorsor G' U' T`**: the
  pushout of the quotient-stack fibre along a relative homomorphism `ρ` and a `ρ`-equivariant
  `τ`, as a genuine `CategoryTheory.Functor` (unconditionally, for every torsor, not just
  trivialised ones).
* **`ConeQuotient.contractionFunctor A bas r : ActionTorsor (vectorBundleGroup σ)
  (coneActionSpace A bas) T ⥤ ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T`**:
  the specialisation of `pushoutFunctorRel` to the scalar homomorphism, i.e. the *unconditional*
  scalar contraction of `[C/E]` as a genuine endofunctor of the whole torsor groupoid, agreeing
  with `TorsorPushoutRel.coneContraction` on objects (`contractionFunctor_obj`).
* `ConeQuotient.contractionFunctor_trivialPointIso`: over an affine base `T = Spec B`, the
  restriction of `contractionFunctor` to the image of `TrivialPoint.embedding` is isomorphic to
  the image of `ConeQuotient.coneTwist`, i.e. the *object-level* comparison the round-12 file
  could only make under `AllTorsorsTrivial`; it is unconditional here (transported directly from
  `TorsorPushoutRel.coneContractionEmbeddingIso`).

## What is not done

`ConeStack`'s six coherence isomorphisms of `contraction` (unit, multiplicativity, zero, vertex,
projection, base-change) are not proved for `contractionFunctor`. The unit law (`scaleRelMonHom
σ T 1 ≅` the identity relative homomorphism) looks reachable with `Functor.Monoidal.μ_fst` and an
extensionality lemma for `RelMonHom`, but was not carried through to a natural isomorphism of
functors. Multiplicativity needs a new "iterated relative pushout `≅` pushout along a composite
relative homomorphism" construction (no composition operation on `RelMonHom` exists yet). Base
change needs the analogue of `pushoutPullbackIso`. Zero/vertex/projection, as literally shaped by
`Cones/Stack.lean`'s `ConeStack`, refer to the stack-level `projection`/`vertex` `StackHom`s, so
they (and the full `ConeStack` assembly, issue #60's remaining goal) need the universe fix to
`ActionTorsor.quotientStack` and the rest of the stack-assembly machinery, not attempted here.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

namespace TorsorPushoutRel

universe u

open TorsorPushout

/-! ### Uniqueness of a relative pushout datum -/

namespace PushoutTorsorRel

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}
  {ρ : RelMonHom G G' T} {P : FppfTorsor G T}

/-- Evaluation of a relative pushout datum only depends on the points, not on the proof that
they lie over the same base point. -/
theorem ev_congr (A : PushoutTorsorRel ρ P) {W : Scheme.{u}}
    {α β : fppfYoneda.obj W ⟶ A.sheaf} (hαβ : α = β) {p q : fppfYoneda.obj W ⟶ P.P}
    (hpq : p = q) (h : α ≫ A.projection = p ≫ P.projection)
    (h' : β ≫ A.projection = q ≫ P.projection) : A.ev α p h = A.ev β q h' := by
  subst hαβ
  subst hpq
  rfl

/-- **Evaluation of a relative pushout datum at two points of `P` over the same base differ by
the relative pairing, at the second point's base, of the difference point of `P` (inverted).** -/
theorem ev_congr_pt (A : PushoutTorsorRel ρ P) {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ A.sheaf) (p q : fppfYoneda.obj W ⟶ P.P)
    (hp : α ≫ A.projection = p ≫ P.projection) (hq : α ≫ A.projection = q ≫ P.projection) :
    A.ev α p hp =
      A.ev α q hq * (ρ.pt (q ≫ P.projection) (divPt P p q (hp.symm.trans hq)))⁻¹ := by
  have hact : actPt (divPt P p q (hp.symm.trans hq)) q = p := actPt_divPt p q _
  have h' : α ≫ A.projection = actPt (divPt P p q (hp.symm.trans hq)) q ≫ P.projection := by
    rw [hact]; exact hp
  calc A.ev α p hp = A.ev α (actPt (divPt P p q (hp.symm.trans hq)) q) h' :=
        A.ev_congr_right α hact.symm hp h'
    _ = A.ev α q hq * (ρ.pt (q ≫ P.projection) (divPt P p q (hp.symm.trans hq)))⁻¹ :=
        A.ev_actPt_right (divPt P p q (hp.symm.trans hq)) α q hq h'

variable (A B : PushoutTorsorRel ρ P)

/-- The local comparison of two relative pushout data for the same torsor `P`: the point of `B`
with the same evaluation as `α` against the tautological point of `P` at a lift `c` of the base
of `α` through the trivialising cover of `P`. -/
noncomputable def cmpLocal {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hc : α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    fppfYoneda.obj W ⟶ B.sheaf :=
  (B.ev_bijective (coverPt c) (A.ev α (coverPt c) (by rw [hc, coverPt_proj]))).choose.1

variable {A B}

theorem cmpLocal_proj {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hc : α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    cmpLocal A B α c hc ≫ B.projection = coverPt c ≫ P.projection :=
  (B.ev_bijective (coverPt c) (A.ev α (coverPt c) (by rw [hc, coverPt_proj]))).choose.2

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
  have hcombine : A.ev α (coverPt c') hp' *
      (ρ.pt (coverPt c' ≫ P.projection) (divPt P (coverPt c) (coverPt c') _))⁻¹ =
      B.ev (cmpLocal A B α c hc) (coverPt c') hβp' *
      (ρ.pt (coverPt c' ≫ P.projection) (divPt P (coverPt c) (coverPt c') _))⁻¹ :=
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

/-- **Two morphisms out of a relative pushout datum agreeing on the trivialising cover of `P`
agree everywhere.** -/
theorem hom_ext_of_cmp {A : PushoutTorsorRel ρ P} {S : FppfSheaf.{u}} {φ ψ : A.sheaf ⟶ S}
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

open GromovWitten.SheafGluing

theorem cmpLocal_congr_pt {W : Scheme.{u}} {α α' : fppfYoneda.obj W ⟶ A.sheaf} (hαα' : α = α')
    {c : W ⟶ P.locallyTrivial.coverScheme}
    (hc : α ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hc' : α' ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    cmpLocal A B α c hc = cmpLocal A B α' c hc' := by
  subst hαα'
  rfl

variable (A B)

/-- The comparison morphism between two relative pushout data for the same torsor, defined on
the sections whose base lifts to the trivialising cover of `P`. -/
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

/-- **The comparison morphism between two relative pushout data for the same torsor**, glued
from `cmpLocal` along the trivialising cover of `P`. -/
noncomputable def cmpMap : A.sheaf ⟶ B.sheaf :=
  (cmpPartial A B).glue (coverSieve_mem P)

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

theorem cmpMap_proj : cmpMap A B ≫ B.projection = A.projection := by
  refine hom_ext_of_cmp (fun α c hc => ?_)
  rw [← Category.assoc, cmpMap_spec A B α c hc, cmpLocal_proj α c hc, coverPt_proj, ← hc]

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

theorem cmpMap_equivariant :
    ModObj.smul (M := G'.space.toSheaf) (X := A.sheaf) ≫ cmpMap A B =
      (G'.space.toSheaf ◁ cmpMap A B) ≫ ModObj.smul (M := G'.space.toSheaf) (X := B.sheaf) := by
  refine hom_ext_points fun W ω => ?_
  rw [← Category.assoc, ← Category.assoc, ← TorsorPushout.lift_comp_fst_snd ω,
    ConeQuotient.lift_whiskerLeft]
  exact cmpMap_actPt A B (ω ≫ fst _ _) (ω ≫ snd _ _)

/-- **Uniqueness of a relative pushout datum**: two `PushoutTorsorRel ρ P` structures for the
same torsor `P` are canonically isomorphic, compatibly with the projection to `T` and the action
of `G'`.  This is the uniqueness statement flagged as missing in
`Stacks/TorsorPushoutRelative.lean`'s docstring. -/
noncomputable def compareIso : A.sheaf ≅ B.sheaf where
  hom := cmpMap A B
  inv := cmpMap B A
  hom_inv_id := cmpMap_hom_inv A B
  inv_hom_id := cmpMap_inv_hom A B

end PushoutTorsorRel

/-! ### Functoriality in the torsor -/

namespace PushoutTorsorRel

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}
  {ρ : RelMonHom G G' T} {P Q R : FppfTorsor G T}

/-- **From the trivialising cover to all points**, for a map of relative pushout data over an
equivariant map `u` of the underlying torsors: if the evaluation pairing of `f` is computed
through `u` at the tautological points of the trivialising cover of `P`, then it is computed
through `u` at every point of `P`. -/
theorem ev_eq_of_ev_cover_over (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q)
    {u : P.P ⟶ Q.P} (hu : TorsorPushout.PushoutTorsor.IsEquivariantPt u)
    (hover : u ≫ Q.projection = P.projection) (f : A.sheaf ⟶ B.sheaf)
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
          (ρ.pt ((coverPt c ≫ u) ≫ Q.projection)
            (divPt Q ((fppfYoneda.map w ≫ p) ≫ u) (coverPt c ≫ u) (h₁.symm.trans h₂)))⁻¹ :=
        B.ev_congr_pt ((fppfYoneda.map w ≫ α) ≫ f) _ _ h₁ h₂
    _ = A.ev (fppfYoneda.map w ≫ α) (coverPt c) hq *
          (ρ.pt (coverPt c ≫ P.projection)
            (divPt P (fppfYoneda.map w ≫ p) (coverPt c) (hp.symm.trans hq)))⁻¹ := by
        rw [hloc (fppfYoneda.map w ≫ α) c hα' h₂ hq]
        exact congrArg (A.ev (fppfYoneda.map w ≫ α) (coverPt c) hq * ·⁻¹)
          (ρ.pt_congr (by rw [Category.assoc, hover])
            (TorsorPushout.PushoutTorsor.divPt_comp_of_isEquivariantPt hu
              (fppfYoneda.map w ≫ p) (coverPt c) (hp.symm.trans hq) (h₁.symm.trans h₂)))
    _ = A.ev (fppfYoneda.map w ≫ α) (fppfYoneda.map w ≫ p) hp :=
        (A.ev_congr_pt (fppfYoneda.map w ≫ α) (fppfYoneda.map w ≫ p) (coverPt c) hp hq).symm
    _ = fppfYoneda.map w ≫ A.ev α p h := (A.ev_naturality w α p h hp).symm

/-! ### The morphism of relative pushout data induced by a morphism of torsors -/

variable {P Q : FppfTorsor G T}

/-- **Reindexing a relative pushout datum along a morphism of torsors.** -/
noncomputable def reindexAlong (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q) : PushoutTorsorRel ρ P where
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
    have hstep : B.ev α (actPt g p ≫ φ.iso.hom) hQ' =
        B.ev α (p ≫ φ.iso.hom) hQ * (ρ.pt ((p ≫ φ.iso.hom) ≫ Q.projection) g)⁻¹ :=
      (B.ev_congr_right α e2 hQ' (by rw [e2] at hQ'; exact hQ')).trans
        (B.ev_actPt_right g α (p ≫ φ.iso.hom) hQ (by rw [e2] at hQ'; exact hQ'))
    refine hstep.trans ?_
    exact congrArg (B.ev α (p ≫ φ.iso.hom) hQ * ·⁻¹)
      (ρ.pt_congr (by rw [Category.assoc, φ.over]) rfl)
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
theorem reindexAlong_ev (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q) {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ B.sheaf) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ B.projection = p ≫ P.projection) :
    (reindexAlong B φ).ev α p h =
      B.ev α (p ≫ φ.iso.hom) (by rw [Category.assoc, φ.over]; exact h) :=
  rfl

/-- **The morphism of relative pushout data induced by a morphism `φ : P ⟶ Q` of `G`-torsors.** -/
noncomputable def pushMap (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q) :
    A.sheaf ⟶ B.sheaf :=
  cmpMap A (reindexAlong B φ)

theorem pushMap_proj (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q) :
    pushMap A B φ ≫ B.projection = A.projection :=
  cmpMap_proj A (reindexAlong B φ)

theorem pushMap_equivariant (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q) :
    ModObj.smul (M := G'.space.toSheaf) (X := A.sheaf) ≫ pushMap A B φ =
      (G'.space.toSheaf ◁ pushMap A B φ) ≫ ModObj.smul (M := G'.space.toSheaf) (X := B.sheaf) :=
  cmpMap_equivariant A (reindexAlong B φ)

theorem ev_pushMap_cover (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q)
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

theorem ev_eq_of_ev_cover (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q)
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
  ev_eq_of_ev_cover_over A B (TorsorPushout.PushoutTorsor.isEquivariantPt_iso_hom φ) φ.over f
    (fun β q hq => by rw [Category.assoc, hf, hq, Category.assoc, φ.over]) hloc α p h h'

theorem ev_pushMap (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q)
    {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ A.projection = p ≫ P.projection)
    (h' : (α ≫ pushMap A B φ) ≫ B.projection = (p ≫ φ.iso.hom) ≫ Q.projection) :
    B.ev (α ≫ pushMap A B φ) (p ≫ φ.iso.hom) h' = A.ev α p h :=
  ev_eq_of_ev_cover A B φ (pushMap A B φ) (pushMap_proj A B φ)
    (fun β c hc h₁ h₂ => ev_pushMap_cover A B φ β c hc h₁ h₂) α p h h'

/-- **Uniqueness of the induced morphism**. -/
theorem eq_pushMap (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q)
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

theorem pushMap_congr (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q) {φ ψ : P ⟶ Q}
    (h : φ = ψ) : pushMap A B φ = pushMap A B ψ := by
  subst h
  rfl

/-- **The pushout of the identity is the identity.** -/
theorem pushMap_id (A : PushoutTorsorRel ρ P) : pushMap A A (𝟙 P) = 𝟙 A.sheaf :=
  (eq_pushMap A A (𝟙 P) (𝟙 A.sheaf) (Category.id_comp _) fun β c _ h₁ h₂ =>
    A.ev_congr (Category.comp_id β) (by rw [FppfTorsor.id_iso_hom, Category.comp_id]) h₁ h₂).symm

variable {R : FppfTorsor G T}

/-- **The pushout of a composite is the composite of the pushouts.** -/
theorem pushMap_comp (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q)
    (C : PushoutTorsorRel ρ R) (φ : P ⟶ Q) (ψ : Q ⟶ R) :
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

/-- **The isomorphism of relative pushout data induced by a morphism of torsors.** -/
noncomputable def pushIso (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q) :
    A.sheaf ≅ B.sheaf where
  hom := pushMap A B φ
  inv := pushMap B A (Groupoid.inv φ)
  hom_inv_id := by
    rw [pushMap_comp A B A φ (Groupoid.inv φ),
      pushMap_congr A A (Groupoid.comp_inv φ), pushMap_id]
  inv_hom_id := by
    rw [pushMap_comp B A B (Groupoid.inv φ) φ,
      pushMap_congr B B (Groupoid.inv_comp φ), pushMap_id]

@[simp]
theorem pushIso_hom (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q) :
    (pushIso A B φ).hom = pushMap A B φ :=
  rfl

end PushoutTorsorRel

end TorsorPushoutRel

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T : Scheme.{u}}

/-- Composition of quotient-stack arrows is composition of the underlying sheaf isomorphisms. -/
theorem Hom.comp_iso_hom {P Q R : ActionTorsor G U T} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).iso.hom = f.iso.hom ≫ g.iso.hom :=
  rfl

/-- The identity quotient-stack arrow is the identity sheaf isomorphism. -/
theorem Hom.id_iso_hom (P : ActionTorsor G U T) : (𝟙 P : P ⟶ P).iso.hom = 𝟙 P.P :=
  rfl

end ActionTorsor

namespace TorsorPushoutRel

open TorsorPushout

/-! ### The pushout functor on the quotient-stack fibre -/

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {U : AlgebraicSpaceAction G}
  {U' : AlgebraicSpaceAction G'} (ρ : RelMonHom G G' T) (τ : RelEquivMap ρ U U')

/-- **The induced arrow of relative pushout torsors commutes with the maps to `U'`.**  Both
sides are computed at the tautological points of the trivialising cover of `P` by
`TorsorPushoutRel.targetMap_eq_actPt`, where they agree by
`PushoutTorsorRel.ev_pushMap_cover` and the compatibility of `φ` with the maps to `U`. -/
theorem pushoutMap_comp_target {P Q : ActionTorsor G U T} (φ : P ⟶ Q) :
    PushoutTorsorRel.pushMap (pushoutTorsor P.toFppfTorsor ρ) (pushoutTorsor Q.toFppfTorsor ρ)
        (ActionTorsor.Hom.toFppfHom φ) ≫ targetMap Q ρ τ = targetMap P ρ τ := by
  refine PushoutTorsorRel.hom_ext_of_cmp (fun α c hc => ?_)
  rw [← Category.assoc α (PushoutTorsorRel.pushMap (pushoutTorsor P.toFppfTorsor ρ)
      (pushoutTorsor Q.toFppfTorsor ρ) (ActionTorsor.Hom.toFppfHom φ)) (targetMap Q ρ τ)]
  set β := α ≫ PushoutTorsorRel.pushMap (pushoutTorsor P.toFppfTorsor ρ)
      (pushoutTorsor Q.toFppfTorsor ρ) (ActionTorsor.Hom.toFppfHom φ) with hβdef
  have h' : α ≫ (pushoutTorsor P.toFppfTorsor ρ).projection = coverPt c ≫ P.projection := by
    rw [hc, coverPt_proj]
  have hβproj : β ≫ (pushoutTorsor Q.toFppfTorsor ρ).projection =
      (coverPt c ≫ φ.iso.hom) ≫ Q.projection := by
    rw [hβdef, Category.assoc, PushoutTorsorRel.pushMap_proj, h', Category.assoc, φ.over]
  have hev : evPt Q.toFppfTorsor ρ β (coverPt c ≫ φ.iso.hom) hβproj =
      evPt P.toFppfTorsor ρ α (coverPt c) h' :=
    PushoutTorsorRel.ev_pushMap_cover (pushoutTorsor P.toFppfTorsor ρ)
      (pushoutTorsor Q.toFppfTorsor ρ) (ActionTorsor.Hom.toFppfHom φ) α c hc hβproj h'
  have htgt : (coverPt c ≫ φ.iso.hom) ≫ Q.target = coverPt c ≫ P.target := by
    rw [Category.assoc, φ.target]
  have hproj : (coverPt c ≫ φ.iso.hom) ≫ Q.projection = coverPt c ≫ P.projection := by
    rw [Category.assoc, φ.over]
  refine (targetMap_eq_actPt (P := Q) (τ := τ) β (coverPt c ≫ φ.iso.hom) hβproj).trans ?_
  rw [hev]
  refine (congrArg (actPt (evPt P.toFppfTorsor ρ α (coverPt c) h')) ?_).trans
    (targetMap_eq_actPt (P := P) (τ := τ) α (coverPt c) h').symm
  rw [hproj, htgt]

variable {ρ τ}

/-- **The morphism of the pushout torsor induced by a morphism of the quotient-stack fibre.** -/
noncomputable def pushoutHom {P Q : ActionTorsor G U T} (φ : P ⟶ Q) :
    pushoutActionTorsor P ρ τ ⟶ pushoutActionTorsor Q ρ τ where
  iso := PushoutTorsorRel.pushIso (pushoutTorsor P.toFppfTorsor ρ) (pushoutTorsor Q.toFppfTorsor ρ)
    (ActionTorsor.Hom.toFppfHom φ)
  over := PushoutTorsorRel.pushMap_proj (pushoutTorsor P.toFppfTorsor ρ)
    (pushoutTorsor Q.toFppfTorsor ρ) (ActionTorsor.Hom.toFppfHom φ)
  equivariant := PushoutTorsorRel.pushMap_equivariant (pushoutTorsor P.toFppfTorsor ρ)
    (pushoutTorsor Q.toFppfTorsor ρ) (ActionTorsor.Hom.toFppfHom φ)
  target := by
    rw [PushoutTorsorRel.pushIso_hom, pushoutActionTorsor_target, pushoutActionTorsor_target]
    exact pushoutMap_comp_target ρ τ φ

/-- The underlying isomorphism of sheaves of the induced morphism. -/
@[simp]
theorem pushoutHom_iso_hom {P Q : ActionTorsor G U T} (φ : P ⟶ Q) :
    (pushoutHom (ρ := ρ) (τ := τ) φ).iso.hom =
      PushoutTorsorRel.pushMap (pushoutTorsor P.toFppfTorsor ρ) (pushoutTorsor Q.toFppfTorsor ρ)
        (ActionTorsor.Hom.toFppfHom φ) :=
  rfl

/-- **The pushout preserves identities.** -/
theorem pushoutHom_id (P : ActionTorsor G U T) :
    pushoutHom (ρ := ρ) (τ := τ) (𝟙 P) = 𝟙 (pushoutActionTorsor P ρ τ) := by
  refine ActionTorsor.Hom.ext _ _ ?_
  rw [pushoutHom_iso_hom, ActionTorsor.Hom.toFppfHom_id, ActionTorsor.Hom.id_iso_hom]
  exact PushoutTorsorRel.pushMap_id (pushoutTorsor P.toFppfTorsor ρ)

/-- **The pushout preserves composition.** -/
theorem pushoutHom_comp {P Q R : ActionTorsor G U T} (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    pushoutHom (ρ := ρ) (τ := τ) (φ ≫ ψ) =
      pushoutHom (ρ := ρ) (τ := τ) φ ≫ pushoutHom (ρ := ρ) (τ := τ) ψ := by
  refine ActionTorsor.Hom.ext _ _ ?_
  rw [pushoutHom_iso_hom, ActionTorsor.Hom.toFppfHom_comp, ActionTorsor.Hom.comp_iso_hom,
    pushoutHom_iso_hom, pushoutHom_iso_hom]
  exact (PushoutTorsorRel.pushMap_comp (pushoutTorsor P.toFppfTorsor ρ)
    (pushoutTorsor Q.toFppfTorsor ρ) (pushoutTorsor R.toFppfTorsor ρ)
    (ActionTorsor.Hom.toFppfHom φ) (ActionTorsor.Hom.toFppfHom ψ)).symm

/-- **The pushout functor `ρ_* : ActionTorsor G U T ⥤ ActionTorsor G' U' T`, unconditionally,
for a relative homomorphism `ρ` and a `ρ`-equivariant map `τ`.** -/
noncomputable def pushoutFunctorRel : ActionTorsor G U T ⥤ ActionTorsor G' U' T where
  obj P := pushoutActionTorsor P ρ τ
  map φ := pushoutHom φ
  map_id := pushoutHom_id
  map_comp φ ψ := pushoutHom_comp φ ψ

/-- The pushout functor on objects. -/
@[simp]
theorem pushoutFunctorRel_obj (P : ActionTorsor G U T) :
    (pushoutFunctorRel (ρ := ρ) (τ := τ)).obj P = pushoutActionTorsor P ρ τ :=
  rfl

/-- The pushout functor on morphisms. -/
@[simp]
theorem pushoutFunctorRel_map {P Q : ActionTorsor G U T} (φ : P ⟶ Q) :
    (pushoutFunctorRel (ρ := ρ) (τ := τ)).map φ = pushoutHom φ :=
  rfl

end TorsorPushoutRel

/-! ### The unconditional scalar contraction of the affine cone quotient `[C/E]` -/

namespace ConeQuotient

universe u

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T : Scheme.{u}}
  (A : ConeAction R S F) (bas : Module.Basis σ R F)

/-- **The unconditional scalar contraction of `[C/E]`, as a genuine endofunctor of the whole
torsor groupoid `ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T`.**  Unlike
`ActionTwist.torsorContraction`, this needs no `AllTorsorsTrivial` hypothesis: it is the pushout
functor of `TorsorPushoutRel.pushoutFunctorRel` along the relative scalar homomorphism
`TorsorPushoutRel.scaleRelMonHom`. -/
noncomputable def contractionFunctor (r : Γ(T, ⊤)) :
    ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T ⥤
      ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T :=
  TorsorPushoutRel.pushoutFunctorRel (ρ := TorsorPushoutRel.scaleRelMonHom σ T r)
    (τ := TorsorPushoutRel.coneScaleRelEquivMap A bas r)

/-- The contraction functor agrees, on objects, with `TorsorPushoutRel.coneContraction`. -/
@[simp]
theorem contractionFunctor_obj (r : Γ(T, ⊤))
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    (contractionFunctor A bas r).obj P = TorsorPushoutRel.coneContraction A bas r P :=
  rfl

/-- **The unconditional contraction restricted to trivialised torsors is
`ConeQuotient.coneTwist`.**  This is the comparison the round-12 `Cones/QuotientTorsorStack.lean`
could only establish under `AllTorsorsTrivial G T` (via `coneTorsorContractionComparison`), now
for the genuine endofunctor `contractionFunctor`, over an affine base `T = Spec B`. -/
noncomputable def contractionFunctor_trivialPointIso {B : Type u} [CommRing B] (r₀ : B)
    (x : TrivialPoint (vectorBundleGroup σ) (coneActionSpace A bas) (coneScheme B)) :
    (TrivialPoint.embedding (vectorBundleGroup σ) (coneActionSpace A bas) (coneScheme B)).obj
        ((coneTwist A bas r₀).functor.obj x) ≅
      (contractionFunctor A bas (gammaMap B r₀)).obj
        ((TrivialPoint.embedding (vectorBundleGroup σ) (coneActionSpace A bas)
          (coneScheme B)).obj x) :=
  TorsorPushoutRel.coneContractionEmbeddingIso A bas r₀ x

end ConeQuotient

end GromovWitten.AlgebraicGeometry
