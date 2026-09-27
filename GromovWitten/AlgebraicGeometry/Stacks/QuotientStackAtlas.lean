/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.QuotientStackGroupMaps
import GromovWitten.AlgebraicGeometry.Stacks.AlgebraicSpace
import GromovWitten.AlgebraicGeometry.Stacks.StrongTransOfDiscrete
import GromovWitten.AlgebraicGeometry.Cones.QuotientTorsorStack
import GromovWitten.AlgebraicGeometry.Spaces.Scheme

/-!
# The atlas map `U → [U/G]` and stack-level maps of quotient stacks

This file constructs the presentation of the quotient stack `[U/G]` by the algebraic space `U`
itself: every `T`-point `t` of `U.space` determines the trivial `G`-torsor over `T` with
equivariant map `(g, s) ↦ g · t(s)` (`ActionTorsor.trivialTorsor`, a thin re-export of
`ConeQuotient.trivialWithPoint`), and this assignment assembles into a fibrewise functor
`ActionTorsor.atlasFunctor` with a base-change comparison `ActionTorsor.atlasNaturalityIsoApp`.

It also records that the quotient-stack maps of `Stacks/QuotientStackGroupMaps.lean` are already
honest `StackHom`s of `Stacks/Algebraic.lean`, now that `[U/G]`/`BG` are `FppfStack`-valued
(`ActionTorsor.quotientStackHom`, `ActionTorsor.toClassifyingStackHom`).

## Main declarations

* `ActionTorsor.trivialTorsor t`: the trivial `G`-torsor of a `T`-point `t` of `U.space`.
* `ActionTorsor.atlasFunctor G U T`: the fibrewise functor sending a `T`-point of `U.space` to
  the trivial torsor it classifies; `atlasFunctor_obj` computes it on objects (`rfl`).
* `ActionTorsor.atlasNaturalityIsoApp`: the base-change comparison of `atlasFunctor`, identifying
  the atlas functor at a pulled-back point with the pullback of the atlas functor at the
  original point (built from `ConeQuotient.TrivialPoint.embeddingPullbackIsoApp` and the
  naturality of the Yoneda equivalence).
* `ActionTorsor.quotientStackHom`, `ActionTorsor.toClassifyingStackHom`: the quotient-stack maps
  of `Stacks/QuotientStackGroupMaps.lean`, restated at the `StackHom` level.
* `ActionTorsor.atlasMap G U : StackHom (FppfStack.ofAlgebraicSpace U.space) (quotientStack G U)`:
  **the atlas map `U → [U/G]`**; `atlasMap_app_obj` computes it on fibre objects (`rfl`).
* `ActionTorsor.sectionEquivTrivialisation`, `ActionTorsor.pullbackSectionEquiv` and
  `ActionTorsor.atlasFibreEquiv`: **the fibre of the atlas map over a torsor `P` is `P`** —
  isomorphisms `atlasMap(s) ≅ P|_S` correspond bijectively to sections of the sheaf `P.P` over
  the test map with associated point `s`.
* `ActionTorsor.schemeAtlasChart`, `ActionTorsor.atlasChart`: charts
  `StackChart (quotientStack G U)` attached to a scheme-valued point of `U.space`, resp. to a
  presentation of `U.space` as the algebraic space of a scheme.  Neither smoothness nor
  surjectivity of the chart is claimed (that is issue #37).

## The atlas map

`ActionTorsor.atlasMap` assembles `atlasFunctor` and `atlasNaturalityIsoApp` into an honest
`StackHom (FppfStack.ofAlgebraicSpace U.space) (quotientStack G U)`.  Its two nontrivial
coherence laws are `ActionTorsor.atlasNaturality_id` and `ActionTorsor.atlasNaturality_comp`,
proved from a *section calculus* for trivial torsors developed in the `ConeQuotient` section
below: a morphism out of a trivial torsor is determined by the image of the unit section
(`ConeQuotient.hom_ext_of_section`), and all the canonical comparison morphisms carry the unit
section to the expected pulled-back sections.  The bicategorical bookkeeping is isolated in
`Stacks/StrongTransOfDiscrete.lean`
(`CategoryTheory.Pseudofunctor.StrongTrans.mkCatOfComponents`), which is stated for abstract
pseudofunctors so that the kernel never has to unfold a concrete fibre category.

-/

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace ActionTorsor

variable {G H : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G}
  {V : AlgebraicSpaceAction H} {T : Scheme.{u}}

/-! ### The trivial torsor of a point -/

/-- The trivial `G`-torsor `G × T → T` attached to a `T`-point `t` of `U.space`, with equivariant
map to `U` given by the action `(g, s) ↦ g · t(s)`.  A thin re-export, under the `ActionTorsor`
namespace, of `ConeQuotient.trivialWithPoint`. -/
noncomputable abbrev trivialTorsor (t : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    ActionTorsor G U T :=
  ConeQuotient.trivialWithPoint t

/-! ### Quotient-stack maps as honest `StackHom`s -/

/-- **The quotient-stack map `[U/G] ⟶ [V/H]`**, restated as an honest `StackHom` of
`Stacks/Algebraic.lean` now that `[U/G]`/`BH` are `FppfStack`-valued.  Definitionally
`ActionTorsor.quotientStackMap r f`. -/
noncomputable abbrev quotientStackHom (r : G.space.toSheaf ⟶ H.space.toSheaf) [IsMonHom r]
    (f : AlgebraicSpaceAction.HomOver r U V) :
    StackHom (quotientStack G U) (quotientStack H V) :=
  ActionTorsor.quotientStackMap r f

/-- **The structure map `[U/G] ⟶ BG`**, restated as an honest `StackHom` of
`Stacks/Algebraic.lean`.  Definitionally `ActionTorsor.toClassifyingStackMap` at the identity
homomorphism. -/
noncomputable abbrev toClassifyingStackHom (G : AlgebraicSpaceGroup.{u})
    (U : AlgebraicSpaceAction G) :
    StackHom (quotientStack G U) (classifyingStack G) :=
  ActionTorsor.toClassifyingStackMap (H := G) (𝟙 G.space.toSheaf) U

/-! ### The fibrewise data of the atlas map `U → [U/G]` -/

/-- **The fibre of the atlas map over a test scheme `T`**: the fibre of
`FppfStack.ofAlgebraicSpace U.space` over `T` is `Discrete (ULift (section type of
`U.space.toSheaf` over `T`))`; this functor sends a section `⟨⟨s⟩⟩` to the trivial torsor of the
corresponding `T`-point, obtained from `s` via the Yoneda equivalence `fppfJ.yonedaEquiv`. -/
noncomputable def atlasFunctor (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (T : Scheme.{u}) :
    StackFiber (FppfStack.ofAlgebraicSpace U.space) T ⥤ StackFiber (quotientStack G U) T :=
  Discrete.functor (fun x : ULift (U.space.toSheaf.obj.obj (Opposite.op T)) =>
    trivialTorsor (fppfJ.yonedaEquiv.symm x.down))

/-- The atlas functor sends the object `⟨⟨s⟩⟩` (for a section `s` corresponding, via
`fppfJ.yonedaEquiv`, to the `T`-point `t`) to the trivial torsor of `t`.  This is `rfl`. -/
@[simp]
theorem atlasFunctor_obj (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G) (T : Scheme.{u})
    (s : U.space.toSheaf.obj.obj (Opposite.op T)) :
    (atlasFunctor G U T).obj (Discrete.mk (ULift.up s)) =
      trivialTorsor (fppfJ.yonedaEquiv.symm s) :=
  rfl

/-- **Base change of the atlas map**: the atlas functor at the pulled-back section is the
pullback (in `[U/G]`) of the atlas functor at the original section, i.e. the pullback of the
trivial torsor of a point `t` is the trivial torsor of the pulled-back point `β ≫ t`
(`ConeQuotient.pullbackTrivialIso`, via the naturality of the Yoneda equivalence in the
section variable). -/
noncomputable def atlasNaturalityIsoApp (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    {T T' : Scheme.{u}} (β : T' ⟶ T) (s : U.space.toSheaf.obj.obj (Opposite.op T)) :
    trivialTorsor (fppfJ.yonedaEquiv.symm (U.space.toSheaf.obj.map β.op s)) ≅
      (ActionTorsor.pullbackFunctor β).obj (trivialTorsor (fppfJ.yonedaEquiv.symm s)) :=
  (eqToIso (congrArg trivialTorsor (fppfJ.yonedaEquiv_symm_map β.op s))).trans
    (ConeQuotient.TrivialPoint.embeddingPullbackIsoApp β ⟨fppfJ.yonedaEquiv.symm s⟩)

end ActionTorsor

namespace ConeQuotient

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T T' T'' : Scheme.{u}}

/-! ### A section calculus for trivial torsors

The unit section `ConeQuotient.unitSection G T` of the trivial torsor is the universal tool for
comparing morphisms out of a trivial torsor: by equivariance such a morphism is determined by the
image of the unit section (`hom_ext_of_section`).  The lemmas of this section compute that image
for each canonical comparison morphism appearing in the coherence laws of the atlas map. -/

/-- The unit section of the trivial `G`-torsor attached to a point `t`, typed as a section of
`(trivialWithPoint t).P` (rather than of `G × T`, which is only definitionally the same sheaf;
the distinction matters for `rw`/`simp`). -/
noncomputable def trivialSection (t : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    fppfYoneda.obj T ⟶ (trivialWithPoint (U := U) t).P :=
  unitSection G T

/-- The unit section of a trivial torsor is a section of its projection. -/
theorem trivialSection_projection (t : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    trivialSection (U := U) t ≫ (trivialWithPoint (U := U) t).projection = 𝟙 _ :=
  unitSection_snd

/-- The unit section of a trivial torsor computes the point of `U` it is attached to. -/
theorem trivialSection_comp_trivialTarget (t : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    trivialSection (U := U) t ≫ (trivialWithPoint (U := U) t).target = t :=
  unitSection_comp_trivialTarget t

/-- The comparison map attached to a global section carries the unit section of the trivial
torsor to that section. -/
theorem unitSection_comp_sectionMap {Q : ActionTorsor G U T} (s : fppfYoneda.obj T ⟶ Q.P) :
    unitSection G T ≫ sectionMap Q s = s := by
  rw [sectionMap, unitSection, lift_whiskerLeft_assoc, Category.id_comp, lift_one_smul]

/-- **A morphism out of a torsor with a global section is determined by the image of that
section**: equivariance propagates the value at the section to the whole torsor.  This is the
extensionality principle used for all the coherence laws of the atlas map. -/
theorem hom_ext_of_section {P Q : ActionTorsor G U T} (σ : fppfYoneda.obj T ⟶ P.P)
    (hσ : σ ≫ P.projection = 𝟙 _) (f g : P ⟶ Q)
    (h : σ ≫ f.iso.hom = σ ≫ g.iso.hom) : f = g := by
  have key : ∀ k : P ⟶ Q, sectionMap P σ ≫ k.iso.hom =
      (G.space.toSheaf ◁ (σ ≫ k.iso.hom)) ≫
        ModObj.smul (M := G.space.toSheaf) (X := Q.P) := by
    intro k
    rw [sectionMap, Category.assoc, k.equivariant, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp]
  have hiso : IsIso (sectionMap P σ) :=
    ⟨sectionInv P σ hσ, sectionMap_sectionInv P σ hσ, sectionInv_sectionMap P σ hσ⟩
  refine ActionTorsor.Hom.ext _ _ ((cancel_epi (sectionMap P σ)).1 ?_)
  rw [key f, key g, h]

/-- An `eqToHom` between trivial torsors with equal points carries the unit section to the unit
section. -/
theorem trivialSection_comp_eqToHom {t₁ t₂ : fppfYoneda.obj T ⟶ U.space.toSheaf}
    (e : t₁ = t₂) (h : trivialWithPoint (U := U) t₁ = trivialWithPoint t₂) :
    trivialSection (U := U) t₁ ≫
        (eqToHom h : trivialWithPoint (U := U) t₁ ⟶ trivialWithPoint t₂).iso.hom =
      trivialSection (U := U) t₂ := by
  subst e
  exact Category.comp_id _

/-- The underlying sheaf morphism of the trivialisation attached to a global section is the
comparison map of that section. -/
theorem isoTrivialOfSection_hom_iso_hom {Q : ActionTorsor G U T} (s : fppfYoneda.obj T ⟶ Q.P)
    (hs : s ≫ Q.projection = 𝟙 _) :
    (isoTrivialOfSection Q s hs).hom.iso.hom = sectionMap Q s := rfl

/-- The first leg of a base-changed section is the base change of the section. -/
@[reassoc]
theorem pullbackSection_fst {P : ActionTorsor G U T} (s : fppfYoneda.obj T ⟶ P.P)
    (hs : s ≫ P.projection = 𝟙 _) (b : T' ⟶ T) :
    pullbackSection P s hs b ≫
        Limits.pullback.fst P.projection (fppfYoneda.map b) = fppfYoneda.map b ≫ s :=
  Limits.pullback.lift_fst _ _ _

/-- The second leg of a base-changed section is the identity: it is again a section. -/
@[reassoc]
theorem pullbackSection_snd {P : ActionTorsor G U T} (s : fppfYoneda.obj T ⟶ P.P)
    (hs : s ≫ P.projection = 𝟙 _) (b : T' ⟶ T) :
    pullbackSection P s hs b ≫
        Limits.pullback.snd P.projection (fppfYoneda.map b) = 𝟙 _ :=
  Limits.pullback.lift_snd _ _ _

/-- **The base-change comparison of trivial torsors carries the unit section to the base change
of the unit section.** -/
theorem trivialSection_comp_pullbackTrivialIso (t : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (b : T' ⟶ T) :
    trivialSection (U := U) (fppfYoneda.map b ≫ t) ≫ (pullbackTrivialIso t b).hom.iso.hom =
      pullbackSection (trivialWithPoint t) (trivialSection (U := U) t)
        (trivialSection_projection t) b := by
  rw [pullbackTrivialIso, Iso.trans_hom, ActionTorsor.comp_iso_hom, ← Category.assoc,
    eqToIso.hom,
    trivialSection_comp_eqToHom (Eq.symm (by
      have h1 := pullbackSection_target (trivialWithPoint t) (unitSection G T) unitSection_snd b
      exact h1.trans (congrArg (fun k => fppfYoneda.map b ≫ k)
        (unitSection_comp_trivialTarget t)))),
    isoTrivialOfSection_hom_iso_hom]
  exact unitSection_comp_sectionMap _

end ConeQuotient

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T T' T'' : Scheme.{u}}

/-! ### The coherence laws of the atlas map -/

/-- The first leg of the base change of a morphism landing in an iterated base change, in the
syntactic form in which the iterated fibre product appears in `naturality_comp`. -/
@[reassoc]
theorem pullbackMap_fst_iterated {A : ActionTorsor G U T} {P : ActionTorsor G U T'}
    (β₁ : T' ⟶ T) (β₂ : T'' ⟶ T') (φ : P.P ⟶ (ActionTorsor.pullbackObj β₁ A).P)
    (hφ : φ ≫ (ActionTorsor.pullbackObj β₁ A).projection = P.projection) :
    FppfTorsor.pullbackMap β₂ φ hφ ≫
        Limits.pullback.fst (Limits.pullback.snd A.projection (fppfYoneda.map β₁))
          (fppfYoneda.map β₂) =
      Limits.pullback.fst P.projection (fppfYoneda.map β₂) ≫ φ :=
  FppfTorsor.pullbackMap_fst β₂ φ hφ

/-- The second leg of the base change of a morphism landing in an iterated base change. -/
@[reassoc]
theorem pullbackMap_snd_iterated {A : ActionTorsor G U T} {P : ActionTorsor G U T'}
    (β₁ : T' ⟶ T) (β₂ : T'' ⟶ T') (φ : P.P ⟶ (ActionTorsor.pullbackObj β₁ A).P)
    (hφ : φ ≫ (ActionTorsor.pullbackObj β₁ A).projection = P.projection) :
    FppfTorsor.pullbackMap β₂ φ hφ ≫
        Limits.pullback.snd (Limits.pullback.snd A.projection (fppfYoneda.map β₁))
          (fppfYoneda.map β₂) =
      Limits.pullback.snd P.projection (fppfYoneda.map β₂) :=
  FppfTorsor.pullbackMap_snd β₂ φ hφ

/-- **The atlas naturality comparison carries the unit section of the trivial torsor of a
restricted point to the base change of the unit section.**  This is the single computation on
which both coherence laws of the atlas map rest. -/
@[reassoc]
theorem trivialSection_comp_atlasNaturalityIsoApp (G : AlgebraicSpaceGroup.{u})
    (U : AlgebraicSpaceAction G) {T T' : Scheme.{u}} (β : T' ⟶ T)
    (s : U.space.toSheaf.obj.obj (Opposite.op T)) :
    ConeQuotient.trivialSection
          (fppfJ.yonedaEquiv.symm (U.space.toSheaf.obj.map β.op s)) ≫
        (atlasNaturalityIsoApp G U β s).hom.iso.hom =
      ConeQuotient.pullbackSection (trivialTorsor (G := G) (fppfJ.yonedaEquiv.symm s))
        (ConeQuotient.trivialSection (fppfJ.yonedaEquiv.symm s))
        (ConeQuotient.trivialSection_projection _) β := by
  rw [atlasNaturalityIsoApp, ConeQuotient.TrivialPoint.embeddingPullbackIsoApp, Iso.trans_hom,
    comp_iso_hom, eqToIso.hom, ← Category.assoc,
    ConeQuotient.trivialSection_comp_eqToHom (fppfJ.yonedaEquiv_symm_map β.op s)]
  dsimp only [Quiver.Hom.unop_op]
  exact ConeQuotient.trivialSection_comp_pullbackTrivialIso _ _

/-- **Unit coherence of the atlas map** (the componentwise `naturality_id`): the atlas naturality
comparison along `𝟙 T`, followed by the unit comparison of base change, is the canonical
identification of the trivial torsors of `s` and of its restriction along `𝟙 T`. -/
theorem atlasNaturality_id (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (T : Scheme.{u}) (s : U.space.toSheaf.obj.obj (Opposite.op T))
    (h : trivialTorsor (G := G) (U := U)
        (fppfJ.yonedaEquiv.symm (U.space.toSheaf.obj.map (𝟙 T).op s)) =
      trivialTorsor (fppfJ.yonedaEquiv.symm s)) :
    (atlasNaturalityIsoApp G U (𝟙 T) s).hom ≫
        (ActionTorsor.pullbackIdIsoApp
          (trivialTorsor (G := G) (U := U) (fppfJ.yonedaEquiv.symm s))).hom =
      eqToHom h := by
  have e : fppfJ.yonedaEquiv.symm (U.space.toSheaf.obj.map (𝟙 T).op s) =
      fppfJ.yonedaEquiv.symm s := congrArg _ (by simp)
  refine ConeQuotient.hom_ext_of_section (ConeQuotient.trivialSection _)
    (ConeQuotient.trivialSection_projection _) _ _ ?_
  rw [comp_iso_hom, ← Category.assoc, trivialSection_comp_atlasNaturalityIsoApp,
    pullbackIdIsoApp_hom_iso_hom, ConeQuotient.pullbackSection_fst,
    ConeQuotient.trivialSection_comp_eqToHom e h, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- **Composition coherence of the atlas map** (the componentwise `naturality_comp`): the atlas
naturality comparison along a composite `β₂ ≫ β₁`, followed by the composition comparison of
base change, is the composite of the comparisons along `β₁` and `β₂`. -/
theorem atlasNaturality_comp (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    {T T' T'' : Scheme.{u}} (β₁ : T' ⟶ T) (β₂ : T'' ⟶ T')
    (s : U.space.toSheaf.obj.obj (Opposite.op T))
    (h : trivialTorsor (G := G) (U := U)
          (fppfJ.yonedaEquiv.symm (U.space.toSheaf.obj.map (β₂ ≫ β₁).op s)) =
        trivialTorsor (fppfJ.yonedaEquiv.symm
          (U.space.toSheaf.obj.map β₂.op (U.space.toSheaf.obj.map β₁.op s)))) :
    (atlasNaturalityIsoApp G U (β₂ ≫ β₁) s).hom ≫
        (ActionTorsor.pullbackCompIsoApp β₂ β₁
          (trivialTorsor (G := G) (U := U) (fppfJ.yonedaEquiv.symm s))).hom =
      eqToHom h ≫ (atlasNaturalityIsoApp G U β₂ (U.space.toSheaf.obj.map β₁.op s)).hom ≫
        (ActionTorsor.pullbackFunctor β₂).map ((atlasNaturalityIsoApp G U β₁ s).hom) := by
  have e : fppfJ.yonedaEquiv.symm (U.space.toSheaf.obj.map (β₂ ≫ β₁).op s) =
      fppfJ.yonedaEquiv.symm
        (U.space.toSheaf.obj.map β₂.op (U.space.toSheaf.obj.map β₁.op s)) :=
    congrArg _ (by simp)
  refine ConeQuotient.hom_ext_of_section (ConeQuotient.trivialSection _)
    (ConeQuotient.trivialSection_projection _) _ _ ?_
  conv_lhs => rw [comp_iso_hom, ← Category.assoc, trivialSection_comp_atlasNaturalityIsoApp,
    pullbackCompIsoApp_hom_iso_hom]
  conv_rhs => rw [comp_iso_hom, comp_iso_hom, ← Category.assoc,
    ConeQuotient.trivialSection_comp_eqToHom e h, ← Category.assoc,
    trivialSection_comp_atlasNaturalityIsoApp, pullbackFunctor_map_iso_hom]
  refine hom_ext_pullback₂ _ _ _ ?_ ?_
  · simp only [Category.assoc, FppfTorsor.pullbackCompIso_hom_fst_fst,
      pullbackMap_fst_iterated_assoc, ConeQuotient.pullbackSection_fst,
      ConeQuotient.pullbackSection_fst_assoc, trivialSection_comp_atlasNaturalityIsoApp_assoc,
      CategoryTheory.Functor.map_comp]
  · simp only [Category.assoc, FppfTorsor.pullbackCompIso_hom_snd,
      pullbackMap_snd_iterated, ConeQuotient.pullbackSection_snd]

/-! ### The atlas map -/

/-- The base-change comparison of the atlas map, as a natural isomorphism of fibre functors:
the atlas functor of the restricted points is the base change of the atlas functor. -/
noncomputable def atlasNaturalityIso (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    {T T' : Scheme.{u}} (β : T' ⟶ T) :
    stackPullback (FppfStack.ofAlgebraicSpace U.space) β ⋙ atlasFunctor G U T' ≅
      atlasFunctor G U T ⋙ ActionTorsor.pullbackFunctor β :=
  Discrete.natIso (fun x => atlasNaturalityIsoApp G U β x.as.down)

/-- **The atlas map `U → [U/G]`**: the morphism of fppf stacks sending a `T`-point `t` of the
algebraic space `U.space` to the trivial `G`-torsor over `T` with equivariant map `(g, s) ↦
g · t(s)`.  Its fibrewise functors are `ActionTorsor.atlasFunctor`, its strong naturality
isomorphisms are `ActionTorsor.atlasNaturalityIso`, and its two coherence laws are
`ActionTorsor.atlasNaturality_id` and `ActionTorsor.atlasNaturality_comp`. -/
noncomputable def atlasMap (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G) :
    StackHom (FppfStack.ofAlgebraicSpace U.space) (quotientStack G U) :=
  Pseudofunctor.StrongTrans.mkCatOfComponents
    (F := (FppfStack.ofAlgebraicSpace U.space).toPseudofunctor)
    (X := (quotientStack G U).toPseudofunctor)
    (fun (a : LocallyDiscrete Scheme.{u}ᵒᵖ) => (atlasFunctor G U a.as.unop).toCatHom)
    (fun {a b : LocallyDiscrete Scheme.{u}ᵒᵖ} (f : a ⟶ b) =>
      Cat.Hom.isoMk (atlasNaturalityIso G U f.as.unop))
    (fun a y => by
      obtain ⟨⟨s⟩⟩ := y
      exact atlasNaturality_id G U a.as.unop s (by simp))
    (fun f g y => by
      obtain ⟨⟨s⟩⟩ := y
      exact atlasNaturality_comp G U f.as.unop g.as.unop s (by simp))

/-- The value of the atlas map on a test scheme is the atlas functor. -/
theorem atlasMap_app (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (T : Scheme.{u}) :
    (atlasMap G U).app ⟨Opposite.op T⟩ = (atlasFunctor G U T).toCatHom :=
  rfl

/-- **The atlas map sends a `T`-point of `U.space` to its trivial torsor.** -/
@[simp]
theorem atlasMap_app_obj (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (T : Scheme.{u}) (s : U.space.toSheaf.obj.obj (Opposite.op T)) :
    ((atlasMap G U).app ⟨Opposite.op T⟩).toFunctor.obj (Discrete.mk (ULift.up s)) =
      trivialTorsor (fppfJ.yonedaEquiv.symm s) :=
  rfl

/-! ### The fibre of the atlas map over a torsor -/

/-- **Sections of an equivariant torsor with a prescribed point of `U` are the same as
trivialisations of it by that point.**  The forward map sends a section to the trivialisation
`ConeQuotient.isoTrivialOfSection`, the backward map evaluates a trivialisation at the unit
section of the trivial torsor. -/
noncomputable def sectionEquivTrivialisation (P : ActionTorsor G U T)
    (t : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    {σ : fppfYoneda.obj T ⟶ P.P // σ ≫ P.projection = 𝟙 _ ∧ σ ≫ P.target = t} ≃
      (ConeQuotient.trivialWithPoint t ≅ P) where
  toFun σ :=
    (eqToIso (congrArg ConeQuotient.trivialWithPoint σ.2.2.symm)).trans
      (ConeQuotient.isoTrivialOfSection P σ.1 σ.2.1)
  invFun e :=
    ⟨ConeQuotient.trivialSection t ≫ e.hom.iso.hom, by
        rw [Category.assoc, e.hom.over]
        exact ConeQuotient.trivialSection_projection t, by
        rw [Category.assoc, e.hom.target]
        exact ConeQuotient.trivialSection_comp_trivialTarget t⟩
  left_inv σ := by
    refine Subtype.ext ?_
    dsimp only
    rw [Iso.trans_hom, comp_iso_hom, eqToIso.hom, ← Category.assoc,
      ConeQuotient.trivialSection_comp_eqToHom σ.2.2.symm,
      ConeQuotient.isoTrivialOfSection_hom_iso_hom]
    exact ConeQuotient.unitSection_comp_sectionMap _
  right_inv e := by
    have ht : (ConeQuotient.trivialSection t ≫ e.hom.iso.hom) ≫ P.target = t := by
      rw [Category.assoc, e.hom.target]
      exact ConeQuotient.trivialSection_comp_trivialTarget t
    refine Iso.ext (ConeQuotient.hom_ext_of_section (ConeQuotient.trivialSection t)
      (ConeQuotient.trivialSection_projection t) _ _ ?_)
    dsimp only
    rw [Iso.trans_hom, comp_iso_hom, eqToIso.hom, ← Category.assoc,
      ConeQuotient.trivialSection_comp_eqToHom ht.symm,
      ConeQuotient.isoTrivialOfSection_hom_iso_hom]
    exact ConeQuotient.unitSection_comp_sectionMap _

/-- Sections of a base change `P|_S` with a prescribed point of `U` are the same as sections of
`P` over the base map `b : S ⟶ T` with that point. -/
noncomputable def pullbackSectionEquiv (P : ActionTorsor G U T) {S : Scheme.{u}} (b : S ⟶ T)
    (t : fppfYoneda.obj S ⟶ U.space.toSheaf) :
    {τ : fppfYoneda.obj S ⟶ P.P // τ ≫ P.projection = fppfYoneda.map b ∧ τ ≫ P.target = t} ≃
      {σ : fppfYoneda.obj S ⟶ (pullbackObj b P).P //
        σ ≫ (pullbackObj b P).projection = 𝟙 _ ∧ σ ≫ (pullbackObj b P).target = t} where
  toFun τ :=
    ⟨Limits.pullback.lift τ.1 (𝟙 _) (by rw [τ.2.1, Category.id_comp]),
      Limits.pullback.lift_snd _ _ _, by
        rw [pullbackObj_target, ← Category.assoc, Limits.pullback.lift_fst]
        exact τ.2.2⟩
  invFun σ :=
    ⟨σ.1 ≫ Limits.pullback.fst P.projection (fppfYoneda.map b), by
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, σ.2.1,
          Category.id_comp], by
        rw [Category.assoc]
        exact σ.2.2⟩
  left_inv τ := Subtype.ext (Limits.pullback.lift_fst _ _ _)
  right_inv σ := by
    refine Subtype.ext (Limits.pullback.hom_ext ?_ ?_)
    · exact Limits.pullback.lift_fst _ _ _
    · rw [Limits.pullback.lift_snd]
      exact σ.2.1.symm

/-- **The fibre of the atlas map over a torsor `P` is the torsor `P` itself**: for a
test scheme `S`, a scheme morphism `b : S ⟶ T` and an `S`-point `s` of `U.space`, the
isomorphisms between the image `atlasMap(s)` of `s` and the base change `P|_S` — that is, the
objects of the 2-fibre product `S ×_{[U/G]} U.space` over `(b, P)` — are exactly the sections of
the sheaf `P.P` over `b` whose associated point of `U.space` is `s`. -/
noncomputable def atlasFibreEquiv (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    {T S : Scheme.{u}} (P : ActionTorsor G U T) (b : S ⟶ T)
    (s : U.space.toSheaf.obj.obj (Opposite.op S)) :
    {τ : fppfYoneda.obj S ⟶ P.P // τ ≫ P.projection = fppfYoneda.map b ∧
        τ ≫ P.target = fppfJ.yonedaEquiv.symm s} ≃
      (((atlasMap G U).app ⟨Opposite.op S⟩).toFunctor.obj (Discrete.mk (ULift.up s)) ≅
        (stackPullback (quotientStack G U) b).obj P) :=
  (pullbackSectionEquiv P b (fppfJ.yonedaEquiv.symm s)).trans
    (sectionEquivTrivialisation (pullbackObj b P) (fppfJ.yonedaEquiv.symm s))

/-! ### Charts of the quotient stack -/

/-- The represented stack of a scheme is the discrete stack of the algebraic space of that
scheme; both are the discrete stack of the fppf sheaf `fppfYoneda.obj X₀`. -/
theorem representedStack_eq (X₀ : Scheme.{u}) :
    representedStack X₀ = FppfStack.ofAlgebraicSpace (AlgebraicSpace.ofScheme.obj X₀) :=
  rfl

/-- **A chart of `[U/G]` attached to a scheme-valued point of `U.space`**: for any morphism of
fppf sheaves `a : fppfYoneda.obj X₀ ⟶ U.space.toSheaf` — for instance the étale atlas of the
algebraic space `U.space`, or the identity when `U.space` is represented by `X₀` — the composite
of the induced map of discrete stacks with the atlas map is a chart with chart scheme `X₀`.
No smoothness or surjectivity is claimed here (that is issue #37). -/
noncomputable def schemeAtlasChart (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (X₀ : Scheme.{u}) (a : fppfYoneda.obj X₀ ⟶ U.space.toSheaf) :
    StackChart (quotientStack G U) where
  scheme := X₀
  map := Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSheafHom a) (atlasMap G U)

/-- The chart scheme of `schemeAtlasChart` is the given scheme. -/
@[simp]
theorem schemeAtlasChart_scheme (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (X₀ : Scheme.{u}) (a : fppfYoneda.obj X₀ ⟶ U.space.toSheaf) :
    (schemeAtlasChart G U X₀ a).scheme = X₀ :=
  rfl

/-- The objects of the chart `schemeAtlasChart` are the trivial torsors of the points of
`U.space` obtained from the scheme morphisms into the chart scheme.  This is `rfl`. -/
@[simp]
theorem schemeAtlasChart_obj (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (X₀ : Scheme.{u}) (a : fppfYoneda.obj X₀ ⟶ U.space.toSheaf) (T : Scheme.{u})
    (g : T ⟶ X₀) :
    (schemeAtlasChart G U X₀ a).obj T g =
      trivialTorsor (fppfJ.yonedaEquiv.symm (a.hom.app (Opposite.op T) g)) :=
  rfl

/-- **The atlas chart of `[U/G]` for an action on the algebraic space of a scheme**: if
`U.space` is the algebraic space of a scheme `X₀`, the atlas map is a chart of `[U/G]` with
chart scheme `X₀`.  Again no smoothness or surjectivity is claimed. -/
noncomputable def atlasChart (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (X₀ : Scheme.{u}) (h : U.space = AlgebraicSpace.ofScheme.obj X₀) :
    StackChart (quotientStack G U) :=
  schemeAtlasChart G U X₀ (eqToHom (congrArg (fun Y : AlgebraicSpace.{u} => Y.toSheaf) h).symm)

/-- The chart scheme of `atlasChart` is the given scheme. -/
@[simp]
theorem atlasChart_scheme (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (X₀ : Scheme.{u}) (h : U.space = AlgebraicSpace.ofScheme.obj X₀) :
    (atlasChart G U X₀ h).scheme = X₀ :=
  rfl

end ActionTorsor

end GromovWitten.AlgebraicGeometry
