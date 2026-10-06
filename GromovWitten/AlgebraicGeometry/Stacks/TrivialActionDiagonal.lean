/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Stacks.ClassifyingStackDiagonal
import GromovWitten.AlgebraicGeometry.Stacks.ClassifyingStackSelfOverlap
import GromovWitten.AlgebraicGeometry.Stacks.TorsorPushout

/-!
# The diagonal of `[S/G]` for a trivial action, and the Deligne–Mumford stack `[Spec k / Γ]`

Let `G` be a group algebraic space acting trivially on a scheme `S`, i.e. on the algebraic space
`AlgebraicSpace.ofScheme.obj S`, through `AlgebraicSpaceAction.trivial`.  An object of the
quotient stack `[S/G]` over `T` is a `G`-torsor `P → T` together with a `G`-equivariant map
`ψ : P → S`; since the action on `S` is trivial, `ψ` is `G`-invariant and descends uniquely
through the torsor to a morphism of schemes `T ⟶ S`, the *structure map* of the object.

## Main results

* `ActionTorsor.structureMap`, `ActionTorsor.projection_structureMap`,
  `ActionTorsor.structureMap_unique`: the descent of the equivariant map of an object of
  `[S/G]` through its torsor, and its uniqueness; `ActionTorsor.structureMap_pullbackObj` is its
  naturality in the base.
* `ActionTorsor.structureMap_eq_of_iso`, `ActionTorsor.isoOfPointIso`,
  `ActionTorsor.exists_iso_iff_structureMap`: an isomorphism of the underlying `BG`-objects of
  `f^* x` and `f^* y` is an isomorphism in `[S/G]` exactly when
  `f ≫ x.structureMap = f ≫ y.structureMap`.
* `ActionTorsor.forgetToPoint`, `ActionTorsor.isomSheafIsoEqualizer`: the isomorphism sheaf
  `Isom_{[S/G]}(x, y)` is the equaliser of the two maps `Isom_{BG}(x̄, ȳ) ⟶ S` given by the
  structure maps, as fppf sheaves.
* `ActionTorsor.exists_isomRepresentation_of_point`, `ActionTorsor.isomSheafIsoOfPoint`: if
  `Isom_{BG}(x̄, ȳ)` is represented by `w : W ⟶ T`, then `Isom_{[S/G]}(x, y)` is represented by
  the equaliser of `w ≫ x.structureMap` and `w ≫ y.structureMap` (a closed immersion into `W`
  when `S` is separated), and by `W` itself when these two maps agree.
* `ActionTorsor.exists_isomRepresentation_trivial`: for `G = affineGroup R grp` with `R` finite
  étale over `ℤ` and `S` separated, `Isom_{[S/G]}(x, y)` is represented by a scheme finite over
  the base.
* `ActionTorsor.hasRepresentableDiagonal_quotientStack_trivial`,
  `ActionTorsor.trivialQuotientAlgebraicStack`, `ActionTorsor.trivialQuotientDeligneMumfordStack`:
  `[S/G]` has a representable diagonal and is a Deligne–Mumford stack with étale atlas
  `S → [S/G]`.
* `constantQuotientDeligneMumfordStack k Γ`: the Deligne–Mumford stack `[Spec k / Γ]` for a
  finite group `Γ` acting trivially on `Spec k` (`constantTrivialAction k Γ` of
  `Stacks/ClassifyingStackSelfOverlap.lean`), with the explicit étale surjective atlas
  `constantAtlasChart k Γ` of scheme `Spec k`.  (The atlas
  `DeligneMumfordStack.chosenEtaleAtlas` of a Deligne–Mumford stack is `Classical.choose` of the
  existence statement, so nothing can be said about its scheme; all statements about the atlas
  of `[Spec k / Γ]` are made for the explicit chart `constantAtlasChart k Γ`.)
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

open TorsorPushout

namespace ActionTorsor

/-! ### Descent of the equivariant map through the torsor -/

section Descent

variable {G : AlgebraicSpaceGroup.{u}} {S T : Scheme.{u}}

/-- The map `x.target : P ⟶ S` of an object of `[S/G]` (trivial action on `S`), with its
codomain written as the fppf sheaf `fppfYoneda.obj S` of the scheme `S`. -/
noncomputable abbrev structureTarget
    (x : ActionTorsor G (AlgebraicSpaceAction.trivial G (AlgebraicSpace.ofScheme.obj S)) T) :
    x.P ⟶ fppfYoneda.obj S :=
  x.target

/-- For the trivial action on `S`, the map `x.target : P ⟶ S` of an object of `[S/G]` is
`G`-invariant. -/
theorem smul_structureTarget
    (x : ActionTorsor G (AlgebraicSpaceAction.trivial G (AlgebraicSpace.ofScheme.obj S)) T) :
    ModObj.smul (M := G.space.toSheaf) (X := x.P) ≫ x.structureTarget =
      snd G.space.toSheaf x.P ≫ x.structureTarget := by
  change ModObj.smul (M := G.space.toSheaf) (X := x.P) ≫ x.target =
    snd G.space.toSheaf x.P ≫ x.target
  rw [x.target_equivariant]
  exact whiskerLeft_snd _ _

/-- Translating a point of the torsor by a point of the group does not change its image in
`S` (trivial action). -/
theorem actPt_structureTarget
    (x : ActionTorsor G (AlgebraicSpaceAction.trivial G (AlgebraicSpace.ofScheme.obj S)) T)
    {Z : FppfSheaf.{u}} (g : Z ⟶ G.space.toSheaf) (p : Z ⟶ x.P) :
    actPt g p ≫ x.structureTarget = p ≫ x.structureTarget := by
  rw [actPt, Category.assoc, smul_structureTarget, lift_snd_assoc]

/-- Two points of the torsor with the same image in the base have the same image in `S`
(trivial action). -/
theorem structureTarget_eq_of_projection_eq
    (x : ActionTorsor G (AlgebraicSpaceAction.trivial G (AlgebraicSpace.ofScheme.obj S)) T)
    {Z : FppfSheaf.{u}} (p q : Z ⟶ x.P) (h : p ≫ x.projection = q ≫ x.projection) :
    p ≫ x.structureTarget = q ≫ x.structureTarget := by
  rw [← actPt_divPt p q h, actPt_structureTarget]

variable (x : ActionTorsor G (AlgebraicSpaceAction.trivial G (AlgebraicSpace.ofScheme.obj S)) T)

/-- The tautological point of the torsor of `x` above a member of its trivialising covering
sieve. -/
noncomputable def sievePt {W : Scheme.{u}} {g : W ⟶ T} (hg : (coverSieve x.toFppfTorsor).arrows g) :
    fppfYoneda.obj W ⟶ x.P :=
  coverPt (exists_factor_of_coverSieve hg).choose

/-- The tautological point lies above the member of the sieve. -/
theorem sievePt_projection {W : Scheme.{u}} {g : W ⟶ T}
    (hg : (coverSieve x.toFppfTorsor).arrows g) :
    sievePt x hg ≫ x.projection = fppfYoneda.map g := by
  change coverPt (P := x.toFppfTorsor) _ ≫ x.toFppfTorsor.projection = _
  rw [coverPt_proj, (exists_factor_of_coverSieve hg).choose_spec]

/-- The compatible family of morphisms to `S` on the members of the trivialising covering sieve
of the torsor of `x`: a member `g : W ⟶ T` factors through the trivialising cover, and the
corresponding tautological point of the torsor is sent to `S` by `x.target`. -/
noncomputable def structureFamily :
    Presieve.FamilyOfElements (fppfYoneda.obj S).obj (coverSieve x.toFppfTorsor).arrows :=
  fun _ _ hg => fppfYoneda.preimage (sievePt x hg ≫ x.structureTarget)

/-- The value of `structureFamily` at a member `g` is the image of any point of the torsor
above `g`. -/
theorem structureFamily_eq {W : Scheme.{u}} {g : W ⟶ T} (hg : (coverSieve x.toFppfTorsor).arrows g)
    (p : fppfYoneda.obj W ⟶ x.P) (hp : p ≫ x.projection = fppfYoneda.map g) :
    fppfYoneda.map (structureFamily x g hg) = p ≫ x.structureTarget := by
  unfold structureFamily
  rw [Functor.map_preimage]
  refine structureTarget_eq_of_projection_eq x _ _ ?_
  rw [hp, sievePt_projection]

/-- The family `structureFamily` is compatible. -/
theorem structureFamily_compatible : (structureFamily x).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hc
  change g₁ ≫ structureFamily x f₁ h₁ = g₂ ≫ structureFamily x f₂ h₂
  apply fppfYoneda.map_injective
  rw [Functor.map_comp, Functor.map_comp, structureFamily_eq x h₁ _ (sievePt_projection x h₁),
    structureFamily_eq x h₂ _ (sievePt_projection x h₂), ← Category.assoc, ← Category.assoc]
  refine structureTarget_eq_of_projection_eq x _ _ ?_
  rw [Category.assoc, Category.assoc, sievePt_projection, sievePt_projection,
    ← Functor.map_comp, ← Functor.map_comp, hc]

/-- A point of the torsor with representable source lies above the morphism of schemes
`yonedaEquiv (p ≫ x.projection)`. -/
theorem comp_projection_eq_map {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ x.P) :
    p ≫ x.projection = fppfYoneda.map (fppfJ.yonedaEquiv (p ≫ x.projection)) := by
  apply fppfJ.yonedaEquiv.injective
  rw [GrothendieckTopology.yonedaEquiv_yoneda_map]

/-- Separatedness of morphisms out of a sheaf over `T` along a covering sieve, in terms of
points: two morphisms `φ ψ : A ⟶ B` agree as soon as they agree on every point of `A` with
representable source lying above a member of the sieve. -/
theorem hom_ext_of_sieve_points {A B : FppfSheaf.{u}} (π : A ⟶ fppfYoneda.obj T) {R : Sieve T}
    (hR : R ∈ fppfJ.{u} T) {φ ψ : A ⟶ B}
    (h : ∀ (W : Scheme.{u}) (p : fppfYoneda.obj W ⟶ A), R.arrows (fppfJ.yonedaEquiv (p ≫ π)) →
      p ≫ φ = p ≫ ψ) : φ = ψ := by
  refine SheafGluing.hom_ext_of_sieve π hR fun W z => ?_
  have hz : R.arrows (fppfJ.yonedaEquiv (fppfJ.yonedaEquiv.symm z.1 ≫ π)) := by
    rw [GrothendieckTopology.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact z.2
  have key := h W (fppfJ.yonedaEquiv.symm z.1) hz
  have e1 := GrothendieckTopology.yonedaEquiv_comp fppfJ (fppfJ.yonedaEquiv.symm z.1) φ
  have e2 := GrothendieckTopology.yonedaEquiv_comp fppfJ (fppfJ.yonedaEquiv.symm z.1) ψ
  rw [Equiv.apply_symm_apply] at e1 e2
  rw [← e1, ← e2, key]

/-- **Descent of the equivariant map** (blueprint B1.1): for the trivial action on `S`, the
map `x.target : P ⟶ S` of an object of `[S/G]` over `T` factors uniquely through the torsor
projection `P ⟶ T`. -/
theorem existsUnique_structureMap :
    ∃! t : T ⟶ S, x.projection ≫ fppfYoneda.map t = x.structureTarget := by
  have hsheaf : Presieve.IsSheafFor (fppfYoneda.obj S).obj (coverSieve x.toFppfTorsor).arrows :=
    SheafGluing.isSheafOfType (fppfYoneda.obj S) _ (coverSieve_mem x.toFppfTorsor)
  obtain ⟨t, ht, -⟩ := hsheaf (structureFamily x) (structureFamily_compatible x)
  have hamalg : ∀ {W : Scheme.{u}} (g : W ⟶ T) (hg : (coverSieve x.toFppfTorsor).arrows g),
      g ≫ t = structureFamily x g hg := fun g hg => ht g hg
  refine ⟨t, ?_, fun t' ht' => ?_⟩
  · refine hom_ext_of_sieve_points x.projection (coverSieve_mem x.toFppfTorsor)
      fun W p hp => ?_
    rw [← Category.assoc, comp_projection_eq_map x p, ← Functor.map_comp, hamalg _ hp,
      structureFamily_eq x hp p (comp_projection_eq_map x p)]
  · apply fppfYoneda.map_injective
    refine hom_ext_of_sieve_points (𝟙 (fppfYoneda.obj T)) (coverSieve_mem x.toFppfTorsor)
      (φ := fppfYoneda.map t') (ψ := fppfYoneda.map t) fun W p hp => ?_
    rw [Category.comp_id] at hp
    have hp' : p = fppfYoneda.map (fppfJ.yonedaEquiv p) := by
      apply fppfJ.yonedaEquiv.injective
      rw [GrothendieckTopology.yonedaEquiv_yoneda_map]
    rw [hp', ← Functor.map_comp, ← Functor.map_comp, hamalg _ hp,
      structureFamily_eq x hp _ (sievePt_projection x hp), Functor.map_comp,
      ← sievePt_projection x hp, Category.assoc]
    exact congrArg _ ht'

/-- **The structure map** `T ⟶ S` of an object of `[S/G]` over `T` (trivial action on `S`):
the unique morphism through which `x.target : P ⟶ S` factors via the torsor projection. -/
noncomputable def structureMap : T ⟶ S :=
  (existsUnique_structureMap x).exists.choose

/-- The defining property of the structure map. -/
@[reassoc (attr := simp)]
theorem projection_structureMap :
    x.projection ≫ fppfYoneda.map x.structureMap = x.structureTarget :=
  (existsUnique_structureMap x).exists.choose_spec

/-- The structure map is the unique morphism through which `x.target` factors. -/
theorem structureMap_unique (t : T ⟶ S)
    (ht : x.projection ≫ fppfYoneda.map t = x.structureTarget) :
    t = x.structureMap :=
  (existsUnique_structureMap x).unique ht (projection_structureMap x)

/-- **Naturality of the structure map**: the structure map of the base change `f^* x` is
`f ≫ x.structureMap`. -/
@[simp]
theorem structureMap_pullbackObj {T' : Scheme.{u}} (f : T' ⟶ T) :
    (pullbackObj f x).structureMap = f ≫ x.structureMap := by
  symm
  apply structureMap_unique
  change pullback.snd x.projection (fppfYoneda.map f) ≫ fppfYoneda.map (f ≫ x.structureMap) =
    pullback.fst x.projection (fppfYoneda.map f) ≫ x.structureTarget
  rw [Functor.map_comp, ← Category.assoc, ← pullback.condition, Category.assoc,
    projection_structureMap]

end Descent

/-! ### Isomorphisms in `[S/G]` versus isomorphisms in `BG` -/

section Point

variable {G : AlgebraicSpaceGroup.{u}} {S T : Scheme.{u}}

/-- The object of `BG` underlying an object of `[S/G]` (trivial action on `S`): the same torsor,
mapped to the point (see `toPointObj_eq_mapTarget`). -/
noncomputable abbrev toPointObj
    (x : ActionTorsor G (AlgebraicSpaceAction.trivial G (AlgebraicSpace.ofScheme.obj S)) T) :
    ActionTorsor G (AlgebraicSpaceAction.pointAction G) T where
  toFppfTorsor := x.toFppfTorsor
  target := AlgebraicSpaceAction.pointIsTerminal.from x.P
  target_equivariant := AlgebraicSpaceAction.pointIsTerminal.hom_ext _ _

/-- `toPointObj x` is the image of `x` under the functor `[S/G] → BG` induced by the equivariant
map `S → pt` (`ActionTorsor.mapTarget`). -/
theorem toPointObj_eq_mapTarget
    (x : ActionTorsor G (AlgebraicSpaceAction.trivial G (AlgebraicSpace.ofScheme.obj S)) T) :
    toPointObj x = mapTarget (AlgebraicSpaceAction.toPoint _) x := by
  cases x
  simp only [toPointObj, mapTarget]
  congr 1
  exact AlgebraicSpaceAction.pointIsTerminal.hom_ext _ _

/-- The torsor underlying `toPointObj x` is that of `x`. -/
@[simp]
theorem toPointObj_toFppfTorsor
    (x : ActionTorsor G (AlgebraicSpaceAction.trivial G (AlgebraicSpace.ofScheme.obj S)) T) :
    (toPointObj x).toFppfTorsor = x.toFppfTorsor :=
  rfl

variable (x y : ActionTorsor G (AlgebraicSpaceAction.trivial G (AlgebraicSpace.ofScheme.obj S)) T)
  {S' : Scheme.{u}} (f : S' ⟶ T)

/-- An isomorphism `f^* x ≅ f^* y` in `[S/G]` is in particular an isomorphism of the underlying
objects of `BG`. -/
noncomputable def pointIsoOfIso (e : pullbackObj f x ≅ pullbackObj f y) :
    pullbackObj f (toPointObj x) ≅ pullbackObj f (toPointObj y) :=
  asIso
    { iso := e.hom.iso
      over := e.hom.over
      equivariant := e.hom.equivariant
      target := AlgebraicSpaceAction.pointIsTerminal.hom_ext _ _ }

/-- The underlying sheaf map of `pointIsoOfIso e` is that of `e`. -/
@[simp]
theorem pointIsoOfIso_hom_iso_hom (e : pullbackObj f x ≅ pullbackObj f y) :
    (pointIsoOfIso x y f e).hom.iso.hom = e.hom.iso.hom :=
  rfl

/-- **An isomorphism in `[S/G]` forces the structure maps to agree** (blueprint B1.2, `→`):
if `f^* x ≅ f^* y` in `[S/G]`, then `f ≫ x.structureMap = f ≫ y.structureMap`. -/
theorem structureMap_eq_of_iso (e : pullbackObj f x ≅ pullbackObj f y) :
    f ≫ x.structureMap = f ≫ y.structureMap := by
  rw [← structureMap_pullbackObj x f]
  symm
  apply structureMap_unique
  rw [← e.hom.over, Category.assoc, ← structureMap_pullbackObj y f, projection_structureMap]
  exact e.hom.target

/-- If `f ≫ x.structureMap = f ≫ y.structureMap`, every isomorphism of the underlying
`BG`-objects of `f^* x` and `f^* y` is compatible with the maps to `S`. -/
theorem comp_structureTarget_pullbackObj (hf : f ≫ x.structureMap = f ≫ y.structureMap)
    (ē : pullbackObj f (toPointObj x) ≅ pullbackObj f (toPointObj y)) :
    ē.hom.iso.hom ≫ (pullbackObj f y).structureTarget = (pullbackObj f x).structureTarget := by
  rw [← projection_structureMap (pullbackObj f y), ← projection_structureMap (pullbackObj f x),
    structureMap_pullbackObj, structureMap_pullbackObj, ← hf, ← Category.assoc]
  congr 1
  exact ē.hom.over

/-- **An isomorphism in `BG` with agreeing structure maps is an isomorphism in `[S/G]`**
(blueprint B1.2, `←`). -/
noncomputable def isoOfPointIso (hf : f ≫ x.structureMap = f ≫ y.structureMap)
    (ē : pullbackObj f (toPointObj x) ≅ pullbackObj f (toPointObj y)) :
    pullbackObj f x ≅ pullbackObj f y :=
  asIso
    { iso := ē.hom.iso
      over := ē.hom.over
      equivariant := ē.hom.equivariant
      target := comp_structureTarget_pullbackObj x y f hf ē }

/-- The underlying sheaf map of `isoOfPointIso hf ē` is that of `ē`. -/
@[simp]
theorem isoOfPointIso_hom_iso_hom (hf : f ≫ x.structureMap = f ≫ y.structureMap)
    (ē : pullbackObj f (toPointObj x) ≅ pullbackObj f (toPointObj y)) :
    (isoOfPointIso x y f hf ē).hom.iso.hom = ē.hom.iso.hom :=
  rfl

end Point

/-! ### The isomorphism sheaf of `[S/G]` inside that of `BG` -/

section IsomSheaf

variable {G : AlgebraicSpaceGroup.{u}} {S T : Scheme.{u}}
  (x y : ActionTorsor G (AlgebraicSpaceAction.trivial G (AlgebraicSpace.ofScheme.obj S)) T)
  (RP : TorsorRepresentation x.toFppfTorsor) (RQ : TorsorRepresentation y.toFppfTorsor)

namespace IsomPoint

variable {x y RP RQ} {S' : Scheme.{u}}

/-- The point of `Isom_{BG}(x̄, ȳ)` underlying a point of `Isom_{[S/G]}(x, y)`. -/
noncomputable def toPoint (p : IsomPoint x y RP RQ S') :
    IsomPoint (toPointObj x) (toPointObj y) RP RQ S' where
  f := p.f
  hom := p.hom
  exists_iso := ⟨pointIsoOfIso x y p.f p.iso, p.repPullbackHom_comp_iso_hom⟩

/-- The test map of `p.toPoint` is that of `p`. -/
@[simp]
theorem toPoint_f (p : IsomPoint x y RP RQ S') : p.toPoint.f = p.f :=
  rfl

/-- The morphism of representing schemes of `p.toPoint` is that of `p`. -/
@[simp]
theorem toPoint_hom (p : IsomPoint x y RP RQ S') : p.toPoint.hom = p.hom :=
  rfl

/-- `toPoint` is injective: a point of `Isom_{[S/G]}(x, y)` is determined by its underlying
point of `Isom_{BG}(x̄, ȳ)`. -/
theorem toPoint_injective :
    Function.Injective (toPoint : IsomPoint x y RP RQ S' → _) := by
  intro p q h
  have hf : p.f = q.f :=
    congrArg (fun r : IsomPoint (toPointObj x) (toPointObj y) RP RQ S' => r.f) h
  have hh : HEq p.hom q.hom := by
    have : HEq p.toPoint.hom q.toPoint.hom := by rw [h]
    exact this
  exact ext_heq hf hh

/-- The structure maps of `x` and `y` agree after composition with the test map of any point of
`Isom_{[S/G]}(x, y)`. -/
theorem f_comp_structureMap (p : IsomPoint x y RP RQ S') :
    p.f ≫ x.structureMap = p.f ≫ y.structureMap :=
  structureMap_eq_of_iso x y p.f p.iso

/-- A point of `Isom_{BG}(x̄, ȳ)` whose test map equalises the structure maps of `x` and `y`
is a point of `Isom_{[S/G]}(x, y)`. -/
noncomputable def ofPoint (q : IsomPoint (toPointObj x) (toPointObj y) RP RQ S')
    (h : q.f ≫ x.structureMap = q.f ≫ y.structureMap) : IsomPoint x y RP RQ S' where
  f := q.f
  hom := q.hom
  exists_iso := ⟨isoOfPointIso x y q.f h q.iso, q.repPullbackHom_comp_iso_hom⟩

/-- `ofPoint` is a section of `toPoint`. -/
@[simp]
theorem toPoint_ofPoint (q : IsomPoint (toPointObj x) (toPointObj y) RP RQ S')
    (h : q.f ≫ x.structureMap = q.f ≫ y.structureMap) : (ofPoint q h).toPoint = q :=
  rfl

/-- `ofPoint` is a retraction of `toPoint`. -/
@[simp]
theorem ofPoint_toPoint (p : IsomPoint x y RP RQ S')
    (h : p.toPoint.f ≫ x.structureMap = p.toPoint.f ≫ y.structureMap) :
    ofPoint p.toPoint h = p :=
  rfl

/-- `toPoint` commutes with restriction along morphisms of test schemes. -/
theorem toPoint_restrict {S'' : Scheme.{u}} (g : S'' ⟶ S') (p : IsomPoint x y RP RQ S') :
    (p.restrict g).toPoint = p.toPoint.restrict g :=
  rfl

end IsomPoint

/-- **The isomorphism sheaf of `[S/G]` maps to that of `BG`**: the morphism of fppf sheaves
`Isom_{[S/G]}(x, y) ⟶ Isom_{BG}(x̄, ȳ)` forgetting the compatibility with the maps to `S`. -/
noncomputable def forgetToPoint :
    isomSheaf x y RP RQ ⟶ isomSheaf (toPointObj x) (toPointObj y) RP RQ :=
  ObjectProperty.homMk
    { app := fun Z => ↾fun p : IsomPoint x y RP RQ Z.unop => p.toPoint
      naturality := fun _ _ _ => rfl }

/-- `forgetToPoint` acts on points by `IsomPoint.toPoint`. -/
@[simp]
theorem forgetToPoint_app {Z : Scheme.{u}} (p : IsomPoint x y RP RQ Z) :
    (forgetToPoint x y RP RQ).hom.app (op Z) p = p.toPoint :=
  rfl

/-- `forgetToPoint` acts on points with representable source by `IsomPoint.toPoint`. -/
theorem yonedaEquiv_comp_forgetToPoint {Z : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ isomSheaf x y RP RQ) :
    fppfJ.yonedaEquiv (α ≫ forgetToPoint x y RP RQ) = (fppfJ.yonedaEquiv α).toPoint := by
  rw [GrothendieckTopology.yonedaEquiv_comp]
  rfl

/-- `forgetToPoint` lies over `T`. -/
@[reassoc (attr := simp)]
theorem forgetToPoint_isomProjection :
    forgetToPoint x y RP RQ ≫ isomProjection (toPointObj x) (toPointObj y) RP RQ =
      isomProjection x y RP RQ := by
  apply ObjectProperty.hom_ext
  ext ⟨Z⟩ p
  rfl

/-- `forgetToPoint` equalises the two maps `Isom_{BG}(x̄, ȳ) ⟶ S` given by the structure
maps of `x` and `y`. -/
theorem forgetToPoint_comp_structureMap :
    forgetToPoint x y RP RQ ≫ isomProjection (toPointObj x) (toPointObj y) RP RQ ≫
        fppfYoneda.map x.structureMap =
      forgetToPoint x y RP RQ ≫ isomProjection (toPointObj x) (toPointObj y) RP RQ ≫
        fppfYoneda.map y.structureMap := by
  rw [forgetToPoint_isomProjection_assoc, forgetToPoint_isomProjection_assoc]
  apply hom_ext_points
  intro Z α
  rw [← Category.assoc, ← Category.assoc, comp_isomProjection, ← Functor.map_comp,
    ← Functor.map_comp, (fppfJ.yonedaEquiv α).f_comp_structureMap]

/-- The comparison map from `Isom_{[S/G]}(x, y)` to the equaliser of the two maps
`Isom_{BG}(x̄, ȳ) ⟶ S` given by the structure maps. -/
noncomputable def toIsomEqualizer :
    isomSheaf x y RP RQ ⟶
      equalizer (isomProjection (toPointObj x) (toPointObj y) RP RQ ≫
          fppfYoneda.map x.structureMap)
        (isomProjection (toPointObj x) (toPointObj y) RP RQ ≫ fppfYoneda.map y.structureMap) :=
  equalizer.lift (forgetToPoint x y RP RQ) (forgetToPoint_comp_structureMap x y RP RQ)

/-- `toIsomEqualizer` followed by the inclusion of the equaliser is `forgetToPoint`. -/
@[reassoc (attr := simp)]
theorem toIsomEqualizer_ι :
    toIsomEqualizer x y RP RQ ≫ equalizer.ι _ _ = forgetToPoint x y RP RQ :=
  equalizer.lift_ι _ _

/-- **`Isom_{[S/G]}(x, y)` is the equaliser inside `Isom_{BG}(x̄, ȳ)`** (blueprint B1.2):
the comparison map `toIsomEqualizer` is an isomorphism of fppf sheaves. -/
instance isIso_toIsomEqualizer : IsIso (toIsomEqualizer x y RP RQ) := by
  refine fppfSheaf_isIso_of_bijective _ fun Z => ⟨?_, ?_⟩
  · intro α β h
    have h' : α ≫ forgetToPoint x y RP RQ = β ≫ forgetToPoint x y RP RQ := by
      have := congrArg (· ≫ equalizer.ι _ _) h
      simpa only [Category.assoc, toIsomEqualizer_ι] using this
    apply fppfJ.yonedaEquiv.injective
    apply IsomPoint.toPoint_injective
    rw [← yonedaEquiv_comp_forgetToPoint, ← yonedaEquiv_comp_forgetToPoint, h']
  · intro β
    obtain ⟨q, hq⟩ : ∃ q : IsomPoint (toPointObj x) (toPointObj y) RP RQ Z,
        q = fppfJ.yonedaEquiv (β ≫ equalizer.ι _ _) := ⟨_, rfl⟩
    have hβ : β ≫ equalizer.ι _ _ = fppfJ.yonedaEquiv.symm q := by
      rw [hq, Equiv.symm_apply_apply]
    have hcond : q.f ≫ x.structureMap = q.f ≫ y.structureMap := by
      apply fppfYoneda.map_injective
      have := β ≫= equalizer.condition
        (isomProjection (toPointObj x) (toPointObj y) RP RQ ≫ fppfYoneda.map x.structureMap)
        (isomProjection (toPointObj x) (toPointObj y) RP RQ ≫ fppfYoneda.map y.structureMap)
      simp only [← Category.assoc, comp_isomProjection] at this
      rw [Functor.map_comp, Functor.map_comp, hq]
      exact this
    obtain ⟨σ, hσ⟩ : ∃ σ : (isomSheaf x y RP RQ).obj.obj (op Z), σ = IsomPoint.ofPoint q hcond :=
      ⟨_, rfl⟩
    refine ⟨fppfJ.yonedaEquiv.symm σ, ?_⟩
    apply (cancel_mono (equalizer.ι _ _)).1
    change (_ ≫ toIsomEqualizer x y RP RQ) ≫ _ = _
    rw [Category.assoc, toIsomEqualizer_ι, hβ,
      GrothendieckTopology.yonedaEquiv_symm_naturality_right, hσ]
    rfl

/-- **`Isom_{[S/G]}(x, y) ≅ Eq(Isom_{BG}(x̄, ȳ) ⇉ S)`** (blueprint B1.2): the isomorphism sheaf
of two objects of `[S/G]` is the equaliser, inside the isomorphism sheaf of their underlying
`BG`-objects, of the two maps to `S` given by the structure maps of `x` and `y`. -/
noncomputable def isomSheafIsoEqualizer :
    isomSheaf x y RP RQ ≅
      equalizer (isomProjection (toPointObj x) (toPointObj y) RP RQ ≫
          fppfYoneda.map x.structureMap)
        (isomProjection (toPointObj x) (toPointObj y) RP RQ ≫ fppfYoneda.map y.structureMap) :=
  asIso (toIsomEqualizer x y RP RQ)

/-- The isomorphism `isomSheafIsoEqualizer` followed by the inclusion of the equaliser is
`forgetToPoint`. -/
@[reassoc (attr := simp)]
theorem isomSheafIsoEqualizer_hom_ι :
    (isomSheafIsoEqualizer x y RP RQ).hom ≫ equalizer.ι _ _ = forgetToPoint x y RP RQ :=
  toIsomEqualizer_ι x y RP RQ

/-- **Pointwise form of blueprint B1.2** (`isomPoint_iff`): a point of `Isom_{BG}(x̄, ȳ)` is the
underlying point of a point of `Isom_{[S/G]}(x, y)`, i.e. its isomorphism is compatible with
the maps to `S`, exactly when its test map equalises the structure maps of `x` and `y`. -/
theorem exists_iso_iff_structureMap {S' : Scheme.{u}}
    (q : IsomPoint (toPointObj x) (toPointObj y) RP RQ S') :
    (∃ e : pullbackObj q.f x ≅ pullbackObj q.f y,
        repPullbackHom RP q.f ≫ e.hom.iso.hom = fppfYoneda.map q.hom ≫ repPullbackHom RQ q.f) ↔
      q.f ≫ x.structureMap = q.f ≫ y.structureMap :=
  ⟨fun ⟨e, _⟩ => structureMap_eq_of_iso x y q.f e, fun h => (IsomPoint.ofPoint q h).exists_iso⟩

end IsomSheaf

/-! ### Representability of the isomorphism sheaf -/

section Representation

variable {G : AlgebraicSpaceGroup.{u}} {S T : Scheme.{u}} [S.IsSeparated]
  (x y : ActionTorsor G (AlgebraicSpaceAction.trivial G (AlgebraicSpace.ofScheme.obj S)) T)
  (RP : TorsorRepresentation x.toFppfTorsor) (RQ : TorsorRepresentation y.toFppfTorsor)

/-- **Representability of `Isom_{[S/G]}(x, y)` from representability of `Isom_{BG}(x̄, ȳ)`**
(blueprint B1.3): if the isomorphism sheaf of the underlying `BG`-objects is represented by
`w : W ⟶ T`, then the isomorphism sheaf of `x` and `y` in `[S/G]` is represented by the
equaliser `W' ⟶ W` of `w ≫ x.structureMap` and `w ≫ y.structureMap`, a closed immersion since
`S` is separated. -/
theorem exists_isomRepresentation_of_point {W : Scheme.{u}} (w : W ⟶ T)
    (e : fppfYoneda.obj W ≅ isomSheaf (toPointObj x) (toPointObj y) RP RQ)
    (he : e.hom ≫ isomProjection (toPointObj x) (toPointObj y) RP RQ = fppfYoneda.map w) :
    ∃ (W' : Scheme.{u}) (w' : W' ⟶ T) (e' : fppfYoneda.obj W' ≅ isomSheaf x y RP RQ),
      e'.hom ≫ isomProjection x y RP RQ = fppfYoneda.map w' ∧
        ∃ ι : W' ⟶ W, IsClosedImmersion ι ∧ ι ≫ w = w' := by
  let W' : Scheme.{u} := equalizer (w ≫ x.structureMap) (w ≫ y.structureMap)
  let ι : W' ⟶ W := equalizer.ι _ _
  have hcond : (fppfYoneda.map ι ≫ e.hom) ≫
      isomProjection (toPointObj x) (toPointObj y) RP RQ ≫ fppfYoneda.map x.structureMap =
      (fppfYoneda.map ι ≫ e.hom) ≫
        isomProjection (toPointObj x) (toPointObj y) RP RQ ≫ fppfYoneda.map y.structureMap := by
    rw [Category.assoc, Category.assoc, reassoc_of% he, reassoc_of% he, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg fppfYoneda.map (equalizer.condition _ _)
  let φ : fppfYoneda.obj W' ⟶
      equalizer (isomProjection (toPointObj x) (toPointObj y) RP RQ ≫
          fppfYoneda.map x.structureMap)
        (isomProjection (toPointObj x) (toPointObj y) RP RQ ≫ fppfYoneda.map y.structureMap) :=
    equalizer.lift (fppfYoneda.map ι ≫ e.hom) hcond
  have hφι : φ ≫ equalizer.ι _ _ = fppfYoneda.map ι ≫ e.hom := equalizer.lift_ι _ _
  have : IsIso φ := by
    refine fppfSheaf_isIso_of_bijective _ fun Z => ⟨?_, ?_⟩
    · intro α β h
      obtain ⟨a, rfl⟩ := fppfYoneda.map_surjective α
      obtain ⟨b, rfl⟩ := fppfYoneda.map_surjective β
      have h' := congrArg (· ≫ equalizer.ι _ _) h
      simp only [Category.assoc, hφι] at h'
      rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Functor.map_comp,
        ← Functor.map_comp] at h'
      have h'' := fppfYoneda.map_injective h'
      rw [cancel_mono] at h''
      rw [h'']
    · intro β
      obtain ⟨z₀, hz₀⟩ := fppfYoneda.map_surjective (β ≫ equalizer.ι _ _ ≫ e.inv)
      have hz₀cond : z₀ ≫ w ≫ x.structureMap = z₀ ≫ w ≫ y.structureMap := by
        apply fppfYoneda.map_injective
        simp only [Functor.map_comp, hz₀, ← he, Category.assoc, Iso.inv_hom_id_assoc]
        exact β ≫= equalizer.condition _ _
      refine ⟨fppfYoneda.map (equalizer.lift z₀ hz₀cond), ?_⟩
      apply (cancel_mono (equalizer.ι _ _)).1
      change (_ ≫ φ) ≫ _ = _
      rw [Category.assoc, hφι, ← Category.assoc, ← Functor.map_comp, equalizer.lift_ι, hz₀]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨W', ι ≫ w, asIso φ ≪≫ (isomSheafIsoEqualizer x y RP RQ).symm, ?_, ι, inferInstance, rfl⟩
  rw [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc, ← forgetToPoint_isomProjection,
    ← isomSheafIsoEqualizer_hom_ι]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hφι, Category.assoc, he, ← Functor.map_comp]

omit [S.IsSeparated] in
/-- **`Isom_{[S/G]}(x, y)` is represented by `W` when the structure maps agree on `W`**: if
`Isom_{BG}(x̄, ȳ)` is represented by `w : W ⟶ T` and `w ≫ x.structureMap = w ≫ y.structureMap`,
then `W` also represents `Isom_{[S/G]}(x, y)`, compatibly with the structure maps
(`isomSheafIsoOfPoint_hom_isomProjection`) and with `forgetToPoint`
(`isomSheafIsoOfPoint_hom_forgetToPoint`). -/
noncomputable def isomSheafIsoOfPoint {W : Scheme.{u}} (w : W ⟶ T)
    (e : fppfYoneda.obj W ≅ isomSheaf (toPointObj x) (toPointObj y) RP RQ)
    (he : e.hom ≫ isomProjection (toPointObj x) (toPointObj y) RP RQ = fppfYoneda.map w)
    (hw : w ≫ x.structureMap = w ≫ y.structureMap) :
    fppfYoneda.obj W ≅ isomSheaf x y RP RQ where
  hom := equalizer.lift e.hom (by
      rw [← Category.assoc, ← Category.assoc, he, ← Functor.map_comp, ← Functor.map_comp, hw]) ≫
    (isomSheafIsoEqualizer x y RP RQ).inv
  inv := (isomSheafIsoEqualizer x y RP RQ).hom ≫ equalizer.ι _ _ ≫ e.inv
  hom_inv_id := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, equalizer.lift_ι_assoc, Iso.hom_inv_id]
  inv_hom_id := by
    have key : equalizer.ι (isomProjection (toPointObj x) (toPointObj y) RP RQ ≫
          fppfYoneda.map x.structureMap)
        (isomProjection (toPointObj x) (toPointObj y) RP RQ ≫ fppfYoneda.map y.structureMap) ≫
          e.inv ≫ equalizer.lift e.hom (by
            rw [← Category.assoc, ← Category.assoc, he, ← Functor.map_comp, ← Functor.map_comp,
              hw]) = 𝟙 _ := by
      apply (cancel_mono (equalizer.ι _ _)).1
      simp only [Category.assoc, equalizer.lift_ι, Iso.inv_hom_id, Category.comp_id,
        Category.id_comp]
    simp only [Category.assoc]
    rw [reassoc_of% key, Iso.hom_inv_id]

omit [S.IsSeparated] in
/-- `isomSheafIsoOfPoint` lies over `T`. -/
@[reassoc (attr := simp)]
theorem isomSheafIsoOfPoint_hom_isomProjection {W : Scheme.{u}} (w : W ⟶ T)
    (e : fppfYoneda.obj W ≅ isomSheaf (toPointObj x) (toPointObj y) RP RQ)
    (he : e.hom ≫ isomProjection (toPointObj x) (toPointObj y) RP RQ = fppfYoneda.map w)
    (hw : w ≫ x.structureMap = w ≫ y.structureMap) :
    (isomSheafIsoOfPoint x y RP RQ w e he hw).hom ≫ isomProjection x y RP RQ =
      fppfYoneda.map w := by
  rw [isomSheafIsoOfPoint, ← forgetToPoint_isomProjection, ← isomSheafIsoEqualizer_hom_ι]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, equalizer.lift_ι_assoc, he]

omit [S.IsSeparated] in
/-- `isomSheafIsoOfPoint` is compatible with the given representation of `Isom_{BG}(x̄, ȳ)`. -/
@[reassoc (attr := simp)]
theorem isomSheafIsoOfPoint_hom_forgetToPoint {W : Scheme.{u}} (w : W ⟶ T)
    (e : fppfYoneda.obj W ≅ isomSheaf (toPointObj x) (toPointObj y) RP RQ)
    (he : e.hom ≫ isomProjection (toPointObj x) (toPointObj y) RP RQ = fppfYoneda.map w)
    (hw : w ≫ x.structureMap = w ≫ y.structureMap) :
    (isomSheafIsoOfPoint x y RP RQ w e he hw).hom ≫ forgetToPoint x y RP RQ = e.hom := by
  rw [isomSheafIsoOfPoint, ← isomSheafIsoEqualizer_hom_ι]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, equalizer.lift_ι]

end Representation

/-! ### `[S/G]` as a Deligne–Mumford stack -/

section DeligneMumford

variable {R : Type u} [CommRing R] (grp : GrpObj (fppfYoneda.obj (Spec (CommRingCat.of R))))
  [Algebra.Etale ℤ R] [Module.Finite ℤ R]
  (hR : _root_.AlgebraicGeometry.Surjective
    (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
      (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)))))
  (S : Scheme.{u}) [S.IsSeparated]

/-- **Representability of the isomorphism sheaf of `[S/G]`** (blueprint B1.3): for
`G = affineGroup R grp` with `R` finite étale over `ℤ` and `Spec R → Spec ℤ` surjective, and
`S` a separated scheme with the trivial `G`-action, the isomorphism sheaf of two objects `x y`
of `[S/G]` over `T` with represented torsors is represented by a scheme finite over `T`. -/
theorem exists_isomRepresentation_trivial {T : Scheme.{u}}
    (x y : ActionTorsor (affineGroup R grp)
      (AlgebraicSpaceAction.trivial (affineGroup R grp) (AlgebraicSpace.ofScheme.obj S)) T)
    (RP : TorsorRepresentation x.toFppfTorsor) (RQ : TorsorRepresentation y.toFppfTorsor) :
    ∃ (W' : Scheme.{u}) (w' : W' ⟶ T) (e' : fppfYoneda.obj W' ≅ isomSheaf x y RP RQ),
      e'.hom ≫ isomProjection x y RP RQ = fppfYoneda.map w' ∧ IsFinite w' := by
  obtain ⟨W, w, e, he, -, hfin⟩ := exists_isomRepresentation (toPointObj x) (toPointObj y) RP RQ
  obtain ⟨W', w', e', he', ι, hι, rfl⟩ := exists_isomRepresentation_of_point x y RP RQ w e he
  exact ⟨W', ι ≫ w, e', he', inferInstance⟩

include hR in
/-- **The diagonal of `[S/G]` is representable** (blueprint B1.4) for `G = affineGroup R grp`
with `R` finite étale over `ℤ` and `Spec R → Spec ℤ` surjective, acting trivially on a separated
scheme `S`. -/
theorem hasRepresentableDiagonal_quotientStack_trivial :
    HasRepresentableDiagonal (quotientStack (affineGroup R grp)
      (AlgebraicSpaceAction.trivial (affineGroup R grp) (AlgebraicSpace.ofScheme.obj S))) := by
  refine hasRepresentableDiagonal_quotientStack_of_isomRepresentation _ _ fun T x y => ?_
  obtain ⟨RP, -⟩ := FppfTorsor.exists_torsorRepresentation_affineGroup_of_int hR x.toFppfTorsor
  obtain ⟨RQ, -⟩ := FppfTorsor.exists_torsorRepresentation_affineGroup_of_int hR y.toFppfTorsor
  obtain ⟨W, w, e, he, -⟩ := exists_isomRepresentation_trivial grp S x y RP RQ
  exact ⟨RP, RQ, W, w, e, he⟩

omit [S.IsSeparated] in
include hR in
/-- The atlas chart `S → [S/G]` of the quotient of the trivial action is étale surjective. -/
theorem atlasChart_trivial_isEtaleSurjective :
    (atlasChart (affineGroup R grp)
      (AlgebraicSpaceAction.trivial (affineGroup R grp) (AlgebraicSpace.ofScheme.obj S)) S
        rfl).IsEtaleSurjective :=
  atlasChart_affineGroup_isEtaleSurjective_of_int hR _ S rfl

/-- **`[S/G]` as an algebraic stack** for a trivial action on a separated scheme `S`
(`G = affineGroup R grp`, `R` finite étale over `ℤ`, `Spec R → Spec ℤ` surjective): the diagonal
is representable and the atlas `S → [S/G]` is étale surjective, hence smooth surjective. -/
noncomputable def trivialQuotientAlgebraicStack : AlgebraicStack.{u} where
  toStack := quotientStack (affineGroup R grp)
    (AlgebraicSpaceAction.trivial (affineGroup R grp) (AlgebraicSpace.ofScheme.obj S))
  diagonal_representable := hasRepresentableDiagonal_quotientStack_trivial grp hR S
  smoothAtlas := ⟨_, (atlasChart _ _ S rfl).isSmoothSurjective_of_isEtaleSurjective
    (atlasChart_trivial_isEtaleSurjective grp hR S)⟩

/-- The underlying stack of `trivialQuotientAlgebraicStack` is `[S/G]`. -/
@[simp]
theorem trivialQuotientAlgebraicStack_toStack :
    (trivialQuotientAlgebraicStack grp hR S).toStack = quotientStack (affineGroup R grp)
      (AlgebraicSpaceAction.trivial (affineGroup R grp) (AlgebraicSpace.ofScheme.obj S)) :=
  rfl

/-- **`[S/G]` as a Deligne–Mumford stack** for a trivial action on a separated scheme `S`
(`G = affineGroup R grp`, `R` finite étale over `ℤ`, `Spec R → Spec ℤ` surjective), with the
étale surjective atlas `S → [S/G]`. -/
noncomputable def trivialQuotientDeligneMumfordStack : DeligneMumfordStack.{u} where
  toAlgebraicStack := trivialQuotientAlgebraicStack grp hR S
  etaleAtlas := ⟨_, atlasChart_trivial_isEtaleSurjective grp hR S⟩

/-- The underlying stack of `trivialQuotientDeligneMumfordStack` is `[S/G]`. -/
@[simp]
theorem trivialQuotientDeligneMumfordStack_toStack :
    (trivialQuotientDeligneMumfordStack grp hR S).toStack = quotientStack (affineGroup R grp)
      (AlgebraicSpaceAction.trivial (affineGroup R grp) (AlgebraicSpace.ofScheme.obj S)) :=
  rfl

end DeligneMumford

end ActionTorsor

/-! ### The Deligne–Mumford stack `[Spec k / Γ]` -/

section Constant

variable (k : Type u) [Field k] (Γ : Type u) [Group Γ] [Finite Γ] [DecidableEq Γ]

/-- **The diagonal of `[Spec k / Γ]` is representable** for a finite group `Γ` acting trivially
on `Spec k`. -/
theorem hasRepresentableDiagonal_constantQuotientStack :
    HasRepresentableDiagonal
      (ActionTorsor.quotientStack (constantGroup Γ) (constantTrivialAction k Γ)) :=
  ActionTorsor.hasRepresentableDiagonal_quotientStack_trivial (constantGrpObj Γ)
    (surjective_constant Γ) (Spec (CommRingCat.of k))

/-- **`[Spec k / Γ]` as a Deligne–Mumford stack**: the quotient stack of the trivial action
`constantTrivialAction k Γ` of the constant finite group `constantGroup Γ` on `Spec k`, with
representable diagonal and the étale surjective atlas `constantAtlasChart k Γ`
(`Spec k → [Spec k / Γ]`, scheme `Spec k`). -/
noncomputable def constantQuotientDeligneMumfordStack : DeligneMumfordStack.{u} where
  toStack := ActionTorsor.quotientStack (constantGroup Γ) (constantTrivialAction k Γ)
  diagonal_representable := hasRepresentableDiagonal_constantQuotientStack k Γ
  smoothAtlas := ⟨constantAtlasChart k Γ,
    (constantAtlasChart k Γ).isSmoothSurjective_of_isEtaleSurjective
      (constantAtlasChart_isEtaleSurjective k Γ)⟩
  etaleAtlas := ⟨constantAtlasChart k Γ, constantAtlasChart_isEtaleSurjective k Γ⟩

/-- The underlying stack of `constantQuotientDeligneMumfordStack k Γ` is `[Spec k / Γ]`. -/
@[simp]
theorem constantQuotientDeligneMumfordStack_toStack :
    (constantQuotientDeligneMumfordStack k Γ).toStack =
      ActionTorsor.quotientStack (constantGroup Γ) (constantTrivialAction k Γ) :=
  rfl

/-- `constantQuotientDeligneMumfordStack k Γ` is the general construction
`trivialQuotientDeligneMumfordStack` for `G = constantGroup Γ` and `S = Spec k`. -/
theorem constantQuotientDeligneMumfordStack_eq :
    constantQuotientDeligneMumfordStack k Γ =
      ActionTorsor.trivialQuotientDeligneMumfordStack (constantGrpObj Γ) (surjective_constant Γ)
        (Spec (CommRingCat.of k)) :=
  rfl

end Constant

end GromovWitten.AlgebraicGeometry
