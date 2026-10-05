/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Stacks.TorsorRepresentable
import GromovWitten.AlgebraicGeometry.Stacks.TorsorStackDescent

/-!
# The isomorphism sheaf of two torsors

Let `G` be a group algebraic space acting on `U`, let `x y : ActionTorsor G U T` be two objects
of the quotient stack `[U/G]` over a scheme `T`, and suppose both underlying torsors are
represented by schemes (`RP : TorsorRepresentation x.toFppfTorsor`,
`RQ : TorsorRepresentation y.toFppfTorsor`).  This file constructs the fppf sheaf
`Isom(x, y) → T` whose `S`-points over `f : S ⟶ T` are the isomorphisms
`f^* x ≅ f^* y` in the fibre `[U/G](S)`.

The hom-set `f^* x ⟶ f^* y` lives one universe too high to be a value of a `Type u`-valued
presheaf.  The representations make it small: an isomorphism `f^* x ≅ f^* y` is determined by
(and, when it exists, is the Yoneda transport of) a morphism of schemes
`S ×_T RP.space ⟶ S ×_T RQ.space` over `S` (`ActionTorsor.IsomPoint`).  The `Prop`-valued
field `exists_iso` records that the scheme morphism does come from an isomorphism of torsors
(equivariance, compatibility with the maps to `U`), so no separate theory of "equivariant maps
of torsors are isomorphisms" is needed.

The sheaf property is deduced from the descent of morphisms for `[U/G]`
(`ActionTorsor.existsUnique_hom_of_torsorHomFamily`, `Stacks/TorsorStackDescent.lean`), through
the naturality of the bijection `IsomPoint ≃ Σ f, (f^* x ≅ f^* y)` with respect to the
pseudofunctorial pullback `stackPullbackIso` (`ActionTorsor.isomPointEquiv_restrict`).

## Main results

* `ActionTorsor.repPullbackIso RP f`: the identification
  `fppfYoneda.obj (S ×_T RP.space) ≅ pullbackSheaf P f` of the base change of a represented
  torsor (fppf-Yoneda preserves fibre products), and `TorsorRepresentation.pullbackRep`, the
  induced representation of the base-changed torsor.
* `ActionTorsor.IsomPoint x y RP RQ S : Type u`: the small type of `S`-points of the isomorphism
  sheaf; `ActionTorsor.IsomPoint.iso`, the attached isomorphism `f^* x ≅ f^* y`, and
  `ActionTorsor.IsomPoint.ofIso`, its inverse.
* `ActionTorsor.isomPointEquiv x y RP RQ S : IsomPoint x y RP RQ S ≃
    Σ f : S ⟶ T, ((stackPullback [U/G] f).obj x ≅ (stackPullback [U/G] f).obj y)`.
* `ActionTorsor.isomPresheaf x y RP RQ : Scheme.{u}ᵒᵖ ⥤ Type u`, with
  `ActionTorsor.isomPointEquiv_restrict`: naturality of the bijection in `S`, in terms of
  `stackPullbackIso` (the form consumed by `DiagonalClassifies`).
* `ActionTorsor.toStackIso`/`ActionTorsor.ofStackIso`: the (definitional) identification of
  isomorphisms `pullbackObj f x ≅ pullbackObj f y` with isomorphisms in the stack fibre, and
  `ActionTorsor.stackPullbackIso_toStackIso_hom_iso_hom`, the computation of the underlying
  sheaf map of `stackPullbackIso [U/G] g f e`.
* `ActionTorsor.IsomPoint.ext_of_sieve`: the isomorphism presheaf is separated for fppf
  covering sieves; `ActionTorsor.isSheaf_isomPresheaf`: it is an fppf sheaf (via the descent
  datum `ActionTorsor.isomDescentFamily` and `existsUnique_hom_of_torsorHomFamily`).
* `ActionTorsor.isomSheaf x y RP RQ : FppfSheaf`, the isomorphism sheaf, with its structure map
  `ActionTorsor.isomProjection x y RP RQ : isomSheaf x y RP RQ ⟶ fppfYoneda.obj T`
  (`ActionTorsor.comp_isomProjection`: on a representable, it reads off the test map).
* Base change (blueprint D2a.4): for `b : S ⟶ T`, `ActionTorsor.IsomPoint.pushBase`,
  `ActionTorsor.IsomPoint.pullBase`, the sheaf map `ActionTorsor.isomPushBase` over `b`, and
  `ActionTorsor.isomBaseChangeIso :
    isomSheaf (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) ≅
      pullback (isomProjection x y RP RQ) (fppfYoneda.map b)`
  with `ActionTorsor.isomBaseChangeIso_hom_snd` (it lies over `S`).

No hypothesis on `G` or `U` is needed: the affineness of `G` only enters the representability
of `Isom(x, y)` (not proved here).
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

/-- The first projection of `pullback.map`; `simp` does not see through the abbreviation. -/
@[reassoc (attr := simp)]
theorem pullback_map_comp_fst {C : Type*} [Category C] {W X Y Z S T : C} (f₁ : W ⟶ S)
    (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂]
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂ ≫ pullback.fst g₁ g₂ = pullback.fst f₁ f₂ ≫ i₁ :=
  pullback.lift_fst _ _ _

/-- The second projection of `pullback.map`. -/
@[reassoc (attr := simp)]
theorem pullback_map_comp_snd {C : Type*} [Category C] {W X Y Z S T : C} (f₁ : W ⟶ S)
    (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂]
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂ ≫ pullback.snd g₁ g₂ = pullback.snd f₁ f₂ ≫ i₂ :=
  pullback.lift_snd _ _ _

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T : Scheme.{u}}

/-! ### Isomorphisms in the stack fibre versus isomorphisms of base-changed torsors -/

/-- The inverse of the composition comparison of base change in `[U/G]` is
`ActionTorsor.pullbackCompIsoApp`.  This is `rfl`. -/
theorem stackPullbackCompIso_quotientStack_inv {S S' : Scheme.{u}} (m : S' ⟶ S)
    (b : S ⟶ T) (P : ActionTorsor G U T) :
    (stackPullbackCompIso (quotientStack G U) m b P).inv = (pullbackCompIsoApp m b P).hom :=
  rfl

/-- Pullback of arrows in the stack `[U/G]` is `ActionTorsor.pullbackFunctor`.  This is `rfl`. -/
theorem stackPullback_map_quotientStack {S S' : Scheme.{u}} (m : S' ⟶ S)
    {P Q : ActionTorsor G U S} (φ : P ⟶ Q) :
    (stackPullback (quotientStack G U) m).map φ = (pullbackFunctor m).map φ :=
  rfl

/-- An isomorphism of base-changed torsors, regarded as an isomorphism in the fibre of the
quotient stack.  The two types are definitionally equal; this definition only fixes the
elaboration. -/
def toStackIso (x y : ActionTorsor G U T) {S : Scheme.{u}} {f : S ⟶ T}
    (e : pullbackObj f x ≅ pullbackObj f y) :
    (stackPullback (quotientStack G U) f).obj x ≅ (stackPullback (quotientStack G U) f).obj y :=
  e

/-- An isomorphism in the fibre of the quotient stack, regarded as an isomorphism of
base-changed torsors. -/
def ofStackIso (x y : ActionTorsor G U T) {S : Scheme.{u}} {f : S ⟶ T}
    (e : (stackPullback (quotientStack G U) f).obj x ≅
      (stackPullback (quotientStack G U) f).obj y) :
    pullbackObj f x ≅ pullbackObj f y :=
  e

/-- `toStackIso` and `ofStackIso` are inverse (definitionally). -/
@[simp]
theorem toStackIso_ofStackIso (x y : ActionTorsor G U T) {S : Scheme.{u}} {f : S ⟶ T}
    (e : (stackPullback (quotientStack G U) f).obj x ≅
      (stackPullback (quotientStack G U) f).obj y) :
    toStackIso x y (ofStackIso x y e) = e :=
  rfl

/-- `ofStackIso` and `toStackIso` are inverse (definitionally). -/
@[simp]
theorem ofStackIso_toStackIso (x y : ActionTorsor G U T) {S : Scheme.{u}} {f : S ⟶ T}
    (e : pullbackObj f x ≅ pullbackObj f y) :
    ofStackIso x y (toStackIso x y e) = e :=
  rfl

/-- The underlying sheaf map of `toStackIso x y e` is that of `e`. -/
@[simp]
theorem toStackIso_hom_iso_hom (x y : ActionTorsor G U T) {S : Scheme.{u}} {f : S ⟶ T}
    (e : pullbackObj f x ≅ pullbackObj f y) :
    (toStackIso x y e).hom.iso.hom = e.hom.iso.hom :=
  rfl

/-- The underlying sheaf map of `ofStackIso x y e` is that of `e`. -/
@[simp]
theorem ofStackIso_hom_iso_hom (x y : ActionTorsor G U T) {S : Scheme.{u}} {f : S ⟶ T}
    (e : (stackPullback (quotientStack G U) f).obj x ≅
      (stackPullback (quotientStack G U) f).obj y) :
    (ofStackIso x y e).hom.iso.hom = e.hom.iso.hom :=
  rfl

/-- **The underlying sheaf map of a pulled-back isomorphism in `[U/G]`.**  The pseudofunctorial
pullback `stackPullbackIso` of an isomorphism `e : f^* x ≅ f^* y` along `g` is the base change
`FppfTorsor.pullbackMap g` of its underlying sheaf map, conjugated by the composition
comparisons `FppfTorsor.pullbackCompIso`. -/
theorem stackPullbackIso_toStackIso_hom_iso_hom (x y : ActionTorsor G U T) {S S' : Scheme.{u}}
    (f : S ⟶ T) (g : S' ⟶ S) (e : pullbackObj f x ≅ pullbackObj f y) :
    (stackPullbackIso (quotientStack G U) g f (toStackIso x y e)).hom.iso.hom =
      (FppfTorsor.pullbackCompIso x.toFppfTorsor g f).hom ≫
        FppfTorsor.pullbackMap g e.hom.iso.hom e.hom.over ≫
          (FppfTorsor.pullbackCompIso y.toFppfTorsor g f).inv := by
  change (((pullbackCompIsoApp g f x).hom ≫ (pullbackFunctor g).map e.hom) ≫
    (pullbackCompIsoApp g f y).inv).iso.hom = _
  rw [comp_iso_hom, comp_iso_hom, pullbackCompIsoApp_hom_iso_hom,
    pullbackCompIsoApp_inv_iso_hom, pullbackFunctor_map_iso_hom, Category.assoc]

/-! ### Base change of a represented torsor -/

section RepPullback

variable {P : FppfTorsor G T} (RP : TorsorRepresentation P) {S : Scheme.{u}} (f : S ⟶ T)

/-- The comparison map from the fppf-Yoneda sheaf of the scheme fibre product `S ×_T RP.space`
to the sheaf base change `pullbackSheaf P f`. -/
noncomputable def repPullbackHom :
    fppfYoneda.obj (pullback RP.toBase f) ⟶ FppfTorsor.pullbackSheaf P f :=
  pullback.lift (fppfYoneda.map (pullback.fst RP.toBase f) ≫ RP.iso.hom)
    (fppfYoneda.map (pullback.snd RP.toBase f))
    (by rw [Category.assoc, RP.iso_hom_projection, ← fppfYoneda.map_comp,
      ← fppfYoneda.map_comp, pullback.condition])

/-- The first projection of the comparison map. -/
@[reassoc (attr := simp)]
theorem repPullbackHom_fst :
    repPullbackHom RP f ≫ pullback.fst P.projection (fppfYoneda.map f) =
      fppfYoneda.map (pullback.fst RP.toBase f) ≫ RP.iso.hom :=
  pullback.lift_fst _ _ _

/-- The second projection of the comparison map. -/
@[reassoc (attr := simp)]
theorem repPullbackHom_snd :
    repPullbackHom RP f ≫ pullback.snd P.projection (fppfYoneda.map f) =
      fppfYoneda.map (pullback.snd RP.toBase f) :=
  pullback.lift_snd _ _ _

/-- The comparison map is the pullback comparison of `fppfYoneda` followed by the
identification of the first factor. -/
theorem repPullbackHom_eq :
    repPullbackHom RP f =
      (PreservesPullback.iso fppfYoneda RP.toBase f).hom ≫
        pullback.map (fppfYoneda.map RP.toBase) (fppfYoneda.map f) P.projection
          (fppfYoneda.map f) RP.iso.hom (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, RP.iso_hom_projection]) (by simp) := by
  apply pullback.hom_ext
  · simp [PreservesPullback.iso_hom]
  · simp [PreservesPullback.iso_hom]

/-- `fppfYoneda` preserves fibre products, so the comparison map is an isomorphism. -/
instance isIso_repPullbackHom : IsIso (repPullbackHom RP f) := by
  rw [repPullbackHom_eq]
  infer_instance

/-- The identification of the fppf-Yoneda sheaf of `S ×_T RP.space` with the base change of a
represented torsor along `f : S ⟶ T`. -/
noncomputable def repPullbackIso :
    fppfYoneda.obj (pullback RP.toBase f) ≅ FppfTorsor.pullbackSheaf P f :=
  asIso (repPullbackHom RP f)

/-- The comparison isomorphism is `repPullbackHom`. -/
@[simp]
theorem repPullbackIso_hom : (repPullbackIso RP f).hom = repPullbackHom RP f :=
  rfl

/-- The base change of a representation: the base-changed torsor is represented by the scheme
fibre product.  This is an abbreviation so that its projections unfold in rewrites. -/
noncomputable abbrev _root_.GromovWitten.AlgebraicGeometry.TorsorRepresentation.pullbackRep :
    TorsorRepresentation (P.pullbackTorsor f) where
  space := pullback RP.toBase f
  toBase := pullback.snd RP.toBase f
  iso := repPullbackIso RP f
  iso_hom_projection := repPullbackHom_snd RP f

/-- The representing scheme of the base-changed representation. -/
@[simp]
theorem _root_.GromovWitten.AlgebraicGeometry.TorsorRepresentation.pullbackRep_space :
    (RP.pullbackRep f).space = pullback RP.toBase f :=
  rfl

/-- The structure map of the base-changed representation. -/
@[simp]
theorem _root_.GromovWitten.AlgebraicGeometry.TorsorRepresentation.pullbackRep_toBase :
    (RP.pullbackRep f).toBase = pullback.snd RP.toBase f :=
  rfl

/-- The identification of the base-changed representation is the comparison map. -/
@[simp]
theorem _root_.GromovWitten.AlgebraicGeometry.TorsorRepresentation.pullbackRep_iso_hom :
    (RP.pullbackRep f).iso.hom = repPullbackHom RP f :=
  rfl

/-- The transition morphism `S' ×_T RP.space ⟶ S ×_T RP.space` attached to `g : S' ⟶ S`. -/
noncomputable def repBaseChange {S' : Scheme.{u}} (g : S' ⟶ S) :
    pullback RP.toBase (g ≫ f) ⟶ pullback RP.toBase f :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g)
    (by rw [pullback.condition, Category.assoc])

/-- The transition morphism commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem repBaseChange_fst {S' : Scheme.{u}} (g : S' ⟶ S) :
    repBaseChange RP f g ≫ pullback.fst RP.toBase f = pullback.fst RP.toBase (g ≫ f) :=
  pullback.lift_fst _ _ _

/-- The transition morphism lies over `g`. -/
@[reassoc (attr := simp)]
theorem repBaseChange_snd {S' : Scheme.{u}} (g : S' ⟶ S) :
    repBaseChange RP f g ≫ pullback.snd RP.toBase f = pullback.snd RP.toBase (g ≫ f) ≫ g :=
  pullback.lift_snd _ _ _

/-- The transition morphism along an identity is the canonical identification of fibre
products. -/
@[simp]
theorem repBaseChange_id :
    repBaseChange RP f (𝟙 S) = (pullback.congrHom rfl (Category.id_comp f)).hom := by
  apply pullback.hom_ext <;> simp

/-- The transition morphism along a composite is the composite of the transition morphisms,
up to the canonical identification of fibre products. -/
@[reassoc (attr := simp)]
theorem repBaseChange_comp {S' S'' : Scheme.{u}} (g : S' ⟶ S) (g' : S'' ⟶ S') :
    pullback.map RP.toBase (g' ≫ g ≫ f) RP.toBase ((g' ≫ g) ≫ f) (𝟙 _) (𝟙 _) (𝟙 _)
        (by simp) (by simp) ≫ repBaseChange RP f (g' ≫ g) =
      repBaseChange RP (g ≫ f) g' ≫ repBaseChange RP f g := by
  apply pullback.hom_ext <;> simp

/-- The comparison map for `g ≫ f` followed by the composition comparison and the projection
to the base change along `f` is the transition morphism followed by the comparison map for
`f`. -/
@[reassoc (attr := simp)]
theorem repPullbackHom_comp_pullbackCompIso_hom_fst {S' : Scheme.{u}} (g : S' ⟶ S) :
    repPullbackHom RP (g ≫ f) ≫ (FppfTorsor.pullbackCompIso P g f).hom ≫
        pullback.fst (pullback.snd P.projection (fppfYoneda.map f)) (fppfYoneda.map g) =
      fppfYoneda.map (repBaseChange RP f g) ≫ repPullbackHom RP f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, FppfTorsor.pullbackCompIso_hom_fst_fst, repPullbackHom_fst,
      ← fppfYoneda.map_comp_assoc, repBaseChange_fst]
  · simp only [Category.assoc, FppfTorsor.pullbackCompIso_hom_fst_snd, repPullbackHom_snd_assoc,
      repPullbackHom_snd, ← fppfYoneda.map_comp, repBaseChange_snd]

/-- The comparison maps are compatible with the composition comparison of sheaf base change:
after the pasting isomorphism of scheme fibre products, the comparison for `g ≫ f` is the
comparison for `g` of the base-changed representation. -/
theorem repPullbackHom_comp_pullbackCompIso_hom {S' : Scheme.{u}} (g : S' ⟶ S) :
    repPullbackHom RP (g ≫ f) ≫ (FppfTorsor.pullbackCompIso P g f).hom =
      fppfYoneda.map (pullbackLeftPullbackSndIso RP.toBase f g).inv ≫
        repPullbackHom (RP.pullbackRep f) g := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [FppfTorsor.pullbackCompIso_hom_fst_fst, repPullbackHom_fst RP (g ≫ f),
        repPullbackHom_fst_assoc (RP.pullbackRep f) g, TorsorRepresentation.pullbackRep_iso_hom,
        repPullbackHom_fst RP f, ← fppfYoneda.map_comp_assoc, ← fppfYoneda.map_comp_assoc,
        Category.assoc]
      exact congrArg (fun k => fppfYoneda.map k ≫ RP.iso.hom)
        (pullbackLeftPullbackSndIso_inv_fst RP.toBase f g).symm
    · simp only [Category.assoc]
      rw [FppfTorsor.pullbackCompIso_hom_fst_snd, repPullbackHom_snd_assoc RP (g ≫ f),
        repPullbackHom_fst_assoc (RP.pullbackRep f) g, TorsorRepresentation.pullbackRep_iso_hom,
        repPullbackHom_snd RP f, ← fppfYoneda.map_comp, ← fppfYoneda.map_comp]
      exact congrArg fppfYoneda.map (pullbackLeftPullbackSndIso_inv_fst_snd RP.toBase f g).symm
  · simp only [Category.assoc]
    rw [FppfTorsor.pullbackCompIso_hom_snd, repPullbackHom_snd RP (g ≫ f),
      repPullbackHom_snd (RP.pullbackRep f) g, ← fppfYoneda.map_comp]
    exact congrArg fppfYoneda.map (pullbackLeftPullbackSndIso_inv_snd_snd RP.toBase f g).symm

/-! #### Restriction of morphisms of representing schemes -/

section Restrict

variable {Q : FppfTorsor G T} (RQ : TorsorRepresentation Q) {S' : Scheme.{u}} (g : S' ⟶ S)

/-- The restriction along `g : S' ⟶ S` of a morphism of representing schemes over `S`. -/
noncomputable def restrictHom (h : pullback RP.toBase f ⟶ pullback RQ.toBase f)
    (hsnd : h ≫ pullback.snd RQ.toBase f = pullback.snd RP.toBase f) :
    pullback RP.toBase (g ≫ f) ⟶ pullback RQ.toBase (g ≫ f) :=
  pullback.lift (repBaseChange RP f g ≫ h ≫ pullback.fst RQ.toBase f) (pullback.snd _ _) (by
    rw [Category.assoc, Category.assoc, pullback.condition (f := RQ.toBase) (g := f),
      ← Category.assoc h, hsnd, repBaseChange_snd_assoc])

/-- The first projection of the restricted morphism. -/
@[reassoc (attr := simp)]
theorem restrictHom_fst (h : pullback RP.toBase f ⟶ pullback RQ.toBase f)
    (hsnd : h ≫ pullback.snd RQ.toBase f = pullback.snd RP.toBase f) :
    restrictHom RP f RQ g h hsnd ≫ pullback.fst RQ.toBase (g ≫ f) =
      repBaseChange RP f g ≫ h ≫ pullback.fst RQ.toBase f :=
  pullback.lift_fst _ _ _

/-- The restricted morphism lies over the test scheme. -/
@[reassoc (attr := simp)]
theorem restrictHom_snd (h : pullback RP.toBase f ⟶ pullback RQ.toBase f)
    (hsnd : h ≫ pullback.snd RQ.toBase f = pullback.snd RP.toBase f) :
    restrictHom RP f RQ g h hsnd ≫ pullback.snd RQ.toBase (g ≫ f) =
      pullback.snd RP.toBase (g ≫ f) :=
  pullback.lift_snd _ _ _

/-- The restricted morphism is compatible with the transition morphisms. -/
@[reassoc]
theorem restrictHom_comp_repBaseChange (h : pullback RP.toBase f ⟶ pullback RQ.toBase f)
    (hsnd : h ≫ pullback.snd RQ.toBase f = pullback.snd RP.toBase f) :
    restrictHom RP f RQ g h hsnd ≫ repBaseChange RQ f g = repBaseChange RP f g ≫ h := by
  apply pullback.hom_ext
  · simp
  · simp [hsnd]

/-- **The key computation**, for plain torsors: a sheaf map `h` between the base changes along
`f` which is the Yoneda transport of `hom`, once base changed along `g` and conjugated by the
composition comparisons, is the Yoneda transport of the restriction of `hom`. -/
theorem repPullbackHom_comp_pullbackMap_conj
    (h : FppfTorsor.pullbackSheaf P f ⟶ FppfTorsor.pullbackSheaf Q f)
    (hover : h ≫ pullback.snd Q.projection (fppfYoneda.map f) =
      pullback.snd P.projection (fppfYoneda.map f))
    (hom : pullback RP.toBase f ⟶ pullback RQ.toBase f)
    (hsnd : hom ≫ pullback.snd RQ.toBase f = pullback.snd RP.toBase f)
    (hcomp : repPullbackHom RP f ≫ h = fppfYoneda.map hom ≫ repPullbackHom RQ f) :
    repPullbackHom RP (g ≫ f) ≫ (FppfTorsor.pullbackCompIso P g f).hom ≫
        FppfTorsor.pullbackMap (P := P.pullbackTorsor f) (Q := Q.pullbackTorsor f) g h hover ≫
          (FppfTorsor.pullbackCompIso Q g f).inv =
      fppfYoneda.map (restrictHom RP f RQ g hom hsnd) ≫ repPullbackHom RQ (g ≫ f) := by
  -- The two projection identities of `pullbackMap`, stated with the projections unfolded (the
  -- `simp` lemmas do not fire through `(Q.pullbackTorsor f).projection`).
  have e₁ : FppfTorsor.pullbackMap (P := P.pullbackTorsor f) (Q := Q.pullbackTorsor f) g h
        hover ≫ pullback.fst (pullback.snd Q.projection (fppfYoneda.map f)) (fppfYoneda.map g) =
      pullback.fst (pullback.snd P.projection (fppfYoneda.map f)) (fppfYoneda.map g) ≫ h :=
    FppfTorsor.pullbackMap_fst (P := P.pullbackTorsor f) (Q := Q.pullbackTorsor f) g h hover
  have e₂ : FppfTorsor.pullbackMap (P := P.pullbackTorsor f) (Q := Q.pullbackTorsor f) g h
        hover ≫ pullback.snd (pullback.snd Q.projection (fppfYoneda.map f)) (fppfYoneda.map g) =
      pullback.snd (pullback.snd P.projection (fppfYoneda.map f)) (fppfYoneda.map g) :=
    FppfTorsor.pullbackMap_snd (P := P.pullbackTorsor f) (Q := Q.pullbackTorsor f) g h hover
  apply pullback.hom_ext
  · simp only [Category.assoc, FppfTorsor.pullbackCompIso_inv_fst, reassoc_of% e₁,
      repPullbackHom_comp_pullbackCompIso_hom_fst_assoc, reassoc_of% hcomp, repPullbackHom_fst,
      ← fppfYoneda.map_comp_assoc, restrictHom_fst]
  · simp only [Category.assoc, FppfTorsor.pullbackCompIso_inv_snd, e₂,
      FppfTorsor.pullbackCompIso_hom_snd, repPullbackHom_snd, ← fppfYoneda.map_comp,
      restrictHom_snd]

end Restrict

end RepPullback

/-! ### Points of the isomorphism sheaf -/

section IsomPoint

variable (x y : ActionTorsor G U T) (RP : TorsorRepresentation x.toFppfTorsor)
  (RQ : TorsorRepresentation y.toFppfTorsor)

/-- **A point of the isomorphism sheaf of `x` and `y` over `S`**: a test map `f : S ⟶ T` and a
morphism of schemes `S ×_T RP.space ⟶ S ×_T RQ.space` which is the Yoneda transport of an
isomorphism `f^* x ≅ f^* y` of base-changed torsors (hence lies over `S`, is equivariant and is
compatible with the maps to `U`).  The type is small; the isomorphism is recovered by
`IsomPoint.iso`. -/
structure IsomPoint (S : Scheme.{u}) : Type u where
  /-- The test map. -/
  f : S ⟶ T
  /-- The morphism of representing schemes. -/
  hom : pullback RP.toBase f ⟶ pullback RQ.toBase f
  /-- `hom` is the Yoneda transport of an isomorphism of base-changed torsors. -/
  exists_iso : ∃ e : pullbackObj f x ≅ pullbackObj f y,
    repPullbackHom RP f ≫ e.hom.iso.hom = fppfYoneda.map hom ≫ repPullbackHom RQ f

namespace IsomPoint

variable {x y RP RQ} {S : Scheme.{u}}

/-- An isomorphism of base-changed torsors is determined by the composite of its underlying
sheaf map with the comparison isomorphism. -/
theorem iso_ext {f : S ⟶ T} {e e' : pullbackObj f x ≅ pullbackObj f y}
    (h : repPullbackHom RP f ≫ e.hom.iso.hom = repPullbackHom RP f ≫ e'.hom.iso.hom) :
    e = e' :=
  Iso.ext (Hom.ext _ _ ((cancel_epi (repPullbackHom RP f)).1 h))

/-- The isomorphism of base-changed torsors attached to a point. -/
noncomputable def iso (p : IsomPoint x y RP RQ S) : pullbackObj p.f x ≅ pullbackObj p.f y :=
  p.exists_iso.choose

/-- The defining property of `IsomPoint.iso`. -/
@[reassoc]
theorem repPullbackHom_comp_iso_hom (p : IsomPoint x y RP RQ S) :
    repPullbackHom RP p.f ≫ p.iso.hom.iso.hom = fppfYoneda.map p.hom ≫ repPullbackHom RQ p.f :=
  p.exists_iso.choose_spec

/-- The isomorphism attached to a point is the unique one with the defining property. -/
theorem iso_eq (p : IsomPoint x y RP RQ S) (e : pullbackObj p.f x ≅ pullbackObj p.f y)
    (h : repPullbackHom RP p.f ≫ e.hom.iso.hom = fppfYoneda.map p.hom ≫ repPullbackHom RQ p.f) :
    p.iso = e :=
  iso_ext (p.repPullbackHom_comp_iso_hom.trans h.symm)

/-- The morphism of representing schemes of a point lies over the test scheme. -/
@[reassoc (attr := simp)]
theorem hom_snd (p : IsomPoint x y RP RQ S) :
    p.hom ≫ pullback.snd RQ.toBase p.f = pullback.snd RP.toBase p.f := by
  apply fppfYoneda.map_injective
  have h := congrArg (· ≫ pullback.snd y.projection (fppfYoneda.map p.f))
    p.repPullbackHom_comp_iso_hom
  have hover : p.iso.hom.iso.hom ≫ pullback.snd y.projection (fppfYoneda.map p.f) =
      pullback.snd x.projection (fppfYoneda.map p.f) := p.iso.hom.over
  simp only [Category.assoc, hover, repPullbackHom_snd] at h
  rw [fppfYoneda.map_comp, h]

/-- Two points with the same test map and the same morphism of representing schemes (up to
the canonical identification of the fibre products) are equal. -/
theorem ext {p q : IsomPoint x y RP RQ S} (hf : p.f = q.f)
    (hh : p.hom ≫ (pullback.congrHom rfl hf).hom = (pullback.congrHom rfl hf).hom ≫ q.hom) :
    p = q := by
  obtain ⟨f, h, _⟩ := p
  obtain ⟨f', h', _⟩ := q
  dsimp only at hf
  subst hf
  have e₁ : (pullback.congrHom rfl rfl : pullback RP.toBase f ≅ pullback RP.toBase f).hom =
      𝟙 _ := by apply pullback.hom_ext <;> simp
  have e₂ : (pullback.congrHom rfl rfl : pullback RQ.toBase f ≅ pullback RQ.toBase f).hom =
      𝟙 _ := by apply pullback.hom_ext <;> simp
  rw [e₁, e₂, Category.comp_id, Category.id_comp] at hh
  subst hh
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The point attached to an isomorphism of base-changed torsors**: its morphism of
representing schemes is the Yoneda preimage of the underlying sheaf map, transported through
the comparison isomorphisms.  (The transparency option lets `simp` see that the sheaf of
`pullbackObj f y` is `pullbackSheaf y.toFppfTorsor f`.) -/
noncomputable def ofIso (f : S ⟶ T) (e : pullbackObj f x ≅ pullbackObj f y) :
    IsomPoint x y RP RQ S where
  f := f
  hom := fppfYoneda.preimage (repPullbackHom RP f ≫ e.hom.iso.hom ≫ inv (repPullbackHom RQ f))
  exists_iso := ⟨e, by simp only [Functor.map_preimage, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]⟩

/-- The test map of the point attached to an isomorphism. -/
@[simp]
theorem ofIso_f (f : S ⟶ T) (e : pullbackObj f x ≅ pullbackObj f y) :
    (ofIso (RP := RP) (RQ := RQ) f e).f = f :=
  rfl

/-- The underlying sheaf map of the point attached to an isomorphism. -/
theorem map_ofIso_hom (f : S ⟶ T) (e : pullbackObj f x ≅ pullbackObj f y) :
    fppfYoneda.map (ofIso (RP := RP) (RQ := RQ) f e).hom =
      repPullbackHom RP f ≫ e.hom.iso.hom ≫ inv (repPullbackHom RQ f) :=
  Functor.map_preimage _ _

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism attached to the point of an isomorphism is that isomorphism. -/
@[simp]
theorem ofIso_iso (f : S ⟶ T) (e : pullbackObj f x ≅ pullbackObj f y) :
    (ofIso (RP := RP) (RQ := RQ) f e).iso = e := by
  refine iso_eq _ _ ?_
  change repPullbackHom RP f ≫ e.hom.iso.hom =
    fppfYoneda.map (ofIso (RP := RP) (RQ := RQ) f e).hom ≫ repPullbackHom RQ f
  simp only [map_ofIso_hom, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The morphisms of representing schemes of equal points agree, up to the canonical
identification of the fibre products. -/
theorem hom_eq_of_eq {p q : IsomPoint x y RP RQ S} (h : p = q) (hf : p.f = q.f) :
    p.hom ≫ (pullback.congrHom rfl hf).hom = (pullback.congrHom rfl hf).hom ≫ q.hom := by
  subst h
  apply pullback.hom_ext <;> simp

/-- Two points with the same test map and the same morphism of representing schemes are
equal. -/
theorem ext_heq {p q : IsomPoint x y RP RQ S} (hf : p.f = q.f) (hh : HEq p.hom q.hom) :
    p = q := by
  obtain ⟨f, h, _⟩ := p
  obtain ⟨f', h', _⟩ := q
  dsimp only at hf hh
  subst hf
  obtain rfl := eq_of_heq hh
  rfl

/-- The point attached to the isomorphism of a point is that point. -/
@[simp]
theorem ofIso_f_iso (p : IsomPoint x y RP RQ S) : ofIso p.f p.iso = p := by
  refine ext_heq rfl (heq_of_eq ?_)
  change fppfYoneda.preimage
    (repPullbackHom RP p.f ≫ p.iso.hom.iso.hom ≫ inv (repPullbackHom RQ p.f)) = p.hom
  apply fppfYoneda.map_injective
  rw [Functor.map_preimage, ← Category.assoc, p.repPullbackHom_comp_iso_hom, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-! #### Restriction along a morphism of test schemes -/

section Restrict

variable {S' : Scheme.{u}} (g : S' ⟶ S)

/-- **The key computation**: the pseudofunctorial pullback along `g` of the isomorphism of a
point corresponds to the restriction of its morphism of representing schemes. -/
theorem repPullbackHom_comp_stackPullbackIso_hom_iso_hom (p : IsomPoint x y RP RQ S) :
    repPullbackHom RP (g ≫ p.f) ≫
        (stackPullbackIso (quotientStack G U) g p.f (toStackIso x y p.iso)).hom.iso.hom =
      fppfYoneda.map (restrictHom RP p.f RQ g p.hom p.hom_snd) ≫ repPullbackHom RQ (g ≫ p.f) := by
  rw [stackPullbackIso_toStackIso_hom_iso_hom]
  exact repPullbackHom_comp_pullbackMap_conj RP p.f RQ g p.iso.hom.iso.hom p.iso.hom.over
    p.hom p.hom_snd p.repPullbackHom_comp_iso_hom

/-- **Restriction of a point along `g : S' ⟶ S`.** -/
noncomputable def restrict (p : IsomPoint x y RP RQ S) : IsomPoint x y RP RQ S' where
  f := g ≫ p.f
  hom := restrictHom RP p.f RQ g p.hom p.hom_snd
  exists_iso := ⟨ofStackIso x y (stackPullbackIso (quotientStack G U) g p.f (toStackIso x y p.iso)),
    repPullbackHom_comp_stackPullbackIso_hom_iso_hom g p⟩

/-- The test map of a restricted point. -/
@[simp]
theorem restrict_f (p : IsomPoint x y RP RQ S) : (p.restrict g).f = g ≫ p.f :=
  rfl

/-- The morphism of representing schemes of a restricted point. -/
@[simp]
theorem restrict_hom (p : IsomPoint x y RP RQ S) :
    (p.restrict g).hom = restrictHom RP p.f RQ g p.hom p.hom_snd :=
  rfl

/-- **Naturality of the attached isomorphism**: the isomorphism of the restricted point is the
pseudofunctorial pullback of the isomorphism of the point. -/
theorem restrict_iso (p : IsomPoint x y RP RQ S) :
    (p.restrict g).iso =
      ofStackIso x y (stackPullbackIso (quotientStack G U) g p.f (toStackIso x y p.iso)) :=
  iso_eq _ _ (repPullbackHom_comp_stackPullbackIso_hom_iso_hom g p)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along the identity is the identity. -/
theorem restrict_id (p : IsomPoint x y RP RQ S) : p.restrict (𝟙 S) = p := by
  refine ext (Category.id_comp p.f) ?_
  apply pullback.hom_ext
  · simp
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along a composite is the composite of the restrictions. -/
theorem restrict_comp {S'' : Scheme.{u}} (g' : S'' ⟶ S') (p : IsomPoint x y RP RQ S) :
    (p.restrict g).restrict g' = p.restrict (g' ≫ g) := by
  refine ext (Category.assoc g' g p.f).symm ?_
  apply pullback.hom_ext
  · simp
  · simp

end Restrict

end IsomPoint

/-- **The isomorphism presheaf** of two objects `x y` of `[U/G]` over `T` with represented
underlying torsors: its sections over `S` are the points `IsomPoint x y RP RQ S`, restricted
along morphisms of test schemes by `IsomPoint.restrict`. -/
noncomputable def isomPresheaf : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj S := IsomPoint x y RP RQ S.unop
  map {S S'} g := ↾fun p : IsomPoint x y RP RQ S.unop => IsomPoint.restrict g.unop p
  map_id S := by
    ext p
    exact p.restrict_id
  map_comp g g' := by
    ext p
    exact (p.restrict_comp g.unop g'.unop).symm

/-- The sections of the isomorphism presheaf over `S` are the points over `S`. -/
@[simp]
theorem isomPresheaf_obj (S : Scheme.{u}) :
    (isomPresheaf x y RP RQ).obj (Opposite.op S) = IsomPoint x y RP RQ S :=
  rfl

/-- The restriction maps of the isomorphism presheaf are `IsomPoint.restrict`. -/
@[simp]
theorem isomPresheaf_map {S S' : Scheme.{u}} (g : S' ⟶ S) (p : IsomPoint x y RP RQ S) :
    (isomPresheaf x y RP RQ).map g.op p = p.restrict g :=
  rfl

/-- **Points of the isomorphism presheaf are isomorphisms in the stack fibre**: the bijection
between `IsomPoint x y RP RQ S` and pairs of a test map `f : S ⟶ T` and an isomorphism
`f^* x ≅ f^* y` in the fibre of `[U/G]` over `S`. -/
noncomputable def isomPointEquiv (S : Scheme.{u}) :
    IsomPoint x y RP RQ S ≃
      Σ f : S ⟶ T, ((stackPullback (quotientStack G U) f).obj x ≅
        (stackPullback (quotientStack G U) f).obj y) where
  toFun p := ⟨p.f, toStackIso x y p.iso⟩
  invFun s := IsomPoint.ofIso s.1 (ofStackIso x y s.2)
  left_inv p := by simp
  right_inv s := by
    obtain ⟨f, e⟩ := s
    simp

/-- The test map of the pair attached to a point. -/
@[simp]
theorem isomPointEquiv_apply_fst (S : Scheme.{u}) (p : IsomPoint x y RP RQ S) :
    (isomPointEquiv x y RP RQ S p).1 = p.f :=
  rfl

/-- The isomorphism of the pair attached to a point. -/
@[simp]
theorem isomPointEquiv_apply_snd (S : Scheme.{u}) (p : IsomPoint x y RP RQ S) :
    (isomPointEquiv x y RP RQ S p).2 = toStackIso x y p.iso :=
  rfl

/-- The point attached to a pair is `IsomPoint.ofIso`. -/
@[simp]
theorem isomPointEquiv_symm_apply (S : Scheme.{u}) (f : S ⟶ T)
    (e : (stackPullback (quotientStack G U) f).obj x ≅
      (stackPullback (quotientStack G U) f).obj y) :
    (isomPointEquiv x y RP RQ S).symm ⟨f, e⟩ = IsomPoint.ofIso f (ofStackIso x y e) :=
  rfl

/-- **Naturality of `isomPointEquiv` in the test scheme**: restricting a point along
`g : S' ⟶ S` corresponds to the pseudofunctorial pullback `stackPullbackIso` of its
isomorphism.  (The test maps agree definitionally: `(p.restrict g).f = g ≫ p.f`.) -/
theorem isomPointEquiv_restrict {S S' : Scheme.{u}} (g : S' ⟶ S) (p : IsomPoint x y RP RQ S) :
    (isomPointEquiv x y RP RQ S' (p.restrict g)).2 =
      stackPullbackIso (quotientStack G U) g p.f (isomPointEquiv x y RP RQ S p).2 := by
  change toStackIso x y (p.restrict g).iso = _
  rw [IsomPoint.restrict_iso]
  rfl

/-- Naturality of `isomPointEquiv.symm`: the restriction of the point of `(f, e)` is the point
of `(g ≫ f, stackPullbackIso g f e)`. -/
theorem isomPointEquiv_symm_restrict {S S' : Scheme.{u}} (g : S' ⟶ S) (f : S ⟶ T)
    (e : (stackPullback (quotientStack G U) f).obj x ≅
      (stackPullback (quotientStack G U) f).obj y) :
    ((isomPointEquiv x y RP RQ S).symm ⟨f, e⟩).restrict g =
      (isomPointEquiv x y RP RQ S').symm ⟨g ≫ f, stackPullbackIso (quotientStack G U) g f e⟩ := by
  apply (isomPointEquiv x y RP RQ S').injective
  rw [Equiv.apply_symm_apply, isomPointEquiv_symm_apply]
  refine Sigma.ext rfl (heq_of_eq ?_)
  change toStackIso x y ((IsomPoint.ofIso f (ofStackIso x y e)).restrict g).iso = _
  rw [IsomPoint.restrict_iso, IsomPoint.ofIso_iso]
  rfl

/-- Restriction of the point of an isomorphism `e : pullbackObj f x ≅ pullbackObj f y`. -/
theorem restrict_ofIso {S S' : Scheme.{u}} (g : S' ⟶ S) (f : S ⟶ T)
    (e : pullbackObj f x ≅ pullbackObj f y) :
    (IsomPoint.ofIso (RP := RP) (RQ := RQ) f e).restrict g =
      IsomPoint.ofIso (g ≫ f)
        (ofStackIso x y (stackPullbackIso (quotientStack G U) g f (toStackIso x y e))) :=
  isomPointEquiv_symm_restrict x y RP RQ g f (toStackIso x y e)

end IsomPoint

/-! ### The sheaf property -/

section Sheaf

variable {x y : ActionTorsor G U T} {RP : TorsorRepresentation x.toFppfTorsor}
  {RQ : TorsorRepresentation y.toFppfTorsor}

/-- Transport of an isomorphism of base-changed torsors along an equality of test maps. -/
def isoOfEq {S : Scheme.{u}} {f₁ f₂ : S ⟶ T} (h : f₁ = f₂)
    (e : pullbackObj f₁ x ≅ pullbackObj f₁ y) : pullbackObj f₂ x ≅ pullbackObj f₂ y :=
  h ▸ e

/-- Transport along a reflexivity proof is the identity. -/
@[simp]
theorem isoOfEq_rfl {S : Scheme.{u}} {f : S ⟶ T} (h : f = f)
    (e : pullbackObj f x ≅ pullbackObj f y) : isoOfEq h e = e :=
  rfl

/-- The point of a transported isomorphism is the point of the isomorphism. -/
theorem _root_.GromovWitten.AlgebraicGeometry.ActionTorsor.IsomPoint.ofIso_isoOfEq
    {S : Scheme.{u}} {f₁ f₂ : S ⟶ T} (h : f₁ = f₂) (e : pullbackObj f₁ x ≅ pullbackObj f₁ y) :
    IsomPoint.ofIso (RP := RP) (RQ := RQ) f₂ (isoOfEq h e) = IsomPoint.ofIso f₁ e := by
  subst h
  rfl

/-- The canonical identification of the sheaf base changes of a torsor along equal test
maps. -/
noncomputable def sheafCast (P : FppfTorsor G T) {S : Scheme.{u}} {f₁ f₂ : S ⟶ T} (h : f₁ = f₂) :
    FppfTorsor.pullbackSheaf P f₁ ⟶ FppfTorsor.pullbackSheaf P f₂ :=
  pullback.map P.projection (fppfYoneda.map f₁) P.projection (fppfYoneda.map f₂) (𝟙 _) (𝟙 _)
    (𝟙 _) (by simp) (by simp [h])

/-- The canonical identification commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem sheafCast_fst (P : FppfTorsor G T) {S : Scheme.{u}} {f₁ f₂ : S ⟶ T} (h : f₁ = f₂) :
    sheafCast P h ≫ pullback.fst P.projection (fppfYoneda.map f₂) =
      pullback.fst P.projection (fppfYoneda.map f₁) := by
  simp [sheafCast]

/-- The canonical identification commutes with the second projections. -/
@[reassoc (attr := simp)]
theorem sheafCast_snd (P : FppfTorsor G T) {S : Scheme.{u}} {f₁ f₂ : S ⟶ T} (h : f₁ = f₂) :
    sheafCast P h ≫ pullback.snd P.projection (fppfYoneda.map f₂) =
      pullback.snd P.projection (fppfYoneda.map f₁) := by
  simp [sheafCast]

/-- The canonical identification along a reflexivity proof is the identity. -/
@[simp]
theorem sheafCast_rfl (P : FppfTorsor G T) {S : Scheme.{u}} {f : S ⟶ T} (h : f = f) :
    sheafCast P h = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- The underlying sheaf map of a transported isomorphism: the sheaf map conjugated by the
canonical identifications of the fibre products. -/
theorem isoOfEq_hom_iso_hom {S : Scheme.{u}} {f₁ f₂ : S ⟶ T} (h : f₁ = f₂)
    (e : pullbackObj f₁ x ≅ pullbackObj f₁ y) :
    (isoOfEq h e).hom.iso.hom =
      sheafCast x.toFppfTorsor h.symm ≫ e.hom.iso.hom ≫ sheafCast y.toFppfTorsor h := by
  subst h
  simp

/-- Gluing morphisms of schemes along an fppf covering sieve (`fppfYoneda.obj T` is a sheaf):
a compatible family of morphisms to `T` on the members of the sieve comes from a unique
morphism on the base. -/
theorem existsUnique_hom_of_sieve {S : Scheme.{u}} {R : Sieve S} (hR : R ∈ fppfJ.{u} S)
    (f : ∀ {Y : Scheme.{u}} (g : Y ⟶ S), R.arrows g → (Y ⟶ T))
    (compat : ∀ {Y₁ Y₂ Z : Scheme.{u}} (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) {k₁ : Y₁ ⟶ S} {k₂ : Y₂ ⟶ S}
      (h₁ : R.arrows k₁) (h₂ : R.arrows k₂), g₁ ≫ k₁ = g₂ ≫ k₂ → g₁ ≫ f k₁ h₁ = g₂ ≫ f k₂ h₂) :
    ∃! φ : S ⟶ T, ∀ {Y : Scheme.{u}} (g : Y ⟶ S) (hg : R.arrows g), g ≫ φ = f g hg := by
  have hs : Presieve.IsSheafFor (fppfYoneda.obj T).obj R.arrows :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (fppfYoneda.obj T).property R hR
  obtain ⟨φ, hφ, huniq⟩ := hs (fun _ g hg => f g hg)
    (fun _ _ _ g₁ g₂ _ _ h₁ h₂ hh => compat g₁ g₂ h₁ h₂ hh)
  exact ⟨φ, fun g hg => hφ g hg, fun φ' hφ' => huniq φ' (fun _ g hg => hφ' g hg)⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The isomorphism presheaf is separated**: two points over `S` whose restrictions along the
members of an fppf covering sieve agree are equal. -/
theorem IsomPoint.ext_of_sieve {S : Scheme.{u}} {R : Sieve S} (hR : R ∈ fppfJ.{u} S)
    {p q : IsomPoint x y RP RQ S}
    (h : ∀ {Y : Scheme.{u}} (g : Y ⟶ S), R.arrows g → p.restrict g = q.restrict g) : p = q := by
  have hf : p.f = q.f := by
    obtain ⟨φ, -, huniq⟩ := existsUnique_hom_of_sieve hR (fun g hg => (p.restrict g).f)
      (fun g₁ g₂ _ _ h₁ h₂ hh => by simp only [IsomPoint.restrict_f, ← Category.assoc, hh])
    rw [huniq p.f (fun g hg => rfl), huniq q.f (fun g hg => by rw [h g hg]; rfl)]
  obtain ⟨f₁, h₁, e₁⟩ := p
  obtain ⟨f₂, h₂, e₂⟩ := q
  dsimp only at hf
  subst hf
  refine IsomPoint.ext_heq rfl (heq_of_eq ?_)
  change h₁ = h₂
  have k₁ : repPullbackHom RP f₁ ≫ (⟨f₁, h₁, e₁⟩ : IsomPoint x y RP RQ S).iso.hom.iso.hom =
      fppfYoneda.map h₁ ≫ repPullbackHom RQ f₁ :=
    IsomPoint.repPullbackHom_comp_iso_hom (⟨f₁, h₁, e₁⟩ : IsomPoint x y RP RQ S)
  have k₂ : repPullbackHom RP f₁ ≫ (⟨f₁, h₂, e₂⟩ : IsomPoint x y RP RQ S).iso.hom.iso.hom =
      fppfYoneda.map h₂ ≫ repPullbackHom RQ f₁ :=
    IsomPoint.repPullbackHom_comp_iso_hom (⟨f₁, h₂, e₂⟩ : IsomPoint x y RP RQ S)
  have hiso : (⟨f₁, h₁, e₁⟩ : IsomPoint x y RP RQ S).iso =
      (⟨f₁, h₂, e₂⟩ : IsomPoint x y RP RQ S).iso := by
    apply Iso.ext
    apply hom_ext_of_cover_torsor hR
    intro Y g hg
    have hg' : fppfYoneda.map (restrictHom RP f₁ RQ g h₁ (IsomPoint.hom_snd ⟨f₁, h₁, e₁⟩)) =
        fppfYoneda.map (restrictHom RP f₁ RQ g h₂ (IsomPoint.hom_snd ⟨f₁, h₂, e₂⟩)) :=
      congrArg fppfYoneda.map (eq_of_heq (congr_arg_heq IsomPoint.hom (h g hg)))
    have e₀ : repPullbackHom RP (g ≫ f₁) ≫ (FppfTorsor.pullbackCompIso x.toFppfTorsor g f₁).hom ≫
        proj (pullbackObj f₁ x) g = fppfYoneda.map (repBaseChange RP f₁ g) ≫ repPullbackHom RP f₁ :=
      repPullbackHom_comp_pullbackCompIso_hom_fst RP f₁ g
    rw [← cancel_epi (repPullbackHom RP (g ≫ f₁) ≫
      (FppfTorsor.pullbackCompIso x.toFppfTorsor g f₁).hom)]
    simp only [Category.assoc]
    rw [reassoc_of% e₀, reassoc_of% e₀, k₁, k₂, ← Category.assoc, ← Category.assoc,
      ← fppfYoneda.map_comp, ← fppfYoneda.map_comp,
      ← restrictHom_comp_repBaseChange RP f₁ RQ g h₁ (IsomPoint.hom_snd ⟨f₁, h₁, e₁⟩),
      ← restrictHom_comp_repBaseChange RP f₁ RQ g h₂ (IsomPoint.hom_snd ⟨f₁, h₂, e₂⟩),
      fppfYoneda.map_comp, fppfYoneda.map_comp, hg']
  apply fppfYoneda.map_injective
  rw [hiso] at k₁
  exact (cancel_mono (repPullbackHom RQ f₁)).1 (k₁.symm.trans k₂)

/-- The sheaf map `fppfYoneda.map h` of a point, written through the attached isomorphism. -/
theorem IsomPoint.map_hom_eq {S : Scheme.{u}} (p : IsomPoint x y RP RQ S) :
    fppfYoneda.map p.hom =
      repPullbackHom RP p.f ≫ p.iso.hom.iso.hom ≫ inv (repPullbackHom RQ p.f) := by
  rw [← Category.assoc, p.repPullbackHom_comp_iso_hom, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

section Descent

variable {S : Scheme.{u}} {R : Sieve S}
  (p : ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ S), R.arrows g → IsomPoint x y RP RQ Y)
  (φ : S ⟶ T) (hφ : ∀ {Y : Scheme.{u}} (g : Y ⟶ S) (hg : R.arrows g), g ≫ φ = (p g hg).f)

/-- The arrow of the descent datum attached to a member `g : Y ⟶ S` of the sieve: the
isomorphism of the point `p g hg`, transported to the test map `g ≫ φ` and conjugated by the
composition comparisons of base change. -/
noncomputable def isomDescentHom {Y : Scheme.{u}} (g : Y ⟶ S) (hg : R.arrows g) :
    pullbackObj g (pullbackObj φ x) ⟶ pullbackObj g (pullbackObj φ y) :=
  (pullbackCompIsoApp g φ x).inv ≫ (isoOfEq (hφ g hg).symm (p g hg).iso).hom ≫
    (pullbackCompIsoApp g φ y).hom

/-- The underlying sheaf map of `isomDescentHom`. -/
theorem isomDescentHom_iso_hom {Y : Scheme.{u}} (g : Y ⟶ S) (hg : R.arrows g) :
    (isomDescentHom p φ hφ g hg).iso.hom =
      (FppfTorsor.pullbackCompIso x.toFppfTorsor g φ).inv ≫
        sheafCast x.toFppfTorsor (hφ g hg) ≫ (p g hg).iso.hom.iso.hom ≫
          sheafCast y.toFppfTorsor (hφ g hg).symm ≫
            (FppfTorsor.pullbackCompIso y.toFppfTorsor g φ).hom := by
  rw [isomDescentHom, comp_iso_hom, comp_iso_hom, pullbackCompIsoApp_inv_iso_hom,
    pullbackCompIsoApp_hom_iso_hom, isoOfEq_hom_iso_hom, Category.assoc, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The compatibility of the arrows `isomDescentHom` with base change inside the sieve, in the
form required by `TorsorHomFamily`. -/
theorem isomDescentHom_compat
    (hp : ∀ ⦃Y₁ Y₂ Z : Scheme.{u}⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) ⦃k₁ : Y₁ ⟶ S⦄ ⦃k₂ : Y₂ ⟶ S⦄
      (h₁ : R.arrows k₁) (h₂ : R.arrows k₂), g₁ ≫ k₁ = g₂ ≫ k₂ →
        (p k₁ h₁).restrict g₁ = (p k₂ h₂).restrict g₂)
    {Y Z : Scheme.{u}} (k : Y ⟶ S) (g : Z ⟶ Y) (h : Z ⟶ S) (hh : g ≫ k = h)
    (hk : R.arrows k) (hh' : R.arrows h) :
    (isomDescentHom p φ hφ h hh').iso.hom ≫ proj (pullbackObj φ y) h =
      relBaseChange (pullbackObj φ x).projection k g h hh ≫
        (isomDescentHom p φ hφ k hk).iso.hom ≫ proj (pullbackObj φ y) k := by
  subst hh
  -- The point over `g ≫ k` is the restriction of the point over `k`.
  have hc : p (g ≫ k) hh' = (p k hk).restrict g := by
    have := hp g (𝟙 Z) hk hh' (by simp)
    rw [IsomPoint.restrict_id] at this
    exact this.symm
  have key : ∀ (q : IsomPoint x y RP RQ Z) (hq : (g ≫ k) ≫ φ = q.f),
      q = (p k hk).restrict g →
      sheafCast x.toFppfTorsor hq ≫ q.iso.hom.iso.hom ≫ sheafCast y.toFppfTorsor hq.symm =
        sheafCast x.toFppfTorsor (by rw [IsomPoint.restrict_f, ← hφ k hk, Category.assoc]) ≫
          ((p k hk).restrict g).iso.hom.iso.hom ≫
            sheafCast y.toFppfTorsor (by rw [IsomPoint.restrict_f, ← hφ k hk, Category.assoc]) := by
    rintro q hq rfl
    rfl
  rw [isomDescentHom_iso_hom, isomDescentHom_iso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% (key _ (hφ (g ≫ k) hh') hc), IsomPoint.restrict_iso, ofStackIso_hom_iso_hom,
    stackPullbackIso_toStackIso_hom_iso_hom]
  -- Projection identities of `pullbackMap`, stated with the projections unfolded.
  have e₁ : FppfTorsor.pullbackMap (P := x.toFppfTorsor.pullbackTorsor (p k hk).f)
        (Q := y.toFppfTorsor.pullbackTorsor (p k hk).f) g (p k hk).iso.hom.iso.hom
          (p k hk).iso.hom.over ≫
        pullback.fst (pullback.snd y.projection (fppfYoneda.map (p k hk).f)) (fppfYoneda.map g) =
      pullback.fst (pullback.snd x.projection (fppfYoneda.map (p k hk).f)) (fppfYoneda.map g) ≫
        (p k hk).iso.hom.iso.hom :=
    FppfTorsor.pullbackMap_fst (P := x.toFppfTorsor.pullbackTorsor (p k hk).f)
      (Q := y.toFppfTorsor.pullbackTorsor (p k hk).f) g _ (p k hk).iso.hom.over
  have e₂ : FppfTorsor.pullbackMap (P := x.toFppfTorsor.pullbackTorsor (p k hk).f)
        (Q := y.toFppfTorsor.pullbackTorsor (p k hk).f) g (p k hk).iso.hom.iso.hom
          (p k hk).iso.hom.over ≫
        pullback.snd (pullback.snd y.projection (fppfYoneda.map (p k hk).f)) (fppfYoneda.map g) =
      pullback.snd (pullback.snd x.projection (fppfYoneda.map (p k hk).f)) (fppfYoneda.map g) :=
    FppfTorsor.pullbackMap_snd (P := x.toFppfTorsor.pullbackTorsor (p k hk).f)
      (Q := y.toFppfTorsor.pullbackTorsor (p k hk).f) g _ (p k hk).iso.hom.over
  have hover : (p k hk).iso.hom.iso.hom ≫ pullback.snd y.projection (fppfYoneda.map (p k hk).f) =
      pullback.snd x.projection (fppfYoneda.map (p k hk).f) := (p k hk).iso.hom.over
  have hproj₁ : proj (pullbackObj φ y) (g ≫ k) =
      pullback.fst (pullback.snd y.projection (fppfYoneda.map φ)) (fppfYoneda.map (g ≫ k)) := rfl
  have hproj₂ : proj (pullbackObj φ y) k =
      pullback.fst (pullback.snd y.projection (fppfYoneda.map φ)) (fppfYoneda.map k) := rfl
  rw [hproj₁, hproj₂]
  -- The comparison of the two base changes of `x`, before applying `A`.
  have sub : (FppfTorsor.pullbackCompIso x.toFppfTorsor (g ≫ k) φ).inv ≫
      sheafCast x.toFppfTorsor
          (show (g ≫ k) ≫ φ = g ≫ (p k hk).f by rw [← hφ k hk, Category.assoc]) ≫
        (FppfTorsor.pullbackCompIso x.toFppfTorsor g (p k hk).f).hom ≫
          pullback.fst (pullback.snd x.projection (fppfYoneda.map (p k hk).f))
            (fppfYoneda.map g) =
      relBaseChange (pullback.snd x.projection (fppfYoneda.map φ)) k g (g ≫ k) rfl ≫
        (FppfTorsor.pullbackCompIso x.toFppfTorsor k φ).inv ≫
          sheafCast x.toFppfTorsor (hφ k hk) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, FppfTorsor.pullbackCompIso_hom_fst_fst, sheafCast_fst,
        FppfTorsor.pullbackCompIso_inv_fst, relBaseChange_fst_assoc]
    · simp only [Category.assoc, FppfTorsor.pullbackCompIso_hom_fst_snd, sheafCast_snd_assoc,
        sheafCast_snd, FppfTorsor.pullbackCompIso_inv_snd_assoc, FppfTorsor.pullbackCompIso_inv_snd,
        relBaseChange_snd]
  apply pullback.hom_ext
  · simp only [Category.assoc, FppfTorsor.pullbackCompIso_hom_fst_fst, sheafCast_fst,
      IsomPoint.restrict_f, FppfTorsor.pullbackCompIso_inv_fst, reassoc_of% e₁, reassoc_of% sub]
  · simp only [Category.assoc, FppfTorsor.pullbackCompIso_hom_fst_snd, sheafCast_snd_assoc,
      IsomPoint.restrict_f, FppfTorsor.pullbackCompIso_inv_snd_assoc, reassoc_of% e₂,
      FppfTorsor.pullbackCompIso_hom_snd_assoc, reassoc_of% hover, relBaseChange_snd_assoc,
      fppfYoneda.map_comp]

variable (x y RP RQ) in
/-- **The descent datum of torsor isomorphisms** attached to a compatible family of points of
the isomorphism presheaf on a covering sieve of `S`, once the test maps have been glued to
`φ : S ⟶ T`. -/
noncomputable def isomDescentFamily
    (hp : ∀ ⦃Y₁ Y₂ Z : Scheme.{u}⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) ⦃k₁ : Y₁ ⟶ S⦄ ⦃k₂ : Y₂ ⟶ S⦄
      (h₁ : R.arrows k₁) (h₂ : R.arrows k₂), g₁ ≫ k₁ = g₂ ≫ k₂ →
        (p k₁ h₁).restrict g₁ = (p k₂ h₂).restrict g₂) :
    TorsorHomFamily (pullbackObj φ x) (pullbackObj φ y) R where
  hom g hg := isomDescentHom p φ hφ g hg
  compat k g h hh hk hh' := isomDescentHom_compat p φ hφ hp k g h hh hk hh'

end Descent

variable (x y RP RQ)

set_option backward.isDefEq.respectTransparency false in
/-- **The isomorphism presheaf is an fppf sheaf.**  A compatible family of points on a covering
sieve has glued test maps (`fppfYoneda.obj T` is a sheaf) and glued isomorphism (descent of
morphisms for `[U/G]`, `ActionTorsor.existsUnique_hom_of_torsorHomFamily`); the glued point is
unique by `IsomPoint.ext_of_sieve`. -/
theorem isSheaf_isomPresheaf : Presieve.IsSheaf fppfJ.{u} (isomPresheaf x y RP RQ) := by
  intro S R hR p hp
  have hp' : ∀ ⦃Y₁ Y₂ Z : Scheme.{u}⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) ⦃k₁ : Y₁ ⟶ S⦄ ⦃k₂ : Y₂ ⟶ S⦄
      (h₁ : R.arrows k₁) (h₂ : R.arrows k₂), g₁ ≫ k₁ = g₂ ≫ k₂ →
        (p k₁ h₁).restrict g₁ = (p k₂ h₂).restrict g₂ :=
    fun _ _ _ g₁ g₂ _ _ h₁ h₂ hh => hp g₁ g₂ h₁ h₂ hh
  obtain ⟨φ, hφ, -⟩ := existsUnique_hom_of_sieve hR (fun g hg => (p g hg).f)
    (fun g₁ g₂ _ _ h₁ h₂ hh => congrArg IsomPoint.f (hp' g₁ g₂ h₁ h₂ hh))
  obtain ⟨ψ, hψ, -⟩ := existsUnique_hom_of_torsorHomFamily hR
    (isomDescentFamily x y RP RQ p φ hφ hp')
  -- The glued point restricts to the given family.
  have hamalg : ∀ {Y : Scheme.{u}} (g : Y ⟶ S) (hg : R.arrows g),
      (IsomPoint.ofIso φ (asIso ψ)).restrict g = p g hg := by
    intro Y g hg
    rw [restrict_ofIso]
    have key : ofStackIso x y (stackPullbackIso (quotientStack G U) g φ
        (toStackIso x y (asIso ψ))) = isoOfEq (hφ g hg).symm (p g hg).iso := by
      apply Iso.ext
      change ((pullbackCompIsoApp g φ x).hom ≫ (pullbackFunctor g).map ψ) ≫
        (pullbackCompIsoApp g φ y).inv = _
      rw [hψ g hg]
      change ((pullbackCompIsoApp g φ x).hom ≫ isomDescentHom p φ hφ g hg) ≫
        (pullbackCompIsoApp g φ y).inv = _
      rw [isomDescentHom]
      simp
    rw [key, IsomPoint.ofIso_isoOfEq, IsomPoint.ofIso_f_iso]
  refine ⟨IsomPoint.ofIso φ (asIso ψ), fun Y g hg => hamalg g hg, fun q hq => ?_⟩
  exact IsomPoint.ext_of_sieve hR (fun g hg => (hq g hg).trans (hamalg g hg).symm)

/-- **The isomorphism sheaf** `Isom(x, y)` of two objects of `[U/G]` over `T` with represented
underlying torsors: the fppf sheaf whose `S`-points are the pairs of a test map `f : S ⟶ T` and
an isomorphism `f^* x ≅ f^* y` (`IsomPoint`, `isomPointEquiv`). -/
noncomputable def isomSheaf : FppfSheaf.{u} :=
  ⟨isomPresheaf x y RP RQ, (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_isomPresheaf x y RP RQ)⟩

/-- The underlying presheaf of the isomorphism sheaf is `isomPresheaf`. -/
@[simp]
theorem isomSheaf_obj : (isomSheaf x y RP RQ).obj = isomPresheaf x y RP RQ :=
  rfl

/-- The structure map `Isom(x, y) ⟶ T`, sending a point to its test map. -/
noncomputable def isomProjection : isomSheaf x y RP RQ ⟶ fppfYoneda.obj T :=
  ObjectProperty.homMk
    { app := fun S => ↾fun p : IsomPoint x y RP RQ S.unop => p.f
      naturality := fun S S' g => by
        ext p
        rfl }

/-- The structure map sends a point to its test map. -/
@[simp]
theorem isomProjection_app (S : Scheme.{u}) (p : IsomPoint x y RP RQ S) :
    (isomProjection x y RP RQ).hom.app (Opposite.op S) p = p.f :=
  rfl

/-- A morphism from a representable sheaf to the isomorphism sheaf, composed with the structure
map, is the test map of the corresponding point. -/
theorem comp_isomProjection {S : Scheme.{u}} (α : fppfYoneda.obj S ⟶ isomSheaf x y RP RQ) :
    α ≫ isomProjection x y RP RQ = fppfYoneda.map (fppfJ.yonedaEquiv α).f := by
  apply fppfJ.yonedaEquiv.injective
  rw [GrothendieckTopology.yonedaEquiv_comp, GrothendieckTopology.yonedaEquiv_yoneda_map]
  rfl

end Sheaf

/-! ### Base change of the isomorphism sheaf -/

section BaseChange

variable {x y : ActionTorsor G U T} {RP : TorsorRepresentation x.toFppfTorsor}
  {RQ : TorsorRepresentation y.toFppfTorsor} {S : Scheme.{u}} (b : S ⟶ T)

/-- The comparison map of the base-changed representation, followed by the inverse of the
composition comparison, is the pasting isomorphism followed by the comparison map. -/
@[reassoc]
theorem repPullbackHom_pullbackRep_comp_pullbackCompIso_inv {P : FppfTorsor G T}
    (RP' : TorsorRepresentation P) {S' : Scheme.{u}} (g : S' ⟶ S) :
    repPullbackHom (RP'.pullbackRep b) g ≫ (FppfTorsor.pullbackCompIso P g b).inv =
      fppfYoneda.map (pullbackLeftPullbackSndIso RP'.toBase b g).hom ≫
        repPullbackHom RP' (g ≫ b) := by
  rw [Iso.comp_inv_eq, Category.assoc, repPullbackHom_comp_pullbackCompIso_hom,
    ← Category.assoc, ← fppfYoneda.map_comp, Iso.hom_inv_id, fppfYoneda.map_id,
    Category.id_comp]

/-- The comparison map is compatible with the canonical identifications of base changes along
equal test maps. -/
@[reassoc]
theorem repPullbackHom_comp_sheafCast {P : FppfTorsor G T} (RP' : TorsorRepresentation P)
    {S' : Scheme.{u}} {f₁ f₂ : S' ⟶ T} (h : f₁ = f₂) :
    repPullbackHom RP' f₁ ≫ sheafCast P h =
      fppfYoneda.map (pullback.congrHom rfl h).hom ≫ repPullbackHom RP' f₂ := by
  subst h
  apply pullback.hom_ext <;> simp

/-- The defining identity of `IsomPoint.pushBase`: the isomorphism of a point of
`Isom(b^* x, b^* y)` over `f`, conjugated by the composition comparisons, is the Yoneda
transport of the pasted morphism of representing schemes over `f ≫ b`. -/
theorem IsomPoint.pushBase_spec {S' : Scheme.{u}}
    (p : IsomPoint (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) S') :
    repPullbackHom RP (p.f ≫ b) ≫
        (pullbackCompIsoApp p.f b x ≪≫ p.iso ≪≫ (pullbackCompIsoApp p.f b y).symm).hom.iso.hom =
      fppfYoneda.map ((pullbackLeftPullbackSndIso RP.toBase b p.f).inv ≫ p.hom ≫
          (pullbackLeftPullbackSndIso RQ.toBase b p.f).hom) ≫
        repPullbackHom RQ (p.f ≫ b) := by
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, comp_iso_hom, comp_iso_hom,
    pullbackCompIsoApp_hom_iso_hom, pullbackCompIsoApp_inv_iso_hom, ← Category.assoc,
    repPullbackHom_comp_pullbackCompIso_hom, Category.assoc,
    p.repPullbackHom_comp_iso_hom_assoc, repPullbackHom_pullbackRep_comp_pullbackCompIso_inv]
  simp only [fppfYoneda.map_comp, Category.assoc]

/-- **Pushing a point of the base-changed isomorphism sheaf down to `T`**: a point over
`f : S' ⟶ S` of `Isom(b^* x, b^* y)` gives the point over `f ≫ b` of `Isom(x, y)`, through the
pasting of fibre products and the composition comparisons. -/
noncomputable def IsomPoint.pushBase {S' : Scheme.{u}}
    (p : IsomPoint (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) S') :
    IsomPoint x y RP RQ S' where
  f := p.f ≫ b
  hom := (pullbackLeftPullbackSndIso RP.toBase b p.f).inv ≫ p.hom ≫
    (pullbackLeftPullbackSndIso RQ.toBase b p.f).hom
  exists_iso := ⟨_, p.pushBase_spec b⟩

/-- The test map of a pushed-down point. -/
@[simp]
theorem IsomPoint.pushBase_f {S' : Scheme.{u}}
    (p : IsomPoint (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) S') :
    (p.pushBase b).f = p.f ≫ b :=
  rfl

/-- The morphism of representing schemes of a pushed-down point. -/
@[simp]
theorem IsomPoint.pushBase_hom {S' : Scheme.{u}}
    (p : IsomPoint (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) S') :
    (p.pushBase b).hom = (pullbackLeftPullbackSndIso RP.toBase b p.f).inv ≫ p.hom ≫
      (pullbackLeftPullbackSndIso RQ.toBase b p.f).hom :=
  rfl

/-- The isomorphism attached to a pushed-down point. -/
theorem IsomPoint.pushBase_iso {S' : Scheme.{u}}
    (p : IsomPoint (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) S') :
    (p.pushBase b).iso =
      pullbackCompIsoApp p.f b x ≪≫ p.iso ≪≫ (pullbackCompIsoApp p.f b y).symm :=
  IsomPoint.iso_eq _ _ (p.pushBase_spec b)

/-- The transition morphisms of the base-changed representation are the transition morphisms
of the representation, up to the pasting isomorphisms and the canonical identification of fibre
products. -/
theorem repBaseChange_comp_pullbackLeftPullbackSndIso_inv {P : FppfTorsor G T}
    (RP' : TorsorRepresentation P) {S' S'' : Scheme.{u}} (f : S' ⟶ S) (g : S'' ⟶ S') :
    repBaseChange RP' (f ≫ b) g ≫ (pullbackLeftPullbackSndIso RP'.toBase b f).inv =
      (pullback.congrHom rfl (Category.assoc g f b).symm).hom ≫
        (pullbackLeftPullbackSndIso RP'.toBase b (g ≫ f)).inv ≫
          repBaseChange (RP'.pullbackRep b) f g := by
  have h₁ : repBaseChange (RP'.pullbackRep b) f g ≫ pullback.fst (pullback.snd RP'.toBase b) f =
      pullback.fst (pullback.snd RP'.toBase b) (g ≫ f) := repBaseChange_fst _ _ _
  have h₂ : repBaseChange (RP'.pullbackRep b) f g ≫ pullback.snd (pullback.snd RP'.toBase b) f =
      pullback.snd (pullback.snd RP'.toBase b) (g ≫ f) ≫ g := repBaseChange_snd _ _ _
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst, repBaseChange_fst,
        reassoc_of% h₁, pullback.congrHom_hom, pullback_map_comp_fst, Category.comp_id]
    · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd, repBaseChange_snd_assoc,
        reassoc_of% h₁, pullback.congrHom_hom, pullback_map_comp_snd_assoc, Category.id_comp]
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd,
      pullbackLeftPullbackSndIso_inv_snd_snd_assoc, repBaseChange_snd, h₂,
      pullback.congrHom_hom, pullback_map_comp_snd_assoc, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of `pushBase`**: pushing down commutes with restriction along a morphism of
test schemes. -/
theorem IsomPoint.pushBase_restrict {S' S'' : Scheme.{u}} (g : S'' ⟶ S')
    (p : IsomPoint (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) S') :
    (p.pushBase b).restrict g = (p.restrict g).pushBase b := by
  refine IsomPoint.ext (Category.assoc g p.f b).symm ?_
  have h₁ : restrictHom (RP.pullbackRep b) p.f (RQ.pullbackRep b) g p.hom p.hom_snd ≫
      pullback.fst (pullback.snd RQ.toBase b) (g ≫ p.f) =
        repBaseChange (RP.pullbackRep b) p.f g ≫ p.hom ≫
          pullback.fst (pullback.snd RQ.toBase b) p.f :=
    restrictHom_fst _ _ _ _ _ _
  have h₂ : restrictHom (RP.pullbackRep b) p.f (RQ.pullbackRep b) g p.hom p.hom_snd ≫
      pullback.snd (pullback.snd RQ.toBase b) (g ≫ p.f) =
        pullback.snd (pullback.snd RP.toBase b) (g ≫ p.f) :=
    restrictHom_snd _ _ _ _ _ _
  have h₃ : p.hom ≫ pullback.snd (pullback.snd RQ.toBase b) p.f =
      pullback.snd (pullback.snd RP.toBase b) p.f := p.hom_snd
  simp only [IsomPoint.restrict_hom, IsomPoint.pushBase_hom, IsomPoint.restrict_f,
    IsomPoint.pushBase_f]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.congrHom_hom, pullback_map_comp_fst, Category.comp_id,
      restrictHom_fst, pullbackLeftPullbackSndIso_hom_fst,
      reassoc_of% (repBaseChange_comp_pullbackLeftPullbackSndIso_inv b RP p.f g),
      reassoc_of% h₁]
  · simp only [Category.assoc, pullback.congrHom_hom, pullback_map_comp_snd, Category.comp_id,
      restrictHom_snd, pullbackLeftPullbackSndIso_hom_snd, h₂,
      pullbackLeftPullbackSndIso_inv_snd_snd]

/-- Pushing down is injective on points with the same test map. -/
theorem IsomPoint.pushBase_injective {S' : Scheme.{u}}
    {p q : IsomPoint (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) S'}
    (hf : p.f = q.f) (h : p.pushBase b = q.pushBase b) : p = q := by
  obtain ⟨f₁, h₁, e₁⟩ := p
  obtain ⟨f₂, h₂, e₂⟩ := q
  dsimp only at hf
  subst hf
  refine IsomPoint.ext_heq rfl (heq_of_eq ?_)
  have e₁ : (pullback.congrHom rfl rfl : pullback RP.toBase (f₁ ≫ b) ≅
      pullback RP.toBase (f₁ ≫ b)).hom = 𝟙 _ := by apply pullback.hom_ext <;> simp
  have e₂ : (pullback.congrHom rfl rfl : pullback RQ.toBase (f₁ ≫ b) ≅
      pullback RQ.toBase (f₁ ≫ b)).hom = 𝟙 _ := by apply pullback.hom_ext <;> simp
  have := IsomPoint.hom_eq_of_eq h rfl
  dsimp only [IsomPoint.pushBase_f] at this
  rw [IsomPoint.pushBase_hom, IsomPoint.pushBase_hom, e₁, e₂, Category.comp_id,
    Category.id_comp] at this
  exact (cancel_epi (pullbackLeftPullbackSndIso RP.toBase b f₁).inv).1
    ((cancel_mono (pullbackLeftPullbackSndIso RQ.toBase b f₁).hom).1 this)

/-- The defining identity of `IsomPoint.pullBase`. -/
theorem IsomPoint.pullBase_spec {S' : Scheme.{u}} (q : IsomPoint x y RP RQ S') (g : S' ⟶ S)
    (hq : q.f = g ≫ b) :
    repPullbackHom (RP.pullbackRep b) g ≫
        ((pullbackCompIsoApp g b x).symm ≪≫ isoOfEq hq q.iso ≪≫
          pullbackCompIsoApp g b y).hom.iso.hom =
      fppfYoneda.map ((pullbackLeftPullbackSndIso RP.toBase b g).hom ≫
          (pullback.congrHom rfl hq.symm).hom ≫ q.hom ≫ (pullback.congrHom rfl hq).hom ≫
            (pullbackLeftPullbackSndIso RQ.toBase b g).inv) ≫
        repPullbackHom (RQ.pullbackRep b) g := by
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, comp_iso_hom, comp_iso_hom,
    pullbackCompIsoApp_hom_iso_hom, pullbackCompIsoApp_inv_iso_hom, isoOfEq_hom_iso_hom]
  simp only [Category.assoc]
  rw [← Category.assoc, repPullbackHom_pullbackRep_comp_pullbackCompIso_inv, Category.assoc,
    repPullbackHom_comp_sheafCast_assoc, q.repPullbackHom_comp_iso_hom_assoc,
    repPullbackHom_comp_sheafCast_assoc, repPullbackHom_comp_pullbackCompIso_hom]
  simp only [fppfYoneda.map_comp, Category.assoc]

/-- **Pulling a point of `Isom(x, y)` back to the base change**: a point `q` over `S'` whose
test map factors as `g ≫ b` gives a point of `Isom(b^* x, b^* y)` over `g`. -/
noncomputable def IsomPoint.pullBase {S' : Scheme.{u}} (q : IsomPoint x y RP RQ S') (g : S' ⟶ S)
    (hq : q.f = g ≫ b) :
    IsomPoint (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) S' where
  f := g
  hom := (pullbackLeftPullbackSndIso RP.toBase b g).hom ≫ (pullback.congrHom rfl hq.symm).hom ≫
    q.hom ≫ (pullback.congrHom rfl hq).hom ≫ (pullbackLeftPullbackSndIso RQ.toBase b g).inv
  exists_iso := ⟨_, q.pullBase_spec b g hq⟩

/-- The test map of a pulled-back point. -/
@[simp]
theorem IsomPoint.pullBase_f {S' : Scheme.{u}} (q : IsomPoint x y RP RQ S') (g : S' ⟶ S)
    (hq : q.f = g ≫ b) : (q.pullBase b g hq).f = g :=
  rfl

/-- The morphism of representing schemes of a pulled-back point. -/
@[simp]
theorem IsomPoint.pullBase_hom {S' : Scheme.{u}} (q : IsomPoint x y RP RQ S') (g : S' ⟶ S)
    (hq : q.f = g ≫ b) :
    (q.pullBase b g hq).hom = (pullbackLeftPullbackSndIso RP.toBase b g).hom ≫
      (pullback.congrHom rfl hq.symm).hom ≫ q.hom ≫ (pullback.congrHom rfl hq).hom ≫
        (pullbackLeftPullbackSndIso RQ.toBase b g).inv :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Pushing down a pulled-back point recovers the point. -/
theorem IsomPoint.pushBase_pullBase {S' : Scheme.{u}} (q : IsomPoint x y RP RQ S') (g : S' ⟶ S)
    (hq : q.f = g ≫ b) : (q.pullBase b g hq).pushBase b = q := by
  refine IsomPoint.ext hq.symm ?_
  rw [IsomPoint.pushBase_hom, IsomPoint.pullBase_hom]
  dsimp only [IsomPoint.pushBase_f, IsomPoint.pullBase_f]
  simp only [Iso.inv_hom_id_assoc, Category.assoc]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.congrHom_hom, pullback_map_comp_fst, Category.comp_id]
  · simp only [Category.assoc, pullback.congrHom_hom, pullback_map_comp_snd, Category.comp_id,
      IsomPoint.hom_snd]

variable (x y RP RQ)

/-- **The morphism `Isom(b^* x, b^* y) ⟶ Isom(x, y)`** of fppf sheaves, pushing points down to
`T`. -/
noncomputable def isomPushBase :
    isomSheaf (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) ⟶
      isomSheaf x y RP RQ :=
  ObjectProperty.homMk
    { app := fun S' => ↾fun p => IsomPoint.pushBase b p
      naturality := fun _ _ g => by
        ext p
        exact (IsomPoint.pushBase_restrict b g.unop p).symm }

/-- `isomPushBase` acts on points by `IsomPoint.pushBase`. -/
@[simp]
theorem isomPushBase_app {S' : Scheme.{u}}
    (p : IsomPoint (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) S') :
    (isomPushBase x y RP RQ b).hom.app (Opposite.op S') p = p.pushBase b :=
  rfl

/-- The pushed-down point of a morphism from a representable sheaf. -/
theorem yonedaEquiv_comp_isomPushBase {S' : Scheme.{u}} (α : fppfYoneda.obj S' ⟶
    isomSheaf (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b)) :
    fppfJ.yonedaEquiv (α ≫ isomPushBase x y RP RQ b) = (fppfJ.yonedaEquiv α).pushBase b :=
  rfl

/-- `isomPushBase` lies over `b`. -/
theorem isomPushBase_comp_isomProjection :
    isomPushBase x y RP RQ b ≫ isomProjection x y RP RQ =
      isomProjection (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) ≫
        fppfYoneda.map b := by
  apply ObjectProperty.hom_ext
  ext S' p
  rfl

/-- The comparison morphism from `Isom(b^* x, b^* y)` to the base change of `Isom(x, y)`
along `b`. -/
noncomputable def isomBaseChangeHom :
    isomSheaf (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) ⟶
      pullback (isomProjection x y RP RQ) (fppfYoneda.map b) :=
  pullback.lift (isomPushBase x y RP RQ b)
    (isomProjection (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b))
    (isomPushBase_comp_isomProjection x y RP RQ b)

/-- The first component of the base-change comparison is `isomPushBase`. -/
@[reassoc (attr := simp)]
theorem isomBaseChangeHom_fst :
    isomBaseChangeHom x y RP RQ b ≫ pullback.fst _ _ = isomPushBase x y RP RQ b := by
  unfold isomBaseChangeHom
  exact pullback.lift_fst _ _ _

/-- The second component of the base-change comparison is the structure map. -/
@[reassoc (attr := simp)]
theorem isomBaseChangeHom_snd :
    isomBaseChangeHom x y RP RQ b ≫ pullback.snd _ _ =
      isomProjection (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) := by
  unfold isomBaseChangeHom
  exact pullback.lift_snd _ _ _

/-- **Base change of the isomorphism sheaf**: the comparison morphism is an isomorphism. -/
instance isIso_isomBaseChangeHom : IsIso (isomBaseChangeHom x y RP RQ b) := by
  refine fppfSheaf_isIso_of_bijective _ (fun S' => ⟨?_, ?_⟩)
  · intro α β h
    have h₁ := congrArg (· ≫ pullback.fst _ _) h
    have h₂ := congrArg (· ≫ pullback.snd _ _) h
    simp only [Category.assoc, isomBaseChangeHom_fst, isomBaseChangeHom_snd] at h₁ h₂
    apply fppfJ.yonedaEquiv.injective
    refine IsomPoint.pushBase_injective b ?_ ?_
    · have := congrArg fppfJ.yonedaEquiv h₂
      rwa [GrothendieckTopology.yonedaEquiv_comp, GrothendieckTopology.yonedaEquiv_comp] at this
    · have := congrArg fppfJ.yonedaEquiv h₁
      rwa [yonedaEquiv_comp_isomPushBase, yonedaEquiv_comp_isomPushBase] at this
  · intro γ
    set q : IsomPoint x y RP RQ S' := fppfJ.yonedaEquiv (γ ≫ pullback.fst _ _) with hq_def
    set g : S' ⟶ S := fppfJ.yonedaEquiv (γ ≫ pullback.snd _ _) with hg_def
    have hγsnd : γ ≫ pullback.snd _ _ = fppfYoneda.map g := by
      apply fppfJ.yonedaEquiv.injective
      rw [GrothendieckTopology.yonedaEquiv_yoneda_map]
    have hq : q.f = g ≫ b := by
      apply fppfYoneda.map_injective
      rw [← comp_isomProjection, fppfYoneda.map_comp, ← hγsnd, Category.assoc, Category.assoc,
        pullback.condition]
    refine ⟨fppfJ.yonedaEquiv.symm (q.pullBase b g hq), ?_⟩
    have e := Equiv.apply_symm_apply (fppfJ.yonedaEquiv : (fppfYoneda.obj S' ⟶
      isomSheaf (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b)) ≃ _)
      (q.pullBase b g hq)
    dsimp only
    apply pullback.hom_ext
    · rw [Category.assoc, isomBaseChangeHom_fst]
      apply fppfJ.yonedaEquiv.injective
      rw [yonedaEquiv_comp_isomPushBase, e, IsomPoint.pushBase_pullBase]
    · rw [Category.assoc, isomBaseChangeHom_snd, hγsnd]
      apply fppfJ.yonedaEquiv.injective
      rw [GrothendieckTopology.yonedaEquiv_comp, e,
        GrothendieckTopology.yonedaEquiv_yoneda_map]
      rfl

/-- **Base change of the isomorphism sheaf** (blueprint D2a.4): the isomorphism sheaf of the
base-changed torsors is the base change of the isomorphism sheaf, over `S`. -/
noncomputable def isomBaseChangeIso :
    isomSheaf (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) ≅
      pullback (isomProjection x y RP RQ) (fppfYoneda.map b) :=
  asIso (isomBaseChangeHom x y RP RQ b)

/-- The base-change isomorphism is `isomBaseChangeHom`. -/
@[simp]
theorem isomBaseChangeIso_hom :
    (isomBaseChangeIso x y RP RQ b).hom = isomBaseChangeHom x y RP RQ b :=
  rfl

/-- The base-change isomorphism lies over `S`. -/
theorem isomBaseChangeIso_hom_snd :
    (isomBaseChangeIso x y RP RQ b).hom ≫ pullback.snd _ _ =
      isomProjection (pullbackObj b x) (pullbackObj b y) (RP.pullbackRep b) (RQ.pullbackRep b) := by
  rw [isomBaseChangeIso_hom, isomBaseChangeHom_snd]

end BaseChange

/-! ### The classifying stack `BG`

`classifyingStack G` is by definition `quotientStack G (pointAction G)`; the following
restatements fix the elaboration for consumers working with `BG` directly. -/

section Classifying

variable (x y : ActionTorsor G (AlgebraicSpaceAction.pointAction G) T)
  (RP : TorsorRepresentation x.toFppfTorsor) (RQ : TorsorRepresentation y.toFppfTorsor)

/-- `isomPointEquiv` for the classifying stack `BG`: points of the isomorphism sheaf are pairs
of a test map and an isomorphism in the fibre of `BG`. -/
noncomputable def isomPointEquivClassifying (S : Scheme.{u}) :
    IsomPoint x y RP RQ S ≃
      Σ f : S ⟶ T, ((stackPullback (classifyingStack G) f).obj x ≅
        (stackPullback (classifyingStack G) f).obj y) :=
  isomPointEquiv x y RP RQ S

/-- The test map of the pair attached to a point (for `BG`). -/
@[simp]
theorem isomPointEquivClassifying_apply_fst (S : Scheme.{u}) (p : IsomPoint x y RP RQ S) :
    (isomPointEquivClassifying x y RP RQ S p).1 = p.f :=
  rfl

/-- Naturality of `isomPointEquivClassifying` in the test scheme, in terms of the
pseudofunctorial pullback of `BG` (the form consumed by `DiagonalClassifies`). -/
theorem isomPointEquivClassifying_restrict {S S' : Scheme.{u}} (g : S' ⟶ S)
    (p : IsomPoint x y RP RQ S) :
    (isomPointEquivClassifying x y RP RQ S' (p.restrict g)).2 =
      stackPullbackIso (classifyingStack G) g p.f (isomPointEquivClassifying x y RP RQ S p).2 :=
  isomPointEquiv_restrict x y RP RQ g p

/-- Naturality of `isomPointEquivClassifying.symm` (for `BG`). -/
theorem isomPointEquivClassifying_symm_restrict {S S' : Scheme.{u}} (g : S' ⟶ S) (f : S ⟶ T)
    (e : (stackPullback (classifyingStack G) f).obj x ≅
      (stackPullback (classifyingStack G) f).obj y) :
    ((isomPointEquivClassifying x y RP RQ S).symm ⟨f, e⟩).restrict g =
      (isomPointEquivClassifying x y RP RQ S').symm
        ⟨g ≫ f, stackPullbackIso (classifyingStack G) g f e⟩ :=
  isomPointEquiv_symm_restrict x y RP RQ g f e

end Classifying

end ActionTorsor

end GromovWitten.AlgebraicGeometry
