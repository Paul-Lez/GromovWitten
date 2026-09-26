/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.QuotientTorsorContractionCoherence
import GromovWitten.AlgebraicGeometry.Cones.Stack
import GromovWitten.AlgebraicGeometry.Stacks.QuotientStackAtlas

/-!
# The affine cone quotient `[C/E]` as a cone stack

This file assembles the affine cone quotient `[C/E]` of `Cones/QuotientTorsor.lean` into a
`GromovWitten.AlgebraicGeometry.ConeStack` over the represented stack of the base `Spec R`:
`ConeQuotient.coneQuotientStack`.  The total stack is
`ActionTorsor.quotientStack (vectorBundleGroup σ) (coneActionSpace A bas)`, the contraction is the
unconditional `ConeQuotient.contractionFunctor` of `Cones/QuotientTorsorContraction.lean`, and every
`ConeStack` field is constructed here or in `Cones/QuotientTorsorContractionCoherence.lean`.

## The descent of the base point

The construction that was missing for the assembly (see the "What is not done" section of
`Cones/QuotientTorsorContractionCoherence.lean`) is the *descent of the base point*: an object `P`
of `[C/E]` over a test scheme `T` is a torsor `P.P` under the vector bundle group `E` with an
equivariant map `P.target : P.P ⟶ C`, and the composite `P.P ⟶ C ⟶ Spec R` is `E`-invariant, hence
should descend to a `T`-point of `Spec R`.  It is obtained here without any new descent argument,
by reading it off the contraction by the scalar `0`: that contraction lands in *trivialised*
objects (`ConeQuotient.contractionFunctorZeroIso`), so it provides a canonical `T`-point
`ConeQuotient.zeroPoint A bas P : T ⟶ C` of the cone -- the vertex over the base point -- whose
composite with the structure morphism `ConeQuotient.coneBase R S : C ⟶ Spec R` is the base point
`ConeQuotient.basePoint A bas P : T ⟶ Spec R`.  Its characteristic property
`ConeQuotient.projection_comp_basePoint` follows from
`TorsorPushoutRel.trivialHomSection_comp_targetMap` together with
`TorsorPushoutRel.conePt_scaleConeScheme_comp_algebraMap` ("the contraction does not move the point
of the base"), and it *determines* the base point because the projection of an fppf torsor is an
epimorphism of fppf sheaves (`ConeQuotient.hom_ext_of_projection`, proved from the trivialising
cover of the torsor).  Uniqueness is what makes the base point invariant under isomorphisms of
objects (`ConeQuotient.basePoint_congr`) and compatible with base change
(`ConeQuotient.basePoint_pullbackObj`), hence functorial.

## Coherence for free

Every fibre of the base `representedStack (Spec R)` is a discrete groupoid, so all hom-types of the
base fibres are subsingletons.  Consequently the coherence laws of a stack morphism *into* the base
and of a 2-isomorphism between two such are automatic.  The abstract helpers
`ConeQuotient.mkStrongTransOfSubsingleton`, `ConeQuotient.natIsoOfObjEq` and
`ConeQuotient.discreteFunctorTo` isolate that argument at abstract (pseudo)functors: instantiating
them at a concrete fibre then costs a single definitional check, whereas discharging the same laws
inside an anonymous structure literal makes the kernel unfold the fibre and time out.  This is the
same design as `Stacks/StrongTransOfDiscrete.lean` and `Stacks/Inertia.lean`.

## Main declarations

* `ConeQuotient.hom_ext_of_projection`: the projection `P.P ⟶ y(T)` of an fppf torsor is an
  epimorphism of fppf sheaves.
* `ConeQuotient.coneBase R S : coneScheme S ⟶ coneScheme R`, the structure morphism of the affine
  cone over its base, and `ConeQuotient.coneVertex ε : coneScheme R ⟶ coneScheme S`, the vertex
  section attached to an augmentation, with `ConeQuotient.coneVertex_comp_coneBase`.
* `ConeQuotient.basePoint A bas P : T ⟶ coneScheme R`, the descended base point, with
  `projection_comp_basePoint`, `basePoint_unique`, `basePoint_congr`, `basePoint_pullbackObj` and
  `basePoint_trivialWithPoint`.
* **`ConeQuotient.baseProjection A bas : StackHom (coneTotalStack A bas) (coneBaseStack R)`** --
  the projection `[C/E] ⟶ Spec R`.
* **`ConeQuotient.coneVertexHom A bas ε : StackHom (coneBaseStack R) (coneTotalStack A bas)`** --
  the vertex section, the composite of the morphism of represented stacks
  `ConeQuotient.coneMapStackHom (coneVertex ε)` with `ActionTorsor.atlasMap`.
* **`ConeQuotient.coneVertexProjectionIso`** -- the vertex is a section of the projection.
* **`ConeQuotient.coneContractionProjectionIso`** -- the projection law of the contraction, from
  `ConeQuotient.basePoint_contractionFunctor` (the contraction does not move the base point).
* **`ConeQuotient.coneContractionVertexIso`** -- the vertex law of the contraction.
* **`ConeQuotient.coneContractionZeroIsoApp`** -- the vanishing law at the level of objects, from
  `ConeQuotient.zeroSection_eq` (the vertex over the base point of an object is the vertex section
  applied to its base point) and `ConeQuotient.lift_scaleConeScheme_zero`.
* **`ConeQuotient.coneContractionZeroIso`** -- the vanishing law of the contraction as a natural
  isomorphism, the transport of `ConeQuotient.zeroVertexIso_naturality` along
  `ConeQuotient.trivialWithPoint_vertexPoint_eq`.
* **`ConeQuotient.coneQuotientStack`** -- the `ConeStack` itself, with
  `ConeQuotient.coneQuotientStackOfZeroIso` the auxiliary form parametrised by the vanishing law.
* `ConeQuotient.trivialHomSection_comp_pushMap` (with `pushMap_trivialDatum`): **the canonical
  section of a pointwise trivial relative pushout is natural in the torsor**, the missing
  ingredient for the naturality of the vanishing law; and
  `ConeQuotient.sectionMap_comp_iso_hom`: the trivialisation attached to a section is natural.

## The vanishing law, and the two category instances on a fibre of `[C/E]`

The vanishing law `contractionFunctor A bas 0 ≅ projection ⋙ vertex` is the delicate field, and the
reason is worth recording.  Its content is
`ConeQuotient.zeroVertexIso` -- the isomorphism of the contraction by `0` of an object with the
trivialised object of the vertex over its base point -- together with its naturality
`ConeQuotient.zeroVertexIso_naturality`, which rests on
`ConeQuotient.trivialHomSection_comp_pushMap` (the canonical section of a pointwise trivial
relative pushout is natural in the torsor, the statement
`Cones/QuotientTorsorContractionCoherence.lean` does not provide),
`ConeQuotient.zeroHomSection_comp_zeroTrivialisation_inv` and
`ConeQuotient.trivialSection_comp_eqToHom`; the identification of that trivialised object with the
value of `projection ⋙ vertex` is `ConeQuotient.trivialWithPoint_vertexPoint_eq`.

Transporting the naturality along that identification is pure `eqToHom` bookkeeping, but it cannot
be done by rewriting.  The domain of `contractionFunctor A bas 0` carries the category instance
`ActionTorsor.instCategory`, whereas the domain of
`StackHom.appFunctor (baseProjection A bas) T ⋙ StackHom.appFunctor (coneVertexHom A bas ε) T`
carries `(StackFiber (coneTotalStack A bas) T).str`.  The two are definitionally equal, so every
statement relating them elaborates, but such a statement is *not* type-correct at `implicit`
transparency, so `rw` and `simp` cannot be used on it at all (they fail with "did not find an
occurrence of the pattern").  The way through is to keep every rewriting step inside a lemma about
an *abstract* category -- here `ConeQuotient.comp_assoc_paste` and
`ConeQuotient.natIsoOfDiscreteFactor`, whose `Category` instances are arguments -- and to
instantiate those lemmas by ordinary term application, which is checked at default transparency and
costs a handful of projection reductions instead of an unfolding of the fibre.  This is the same
design as the "coherence for free" helpers above, and
`ConeQuotient.natIsoOfDiscreteFactor` additionally uses the fact that the middle fibre
`StackFiber (coneBaseStack R) T` is discrete, so that `projection ⋙ vertex` acts on arrows by the
identification of their endpoints (`ConeQuotient.projVertex_map_eq_eqToHom` is the same fact,
proved directly at the concrete fibre).

## Not done

No claim is made that `[C/E]` is an *algebraic* stack, nor that the cone stack is coherent in the
sense of `ConeStack.IsCoherent` (`Cones/StackCoherence.lean`).
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace ConeQuotient

/-! ### The projection of an fppf torsor is an epimorphism -/

section Epi

variable {G : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}

/-- **The projection of an fppf torsor is an epimorphism of fppf sheaves**: two morphisms out of
`y(T)` which agree after composition with `P.projection` are equal, because the trivialising
cover of `P` generates an fppf covering sieve of `T` and factors through `P.P`. -/
theorem hom_ext_of_projection {B : FppfSheaf.{u}} (P : FppfTorsor G T)
    {u v : fppfYoneda.obj T ⟶ B} (h : P.projection ≫ u = P.projection ≫ v) : u = v := by
  refine FppfSheaf.hom_ext_of_cover (𝟙 (fppfYoneda.obj T))
    (TorsorPushout.coverSieve_mem P) ?_
  intro X g hg
  obtain ⟨c, rfl⟩ := TorsorPushout.exists_factor_of_coverSieve hg
  have h1 : fppfYoneda.map (c ≫ P.locallyTrivial.cover) =
      fppfYoneda.map c ≫ P.locallyTrivial.localLift ≫ P.projection := by
    rw [P.locallyTrivial.localLift_over, ← CategoryTheory.Functor.map_comp]
  have hy : fppfYoneda.map (c ≫ P.locallyTrivial.cover) ≫ u =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) ≫ v := by
    rw [h1]
    simp only [Category.assoc]
    rw [h]
  have hcond := Limits.pullback.condition (f := (𝟙 (fppfYoneda.obj T)))
    (g := fppfYoneda.map (c ≫ P.locallyTrivial.cover))
  rw [Category.comp_id] at hcond
  rw [hcond, Category.assoc, Category.assoc, hy]

end Epi

/-! ### The structure morphism of the affine cone over its base -/

section ConeBase

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- **The structure morphism `C = Spec S ⟶ Spec R` of the affine cone over its base.**  It is
the morphism of affine schemes attached to `algebraMap R S`. -/
noncomputable def coneBase : coneScheme S ⟶ coneScheme R :=
  ofConePt (S := R) ((gammaMap S).comp (algebraMap R S))

variable {R S}

/-- The ring map of a point of the affine cone, in terms of global sections. -/
theorem conePt_eq {X : Scheme.{u}} (f : X ⟶ coneScheme S) :
    conePt f = (f.appTop).hom.comp (gammaMap S) := by
  rw [conePt, pt, gammaMap]
  rfl

/-- **The ring map of a point of the cone composed with the structure morphism over the base**
is the ring map of the point restricted along `algebraMap R S`. -/
theorem conePt_comp_coneBase {X : Scheme.{u}} (f : X ⟶ coneScheme S) :
    conePt (S := R) (f ≫ coneBase R S) = (conePt f).comp (algebraMap R S) := by
  rw [conePt_comp, coneBase, conePt_ofConePt, ← RingHom.comp_assoc, ← conePt_eq]

/-- **Two points of the affine cone lie over the same point of the base** as soon as their ring
maps agree on `R`. -/
theorem comp_coneBase_congr {X : Scheme.{u}} {f g : X ⟶ coneScheme S}
    (h : (conePt f).comp (algebraMap R S) = (conePt g).comp (algebraMap R S)) :
    f ≫ coneBase R S = g ≫ coneBase R S :=
  conePt_injective (by rw [conePt_comp_coneBase, conePt_comp_coneBase, h])

end ConeBase

/-! ### The base point of an object of `[C/E]` -/

section BasePoint

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T T' : Scheme.{u}}
variable (A : ConeAction R S F) (bas : Module.Basis σ R F)

/-- The structure morphism of the cone over its base, as a morphism of fppf sheaves out of the
cone action space. -/
noncomputable abbrev coneBaseHom :
    (coneActionSpace A bas).space.toSheaf ⟶ fppfYoneda.obj (coneScheme R) :=
  fppfYoneda.map (coneBase R S)

/-- The scalar homomorphism at the scalar `0` is pointwise trivial. -/
theorem scaleRelMonHom_zero_pt_one {Z : FppfSheaf.{u}}
    (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ (vectorBundleGroup σ).space.toSheaf) :
    (TorsorPushoutRel.scaleRelMonHom σ T (0 : Γ(T, ⊤))).pt b x = 1 :=
  TorsorPushoutRel.scaleRelMonHom_pt_zero b x

/-- **The vertex over the base point of an object of `[C/E]`, as a point of the cone.**  It is
the point of the cone of the trivialised object `contractionFunctor A bas 0` (see
`ConeQuotient.contractionFunctorZeroIso`). -/
noncomputable def zeroSection
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    fppfYoneda.obj T ⟶ (coneActionSpace A bas).space.toSheaf :=
  TorsorPushoutRel.trivialHomSection (TorsorPushoutRel.scaleRelMonHom σ T (0 : Γ(T, ⊤)))
      (fun b x => scaleRelMonHom_zero_pt_one b x) P.toFppfTorsor ≫
    TorsorPushoutRel.targetMap P (TorsorPushoutRel.scaleRelMonHom σ T (0 : Γ(T, ⊤)))
      (TorsorPushoutRel.coneScaleRelEquivMap A bas (0 : Γ(T, ⊤)))

/-- The vertex over the base point, as a morphism of schemes `T ⟶ C`. -/
noncomputable def zeroPoint
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) : T ⟶ coneScheme S :=
  fppfYoneda.preimage (zeroSection A bas P)

/-- The scheme morphism `zeroPoint` represents the point `zeroSection` of the cone. -/
theorem cnPt_zeroPoint (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    TorsorPushoutRel.cnPt A bas (zeroPoint A bas P) = zeroSection A bas P :=
  fppfYoneda.map_preimage _

/-- **The base point of an object of `[C/E]`**: the image under the structure morphism
`C ⟶ Spec R` of the vertex over the base point.  This is the descent to `T` of the
`E`-invariant map `P.P ⟶ C ⟶ Spec R`; see `ConeQuotient.projection_comp_basePoint`. -/
noncomputable def basePoint
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) : T ⟶ coneScheme R :=
  zeroPoint A bas P ≫ coneBase R S

/-- **The base point of an object of `[C/E]` computes the invariant map `P.P ⟶ C ⟶ Spec R`.**
This is the defining property of the descended base point. -/
theorem projection_comp_basePoint
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    P.projection ≫ fppfYoneda.map (basePoint A bas P) = P.target ≫ coneBaseHom A bas := by
  refine fppfSheaf_hom_ext ?_
  intro W p
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : W ⟶ T, fppfYoneda.map b₀ = p ≫ P.projection :=
    ⟨fppfYoneda.preimage _, fppfYoneda.map_preimage _⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : W ⟶ coneScheme S,
      TorsorPushoutRel.cnPt A bas x₀ = p ≫ P.target :=
    TorsorPushoutRel.cnPt_surjective A bas _
  have h1 := TorsorPushoutRel.trivialHomSection_comp_targetMap
    (TorsorPushoutRel.scaleRelMonHom σ T (0 : Γ(T, ⊤)))
    (fun b x => scaleRelMonHom_zero_pt_one b x)
    (TorsorPushoutRel.coneScaleRelEquivMap A bas (0 : Γ(T, ⊤))) P (p ≫ P.projection) p rfl
  have h2 := TorsorPushoutRel.coneScaleRelEquivMap_pt A bas (0 : Γ(T, ⊤)) x₀ b₀
  rw [hb₀, hx₀] at h2
  have h3 : (lift x₀ b₀ ≫ TorsorPushoutRel.scaleConeScheme A (0 : Γ(T, ⊤))) ≫ coneBase R S =
      x₀ ≫ coneBase R S :=
    comp_coneBase_congr
      (TorsorPushoutRel.conePt_scaleConeScheme_comp_algebraMap A (0 : Γ(T, ⊤)) x₀ b₀)
  calc p ≫ P.projection ≫ fppfYoneda.map (basePoint A bas P)
      = ((p ≫ P.projection) ≫ zeroSection A bas P) ≫ coneBaseHom A bas := by
        rw [basePoint, CategoryTheory.Functor.map_comp, ← cnPt_zeroPoint A bas P]
        simp only [Category.assoc]
        rfl
    _ = TorsorPushoutRel.cnPt A bas (lift x₀ b₀ ≫
          TorsorPushoutRel.scaleConeScheme A (0 : Γ(T, ⊤))) ≫ coneBaseHom A bas :=
        congrArg (fun q => q ≫ coneBaseHom A bas) (h1.trans h2)
    _ = (p ≫ P.target) ≫ coneBaseHom A bas := by
        have e : fppfYoneda.map (lift x₀ b₀ ≫
              TorsorPushoutRel.scaleConeScheme A (0 : Γ(T, ⊤))) ≫
                fppfYoneda.map (coneBase R S) =
            fppfYoneda.map x₀ ≫ fppfYoneda.map (coneBase R S) := by
          rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h3]
        rw [← hx₀]
        exact e
    _ = p ≫ P.target ≫ coneBaseHom A bas := Category.assoc _ _ _

/-- **Uniqueness of the base point**: any `T`-point of `Spec R` through which the invariant map
`P.P ⟶ C ⟶ Spec R` factors is the base point. -/
theorem basePoint_unique
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) (t : T ⟶ coneScheme R)
    (h : P.projection ≫ fppfYoneda.map t = P.target ≫ coneBaseHom A bas) :
    t = basePoint A bas P :=
  fppfYoneda.map_injective
    (hom_ext_of_projection P.toFppfTorsor (h.trans (projection_comp_basePoint A bas P).symm))

/-- **The base point is invariant under isomorphisms of objects of `[C/E]`.** -/
theorem basePoint_congr {P Q : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T}
    (f : P ⟶ Q) : basePoint A bas P = basePoint A bas Q := by
  refine basePoint_unique A bas Q (basePoint A bas P) ?_
  refine (cancel_epi f.iso.hom).1 ?_
  rw [← Category.assoc, f.over, ← Category.assoc, f.target]
  exact projection_comp_basePoint A bas P

/-- **The base point is compatible with base change.** -/
theorem basePoint_pullbackObj (b : T' ⟶ T)
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    basePoint A bas (ActionTorsor.pullbackObj b P) = b ≫ basePoint A bas P := by
  refine (basePoint_unique A bas _ _ ?_).symm
  have hc := Limits.pullback.condition (f := P.projection) (g := fppfYoneda.map b)
  rw [CategoryTheory.Functor.map_comp]
  change Limits.pullback.snd P.projection (fppfYoneda.map b) ≫
      fppfYoneda.map b ≫ fppfYoneda.map (basePoint A bas P) =
    (Limits.pullback.fst P.projection (fppfYoneda.map b) ≫ P.target) ≫ coneBaseHom A bas
  rw [← Category.assoc, ← hc, Category.assoc, projection_comp_basePoint, Category.assoc]

end BasePoint

/-! ### Strong transformations into a stack with discrete fibres -/

section AbstractStrongTrans

open CategoryTheory.Bicategory

universe w₀ w₁ v₁ u₁

/-- **A strong transformation into a `Cat`-valued pseudofunctor whose fibres have subsingleton
hom-types**, from the fibrewise functors and their base-change comparisons alone: the two
remaining coherence laws of a strong transformation are then automatic.  Stated at abstract
pseudofunctors, exactly as
`CategoryTheory.Pseudofunctor.StrongTrans.mkCatOfComponents` and for the same reason -- the kernel
must never be asked to unfold a concrete fibre. -/
def mkStrongTransOfSubsingleton {B : Type u₁} [Bicategory.{w₁, v₁} B] [IsLocallyDiscrete B]
    {F X : Pseudofunctor B Cat.{w₀, w₀}}
    (app : ∀ a : B, F.obj a ⟶ X.obj a)
    (naturality : ∀ {a b : B} (f : a ⟶ b), F.map f ≫ app b ≅ app a ≫ X.map f)
    (hs : ∀ (a : B) (x y : (X.obj a : Type w₀)), Subsingleton (x ⟶ y)) :
    Pseudofunctor.StrongTrans F X :=
  Pseudofunctor.StrongTrans.mkCatOfComponents app naturality
    (fun a _ => (hs a _ _).elim _ _) (fun {_ _ c} _ _ _ => (hs c _ _).elim _ _)

/-- The value on objects of a vertical composite of stack morphisms.  Stated at abstract stacks so
that it is a cheap `rfl`. -/
theorem vcomp_appFunctor_obj {X Y Z : FppfStack.{u}} (f : StackHom X Y) (g : StackHom Y Z)
    (T : Scheme.{u}) (x : StackFiber X T) :
    (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) T).obj x =
      (StackHom.appFunctor g T).obj ((StackHom.appFunctor f T).obj x) :=
  rfl

end AbstractStrongTrans

/-! ### Functors into a discrete category -/

section DiscreteTarget

universe w w' v' v''

/-- **An isomorphism of functors into a category whose hom-types are subsingletons**, from an
equality of the values on objects.  Stated for abstract categories, so that instantiating it at a
fibre of a represented stack costs a single defeq check. -/
def natIsoOfObjEq {C : Type v'} [Category.{w} C] {D : Type v''} [Category.{w'} D]
    {F G : C ⥤ D} (h : ∀ x, F.obj x = G.obj x)
    (hs : ∀ x y : D, Subsingleton (x ⟶ y)) : F ≅ G where
  hom := { app := fun x => eqToHom (h x), naturality := fun _ _ _ => (hs _ _).elim _ _ }
  inv := { app := fun x => eqToHom (h x).symm, naturality := fun _ _ _ => (hs _ _).elim _ _ }
  hom_inv_id := by
    apply NatTrans.ext
    funext x
    exact (hs _ _).elim _ _
  inv_hom_id := by
    apply NatTrans.ext
    funext x
    exact (hs _ _).elim _ _

/-- **A functor into a discrete category**, from a map on objects which is constant on
isomorphism classes.  Stated for an abstract discrete category, so that instantiating it at a
fibre of a represented stack costs a single defeq check. -/
def discreteFunctorTo {C : Type v'} [Category.{w} C] {α : Type w} (obj : C → α)
    (map : ∀ {x y : C}, (x ⟶ y) → obj x = obj y) : C ⥤ Discrete α where
  obj x := Discrete.mk (obj x)
  map f := Discrete.eqToHom (map f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The value on objects of `ConeQuotient.discreteFunctorTo`. -/
theorem discreteFunctorTo_obj {C : Type v'} [Category.{w} C] {α : Type w} (obj : C → α)
    (map : ∀ {x y : C}, (x ⟶ y) → obj x = obj y) (x : C) :
    (discreteFunctorTo obj map).obj x = Discrete.mk (obj x) :=
  rfl

end DiscreteTarget

/-! ### The projection of `[C/E]` to its base -/

section Projection

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T T' : Scheme.{u}}
variable (A : ConeAction R S F) (bas : Module.Basis σ R F)

variable (R) in
/-- **The base of the cone stack `[C/E]`**: the represented stack of `Spec R`. -/
noncomputable abbrev coneBaseStack : FppfStack.{u} :=
  representedStack (coneScheme R)

/-- **The total stack of the cone stack `[C/E]`**: the quotient stack of the affine cone by the
vector bundle group. -/
noncomputable abbrev coneTotalStack : FppfStack.{u} :=
  ActionTorsor.quotientStack (vectorBundleGroup σ) (coneActionSpace A bas)

section Subsingleton

universe w v'

variable (R) in
/-- Arrows between objects of a fibre of the base are unique: the fibres of a represented stack
are discrete.  Stated at the concrete fibre so that the (expensive) identification of that fibre
with a discrete category is performed once and for all. -/
theorem coneBaseStack_hom_subsingleton (x y : StackFiber (coneBaseStack R) T) :
    Subsingleton (x ⟶ y) :=
  Discrete.instSubsingletonDiscreteHom x y

variable (R) in
/-- Natural transformations into a fibre of the base are unique. -/
theorem coneBaseStack_natTrans_subsingleton {C : Type v'} [Category.{w} C]
    (F G : C ⥤ StackFiber (coneBaseStack R) T) : Subsingleton (F ⟶ G) :=
  ⟨fun _ _ ↦ by
    apply NatTrans.ext
    funext x
    exact (coneBaseStack_hom_subsingleton R _ _).elim _ _⟩

end Subsingleton

/-- **The projection functor of `[C/E]` over a test scheme**: an object of `[C/E]` goes to its
descended base point. -/
noncomputable def baseProjectionFunctor (T : Scheme.{u}) :
    StackFiber (coneTotalStack A bas) T ⥤ StackFiber (coneBaseStack R) T :=
  discreteFunctorTo (fun P => ULift.up (basePoint A bas P))
    (fun f => congrArg ULift.up (basePoint_congr A bas f))

/-- **The projection functor sends an object of `[C/E]` to its base point.** -/
theorem baseProjectionFunctor_obj (T : Scheme.{u})
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    (baseProjectionFunctor A bas T).obj P = Discrete.mk (ULift.up (basePoint A bas P)) :=
  rfl

/-- The base point of a base-changed object, as an equality of objects of the base fibre. -/
theorem baseProjectionFunctor_obj_pullback (b : T' ⟶ T)
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    (baseProjectionFunctor A bas T').obj ((stackPullback (coneTotalStack A bas) b).obj P) =
      (stackPullback (coneBaseStack R) b).obj ((baseProjectionFunctor A bas T).obj P) :=
  congrArg (fun t => (Discrete.mk (ULift.up t) : StackFiber (coneBaseStack R) T'))
    (basePoint_pullbackObj A bas b P)

/-- The base-change comparison of the projection functors: the base point of a base-changed
object is the base-changed base point (`ConeQuotient.basePoint_pullbackObj`). -/
noncomputable def baseProjectionNaturalityIso (b : T' ⟶ T) :
    stackPullback (coneTotalStack A bas) b ⋙ baseProjectionFunctor A bas T' ≅
      baseProjectionFunctor A bas T ⋙ stackPullback (coneBaseStack R) b :=
  natIsoOfObjEq (baseProjectionFunctor_obj_pullback A bas b) (coneBaseStack_hom_subsingleton R)

/-- **The projection `[C/E] ⟶ Spec R` of the affine cone quotient to its base.**  On a test
scheme it sends an object to its descended base point `ConeQuotient.basePoint`; the coherence
laws are automatic because the fibres of the base are discrete. -/
noncomputable def baseProjection : StackHom (coneTotalStack A bas) (coneBaseStack R) :=
  mkStrongTransOfSubsingleton
    (F := (coneTotalStack A bas).toPseudofunctor)
    (X := (coneBaseStack R).toPseudofunctor)
    (fun a => (baseProjectionFunctor A bas a.as.unop).toCatHom)
    (fun {_ _} f => Cat.Hom.isoMk (baseProjectionNaturalityIso A bas f.as.unop))
    (fun a x y => coneBaseStack_hom_subsingleton R (T := a.as.unop) x y)

/-- The value of the projection on a test scheme is the base-point functor. -/
theorem baseProjection_app (T : Scheme.{u}) :
    (baseProjection A bas).app ⟨Opposite.op T⟩ = (baseProjectionFunctor A bas T).toCatHom :=
  rfl

/-- **The projection sends an object of `[C/E]` to its base point.** -/
theorem baseProjection_app_obj (T : Scheme.{u})
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    (StackHom.appFunctor (baseProjection A bas) T).obj P =
      Discrete.mk (ULift.up (basePoint A bas P)) :=
  rfl

end Projection

/-! ### The vertex section of `[C/E]` -/

section Vertex

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T T' : Scheme.{u}}
variable (A : ConeAction R S F) (bas : Module.Basis σ R F)

/-- The ring map of the tautological point of the affine cone. -/
theorem conePt_id : conePt (𝟙 (coneScheme S)) = gammaMap S := by
  rw [conePt_eq, _root_.AlgebraicGeometry.Scheme.Hom.id_appTop, CommRingCat.hom_id,
    RingHom.id_comp]

/-- **The vertex section `Spec R ⟶ C` of the affine cone** attached to an augmentation
`ε : S →ₐ[R] R`. -/
noncomputable def coneVertex (ε : S →ₐ[R] R) : coneScheme R ⟶ coneScheme S :=
  ofConePt ((gammaMap R).comp (ε : S →+* R))

/-- **The vertex section is a section of the structure morphism of the cone.** -/
theorem coneVertex_comp_coneBase (ε : S →ₐ[R] R) :
    coneVertex ε ≫ coneBase R S = 𝟙 (coneScheme R) := by
  have hε : (ε : S →+* R).comp (algebraMap R S) = RingHom.id R :=
    RingHom.ext fun r => ε.commutes r
  refine conePt_injective ?_
  rw [conePt_comp_coneBase, coneVertex, conePt_ofConePt, RingHom.comp_assoc, hε,
    RingHom.comp_id, conePt_id]

/-- **The base point of a trivialised object of `[C/E]`** is the image of its point of the cone
under the structure morphism over the base.  This is where the descended base point is computed
in closed form. -/
theorem basePoint_trivialWithPoint (x : T ⟶ coneScheme S) :
    basePoint A bas (trivialWithPoint (TorsorPushoutRel.cnPt A bas x)) = x ≫ coneBase R S := by
  refine fppfYoneda.map_injective ?_
  have h : trivialSection (TorsorPushoutRel.cnPt A bas x) ≫
        (trivialWithPoint (TorsorPushoutRel.cnPt A bas x)).projection ≫
          fppfYoneda.map (basePoint A bas (trivialWithPoint (TorsorPushoutRel.cnPt A bas x))) =
      trivialSection (TorsorPushoutRel.cnPt A bas x) ≫
        (trivialWithPoint (TorsorPushoutRel.cnPt A bas x)).target ≫ coneBaseHom A bas :=
    congrArg (fun q => trivialSection (TorsorPushoutRel.cnPt A bas x) ≫ q)
      (projection_comp_basePoint A bas (trivialWithPoint (TorsorPushoutRel.cnPt A bas x)))
  rw [← Category.assoc, ← Category.assoc, trivialSection_projection,
    trivialSection_comp_trivialTarget, Category.id_comp] at h
  rw [h, CategoryTheory.Functor.map_comp]
  rfl

/-- The fibrewise functor of the morphism of represented stacks induced by a morphism of affine
schemes over the base. -/
noncomputable def coneMapFunctor (v : coneScheme R ⟶ coneScheme S) (T : Scheme.{u}) :
    StackFiber (coneBaseStack R) T ⥤ StackFiber (coneBaseStack S) T :=
  Discrete.functor (fun (g : ULift (T ⟶ coneScheme R)) =>
    (Discrete.mk (ULift.up (g.down ≫ v)) : StackFiber (coneBaseStack S) T))

/-- The base-change comparison of `ConeQuotient.coneMapFunctor`: composition of scheme morphisms
is associative. -/
noncomputable def coneMapNaturalityIso (v : coneScheme R ⟶ coneScheme S) (b : T' ⟶ T) :
    stackPullback (coneBaseStack R) b ⋙ coneMapFunctor v T' ≅
      coneMapFunctor v T ⋙ stackPullback (coneBaseStack S) b :=
  Discrete.natIso (fun x => eqToIso (congrArg
    (fun t => (Discrete.mk (ULift.up t) : StackFiber (coneBaseStack S) T'))
    (Category.assoc b x.as.down v)))

/-- **The morphism of represented stacks induced by a morphism of affine schemes.** -/
noncomputable def coneMapStackHom (v : coneScheme R ⟶ coneScheme S) :
    StackHom (coneBaseStack R) (coneBaseStack S) :=
  mkStrongTransOfSubsingleton
    (F := (coneBaseStack R).toPseudofunctor)
    (X := (coneBaseStack S).toPseudofunctor)
    (fun a => (coneMapFunctor v a.as.unop).toCatHom)
    (fun {_ _} f => Cat.Hom.isoMk (coneMapNaturalityIso v f.as.unop))
    (fun a x y => coneBaseStack_hom_subsingleton S (T := a.as.unop) x y)

omit [Algebra R S] [AddCommGroup F] [Module R F] in
/-- The value of `ConeQuotient.coneMapStackHom` on a `T`-point of the base. -/
theorem coneMapStackHom_app_obj (v : coneScheme R ⟶ coneScheme S) (T : Scheme.{u})
    (g : T ⟶ coneScheme R) :
    (StackHom.appFunctor (coneMapStackHom v) T).obj (Discrete.mk (ULift.up g)) =
      Discrete.mk (ULift.up (g ≫ v)) :=
  rfl

/-- **The vertex section `Spec R ⟶ [C/E]` of the affine cone quotient**: the trivial `E`-torsor
with the vertex of the cone over the given point of the base, obtained by composing the morphism
of represented stacks of the vertex section of the cone with the atlas map of the quotient
stack. -/
noncomputable def coneVertexHom (ε : S →ₐ[R] R) :
    StackHom (coneBaseStack R) (coneTotalStack A bas) :=
  Pseudofunctor.StrongTrans.vcomp (coneMapStackHom (coneVertex ε))
    (ActionTorsor.atlasMap (vectorBundleGroup σ) (coneActionSpace A bas) :
      StackHom (coneBaseStack S) (coneTotalStack A bas))

/-- The vertex section sends a `T`-point `g` of the base to the trivial torsor with point the
vertex over `g`. -/
theorem coneVertexHom_app_obj (ε : S →ₐ[R] R) (T : Scheme.{u}) (g : T ⟶ coneScheme R) :
    (StackHom.appFunctor (coneVertexHom A bas ε) T).obj (Discrete.mk (ULift.up g)) =
      trivialWithPoint (TorsorPushoutRel.cnPt A bas (g ≫ coneVertex ε)) := by
  refine Eq.trans (vcomp_appFunctor_obj (coneMapStackHom (coneVertex ε))
    (ActionTorsor.atlasMap (vectorBundleGroup σ) (coneActionSpace A bas) :
      StackHom (coneBaseStack S) (coneTotalStack A bas)) T
    (Discrete.mk (ULift.up g) : StackFiber (coneBaseStack R) T)) ?_
  refine Eq.trans (congrArg
    (StackHom.appFunctor (ActionTorsor.atlasMap (vectorBundleGroup σ)
      (coneActionSpace A bas) : StackHom (coneBaseStack S) (coneTotalStack A bas)) T).obj
    (coneMapStackHom_app_obj (coneVertex ε) T g)) ?_
  exact congrArg trivialWithPoint (TorsorPushout.yonedaEquiv_symm_map (g ≫ coneVertex ε))

/-- **The vertex section is a section of the projection of `[C/E]`**, at the level of objects of
the fibres. -/
theorem basePoint_coneVertexHom_obj (ε : S →ₐ[R] R) (T : Scheme.{u}) (g : T ⟶ coneScheme R) :
    (StackHom.appFunctor (baseProjection A bas) T).obj
        ((StackHom.appFunctor (coneVertexHom A bas ε) T).obj (Discrete.mk (ULift.up g))) =
      Discrete.mk (ULift.up g) := by
  rw [coneVertexHom_app_obj, baseProjection_app_obj, basePoint_trivialWithPoint,
    Category.assoc, coneVertex_comp_coneBase, Category.comp_id]

end Vertex

/-! ### The vertex is a section of the projection -/

section VertexSection

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T T' : Scheme.{u}}
variable (A : ConeAction R S F) (bas : Module.Basis σ R F)

/-- The comparison of `vertex ≫ projection` with the identity of the base, on a test scheme. -/
noncomputable def vertexProjectionNatIso (ε : S →ₐ[R] R) (T : Scheme.{u}) :
    StackHom.appFunctor (coneVertexHom A bas ε) T ⋙
        StackHom.appFunctor (baseProjection A bas) T ≅
      𝟭 (StackFiber (coneBaseStack R) T) :=
  Discrete.natIso (fun x => eqToIso (basePoint_coneVertexHom_obj A bas ε T x.as.down))

/-- **The vertex section of `[C/E]` is a genuine section of the projection to the base.** -/
noncomputable def coneVertexProjectionIso (ε : S →ₐ[R] R) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp (coneVertexHom A bas ε) (baseProjection A bas))
      (Pseudofunctor.StrongTrans.id (coneBaseStack R).toPseudofunctor) where
  hom :=
    { app := fun a => NatTrans.toCatHom₂ (vertexProjectionNatIso A bas ε a.as.unop).hom
      naturality := fun _ => by
        apply Cat.Hom₂.ext
        exact (coneBaseStack_natTrans_subsingleton R _ _).elim _ _ }
  inv :=
    { app := fun a => NatTrans.toCatHom₂ (vertexProjectionNatIso A bas ε a.as.unop).inv
      naturality := fun _ => by
        apply Cat.Hom₂.ext
        exact (coneBaseStack_natTrans_subsingleton R _ _).elim _ _ }
  hom_inv_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    apply Cat.Hom₂.ext
    exact (coneBaseStack_natTrans_subsingleton R _ _).elim _ _
  inv_hom_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    apply Cat.Hom₂.ext
    exact (coneBaseStack_natTrans_subsingleton R _ _).elim _ _

end VertexSection

/-! ### The contraction is over the base -/

section ContractionProjection

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T T' : Scheme.{u}}
variable (A : ConeAction R S F) (bas : Module.Basis σ R F)

/-- The contraction by the scalar `0` does not move the base point. -/
theorem basePoint_contractionFunctor_zero
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    basePoint A bas ((contractionFunctor A bas (0 : Γ(T, ⊤))).obj P) = basePoint A bas P := by
  have h := basePoint_trivialWithPoint A bas (zeroPoint A bas P)
  rw [cnPt_zeroPoint] at h
  exact (basePoint_congr A bas (contractionFunctorZeroIso A bas P).hom).symm.trans h

/-- **The contraction of `[C/E]` does not move the base point.**  This is the projection law of
the contraction, obtained from the vanishing law and the multiplicativity of the contraction. -/
theorem basePoint_contractionFunctor (r : Γ(T, ⊤))
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    basePoint A bas ((contractionFunctor A bas r).obj P) = basePoint A bas P := by
  have h1 := basePoint_contractionFunctor_zero A bas ((contractionFunctor A bas r).obj P)
  have h2 := basePoint_congr A bas ((contractionFunctorMulIso A bas (0 : Γ(T, ⊤)) r).hom.app P)
  rw [zero_mul] at h2
  exact h1.symm.trans (h2.symm.trans (basePoint_contractionFunctor_zero A bas P))

/-- **The projection law of the contraction of `[C/E]`**: contracting by a scalar does not change
the point of the base. -/
noncomputable def coneContractionProjectionIso (r : Γ(T, ⊤)) :
    contractionFunctor A bas r ⋙ StackHom.appFunctor (baseProjection A bas) T ≅
      StackHom.appFunctor (baseProjection A bas) T :=
  natIsoOfObjEq
    (fun P => congrArg
      (fun t => (Discrete.mk (ULift.up t) : StackFiber (coneBaseStack R) T))
      (basePoint_contractionFunctor A bas r P))
    (coneBaseStack_hom_subsingleton R)

end ContractionProjection

/-! ### The vertex is fixed by the contraction -/

section ContractionVertex

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T T' : Scheme.{u}}
variable (A : ConeAction R S F) (bas : Module.Basis σ R F)

/-- The ring map of a point of the vertex of the cone. -/
theorem conePt_coneVertex (ε : S →ₐ[R] R) {X : Scheme.{u}} (g : X ⟶ coneScheme R) :
    conePt (g ≫ coneVertex ε) = (conePt (S := R) g).comp (ε : S →+* R) := by
  rw [conePt_comp, coneVertex, conePt_ofConePt, ← RingHom.comp_assoc, ← conePt_eq]

/-- A point of the vertex of the cone factors through the vertex homomorphism. -/
theorem conePt_coneVertex_fixed (ε : S →ₐ[R] R) {X : Scheme.{u}} (g : X ⟶ coneScheme R) :
    conePt (g ≫ coneVertex ε) = (conePt (g ≫ coneVertex ε)).comp (vertexHom ε) := by
  rw [conePt_coneVertex]
  refine RingHom.ext fun s => congrArg (conePt (S := R) g) ?_
  exact (ε.commutes (ε s)).symm

/-- **Every contraction of `[C/E]` fixes a point of the vertex of the cone.** -/
theorem coneScale_pt_coneVertex {ε : S →ₐ[R] R} (hv : GradedCone.IsConeVertex A.coaction ε)
    (r : Γ(T, ⊤)) (g : T ⟶ coneScheme R) :
    (TorsorPushoutRel.coneScaleRelEquivMap A bas r).pt (𝟙 (fppfYoneda.obj T))
        (TorsorPushoutRel.cnPt A bas (g ≫ coneVertex ε)) =
      TorsorPushoutRel.cnPt A bas (g ≫ coneVertex ε) := by
  rw [TorsorPushoutRel.coneScaleRelEquivMap_pt_id]
  refine congrArg (fun z => TorsorPushoutRel.cnPt A bas z) (conePt_injective ?_)
  rw [conePt_ofConePt]
  conv_lhs => rw [conePt_coneVertex_fixed ε g]
  rw [scaleRing_vertexHom A hv]
  exact (conePt_coneVertex_fixed ε g).symm

/-- **The vertex law of the contraction of `[C/E]`**: the vertex section is fixed by every
contraction. -/
noncomputable def coneContractionVertexIso {ε : S →ₐ[R] R}
    (hv : GradedCone.IsConeVertex A.coaction ε) (r : Γ(T, ⊤)) :
    StackHom.appFunctor (coneVertexHom A bas ε) T ⋙ contractionFunctor A bas r ≅
      StackHom.appFunctor (coneVertexHom A bas ε) T :=
  Discrete.natIso (fun x =>
    eqToIso (congrArg (contractionFunctor A bas r).obj
        (coneVertexHom_app_obj A bas ε T x.as.down)) ≪≫
      (contractionFunctorVertexIso A bas r
        (TorsorPushoutRel.cnPt A bas (x.as.down ≫ coneVertex ε))
        (coneScale_pt_coneVertex A bas hv r x.as.down)).symm ≪≫
      eqToIso (coneVertexHom_app_obj A bas ε T x.as.down).symm)

end ContractionVertex

/-! ### The vanishing law of the contraction -/

section ContractionZero

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T T' : Scheme.{u}}
variable (A : ConeAction R S F) (bas : Module.Basis σ R F)

/-- **Contracting a point of the cone by the scalar `0` is the vertex over its base point.** -/
theorem lift_scaleConeScheme_zero {ε : S →ₐ[R] R}
    (hv : GradedCone.IsConeVertex A.coaction ε) {W : Scheme.{u}}
    (x : W ⟶ coneScheme S) (b : W ⟶ T) :
    lift x b ≫ TorsorPushoutRel.scaleConeScheme A (0 : Γ(T, ⊤)) =
      (x ≫ coneBase R S) ≫ coneVertex ε := by
  refine conePt_injective ?_
  rw [TorsorPushoutRel.conePt_comp_scaleConeScheme, lift_fst, lift_snd, map_zero,
    scaleRing_zero A hv, conePt_coneVertex, conePt_comp_coneBase, vertexHom,
    ← RingHom.comp_assoc]

/-- **The vertex over the base point of an object of `[C/E]` is the vertex section applied to its
base point.**  This upgrades the vanishing law of the contraction to the form required by
`ConeStack.contractionZeroIso`. -/
theorem zeroSection_eq {ε : S →ₐ[R] R} (hv : GradedCone.IsConeVertex A.coaction ε)
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    zeroSection A bas P =
      TorsorPushoutRel.cnPt A bas (basePoint A bas P ≫ coneVertex ε) := by
  refine hom_ext_of_projection P.toFppfTorsor (fppfSheaf_hom_ext ?_)
  intro W p
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : W ⟶ T, fppfYoneda.map b₀ = p ≫ P.projection :=
    ⟨fppfYoneda.preimage _, fppfYoneda.map_preimage _⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : W ⟶ coneScheme S,
      TorsorPushoutRel.cnPt A bas x₀ = p ≫ P.target :=
    TorsorPushoutRel.cnPt_surjective A bas _
  have h1 := TorsorPushoutRel.trivialHomSection_comp_targetMap
    (TorsorPushoutRel.scaleRelMonHom σ T (0 : Γ(T, ⊤)))
    (fun b x => scaleRelMonHom_zero_pt_one b x)
    (TorsorPushoutRel.coneScaleRelEquivMap A bas (0 : Γ(T, ⊤))) P (p ≫ P.projection) p rfl
  have h2 := TorsorPushoutRel.coneScaleRelEquivMap_pt A bas (0 : Γ(T, ⊤)) x₀ b₀
  rw [hb₀, hx₀] at h2
  have hbase : b₀ ≫ basePoint A bas P = x₀ ≫ coneBase R S := by
    refine fppfYoneda.map_injective ?_
    calc fppfYoneda.map (b₀ ≫ basePoint A bas P)
        = fppfYoneda.map b₀ ≫ fppfYoneda.map (basePoint A bas P) :=
          CategoryTheory.Functor.map_comp _ _ _
      _ = (p ≫ P.projection) ≫ fppfYoneda.map (basePoint A bas P) := by rw [hb₀]
      _ = p ≫ P.projection ≫ fppfYoneda.map (basePoint A bas P) := Category.assoc _ _ _
      _ = p ≫ P.target ≫ coneBaseHom A bas :=
          congrArg (fun q => p ≫ q) (projection_comp_basePoint A bas P)
      _ = (p ≫ P.target) ≫ coneBaseHom A bas := (Category.assoc _ _ _).symm
      _ = TorsorPushoutRel.cnPt A bas x₀ ≫ coneBaseHom A bas :=
          congrArg (fun q => q ≫ coneBaseHom A bas) hx₀.symm
      _ = fppfYoneda.map (x₀ ≫ coneBase R S) :=
          (CategoryTheory.Functor.map_comp _ _ _).symm
  calc p ≫ P.projection ≫ zeroSection A bas P
      = (p ≫ P.projection) ≫ zeroSection A bas P := (Category.assoc _ _ _).symm
    _ = TorsorPushoutRel.cnPt A bas (lift x₀ b₀ ≫
          TorsorPushoutRel.scaleConeScheme A (0 : Γ(T, ⊤))) := h1.trans h2
    _ = TorsorPushoutRel.cnPt A bas ((x₀ ≫ coneBase R S) ≫ coneVertex ε) :=
        congrArg (TorsorPushoutRel.cnPt A bas) (lift_scaleConeScheme_zero A hv x₀ b₀)
    _ = p ≫ P.projection ≫ TorsorPushoutRel.cnPt A bas (basePoint A bas P ≫ coneVertex ε) := by
      refine Eq.trans ?_ (Category.assoc p P.projection _)
      refine Eq.trans ?_ (congrArg
        (fun q => q ≫ fppfYoneda.map (basePoint A bas P ≫ coneVertex ε)) hb₀)
      refine Eq.trans ?_ (CategoryTheory.Functor.map_comp fppfYoneda b₀
        (basePoint A bas P ≫ coneVertex ε)).symm
      have hfin : (x₀ ≫ coneBase R S) ≫ coneVertex ε =
          b₀ ≫ basePoint A bas P ≫ coneVertex ε := by
        rw [← Category.assoc, hbase]
      exact congrArg fppfYoneda.map hfin

/-- **The vanishing law of the contraction of `[C/E]`, at the level of objects**: the contraction
by `0` of an object is the vertex over its base point, i.e. the value of the vertex section on the
image of the object under the projection. -/
noncomputable def coneContractionZeroIsoApp {ε : S →ₐ[R] R}
    (hv : GradedCone.IsConeVertex A.coaction ε)
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    (contractionFunctor A bas (0 : Γ(T, ⊤))).obj P ≅
      (StackHom.appFunctor (baseProjection A bas) T ⋙
        StackHom.appFunctor (coneVertexHom A bas ε) T).obj P :=
  (contractionFunctorZeroIso A bas P).symm ≪≫
    eqToIso ((congrArg trivialWithPoint (zeroSection_eq A bas hv P)).trans
      (coneVertexHom_app_obj A bas ε T (basePoint A bas P)).symm)

end ContractionZero

/-! ### Naturality of the canonical section of a pointwise trivial pushout -/

section TrivialHomSectionNaturality

open TorsorPushoutRel

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {ρ : RelMonHom G G' T}
  (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
    ρ.pt b x = 1)

/-- **The pushout of a morphism of torsors along a pointwise trivial homomorphism is the identity
of the trivial pushout datum**: the evaluation pairing of `PushoutTorsorRel.trivialDatum` does not
look at the point of the torsor at all. -/
theorem pushMap_trivialDatum {P Q : FppfTorsor G T} (φ : P ⟶ Q) :
    PushoutTorsorRel.pushMap (PushoutTorsorRel.trivialDatum ρ hρ P)
        (PushoutTorsorRel.trivialDatum ρ hρ Q) φ = 𝟙 _ :=
  (PushoutTorsorRel.eq_pushMap (PushoutTorsorRel.trivialDatum ρ hρ P)
    (PushoutTorsorRel.trivialDatum ρ hρ Q) φ (𝟙 _) (Category.id_comp _)
    (fun β _ _ _ _ => by
      change (β ≫ 𝟙 _) ≫ fst _ _ = β ≫ fst _ _
      rw [Category.comp_id])).symm

/-- **The canonical section of a pointwise trivial pushout is natural in the torsor.**  This is the
statement that `Cones/QuotientTorsorContractionCoherence.lean` does not provide and that upgrades
the vanishing law of the contraction of `[C/E]` from objects to a natural isomorphism. -/
theorem trivialHomSection_comp_pushMap {P Q : FppfTorsor G T} (φ : P ⟶ Q) :
    trivialHomSection ρ hρ P ≫
        PushoutTorsorRel.pushMap (pushoutTorsor P ρ) (pushoutTorsor Q ρ) φ =
      trivialHomSection ρ hρ Q := by
  have key : PushoutTorsorRel.cmpMap (PushoutTorsorRel.trivialDatum ρ hρ P)
        (pushoutTorsor P ρ) ≫
        PushoutTorsorRel.pushMap (pushoutTorsor P ρ) (pushoutTorsor Q ρ) φ =
      PushoutTorsorRel.cmpMap (PushoutTorsorRel.trivialDatum ρ hρ Q) (pushoutTorsor Q ρ) := by
    rw [PushoutTorsorRel.cmpMap_comp_pushMap,
      ← PushoutTorsorRel.pushMap_comp_cmpMap (PushoutTorsorRel.trivialDatum ρ hρ P)
        (PushoutTorsorRel.trivialDatum ρ hρ Q) (pushoutTorsor Q ρ) φ,
      pushMap_trivialDatum hρ φ]
    exact Category.id_comp _
  exact (Category.assoc _ _ _).trans (congrArg (fun q => unitSection G' T ≫ q) key)

end TrivialHomSectionNaturality

/-! ### Trivialisations attached to sections are natural -/

section SectionNaturality

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T : Scheme.{u}}

/-- **The comparison map attached to a section is natural**: a morphism of the quotient groupoid
carries the trivialisation given by a section to the trivialisation given by the image of that
section. -/
theorem sectionMap_comp_iso_hom {X Y : ActionTorsor G U T} (s : fppfYoneda.obj T ⟶ X.P)
    (u : X ⟶ Y) :
    sectionMap X s ≫ u.iso.hom = sectionMap Y (s ≫ u.iso.hom) := by
  rw [sectionMap, sectionMap, Category.assoc, u.equivariant, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp]

end SectionNaturality

/-! ### The vanishing law as a natural isomorphism -/

section ContractionZeroNatural

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T : Scheme.{u}}
variable (A : ConeAction R S F) (bas : Module.Basis σ R F)

/-- The canonical section of the contraction by the scalar `0`. -/
noncomputable abbrev zeroHomSection
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    fppfYoneda.obj T ⟶ ((contractionFunctor A bas (0 : Γ(T, ⊤))).obj P).P :=
  TorsorPushoutRel.trivialHomSection (TorsorPushoutRel.scaleRelMonHom σ T (0 : Γ(T, ⊤)))
    (fun b x => scaleRelMonHom_zero_pt_one b x) P.toFppfTorsor

/-- The canonical section of the contraction by `0` is a section. -/
theorem zeroHomSection_projection
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    zeroHomSection A bas P ≫ ((contractionFunctor A bas (0 : Γ(T, ⊤))).obj P).projection = 𝟙 _ :=
  TorsorPushoutRel.trivialHomSection_projection _ _ _

/-- **The canonical trivialisation of the contraction by the scalar `0`.** -/
noncomputable def zeroTrivialisation
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    trivialWithPoint (zeroSection A bas P) ≅ (contractionFunctor A bas (0 : Γ(T, ⊤))).obj P :=
  isoTrivialOfSection _ (zeroHomSection A bas P) (zeroHomSection_projection A bas P)

/-- The canonical section is carried to the unit section by the canonical trivialisation. -/
theorem zeroHomSection_comp_zeroTrivialisation_inv
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    zeroHomSection A bas P ≫ (zeroTrivialisation A bas P).inv.iso.hom =
      trivialSection (zeroSection A bas P) := by
  have h1 : trivialSection (zeroSection A bas P) ≫ (zeroTrivialisation A bas P).hom.iso.hom =
      zeroHomSection A bas P := unitSection_comp_sectionMap (zeroHomSection A bas P)
  have h2 : (zeroTrivialisation A bas P).hom.iso.hom ≫ (zeroTrivialisation A bas P).inv.iso.hom =
      𝟙 _ := by
    rw [← ActionTorsor.comp_iso_hom, Iso.hom_inv_id]
    rfl
  calc zeroHomSection A bas P ≫ (zeroTrivialisation A bas P).inv.iso.hom
      = (trivialSection (zeroSection A bas P) ≫ (zeroTrivialisation A bas P).hom.iso.hom) ≫
          (zeroTrivialisation A bas P).inv.iso.hom := by rw [h1]
    _ = trivialSection (zeroSection A bas P) ≫ ((zeroTrivialisation A bas P).hom.iso.hom ≫
          (zeroTrivialisation A bas P).inv.iso.hom) := Category.assoc _ _ _
    _ = trivialSection (zeroSection A bas P) := by rw [h2, Category.comp_id]

variable {ε : S →ₐ[R] R}

/-- The vertex over the base point of an object of `[C/E]`, as a point of the cone. -/
noncomputable abbrev vertexPoint
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    fppfYoneda.obj T ⟶ (coneActionSpace A bas).space.toSheaf :=
  TorsorPushoutRel.cnPt A bas (basePoint A bas P ≫ coneVertex ε)

/-- Isomorphic objects of `[C/E]` have the same vertex over the base point. -/
theorem vertexPoint_congr
    {P Q : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T} (f : P ⟶ Q) :
    vertexPoint A bas (ε := ε) P = vertexPoint A bas (ε := ε) Q :=
  congrArg (fun t => TorsorPushoutRel.cnPt A bas (t ≫ coneVertex ε)) (basePoint_congr A bas f)

/-- **The vanishing law of the contraction of `[C/E]`, as an isomorphism with the trivialised
object of the vertex over the base point.** -/
noncomputable def zeroVertexIso (hv : GradedCone.IsConeVertex A.coaction ε)
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    (contractionFunctor A bas (0 : Γ(T, ⊤))).obj P ≅
      trivialWithPoint (vertexPoint A bas (ε := ε) P) :=
  (zeroTrivialisation A bas P).symm ≪≫
    eqToIso (congrArg trivialWithPoint (zeroSection_eq A bas hv P))

/-- **The vanishing law is natural in the object**, up to the identification of the trivialised
vertex objects of isomorphic objects. -/
theorem zeroVertexIso_naturality (hv : GradedCone.IsConeVertex A.coaction ε)
    {P Q : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T} (f : P ⟶ Q) :
    (contractionFunctor A bas (0 : Γ(T, ⊤))).map f ≫ (zeroVertexIso A bas hv Q).hom =
      (zeroVertexIso A bas hv P).hom ≫
        eqToHom (congrArg trivialWithPoint (vertexPoint_congr A bas (ε := ε) f)) := by
  have hstep : zeroHomSection A bas P ≫
      ((contractionFunctor A bas (0 : Γ(T, ⊤))).map f).iso.hom = zeroHomSection A bas Q :=
    trivialHomSection_comp_pushMap
      (fun b x => scaleRelMonHom_zero_pt_one b x) (ActionTorsor.Hom.toFppfHom f)
  refine hom_ext_of_section (zeroHomSection A bas P) (zeroHomSection_projection A bas P) _ _ ?_
  rw [ActionTorsor.comp_iso_hom, ActionTorsor.comp_iso_hom, zeroVertexIso, zeroVertexIso,
    Iso.trans_hom, Iso.trans_hom, ActionTorsor.comp_iso_hom, ActionTorsor.comp_iso_hom,
    Iso.symm_hom, Iso.symm_hom, eqToIso.hom, eqToIso.hom]
  simp only [← Category.assoc]
  rw [hstep, zeroHomSection_comp_zeroTrivialisation_inv A bas Q,
    zeroHomSection_comp_zeroTrivialisation_inv A bas P,
    trivialSection_comp_eqToHom (zeroSection_eq A bas hv Q)
      (congrArg trivialWithPoint (zeroSection_eq A bas hv Q)),
    trivialSection_comp_eqToHom (zeroSection_eq A bas hv P)
      (congrArg trivialWithPoint (zeroSection_eq A bas hv P)),
    trivialSection_comp_eqToHom (vertexPoint_congr A bas (ε := ε) f)
      (congrArg trivialWithPoint (vertexPoint_congr A bas (ε := ε) f))]

/-- The value of the vertex section on the base point of an object, as an equality of objects. -/
theorem trivialWithPoint_vertexPoint_eq
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    trivialWithPoint (vertexPoint A bas (ε := ε) P) =
      (StackHom.appFunctor (baseProjection A bas) T ⋙
        StackHom.appFunctor (coneVertexHom A bas ε) T).obj P :=
  (coneVertexHom_app_obj A bas ε T (basePoint A bas P)).symm

/-- **The composite of the projection with the vertex section acts on arrows by the canonical
identification**, because the projection lands in a discrete fibre. -/
theorem projVertex_map_eq_eqToHom
    {P Q : StackFiber (coneTotalStack A bas) T} (f : P ⟶ Q)
    (h : (StackHom.appFunctor (baseProjection A bas) T ⋙
        StackHom.appFunctor (coneVertexHom A bas ε) T).obj P =
      (StackHom.appFunctor (baseProjection A bas) T ⋙
        StackHom.appFunctor (coneVertexHom A bas ε) T).obj Q) :
    (StackHom.appFunctor (baseProjection A bas) T ⋙
        StackHom.appFunctor (coneVertexHom A bas ε) T).map f = eqToHom h := by
  have hd : (StackHom.appFunctor (baseProjection A bas) T).obj P =
      (StackHom.appFunctor (baseProjection A bas) T).obj Q :=
    congrArg (fun t => (Discrete.mk (ULift.up t) : StackFiber (coneBaseStack R) T))
      (basePoint_congr A bas f)
  have hmap : (StackHom.appFunctor (baseProjection A bas) T).map f = eqToHom hd :=
    (coneBaseStack_hom_subsingleton R _ _).elim _ _
  change (StackHom.appFunctor (coneVertexHom A bas ε) T).map
      ((StackHom.appFunctor (baseProjection A bas) T).map f) = eqToHom h
  rw [hmap, eqToHom_map]

/-! `ConeStack.contractionZeroIso` as a natural isomorphism is `ConeQuotient.coneContractionZeroIso`
below, the transport of `ConeQuotient.zeroVertexIso_naturality` along
`ConeQuotient.trivialWithPoint_vertexPoint_eq`; see the module docstring for why that transport has
to be done by term application rather than by rewriting. -/

end ContractionZeroNatural

/-! ### The cone stack `[C/E]` -/

section Assembly

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T T' : Scheme.{u}}
variable (A : ConeAction R S F) (bas : Module.Basis σ R F)

/-- **The affine cone quotient `[C/E]` as a cone stack over `Spec R`**, parametrised by the
vanishing law of the contraction in its natural form.  That datum is constructed below
(`ConeQuotient.coneContractionZeroIso`), which turns this into the unconditional
`ConeQuotient.coneQuotientStack`; the parametrised form is kept because it isolates the vanishing
law from every other field -- the projection, the vertex, the fact that the vertex is a section of
the projection, and the unit, multiplicativity, vertex, projection and base-change laws of the
contraction -- all of which come from this file or from
`Cones/QuotientTorsorContractionCoherence.lean`. -/
noncomputable def coneQuotientStackOfZeroIso {ε : S →ₐ[R] R}
    (hv : GradedCone.IsConeVertex A.coaction ε)
    (zeroIso : ∀ T : Scheme.{u}, contractionFunctor A bas (0 : Γ(T, ⊤)) ≅
      StackHom.appFunctor (baseProjection A bas) T ⋙
        StackHom.appFunctor (coneVertexHom A bas ε) T) :
    ConeStack (coneBaseStack R) canonicalFppfScalarRings.{u} where
  total := coneTotalStack A bas
  projection := baseProjection A bas
  vertex := coneVertexHom A bas ε
  vertexProjectionIso := coneVertexProjectionIso A bas ε
  contraction _ r := contractionFunctor A bas r
  contractionOneIso _ := contractionFunctorOneIso A bas
  contractionMulIso _ r s := contractionFunctorMulIso A bas r s
  contractionZeroIso T := zeroIso T
  contractionVertexIso _ r := coneContractionVertexIso A bas hv r
  contractionProjectionIso _ r := coneContractionProjectionIso A bas r
  contractionPullbackIso f r := contractionFunctorPullbackIso A bas r f

end Assembly

/-! ### The vanishing law as a natural isomorphism -/

section DiscreteFactor

universe w₂ w₃ w₄ v₂ v₃ v₄

/-- **Pasting a naturality square onto an identification of its targets.**  Stated for an abstract
category, so that it can be applied to a goal whose terms are only *definitionally* type-correct
(the fibre of `[C/E]` carries two definitionally equal category instances, so `rw` cannot be used
on such a goal at all: the goal is not type-correct at `implicit` transparency). -/
theorem comp_assoc_paste {C : Type v₂} [Category.{w₂} C] {W X Y Y' Z V : C}
    {m : W ⟶ X} {a : X ⟶ Y'} {a' : W ⟶ Y} {u : Y ⟶ Y'} {e : Y' ⟶ Z} {e' : Y ⟶ V}
    {ef : V ⟶ Z} (h1 : m ≫ a = a' ≫ u) (h2 : u ≫ e = e' ≫ ef) :
    m ≫ a ≫ e = (a' ≫ e') ≫ ef := by
  rw [← Category.assoc, h1, Category.assoc, h2, Category.assoc]

/-- **A natural isomorphism onto a functor which factors through a category with subsingleton
hom-types**, from the isomorphisms of the values on objects together with the naturality expressed
through the canonical identifications `hobjH` of those values.  Because the middle category has
subsingleton hom-types, the composite `Ψ ⋙ Θ` acts on an arrow by the identification of its
endpoints, so the naturality square of the components collapses to `hnat`.

Stated for abstract categories, whose `Category` instances are therefore *arguments*: instantiating
it at a fibre of a stack fixes one instance once and for all, costs a single definitional check,
and never asks the kernel to unfold the fibre. -/
def natIsoOfDiscreteFactor {C : Type v₂} [Category.{w₂} C] {D : Type v₃} [Category.{w₃} D]
    {E : Type v₄} [Category.{w₄} E] {Φ : C ⥤ D} {Ψ : C ⥤ E} {Θ : E ⥤ D}
    (hs : ∀ x y : E, Subsingleton (x ⟶ y))
    (hobjG : ∀ {X Y : C}, (X ⟶ Y) → Ψ.obj X = Ψ.obj Y)
    (hobjH : ∀ {X Y : C}, (X ⟶ Y) → (Ψ ⋙ Θ).obj X = (Ψ ⋙ Θ).obj Y)
    (app : ∀ X, Φ.obj X ≅ (Ψ ⋙ Θ).obj X)
    (hnat : ∀ {X Y : C} (f : X ⟶ Y),
      Φ.map f ≫ (app Y).hom = (app X).hom ≫ eqToHom (hobjH f)) :
    Φ ≅ Ψ ⋙ Θ :=
  NatIso.ofComponents app (fun {_ _} f => by
    have hmap : (Ψ ⋙ Θ).map f = eqToHom (hobjH f) := by
      have h1 : Ψ.map f = eqToHom (hobjG f) := (hs _ _).elim _ _
      rw [Functor.comp_map, h1, eqToHom_map]
    rw [hnat f, hmap])

end DiscreteFactor

section ContractionZeroIso

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T : Scheme.{u}}
variable (A : ConeAction R S F) (bas : Module.Basis σ R F)
variable {ε : S →ₐ[R] R}

/-- **The projection to the base identifies isomorphic objects of `[C/E]`**, as an equality of
objects of the fibre of the base. -/
theorem baseProjection_obj_congr
    {P Q : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T} (f : P ⟶ Q) :
    (StackHom.appFunctor (baseProjection A bas) T).obj P =
      (StackHom.appFunctor (baseProjection A bas) T).obj Q :=
  (baseProjection_app_obj A bas T P).trans
    ((congrArg (fun t => (Discrete.mk (ULift.up t) : StackFiber (coneBaseStack R) T))
      (basePoint_congr A bas f)).trans (baseProjection_app_obj A bas T Q).symm)

/-- The canonical identification of the values of `projection ⋙ vertex` on isomorphic objects of
`[C/E]`: both are the trivialised object of the vertex over the common base point. -/
theorem projVertex_obj_congr
    {P Q : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T} (f : P ⟶ Q) :
    (StackHom.appFunctor (baseProjection A bas) T ⋙
        StackHom.appFunctor (coneVertexHom A bas ε) T).obj P =
      (StackHom.appFunctor (baseProjection A bas) T ⋙
        StackHom.appFunctor (coneVertexHom A bas ε) T).obj Q :=
  (trivialWithPoint_vertexPoint_eq A bas (ε := ε) P).symm.trans
    ((congrArg trivialWithPoint (vertexPoint_congr A bas (ε := ε) f)).trans
      (trivialWithPoint_vertexPoint_eq A bas (ε := ε) Q))

/-- **The vanishing law of the contraction of `[C/E]` is natural in the object**, in the form
required by `ConeQuotient.natIsoOfDiscreteFactor`: the transport of
`ConeQuotient.zeroVertexIso_naturality` along `ConeQuotient.trivialWithPoint_vertexPoint_eq`.  The
proof is in term mode, because the goal mentions the fibre of `[C/E]` through two definitionally
equal category instances and is therefore not type-correct at `implicit` transparency. -/
theorem zeroVertexIso_naturality' (hv : GradedCone.IsConeVertex A.coaction ε)
    {P Q : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T} (f : P ⟶ Q) :
    (contractionFunctor A bas (0 : Γ(T, ⊤))).map f ≫
        (zeroVertexIso A bas hv Q).hom ≫
          eqToHom (trivialWithPoint_vertexPoint_eq A bas (ε := ε) Q) =
      ((zeroVertexIso A bas hv P).hom ≫
          eqToHom (trivialWithPoint_vertexPoint_eq A bas (ε := ε) P)) ≫
        eqToHom (projVertex_obj_congr A bas (ε := ε) f) :=
  comp_assoc_paste (zeroVertexIso_naturality A bas hv f)
    ((eqToHom_trans (congrArg trivialWithPoint (vertexPoint_congr A bas (ε := ε) f))
        (trivialWithPoint_vertexPoint_eq A bas (ε := ε) Q)).trans
      (eqToHom_trans (trivialWithPoint_vertexPoint_eq A bas (ε := ε) P)
        (projVertex_obj_congr A bas (ε := ε) f)).symm)

/-- **The vanishing law of the contraction of `[C/E]`, as a natural isomorphism**: contracting by
the scalar `0` is the projection to the base followed by the vertex section.  This is the last
field of the cone stack `ConeQuotient.coneQuotientStack`. -/
noncomputable def coneContractionZeroIso (hv : GradedCone.IsConeVertex A.coaction ε)
    (T : Scheme.{u}) :
    contractionFunctor A bas (0 : Γ(T, ⊤)) ≅
      StackHom.appFunctor (baseProjection A bas) T ⋙
        StackHom.appFunctor (coneVertexHom A bas ε) T :=
  natIsoOfDiscreteFactor (coneBaseStack_hom_subsingleton R (T := T))
    (fun {_ _} f => baseProjection_obj_congr A bas f)
    (fun {_ _} f => projVertex_obj_congr A bas (ε := ε) f)
    (fun P => zeroVertexIso A bas hv P ≪≫
      eqToIso (trivialWithPoint_vertexPoint_eq A bas (ε := ε) P))
    (fun {_ _} f => zeroVertexIso_naturality' A bas hv f)

end ContractionZeroIso

/-! ### The cone stack `[C/E]` -/

section ConeStackFinal

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u}
variable (A : ConeAction R S F) (bas : Module.Basis σ R F)

/-- **The affine cone quotient `[C/E]` as a cone stack over `Spec R`.**  Every field is
constructed: the total stack is `ActionTorsor.quotientStack (vectorBundleGroup σ)
(coneActionSpace A bas)`, the projection is `ConeQuotient.baseProjection` (the descent of the base
point), the vertex is `ConeQuotient.coneVertexHom`, the contraction is the unconditional
`ConeQuotient.contractionFunctor`, and the vanishing law is
`ConeQuotient.coneContractionZeroIso`. -/
noncomputable def coneQuotientStack {ε : S →ₐ[R] R}
    (hv : GradedCone.IsConeVertex A.coaction ε) :
    ConeStack (coneBaseStack R) canonicalFppfScalarRings.{u} :=
  coneQuotientStackOfZeroIso A bas hv (coneContractionZeroIso A bas hv)

/-- The total stack of `ConeQuotient.coneQuotientStack` is the quotient stack `[C/E]`. -/
theorem coneQuotientStack_total {ε : S →ₐ[R] R}
    (hv : GradedCone.IsConeVertex A.coaction ε) :
    (coneQuotientStack A bas hv).total = coneTotalStack A bas :=
  rfl

/-- The projection of `ConeQuotient.coneQuotientStack` is `ConeQuotient.baseProjection`. -/
theorem coneQuotientStack_projection {ε : S →ₐ[R] R}
    (hv : GradedCone.IsConeVertex A.coaction ε) :
    (coneQuotientStack A bas hv).projection = baseProjection A bas :=
  rfl

/-- The vertex of `ConeQuotient.coneQuotientStack` is `ConeQuotient.coneVertexHom`. -/
theorem coneQuotientStack_vertex {ε : S →ₐ[R] R}
    (hv : GradedCone.IsConeVertex A.coaction ε) :
    (coneQuotientStack A bas hv).vertex = coneVertexHom A bas ε :=
  rfl

/-- The contraction of `ConeQuotient.coneQuotientStack` is
`ConeQuotient.contractionFunctor`. -/
theorem coneQuotientStack_contraction {ε : S →ₐ[R] R}
    (hv : GradedCone.IsConeVertex A.coaction ε) (T : Scheme.{u}) (r : Γ(T, ⊤)) :
    (coneQuotientStack A bas hv).contraction T r = contractionFunctor A bas r :=
  rfl

/-- The vanishing law of `ConeQuotient.coneQuotientStack` is
`ConeQuotient.coneContractionZeroIso`. -/
theorem coneQuotientStack_contractionZeroIso {ε : S →ₐ[R] R}
    (hv : GradedCone.IsConeVertex A.coaction ε) (T : Scheme.{u}) :
    (coneQuotientStack A bas hv).contractionZeroIso T = coneContractionZeroIso A bas hv T :=
  rfl

end ConeStackFinal

end ConeQuotient

end GromovWitten.AlgebraicGeometry
