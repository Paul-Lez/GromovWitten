/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.QuotientTorsor

/-!
# The `𝔸¹`-contraction on the torsor prestack `[C/E]`

`GromovWitten.AlgebraicGeometry.Cones.QuotientTorsor` realises the quotient `[C/E]` of an
affine cone `C = Spec S` by a vector bundle `E = 𝔾ₐ^σ` as a prestack of torsor groupoids
`ActionTorsor (vectorBundleGroup σ) (coneActionSpace A b) T`.  This file adds the missing
cone-stack ingredient: the *contraction* by a scalar.

## The trivialised torsor groupoid

The pushout `r_* P` of a torsor along the multiplication-by-`r` endomorphism of `E` cannot be
formed here, because fppf sheafification is not available.  Instead we isolate the full
subgroupoid on which the contraction is completely explicit:

* `TrivialPoint G U T`: the groupoid whose objects are `T`-points of `U` and whose arrows
  `x ⟶ y` are `T`-points `g` of `G` with `g · y = x`.  This is the groupoid of *trivialised*
  `G`-torsors with an equivariant map to `U`.
* `TrivialPoint.embedding : TrivialPoint G U T ⥤ ActionTorsor G U T` is fully faithful
  (`TrivialPoint.embeddingFullyFaithful`), and it is an equivalence
  (`TrivialPoint.embeddingEquivalence`) as soon as every `G`-torsor over `T` is trivial.  The
  latter hypothesis, `AllTorsorsTrivial G T`, is the vanishing of `H¹(T, G)`; it is *not*
  proved here and appears as an explicit hypothesis of every statement that uses it.

## Contractions as twists

* `ActionTwist G U T`: an endomorphism `grp` of the group `G(T)` of `T`-points together with a
  self-map `pt` of the `T`-points of `U` satisfying `pt (g · t) = grp g · pt t`.  This is
  exactly the datum needed to contract trivialised torsors, and it induces an endofunctor
  `ActionTwist.functor` of `TrivialPoint G U T`.
* `ActionTwist.torsorContraction`: the induced endofunctor of the whole torsor groupoid
  `ActionTorsor G U T`, defined by transport along `embeddingEquivalence`, hence conditional on
  `AllTorsorsTrivial G T`.  `ActionTwist.embeddingTorsorContractionIso` identifies it with the
  twist on trivialised torsors, and `ActionTwist.torsorContractionCongr`,
  `ActionTwist.torsorContractionIsoId` transport isomorphisms of twists.

## The contraction of the affine cone quotient

* `coneTwist A b r`: for a scalar `r : B` the twist of `[C/E]` over `Spec B` given by scalar
  multiplication by `r` on `E` and by the cone contraction `c_r` on `C`.  Its defining equation
  `scaleRing_actOn` (`c_r (v · x) = (r v) · c_r x`) is proved for *ring*-valued points, with no
  `R`-algebra structure on the test ring.
* `coneTwistOneIso`, `coneTwistMulIso`, `coneTwistZeroIso`, `coneTwistVertexIso`,
  `coneTwistProjectionIso`, `coneTwistPullbackIso`: the unit, multiplicativity, zero, vertex,
  over-the-base and base-change laws of the contraction, on trivialised torsors.  They are
  proved unconditionally, the vertex laws using an explicit `IsConeVertex` hypothesis.
* `quotientToTrivialPoint`, `quotientToTrivialPoint_comp_embedding` and
  `contractionComparison`: the comparison with `QuotientGroupoid.contractionFunctor`, i.e. the
  statement that on trivial torsors the torsor contraction is the cone's own contraction;
  `coneTorsorContraction` and `coneTorsorContractionComparison` are the versions for all
  torsors, under `AllTorsorsTrivial`.

## What is not done here

The pushout torsor `r_* P` for a *general* torsor `P` is not constructed, so the contraction on
`ActionTorsor G U T` is only obtained under `AllTorsorsTrivial G T`.  Consequently the full
`ConeStack` structure over the fppf site is not assembled; what is provided is the fibrewise
contraction together with all of its coherence isomorphisms on trivialised torsors.
-/

universe u

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

namespace ConeQuotient

/-! ### The groupoid of trivialised torsors -/

section TrivialisedTorsors

open scoped CategoryTheory.MonObj

variable (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G) (T : Scheme.{u})

/-- The groupoid of trivialised `G`-torsors over `T` with an equivariant map to `U`: an object
is a `T`-point of `U`, thought of as the trivial torsor `G × T` with the equivariant map
`(g, s) ↦ g · t(s)`. -/
@[ext]
structure TrivialPoint where
  /-- The `T`-point of `U` classifying the trivialised torsor. -/
  pt : fppfYoneda.obj T ⟶ U.space.toSheaf

namespace TrivialPoint

variable {G U T}

/-- An arrow of trivialised torsors is a `T`-point of `G` carrying the target point of `U` to
the source point. -/
structure Hom (x y : TrivialPoint G U T) where
  /-- The translating `T`-point of `G`. -/
  val : fppfYoneda.obj T ⟶ G.space.toSheaf
  /-- The translation carries the second point of `U` to the first one. -/
  smul_eq : lift val y.pt ≫ ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) = x.pt

@[ext]
theorem Hom.ext {x y : TrivialPoint G U T} (f g : Hom x y) (h : f.val = g.val) : f = g := by
  cases f
  cases g
  simp only [Hom.mk.injEq]
  exact h

/-- Trivialised torsors over `T` form a category, with composition the product of the
translating points. -/
instance instCategory : Category (TrivialPoint G U T) where
  Hom := Hom
  id x := ⟨1, lift_one_smul x.pt⟩
  comp {x y z} f g :=
    ⟨f.val * g.val, by
      rw [lift_mul_smul, g.smul_eq, f.smul_eq]⟩
  id_comp f := Hom.ext _ _ (one_mul _)
  comp_id f := Hom.ext _ _ (mul_one _)
  assoc f g h := Hom.ext _ _ (_root_.mul_assoc _ _ _)

/-- The translating point of the identity arrow is the unit. -/
@[simp]
theorem id_val (x : TrivialPoint G U T) : (𝟙 x : x ⟶ x).val = 1 := rfl

/-- The translating point of a composite is the product. -/
@[simp]
theorem comp_val {x y z : TrivialPoint G U T} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = f.val * g.val := rfl

/-- Every arrow of trivialised torsors is invertible. -/
instance instGroupoid : Groupoid (TrivialPoint G U T) where
  inv {x y} f :=
    ⟨f.val⁻¹, by
      rw [← f.smul_eq, ← lift_mul_smul, inv_mul_cancel, lift_one_smul]⟩
  inv_comp f := Hom.ext _ _ (inv_mul_cancel _)
  comp_inv f := Hom.ext _ _ (mul_inv_cancel _)

/-- The translating point of the inverse arrow. -/
@[simp]
theorem inv_val {x y : TrivialPoint G U T} (f : x ⟶ y) :
    (CategoryTheory.inv f).val = f.val⁻¹ := by
  rw [← Groupoid.inv_eq_inv]
  rfl

/-- The translating point of an `eqToHom` is the unit. -/
@[simp]
theorem eqToHom_val {x y : TrivialPoint G U T} (h : x = y) :
    (eqToHom h : x ⟶ y).val = 1 := by
  subst h
  rfl

/-- Two functors into the groupoid of trivialised torsors that agree on objects and on the
translating points of arrows are isomorphic. -/
noncomputable def natIsoOfEq {C : Type*} [Category C] (F H : C ⥤ TrivialPoint G U T)
    (hobj : ∀ x, F.obj x = H.obj x)
    (hmap : ∀ {x y : C} (f : x ⟶ y), (F.map f).val = (H.map f).val) : F ≅ H :=
  NatIso.ofComponents (fun x => eqToIso (hobj x)) (by
    intro x y f
    refine Hom.ext _ _ ?_
    simp only [comp_val, eqToIso.hom, eqToHom_val, mul_one, one_mul]
    exact hmap f)

variable (G U T)

/-- The fully faithful embedding of trivialised torsors into all torsors. -/
noncomputable def embedding : TrivialPoint G U T ⥤ ActionTorsor G U T where
  obj x := trivialWithPoint x.pt
  map {x y} f := (trivialHomEquiv _ _).symm ⟨f.val, f.smul_eq⟩
  map_id x := ActionTorsor.Hom.ext _ _ (by
    change translationMap (1 : fppfYoneda.obj T ⟶ G.space.toSheaf) = 𝟙 _
    exact translationMap_one)
  map_comp f g := ActionTorsor.Hom.ext _ _ (by
    change translationMap (f.val * g.val) = translationMap f.val ≫ translationMap g.val
    exact (translationMap_comp _ _).symm)

/-- The embedding sends a point to the trivial torsor with that point. -/
@[simp]
theorem embedding_obj (x : TrivialPoint G U T) :
    (embedding G U T).obj x = trivialWithPoint x.pt := rfl

/-- The embedding sends an arrow to the corresponding translation. -/
@[simp]
theorem embedding_map_iso_hom {x y : TrivialPoint G U T} (f : x ⟶ y) :
    ((embedding G U T).map f).iso.hom = translationMap f.val := rfl

/-- The embedding of trivialised torsors is fully faithful. -/
noncomputable def embeddingFullyFaithful : (embedding G U T).FullyFaithful where
  preimage {x y} h := ⟨(trivialHomEquiv x.pt y.pt h).1, (trivialHomEquiv x.pt y.pt h).2⟩
  map_preimage {x y} h := by
    refine ActionTorsor.Hom.ext _ _ ?_
    change translationMap ((trivialHomEquiv x.pt y.pt h).1) = h.iso.hom
    have := (trivialHomEquiv x.pt y.pt).symm_apply_apply h
    exact congrArg (fun k : trivialWithPoint x.pt ⟶ trivialWithPoint y.pt => k.iso.hom) this
  preimage_map {x y} f := by
    refine Hom.ext _ _ ?_
    change ((trivialHomEquiv x.pt y.pt) ((trivialHomEquiv x.pt y.pt).symm ⟨f.val, f.smul_eq⟩)).1 =
      f.val
    rw [Equiv.apply_symm_apply]

instance : (embedding G U T).Full := (embeddingFullyFaithful G U T).full

instance : (embedding G U T).Faithful := (embeddingFullyFaithful G U T).faithful

/-- If every `G`-torsor over `T` is trivial then every object of the torsor groupoid is in the
essential image of the embedding.  The hypothesis is the vanishing of `H¹(T, G)`; it is not
proved here. -/
theorem essSurj_embedding (h : AllTorsorsTrivial G T) : (embedding G U T).EssSurj := by
  refine ⟨fun P => ?_⟩
  obtain ⟨s, hs⟩ := h P.toFppfTorsor
  exact ⟨⟨s ≫ P.target⟩, ⟨isoTrivialOfSection P s hs⟩⟩

/-- Under the vanishing of `H¹(T, G)` the embedding of trivialised torsors is an equivalence. -/
theorem isEquivalence_embedding (h : AllTorsorsTrivial G T) :
    (embedding G U T).IsEquivalence :=
  have _ : (embedding G U T).EssSurj := essSurj_embedding G U T h
  { }

/-- Under the vanishing of `H¹(T, G)` the trivialised torsors are *all* the torsors. -/
noncomputable def embeddingEquivalence (h : AllTorsorsTrivial G T) :
    TrivialPoint G U T ≌ ActionTorsor G U T :=
  @Functor.asEquivalence _ _ _ _ (embedding G U T) (isEquivalence_embedding G U T h)

/-- The equivalence of the previous declaration has the embedding as its underlying functor. -/
@[simp]
theorem embeddingEquivalence_functor (h : AllTorsorsTrivial G T) :
    (embeddingEquivalence G U T h).functor = embedding G U T := rfl

/-! #### Base change of trivialised torsors -/

variable {G U T} {T' : Scheme.{u}}

variable (G U) in
/-- Base change of trivialised torsors along a morphism of schemes: both the point of `U` and
the translating points of `G` are composed with the morphism. -/
noncomputable def pullbackFunctor (β : T' ⟶ T) :
    TrivialPoint G U T ⥤ TrivialPoint G U T' where
  obj x := ⟨fppfYoneda.map β ≫ x.pt⟩
  map {x y} f :=
    ⟨fppfYoneda.map β ≫ f.val, by
      rw [← comp_lift, Category.assoc, f.smul_eq]⟩
  map_id x := Hom.ext _ _ (MonObj.comp_one _)
  map_comp f g := Hom.ext _ _ (MonObj.comp_mul _ _ _)

/-- Base change of trivialised torsors, on objects. -/
@[simp]
theorem pullbackFunctor_obj_pt (β : T' ⟶ T) (x : TrivialPoint G U T) :
    ((pullbackFunctor G U β).obj x).pt = fppfYoneda.map β ≫ x.pt := rfl

/-- Base change of trivialised torsors, on arrows. -/
@[simp]
theorem pullbackFunctor_map_val (β : T' ⟶ T) {x y : TrivialPoint G U T} (f : x ⟶ y) :
    ((pullbackFunctor G U β).map f).val = fppfYoneda.map β ≫ f.val := rfl

/-- Base change of a trivialised torsor is the base change of the corresponding torsor.  This
is the object-level compatibility of `pullbackFunctor` with `ActionTorsor.pullbackFunctor`. -/
noncomputable def embeddingPullbackIsoApp (β : T' ⟶ T) (x : TrivialPoint G U T) :
    (pullbackFunctor G U β ⋙ embedding G U T').obj x ≅
      (embedding G U T ⋙ ActionTorsor.pullbackFunctor β).obj x :=
  pullbackTrivialIso x.pt β

end TrivialPoint

end TrivialisedTorsors

/-! ### Contractions of trivialised torsors -/

section Twists

open scoped CategoryTheory.MonObj

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T T' : Scheme.{u}}

variable (G U T) in
/-- A twisting datum for the action of `G` on `U` over `T`: an endomorphism `grp` of the group
of `T`-points of `G` together with a self-map `pt` of the `T`-points of `U` which is
`grp`-equivariant.  This is exactly what is needed to contract trivialised torsors: on the
trivial torsor with point `t` the twist acts by `(g, s) ↦ (grp g, pt t (s))`. -/
structure ActionTwist where
  /-- The endomorphism of the group of `T`-points of `G`. -/
  grp : (fppfYoneda.obj T ⟶ G.space.toSheaf) →* (fppfYoneda.obj T ⟶ G.space.toSheaf)
  /-- The self-map of the `T`-points of `U`. -/
  pt : (fppfYoneda.obj T ⟶ U.space.toSheaf) → (fppfYoneda.obj T ⟶ U.space.toSheaf)
  /-- Twisted equivariance: `pt (g · t) = grp g · pt t`. -/
  pt_smul : ∀ (g : fppfYoneda.obj T ⟶ G.space.toSheaf) (t : fppfYoneda.obj T ⟶ U.space.toSheaf),
    pt (lift g t ≫ ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)) =
      lift (grp g) (pt t) ≫ ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)

namespace ActionTwist

/-- The endofunctor of trivialised torsors induced by a twisting datum. -/
noncomputable def functor (w : ActionTwist G U T) :
    TrivialPoint G U T ⥤ TrivialPoint G U T where
  obj x := ⟨w.pt x.pt⟩
  map {x y} f := ⟨w.grp f.val, by rw [← w.pt_smul, f.smul_eq]⟩
  map_id x := TrivialPoint.Hom.ext _ _ (by
    change w.grp (1 : fppfYoneda.obj T ⟶ G.space.toSheaf) = 1
    exact map_one w.grp)
  map_comp f g := TrivialPoint.Hom.ext _ _ (by
    change w.grp (f.val * g.val) = w.grp f.val * w.grp g.val
    exact map_mul w.grp _ _)

/-- The twist functor on objects. -/
@[simp]
theorem functor_obj_pt (w : ActionTwist G U T) (x : TrivialPoint G U T) :
    (w.functor.obj x).pt = w.pt x.pt := rfl

/-- The twist functor on arrows. -/
@[simp]
theorem functor_map_val (w : ActionTwist G U T) {x y : TrivialPoint G U T} (f : x ⟶ y) :
    (w.functor.map f).val = w.grp f.val := rfl

/-- A twist whose data are the identity induces the identity functor. -/
noncomputable def functorIsoId (w : ActionTwist G U T) (hpt : ∀ t, w.pt t = t)
    (hgrp : ∀ g, w.grp g = g) : w.functor ≅ 𝟭 (TrivialPoint G U T) :=
  TrivialPoint.natIsoOfEq _ _ (fun x => TrivialPoint.ext (hpt x.pt)) fun f => hgrp f.val

/-- A twist whose data are the composite of two others induces the composite functor. -/
noncomputable def functorIsoComp (w w₁ w₂ : ActionTwist G U T)
    (hpt : ∀ t, w.pt t = w₁.pt (w₂.pt t)) (hgrp : ∀ g, w.grp g = w₁.grp (w₂.grp g)) :
    w.functor ≅ w₂.functor ⋙ w₁.functor :=
  TrivialPoint.natIsoOfEq _ _ (fun x => TrivialPoint.ext (hpt x.pt)) fun f => hgrp f.val

/-- A twist which collapses everything to a fixed point of `U` induces the constant functor. -/
noncomputable def functorIsoConst (w : ActionTwist G U T)
    (c : fppfYoneda.obj T ⟶ U.space.toSheaf) (hpt : ∀ t, w.pt t = c)
    (hgrp : ∀ g, w.grp g = 1) :
    w.functor ≅ (Functor.const (TrivialPoint G U T)).obj ⟨c⟩ :=
  TrivialPoint.natIsoOfEq _ _ (fun x => TrivialPoint.ext (hpt x.pt)) fun f => hgrp f.val

/-- Twists commuting with base change induce a base-change isomorphism of the corresponding
contraction functors. -/
noncomputable def pullbackIso (w : ActionTwist G U T) (w' : ActionTwist G U T') (β : T' ⟶ T)
    (hpt : ∀ t, w'.pt (fppfYoneda.map β ≫ t) = fppfYoneda.map β ≫ w.pt t)
    (hgrp : ∀ g, w'.grp (fppfYoneda.map β ≫ g) = fppfYoneda.map β ≫ w.grp g) :
    w.functor ⋙ TrivialPoint.pullbackFunctor G U β ≅
      TrivialPoint.pullbackFunctor G U β ⋙ w'.functor :=
  TrivialPoint.natIsoOfEq _ _ (fun x => TrivialPoint.ext (hpt x.pt).symm)
    fun f => (hgrp f.val).symm

/-! #### Transport to the whole torsor groupoid -/

/-- The contraction of *all* torsors induced by a twisting datum, obtained by transporting the
twist along the equivalence with trivialised torsors.  It depends on the hypothesis that every
`G`-torsor over `T` is trivial, which is not proved here. -/
noncomputable def torsorContraction (w : ActionTwist G U T) (h : AllTorsorsTrivial G T) :
    ActionTorsor G U T ⥤ ActionTorsor G U T :=
  (TrivialPoint.embeddingEquivalence G U T h).inverse ⋙ w.functor ⋙
    TrivialPoint.embedding G U T

/-- On trivialised torsors the transported contraction is the twist itself: the contraction of
the trivial torsor with point `t` is the trivial torsor with point `w.pt t`. -/
noncomputable def embeddingTorsorContractionIso (w : ActionTwist G U T)
    (h : AllTorsorsTrivial G T) :
    TrivialPoint.embedding G U T ⋙ w.torsorContraction h ≅
      w.functor ⋙ TrivialPoint.embedding G U T :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight (TrivialPoint.embeddingEquivalence G U T h).unitIso.symm w.functor)
    (TrivialPoint.embedding G U T)

/-- Isomorphic twists induce isomorphic contractions of the torsor groupoid. -/
noncomputable def torsorContractionCongr {w w' : ActionTwist G U T}
    (h : AllTorsorsTrivial G T) (e : w.functor ≅ w'.functor) :
    w.torsorContraction h ≅ w'.torsorContraction h :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight e (TrivialPoint.embedding G U T))

/-- The contraction attached to a twist acting as the identity is isomorphic to the identity
functor of the torsor groupoid. -/
noncomputable def torsorContractionIsoId (w : ActionTwist G U T) (h : AllTorsorsTrivial G T)
    (e : w.functor ≅ 𝟭 (TrivialPoint G U T)) :
    w.torsorContraction h ≅ 𝟭 (ActionTorsor G U T) :=
  (Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight e (TrivialPoint.embedding G U T))).trans
    (TrivialPoint.embeddingEquivalence G U T h).counitIso

end ActionTwist

end Twists

/-! ### Contracting ring-valued points of the cone -/

section RingScale

open GradedCone

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u}
variable (A : ConeAction R S F)
variable {B D : Type u} [CommRing B] [CommRing D]

/-- The contraction of a ring-valued point of the cone by a scalar of the test ring.  No
`R`-algebra structure on the test ring is needed: the structure map of the test ring is the
point itself. -/
noncomputable def scaleRing (r : B) (φ : S →+* B) : S →+* B :=
  (Polynomial.eval₂RingHom φ r).comp A.coaction.toRingHom

/-- Over a test `R`-algebra the ring-level contraction is the contraction `scale` of the cone
structure. -/
theorem scaleRing_coe [Algebra R B] (φ : S →ₐ[R] B) (r : B) :
    scaleRing A r (φ : S →+* B) = ((scale A.coaction φ r : S →ₐ[R] B) : S →+* B) :=
  rfl

omit [Algebra R S] in
/-- A scalar of the test ring can be pulled out of `Basis.constr`. -/
theorem constr_smul (b : Module.Basis σ R F) [Algebra R B] (r : B) (v : σ → B) :
    b.constr R (r • v) = r • (b.constr R v) := by
  refine b.ext fun i => ?_
  rw [Module.Basis.constr_basis, LinearMap.smul_apply, Module.Basis.constr_basis]
  rfl

/-- The contraction is natural in the test ring. -/
theorem comp_scaleRing (g : B →+* D) (r : B) (φ : S →+* B) :
    g.comp (scaleRing A r φ) = scaleRing A (g r) (g.comp φ) :=
  RingHom.ext fun _ => Polynomial.hom_eval₂ _ _ _ _

/-- Contracting a ring-valued point by `1` does nothing. -/
theorem scaleRing_one (φ : S →+* B) : scaleRing A (1 : B) φ = φ := by
  let _ : Algebra R B := (φ.comp (algebraMap R S)).toAlgebra
  let φ' : S →ₐ[R] B := { φ with commutes' := fun _ => rfl }
  have hcoe : ((φ' : S →+* B)) = φ := rfl
  rw [← hcoe, scaleRing_coe, A.isCone.scale_one]

/-- Contracting a ring-valued point twice is contracting by the product. -/
theorem scaleRing_scaleRing (r s : B) (φ : S →+* B) :
    scaleRing A s (scaleRing A r φ) = scaleRing A (r * s) φ := by
  let _ : Algebra R B := (φ.comp (algebraMap R S)).toAlgebra
  let φ' : S →ₐ[R] B := { φ with commutes' := fun _ => rfl }
  have hcoe : ((φ' : S →+* B)) = φ := rfl
  rw [← hcoe, scaleRing_coe, scaleRing_coe, scaleRing_coe, A.isCone.scale_scale]

/-- Contracting by the image of a scalar of the base ring is composing with the contraction
endomorphism of the cone. -/
theorem scaleRing_algebraMap (r : R) (φ : S →+* B) :
    scaleRing A (φ (algebraMap R S r)) φ =
      φ.comp ((contraction A.coaction r : S →ₐ[R] S) : S →+* S) := by
  let _ : Algebra R B := (φ.comp (algebraMap R S)).toAlgebra
  let φ' : S →ₐ[R] B := { φ with commutes' := fun _ => rfl }
  have hcoe : ((φ' : S →+* B)) = φ := rfl
  have h : φ'.comp (contraction A.coaction r) = scale A.coaction φ' (φ (algebraMap R S r)) :=
    comp_contraction A.coaction φ' r
  have h2 : scaleRing A (φ (algebraMap R S r)) φ =
      ((scale A.coaction φ' (φ (algebraMap R S r)) : S →ₐ[R] B) : S →+* B) := by
    rw [← hcoe, scaleRing_coe]
  rw [h2, ← h]
  rfl

/-- The contraction of a ring-valued point lies over the base: it has the same structure map. -/
theorem scaleRing_comp_algebraMap (r : B) (φ : S →+* B) :
    (scaleRing A r φ).comp ((algebraMap R S : R →+* S)) = φ.comp (algebraMap R S) := by
  let _ : Algebra R B := (φ.comp (algebraMap R S)).toAlgebra
  let φ' : S →ₐ[R] B := { φ with commutes' := fun _ => rfl }
  have hcoe : ((φ' : S →+* B)) = φ := rfl
  rw [← hcoe, scaleRing_coe]
  exact RingHom.ext fun x => (scale A.coaction φ' r).commutes x

/-- The translate of a ring-valued point lies over the base: it has the same structure map. -/
theorem actOn_comp_algebraMap (b : Module.Basis σ R F) (φ : S →+* B) (v : σ → B) :
    (actOn A b φ v).comp ((algebraMap R S : R →+* S)) = φ.comp (algebraMap R S) := by
  let _ : Algebra R B := (φ.comp (algebraMap R S)).toAlgebra
  let φ' : S →ₐ[R] B := { φ with commutes' := fun _ => rfl }
  have hcoe : ((φ' : S →+* B)) = φ := rfl
  have h := actOn_eq_translate A b φ' v
  rw [hcoe] at h
  rw [h]
  exact RingHom.ext fun x => (translate A.act φ' (b.constr R v)).commutes x

/-- The contraction commutes with the action of the bundle: contracting a translate by `r` is
translating the contraction by `r · v`.  This is the defining equation of the contraction of the
quotient `[C/E]`, on ring-valued points. -/
theorem scaleRing_actOn (b : Module.Basis σ R F) (r : B) (φ : S →+* B) (v : σ → B) :
    scaleRing A r (actOn A b φ v) = actOn A b (scaleRing A r φ) (r • v) := by
  let _ : Algebra R B := (φ.comp (algebraMap R S)).toAlgebra
  let φ' : S →ₐ[R] B := { φ with commutes' := fun _ => rfl }
  have hcoe : ((φ' : S →+* B)) = φ := rfl
  have h1 := actOn_eq_translate A b φ' v
  rw [hcoe] at h1
  have h2 := actOn_eq_translate A b (scale A.coaction φ' r) (r • v)
  rw [h1, scaleRing_coe, A.scale_translate, ← hcoe, scaleRing_coe, h2, constr_smul]

end RingScale

/-! ### Points of the bundle and of the cone over an affine base -/

section ConePoints

open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {B : Type u} [CommRing B]

/-- The vector of `B` underlying a `Spec B`-point of the bundle `𝔾ₐ^σ`. -/
noncomputable def bundleVec
    (g : fppfYoneda.obj (coneScheme B) ⟶ (vectorBundleGroup σ).space.toSheaf) : σ → B :=
  fun i => gammaMapInv B (coords (fppfYoneda.preimage
    (g : fppfYoneda.obj (coneScheme B) ⟶ fppfYoneda.obj (bundleScheme σ))) i)

/-- A point of the bundle is the point attached to its vector. -/
@[simp]
theorem bundlePoint_bundleVec
    (g : fppfYoneda.obj (coneScheme B) ⟶ (vectorBundleGroup σ).space.toSheaf) :
    bundlePoint (bundleVec g) = g := by
  have h : (ofCoords fun i => gammaMap B (bundleVec g i)) = fppfYoneda.preimage
      (g : fppfYoneda.obj (coneScheme B) ⟶ fppfYoneda.obj (bundleScheme σ)) := by
    refine coords_injective ?_
    funext i
    rw [coords_ofCoords, bundleVec, gammaMap_gammaMapInv]
  rw [bundlePoint, h]
  exact fppfYoneda.map_preimage _

/-- The vector of the point attached to a vector is that vector. -/
@[simp]
theorem bundleVec_bundlePoint (v : σ → B) : bundleVec (bundlePoint v) = v :=
  bundlePoint_injective (bundlePoint_bundleVec _)

/-- The vector of the unit point is zero. -/
theorem bundleVec_one : bundleVec (σ := σ) (B := B) 1 = 0 := by
  rw [← bundlePoint_zero (σ := σ) (B := B), bundleVec_bundlePoint]

/-- The vector of a product of points is the sum of the vectors. -/
theorem bundleVec_mul (g g' : fppfYoneda.obj (coneScheme B) ⟶
    (vectorBundleGroup σ).space.toSheaf) :
    bundleVec (g * g') = bundleVec g + bundleVec g' :=
  bundlePoint_injective (by
    rw [bundlePoint_bundleVec, bundlePoint_add, bundlePoint_bundleVec, bundlePoint_bundleVec])

variable (A : ConeAction R S F) (b : Module.Basis σ R F)

/-- The ring map underlying a `Spec B`-point of the cone. -/
noncomputable def conePointHom
    (t : fppfYoneda.obj (coneScheme B) ⟶ (coneActionSpace A b).space.toSheaf) : S →+* B :=
  (gammaMapInv B).comp (conePt (fppfYoneda.preimage
    (t : fppfYoneda.obj (coneScheme B) ⟶ fppfYoneda.obj (coneScheme S))))

/-- A point of the cone is the point attached to its ring map. -/
@[simp]
theorem conePoint_conePointHom
    (t : fppfYoneda.obj (coneScheme B) ⟶ (coneActionSpace A b).space.toSheaf) :
    conePoint A b (conePointHom A b t) = t := by
  have h : ofConePt ((gammaMap B).comp (conePointHom A b t)) = fppfYoneda.preimage
      (t : fppfYoneda.obj (coneScheme B) ⟶ fppfYoneda.obj (coneScheme S)) := by
    refine conePt_injective ?_
    rw [conePt_ofConePt]
    exact RingHom.ext fun x => gammaMap_gammaMapInv _
  rw [conePoint, h]
  exact fppfYoneda.map_preimage _

/-- The ring map of the point attached to a ring map is that ring map. -/
@[simp]
theorem conePointHom_conePoint (φ : S →+* B) : conePointHom A b (conePoint A b φ) = φ :=
  conePoint_injective A b (conePoint_conePointHom A b _)

end ConePoints

/-! ### The contraction twist of the affine cone quotient -/

section ConeTwist

open GradedCone
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {B : Type u} [CommRing B]
variable (A : ConeAction R S F) (b : Module.Basis σ R F)

/-- The contraction of the quotient `[C/E]` over `Spec B` by a scalar `r : B`, as a twisting
datum: on the bundle it is multiplication by `r`, and on the cone it is the contraction `c_r`.
The compatibility `pt_smul` is the equivariance `c_r (v · x) = (r v) · c_r x`. -/
noncomputable def coneTwist (r : B) :
    ActionTwist (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B) where
  grp :=
    { toFun := fun g => bundlePoint (r • bundleVec g)
      map_one' := by rw [bundleVec_one, smul_zero, bundlePoint_zero]
      map_mul' := fun g g' => by rw [bundleVec_mul, smul_add, bundlePoint_add] }
  pt := fun t => conePoint A b (scaleRing A r (conePointHom A b t))
  pt_smul := by
    intro g t
    obtain ⟨v, rfl⟩ : ∃ v, bundlePoint v = g := ⟨bundleVec g, bundlePoint_bundleVec g⟩
    obtain ⟨φ, rfl⟩ : ∃ φ, conePoint A b φ = t :=
      ⟨conePointHom A b t, conePoint_conePointHom A b t⟩
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    rw [lift_bundlePoint_conePoint, conePointHom_conePoint, conePointHom_conePoint,
      bundleVec_bundlePoint, scaleRing_actOn, lift_bundlePoint_conePoint]

/-- The contraction twist on points of the cone. -/
@[simp]
theorem coneTwist_pt (r : B)
    (t : fppfYoneda.obj (coneScheme B) ⟶ (coneActionSpace A b).space.toSheaf) :
    (coneTwist A b r).pt t = conePoint A b (scaleRing A r (conePointHom A b t)) := rfl

/-- The contraction twist on points of the bundle. -/
@[simp]
theorem coneTwist_grp (r : B)
    (g : fppfYoneda.obj (coneScheme B) ⟶ (vectorBundleGroup σ).space.toSheaf) :
    (coneTwist A b r).grp g = bundlePoint (r • bundleVec g) := rfl

/-! #### The vertex -/

/-- The endomorphism of the coordinate ring of the cone which collapses it onto its vertex. -/
noncomputable def vertexHom (ε : S →ₐ[R] R) : S →+* S :=
  ((algebraMap R S : R →+* S)).comp (ε : S →+* R)

/-- Contracting a ring-valued point by `0` gives the vertex over the same point of the base. -/
theorem scaleRing_zero {ε : S →ₐ[R] R} (hv : IsConeVertex A.coaction ε) (φ : S →+* B) :
    scaleRing A (0 : B) φ = φ.comp (vertexHom ε) := by
  have h := scaleRing_algebraMap A (0 : R) φ
  rw [map_zero, map_zero] at h
  have h2 : ((contraction A.coaction (0 : R) : S →ₐ[R] S) : S →+* S) = vertexHom ε := by
    rw [hv]
    rfl
  rw [h, h2]

/-- Every contraction fixes the vertex. -/
theorem scaleRing_vertexHom {ε : S →ₐ[R] R} (hv : IsConeVertex A.coaction ε) (r : B)
    (φ : S →+* B) :
    scaleRing A r (φ.comp (vertexHom ε)) = φ.comp (vertexHom ε) := by
  let _ : Algebra R B := (φ.comp (algebraMap R S)).toAlgebra
  have hcoe : (((Algebra.ofId R B).comp ε : S →ₐ[R] B) : S →+* B) = φ.comp (vertexHom ε) :=
    RingHom.ext fun _ => rfl
  rw [← hcoe, scaleRing_coe, A.scale_vertex hv]

/-- The contraction does not change the point of the base underneath. -/
theorem scaleRing_comp_vertexHom (ε : S →ₐ[R] R) (r : B) (φ : S →+* B) :
    (scaleRing A r φ).comp (vertexHom ε) = φ.comp (vertexHom ε) := by
  rw [vertexHom, ← RingHom.comp_assoc, scaleRing_comp_algebraMap, RingHom.comp_assoc]

/-- Translating does not change the point of the base underneath. -/
theorem conePointHom_smul_eq {ε : S →ₐ[R] R}
    {x y : TrivialPoint (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B)} (f : x ⟶ y) :
    (conePointHom A b x.pt).comp (vertexHom ε) = (conePointHom A b y.pt).comp (vertexHom ε) := by
  have hx : x.pt = conePoint A b (actOn A b (conePointHom A b y.pt) (bundleVec f.val)) := by
    rw [← f.smul_eq, ← lift_bundlePoint_conePoint, bundlePoint_bundleVec,
      conePoint_conePointHom]
  rw [hx, conePointHom_conePoint, vertexHom, ← RingHom.comp_assoc, actOn_comp_algebraMap,
    RingHom.comp_assoc]

/-- The vertex section as an endofunctor of trivialised torsors: it sends every object to the
vertex lying over the same point of the base `Spec R`.  It factors through the base, so all its
arrows are the identity translation. -/
noncomputable def vertexFunctor (ε : S →ₐ[R] R) :
    TrivialPoint (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B) ⥤
      TrivialPoint (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B) where
  obj x := ⟨conePoint A b ((conePointHom A b x.pt).comp (vertexHom ε))⟩
  map {x y} f :=
    ⟨1, by
      rw [lift_one_smul]
      exact congrArg (conePoint A b) (conePointHom_smul_eq A b (ε := ε) f).symm⟩
  map_id x := TrivialPoint.Hom.ext _ _ rfl
  map_comp f g := TrivialPoint.Hom.ext _ _ (one_mul _).symm

/-- The vertex functor on objects. -/
@[simp]
theorem vertexFunctor_obj_pt (ε : S →ₐ[R] R)
    (x : TrivialPoint (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B)) :
    ((vertexFunctor A b ε).obj x).pt =
      conePoint A b ((conePointHom A b x.pt).comp (vertexHom ε)) := rfl

/-- The vertex functor on arrows. -/
@[simp]
theorem vertexFunctor_map_val (ε : S →ₐ[R] R)
    {x y : TrivialPoint (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B)} (f : x ⟶ y) :
    ((vertexFunctor A b ε).map f).val = 1 := rfl

/-! #### The contraction laws -/

/-- Contracting by `1` is the identity. -/
noncomputable def coneTwistOneIso :
    (coneTwist A b (1 : B)).functor ≅ 𝟭 _ :=
  ActionTwist.functorIsoId _
    (fun t => by rw [coneTwist_pt, scaleRing_one, conePoint_conePointHom])
    fun g => by rw [coneTwist_grp, one_smul, bundlePoint_bundleVec]

/-- Contracting by a product is contracting twice. -/
noncomputable def coneTwistMulIso (r s : B) :
    (coneTwist A b (r * s)).functor ≅
      (coneTwist A b s).functor ⋙ (coneTwist A b r).functor :=
  ActionTwist.functorIsoComp (coneTwist A b (r * s)) (coneTwist A b r) (coneTwist A b s)
    (fun t => by
      rw [coneTwist_pt, coneTwist_pt, coneTwist_pt, conePointHom_conePoint,
        scaleRing_scaleRing, mul_comm])
    fun g => by
      rw [coneTwist_grp, coneTwist_grp, coneTwist_grp, bundleVec_bundlePoint, smul_smul,
        mul_comm]

/-- Contracting by `0` is the vertex over the same point of the base. -/
noncomputable def coneTwistZeroIso {ε : S →ₐ[R] R} (hv : IsConeVertex A.coaction ε) :
    (coneTwist A b (0 : B)).functor ≅ vertexFunctor A b ε :=
  TrivialPoint.natIsoOfEq _ _
    (fun x => TrivialPoint.ext (by
      rw [ActionTwist.functor_obj_pt, coneTwist_pt, scaleRing_zero A hv]
      rfl))
    fun f => by
      rw [ActionTwist.functor_map_val, coneTwist_grp, zero_smul, bundlePoint_zero]
      rfl

/-- The vertex is fixed by every contraction. -/
noncomputable def coneTwistVertexIso {ε : S →ₐ[R] R} (hv : IsConeVertex A.coaction ε) (r : B) :
    vertexFunctor A b ε ⋙ (coneTwist A b r).functor ≅ vertexFunctor A b ε :=
  TrivialPoint.natIsoOfEq _ _
    (fun x => TrivialPoint.ext (by
      rw [Functor.comp_obj, ActionTwist.functor_obj_pt, coneTwist_pt, vertexFunctor_obj_pt,
        conePointHom_conePoint, scaleRing_vertexHom A hv]))
    fun f => by
      rw [Functor.comp_map, ActionTwist.functor_map_val, vertexFunctor_map_val, coneTwist_grp,
        bundleVec_one, smul_zero, bundlePoint_zero]

/-- Contraction is over the base: it does not move the underlying point of `Spec R`. -/
noncomputable def coneTwistProjectionIso (ε : S →ₐ[R] R) (r : B) :
    (coneTwist A b r).functor ⋙ vertexFunctor A b ε ≅ vertexFunctor A b ε :=
  TrivialPoint.natIsoOfEq _ _
    (fun x => TrivialPoint.ext (by
      rw [Functor.comp_obj, vertexFunctor_obj_pt, ActionTwist.functor_obj_pt, coneTwist_pt,
        conePointHom_conePoint, scaleRing_comp_vertexHom]
      rfl))
    fun f => by
      rw [Functor.comp_map, vertexFunctor_map_val]
      rfl

/-! #### Base change in the test ring -/

variable {D : Type u} [CommRing D]

/-- Points of the bundle are natural in the test ring. -/
theorem bundlePoint_naturality (g : B →+* D) (v : σ → B) :
    fppfYoneda.map (Spec.map (CommRingCat.ofHom g)) ≫ bundlePoint v =
      bundlePoint (σ := σ) fun i => g (v i) := by
  have key : fppfYoneda.map (Spec.map (CommRingCat.ofHom g)) ≫
      fppfYoneda.map (ofCoords fun i => gammaMap B (v i)) =
      fppfYoneda.map (ofCoords fun i => gammaMap D (g (v i))) := by
    rw [← Functor.map_comp]
    congr 1
    refine coords_injective ?_
    funext i
    rw [coords_comp, coords_ofCoords, coords_ofCoords]
    exact RingHom.congr_fun (gammaMap_naturality g) (v i)
  exact key

/-- The contraction commutes with base change in the test ring. -/
noncomputable def coneTwistPullbackIso (g : B →+* D) (r : B) :
    (coneTwist A b r).functor ⋙
        TrivialPoint.pullbackFunctor _ _ (Spec.map (CommRingCat.ofHom g)) ≅
      TrivialPoint.pullbackFunctor _ _ (Spec.map (CommRingCat.ofHom g)) ⋙
        (coneTwist A b (g r)).functor :=
  ActionTwist.pullbackIso (coneTwist A b r) (coneTwist A b (g r))
    (Spec.map (CommRingCat.ofHom g))
    (fun t => by
      obtain ⟨φ, rfl⟩ : ∃ φ, conePoint A b φ = t :=
        ⟨conePointHom A b t, conePoint_conePointHom A b t⟩
      rw [coneTwist_pt, coneTwist_pt, conePoint_naturality, conePointHom_conePoint,
        conePointHom_conePoint, conePoint_naturality, comp_scaleRing])
    fun h => by
      obtain ⟨v, rfl⟩ : ∃ v, bundlePoint v = h := ⟨bundleVec h, bundlePoint_bundleVec h⟩
      rw [coneTwist_grp, coneTwist_grp, bundlePoint_naturality, bundleVec_bundlePoint,
        bundleVec_bundlePoint, bundlePoint_naturality]
      congr 1
      funext i
      exact (map_mul g r (v i)).symm

end ConeTwist

/-! ### Comparison with the contraction of the quotient groupoid -/

section Comparison

open GradedCone
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {B : Type u} [CommRing B] [Algebra R B]
variable (A : ConeAction R S F) (b : Module.Basis σ R F)

/-- A scalar of the test algebra can be pulled out of the inverse of `Basis.constr`. -/
theorem constr_symm_smul (r : B) (l : F →ₗ[R] B) :
    (b.constr R).symm (r • l) = r • (b.constr R).symm l := by
  refine (b.constr R).injective ?_
  rw [LinearEquiv.apply_symm_apply, constr_smul, LinearEquiv.apply_symm_apply]

/-- The comparison functor from the quotient groupoid `[C/E](B)` to the trivialised torsors over
`Spec B`.  Composing it with `TrivialPoint.embedding` is `trivialTorsorFunctor`. -/
noncomputable def quotientToTrivialPoint :
    QuotientGroupoid A B ⥤
      TrivialPoint (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B) where
  obj x := ⟨conePoint A b (x.point : S →+* B)⟩
  map {x y} f :=
    ⟨bundlePoint ((b.constr R).symm (-f.val)),
      torsorOfPoint_condition A b (-f.val) (by
        rw [← f.translate_eq, A.act_add, add_neg_cancel, A.act_zero])⟩
  map_id x := TrivialPoint.Hom.ext _ _ (by
    have h1 : bundlePoint ((b.constr R).symm (-(𝟙 x : x ⟶ x).val)) = 1 := by
      rw [QuotientGroupoid.id_val, neg_zero, map_zero, bundlePoint_zero]
    exact h1)
  map_comp f g := TrivialPoint.Hom.ext _ _ (by
    have h1 : bundlePoint ((b.constr R).symm (-(f ≫ g).val)) =
        bundlePoint ((b.constr R).symm (-f.val)) *
          bundlePoint ((b.constr R).symm (-g.val)) := by
      rw [QuotientGroupoid.comp_val, neg_add, map_add, bundlePoint_add]
    exact h1)

/-- The comparison functor on objects. -/
@[simp]
theorem quotientToTrivialPoint_obj_pt (x : QuotientGroupoid A B) :
    ((quotientToTrivialPoint A b).obj x).pt = conePoint A b (x.point : S →+* B) := rfl

/-- The comparison functor on arrows. -/
@[simp]
theorem quotientToTrivialPoint_map_val {x y : QuotientGroupoid A B} (f : x ⟶ y) :
    ((quotientToTrivialPoint A b).map f).val = bundlePoint ((b.constr R).symm (-f.val)) := rfl

/-- On trivialised torsors the contraction twist *is* the contraction of the quotient groupoid
`[C/E](B)`: the two functors are naturally isomorphic. -/
noncomputable def contractionComparison (r : B) :
    quotientToTrivialPoint A b ⋙ (coneTwist A b r).functor ≅
      QuotientGroupoid.contractionFunctor A B r ⋙ quotientToTrivialPoint A b :=
  TrivialPoint.natIsoOfEq _ _
    (fun x => TrivialPoint.ext (by
      rw [Functor.comp_obj, ActionTwist.functor_obj_pt, quotientToTrivialPoint_obj_pt,
        coneTwist_pt, conePointHom_conePoint, scaleRing_coe]
      rfl))
    fun f => by
      rw [Functor.comp_map, Functor.comp_map, ActionTwist.functor_map_val,
        quotientToTrivialPoint_map_val, coneTwist_grp, bundleVec_bundlePoint,
        quotientToTrivialPoint_map_val, QuotientGroupoid.contractionFunctor_map_val,
        ← smul_neg, constr_symm_smul]

/-- The comparison functor of `QuotientTorsor` factors through the trivialised torsors. -/
theorem quotientToTrivialPoint_comp_embedding :
    quotientToTrivialPoint A b ⋙
        TrivialPoint.embedding (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B) =
      trivialTorsorFunctor A b :=
  rfl

/-- The contraction of *all* `E`-torsors over `Spec B` with an equivariant map to the cone.  It
depends on the hypothesis that every `E`-torsor over `Spec B` is trivial, i.e. on the vanishing
of `H¹(Spec B, E)`, which is *not* proved here. -/
noncomputable def coneTorsorContraction (r : B)
    (h : AllTorsorsTrivial (vectorBundleGroup σ) (coneScheme B)) :
    ActionTorsor (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B) ⥤
      ActionTorsor (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B) :=
  (coneTwist A b r).torsorContraction h

/-- The contraction of torsors agrees, on the trivial torsors coming from `B`-points of the
cone, with the contraction of the quotient groupoid `[C/E](B)`.  By
`quotientToTrivialPoint_comp_embedding` the two outer composites are `trivialTorsorFunctor`;
they are spelled out here so that the statement typechecks without an expensive unfolding. -/
noncomputable def coneTorsorContractionComparison (r : B)
    (h : AllTorsorsTrivial (vectorBundleGroup σ) (coneScheme B)) :
    quotientToTrivialPoint A b ⋙
        (TrivialPoint.embedding (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B) ⋙
          coneTorsorContraction A b r h) ≅
      (QuotientGroupoid.contractionFunctor A B r ⋙ quotientToTrivialPoint A b) ⋙
        TrivialPoint.embedding (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B) :=
  (Functor.isoWhiskerLeft (quotientToTrivialPoint A b)
      ((coneTwist A b r).embeddingTorsorContractionIso h)).trans
    ((Functor.associator (quotientToTrivialPoint A b) (coneTwist A b r).functor
        (TrivialPoint.embedding (vectorBundleGroup σ) (coneActionSpace A b)
          (coneScheme B))).symm.trans
      (Functor.isoWhiskerRight (contractionComparison A b r)
        (TrivialPoint.embedding (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B))))

/-- Contracting all torsors by `1` is the identity, under the triviality hypothesis. -/
noncomputable def coneTorsorContractionOneIso
    (h : AllTorsorsTrivial (vectorBundleGroup σ) (coneScheme B)) :
    coneTorsorContraction A b (1 : B) h ≅ 𝟭 _ :=
  (coneTwist A b (1 : B)).torsorContractionIsoId h (coneTwistOneIso A b (B := B))

end Comparison

end ConeQuotient

end GromovWitten.AlgebraicGeometry
