/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.SheafGluing
import GromovWitten.AlgebraicGeometry.Cones.QuotientTorsorStack

/-!
# The pushout of an fppf torsor along a homomorphism of group objects

Let `G` and `G'` be group algebraic spaces, `r : G ⟶ G'` a homomorphism of the underlying group
objects of fppf sheaves, and `P` a `G`-torsor over a scheme `T`.  The *pushout* `r_* P` is the
`G'`-torsor whose sections are the `G`-equivariant maps `φ : P ⟶ G'`, where `G` acts on `G'`
through `r`.  Classically one writes `r_* P = (P × G')/G`; both descriptions involve a
sheafification, which is not available for `Sheaf Scheme.fppfTopology (Type u)` for universe
reasons (a hom sheaf of the big fppf site is not `Type u`-valued).

This file constructs `r_* P` unconditionally, for every fppf torsor `P`, by descent along the
trivialising cover of `P`; no sheafification and no hom sheaf occur anywhere.

## Points of a torsor

`TorsorPushout.actPt g p` is the action of a generalised point `g` of a group object on a
generalised point `p` of a module object, and `TorsorPushout.divPt P p q h` is the unique point
of `G` carrying `q` to `p`, extracted from the principality isomorphism of the torsor
(`actPt_divPt`, `eq_divPt`, `exists_unique_actPt`).  This is the usual "difference" of two points
of a torsor, with its cocycle calculus (`divPt_self`, `divPt_mul`, `comp_divPt`).

## The pushout datum

`TorsorPushout.PushoutTorsor r P` packages a sheaf `A` over `T` with a `G'`-action together with
the *evaluation* pairing `ev α p : fppfYoneda.obj W ⟶ G'` of a point of `A` against a point of
`P` over the same base, subject to the two equivariance rules
`ev (g' · α) p = g' * ev α p`, `ev α (g · p) = ev α p * (r g)⁻¹`, and the requirement that, for a
fixed point `p` of `P`, evaluation is a bijection from the fibre of `A` to the points of `G'`.
This is exactly the datum "`A` is the sheaf of `G`-equivariant maps `P ⟶ G'`", written without
ever forming a hom sheaf.  Everything else is *derived*:

* `PushoutTorsor.toFppfTorsor`: `A` is an fppf `G'`-torsor over `T`.  In particular the
  principality isomorphism (`PushoutTorsor.isIso_principalMap`, through
  `SheafGluing.isIso_of_sections`) and the local triviality (`PushoutTorsor.localSection`) are
  theorems, not hypotheses.
* `PushoutTorsor.ev_injective` and `PushoutTorsor.exists_unique_actPt_sheaf`: the fibres of `A`
  over a base point carrying a point of `P` are simply transitive `G'`-sets.

## The construction

Let `f : X ⟶ T` be the chosen trivialising cover of `P` and `L` its tautological section.

* `TorsorPushout.coverDiv` is the transition cocycle `L a / L b` of `P` and
  `TorsorPushout.descentDatum P r` is the descent datum of the trivial `G'`-torsor over `X`
  glued by right translation by `r (coverDiv)`.
* `TorsorPushout.pushoutSheaf P r` is the sheaf glued from that datum
  (`SheafGluing.glueSheaf`), `pushoutProj` its structure morphism, `pushoutSmul` the `G'`-action
  (`pushoutAction`, through the pointwise criterion `modObjOfPoints`), and `pushoutSmul_proj`
  says the action is fibrewise.
* `TorsorPushout.coordAt`, `ptOfCoord` are the local trivialisations of the glued sheaf, and
  `TorsorPushout.evLocal` is the local evaluation formula
  `ev α p = coord (α) * r (p / L c)⁻¹`, independent of the chosen lift `c` of the base
  (`evLocal_lift_congr`).
* `TorsorPushout.evMap`, `evPt` glue the local formula to the evaluation pairing
  (`SheafGluing.PartialHom.glue`), and `ptOfEv` produces a point of the pushout with a
  prescribed value at a given point of `P`.
* `TorsorPushout.pushoutTorsor P r : PushoutTorsor r P` assembles everything, and
  `TorsorPushout.pushoutFppfTorsor P r : FppfTorsor G' T` is the pushout torsor itself.

## The contraction of an action torsor

For `P : ActionTorsor G U T` and an `r`-equivariant morphism `pt : U ⟶ U'` of action spaces
(`TorsorPushout.IsEquivariantOver`), `TorsorPushout.targetMap` is the induced equivariant map
`r_* P ⟶ U'`, glued from the local formula `α ↦ α (L c) · pt (L c)` (`targetLocal`), which is
independent of the chosen lift `c` (`targetLocal_lift_congr`).  It is `G'`-equivariant
(`targetMap_equivariant`), so `TorsorPushout.pushoutActionTorsor` is the contraction
`r_* P : ActionTorsor G' U' T`.

What is *not* done here: the functoriality of `r_*` in `r` and in `P` (its action on arrows of
torsors, `(𝟙 G)_* P ≅ P`, `(r ∘ s)_* ≅ r_* ∘ s_*`, `r_* G ≅ G'`), and the uniqueness of a
pushout datum.  Note also that `ConeQuotient.ActionTwist` twists the `T`-points only, so it is
not a homomorphism of group objects `G ⟶ G'`; relating the two requires group objects relative
to `T`.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

namespace TorsorPushout

universe u

/-! ### The action of generalised points -/

section ActionPoints

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {M X : C} [MonObj M] [ModObj M X]

/-- A point of a binary product is the lift of its two components. -/
@[simp]
theorem lift_comp_fst_snd {D : Type*} [Category D] [CartesianMonoidalCategory D] {X Y Z : D}
    (ω : Z ⟶ X ⊗ Y) : lift (ω ≫ fst X Y) (ω ≫ snd X Y) = ω := by
  ext <;> simp

/-- The action of a generalised point `g` of a monoid object `M` on a generalised point `p` of
an `M`-module object `X`. -/
def actPt {Z : C} (g : Z ⟶ M) (p : Z ⟶ X) : Z ⟶ X :=
  lift g p ≫ ModObj.smul (M := M) (X := X)

/-- The unit of the monoid object acts trivially on points. -/
@[simp]
theorem actPt_one {Z : C} (p : Z ⟶ X) : actPt (1 : Z ⟶ M) p = p :=
  ConeQuotient.lift_one_smul p

/-- The action on points is compatible with the multiplication of the monoid object. -/
theorem actPt_mul {Z : C} (a b : Z ⟶ M) (p : Z ⟶ X) :
    actPt (a * b) p = actPt a (actPt b p) :=
  ConeQuotient.lift_mul_smul a b p

/-- The action on points is natural: it commutes with precomposition. -/
theorem comp_actPt {Y Z : C} (u : Y ⟶ Z) (g : Z ⟶ M) (p : Z ⟶ X) :
    u ≫ actPt g p = actPt (u ≫ g) (u ≫ p) := by
  rw [actPt, actPt, ← Category.assoc, comp_lift]

end ActionPoints

section GroupActionPoints

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {M X : C} [GrpObj M] [ModObj M X]

/-- An action which is fibrewise over a morphism `π` does not change the image under `π`. -/
theorem actPt_comp_over {C : Type*} [Category C] [CartesianMonoidalCategory C] {M X Y : C}
    [MonObj M] [ModObj M X] (π : X ⟶ Y)
    (hover : ModObj.smul (M := M) (X := X) ≫ π = snd M X ≫ π) {Z : C} (g : Z ⟶ M) (p : Z ⟶ X) :
    actPt g p ≫ π = p ≫ π := by
  rw [actPt, Category.assoc, hover, ← Category.assoc, lift_snd]

/-- Acting by an inverse undoes the action, for a group object. -/
theorem actPt_inv_actPt {Z : C} (g : Z ⟶ M) (p : Z ⟶ X) :
    actPt g⁻¹ (actPt g p) = p := by
  rw [← actPt_mul, inv_mul_cancel, actPt_one]

end GroupActionPoints

/-! ### Differences of points of a torsor -/

section TorsorPoints

variable {G : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} (P : FppfTorsor G T)

/-- Translating a point of a torsor does not change its image in the base. -/
@[simp]
theorem actPt_proj {Z : FppfSheaf.{u}} (g : Z ⟶ G.space.toSheaf) (p : Z ⟶ P.P) :
    actPt g p ≫ P.projection = p ≫ P.projection :=
  actPt_comp_over P.projection P.action_over g p

/-- The point of `G ⊗ P` produced by the principality isomorphism from two points of the torsor
with the same image in the base. -/
noncomputable def divAux {Z : FppfSheaf.{u}} (p q : Z ⟶ P.P)
    (h : p ≫ P.projection = q ≫ P.projection) : Z ⟶ G.space.toSheaf ⊗ P.P :=
  pullback.lift p q h ≫ inv P.principalMap

/-- The unique point of `G` carrying `q` to `p`, for two points of the torsor with the same
image in the base. -/
noncomputable def divPt {Z : FppfSheaf.{u}} (p q : Z ⟶ P.P)
    (h : p ≫ P.projection = q ≫ P.projection) : Z ⟶ G.space.toSheaf :=
  divAux P p q h ≫ fst G.space.toSheaf P.P

variable {P}

/-- The principality isomorphism sends `divAux` back to the pair of points. -/
theorem divAux_principalMap {Z : FppfSheaf.{u}} (p q : Z ⟶ P.P)
    (h : p ≫ P.projection = q ≫ P.projection) :
    divAux P p q h ≫ P.principalMap = pullback.lift p q h := by
  rw [divAux, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The second component of `divAux` is the second point. -/
theorem divAux_snd {Z : FppfSheaf.{u}} (p q : Z ⟶ P.P)
    (h : p ≫ P.projection = q ≫ P.projection) :
    divAux P p q h ≫ snd G.space.toSheaf P.P = q := by
  rw [← P.principal_snd, ← Category.assoc, divAux_principalMap, pullback.lift_snd]

/-- Acting by `divAux` sends the second point to the first. -/
theorem divAux_smul {Z : FppfSheaf.{u}} (p q : Z ⟶ P.P)
    (h : p ≫ P.projection = q ≫ P.projection) :
    divAux P p q h ≫ ModObj.smul (M := G.space.toSheaf) (X := P.P) = p := by
  rw [← P.principal_fst, ← Category.assoc, divAux_principalMap, pullback.lift_fst]

/-- **Transitivity of the torsor action on points.**  The difference point carries `q` to `p`. -/
@[simp]
theorem actPt_divPt {Z : FppfSheaf.{u}} (p q : Z ⟶ P.P)
    (h : p ≫ P.projection = q ≫ P.projection) : actPt (divPt P p q h) q = p := by
  have hsnd := divAux_snd p q h
  calc actPt (divPt P p q h) q
      = lift (divAux P p q h ≫ fst G.space.toSheaf P.P)
        (divAux P p q h ≫ snd G.space.toSheaf P.P) ≫
          ModObj.smul (M := G.space.toSheaf) (X := P.P) := by rw [hsnd]; rfl
    _ = divAux P p q h ≫ ModObj.smul (M := G.space.toSheaf) (X := P.P) := by
        rw [← comp_lift, lift_fst_snd, Category.comp_id]
    _ = p := divAux_smul p q h

/-- **Freeness of the torsor action on points.**  Any point carrying `q` to `p` is the
difference point. -/
theorem eq_divPt {Z : FppfSheaf.{u}} (p q : Z ⟶ P.P)
    (h : p ≫ P.projection = q ≫ P.projection) (g : Z ⟶ G.space.toSheaf)
    (hg : actPt g q = p) : g = divPt P p q h := by
  have key : lift g q ≫ P.principalMap = pullback.lift p q h := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, P.principal_fst, pullback.lift_fst]
      exact hg
    · rw [Category.assoc, P.principal_snd, lift_snd, pullback.lift_snd]
  have hlift : lift g q = divAux P p q h := by
    rw [divAux, ← key, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [divPt, ← hlift, lift_fst]

/-- **The torsor action on points is simply transitive.** -/
theorem exists_unique_actPt {Z : FppfSheaf.{u}} (p q : Z ⟶ P.P)
    (h : p ≫ P.projection = q ≫ P.projection) :
    ∃! g : Z ⟶ G.space.toSheaf, actPt g q = p :=
  ⟨divPt P p q h, actPt_divPt p q h, fun g hg => eq_divPt p q h g hg⟩

/-- Two points of the group acting equally on a point of the torsor are equal. -/
theorem actPt_left_cancel {Z : FppfSheaf.{u}} {g g' : Z ⟶ G.space.toSheaf} {p : Z ⟶ P.P}
    (hgg : actPt g p = actPt g' p) : g = g' := by
  have h : actPt g p ≫ P.projection = p ≫ P.projection := actPt_proj P g p
  rw [eq_divPt (actPt g p) p h g rfl, eq_divPt (actPt g p) p h g' hgg.symm]

/-- A point of the group fixing a point of the torsor is the unit. -/
theorem eq_one_of_actPt_eq {Z : FppfSheaf.{u}} {g : Z ⟶ G.space.toSheaf} {p : Z ⟶ P.P}
    (hg : actPt g p = p) : g = 1 :=
  actPt_left_cancel (P := P) (by rw [hg, actPt_one])

/-- The difference of a point with itself is the unit. -/
@[simp]
theorem divPt_self {Z : FppfSheaf.{u}} (p : Z ⟶ P.P)
    (h : p ≫ P.projection = p ≫ P.projection) : divPt P p p h = 1 :=
  (eq_divPt p p h 1 (actPt_one p)).symm

/-- The difference point only depends on the two points. -/
theorem divPt_congr {Z : FppfSheaf.{u}} {p p' q q' : Z ⟶ P.P} (hp : p = p') (hq : q = q')
    (h : p ≫ P.projection = q ≫ P.projection)
    (h' : p' ≫ P.projection = q' ≫ P.projection) : divPt P p q h = divPt P p' q' h' := by
  subst hp
  subst hq
  rfl

/-- The difference point is natural in the test object. -/
theorem comp_divPt {Y Z : FppfSheaf.{u}} (u : Y ⟶ Z) (p q : Z ⟶ P.P)
    (h : p ≫ P.projection = q ≫ P.projection)
    (h' : u ≫ p ≫ P.projection = u ≫ q ≫ P.projection) :
    u ≫ divPt P p q h = divPt P (u ≫ p) (u ≫ q) (by
      rw [Category.assoc, Category.assoc]; exact h') :=
  eq_divPt _ _ _ _ (by rw [← comp_actPt, actPt_divPt])

/-- The cocycle rule for difference points. -/
theorem divPt_mul {Z : FppfSheaf.{u}} (p q s : Z ⟶ P.P)
    (h₁ : p ≫ P.projection = q ≫ P.projection) (h₂ : q ≫ P.projection = s ≫ P.projection) :
    divPt P p q h₁ * divPt P q s h₂ = divPt P p s (h₁.trans h₂) :=
  eq_divPt _ _ _ _ (by rw [actPt_mul, actPt_divPt, actPt_divPt])

/-- The difference point of a translated pair. -/
theorem divPt_actPt_left {Z : FppfSheaf.{u}} (g : Z ⟶ G.space.toSheaf) (p q : Z ⟶ P.P)
    (h : p ≫ P.projection = q ≫ P.projection)
    (h' : actPt g p ≫ P.projection = q ≫ P.projection) :
    divPt P (actPt g p) q h' = g * divPt P p q h :=
  (eq_divPt _ _ _ _ (by rw [actPt_mul, actPt_divPt])).symm

/-- Inverting a difference point exchanges the two points. -/
theorem divPt_symm {Z : FppfSheaf.{u}} (p q : Z ⟶ P.P)
    (h : p ≫ P.projection = q ≫ P.projection) :
    (divPt P p q h)⁻¹ = divPt P q p h.symm := by
  rw [← mul_left_cancel_iff (a := divPt P p q h), mul_inv_cancel, divPt_mul, divPt_self]

end TorsorPoints

/-! ### The trivialising cover of a torsor -/

section Cover

variable {G : AlgebraicSpaceGroup.{u}} {T W : Scheme.{u}} (P : FppfTorsor G T)

/-- The covering sieve generated by the chosen trivialising cover of a torsor. -/
def coverSieve : Sieve T :=
  Sieve.generate (Presieve.singleton P.locallyTrivial.cover)

/-- The trivialising cover of a torsor generates an fppf covering sieve. -/
theorem coverSieve_mem : coverSieve P ∈ Scheme.fppfTopology T := by
  have h1 := P.locallyTrivial.flat
  have h2 := P.locallyTrivial.surjective
  have h3 := P.locallyTrivial.locallyOfFinitePresentation
  exact Precoverage.generate_mem_toGrothendieck
    (Scheme.Hom.singleton_mem_fppfPrecoverage P.locallyTrivial.cover)

variable {P}

/-- Every member of the covering sieve of a torsor factors through the trivialising cover. -/
theorem exists_factor_of_coverSieve {g : W ⟶ T} (hg : (coverSieve P).arrows g) :
    ∃ c : W ⟶ P.locallyTrivial.coverScheme, c ≫ P.locallyTrivial.cover = g := by
  obtain ⟨Y, c, u, hu, rfl⟩ := hg
  cases hu
  exact ⟨c, rfl⟩

/-- The tautological point of the torsor above a morphism to the trivialising cover. -/
noncomputable def coverPt (c : W ⟶ P.locallyTrivial.coverScheme) :
    fppfYoneda.obj W ⟶ P.P :=
  fppfYoneda.map c ≫ P.locallyTrivial.localLift

/-- The tautological point lies above the given morphism to the base. -/
theorem coverPt_proj (c : W ⟶ P.locallyTrivial.coverScheme) :
    coverPt c ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
  rw [coverPt, Category.assoc, P.locallyTrivial.localLift_over, ← Functor.map_comp]

end Cover

/-! ### Elementary dictionary between sections and points -/

section Dictionary

/-- The inverse of the Yoneda bijection on a representable sheaf is the image of the
morphism. -/
theorem yonedaEquiv_symm_map {V W : Scheme.{u}} (b : V ⟶ W) :
    Scheme.fppfTopology.yonedaEquiv.symm b = fppfYoneda.map b := by
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, GrothendieckTopology.yonedaEquiv_yoneda_map]

/-- A morphism of sheaves takes a point to a prescribed section exactly when the composite is
the corresponding point. -/
theorem app_eq_iff_comp {A B : FppfSheaf.{u}} (φ : A ⟶ B) {W : Scheme.{u}}
    (ω : fppfYoneda.obj W ⟶ A) (y : B.obj.obj (op W)) :
    φ.hom.app (op W) (Scheme.fppfTopology.yonedaEquiv ω) = y ↔
      ω ≫ φ = Scheme.fppfTopology.yonedaEquiv.symm y := by
  rw [← GrothendieckTopology.yonedaEquiv_comp]
  constructor
  · intro h
    rw [← h, Equiv.symm_apply_apply]
  · intro h
    rw [h, Equiv.apply_symm_apply]

end Dictionary

/-! ### The pushout datum -/

section Pushout

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}

/-- **The pushout `r_* P` of a `G`-torsor `P` along a homomorphism `r : G ⟶ G'`**, presented by
its defining property rather than by a construction.

A point of `r_* P` over a scheme `W` is a `G`-equivariant map `φ` from the fibre of `P` over `W`
to `G'`, where `G` acts on `G'` through `r`; `ev α p` is the value `φ (p)` of the equivariant
map `α` at a point `p` of `P`.  The equivariance rules are `ev (g' · α) p = g' * ev α p` and
`ev α (g · p) = ev α p * (r g)⁻¹`, and `ev` identifies the fibre of `r_* P` over `W` with the
points of `G'` over `W` as soon as `P` has a point over `W`.

No sheafification and no hom sheaf occur: the data is the sheaf itself together with the
evaluation pairing on points. -/
structure PushoutTorsor (r : G.space.toSheaf ⟶ G'.space.toSheaf) (P : FppfTorsor G T) where
  /-- The underlying fppf sheaf of the pushout. -/
  sheaf : FppfSheaf.{u}
  /-- The action of `G'` on the pushout. -/
  action : ModObj G'.space.toSheaf sheaf
  /-- The structure morphism to the base. -/
  projection : sheaf ⟶ fppfYoneda.obj T
  /-- The action of `G'` preserves the fibres over the base. -/
  action_over : ModObj.smul (M := G'.space.toSheaf) (X := sheaf) ≫ projection =
    snd G'.space.toSheaf sheaf ≫ projection
  /-- Evaluation of a point of the pushout at a point of `P` lying over the same base point. -/
  ev : ∀ {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ sheaf) (p : fppfYoneda.obj W ⟶ P.P),
    α ≫ projection = p ≫ P.projection → (fppfYoneda.obj W ⟶ G'.space.toSheaf)
  /-- Evaluation is natural in the test scheme. -/
  ev_naturality : ∀ {V W : Scheme.{u}} (u : V ⟶ W) (α : fppfYoneda.obj W ⟶ sheaf)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ projection = p ≫ P.projection)
    (h' : (fppfYoneda.map u ≫ α) ≫ projection = (fppfYoneda.map u ≫ p) ≫ P.projection),
    fppfYoneda.map u ≫ ev α p h = ev (fppfYoneda.map u ≫ α) (fppfYoneda.map u ≫ p) h'
  /-- Evaluation is equivariant for the action of `G'` on the pushout. -/
  ev_actPt : ∀ {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (α : fppfYoneda.obj W ⟶ sheaf) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ projection = p ≫ P.projection)
    (h' : actPt g' α ≫ projection = p ≫ P.projection),
    ev (actPt g' α) p h' = g' * ev α p h
  /-- Evaluation is equivariant for the action of `G` on `P`, through `r`. -/
  ev_actPt_right : ∀ {W : Scheme.{u}} (g : fppfYoneda.obj W ⟶ G.space.toSheaf)
    (α : fppfYoneda.obj W ⟶ sheaf) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ projection = p ≫ P.projection)
    (h' : α ≫ projection = actPt g p ≫ P.projection),
    ev α (actPt g p) h' = ev α p h * (g ≫ r)⁻¹
  /-- Evaluation at a point of `P` is a bijection from the fibre of the pushout to the points
  of `G'`. -/
  ev_bijective : ∀ {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf),
    ∃! α : {α : fppfYoneda.obj W ⟶ sheaf // α ≫ projection = p ≫ P.projection},
      ev α.1 p α.2 = g'

attribute [instance] PushoutTorsor.action

namespace PushoutTorsor

variable {r : G.space.toSheaf ⟶ G'.space.toSheaf} {P : FppfTorsor G T} (A : PushoutTorsor r P)

/-- Evaluation only depends on the point of the pushout, not on the proof that it lies over the
right base point. -/
theorem ev_congr_left {W : Scheme.{u}} {α β : fppfYoneda.obj W ⟶ A.sheaf} (hαβ : α = β)
    (p : fppfYoneda.obj W ⟶ P.P) (hα : α ≫ A.projection = p ≫ P.projection)
    (hβ : β ≫ A.projection = p ≫ P.projection) : A.ev α p hα = A.ev β p hβ := by
  subst hαβ
  rfl

/-- Evaluation only depends on the point of `P`, not on the proof that it lies over the right
base point. -/
theorem ev_congr_right {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ A.sheaf)
    {p q : fppfYoneda.obj W ⟶ P.P} (hpq : p = q)
    (hp : α ≫ A.projection = p ≫ P.projection)
    (hq : α ≫ A.projection = q ≫ P.projection) : A.ev α p hp = A.ev α q hq := by
  subst hpq
  rfl

/-- The action of `G'` on the pushout preserves the fibres over the base. -/
@[simp]
theorem actPt_projection {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (α : fppfYoneda.obj W ⟶ A.sheaf) :
    actPt g' α ≫ A.projection = α ≫ A.projection :=
  actPt_comp_over A.projection A.action_over g' α

/-- **Evaluation at a point of `P` is injective on the fibre of the pushout.** -/
theorem ev_injective {W : Scheme.{u}} {α β : fppfYoneda.obj W ⟶ A.sheaf}
    (p : fppfYoneda.obj W ⟶ P.P) (hα : α ≫ A.projection = p ≫ P.projection)
    (hβ : β ≫ A.projection = p ≫ P.projection) (h : A.ev α p hα = A.ev β p hβ) : α = β := by
  obtain ⟨a₀, -, huniq⟩ := A.ev_bijective p (A.ev α p hα)
  exact congrArg Subtype.val ((huniq ⟨α, hα⟩ rfl).trans (huniq ⟨β, hβ⟩ h.symm).symm)

/-- **The action of `G'` is simply transitive on the fibres of the pushout above a base point
carrying a point of `P`.** -/
theorem exists_unique_actPt_sheaf {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    {α β : fppfYoneda.obj W ⟶ A.sheaf} (hα : α ≫ A.projection = p ≫ P.projection)
    (hβ : β ≫ A.projection = p ≫ P.projection) :
    ∃! g' : fppfYoneda.obj W ⟶ G'.space.toSheaf, actPt g' α = β := by
  refine ⟨A.ev β p hβ * (A.ev α p hα)⁻¹, ?_, ?_⟩
  · refine A.ev_injective p (by rw [A.actPt_projection, hα]) hβ ?_
    rw [A.ev_actPt _ _ _ hα, inv_mul_cancel_right]
  · intro g hg
    have h1 : g * A.ev α p hα = A.ev β p hβ := by
      rw [← A.ev_actPt g α p hα (by rw [A.actPt_projection, hα])]
      exact A.ev_congr_left hg p _ hβ
    rw [← h1, mul_inv_cancel_right]

/-- The principality morphism of the pushout. -/
noncomputable def principalMap :
    G'.space.toSheaf ⊗ A.sheaf ⟶ pullback A.projection A.projection :=
  pullback.lift (ModObj.smul (M := G'.space.toSheaf) (X := A.sheaf))
    (snd G'.space.toSheaf A.sheaf) A.action_over

/-- The first component of the principality morphism is the action. -/
@[simp]
theorem principalMap_fst :
    A.principalMap ≫ pullback.fst A.projection A.projection =
      ModObj.smul (M := G'.space.toSheaf) (X := A.sheaf) :=
  pullback.lift_fst _ _ _

/-- The second component of the principality morphism is the projection. -/
@[simp]
theorem principalMap_snd :
    A.principalMap ≫ pullback.snd A.projection A.projection = snd G'.space.toSheaf A.sheaf :=
  pullback.lift_snd _ _ _

/-- **The principality morphism of the pushout is an isomorphism.** -/
theorem isIso_principalMap : IsIso A.principalMap := by
  refine GromovWitten.SheafGluing.isIso_of_sections
    (ModObj.smul (M := G'.space.toSheaf) (X := A.sheaf) ≫ A.projection)
    (pullback.fst A.projection A.projection ≫ A.projection) (coverSieve_mem P) A.principalMap
    (by rw [← Category.assoc, A.principalMap_fst]) ?_
  intro W y
  obtain ⟨c, hc⟩ := exists_factor_of_coverSieve y.2
  set ρ := Scheme.fppfTopology.yonedaEquiv.symm y.1 with hρ
  have hbase : ρ ≫ pullback.fst A.projection A.projection ≫ A.projection =
      fppfYoneda.map (GromovWitten.SheafGluing.base
        (pullback.fst A.projection A.projection ≫ A.projection) y.1) := by
    rw [hρ, GrothendieckTopology.yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_map]
    rfl
  have hβ₁ : (ρ ≫ pullback.fst A.projection A.projection) ≫ A.projection =
      coverPt c ≫ P.projection := by
    rw [Category.assoc, hbase, coverPt_proj, hc]
  have hβ₂ : (ρ ≫ pullback.snd A.projection A.projection) ≫ A.projection =
      coverPt c ≫ P.projection := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hβ₁]
  obtain ⟨g', hg', huniq⟩ := A.exists_unique_actPt_sheaf (coverPt c) hβ₂ hβ₁
  have hlift : lift g' (ρ ≫ pullback.snd A.projection A.projection) ≫ A.principalMap = ρ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, A.principalMap_fst]
      exact hg'
    · rw [Category.assoc, A.principalMap_snd, lift_snd]
  refine ⟨Scheme.fppfTopology.yonedaEquiv
    (lift g' (ρ ≫ pullback.snd A.projection A.projection)), ?_, ?_⟩
  · exact (app_eq_iff_comp A.principalMap _ y.1).mpr hlift
  · intro x hx
    set ω := Scheme.fppfTopology.yonedaEquiv.symm x with hω
    have hxω : Scheme.fppfTopology.yonedaEquiv ω = x := by
      rw [hω, Equiv.apply_symm_apply]
    have hωρ : ω ≫ A.principalMap = ρ :=
      (app_eq_iff_comp A.principalMap ω y.1).mp (by rw [hxω]; exact hx)
    have hsnd : ω ≫ snd G'.space.toSheaf A.sheaf =
        ρ ≫ pullback.snd A.projection A.projection := by
      rw [← A.principalMap_snd, ← Category.assoc, hωρ]
    have hfst : actPt (ω ≫ fst G'.space.toSheaf A.sheaf)
        (ρ ≫ pullback.snd A.projection A.projection) =
          ρ ≫ pullback.fst A.projection A.projection := by
      rw [actPt, ← hsnd, lift_comp_fst_snd, ← A.principalMap_fst, ← Category.assoc, hωρ]
    have hωeq : ω = lift g' (ρ ≫ pullback.snd A.projection A.projection) := by
      rw [← huniq _ hfst, ← hsnd, lift_comp_fst_snd]
    rw [← hxω, hωeq]

/-- The pushout is trivial over the cover trivialising `P`. -/
noncomputable def localSection : FppfLocalSection A.sheaf T A.projection where
  coverScheme := P.locallyTrivial.coverScheme
  cover := P.locallyTrivial.cover
  flat := P.locallyTrivial.flat
  locallyOfFinitePresentation := P.locallyTrivial.locallyOfFinitePresentation
  surjective := P.locallyTrivial.surjective
  localLift := (A.ev_bijective P.locallyTrivial.localLift 1).choose.1
  localLift_over := by
    rw [(A.ev_bijective P.locallyTrivial.localLift 1).choose.2,
      P.locallyTrivial.localLift_over]

/-- **The pushout of an fppf `G`-torsor along `r : G ⟶ G'` is an fppf `G'`-torsor.**  All the
torsor axioms are proved from the evaluation pairing. -/
noncomputable def toFppfTorsor : FppfTorsor G' T where
  P := A.sheaf
  action := A.action
  projection := A.projection
  action_over := A.action_over
  principalMap := A.principalMap
  principal_fst := A.principalMap_fst
  principal_snd := A.principalMap_snd
  principal_isIso := A.isIso_principalMap
  locallyTrivial := A.localSection

/-- The underlying sheaf of the pushout torsor. -/
@[simp]
theorem toFppfTorsor_P : A.toFppfTorsor.P = A.sheaf :=
  rfl

/-- The projection of the pushout torsor. -/
@[simp]
theorem toFppfTorsor_projection : A.toFppfTorsor.projection = A.projection :=
  rfl

end PushoutTorsor

end Pushout

/-! ### Morphisms of sheaves through their action on points -/

section PointsOfSheaves

/-- Two morphisms of fppf sheaves agreeing on all points with representable source are equal. -/
theorem hom_ext_points {S S' : FppfSheaf.{u}} {φ ψ : S ⟶ S'}
    (h : ∀ (W : Scheme.{u}) (ω : fppfYoneda.obj W ⟶ S), ω ≫ φ = ω ≫ ψ) : φ = ψ :=
  Scheme.fppfTopology.hom_ext_yoneda h

/-- A natural family of maps on points with representable source defines a morphism of fppf
sheaves. -/
noncomputable def ofPoints {S S' : FppfSheaf.{u}}
    (F : ∀ {W : Scheme.{u}}, (fppfYoneda.obj W ⟶ S) → (fppfYoneda.obj W ⟶ S'))
    (hF : ∀ {V W : Scheme.{u}} (u : V ⟶ W) (ω : fppfYoneda.obj W ⟶ S),
      fppfYoneda.map u ≫ F ω = F (fppfYoneda.map u ≫ ω)) : S ⟶ S' :=
  ObjectProperty.homMk
    { app := fun W => TypeCat.ofHom fun x =>
        Scheme.fppfTopology.yonedaEquiv (F (Scheme.fppfTopology.yonedaEquiv.symm x))
      naturality := fun W V f => by
        obtain ⟨u, rfl⟩ : ∃ u : V.unop ⟶ W.unop, f = u.op := ⟨f.unop, rfl⟩
        ext x
        change Scheme.fppfTopology.yonedaEquiv (F (Scheme.fppfTopology.yonedaEquiv.symm
            (S.obj.map u.op x))) = S'.obj.map u.op (Scheme.fppfTopology.yonedaEquiv
            (F (Scheme.fppfTopology.yonedaEquiv.symm x)))
        rw [GrothendieckTopology.yonedaEquiv_naturality, hF,
          GrothendieckTopology.yonedaEquiv_symm_naturality_left] }

/-- The morphism built from a family of maps on points computes that family. -/
@[simp]
theorem comp_ofPoints {S S' : FppfSheaf.{u}}
    (F : ∀ {W : Scheme.{u}}, (fppfYoneda.obj W ⟶ S) → (fppfYoneda.obj W ⟶ S'))
    (hF : ∀ {V W : Scheme.{u}} (u : V ⟶ W) (ω : fppfYoneda.obj W ⟶ S),
      fppfYoneda.map u ≫ F ω = F (fppfYoneda.map u ≫ ω)) {W : Scheme.{u}}
    (ω : fppfYoneda.obj W ⟶ S) : ω ≫ ofPoints F hF = F ω := by
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [GrothendieckTopology.yonedaEquiv_comp]
  change Scheme.fppfTopology.yonedaEquiv (F (Scheme.fppfTopology.yonedaEquiv.symm
    (Scheme.fppfTopology.yonedaEquiv ω))) = _
  rw [Equiv.symm_apply_apply]

end PointsOfSheaves

/-! ### A pointwise criterion for an action of a monoid object -/

section PointwiseAction

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {M X : C} [MonObj M]

/-- **An action of a monoid object may be given on points.**  A morphism `M ⊗ X ⟶ X` which
acts trivially through the unit and is compatible with the multiplication, on all generalised
points, is an action of `M` on `X`. -/
@[instance_reducible]
def modObjOfPointwise (smul : M ⊗ X ⟶ X)
    (h1 : ∀ {Z : C} (p : Z ⟶ X), lift (1 : Z ⟶ M) p ≫ smul = p)
    (h2 : ∀ {Z : C} (a b : Z ⟶ M) (p : Z ⟶ X),
      lift (a * b) p ≫ smul = lift a (lift b p ≫ smul) ≫ smul) :
    ModObj M X where
  smul := smul
  one_smul := by
    change (MonObj.one ▷ X) ≫ smul = (λ_ X).hom
    have hone : lift (1 : 𝟙_ C ⊗ X ⟶ M) (snd (𝟙_ C) X) = MonObj.one ▷ X := by
      rw [show (1 : 𝟙_ C ⊗ X ⟶ M) = toUnit (𝟙_ C ⊗ X) ≫ MonObj.one from rfl,
        ← ConeQuotient.lift_whiskerRight,
        toUnit_unique (toUnit (𝟙_ C ⊗ X)) (fst (𝟙_ C) X), lift_fst_snd, Category.id_comp]
    rw [← hone, h1 (snd (𝟙_ C) X), leftUnitor_hom]
  mul_smul := by
    change (MonObj.mul ▷ X) ≫ smul = (α_ M M X).hom ≫ (M ◁ smul) ≫ smul
    have key := h2 (Z := (M ⊗ M) ⊗ X) (fst (M ⊗ M) X ≫ fst M M)
      (fst (M ⊗ M) X ≫ snd M M) (snd (M ⊗ M) X)
    have hleft : lift ((fst (M ⊗ M) X ≫ fst M M) * (fst (M ⊗ M) X ≫ snd M M))
        (snd (M ⊗ M) X) = MonObj.mul ▷ X := by
      rw [← MonObj.comp_mul, ← MonObj.mul_eq_mul, ← ConeQuotient.lift_whiskerRight,
        lift_fst_snd, Category.id_comp]
    have hright : (α_ M M X).hom = lift (fst (M ⊗ M) X ≫ fst M M)
        (lift (fst (M ⊗ M) X ≫ snd M M) (snd (M ⊗ M) X)) := by
      rw [← ConeQuotient.lift_associator_hom, lift_comp_fst_snd, lift_fst_snd, Category.id_comp]
    rw [← hleft, key, hright, ← Category.assoc, ConeQuotient.lift_whiskerLeft]

end PointwiseAction

/-! ### The local model and the transition cocycle -/

section Construction

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}

/-- The local model of the pushout over the trivialising cover of `P`: the trivial
`G'`-torsor. -/
abbrev localModel (G' : AlgebraicSpaceGroup.{u}) {G : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}
    (P : FppfTorsor G T) : FppfSheaf.{u} :=
  G'.space.toSheaf ⊗ fppfYoneda.obj P.locallyTrivial.coverScheme

/-- The projection of the local model to the trivialising cover. -/
abbrev localProj (G' : AlgebraicSpaceGroup.{u}) {G : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}
    (P : FppfTorsor G T) : localModel G' P ⟶ fppfYoneda.obj P.locallyTrivial.coverScheme :=
  snd _ _

variable {P : FppfTorsor G T}

/-- The `G'`-coordinate of a section of the local model in the fibre at `a`. -/
noncomputable def fibVal {W : Scheme.{u}} {a : W ⟶ P.locallyTrivial.coverScheme}
    (x : Fibre (localProj G' P) a) : fppfYoneda.obj W ⟶ G'.space.toSheaf :=
  Scheme.fppfTopology.yonedaEquiv.symm x.1 ≫ fst _ _

/-- The `G'`-coordinate only depends on the underlying section. -/
theorem fibVal_congr {W : Scheme.{u}} {a a' : W ⟶ P.locallyTrivial.coverScheme}
    (x : Fibre (localProj G' P) a) (x' : Fibre (localProj G' P) a') (h : x.1 = x'.1) :
    fibVal x = fibVal x' := by
  rw [fibVal, fibVal, h]

/-- A section of the local model is the lift of its `G'`-coordinate and its base. -/
theorem symm_val_eq {W : Scheme.{u}} {a : W ⟶ P.locallyTrivial.coverScheme}
    (x : Fibre (localProj G' P) a) :
    Scheme.fppfTopology.yonedaEquiv.symm x.1 = lift (fibVal x) (fppfYoneda.map a) := by
  have h2 : (localProj G' P).hom.app (op W) x.1 = a := x.2
  have h : Scheme.fppfTopology.yonedaEquiv.symm x.1 ≫ localProj G' P = fppfYoneda.map a := by
    rw [GrothendieckTopology.yonedaEquiv_symm_naturality_right, h2, yonedaEquiv_symm_map]
  rw [fibVal, ← h, lift_comp_fst_snd]

/-- The section of the local model in the fibre at `a` with prescribed `G'`-coordinate. -/
noncomputable def fibOf {W : Scheme.{u}} (a : W ⟶ P.locallyTrivial.coverScheme)
    (g : fppfYoneda.obj W ⟶ G'.space.toSheaf) : Fibre (localProj G' P) a :=
  ⟨Scheme.fppfTopology.yonedaEquiv (lift g (fppfYoneda.map a)), by
    change (localProj G' P).hom.app (op W)
      (Scheme.fppfTopology.yonedaEquiv (lift g (fppfYoneda.map a))) = a
    rw [← GrothendieckTopology.yonedaEquiv_comp]
    change Scheme.fppfTopology.yonedaEquiv (lift g (fppfYoneda.map a) ≫ snd _ _) = a
    rw [lift_snd, GrothendieckTopology.yonedaEquiv_yoneda_map]⟩

/-- The `G'`-coordinate of `fibOf` is the given one. -/
@[simp]
theorem fibVal_fibOf {W : Scheme.{u}} (a : W ⟶ P.locallyTrivial.coverScheme)
    (g : fppfYoneda.obj W ⟶ G'.space.toSheaf) : fibVal (fibOf (G' := G') a g) = g := by
  rw [fibVal, fibOf, Equiv.symm_apply_apply, lift_fst]

/-- A section of the local model is recovered from its `G'`-coordinate. -/
@[simp]
theorem fibOf_fibVal {W : Scheme.{u}} {a : W ⟶ P.locallyTrivial.coverScheme}
    (x : Fibre (localProj G' P) a) : fibOf a (fibVal x) = x := by
  refine Subtype.ext (Scheme.fppfTopology.yonedaEquiv.symm.injective ?_)
  change Scheme.fppfTopology.yonedaEquiv.symm
    (Scheme.fppfTopology.yonedaEquiv (lift (fibVal x) (fppfYoneda.map a))) = _
  rw [Equiv.symm_apply_apply, symm_val_eq]

/-- Sections of the local model in the same fibre are determined by their `G'`-coordinate. -/
theorem fibVal_injective {W : Scheme.{u}} {a : W ⟶ P.locallyTrivial.coverScheme}
    {x x' : Fibre (localProj G' P) a} (h : fibVal x = fibVal x') : x = x' := by
  rw [← fibOf_fibVal x, ← fibOf_fibVal x', h]

/-- The `G'`-coordinate is natural under restriction. -/
theorem fibVal_restrict {V W : Scheme.{u}} {a : W ⟶ P.locallyTrivial.coverScheme} (u : V ⟶ W)
    (x : Fibre (localProj G' P) a) :
    fibVal (Fibre.restrict (localProj G' P) u x) = fppfYoneda.map u ≫ fibVal x := by
  rw [fibVal, fibVal, Fibre.restrict_val, ← GrothendieckTopology.yonedaEquiv_symm_naturality_left,
    Category.assoc]

/-- The transition cocycle of the trivialisation of `P` over its cover: the unique point of `G`
carrying the tautological point at `b` to the tautological point at `a`. -/
noncomputable def coverDiv {W : Scheme.{u}} {a b : W ⟶ P.locallyTrivial.coverScheme}
    (hab : a ≫ P.locallyTrivial.cover = b ≫ P.locallyTrivial.cover) :
    fppfYoneda.obj W ⟶ G.space.toSheaf :=
  divPt P (coverPt a) (coverPt b) (by rw [coverPt_proj, coverPt_proj, hab])

/-- The cocycle at a constant pair is the unit. -/
@[simp]
theorem coverDiv_self {W : Scheme.{u}} (a : W ⟶ P.locallyTrivial.coverScheme) :
    coverDiv (rfl : a ≫ P.locallyTrivial.cover = a ≫ P.locallyTrivial.cover) = 1 :=
  divPt_self _ _

/-- The cocycle rule. -/
theorem coverDiv_mul {W : Scheme.{u}} {a b c : W ⟶ P.locallyTrivial.coverScheme}
    (hab : a ≫ P.locallyTrivial.cover = b ≫ P.locallyTrivial.cover)
    (hbc : b ≫ P.locallyTrivial.cover = c ≫ P.locallyTrivial.cover) :
    coverDiv hab * coverDiv hbc = coverDiv (hab.trans hbc) :=
  divPt_mul _ _ _ _ _

/-- The tautological point is natural. -/
theorem comp_coverPt {V W : Scheme.{u}} (u : V ⟶ W) (a : W ⟶ P.locallyTrivial.coverScheme) :
    fppfYoneda.map u ≫ coverPt a = coverPt (u ≫ a) := by
  rw [coverPt, coverPt, ← Category.assoc, ← Functor.map_comp]

/-- The cocycle is natural. -/
theorem comp_coverDiv {V W : Scheme.{u}} (u : V ⟶ W)
    {a b : W ⟶ P.locallyTrivial.coverScheme}
    (hab : a ≫ P.locallyTrivial.cover = b ≫ P.locallyTrivial.cover)
    (hab' : (u ≫ a) ≫ P.locallyTrivial.cover = (u ≫ b) ≫ P.locallyTrivial.cover) :
    fppfYoneda.map u ≫ coverDiv hab = coverDiv hab' := by
  simp only [coverDiv]
  refine eq_divPt _ _ _ _ ?_
  rw [← comp_coverPt, ← comp_coverPt, ← comp_actPt, actPt_divPt]

variable (P) (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r]

/-- **The descent datum defining the pushout.**  Over the trivialising cover of `P` the pushout
is the trivial `G'`-torsor; the transition maps are the right translations by the image under
`r` of the transition cocycle of `P`. -/
noncomputable def descentDatum : DescentDatum P.locallyTrivial.cover (localProj G' P) where
  θ {_ _ b} hab x := fibOf b (fibVal x * (coverDiv hab ≫ r))
  θ_restrict := by
    intro V W u a b hab x
    refine fibVal_injective ?_
    rw [fibVal_restrict, fibVal_fibOf, fibVal_fibOf, MonObj.comp_mul, fibVal_restrict,
      ← Category.assoc, comp_coverDiv]
  θ_id := by
    intro W a x
    rw [coverDiv_self, MonObj.one_comp, mul_one, fibOf_fibVal]
  θ_comp := by
    intro W a b c hab hbc x
    rw [fibVal_fibOf, mul_assoc, ← MonObj.mul_comp, coverDiv_mul]

/-- **The underlying sheaf of the pushout**, glued from the descent datum along the trivialising
cover of `P`. -/
@[reducible] noncomputable def pushoutSheaf : FppfSheaf.{u} :=
  glueSheaf (descentDatum P r)

/-- The structure morphism of the pushout to the base. -/
@[reducible] noncomputable def pushoutProj : pushoutSheaf P r ⟶ fppfYoneda.obj T :=
  glueSheafBase (descentDatum P r)

end Construction

/-! ### The coordinates of a section of the glued sheaf -/

section Coordinates

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {P : FppfTorsor G T}
  {r : G.space.toSheaf ⟶ G'.space.toSheaf} [IsMonHom r]

/-- The `G'`-coordinate of a section of the local model at a test square of the cover. -/
noncomputable def coordOf {W : Scheme.{u}} {s : W ⟶ T}
    (ξ : Fibre (localProj G' P) (pullback.snd s P.locallyTrivial.cover)) {Z : Scheme.{u}}
    (c : Z ⟶ W) (d : Z ⟶ P.locallyTrivial.coverScheme)
    (h : c ≫ s = d ≫ P.locallyTrivial.cover) : fppfYoneda.obj Z ⟶ G'.space.toSheaf :=
  fibVal (evOf ξ c d h)

/-- The coordinate at a test square is the restriction of the coordinate of the section. -/
theorem coordOf_eq {W : Scheme.{u}} {s : W ⟶ T}
    (ξ : Fibre (localProj G' P) (pullback.snd s P.locallyTrivial.cover)) {Z : Scheme.{u}}
    (c : Z ⟶ W) (d : Z ⟶ P.locallyTrivial.coverScheme)
    (h : c ≫ s = d ≫ P.locallyTrivial.cover) :
    coordOf ξ c d h = fppfYoneda.map (pullback.lift c d h) ≫ fibVal ξ := by
  rw [coordOf, fibVal_congr (evOf ξ c d h)
    (Fibre.restrict (localProj G' P) (pullback.lift c d h) ξ) rfl, fibVal_restrict]

/-- The coordinate only depends on the test square. -/
theorem coordOf_congr {W : Scheme.{u}} {s : W ⟶ T}
    (ξ : Fibre (localProj G' P) (pullback.snd s P.locallyTrivial.cover)) {Z : Scheme.{u}}
    {c c' : Z ⟶ W} {d d' : Z ⟶ P.locallyTrivial.coverScheme} (hc : c = c') (hd : d = d')
    (h : c ≫ s = d ≫ P.locallyTrivial.cover) (h' : c' ≫ s = d' ≫ P.locallyTrivial.cover) :
    coordOf ξ c d h = coordOf ξ c' d' h' := by
  subst hc
  subst hd
  rfl

/-- The transition maps of the descent datum multiply the coordinate by the image of the
cocycle. -/
theorem fibVal_theta {W : Scheme.{u}} {a b : W ⟶ P.locallyTrivial.coverScheme}
    (hab : a ≫ P.locallyTrivial.cover = b ≫ P.locallyTrivial.cover)
    (x : Fibre (localProj G' P) a) :
    fibVal ((descentDatum P r).θ hab x) = fibVal x * (coverDiv hab ≫ r) :=
  fibVal_fibOf _ _

/-- **The descent condition, read on coordinates.** -/
theorem coordOf_descent {W : Scheme.{u}} {s : W ⟶ T}
    {ξ : Fibre (localProj G' P) (pullback.snd s P.locallyTrivial.cover)}
    (hξ : IsDescentSection (descentDatum P r) ξ) {Z : Scheme.{u}} (c : Z ⟶ W)
    (d₁ d₂ : Z ⟶ P.locallyTrivial.coverScheme) (h₁ : c ≫ s = d₁ ≫ P.locallyTrivial.cover)
    (h₂ : c ≫ s = d₂ ≫ P.locallyTrivial.cover) :
    coordOf ξ c d₂ h₂ = coordOf ξ c d₁ h₁ * (coverDiv (h₁.symm.trans h₂) ≫ r) := by
  rw [coordOf, ← hξ c d₁ d₂ h₁ h₂, fibVal_theta, coordOf]

/-- **A section of the local model satisfying the coordinate cocycle rule is a descent
section.** -/
theorem isDescentSection_of_coordOf {W : Scheme.{u}} {s : W ⟶ T}
    (ξ : Fibre (localProj G' P) (pullback.snd s P.locallyTrivial.cover))
    (h : ∀ {Z : Scheme.{u}} (c : Z ⟶ W) (d₁ d₂ : Z ⟶ P.locallyTrivial.coverScheme)
      (h₁ : c ≫ s = d₁ ≫ P.locallyTrivial.cover) (h₂ : c ≫ s = d₂ ≫ P.locallyTrivial.cover),
      coordOf ξ c d₂ h₂ = coordOf ξ c d₁ h₁ * (coverDiv (h₁.symm.trans h₂) ≫ r)) :
    IsDescentSection (descentDatum P r) ξ := by
  intro Z c d₁ d₂ h₁ h₂
  refine fibVal_injective ?_
  rw [fibVal_theta]
  exact (h c d₁ d₂ h₁ h₂).symm

/-- Two sections of the glued sheaf with the same base and the same coordinates are equal. -/
theorem glueObj_ext_coordOf {W : Scheme.{u}} {z z' : GlueObj (descentDatum P r) W}
    (h1 : z.1 = z'.1)
    (h2 : ∀ {Z : Scheme.{u}} (c : Z ⟶ W) (d : Z ⟶ P.locallyTrivial.coverScheme)
      (h : c ≫ z.1 = d ≫ P.locallyTrivial.cover)
      (h' : c ≫ z'.1 = d ≫ P.locallyTrivial.cover),
      coordOf z.2.1 c d h = coordOf z'.2.1 c d h') : z = z' :=
  glueObj_ext h1 fun c d h h' => congrArg Subtype.val (fibVal_injective (h2 c d h h'))

/-- The coordinates of a restricted section. -/
theorem coordOf_glueMap {V W : Scheme.{u}} (u : V ⟶ W) (z : GlueObj (descentDatum P r) W)
    {Z : Scheme.{u}} (c : Z ⟶ V) (d : Z ⟶ P.locallyTrivial.coverScheme)
    (h : c ≫ (glueMap u z).1 = d ≫ P.locallyTrivial.cover)
    (h' : (c ≫ u) ≫ z.1 = d ≫ P.locallyTrivial.cover) :
    coordOf (glueMap u z).2.1 c d h = coordOf z.2.1 (c ≫ u) d h' :=
  fibVal_congr _ _ (ev_glueMap u z c d h h')

end Coordinates

/-! ### The action of `G'` on the glued sheaf -/

section Action

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} (P : FppfTorsor G T)
  (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r]

/-- The section of the local model obtained by translating the coordinate of a section of the
glued sheaf by a point of `G'`. -/
noncomputable def smulFibre {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : GlueObj (descentDatum P r) W) :
    Fibre (localProj G' P) (pullback.snd z.1 P.locallyTrivial.cover) :=
  fibOf (pullback.snd z.1 P.locallyTrivial.cover)
    ((fppfYoneda.map (pullback.fst z.1 P.locallyTrivial.cover) ≫ g') * fibVal z.2.1)

variable {P r}

/-- The coordinates of the translated section. -/
theorem coordOf_smulFibre {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : GlueObj (descentDatum P r) W) {Z : Scheme.{u}} (c : Z ⟶ W)
    (d : Z ⟶ P.locallyTrivial.coverScheme) (h : c ≫ z.1 = d ≫ P.locallyTrivial.cover) :
    coordOf (smulFibre P r g' z) c d h = (fppfYoneda.map c ≫ g') * coordOf z.2.1 c d h := by
  rw [coordOf_eq, smulFibre, fibVal_fibOf, MonObj.comp_mul, coordOf_eq, ← Category.assoc,
    ← Functor.map_comp, pullback.lift_fst]

/-- The translated section is again a descent section. -/
theorem isDescentSection_smulFibre {W : Scheme.{u}}
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (z : GlueObj (descentDatum P r) W) :
    IsDescentSection (descentDatum P r) (smulFibre P r g' z) := by
  refine isDescentSection_of_coordOf _ fun c d₁ d₂ h₁ h₂ => ?_
  rw [coordOf_smulFibre, coordOf_smulFibre, coordOf_descent z.2.2 c d₁ d₂ h₁ h₂, mul_assoc]

variable (P r)

/-- The translation of a section of the glued sheaf by a point of `G'`. -/
noncomputable def smulGlue {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : GlueObj (descentDatum P r) W) : GlueObj (descentDatum P r) W :=
  ⟨z.1, ⟨smulFibre P r g' z, isDescentSection_smulFibre g' z⟩⟩

variable {P r}

/-- Translation does not change the base of a section. -/
@[simp]
theorem smulGlue_fst {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : GlueObj (descentDatum P r) W) : (smulGlue P r g' z).1 = z.1 :=
  rfl

/-- The coordinates of a translated section of the glued sheaf. -/
theorem coordOf_smulGlue {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : GlueObj (descentDatum P r) W) {Z : Scheme.{u}} (c : Z ⟶ W)
    (d : Z ⟶ P.locallyTrivial.coverScheme) (h : c ≫ z.1 = d ≫ P.locallyTrivial.cover) :
    coordOf (smulGlue P r g' z).2.1 c d h = (fppfYoneda.map c ≫ g') * coordOf z.2.1 c d h :=
  coordOf_smulFibre g' z c d h

/-- Translation by the unit is the identity. -/
theorem smulGlue_one {W : Scheme.{u}} (z : GlueObj (descentDatum P r) W) :
    smulGlue P r (1 : fppfYoneda.obj W ⟶ G'.space.toSheaf) z = z := by
  refine glueObj_ext_coordOf rfl fun c d h h' => ?_
  rw [coordOf_smulGlue (1 : fppfYoneda.obj W ⟶ G'.space.toSheaf) z c d h', MonObj.comp_one,
    one_mul]

/-- Translation is compatible with multiplication. -/
theorem smulGlue_mul {W : Scheme.{u}} (a b : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : GlueObj (descentDatum P r) W) :
    smulGlue P r (a * b) z = smulGlue P r a (smulGlue P r b z) := by
  refine glueObj_ext_coordOf rfl fun c d h h' => ?_
  rw [coordOf_smulGlue (a * b) z c d h, coordOf_smulGlue a (smulGlue P r b z) c d h,
    coordOf_smulGlue b z c d h, MonObj.comp_mul, mul_assoc]

/-- Translation is compatible with restriction. -/
theorem glueMap_smulGlue {V W : Scheme.{u}} (u : V ⟶ W)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (z : GlueObj (descentDatum P r) W) :
    glueMap u (smulGlue P r g' z) =
      smulGlue P r (fppfYoneda.map u ≫ g') (glueMap u z) := by
  refine glueObj_ext_coordOf rfl fun c d h h' => ?_
  have hz : (c ≫ u) ≫ z.1 = d ≫ P.locallyTrivial.cover := h
  rw [coordOf_glueMap u (smulGlue P r g' z) c d h hz, coordOf_smulGlue g' z (c ≫ u) d hz,
    coordOf_smulGlue (fppfYoneda.map u ≫ g') (glueMap u z) c d h',
    coordOf_glueMap u z c d h' hz, ← Category.assoc, ← Functor.map_comp]

end Action

/-! ### The pushout sheaf as a `G'`-sheaf -/

section SheafAction

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} (P : FppfTorsor G T)
  (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r]

/-- The section of the glued sheaf underlying a point of the pushout sheaf. -/
noncomputable def glueSec {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) :
    GlueObj (descentDatum P r) W :=
  Scheme.fppfTopology.yonedaEquiv z

/-- The point of the pushout sheaf attached to a section of the glued sheaf. -/
noncomputable def ptOfGlue {W : Scheme.{u}} (z : GlueObj (descentDatum P r) W) :
    fppfYoneda.obj W ⟶ pushoutSheaf P r :=
  Scheme.fppfTopology.yonedaEquiv.symm z

variable {P r}

/-- The two descriptions of a point of the pushout sheaf are inverse to each other. -/
@[simp]
theorem glueSec_ptOfGlue {W : Scheme.{u}} (z : GlueObj (descentDatum P r) W) :
    glueSec P r (ptOfGlue P r z) = z :=
  Equiv.apply_symm_apply _ _

/-- The two descriptions of a point of the pushout sheaf are inverse to each other. -/
@[simp]
theorem ptOfGlue_glueSec {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) :
    ptOfGlue P r (glueSec P r z) = z :=
  Equiv.symm_apply_apply _ _

/-- Points of the pushout sheaf are determined by their sections. -/
theorem glueSec_injective {W : Scheme.{u}} {z z' : fppfYoneda.obj W ⟶ pushoutSheaf P r}
    (h : glueSec P r z = glueSec P r z') : z = z' := by
  rw [← ptOfGlue_glueSec z, ← ptOfGlue_glueSec z', h]

/-- Restriction of a point of the pushout sheaf is restriction of its section. -/
theorem glueSec_comp {V W : Scheme.{u}} (u : V ⟶ W)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) :
    glueSec P r (fppfYoneda.map u ≫ z) = glueMap u (glueSec P r z) :=
  (Scheme.fppfTopology.yonedaEquiv_naturality z u).symm

/-- Restriction of a point attached to a section. -/
theorem comp_ptOfGlue {V W : Scheme.{u}} (u : V ⟶ W) (z : GlueObj (descentDatum P r) W) :
    fppfYoneda.map u ≫ ptOfGlue P r z = ptOfGlue P r (glueMap u z) := by
  refine glueSec_injective ?_
  rw [glueSec_comp, glueSec_ptOfGlue, glueSec_ptOfGlue]

/-- The base of the section of a point of the pushout sheaf. -/
theorem glueSec_fst {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) :
    (glueSec P r z).1 = Scheme.fppfTopology.yonedaEquiv (z ≫ pushoutProj P r) :=
  rfl

variable (P r)

/-- The translation of a point of the pushout sheaf by a point of `G'`. -/
noncomputable def actGluePt {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) : fppfYoneda.obj W ⟶ pushoutSheaf P r :=
  ptOfGlue P r (smulGlue P r g' (glueSec P r z))

variable {P r}

/-- The section underlying a translated point. -/
@[simp]
theorem glueSec_actGluePt {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) :
    glueSec P r (actGluePt P r g' z) = smulGlue P r g' (glueSec P r z) := by
  rw [actGluePt, glueSec_ptOfGlue]

/-- Translation of points is natural. -/
theorem comp_actGluePt {V W : Scheme.{u}} (u : V ⟶ W)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) :
    fppfYoneda.map u ≫ actGluePt P r g' z =
      actGluePt P r (fppfYoneda.map u ≫ g') (fppfYoneda.map u ≫ z) := by
  refine glueSec_injective ?_
  rw [glueSec_comp, glueSec_actGluePt, glueSec_actGluePt, glueMap_smulGlue, glueSec_comp]

/-- Translation by the unit does nothing. -/
theorem actGluePt_one {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) :
    actGluePt P r (1 : fppfYoneda.obj W ⟶ G'.space.toSheaf) z = z := by
  refine glueSec_injective ?_
  rw [glueSec_actGluePt, smulGlue_one]

/-- Translation is compatible with multiplication. -/
theorem actGluePt_mul {W : Scheme.{u}} (a b : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) :
    actGluePt P r (a * b) z = actGluePt P r a (actGluePt P r b z) := by
  refine glueSec_injective ?_
  rw [glueSec_actGluePt, glueSec_actGluePt, glueSec_actGluePt, smulGlue_mul]

/-- Translation does not change the image in the base. -/
theorem actGluePt_proj {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) :
    actGluePt P r g' z ≫ pushoutProj P r = z ≫ pushoutProj P r := by
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [← glueSec_fst, ← glueSec_fst, glueSec_actGluePt, smulGlue_fst]

variable (P r)

/-- The naturality of the translation formula. -/
theorem actGluePt_natural : ∀ {V W : Scheme.{u}} (u : V ⟶ W)
    (ω : fppfYoneda.obj W ⟶ G'.space.toSheaf ⊗ pushoutSheaf P r),
    fppfYoneda.map u ≫ actGluePt P r (ω ≫ fst _ _) (ω ≫ snd _ _) =
      actGluePt P r ((fppfYoneda.map u ≫ ω) ≫ fst _ _)
        ((fppfYoneda.map u ≫ ω) ≫ snd _ _) :=
  fun u ω => by rw [comp_actGluePt, Category.assoc, Category.assoc]

/-- The action of `G'` on the pushout sheaf. -/
noncomputable def pushoutSmul : G'.space.toSheaf ⊗ pushoutSheaf P r ⟶ pushoutSheaf P r :=
  ofPoints (fun ω => actGluePt P r (ω ≫ fst _ _) (ω ≫ snd _ _)) (actGluePt_natural P r)

variable {P r}

/-- The action of `G'` on the pushout sheaf, computed on points. -/
@[simp]
theorem lift_comp_pushoutSmul {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) :
    lift g' z ≫ pushoutSmul P r = actGluePt P r g' z := by
  rw [pushoutSmul]
  refine (comp_ofPoints _ (actGluePt_natural P r) (lift g' z)).trans ?_
  rw [lift_fst, lift_snd]

/-- **An action of a monoid object on an fppf sheaf may be given on points with representable
source.** -/
@[instance_reducible]
def modObjOfPoints {M X : FppfSheaf.{u}} [MonObj M] (smul : M ⊗ X ⟶ X)
    (h1 : ∀ {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ X),
      lift (1 : fppfYoneda.obj W ⟶ M) p ≫ smul = p)
    (h2 : ∀ {W : Scheme.{u}} (a b : fppfYoneda.obj W ⟶ M) (p : fppfYoneda.obj W ⟶ X),
      lift (a * b) p ≫ smul = lift a (lift b p ≫ smul) ≫ smul) :
    ModObj M X :=
  modObjOfPointwise smul
    (fun {_} p => hom_ext_points fun _ ω => by
      simp only [← Category.assoc, comp_lift, MonObj.comp_one]
      exact h1 _)
    (fun {_} a b p => hom_ext_points fun _ ω => by
      simp only [← Category.assoc, comp_lift, MonObj.comp_mul]
      exact h2 _ _ _)

variable (P r)

/-- **The pushout sheaf is a `G'`-sheaf.** -/
@[instance_reducible]
noncomputable def pushoutAction : ModObj G'.space.toSheaf (pushoutSheaf P r) :=
  modObjOfPoints (pushoutSmul P r)
    (fun z => by rw [lift_comp_pushoutSmul, actGluePt_one])
    (fun a b z => by rw [lift_comp_pushoutSmul, lift_comp_pushoutSmul, lift_comp_pushoutSmul,
      actGluePt_mul])

attribute [instance] pushoutAction

/-- The action of the `G'`-sheaf structure of the pushout is the glued translation. -/
@[simp]
theorem pushoutAction_smul :
    ModObj.smul (M := G'.space.toSheaf) (X := pushoutSheaf P r) = pushoutSmul P r :=
  rfl

/-- **The action of `G'` on the pushout sheaf is fibrewise over the base.** -/
theorem pushoutSmul_proj :
    pushoutSmul P r ≫ pushoutProj P r =
      snd G'.space.toSheaf (pushoutSheaf P r) ≫ pushoutProj P r := by
  refine hom_ext_points fun W ω => ?_
  rw [← Category.assoc, ← Category.assoc, ← lift_comp_fst_snd ω, lift_comp_pushoutSmul, lift_snd,
    actGluePt_proj]

end SheafAction

/-! ### Local trivialisation of the pushout sheaf -/

section CoordinatesAux

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {P : FppfTorsor G T}
  {r : G.space.toSheaf ⟶ G'.space.toSheaf} [IsMonHom r]

/-- The coordinate of a test square is natural in the test scheme. -/
theorem coordOf_comp {W : Scheme.{u}} {s : W ⟶ T}
    (ξ : Fibre (localProj G' P) (pullback.snd s P.locallyTrivial.cover)) {Z Z' : Scheme.{u}}
    (w : Z' ⟶ Z) (c : Z ⟶ W) (d : Z ⟶ P.locallyTrivial.coverScheme)
    (h : c ≫ s = d ≫ P.locallyTrivial.cover)
    (h' : (w ≫ c) ≫ s = (w ≫ d) ≫ P.locallyTrivial.cover) :
    fppfYoneda.map w ≫ coordOf ξ c d h = coordOf ξ (w ≫ c) (w ≫ d) h' := by
  have hlift : pullback.lift (w ≫ c) (w ≫ d) h' = w ≫ pullback.lift c d h := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
  rw [coordOf_eq, coordOf_eq, hlift, Functor.map_comp, Category.assoc]

/-- The coordinates of equal sections of the glued sheaf agree. -/
theorem coordOf_glueObj_congr {W : Scheme.{u}} {z z' : GlueObj (descentDatum P r) W}
    (hzz : z = z') {Z : Scheme.{u}} (c : Z ⟶ W) (d : Z ⟶ P.locallyTrivial.coverScheme)
    (h : c ≫ z.1 = d ≫ P.locallyTrivial.cover) (h' : c ≫ z'.1 = d ≫ P.locallyTrivial.cover) :
    coordOf z.2.1 c d h = coordOf z'.2.1 c d h' := by
  subst hzz
  rfl

end CoordinatesAux

section LocalTrivialisation

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} (P : FppfTorsor G T)
  (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r]

/-- The coordinate of a point of the pushout sheaf at a lift of its base to the cover. -/
noncomputable def coordAt {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    fppfYoneda.obj W ⟶ G'.space.toSheaf :=
  coordOf (glueSec P r z).2.1 (𝟙 W) c (by
    rw [Category.id_comp, glueSec_fst, hz, GrothendieckTopology.yonedaEquiv_yoneda_map])

variable {P r}

/-- The base of the section of a point of the pushout sheaf with a chosen lift. -/
theorem glueSec_fst_of_lift {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    (glueSec P r z).1 = c ≫ P.locallyTrivial.cover := by
  rw [glueSec_fst, hz, GrothendieckTopology.yonedaEquiv_yoneda_map]

/-- The coordinate is the `G'`-coordinate of the fibre of the glued sheaf. -/
theorem coordAt_eq_fibVal {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    coordAt P r z c hz =
      fibVal (glueFibreEquiv (descentDatum P r) c ⟨glueSec P r z, glueSec_fst_of_lift z c hz⟩) :=
  rfl

/-- The coordinate is natural in the test scheme. -/
theorem comp_coordAt {V W : Scheme.{u}} (u : V ⟶ W) (z : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : (fppfYoneda.map u ≫ z) ≫ pushoutProj P r =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover)) :
    fppfYoneda.map u ≫ coordAt P r z c hz = coordAt P r (fppfYoneda.map u ≫ z) (u ≫ c) hz' := by
  have hb : (glueSec P r z).1 = c ≫ P.locallyTrivial.cover := glueSec_fst_of_lift z c hz
  have hu : u ≫ (glueSec P r z).1 = (u ≫ c) ≫ P.locallyTrivial.cover := by
    rw [hb, Category.assoc]
  have h1 : (u ≫ 𝟙 W) ≫ (glueSec P r z).1 = (u ≫ c) ≫ P.locallyTrivial.cover := by
    rw [Category.comp_id]; exact hu
  have h2 : (𝟙 V ≫ u) ≫ (glueSec P r z).1 = (u ≫ c) ≫ P.locallyTrivial.cover := by
    rw [Category.id_comp]; exact hu
  have h0 : 𝟙 V ≫ (glueMap u (glueSec P r z)).1 = (u ≫ c) ≫ P.locallyTrivial.cover := by
    rw [Category.id_comp, glueMap_fst]; exact hu
  rw [coordAt, coordAt]
  calc fppfYoneda.map u ≫ coordOf (glueSec P r z).2.1 (𝟙 W) c _
      = coordOf (glueSec P r z).2.1 (u ≫ 𝟙 W) (u ≫ c) h1 := coordOf_comp _ u (𝟙 W) c _ h1
    _ = coordOf (glueSec P r z).2.1 (𝟙 V ≫ u) (u ≫ c) h2 :=
        coordOf_congr _ (by rw [Category.comp_id, Category.id_comp]) rfl h1 h2
    _ = coordOf (glueMap u (glueSec P r z)).2.1 (𝟙 V) (u ≫ c) h0 :=
        (coordOf_glueMap u (glueSec P r z) (𝟙 V) (u ≫ c) h0 h2).symm
    _ = coordOf (glueSec P r (fppfYoneda.map u ≫ z)).2.1 (𝟙 V) (u ≫ c) _ :=
        coordOf_glueObj_congr (glueSec_comp u z).symm (𝟙 V) (u ≫ c) h0 _

/-- **Independence of the chosen lift**: two lifts of the base give coordinates differing by the
image under `r` of the transition cocycle. -/
theorem coordAt_lift_congr {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    {c c' : W ⟶ P.locallyTrivial.coverScheme}
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : z ≫ pushoutProj P r = fppfYoneda.map (c' ≫ P.locallyTrivial.cover))
    (hcc : c ≫ P.locallyTrivial.cover = c' ≫ P.locallyTrivial.cover) :
    coordAt P r z c' hz' = coordAt P r z c hz * (coverDiv hcc ≫ r) := by
  rw [coordAt, coordAt, coordOf_descent (glueSec P r z).2.2 (𝟙 W) c c']

variable (P r)

/-- The point of the pushout sheaf with prescribed base lift and coordinate. -/
noncomputable def ptOfCoord {W : Scheme.{u}} (c : W ⟶ P.locallyTrivial.coverScheme)
    (g : fppfYoneda.obj W ⟶ G'.space.toSheaf) : fppfYoneda.obj W ⟶ pushoutSheaf P r :=
  ptOfGlue P r ((glueFibreEquiv (descentDatum P r) c).symm (fibOf c g)).1

variable {P r}

/-- The section of a point with prescribed coordinate. -/
theorem glueSec_ptOfCoord {W : Scheme.{u}} (c : W ⟶ P.locallyTrivial.coverScheme)
    (g : fppfYoneda.obj W ⟶ G'.space.toSheaf) :
    glueSec P r (ptOfCoord P r c g) =
      ((glueFibreEquiv (descentDatum P r) c).symm (fibOf c g)).1 := by
  rw [ptOfCoord, glueSec_ptOfGlue]

/-- The point with prescribed coordinate lies above the expected base point. -/
theorem ptOfCoord_proj {W : Scheme.{u}} (c : W ⟶ P.locallyTrivial.coverScheme)
    (g : fppfYoneda.obj W ⟶ G'.space.toSheaf) :
    ptOfCoord P r c g ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [← glueSec_fst, glueSec_ptOfCoord, GrothendieckTopology.yonedaEquiv_yoneda_map]
  exact ((glueFibreEquiv (descentDatum P r) c).symm (fibOf c g)).2

/-- **The coordinate of the point with prescribed coordinate.** -/
@[simp]
theorem coordAt_ptOfCoord {W : Scheme.{u}} (c : W ⟶ P.locallyTrivial.coverScheme)
    (g : fppfYoneda.obj W ⟶ G'.space.toSheaf) :
    coordAt P r (ptOfCoord P r c g) c (ptOfCoord_proj c g) = g := by
  rw [coordAt_eq_fibVal]
  have hsub : (⟨glueSec P r (ptOfCoord P r c g),
      glueSec_fst_of_lift (ptOfCoord P r c g) c (ptOfCoord_proj c g)⟩ :
        {w : GlueObj (descentDatum P r) W // w.1 = c ≫ P.locallyTrivial.cover}) =
      (glueFibreEquiv (descentDatum P r) c).symm (fibOf c g) :=
    Subtype.ext (glueSec_ptOfCoord c g)
  rw [hsub, Equiv.apply_symm_apply, fibVal_fibOf]

/-- **A point of the pushout sheaf is determined by its coordinate at a lift.** -/
@[simp]
theorem ptOfCoord_coordAt {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    ptOfCoord P r c (coordAt P r z c hz) = z := by
  rw [ptOfCoord, coordAt_eq_fibVal, fibOf_fibVal, Equiv.symm_apply_apply, ptOfGlue_glueSec]

/-- Two points of the pushout sheaf above the same lift with the same coordinate are equal. -/
theorem coordAt_injective {W : Scheme.{u}} {z z' : fppfYoneda.obj W ⟶ pushoutSheaf P r}
    {c : W ⟶ P.locallyTrivial.coverScheme}
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : z' ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h : coordAt P r z c hz = coordAt P r z' c hz') : z = z' := by
  rw [← ptOfCoord_coordAt z c hz, ← ptOfCoord_coordAt z' c hz', h]

/-- Translating a point multiplies its coordinate. -/
theorem coordAt_actGluePt {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : actGluePt P r g' z ≫ pushoutProj P r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    coordAt P r (actGluePt P r g' z) c hz' = g' * coordAt P r z c hz := by
  have h0 : 𝟙 W ≫ (smulGlue P r g' (glueSec P r z)).1 = c ≫ P.locallyTrivial.cover := by
    rw [smulGlue_fst, Category.id_comp]
    exact glueSec_fst_of_lift z c hz
  have hpf : 𝟙 W ≫ (glueSec P r z).1 = c ≫ P.locallyTrivial.cover := by
    rw [Category.id_comp]
    exact glueSec_fst_of_lift z c hz
  rw [coordAt, coordAt]
  refine (coordOf_glueObj_congr (glueSec_actGluePt g' z) (𝟙 W) c _ h0).trans ?_
  refine (coordOf_smulGlue g' (glueSec P r z) (𝟙 W) c hpf).trans ?_
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

end LocalTrivialisation

/-! ### The local evaluation pairing -/

section EvLocal

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} (P : FppfTorsor G T)
  (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r]

/-- The value at a point `p` of `P` of the equivariant map given by a point `z` of the pushout
sheaf, computed through a lift `c` of the base to the trivialising cover.  The formula is
`z (p) = z (L c) * r (p / L c)⁻¹`, where `L c` is the tautological point of `P` at `c`. -/
noncomputable def evLocal {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (p : fppfYoneda.obj W ⟶ P.P) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    fppfYoneda.obj W ⟶ G'.space.toSheaf :=
  coordAt P r z c hz * ((divPt P p (coverPt c) (by rw [hp, coverPt_proj])) ≫ r)⁻¹

variable {P r}

/-- Two lifts of the same base point are comparable. -/
theorem cover_lift_eq {W : Scheme.{u}} {c c' : W ⟶ P.locallyTrivial.coverScheme}
    (h : (fppfYoneda.map (c ≫ P.locallyTrivial.cover) :
      fppfYoneda.obj W ⟶ fppfYoneda.obj T) = fppfYoneda.map (c' ≫ P.locallyTrivial.cover)) :
    c ≫ P.locallyTrivial.cover = c' ≫ P.locallyTrivial.cover := by
  have h2 := congrArg Scheme.fppfTopology.yonedaEquiv h
  rwa [GrothendieckTopology.yonedaEquiv_yoneda_map,
    GrothendieckTopology.yonedaEquiv_yoneda_map] at h2

/-- **The local evaluation does not depend on the chosen lift.** -/
theorem evLocal_lift_congr {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (p : fppfYoneda.obj W ⟶ P.P) {c c' : W ⟶ P.locallyTrivial.coverScheme}
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : z ≫ pushoutProj P r = fppfYoneda.map (c' ≫ P.locallyTrivial.cover))
    (hp' : p ≫ P.projection = fppfYoneda.map (c' ≫ P.locallyTrivial.cover)) :
    evLocal P r z p c' hz' hp' = evLocal P r z p c hz hp := by
  have hcc : c ≫ P.locallyTrivial.cover = c' ≫ P.locallyTrivial.cover :=
    cover_lift_eq (hz.symm.trans hz')
  have hd : divPt P p (coverPt c') (by rw [hp', coverPt_proj]) =
      divPt P p (coverPt c) (by rw [hp, coverPt_proj]) * coverDiv hcc :=
    (divPt_mul _ _ _ _ _).symm
  rw [evLocal, evLocal, coordAt_lift_congr z hz hz' hcc, hd, MonObj.mul_comp]
  group

/-- The local evaluation is natural in the test scheme. -/
theorem comp_evLocal {V W : Scheme.{u}} (u : V ⟶ W) (z : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (p : fppfYoneda.obj W ⟶ P.P) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : (fppfYoneda.map u ≫ z) ≫ pushoutProj P r =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover))
    (hp' : (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover)) :
    fppfYoneda.map u ≫ evLocal P r z p c hz hp =
      evLocal P r (fppfYoneda.map u ≫ z) (fppfYoneda.map u ≫ p) (u ≫ c) hz' hp' := by
  have hd : fppfYoneda.map u ≫ divPt P p (coverPt c) (by rw [hp, coverPt_proj]) =
      divPt P (fppfYoneda.map u ≫ p) (coverPt (u ≫ c)) (by rw [hp', coverPt_proj]) := by
    refine eq_divPt _ _ _ _ ?_
    rw [← comp_coverPt, ← comp_actPt, actPt_divPt]
  rw [evLocal, evLocal, MonObj.comp_mul, comp_coordAt u z c hz hz', GrpObj.comp_inv,
    ← Category.assoc, hd]

/-- The local evaluation is equivariant for the action of `G'` on the pushout sheaf. -/
theorem evLocal_actGluePt {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) (p : fppfYoneda.obj W ⟶ P.P)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : actGluePt P r g' z ≫ pushoutProj P r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evLocal P r (actGluePt P r g' z) p c hz' hp = g' * evLocal P r z p c hz hp := by
  rw [evLocal, evLocal, coordAt_actGluePt g' z c hz hz', mul_assoc]

/-- The local evaluation is equivariant for the action of `G` on `P`, through `r`. -/
theorem evLocal_actPt {W : Scheme.{u}} (g : fppfYoneda.obj W ⟶ G.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P r) (p : fppfYoneda.obj W ⟶ P.P)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp' : actPt g p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evLocal P r z (actPt g p) c hz hp' = evLocal P r z p c hz hp * (g ≫ r)⁻¹ := by
  have hd : divPt P (actPt g p) (coverPt c) (by rw [hp', coverPt_proj]) =
      g * divPt P p (coverPt c) (by rw [hp, coverPt_proj]) :=
    divPt_actPt_left _ _ _ _ _
  rw [evLocal, evLocal, hd, MonObj.mul_comp]
  group

/-- **The local evaluation is surjective on the fibre**: the point of the pushout sheaf with the
prescribed value at `p`. -/
theorem evLocal_ptOfCoord {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (c : W ⟶ P.locallyTrivial.coverScheme) (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evLocal P r (ptOfCoord P r c
        (g' * (divPt P p (coverPt c) (by rw [hp, coverPt_proj]) ≫ r))) p c
      (ptOfCoord_proj c _) hp = g' := by
  rw [evLocal, coordAt_ptOfCoord, mul_inv_cancel_right]

/-- **The local evaluation is injective on the fibre.** -/
theorem evLocal_injective {W : Scheme.{u}} {z z' : fppfYoneda.obj W ⟶ pushoutSheaf P r}
    (p : fppfYoneda.obj W ⟶ P.P) {c : W ⟶ P.locallyTrivial.coverScheme}
    (hz : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : z' ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h : evLocal P r z p c hz hp = evLocal P r z' p c hz' hp) : z = z' := by
  refine coordAt_injective hz hz' ?_
  rw [evLocal, evLocal] at h
  exact mul_right_cancel h

end EvLocal

/-! ### The global evaluation pairing -/

section Ev

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} (P : FppfTorsor G T)
  (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r]

/-- Two morphisms from a representable sheaf agreeing on a covering sieve are equal. -/
theorem hom_ext_of_sieve_pt {W : Scheme.{u}} {R : Sieve W}
    (hR : R ∈ Scheme.fppfTopology W) {B : FppfSheaf.{u}}
    {φ ψ : fppfYoneda.obj W ⟶ B}
    (h : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ W), R u →
      fppfYoneda.map u ≫ φ = fppfYoneda.map u ≫ ψ) : φ = ψ := by
  refine Scheme.fppfTopology.yonedaEquiv.injective
    ((isSheafOfType B R hR).isSeparatedFor.ext fun V u hu => ?_)
  rw [GrothendieckTopology.yonedaEquiv_naturality, GrothendieckTopology.yonedaEquiv_naturality,
    h u hu]

/-- A morphism to a representable sheaf is the image of its Yoneda element. -/
theorem fppfYoneda_map_yonedaEquiv {V W : Scheme.{u}}
    (ψ : fppfYoneda.obj V ⟶ fppfYoneda.obj W) :
    fppfYoneda.map (Scheme.fppfTopology.yonedaEquiv ψ) = ψ := by
  rw [← yonedaEquiv_symm_map, Equiv.symm_apply_apply]

variable {P r}

/-- The local evaluation only depends on the two points. -/
theorem evLocal_congr {W : Scheme.{u}} {z z' : fppfYoneda.obj W ⟶ pushoutSheaf P r}
    {p p' : fppfYoneda.obj W ⟶ P.P} (hz : z = z') (hp : p = p')
    {c : W ⟶ P.locallyTrivial.coverScheme}
    (h1 : z ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h2 : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h3 : z' ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h4 : p' ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evLocal P r z p c h1 h2 = evLocal P r z' p' c h3 h4 := by
  subst hz
  subst hp
  rfl

variable (P r)

/-- The fibre product of the pushout sheaf and of `P` over the base.

It is deliberately *not* reducible: unfolding it to the pullback of sheaves makes the elaborator
evaluate the limit construction on sections, which does not terminate in practice.  All the
statements below go through the wrappers `evFst`, `evSnd`, `evLift`. -/
noncomputable def evSource : FppfSheaf.{u} :=
  pullback (pushoutProj P r) P.projection

/-- The projection of the fibre product to the pushout sheaf. -/
noncomputable def evFst : evSource P r ⟶ pushoutSheaf P r :=
  pullback.fst (pushoutProj P r) P.projection

/-- The projection of the fibre product to the torsor. -/
noncomputable def evSnd : evSource P r ⟶ P.P :=
  pullback.snd (pushoutProj P r) P.projection

/-- The structure morphism of the fibre product to the base. -/
noncomputable def evBase : evSource P r ⟶ fppfYoneda.obj T :=
  evFst P r ≫ pushoutProj P r

/-- The two projections of the fibre product agree over the base. -/
theorem evSource_condition :
    evFst P r ≫ pushoutProj P r = evSnd P r ≫ P.projection :=
  pullback.condition

/-- Points of the fibre product are determined by their two components. -/
theorem evSource_hom_ext {Z : FppfSheaf.{u}} {a b : Z ⟶ evSource P r}
    (h1 : a ≫ evFst P r = b ≫ evFst P r) (h2 : a ≫ evSnd P r = b ≫ evSnd P r) : a = b :=
  pullback.hom_ext h1 h2

/-- The point of the fibre product attached to a pair of points over the same base point. -/
noncomputable def evLift {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P r = p ≫ P.projection) :
    fppfYoneda.obj W ⟶ evSource P r :=
  pullback.lift α p h

variable {P r}

/-- The first component of `evLift`. -/
@[simp]
theorem evLift_fst {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P r = p ≫ P.projection) :
    evLift P r α p h ≫ evFst P r = α :=
  pullback.lift_fst _ _ _

/-- The second component of `evLift`. -/
@[simp]
theorem evLift_snd {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P r = p ≫ P.projection) :
    evLift P r α p h ≫ evSnd P r = p :=
  pullback.lift_snd _ _ _

/-- The base point of `evLift`. -/
theorem evLift_base {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P r = p ≫ P.projection) :
    evLift P r α p h ≫ evBase P r = α ≫ pushoutProj P r := by
  rw [evBase, ← Category.assoc, evLift_fst]

/-- The first component of a point of the fibre product lies over its base point. -/
theorem evSource_fst_proj {W : Scheme.{u}} (σ : fppfYoneda.obj W ⟶ evSource P r)
    {c : W ⟶ P.locallyTrivial.coverScheme}
    (hσ : σ ≫ evBase P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    (σ ≫ evFst P r) ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
  rw [Category.assoc, ← evBase]
  exact hσ

/-- The second component of a point of the fibre product lies over its base point. -/
theorem evSource_snd_proj {W : Scheme.{u}} (σ : fppfYoneda.obj W ⟶ evSource P r)
    {c : W ⟶ P.locallyTrivial.coverScheme}
    (hσ : σ ≫ evBase P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    (σ ≫ evSnd P r) ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
  rw [Category.assoc, ← evSource_condition, ← evBase]
  exact hσ

variable (P r)

/-- The local evaluation of a point of the fibre product, through a lift of its base. -/
noncomputable def evSourceLocal {W : Scheme.{u}} (σ : fppfYoneda.obj W ⟶ evSource P r)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hσ : σ ≫ evBase P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    fppfYoneda.obj W ⟶ G'.space.toSheaf :=
  evLocal P r (σ ≫ evFst P r) (σ ≫ evSnd P r) c (evSource_fst_proj σ hσ)
    (evSource_snd_proj σ hσ)

variable {P r}

/-- The local evaluation on the fibre product only depends on the point. -/
theorem evSourceLocal_congr_pt {W : Scheme.{u}} {σ σ' : fppfYoneda.obj W ⟶ evSource P r}
    (hσσ : σ = σ') {c : W ⟶ P.locallyTrivial.coverScheme}
    (h : σ ≫ evBase P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h' : σ' ≫ evBase P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evSourceLocal P r σ c h = evSourceLocal P r σ' c h' := by
  subst hσσ
  rfl

/-- The local evaluation on the fibre product does not depend on the lift. -/
theorem evSourceLocal_congr {W : Scheme.{u}} (σ : fppfYoneda.obj W ⟶ evSource P r)
    {c c' : W ⟶ P.locallyTrivial.coverScheme}
    (hσ : σ ≫ evBase P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hσ' : σ ≫ evBase P r = fppfYoneda.map (c' ≫ P.locallyTrivial.cover)) :
    evSourceLocal P r σ c' hσ' = evSourceLocal P r σ c hσ :=
  evLocal_lift_congr _ _ _ _ _ _

/-- The local evaluation on the fibre product is natural. -/
theorem comp_evSourceLocal {V W : Scheme.{u}} (u : V ⟶ W)
    (σ : fppfYoneda.obj W ⟶ evSource P r) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hσ : σ ≫ evBase P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hσ' : (fppfYoneda.map u ≫ σ) ≫ evBase P r =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover)) :
    fppfYoneda.map u ≫ evSourceLocal P r σ c hσ =
      evSourceLocal P r (fppfYoneda.map u ≫ σ) (u ≫ c) hσ' := by
  have h1 : (fppfYoneda.map u ≫ σ ≫ evFst P r) ≫ pushoutProj P r =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover) := by
    rw [← Category.assoc]
    exact evSource_fst_proj (fppfYoneda.map u ≫ σ) hσ'
  have h2 : (fppfYoneda.map u ≫ σ ≫ evSnd P r) ≫ P.projection =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover) := by
    rw [← Category.assoc]
    exact evSource_snd_proj (fppfYoneda.map u ≫ σ) hσ'
  rw [evSourceLocal, evSourceLocal]
  refine (comp_evLocal u _ _ c _ _ h1 h2).trans ?_
  exact evLocal_congr (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm h1 h2 _ _

variable (P r)

/-- The evaluation pairing, defined on the sections of the fibre product whose base lies in the
covering sieve of the trivialising cover of `P`. -/
noncomputable def evPartial : PartialHom (evBase P r) G'.space.toSheaf (coverSieve P) where
  app {W} x :=
    Scheme.fppfTopology.yonedaEquiv (evSourceLocal P r
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
    have hA : (fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1) ≫ evBase P r =
        fppfYoneda.map ((u ≫ (exists_factor_of_coverSieve x.2).choose) ≫
          P.locallyTrivial.cover) := by
      rw [Category.assoc, GrothendieckTopology.yonedaEquiv_symm_naturality_right,
        yonedaEquiv_symm_map, ← CategoryTheory.Functor.map_comp]
      refine congrArg _ ?_
      rw [Category.assoc, (exists_factor_of_coverSieve x.2).choose_spec]
      rfl
    have hB : (fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1) ≫ evBase P r =
        fppfYoneda.map ((exists_factor_of_coverSieve (SectionsOver.res u x).2).choose ≫
          P.locallyTrivial.cover) := by
      rw [← hres, GrothendieckTopology.yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_map]
      exact congrArg _ (exists_factor_of_coverSieve (SectionsOver.res u x).2).choose_spec.symm
    refine Eq.trans (comp_evSourceLocal u (Scheme.fppfTopology.yonedaEquiv.symm x.1)
      (exists_factor_of_coverSieve x.2).choose _ hA) ?_
    refine Eq.trans (evSourceLocal_congr _ hA hB).symm ?_
    exact (evSourceLocal_congr_pt hres _ hB).symm

/-- **The evaluation pairing** of the pushout sheaf against `P`, glued from the local
formula. -/
noncomputable def evMap : evSource P r ⟶ G'.space.toSheaf :=
  (evPartial P r).glue (coverSieve_mem P)

variable {P r}

/-- The evaluation pairing is computed by the local formula. -/
theorem comp_evMap {W : Scheme.{u}} (σ : fppfYoneda.obj W ⟶ evSource P r)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hσ : σ ≫ evBase P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    σ ≫ evMap P r = evSourceLocal P r σ c hσ := by
  have hbe : GromovWitten.SheafGluing.base (evBase P r)
      (Scheme.fppfTopology.yonedaEquiv σ) = c ≫ P.locallyTrivial.cover := by
    rw [SheafGluing.base_yonedaEquiv, hσ, GrothendieckTopology.yonedaEquiv_yoneda_map]
  have hb : (coverSieve P).arrows
      (GromovWitten.SheafGluing.base (evBase P r) (Scheme.fppfTopology.yonedaEquiv σ)) := by
    rw [hbe]
    exact ⟨_, c, P.locallyTrivial.cover, Presieve.singleton.mk, rfl⟩
  have key := (evPartial P r).glue_app (coverSieve_mem P)
    (⟨Scheme.fppfTopology.yonedaEquiv σ, hb⟩ : SectionsOver (evBase P r) (coverSieve P) W)
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [evMap, GrothendieckTopology.yonedaEquiv_comp, key]
  refine congrArg Scheme.fppfTopology.yonedaEquiv ?_
  have hpt : Scheme.fppfTopology.yonedaEquiv.symm
      ((⟨Scheme.fppfTopology.yonedaEquiv σ, hb⟩ :
        SectionsOver (evBase P r) (coverSieve P) W).1) = σ :=
    Equiv.symm_apply_apply _ _
  have hA : σ ≫ evBase P r = fppfYoneda.map
      ((exists_factor_of_coverSieve (⟨Scheme.fppfTopology.yonedaEquiv σ, hb⟩ :
        SectionsOver (evBase P r) (coverSieve P) W).2).choose ≫ P.locallyTrivial.cover) := by
    rw [hσ, hbe.symm]
    exact congrArg _ (exists_factor_of_coverSieve hb).choose_spec.symm
  refine (evSourceLocal_congr_pt hpt _ hA).trans ?_
  exact evSourceLocal_congr σ hσ hA

variable (P r)

/-- The evaluation of a point of the pushout sheaf at a point of `P` over the same base. -/
noncomputable def evPt {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P r = p ≫ P.projection) :
    fppfYoneda.obj W ⟶ G'.space.toSheaf :=
  evLift P r α p h ≫ evMap P r

variable {P r}

/-- The evaluation only depends on the two points. -/
theorem evPt_congr {W : Scheme.{u}} {α α' : fppfYoneda.obj W ⟶ pushoutSheaf P r}
    {p p' : fppfYoneda.obj W ⟶ P.P} (hα : α = α') (hp : p = p')
    (h : α ≫ pushoutProj P r = p ≫ P.projection)
    (h' : α' ≫ pushoutProj P r = p' ≫ P.projection) : evPt P r α p h = evPt P r α' p' h' := by
  subst hα
  subst hp
  rfl

/-- **The evaluation is computed by the local formula.** -/
theorem evPt_eq_evLocal {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P r = p ≫ P.projection)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hα : α ≫ pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evPt P r α p h = evLocal P r α p c hα hp := by
  have hσ : evLift P r α p h ≫ evBase P r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [evLift_base]
    exact hα
  rw [evPt, comp_evMap _ c hσ, evSourceLocal]
  exact evLocal_congr (evLift_fst _ _ _) (evLift_snd _ _ _) _ _ hα hp

/-- The evaluation is natural in the test scheme. -/
theorem comp_evPt {V W : Scheme.{u}} (u : V ⟶ W) (α : fppfYoneda.obj W ⟶ pushoutSheaf P r)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P r = p ≫ P.projection)
    (h' : (fppfYoneda.map u ≫ α) ≫ pushoutProj P r =
      (fppfYoneda.map u ≫ p) ≫ P.projection) :
    fppfYoneda.map u ≫ evPt P r α p h =
      evPt P r (fppfYoneda.map u ≫ α) (fppfYoneda.map u ≫ p) h' := by
  have hlift : fppfYoneda.map u ≫ evLift P r α p h =
      evLift P r (fppfYoneda.map u ≫ α) (fppfYoneda.map u ≫ p) h' := by
    refine evSource_hom_ext P r ?_ ?_
    · rw [Category.assoc, evLift_fst, evLift_fst]
    · rw [Category.assoc, evLift_snd, evLift_snd]
  rw [evPt, evPt, ← Category.assoc, hlift]

end Ev

/-! ### The evaluation pairing is a bijection on fibres -/

section EvBijective

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} (P : FppfTorsor G T)
  (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r]

/-- The covering sieve of a test scheme on which the trivialisation of `P` is available. -/
theorem pullback_coverSieve_mem {W : Scheme.{u}} (s : W ⟶ T) :
    (coverSieve P).pullback s ∈ Scheme.fppfTopology W :=
  Scheme.fppfTopology.pullback_stable s (coverSieve_mem P)

variable {P r}

/-- Every member of that sieve carries a lift to the trivialising cover. -/
theorem exists_lift_of_pullback {V W : Scheme.{u}} {s : W ⟶ T} {u : V ⟶ W}
    (hu : ((coverSieve P).pullback s).arrows u) :
    ∃ c : V ⟶ P.locallyTrivial.coverScheme, c ≫ P.locallyTrivial.cover = u ≫ s :=
  exists_factor_of_coverSieve hu

/-- **The evaluation is equivariant for the action of `G'`.** -/
theorem evPt_actGluePt {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P r) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ pushoutProj P r = p ≫ P.projection)
    (h' : actGluePt P r g' α ≫ pushoutProj P r = p ≫ P.projection) :
    evPt P r (actGluePt P r g' α) p h' = g' * evPt P r α p h := by
  have hbase : α ≫ pushoutProj P r =
      fppfYoneda.map (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P r)) :=
    (fppfYoneda_map_yonedaEquiv _).symm
  refine hom_ext_of_sieve_pt (pullback_coverSieve_mem P
    (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P r))) fun V u hu => ?_
  obtain ⟨c, hc⟩ := exists_lift_of_pullback hu
  have hα : (fppfYoneda.map u ≫ α) ≫ pushoutProj P r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hbase, ← CategoryTheory.Functor.map_comp, hc]
  have hp : (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, ← h, ← Category.assoc]
    exact hα
  have hgα : (fppfYoneda.map u ≫ actGluePt P r g' α) ≫ pushoutProj P r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [comp_actGluePt, actGluePt_proj]
    exact hα
  have hgα2 : (fppfYoneda.map u ≫ actGluePt P r g' α) ≫ pushoutProj P r =
      (fppfYoneda.map u ≫ p) ≫ P.projection := hgα.trans hp.symm
  have hgα3 : actGluePt P r (fppfYoneda.map u ≫ g') (fppfYoneda.map u ≫ α) ≫
      pushoutProj P r = (fppfYoneda.map u ≫ p) ≫ P.projection := by
    rw [actGluePt_proj]
    exact hα.trans hp.symm
  have hgα4 : actGluePt P r (fppfYoneda.map u ≫ g') (fppfYoneda.map u ≫ α) ≫
      pushoutProj P r = fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [actGluePt_proj]
    exact hα
  rw [comp_evPt u _ _ h' hgα2, MonObj.comp_mul, comp_evPt u _ _ h (hα.trans hp.symm),
    evPt_congr (comp_actGluePt u g' α) rfl hgα2 hgα3,
    evPt_eq_evLocal _ _ _ c hgα4 hp, evPt_eq_evLocal _ _ _ c hα hp,
    evLocal_actGluePt (fppfYoneda.map u ≫ g') _ _ c hα hp hgα4]

/-- **The evaluation is equivariant for the action of `G` on `P`, through `r`.** -/
theorem evPt_actPt {W : Scheme.{u}} (g : fppfYoneda.obj W ⟶ G.space.toSheaf)
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P r) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ pushoutProj P r = p ≫ P.projection)
    (h' : α ≫ pushoutProj P r = actPt g p ≫ P.projection) :
    evPt P r α (actPt g p) h' = evPt P r α p h * (g ≫ r)⁻¹ := by
  have hbase : α ≫ pushoutProj P r =
      fppfYoneda.map (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P r)) :=
    (fppfYoneda_map_yonedaEquiv _).symm
  refine hom_ext_of_sieve_pt (pullback_coverSieve_mem P
    (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P r))) fun V u hu => ?_
  obtain ⟨c, hc⟩ := exists_lift_of_pullback hu
  have hα : (fppfYoneda.map u ≫ α) ≫ pushoutProj P r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hbase, ← CategoryTheory.Functor.map_comp, hc]
  have hp : (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, ← h, ← Category.assoc]
    exact hα
  have hgp : (fppfYoneda.map u ≫ actPt g p) ≫ P.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [comp_actPt, actPt_proj]
    exact hp
  have hgp2 : (fppfYoneda.map u ≫ α) ≫ pushoutProj P r =
      (fppfYoneda.map u ≫ actPt g p) ≫ P.projection := hα.trans hgp.symm
  have hgp3 : (fppfYoneda.map u ≫ α) ≫ pushoutProj P r =
      actPt (fppfYoneda.map u ≫ g) (fppfYoneda.map u ≫ p) ≫ P.projection := by
    rw [actPt_proj]
    exact hα.trans hp.symm
  have hgp4 : actPt (fppfYoneda.map u ≫ g) (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [actPt_proj]
    exact hp
  rw [comp_evPt u _ _ h' hgp2, MonObj.comp_mul, GrpObj.comp_inv,
    comp_evPt u _ _ h (hα.trans hp.symm),
    evPt_congr rfl (comp_actPt (fppfYoneda.map u) g p) hgp2 hgp3, evPt_eq_evLocal _ _ _ c hα hgp4,
    evPt_eq_evLocal _ _ _ c hα hp, evLocal_actPt (fppfYoneda.map u ≫ g) _ _ c hα hp hgp4,
    ← Category.assoc]

/-- **The evaluation at a point of `P` is injective on the fibre.** -/
theorem evPt_injective {W : Scheme.{u}} {α β : fppfYoneda.obj W ⟶ pushoutSheaf P r}
    (p : fppfYoneda.obj W ⟶ P.P) (hα : α ≫ pushoutProj P r = p ≫ P.projection)
    (hβ : β ≫ pushoutProj P r = p ≫ P.projection)
    (heq : evPt P r α p hα = evPt P r β p hβ) : α = β := by
  have hbase : p ≫ P.projection =
      fppfYoneda.map (Scheme.fppfTopology.yonedaEquiv (p ≫ P.projection)) :=
    (fppfYoneda_map_yonedaEquiv _).symm
  refine hom_ext_of_sieve_pt (pullback_coverSieve_mem P
    (Scheme.fppfTopology.yonedaEquiv (p ≫ P.projection))) fun V u hu => ?_
  obtain ⟨c, hc⟩ := exists_lift_of_pullback hu
  have hp : (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hbase, ← CategoryTheory.Functor.map_comp, hc]
  have hα' : (fppfYoneda.map u ≫ α) ≫ pushoutProj P r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hα, ← Category.assoc]
    exact hp
  have hβ' : (fppfYoneda.map u ≫ β) ≫ pushoutProj P r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hβ, ← Category.assoc]
    exact hp
  refine evLocal_injective (fppfYoneda.map u ≫ p) hα' hβ' hp ?_
  rw [← evPt_eq_evLocal _ _ (by rw [Category.assoc, hα, ← Category.assoc]) c hα' hp,
    ← evPt_eq_evLocal _ _ (by rw [Category.assoc, hβ, ← Category.assoc]) c hβ' hp,
    ← comp_evPt u _ _ hα, ← comp_evPt u _ _ hβ, heq]

variable (P r)

/-- The point of the pushout sheaf with prescribed value at a point of `P`, over a test scheme
carrying a lift to the trivialising cover. -/
noncomputable def ptOfEvLocal {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    fppfYoneda.obj W ⟶ pushoutSheaf P r :=
  ptOfCoord P r c (g' * (divPt P p (coverPt c) (by rw [hp, coverPt_proj]) ≫ r))

variable {P r}

/-- The point with prescribed value lies over the expected base point. -/
theorem ptOfEvLocal_proj {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    ptOfEvLocal P r p g' c hp ≫ pushoutProj P r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) :=
  ptOfCoord_proj _ _

/-- **The point with prescribed value has that value.** -/
@[simp]
theorem evPt_ptOfEvLocal {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evPt P r (ptOfEvLocal P r p g' c hp) p
      ((ptOfEvLocal_proj p g' c hp).trans hp.symm) = g' := by
  rw [evPt_eq_evLocal _ _ _ c (ptOfEvLocal_proj p g' c hp) hp]
  exact evLocal_ptOfCoord p c g' hp

/-- The point with prescribed value does not depend on the lift. -/
theorem ptOfEvLocal_congr {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) {c c' : W ⟶ P.locallyTrivial.coverScheme}
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp' : p ≫ P.projection = fppfYoneda.map (c' ≫ P.locallyTrivial.cover)) :
    ptOfEvLocal P r p g' c hp = ptOfEvLocal P r p g' c' hp' := by
  refine evPt_injective p ((ptOfEvLocal_proj p g' c hp).trans hp.symm)
    ((ptOfEvLocal_proj p g' c' hp').trans hp'.symm) ?_
  rw [evPt_ptOfEvLocal, evPt_ptOfEvLocal]

/-- The point with prescribed value is natural in the test scheme. -/
theorem comp_ptOfEvLocal {V W : Scheme.{u}} (u : V ⟶ W) (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp' : (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover)) :
    fppfYoneda.map u ≫ ptOfEvLocal P r p g' c hp =
      ptOfEvLocal P r (fppfYoneda.map u ≫ p) (fppfYoneda.map u ≫ g') (u ≫ c) hp' := by
  have h1 : (fppfYoneda.map u ≫ ptOfEvLocal P r p g' c hp) ≫ pushoutProj P r =
      (fppfYoneda.map u ≫ p) ≫ P.projection := by
    rw [Category.assoc, ptOfEvLocal_proj, Category.assoc, hp]
  refine evPt_injective (fppfYoneda.map u ≫ p) h1
    ((ptOfEvLocal_proj _ _ _ hp').trans hp'.symm) ?_
  rw [← comp_evPt u _ _ ((ptOfEvLocal_proj p g' c hp).trans hp.symm), evPt_ptOfEvLocal,
    evPt_ptOfEvLocal]

end EvBijective

/-! ### Existence of points with prescribed values, and the pushout datum -/

section PushoutExists

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} (P : FppfTorsor G T)
  (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r]

variable {P r}

/-- The base point of a section of a representable sheaf over a base. -/
theorem base_yoneda_map {V W : Scheme.{u}} (s : W ⟶ T) (u : V ⟶ W) :
    GromovWitten.SheafGluing.base (fppfYoneda.map s)
      (u : (fppfYoneda.obj W).obj.obj (op V)) = u ≫ s := by
  have h1 : GromovWitten.SheafGluing.base (fppfYoneda.map s)
      (Scheme.fppfTopology.yonedaEquiv (fppfYoneda.map u)) = u ≫ s := by
    rw [SheafGluing.base_yonedaEquiv, ← CategoryTheory.Functor.map_comp,
      Scheme.fppfTopology.yonedaEquiv_yoneda_map]
  rw [← h1, Scheme.fppfTopology.yonedaEquiv_yoneda_map]

/-- The point with prescribed value only depends on the point of `P` and the value. -/
theorem ptOfEvLocal_congr_pt {W : Scheme.{u}} {p p' : fppfYoneda.obj W ⟶ P.P}
    {g' g'' : fppfYoneda.obj W ⟶ G'.space.toSheaf} (hp0 : p = p') (hg : g' = g'')
    {c : W ⟶ P.locallyTrivial.coverScheme}
    (h : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h' : p' ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    ptOfEvLocal P r p g' c h = ptOfEvLocal P r p' g'' c h' := by
  subst hp0
  subst hg
  rfl

variable (P r)

/-- The partially defined point of the pushout sheaf with prescribed value at a point of `P`. -/
noncomputable def ptOfEvPartial {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (s : W ⟶ T)
    (hs : p ≫ P.projection = fppfYoneda.map s) :
    PartialHom (fppfYoneda.map s) (pushoutSheaf P r) (coverSieve P) where
  app {V} x :=
    Scheme.fppfTopology.yonedaEquiv (ptOfEvLocal P r
      (Scheme.fppfTopology.yonedaEquiv.symm x.1 ≫ p)
      (Scheme.fppfTopology.yonedaEquiv.symm x.1 ≫ g')
      (exists_factor_of_coverSieve x.2).choose (by
        rw [Category.assoc, hs, GrothendieckTopology.yonedaEquiv_symm_naturality_right,
          yonedaEquiv_symm_map]
        exact congrArg _ (exists_factor_of_coverSieve x.2).choose_spec.symm))
  naturality := by
    intro V W' u x
    rw [GrothendieckTopology.yonedaEquiv_naturality]
    refine congrArg Scheme.fppfTopology.yonedaEquiv ?_
    have hres : Scheme.fppfTopology.yonedaEquiv.symm ((SectionsOver.res u x).1) =
        fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1 :=
      (Scheme.fppfTopology.yonedaEquiv_symm_naturality_left u _ x.1).symm
    have hA : (fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1 ≫ p) ≫
        P.projection = fppfYoneda.map ((u ≫ (exists_factor_of_coverSieve x.2).choose) ≫
          P.locallyTrivial.cover) := by
      rw [Category.assoc, Category.assoc, hs,
        GrothendieckTopology.yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_map,
        ← CategoryTheory.Functor.map_comp]
      refine congrArg _ ?_
      rw [Category.assoc, (exists_factor_of_coverSieve x.2).choose_spec]
      rfl
    have hB : (Scheme.fppfTopology.yonedaEquiv.symm ((SectionsOver.res u x).1) ≫ p) ≫
        P.projection = fppfYoneda.map
          ((exists_factor_of_coverSieve (SectionsOver.res u x).2).choose ≫
            P.locallyTrivial.cover) := by
      rw [Category.assoc, hs, GrothendieckTopology.yonedaEquiv_symm_naturality_right,
        yonedaEquiv_symm_map]
      exact congrArg _ (exists_factor_of_coverSieve (SectionsOver.res u x).2).choose_spec.symm
    have hC : (Scheme.fppfTopology.yonedaEquiv.symm ((SectionsOver.res u x).1) ≫ p) ≫
        P.projection = fppfYoneda.map ((u ≫ (exists_factor_of_coverSieve x.2).choose) ≫
          P.locallyTrivial.cover) := by
      rw [hres]
      exact hA
    have hp1 : Scheme.fppfTopology.yonedaEquiv.symm ((SectionsOver.res u x).1) ≫ p =
        fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1 ≫ p := by
      rw [hres, Category.assoc]
    have hg1 : Scheme.fppfTopology.yonedaEquiv.symm ((SectionsOver.res u x).1) ≫ g' =
        fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1 ≫ g' := by
      rw [hres, Category.assoc]
    refine Eq.trans (comp_ptOfEvLocal u _ _ _ _ hA) ?_
    refine Eq.trans (ptOfEvLocal_congr_pt hp1.symm hg1.symm hA hC) ?_
    exact ptOfEvLocal_congr _ _ hC hB

/-- **The point of the pushout sheaf with prescribed value at a point of `P`.** -/
noncomputable def ptOfEv {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (s : W ⟶ T)
    (hs : p ≫ P.projection = fppfYoneda.map s) : fppfYoneda.obj W ⟶ pushoutSheaf P r :=
  (ptOfEvPartial P r p g' s hs).glue (coverSieve_mem P)

variable {P r}

/-- The point with prescribed value lies over the expected base point. -/
theorem ptOfEv_proj {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (s : W ⟶ T)
    (hs : p ≫ P.projection = fppfYoneda.map s) :
    ptOfEv P r p g' s hs ≫ pushoutProj P r = fppfYoneda.map s := by
  refine (ptOfEvPartial P r p g' s hs).glue_comp (coverSieve_mem P) (pushoutProj P r) ?_
  intro V x
  rw [show (ptOfEvPartial P r p g' s hs).app x = Scheme.fppfTopology.yonedaEquiv
      (ptOfEvLocal P r (Scheme.fppfTopology.yonedaEquiv.symm x.1 ≫ p)
        (Scheme.fppfTopology.yonedaEquiv.symm x.1 ≫ g')
        (exists_factor_of_coverSieve x.2).choose _) from rfl,
    SheafGluing.base_yonedaEquiv, ptOfEvLocal_proj,
    GrothendieckTopology.yonedaEquiv_yoneda_map]
  exact (exists_factor_of_coverSieve x.2).choose_spec

/-- The point with prescribed value restricts to the local formula. -/
theorem comp_ptOfEv {V W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (s : W ⟶ T)
    (hs : p ≫ P.projection = fppfYoneda.map s) (u : V ⟶ W)
    (hu : (coverSieve P).arrows (u ≫ s)) (c : V ⟶ P.locallyTrivial.coverScheme)
    (_hc : c ≫ P.locallyTrivial.cover = u ≫ s)
    (hp : (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    fppfYoneda.map u ≫ ptOfEv P r p g' s hs =
      ptOfEvLocal P r (fppfYoneda.map u ≫ p) (fppfYoneda.map u ≫ g') c hp := by
  have hu' : (coverSieve P).arrows
      (GromovWitten.SheafGluing.base (fppfYoneda.map s)
        (u : (fppfYoneda.obj W).obj.obj (op V))) := by
    rw [base_yoneda_map]
    exact hu
  have key := (ptOfEvPartial P r p g' s hs).glue_app (coverSieve_mem P)
    (⟨u, hu'⟩ : SectionsOver (fppfYoneda.map s) (coverSieve P) V)
  have hval : Scheme.fppfTopology.yonedaEquiv (fppfYoneda.map u ≫ ptOfEv P r p g' s hs) =
      (ptOfEvPartial P r p g' s hs).app
        (⟨u, hu'⟩ : SectionsOver (fppfYoneda.map s) (coverSieve P) V) := by
    rw [GrothendieckTopology.yonedaEquiv_comp, ptOfEv]
    exact key
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [hval, show (ptOfEvPartial P r p g' s hs).app
      (⟨u, hu'⟩ : SectionsOver (fppfYoneda.map s) (coverSieve P) V) =
      Scheme.fppfTopology.yonedaEquiv (ptOfEvLocal P r
        (Scheme.fppfTopology.yonedaEquiv.symm
          ((⟨u, hu'⟩ : SectionsOver (fppfYoneda.map s) (coverSieve P) V).1) ≫ p)
        (Scheme.fppfTopology.yonedaEquiv.symm
          ((⟨u, hu'⟩ : SectionsOver (fppfYoneda.map s) (coverSieve P) V).1) ≫ g')
        (exists_factor_of_coverSieve
          (⟨u, hu'⟩ : SectionsOver (fppfYoneda.map s) (coverSieve P) V).2).choose _) from rfl]
  refine congrArg Scheme.fppfTopology.yonedaEquiv ?_
  have hsymm : Scheme.fppfTopology.yonedaEquiv.symm
      ((⟨u, hu'⟩ : SectionsOver (fppfYoneda.map s) (coverSieve P) V).1) =
      fppfYoneda.map u := yonedaEquiv_symm_map u
  have hD : (fppfYoneda.map u ≫ p) ≫ P.projection = fppfYoneda.map
      ((exists_factor_of_coverSieve
        (⟨u, hu'⟩ : SectionsOver (fppfYoneda.map s) (coverSieve P) V).2).choose ≫
          P.locallyTrivial.cover) := by
    rw [Category.assoc, hs, ← CategoryTheory.Functor.map_comp]
    refine congrArg _ ?_
    rw [(exists_factor_of_coverSieve hu').choose_spec, base_yoneda_map]
  refine Eq.trans (ptOfEvLocal_congr_pt (by rw [hsymm]) (by rw [hsymm]) _ hD) ?_
  exact ptOfEvLocal_congr _ _ hD hp

/-- **The point with prescribed value has that value.** -/
theorem evPt_ptOfEv {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (s : W ⟶ T)
    (hs : p ≫ P.projection = fppfYoneda.map s) :
    evPt P r (ptOfEv P r p g' s hs) p ((ptOfEv_proj p g' s hs).trans hs.symm) = g' := by
  refine hom_ext_of_sieve_pt (pullback_coverSieve_mem P s) fun V u hu => ?_
  obtain ⟨c, hc⟩ := exists_lift_of_pullback hu
  have hp : (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hs, ← CategoryTheory.Functor.map_comp, hc]
  have hloc := comp_ptOfEv (P := P) (r := r) p g' s hs u hu c hc hp
  have h1 : (fppfYoneda.map u ≫ ptOfEv P r p g' s hs) ≫ pushoutProj P r =
      (fppfYoneda.map u ≫ p) ≫ P.projection := by
    rw [Category.assoc, ptOfEv_proj, Category.assoc, hs]
  rw [comp_evPt u _ _ _ h1, evPt_congr hloc rfl h1
    ((ptOfEvLocal_proj (fppfYoneda.map u ≫ p) (fppfYoneda.map u ≫ g') c hp).trans hp.symm),
    evPt_ptOfEvLocal]

variable (P r)

/-- **The pushout datum of a `G`-torsor along a homomorphism `r : G ⟶ G'`.**  This is the
existence statement announced in the module docstring: it is unconditional, and no
sheafification is involved. -/
noncomputable def pushoutTorsor : PushoutTorsor r P where
  sheaf := pushoutSheaf P r
  action := pushoutAction P r
  projection := pushoutProj P r
  action_over := pushoutSmul_proj P r
  ev α p h := evPt P r α p h
  ev_naturality u α p h h' := comp_evPt u α p h h'
  ev_actPt g' α p h h' := by
    have hg : actGluePt P r g' α ≫ pushoutProj P r = p ≫ P.projection := by
      rw [actGluePt_proj]
      exact h
    have key : evPt P r (actGluePt P r g' α) p hg = g' * evPt P r α p h :=
      evPt_actGluePt (P := P) (r := r) g' α p h hg
    refine Eq.trans ?_ key
    exact evPt_congr (lift_comp_pushoutSmul (P := P) (r := r) g' α) rfl h' hg
  ev_actPt_right g α p h h' := evPt_actPt (P := P) (r := r) g α p h h'
  ev_bijective {W} p g' := by
    have hs : p ≫ P.projection =
        fppfYoneda.map (Scheme.fppfTopology.yonedaEquiv (p ≫ P.projection)) :=
      (fppfYoneda_map_yonedaEquiv _).symm
    have hbase : ptOfEv P r p g' (Scheme.fppfTopology.yonedaEquiv (p ≫ P.projection)) hs ≫
        pushoutProj P r = p ≫ P.projection := by
      rw [ptOfEv_proj, fppfYoneda_map_yonedaEquiv]
    refine ⟨⟨ptOfEv P r p g' _ hs, hbase⟩, evPt_ptOfEv p g' _ hs, ?_⟩
    intro β hβ
    refine Subtype.ext (evPt_injective p β.2 hbase ?_)
    rw [hβ, evPt_ptOfEv]

/-- **The pushout torsor.**  Every fppf `G`-torsor `P` over `T` and every homomorphism
`r : G ⟶ G'` of group objects produce an fppf `G'`-torsor `r_* P` over `T`. -/
noncomputable def pushoutFppfTorsor : FppfTorsor G' T :=
  (pushoutTorsor P r).toFppfTorsor

/-- The underlying sheaf of the pushout torsor is the glued sheaf. -/
@[simp]
theorem pushoutFppfTorsor_P : (pushoutFppfTorsor P r).P = pushoutSheaf P r :=
  rfl

/-- The projection of the pushout torsor is the glued structure morphism. -/
@[simp]
theorem pushoutFppfTorsor_projection :
    (pushoutFppfTorsor P r).projection = pushoutProj P r :=
  rfl

end PushoutExists

/-! ### The induced equivariant map on the pushout -/

section Target

open GromovWitten.SheafGluing

/-- An equivariant morphism of module objects commutes with the action on points. -/
theorem actPt_comp_equivariant {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {M X Y : C} [MonObj M] [ModObj M X] [ModObj M Y] (φ : X ⟶ Y)
    (hφ : ModObj.smul (M := M) (X := X) ≫ φ = (M ◁ φ) ≫ ModObj.smul (M := M) (X := Y))
    {Z : C} (g : Z ⟶ M) (p : Z ⟶ X) : actPt g p ≫ φ = actPt g (p ≫ φ) := by
  rw [actPt, Category.assoc, hφ, ← Category.assoc, ConeQuotient.lift_whiskerLeft, actPt]

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {U : AlgebraicSpaceAction G}
  {U' : AlgebraicSpaceAction G'} (P : ActionTorsor G U T)
  (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r]
  (pt : U.space.toSheaf ⟶ U'.space.toSheaf)

/-- `r`-equivariance of a morphism between the two action spaces, on points. -/
def IsEquivariantOver : Prop :=
  ∀ ⦃Z : FppfSheaf.{u}⦄ (g : Z ⟶ G.space.toSheaf) (x : Z ⟶ U.space.toSheaf),
    actPt g x ≫ pt = actPt (g ≫ r) (x ≫ pt)

variable {P r pt}

/-- The equivariant map of an action torsor commutes with the action on points. -/
theorem actPt_comp_target {Z : FppfSheaf.{u}} (g : Z ⟶ G.space.toSheaf) (p : Z ⟶ P.P) :
    actPt g p ≫ P.target = actPt g (p ≫ P.target) :=
  actPt_comp_equivariant P.target P.target_equivariant g p

variable (P r pt)

/-- The local formula for the induced equivariant map on the pushout: `α ↦ α (L c) · pt (L c)`,
where `L c` is the tautological point of `P` at a lift `c` of the base. -/
noncomputable def targetLocal {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor r)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hα : α ≫ pushoutProj P.toFppfTorsor r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover)) : fppfYoneda.obj W ⟶ U'.space.toSheaf :=
  actPt (evPt P.toFppfTorsor r α (coverPt c) (by rw [hα, coverPt_proj]))
    (coverPt c ≫ P.target ≫ pt)

variable {P r pt}

/-- The local formula only depends on the point of the pushout. -/
theorem targetLocal_congr_pt {W : Scheme.{u}}
    {α β : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor r} (hαβ : α = β)
    {c : W ⟶ P.locallyTrivial.coverScheme}
    (hα : α ≫ pushoutProj P.toFppfTorsor r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hβ : β ≫ pushoutProj P.toFppfTorsor r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    targetLocal P r pt α c hα = targetLocal P r pt β c hβ := by
  subst hαβ
  rfl

/-- **The local formula does not depend on the chosen lift.** -/
theorem targetLocal_lift_congr (hpt : IsEquivariantOver r pt) {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor r)
    {c c' : W ⟶ P.locallyTrivial.coverScheme}
    (hα : α ≫ pushoutProj P.toFppfTorsor r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hα' : α ≫ pushoutProj P.toFppfTorsor r =
      fppfYoneda.map (c' ≫ P.locallyTrivial.cover)) :
    targetLocal P r pt α c' hα' = targetLocal P r pt α c hα := by
  have hcc : c ≫ P.locallyTrivial.cover = c' ≫ P.locallyTrivial.cover :=
    cover_lift_eq (hα.symm.trans hα')
  have hL : coverPt c = actPt (coverDiv hcc) (coverPt c') := (actPt_divPt _ _ _).symm
  have hev : evPt P.toFppfTorsor r α (coverPt c) (by rw [hα, coverPt_proj]) =
      evPt P.toFppfTorsor r α (coverPt c') (by rw [hα', coverPt_proj]) *
        (coverDiv hcc ≫ r)⁻¹ := by
    refine Eq.trans (evPt_congr rfl hL (by rw [hα, coverPt_proj])
      (by rw [hα', actPt_proj, coverPt_proj])) ?_
    exact evPt_actPt (coverDiv hcc) α (coverPt c') (by rw [hα', coverPt_proj])
      (by rw [hα', actPt_proj, coverPt_proj])
  have htg : coverPt c ≫ P.target ≫ pt =
      actPt (coverDiv hcc ≫ r) (coverPt c' ≫ P.target ≫ pt) := by
    rw [← Category.assoc, hL, actPt_comp_target, hpt (coverDiv hcc) (coverPt c' ≫ P.target),
      Category.assoc]
  rw [targetLocal, targetLocal, hev, htg, ← actPt_mul, inv_mul_cancel_right]

/-- The local formula is natural in the test scheme. -/
theorem comp_targetLocal {V W : Scheme.{u}} (u : V ⟶ W)
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor r)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hα : α ≫ pushoutProj P.toFppfTorsor r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hα' : (fppfYoneda.map u ≫ α) ≫ pushoutProj P.toFppfTorsor r =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover)) :
    fppfYoneda.map u ≫ targetLocal P r pt α c hα =
      targetLocal P r pt (fppfYoneda.map u ≫ α) (u ≫ c) hα' := by
  have hcp : fppfYoneda.map u ≫ coverPt c = coverPt (u ≫ c) := comp_coverPt u c
  have pf1 : (fppfYoneda.map u ≫ α) ≫ pushoutProj P.toFppfTorsor r =
      (fppfYoneda.map u ≫ coverPt c) ≫ P.projection := by
    rw [Category.assoc, hα, Category.assoc, coverPt_proj]
  have pf2 : (fppfYoneda.map u ≫ α) ≫ pushoutProj P.toFppfTorsor r =
      coverPt (u ≫ c) ≫ P.projection := by
    rw [hα', coverPt_proj]
  have hev := comp_evPt u α (coverPt c) (by rw [hα, coverPt_proj]) pf1
  have hA := evPt_congr (P := P.toFppfTorsor) (r := r) rfl hcp pf1 pf2
  rw [targetLocal, targetLocal, comp_actPt, hev, hA, ← Category.assoc, hcp]

end Target

/-! ### The contraction of an action torsor -/

section Contraction

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {U : AlgebraicSpaceAction G}
  {U' : AlgebraicSpaceAction G'} (P : ActionTorsor G U T)
  (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r]
  (pt : U.space.toSheaf ⟶ U'.space.toSheaf) (hpt : IsEquivariantOver r pt)

/-- The induced equivariant map on the pushout, defined on the sections whose base lies in the
covering sieve of the trivialising cover of `P`. -/
noncomputable def targetPartial :
    PartialHom (pushoutProj P.toFppfTorsor r) U'.space.toSheaf (coverSieve P.toFppfTorsor) where
  app {W} x :=
    Scheme.fppfTopology.yonedaEquiv (targetLocal P r pt
      (Scheme.fppfTopology.yonedaEquiv.symm x.1)
      (exists_factor_of_coverSieve x.2).choose (by
        rw [GrothendieckTopology.yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_map]
        exact congrArg _ (exists_factor_of_coverSieve x.2).choose_spec.symm))
  naturality := by
    intro V W u x
    rw [GrothendieckTopology.yonedaEquiv_naturality]
    refine congrArg Scheme.fppfTopology.yonedaEquiv ?_
    have hres : Scheme.fppfTopology.yonedaEquiv.symm ((SectionsOver.res u x).1) =
        fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1 :=
      (Scheme.fppfTopology.yonedaEquiv_symm_naturality_left u _ x.1).symm
    have hA : (fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1) ≫
        pushoutProj P.toFppfTorsor r = fppfYoneda.map
          ((u ≫ (exists_factor_of_coverSieve x.2).choose) ≫ P.locallyTrivial.cover) := by
      rw [Category.assoc, GrothendieckTopology.yonedaEquiv_symm_naturality_right,
        yonedaEquiv_symm_map, ← CategoryTheory.Functor.map_comp]
      refine congrArg _ ?_
      rw [Category.assoc, (exists_factor_of_coverSieve x.2).choose_spec]
      rfl
    have hB : (fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1) ≫
        pushoutProj P.toFppfTorsor r = fppfYoneda.map
          ((exists_factor_of_coverSieve (SectionsOver.res u x).2).choose ≫
            P.locallyTrivial.cover) := by
      rw [← hres, GrothendieckTopology.yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_map]
      exact congrArg _ (exists_factor_of_coverSieve (SectionsOver.res u x).2).choose_spec.symm
    refine Eq.trans (comp_targetLocal u (Scheme.fppfTopology.yonedaEquiv.symm x.1)
      (exists_factor_of_coverSieve x.2).choose _ hA) ?_
    refine Eq.trans (targetLocal_lift_congr hpt _ hA hB).symm ?_
    exact (targetLocal_congr_pt hres _ hB).symm

/-- **The induced equivariant map `r_* P ⟶ U'`.** -/
noncomputable def targetMap : pushoutSheaf P.toFppfTorsor r ⟶ U'.space.toSheaf :=
  (targetPartial P r pt hpt).glue (coverSieve_mem P.toFppfTorsor)

variable {P r pt}

/-- The induced map is computed by the local formula. -/
theorem comp_targetMap {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor r)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hα : α ≫ pushoutProj P.toFppfTorsor r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    α ≫ targetMap P r pt hpt = targetLocal P r pt α c hα := by
  have hbe : GromovWitten.SheafGluing.base (pushoutProj P.toFppfTorsor r)
      (Scheme.fppfTopology.yonedaEquiv α) = c ≫ P.locallyTrivial.cover := by
    rw [SheafGluing.base_yonedaEquiv, hα, GrothendieckTopology.yonedaEquiv_yoneda_map]
  have hb : (coverSieve P.toFppfTorsor).arrows
      (GromovWitten.SheafGluing.base (pushoutProj P.toFppfTorsor r)
        (Scheme.fppfTopology.yonedaEquiv α)) := by
    rw [hbe]
    exact ⟨_, c, P.locallyTrivial.cover, Presieve.singleton.mk, rfl⟩
  have key := (targetPartial P r pt hpt).glue_app (coverSieve_mem P.toFppfTorsor)
    (⟨Scheme.fppfTopology.yonedaEquiv α, hb⟩ :
      SectionsOver (pushoutProj P.toFppfTorsor r) (coverSieve P.toFppfTorsor) W)
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [targetMap, GrothendieckTopology.yonedaEquiv_comp, key]
  refine congrArg Scheme.fppfTopology.yonedaEquiv ?_
  have hpt2 : Scheme.fppfTopology.yonedaEquiv.symm
      ((⟨Scheme.fppfTopology.yonedaEquiv α, hb⟩ :
        SectionsOver (pushoutProj P.toFppfTorsor r) (coverSieve P.toFppfTorsor) W).1) = α :=
    Equiv.symm_apply_apply _ _
  have hA : α ≫ pushoutProj P.toFppfTorsor r = fppfYoneda.map
      ((exists_factor_of_coverSieve (⟨Scheme.fppfTopology.yonedaEquiv α, hb⟩ :
        SectionsOver (pushoutProj P.toFppfTorsor r)
          (coverSieve P.toFppfTorsor) W).2).choose ≫ P.locallyTrivial.cover) := by
    rw [hα, hbe.symm]
    exact congrArg _ (exists_factor_of_coverSieve hb).choose_spec.symm
  refine (targetLocal_congr_pt hpt2 _ hA).trans ?_
  exact targetLocal_lift_congr hpt α hα hA

/-- **The induced map is `G'`-equivariant, on points.** -/
theorem actGluePt_comp_targetMap {W : Scheme.{u}}
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor r) :
    actGluePt P.toFppfTorsor r g' α ≫ targetMap P r pt hpt =
      actPt g' (α ≫ targetMap P r pt hpt) := by
  have hbase : α ≫ pushoutProj P.toFppfTorsor r = fppfYoneda.map
      (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P.toFppfTorsor r)) :=
    (fppfYoneda_map_yonedaEquiv _).symm
  refine hom_ext_of_sieve_pt (pullback_coverSieve_mem P.toFppfTorsor
    (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P.toFppfTorsor r))) fun V u hu => ?_
  obtain ⟨c, hc⟩ := exists_lift_of_pullback hu
  have hα : (fppfYoneda.map u ≫ α) ≫ pushoutProj P.toFppfTorsor r =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hbase, ← CategoryTheory.Functor.map_comp, hc]
  have hgα : actGluePt P.toFppfTorsor r (fppfYoneda.map u ≫ g') (fppfYoneda.map u ≫ α) ≫
      pushoutProj P.toFppfTorsor r = fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [actGluePt_proj]
    exact hα
  have hp : coverPt c ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover) :=
    coverPt_proj c
  rw [← Category.assoc, comp_actGluePt, comp_targetMap hpt _ c hgα, targetLocal,
    evPt_actGluePt (fppfYoneda.map u ≫ g') _ _ (hα.trans hp.symm) (hgα.trans hp.symm),
    actPt_mul, comp_actPt]
  refine congrArg (fun q => actPt (fppfYoneda.map u ≫ g') q) ?_
  exact ((Category.assoc (fppfYoneda.map u) α (targetMap P r pt hpt)).symm.trans
    (comp_targetMap hpt (fppfYoneda.map u ≫ α) c hα)).symm

variable (P r pt)

/-- **The induced map is `G'`-equivariant.** -/
theorem targetMap_equivariant :
    ModObj.smul (M := G'.space.toSheaf) (X := pushoutSheaf P.toFppfTorsor r) ≫
        targetMap P r pt hpt =
      (G'.space.toSheaf ◁ targetMap P r pt hpt) ≫
        ModObj.smul (M := G'.space.toSheaf) (X := U'.space.toSheaf) := by
  refine hom_ext_points fun W ω => ?_
  rw [← Category.assoc, ← Category.assoc, ← lift_comp_fst_snd ω,
    ConeQuotient.lift_whiskerLeft, pushoutAction_smul (P := P.toFppfTorsor) (r := r),
    lift_comp_pushoutSmul]
  exact actGluePt_comp_targetMap hpt _ _

/-- **The contraction of an action torsor along a homomorphism of group objects.**  The pushout
`r_* P` of the underlying torsor, with the induced equivariant map to `U'`. -/
noncomputable def pushoutActionTorsor : ActionTorsor G' U' T where
  toFppfTorsor := pushoutFppfTorsor P.toFppfTorsor r
  target := targetMap P r pt hpt
  target_equivariant := targetMap_equivariant P r pt hpt

/-- The underlying torsor of the contraction is the pushout torsor. -/
@[simp]
theorem pushoutActionTorsor_toFppfTorsor :
    (pushoutActionTorsor P r pt hpt).toFppfTorsor = pushoutFppfTorsor P.toFppfTorsor r :=
  rfl

/-- The equivariant map of the contraction is the induced map. -/
@[simp]
theorem pushoutActionTorsor_target :
    (pushoutActionTorsor P r pt hpt).target = targetMap P r pt hpt :=
  rfl

end Contraction

end TorsorPushout

end GromovWitten.AlgebraicGeometry
