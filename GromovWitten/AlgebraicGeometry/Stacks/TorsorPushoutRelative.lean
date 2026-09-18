/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.TorsorPushout

/-!
# The pushout of an fppf torsor along a homomorphism of group objects *over the base*

`Stacks/TorsorPushout.lean` constructs the pushout `r_* P` of an fppf `G`-torsor `P` over a
scheme `T` along a homomorphism `r : G ⟶ G'` of *absolute* group objects.  The contraction of
the affine cone quotient `[C/E]` by a scalar `r : Γ(T, 𝒪)` is not of that shape: multiplication
by `r` on the vector bundle group `𝔾ₐ^σ` is a homomorphism only *relative to `T`*, since the
scalar itself is a section over `T`.

This file removes that restriction.  A `TorsorPushoutRel.RelMonHom G G' T` is a morphism
`G ⊗ y(T) ⟶ G'` of fppf sheaves which, on the `W`-points lying over a base point `b : W ⟶ T`,
is a homomorphism of groups; naturality in `W` is automatic, since the datum is a single
morphism of sheaves.  This is exactly a homomorphism of group objects over `y(T)`.

The whole descent construction of `Stacks/TorsorPushout.lean` goes through verbatim with
`g ≫ r` replaced by `ρ.pt b g`, where `b` is the base point over which `g` lives, and this file
carries it out.

## Main definitions

* `TorsorPushoutRel.RelMonHom G G' T`, with its point calculus `RelMonHom.pt`,
  `RelMonHom.pt_one`, `RelMonHom.pt_mul`, `RelMonHom.pt_inv`, `RelMonHom.comp_pt`, and the
  comparison `RelMonHom.ofMonHom` with absolute homomorphisms.
* `TorsorPushoutRel.RelEquivMap ρ U U'`: a morphism `U ⊗ y(T) ⟶ U'` of action spaces which is
  `ρ`-equivariant over `T`, again stated on points.
* `TorsorPushoutRel.PushoutTorsorRel ρ P`: the defining property of the relative pushout
  (a sheaf with a `G'`-action and an evaluation pairing `ev`), from which the torsor axioms are
  *derived* (`PushoutTorsorRel.toFppfTorsor`).
* `TorsorPushoutRel.pushoutSheaf P ρ`, glued from `TorsorPushoutRel.descentDatum P ρ` along the
  trivialising cover of `P`, with its action `pushoutAction`, its evaluation `evPt` and the
  points `ptOfEv` with prescribed values; `TorsorPushoutRel.pushoutFppfTorsor P ρ : FppfTorsor
  G' T` is the relative pushout `ρ_* P`.
* `TorsorPushoutRel.pushoutActionTorsor P ρ τ : ActionTorsor G' U' T`, the contraction of an
  action torsor along `ρ` and a `ρ`-equivariant `τ`.
* `TorsorPushoutRel.targetMap_eq_actPt`: the induced map of the contraction, evaluated at any
  point `p` of `P` over the same base, is `ev α p · τ (p)`; no lift of the base to the
  trivialising cover is needed.  It yields `TorsorPushoutRel.contractionIsoTrivial` (the
  contraction of a torsor with a global section is trivial, with the contracted point) and
  `TorsorPushoutRel.pushoutTrivialIso` (`ρ_*` of the trivial torsor with point `t` is the
  trivial torsor with point `τ (t)`).
* `TorsorPushoutRel.idPushoutTorsorRel`: the torsor `P` itself is a pushout datum of `P` along
  the identity, with `ev` the difference of two points.
* The instance needed for the cone quotient: `TorsorPushoutRel.scaleRelMonHom σ T r`
  (multiplication by `r : Γ(T, 𝒪)` on `𝔾ₐ^σ`, a homomorphism of group objects only over `T`),
  `TorsorPushoutRel.coneScaleRelEquivMap A bas r` (the cone contraction `ConeQuotient.scaleRing`,
  whose equivariance is exactly `ConeQuotient.scaleRing_actOn`), the resulting
  `TorsorPushoutRel.coneContraction` of *every* object of `[C/E]` over `T`, and the comparisons
  `TorsorPushoutRel.coneScaleRelEquivMap_pt_eq_coneTwist` and
  `TorsorPushoutRel.coneContractionEmbeddingIso` with `ConeQuotient.coneTwist` on trivialised
  torsors.

Everything is unconditional: no sheafification, no hom sheaf, no triviality hypothesis on `P`.
What is *not* done is the functoriality of `ρ_*` on arrows of torsors and the uniqueness of a
pushout datum (hence the unit law `(𝟙)_* P ≅ P` as an isomorphism of torsors).
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

namespace TorsorPushoutRel

universe u

open TorsorPushout

/-! ### Homomorphisms of group objects relative to the base -/

section RelMonHom

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}

/-- **A homomorphism of group objects over `y(T)`.**  The datum is a morphism of fppf sheaves
`G ⊗ y(T) ⟶ G'`; the axioms say that, for every scheme `W` and every base point
`b : y(W) ⟶ y(T)`, the induced map on `W`-points is a homomorphism of groups
`G(W) → G'(W)`.  Naturality in `W` is automatic because the datum is a single morphism of
sheaves. -/
structure RelMonHom (G G' : AlgebraicSpaceGroup.{u}) (T : Scheme.{u}) where
  /-- The underlying morphism of fppf sheaves. -/
  toFun : G.space.toSheaf ⊗ fppfYoneda.obj T ⟶ G'.space.toSheaf
  /-- On `W`-points over a base point, the unit goes to the unit. -/
  map_one' : ∀ {W : Scheme.{u}} (b : fppfYoneda.obj W ⟶ fppfYoneda.obj T),
    lift (1 : fppfYoneda.obj W ⟶ G.space.toSheaf) b ≫ toFun = 1
  /-- On `W`-points over a base point, products go to products. -/
  map_mul' : ∀ {W : Scheme.{u}} (b : fppfYoneda.obj W ⟶ fppfYoneda.obj T)
    (x y : fppfYoneda.obj W ⟶ G.space.toSheaf),
    lift (x * y) b ≫ toFun = (lift x b ≫ toFun) * (lift y b ≫ toFun)

namespace RelMonHom

variable (ρ : RelMonHom G G' T)

/-- The value of a relative homomorphism at a generalised point `x` of `G` lying over the base
point `b`. -/
noncomputable def pt {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T)
    (x : Z ⟶ G.space.toSheaf) : Z ⟶ G'.space.toSheaf :=
  lift x b ≫ ρ.toFun

/-- The value of a relative homomorphism is natural in the source. -/
theorem comp_pt {Y Z : FppfSheaf.{u}} (u : Y ⟶ Z) (b : Z ⟶ fppfYoneda.obj T)
    (x : Z ⟶ G.space.toSheaf) : u ≫ ρ.pt b x = ρ.pt (u ≫ b) (u ≫ x) := by
  rw [pt, pt, ← Category.assoc, comp_lift]

/-- The value of a relative homomorphism only depends on the base point and the point. -/
theorem pt_congr {Z : FppfSheaf.{u}} {b b' : Z ⟶ fppfYoneda.obj T}
    {x x' : Z ⟶ G.space.toSheaf} (hb : b = b') (hx : x = x') : ρ.pt b x = ρ.pt b' x' := by
  rw [hb, hx]

/-- A relative homomorphism takes the unit to the unit, on arbitrary generalised points. -/
@[simp]
theorem pt_one {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) :
    ρ.pt b (1 : Z ⟶ G.space.toSheaf) = 1 := by
  refine hom_ext_points fun W ω => ?_
  rw [comp_pt, MonObj.comp_one, MonObj.comp_one]
  exact ρ.map_one' _

/-- A relative homomorphism is multiplicative, on arbitrary generalised points. -/
theorem pt_mul {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T)
    (x y : Z ⟶ G.space.toSheaf) : ρ.pt b (x * y) = ρ.pt b x * ρ.pt b y := by
  refine hom_ext_points fun W ω => ?_
  rw [comp_pt, MonObj.comp_mul, MonObj.comp_mul, comp_pt, comp_pt]
  exact ρ.map_mul' _ _ _

/-- A relative homomorphism commutes with inverses. -/
theorem pt_inv {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf) :
    ρ.pt b x⁻¹ = (ρ.pt b x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pt_mul, inv_mul_cancel, pt_one]

end RelMonHom

/-- An absolute homomorphism of group objects is a relative one. -/
noncomputable def RelMonHom.ofMonHom (T : Scheme.{u})
    (r : G.space.toSheaf ⟶ G'.space.toSheaf) [IsMonHom r] : RelMonHom G G' T where
  toFun := fst _ _ ≫ r
  map_one' _ := by simp only [← Category.assoc, lift_fst, MonObj.one_comp]
  map_mul' _ _ _ := by simp only [← Category.assoc, lift_fst, MonObj.mul_comp]

/-- The relative homomorphism attached to an absolute one acts by composition. -/
@[simp]
theorem RelMonHom.pt_ofMonHom (T : Scheme.{u}) (r : G.space.toSheaf ⟶ G'.space.toSheaf)
    [IsMonHom r] {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf) :
    (RelMonHom.ofMonHom T r).pt b x = x ≫ r := by
  rw [RelMonHom.pt, RelMonHom.ofMonHom, ← Category.assoc, lift_fst]

end RelMonHom

/-! ### Equivariant maps of action spaces relative to the base -/

section RelEquivMap

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}

/-- **A `ρ`-equivariant morphism of action spaces over `y(T)`.**  The datum is a morphism of
fppf sheaves `U ⊗ y(T) ⟶ U'`; the axiom says that on `W`-points over a base point `b` it
intertwines the action of `G` with the action of `G'` through `ρ`. -/
structure RelEquivMap (ρ : RelMonHom G G' T) (U : AlgebraicSpaceAction G)
    (U' : AlgebraicSpaceAction G') where
  /-- The underlying morphism of fppf sheaves. -/
  toFun : U.space.toSheaf ⊗ fppfYoneda.obj T ⟶ U'.space.toSheaf
  /-- Equivariance on `W`-points lying over a base point. -/
  equivariant' : ∀ {W : Scheme.{u}} (b : fppfYoneda.obj W ⟶ fppfYoneda.obj T)
    (g : fppfYoneda.obj W ⟶ G.space.toSheaf) (x : fppfYoneda.obj W ⟶ U.space.toSheaf),
    lift (actPt g x) b ≫ toFun = actPt (ρ.pt b g) (lift x b ≫ toFun)

namespace RelEquivMap

variable {ρ : RelMonHom G G' T} {U : AlgebraicSpaceAction G} {U' : AlgebraicSpaceAction G'}
  (τ : RelEquivMap ρ U U')

/-- The value of a relative equivariant map at a generalised point of `U` over a base point. -/
noncomputable def pt {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T)
    (x : Z ⟶ U.space.toSheaf) : Z ⟶ U'.space.toSheaf :=
  lift x b ≫ τ.toFun

/-- The value of a relative equivariant map is natural in the source. -/
theorem comp_pt {Y Z : FppfSheaf.{u}} (u : Y ⟶ Z) (b : Z ⟶ fppfYoneda.obj T)
    (x : Z ⟶ U.space.toSheaf) : u ≫ τ.pt b x = τ.pt (u ≫ b) (u ≫ x) := by
  rw [pt, pt, ← Category.assoc, comp_lift]

/-- The value of a relative equivariant map only depends on the base point and the point. -/
theorem pt_congr {Z : FppfSheaf.{u}} {b b' : Z ⟶ fppfYoneda.obj T}
    {x x' : Z ⟶ U.space.toSheaf} (hb : b = b') (hx : x = x') : τ.pt b x = τ.pt b' x' := by
  rw [hb, hx]

/-- **Equivariance on arbitrary generalised points.** -/
theorem pt_actPt {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T)
    (g : Z ⟶ G.space.toSheaf) (x : Z ⟶ U.space.toSheaf) :
    τ.pt b (actPt g x) = actPt (ρ.pt b g) (τ.pt b x) := by
  refine hom_ext_points fun W ω => ?_
  rw [comp_pt, comp_actPt, comp_actPt, comp_pt, ρ.comp_pt]
  exact τ.equivariant' _ _ _

end RelEquivMap

end RelEquivMap

/-! ### The pushout datum -/

section Pushout

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}

/-- **The pushout `ρ_* P` of a `G`-torsor `P` along a relative homomorphism `ρ`**, presented
by its defining property rather than by a construction.

A point of `ρ_* P` over a scheme `W` is a `G`-equivariant map `φ` from the fibre of `P` over `W`
to `G'`, where `G` acts on `G'` through `ρ`; `ev α p` is the value `φ (p)` of the equivariant
map `α` at a point `p` of `P`.  The equivariance rules are `ev (g' · α) p = g' * ev α p` and
`ev α (g · p) = ev α p * (ρ g)⁻¹`, and `ev` identifies the fibre of `ρ_* P` over `W` with the
points of `G'` over `W` as soon as `P` has a point over `W`.

No sheafification and no hom sheaf occur: the data is the sheaf itself together with the
evaluation pairing on points. -/
structure PushoutTorsorRel (ρ : RelMonHom G G' T) (P : FppfTorsor G T) where
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
  /-- Evaluation is equivariant for the action of `G` on `P`, through `ρ`. -/
  ev_actPt_right : ∀ {W : Scheme.{u}} (g : fppfYoneda.obj W ⟶ G.space.toSheaf)
    (α : fppfYoneda.obj W ⟶ sheaf) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ projection = p ≫ P.projection)
    (h' : α ≫ projection = actPt g p ≫ P.projection),
    ev α (actPt g p) h' = ev α p h * (ρ.pt (p ≫ P.projection) g)⁻¹
  /-- Evaluation at a point of `P` is a bijection from the fibre of the pushout to the points
  of `G'`. -/
  ev_bijective : ∀ {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf),
    ∃! α : {α : fppfYoneda.obj W ⟶ sheaf // α ≫ projection = p ≫ P.projection},
      ev α.1 p α.2 = g'

attribute [instance] PushoutTorsorRel.action

namespace PushoutTorsorRel

variable {ρ : RelMonHom G G' T} {P : FppfTorsor G T} (A : PushoutTorsorRel ρ P)

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
  set ζ := Scheme.fppfTopology.yonedaEquiv.symm y.1 with hζ
  have hbase : ζ ≫ pullback.fst A.projection A.projection ≫ A.projection =
      fppfYoneda.map (GromovWitten.SheafGluing.base
        (pullback.fst A.projection A.projection ≫ A.projection) y.1) := by
    rw [hζ, GrothendieckTopology.yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_map]
    rfl
  have hβ₁ : (ζ ≫ pullback.fst A.projection A.projection) ≫ A.projection =
      coverPt c ≫ P.projection := by
    rw [Category.assoc, hbase, coverPt_proj, hc]
  have hβ₂ : (ζ ≫ pullback.snd A.projection A.projection) ≫ A.projection =
      coverPt c ≫ P.projection := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hβ₁]
  obtain ⟨g', hg', huniq⟩ := A.exists_unique_actPt_sheaf (coverPt c) hβ₂ hβ₁
  have hlift : lift g' (ζ ≫ pullback.snd A.projection A.projection) ≫ A.principalMap = ζ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, A.principalMap_fst]
      exact hg'
    · rw [Category.assoc, A.principalMap_snd, lift_snd]
  refine ⟨Scheme.fppfTopology.yonedaEquiv
    (lift g' (ζ ≫ pullback.snd A.projection A.projection)), ?_, ?_⟩
  · exact (app_eq_iff_comp A.principalMap _ y.1).mpr hlift
  · intro x hx
    set ω := Scheme.fppfTopology.yonedaEquiv.symm x with hω
    have hxω : Scheme.fppfTopology.yonedaEquiv ω = x := by
      rw [hω, Equiv.apply_symm_apply]
    have hωζ : ω ≫ A.principalMap = ζ :=
      (app_eq_iff_comp A.principalMap ω y.1).mp (by rw [hxω]; exact hx)
    have hsnd : ω ≫ snd G'.space.toSheaf A.sheaf =
        ζ ≫ pullback.snd A.projection A.projection := by
      rw [← A.principalMap_snd, ← Category.assoc, hωζ]
    have hfst : actPt (ω ≫ fst G'.space.toSheaf A.sheaf)
        (ζ ≫ pullback.snd A.projection A.projection) =
          ζ ≫ pullback.fst A.projection A.projection := by
      rw [actPt, ← hsnd, TorsorPushout.lift_comp_fst_snd, ← A.principalMap_fst,
        ← Category.assoc, hωζ]
    have hωeq : ω = lift g' (ζ ≫ pullback.snd A.projection A.projection) := by
      rw [← huniq _ hfst, ← hsnd, TorsorPushout.lift_comp_fst_snd]
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

/-- **The pushout of an fppf `G`-torsor along `ρ` is an fppf `G'`-torsor.**  All the
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

end PushoutTorsorRel

end Pushout

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
  rw [fibVal, ← h, TorsorPushout.lift_comp_fst_snd]

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

/-- The image under a relative homomorphism `ρ` of the transition cocycle of the
trivialisation of `P`, taken over the base point of the second lift. -/
noncomputable def relDiv (ρ : RelMonHom G G' T) {W : Scheme.{u}}
    {a b : W ⟶ P.locallyTrivial.coverScheme}
    (hab : a ≫ P.locallyTrivial.cover = b ≫ P.locallyTrivial.cover) :
    fppfYoneda.obj W ⟶ G'.space.toSheaf :=
  ρ.pt (fppfYoneda.map (b ≫ P.locallyTrivial.cover)) (coverDiv hab)

/-- The image of the cocycle at a constant pair is the unit. -/
@[simp]
theorem relDiv_self (ρ : RelMonHom G G' T) {W : Scheme.{u}}
    (a : W ⟶ P.locallyTrivial.coverScheme) :
    relDiv ρ (rfl : a ≫ P.locallyTrivial.cover = a ≫ P.locallyTrivial.cover) = 1 := by
  rw [relDiv, coverDiv_self, RelMonHom.pt_one]

/-- The cocycle rule for the image of the transition cocycle. -/
theorem relDiv_mul (ρ : RelMonHom G G' T) {W : Scheme.{u}}
    {a b c : W ⟶ P.locallyTrivial.coverScheme}
    (hab : a ≫ P.locallyTrivial.cover = b ≫ P.locallyTrivial.cover)
    (hbc : b ≫ P.locallyTrivial.cover = c ≫ P.locallyTrivial.cover) :
    relDiv ρ hab * relDiv ρ hbc = relDiv ρ (hab.trans hbc) := by
  have hb : (fppfYoneda.map (b ≫ P.locallyTrivial.cover) :
      fppfYoneda.obj W ⟶ fppfYoneda.obj T) =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by rw [hbc]
  rw [relDiv, relDiv, relDiv, hb, ← RelMonHom.pt_mul, coverDiv_mul]

/-- The image of the transition cocycle is natural in the test scheme. -/
theorem comp_relDiv (ρ : RelMonHom G G' T) {V W : Scheme.{u}} (u : V ⟶ W)
    {a b : W ⟶ P.locallyTrivial.coverScheme}
    (hab : a ≫ P.locallyTrivial.cover = b ≫ P.locallyTrivial.cover)
    (hab' : (u ≫ a) ≫ P.locallyTrivial.cover = (u ≫ b) ≫ P.locallyTrivial.cover) :
    fppfYoneda.map u ≫ relDiv ρ hab = relDiv ρ hab' := by
  rw [relDiv, relDiv, RelMonHom.comp_pt, comp_coverDiv u hab hab',
    ← CategoryTheory.Functor.map_comp, ← Category.assoc]

variable (P) (ρ : RelMonHom G G' T)

/-- **The descent datum defining the pushout.**  Over the trivialising cover of `P` the pushout
is the trivial `G'`-torsor; the transition maps are the right translations by the image under
`ρ` of the transition cocycle of `P`. -/
noncomputable def descentDatum : DescentDatum P.locallyTrivial.cover (localProj G' P) where
  θ {_ _ b} hab x := fibOf b (fibVal x * relDiv ρ hab)
  θ_restrict := by
    intro V W u a b hab x
    refine fibVal_injective ?_
    rw [fibVal_restrict, fibVal_fibOf, fibVal_fibOf, MonObj.comp_mul, fibVal_restrict,
      comp_relDiv]
  θ_id := by
    intro W a x
    rw [relDiv_self, mul_one, fibOf_fibVal]
  θ_comp := by
    intro W a b c hab hbc x
    rw [fibVal_fibOf, mul_assoc, relDiv_mul]

/-- **The underlying sheaf of the pushout**, glued from the descent datum along the trivialising
cover of `P`. -/
@[reducible] noncomputable def pushoutSheaf : FppfSheaf.{u} :=
  glueSheaf (descentDatum P ρ)

/-- The structure morphism of the pushout to the base. -/
@[reducible] noncomputable def pushoutProj : pushoutSheaf P ρ ⟶ fppfYoneda.obj T :=
  glueSheafBase (descentDatum P ρ)

end Construction

/-! ### The coordinates of a section of the glued sheaf -/

section Coordinates

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {P : FppfTorsor G T}
  {ρ : RelMonHom G G' T}

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
    fibVal ((descentDatum P ρ).θ hab x) = fibVal x * relDiv ρ hab :=
  fibVal_fibOf _ _

/-- **The descent condition, read on coordinates.** -/
theorem coordOf_descent {W : Scheme.{u}} {s : W ⟶ T}
    {ξ : Fibre (localProj G' P) (pullback.snd s P.locallyTrivial.cover)}
    (hξ : IsDescentSection (descentDatum P ρ) ξ) {Z : Scheme.{u}} (c : Z ⟶ W)
    (d₁ d₂ : Z ⟶ P.locallyTrivial.coverScheme) (h₁ : c ≫ s = d₁ ≫ P.locallyTrivial.cover)
    (h₂ : c ≫ s = d₂ ≫ P.locallyTrivial.cover) :
    coordOf ξ c d₂ h₂ = coordOf ξ c d₁ h₁ * relDiv ρ (h₁.symm.trans h₂) := by
  rw [coordOf, ← hξ c d₁ d₂ h₁ h₂, fibVal_theta, coordOf]

/-- **A section of the local model satisfying the coordinate cocycle rule is a descent
section.** -/
theorem isDescentSection_of_coordOf {W : Scheme.{u}} {s : W ⟶ T}
    (ξ : Fibre (localProj G' P) (pullback.snd s P.locallyTrivial.cover))
    (h : ∀ {Z : Scheme.{u}} (c : Z ⟶ W) (d₁ d₂ : Z ⟶ P.locallyTrivial.coverScheme)
      (h₁ : c ≫ s = d₁ ≫ P.locallyTrivial.cover) (h₂ : c ≫ s = d₂ ≫ P.locallyTrivial.cover),
      coordOf ξ c d₂ h₂ = coordOf ξ c d₁ h₁ * relDiv ρ (h₁.symm.trans h₂)) :
    IsDescentSection (descentDatum P ρ) ξ := by
  intro Z c d₁ d₂ h₁ h₂
  refine fibVal_injective ?_
  rw [fibVal_theta]
  exact (h c d₁ d₂ h₁ h₂).symm

/-- Two sections of the glued sheaf with the same base and the same coordinates are equal. -/
theorem glueObj_ext_coordOf {W : Scheme.{u}} {z z' : GlueObj (descentDatum P ρ) W}
    (h1 : z.1 = z'.1)
    (h2 : ∀ {Z : Scheme.{u}} (c : Z ⟶ W) (d : Z ⟶ P.locallyTrivial.coverScheme)
      (h : c ≫ z.1 = d ≫ P.locallyTrivial.cover)
      (h' : c ≫ z'.1 = d ≫ P.locallyTrivial.cover),
      coordOf z.2.1 c d h = coordOf z'.2.1 c d h') : z = z' :=
  glueObj_ext h1 fun c d h h' => congrArg Subtype.val (fibVal_injective (h2 c d h h'))

/-- The coordinates of a restricted section. -/
theorem coordOf_glueMap {V W : Scheme.{u}} (u : V ⟶ W) (z : GlueObj (descentDatum P ρ) W)
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
  (ρ : RelMonHom G G' T)

/-- The section of the local model obtained by translating the coordinate of a section of the
glued sheaf by a point of `G'`. -/
noncomputable def smulFibre {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : GlueObj (descentDatum P ρ) W) :
    Fibre (localProj G' P) (pullback.snd z.1 P.locallyTrivial.cover) :=
  fibOf (pullback.snd z.1 P.locallyTrivial.cover)
    ((fppfYoneda.map (pullback.fst z.1 P.locallyTrivial.cover) ≫ g') * fibVal z.2.1)

variable {P ρ}

/-- The coordinates of the translated section. -/
theorem coordOf_smulFibre {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : GlueObj (descentDatum P ρ) W) {Z : Scheme.{u}} (c : Z ⟶ W)
    (d : Z ⟶ P.locallyTrivial.coverScheme) (h : c ≫ z.1 = d ≫ P.locallyTrivial.cover) :
    coordOf (smulFibre P ρ g' z) c d h = (fppfYoneda.map c ≫ g') * coordOf z.2.1 c d h := by
  rw [coordOf_eq, smulFibre, fibVal_fibOf, MonObj.comp_mul, coordOf_eq, ← Category.assoc,
    ← Functor.map_comp, pullback.lift_fst]

/-- The translated section is again a descent section. -/
theorem isDescentSection_smulFibre {W : Scheme.{u}}
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (z : GlueObj (descentDatum P ρ) W) :
    IsDescentSection (descentDatum P ρ) (smulFibre P ρ g' z) := by
  refine isDescentSection_of_coordOf _ fun c d₁ d₂ h₁ h₂ => ?_
  rw [coordOf_smulFibre, coordOf_smulFibre, coordOf_descent z.2.2 c d₁ d₂ h₁ h₂, mul_assoc]

variable (P ρ)

/-- The translation of a section of the glued sheaf by a point of `G'`. -/
noncomputable def smulGlue {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : GlueObj (descentDatum P ρ) W) : GlueObj (descentDatum P ρ) W :=
  ⟨z.1, ⟨smulFibre P ρ g' z, isDescentSection_smulFibre g' z⟩⟩

variable {P ρ}

/-- Translation does not change the base of a section. -/
@[simp]
theorem smulGlue_fst {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : GlueObj (descentDatum P ρ) W) : (smulGlue P ρ g' z).1 = z.1 :=
  rfl

/-- The coordinates of a translated section of the glued sheaf. -/
theorem coordOf_smulGlue {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : GlueObj (descentDatum P ρ) W) {Z : Scheme.{u}} (c : Z ⟶ W)
    (d : Z ⟶ P.locallyTrivial.coverScheme) (h : c ≫ z.1 = d ≫ P.locallyTrivial.cover) :
    coordOf (smulGlue P ρ g' z).2.1 c d h = (fppfYoneda.map c ≫ g') * coordOf z.2.1 c d h :=
  coordOf_smulFibre g' z c d h

/-- Translation by the unit is the identity. -/
theorem smulGlue_one {W : Scheme.{u}} (z : GlueObj (descentDatum P ρ) W) :
    smulGlue P ρ (1 : fppfYoneda.obj W ⟶ G'.space.toSheaf) z = z := by
  refine glueObj_ext_coordOf rfl fun c d h h' => ?_
  rw [coordOf_smulGlue (1 : fppfYoneda.obj W ⟶ G'.space.toSheaf) z c d h', MonObj.comp_one,
    one_mul]

/-- Translation is compatible with multiplication. -/
theorem smulGlue_mul {W : Scheme.{u}} (a b : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : GlueObj (descentDatum P ρ) W) :
    smulGlue P ρ (a * b) z = smulGlue P ρ a (smulGlue P ρ b z) := by
  refine glueObj_ext_coordOf rfl fun c d h h' => ?_
  rw [coordOf_smulGlue (a * b) z c d h, coordOf_smulGlue a (smulGlue P ρ b z) c d h,
    coordOf_smulGlue b z c d h, MonObj.comp_mul, mul_assoc]

/-- Translation is compatible with restriction. -/
theorem glueMap_smulGlue {V W : Scheme.{u}} (u : V ⟶ W)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (z : GlueObj (descentDatum P ρ) W) :
    glueMap u (smulGlue P ρ g' z) =
      smulGlue P ρ (fppfYoneda.map u ≫ g') (glueMap u z) := by
  refine glueObj_ext_coordOf rfl fun c d h h' => ?_
  have hz : (c ≫ u) ≫ z.1 = d ≫ P.locallyTrivial.cover := h
  rw [coordOf_glueMap u (smulGlue P ρ g' z) c d h hz, coordOf_smulGlue g' z (c ≫ u) d hz,
    coordOf_smulGlue (fppfYoneda.map u ≫ g') (glueMap u z) c d h',
    coordOf_glueMap u z c d h' hz, ← Category.assoc, ← Functor.map_comp]

end Action

/-! ### The pushout sheaf as a `G'`-sheaf -/

section SheafAction

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} (P : FppfTorsor G T)
  (ρ : RelMonHom G G' T)

/-- The section of the glued sheaf underlying a point of the pushout sheaf. -/
noncomputable def glueSec {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) :
    GlueObj (descentDatum P ρ) W :=
  Scheme.fppfTopology.yonedaEquiv z

/-- The point of the pushout sheaf attached to a section of the glued sheaf. -/
noncomputable def ptOfGlue {W : Scheme.{u}} (z : GlueObj (descentDatum P ρ) W) :
    fppfYoneda.obj W ⟶ pushoutSheaf P ρ :=
  Scheme.fppfTopology.yonedaEquiv.symm z

variable {P ρ}

/-- The two descriptions of a point of the pushout sheaf are inverse to each other. -/
@[simp]
theorem glueSec_ptOfGlue {W : Scheme.{u}} (z : GlueObj (descentDatum P ρ) W) :
    glueSec P ρ (ptOfGlue P ρ z) = z :=
  Equiv.apply_symm_apply _ _

/-- The two descriptions of a point of the pushout sheaf are inverse to each other. -/
@[simp]
theorem ptOfGlue_glueSec {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) :
    ptOfGlue P ρ (glueSec P ρ z) = z :=
  Equiv.symm_apply_apply _ _

/-- Points of the pushout sheaf are determined by their sections. -/
theorem glueSec_injective {W : Scheme.{u}} {z z' : fppfYoneda.obj W ⟶ pushoutSheaf P ρ}
    (h : glueSec P ρ z = glueSec P ρ z') : z = z' := by
  rw [← ptOfGlue_glueSec z, ← ptOfGlue_glueSec z', h]

/-- Restriction of a point of the pushout sheaf is restriction of its section. -/
theorem glueSec_comp {V W : Scheme.{u}} (u : V ⟶ W)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) :
    glueSec P ρ (fppfYoneda.map u ≫ z) = glueMap u (glueSec P ρ z) :=
  (Scheme.fppfTopology.yonedaEquiv_naturality z u).symm

/-- Restriction of a point attached to a section. -/
theorem comp_ptOfGlue {V W : Scheme.{u}} (u : V ⟶ W) (z : GlueObj (descentDatum P ρ) W) :
    fppfYoneda.map u ≫ ptOfGlue P ρ z = ptOfGlue P ρ (glueMap u z) := by
  refine glueSec_injective ?_
  rw [glueSec_comp, glueSec_ptOfGlue, glueSec_ptOfGlue]

/-- The base of the section of a point of the pushout sheaf. -/
theorem glueSec_fst {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) :
    (glueSec P ρ z).1 = Scheme.fppfTopology.yonedaEquiv (z ≫ pushoutProj P ρ) :=
  rfl

variable (P ρ)

/-- The translation of a point of the pushout sheaf by a point of `G'`. -/
noncomputable def actGluePt {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) : fppfYoneda.obj W ⟶ pushoutSheaf P ρ :=
  ptOfGlue P ρ (smulGlue P ρ g' (glueSec P ρ z))

variable {P ρ}

/-- The section underlying a translated point. -/
@[simp]
theorem glueSec_actGluePt {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) :
    glueSec P ρ (actGluePt P ρ g' z) = smulGlue P ρ g' (glueSec P ρ z) := by
  rw [actGluePt, glueSec_ptOfGlue]

/-- Translation of points is natural. -/
theorem comp_actGluePt {V W : Scheme.{u}} (u : V ⟶ W)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) :
    fppfYoneda.map u ≫ actGluePt P ρ g' z =
      actGluePt P ρ (fppfYoneda.map u ≫ g') (fppfYoneda.map u ≫ z) := by
  refine glueSec_injective ?_
  rw [glueSec_comp, glueSec_actGluePt, glueSec_actGluePt, glueMap_smulGlue, glueSec_comp]

/-- Translation by the unit does nothing. -/
theorem actGluePt_one {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) :
    actGluePt P ρ (1 : fppfYoneda.obj W ⟶ G'.space.toSheaf) z = z := by
  refine glueSec_injective ?_
  rw [glueSec_actGluePt, smulGlue_one]

/-- Translation is compatible with multiplication. -/
theorem actGluePt_mul {W : Scheme.{u}} (a b : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) :
    actGluePt P ρ (a * b) z = actGluePt P ρ a (actGluePt P ρ b z) := by
  refine glueSec_injective ?_
  rw [glueSec_actGluePt, glueSec_actGluePt, glueSec_actGluePt, smulGlue_mul]

/-- Translation does not change the image in the base. -/
theorem actGluePt_proj {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) :
    actGluePt P ρ g' z ≫ pushoutProj P ρ = z ≫ pushoutProj P ρ := by
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [← glueSec_fst, ← glueSec_fst, glueSec_actGluePt, smulGlue_fst]

variable (P ρ)

/-- The naturality of the translation formula. -/
theorem actGluePt_natural : ∀ {V W : Scheme.{u}} (u : V ⟶ W)
    (ω : fppfYoneda.obj W ⟶ G'.space.toSheaf ⊗ pushoutSheaf P ρ),
    fppfYoneda.map u ≫ actGluePt P ρ (ω ≫ fst _ _) (ω ≫ snd _ _) =
      actGluePt P ρ ((fppfYoneda.map u ≫ ω) ≫ fst _ _)
        ((fppfYoneda.map u ≫ ω) ≫ snd _ _) :=
  fun u ω => by rw [comp_actGluePt, Category.assoc, Category.assoc]

/-- The action of `G'` on the pushout sheaf. -/
noncomputable def pushoutSmul : G'.space.toSheaf ⊗ pushoutSheaf P ρ ⟶ pushoutSheaf P ρ :=
  ofPoints (fun ω => actGluePt P ρ (ω ≫ fst _ _) (ω ≫ snd _ _)) (actGluePt_natural P ρ)

variable {P ρ}

/-- The action of `G'` on the pushout sheaf, computed on points. -/
@[simp]
theorem lift_comp_pushoutSmul {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) :
    lift g' z ≫ pushoutSmul P ρ = actGluePt P ρ g' z := by
  rw [pushoutSmul]
  refine (comp_ofPoints _ (actGluePt_natural P ρ) (lift g' z)).trans ?_
  rw [lift_fst, lift_snd]

variable (P ρ)

/-- **The pushout sheaf is a `G'`-sheaf.** -/
@[instance_reducible]
noncomputable def pushoutAction : ModObj G'.space.toSheaf (pushoutSheaf P ρ) :=
  modObjOfPoints (pushoutSmul P ρ)
    (fun z => by rw [lift_comp_pushoutSmul, actGluePt_one])
    (fun a b z => by rw [lift_comp_pushoutSmul, lift_comp_pushoutSmul, lift_comp_pushoutSmul,
      actGluePt_mul])

attribute [instance] pushoutAction

/-- The action of the `G'`-sheaf structure of the pushout is the glued translation. -/
@[simp]
theorem pushoutAction_smul :
    ModObj.smul (M := G'.space.toSheaf) (X := pushoutSheaf P ρ) = pushoutSmul P ρ :=
  rfl

/-- **The action of `G'` on the pushout sheaf is fibrewise over the base.** -/
theorem pushoutSmul_proj :
    pushoutSmul P ρ ≫ pushoutProj P ρ =
      snd G'.space.toSheaf (pushoutSheaf P ρ) ≫ pushoutProj P ρ := by
  refine hom_ext_points fun W ω => ?_
  rw [← Category.assoc, ← Category.assoc, ← TorsorPushout.lift_comp_fst_snd ω,
    lift_comp_pushoutSmul, lift_snd, actGluePt_proj]

end SheafAction

/-! ### Local trivialisation of the pushout sheaf -/

section CoordinatesAux

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {P : FppfTorsor G T}
  {ρ : RelMonHom G G' T}

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
theorem coordOf_glueObj_congr {W : Scheme.{u}} {z z' : GlueObj (descentDatum P ρ) W}
    (hzz : z = z') {Z : Scheme.{u}} (c : Z ⟶ W) (d : Z ⟶ P.locallyTrivial.coverScheme)
    (h : c ≫ z.1 = d ≫ P.locallyTrivial.cover) (h' : c ≫ z'.1 = d ≫ P.locallyTrivial.cover) :
    coordOf z.2.1 c d h = coordOf z'.2.1 c d h' := by
  subst hzz
  rfl

end CoordinatesAux

section LocalTrivialisation

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} (P : FppfTorsor G T)
  (ρ : RelMonHom G G' T)

/-- The coordinate of a point of the pushout sheaf at a lift of its base to the cover. -/
noncomputable def coordAt {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    fppfYoneda.obj W ⟶ G'.space.toSheaf :=
  coordOf (glueSec P ρ z).2.1 (𝟙 W) c (by
    rw [Category.id_comp, glueSec_fst, hz, GrothendieckTopology.yonedaEquiv_yoneda_map])

variable {P ρ}

/-- The base of the section of a point of the pushout sheaf with a chosen lift. -/
theorem glueSec_fst_of_lift {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    (glueSec P ρ z).1 = c ≫ P.locallyTrivial.cover := by
  rw [glueSec_fst, hz, GrothendieckTopology.yonedaEquiv_yoneda_map]

/-- The coordinate is the `G'`-coordinate of the fibre of the glued sheaf. -/
theorem coordAt_eq_fibVal {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    coordAt P ρ z c hz =
      fibVal (glueFibreEquiv (descentDatum P ρ) c ⟨glueSec P ρ z, glueSec_fst_of_lift z c hz⟩) :=
  rfl

/-- The coordinate is natural in the test scheme. -/
theorem comp_coordAt {V W : Scheme.{u}} (u : V ⟶ W) (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : (fppfYoneda.map u ≫ z) ≫ pushoutProj P ρ =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover)) :
    fppfYoneda.map u ≫ coordAt P ρ z c hz = coordAt P ρ (fppfYoneda.map u ≫ z) (u ≫ c) hz' := by
  have hb : (glueSec P ρ z).1 = c ≫ P.locallyTrivial.cover := glueSec_fst_of_lift z c hz
  have hu : u ≫ (glueSec P ρ z).1 = (u ≫ c) ≫ P.locallyTrivial.cover := by
    rw [hb, Category.assoc]
  have h1 : (u ≫ 𝟙 W) ≫ (glueSec P ρ z).1 = (u ≫ c) ≫ P.locallyTrivial.cover := by
    rw [Category.comp_id]; exact hu
  have h2 : (𝟙 V ≫ u) ≫ (glueSec P ρ z).1 = (u ≫ c) ≫ P.locallyTrivial.cover := by
    rw [Category.id_comp]; exact hu
  have h0 : 𝟙 V ≫ (glueMap u (glueSec P ρ z)).1 = (u ≫ c) ≫ P.locallyTrivial.cover := by
    rw [Category.id_comp, glueMap_fst]; exact hu
  rw [coordAt, coordAt]
  calc fppfYoneda.map u ≫ coordOf (glueSec P ρ z).2.1 (𝟙 W) c _
      = coordOf (glueSec P ρ z).2.1 (u ≫ 𝟙 W) (u ≫ c) h1 := coordOf_comp _ u (𝟙 W) c _ h1
    _ = coordOf (glueSec P ρ z).2.1 (𝟙 V ≫ u) (u ≫ c) h2 :=
        coordOf_congr _ (by rw [Category.comp_id, Category.id_comp]) rfl h1 h2
    _ = coordOf (glueMap u (glueSec P ρ z)).2.1 (𝟙 V) (u ≫ c) h0 :=
        (coordOf_glueMap u (glueSec P ρ z) (𝟙 V) (u ≫ c) h0 h2).symm
    _ = coordOf (glueSec P ρ (fppfYoneda.map u ≫ z)).2.1 (𝟙 V) (u ≫ c) _ :=
        coordOf_glueObj_congr (glueSec_comp u z).symm (𝟙 V) (u ≫ c) h0 _

/-- **Independence of the chosen lift**: two lifts of the base give coordinates differing by the
image under `ρ` of the transition cocycle. -/
theorem coordAt_lift_congr {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    {c c' : W ⟶ P.locallyTrivial.coverScheme}
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : z ≫ pushoutProj P ρ = fppfYoneda.map (c' ≫ P.locallyTrivial.cover))
    (hcc : c ≫ P.locallyTrivial.cover = c' ≫ P.locallyTrivial.cover) :
    coordAt P ρ z c' hz' = coordAt P ρ z c hz * relDiv ρ hcc := by
  rw [coordAt, coordAt, coordOf_descent (glueSec P ρ z).2.2 (𝟙 W) c c']

variable (P ρ)

/-- The point of the pushout sheaf with prescribed base lift and coordinate. -/
noncomputable def ptOfCoord {W : Scheme.{u}} (c : W ⟶ P.locallyTrivial.coverScheme)
    (g : fppfYoneda.obj W ⟶ G'.space.toSheaf) : fppfYoneda.obj W ⟶ pushoutSheaf P ρ :=
  ptOfGlue P ρ ((glueFibreEquiv (descentDatum P ρ) c).symm (fibOf c g)).1

variable {P ρ}

/-- The section of a point with prescribed coordinate. -/
theorem glueSec_ptOfCoord {W : Scheme.{u}} (c : W ⟶ P.locallyTrivial.coverScheme)
    (g : fppfYoneda.obj W ⟶ G'.space.toSheaf) :
    glueSec P ρ (ptOfCoord P ρ c g) =
      ((glueFibreEquiv (descentDatum P ρ) c).symm (fibOf c g)).1 := by
  rw [ptOfCoord, glueSec_ptOfGlue]

/-- The point with prescribed coordinate lies above the expected base point. -/
theorem ptOfCoord_proj {W : Scheme.{u}} (c : W ⟶ P.locallyTrivial.coverScheme)
    (g : fppfYoneda.obj W ⟶ G'.space.toSheaf) :
    ptOfCoord P ρ c g ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [← glueSec_fst, glueSec_ptOfCoord, GrothendieckTopology.yonedaEquiv_yoneda_map]
  exact ((glueFibreEquiv (descentDatum P ρ) c).symm (fibOf c g)).2

/-- **The coordinate of the point with prescribed coordinate.** -/
@[simp]
theorem coordAt_ptOfCoord {W : Scheme.{u}} (c : W ⟶ P.locallyTrivial.coverScheme)
    (g : fppfYoneda.obj W ⟶ G'.space.toSheaf) :
    coordAt P ρ (ptOfCoord P ρ c g) c (ptOfCoord_proj c g) = g := by
  rw [coordAt_eq_fibVal]
  have hsub : (⟨glueSec P ρ (ptOfCoord P ρ c g),
      glueSec_fst_of_lift (ptOfCoord P ρ c g) c (ptOfCoord_proj c g)⟩ :
        {w : GlueObj (descentDatum P ρ) W // w.1 = c ≫ P.locallyTrivial.cover}) =
      (glueFibreEquiv (descentDatum P ρ) c).symm (fibOf c g) :=
    Subtype.ext (glueSec_ptOfCoord c g)
  rw [hsub, Equiv.apply_symm_apply, fibVal_fibOf]

/-- **A point of the pushout sheaf is determined by its coordinate at a lift.** -/
@[simp]
theorem ptOfCoord_coordAt {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    ptOfCoord P ρ c (coordAt P ρ z c hz) = z := by
  rw [ptOfCoord, coordAt_eq_fibVal, fibOf_fibVal, Equiv.symm_apply_apply, ptOfGlue_glueSec]

/-- Two points of the pushout sheaf above the same lift with the same coordinate are equal. -/
theorem coordAt_injective {W : Scheme.{u}} {z z' : fppfYoneda.obj W ⟶ pushoutSheaf P ρ}
    {c : W ⟶ P.locallyTrivial.coverScheme}
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : z' ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h : coordAt P ρ z c hz = coordAt P ρ z' c hz') : z = z' := by
  rw [← ptOfCoord_coordAt z c hz, ← ptOfCoord_coordAt z' c hz', h]

/-- Translating a point multiplies its coordinate. -/
theorem coordAt_actGluePt {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : actGluePt P ρ g' z ≫ pushoutProj P ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    coordAt P ρ (actGluePt P ρ g' z) c hz' = g' * coordAt P ρ z c hz := by
  have h0 : 𝟙 W ≫ (smulGlue P ρ g' (glueSec P ρ z)).1 = c ≫ P.locallyTrivial.cover := by
    rw [smulGlue_fst, Category.id_comp]
    exact glueSec_fst_of_lift z c hz
  have hpf : 𝟙 W ≫ (glueSec P ρ z).1 = c ≫ P.locallyTrivial.cover := by
    rw [Category.id_comp]
    exact glueSec_fst_of_lift z c hz
  rw [coordAt, coordAt]
  refine (coordOf_glueObj_congr (glueSec_actGluePt g' z) (𝟙 W) c _ h0).trans ?_
  refine (coordOf_smulGlue g' (glueSec P ρ z) (𝟙 W) c hpf).trans ?_
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

end LocalTrivialisation

/-! ### The local evaluation pairing -/

section EvLocal

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} (P : FppfTorsor G T)
  (ρ : RelMonHom G G' T)

/-- The value at a point `p` of `P` of the equivariant map given by a point `z` of the pushout
sheaf, computed through a lift `c` of the base to the trivialising cover.  The formula is
`z (p) = z (L c) * ρ (p / L c)⁻¹`, where `L c` is the tautological point of `P` at `c`. -/
noncomputable def evLocal {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (p : fppfYoneda.obj W ⟶ P.P) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    fppfYoneda.obj W ⟶ G'.space.toSheaf :=
  coordAt P ρ z c hz *
    (ρ.pt (p ≫ P.projection) (divPt P p (coverPt c) (by rw [hp, coverPt_proj])))⁻¹

variable {P ρ}

/-- Two lifts of the same base point are comparable. -/
theorem cover_lift_eq {W : Scheme.{u}} {c c' : W ⟶ P.locallyTrivial.coverScheme}
    (h : (fppfYoneda.map (c ≫ P.locallyTrivial.cover) :
      fppfYoneda.obj W ⟶ fppfYoneda.obj T) = fppfYoneda.map (c' ≫ P.locallyTrivial.cover)) :
    c ≫ P.locallyTrivial.cover = c' ≫ P.locallyTrivial.cover := by
  have h2 := congrArg Scheme.fppfTopology.yonedaEquiv h
  rwa [GrothendieckTopology.yonedaEquiv_yoneda_map,
    GrothendieckTopology.yonedaEquiv_yoneda_map] at h2

/-- **The local evaluation does not depend on the chosen lift.** -/
theorem evLocal_lift_congr {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (p : fppfYoneda.obj W ⟶ P.P) {c c' : W ⟶ P.locallyTrivial.coverScheme}
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : z ≫ pushoutProj P ρ = fppfYoneda.map (c' ≫ P.locallyTrivial.cover))
    (hp' : p ≫ P.projection = fppfYoneda.map (c' ≫ P.locallyTrivial.cover)) :
    evLocal P ρ z p c' hz' hp' = evLocal P ρ z p c hz hp := by
  have hcc : c ≫ P.locallyTrivial.cover = c' ≫ P.locallyTrivial.cover :=
    cover_lift_eq (hz.symm.trans hz')
  have hd : divPt P p (coverPt c') (by rw [hp', coverPt_proj]) =
      divPt P p (coverPt c) (by rw [hp, coverPt_proj]) * coverDiv hcc :=
    (divPt_mul _ _ _ _ _).symm
  have hbase : ρ.pt (p ≫ P.projection) (coverDiv hcc) = relDiv ρ hcc :=
    ρ.pt_congr hp' rfl
  rw [evLocal, evLocal, coordAt_lift_congr z hz hz' hcc, hd, RelMonHom.pt_mul, hbase]
  group

/-- The local evaluation is natural in the test scheme. -/
theorem comp_evLocal {V W : Scheme.{u}} (u : V ⟶ W) (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (p : fppfYoneda.obj W ⟶ P.P) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : (fppfYoneda.map u ≫ z) ≫ pushoutProj P ρ =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover))
    (hp' : (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover)) :
    fppfYoneda.map u ≫ evLocal P ρ z p c hz hp =
      evLocal P ρ (fppfYoneda.map u ≫ z) (fppfYoneda.map u ≫ p) (u ≫ c) hz' hp' := by
  have hd : fppfYoneda.map u ≫ divPt P p (coverPt c) (by rw [hp, coverPt_proj]) =
      divPt P (fppfYoneda.map u ≫ p) (coverPt (u ≫ c)) (by rw [hp', coverPt_proj]) := by
    refine eq_divPt _ _ _ _ ?_
    rw [← comp_coverPt, ← comp_actPt, actPt_divPt]
  have hassoc : fppfYoneda.map u ≫ p ≫ P.projection =
      (fppfYoneda.map u ≫ p) ≫ P.projection := (Category.assoc _ _ _).symm
  rw [evLocal, evLocal, MonObj.comp_mul, comp_coordAt u z c hz hz', GrpObj.comp_inv,
    RelMonHom.comp_pt, hassoc, hd]

/-- The local evaluation is equivariant for the action of `G'` on the pushout sheaf. -/
theorem evLocal_actGluePt {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) (p : fppfYoneda.obj W ⟶ P.P)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : actGluePt P ρ g' z ≫ pushoutProj P ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evLocal P ρ (actGluePt P ρ g' z) p c hz' hp = g' * evLocal P ρ z p c hz hp := by
  rw [evLocal, evLocal, coordAt_actGluePt g' z c hz hz', mul_assoc]

/-- The local evaluation is equivariant for the action of `G` on `P`, through `ρ`. -/
theorem evLocal_actPt {W : Scheme.{u}} (g : fppfYoneda.obj W ⟶ G.space.toSheaf)
    (z : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) (p : fppfYoneda.obj W ⟶ P.P)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp' : actPt g p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evLocal P ρ z (actPt g p) c hz hp' =
      evLocal P ρ z p c hz hp * (ρ.pt (p ≫ P.projection) g)⁻¹ := by
  have hd : divPt P (actPt g p) (coverPt c) (by rw [hp', coverPt_proj]) =
      g * divPt P p (coverPt c) (by rw [hp, coverPt_proj]) :=
    divPt_actPt_left _ _ _ _ _
  have hb : ρ.pt (actPt g p ≫ P.projection)
        (g * divPt P p (coverPt c) (by rw [hp, coverPt_proj])) =
      ρ.pt (p ≫ P.projection) (g * divPt P p (coverPt c) (by rw [hp, coverPt_proj])) :=
    ρ.pt_congr (by rw [actPt_proj]) rfl
  rw [evLocal, evLocal, hd, hb, RelMonHom.pt_mul]
  group

/-- **The local evaluation is surjective on the fibre**: the point of the pushout sheaf with the
prescribed value at `p`. -/
theorem evLocal_ptOfCoord {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (c : W ⟶ P.locallyTrivial.coverScheme) (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evLocal P ρ (ptOfCoord P ρ c
        (g' * ρ.pt (p ≫ P.projection)
          (divPt P p (coverPt c) (by rw [hp, coverPt_proj])))) p c
      (ptOfCoord_proj c _) hp = g' := by
  rw [evLocal, coordAt_ptOfCoord, mul_inv_cancel_right]

/-- **The local evaluation is injective on the fibre.** -/
theorem evLocal_injective {W : Scheme.{u}} {z z' : fppfYoneda.obj W ⟶ pushoutSheaf P ρ}
    (p : fppfYoneda.obj W ⟶ P.P) {c : W ⟶ P.locallyTrivial.coverScheme}
    (hz : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hz' : z' ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h : evLocal P ρ z p c hz hp = evLocal P ρ z' p c hz' hp) : z = z' := by
  refine coordAt_injective hz hz' ?_
  rw [evLocal, evLocal] at h
  exact mul_right_cancel h

end EvLocal

/-! ### The global evaluation pairing -/

section Ev

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} (P : FppfTorsor G T)
  (ρ : RelMonHom G G' T)

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

variable {P ρ}

/-- The local evaluation only depends on the two points. -/
theorem evLocal_congr {W : Scheme.{u}} {z z' : fppfYoneda.obj W ⟶ pushoutSheaf P ρ}
    {p p' : fppfYoneda.obj W ⟶ P.P} (hz : z = z') (hp : p = p')
    {c : W ⟶ P.locallyTrivial.coverScheme}
    (h1 : z ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h2 : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h3 : z' ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h4 : p' ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evLocal P ρ z p c h1 h2 = evLocal P ρ z' p' c h3 h4 := by
  subst hz
  subst hp
  rfl

variable (P ρ)

/-- The fibre product of the pushout sheaf and of `P` over the base.

It is deliberately *not* reducible: unfolding it to the pullback of sheaves makes the elaborator
evaluate the limit construction on sections, which does not terminate in practice.  All the
statements below go through the wrappers `evFst`, `evSnd`, `evLift`. -/
noncomputable def evSource : FppfSheaf.{u} :=
  pullback (pushoutProj P ρ) P.projection

/-- The projection of the fibre product to the pushout sheaf. -/
noncomputable def evFst : evSource P ρ ⟶ pushoutSheaf P ρ :=
  pullback.fst (pushoutProj P ρ) P.projection

/-- The projection of the fibre product to the torsor. -/
noncomputable def evSnd : evSource P ρ ⟶ P.P :=
  pullback.snd (pushoutProj P ρ) P.projection

/-- The structure morphism of the fibre product to the base. -/
noncomputable def evBase : evSource P ρ ⟶ fppfYoneda.obj T :=
  evFst P ρ ≫ pushoutProj P ρ

/-- The two projections of the fibre product agree over the base. -/
theorem evSource_condition :
    evFst P ρ ≫ pushoutProj P ρ = evSnd P ρ ≫ P.projection :=
  pullback.condition

/-- Points of the fibre product are determined by their two components. -/
theorem evSource_hom_ext {Z : FppfSheaf.{u}} {a b : Z ⟶ evSource P ρ}
    (h1 : a ≫ evFst P ρ = b ≫ evFst P ρ) (h2 : a ≫ evSnd P ρ = b ≫ evSnd P ρ) : a = b :=
  pullback.hom_ext h1 h2

/-- The point of the fibre product attached to a pair of points over the same base point. -/
noncomputable def evLift {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P ρ = p ≫ P.projection) :
    fppfYoneda.obj W ⟶ evSource P ρ :=
  pullback.lift α p h

variable {P ρ}

/-- The first component of `evLift`. -/
@[simp]
theorem evLift_fst {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P ρ = p ≫ P.projection) :
    evLift P ρ α p h ≫ evFst P ρ = α :=
  pullback.lift_fst _ _ _

/-- The second component of `evLift`. -/
@[simp]
theorem evLift_snd {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P ρ = p ≫ P.projection) :
    evLift P ρ α p h ≫ evSnd P ρ = p :=
  pullback.lift_snd _ _ _

/-- The base point of `evLift`. -/
theorem evLift_base {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P ρ = p ≫ P.projection) :
    evLift P ρ α p h ≫ evBase P ρ = α ≫ pushoutProj P ρ := by
  rw [evBase, ← Category.assoc, evLift_fst]

/-- The first component of a point of the fibre product lies over its base point. -/
theorem evSource_fst_proj {W : Scheme.{u}} (σ : fppfYoneda.obj W ⟶ evSource P ρ)
    {c : W ⟶ P.locallyTrivial.coverScheme}
    (hσ : σ ≫ evBase P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    (σ ≫ evFst P ρ) ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
  rw [Category.assoc, ← evBase]
  exact hσ

/-- The second component of a point of the fibre product lies over its base point. -/
theorem evSource_snd_proj {W : Scheme.{u}} (σ : fppfYoneda.obj W ⟶ evSource P ρ)
    {c : W ⟶ P.locallyTrivial.coverScheme}
    (hσ : σ ≫ evBase P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    (σ ≫ evSnd P ρ) ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
  rw [Category.assoc, ← evSource_condition, ← evBase]
  exact hσ

variable (P ρ)

/-- The local evaluation of a point of the fibre product, through a lift of its base. -/
noncomputable def evSourceLocal {W : Scheme.{u}} (σ : fppfYoneda.obj W ⟶ evSource P ρ)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hσ : σ ≫ evBase P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    fppfYoneda.obj W ⟶ G'.space.toSheaf :=
  evLocal P ρ (σ ≫ evFst P ρ) (σ ≫ evSnd P ρ) c (evSource_fst_proj σ hσ)
    (evSource_snd_proj σ hσ)

variable {P ρ}

/-- The local evaluation on the fibre product only depends on the point. -/
theorem evSourceLocal_congr_pt {W : Scheme.{u}} {σ σ' : fppfYoneda.obj W ⟶ evSource P ρ}
    (hσσ : σ = σ') {c : W ⟶ P.locallyTrivial.coverScheme}
    (h : σ ≫ evBase P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (h' : σ' ≫ evBase P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evSourceLocal P ρ σ c h = evSourceLocal P ρ σ' c h' := by
  subst hσσ
  rfl

/-- The local evaluation on the fibre product does not depend on the lift. -/
theorem evSourceLocal_congr {W : Scheme.{u}} (σ : fppfYoneda.obj W ⟶ evSource P ρ)
    {c c' : W ⟶ P.locallyTrivial.coverScheme}
    (hσ : σ ≫ evBase P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hσ' : σ ≫ evBase P ρ = fppfYoneda.map (c' ≫ P.locallyTrivial.cover)) :
    evSourceLocal P ρ σ c' hσ' = evSourceLocal P ρ σ c hσ :=
  evLocal_lift_congr _ _ _ _ _ _

/-- The local evaluation on the fibre product is natural. -/
theorem comp_evSourceLocal {V W : Scheme.{u}} (u : V ⟶ W)
    (σ : fppfYoneda.obj W ⟶ evSource P ρ) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hσ : σ ≫ evBase P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hσ' : (fppfYoneda.map u ≫ σ) ≫ evBase P ρ =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover)) :
    fppfYoneda.map u ≫ evSourceLocal P ρ σ c hσ =
      evSourceLocal P ρ (fppfYoneda.map u ≫ σ) (u ≫ c) hσ' := by
  have h1 : (fppfYoneda.map u ≫ σ ≫ evFst P ρ) ≫ pushoutProj P ρ =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover) := by
    rw [← Category.assoc]
    exact evSource_fst_proj (fppfYoneda.map u ≫ σ) hσ'
  have h2 : (fppfYoneda.map u ≫ σ ≫ evSnd P ρ) ≫ P.projection =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover) := by
    rw [← Category.assoc]
    exact evSource_snd_proj (fppfYoneda.map u ≫ σ) hσ'
  rw [evSourceLocal, evSourceLocal]
  refine (comp_evLocal u _ _ c _ _ h1 h2).trans ?_
  exact evLocal_congr (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm h1 h2 _ _

variable (P ρ)

/-- The evaluation pairing, defined on the sections of the fibre product whose base lies in the
covering sieve of the trivialising cover of `P`. -/
noncomputable def evPartial : PartialHom (evBase P ρ) G'.space.toSheaf (coverSieve P) where
  app {W} x :=
    Scheme.fppfTopology.yonedaEquiv (evSourceLocal P ρ
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
    have hA : (fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1) ≫ evBase P ρ =
        fppfYoneda.map ((u ≫ (exists_factor_of_coverSieve x.2).choose) ≫
          P.locallyTrivial.cover) := by
      rw [Category.assoc, GrothendieckTopology.yonedaEquiv_symm_naturality_right,
        yonedaEquiv_symm_map, ← CategoryTheory.Functor.map_comp]
      refine congrArg _ ?_
      rw [Category.assoc, (exists_factor_of_coverSieve x.2).choose_spec]
      rfl
    have hB : (fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1) ≫ evBase P ρ =
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
noncomputable def evMap : evSource P ρ ⟶ G'.space.toSheaf :=
  (evPartial P ρ).glue (coverSieve_mem P)

variable {P ρ}

/-- The evaluation pairing is computed by the local formula. -/
theorem comp_evMap {W : Scheme.{u}} (σ : fppfYoneda.obj W ⟶ evSource P ρ)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hσ : σ ≫ evBase P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    σ ≫ evMap P ρ = evSourceLocal P ρ σ c hσ := by
  have hbe : GromovWitten.SheafGluing.base (evBase P ρ)
      (Scheme.fppfTopology.yonedaEquiv σ) = c ≫ P.locallyTrivial.cover := by
    rw [SheafGluing.base_yonedaEquiv, hσ, GrothendieckTopology.yonedaEquiv_yoneda_map]
  have hb : (coverSieve P).arrows
      (GromovWitten.SheafGluing.base (evBase P ρ) (Scheme.fppfTopology.yonedaEquiv σ)) := by
    rw [hbe]
    exact ⟨_, c, P.locallyTrivial.cover, Presieve.singleton.mk, rfl⟩
  have key := (evPartial P ρ).glue_app (coverSieve_mem P)
    (⟨Scheme.fppfTopology.yonedaEquiv σ, hb⟩ : SectionsOver (evBase P ρ) (coverSieve P) W)
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [evMap, GrothendieckTopology.yonedaEquiv_comp, key]
  refine congrArg Scheme.fppfTopology.yonedaEquiv ?_
  have hpt : Scheme.fppfTopology.yonedaEquiv.symm
      ((⟨Scheme.fppfTopology.yonedaEquiv σ, hb⟩ :
        SectionsOver (evBase P ρ) (coverSieve P) W).1) = σ :=
    Equiv.symm_apply_apply _ _
  have hA : σ ≫ evBase P ρ = fppfYoneda.map
      ((exists_factor_of_coverSieve (⟨Scheme.fppfTopology.yonedaEquiv σ, hb⟩ :
        SectionsOver (evBase P ρ) (coverSieve P) W).2).choose ≫ P.locallyTrivial.cover) := by
    rw [hσ, hbe.symm]
    exact congrArg _ (exists_factor_of_coverSieve hb).choose_spec.symm
  refine (evSourceLocal_congr_pt hpt _ hA).trans ?_
  exact evSourceLocal_congr σ hσ hA

variable (P ρ)

/-- The evaluation of a point of the pushout sheaf at a point of `P` over the same base. -/
noncomputable def evPt {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P ρ = p ≫ P.projection) :
    fppfYoneda.obj W ⟶ G'.space.toSheaf :=
  evLift P ρ α p h ≫ evMap P ρ

variable {P ρ}

/-- The evaluation only depends on the two points. -/
theorem evPt_congr {W : Scheme.{u}} {α α' : fppfYoneda.obj W ⟶ pushoutSheaf P ρ}
    {p p' : fppfYoneda.obj W ⟶ P.P} (hα : α = α') (hp : p = p')
    (h : α ≫ pushoutProj P ρ = p ≫ P.projection)
    (h' : α' ≫ pushoutProj P ρ = p' ≫ P.projection) : evPt P ρ α p h = evPt P ρ α' p' h' := by
  subst hα
  subst hp
  rfl

/-- **The evaluation is computed by the local formula.** -/
theorem evPt_eq_evLocal {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P ρ = p ≫ P.projection)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hα : α ≫ pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evPt P ρ α p h = evLocal P ρ α p c hα hp := by
  have hσ : evLift P ρ α p h ≫ evBase P ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [evLift_base]
    exact hα
  rw [evPt, comp_evMap _ c hσ, evSourceLocal]
  exact evLocal_congr (evLift_fst _ _ _) (evLift_snd _ _ _) _ _ hα hp

/-- The evaluation is natural in the test scheme. -/
theorem comp_evPt {V W : Scheme.{u}} (u : V ⟶ W) (α : fppfYoneda.obj W ⟶ pushoutSheaf P ρ)
    (p : fppfYoneda.obj W ⟶ P.P) (h : α ≫ pushoutProj P ρ = p ≫ P.projection)
    (h' : (fppfYoneda.map u ≫ α) ≫ pushoutProj P ρ =
      (fppfYoneda.map u ≫ p) ≫ P.projection) :
    fppfYoneda.map u ≫ evPt P ρ α p h =
      evPt P ρ (fppfYoneda.map u ≫ α) (fppfYoneda.map u ≫ p) h' := by
  have hlift : fppfYoneda.map u ≫ evLift P ρ α p h =
      evLift P ρ (fppfYoneda.map u ≫ α) (fppfYoneda.map u ≫ p) h' := by
    refine evSource_hom_ext P ρ ?_ ?_
    · rw [Category.assoc, evLift_fst, evLift_fst]
    · rw [Category.assoc, evLift_snd, evLift_snd]
  rw [evPt, evPt, ← Category.assoc, hlift]

end Ev

/-! ### The evaluation pairing is a bijection on fibres -/

section EvBijective

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} (P : FppfTorsor G T)
  (ρ : RelMonHom G G' T)

/-- The covering sieve of a test scheme on which the trivialisation of `P` is available. -/
theorem pullback_coverSieve_mem {W : Scheme.{u}} (s : W ⟶ T) :
    (coverSieve P).pullback s ∈ Scheme.fppfTopology W :=
  Scheme.fppfTopology.pullback_stable s (coverSieve_mem P)

variable {P ρ}

/-- Every member of that sieve carries a lift to the trivialising cover. -/
theorem exists_lift_of_pullback {V W : Scheme.{u}} {s : W ⟶ T} {u : V ⟶ W}
    (hu : ((coverSieve P).pullback s).arrows u) :
    ∃ c : V ⟶ P.locallyTrivial.coverScheme, c ≫ P.locallyTrivial.cover = u ≫ s :=
  exists_factor_of_coverSieve hu

/-- **The evaluation is equivariant for the action of `G'`.** -/
theorem evPt_actGluePt {W : Scheme.{u}} (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ pushoutProj P ρ = p ≫ P.projection)
    (h' : actGluePt P ρ g' α ≫ pushoutProj P ρ = p ≫ P.projection) :
    evPt P ρ (actGluePt P ρ g' α) p h' = g' * evPt P ρ α p h := by
  have hbase : α ≫ pushoutProj P ρ =
      fppfYoneda.map (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P ρ)) :=
    (fppfYoneda_map_yonedaEquiv _).symm
  refine hom_ext_of_sieve_pt (pullback_coverSieve_mem P
    (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P ρ))) fun V u hu => ?_
  obtain ⟨c, hc⟩ := exists_lift_of_pullback hu
  have hα : (fppfYoneda.map u ≫ α) ≫ pushoutProj P ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hbase, ← CategoryTheory.Functor.map_comp, hc]
  have hp : (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, ← h, ← Category.assoc]
    exact hα
  have hgα : (fppfYoneda.map u ≫ actGluePt P ρ g' α) ≫ pushoutProj P ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [comp_actGluePt, actGluePt_proj]
    exact hα
  have hgα2 : (fppfYoneda.map u ≫ actGluePt P ρ g' α) ≫ pushoutProj P ρ =
      (fppfYoneda.map u ≫ p) ≫ P.projection := hgα.trans hp.symm
  have hgα3 : actGluePt P ρ (fppfYoneda.map u ≫ g') (fppfYoneda.map u ≫ α) ≫
      pushoutProj P ρ = (fppfYoneda.map u ≫ p) ≫ P.projection := by
    rw [actGluePt_proj]
    exact hα.trans hp.symm
  have hgα4 : actGluePt P ρ (fppfYoneda.map u ≫ g') (fppfYoneda.map u ≫ α) ≫
      pushoutProj P ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [actGluePt_proj]
    exact hα
  rw [comp_evPt u _ _ h' hgα2, MonObj.comp_mul, comp_evPt u _ _ h (hα.trans hp.symm),
    evPt_congr (comp_actGluePt u g' α) rfl hgα2 hgα3,
    evPt_eq_evLocal _ _ _ c hgα4 hp, evPt_eq_evLocal _ _ _ c hα hp,
    evLocal_actGluePt (fppfYoneda.map u ≫ g') _ _ c hα hp hgα4]

/-- **The evaluation is equivariant for the action of `G` on `P`, through `ρ`.** -/
theorem evPt_actPt {W : Scheme.{u}} (g : fppfYoneda.obj W ⟶ G.space.toSheaf)
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P ρ) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ pushoutProj P ρ = p ≫ P.projection)
    (h' : α ≫ pushoutProj P ρ = actPt g p ≫ P.projection) :
    evPt P ρ α (actPt g p) h' = evPt P ρ α p h * (ρ.pt (p ≫ P.projection) g)⁻¹ := by
  have hbase : α ≫ pushoutProj P ρ =
      fppfYoneda.map (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P ρ)) :=
    (fppfYoneda_map_yonedaEquiv _).symm
  refine hom_ext_of_sieve_pt (pullback_coverSieve_mem P
    (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P ρ))) fun V u hu => ?_
  obtain ⟨c, hc⟩ := exists_lift_of_pullback hu
  have hα : (fppfYoneda.map u ≫ α) ≫ pushoutProj P ρ =
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
  have hgp2 : (fppfYoneda.map u ≫ α) ≫ pushoutProj P ρ =
      (fppfYoneda.map u ≫ actPt g p) ≫ P.projection := hα.trans hgp.symm
  have hgp3 : (fppfYoneda.map u ≫ α) ≫ pushoutProj P ρ =
      actPt (fppfYoneda.map u ≫ g) (fppfYoneda.map u ≫ p) ≫ P.projection := by
    rw [actPt_proj]
    exact hα.trans hp.symm
  have hgp4 : actPt (fppfYoneda.map u ≫ g) (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [actPt_proj]
    exact hp
  have hassoc : fppfYoneda.map u ≫ p ≫ P.projection =
      (fppfYoneda.map u ≫ p) ≫ P.projection := (Category.assoc _ _ _).symm
  rw [comp_evPt u _ _ h' hgp2, MonObj.comp_mul, GrpObj.comp_inv,
    comp_evPt u _ _ h (hα.trans hp.symm),
    evPt_congr rfl (comp_actPt (fppfYoneda.map u) g p) hgp2 hgp3, evPt_eq_evLocal _ _ _ c hα hgp4,
    evPt_eq_evLocal _ _ _ c hα hp, evLocal_actPt (fppfYoneda.map u ≫ g) _ _ c hα hp hgp4,
    RelMonHom.comp_pt, hassoc]

/-- **The evaluation at a point of `P` is injective on the fibre.** -/
theorem evPt_injective {W : Scheme.{u}} {α β : fppfYoneda.obj W ⟶ pushoutSheaf P ρ}
    (p : fppfYoneda.obj W ⟶ P.P) (hα : α ≫ pushoutProj P ρ = p ≫ P.projection)
    (hβ : β ≫ pushoutProj P ρ = p ≫ P.projection)
    (heq : evPt P ρ α p hα = evPt P ρ β p hβ) : α = β := by
  have hbase : p ≫ P.projection =
      fppfYoneda.map (Scheme.fppfTopology.yonedaEquiv (p ≫ P.projection)) :=
    (fppfYoneda_map_yonedaEquiv _).symm
  refine hom_ext_of_sieve_pt (pullback_coverSieve_mem P
    (Scheme.fppfTopology.yonedaEquiv (p ≫ P.projection))) fun V u hu => ?_
  obtain ⟨c, hc⟩ := exists_lift_of_pullback hu
  have hp : (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hbase, ← CategoryTheory.Functor.map_comp, hc]
  have hα' : (fppfYoneda.map u ≫ α) ≫ pushoutProj P ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hα, ← Category.assoc]
    exact hp
  have hβ' : (fppfYoneda.map u ≫ β) ≫ pushoutProj P ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hβ, ← Category.assoc]
    exact hp
  refine evLocal_injective (fppfYoneda.map u ≫ p) hα' hβ' hp ?_
  rw [← evPt_eq_evLocal _ _ (by rw [Category.assoc, hα, ← Category.assoc]) c hα' hp,
    ← evPt_eq_evLocal _ _ (by rw [Category.assoc, hβ, ← Category.assoc]) c hβ' hp,
    ← comp_evPt u _ _ hα, ← comp_evPt u _ _ hβ, heq]

variable (P ρ)

/-- The point of the pushout sheaf with prescribed value at a point of `P`, over a test scheme
carrying a lift to the trivialising cover. -/
noncomputable def ptOfEvLocal {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    fppfYoneda.obj W ⟶ pushoutSheaf P ρ :=
  ptOfCoord P ρ c
    (g' * ρ.pt (p ≫ P.projection) (divPt P p (coverPt c) (by rw [hp, coverPt_proj])))

variable {P ρ}

/-- The point with prescribed value lies over the expected base point. -/
theorem ptOfEvLocal_proj {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    ptOfEvLocal P ρ p g' c hp ≫ pushoutProj P ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) :=
  ptOfCoord_proj _ _

/-- **The point with prescribed value has that value.** -/
@[simp]
theorem evPt_ptOfEvLocal {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    evPt P ρ (ptOfEvLocal P ρ p g' c hp) p
      ((ptOfEvLocal_proj p g' c hp).trans hp.symm) = g' := by
  rw [evPt_eq_evLocal _ _ _ c (ptOfEvLocal_proj p g' c hp) hp]
  exact evLocal_ptOfCoord p c g' hp

/-- The point with prescribed value does not depend on the lift. -/
theorem ptOfEvLocal_congr {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) {c c' : W ⟶ P.locallyTrivial.coverScheme}
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp' : p ≫ P.projection = fppfYoneda.map (c' ≫ P.locallyTrivial.cover)) :
    ptOfEvLocal P ρ p g' c hp = ptOfEvLocal P ρ p g' c' hp' := by
  refine evPt_injective p ((ptOfEvLocal_proj p g' c hp).trans hp.symm)
    ((ptOfEvLocal_proj p g' c' hp').trans hp'.symm) ?_
  rw [evPt_ptOfEvLocal, evPt_ptOfEvLocal]

/-- The point with prescribed value is natural in the test scheme. -/
theorem comp_ptOfEvLocal {V W : Scheme.{u}} (u : V ⟶ W) (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (c : W ⟶ P.locallyTrivial.coverScheme)
    (hp : p ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hp' : (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover)) :
    fppfYoneda.map u ≫ ptOfEvLocal P ρ p g' c hp =
      ptOfEvLocal P ρ (fppfYoneda.map u ≫ p) (fppfYoneda.map u ≫ g') (u ≫ c) hp' := by
  have h1 : (fppfYoneda.map u ≫ ptOfEvLocal P ρ p g' c hp) ≫ pushoutProj P ρ =
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
  (ρ : RelMonHom G G' T)

variable {P ρ}

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
    ptOfEvLocal P ρ p g' c h = ptOfEvLocal P ρ p' g'' c h' := by
  subst hp0
  subst hg
  rfl

variable (P ρ)

/-- The partially defined point of the pushout sheaf with prescribed value at a point of `P`. -/
noncomputable def ptOfEvPartial {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (s : W ⟶ T)
    (hs : p ≫ P.projection = fppfYoneda.map s) :
    PartialHom (fppfYoneda.map s) (pushoutSheaf P ρ) (coverSieve P) where
  app {V} x :=
    Scheme.fppfTopology.yonedaEquiv (ptOfEvLocal P ρ
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
    (hs : p ≫ P.projection = fppfYoneda.map s) : fppfYoneda.obj W ⟶ pushoutSheaf P ρ :=
  (ptOfEvPartial P ρ p g' s hs).glue (coverSieve_mem P)

variable {P ρ}

/-- The point with prescribed value lies over the expected base point. -/
theorem ptOfEv_proj {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf) (s : W ⟶ T)
    (hs : p ≫ P.projection = fppfYoneda.map s) :
    ptOfEv P ρ p g' s hs ≫ pushoutProj P ρ = fppfYoneda.map s := by
  refine (ptOfEvPartial P ρ p g' s hs).glue_comp (coverSieve_mem P) (pushoutProj P ρ) ?_
  intro V x
  rw [show (ptOfEvPartial P ρ p g' s hs).app x = Scheme.fppfTopology.yonedaEquiv
      (ptOfEvLocal P ρ (Scheme.fppfTopology.yonedaEquiv.symm x.1 ≫ p)
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
    fppfYoneda.map u ≫ ptOfEv P ρ p g' s hs =
      ptOfEvLocal P ρ (fppfYoneda.map u ≫ p) (fppfYoneda.map u ≫ g') c hp := by
  have hu' : (coverSieve P).arrows
      (GromovWitten.SheafGluing.base (fppfYoneda.map s)
        (u : (fppfYoneda.obj W).obj.obj (op V))) := by
    rw [base_yoneda_map]
    exact hu
  have key := (ptOfEvPartial P ρ p g' s hs).glue_app (coverSieve_mem P)
    (⟨u, hu'⟩ : SectionsOver (fppfYoneda.map s) (coverSieve P) V)
  have hval : Scheme.fppfTopology.yonedaEquiv (fppfYoneda.map u ≫ ptOfEv P ρ p g' s hs) =
      (ptOfEvPartial P ρ p g' s hs).app
        (⟨u, hu'⟩ : SectionsOver (fppfYoneda.map s) (coverSieve P) V) := by
    rw [GrothendieckTopology.yonedaEquiv_comp, ptOfEv]
    exact key
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [hval, show (ptOfEvPartial P ρ p g' s hs).app
      (⟨u, hu'⟩ : SectionsOver (fppfYoneda.map s) (coverSieve P) V) =
      Scheme.fppfTopology.yonedaEquiv (ptOfEvLocal P ρ
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
    evPt P ρ (ptOfEv P ρ p g' s hs) p ((ptOfEv_proj p g' s hs).trans hs.symm) = g' := by
  refine hom_ext_of_sieve_pt (pullback_coverSieve_mem P s) fun V u hu => ?_
  obtain ⟨c, hc⟩ := exists_lift_of_pullback hu
  have hp : (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hs, ← CategoryTheory.Functor.map_comp, hc]
  have hloc := comp_ptOfEv (P := P) (ρ := ρ) p g' s hs u hu c hc hp
  have h1 : (fppfYoneda.map u ≫ ptOfEv P ρ p g' s hs) ≫ pushoutProj P ρ =
      (fppfYoneda.map u ≫ p) ≫ P.projection := by
    rw [Category.assoc, ptOfEv_proj, Category.assoc, hs]
  rw [comp_evPt u _ _ _ h1, evPt_congr hloc rfl h1
    ((ptOfEvLocal_proj (fppfYoneda.map u ≫ p) (fppfYoneda.map u ≫ g') c hp).trans hp.symm),
    evPt_ptOfEvLocal]

variable (P ρ)

/-- **The pushout datum of a `G`-torsor along a relative homomorphism `ρ`.**  This is the
existence statement announced in the module docstring: it is unconditional, and no
sheafification is involved. -/
noncomputable def pushoutTorsor : PushoutTorsorRel ρ P where
  sheaf := pushoutSheaf P ρ
  action := pushoutAction P ρ
  projection := pushoutProj P ρ
  action_over := pushoutSmul_proj P ρ
  ev α p h := evPt P ρ α p h
  ev_naturality u α p h h' := comp_evPt u α p h h'
  ev_actPt g' α p h h' := by
    have hg : actGluePt P ρ g' α ≫ pushoutProj P ρ = p ≫ P.projection := by
      rw [actGluePt_proj]
      exact h
    have key : evPt P ρ (actGluePt P ρ g' α) p hg = g' * evPt P ρ α p h :=
      evPt_actGluePt (P := P) (ρ := ρ) g' α p h hg
    refine Eq.trans ?_ key
    exact evPt_congr (lift_comp_pushoutSmul (P := P) (ρ := ρ) g' α) rfl h' hg
  ev_actPt_right g α p h h' := evPt_actPt (P := P) (ρ := ρ) g α p h h'
  ev_bijective {W} p g' := by
    have hs : p ≫ P.projection =
        fppfYoneda.map (Scheme.fppfTopology.yonedaEquiv (p ≫ P.projection)) :=
      (fppfYoneda_map_yonedaEquiv _).symm
    have hbase : ptOfEv P ρ p g' (Scheme.fppfTopology.yonedaEquiv (p ≫ P.projection)) hs ≫
        pushoutProj P ρ = p ≫ P.projection := by
      rw [ptOfEv_proj, fppfYoneda_map_yonedaEquiv]
    refine ⟨⟨ptOfEv P ρ p g' _ hs, hbase⟩, evPt_ptOfEv p g' _ hs, ?_⟩
    intro β hβ
    refine Subtype.ext (evPt_injective p β.2 hbase ?_)
    rw [hβ, evPt_ptOfEv]

/-- **The pushout torsor.**  Every fppf `G`-torsor `P` over `T` and every homomorphism
`ρ` of group objects over `T` produce an fppf `G'`-torsor `ρ_* P` over `T`. -/
noncomputable def pushoutFppfTorsor : FppfTorsor G' T :=
  (pushoutTorsor P ρ).toFppfTorsor

/-- The underlying sheaf of the pushout torsor is the glued sheaf. -/
@[simp]
theorem pushoutFppfTorsor_P : (pushoutFppfTorsor P ρ).P = pushoutSheaf P ρ :=
  rfl

/-- The projection of the pushout torsor is the glued structure morphism. -/
@[simp]
theorem pushoutFppfTorsor_projection :
    (pushoutFppfTorsor P ρ).projection = pushoutProj P ρ :=
  rfl

end PushoutExists

/-! ### The induced equivariant map on the pushout -/

section Target

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {U : AlgebraicSpaceAction G}
  {U' : AlgebraicSpaceAction G'} (P : ActionTorsor G U T)
  (ρ : RelMonHom G G' T) (τ : RelEquivMap ρ U U')

/-- The local formula for the induced equivariant map on the pushout: `α ↦ α (L c) · pt (L c)`,
where `L c` is the tautological point of `P` at a lift `c` of the base. -/
noncomputable def targetLocal {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor ρ)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hα : α ≫ pushoutProj P.toFppfTorsor ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover)) : fppfYoneda.obj W ⟶ U'.space.toSheaf :=
  actPt (evPt P.toFppfTorsor ρ α (coverPt c) (by rw [hα, coverPt_proj]))
    (τ.pt (fppfYoneda.map (c ≫ P.locallyTrivial.cover)) (coverPt c ≫ P.target))

variable {P ρ τ}

/-- The local formula only depends on the point of the pushout. -/
theorem targetLocal_congr_pt {W : Scheme.{u}}
    {α β : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor ρ} (hαβ : α = β)
    {c : W ⟶ P.locallyTrivial.coverScheme}
    (hα : α ≫ pushoutProj P.toFppfTorsor ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hβ : β ≫ pushoutProj P.toFppfTorsor ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    targetLocal P ρ τ α c hα = targetLocal P ρ τ β c hβ := by
  subst hαβ
  rfl

/-- **The local formula does not depend on the chosen lift.** -/
theorem targetLocal_lift_congr {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor ρ)
    {c c' : W ⟶ P.locallyTrivial.coverScheme}
    (hα : α ≫ pushoutProj P.toFppfTorsor ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hα' : α ≫ pushoutProj P.toFppfTorsor ρ =
      fppfYoneda.map (c' ≫ P.locallyTrivial.cover)) :
    targetLocal P ρ τ α c' hα' = targetLocal P ρ τ α c hα := by
  have hcc : c ≫ P.locallyTrivial.cover = c' ≫ P.locallyTrivial.cover :=
    cover_lift_eq (hα.symm.trans hα')
  have hL : coverPt c = actPt (coverDiv hcc) (coverPt c') := (actPt_divPt _ _ _).symm
  have hbase : ρ.pt (coverPt c' ≫ P.projection) (coverDiv hcc) = relDiv ρ hcc :=
    ρ.pt_congr (coverPt_proj c') rfl
  have hev : evPt P.toFppfTorsor ρ α (coverPt c) (by rw [hα, coverPt_proj]) =
      evPt P.toFppfTorsor ρ α (coverPt c') (by rw [hα', coverPt_proj]) *
        (relDiv ρ hcc)⁻¹ := by
    rw [← hbase]
    refine Eq.trans (evPt_congr rfl hL (by rw [hα, coverPt_proj])
      (by rw [hα', actPt_proj, coverPt_proj])) ?_
    exact evPt_actPt (coverDiv hcc) α (coverPt c') (by rw [hα', coverPt_proj])
      (by rw [hα', actPt_proj, coverPt_proj])
  have h1 : (fppfYoneda.map (c ≫ P.locallyTrivial.cover) :
      fppfYoneda.obj W ⟶ fppfYoneda.obj T) =
      fppfYoneda.map (c' ≫ P.locallyTrivial.cover) := by rw [hcc]
  have htg : τ.pt (fppfYoneda.map (c ≫ P.locallyTrivial.cover)) (coverPt c ≫ P.target) =
      actPt (relDiv ρ hcc)
        (τ.pt (fppfYoneda.map (c' ≫ P.locallyTrivial.cover)) (coverPt c' ≫ P.target)) := by
    rw [h1, hL, actPt_comp_target, RelEquivMap.pt_actPt, relDiv]
  rw [targetLocal, targetLocal, hev, htg, ← actPt_mul, inv_mul_cancel_right]

/-- The local formula is natural in the test scheme. -/
theorem comp_targetLocal {V W : Scheme.{u}} (u : V ⟶ W)
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor ρ)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hα : α ≫ pushoutProj P.toFppfTorsor ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover))
    (hα' : (fppfYoneda.map u ≫ α) ≫ pushoutProj P.toFppfTorsor ρ =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover)) :
    fppfYoneda.map u ≫ targetLocal P ρ τ α c hα =
      targetLocal P ρ τ (fppfYoneda.map u ≫ α) (u ≫ c) hα' := by
  have hcp : fppfYoneda.map u ≫ coverPt c = coverPt (u ≫ c) := comp_coverPt u c
  have pf1 : (fppfYoneda.map u ≫ α) ≫ pushoutProj P.toFppfTorsor ρ =
      (fppfYoneda.map u ≫ coverPt c) ≫ P.projection := by
    rw [Category.assoc, hα, Category.assoc, coverPt_proj]
  have pf2 : (fppfYoneda.map u ≫ α) ≫ pushoutProj P.toFppfTorsor ρ =
      coverPt (u ≫ c) ≫ P.projection := by
    rw [hα', coverPt_proj]
  have hev := comp_evPt u α (coverPt c) (by rw [hα, coverPt_proj]) pf1
  have hA := evPt_congr (P := P.toFppfTorsor) (ρ := ρ) rfl hcp pf1 pf2
  have hb1 : fppfYoneda.map u ≫ coverPt c ≫ P.target = coverPt (u ≫ c) ≫ P.target := by
    rw [← Category.assoc, hcp]
  have hb2 : (fppfYoneda.map u ≫ fppfYoneda.map (c ≫ P.locallyTrivial.cover) :
      fppfYoneda.obj V ⟶ fppfYoneda.obj T) =
      fppfYoneda.map ((u ≫ c) ≫ P.locallyTrivial.cover) := by
    rw [← CategoryTheory.Functor.map_comp, Category.assoc]
  rw [targetLocal, targetLocal, comp_actPt, hev, hA, RelEquivMap.comp_pt, hb1, hb2]

end Target

/-! ### The contraction of an action torsor -/

section Contraction

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {U : AlgebraicSpaceAction G}
  {U' : AlgebraicSpaceAction G'} (P : ActionTorsor G U T)
  (ρ : RelMonHom G G' T) (τ : RelEquivMap ρ U U')

/-- The induced equivariant map on the pushout, defined on the sections whose base lies in the
covering sieve of the trivialising cover of `P`. -/
noncomputable def targetPartial :
    PartialHom (pushoutProj P.toFppfTorsor ρ) U'.space.toSheaf (coverSieve P.toFppfTorsor) where
  app {W} x :=
    Scheme.fppfTopology.yonedaEquiv (targetLocal P ρ τ
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
        pushoutProj P.toFppfTorsor ρ = fppfYoneda.map
          ((u ≫ (exists_factor_of_coverSieve x.2).choose) ≫ P.locallyTrivial.cover) := by
      rw [Category.assoc, GrothendieckTopology.yonedaEquiv_symm_naturality_right,
        yonedaEquiv_symm_map, ← CategoryTheory.Functor.map_comp]
      refine congrArg _ ?_
      rw [Category.assoc, (exists_factor_of_coverSieve x.2).choose_spec]
      rfl
    have hB : (fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm x.1) ≫
        pushoutProj P.toFppfTorsor ρ = fppfYoneda.map
          ((exists_factor_of_coverSieve (SectionsOver.res u x).2).choose ≫
            P.locallyTrivial.cover) := by
      rw [← hres, GrothendieckTopology.yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_map]
      exact congrArg _ (exists_factor_of_coverSieve (SectionsOver.res u x).2).choose_spec.symm
    refine Eq.trans (comp_targetLocal u (Scheme.fppfTopology.yonedaEquiv.symm x.1)
      (exists_factor_of_coverSieve x.2).choose _ hA) ?_
    refine Eq.trans (targetLocal_lift_congr _ hA hB).symm ?_
    exact (targetLocal_congr_pt hres _ hB).symm

/-- **The induced equivariant map `r_* P ⟶ U'`.** -/
noncomputable def targetMap : pushoutSheaf P.toFppfTorsor ρ ⟶ U'.space.toSheaf :=
  (targetPartial P ρ τ).glue (coverSieve_mem P.toFppfTorsor)

variable {P ρ τ}

/-- The induced map is computed by the local formula. -/
theorem comp_targetMap {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor ρ)
    (c : W ⟶ P.locallyTrivial.coverScheme)
    (hα : α ≫ pushoutProj P.toFppfTorsor ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover)) :
    α ≫ targetMap P ρ τ = targetLocal P ρ τ α c hα := by
  have hbe : GromovWitten.SheafGluing.base (pushoutProj P.toFppfTorsor ρ)
      (Scheme.fppfTopology.yonedaEquiv α) = c ≫ P.locallyTrivial.cover := by
    rw [SheafGluing.base_yonedaEquiv, hα, GrothendieckTopology.yonedaEquiv_yoneda_map]
  have hb : (coverSieve P.toFppfTorsor).arrows
      (GromovWitten.SheafGluing.base (pushoutProj P.toFppfTorsor ρ)
        (Scheme.fppfTopology.yonedaEquiv α)) := by
    rw [hbe]
    exact ⟨_, c, P.locallyTrivial.cover, Presieve.singleton.mk, rfl⟩
  have key := (targetPartial P ρ τ).glue_app (coverSieve_mem P.toFppfTorsor)
    (⟨Scheme.fppfTopology.yonedaEquiv α, hb⟩ :
      SectionsOver (pushoutProj P.toFppfTorsor ρ) (coverSieve P.toFppfTorsor) W)
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [targetMap, GrothendieckTopology.yonedaEquiv_comp, key]
  refine congrArg Scheme.fppfTopology.yonedaEquiv ?_
  have hpt2 : Scheme.fppfTopology.yonedaEquiv.symm
      ((⟨Scheme.fppfTopology.yonedaEquiv α, hb⟩ :
        SectionsOver (pushoutProj P.toFppfTorsor ρ) (coverSieve P.toFppfTorsor) W).1) = α :=
    Equiv.symm_apply_apply _ _
  have hA : α ≫ pushoutProj P.toFppfTorsor ρ = fppfYoneda.map
      ((exists_factor_of_coverSieve (⟨Scheme.fppfTopology.yonedaEquiv α, hb⟩ :
        SectionsOver (pushoutProj P.toFppfTorsor ρ)
          (coverSieve P.toFppfTorsor) W).2).choose ≫ P.locallyTrivial.cover) := by
    rw [hα, hbe.symm]
    exact congrArg _ (exists_factor_of_coverSieve hb).choose_spec.symm
  refine (targetLocal_congr_pt hpt2 _ hA).trans ?_
  exact targetLocal_lift_congr α hα hA

/-- **The induced map is `G'`-equivariant, on points.** -/
theorem actGluePt_comp_targetMap {W : Scheme.{u}}
    (g' : fppfYoneda.obj W ⟶ G'.space.toSheaf)
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor ρ) :
    actGluePt P.toFppfTorsor ρ g' α ≫ targetMap P ρ τ =
      actPt g' (α ≫ targetMap P ρ τ) := by
  have hbase : α ≫ pushoutProj P.toFppfTorsor ρ = fppfYoneda.map
      (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P.toFppfTorsor ρ)) :=
    (fppfYoneda_map_yonedaEquiv _).symm
  refine hom_ext_of_sieve_pt (pullback_coverSieve_mem P.toFppfTorsor
    (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P.toFppfTorsor ρ))) fun V u hu => ?_
  obtain ⟨c, hc⟩ := exists_lift_of_pullback hu
  have hα : (fppfYoneda.map u ≫ α) ≫ pushoutProj P.toFppfTorsor ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hbase, ← CategoryTheory.Functor.map_comp, hc]
  have hgα : actGluePt P.toFppfTorsor ρ (fppfYoneda.map u ≫ g') (fppfYoneda.map u ≫ α) ≫
      pushoutProj P.toFppfTorsor ρ = fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [actGluePt_proj]
    exact hα
  have hp : coverPt c ≫ P.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover) :=
    coverPt_proj c
  rw [← Category.assoc, comp_actGluePt, comp_targetMap _ c hgα, targetLocal,
    evPt_actGluePt (fppfYoneda.map u ≫ g') _ _ (hα.trans hp.symm) (hgα.trans hp.symm),
    actPt_mul, comp_actPt]
  refine congrArg (fun q => actPt (fppfYoneda.map u ≫ g') q) ?_
  exact ((Category.assoc (fppfYoneda.map u) α (targetMap P ρ τ)).symm.trans
    (comp_targetMap (fppfYoneda.map u ≫ α) c hα)).symm

variable (P ρ τ)

/-- **The induced map is `G'`-equivariant.** -/
theorem targetMap_equivariant :
    ModObj.smul (M := G'.space.toSheaf) (X := pushoutSheaf P.toFppfTorsor ρ) ≫
        targetMap P ρ τ =
      (G'.space.toSheaf ◁ targetMap P ρ τ) ≫
        ModObj.smul (M := G'.space.toSheaf) (X := U'.space.toSheaf) := by
  refine hom_ext_points fun W ω => ?_
  rw [← Category.assoc, ← Category.assoc, ← TorsorPushout.lift_comp_fst_snd ω,
    ConeQuotient.lift_whiskerLeft, pushoutAction_smul (P := P.toFppfTorsor) (ρ := ρ),
    lift_comp_pushoutSmul]
  exact actGluePt_comp_targetMap _ _

/-- **The contraction of an action torsor along a relative homomorphism.**  The pushout
`ρ_* P` of the underlying torsor, with the induced equivariant map to `U'`. -/
noncomputable def pushoutActionTorsor : ActionTorsor G' U' T where
  toFppfTorsor := pushoutFppfTorsor P.toFppfTorsor ρ
  target := targetMap P ρ τ
  target_equivariant := targetMap_equivariant P ρ τ

/-- The underlying torsor of the contraction is the pushout torsor. -/
@[simp]
theorem pushoutActionTorsor_toFppfTorsor :
    (pushoutActionTorsor P ρ τ).toFppfTorsor = pushoutFppfTorsor P.toFppfTorsor ρ :=
  rfl

/-- The equivariant map of the contraction is the induced map. -/
@[simp]
theorem pushoutActionTorsor_target :
    (pushoutActionTorsor P ρ τ).target = targetMap P ρ τ :=
  rfl

end Contraction

/-! ### The induced map evaluated at a point of `P`, and trivialised torsors -/

section TargetPoint

open GromovWitten.SheafGluing

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {U : AlgebraicSpaceAction G}
  {U' : AlgebraicSpaceAction G'} {P : ActionTorsor G U T}
  {ρ : RelMonHom G G' T} {τ : RelEquivMap ρ U U'}

/-- **The induced map of the contraction, computed globally at a point of `P`.**  If `α` is a
point of `ρ_* P` and `p` a point of `P` over the same base point, then the image of `α` is the
translate of `τ (p)` by the evaluation `ev α p`.  No lift of the base to the trivialising cover
is needed. -/
theorem targetMap_eq_actPt {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ pushoutSheaf P.toFppfTorsor ρ) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ pushoutProj P.toFppfTorsor ρ = p ≫ P.projection) :
    α ≫ targetMap P ρ τ =
      actPt (evPt P.toFppfTorsor ρ α p h) (τ.pt (p ≫ P.projection) (p ≫ P.target)) := by
  have hbase : α ≫ pushoutProj P.toFppfTorsor ρ = fppfYoneda.map
      (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P.toFppfTorsor ρ)) :=
    (fppfYoneda_map_yonedaEquiv _).symm
  refine hom_ext_of_sieve_pt (pullback_coverSieve_mem P.toFppfTorsor
    (Scheme.fppfTopology.yonedaEquiv (α ≫ pushoutProj P.toFppfTorsor ρ))) fun V u hu => ?_
  obtain ⟨c, hc⟩ := exists_lift_of_pullback hu
  have hα : (fppfYoneda.map u ≫ α) ≫ pushoutProj P.toFppfTorsor ρ =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, hbase, ← CategoryTheory.Functor.map_comp, hc]
  have hp : (fppfYoneda.map u ≫ p) ≫ P.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
    rw [Category.assoc, ← h, ← Category.assoc]
    exact hα
  have hcp : coverPt c ≫ P.projection =
      fppfYoneda.map (c ≫ P.locallyTrivial.cover) := coverPt_proj c
  set g := divPt P.toFppfTorsor (fppfYoneda.map u ≫ p) (coverPt c) (hp.trans hcp.symm) with hgdef
  have hgp : actPt g (coverPt c) = fppfYoneda.map u ≫ p := actPt_divPt _ _ _
  have hL : fppfYoneda.map u ≫ α ≫ targetMap P ρ τ =
      actPt (evPt P.toFppfTorsor ρ (fppfYoneda.map u ≫ α) (coverPt c) (hα.trans hcp.symm))
        (τ.pt (fppfYoneda.map (c ≫ P.locallyTrivial.cover)) (coverPt c ≫ P.target)) := by
    rw [← Category.assoc, comp_targetMap _ c hα, targetLocal]
  have hev : evPt P.toFppfTorsor ρ (fppfYoneda.map u ≫ α) (fppfYoneda.map u ≫ p)
        (hα.trans hp.symm) =
      evPt P.toFppfTorsor ρ (fppfYoneda.map u ≫ α) (coverPt c) (hα.trans hcp.symm) *
        (ρ.pt (fppfYoneda.map (c ≫ P.locallyTrivial.cover)) g)⁻¹ := by
    rw [← ρ.pt_congr hcp rfl]
    refine Eq.trans (evPt_congr rfl hgp.symm (hα.trans hp.symm)
      (hα.trans (by rw [hgp]; exact hp.symm))) ?_
    exact evPt_actPt g (fppfYoneda.map u ≫ α) (coverPt c) (hα.trans hcp.symm)
      (hα.trans (by rw [hgp]; exact hp.symm))
  have htg : fppfYoneda.map u ≫ τ.pt (p ≫ P.projection) (p ≫ P.target) =
      actPt (ρ.pt (fppfYoneda.map (c ≫ P.locallyTrivial.cover)) g)
        (τ.pt (fppfYoneda.map (c ≫ P.locallyTrivial.cover)) (coverPt c ≫ P.target)) := by
    have h1 : fppfYoneda.map u ≫ p ≫ P.projection =
        fppfYoneda.map (c ≫ P.locallyTrivial.cover) := by
      rw [← Category.assoc]
      exact hp
    have h2 : fppfYoneda.map u ≫ p ≫ P.target = actPt g (coverPt c ≫ P.target) := by
      rw [← Category.assoc, ← hgp, actPt_comp_target]
    rw [RelEquivMap.comp_pt, τ.pt_congr h1 h2, RelEquivMap.pt_actPt]
  rw [hL, comp_actPt, comp_evPt u α p h (hα.trans hp.symm), hev, htg, ← actPt_mul,
    inv_mul_cancel_right]

variable (P ρ)

/-- The global section of the contraction `ρ_* P` attached to a global section of `P`: the point
whose evaluation at that section is the unit. -/
noncomputable def contractionSection (s : fppfYoneda.obj T ⟶ P.P)
    (hs : s ≫ P.projection = 𝟙 _) :
    fppfYoneda.obj T ⟶ pushoutSheaf P.toFppfTorsor ρ :=
  ptOfEv P.toFppfTorsor ρ s 1 (𝟙 T) (hs.trans (CategoryTheory.Functor.map_id fppfYoneda T).symm)

variable {P ρ}

/-- The projection of the section of the contraction. -/
theorem contractionSection_proj (s : fppfYoneda.obj T ⟶ P.P)
    (hs : s ≫ P.projection = 𝟙 _) :
    contractionSection P ρ s hs ≫ pushoutProj P.toFppfTorsor ρ = s ≫ P.projection := by
  rw [contractionSection, ptOfEv_proj, CategoryTheory.Functor.map_id, hs]

/-- The section of the contraction is a section. -/
theorem contractionSection_projection (s : fppfYoneda.obj T ⟶ P.P)
    (hs : s ≫ P.projection = 𝟙 _) :
    contractionSection P ρ s hs ≫ (pushoutActionTorsor P ρ τ).projection = 𝟙 _ :=
  (contractionSection_proj s hs).trans hs

/-- The evaluation of the section of the contraction at the given section of `P` is the unit. -/
@[simp]
theorem evPt_contractionSection (s : fppfYoneda.obj T ⟶ P.P)
    (hs : s ≫ P.projection = 𝟙 _) :
    evPt P.toFppfTorsor ρ (contractionSection P ρ s hs) s (contractionSection_proj s hs) = 1 :=
  evPt_ptOfEv s 1 (𝟙 T) (hs.trans (CategoryTheory.Functor.map_id fppfYoneda T).symm)

/-- **The point of `U'` attached to the section of the contraction is the contracted point.** -/
theorem contractionSection_target (s : fppfYoneda.obj T ⟶ P.P)
    (hs : s ≫ P.projection = 𝟙 _) :
    contractionSection P ρ s hs ≫ (pushoutActionTorsor P ρ τ).target =
      τ.pt (𝟙 (fppfYoneda.obj T)) (s ≫ P.target) := by
  change contractionSection P ρ s hs ≫ targetMap P ρ τ = _
  rw [targetMap_eq_actPt (contractionSection P ρ s hs) s (contractionSection_proj s hs),
    evPt_contractionSection, actPt_one, τ.pt_congr hs rfl]

/-- **The contraction of a torsor with a global section is again trivial**, with the point of
`U'` obtained by applying `τ` to the point of `U` of the section. -/
noncomputable def contractionIsoTrivial (s : fppfYoneda.obj T ⟶ P.P)
    (hs : s ≫ P.projection = 𝟙 _) :
    ConeQuotient.trivialWithPoint (τ.pt (𝟙 (fppfYoneda.obj T)) (s ≫ P.target)) ≅
      pushoutActionTorsor P ρ τ :=
  (eqToIso (congrArg ConeQuotient.trivialWithPoint
      (contractionSection_target (τ := τ) s hs).symm)).trans
    (ConeQuotient.isoTrivialOfSection (pushoutActionTorsor P ρ τ)
      (contractionSection P ρ s hs) (contractionSection_projection (τ := τ) s hs))

/-- **The contraction of the trivial torsor with point `t` is the trivial torsor with point
`τ (t)`.**  Together with `ConeQuotient.TrivialPoint.embedding` this identifies the relative
pushout with the elementary contraction of trivialised torsors. -/
noncomputable def pushoutTrivialIso (t : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    ConeQuotient.trivialWithPoint (τ.pt (𝟙 (fppfYoneda.obj T)) t) ≅
      pushoutActionTorsor (ConeQuotient.trivialWithPoint t) ρ τ :=
  have hsec : ConeQuotient.unitSection G T ≫
      (ConeQuotient.trivialWithPoint t).projection = 𝟙 _ := ConeQuotient.unitSection_snd
  have hpt : ConeQuotient.unitSection G T ≫ (ConeQuotient.trivialWithPoint t).target = t :=
    ConeQuotient.unitSection_comp_trivialTarget t
  (eqToIso (congrArg (fun q => ConeQuotient.trivialWithPoint (τ.pt (𝟙 (fppfYoneda.obj T)) q))
      hpt.symm)).trans
    (contractionIsoTrivial (P := ConeQuotient.trivialWithPoint t) (ρ := ρ) (τ := τ)
      (ConeQuotient.unitSection G T) hsec)

end TargetPoint

/-! ### The identity pushout datum, and the scalar contraction of the cone quotient -/

section IdentityPushout

variable {G : AlgebraicSpaceGroup.{u}} {T' : Scheme.{u}}

/-- **The torsor `P` itself is a pushout datum of `P` along the identity homomorphism**: the
evaluation pairing is the difference of two points of `P`.  Together with a uniqueness statement
for pushout data this gives the unit law `(𝟙)_* P ≅ P`; uniqueness is not proved here. -/
noncomputable def idPushoutTorsorRel (P : FppfTorsor G T') :
    PushoutTorsorRel (RelMonHom.ofMonHom T' (𝟙 G.space.toSheaf)) P where
  sheaf := P.P
  action := P.action
  projection := P.projection
  action_over := P.action_over
  ev α p h := divPt P α p h
  ev_naturality u α p h h' :=
    comp_divPt (fppfYoneda.map u) α p h (by
      rw [← Category.assoc, ← Category.assoc]
      exact h')
  ev_actPt g' α p h h' := divPt_actPt_left g' α p h h'
  ev_actPt_right g α p h h' := by
    rw [RelMonHom.pt_ofMonHom, Category.comp_id]
    have hgp : actPt g p ≫ P.projection = p ≫ P.projection := actPt_proj P g p
    have h1 : divPt P (actPt g p) p hgp = g := by
      rw [divPt_actPt_left g p p rfl hgp, divPt_self p rfl, mul_one]
    have h2 : divPt P α (actPt g p) h' * divPt P (actPt g p) p hgp = divPt P α p h :=
      divPt_mul α (actPt g p) p h' hgp
    rw [h1] at h2
    rw [← h2, mul_inv_cancel_right]
  ev_bijective p g' := by
    refine ⟨⟨actPt g' p, actPt_proj P g' p⟩, ?_, ?_⟩
    · exact (eq_divPt (actPt g' p) p (actPt_proj P g' p) g' rfl).symm
    · rintro ⟨β, hβ⟩ hev
      refine Subtype.ext ?_
      change β = actPt g' p
      rw [← hev]
      exact (actPt_divPt β p hβ).symm

/-- The sheaf of the identity pushout datum is the torsor itself. -/
@[simp]
theorem idPushoutTorsorRel_sheaf (P : FppfTorsor G T') :
    (idPushoutTorsorRel P).sheaf = P.P :=
  rfl

end IdentityPushout

section ConeScale

open ConeQuotient
open scoped CategoryTheory.Obj

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T : Scheme.{u}}

variable (σ) in
/-- A morphism of schemes into `𝔸^σ`, read as a point of the vector bundle group. -/
noncomputable def bdlPt {W : Scheme.{u}} (x : W ⟶ bundleScheme σ) :
    fppfYoneda.obj W ⟶ (vectorBundleGroup σ).space.toSheaf :=
  fppfYoneda.map x

/-- Every point of the vector bundle group comes from a morphism of schemes. -/
theorem bdlPt_surjective {W : Scheme.{u}}
    (g : fppfYoneda.obj W ⟶ (vectorBundleGroup σ).space.toSheaf) : ∃ x, bdlPt σ x = g :=
  ⟨fppfYoneda.preimage g, fppfYoneda.map_preimage g⟩

/-- The unit point of the vector bundle group. -/
@[simp]
theorem bdlPt_one {W : Scheme.{u}} : bdlPt σ (1 : W ⟶ bundleScheme σ) = 1 :=
  map_one_of_monoidal (Z := W) (M := bundleScheme σ) fppfYoneda

/-- The point attached to a product is the product of the points. -/
@[simp]
theorem bdlPt_mul {W : Scheme.{u}} (x y : W ⟶ bundleScheme σ) :
    bdlPt σ (x * y) = bdlPt σ x * bdlPt σ y :=
  map_mul_of_monoidal fppfYoneda x y

variable (σ) in
/-- Multiplication by a scalar `r ∈ Γ(T, 𝒪)` on the `T`-points of the vector bundle group,
as a morphism of schemes `𝔸^σ × T ⟶ 𝔸^σ`. -/
noncomputable def scaleBundleScheme (r : Γ(T, ⊤)) : bundleScheme σ ⊗ T ⟶ bundleScheme σ :=
  ofCoords fun i => (snd (bundleScheme σ) T).appTop r * coords (fst (bundleScheme σ) T) i

/-- The coordinates of a point of the scaling morphism. -/
theorem coords_comp_scaleBundleScheme (r : Γ(T, ⊤)) {X : Scheme.{u}}
    (h : X ⟶ bundleScheme σ ⊗ T) (i : σ) :
    coords (h ≫ scaleBundleScheme σ r) i =
      (h ≫ snd _ _).appTop r * coords (h ≫ fst _ _) i := by
  rw [coords_comp, scaleBundleScheme, coords_ofCoords, map_mul, ← coords_comp,
    _root_.AlgebraicGeometry.Scheme.Hom.comp_appTop]
  rfl

variable (σ T) in
/-- The underlying morphism of fppf sheaves of the scalar contraction of the vector bundle
group. -/
noncomputable def scaleRelMonHomFun (r : Γ(T, ⊤)) :
    (vectorBundleGroup σ).space.toSheaf ⊗ fppfYoneda.obj T ⟶
      (vectorBundleGroup σ).space.toSheaf :=
  Functor.LaxMonoidal.μ fppfYoneda (bundleScheme σ) T ≫ fppfYoneda.map (scaleBundleScheme σ r)

/-- The scalar multiplication morphism, evaluated at a pair of scheme-valued points. -/
theorem lift_comp_scaleRelMonHomFun (r : Γ(T, ⊤)) {W : Scheme.{u}} (x : W ⟶ bundleScheme σ)
    (b : W ⟶ T) :
    lift (bdlPt σ x) (fppfYoneda.map b) ≫ scaleRelMonHomFun σ T r =
      bdlPt σ (lift x b ≫ scaleBundleScheme σ r) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ fppfYoneda.map (scaleBundleScheme σ r))
      (Functor.Monoidal.lift_μ (F := fppfYoneda) x b)).trans (fppfYoneda.map_comp _ _).symm)

variable (σ T) in
/-- **Scalar multiplication by `r : Γ(T, 𝒪)` on the vector bundle group**, as a homomorphism of
group objects relative to `T`.  It is *not* a homomorphism of the absolute group object: the
scalar is a section over `T`, so it only makes sense on points lying over `T`. -/
noncomputable def scaleRelMonHom (r : Γ(T, ⊤)) :
    RelMonHom (vectorBundleGroup σ) (vectorBundleGroup σ) T where
  toFun := scaleRelMonHomFun σ T r
  map_one' {W} b := by
    obtain ⟨b₀, rfl⟩ : ∃ b₀ : W ⟶ T, fppfYoneda.map b₀ = b :=
      ⟨fppfYoneda.preimage b, fppfYoneda.map_preimage b⟩
    have h2 : lift (1 : W ⟶ bundleScheme σ) b₀ ≫ scaleBundleScheme σ r =
        (1 : W ⟶ bundleScheme σ) := by
      refine coords_injective (funext fun i => ?_)
      rw [coords_comp_scaleBundleScheme, lift_fst, coords_one, mul_zero]
    rw [← bdlPt_one (σ := σ) (W := W), lift_comp_scaleRelMonHomFun, h2]
  map_mul' {W} b x y := by
    obtain ⟨b₀, rfl⟩ : ∃ b₀ : W ⟶ T, fppfYoneda.map b₀ = b :=
      ⟨fppfYoneda.preimage b, fppfYoneda.map_preimage b⟩
    obtain ⟨x₀, rfl⟩ := bdlPt_surjective (σ := σ) x
    obtain ⟨y₀, rfl⟩ := bdlPt_surjective (σ := σ) y
    have h2 : lift (x₀ * y₀) b₀ ≫ scaleBundleScheme σ r =
        (lift x₀ b₀ ≫ scaleBundleScheme σ r) * (lift y₀ b₀ ≫ scaleBundleScheme σ r) := by
      refine coords_injective (funext fun i => ?_)
      rw [coords_comp_scaleBundleScheme, lift_fst, lift_snd, coords_mul, mul_add, coords_mul,
        coords_comp_scaleBundleScheme, coords_comp_scaleBundleScheme, lift_fst, lift_fst,
        lift_snd, lift_snd]
    rw [← bdlPt_mul, lift_comp_scaleRelMonHomFun, lift_comp_scaleRelMonHomFun,
      lift_comp_scaleRelMonHomFun, h2, bdlPt_mul]

/-- The scalar homomorphism, computed on scheme-valued points. -/
theorem scaleRelMonHom_pt (r : Γ(T, ⊤)) {W : Scheme.{u}} (x : W ⟶ bundleScheme σ) (b : W ⟶ T) :
    (scaleRelMonHom σ T r).pt (fppfYoneda.map b) (bdlPt σ x) =
      bdlPt σ (lift x b ≫ scaleBundleScheme σ r) :=
  lift_comp_scaleRelMonHomFun r x b


variable (A : ConeAction R S F) (bas : Module.Basis σ R F)

/-- A morphism of schemes into the affine cone, read as a point of the cone action space. -/
noncomputable def cnPt {W : Scheme.{u}} (x : W ⟶ coneScheme S) :
    fppfYoneda.obj W ⟶ (coneActionSpace A bas).space.toSheaf :=
  fppfYoneda.map x

/-- Every point of the cone action space comes from a morphism of schemes. -/
theorem cnPt_surjective {W : Scheme.{u}}
    (g : fppfYoneda.obj W ⟶ (coneActionSpace A bas).space.toSheaf) : ∃ x, cnPt A bas x = g :=
  ⟨fppfYoneda.preimage g, fppfYoneda.map_preimage g⟩

/-- Points of the cone action space are determined by the underlying morphism of schemes. -/
theorem cnPt_injective {W : Scheme.{u}} :
    Function.Injective (cnPt A bas (W := W)) := fun _ _ h => fppfYoneda.map_injective h

/-- **The action of the bundle group on the cone, on scheme-valued points.** -/
theorem actPt_cnPt {W : Scheme.{u}} (g : W ⟶ bundleScheme σ) (x : W ⟶ coneScheme S) :
    actPt (bdlPt σ g) (cnPt A bas x) = cnPt A bas (lift g x ≫ actScheme A bas) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ fppfYoneda.map (actScheme A bas))
      (Functor.Monoidal.lift_μ (F := fppfYoneda) g x)).trans (fppfYoneda.map_comp _ _).symm)

/-- The contraction of the affine cone by a scalar `r ∈ Γ(T, 𝒪)`, as a morphism of schemes
`C × T ⟶ C`. -/
noncomputable def scaleConeScheme (r : Γ(T, ⊤)) : coneScheme S ⊗ T ⟶ coneScheme S :=
  ofConePt (scaleRing A ((snd (coneScheme S) T).appTop r) (conePt (fst (coneScheme S) T)))

/-- The ring map of a point of the cone contraction. -/
theorem conePt_comp_scaleConeScheme (r : Γ(T, ⊤)) {X : Scheme.{u}}
    (h : X ⟶ coneScheme S ⊗ T) :
    conePt (h ≫ scaleConeScheme A r) =
      scaleRing A ((h ≫ snd _ _).appTop r) (conePt (h ≫ fst _ _)) := by
  rw [conePt_comp, scaleConeScheme, conePt_ofConePt, comp_scaleRing, ← conePt_comp,
    _root_.AlgebraicGeometry.Scheme.Hom.comp_appTop]
  rfl

/-- The underlying morphism of fppf sheaves of the scalar contraction of the cone. -/
noncomputable def scaleConeFun (r : Γ(T, ⊤)) :
    (coneActionSpace A bas).space.toSheaf ⊗ fppfYoneda.obj T ⟶
      (coneActionSpace A bas).space.toSheaf :=
  Functor.LaxMonoidal.μ fppfYoneda (coneScheme S) T ≫ fppfYoneda.map (scaleConeScheme A r)

/-- The cone contraction morphism, evaluated at a pair of scheme-valued points. -/
theorem lift_comp_scaleConeFun (r : Γ(T, ⊤)) {W : Scheme.{u}} (x : W ⟶ coneScheme S)
    (b : W ⟶ T) :
    lift (cnPt A bas x) (fppfYoneda.map b) ≫ scaleConeFun A bas r =
      cnPt A bas (lift x b ≫ scaleConeScheme A r) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ fppfYoneda.map (scaleConeScheme A r))
      (Functor.Monoidal.lift_μ (F := fppfYoneda) x b)).trans (fppfYoneda.map_comp _ _).symm)

/-- **The scalar contraction of the affine cone quotient `[C/E]`, relative to `T`.**  The
`ρ`-equivariance is exactly `ConeQuotient.scaleRing_actOn`, `c_r (v · x) = (r v) · c_r x`. -/
noncomputable def coneScaleRelEquivMap (r : Γ(T, ⊤)) :
    RelEquivMap (scaleRelMonHom σ T r) (coneActionSpace A bas) (coneActionSpace A bas) where
  toFun := scaleConeFun A bas r
  equivariant' {W} b g x := by
    obtain ⟨b₀, rfl⟩ : ∃ b₀ : W ⟶ T, fppfYoneda.map b₀ = b :=
      ⟨fppfYoneda.preimage b, fppfYoneda.map_preimage b⟩
    obtain ⟨g₀, rfl⟩ := bdlPt_surjective (σ := σ) g
    obtain ⟨x₀, rfl⟩ := cnPt_surjective A bas x
    rw [actPt_cnPt, lift_comp_scaleConeFun, lift_comp_scaleConeFun, scaleRelMonHom_pt,
      actPt_cnPt]
    refine congrArg (cnPt A bas) (conePt_injective ?_)
    have hv : coords (lift g₀ b₀ ≫ scaleBundleScheme σ r) =
        ((b₀.appTop) r) • coords g₀ := by
      funext i
      rw [coords_comp_scaleBundleScheme, lift_fst, lift_snd]
      rfl
    rw [conePt_comp_scaleConeScheme, conePt_comp_actScheme, lift_fst, lift_snd, lift_fst,
      lift_snd, conePt_comp_actScheme, lift_fst, lift_snd, conePt_comp_scaleConeScheme,
      lift_fst, lift_snd, hv, scaleRing_actOn]

/-- The cone contraction, computed on scheme-valued points. -/
theorem coneScaleRelEquivMap_pt (r : Γ(T, ⊤)) {W : Scheme.{u}} (x : W ⟶ coneScheme S)
    (b : W ⟶ T) :
    (coneScaleRelEquivMap A bas r).pt (fppfYoneda.map b) (cnPt A bas x) =
      cnPt A bas (lift x b ≫ scaleConeScheme A r) :=
  lift_comp_scaleConeFun A bas r x b


/-- The cone contraction on `T`-points, in terms of ring-valued points of the cone. -/
theorem coneScaleRelEquivMap_pt_id (r : Γ(T, ⊤)) (x : T ⟶ coneScheme S) :
    (coneScaleRelEquivMap A bas r).pt (𝟙 (fppfYoneda.obj T)) (cnPt A bas x) =
      cnPt A bas (ofConePt (scaleRing A r (conePt x))) := by
  have hid : (fppfYoneda.map (𝟙 T) : fppfYoneda.obj T ⟶ fppfYoneda.obj T) = 𝟙 _ :=
    CategoryTheory.Functor.map_id fppfYoneda T
  rw [← hid, coneScaleRelEquivMap_pt]
  refine congrArg (cnPt A bas) (conePt_injective ?_)
  rw [conePt_comp_scaleConeScheme, lift_fst, lift_snd, conePt_ofConePt]
  simp

/-- **The unconditional scalar contraction of the affine cone quotient `[C/E]`.**  For every
scalar `r : Γ(T, 𝒪)` it contracts *every* object of the quotient stack over `T`, with no
triviality hypothesis on the torsor. -/
noncomputable def coneContraction (r : Γ(T, ⊤))
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T :=
  pushoutActionTorsor P (scaleRelMonHom σ T r) (coneScaleRelEquivMap A bas r)

/-- **The relative contraction agrees with `ConeQuotient.coneTwist` on `T`-points**, for an
affine base `T = Spec B` and a scalar `r₀ : B`. -/
theorem coneScaleRelEquivMap_pt_eq_coneTwist {B : Type u} [CommRing B] (r₀ : B)
    (t : fppfYoneda.obj (coneScheme B) ⟶ (coneActionSpace A bas).space.toSheaf) :
    (coneScaleRelEquivMap A bas (gammaMap B r₀)).pt
        (𝟙 (fppfYoneda.obj (coneScheme B))) t = (coneTwist A bas r₀).pt t := by
  obtain ⟨φ, rfl⟩ : ∃ φ, conePoint A bas φ = t :=
    ⟨conePointHom A bas t, conePoint_conePointHom A bas t⟩
  have hc : conePoint A bas φ = cnPt A bas (ofConePt ((gammaMap B).comp φ)) := rfl
  rw [hc, coneScaleRelEquivMap_pt_id, conePt_ofConePt, coneTwist_pt, ← hc,
    conePointHom_conePoint]
  exact congrArg (cnPt A bas) (congrArg ofConePt (comp_scaleRing A (gammaMap B) r₀ φ).symm)


/-- **The unconditional contraction restricted to trivialised torsors is the elementary
contraction `ConeQuotient.ActionTwist.functor` of `ConeQuotient.coneTwist`.**  This is the
comparison announced in `Cones/QuotientTorsorStack.lean`, now with no `AllTorsorsTrivial`
hypothesis on the left-hand side. -/
noncomputable def coneContractionEmbeddingIso {B : Type u} [CommRing B] (r₀ : B)
    (x : TrivialPoint (vectorBundleGroup σ) (coneActionSpace A bas) (coneScheme B)) :
    (TrivialPoint.embedding (vectorBundleGroup σ) (coneActionSpace A bas) (coneScheme B)).obj
        ((coneTwist A bas r₀).functor.obj x) ≅
      coneContraction A bas (gammaMap B r₀)
        ((TrivialPoint.embedding (vectorBundleGroup σ) (coneActionSpace A bas)
          (coneScheme B)).obj x) :=
  (eqToIso (congrArg trivialWithPoint
      (coneScaleRelEquivMap_pt_eq_coneTwist A bas r₀ x.pt).symm)).trans
    (pushoutTrivialIso (τ := coneScaleRelEquivMap A bas (gammaMap B r₀)) x.pt)

end ConeScale

end TorsorPushoutRel

end GromovWitten.AlgebraicGeometry
