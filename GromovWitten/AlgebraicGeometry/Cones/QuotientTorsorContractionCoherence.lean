/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.QuotientTorsorContraction

/-!
# Coherence isomorphisms of the unconditional scalar contraction of `[C/E]`

`Cones/QuotientTorsorContraction.lean` constructs the unconditional scalar contraction
`ConeQuotient.contractionFunctor A bas r` of the affine cone quotient `[C/E]` as a genuine
endofunctor of the whole torsor groupoid `ActionTorsor (vectorBundleGroup σ) (coneActionSpace A
bas) T`, but proves none of the coherence isomorphisms a `ConeStack` (see `Cones/Stack.lean`)
requires.  This file proves the unit, multiplicativity and base-change laws as natural
isomorphisms of functors, and the object-level vanishing and vertex laws, all unconditionally
(no `AllTorsorsTrivial` hypothesis).

## Technique

A relative pushout datum `TorsorPushoutRel.PushoutTorsorRel ρ P` mentions the relative
homomorphism `ρ` only through `ρ.pt` in its `ev_actPt_right` field.  Consequently every
construction below takes a *pointwise* hypothesis on `ρ.pt` rather than an equality of
`RelMonHom`s, which avoids transporting pushout data along an equality of homomorphisms and makes
the results directly applicable to the scalar homomorphisms of `1`, `r * s`, `0` and of a
pulled-back scalar:

* `PushoutTorsorRel.idDatumOf ρ hρ P`, for `hρ : ∀ b x, ρ.pt b x = x`, exhibits `P` itself as a
  pushout datum of `P` along `ρ` (the evaluation pairing is the difference point).
* `PushoutTorsorRel.compDatum hcomp B C`, for
  `hcomp : ∀ b x, ρ''.pt b x = ρ'.pt b (ρ.pt b x)`, exhibits an iterated pushout as a pushout
  datum along `ρ''` (the evaluation pairing goes through the unit point
  `PushoutTorsorRel.unitPt`).
* `PushoutTorsorRel.pullbackDatum b hpull A`, for `hpull : ∀ b' x, ρ'.pt b' x = ρ.pt (b' ≫ b) x`,
  exhibits the base change of a pushout datum as a pushout datum of the base-changed torsor.
* `PushoutTorsorRel.trivialDatum ρ hρ P`, for `hρ : ∀ b x, ρ.pt b x = 1`, exhibits the *trivial*
  torsor as a pushout datum of every `P` along `ρ`.

Naturality of the resulting comparisons is proved by the uniqueness of maps out of a pushout
datum (`PushoutTorsorRel.eq_pushMap`), through the two commutation lemmas
`PushoutTorsorRel.cmpMap_comp_pushMap` and `PushoutTorsorRel.pushMap_comp_cmpMap` together with
the identification of the induced map for each of the above data
(`PushoutTorsorRel.pushMap_idDatumOf`, `pushMap_compDatum`, `pushMap_pullbackDatum`).  The
compatibility with the maps to the action space is proved with
`TorsorPushoutRel.targetMap_eq_actPt`, packaged as
`TorsorPushoutRel.cmpMap_comp_targetMap_of_ev`.  The descent construction of the pushout sheaf is
never unfolded.

## Main results

General form, for `TorsorPushoutRel.pushoutFunctorRel`:

* `TorsorPushoutRel.pushoutFunctorRelIdIso`: for `ρ`, `τ` the identity on points,
  `pushoutFunctorRel ρ τ ≅ 𝟭 (ActionTorsor G U T)`.
* `TorsorPushoutRel.pushoutFunctorRelCompIso`: for `ρ''`, `τ''` pointwise the composites,
  `pushoutFunctorRel ρ'' τ'' ≅ pushoutFunctorRel ρ τ ⋙ pushoutFunctorRel ρ' τ'`.
* `TorsorPushoutRel.pushoutFunctorRelPullbackIso`: for `ρ'`, `τ'` pointwise the base changes
  along `b : T' ⟶ T`,
  `pullbackFunctor b ⋙ pushoutFunctorRel ρ' τ' ≅ pushoutFunctorRel ρ τ ⋙ pullbackFunctor b`.
* `TorsorPushoutRel.pushoutTrivialHomIso` and `TorsorPushoutRel.pushoutTrivialHomActionIso`: for
  `ρ` trivial on points, the pushout of *every* torsor is the trivial torsor, and the pushout of
  every object of `[U/G]` is a trivialised object, whose point of the action space is computed by
  `TorsorPushoutRel.trivialHomSection_comp_targetMap`.

Cone quotient form, for `ConeQuotient.contractionFunctor`:

* **`ConeQuotient.contractionFunctorOneIso : contractionFunctor A bas 1 ≅ 𝟭 _`** — the unit law.
* **`ConeQuotient.contractionFunctorMulIso : contractionFunctor A bas (r * s) ≅
  contractionFunctor A bas s ⋙ contractionFunctor A bas r`** — multiplicativity.
* **`ConeQuotient.contractionFunctorPullbackIso : contractionFunctor A bas r ⋙
  pullbackFunctor b ≅ pullbackFunctor b ⋙ contractionFunctor A bas (b.appTop r)`** — base change
  (the scalar `Scheme.Hom.appTop b r` is `canonicalFppfScalarRings.pullback b r`).
* **`ConeQuotient.contractionFunctorZeroIso`** and `contractionFunctorZeroTorsorIso` — the
  vanishing law: the contraction by `0` of any object is a trivialised object, with trivial
  underlying `E`-torsor, whose point of the cone is the contraction by `0`, i.e. the vertex, of
  the point of the cone of any local point of the torsor.
* **`ConeQuotient.contractionFunctorVertexIso`** and `contractionFunctorVertexIsoOfConeVertex` —
  the vertex law: a trivialised object whose point of the cone is invariant under the contraction
  is fixed by it, and the vertex of the cone (over any point of the base, `GradedCone.IsConeVertex`)
  is such a point.
* `TorsorPushoutRel.conePt_scaleConeScheme_comp_algebraMap` and
  `conePt_actScheme_comp_algebraMap` — the contraction and the action of the bundle group do not
  move the point of the base underneath, on generalised points.

## What is not done

`ConeStack.contractionZeroIso`, `contractionVertexIso` and `contractionProjectionIso` of
`Cones/Stack.lean` are stated in terms of the stack morphisms `projection : total ⟶ base` and
`vertex : base ⟶ total` of a cone stack, hence in terms of the `ConeStack` assembly of `[C/E]`,
which is still blocked (`ActionTorsor.quotientStack` lands in `LargeFppfStack.{u}`, not
`FppfStack.{u}`).  Beyond the assembly itself, those three laws require one further geometric
construction which is absent from the repository: the *descent of the base point*, i.e. the
factorisation of the `E`-invariant map `P.P ⟶ C ⟶ Spec R` through `P.P ⟶ y(T)`, which is what
names the vertex over the base point of an object as a `T`-point of the cone.  The results above
are the strongest unconditional statements available without it: the zero and vertex laws are
proved at the level of objects (and the point of the cone is characterised on generalised points
of the base), and the projection law is proved on generalised points of the cone.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

namespace TorsorPushoutRel

universe u

open TorsorPushout

/-! ### Comparison of pushout data versus functoriality in the torsor -/

namespace PushoutTorsorRel

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}
  {ρ : RelMonHom G G' T} {P Q : FppfTorsor G T}

/-- **The comparison of two pushout data for the same torsor preserves the evaluation pairing**,
at every point of `P`, not only at the tautological points of the trivialising cover. -/
theorem ev_cmpMap (A B : PushoutTorsorRel ρ P) {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ A.sheaf) (p : fppfYoneda.obj W ⟶ P.P)
    (h : α ≫ A.projection = p ≫ P.projection)
    (h' : (α ≫ cmpMap A B) ≫ B.projection = p ≫ P.projection) :
    B.ev (α ≫ cmpMap A B) p h' = A.ev α p h := by
  have hid : TorsorPushout.PushoutTorsor.IsEquivariantPt (𝟙 P.P) := by
    intro Z g x
    rw [Category.comp_id, Category.comp_id]
  have hbase : ∀ {V : Scheme.{u}} (β : fppfYoneda.obj V ⟶ A.sheaf)
      (q : fppfYoneda.obj V ⟶ P.P), β ≫ A.projection = q ≫ P.projection →
      (β ≫ cmpMap A B) ≫ B.projection = (q ≫ 𝟙 P.P) ≫ P.projection := by
    intro V β q hq
    rw [Category.assoc, cmpMap_proj, hq, Category.comp_id]
  have hloc : ∀ {V : Scheme.{u}} (β : fppfYoneda.obj V ⟶ A.sheaf)
      (c : V ⟶ P.locallyTrivial.coverScheme),
      β ≫ A.projection = fppfYoneda.map (c ≫ P.locallyTrivial.cover) →
      ∀ (h₁ : (β ≫ cmpMap A B) ≫ B.projection = (coverPt c ≫ 𝟙 P.P) ≫ P.projection)
        (h₂ : β ≫ A.projection = coverPt c ≫ P.projection),
        B.ev (β ≫ cmpMap A B) (coverPt c ≫ 𝟙 P.P) h₁ = A.ev β (coverPt c) h₂ := by
    intro V β c hc h₁ h₂
    have h₃ : (β ≫ cmpMap A B) ≫ B.projection = coverPt c ≫ P.projection := by
      rw [Category.assoc, cmpMap_proj]
      exact h₂
    refine (B.ev_congr_right (β ≫ cmpMap A B) (Category.comp_id _) h₁ h₃).trans ?_
    refine (B.ev_congr_left (cmpMap_spec A B β c hc) (coverPt c) h₃
      (cmpLocal_proj β c hc)).trans ?_
    exact ev_cmpLocal β c hc
  have hcomp : (α ≫ cmpMap A B) ≫ B.projection = (p ≫ 𝟙 P.P) ≫ P.projection := hbase α p h
  have key := ev_eq_of_ev_cover_over A B hid (Category.id_comp _) (cmpMap A B) hbase hloc α p h
    hcomp
  exact (B.ev_congr_right (α ≫ cmpMap A B) (Category.comp_id _).symm h' hcomp).trans key

/-- **The comparison of two pushout data for `P`, followed by the map induced by `φ : P ⟶ Q`,
is the map induced by `φ`.** -/
theorem cmpMap_comp_pushMap (A A' : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q)
    (φ : P ⟶ Q) : cmpMap A A' ≫ pushMap A' B φ = pushMap A B φ := by
  refine eq_pushMap A B φ _ ?_ ?_
  · rw [Category.assoc, pushMap_proj, cmpMap_proj]
  · intro V β c hc h₁ h₂
    have hγ : (β ≫ cmpMap A A') ≫ A'.projection = coverPt c ≫ P.projection := by
      rw [Category.assoc, cmpMap_proj]
      exact h₂
    have h₃ : ((β ≫ cmpMap A A') ≫ pushMap A' B φ) ≫ B.projection =
        (coverPt c ≫ φ.iso.hom) ≫ Q.projection := by
      rw [Category.assoc, pushMap_proj, hγ, Category.assoc, φ.over]
    calc B.ev (β ≫ cmpMap A A' ≫ pushMap A' B φ) (coverPt c ≫ φ.iso.hom) h₁
        = B.ev ((β ≫ cmpMap A A') ≫ pushMap A' B φ) (coverPt c ≫ φ.iso.hom) h₃ :=
          B.ev_congr (Category.assoc _ _ _).symm rfl h₁ h₃
      _ = A'.ev (β ≫ cmpMap A A') (coverPt c) hγ :=
          ev_pushMap A' B φ (β ≫ cmpMap A A') (coverPt c) hγ h₃
      _ = A.ev β (coverPt c) h₂ := ev_cmpMap A A' β (coverPt c) h₂ hγ

/-- **The map induced by `φ : P ⟶ Q`, followed by the comparison of two pushout data for `Q`, is
the map induced by `φ`.** -/
theorem pushMap_comp_cmpMap (A : PushoutTorsorRel ρ P) (B B' : PushoutTorsorRel ρ Q)
    (φ : P ⟶ Q) : pushMap A B φ ≫ cmpMap B B' = pushMap A B' φ := by
  refine eq_pushMap A B' φ _ ?_ ?_
  · rw [Category.assoc, cmpMap_proj, pushMap_proj]
  · intro V β c hc h₁ h₂
    have hδ : (β ≫ pushMap A B φ) ≫ B.projection = (coverPt c ≫ φ.iso.hom) ≫ Q.projection := by
      rw [Category.assoc, pushMap_proj, h₂, Category.assoc, φ.over]
    have h₃ : ((β ≫ pushMap A B φ) ≫ cmpMap B B') ≫ B'.projection =
        (coverPt c ≫ φ.iso.hom) ≫ Q.projection := by
      rw [Category.assoc, cmpMap_proj]
      exact hδ
    calc B'.ev (β ≫ pushMap A B φ ≫ cmpMap B B') (coverPt c ≫ φ.iso.hom) h₁
        = B'.ev ((β ≫ pushMap A B φ) ≫ cmpMap B B') (coverPt c ≫ φ.iso.hom) h₃ :=
          B'.ev_congr (Category.assoc _ _ _).symm rfl h₁ h₃
      _ = B.ev (β ≫ pushMap A B φ) (coverPt c ≫ φ.iso.hom) hδ :=
          ev_cmpMap B B' (β ≫ pushMap A B φ) (coverPt c ≫ φ.iso.hom) hδ h₃
      _ = A.ev β (coverPt c) h₂ := ev_pushMap A B φ β (coverPt c) h₂ hδ

/-! ### The torsor itself as a pushout datum along a pointwise trivial homomorphism -/

variable (ρ)

/-- **A torsor is its own pushout along a relative homomorphism that is the identity on
points**: the evaluation pairing is the difference of two points of `P`.  This is
`TorsorPushoutRel.idPushoutTorsorRel` with the hypothesis `ρ = 1` weakened to a pointwise
statement, so that no transport of pushout data along an equality of homomorphisms is needed. -/
noncomputable def idDatumOf {G : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}
    (ρ : RelMonHom G G T)
    (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ.pt b x = x)
    (P : FppfTorsor G T) : PushoutTorsorRel ρ P where
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
    rw [hρ]
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

variable {ρ}

section IdDatum

variable {H : AlgebraicSpaceGroup.{u}} {ρ₁ : RelMonHom H H T} {X Y : FppfTorsor H T}
  (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ H.space.toSheaf),
    ρ₁.pt b x = x)

/-- The underlying sheaf of the tautological pushout datum is the torsor itself. -/
@[simp]
theorem idDatumOf_sheaf : (idDatumOf ρ₁ hρ X).sheaf = X.P :=
  rfl

/-- The evaluation pairing of the tautological pushout datum is the difference point. -/
theorem idDatumOf_ev {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ X.P)
    (p : fppfYoneda.obj W ⟶ X.P) (h : α ≫ X.projection = p ≫ X.projection) :
    (idDatumOf ρ₁ hρ X).ev α p h = divPt X α p h :=
  rfl

/-- **The map of tautological pushout data induced by a morphism of torsors is the morphism
itself.** -/
theorem pushMap_idDatumOf (φ : X ⟶ Y) :
    pushMap (idDatumOf ρ₁ hρ X) (idDatumOf ρ₁ hρ Y) φ = φ.iso.hom := by
  refine (eq_pushMap (idDatumOf ρ₁ hρ X) (idDatumOf ρ₁ hρ Y) φ φ.iso.hom φ.over ?_).symm
  intro V β c hc h₁ h₂
  exact TorsorPushout.PushoutTorsor.divPt_comp_iso φ β (coverPt c) h₂ h₁

/-- **The comparison of a pushout datum with the tautological one, evaluated at a point.**  The
image of `α` in `X` is the translate of `p` by the evaluation of `α` at `p`. -/
theorem cmpMap_idDatumOf_eq_actPt (A : PushoutTorsorRel ρ₁ X) {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ A.sheaf) (p : fppfYoneda.obj W ⟶ X.P)
    (h : α ≫ A.projection = p ≫ X.projection) :
    α ≫ cmpMap A (idDatumOf ρ₁ hρ X) = actPt (A.ev α p h) p :=
  have h' : (α ≫ cmpMap A (idDatumOf ρ₁ hρ X)) ≫ (idDatumOf ρ₁ hρ X).projection =
      p ≫ X.projection :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => α ≫ q) (cmpMap_proj A (idDatumOf ρ₁ hρ X))).trans h)
  (actPt_divPt (α ≫ cmpMap A (idDatumOf ρ₁ hρ X)) p h').symm.trans
    (congrArg (fun g => actPt g p) (ev_cmpMap A (idDatumOf ρ₁ hρ X) α p h h'))

end IdDatum

end PushoutTorsorRel

/-! ### The pushout along a pointwise trivial homomorphism is the identity functor -/

section IdIso

variable {G : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}} {U : AlgebraicSpaceAction G}
  (ρ : RelMonHom G G T) (τ : RelEquivMap ρ U U)

/-- **The comparison with the tautological pushout datum is compatible with the maps to the
action space**, when `ρ` and `τ` are the identity on points.  Both sides are computed at the
tautological points of the trivialising cover of `P` by `TorsorPushoutRel.targetMap_eq_actPt` and
`PushoutTorsorRel.cmpMap_idDatumOf_eq_actPt`. -/
theorem cmpMap_idDatumOf_comp_target
    (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ.pt b x = x)
    (hτ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ U.space.toSheaf),
      τ.pt b x = x) (P : ActionTorsor G U T) :
    PushoutTorsorRel.cmpMap (pushoutTorsor P.toFppfTorsor ρ)
        (PushoutTorsorRel.idDatumOf ρ hρ P.toFppfTorsor) ≫ P.target = targetMap P ρ τ := by
  refine PushoutTorsorRel.hom_ext_of_cmp (fun α c hc => ?_)
  have h' : α ≫ (pushoutTorsor P.toFppfTorsor ρ).projection = coverPt c ≫ P.projection := by
    rw [hc, coverPt_proj]
  have hL : α ≫ PushoutTorsorRel.cmpMap (pushoutTorsor P.toFppfTorsor ρ)
        (PushoutTorsorRel.idDatumOf ρ hρ P.toFppfTorsor) =
      actPt (evPt P.toFppfTorsor ρ α (coverPt c) h') (coverPt c) :=
    PushoutTorsorRel.cmpMap_idDatumOf_eq_actPt hρ (pushoutTorsor P.toFppfTorsor ρ) α
      (coverPt c) h'
  have hR : α ≫ targetMap P ρ τ =
      actPt (evPt P.toFppfTorsor ρ α (coverPt c) h') (coverPt c ≫ P.target) :=
    (targetMap_eq_actPt (τ := τ) α (coverPt c) h').trans
      (congrArg (actPt (evPt P.toFppfTorsor ρ α (coverPt c) h')) (hτ _ _))
  refine Eq.trans ?_ hR.symm
  refine (Category.assoc α _ P.target).symm.trans ?_
  refine (congrArg (fun q => q ≫ P.target) hL).trans ?_
  exact actPt_comp_target (evPt P.toFppfTorsor ρ α (coverPt c) h') (coverPt c)

/-- **The comparison of the pushout along a pointwise trivial homomorphism with the torsor
itself**, as an arrow of the quotient-stack fibre. -/
noncomputable def pushoutIdActionHom
    (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ.pt b x = x)
    (hτ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ U.space.toSheaf),
      τ.pt b x = x) (P : ActionTorsor G U T) :
    pushoutActionTorsor P ρ τ ⟶ P where
  iso := PushoutTorsorRel.compareIso (pushoutTorsor P.toFppfTorsor ρ)
    (PushoutTorsorRel.idDatumOf ρ hρ P.toFppfTorsor)
  over := PushoutTorsorRel.cmpMap_proj (pushoutTorsor P.toFppfTorsor ρ)
    (PushoutTorsorRel.idDatumOf ρ hρ P.toFppfTorsor)
  equivariant := PushoutTorsorRel.cmpMap_equivariant (pushoutTorsor P.toFppfTorsor ρ)
    (PushoutTorsorRel.idDatumOf ρ hρ P.toFppfTorsor)
  target := cmpMap_idDatumOf_comp_target ρ τ hρ hτ P

/-- **Naturality of the comparison of the pushout along a pointwise trivial homomorphism with the
identity**: both composites are the map induced by `φ` from the pushout datum of `P` to the
tautological pushout datum of `Q`. -/
theorem pushoutHom_comp_pushoutIdActionHom
    (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ.pt b x = x)
    (hτ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ U.space.toSheaf),
      τ.pt b x = x) {P Q : ActionTorsor G U T} (φ : P ⟶ Q) :
    pushoutHom (ρ := ρ) (τ := τ) φ ≫ pushoutIdActionHom ρ τ hρ hτ Q =
      pushoutIdActionHom ρ τ hρ hτ P ≫ φ := by
  refine ActionTorsor.Hom.ext _ _ ?_
  have h1 : PushoutTorsorRel.pushMap (pushoutTorsor P.toFppfTorsor ρ)
        (pushoutTorsor Q.toFppfTorsor ρ) (ActionTorsor.Hom.toFppfHom φ) ≫
        PushoutTorsorRel.cmpMap (pushoutTorsor Q.toFppfTorsor ρ)
          (PushoutTorsorRel.idDatumOf ρ hρ Q.toFppfTorsor) =
      PushoutTorsorRel.pushMap (pushoutTorsor P.toFppfTorsor ρ)
        (PushoutTorsorRel.idDatumOf ρ hρ Q.toFppfTorsor) (ActionTorsor.Hom.toFppfHom φ) :=
    PushoutTorsorRel.pushMap_comp_cmpMap _ _ _ _
  have hid : PushoutTorsorRel.pushMap (PushoutTorsorRel.idDatumOf ρ hρ P.toFppfTorsor)
      (PushoutTorsorRel.idDatumOf ρ hρ Q.toFppfTorsor) (ActionTorsor.Hom.toFppfHom φ) =
      φ.iso.hom :=
    PushoutTorsorRel.pushMap_idDatumOf hρ (ActionTorsor.Hom.toFppfHom φ)
  have h2 : PushoutTorsorRel.cmpMap (pushoutTorsor P.toFppfTorsor ρ)
        (PushoutTorsorRel.idDatumOf ρ hρ P.toFppfTorsor) ≫ φ.iso.hom =
      PushoutTorsorRel.pushMap (pushoutTorsor P.toFppfTorsor ρ)
        (PushoutTorsorRel.idDatumOf ρ hρ Q.toFppfTorsor) (ActionTorsor.Hom.toFppfHom φ) := by
    rw [← hid]
    exact PushoutTorsorRel.cmpMap_comp_pushMap _ _ _ _
  exact h1.trans h2.symm

/-- **The pushout along a relative homomorphism that is the identity on points, with an
equivariant map that is the identity on points, is the identity functor.**  This is the unit
coherence isomorphism of a contraction, in the generality of `pushoutFunctorRel`. -/
noncomputable def pushoutFunctorRelIdIso
    (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ.pt b x = x)
    (hτ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ U.space.toSheaf),
      τ.pt b x = x) :
    pushoutFunctorRel (ρ := ρ) (τ := τ) ≅ 𝟭 (ActionTorsor G U T) :=
  NatIso.ofComponents
    (fun P => ⟨pushoutIdActionHom ρ τ hρ hτ P, Groupoid.inv (pushoutIdActionHom ρ τ hρ hτ P),
      Groupoid.comp_inv _, Groupoid.inv_comp _⟩)
    fun φ => pushoutHom_comp_pushoutIdActionHom ρ τ hρ hτ φ

end IdIso

/-! ### The scalar homomorphism at the scalar `1` -/

section ConeScaleOne

open ConeQuotient

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T : Scheme.{u}}

/-- Scaling the vector bundle group by the scalar `1` does nothing. -/
theorem scaleBundleScheme_one {W : Scheme.{u}} (x : W ⟶ bundleScheme σ) (b : W ⟶ T) :
    lift x b ≫ scaleBundleScheme σ (1 : Γ(T, ⊤)) = x := by
  refine coords_injective (funext fun i => ?_)
  rw [coords_comp_scaleBundleScheme, lift_fst, lift_snd, map_one, one_mul]

/-- **The scalar homomorphism at the scalar `1` is the identity on all generalised points.** -/
theorem scaleRelMonHom_pt_one {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T)
    (x : Z ⟶ (vectorBundleGroup σ).space.toSheaf) :
    (scaleRelMonHom σ T (1 : Γ(T, ⊤))).pt b x = x := by
  refine hom_ext_points fun W ω => ?_
  rw [RelMonHom.comp_pt]
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : W ⟶ T, fppfYoneda.map b₀ = ω ≫ b :=
    ⟨fppfYoneda.preimage (ω ≫ b), fppfYoneda.map_preimage _⟩
  obtain ⟨x₀, hx₀⟩ := bdlPt_surjective (σ := σ) (ω ≫ x)
  rw [← hb₀, ← hx₀, scaleRelMonHom_pt, scaleBundleScheme_one]

/-- Contracting the affine cone by the scalar `1` does nothing. -/
theorem scaleConeScheme_one (A : ConeAction R S F) {W : Scheme.{u}} (x : W ⟶ coneScheme S)
    (b : W ⟶ T) : lift x b ≫ scaleConeScheme A (1 : Γ(T, ⊤)) = x := by
  refine conePt_injective ?_
  rw [conePt_comp_scaleConeScheme, lift_fst, lift_snd, map_one, scaleRing_one]

/-- **The cone contraction at the scalar `1` is the identity on all generalised points.** -/
theorem coneScaleRelEquivMap_pt_one (A : ConeAction R S F) (bas : Module.Basis σ R F)
    {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T)
    (x : Z ⟶ (coneActionSpace A bas).space.toSheaf) :
    (coneScaleRelEquivMap A bas (1 : Γ(T, ⊤))).pt b x = x := by
  refine hom_ext_points fun W ω => ?_
  rw [RelEquivMap.comp_pt]
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : W ⟶ T, fppfYoneda.map b₀ = ω ≫ b :=
    ⟨fppfYoneda.preimage (ω ≫ b), fppfYoneda.map_preimage _⟩
  obtain ⟨x₀, hx₀⟩ := cnPt_surjective A bas (ω ≫ x)
  rw [← hb₀, ← hx₀, coneScaleRelEquivMap_pt, scaleConeScheme_one]

end ConeScaleOne

/-! ### The unit point of a relative pushout datum -/

namespace PushoutTorsorRel

variable {G G' G'' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}
  {ρ : RelMonHom G G' T} {ρ' : RelMonHom G' G'' T} {ρ'' : RelMonHom G G'' T}
  {P Q : FppfTorsor G T}

/-- The point of a relative pushout datum over the base of `p` whose evaluation at `p` is the
unit: the image of `p` under the canonical map `P ⟶ ρ_* P`. -/
noncomputable def unitPt (B : PushoutTorsorRel ρ P) {W : Scheme.{u}}
    (p : fppfYoneda.obj W ⟶ P.P) : fppfYoneda.obj W ⟶ B.sheaf :=
  (B.ev_bijective p 1).choose.1

/-- The unit point lies over the same base point as `p`. -/
theorem unitPt_proj (B : PushoutTorsorRel ρ P) {W : Scheme.{u}}
    (p : fppfYoneda.obj W ⟶ P.P) : unitPt B p ≫ B.projection = p ≫ P.projection :=
  (B.ev_bijective p 1).choose.2

/-- The evaluation of the unit point at `p` is the unit. -/
theorem ev_unitPt (B : PushoutTorsorRel ρ P) {W : Scheme.{u}}
    (p : fppfYoneda.obj W ⟶ P.P) : B.ev (unitPt B p) p (unitPt_proj B p) = 1 :=
  (B.ev_bijective p 1).choose_spec.1

/-- **Characterisation of the unit point.** -/
theorem eq_unitPt (B : PushoutTorsorRel ρ P) {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P)
    (β : fppfYoneda.obj W ⟶ B.sheaf) (hβ : β ≫ B.projection = p ≫ P.projection)
    (h : B.ev β p hβ = 1) : β = unitPt B p :=
  B.ev_injective p hβ (unitPt_proj B p) (h.trans (ev_unitPt B p).symm)

/-- The unit point is natural in the test scheme. -/
theorem comp_unitPt (B : PushoutTorsorRel ρ P) {V W : Scheme.{u}} (u : V ⟶ W)
    (p : fppfYoneda.obj W ⟶ P.P) :
    fppfYoneda.map u ≫ unitPt B p = unitPt B (fppfYoneda.map u ≫ p) := by
  have hproj : (fppfYoneda.map u ≫ unitPt B p) ≫ B.projection =
      (fppfYoneda.map u ≫ p) ≫ P.projection := by
    simp only [Category.assoc]
    rw [unitPt_proj]
  refine eq_unitPt B _ _ hproj ?_
  rw [← B.ev_naturality u (unitPt B p) p (unitPt_proj B p) hproj, ev_unitPt, MonObj.comp_one]

/-- **The unit point of a translated point is translated through `ρ`.** -/
theorem unitPt_actPt (B : PushoutTorsorRel ρ P) {W : Scheme.{u}}
    (g : fppfYoneda.obj W ⟶ G.space.toSheaf) (p : fppfYoneda.obj W ⟶ P.P) :
    unitPt B (actPt g p) = actPt (ρ.pt (p ≫ P.projection) g) (unitPt B p) := by
  have hq : unitPt B p ≫ B.projection = actPt g p ≫ P.projection := by
    rw [unitPt_proj, actPt_proj]
  have hp : actPt (ρ.pt (p ≫ P.projection) g) (unitPt B p) ≫ B.projection =
      actPt g p ≫ P.projection := by
    rw [B.actPt_projection]
    exact hq
  refine (eq_unitPt B (actPt g p) _ hp ?_).symm
  rw [B.ev_actPt (ρ.pt (p ≫ P.projection) g) (unitPt B p) (actPt g p) hq hp,
    B.ev_actPt_right g (unitPt B p) p (unitPt_proj B p) hq, ev_unitPt, one_mul, mul_inv_cancel]

/-- **The induced map of relative pushout data, as an arrow of the underlying torsors.** -/
noncomputable def pushFppfHom (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q)
    (φ : P ⟶ Q) : A.toFppfTorsor ⟶ B.toFppfTorsor where
  iso := pushIso A B φ
  over := pushMap_proj A B φ
  equivariant := pushMap_equivariant A B φ

/-- The underlying morphism of sheaves of `pushFppfHom` is `pushMap`. -/
@[simp]
theorem pushFppfHom_iso_hom (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q) :
    (pushFppfHom A B φ).iso.hom = pushMap A B φ :=
  rfl

/-- **The induced map of relative pushout data sends unit points to unit points.** -/
theorem unitPt_comp_pushMap (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q)
    {W : Scheme.{u}} (p : fppfYoneda.obj W ⟶ P.P) :
    unitPt A p ≫ pushMap A B φ = unitPt B (p ≫ φ.iso.hom) := by
  have hproj : (unitPt A p ≫ pushMap A B φ) ≫ B.projection =
      (p ≫ φ.iso.hom) ≫ Q.projection := by
    rw [Category.assoc, pushMap_proj, unitPt_proj, Category.assoc, φ.over]
  refine eq_unitPt B (p ≫ φ.iso.hom) _ hproj ?_
  exact (ev_pushMap A B φ (unitPt A p) p (unitPt_proj A p) hproj).trans (ev_unitPt A p)

/-! ### The iterated relative pushout -/

/-- **The iterated relative pushout is a pushout datum along a homomorphism that is pointwise the
composite.**  If `B` is a pushout datum for `P` along `ρ` and `C` is a pushout datum for `B`
along `ρ'`, then `C` is a pushout datum for `P` along any `ρ''` with
`ρ''.pt b x = ρ'.pt b (ρ.pt b x)`, with evaluation pairing `ev z p := C.ev z (unitPt B p)`. -/
noncomputable def compDatum
    (hcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ''.pt b x = ρ'.pt b (ρ.pt b x))
    (B : PushoutTorsorRel ρ P) (C : PushoutTorsorRel ρ' B.toFppfTorsor) :
    PushoutTorsorRel ρ'' P where
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
    have hB' : z ≫ C.projection =
        actPt (ρ.pt (p ≫ P.projection) g) (unitPt B p) ≫ B.projection :=
      hB.trans (B.actPt_projection (ρ.pt (p ≫ P.projection) g) (unitPt B p)).symm
    refine (C.ev_congr_right z (unitPt_actPt B g p)
      (h'.trans (unitPt_proj B (actPt g p)).symm) hB').trans
      ((C.ev_actPt_right (ρ.pt (p ≫ P.projection) g) z (unitPt B p) hB hB').trans ?_)
    exact congrArg (fun x => C.ev z (unitPt B p) hB * x⁻¹)
      ((ρ'.pt_congr (unitPt_proj B p) rfl).trans (hcomp (p ≫ P.projection) g).symm)
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

/-- The underlying sheaf of the iterated pushout datum is that of the second datum. -/
@[simp]
theorem compDatum_sheaf
    (hcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ''.pt b x = ρ'.pt b (ρ.pt b x))
    (B : PushoutTorsorRel ρ P) (C : PushoutTorsorRel ρ' B.toFppfTorsor) :
    (compDatum hcomp B C).sheaf = C.sheaf :=
  rfl

/-- The evaluation pairing of the iterated pushout datum goes through the unit point. -/
theorem compDatum_ev
    (hcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ''.pt b x = ρ'.pt b (ρ.pt b x))
    (B : PushoutTorsorRel ρ P) (C : PushoutTorsorRel ρ' B.toFppfTorsor) {W : Scheme.{u}}
    (z : fppfYoneda.obj W ⟶ C.sheaf) (p : fppfYoneda.obj W ⟶ P.P)
    (h : z ≫ (compDatum hcomp B C).projection = p ≫ P.projection) :
    (compDatum hcomp B C).ev z p h =
      C.ev z (unitPt B p) (h.trans (unitPt_proj B p).symm) :=
  rfl

/-- **The map of iterated pushout data induced by a morphism of torsors is the iterated induced
map.** -/
theorem pushMap_compDatum
    (hcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ''.pt b x = ρ'.pt b (ρ.pt b x))
    (B : PushoutTorsorRel ρ P) (C : PushoutTorsorRel ρ' B.toFppfTorsor)
    (B' : PushoutTorsorRel ρ Q) (C' : PushoutTorsorRel ρ' B'.toFppfTorsor) (φ : P ⟶ Q) :
    pushMap (compDatum hcomp B C) (compDatum hcomp B' C') φ =
      pushMap C C' (pushFppfHom B B' φ) := by
  refine (eq_pushMap (compDatum hcomp B C) (compDatum hcomp B' C') φ
    (pushMap C C' (pushFppfHom B B' φ)) (pushMap_proj C C' (pushFppfHom B B' φ)) ?_).symm
  intro V β c hc h₁ h₂
  have hu : unitPt B' (coverPt c ≫ φ.iso.hom) =
      unitPt B (coverPt c) ≫ (pushFppfHom B B' φ).iso.hom :=
    (unitPt_comp_pushMap B B' φ (coverPt c)).symm
  have hmid : unitPt B (coverPt c) ≫ B.projection = coverPt c ≫ P.projection :=
    unitPt_proj B (coverPt c)
  have hβ : β ≫ C.projection = unitPt B (coverPt c) ≫ B.projection := h₂.trans hmid.symm
  have h₄ : (β ≫ pushMap C C' (pushFppfHom B B' φ)) ≫ C'.projection =
      (unitPt B (coverPt c) ≫ (pushFppfHom B B' φ).iso.hom) ≫ B'.projection :=
    ((Category.assoc β (pushMap C C' (pushFppfHom B B' φ)) C'.projection).trans
      ((congrArg (fun q => β ≫ q) (pushMap_proj C C' (pushFppfHom B B' φ))).trans hβ)).trans
      ((Category.assoc (unitPt B (coverPt c)) (pushFppfHom B B' φ).iso.hom B'.projection).trans
        (congrArg (fun q => unitPt B (coverPt c) ≫ q) (pushFppfHom B B' φ).over)).symm
  exact (C'.ev_congr_right (β ≫ pushMap C C' (pushFppfHom B B' φ)) hu
      (h₁.trans (unitPt_proj B' (coverPt c ≫ φ.iso.hom)).symm) h₄).trans
    (ev_pushMap C C' (pushFppfHom B B' φ) β (unitPt B (coverPt c)) hβ h₄)

end PushoutTorsorRel

/-! ### The iterated pushout functor -/

section CompIso

variable {G G' G'' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}
  {U : AlgebraicSpaceAction G} {U' : AlgebraicSpaceAction G'} {U'' : AlgebraicSpaceAction G''}
  (ρ : RelMonHom G G' T) (ρ' : RelMonHom G' G'' T) (ρ'' : RelMonHom G G'' T)
  (τ : RelEquivMap ρ U U') (τ' : RelEquivMap ρ' U' U'') (τ'' : RelEquivMap ρ'' U U'')

/-- **The image of a unit point of the intermediate pushout under its map to the action space**
is the contracted point: the evaluation of a unit point is the unit. -/
theorem unitPt_comp_targetMap (P : ActionTorsor G U T) {W : Scheme.{u}}
    (p : fppfYoneda.obj W ⟶ P.P) :
    PushoutTorsorRel.unitPt (pushoutTorsor P.toFppfTorsor ρ) p ≫ targetMap P ρ τ =
      τ.pt (p ≫ P.projection) (p ≫ P.target) := by
  have hmid : PushoutTorsorRel.unitPt (pushoutTorsor P.toFppfTorsor ρ) p ≫
      (pushoutTorsor P.toFppfTorsor ρ).projection = p ≫ P.projection :=
    PushoutTorsorRel.unitPt_proj _ _
  refine Eq.trans (targetMap_eq_actPt (τ := τ)
    (PushoutTorsorRel.unitPt (pushoutTorsor P.toFppfTorsor ρ) p) p hmid) ?_
  refine Eq.trans (congrArg (fun g => actPt g (τ.pt (p ≫ P.projection) (p ≫ P.target)))
    (PushoutTorsorRel.ev_unitPt (pushoutTorsor P.toFppfTorsor ρ) p)) ?_
  exact actPt_one _

/-- **A map out of an arbitrary pushout datum along `ρ''` which satisfies the evaluation formula
of `TorsorPushoutRel.targetMap_eq_actPt` agrees with `targetMap` after the comparison of pushout
data.**  This is the general form of the target compatibility of a coherence isomorphism. -/
theorem cmpMap_comp_targetMap_of_ev (P : ActionTorsor G U T)
    (D : PushoutTorsorRel ρ'' P.toFppfTorsor) (f : D.sheaf ⟶ U''.space.toSheaf)
    (hf : ∀ {W : Scheme.{u}} (z : fppfYoneda.obj W ⟶ D.sheaf) (p : fppfYoneda.obj W ⟶ P.P)
      (h : z ≫ D.projection = p ≫ P.projection),
      z ≫ f = actPt (D.ev z p h) (τ''.pt (p ≫ P.projection) (p ≫ P.target))) :
    PushoutTorsorRel.cmpMap (pushoutTorsor P.toFppfTorsor ρ'') D ≫ f = targetMap P ρ'' τ'' := by
  refine PushoutTorsorRel.hom_ext_of_cmp ?_
  intro W α c hc
  have h' : α ≫ (pushoutTorsor P.toFppfTorsor ρ'').projection = coverPt c ≫ P.projection := by
    rw [hc, coverPt_proj]
  have hD : (α ≫ PushoutTorsorRel.cmpMap (pushoutTorsor P.toFppfTorsor ρ'') D) ≫ D.projection =
      coverPt c ≫ P.projection :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => α ≫ q)
        (PushoutTorsorRel.cmpMap_proj (pushoutTorsor P.toFppfTorsor ρ'') D)).trans h')
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (hf (α ≫ PushoutTorsorRel.cmpMap (pushoutTorsor P.toFppfTorsor ρ'') D)
    (coverPt c) hD) ?_
  refine Eq.trans (congrArg (fun g => actPt g
      (τ''.pt (coverPt c ≫ P.projection) (coverPt c ≫ P.target)))
    (PushoutTorsorRel.ev_cmpMap (pushoutTorsor P.toFppfTorsor ρ'') D α (coverPt c) h' hD)) ?_
  exact (targetMap_eq_actPt (τ := τ'') α (coverPt c) h').symm

/-- **The map to the action space of the iterated pushout satisfies the evaluation formula of
`TorsorPushoutRel.targetMap_eq_actPt` for the iterated pushout datum**, the point of the
intermediate pushout being the unit point. -/
theorem targetMap_comp_eq_actPt
    (hcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ''.pt b x = ρ'.pt b (ρ.pt b x))
    (hτcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ U.space.toSheaf),
      τ''.pt b x = τ'.pt b (τ.pt b x))
    (P : ActionTorsor G U T) {W : Scheme.{u}}
    (z : fppfYoneda.obj W ⟶ (PushoutTorsorRel.compDatum hcomp (pushoutTorsor P.toFppfTorsor ρ)
      (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ')).sheaf)
    (p : fppfYoneda.obj W ⟶ P.P)
    (h : z ≫ (PushoutTorsorRel.compDatum hcomp (pushoutTorsor P.toFppfTorsor ρ)
        (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ')).projection =
      p ≫ P.projection) :
    z ≫ targetMap (pushoutActionTorsor P ρ τ) ρ' τ' =
      actPt ((PushoutTorsorRel.compDatum hcomp (pushoutTorsor P.toFppfTorsor ρ)
          (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ')).ev z p h)
        (τ''.pt (p ≫ P.projection) (p ≫ P.target)) := by
  have hmid : PushoutTorsorRel.unitPt (pushoutTorsor P.toFppfTorsor ρ) p ≫
      (pushoutTorsor P.toFppfTorsor ρ).projection = p ≫ P.projection :=
    PushoutTorsorRel.unitPt_proj _ _
  have h₂ : z ≫ (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ').projection =
      PushoutTorsorRel.unitPt (pushoutTorsor P.toFppfTorsor ρ) p ≫
        (pushoutActionTorsor P ρ τ).projection := h.trans hmid.symm
  refine Eq.trans (targetMap_eq_actPt (P := pushoutActionTorsor P ρ τ) (τ := τ') z
    (PushoutTorsorRel.unitPt (pushoutTorsor P.toFppfTorsor ρ) p) h₂) ?_
  refine congrArg (actPt ((PushoutTorsorRel.compDatum hcomp (pushoutTorsor P.toFppfTorsor ρ)
    (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ')).ev z p h)) ?_
  exact (τ'.pt_congr hmid (unitPt_comp_targetMap ρ τ P p)).trans (hτcomp _ _).symm

/-- **The comparison of the pushout along a pointwise composite with the iterated pushout is
compatible with the maps to the action space.** -/
theorem cmpMap_compDatum_comp_target
    (hcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ''.pt b x = ρ'.pt b (ρ.pt b x))
    (hτcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ U.space.toSheaf),
      τ''.pt b x = τ'.pt b (τ.pt b x))
    (P : ActionTorsor G U T) :
    PushoutTorsorRel.cmpMap (pushoutTorsor P.toFppfTorsor ρ'')
        (PushoutTorsorRel.compDatum hcomp (pushoutTorsor P.toFppfTorsor ρ)
          (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ')) ≫
        targetMap (pushoutActionTorsor P ρ τ) ρ' τ' = targetMap P ρ'' τ'' :=
  cmpMap_comp_targetMap_of_ev ρ'' τ'' P
    (PushoutTorsorRel.compDatum hcomp (pushoutTorsor P.toFppfTorsor ρ)
      (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ'))
    (targetMap (pushoutActionTorsor P ρ τ) ρ' τ')
    fun z p h => targetMap_comp_eq_actPt ρ ρ' ρ'' τ τ' τ'' hcomp hτcomp P z p h

/-- **The comparison of the pushout along a pointwise composite with the iterated pushout**, as
an arrow of the quotient-stack fibre. -/
noncomputable def pushoutCompActionHom
    (hcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ''.pt b x = ρ'.pt b (ρ.pt b x))
    (hτcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ U.space.toSheaf),
      τ''.pt b x = τ'.pt b (τ.pt b x))
    (P : ActionTorsor G U T) :
    pushoutActionTorsor P ρ'' τ'' ⟶
      pushoutActionTorsor (pushoutActionTorsor P ρ τ) ρ' τ' where
  iso := PushoutTorsorRel.compareIso (pushoutTorsor P.toFppfTorsor ρ'')
    (PushoutTorsorRel.compDatum hcomp (pushoutTorsor P.toFppfTorsor ρ)
      (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ'))
  over := PushoutTorsorRel.cmpMap_proj (pushoutTorsor P.toFppfTorsor ρ'')
    (PushoutTorsorRel.compDatum hcomp (pushoutTorsor P.toFppfTorsor ρ)
      (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ'))
  equivariant := PushoutTorsorRel.cmpMap_equivariant (pushoutTorsor P.toFppfTorsor ρ'')
    (PushoutTorsorRel.compDatum hcomp (pushoutTorsor P.toFppfTorsor ρ)
      (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ'))
  target := cmpMap_compDatum_comp_target ρ ρ' ρ'' τ τ' τ'' hcomp hτcomp P

/-- **Naturality of the comparison of the pushout along a pointwise composite with the iterated
pushout**: both composites are the map induced by `φ` from the pushout datum of `P` along `ρ''`
to the iterated pushout datum of `Q`. -/
theorem pushoutHom_comp_pushoutCompActionHom
    (hcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ''.pt b x = ρ'.pt b (ρ.pt b x))
    (hτcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ U.space.toSheaf),
      τ''.pt b x = τ'.pt b (τ.pt b x))
    {P Q : ActionTorsor G U T} (φ : P ⟶ Q) :
    pushoutHom (ρ := ρ'') (τ := τ'') φ ≫
        pushoutCompActionHom ρ ρ' ρ'' τ τ' τ'' hcomp hτcomp Q =
      pushoutCompActionHom ρ ρ' ρ'' τ τ' τ'' hcomp hτcomp P ≫
        pushoutHom (ρ := ρ') (τ := τ') (pushoutHom (ρ := ρ) (τ := τ) φ) := by
  refine ActionTorsor.Hom.ext _ _ ?_
  have h1 : PushoutTorsorRel.pushMap (pushoutTorsor P.toFppfTorsor ρ'')
        (pushoutTorsor Q.toFppfTorsor ρ'') (ActionTorsor.Hom.toFppfHom φ) ≫
        PushoutTorsorRel.cmpMap (pushoutTorsor Q.toFppfTorsor ρ'')
          (PushoutTorsorRel.compDatum hcomp (pushoutTorsor Q.toFppfTorsor ρ)
            (pushoutTorsor (pushoutActionTorsor Q ρ τ).toFppfTorsor ρ')) =
      PushoutTorsorRel.pushMap (pushoutTorsor P.toFppfTorsor ρ'')
        (PushoutTorsorRel.compDatum hcomp (pushoutTorsor Q.toFppfTorsor ρ)
          (pushoutTorsor (pushoutActionTorsor Q ρ τ).toFppfTorsor ρ'))
        (ActionTorsor.Hom.toFppfHom φ) :=
    PushoutTorsorRel.pushMap_comp_cmpMap _ _ _ _
  have hhom : ActionTorsor.Hom.toFppfHom (pushoutHom (ρ := ρ) (τ := τ) φ) =
      PushoutTorsorRel.pushFppfHom (pushoutTorsor P.toFppfTorsor ρ)
        (pushoutTorsor Q.toFppfTorsor ρ) (ActionTorsor.Hom.toFppfHom φ) :=
    FppfTorsor.Hom.ext _ _ rfl
  have h2 : PushoutTorsorRel.cmpMap (pushoutTorsor P.toFppfTorsor ρ'')
        (PushoutTorsorRel.compDatum hcomp (pushoutTorsor P.toFppfTorsor ρ)
          (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ')) ≫
        PushoutTorsorRel.pushMap
          (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ')
          (pushoutTorsor (pushoutActionTorsor Q ρ τ).toFppfTorsor ρ')
          (ActionTorsor.Hom.toFppfHom (pushoutHom (ρ := ρ) (τ := τ) φ)) =
      PushoutTorsorRel.pushMap (pushoutTorsor P.toFppfTorsor ρ'')
        (PushoutTorsorRel.compDatum hcomp (pushoutTorsor Q.toFppfTorsor ρ)
          (pushoutTorsor (pushoutActionTorsor Q ρ τ).toFppfTorsor ρ'))
        (ActionTorsor.Hom.toFppfHom φ) := by
    refine Eq.trans ?_ (PushoutTorsorRel.cmpMap_comp_pushMap
      (pushoutTorsor P.toFppfTorsor ρ'')
      (PushoutTorsorRel.compDatum hcomp (pushoutTorsor P.toFppfTorsor ρ)
        (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ'))
      (PushoutTorsorRel.compDatum hcomp (pushoutTorsor Q.toFppfTorsor ρ)
        (pushoutTorsor (pushoutActionTorsor Q ρ τ).toFppfTorsor ρ'))
      (ActionTorsor.Hom.toFppfHom φ))
    refine congrArg (fun q => PushoutTorsorRel.cmpMap (pushoutTorsor P.toFppfTorsor ρ'')
      (PushoutTorsorRel.compDatum hcomp (pushoutTorsor P.toFppfTorsor ρ)
        (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ')) ≫ q) ?_
    refine Eq.trans (congrArg (fun w => PushoutTorsorRel.pushMap
      (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ')
      (pushoutTorsor (pushoutActionTorsor Q ρ τ).toFppfTorsor ρ') w) hhom) ?_
    exact (PushoutTorsorRel.pushMap_compDatum hcomp (pushoutTorsor P.toFppfTorsor ρ)
      (pushoutTorsor (pushoutActionTorsor P ρ τ).toFppfTorsor ρ')
      (pushoutTorsor Q.toFppfTorsor ρ)
      (pushoutTorsor (pushoutActionTorsor Q ρ τ).toFppfTorsor ρ')
      (ActionTorsor.Hom.toFppfHom φ)).symm
  exact h1.trans h2.symm

/-- **The pushout along a relative homomorphism that is pointwise the composite of `ρ` and `ρ'`
is the iterated pushout.**  This is the multiplicativity coherence isomorphism of a contraction,
in the generality of `pushoutFunctorRel`. -/
noncomputable def pushoutFunctorRelCompIso
    (hcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ''.pt b x = ρ'.pt b (ρ.pt b x))
    (hτcomp : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ U.space.toSheaf),
      τ''.pt b x = τ'.pt b (τ.pt b x)) :
    pushoutFunctorRel (ρ := ρ'') (τ := τ'') ≅
      pushoutFunctorRel (ρ := ρ) (τ := τ) ⋙ pushoutFunctorRel (ρ := ρ') (τ := τ') :=
  NatIso.ofComponents
    (fun P => ⟨pushoutCompActionHom ρ ρ' ρ'' τ τ' τ'' hcomp hτcomp P,
      Groupoid.inv (pushoutCompActionHom ρ ρ' ρ'' τ τ' τ'' hcomp hτcomp P),
      Groupoid.comp_inv _, Groupoid.inv_comp _⟩)
    fun φ => pushoutHom_comp_pushoutCompActionHom ρ ρ' ρ'' τ τ' τ'' hcomp hτcomp φ

end CompIso

/-! ### Base change of relative homomorphisms and of relative pushout data -/

section BaseChange

variable {G G' : AlgebraicSpaceGroup.{u}} {T T' : Scheme.{u}}
  {U : AlgebraicSpaceAction G} {U' : AlgebraicSpaceAction G'}

/-- **Base change of a relative homomorphism** along `b : T' ⟶ T`: a homomorphism relative to
`T` restricts to one relative to `T'`.  (The constructions below only use the pointwise property
`RelMonHom.pullback_pt`, so that they also apply to homomorphisms over `T'` which are merely
pointwise equal to this one, such as the scalar homomorphism of a pulled-back scalar.) -/
noncomputable def RelMonHom.pullback (ρ : RelMonHom G G' T) (b : T' ⟶ T) :
    RelMonHom G G' T' where
  toFun := (G.space.toSheaf ◁ fppfYoneda.map b) ≫ ρ.toFun
  map_one' b' := by
    rw [← Category.assoc, ConeQuotient.lift_whiskerLeft]
    exact ρ.map_one' (b' ≫ fppfYoneda.map b)
  map_mul' b' x y := by
    simp only [← Category.assoc, ConeQuotient.lift_whiskerLeft]
    exact ρ.map_mul' (b' ≫ fppfYoneda.map b) x y

/-- The base-changed relative homomorphism is computed by composing the base point with `b`. -/
theorem RelMonHom.pullback_pt (ρ : RelMonHom G G' T) (b : T' ⟶ T) {Z : FppfSheaf.{u}}
    (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ G.space.toSheaf) :
    (ρ.pullback b).pt b' x = ρ.pt (b' ≫ fppfYoneda.map b) x :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ ρ.toFun) (ConeQuotient.lift_whiskerLeft x b' (fppfYoneda.map b)))

/-- **Base change of a relative equivariant map** along `b : T' ⟶ T`. -/
noncomputable def RelEquivMap.pullback {ρ : RelMonHom G G' T} (τ : RelEquivMap ρ U U')
    (b : T' ⟶ T) : RelEquivMap (ρ.pullback b) U U' where
  toFun := (U.space.toSheaf ◁ fppfYoneda.map b) ≫ τ.toFun
  equivariant' b' g x := by
    rw [RelMonHom.pullback_pt, ← Category.assoc, ← Category.assoc,
      ConeQuotient.lift_whiskerLeft, ConeQuotient.lift_whiskerLeft]
    exact τ.equivariant' (b' ≫ fppfYoneda.map b) g x

/-- The base-changed relative equivariant map is computed by composing the base point with `b`. -/
theorem RelEquivMap.pullback_pt {ρ : RelMonHom G G' T} (τ : RelEquivMap ρ U U') (b : T' ⟶ T)
    {Z : FppfSheaf.{u}} (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ U.space.toSheaf) :
    (τ.pullback b).pt b' x = τ.pt (b' ≫ fppfYoneda.map b) x :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ τ.toFun) (ConeQuotient.lift_whiskerLeft x b' (fppfYoneda.map b)))

-- The action on a base-changed torsor is not a global instance; make it one here so that the
-- statements below about points of base-changed torsors elaborate.
attribute [local instance] FppfTorsor.pullbackAction

namespace PushoutTorsorRel

variable {ρ : RelMonHom G G' T} {ρ' : RelMonHom G G' T'} {P Q : FppfTorsor G T}

/-- Two points of base-changed torsors lying over the same point of the new base have first
projections lying over the same point of the old base. -/
theorem pullback_ev_cond (A : PushoutTorsorRel ρ P) (b : T' ⟶ T) {W : Scheme.{u}}
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

/-- The base point of a point of a base-changed torsor, read in the old base. -/
theorem pullback_base_cond (b : T' ⟶ T) {W : Scheme.{u}}
    (p : fppfYoneda.obj W ⟶ (P.pullbackTorsor b).P) :
    (p ≫ (P.pullbackTorsor b).projection) ≫ fppfYoneda.map b =
      (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ P.projection := by
  rw [Category.assoc, Category.assoc, ← Limits.pullback.condition]

/-- **The base change of a relative pushout datum.**  If `A` is a pushout datum for the
`G`-torsor `P` along `ρ`, then its base change along `b : T' ⟶ T` is a pushout datum for the base
change of `P` along any homomorphism `ρ'` over `T'` which is pointwise the base change of `ρ`
(for instance `ρ.pullback b`): a point of `b^* (ρ_* P)` evaluates at a point of `b^* P` through
their first projections. -/
noncomputable def pullbackDatum (b : T' ⟶ T)
    (hpull : ∀ {Z : FppfSheaf.{u}} (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ G.space.toSheaf),
      ρ'.pt b' x = ρ.pt (b' ≫ fppfYoneda.map b) x)
    (A : PushoutTorsorRel ρ P) : PushoutTorsorRel ρ' (P.pullbackTorsor b) where
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
    refine (A.ev_congr
      (TorsorPushout.PushoutTorsor.actPt_pullback_fst A.toFppfTorsor b g' α) rfl
      (pullback_ev_cond A b (actPt g' α) p h') ?_).trans
      (A.ev_actPt g' (α ≫ Limits.pullback.fst A.toFppfTorsor.projection (fppfYoneda.map b))
        (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))
        (pullback_ev_cond A b α p h) ?_)
    · exact (A.actPt_projection g' _).trans (pullback_ev_cond A b α p h)
    · exact (A.actPt_projection g' _).trans (pullback_ev_cond A b α p h)
  ev_actPt_right := by
    intro W g α p h h'
    have hcond : ρ.pt ((p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫
          P.projection) g =
        ρ'.pt (p ≫ (P.pullbackTorsor b).projection) g :=
      ((hpull (p ≫ (P.pullbackTorsor b).projection) g).trans
        (ρ.pt_congr (pullback_base_cond b p) rfl)).symm
    refine (A.ev_congr rfl (TorsorPushout.PushoutTorsor.actPt_pullback_fst P b g p)
      (pullback_ev_cond A b α (actPt g p) h') ?_).trans
      ((A.ev_actPt_right g (α ≫ Limits.pullback.fst A.toFppfTorsor.projection (fppfYoneda.map b))
        (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))
        (pullback_ev_cond A b α p h) ?_).trans ?_)
    · exact (pullback_ev_cond A b α p h).trans
        (actPt_proj P g (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))).symm
    · exact (pullback_ev_cond A b α p h).trans
        (actPt_proj P g (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))).symm
    · exact congrArg (fun q => A.ev (α ≫ Limits.pullback.fst A.toFppfTorsor.projection
        (fppfYoneda.map b)) (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))
        (pullback_ev_cond A b α p h) * q⁻¹) hcond
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

/-- The evaluation pairing of the base-changed pushout datum goes through the first
projections. -/
theorem pullbackDatum_ev (b : T' ⟶ T)
    (hpull : ∀ {Z : FppfSheaf.{u}} (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ G.space.toSheaf),
      ρ'.pt b' x = ρ.pt (b' ≫ fppfYoneda.map b) x)
    (A : PushoutTorsorRel ρ P) {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ (pullbackDatum b hpull A).sheaf)
    (p : fppfYoneda.obj W ⟶ (P.pullbackTorsor b).P)
    (h : α ≫ (pullbackDatum b hpull A).projection = p ≫ (P.pullbackTorsor b).projection) :
    (pullbackDatum b hpull A).ev α p h =
      A.ev (α ≫ Limits.pullback.fst A.toFppfTorsor.projection (fppfYoneda.map b))
        (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))
        (pullback_ev_cond A b α p h) :=
  rfl

/-- **The base change of the induced map of pushout data is the induced map of the base-changed
pushout data.** -/
theorem pushMap_pullbackDatum (b : T' ⟶ T)
    (hpull : ∀ {Z : FppfSheaf.{u}} (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ G.space.toSheaf),
      ρ'.pt b' x = ρ.pt (b' ≫ fppfYoneda.map b) x)
    (A : PushoutTorsorRel ρ P) (B : PushoutTorsorRel ρ Q) (φ : P ⟶ Q)
    (φ' : P.pullbackTorsor b ⟶ Q.pullbackTorsor b)
    (hφ' : φ'.iso.hom = FppfTorsor.pullbackMap b φ.iso.hom φ.over) :
    pushMap (pullbackDatum b hpull A) (pullbackDatum b hpull B) φ' =
      FppfTorsor.pullbackMap b (pushMap A B φ) (pushMap_proj A B φ) := by
  refine (eq_pushMap (pullbackDatum b hpull A) (pullbackDatum b hpull B) φ'
    (FppfTorsor.pullbackMap b (pushMap A B φ) (pushMap_proj A B φ)) ?_ ?_).symm
  · exact FppfTorsor.pullbackMap_snd (P := A.toFppfTorsor) (Q := B.toFppfTorsor) b
      (pushMap A B φ) (pushMap_proj A B φ)
  · intro V β c hc h₁ h₂
    have hfst : (β ≫ FppfTorsor.pullbackMap (P := A.toFppfTorsor) (Q := B.toFppfTorsor) b
          (pushMap A B φ) (pushMap_proj A B φ)) ≫
        Limits.pullback.fst B.toFppfTorsor.projection (fppfYoneda.map b) =
        (β ≫ Limits.pullback.fst A.toFppfTorsor.projection (fppfYoneda.map b)) ≫
          pushMap A B φ :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => β ≫ q)
          (FppfTorsor.pullbackMap_fst (P := A.toFppfTorsor) (Q := B.toFppfTorsor) b
            (pushMap A B φ) (pushMap_proj A B φ))).trans (Category.assoc _ _ _).symm)
    have hpt : (coverPt c ≫ φ'.iso.hom) ≫
        Limits.pullback.fst Q.projection (fppfYoneda.map b) =
        (coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ φ.iso.hom := by
      rw [hφ', Category.assoc, FppfTorsor.pullbackMap_fst, Category.assoc]
    have hA : (β ≫ Limits.pullback.fst A.toFppfTorsor.projection (fppfYoneda.map b)) ≫
        A.projection =
        (coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ P.projection :=
      pullback_ev_cond A b β (coverPt c) h₂
    have hB : ((β ≫ Limits.pullback.fst A.toFppfTorsor.projection (fppfYoneda.map b)) ≫
          pushMap A B φ) ≫ B.projection =
        ((coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ φ.iso.hom) ≫
          Q.projection :=
      ((Category.assoc _ _ _).trans
        ((congrArg (fun q => (β ≫ Limits.pullback.fst A.toFppfTorsor.projection
          (fppfYoneda.map b)) ≫ q) (pushMap_proj A B φ)).trans hA)).trans
        ((Category.assoc (coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b))
          φ.iso.hom Q.projection).trans
          (congrArg (fun q => (coverPt c ≫ Limits.pullback.fst P.projection
            (fppfYoneda.map b)) ≫ q) φ.over)).symm
    refine Eq.trans (B.ev_congr hfst hpt ?_ hB) ?_
    · exact pullback_ev_cond B b (β ≫ FppfTorsor.pullbackMap (P := A.toFppfTorsor)
        (Q := B.toFppfTorsor) b (pushMap A B φ) (pushMap_proj A B φ))
        (coverPt c ≫ φ'.iso.hom) h₁
    · exact ev_pushMap A B φ
        (β ≫ Limits.pullback.fst A.toFppfTorsor.projection (fppfYoneda.map b))
        (coverPt c ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) hA hB

end PushoutTorsorRel

/-! ### The pushout functor commutes with base change -/

variable (ρ : RelMonHom G G' T) (ρ' : RelMonHom G G' T') (τ : RelEquivMap ρ U U')
  (τ' : RelEquivMap ρ' U U') (b : T' ⟶ T)

/-- **The base-change comparison of the pushout is compatible with the maps to the action
space.** -/
theorem cmpMap_pullbackDatum_comp_target
    (hpull : ∀ {Z : FppfSheaf.{u}} (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ G.space.toSheaf),
      ρ'.pt b' x = ρ.pt (b' ≫ fppfYoneda.map b) x)
    (hτpull : ∀ {Z : FppfSheaf.{u}} (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ U.space.toSheaf),
      τ'.pt b' x = τ.pt (b' ≫ fppfYoneda.map b) x)
    (P : ActionTorsor G U T) :
    PushoutTorsorRel.cmpMap (pushoutTorsor (ActionTorsor.pullbackObj b P).toFppfTorsor ρ')
        (PushoutTorsorRel.pullbackDatum b hpull (pushoutTorsor P.toFppfTorsor ρ)) ≫
        (ActionTorsor.pullbackObj b (pushoutActionTorsor P ρ τ)).target =
      targetMap (ActionTorsor.pullbackObj b P) ρ' τ' := by
  refine cmpMap_comp_targetMap_of_ev ρ' τ' (ActionTorsor.pullbackObj b P)
    (PushoutTorsorRel.pullbackDatum b hpull (pushoutTorsor P.toFppfTorsor ρ))
    (ActionTorsor.pullbackObj b (pushoutActionTorsor P ρ τ)).target ?_
  intro W z p h
  have hcond : (z ≫ Limits.pullback.fst
        (pushoutTorsor P.toFppfTorsor ρ).toFppfTorsor.projection (fppfYoneda.map b)) ≫
      (pushoutTorsor P.toFppfTorsor ρ).toFppfTorsor.projection =
      (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ P.projection :=
    PushoutTorsorRel.pullback_ev_cond (pushoutTorsor P.toFppfTorsor ρ) b z p h
  have hsecond : τ'.pt (p ≫ (ActionTorsor.pullbackObj b P).projection)
        (p ≫ (ActionTorsor.pullbackObj b P).target) =
      τ.pt ((p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ P.projection)
        ((p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) ≫ P.target) :=
    (hτpull (p ≫ (ActionTorsor.pullbackObj b P).projection)
      (p ≫ (ActionTorsor.pullbackObj b P).target)).trans
      (τ.pt_congr (PushoutTorsorRel.pullback_base_cond b p)
        (Category.assoc p (Limits.pullback.fst P.projection (fppfYoneda.map b)) P.target).symm)
  refine Eq.trans (Category.assoc z _ _).symm ?_
  refine Eq.trans (targetMap_eq_actPt (τ := τ) (z ≫ Limits.pullback.fst
      (pushoutTorsor P.toFppfTorsor ρ).toFppfTorsor.projection (fppfYoneda.map b))
    (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) hcond) ?_
  exact congrArg (fun q => actPt (evPt P.toFppfTorsor ρ (z ≫ Limits.pullback.fst
    (pushoutTorsor P.toFppfTorsor ρ).toFppfTorsor.projection (fppfYoneda.map b))
    (p ≫ Limits.pullback.fst P.projection (fppfYoneda.map b)) hcond) q) hsecond.symm

/-- **The base-change comparison of the pushout**, as an arrow of the quotient-stack fibre over
`T'`. -/
noncomputable def pushoutPullbackActionHom
    (hpull : ∀ {Z : FppfSheaf.{u}} (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ G.space.toSheaf),
      ρ'.pt b' x = ρ.pt (b' ≫ fppfYoneda.map b) x)
    (hτpull : ∀ {Z : FppfSheaf.{u}} (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ U.space.toSheaf),
      τ'.pt b' x = τ.pt (b' ≫ fppfYoneda.map b) x)
    (P : ActionTorsor G U T) :
    pushoutActionTorsor (ActionTorsor.pullbackObj b P) ρ' τ' ⟶
      ActionTorsor.pullbackObj b (pushoutActionTorsor P ρ τ) where
  iso := PushoutTorsorRel.compareIso
    (pushoutTorsor (ActionTorsor.pullbackObj b P).toFppfTorsor ρ')
    (PushoutTorsorRel.pullbackDatum b hpull (pushoutTorsor P.toFppfTorsor ρ))
  over := PushoutTorsorRel.cmpMap_proj
    (pushoutTorsor (ActionTorsor.pullbackObj b P).toFppfTorsor ρ')
    (PushoutTorsorRel.pullbackDatum b hpull (pushoutTorsor P.toFppfTorsor ρ))
  equivariant := PushoutTorsorRel.cmpMap_equivariant
    (pushoutTorsor (ActionTorsor.pullbackObj b P).toFppfTorsor ρ')
    (PushoutTorsorRel.pullbackDatum b hpull (pushoutTorsor P.toFppfTorsor ρ))
  target := cmpMap_pullbackDatum_comp_target ρ ρ' τ τ' b hpull hτpull P

/-- **Naturality of the base-change comparison of the pushout**: both composites are the map
induced by the base change of `φ` from the pushout datum of `b^* P` to the base change of the
pushout datum of `Q`. -/
theorem pushoutHom_comp_pushoutPullbackActionHom
    (hpull : ∀ {Z : FppfSheaf.{u}} (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ G.space.toSheaf),
      ρ'.pt b' x = ρ.pt (b' ≫ fppfYoneda.map b) x)
    (hτpull : ∀ {Z : FppfSheaf.{u}} (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ U.space.toSheaf),
      τ'.pt b' x = τ.pt (b' ≫ fppfYoneda.map b) x)
    {P Q : ActionTorsor G U T} (φ : P ⟶ Q) :
    pushoutHom (ρ := ρ') (τ := τ') ((ActionTorsor.pullbackFunctor b).map φ) ≫
        pushoutPullbackActionHom ρ ρ' τ τ' b hpull hτpull Q =
      pushoutPullbackActionHom ρ ρ' τ τ' b hpull hτpull P ≫
        (ActionTorsor.pullbackFunctor b).map (pushoutHom (ρ := ρ) (τ := τ) φ) := by
  refine ActionTorsor.Hom.ext _ _ ?_
  have h1 : PushoutTorsorRel.pushMap
        (pushoutTorsor (ActionTorsor.pullbackObj b P).toFppfTorsor ρ')
        (pushoutTorsor (ActionTorsor.pullbackObj b Q).toFppfTorsor ρ')
        (ActionTorsor.Hom.toFppfHom ((ActionTorsor.pullbackFunctor b).map φ)) ≫
        PushoutTorsorRel.cmpMap
          (pushoutTorsor (ActionTorsor.pullbackObj b Q).toFppfTorsor ρ')
          (PushoutTorsorRel.pullbackDatum b hpull (pushoutTorsor Q.toFppfTorsor ρ)) =
      PushoutTorsorRel.pushMap
        (pushoutTorsor (ActionTorsor.pullbackObj b P).toFppfTorsor ρ')
        (PushoutTorsorRel.pullbackDatum b hpull (pushoutTorsor Q.toFppfTorsor ρ))
        (ActionTorsor.Hom.toFppfHom ((ActionTorsor.pullbackFunctor b).map φ)) :=
    PushoutTorsorRel.pushMap_comp_cmpMap _ _ _ _
  have hφ' : (ActionTorsor.Hom.toFppfHom ((ActionTorsor.pullbackFunctor b).map φ)).iso.hom =
      FppfTorsor.pullbackMap b (ActionTorsor.Hom.toFppfHom φ).iso.hom
        (ActionTorsor.Hom.toFppfHom φ).over :=
    rfl
  have h2 : PushoutTorsorRel.cmpMap
        (pushoutTorsor (ActionTorsor.pullbackObj b P).toFppfTorsor ρ')
        (PushoutTorsorRel.pullbackDatum b hpull (pushoutTorsor P.toFppfTorsor ρ)) ≫
        FppfTorsor.pullbackMap (P := (pushoutTorsor P.toFppfTorsor ρ).toFppfTorsor)
          (Q := (pushoutTorsor Q.toFppfTorsor ρ).toFppfTorsor) b
          (PushoutTorsorRel.pushMap (pushoutTorsor P.toFppfTorsor ρ)
            (pushoutTorsor Q.toFppfTorsor ρ) (ActionTorsor.Hom.toFppfHom φ))
          (PushoutTorsorRel.pushMap_proj (pushoutTorsor P.toFppfTorsor ρ)
            (pushoutTorsor Q.toFppfTorsor ρ) (ActionTorsor.Hom.toFppfHom φ)) =
      PushoutTorsorRel.pushMap
        (pushoutTorsor (ActionTorsor.pullbackObj b P).toFppfTorsor ρ')
        (PushoutTorsorRel.pullbackDatum b hpull (pushoutTorsor Q.toFppfTorsor ρ))
        (ActionTorsor.Hom.toFppfHom ((ActionTorsor.pullbackFunctor b).map φ)) := by
    refine Eq.trans ?_ (PushoutTorsorRel.cmpMap_comp_pushMap
      (pushoutTorsor (ActionTorsor.pullbackObj b P).toFppfTorsor ρ')
      (PushoutTorsorRel.pullbackDatum b hpull (pushoutTorsor P.toFppfTorsor ρ))
      (PushoutTorsorRel.pullbackDatum b hpull (pushoutTorsor Q.toFppfTorsor ρ))
      (ActionTorsor.Hom.toFppfHom ((ActionTorsor.pullbackFunctor b).map φ)))
    refine congrArg (fun q => PushoutTorsorRel.cmpMap
      (pushoutTorsor (ActionTorsor.pullbackObj b P).toFppfTorsor ρ')
      (PushoutTorsorRel.pullbackDatum b hpull (pushoutTorsor P.toFppfTorsor ρ)) ≫ q) ?_
    exact (PushoutTorsorRel.pushMap_pullbackDatum b hpull (pushoutTorsor P.toFppfTorsor ρ)
      (pushoutTorsor Q.toFppfTorsor ρ) (ActionTorsor.Hom.toFppfHom φ)
      (ActionTorsor.Hom.toFppfHom ((ActionTorsor.pullbackFunctor b).map φ)) hφ').symm
  exact h1.trans h2.symm

/-- **The pushout functor commutes with base change.**  For a relative homomorphism `ρ'` over
`T'` which is pointwise the base change of `ρ`, and likewise for the equivariant maps, base
change along `b` intertwines the two pushout functors. -/
noncomputable def pushoutFunctorRelPullbackIso
    (hpull : ∀ {Z : FppfSheaf.{u}} (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ G.space.toSheaf),
      ρ'.pt b' x = ρ.pt (b' ≫ fppfYoneda.map b) x)
    (hτpull : ∀ {Z : FppfSheaf.{u}} (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ U.space.toSheaf),
      τ'.pt b' x = τ.pt (b' ≫ fppfYoneda.map b) x) :
    ActionTorsor.pullbackFunctor b ⋙ pushoutFunctorRel (ρ := ρ') (τ := τ') ≅
      pushoutFunctorRel (ρ := ρ) (τ := τ) ⋙ ActionTorsor.pullbackFunctor b :=
  NatIso.ofComponents
    (fun P => ⟨pushoutPullbackActionHom ρ ρ' τ τ' b hpull hτpull P,
      Groupoid.inv (pushoutPullbackActionHom ρ ρ' τ τ' b hpull hτpull P),
      Groupoid.comp_inv _, Groupoid.inv_comp _⟩)
    fun φ => pushoutHom_comp_pushoutPullbackActionHom ρ ρ' τ τ' b hpull hτpull φ

end BaseChange

/-! ### The scalar homomorphism at a product of scalars -/

section ConeScaleMul

open ConeQuotient

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T : Scheme.{u}}

/-- Scaling the vector bundle group by a product is scaling twice. -/
theorem scaleBundleScheme_mul (r s : Γ(T, ⊤)) {W : Scheme.{u}} (x : W ⟶ bundleScheme σ)
    (b : W ⟶ T) :
    lift x b ≫ scaleBundleScheme σ (r * s) =
      lift (lift x b ≫ scaleBundleScheme σ s) b ≫ scaleBundleScheme σ r := by
  refine coords_injective (funext fun i => ?_)
  simp only [coords_comp_scaleBundleScheme, lift_fst, lift_snd, map_mul]
  ring

/-- **The scalar homomorphism at a product of scalars is the composite of the two scalar
homomorphisms, on all generalised points.** -/
theorem scaleRelMonHom_pt_mul (r s : Γ(T, ⊤)) {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T)
    (x : Z ⟶ (vectorBundleGroup σ).space.toSheaf) :
    (scaleRelMonHom σ T (r * s)).pt b x =
      (scaleRelMonHom σ T r).pt b ((scaleRelMonHom σ T s).pt b x) := by
  refine hom_ext_points fun W ω => ?_
  simp only [RelMonHom.comp_pt]
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : W ⟶ T, fppfYoneda.map b₀ = ω ≫ b :=
    ⟨fppfYoneda.preimage (ω ≫ b), fppfYoneda.map_preimage _⟩
  obtain ⟨x₀, hx₀⟩ := bdlPt_surjective (σ := σ) (ω ≫ x)
  rw [← hb₀, ← hx₀, scaleRelMonHom_pt, scaleRelMonHom_pt, scaleRelMonHom_pt,
    scaleBundleScheme_mul]

/-- Contracting the affine cone by a product of scalars is contracting twice. -/
theorem scaleConeScheme_mul (A : ConeAction R S F) (r s : Γ(T, ⊤)) {W : Scheme.{u}}
    (x : W ⟶ coneScheme S) (b : W ⟶ T) :
    lift x b ≫ scaleConeScheme A (r * s) =
      lift (lift x b ≫ scaleConeScheme A s) b ≫ scaleConeScheme A r := by
  refine conePt_injective ?_
  simp only [conePt_comp_scaleConeScheme, lift_fst, lift_snd, map_mul]
  rw [scaleRing_scaleRing, mul_comm]

/-- **The cone contraction at a product of scalars is the composite of the two contractions, on
all generalised points.** -/
theorem coneScaleRelEquivMap_pt_mul (A : ConeAction R S F) (bas : Module.Basis σ R F)
    (r s : Γ(T, ⊤)) {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T)
    (x : Z ⟶ (coneActionSpace A bas).space.toSheaf) :
    (coneScaleRelEquivMap A bas (r * s)).pt b x =
      (coneScaleRelEquivMap A bas r).pt b ((coneScaleRelEquivMap A bas s).pt b x) := by
  refine hom_ext_points fun W ω => ?_
  simp only [RelEquivMap.comp_pt]
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : W ⟶ T, fppfYoneda.map b₀ = ω ≫ b :=
    ⟨fppfYoneda.preimage (ω ≫ b), fppfYoneda.map_preimage _⟩
  obtain ⟨x₀, hx₀⟩ := cnPt_surjective A bas (ω ≫ x)
  rw [← hb₀, ← hx₀, coneScaleRelEquivMap_pt, coneScaleRelEquivMap_pt, coneScaleRelEquivMap_pt,
    scaleConeScheme_mul]

end ConeScaleMul

/-! ### The pushout along a pointwise trivial homomorphism -/

section TrivialHom

variable {G G' : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}

namespace PushoutTorsorRel

/-- **The trivial `G'`-torsor is a pushout datum of any `G`-torsor along a relative homomorphism
which is trivial on points**, the evaluation pairing being the first coordinate (it does not
depend on the point of `P` at all, because the homomorphism is trivial). -/
noncomputable def trivialDatum (ρ : RelMonHom G G' T)
    (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ.pt b x = 1)
    (P : FppfTorsor G T) : PushoutTorsorRel ρ P where
  sheaf := G'.space.toSheaf ⊗ fppfYoneda.obj T
  action := FppfTorsor.trivialAction G' T
  projection := snd _ _
  action_over := FppfTorsor.trivialSmul_snd G' T
  ev := fun {_} α _ _ => α ≫ fst _ _
  ev_naturality u α p h h' := (Category.assoc _ _ _).symm
  ev_actPt := by
    intro W g' α p h h'
    refine Eq.trans (Category.assoc (lift g' α) (FppfTorsor.trivialSmul G' T)
      (fst G'.space.toSheaf (fppfYoneda.obj T))) ?_
    rw [FppfTorsor.trivialSmul_fst, MonObj.comp_mul, lift_fst, ← Category.assoc, lift_snd]
  ev_actPt_right := by
    intro W g α p h h'
    rw [hρ, inv_one, mul_one]
  ev_bijective := by
    intro W p g'
    refine ⟨⟨lift g' (p ≫ P.projection), lift_snd _ _⟩, lift_fst _ _, ?_⟩
    rintro ⟨β, hβ⟩ hev
    have hev' : β ≫ fst G'.space.toSheaf (fppfYoneda.obj T) = g' := hev
    refine Subtype.ext ?_
    change β = lift g' (p ≫ P.projection)
    rw [← hev', ← hβ, TorsorPushout.lift_comp_fst_snd]

end PushoutTorsorRel

/-- **The pushout along a pointwise trivial relative homomorphism is the trivial torsor**, as an
arrow of `G'`-torsors. -/
noncomputable def pushoutTrivialHomHom (ρ : RelMonHom G G' T)
    (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ.pt b x = 1)
    (P : FppfTorsor G T) : pushoutFppfTorsor P ρ ⟶ FppfTorsor.trivial G' T where
  iso := PushoutTorsorRel.compareIso (pushoutTorsor P ρ) (PushoutTorsorRel.trivialDatum ρ hρ P)
  over := PushoutTorsorRel.cmpMap_proj (pushoutTorsor P ρ)
    (PushoutTorsorRel.trivialDatum ρ hρ P)
  equivariant := PushoutTorsorRel.cmpMap_equivariant (pushoutTorsor P ρ)
    (PushoutTorsorRel.trivialDatum ρ hρ P)

/-- **The pushout of an arbitrary torsor along a pointwise trivial relative homomorphism is the
trivial torsor.**  This is the torsor-level content of the vanishing law of a contraction: the
contraction by the scalar `0` kills the torsor, whatever it was. -/
noncomputable def pushoutTrivialHomIso (ρ : RelMonHom G G' T)
    (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ.pt b x = 1)
    (P : FppfTorsor G T) : pushoutFppfTorsor P ρ ≅ FppfTorsor.trivial G' T :=
  ⟨pushoutTrivialHomHom ρ hρ P, Groupoid.inv (pushoutTrivialHomHom ρ hρ P),
    Groupoid.comp_inv _, Groupoid.inv_comp _⟩

/-- **The canonical global section of the pushout along a pointwise trivial homomorphism**: the
unit section of the trivial torsor, read through the comparison of pushout data. -/
noncomputable def trivialHomSection (ρ : RelMonHom G G' T)
    (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ.pt b x = 1)
    (P : FppfTorsor G T) : fppfYoneda.obj T ⟶ (pushoutFppfTorsor P ρ).P :=
  ConeQuotient.unitSection G' T ≫
    PushoutTorsorRel.cmpMap (PushoutTorsorRel.trivialDatum ρ hρ P) (pushoutTorsor P ρ)

/-- The canonical section of the pushout along a pointwise trivial homomorphism is a section. -/
theorem trivialHomSection_projection (ρ : RelMonHom G G' T)
    (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ.pt b x = 1)
    (P : FppfTorsor G T) :
    trivialHomSection ρ hρ P ≫ (pushoutFppfTorsor P ρ).projection = 𝟙 _ :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun q => ConeQuotient.unitSection G' T ≫ q)
      (PushoutTorsorRel.cmpMap_proj (PushoutTorsorRel.trivialDatum ρ hρ P)
        (pushoutTorsor P ρ))).trans (ConeQuotient.unitSection_snd (G := G') (T := T)))

/-- **The evaluation of the canonical section at any point of `P` is the unit.** -/
theorem ev_trivialHomSection (ρ : RelMonHom G G' T)
    (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ.pt b x = 1)
    (P : FppfTorsor G T) {W : Scheme.{u}} (α : fppfYoneda.obj W ⟶ fppfYoneda.obj T)
    (p : fppfYoneda.obj W ⟶ P.P) (hp : p ≫ P.projection = α)
    (h : (α ≫ trivialHomSection ρ hρ P) ≫ (pushoutTorsor P ρ).projection = p ≫ P.projection) :
    (pushoutTorsor P ρ).ev (α ≫ trivialHomSection ρ hρ P) p h = 1 := by
  have hT : (α ≫ ConeQuotient.unitSection G' T) ≫
      (PushoutTorsorRel.trivialDatum ρ hρ P).projection = p ≫ P.projection :=
    ((Category.assoc α _ _).trans
      ((congrArg (fun q => α ≫ q) (ConeQuotient.unitSection_snd (G := G') (T := T))).trans
        (Category.comp_id α))).trans hp.symm
  have h₂ : ((α ≫ ConeQuotient.unitSection G' T) ≫
      PushoutTorsorRel.cmpMap (PushoutTorsorRel.trivialDatum ρ hρ P) (pushoutTorsor P ρ)) ≫
      (pushoutTorsor P ρ).projection = p ≫ P.projection :=
    (congrArg (fun q => q ≫ (pushoutTorsor P ρ).projection) (Category.assoc α _ _)).trans h
  refine Eq.trans ((pushoutTorsor P ρ).ev_congr (Category.assoc α _ _).symm rfl h h₂) ?_
  refine Eq.trans (PushoutTorsorRel.ev_cmpMap (PushoutTorsorRel.trivialDatum ρ hρ P)
    (pushoutTorsor P ρ) (α ≫ ConeQuotient.unitSection G' T) p hT h₂) ?_
  exact (Category.assoc α _ _).trans
    ((congrArg (fun q => α ≫ q) (ConeQuotient.unitSection_fst (G := G') (T := T))).trans
      (MonObj.comp_one α))

variable {U : AlgebraicSpaceAction G} {U' : AlgebraicSpaceAction G'}

/-- **The point of the action space of the canonical section of a pointwise trivial pushout**: on
every generalised point of the base carrying a point `p` of `P`, it is the image of `p` under the
equivariant map `τ`.  For the contraction by the scalar `0` this says that the point is the vertex
lying over the base point. -/
theorem trivialHomSection_comp_targetMap (ρ : RelMonHom G G' T)
    (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ.pt b x = 1)
    (τ : RelEquivMap ρ U U') (P : ActionTorsor G U T) {W : Scheme.{u}}
    (α : fppfYoneda.obj W ⟶ fppfYoneda.obj T) (p : fppfYoneda.obj W ⟶ P.P)
    (hp : p ≫ P.projection = α) :
    α ≫ trivialHomSection ρ hρ P.toFppfTorsor ≫ targetMap P ρ τ =
      τ.pt (p ≫ P.projection) (p ≫ P.target) := by
  have hbase : (α ≫ trivialHomSection ρ hρ P.toFppfTorsor) ≫
      (pushoutTorsor P.toFppfTorsor ρ).projection = p ≫ P.projection :=
    (Category.assoc α _ _).trans
      ((congrArg (fun q => α ≫ q)
        (trivialHomSection_projection ρ hρ P.toFppfTorsor)).trans
        ((Category.comp_id α).trans hp.symm))
  refine Eq.trans (Category.assoc α _ _).symm ?_
  refine Eq.trans (targetMap_eq_actPt (τ := τ)
    (α ≫ trivialHomSection ρ hρ P.toFppfTorsor) p hbase) ?_
  refine Eq.trans (congrArg (fun g => actPt g (τ.pt (p ≫ P.projection) (p ≫ P.target)))
    (ev_trivialHomSection ρ hρ P.toFppfTorsor α p hp hbase)) ?_
  exact actPt_one _

/-- **The pushout of an arbitrary object of `[U/G]` along a pointwise trivial homomorphism is a
trivialised object of `[U'/G']`.**  Its point of the action space is computed by
`TorsorPushoutRel.trivialHomSection_comp_targetMap`. -/
noncomputable def pushoutTrivialHomActionIso (ρ : RelMonHom G G' T)
    (hρ : ∀ {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T) (x : Z ⟶ G.space.toSheaf),
      ρ.pt b x = 1)
    (τ : RelEquivMap ρ U U') (P : ActionTorsor G U T) :
    ConeQuotient.trivialWithPoint
        (trivialHomSection ρ hρ P.toFppfTorsor ≫ targetMap P ρ τ) ≅
      pushoutActionTorsor P ρ τ :=
  ConeQuotient.isoTrivialOfSection (pushoutActionTorsor P ρ τ)
    (trivialHomSection ρ hρ P.toFppfTorsor) (trivialHomSection_projection ρ hρ P.toFppfTorsor)

end TrivialHom

/-! ### The scalar homomorphism at the scalar `0` -/

section ConeScaleZero

open ConeQuotient

variable {σ : Type u} {T : Scheme.{u}}

/-- Scaling the vector bundle group by the scalar `0` is the unit. -/
theorem scaleBundleScheme_zero {W : Scheme.{u}} (x : W ⟶ bundleScheme σ) (b : W ⟶ T) :
    lift x b ≫ scaleBundleScheme σ (0 : Γ(T, ⊤)) = 1 := by
  refine coords_injective (funext fun i => ?_)
  rw [coords_comp_scaleBundleScheme, lift_fst, lift_snd, map_zero, zero_mul, coords_one]

/-- **The scalar homomorphism at the scalar `0` is trivial on all generalised points.** -/
theorem scaleRelMonHom_pt_zero {Z : FppfSheaf.{u}} (b : Z ⟶ fppfYoneda.obj T)
    (x : Z ⟶ (vectorBundleGroup σ).space.toSheaf) :
    (scaleRelMonHom σ T (0 : Γ(T, ⊤))).pt b x = 1 := by
  refine hom_ext_points fun W ω => ?_
  rw [RelMonHom.comp_pt, MonObj.comp_one]
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : W ⟶ T, fppfYoneda.map b₀ = ω ≫ b :=
    ⟨fppfYoneda.preimage (ω ≫ b), fppfYoneda.map_preimage _⟩
  obtain ⟨x₀, hx₀⟩ := bdlPt_surjective (σ := σ) (ω ≫ x)
  rw [← hb₀, ← hx₀, scaleRelMonHom_pt, scaleBundleScheme_zero, bdlPt_one]

end ConeScaleZero

/-! ### The scalar homomorphism of a pulled-back scalar -/

section ConeScalePullback

open ConeQuotient

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T T' : Scheme.{u}}

/-- Scaling by a pulled-back scalar is scaling by the scalar over the original base. -/
theorem scaleBundleScheme_pullback (r : Γ(T, ⊤)) (b : T' ⟶ T) {W : Scheme.{u}}
    (x : W ⟶ bundleScheme σ) (b₀ : W ⟶ T') :
    lift x b₀ ≫ scaleBundleScheme σ (b.appTop r) = lift x (b₀ ≫ b) ≫ scaleBundleScheme σ r := by
  refine coords_injective (funext fun i => ?_)
  simp only [coords_comp_scaleBundleScheme, lift_fst, lift_snd]
  rw [_root_.AlgebraicGeometry.Scheme.Hom.comp_appTop]
  rfl

/-- **The scalar homomorphism of a pulled-back scalar is the base change of the scalar
homomorphism**, on all generalised points. -/
theorem scaleRelMonHom_pt_pullback (r : Γ(T, ⊤)) (b : T' ⟶ T) {Z : FppfSheaf.{u}}
    (b' : Z ⟶ fppfYoneda.obj T') (x : Z ⟶ (vectorBundleGroup σ).space.toSheaf) :
    (scaleRelMonHom σ T' (b.appTop r)).pt b' x =
      (scaleRelMonHom σ T r).pt (b' ≫ fppfYoneda.map b) x := by
  refine hom_ext_points fun W ω => ?_
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : W ⟶ T', fppfYoneda.map b₀ = ω ≫ b' :=
    ⟨fppfYoneda.preimage (ω ≫ b'), fppfYoneda.map_preimage _⟩
  obtain ⟨x₀, hx₀⟩ := bdlPt_surjective (σ := σ) (ω ≫ x)
  have hbase : ω ≫ b' ≫ fppfYoneda.map b = fppfYoneda.map (b₀ ≫ b) := by
    rw [← Category.assoc, ← hb₀, ← CategoryTheory.Functor.map_comp]
  have hL : ω ≫ (scaleRelMonHom σ T' (b.appTop r)).pt b' x =
      bdlPt σ (lift x₀ b₀ ≫ scaleBundleScheme σ (b.appTop r)) := by
    rw [RelMonHom.comp_pt, ← hb₀, ← hx₀, scaleRelMonHom_pt]
  have hR : ω ≫ (scaleRelMonHom σ T r).pt (b' ≫ fppfYoneda.map b) x =
      bdlPt σ (lift x₀ (b₀ ≫ b) ≫ scaleBundleScheme σ r) := by
    rw [RelMonHom.comp_pt, hbase, ← hx₀, scaleRelMonHom_pt]
  rw [hL, hR, scaleBundleScheme_pullback]

/-- Contracting the cone by a pulled-back scalar is contracting by the scalar over the original
base. -/
theorem scaleConeScheme_pullback (A : ConeAction R S F) (r : Γ(T, ⊤)) (b : T' ⟶ T)
    {W : Scheme.{u}} (x : W ⟶ coneScheme S) (b₀ : W ⟶ T') :
    lift x b₀ ≫ scaleConeScheme A (b.appTop r) = lift x (b₀ ≫ b) ≫ scaleConeScheme A r := by
  refine conePt_injective ?_
  simp only [conePt_comp_scaleConeScheme, lift_fst, lift_snd]
  rw [_root_.AlgebraicGeometry.Scheme.Hom.comp_appTop]
  rfl

/-- **The cone contraction by a pulled-back scalar is the base change of the cone contraction**,
on all generalised points. -/
theorem coneScaleRelEquivMap_pt_pullback (A : ConeAction R S F) (bas : Module.Basis σ R F)
    (r : Γ(T, ⊤)) (b : T' ⟶ T) {Z : FppfSheaf.{u}} (b' : Z ⟶ fppfYoneda.obj T')
    (x : Z ⟶ (coneActionSpace A bas).space.toSheaf) :
    (coneScaleRelEquivMap A bas (b.appTop r)).pt b' x =
      (coneScaleRelEquivMap A bas r).pt (b' ≫ fppfYoneda.map b) x := by
  refine hom_ext_points fun W ω => ?_
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : W ⟶ T', fppfYoneda.map b₀ = ω ≫ b' :=
    ⟨fppfYoneda.preimage (ω ≫ b'), fppfYoneda.map_preimage _⟩
  obtain ⟨x₀, hx₀⟩ := cnPt_surjective A bas (ω ≫ x)
  have hbase : ω ≫ b' ≫ fppfYoneda.map b = fppfYoneda.map (b₀ ≫ b) := by
    rw [← Category.assoc, ← hb₀, ← CategoryTheory.Functor.map_comp]
  have hL : ω ≫ (coneScaleRelEquivMap A bas (b.appTop r)).pt b' x =
      cnPt A bas (lift x₀ b₀ ≫ scaleConeScheme A (b.appTop r)) := by
    rw [RelEquivMap.comp_pt, ← hb₀, ← hx₀, coneScaleRelEquivMap_pt]
  have hR : ω ≫ (coneScaleRelEquivMap A bas r).pt (b' ≫ fppfYoneda.map b) x =
      cnPt A bas (lift x₀ (b₀ ≫ b) ≫ scaleConeScheme A r) := by
    rw [RelEquivMap.comp_pt, hbase, ← hx₀, coneScaleRelEquivMap_pt]
  rw [hL, hR, scaleConeScheme_pullback]

end ConeScalePullback

/-! ### The contraction is over the base -/

section ConeBase

open ConeQuotient

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T : Scheme.{u}}

/-- **The scalar contraction of the cone does not move the point of the base underneath**, on
generalised points.  This is the content of the projection law of a contraction in the form
available before the base point of an object of `[C/E]` is descended to `T`. -/
theorem conePt_scaleConeScheme_comp_algebraMap (A : ConeAction R S F) (r : Γ(T, ⊤))
    {W : Scheme.{u}} (x : W ⟶ coneScheme S) (b : W ⟶ T) :
    (conePt (lift x b ≫ scaleConeScheme A r)).comp (algebraMap R S) =
      (conePt x).comp (algebraMap R S) := by
  rw [conePt_comp_scaleConeScheme, lift_fst, scaleRing_comp_algebraMap]

/-- **The action of the vector bundle group on the cone does not move the point of the base
underneath**, on generalised points; hence neither does the translation relating the two sides of
`TorsorPushoutRel.targetMap_eq_actPt`. -/
theorem conePt_actScheme_comp_algebraMap (A : ConeAction R S F) (bas : Module.Basis σ R F)
    {W : Scheme.{u}} (g : W ⟶ bundleScheme σ) (x : W ⟶ coneScheme S) :
    (conePt (lift g x ≫ actScheme A bas)).comp (algebraMap R S) =
      (conePt x).comp (algebraMap R S) := by
  rw [conePt_comp_actScheme, lift_snd, actOn_comp_algebraMap]

end ConeBase

end TorsorPushoutRel

/-! ### The coherence isomorphisms of the contraction of `[C/E]` -/

namespace ConeQuotient

universe u

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u} {T T' : Scheme.{u}}
  (A : ConeAction R S F) (bas : Module.Basis σ R F)

/-- **The unit coherence isomorphism of the unconditional contraction of `[C/E]`**: contracting
by the scalar `1` is the identity functor of `ActionTorsor (vectorBundleGroup σ)
(coneActionSpace A bas) T`.  This is the `ConeStack.contractionOneIso` field, for the
unconditional `ConeQuotient.contractionFunctor`. -/
noncomputable def contractionFunctorOneIso :
    contractionFunctor A bas (1 : Γ(T, ⊤)) ≅
      𝟭 (ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :=
  TorsorPushoutRel.pushoutFunctorRelIdIso (TorsorPushoutRel.scaleRelMonHom σ T 1)
    (TorsorPushoutRel.coneScaleRelEquivMap A bas 1)
    (fun b x => TorsorPushoutRel.scaleRelMonHom_pt_one b x)
    fun b x => TorsorPushoutRel.coneScaleRelEquivMap_pt_one A bas b x

/-- **The multiplicativity coherence isomorphism of the unconditional contraction of `[C/E]`**:
contracting by a product of scalars is contracting twice.  This is the
`ConeStack.contractionMulIso` field, for the unconditional
`ConeQuotient.contractionFunctor`. -/
noncomputable def contractionFunctorMulIso (r s : Γ(T, ⊤)) :
    contractionFunctor A bas (r * s) ≅
      contractionFunctor A bas s ⋙ contractionFunctor A bas r :=
  TorsorPushoutRel.pushoutFunctorRelCompIso (TorsorPushoutRel.scaleRelMonHom σ T s)
    (TorsorPushoutRel.scaleRelMonHom σ T r) (TorsorPushoutRel.scaleRelMonHom σ T (r * s))
    (TorsorPushoutRel.coneScaleRelEquivMap A bas s)
    (TorsorPushoutRel.coneScaleRelEquivMap A bas r)
    (TorsorPushoutRel.coneScaleRelEquivMap A bas (r * s))
    (fun b x => TorsorPushoutRel.scaleRelMonHom_pt_mul r s b x)
    fun b x => TorsorPushoutRel.coneScaleRelEquivMap_pt_mul A bas r s b x

/-- **The base-change coherence isomorphism of the unconditional contraction of `[C/E]`**:
contracting and then restricting to `T'` is restricting and then contracting by the restricted
scalar.  This is the `ConeStack.contractionPullbackIso` field (the scalar
`Scheme.Hom.appTop b r` is `canonicalFppfScalarRings.pullback b r`), for the unconditional
`ConeQuotient.contractionFunctor`. -/
noncomputable def contractionFunctorPullbackIso (r : Γ(T, ⊤)) (b : T' ⟶ T) :
    contractionFunctor A bas r ⋙ ActionTorsor.pullbackFunctor b ≅
      ActionTorsor.pullbackFunctor b ⋙ contractionFunctor A bas (b.appTop r) :=
  (TorsorPushoutRel.pushoutFunctorRelPullbackIso (TorsorPushoutRel.scaleRelMonHom σ T r)
    (TorsorPushoutRel.scaleRelMonHom σ T' (b.appTop r))
    (TorsorPushoutRel.coneScaleRelEquivMap A bas r)
    (TorsorPushoutRel.coneScaleRelEquivMap A bas (b.appTop r)) b
    (fun b' x => TorsorPushoutRel.scaleRelMonHom_pt_pullback r b b' x)
    fun b' x => TorsorPushoutRel.coneScaleRelEquivMap_pt_pullback A bas r b b' x).symm

/-- **The vanishing law of the unconditional contraction of `[C/E]`, at the level of the
underlying torsor**: the contraction by the scalar `0` of *any* object of `[C/E]` has trivial
underlying `E`-torsor, because scalar multiplication by `0` is the trivial endomorphism of the
vector bundle group.  The full `ConeStack.contractionZeroIso` additionally identifies the map to
the cone with the vertex section; see the module docstring for what that needs. -/
noncomputable def contractionFunctorZeroTorsorIso
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    ((contractionFunctor A bas (0 : Γ(T, ⊤))).obj P).toFppfTorsor ≅
      FppfTorsor.trivial (vectorBundleGroup σ) T :=
  TorsorPushoutRel.pushoutTrivialHomIso (TorsorPushoutRel.scaleRelMonHom σ T 0)
    (fun b x => TorsorPushoutRel.scaleRelMonHom_pt_zero b x) P.toFppfTorsor

/-- **The vertex law of the unconditional contraction of `[C/E]`**: a trivialised object of
`[C/E]` whose point of the cone is invariant under the contraction by `r` is fixed by the
contraction by `r`.  Every point of the vertex is such a point
(`ConeQuotient.contractionFunctorVertexIsoOfConeVertex`). -/
noncomputable def contractionFunctorVertexIso (r : Γ(T, ⊤))
    (t₀ : fppfYoneda.obj T ⟶ (coneActionSpace A bas).space.toSheaf)
    (ht₀ : (TorsorPushoutRel.coneScaleRelEquivMap A bas r).pt (𝟙 (fppfYoneda.obj T)) t₀ = t₀) :
    trivialWithPoint t₀ ≅ (contractionFunctor A bas r).obj (trivialWithPoint t₀) :=
  (eqToIso (congrArg trivialWithPoint ht₀.symm)).trans
    (TorsorPushoutRel.pushoutTrivialIso (ρ := TorsorPushoutRel.scaleRelMonHom σ T r)
      (τ := TorsorPushoutRel.coneScaleRelEquivMap A bas r) t₀)

/-- **Every contraction fixes the vertex of the cone**, on generalised points over an affine base
`T = Spec B`: the point of the cone attached to a point `φ` of the base, pushed into the vertex,
is invariant under contraction by any scalar. -/
theorem coneScaleRelEquivMap_pt_vertex {B : Type u} [CommRing B] {ε : S →ₐ[R] R}
    (hv : GradedCone.IsConeVertex A.coaction ε) (r₀ : B) (φ : S →+* B) :
    (TorsorPushoutRel.coneScaleRelEquivMap A bas (gammaMap B r₀)).pt
        (𝟙 (fppfYoneda.obj (coneScheme B))) (conePoint A bas (φ.comp (vertexHom ε))) =
      conePoint A bas (φ.comp (vertexHom ε)) := by
  rw [TorsorPushoutRel.coneScaleRelEquivMap_pt_eq_coneTwist, coneTwist_pt,
    conePointHom_conePoint, scaleRing_vertexHom A hv]

/-- **The vertex of the cone is fixed by every contraction of `[C/E]`, unconditionally**: over an
affine base `T = Spec B`, the trivialised object of `[C/E]` given by the vertex over a point `φ`
of the base is isomorphic to its contraction by any scalar `r₀ : B`.  This is the object-level
`ConeStack.contractionVertexIso` for the unconditional `ConeQuotient.contractionFunctor`. -/
noncomputable def contractionFunctorVertexIsoOfConeVertex {B : Type u} [CommRing B]
    {ε : S →ₐ[R] R} (hv : GradedCone.IsConeVertex A.coaction ε) (r₀ : B) (φ : S →+* B) :
    trivialWithPoint (conePoint A bas (φ.comp (vertexHom ε))) ≅
      (contractionFunctor A bas (gammaMap B r₀)).obj
        (trivialWithPoint (conePoint A bas (φ.comp (vertexHom ε)))) :=
  contractionFunctorVertexIso A bas (gammaMap B r₀) (conePoint A bas (φ.comp (vertexHom ε)))
    (coneScaleRelEquivMap_pt_vertex A bas hv r₀ φ)

/-- **The vanishing law of the unconditional contraction of `[C/E]`**: the contraction by the
scalar `0` of *any* object of `[C/E]` is a *trivialised* object, whose point of the cone is, on
every generalised point of `T` carrying a point `p` of the torsor, the contraction by `0` of the
point of the cone of `p`, i.e. the vertex lying over the base point
(`TorsorPushoutRel.trivialHomSection_comp_targetMap`).  This is the unconditional form of
`ConeStack.contractionZeroIso` available before the cone stack is assembled: the identification
of the point with the vertex section of `Cones/Stack.lean` needs the descent of the base point
of an object of `[C/E]` to `T`, which is not constructed in this repository. -/
noncomputable def contractionFunctorZeroIso
    (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A bas) T) :
    trivialWithPoint (TorsorPushoutRel.trivialHomSection (TorsorPushoutRel.scaleRelMonHom σ T 0)
        (fun b x => TorsorPushoutRel.scaleRelMonHom_pt_zero b x) P.toFppfTorsor ≫
      TorsorPushoutRel.targetMap P (TorsorPushoutRel.scaleRelMonHom σ T 0)
        (TorsorPushoutRel.coneScaleRelEquivMap A bas 0)) ≅
      (contractionFunctor A bas (0 : Γ(T, ⊤))).obj P :=
  TorsorPushoutRel.pushoutTrivialHomActionIso (TorsorPushoutRel.scaleRelMonHom σ T 0)
    (fun b x => TorsorPushoutRel.scaleRelMonHom_pt_zero b x)
    (TorsorPushoutRel.coneScaleRelEquivMap A bas 0) P

end ConeQuotient

end GromovWitten.AlgebraicGeometry
