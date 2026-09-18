/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.TorsorStackDescent
import GromovWitten.AlgebraicGeometry.Stacks.SieveDescentEffective

/-!
# Effectiveness of fppf descent for the quotient stack `[U/G]`

`Stacks/TorsorStackDescent.lean` proves descent of *morphisms* for the quotient prestack
`[U/G] = ActionTorsor.pullbackPseudofunctor G U`.  This file proves the second half,
effectiveness of descent for *objects*: a compatible family of equivariant torsors over the
members of an fppf covering sieve comes from an equivariant torsor over the base.

## Contents

* `ActionTorsor.TorsorDescentDatum G U S R` is the descent datum: an equivariant torsor
  `torsor f hf : ActionTorsor G U X` for every member `f : X ⟶ S` of the sieve `R`, transition
  arrows `torsor h hh' ⟶ pullbackObj g (torsor f hf)` for every factorisation `g ≫ f = h`
  inside the sieve (the fibres of `[U/G]` are groupoids, so these are automatically
  isomorphisms), and the cocycle condition, stated through the explicit projections
  `ActionTorsor.proj`.  No pseudofunctorial coherence cell occurs anywhere in it.
* `ActionTorsor.TorsorGlue D` records the output of effective descent for the underlying
  sheaves: an fppf sheaf `base` over `S` together with isomorphisms `iso f hf` identifying the
  underlying sheaf of `torsor f hf` with the base change of `base` along `f`.  It exists
  unconditionally (`ActionTorsor.nonempty_torsorGlue`), by
  `GromovWitten.AlgebraicGeometry.sheafDescentInput` of `Stacks/SieveDescentEffective.lean`.
* The `G`-action, the map to `U` and the principal map are then transported to `base` by
  gluing morphisms of sheaves: `TorsorGlue.smulBase` (with its defining property
  `TorsorGlue.str_smulBase`), `TorsorGlue.targetBase` and `TorsorGlue.principalMapBase`.  All
  the torsor axioms are proved: `TorsorGlue.one_smulBase`, `TorsorGlue.mul_smulBase`,
  `TorsorGlue.smulBase_over`, `TorsorGlue.targetBase_equivariant`,
  `TorsorGlue.isIso_principalMapBase`.
* `TorsorGlue.torsor hR loc` is the resulting equivariant torsor over `S`, where `loc` is an
  fppf-local section of the glued sheaf; `TorsorGlue.compIso hR loc f hf` are the isomorphisms
  `D.torsor f hf ≅ pullbackObj f (T.torsor hR loc)` of equivariant torsors and
  `TorsorGlue.compIso_trans` is their compatibility with the transition arrows.
* `TorsorGlue.localSectionOfCover` produces the missing fppf-local section from a member of the
  sieve which is itself a surjective flat morphism locally of finite presentation.
* `ActionTorsor.exists_torsor_of_torsorDescentDatum` is the resulting effectiveness statement,
  and `ActionTorsor.TorsorStack`/`ActionTorsor.torsorStack` bundle it with the descent of
  morphisms of `Stacks/TorsorStackDescent.lean`.

## The local-triviality caveat

`FppfTorsor` (see `Stacks/QuotientStack.lean`) asks for an fppf-local section over a *single*
cover `W ⟶ S` which is flat, locally of finite presentation and surjective.  A covering sieve
for the fppf topology contains a jointly surjective *family*, not in general a single
surjective morphism, and turning the family into a single morphism means replacing it by the
coproduct `∐ Wᵢ`, over which a section only exists once one knows that an fppf sheaf carries
coproducts of schemes to products.  That last statement is not available in the repository.

Everything in this file is therefore organised so that the local section is an explicit input:
`TorsorGlue.torsor` takes an `FppfLocalSection` of the glued sheaf as an argument, and every
other ingredient — action, target, principality, comparison isomorphisms — is unconditional.
The final theorems `exists_torsor_of_torsorDescentDatum` and `torsorStack` then supply that
input from the hypothesis that the sieve contains one surjective flat morphism of finite
presentation, which is how fppf descent data arise in practice and is the exact shape of
`FppfLocalSection` itself.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open Opposite
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

/-- Transport of an fppf-local section along an isomorphism of sheaves over the base. -/
noncomputable def FppfLocalSection.ofIso {P Q : FppfSheaf.{u}} {T : Scheme.{u}}
    {pP : P ⟶ fppfYoneda.obj T} {pQ : Q ⟶ fppfYoneda.obj T} (e : P ≅ Q)
    (he : e.hom ≫ pQ = pP) (s : FppfLocalSection P T pP) : FppfLocalSection Q T pQ where
  coverScheme := s.coverScheme
  cover := s.cover
  flat := s.flat
  locallyOfFinitePresentation := s.locallyOfFinitePresentation
  surjective := s.surjective
  localLift := s.localLift ≫ e.hom
  localLift_over := by rw [Category.assoc, he, s.localLift_over]

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {S : Scheme.{u}}

/-- A descent datum for equivariant torsors along a sieve `R` on `S`: an object of the fibre of
`[U/G]` over every member of the sieve, transition arrows identifying the object attached to a
refinement with the corresponding base change, and the cocycle condition.

The fibres of `[U/G]` are groupoids, so the transition arrows are automatically isomorphisms.
The cocycle condition is stated on the underlying sheaves, through the projections
`ActionTorsor.proj`; no pseudofunctorial coherence cell occurs in it. -/
structure TorsorDescentDatum (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (S : Scheme.{u}) (R : Sieve S) where
  /-- The equivariant torsor attached to a member `f : X ⟶ S` of the sieve. -/
  torsor {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) : ActionTorsor G U X
  /-- The transition arrow attached to a factorisation `g ≫ f = h` inside the sieve. -/
  trans {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
    (hf : R.arrows f) (hh' : R.arrows h) : torsor h hh' ⟶ pullbackObj g (torsor f hf)
  /-- The cocycle condition, read on the projections to the underlying sheaf of
  `torsor f hf`. -/
  cocycle {X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (k : Z ⟶ Y) (h : Y ⟶ S) (q : Z ⟶ S)
    (hh : g ≫ f = h) (hq : k ≫ h = q) (hf : R.arrows f) (hh' : R.arrows h)
    (hq' : R.arrows q) :
    (trans h k q hq hh' hq').iso.hom ≫ proj (torsor h hh') k ≫
        (trans f g h hh hf hh').iso.hom ≫ proj (torsor f hf) g =
      (trans f (k ≫ g) q (by rw [Category.assoc, hh, hq]) hf hq').iso.hom ≫
        proj (torsor f hf) (k ≫ g)

namespace TorsorDescentDatum

variable {R : Sieve S}

/-- The descent datum for fppf sheaves underlying a descent datum for equivariant torsors. -/
noncomputable def toSheafDescentDatum (D : TorsorDescentDatum G U S R) :
    SheafDescentDatum S R where
  sheaf f hf := (D.torsor f hf).P
  proj f hf := (D.torsor f hf).projection
  trans f g h hh hf hh' := (D.trans f g h hh hf hh').iso
  trans_proj f g h hh hf hh' := (D.trans f g h hh hf hh').over
  trans_trans f g k h q hh hq hf hh' hq' := D.cocycle f g k h q hh hq hf hh' hq'

end TorsorDescentDatum

/-- The output of effective descent for the sheaves underlying a descent datum for equivariant
torsors: an fppf sheaf over `S` whose base changes along the members of the sieve are the
underlying sheaves of the datum, compatibly with the transition arrows. -/
structure TorsorGlue {R : Sieve S} (D : TorsorDescentDatum G U S R) where
  /-- The glued fppf sheaf. -/
  base : FppfSheaf.{u}
  /-- Its structure morphism to the base scheme. -/
  over : base ⟶ fppfYoneda.obj S
  /-- The identification of the member of the datum with a base change of the glued sheaf. -/
  iso {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) :
    (D.torsor f hf).P ≅ pullback over (fppfYoneda.map f)
  /-- The identification lies over the member of the sieve. -/
  iso_snd {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) :
    (iso f hf).hom ≫ pullback.snd over (fppfYoneda.map f) = (D.torsor f hf).projection
  /-- The identifications are compatible with the transition arrows of the datum. -/
  iso_fst {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
    (hf : R.arrows f) (hh' : R.arrows h) :
    (iso h hh').hom ≫ pullback.fst over (fppfYoneda.map h) =
      (D.trans f g h hh hf hh').iso.hom ≫ proj (D.torsor f hf) g ≫
        (iso f hf).hom ≫ pullback.fst over (fppfYoneda.map f)

/-- **The sheaves underlying a descent datum for equivariant torsors glue.**  This is
`GromovWitten.AlgebraicGeometry.sheafDescentInput` applied to the underlying descent datum of
fppf sheaves; it is unconditional. -/
theorem nonempty_torsorGlue {R : Sieve S} (hR : R ∈ fppfJ.{u} S)
    (D : TorsorDescentDatum G U S R) : Nonempty (TorsorGlue D) := by
  obtain ⟨A, π, e, he1, he2⟩ := sheafDescentInput.effective S R hR D.toSheafDescentDatum
  exact ⟨{ base := A, over := π, iso := e, iso_snd := fun f hf ↦ he1 f hf
           iso_fst := fun f g h hh hf hh' ↦ he2 f g h hh hf hh' }⟩

namespace TorsorDescentDatum

variable {R : Sieve S}

/-- The composite of a transition arrow of the descent datum with the projection to the
underlying sheaf of the target: a morphism `(torsor h hh').P ⟶ (torsor f hf).P` covering the
refinement `g`. -/
noncomputable abbrev theta (D : TorsorDescentDatum G U S R) {X Y : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h) (hf : R.arrows f) (hh' : R.arrows h) :
    (D.torsor h hh').P ⟶ (D.torsor f hf).P :=
  (D.trans f g h hh hf hh').iso.hom ≫ proj (D.torsor f hf) g

variable (D : TorsorDescentDatum G U S R) {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X)
  (h : Y ⟶ S) (hh : g ≫ f = h) (hf : R.arrows f) (hh' : R.arrows h)

/-- `theta` lies over the refinement `g`. -/
theorem theta_projection :
    D.theta f g h hh hf hh' ≫ (D.torsor f hf).projection =
      (D.torsor h hh').projection ≫ fppfYoneda.map g := by
  rw [theta, Category.assoc,
    pullback.condition (f := (D.torsor f hf).projection) (g := fppfYoneda.map g),
    ← Category.assoc, (D.trans f g h hh hf hh').over]

/-- `theta` commutes with the maps to `U`. -/
theorem theta_target :
    D.theta f g h hh hf hh' ≫ (D.torsor f hf).target = (D.torsor h hh').target := by
  rw [theta, Category.assoc]
  exact (D.trans f g h hh hf hh').target

/-- `theta` is `G`-equivariant. -/
theorem theta_equivariant :
    ModObj.smul (M := G.space.toSheaf) (X := (D.torsor h hh').P) ≫ D.theta f g h hh hf hh' =
      G.space.toSheaf ◁ D.theta f g h hh hf hh' ≫
        ModObj.smul (M := G.space.toSheaf) (X := (D.torsor f hf).P) := by
  rw [theta, ← Category.assoc, (D.trans f g h hh hf hh').equivariant, Category.assoc,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  exact congrArg (fun z ↦ G.space.toSheaf ◁ (D.trans f g h hh hf hh').iso.hom ≫ z)
    (FppfTorsor.pullbackSmul_fst (D.torsor f hf).toFppfTorsor g)

end TorsorDescentDatum

namespace TorsorGlue

variable {R : Sieve S} {D : TorsorDescentDatum G U S R} (T : TorsorGlue D)

/-- The structure morphism of a member of the descent datum to the glued sheaf. -/
noncomputable abbrev str {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) :
    (D.torsor f hf).P ⟶ T.base :=
  (T.iso f hf).hom ≫ pullback.fst T.over (fppfYoneda.map f)

/-- The structure morphism to the glued sheaf lies over the member of the sieve. -/
theorem str_over {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) :
    T.str f hf ≫ T.over = (D.torsor f hf).projection ≫ fppfYoneda.map f := by
  rw [str, Category.assoc, pullback.condition (f := T.over) (g := fppfYoneda.map f),
    ← Category.assoc, T.iso_snd f hf]

section Theta

variable {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
  (hf : R.arrows f) (hh' : R.arrows h)

/-- The structure morphisms to the glued sheaf are compatible with the transition arrows. -/
theorem theta_str :
    D.theta f g h hh hf hh' ≫ T.str f hf = T.str h hh' :=
  ((T.iso_fst f g h hh hf hh').trans (Category.assoc _ _ _).symm).symm

/-- The identifications with the base changes of the glued sheaf intertwine `theta` and the
comparison morphism `relBaseChange`. -/
theorem theta_iso :
    (T.iso h hh').hom ≫ relBaseChange T.over f g h hh =
      D.theta f g h hh hf hh' ≫ (T.iso f hf).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, relBaseChange_fst]
    exact (T.theta_str f g h hh hf hh').symm
  · rw [Category.assoc, relBaseChange_snd, ← Category.assoc, T.iso_snd h hh',
      Category.assoc, T.iso_snd f hf]
    exact (D.theta_projection f g h hh hf hh').symm

/-- The inverse form of `theta_iso`. -/
theorem relBaseChange_iso_inv :
    relBaseChange T.over f g h hh ≫ (T.iso f hf).inv =
      (T.iso h hh').inv ≫ D.theta f g h hh hf hh' := by
  rw [← cancel_epi (T.iso h hh').hom, ← Category.assoc, T.theta_iso f g h hh hf hh',
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end Theta

section Ext

variable {B : FppfSheaf.{u}}

/-- Separatedness of the glued sheaf: two morphisms out of it which agree after composition
with all the structure morphisms of the descent datum are equal. -/
theorem hom_ext_str (hR : R ∈ fppfJ.{u} S) {ψ ψ' : T.base ⟶ B}
    (hyp : ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f),
      T.str f hf ≫ ψ = T.str f hf ≫ ψ') : ψ = ψ' := by
  refine hom_ext_of_cover T.over hR ?_
  intro X f hf
  refine (cancel_epi (T.iso f hf).hom).1 ?_
  rw [← Category.assoc, ← Category.assoc]
  exact hyp f hf

/-- The variant of `hom_ext_str` for morphisms out of `V ⊗ base`, needed to check the
equivariance of the glued action. -/
theorem hom_ext_str_whiskerLeft (hR : R ∈ fppfJ.{u} S) (V : FppfSheaf.{u})
    {ψ ψ' : V ⊗ T.base ⟶ B}
    (hyp : ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f),
      V ◁ T.str f hf ≫ ψ = V ◁ T.str f hf ≫ ψ') : ψ = ψ' := by
  refine hom_ext_of_cover_whiskerLeft V T.over hR ?_
  intro X f hf
  have hiso : IsIso (V ◁ (T.iso f hf).hom) :=
    (MonoidalCategory.whiskerLeftIso V (T.iso f hf)).isIso_hom
  refine (cancel_epi (V ◁ (T.iso f hf).hom)).1 ?_
  rw [← Category.assoc, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
  exact hyp f hf

end Ext

section Action

variable {X Y : Scheme.{u}}

/-- The inverse of the identification `(T.iso f hf)`, read on the projection to the base. -/
theorem iso_inv_projection (f : X ⟶ S) (hf : R.arrows f) :
    (T.iso f hf).inv ≫ (D.torsor f hf).projection =
      pullback.snd T.over (fppfYoneda.map f) := by
  rw [← T.iso_snd f hf, Iso.inv_hom_id_assoc]

/-- The canonical comparison `G ⊗ (torsor f hf).P ⟶ (G ⊗ base) ×_S X`. -/
noncomputable def sigmaHom (f : X ⟶ S) (hf : R.arrows f) :
    G.space.toSheaf ⊗ (D.torsor f hf).P ⟶
      pullback (snd G.space.toSheaf T.base ≫ T.over) (fppfYoneda.map f) :=
  pullback.lift (G.space.toSheaf ◁ T.str f hf)
    (snd G.space.toSheaf (D.torsor f hf).P ≫ (D.torsor f hf).projection)
    (by rw [← Category.assoc, whiskerLeft_snd, Category.assoc, T.str_over f hf, Category.assoc])

@[reassoc]
theorem sigmaHom_fst (f : X ⟶ S) (hf : R.arrows f) :
    T.sigmaHom f hf ≫
        pullback.fst (snd G.space.toSheaf T.base ≫ T.over) (fppfYoneda.map f) =
      G.space.toSheaf ◁ T.str f hf :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem sigmaHom_snd (f : X ⟶ S) (hf : R.arrows f) :
    T.sigmaHom f hf ≫
        pullback.snd (snd G.space.toSheaf T.base ≫ T.over) (fppfYoneda.map f) =
      snd G.space.toSheaf (D.torsor f hf).P ≫ (D.torsor f hf).projection :=
  pullback.lift_snd _ _ _

/-- The canonical morphism `(G ⊗ base) ×_S X ⟶ base ×_S X`, forgetting the `G`-coordinate. -/
noncomputable def sigmaInvAux (f : X ⟶ S) :
    pullback (snd G.space.toSheaf T.base ≫ T.over) (fppfYoneda.map f) ⟶
      pullback T.over (fppfYoneda.map f) :=
  pullback.lift
    (pullback.fst (snd G.space.toSheaf T.base ≫ T.over) (fppfYoneda.map f) ≫
      snd G.space.toSheaf T.base)
    (pullback.snd (snd G.space.toSheaf T.base ≫ T.over) (fppfYoneda.map f))
    (by rw [Category.assoc]; exact pullback.condition)

@[reassoc]
theorem sigmaInvAux_fst (f : X ⟶ S) :
    T.sigmaInvAux f ≫ pullback.fst T.over (fppfYoneda.map f) =
      pullback.fst (snd G.space.toSheaf T.base ≫ T.over) (fppfYoneda.map f) ≫
        snd G.space.toSheaf T.base :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem sigmaInvAux_snd (f : X ⟶ S) :
    T.sigmaInvAux f ≫ pullback.snd T.over (fppfYoneda.map f) =
      pullback.snd (snd G.space.toSheaf T.base ≫ T.over) (fppfYoneda.map f) :=
  pullback.lift_snd _ _ _

/-- The inverse of the comparison `sigmaHom`. -/
noncomputable def sigmaInv (f : X ⟶ S) (hf : R.arrows f) :
    pullback (snd G.space.toSheaf T.base ≫ T.over) (fppfYoneda.map f) ⟶
      G.space.toSheaf ⊗ (D.torsor f hf).P :=
  lift (pullback.fst (snd G.space.toSheaf T.base ≫ T.over) (fppfYoneda.map f) ≫
      fst G.space.toSheaf T.base)
    (T.sigmaInvAux f ≫ (T.iso f hf).inv)

@[reassoc]
theorem sigmaInv_fst (f : X ⟶ S) (hf : R.arrows f) :
    T.sigmaInv f hf ≫ fst G.space.toSheaf (D.torsor f hf).P =
      pullback.fst (snd G.space.toSheaf T.base ≫ T.over) (fppfYoneda.map f) ≫
        fst G.space.toSheaf T.base :=
  lift_fst _ _

@[reassoc]
theorem sigmaInv_snd (f : X ⟶ S) (hf : R.arrows f) :
    T.sigmaInv f hf ≫ snd G.space.toSheaf (D.torsor f hf).P =
      T.sigmaInvAux f ≫ (T.iso f hf).inv :=
  lift_snd _ _

/-- The comparison `sigmaHom` followed by the forgetful morphism. -/
theorem sigmaHom_sigmaInvAux (f : X ⟶ S) (hf : R.arrows f) :
    T.sigmaHom f hf ≫ T.sigmaInvAux f =
      snd G.space.toSheaf (D.torsor f hf).P ≫ (T.iso f hf).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, T.sigmaInvAux_fst f, T.sigmaHom_fst_assoc f hf, whiskerLeft_snd,
      Category.assoc]
  · rw [Category.assoc, T.sigmaInvAux_snd f, T.sigmaHom_snd f hf, Category.assoc,
      T.iso_snd f hf]

theorem sigmaHom_sigmaInv (f : X ⟶ S) (hf : R.arrows f) :
    T.sigmaHom f hf ≫ T.sigmaInv f hf = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, T.sigmaInv_fst f hf, T.sigmaHom_fst_assoc f hf, whiskerLeft_fst,
      Category.id_comp]
  · rw [Category.assoc, T.sigmaInv_snd f hf, ← Category.assoc,
      T.sigmaHom_sigmaInvAux f hf, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Category.id_comp]

theorem sigmaInv_sigmaHom (f : X ⟶ S) (hf : R.arrows f) :
    T.sigmaInv f hf ≫ T.sigmaHom f hf = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, T.sigmaHom_fst f hf, Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, T.sigmaInv_fst f hf]
    · rw [Category.assoc, whiskerLeft_snd, T.sigmaInv_snd_assoc f hf, str,
        Iso.inv_hom_id_assoc, T.sigmaInvAux_fst f]
  · rw [Category.assoc, T.sigmaHom_snd f hf, T.sigmaInv_snd_assoc f hf,
      T.iso_inv_projection f hf, T.sigmaInvAux_snd f, Category.id_comp]

/-- The comparison `G ⊗ (torsor f hf).P ≅ (G ⊗ base) ×_S X`. -/
noncomputable def sigmaIso (f : X ⟶ S) (hf : R.arrows f) :
    G.space.toSheaf ⊗ (D.torsor f hf).P ≅
      pullback (snd G.space.toSheaf T.base ≫ T.over) (fppfYoneda.map f) where
  hom := T.sigmaHom f hf
  inv := T.sigmaInv f hf
  hom_inv_id := T.sigmaHom_sigmaInv f hf
  inv_hom_id := T.sigmaInv_sigmaHom f hf

variable (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h) (hf : R.arrows f)
  (hh' : R.arrows h)

/-- The forgetful morphisms commute with the comparison morphisms `relBaseChange`. -/
theorem relBaseChange_sigmaInvAux :
    relBaseChange (snd G.space.toSheaf T.base ≫ T.over) f g h hh ≫ T.sigmaInvAux f =
      T.sigmaInvAux h ≫ relBaseChange T.over f g h hh := by
  apply pullback.hom_ext
  · rw [Category.assoc, T.sigmaInvAux_fst f, ← Category.assoc, relBaseChange_fst,
      Category.assoc, relBaseChange_fst, T.sigmaInvAux_fst h]
  · rw [Category.assoc, T.sigmaInvAux_snd f, relBaseChange_snd, Category.assoc,
      relBaseChange_snd, ← Category.assoc, T.sigmaInvAux_snd h]

/-- The inverse comparisons `sigmaInv` are compatible with base change inside the sieve. -/
theorem relBaseChange_sigmaInv :
    relBaseChange (snd G.space.toSheaf T.base ≫ T.over) f g h hh ≫ T.sigmaInv f hf =
      T.sigmaInv h hh' ≫ G.space.toSheaf ◁ D.theta f g h hh hf hh' := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, T.sigmaInv_fst f hf, ← Category.assoc, relBaseChange_fst,
      Category.assoc, whiskerLeft_fst, T.sigmaInv_fst h hh']
  · rw [Category.assoc, T.sigmaInv_snd f hf, Category.assoc, whiskerLeft_snd,
      T.sigmaInv_snd_assoc h hh', ← Category.assoc, T.relBaseChange_sigmaInvAux f g h hh,
      Category.assoc, T.relBaseChange_iso_inv f g h hh hf hh']

/-- `theta` transports the actions to the structure morphisms of the glued sheaf. -/
theorem theta_smul_str :
    ModObj.smul (M := G.space.toSheaf) (X := (D.torsor h hh').P) ≫ T.str h hh' =
      (G.space.toSheaf ◁ D.theta f g h hh hf hh') ≫
        ModObj.smul (M := G.space.toSheaf) (X := (D.torsor f hf).P) ≫ T.str f hf := by
  rw [← T.theta_str f g h hh hf hh', ← Category.assoc,
    D.theta_equivariant f g h hh hf hh', Category.assoc]

end Action

section Smul

variable {X Y : Scheme.{u}}

/-- The descent datum for morphisms which glues the actions of `G` on the members of a descent
datum for equivariant torsors. -/
noncomputable def smulFamily :
    RelHomFamily (snd G.space.toSheaf T.base ≫ T.over) T.base R where
  hom f hf := T.sigmaInv f hf ≫
    ModObj.smul (M := G.space.toSheaf) (X := (D.torsor f hf).P) ≫ T.str f hf
  compat f g h hh hf hh' := by
    symm
    rw [← Category.assoc, T.relBaseChange_sigmaInv f g h hh hf hh', Category.assoc,
      ← T.theta_smul_str f g h hh hf hh']

theorem smulFamily_hom (f : X ⟶ S) (hf : R.arrows f) :
    T.smulFamily.hom f hf = T.sigmaInv f hf ≫
      ModObj.smul (M := G.space.toSheaf) (X := (D.torsor f hf).P) ≫ T.str f hf :=
  rfl

/-- The `G`-action on the glued sheaf. -/
noncomputable def smulBase (hR : R ∈ fppfJ.{u} S) : G.space.toSheaf ⊗ T.base ⟶ T.base :=
  T.smulFamily.glue hR

/-- **The defining property of the glued action**: it restricts to the given actions along the
structure morphisms of the descent datum. -/
theorem str_smulBase (hR : R ∈ fppfJ.{u} S) (f : X ⟶ S) (hf : R.arrows f) :
    (G.space.toSheaf ◁ T.str f hf) ≫ T.smulBase hR =
      ModObj.smul (M := G.space.toSheaf) (X := (D.torsor f hf).P) ≫ T.str f hf := by
  rw [← T.sigmaHom_fst f hf, Category.assoc, smulBase, T.smulFamily.glue_spec hR f hf,
    T.smulFamily_hom f hf, ← Category.assoc, T.sigmaHom_sigmaInv f hf, Category.id_comp]

/-- The unit axiom for an action, in whiskering notation. -/
theorem one_smul_whiskerRight {M : FppfSheaf.{u}} [MonObj M] (Z : FppfSheaf.{u})
    [ModObj M Z] :
    (MonObj.one (X := M) ▷ Z) ≫ ModObj.smul (M := M) (X := Z) = (λ_ Z).hom :=
  ModObj.one_smul Z

/-- The associativity axiom for an action, in whiskering notation. -/
@[reassoc]
theorem mul_smul_whiskerRight {M : FppfSheaf.{u}} [MonObj M] (Z : FppfSheaf.{u})
    [ModObj M Z] :
    (MonObj.mul (X := M) ▷ Z) ≫ ModObj.smul (M := M) (X := Z) =
      (α_ M M Z).hom ≫ (M ◁ ModObj.smul (M := M) (X := Z)) ≫
        ModObj.smul (M := M) (X := Z) :=
  ModObj.mul_smul Z

/-- The glued action is unital. -/
theorem one_smulBase (hR : R ∈ fppfJ.{u} S) :
    (MonObj.one (X := G.space.toSheaf) ▷ T.base) ≫ T.smulBase hR = (λ_ T.base).hom := by
  refine T.hom_ext_str_whiskerLeft hR (𝟙_ FppfSheaf.{u}) ?_
  intro X f hf
  rw [← Category.assoc, MonoidalCategory.whisker_exchange, Category.assoc,
    T.str_smulBase hR f hf, ← Category.assoc, one_smul_whiskerRight,
    MonoidalCategory.leftUnitor_naturality]

/-- The glued action is associative. -/
theorem mul_smulBase (hR : R ∈ fppfJ.{u} S) :
    (MonObj.mul (X := G.space.toSheaf) ▷ T.base) ≫ T.smulBase hR =
      (α_ G.space.toSheaf G.space.toSheaf T.base).hom ≫
        (G.space.toSheaf ◁ T.smulBase hR) ≫ T.smulBase hR := by
  refine T.hom_ext_str_whiskerLeft hR (G.space.toSheaf ⊗ G.space.toSheaf) ?_
  intro X f hf
  rw [MonoidalCategory.whisker_exchange_assoc, T.str_smulBase hR f hf,
    mul_smul_whiskerRight_assoc, MonoidalCategory.associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, T.str_smulBase hR f hf,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, T.str_smulBase hR f hf]

/-- The glued sheaf is a `G`-object. -/
@[instance_reducible]
noncomputable def actionBase (hR : R ∈ fppfJ.{u} S) : ModObj G.space.toSheaf T.base where
  smul := T.smulBase hR
  one_smul := T.one_smulBase hR
  mul_smul := T.mul_smulBase hR

/-- The glued action lies over the base scheme. -/
theorem smulBase_over (hR : R ∈ fppfJ.{u} S) :
    T.smulBase hR ≫ T.over = snd G.space.toSheaf T.base ≫ T.over := by
  refine T.hom_ext_str_whiskerLeft hR G.space.toSheaf ?_
  intro X f hf
  rw [← Category.assoc, T.str_smulBase hR f hf, Category.assoc, T.str_over f hf,
    ← Category.assoc, (D.torsor f hf).action_over, Category.assoc, whiskerLeft_snd_assoc,
    T.str_over f hf]

end Smul

section Target

variable {X Y : Scheme.{u}}

/-- The descent datum for morphisms which glues the maps to `U`. -/
noncomputable def targetFamily : RelHomFamily T.over U.space.toSheaf R where
  hom f hf := (T.iso f hf).inv ≫ (D.torsor f hf).target
  compat f g h hh hf hh' := by
    symm
    rw [← Category.assoc, T.relBaseChange_iso_inv f g h hh hf hh', Category.assoc,
      D.theta_target f g h hh hf hh']

theorem targetFamily_hom (f : X ⟶ S) (hf : R.arrows f) :
    T.targetFamily.hom f hf = (T.iso f hf).inv ≫ (D.torsor f hf).target :=
  rfl

/-- The map from the glued sheaf to `U`. -/
noncomputable def targetBase (hR : R ∈ fppfJ.{u} S) : T.base ⟶ U.space.toSheaf :=
  T.targetFamily.glue hR

/-- The defining property of the glued map to `U`. -/
theorem str_targetBase (hR : R ∈ fppfJ.{u} S) (f : X ⟶ S) (hf : R.arrows f) :
    T.str f hf ≫ T.targetBase hR = (D.torsor f hf).target := by
  rw [Category.assoc, targetBase, T.targetFamily.glue_spec hR f hf, T.targetFamily_hom f hf,
    Iso.hom_inv_id_assoc]

/-- The glued map to `U` is `G`-equivariant. -/
theorem targetBase_equivariant (hR : R ∈ fppfJ.{u} S) :
    T.smulBase hR ≫ T.targetBase hR =
      (G.space.toSheaf ◁ T.targetBase hR) ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) := by
  refine T.hom_ext_str_whiskerLeft hR G.space.toSheaf ?_
  intro X f hf
  rw [← Category.assoc, T.str_smulBase hR f hf, Category.assoc, T.str_targetBase hR f hf,
    ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, T.str_targetBase hR f hf]
  exact (D.torsor f hf).target_equivariant

end Target

section Principal

variable {X : Scheme.{u}}

/-- The principal map of the glued torsor. -/
noncomputable def principalMapBase (hR : R ∈ fppfJ.{u} S) :
    G.space.toSheaf ⊗ T.base ⟶ pullback T.over T.over :=
  pullback.lift (T.smulBase hR) (snd G.space.toSheaf T.base) (T.smulBase_over hR)

@[reassoc]
theorem principalMapBase_fst (hR : R ∈ fppfJ.{u} S) :
    T.principalMapBase hR ≫ pullback.fst T.over T.over = T.smulBase hR :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem principalMapBase_snd (hR : R ∈ fppfJ.{u} S) :
    T.principalMapBase hR ≫ pullback.snd T.over T.over = snd G.space.toSheaf T.base :=
  pullback.lift_snd _ _ _

/-- The principal map of the glued torsor lies over the base scheme. -/
theorem principalMapBase_over (hR : R ∈ fppfJ.{u} S) :
    T.principalMapBase hR ≫ (pullback.fst T.over T.over ≫ T.over) =
      snd G.space.toSheaf T.base ≫ T.over := by
  rw [← Category.assoc, T.principalMapBase_fst hR, T.smulBase_over hR]

/-- The inverse of the identification `T.iso f hf`, read on the structure morphism. -/
theorem iso_inv_str (f : X ⟶ S) (hf : R.arrows f) :
    (T.iso f hf).inv ≫ T.str f hf = pullback.fst T.over (fppfYoneda.map f) :=
  Iso.inv_hom_id_assoc _ _

/-- The two projections of `(torsor f hf).P ×_X (torsor f hf).P` agree after composition with
the structure morphism and the projection to the base scheme. -/
theorem rho_cond (f : X ⟶ S) (hf : R.arrows f) :
    (pullback.fst (D.torsor f hf).projection (D.torsor f hf).projection ≫ T.str f hf) ≫
        T.over =
      (pullback.snd (D.torsor f hf).projection (D.torsor f hf).projection ≫ T.str f hf) ≫
        T.over := by
  rw [Category.assoc, T.str_over f hf, Category.assoc, T.str_over f hf, ← Category.assoc,
    ← Category.assoc, pullback.condition]

/-- The comparison `(torsor f hf).P ×_X (torsor f hf).P ⟶ base ×_S base`. -/
noncomputable def rhoFst (f : X ⟶ S) (hf : R.arrows f) :
    pullback (D.torsor f hf).projection (D.torsor f hf).projection ⟶
      pullback T.over T.over :=
  pullback.lift
    (pullback.fst (D.torsor f hf).projection (D.torsor f hf).projection ≫ T.str f hf)
    (pullback.snd (D.torsor f hf).projection (D.torsor f hf).projection ≫ T.str f hf)
    (T.rho_cond f hf)

@[reassoc]
theorem rhoFst_fst (f : X ⟶ S) (hf : R.arrows f) :
    T.rhoFst f hf ≫ pullback.fst T.over T.over =
      pullback.fst (D.torsor f hf).projection (D.torsor f hf).projection ≫ T.str f hf :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem rhoFst_snd (f : X ⟶ S) (hf : R.arrows f) :
    T.rhoFst f hf ≫ pullback.snd T.over T.over =
      pullback.snd (D.torsor f hf).projection (D.torsor f hf).projection ≫ T.str f hf :=
  pullback.lift_snd _ _ _

/-- The comparison `(torsor f hf).P ×_X (torsor f hf).P ⟶ (base ×_S base) ×_S X`. -/
noncomputable def rhoHom (f : X ⟶ S) (hf : R.arrows f) :
    pullback (D.torsor f hf).projection (D.torsor f hf).projection ⟶
      pullback (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f) :=
  pullback.lift (T.rhoFst f hf)
    (pullback.fst (D.torsor f hf).projection (D.torsor f hf).projection ≫
      (D.torsor f hf).projection)
    (by rw [← Category.assoc, T.rhoFst_fst f hf, Category.assoc, T.str_over f hf,
      ← Category.assoc])

@[reassoc]
theorem rhoHom_fst (f : X ⟶ S) (hf : R.arrows f) :
    T.rhoHom f hf ≫
        pullback.fst (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f) =
      T.rhoFst f hf :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem rhoHom_snd (f : X ⟶ S) (hf : R.arrows f) :
    T.rhoHom f hf ≫
        pullback.snd (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f) =
      pullback.fst (D.torsor f hf).projection (D.torsor f hf).projection ≫
        (D.torsor f hf).projection :=
  pullback.lift_snd _ _ _

/-- The first component of the inverse of the comparison `rhoHom`. -/
noncomputable def rhoAux1 (f : X ⟶ S) :
    pullback (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f) ⟶
      pullback T.over (fppfYoneda.map f) :=
  pullback.lift
    (pullback.fst (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f) ≫
      pullback.fst T.over T.over)
    (pullback.snd (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f))
    (by rw [Category.assoc]; exact pullback.condition)

/-- The second component of the inverse of the comparison `rhoHom`. -/
noncomputable def rhoAux2 (f : X ⟶ S) :
    pullback (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f) ⟶
      pullback T.over (fppfYoneda.map f) :=
  pullback.lift
    (pullback.fst (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f) ≫
      pullback.snd T.over T.over)
    (pullback.snd (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f))
    (by rw [Category.assoc, ← pullback.condition (f := T.over) (g := T.over)]
        exact pullback.condition)

@[reassoc]
theorem rhoAux1_fst (f : X ⟶ S) :
    T.rhoAux1 f ≫ pullback.fst T.over (fppfYoneda.map f) =
      pullback.fst (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f) ≫
        pullback.fst T.over T.over :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem rhoAux1_snd (f : X ⟶ S) :
    T.rhoAux1 f ≫ pullback.snd T.over (fppfYoneda.map f) =
      pullback.snd (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f) :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem rhoAux2_fst (f : X ⟶ S) :
    T.rhoAux2 f ≫ pullback.fst T.over (fppfYoneda.map f) =
      pullback.fst (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f) ≫
        pullback.snd T.over T.over :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem rhoAux2_snd (f : X ⟶ S) :
    T.rhoAux2 f ≫ pullback.snd T.over (fppfYoneda.map f) =
      pullback.snd (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f) :=
  pullback.lift_snd _ _ _

/-- The inverse of the comparison `rhoHom`. -/
noncomputable def rhoInv (f : X ⟶ S) (hf : R.arrows f) :
    pullback (pullback.fst T.over T.over ≫ T.over) (fppfYoneda.map f) ⟶
      pullback (D.torsor f hf).projection (D.torsor f hf).projection :=
  pullback.lift (T.rhoAux1 f ≫ (T.iso f hf).inv) (T.rhoAux2 f ≫ (T.iso f hf).inv)
    (by rw [Category.assoc, T.iso_inv_projection f hf, Category.assoc,
      T.iso_inv_projection f hf, T.rhoAux1_snd f, T.rhoAux2_snd f])

@[reassoc]
theorem rhoInv_fst (f : X ⟶ S) (hf : R.arrows f) :
    T.rhoInv f hf ≫
        pullback.fst (D.torsor f hf).projection (D.torsor f hf).projection =
      T.rhoAux1 f ≫ (T.iso f hf).inv :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem rhoInv_snd (f : X ⟶ S) (hf : R.arrows f) :
    T.rhoInv f hf ≫
        pullback.snd (D.torsor f hf).projection (D.torsor f hf).projection =
      T.rhoAux2 f ≫ (T.iso f hf).inv :=
  pullback.lift_snd _ _ _

theorem rhoHom_rhoAux1 (f : X ⟶ S) (hf : R.arrows f) :
    T.rhoHom f hf ≫ T.rhoAux1 f =
      pullback.fst (D.torsor f hf).projection (D.torsor f hf).projection ≫
        (T.iso f hf).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, T.rhoAux1_fst f, T.rhoHom_fst_assoc f hf, T.rhoFst_fst f hf,
      Category.assoc]
  · rw [Category.assoc, T.rhoAux1_snd f, T.rhoHom_snd f hf, Category.assoc, T.iso_snd f hf]

theorem rhoHom_rhoAux2 (f : X ⟶ S) (hf : R.arrows f) :
    T.rhoHom f hf ≫ T.rhoAux2 f =
      pullback.snd (D.torsor f hf).projection (D.torsor f hf).projection ≫
        (T.iso f hf).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, T.rhoAux2_fst f, T.rhoHom_fst_assoc f hf, T.rhoFst_snd f hf,
      Category.assoc]
  · rw [Category.assoc, T.rhoAux2_snd f, T.rhoHom_snd f hf, Category.assoc, T.iso_snd f hf,
      pullback.condition]

theorem rhoHom_rhoInv (f : X ⟶ S) (hf : R.arrows f) :
    T.rhoHom f hf ≫ T.rhoInv f hf = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, T.rhoInv_fst f hf, ← Category.assoc, T.rhoHom_rhoAux1 f hf,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, T.rhoInv_snd f hf, ← Category.assoc, T.rhoHom_rhoAux2 f hf,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

theorem rhoInv_rhoHom (f : X ⟶ S) (hf : R.arrows f) :
    T.rhoInv f hf ≫ T.rhoHom f hf = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, T.rhoHom_fst f hf, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, T.rhoFst_fst f hf, ← Category.assoc, T.rhoInv_fst f hf,
        Category.assoc, T.iso_inv_str f hf, T.rhoAux1_fst f]
    · rw [Category.assoc, T.rhoFst_snd f hf, ← Category.assoc, T.rhoInv_snd f hf,
        Category.assoc, T.iso_inv_str f hf, T.rhoAux2_fst f]
  · rw [Category.assoc, T.rhoHom_snd f hf, ← Category.assoc, T.rhoInv_fst f hf,
      Category.assoc, T.iso_inv_projection f hf, T.rhoAux1_snd f, Category.id_comp]

/-- The comparison between the principal map of a member of the descent datum and the base
change of the principal map of the glued sheaf. -/
theorem sigmaHom_relMap (hR : R ∈ fppfJ.{u} S) (f : X ⟶ S) (hf : R.arrows f) :
    T.sigmaHom f hf ≫ relMap (snd G.space.toSheaf T.base ≫ T.over)
        (pullback.fst T.over T.over ≫ T.over) (T.principalMapBase hR)
        (T.principalMapBase_over hR) f =
      (D.torsor f hf).principalMap ≫ T.rhoHom f hf := by
  apply pullback.hom_ext
  · rw [Category.assoc, relMap_fst, T.sigmaHom_fst_assoc f hf, Category.assoc,
      T.rhoHom_fst f hf]
    apply pullback.hom_ext
    · rw [Category.assoc, T.principalMapBase_fst hR, T.str_smulBase hR f hf, Category.assoc,
        T.rhoFst_fst f hf, reassoc_of% (D.torsor f hf).principal_fst]
    · rw [Category.assoc, T.principalMapBase_snd hR, whiskerLeft_snd, Category.assoc,
        T.rhoFst_snd f hf, reassoc_of% (D.torsor f hf).principal_snd]
  · rw [Category.assoc, relMap_snd, T.sigmaHom_snd f hf, Category.assoc, T.rhoHom_snd f hf,
      reassoc_of% (D.torsor f hf).principal_fst, (D.torsor f hf).action_over]

/-- **The principal map of the glued torsor is an isomorphism.** -/
theorem isIso_principalMapBase (hR : R ∈ fppfJ.{u} S) :
    IsIso (T.principalMapBase hR) := by
  refine isIso_of_cover (snd G.space.toSheaf T.base ≫ T.over)
    (pullback.fst T.over T.over ≫ T.over) (T.principalMapBase hR)
    (T.principalMapBase_over hR) hR ?_
  intro X f hf
  have hsi : IsIso (T.sigmaInv f hf) :=
    ⟨T.sigmaHom f hf, T.sigmaInv_sigmaHom f hf, T.sigmaHom_sigmaInv f hf⟩
  have hr : IsIso (T.rhoHom f hf) :=
    ⟨T.rhoInv f hf, T.rhoHom_rhoInv f hf, T.rhoInv_rhoHom f hf⟩
  have hpm := (D.torsor f hf).principal_isIso
  have h2 : relMap (snd G.space.toSheaf T.base ≫ T.over)
      (pullback.fst T.over T.over ≫ T.over) (T.principalMapBase hR)
      (T.principalMapBase_over hR) f =
      T.sigmaInv f hf ≫ (D.torsor f hf).principalMap ≫ T.rhoHom f hf := by
    rw [← T.sigmaHom_relMap hR f hf, ← Category.assoc, T.sigmaInv_sigmaHom f hf,
      Category.id_comp]
  rw [h2]
  infer_instance

end Principal

section Assemble

variable {X Y : Scheme.{u}}

/-- **The equivariant torsor over `S` glued from a descent datum**, given an fppf-local section
of the glued sheaf. -/
noncomputable def torsor (hR : R ∈ fppfJ.{u} S) (loc : FppfLocalSection T.base S T.over) :
    ActionTorsor G U S where
  P := T.base
  action := T.actionBase hR
  projection := T.over
  action_over := T.smulBase_over hR
  principalMap := T.principalMapBase hR
  principal_fst := T.principalMapBase_fst hR
  principal_snd := T.principalMapBase_snd hR
  principal_isIso := T.isIso_principalMapBase hR
  locallyTrivial := loc
  target := T.targetBase hR
  target_equivariant := T.targetBase_equivariant hR

variable (hR : R ∈ fppfJ.{u} S) (loc : FppfLocalSection T.base S T.over)

/-- The glued action, transported to a base change of the glued sheaf.  This is written out
explicitly rather than as `FppfTorsor.pullbackSmul` of the glued torsor, so that its type
mentions `T.over` rather than the projection of the glued torsor; the two are definitionally
equal. -/
noncomputable def pullbackSmulBase (f : X ⟶ S) :
    G.space.toSheaf ⊗ pullback T.over (fppfYoneda.map f) ⟶
      pullback T.over (fppfYoneda.map f) :=
  pullback.lift
    ((G.space.toSheaf ◁ pullback.fst T.over (fppfYoneda.map f)) ≫ T.smulBase hR)
    (snd G.space.toSheaf (pullback T.over (fppfYoneda.map f)) ≫
      pullback.snd T.over (fppfYoneda.map f))
    (by rw [Category.assoc, T.smulBase_over hR, ← Category.assoc, whiskerLeft_snd,
      Category.assoc, pullback.condition, Category.assoc])

@[reassoc]
theorem pullbackSmulBase_fst (f : X ⟶ S) :
    T.pullbackSmulBase hR f ≫ pullback.fst T.over (fppfYoneda.map f) =
      (G.space.toSheaf ◁ pullback.fst T.over (fppfYoneda.map f)) ≫ T.smulBase hR :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem pullbackSmulBase_snd (f : X ⟶ S) :
    T.pullbackSmulBase hR f ≫ pullback.snd T.over (fppfYoneda.map f) =
      snd G.space.toSheaf (pullback T.over (fppfYoneda.map f)) ≫
        pullback.snd T.over (fppfYoneda.map f) :=
  pullback.lift_snd _ _ _

/-- The identifications of the descent datum are `G`-equivariant for the glued action. -/
theorem iso_equivariant (f : X ⟶ S) (hf : R.arrows f) :
    ModObj.smul (M := G.space.toSheaf) (X := (D.torsor f hf).P) ≫ (T.iso f hf).hom =
      (G.space.toSheaf ◁ (T.iso f hf).hom) ≫ T.pullbackSmulBase hR f := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, T.pullbackSmulBase_fst hR f,
      ← MonoidalCategory.whiskerLeft_comp_assoc, T.str_smulBase hR f hf]
  · rw [Category.assoc, T.iso_snd f hf, (D.torsor f hf).action_over, Category.assoc,
      T.pullbackSmulBase_snd hR f, whiskerLeft_snd_assoc, T.iso_snd f hf]

/-- The arrow of equivariant torsors identifying a member of the descent datum with the base
change of the glued torsor. -/
noncomputable def compHom (f : X ⟶ S) (hf : R.arrows f) :
    D.torsor f hf ⟶ pullbackObj f (T.torsor hR loc) where
  iso := T.iso f hf
  over := T.iso_snd f hf
  equivariant := T.iso_equivariant hR f hf
  target := by
    rw [pullbackObj_target, ← Category.assoc]
    exact T.str_targetBase hR f hf

/-- The isomorphism of equivariant torsors identifying a member of the descent datum with the
base change of the glued torsor. -/
noncomputable def compIso (f : X ⟶ S) (hf : R.arrows f) :
    D.torsor f hf ≅ pullbackObj f (T.torsor hR loc) :=
  asIso (T.compHom hR loc f hf)

@[simp]
theorem compIso_hom_iso_hom (f : X ⟶ S) (hf : R.arrows f) :
    (T.compIso hR loc f hf).hom.iso.hom = (T.iso f hf).hom :=
  rfl

/-- **The comparison isomorphisms are compatible with the transition arrows of the descent
datum**, read on the projections to the glued torsor. -/
theorem compIso_trans (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
    (hf : R.arrows f) (hh' : R.arrows h) :
    (T.compIso hR loc h hh').hom.iso.hom ≫ proj (T.torsor hR loc) h =
      (D.trans f g h hh hf hh').iso.hom ≫ proj (D.torsor f hf) g ≫
        (T.compIso hR loc f hf).hom.iso.hom ≫ proj (T.torsor hR loc) f :=
  T.iso_fst f g h hh hf hh'

end Assemble

section LocalSection

/-- An fppf-local section of the glued sheaf, produced from a member of the sieve which is
itself a surjective flat morphism locally of finite presentation: the glued sheaf is then
trivialised over the cover trivialising the corresponding member of the descent datum. -/
noncomputable def localSectionOfCover {W : Scheme.{u}} (w : W ⟶ S) (hw : R.arrows w)
    (hflat : Flat w) (hlfp : LocallyOfFinitePresentation w) (hsurj : Surjective w) :
    FppfLocalSection T.base S T.over where
  coverScheme := (D.torsor w hw).locallyTrivial.coverScheme
  cover := (D.torsor w hw).locallyTrivial.cover ≫ w
  flat := by
    have h1 := (D.torsor w hw).locallyTrivial.flat
    have h2 := hflat
    infer_instance
  locallyOfFinitePresentation := by
    have h1 := (D.torsor w hw).locallyTrivial.locallyOfFinitePresentation
    have h2 := hlfp
    infer_instance
  surjective := by
    have h1 := (D.torsor w hw).locallyTrivial.surjective
    have h2 := hsurj
    infer_instance
  localLift := (D.torsor w hw).locallyTrivial.localLift ≫ T.str w hw
  localLift_over := by
    rw [Category.assoc, T.str_over w hw, ← Category.assoc,
      (D.torsor w hw).locallyTrivial.localLift_over, ← Functor.map_comp]

end LocalSection

end TorsorGlue

/-- **Effectiveness of fppf descent for the quotient stack `[U/G]`.**  Let `R` be an fppf
covering sieve on `S` which contains one surjective flat morphism `w` locally of finite
presentation (see the module docstring for why this hypothesis is imposed).  Then every descent
datum for equivariant torsors along `R` comes from an equivariant torsor `N` over `S`: there are
isomorphisms `D.torsor f hf ≅ pullbackObj f N` in the fibres of `[U/G]`, compatible with the
transition arrows of the datum.  The compatibility is stated on the projections to the
underlying sheaf of `N`, exactly as the cocycle condition of `TorsorDescentDatum`. -/
theorem exists_torsor_of_torsorDescentDatum {R : Sieve S} (hR : R ∈ fppfJ.{u} S)
    (D : TorsorDescentDatum G U S R) {W : Scheme.{u}} (w : W ⟶ S) (hw : R.arrows w)
    (hflat : Flat w) (hlfp : LocallyOfFinitePresentation w) (hsurj : Surjective w) :
    ∃ (N : ActionTorsor G U S) (ε : ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f),
        D.torsor f hf ≅ pullbackObj f N),
      ∀ {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
        (hf : R.arrows f) (hh' : R.arrows h),
        (ε h hh').hom.iso.hom ≫ proj N h =
          (D.trans f g h hh hf hh').iso.hom ≫ proj (D.torsor f hf) g ≫
            (ε f hf).hom.iso.hom ≫ proj N f := by
  obtain ⟨T⟩ := nonempty_torsorGlue hR D
  exact ⟨T.torsor hR (T.localSectionOfCover w hw hflat hlfp hsurj),
    fun f hf ↦ T.compIso hR _ f hf, fun f g h hh hf hh' ↦ T.compIso_trans hR _ f g h hh hf hh'⟩

/-- **The quotient prestack `[U/G]` is a stack for the big fppf topology**, in the
repository-level formulation with explicit data: descent of arrows
(`ActionTorsor.TorsorPrestack`, proved in `Stacks/TorsorStackDescent.lean`) together with
effectiveness of descent of objects along a covering sieve containing a single surjective flat
morphism locally of finite presentation. -/
def TorsorStack (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G) : Prop :=
  TorsorPrestack G U ∧
    ∀ (S : Scheme.{u}) (R : Sieve S), R ∈ fppfJ.{u} S → ∀ (D : TorsorDescentDatum G U S R)
      (W : Scheme.{u}) (w : W ⟶ S), R.arrows w → Flat w → LocallyOfFinitePresentation w →
        Surjective w →
      ∃ (N : ActionTorsor G U S) (ε : ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f),
          D.torsor f hf ≅ pullbackObj f N),
        ∀ {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
          (hf : R.arrows f) (hh' : R.arrows h),
          (ε h hh').hom.iso.hom ≫ proj N h =
            (D.trans f g h hh hf hh').iso.hom ≫ proj (D.torsor f hf) g ≫
              (ε f hf).hom.iso.hom ≫ proj N f

/-- **`[U/G]` is a stack**, unconditionally. -/
theorem torsorStack (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G) :
    TorsorStack G U :=
  ⟨torsorPrestack G U, fun _ _ hR D _ w hw h1 h2 h3 ↦
    exists_torsor_of_torsorDescentDatum hR D w hw h1 h2 h3⟩

end ActionTorsor

end GromovWitten.AlgebraicGeometry
