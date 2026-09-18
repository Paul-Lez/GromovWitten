/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.TorsorStack
import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Descent of morphisms for the quotient prestack `[U/G]`

`Stacks/QuotientStackPullback.lean` builds the pseudofunctor
`ActionTorsor.pullbackPseudofunctor G U : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat`, the quotient
prestack `[U/G]`, and `Stacks/TorsorStack.lean` supplies the sheaf-theoretic gluing inputs
(`RelHomFamily.glue`, `hom_ext_of_cover`, `isIso_of_cover`) together with the computations of
the pseudofunctorial comparison cells on the projections (`mapComp'_pair_proj` and friends).
This file combines the two and proves that `[U/G]` satisfies descent of morphisms for the big
fppf topology.

## Contents

* `descent_compat_aux` is the purely categorical cancellation step behind the descent of
  morphisms; it is stated for an arbitrary category and all of its data is explicit.
* `hom_ext_of_cover_whiskerLeft` extends the separatedness statement `hom_ext_of_cover` of
  `Stacks/TorsorStack.lean` from morphisms out of an fppf sheaf `A` over a base to morphisms
  out of `V ⊗ A`; this is what makes the glued morphism `G`-equivariant.
* `ActionTorsor.TorsorHomFamily M N R` is the descent datum for morphisms: a family of arrows
  `f^* M ⟶ f^* N` of equivariant torsors, indexed by the members of a sieve `R` on `S`,
  compatible with further base change.  All of its data is explicit; no pseudofunctorial
  coherence cell occurs in the statement.
* `ActionTorsor.TorsorHomFamily.glueHom` glues such a family to an arrow `M ⟶ N`.  The glued
  morphism of sheaves is `glueSheafHom`; `proj_glueSheafHom` is its defining property,
  `glueSheafHom_over`, `glueSheafHom_target` and `glueSheafHom_equivariant` are the three
  compatibilities making it an arrow of `[U/G]`, and `isIso_glueSheafHom` (via
  `relMap_glueSheafHom` and `isIso_of_cover`) makes it invertible.
* `ActionTorsor.pullbackFunctor_map_glueHom` identifies the base changes of the glued arrow
  with the given family, and `ActionTorsor.hom_ext_of_cover_torsor` is the corresponding
  uniqueness statement; `ActionTorsor.pullbackFunctor_map_eq_iff` is the sheaf-level criterion
  for an arrow to restrict to a given arrow on a member of the sieve.
* `ActionTorsor.existsUnique_hom_of_torsorHomFamily` packages the two: **descent of morphisms**.
* `ActionTorsor.TorsorPrestack G U` is the resulting `Prop`, and
  `ActionTorsor.torsorPrestack` proves it unconditionally.

## Why this is not stated with Mathlib's `Pseudofunctor.IsPrestack`

`ActionTorsor.TorsorPrestack G U` is, unwound, exactly the sheaf condition for
`Pseudofunctor.presheafHom M N` on `Over S` with respect to `fppfJ.over S`, i.e. the content of
`Pseudofunctor.IsPrestack fppfJ (pullbackPseudofunctor G U)`.  The Mathlib *statement* is fine:
the type `Pseudofunctor.IsPrestack (pullbackPseudofunctor G U) fppfJ`, and likewise
`Pseudofunctor.IsStack`, `Pseudofunctor.IsStackFor`, `(pullbackPseudofunctor G U).presheafHom`
and `(pullbackPseudofunctor G U).toDescentData`, elaborate and kernel-check in milliseconds.
What does not work is the *proof*.  Every route into the Mathlib API goes through
`Pseudofunctor.DescentData` for `pullbackPseudofunctor G U`, and there the comparison between
the two descriptions of a fibre — `Pseudofunctor.DescentData.ofObj M |>.obj i` on one side and
`ActionTorsor.pullbackObj (f i) M` on the other — is only *definitional*.  Three concrete walls
were measured (all timings from `lake env lean` on a one-declaration file):

1. `rw [Pseudofunctor.DescentData.ofObj_hom]` fails outright: the rewrite motive is not type
   correct at `implicit` transparency.  Replacing it by `exact` against
   `ActionTorsor.mapComp'_pair_proj` works in milliseconds — that is `ofObj_hom_proj` above,
   which is kept in this file because it is the one usable bridge.
2. `rw` with any lemma about `ActionTorsor` (for instance `proj_comp_map`) fails on a goal that
   mixes the two descriptions, because `rw` unifies at `instances` transparency.
3. The kernel itself diverges on `Pseudofunctor.DescentData.Hom.comm`.  A one-declaration file
   containing nothing but that equation, written out for `pullbackPseudofunctor G U` at
   `f₁ = 𝟙` and proved by `exact φ.comm …`, gives `(kernel) deterministic timeout` already at
   `maxHeartbeats 40000`, while `ofObj_hom_proj` below, `Pseudofunctor.IsPrestack`/`IsStack`/
   `IsStackFor`/`presheafHom`/`toDescentData` as statements,
   `Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom` instantiated here, `proj_comp_map` at a
   `DescentData.Hom` component and `Epi (proj (pullbackObj b M) (𝟙 Y))` all pass at
   `maxHeartbeats 20000`.  Since the `comm` field has to be consumed (for fullness) and produced
   (for the functor `toDescentData`) on any route to `Pseudofunctor.IsPrestackFor`, Mathlib's
   descent API is unusable at this pseudofunctor as it stands.

Since the mathematics is finished (it is `existsUnique_hom_of_torsorHomFamily`), the choice made
here is the one recorded in `Stacks/TorsorStack.lean`: state the result in this repository with
explicit data rather than fight Mathlib's elaboration.  Turning `TorsorPrestack G U` into
`Pseudofunctor.IsPrestack fppfJ (pullbackPseudofunctor G U)` is a purely formal step that needs
either a Mathlib-side `@[simp]`/`abbrev` interface for `DescentData.ofObj` at a concrete
pseudofunctor, or the `pullbackPseudofunctor` to be built by a construction whose `obj`/`map`
fields reduce without unfolding `LocallyDiscrete.mkPseudofunctor`.

## Effectiveness of descent

Effectiveness (`Pseudofunctor.IsStack`, or a repository-level analogue) is *not* proved here.
Its sheaf-theoretic half is now available unconditionally as
`GromovWitten.AlgebraicGeometry.sheafDescentInput` in `Stacks/SieveDescentEffective.lean`; what
is still missing is the transport of the `G`-action, the principality and the map to `U` along
the glued sheaf, together with the same `DescentData` bridge discussed above.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open CategoryTheory.Bicategory
open scoped CategoryTheory.MonoidalCategory
open Opposite
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u v

/-- The algebraic core of the descent of morphisms.  In any category, the compatibility of a
morphism of descent data with base change follows by cancelling the (epimorphic) projection
`p1` (hypothesis `hp1`) from the four naturality squares `hA1`, `hA2`, `hB1`, `hB2`, the
cocycle identity `hs` and the identity `hrN`.  Isolating this step keeps every use of the
pseudofunctorial data at the level of `exact`, at default transparency. -/
theorem descent_compat_aux {C : Type*} [Category C]
    {Z Z' Wm Wn Mh Nh Mf Nf NS : C} (p1 : Z ⟶ Mh) (q1 : Z' ⟶ Nh) (a1 : Z ⟶ Z')
    (b1 : Z' ⟶ Wn) (pn : Wn ⟶ Nf) (b2 : Z ⟶ Wm) (pm : Wm ⟶ Mf) (a2 : Wm ⟶ Wn)
    (φ1 : Mh ⟶ Nh) (φ2 : Mf ⟶ Nf) (rM : Mh ⟶ Mf) (rN : Nh ⟶ Nf) (tN : Nf ⟶ NS)
    (tNh : Nh ⟶ NS) (hA1 : p1 ≫ φ1 = a1 ≫ q1) (hA2 : pm ≫ φ2 = a2 ≫ pn)
    (hB1 : b1 ≫ pn = q1 ≫ rN) (hB2 : b2 ≫ pm = p1 ≫ rM) (hs : a1 ≫ b1 = b2 ≫ a2)
    (hrN : rN ≫ tN = tNh) (hp1 : Epi p1) :
    φ1 ≫ tNh = rM ≫ φ2 ≫ tN := by
  have hA1' := reassoc_of% hA1
  have hA2' := reassoc_of% hA2
  have hB1' := reassoc_of% hB1
  have hB2' := reassoc_of% hB2
  have hs' := reassoc_of% hs
  rw [← cancel_epi p1, hA1', ← hrN, ← hB1', hs', ← hA2', hB2']

section Separated

variable {S : Scheme.{u}} {A B V : FppfSheaf.{u}}

/-- Separatedness for morphisms out of a product: two morphisms `V ⊗ A ⟶ B` of fppf sheaves
which agree after base change of `A` along every member of a covering sieve of the base are
equal.  This is the variant of `hom_ext_of_cover` needed to check equivariance of a glued
morphism of torsors. -/
theorem hom_ext_of_cover_whiskerLeft (V : FppfSheaf.{u}) (π : A ⟶ fppfYoneda.obj S)
    {R : Sieve S} (hR : R ∈ fppfJ.{u} S) {ψ ψ' : V ⊗ A ⟶ B}
    (h : ∀ {X : Scheme.{u}} (f : X ⟶ S), R.arrows f →
      V ◁ pullback.fst π (fppfYoneda.map f) ≫ ψ =
        V ◁ pullback.fst π (fppfYoneda.map f) ≫ ψ') :
    ψ = ψ' := by
  apply fppfSheaf_hom_ext
  intro Z α
  have hstab := fppfJ.pullback_stable (baseOf π (α ≫ snd V A)) hR
  have hsep : Presieve.IsSeparatedFor B.obj
      (R.pullback (baseOf π (α ≫ snd V A))).arrows :=
    (RelHomFamily.isSheaf_obj B _ hstab).isSeparatedFor
  apply fppfJ.yonedaEquiv.injective
  apply hsep.ext
  intro W k hk
  rw [fppfJ.yonedaEquiv_naturality, fppfJ.yonedaEquiv_naturality]
  refine congrArg _ ?_
  have hcond : fppfYoneda.map k ≫ (α ≫ snd V A) ≫ π =
      fppfYoneda.map (k ≫ baseOf π (α ≫ snd V A)) := by
    simp [Functor.map_comp]
  have hkey : fppfYoneda.map k ≫ α =
      lift (fppfYoneda.map k ≫ α ≫ fst V A)
          (relSection π (α ≫ snd V A) k (k ≫ baseOf π (α ≫ snd V A)) hcond) ≫
        V ◁ pullback.fst π (fppfYoneda.map (k ≫ baseOf π (α ≫ snd V A))) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, whiskerLeft_fst, lift_fst]
    · rw [Category.assoc, Category.assoc, whiskerLeft_snd, lift_snd_assoc, relSection_fst]
  have key : ∀ χ : V ⊗ A ⟶ B, fppfYoneda.map k ≫ α ≫ χ =
      lift (fppfYoneda.map k ≫ α ≫ fst V A)
          (relSection π (α ≫ snd V A) k (k ≫ baseOf π (α ≫ snd V A)) hcond) ≫
        (V ◁ pullback.fst π (fppfYoneda.map (k ≫ baseOf π (α ≫ snd V A)))) ≫ χ := fun χ ↦ by
    rw [← Category.assoc, hkey, Category.assoc]
  rw [key ψ, key ψ', h (k ≫ baseOf π (α ≫ snd V A)) hk]

end Separated

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {S : Scheme.{u}}

/-- A descent datum for morphisms of equivariant torsors: a family of arrows
`f^* M ⟶ f^* N` in the fibres of `[U/G]`, indexed by the members `f : X ⟶ S` of a sieve `R`
on `S`, compatible with further base change inside the sieve.  The compatibility is stated on
the underlying sheaves, through the projections `proj N f : (f^* N).P ⟶ N.P` and the
comparison morphisms `relBaseChange`; no pseudofunctorial coherence cell occurs. -/
structure TorsorHomFamily (M N : ActionTorsor G U S) (R : Sieve S) where
  /-- The arrow attached to a member of the sieve. -/
  hom {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) : pullbackObj f M ⟶ pullbackObj f N
  /-- Compatibility with further base change inside the sieve. -/
  compat {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
    (hf : R.arrows f) (hh' : R.arrows h) :
    (hom h hh').iso.hom ≫ proj N h =
      relBaseChange M.projection f g h hh ≫ (hom f hf).iso.hom ≫ proj N f

namespace TorsorHomFamily

variable {M N : ActionTorsor G U S} {R : Sieve S}

/-- The family of morphisms of fppf sheaves underlying a descent datum for morphisms. -/
noncomputable def toRelHomFamily (u : TorsorHomFamily M N R) :
    RelHomFamily M.projection N.P R where
  hom f hf := (u.hom f hf).iso.hom ≫ proj N f
  compat f g h hh hf hh' := u.compat f g h hh hf hh'

/-- The glued morphism of fppf sheaves attached to a descent datum for morphisms. -/
noncomputable def glueSheafHom (u : TorsorHomFamily M N R) (hR : R ∈ fppfJ.{u} S) :
    M.P ⟶ N.P :=
  u.toRelHomFamily.glue hR

/-- The glued morphism restricts to the given family on every member of the sieve. -/
theorem proj_glueSheafHom (u : TorsorHomFamily M N R) (hR : R ∈ fppfJ.{u} S)
    {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) :
    proj M f ≫ u.glueSheafHom hR = (u.hom f hf).iso.hom ≫ proj N f :=
  u.toRelHomFamily.glue_spec hR f hf

/-- The glued morphism lies over the base. -/
theorem glueSheafHom_over (u : TorsorHomFamily M N R) (hR : R ∈ fppfJ.{u} S) :
    u.glueSheafHom hR ≫ N.projection = M.projection := by
  refine hom_ext_of_cover M.projection hR ?_
  intro X f hf
  rw [← Category.assoc, u.proj_glueSheafHom hR f hf, Category.assoc,
    pullback.condition (f := N.projection) (g := fppfYoneda.map f), ← Category.assoc,
    (u.hom f hf).over, pullback.condition (f := M.projection) (g := fppfYoneda.map f)]

/-- The glued morphism commutes with the maps to `U`. -/
theorem glueSheafHom_target (u : TorsorHomFamily M N R) (hR : R ∈ fppfJ.{u} S) :
    u.glueSheafHom hR ≫ N.target = M.target := by
  refine hom_ext_of_cover M.projection hR ?_
  intro X f hf
  rw [← Category.assoc, u.proj_glueSheafHom hR f hf, Category.assoc]
  exact (u.hom f hf).target

/-- The glued morphism is `G`-equivariant. -/
theorem glueSheafHom_equivariant (u : TorsorHomFamily M N R) (hR : R ∈ fppfJ.{u} S) :
    ModObj.smul (M := G.space.toSheaf) (X := M.P) ≫ u.glueSheafHom hR =
      G.space.toSheaf ◁ u.glueSheafHom hR ≫
        ModObj.smul (M := G.space.toSheaf) (X := N.P) := by
  refine hom_ext_of_cover_whiskerLeft G.space.toSheaf M.projection hR ?_
  intro X f hf
  have h1 : G.space.toSheaf ◁ proj M f ≫ ModObj.smul (M := G.space.toSheaf) (X := M.P) =
      FppfTorsor.pullbackSmul M.toFppfTorsor f ≫ proj M f :=
    (FppfTorsor.pullbackSmul_fst M.toFppfTorsor f).symm
  have h2 : G.space.toSheaf ◁ proj N f ≫ ModObj.smul (M := G.space.toSheaf) (X := N.P) =
      FppfTorsor.pullbackSmul N.toFppfTorsor f ≫ proj N f :=
    (FppfTorsor.pullbackSmul_fst N.toFppfTorsor f).symm
  have heqv : FppfTorsor.pullbackSmul M.toFppfTorsor f ≫ (u.hom f hf).iso.hom =
      G.space.toSheaf ◁ (u.hom f hf).iso.hom ≫ FppfTorsor.pullbackSmul N.toFppfTorsor f :=
    (u.hom f hf).equivariant
  calc G.space.toSheaf ◁ proj M f ≫
        (ModObj.smul (M := G.space.toSheaf) (X := M.P) ≫ u.glueSheafHom hR)
      = (G.space.toSheaf ◁ proj M f ≫ ModObj.smul (M := G.space.toSheaf) (X := M.P)) ≫
          u.glueSheafHom hR := (Category.assoc _ _ _).symm
    _ = FppfTorsor.pullbackSmul M.toFppfTorsor f ≫ proj M f ≫ u.glueSheafHom hR := by
        rw [h1, Category.assoc]
    _ = FppfTorsor.pullbackSmul M.toFppfTorsor f ≫ (u.hom f hf).iso.hom ≫ proj N f := by
        rw [u.proj_glueSheafHom hR f hf]
    _ = (G.space.toSheaf ◁ (u.hom f hf).iso.hom) ≫
          FppfTorsor.pullbackSmul N.toFppfTorsor f ≫ proj N f := by
        rw [← Category.assoc, heqv, Category.assoc]
    _ = (G.space.toSheaf ◁ (u.hom f hf).iso.hom) ≫
          (G.space.toSheaf ◁ proj N f) ≫ ModObj.smul (M := G.space.toSheaf) (X := N.P) := by
        rw [← h2]
    _ = G.space.toSheaf ◁ proj M f ≫
          (G.space.toSheaf ◁ u.glueSheafHom hR ≫
            ModObj.smul (M := G.space.toSheaf) (X := N.P)) := by
        rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
          ← u.proj_glueSheafHom hR f hf, MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- The base change of the glued morphism along a member of the sieve is the given arrow. -/
theorem relMap_glueSheafHom (u : TorsorHomFamily M N R) (hR : R ∈ fppfJ.{u} S)
    {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) :
    relMap M.projection N.projection (u.glueSheafHom hR) (u.glueSheafHom_over hR) f =
      (u.hom f hf).iso.hom := by
  apply pullback.hom_ext
  · rw [relMap_fst]
    exact u.proj_glueSheafHom hR f hf
  · rw [relMap_snd]
    exact ((u.hom f hf).over).symm

/-- The glued morphism of fppf sheaves is an isomorphism. -/
theorem isIso_glueSheafHom (u : TorsorHomFamily M N R) (hR : R ∈ fppfJ.{u} S) :
    IsIso (u.glueSheafHom hR) := by
  refine isIso_of_cover M.projection N.projection _ (u.glueSheafHom_over hR) hR ?_
  intro X f hf
  rw [u.relMap_glueSheafHom hR f hf]
  infer_instance

/-- The arrow `M ⟶ N` of equivariant torsors glued from a descent datum for morphisms. -/
noncomputable def glueHom (u : TorsorHomFamily M N R) (hR : R ∈ fppfJ.{u} S) : M ⟶ N :=
  { iso := @asIso _ _ _ _ (u.glueSheafHom hR) (u.isIso_glueSheafHom hR)
    over := u.glueSheafHom_over hR
    equivariant := u.glueSheafHom_equivariant hR
    target := u.glueSheafHom_target hR }

@[simp]
theorem glueHom_iso_hom (u : TorsorHomFamily M N R) (hR : R ∈ fppfJ.{u} S) :
    (u.glueHom hR).iso.hom = u.glueSheafHom hR :=
  rfl

end TorsorHomFamily

/-- Two arrows of equivariant torsors which agree after base change along every member of a
covering sieve of the base are equal. -/
theorem hom_ext_of_cover_torsor {M N : ActionTorsor G U S} {R : Sieve S}
    (hR : R ∈ fppfJ.{u} S) {ψ ψ' : M ⟶ N}
    (h : ∀ {X : Scheme.{u}} (f : X ⟶ S), R.arrows f →
      proj M f ≫ ψ.iso.hom = proj M f ≫ ψ'.iso.hom) :
    ψ = ψ' :=
  Hom.ext _ _ (hom_ext_of_cover M.projection hR h)

/-- Base change of an arrow of equivariant torsors is determined by its effect on the
projections. -/
theorem pullbackFunctor_map_eq_iff {M N : ActionTorsor G U S} {X : Scheme.{u}} (f : X ⟶ S)
    (ψ : M ⟶ N) (φ : pullbackObj f M ⟶ pullbackObj f N) :
    (pullbackFunctor f).map ψ = φ ↔ proj M f ≫ ψ.iso.hom = φ.iso.hom ≫ proj N f := by
  constructor
  · rintro rfl
    exact (FppfTorsor.pullbackMap_fst f ψ.iso.hom ψ.over).symm
  · intro h
    refine Hom.ext _ _ (pullback.hom_ext ?_ ?_)
    · rw [pullbackFunctor_map_iso_hom, FppfTorsor.pullbackMap_fst]
      exact h
    · rw [pullbackFunctor_map_iso_hom, FppfTorsor.pullbackMap_snd]
      exact (φ.over).symm

/-- The base changes of the glued arrow are the members of the descent datum. -/
theorem pullbackFunctor_map_glueHom {M N : ActionTorsor G U S} {R : Sieve S}
    (u : TorsorHomFamily M N R) (hR : R ∈ fppfJ.{u} S) {X : Scheme.{u}} (f : X ⟶ S)
    (hf : R.arrows f) :
    (pullbackFunctor f).map (u.glueHom hR) = u.hom f hf :=
  (pullbackFunctor_map_eq_iff f _ _).2 (u.proj_glueSheafHom hR f hf)

/-- **Descent of morphisms for `[U/G]`**: a compatible family of arrows between the base
changes of two equivariant torsors along a covering sieve comes from a unique arrow of
equivariant torsors. -/
theorem existsUnique_hom_of_torsorHomFamily {M N : ActionTorsor G U S} {R : Sieve S}
    (hR : R ∈ fppfJ.{u} S) (u : TorsorHomFamily M N R) :
    ∃! ψ : M ⟶ N, ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f),
      (pullbackFunctor f).map ψ = u.hom f hf := by
  refine ⟨u.glueHom hR, fun f hf ↦ pullbackFunctor_map_glueHom u hR f hf, ?_⟩
  intro ψ hψ
  refine hom_ext_of_cover_torsor hR ?_
  intro X f hf
  have h₁ := (pullbackFunctor_map_eq_iff f ψ (u.hom f hf)).1 (hψ f hf)
  rw [h₁]
  exact (u.proj_glueSheafHom hR f hf).symm

section Bridge

variable {ι : Type v} {X : ι → Scheme.{u}}

/-- The transition morphism of the descent datum `Pseudofunctor.DescentData.ofObj M` attached
to an object `M` of `[U/G]` over `S`, read on the projections to the underlying sheaf of `M`.

This is the repository-local version of `Pseudofunctor.DescentData.ofObj_hom` at
`pullbackPseudofunctor G U`: instead of `rw`, which fails on that lemma (see the module
docstring), it is proved by `exact` from `ActionTorsor.mapComp'_pair_proj`, whose statement
carries the two `mapComp'` coherence proofs as explicit data.  It type-checks — elaborator and
kernel — in milliseconds, whereas Mathlib's own formulation does not. -/
theorem ofObj_hom_proj (M : ActionTorsor G U S) (fam : ∀ i, X i ⟶ S) {i₁ i₂ : ι}
    (g : X i₁ ⟶ X i₂) (hh : g ≫ fam i₂ = fam i₁) :
    ((Pseudofunctor.DescentData.ofObj (F := pullbackPseudofunctor G U) (f := fam) M).hom
        (fam i₁) (𝟙 (X i₁)) g (Category.id_comp _) hh).iso.hom ≫
        proj (pullbackObj (fam i₂) M) g =
      proj (pullbackObj (fam i₁) M) (𝟙 (X i₁)) ≫
        relBaseChange M.projection (fam i₂) g (fam i₁) hh :=
  mapComp'_pair_proj M (fam i₂) g (fam i₁) hh _ _

end Bridge

/-- **Descent of morphisms for `[U/G]`, as a repository-level predicate.**  For every scheme
`S`, every fppf covering sieve `R` on `S` and all equivariant torsors `M N` over `S`, every
compatible family of arrows between the base changes of `M` and `N` along the members of `R`
comes from a unique arrow `M ⟶ N`.  This is exactly the sheaf condition for the presheaf
`p ↦ (p^* M ⟶ p^* N)` on `Over S`, written with explicit data: no pseudofunctorial coherence
cell occurs in it, which is what makes it usable (see the module docstring). -/
def TorsorPrestack (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G) : Prop :=
  ∀ (S : Scheme.{u}) (R : Sieve S), R ∈ fppfJ.{u} S → ∀ (M N : ActionTorsor G U S)
    (u : TorsorHomFamily M N R), ∃! ψ : M ⟶ N, ∀ {X : Scheme.{u}} (f : X ⟶ S)
      (hf : R.arrows f), (pullbackFunctor f).map ψ = u.hom f hf

/-- **The quotient prestack `[U/G]` satisfies descent of morphisms for the big fppf
topology.**  This is unconditional. -/
theorem torsorPrestack (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G) :
    TorsorPrestack G U :=
  fun _ _ hR _ _ u ↦ existsUnique_hom_of_torsorHomFamily hR u

end ActionTorsor

end GromovWitten.AlgebraicGeometry
