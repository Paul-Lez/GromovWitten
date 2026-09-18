/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.QuotientStackClassifying

/-!
# Gluing morphisms of fppf sheaves over a base, and descent for equivariant torsors

The quotient prestack `[U/G]` of `Stacks/QuotientStackClassifying.lean` is the groupoid-valued
pseudofunctor `ActionTorsor.pullbackPseudofunctor G U` on the big fppf site of schemes, whose
fibre over a scheme `T` is the groupoid of fppf `G`-torsors over `T` with an equivariant map to
`U`.  Both remaining steps towards bundling it as an `FppfStack` (descent of arrows and
effectiveness of descent) rest on gluing data for fppf sheaves over a base.  This file supplies
that sheaf theory, unconditionally and completely explicitly.

## Gluing morphisms of fppf sheaves over a base

Note that `Sheaf Scheme.fppfTopology (Type u)` has no sheafification available (the universes
do not match), so every construction below is explicit.  Fix a morphism
`π : A ⟶ fppfYoneda.obj S` of fppf sheaves and a sieve `R` on `S`.

* `relBaseChange π f g h hh` is the comparison morphism `A ×_S Y ⟶ A ×_S X` attached to a
  factorisation `g ≫ f = h`;
* `relSection π α k f hf` is the section of `A ×_S W` determined by a morphism
  `α : fppfYoneda.obj Z ⟶ A` and a morphism `k : W ⟶ Z`;
* `RelHomFamily π B R` is a compatible family of morphisms `A ×_S X ⟶ B`, indexed by the
  members `f : X ⟶ S` of `R`;
* `fppfSheaf_hom_ext` is Yoneda extensionality for morphisms of fppf sheaves;
* `hom_ext_of_cover` is separatedness: two morphisms `A ⟶ B` which agree after base change
  along every member of a covering sieve of `S` are equal;
* `RelHomFamily.glue` and `RelHomFamily.glue_spec` glue a compatible family to a morphism
  `A ⟶ B`.  The glued morphism is built with `Presieve.IsSheafFor.amalgamate`, applied on each
  test scheme to the sieve obtained by pulling `R` back along the structure morphism
  `baseOf π α` of a section of `A`;
* `relMap π κ ψ hψ f` is the base change of a morphism over `S` along a member of the sieve,
  and `isIso_of_cover` shows that a morphism of fppf sheaves over a base which becomes an
  isomorphism after base change to every member of a covering sieve is an isomorphism (the
  inverse is glued from the local inverses, `relInvFamily`).

All of the above is unconditional.

## Base change of equivariant torsors against the projections

The second part identifies the pseudofunctorial comparison isomorphisms of iterated base change
for `ActionTorsor.pullbackPseudofunctor G U` with the explicit fibre products:
`proj`, `proj₂`, `map_toLoc_map_iso_hom`, `proj_comp_map`, `mapComp_hom_app_proj`,
`mapComp_inv_app_proj`, `mapComp'_hom_app_proj`, `mapComp'_inv_app_proj`,
`mapComp'_hom_app_projOuter`, `mapComp'_inv_app_projOuter_id` and `isIso_projOuter_id`.
`fibre_comp_iso_hom` computes a composite in a fibre on underlying sheaves, and
`mapComp'_pair_proj` assembles the two comparison cells exactly as they occur in
`Pseudofunctor.DescentData.ofObj`.  These are the computations needed to feed a morphism of
descent data into `RelHomFamily`.

## What is still missing

Two statements remain open and neither is assumed anywhere below.

1. *Descent of arrows*: that `Pseudofunctor.toDescentData` for
   `ActionTorsor.pullbackPseudofunctor G U` is fully faithful along every fppf covering sieve.
   All the mathematical ingredients are available in this file (`RelHomFamily.glue`,
   `hom_ext_of_cover`, `isIso_of_cover`, `mapComp'_pair_proj`); what blocks it is
   *performance*, not mathematics.  Every route into Mathlib's descent API passes through one
   of the two lemmas `Pseudofunctor.DescentData.ofObj_hom` and
   `Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom`, whose statements embed
   tactic-generated proofs inside `Pseudofunctor.mapComp'`.  Instantiating either of them at
   `pullbackPseudofunctor G U` elaborates in under a second but its *kernel* type check does
   not terminate (still running after ten minutes with `maxHeartbeats 0`), whereas the same
   instantiation at a discrete pseudofunctor `Pseudofunctor.ofPresheafOfTypes P` over the same
   base category costs 109 ms.  The blow-up is not caused by inline proofs in
   `pullbackPseudofunctor` (extracting them into `pullbackPs_associator`,
   `pullbackPs_leftUnitor`, `pullbackPs_rightUnitor` leaves the timings unchanged), and every
   lemma stated here with the `mapComp'` coherence proof as an *explicit hypothesis*
   (`mapComp'_hom_app_proj`, `mapComp'_hom_app_projOuter`, `mapComp'_pair_proj`,
   `fibre_comp_iso_hom`) type-checks in milliseconds.
2. *Effectiveness of descent*: that the same functor is essentially surjective.  The only
   sheaf-theoretic input which this repository does not yet contain is isolated below as
   `SheafDescentDatum` and `SheafDescentInput`.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open CategoryTheory.Bicategory
open scoped CategoryTheory.MonoidalCategory
open Opposite
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

/-- In any category, a morphism with a common one-sided inverse is determined. -/
theorem eq_of_comp_eq_id {C : Type*} [Category C] {X Y : C} {d p : X ⟶ Y} {e : Y ⟶ X}
    (h1 : e ≫ p = 𝟙 Y) (h2 : d ≫ e = 𝟙 X) : d = p := by
  rw [← Category.comp_id d, ← h1, ← Category.assoc, h2, Category.id_comp]

/-- The fppf topology on the category of schemes. -/
abbrev fppfJ : GrothendieckTopology Scheme.{u} :=
  (_root_.AlgebraicGeometry.Scheme.fppfTopology : GrothendieckTopology Scheme.{u})

/-- yoneda-style extensionality for maps of fppf sheaves. -/
theorem fppfSheaf_hom_ext {A B : FppfSheaf.{u}} {ψ ψ' : A ⟶ B}
    (h : ∀ (X : Scheme.{u}) (α : fppfYoneda.obj X ⟶ A), α ≫ ψ = α ≫ ψ') : ψ = ψ' := by
  apply Sheaf.hom_ext
  ext X a
  obtain ⟨X⟩ := X
  have h1 := fppfJ.yonedaEquiv_comp (fppfJ.yonedaEquiv.symm a) ψ
  have h2 := fppfJ.yonedaEquiv_comp (fppfJ.yonedaEquiv.symm a) ψ'
  rw [Equiv.apply_symm_apply] at h1 h2
  change (ConcreteCategory.hom (ψ.hom.app (Opposite.op X))) a =
    (ConcreteCategory.hom (ψ'.hom.app (Opposite.op X))) a
  rw [← h1, ← h2, h X (fppfJ.yonedaEquiv.symm a)]


section Glue

variable {S : Scheme.{u}} {A B : FppfSheaf.{u}}

/-- The comparison morphism `A ×_S Y ⟶ A ×_S X` attached to a factorisation `g ≫ f = h`. -/
noncomputable def relBaseChange (π : A ⟶ fppfYoneda.obj S) {X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h) :
    pullback π (fppfYoneda.map h) ⟶ pullback π (fppfYoneda.map f) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ fppfYoneda.map g) (by
    rw [pullback.condition, Category.assoc, ← Functor.map_comp, hh])

@[reassoc (attr := simp)]
theorem relBaseChange_fst (π : A ⟶ fppfYoneda.obj S) {X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h) :
    relBaseChange π f g h hh ≫ pullback.fst π (fppfYoneda.map f) =
      pullback.fst π (fppfYoneda.map h) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem relBaseChange_snd (π : A ⟶ fppfYoneda.obj S) {X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h) :
    relBaseChange π f g h hh ≫ pullback.snd π (fppfYoneda.map f) =
      pullback.snd π (fppfYoneda.map h) ≫ fppfYoneda.map g :=
  pullback.lift_snd _ _ _

/-- A compatible family of morphisms out of the base changes of `A` along the members of a
sieve on the base `S`. -/
structure RelHomFamily (π : A ⟶ fppfYoneda.obj S) (B : FppfSheaf.{u}) (R : Sieve S) where
  /-- The morphism attached to a member of the sieve. -/
  hom {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) : pullback π (fppfYoneda.map f) ⟶ B
  /-- Compatibility with further base change inside the sieve. -/
  compat {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
    (hf : R.arrows f) (hh' : R.arrows h) :
    hom h hh' = relBaseChange π f g h hh ≫ hom f hf

/-- The canonical section of a base change of `A` determined by a morphism from a
representable sheaf. -/
noncomputable def relSection (π : A ⟶ fppfYoneda.obj S) {Z W : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) (k : W ⟶ Z) (f : W ⟶ S)
    (hf : fppfYoneda.map k ≫ α ≫ π = fppfYoneda.map f) :
    fppfYoneda.obj W ⟶ pullback π (fppfYoneda.map f) :=
  pullback.lift (fppfYoneda.map k ≫ α) (𝟙 _) (by rw [Category.assoc, hf, Category.id_comp])

@[reassoc (attr := simp)]
theorem relSection_fst (π : A ⟶ fppfYoneda.obj S) {Z W : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) (k : W ⟶ Z) (f : W ⟶ S)
    (hf : fppfYoneda.map k ≫ α ≫ π = fppfYoneda.map f) :
    relSection π α k f hf ≫ pullback.fst π (fppfYoneda.map f) = fppfYoneda.map k ≫ α :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem relSection_snd (π : A ⟶ fppfYoneda.obj S) {Z W : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) (k : W ⟶ Z) (f : W ⟶ S)
    (hf : fppfYoneda.map k ≫ α ≫ π = fppfYoneda.map f) :
    relSection π α k f hf ≫ pullback.snd π (fppfYoneda.map f) = 𝟙 _ :=
  pullback.lift_snd _ _ _

theorem relSection_comp (π : A ⟶ fppfYoneda.obj S) {Z Z' W : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) (q : Z' ⟶ Z) (k : W ⟶ Z') (f : W ⟶ S)
    (hf : fppfYoneda.map k ≫ (fppfYoneda.map q ≫ α) ≫ π = fppfYoneda.map f)
    (hf' : fppfYoneda.map (k ≫ q) ≫ α ≫ π = fppfYoneda.map f) :
    relSection π (fppfYoneda.map q ≫ α) k f hf = relSection π α (k ≫ q) f hf' := by
  apply pullback.hom_ext <;> simp [Functor.map_comp]

theorem relSection_precomp (π : A ⟶ fppfYoneda.obj S) {Z W V : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) (k : W ⟶ Z) (f : W ⟶ S)
    (hf : fppfYoneda.map k ≫ α ≫ π = fppfYoneda.map f) (l : V ⟶ W) (f' : V ⟶ S)
    (hff : l ≫ f = f') (hf' : fppfYoneda.map (l ≫ k) ≫ α ≫ π = fppfYoneda.map f') :
    fppfYoneda.map l ≫ relSection π α k f hf =
      relSection π α (l ≫ k) f' hf' ≫ relBaseChange π f l f' hff := by
  apply pullback.hom_ext <;> simp [Functor.map_comp]


namespace RelHomFamilyPre
end RelHomFamilyPre

namespace RelHomFamily

variable {π : A ⟶ fppfYoneda.obj S} {R : Sieve S}

/-- The element of `B` over `W` attached to a section of a base change of `A`. -/
noncomputable def famElt (u : RelHomFamily π B R) {Z W : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) (k : W ⟶ Z) (f : W ⟶ S)
    (hf : fppfYoneda.map k ≫ α ≫ π = fppfYoneda.map f) (hR : R.arrows f) :
    B.obj.obj (Opposite.op W) :=
  fppfJ.yonedaEquiv (relSection π α k f hf ≫ u.hom f hR)

theorem famElt_congr (u : RelHomFamily π B R) {Z W : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) (k : W ⟶ Z) (f f' : W ⟶ S)
    (hf : fppfYoneda.map k ≫ α ≫ π = fppfYoneda.map f)
    (hf' : fppfYoneda.map k ≫ α ≫ π = fppfYoneda.map f') (hR : R.arrows f)
    (hR' : R.arrows f') : u.famElt α k f hf hR = u.famElt α k f' hf' hR' := by
  have hff : f = f' := fppfYoneda.map_injective (hf.symm.trans hf')
  subst hff
  rfl

theorem famElt_comp (u : RelHomFamily π B R) {Z Z' W : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) (q : Z' ⟶ Z) (k : W ⟶ Z') (f : W ⟶ S)
    (hf : fppfYoneda.map k ≫ (fppfYoneda.map q ≫ α) ≫ π = fppfYoneda.map f)
    (hf' : fppfYoneda.map (k ≫ q) ≫ α ≫ π = fppfYoneda.map f) (hR : R.arrows f) :
    u.famElt (fppfYoneda.map q ≫ α) k f hf hR = u.famElt α (k ≫ q) f hf' hR := by
  unfold famElt
  rw [relSection_comp π α q k f hf hf']

theorem famElt_map (u : RelHomFamily π B R) {Z W V : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) (k : W ⟶ Z) (f : W ⟶ S)
    (hf : fppfYoneda.map k ≫ α ≫ π = fppfYoneda.map f) (hR : R.arrows f) (l : V ⟶ W)
    (f' : V ⟶ S) (hff : l ≫ f = f')
    (hf' : fppfYoneda.map (l ≫ k) ≫ α ≫ π = fppfYoneda.map f') (hR' : R.arrows f') :
    ConcreteCategory.hom (B.obj.map l.op) (u.famElt α k f hf hR) =
      u.famElt α (l ≫ k) f' hf' hR' := by
  unfold famElt
  rw [fppfJ.yonedaEquiv_naturality, ← Category.assoc,
    relSection_precomp π α k f hf l f' hff hf', Category.assoc,
    u.compat f l f' hff hR hR']

end RelHomFamily

/-- The morphism to the base underlying a section of `A`. -/
noncomputable def baseOf (π : A ⟶ fppfYoneda.obj S) {Z : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) : Z ⟶ S :=
  fppfJ.yonedaEquiv (α ≫ π)

@[simp]
theorem fppfYoneda_map_baseOf (π : A ⟶ fppfYoneda.obj S) {Z : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) : fppfYoneda.map (baseOf π α) = α ≫ π :=
  fppfJ.yonedaEquiv.injective (fppfJ.yonedaEquiv_yoneda_map _)

theorem baseOf_comp (π : A ⟶ fppfYoneda.obj S) {Z Z' : Scheme.{u}} (q : Z' ⟶ Z)
    (α : fppfYoneda.obj Z ⟶ A) : baseOf π (fppfYoneda.map q ≫ α) = q ≫ baseOf π α := by
  apply fppfYoneda.map_injective
  rw [fppfYoneda_map_baseOf, Functor.map_comp, fppfYoneda_map_baseOf, Category.assoc]

namespace RelHomFamily

/-- The family of local sections of `B` attached to a section of `A`. -/
noncomputable def fam (u : RelHomFamily π B R) {Z : Scheme.{u}} (α : fppfYoneda.obj Z ⟶ A) :
    Presieve.FamilyOfElements B.obj (R.pullback (baseOf π α)).arrows :=
  fun _ k hk ↦ u.famElt α k (k ≫ baseOf π α)
    (by rw [Functor.map_comp, fppfYoneda_map_baseOf]) hk

theorem fam_compatible (u : RelHomFamily π B R) {Z : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) : (u.fam α).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro W V k l hk
  change u.famElt α (l ≫ k) ((l ≫ k) ≫ baseOf π α) _ _ =
    ConcreteCategory.hom (B.obj.map l.op) (u.famElt α k (k ≫ baseOf π α) _ hk)
  rw [u.famElt_map α k (k ≫ baseOf π α) _ hk l (l ≫ k ≫ baseOf π α) rfl
    (by simp [Functor.map_comp])
    (by simpa using (R.pullback (baseOf π α)).downward_closed hk l)]
  exact u.famElt_congr α (l ≫ k) _ _ _ _ _ _

end RelHomFamily

namespace RelHomFamily

variable {π : A ⟶ fppfYoneda.obj S} {R : Sieve S}

/-- `B` is a sheaf for the fppf topology, in the type-valued formulation. -/
theorem isSheaf_obj (B : FppfSheaf.{u}) : Presieve.IsSheaf fppfJ.{u} B.obj :=
  (isSheaf_iff_isSheaf_of_type fppfJ.{u} B.obj).1 B.property

/-- The glued section of `B` attached to a section of `A`. -/
noncomputable def glueOf (hR : R ∈ fppfJ.{u} S) (u : RelHomFamily π B R) {Z : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) : B.obj.obj (Opposite.op Z) :=
  (isSheaf_obj B _ (fppfJ.pullback_stable (baseOf π α) hR)).amalgamate (u.fam α)
    (u.fam_compatible α)

theorem glueOf_spec (hR : R ∈ fppfJ.{u} S) (u : RelHomFamily π B R) {Z W : Scheme.{u}}
    (α : fppfYoneda.obj Z ⟶ A) (k : W ⟶ Z) (hk : R.arrows (k ≫ baseOf π α)) :
    ConcreteCategory.hom (B.obj.map k.op) (u.glueOf hR α) =
      u.famElt α k (k ≫ baseOf π α) (by simp [Functor.map_comp]) hk :=
  (isSheaf_obj B _ (fppfJ.pullback_stable (baseOf π α) hR)).valid_glue
    (u.fam_compatible α) k hk

theorem glueOf_naturality (hR : R ∈ fppfJ.{u} S) (u : RelHomFamily π B R)
    {Z Z' : Scheme.{u}} (q : Z' ⟶ Z) (α : fppfYoneda.obj Z ⟶ A) :
    u.glueOf hR (fppfYoneda.map q ≫ α) =
      ConcreteCategory.hom (B.obj.map q.op) (u.glueOf hR α) := by
  have hsep : Presieve.IsSeparatedFor B.obj
      (R.pullback (baseOf π (fppfYoneda.map q ≫ α))).arrows :=
    (isSheaf_obj B _ (fppfJ.pullback_stable _ hR)).isSeparatedFor
  apply hsep.ext
  intro V l hl
  have hl' : R.arrows (l ≫ baseOf π (fppfYoneda.map q ≫ α)) := hl
  rw [u.glueOf_spec hR (fppfYoneda.map q ≫ α) l hl']
  have hcomp : ∀ x : B.obj.obj (Opposite.op Z),
      ConcreteCategory.hom (B.obj.map l.op) (ConcreteCategory.hom (B.obj.map q.op) x) =
        ConcreteCategory.hom (B.obj.map (l ≫ q).op) x := by
    intro x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rw [hcomp]
  have hlq : R.arrows ((l ≫ q) ≫ baseOf π α) := by
    rw [Category.assoc, ← baseOf_comp]
    exact hl'
  rw [u.glueOf_spec hR α (l ≫ q) hlq]
  rw [u.famElt_comp α q l (l ≫ baseOf π (fppfYoneda.map q ≫ α))
    (by simp [Functor.map_comp]) (by simp [Functor.map_comp, baseOf_comp]) hl']
  exact u.famElt_congr α (l ≫ q) _ _ _ _ _ _

/-- The glued morphism of fppf sheaves attached to a compatible family. -/
noncomputable def glue (hR : R ∈ fppfJ.{u} S) (u : RelHomFamily π B R) : A ⟶ B :=
  ⟨{ app := fun Z ↦ ↾fun a ↦ u.glueOf hR
        (fppfJ.yonedaEquiv.symm (@id (A.obj.obj (Opposite.op Z.unop)) a))
     naturality := by
       intro Z Z' q
       ext a
       have h1 := fppfJ.yonedaEquiv_symm_naturality_left q.unop A
         (@id (A.obj.obj (Opposite.op Z.unop)) a)
       have h2 := u.glueOf_naturality hR q.unop
         (fppfJ.yonedaEquiv.symm (@id (A.obj.obj (Opposite.op Z.unop)) a))
       rw [h1] at h2
       exact h2 }⟩


theorem glue_spec (hR : R ∈ fppfJ.{u} S) (u : RelHomFamily π B R) {X : Scheme.{u}}
    (f : X ⟶ S) (hf : R.arrows f) :
    pullback.fst π (fppfYoneda.map f) ≫ u.glue hR = u.hom f hf := by
  apply fppfSheaf_hom_ext
  intro Z γ
  set α : fppfYoneda.obj Z ⟶ A := γ ≫ pullback.fst π (fppfYoneda.map f) with hα
  set g : Z ⟶ X := fppfJ.yonedaEquiv (γ ≫ pullback.snd π (fppfYoneda.map f)) with hg
  have hg' : fppfYoneda.map g = γ ≫ pullback.snd π (fppfYoneda.map f) :=
    fppfJ.yonedaEquiv.injective (fppfJ.yonedaEquiv_yoneda_map _)
  have hbase : baseOf π α = g ≫ f := by
    apply fppfYoneda.map_injective
    rw [fppfYoneda_map_baseOf, Functor.map_comp, hg', hα, Category.assoc,
      pullback.condition, Category.assoc]
  have hgf : R.arrows (g ≫ f) := R.downward_closed hf g
  have hgf' : R.arrows (𝟙 Z ≫ baseOf π α) := by rw [Category.id_comp, hbase]; exact hgf
  have hspec := u.glueOf_spec hR α (𝟙 Z) hgf'
  rw [op_id, CategoryTheory.Functor.map_id] at hspec
  have hval : u.glueOf hR α =
      u.famElt α (𝟙 Z) (g ≫ f) (by simp [hα, pullback.condition, hg']) hgf :=
    hspec.trans (u.famElt_congr α (𝟙 Z) _ _ _ _ _ _)
  apply fppfJ.yonedaEquiv.injective
  rw [← Category.assoc, ← hα, fppfJ.yonedaEquiv_comp]
  change u.glueOf hR (fppfJ.yonedaEquiv.symm (fppfJ.yonedaEquiv α)) = _
  rw [Equiv.symm_apply_apply, hval]
  unfold famElt
  rw [u.compat f g (g ≫ f) rfl hf hgf, ← Category.assoc]
  refine congrArg _ (congrArg (· ≫ u.hom f hf) ?_)
  apply pullback.hom_ext
  · rw [Category.assoc, relBaseChange_fst, relSection_fst, CategoryTheory.Functor.map_id,
      Category.id_comp]
  · rw [Category.assoc, relBaseChange_snd, ← Category.assoc, relSection_snd, Category.id_comp,
      hg']

end RelHomFamily


/-- Separatedness of morphisms of fppf sheaves over a base: two morphisms out of `A` which
agree after base change along every member of a covering sieve of the base are equal. -/
theorem hom_ext_of_cover (π : A ⟶ fppfYoneda.obj S) {R : Sieve S} (hR : R ∈ fppfJ.{u} S)
    {ψ ψ' : A ⟶ B}
    (h : ∀ {X : Scheme.{u}} (f : X ⟶ S), R.arrows f →
      pullback.fst π (fppfYoneda.map f) ≫ ψ = pullback.fst π (fppfYoneda.map f) ≫ ψ') :
    ψ = ψ' := by
  apply fppfSheaf_hom_ext
  intro Z α
  have hsep : Presieve.IsSeparatedFor B.obj (R.pullback (baseOf π α)).arrows :=
    (RelHomFamily.isSheaf_obj B _ (fppfJ.pullback_stable (baseOf π α) hR)).isSeparatedFor
  apply fppfJ.yonedaEquiv.injective
  apply hsep.ext
  intro W k hk
  rw [fppfJ.yonedaEquiv_naturality, fppfJ.yonedaEquiv_naturality]
  refine congrArg _ ?_
  have hcond : fppfYoneda.map k ≫ α ≫ π = fppfYoneda.map (k ≫ baseOf π α) := by
    simp [Functor.map_comp]
  have hβfst : relSection π α k (k ≫ baseOf π α) hcond ≫
      pullback.fst π (fppfYoneda.map (k ≫ baseOf π α)) = fppfYoneda.map k ≫ α :=
    relSection_fst _ _ _ _ _
  have key : ∀ χ : A ⟶ B, fppfYoneda.map k ≫ α ≫ χ =
      relSection π α k (k ≫ baseOf π α) hcond ≫
        pullback.fst π (fppfYoneda.map (k ≫ baseOf π α)) ≫ χ := fun χ ↦ by
    rw [← Category.assoc, ← hβfst, Category.assoc]
  rw [key ψ, key ψ', h (k ≫ baseOf π α) hk]

/-- The base change of a morphism over `S` along a member of a sieve on `S`. -/
noncomputable def relMap (π : A ⟶ fppfYoneda.obj S) (κ : B ⟶ fppfYoneda.obj S) (ψ : A ⟶ B)
    (hψ : ψ ≫ κ = π) {X : Scheme.{u}} (f : X ⟶ S) :
    pullback π (fppfYoneda.map f) ⟶ pullback κ (fppfYoneda.map f) :=
  pullback.lift (pullback.fst _ _ ≫ ψ) (pullback.snd _ _)
    (by rw [Category.assoc, hψ, pullback.condition])

@[reassoc (attr := simp)]
theorem relMap_fst (π : A ⟶ fppfYoneda.obj S) (κ : B ⟶ fppfYoneda.obj S) (ψ : A ⟶ B)
    (hψ : ψ ≫ κ = π) {X : Scheme.{u}} (f : X ⟶ S) :
    relMap π κ ψ hψ f ≫ pullback.fst κ (fppfYoneda.map f) =
      pullback.fst π (fppfYoneda.map f) ≫ ψ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem relMap_snd (π : A ⟶ fppfYoneda.obj S) (κ : B ⟶ fppfYoneda.obj S) (ψ : A ⟶ B)
    (hψ : ψ ≫ κ = π) {X : Scheme.{u}} (f : X ⟶ S) :
    relMap π κ ψ hψ f ≫ pullback.snd κ (fppfYoneda.map f) =
      pullback.snd π (fppfYoneda.map f) :=
  pullback.lift_snd _ _ _

theorem relBaseChange_relMap (π : A ⟶ fppfYoneda.obj S) (κ : B ⟶ fppfYoneda.obj S) (ψ : A ⟶ B)
    (hψ : ψ ≫ κ = π) {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S)
    (hh : g ≫ f = h) :
    relMap π κ ψ hψ h ≫ relBaseChange κ f g h hh =
      relBaseChange π f g h hh ≫ relMap π κ ψ hψ f := by
  apply pullback.hom_ext <;> simp

/-- The family of local inverses of a morphism over a base which is invertible on a cover. -/
noncomputable def relInvFamily (π : A ⟶ fppfYoneda.obj S) (κ : B ⟶ fppfYoneda.obj S)
    (ψ : A ⟶ B) (hψ : ψ ≫ κ = π) {R : Sieve S}
    (hiso : ∀ {X : Scheme.{u}} (f : X ⟶ S), R.arrows f → IsIso (relMap π κ ψ hψ f)) :
    RelHomFamily κ A R where
  hom {X} f hf :=
    @inv _ _ _ _ (relMap π κ ψ hψ f) (hiso f hf) ≫ pullback.fst π (fppfYoneda.map f)
  compat {X Y} f g h hh hf hh' := by
    have h₁ := hiso f hf
    have h₂ := hiso h hh'
    rw [← cancel_epi (relMap π κ ψ hψ h), IsIso.hom_inv_id_assoc, ← Category.assoc,
      ← Category.assoc, relBaseChange_relMap π κ ψ hψ f g h hh, Category.assoc,
      Category.assoc, IsIso.hom_inv_id_assoc, relBaseChange_fst]

@[simp]
theorem relInvFamily_hom (π : A ⟶ fppfYoneda.obj S) (κ : B ⟶ fppfYoneda.obj S)
    (ψ : A ⟶ B) (hψ : ψ ≫ κ = π) {R : Sieve S}
    (hiso : ∀ {X : Scheme.{u}} (f : X ⟶ S), R.arrows f → IsIso (relMap π κ ψ hψ f))
    {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) :
    (relInvFamily π κ ψ hψ hiso).hom f hf =
      @inv _ _ _ _ (relMap π κ ψ hψ f) (hiso f hf) ≫ pullback.fst π (fppfYoneda.map f) :=
  rfl

/-- A morphism of fppf sheaves over a base which becomes an isomorphism after base change to
every member of a covering sieve of the base is an isomorphism. -/
theorem isIso_of_cover (π : A ⟶ fppfYoneda.obj S) (κ : B ⟶ fppfYoneda.obj S) (ψ : A ⟶ B)
    (hψ : ψ ≫ κ = π) {R : Sieve S} (hR : R ∈ fppfJ.{u} S)
    (hiso : ∀ {X : Scheme.{u}} (f : X ⟶ S), R.arrows f → IsIso (relMap π κ ψ hψ f)) :
    IsIso ψ := by
  refine ⟨(relInvFamily π κ ψ hψ hiso).glue hR, ?_, ?_⟩
  · refine hom_ext_of_cover π hR ?_
    intro X f hf
    have := hiso f hf
    rw [← Category.assoc, ← relMap_fst π κ ψ hψ f, Category.assoc,
      (relInvFamily π κ ψ hψ hiso).glue_spec hR f hf, relInvFamily_hom,
      IsIso.hom_inv_id_assoc, Category.comp_id]
  · refine hom_ext_of_cover κ hR ?_
    intro X f hf
    have := hiso f hf
    rw [← Category.assoc, (relInvFamily π κ ψ hψ hiso).glue_spec hR f hf, relInvFamily_hom,
      Category.assoc, ← relMap_fst π κ ψ hψ f, IsIso.inv_hom_id_assoc, Category.comp_id]

end Glue

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {S : Scheme.{u}}

/-- The canonical projection of a base-changed equivariant torsor to the original sheaf. -/
noncomputable abbrev proj (M : ActionTorsor G U S) {X : Scheme.{u}} (b : X ⟶ S) :
    (pullbackObj b M).P ⟶ M.P :=
  pullback.fst M.projection (fppfYoneda.map b)

/-- The projection of a twice base-changed equivariant torsor to the original sheaf. -/
noncomputable abbrev proj₂ (M : ActionTorsor G U S) {X Y : Scheme.{u}} (b : X ⟶ S)
    (a : Y ⟶ X) : (pullbackObj a (pullbackObj b M)).P ⟶ M.P :=
  pullback.fst (pullback.snd M.projection (fppfYoneda.map b)) (fppfYoneda.map a) ≫
    pullback.fst M.projection (fppfYoneda.map b)

/-- The pseudofunctorial comparison of a composite base change is compatible with the
projections to the original sheaf. -/
theorem mapComp_hom_app_proj (M : ActionTorsor G U S) {X Y : Scheme.{u}} (b : X ⟶ S)
    (a : Y ⟶ X) :
    ((((pullbackPseudofunctor G U).mapComp
        b.op.toLoc a.op.toLoc).hom.toNatTrans.app M).iso.hom) ≫ proj₂ M b a =
      proj M (a ≫ b) :=
  FppfTorsor.pullbackCompIso_hom_fst_fst M.toFppfTorsor a b

/-- The inverse pseudofunctorial comparison of a composite base change is compatible with the
projections to the original sheaf. -/
theorem mapComp_inv_app_proj (M : ActionTorsor G U S) {X Y : Scheme.{u}} (b : X ⟶ S)
    (a : Y ⟶ X) :
    ((((pullbackPseudofunctor G U).mapComp
        b.op.toLoc a.op.toLoc).inv.toNatTrans.app M).iso.hom) ≫ proj M (a ≫ b) =
      proj₂ M b a := by
  have h : ((((pullbackPseudofunctor G U).mapComp
      b.op.toLoc a.op.toLoc).inv.toNatTrans.app M).iso.hom) =
      (FppfTorsor.pullbackCompIso M.toFppfTorsor a b).inv :=
    pullbackCompIsoApp_inv_iso_hom a b M
  rw [h]
  exact pullback.lift_fst _ _ _

/-- Version of `mapComp_hom_app_proj` for the corrected comparison isomorphism. -/
theorem mapComp'_hom_app_proj (M : ActionTorsor G U S) {X Y : Scheme.{u}} (b : X ⟶ S)
    (a : Y ⟶ X) (q : Y ⟶ S) (hq : a ≫ b = q)
    (hq' : b.op.toLoc ≫ a.op.toLoc = q.op.toLoc) :
    (((pullbackPseudofunctor G U).mapComp' b.op.toLoc a.op.toLoc q.op.toLoc
        hq').hom.toNatTrans.app M).iso.hom ≫ proj₂ M b a = proj M q := by
  subst hq
  exact mapComp_hom_app_proj M b a

/-- Version of `mapComp_inv_app_proj` for the corrected comparison isomorphism. -/
theorem mapComp'_inv_app_proj (M : ActionTorsor G U S) {X Y : Scheme.{u}} (b : X ⟶ S)
    (a : Y ⟶ X) (q : Y ⟶ S) (hq : a ≫ b = q)
    (hq' : b.op.toLoc ≫ a.op.toLoc = q.op.toLoc) :
    (((pullbackPseudofunctor G U).mapComp' b.op.toLoc a.op.toLoc q.op.toLoc
        hq').inv.toNatTrans.app M).iso.hom ≫ proj M q = proj₂ M b a := by
  subst hq
  exact mapComp_inv_app_proj M b a

/-- The action of the base-change pseudofunctor on arrows, on underlying sheaves. -/
theorem map_toLoc_map_iso_hom {X Y : Scheme.{u}} (b : Y ⟶ X) {P Q : ActionTorsor G U X}
    (φ : P ⟶ Q) :
    ((((pullbackPseudofunctor G U).map b.op.toLoc).toFunctor.map φ).iso.hom) =
      FppfTorsor.pullbackMap b φ.iso.hom φ.over :=
  rfl

/-- Base change commutes with the canonical projections to the unchanged torsors. -/
@[reassoc]
theorem proj_comp_map {T T' : Scheme.{u}} (b : T' ⟶ T) {P Q : ActionTorsor G U T} (φ : P ⟶ Q) :
    proj P b ≫ φ.iso.hom =
      ((((pullbackPseudofunctor G U).map b.op.toLoc).toFunctor.map φ).iso.hom) ≫ proj Q b :=
  (FppfTorsor.pullbackMap_fst b φ.iso.hom φ.over).symm

/-- The comparison isomorphism of a composite base change, read on the outer projection. -/
theorem mapComp'_hom_app_projOuter (M : ActionTorsor G U S) {X Y : Scheme.{u}} (b : X ⟶ S)
    (a : Y ⟶ X) (q : Y ⟶ S) (hq : a ≫ b = q)
    (hq' : b.op.toLoc ≫ a.op.toLoc = q.op.toLoc) :
    (((pullbackPseudofunctor G U).mapComp' b.op.toLoc a.op.toLoc q.op.toLoc
        hq').hom.toNatTrans.app M).iso.hom ≫ proj (pullbackObj b M) a =
      relBaseChange M.projection b a q hq := by
  subst hq
  exact pullback.lift_fst _ _ _

/-- Base change along an identity: the inverse comparison is the outer projection. -/
theorem mapComp'_inv_app_projOuter_id (M : ActionTorsor G U S) {Y : Scheme.{u}} (b : Y ⟶ S)
    (hq' : b.op.toLoc ≫ (𝟙 Y).op.toLoc = b.op.toLoc) :
    (((pullbackPseudofunctor G U).mapComp' b.op.toLoc (𝟙 Y).op.toLoc b.op.toLoc
        hq').inv.toNatTrans.app M).iso.hom = proj (pullbackObj b M) (𝟙 Y) := by
  have h1 := mapComp'_hom_app_projOuter M b (𝟙 Y) b (Category.id_comp b) hq'
  have h2 : relBaseChange M.projection b (𝟙 Y) b (Category.id_comp b) = 𝟙 _ := by
    apply pullback.hom_ext <;> simp
  rw [h2] at h1
  have h3 := Cat.Hom.inv_hom_id_toNatTrans_app
    ((pullbackPseudofunctor G U).mapComp' b.op.toLoc (𝟙 Y).op.toLoc b.op.toLoc hq') M
  have h4 : ((((pullbackPseudofunctor G U).mapComp' b.op.toLoc (𝟙 Y).op.toLoc b.op.toLoc
        hq').inv.toNatTrans.app M).iso.hom) ≫
      ((((pullbackPseudofunctor G U).mapComp' b.op.toLoc (𝟙 Y).op.toLoc b.op.toLoc
        hq').hom.toNatTrans.app M).iso.hom) = 𝟙 _ :=
    congrArg (fun z ↦ Hom.iso z |>.hom) h3
  exact eq_of_comp_eq_id h1 h4

/-- The outer projection of a base change along an identity is an isomorphism. -/
instance isIso_projOuter_id (M : ActionTorsor G U S) {Y : Scheme.{u}} (b : Y ⟶ S) :
    IsIso (proj (pullbackObj b M) (𝟙 Y)) :=
  (FppfTorsor.pullbackIdIso (M.toFppfTorsor.pullbackTorsor b)).isIso_hom

/-- Composition in a fibre of the base-change pseudofunctor, read on the underlying sheaf
isomorphisms. -/
theorem fibre_comp_iso_hom {T : Scheme.{u}}
    {P Q W : ((pullbackPseudofunctor G U).obj ⟨Opposite.op T⟩ : Cat.{u + 1, u + 1})}
    (a : P ⟶ Q) (b : Q ⟶ W) :
    (Hom.iso (a ≫ b)).hom = (Hom.iso a).hom ≫ (Hom.iso b).hom :=
  rfl

/-- The composite of the two pseudofunctorial comparison cells occurring in the descent datum
`DescentData.ofObj M`, read on the projections to `M.P`.  This is the shape of the transition
morphism of `DescentData.ofObj M` for the pair of indices `(h, f)` and the factorisation
`g ≫ f = h`; compare `Pseudofunctor.DescentData.ofObj_hom`. -/
theorem mapComp'_pair_proj (M : ActionTorsor G U S) {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X)
    (h : Y ⟶ S) (hh : g ≫ f = h)
    (e1 : h.op.toLoc ≫ (𝟙 Y).op.toLoc = h.op.toLoc)
    (e2 : f.op.toLoc ≫ g.op.toLoc = h.op.toLoc) :
    (Hom.iso (((pullbackPseudofunctor G U).mapComp' h.op.toLoc (𝟙 Y).op.toLoc h.op.toLoc
          e1).inv.toNatTrans.app M ≫
        ((pullbackPseudofunctor G U).mapComp' f.op.toLoc g.op.toLoc h.op.toLoc
          e2).hom.toNatTrans.app M)).hom ≫ proj (pullbackObj f M) g =
      proj (pullbackObj h M) (𝟙 Y) ≫ relBaseChange M.projection f g h hh := by
  rw [fibre_comp_iso_hom]
  exact Eq.trans (Category.assoc _ _ _)
    (Eq.trans (congrArg (fun z ↦ _ ≫ z) (mapComp'_hom_app_projOuter M f g h hh e2))
      (congrArg (fun z ↦ z ≫ relBaseChange M.projection f g h hh)
        (mapComp'_inv_app_projOuter_id M h e1)))

end ActionTorsor

/-- A descent datum for fppf sheaves over a base `S` relative to a sieve `R` on `S`: a sheaf
over every member of the sieve, together with transition isomorphisms identifying the sheaf
attached to a refinement with the corresponding base change, subject to the cocycle
condition. -/
structure SheafDescentDatum (S : Scheme.{u}) (R : Sieve S) where
  /-- The sheaf attached to a member `f : X ⟶ S` of the sieve. -/
  sheaf {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) : FppfSheaf.{u}
  /-- Its structure morphism to the representable sheaf of that member. -/
  proj {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) : sheaf f hf ⟶ fppfYoneda.obj X
  /-- The transition isomorphism attached to a refinement `g : Y ⟶ X` with `g ≫ f = h`. -/
  trans {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
    (hf : R.arrows f) (hh' : R.arrows h) :
    sheaf h hh' ≅ Limits.pullback (proj f hf) (fppfYoneda.map g)
  /-- The transition isomorphism lies over the refined member. -/
  trans_proj {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
    (hf : R.arrows f) (hh' : R.arrows h) :
    (trans f g h hh hf hh').hom ≫ Limits.pullback.snd (proj f hf) (fppfYoneda.map g) =
      proj h hh'
  /-- The cocycle condition, read on the projections to `sheaf f hf`. -/
  trans_trans {X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (k : Z ⟶ Y) (h : Y ⟶ S)
    (q : Z ⟶ S) (hh : g ≫ f = h) (hq : k ≫ h = q) (hf : R.arrows f) (hh' : R.arrows h)
    (hq' : R.arrows q) :
    (trans h k q hq hh' hq').hom ≫ Limits.pullback.fst (proj h hh') (fppfYoneda.map k) ≫
        (trans f g h hh hf hh').hom ≫
          Limits.pullback.fst (proj f hf) (fppfYoneda.map g) =
      (trans f (k ≫ g) q (by rw [Category.assoc, hh, hq]) hf hq').hom ≫
        Limits.pullback.fst (proj f hf) (fppfYoneda.map (k ≫ g))

/-- Effective descent for fppf sheaves over a base: every descent datum along a covering sieve
of `S` is the base change of a single fppf sheaf over `S`.

This is the *only* remaining input for the effectiveness of descent of equivariant torsors: it
is a statement about fppf sheaves of sets, with no reference to group actions or torsors.  It
is deliberately kept as an explicit hypothesis; nothing in this file assumes it. -/
structure SheafDescentInput : Prop where
  /-- Every descent datum for fppf sheaves along a covering sieve is effective. -/
  effective : ∀ (S : Scheme.{u}) (R : Sieve S), R ∈ fppfJ.{u} S →
    ∀ D : SheafDescentDatum S R, ∃ (A : FppfSheaf.{u}) (π : A ⟶ fppfYoneda.obj S)
      (e : ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f),
        D.sheaf f hf ≅ Limits.pullback π (fppfYoneda.map f)),
      (∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f),
        (e f hf).hom ≫ Limits.pullback.snd π (fppfYoneda.map f) = D.proj f hf) ∧
      ∀ {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
        (hf : R.arrows f) (hh' : R.arrows h),
        (e h hh').hom ≫ Limits.pullback.fst π (fppfYoneda.map h) =
          (D.trans f g h hh hf hh').hom ≫
            Limits.pullback.fst (D.proj f hf) (fppfYoneda.map g) ≫
              (e f hf).hom ≫ Limits.pullback.fst π (fppfYoneda.map f)

end GromovWitten.AlgebraicGeometry
