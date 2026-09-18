/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.SieveCover

/-!
# Effectivity of descent for sieve-indexed data of fppf sheaves

`Stacks/SieveCover.lean` proves effectivity of descent in a *fibrewise* form: a presheaf
`t : T ⟶ yoneda.obj S` satisfying the sheaf condition for the sections whose base lies in a
covering sieve `R` glues to an fppf sheaf over `S`.

This file performs the translation between that form and the usual bundled form of a descent
datum, namely a family of fppf sheaves `sheaf f hf` over `fppfYoneda.obj X` indexed by the
members `f : X ⟶ S` of `R`, with transition isomorphisms
`sheaf h hh' ≅ pullback (prj f hf) (fppfYoneda.map g)` for each factorisation `g ≫ f = h`,
subject to the cocycle condition.  The fields of such a datum (the fields of the structure
`SheafDescentDatum` of `Stacks/TorsorStack.lean`, which is not imported here, being still under
construction) are taken as explicit hypotheses throughout.

## Construction

The total presheaf is
`tot W = Σ (c : {c : W ⟶ S // R c}), {x : sheaf c W // x lies over 𝟙}`;
its restriction maps are built from the transition isomorphisms (`resAux`), functoriality is the
cocycle condition (`resAux_comp`) together with the fact that the transition isomorphism along an
identity is the canonical one (`tr_id`, itself a consequence of the cocycle condition since an
idempotent isomorphism is the identity).  The sheaf condition over `R` (`isSheafOver_tot`) is
the sheaf condition of the individual sheaves `sheaf c`, transported through the transition
isomorphisms by `ev`.  Feeding this into `SieveCover.exists_glue_of_sieve` yields the glued fppf
sheaf and the fibrewise comparison, `exists_glue_fibrewise`.

## Main declarations

All declarations live in `GromovWitten.AlgebraicGeometry.SieveDescent`.

* `Fib`, `fibHom`, `fibOfHom`: the fibre of the datum at a member of the sieve, and its
  description by splittings of the projection.
* `tr_id`: the transition isomorphism along an identity is the canonical one.
* `resAux`, `resAux_id`, `resAux_comp`: the restriction maps of the total presheaf and their
  functoriality, i.e. the cocycle condition.
* `tot`, `totBase`: the total presheaf over `S` and its structure map.
* `ev`, `tot_ext`, `ev_resAux`: transporting sections of the total presheaf to a fixed member of
  the sieve, and the resulting extensionality.
* `isSheafOver_tot`: the total presheaf is a sheaf over the sieve `R`.
* `exists_glue_fibrewise`: effectivity of descent in fibrewise form -- the datum glues to an fppf
  sheaf `A` over `S` with a morphism from the total presheaf which is bijective on the sections
  lying over any member of the sieve.
* `toTotHom`, `fromTotHom` and their round trips: the identification of the sections of
  `sheaf f hf` lying over `b : W ⟶ X` with the fibre of the datum at `b ≫ f`.
* `exists_glue_of_descentDatum`: effectivity of descent in sections form -- for every member
  `f : X ⟶ S` of the sieve and every `b : W ⟶ X`, the sections of `sheaf f hf` over `W` lying
  over `b` are in bijection with the sections of the glued sheaf `A` over `W` lying over
  `b ≫ f`.  This is the elementwise content of an isomorphism
  `sheaf f hf ≅ pullback π (fppfYoneda.map f)` over `fppfYoneda.obj X`.

What is *not* done here is the assembly of these pointwise bijections into a natural
isomorphism `sheaf f hf ≅ pullback π (fppfYoneda.map f)` together with its two compatibility
statements (lying over `fppfYoneda.obj X`, and commuting with the transition isomorphisms), i.e.
the exact shape of the `SheafDescentInput.effective` field of `Stacks/TorsorStack.lean`.  All
the ingredients are here: naturality of `sectionTot` in `W` (which is the same computation as
`ev_resAux`), and the description of the sections of `pullback π (fppfYoneda.map f)` through
`SheafGluing.tautLift` and the universal property.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace GromovWitten.AlgebraicGeometry.SieveDescent

open GromovWitten.SheafGluing GromovWitten.SieveGluing _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {R : Sieve S}
  (sheaf : ∀ {X : Scheme.{u}} (f : X ⟶ S), R.arrows f → FppfSheaf.{u})
  (prj : ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f), sheaf f hf ⟶ fppfYoneda.obj X)

/-- The fibre of the descent datum at a member `c` of the sieve: the sections of `sheaf c` over
the source of `c` which lie over the identity. -/
def Fib (W : Scheme.{u}) (c : {c : W ⟶ S // R.arrows c}) : Type u :=
  {x : (sheaf c.1 c.2).obj.obj (op W) // base (prj c.1 c.2) x = 𝟙 W}

variable {sheaf prj}

/-- The morphism of fppf sheaves attached to an element of a fibre. -/
def fibHom {W : Scheme.{u}} {c : {c : W ⟶ S // R.arrows c}} (x : Fib sheaf prj W c) :
    fppfYoneda.obj W ⟶ sheaf c.1 c.2 :=
  Scheme.fppfTopology.yonedaEquiv.symm x.1

lemma fibHom_comp {W : Scheme.{u}} {c : {c : W ⟶ S // R.arrows c}} (x : Fib sheaf prj W c) :
    fibHom x ≫ prj c.1 c.2 = 𝟙 _ := by
  rw [fibHom, GrothendieckTopology.yonedaEquiv_symm_naturality_right]
  rw [show (prj c.1 c.2).hom.app (op W) x.1 = 𝟙 W from x.2]
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  rfl

lemma fib_ext {W : Scheme.{u}} {c : {c : W ⟶ S // R.arrows c}} {x y : Fib sheaf prj W c}
    (h : fibHom x = fibHom y) : x = y :=
  Subtype.ext (Scheme.fppfTopology.yonedaEquiv.symm.injective h)

variable (sheaf prj) in
/-- The element of a fibre attached to a splitting of the projection. -/
def fibOfHom {W : Scheme.{u}} (c : {c : W ⟶ S // R.arrows c})
    (a : fppfYoneda.obj W ⟶ sheaf c.1 c.2) (ha : a ≫ prj c.1 c.2 = 𝟙 _) :
    Fib sheaf prj W c :=
  ⟨Scheme.fppfTopology.yonedaEquiv a, by
    rw [base, ← GrothendieckTopology.yonedaEquiv_comp, ha]
    rfl⟩

@[simp]
lemma fibHom_fibOfHom {W : Scheme.{u}} (c : {c : W ⟶ S // R.arrows c})
    (a : fppfYoneda.obj W ⟶ sheaf c.1 c.2) (ha : a ≫ prj c.1 c.2 = 𝟙 _) :
    fibHom (fibOfHom sheaf prj c a ha) = a :=
  Equiv.symm_apply_apply _ _

variable (tr : ∀ {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (_hh : g ≫ f = h)
    (hf : R.arrows f) (hh' : R.arrows h),
    sheaf h hh' ≅ pullback (prj f hf) (fppfYoneda.map g))

/-- Congruence for the transition isomorphism in the refining morphism. -/
lemma tr_fst_congr {X Y : Scheme.{u}} (f : X ⟶ S) {g g' : Y ⟶ X} (hgg : g = g')
    (h : Y ⟶ S) (hh : g ≫ f = h) (hh2 : g' ≫ f = h) (hf : R.arrows f) (hh' : R.arrows h) :
    (tr f g h hh hf hh').hom ≫ pullback.fst (prj f hf) (fppfYoneda.map g) =
      (tr f g' h hh2 hf hh').hom ≫ pullback.fst (prj f hf) (fppfYoneda.map g') := by
  subst hgg; rfl

variable (trp : ∀ {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
    (hf : R.arrows f) (hh' : R.arrows h),
    (tr f g h hh hf hh').hom ≫ pullback.snd (prj f hf) (fppfYoneda.map g) = prj h hh')
  (trt : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (k : Z ⟶ Y) (h : Y ⟶ S)
    (q : Z ⟶ S) (hh : g ≫ f = h) (hq : k ≫ h = q) (hf : R.arrows f) (hh' : R.arrows h)
    (hq' : R.arrows q),
    (tr h k q hq hh' hq').hom ≫ pullback.fst (prj h hh') (fppfYoneda.map k) ≫
        (tr f g h hh hf hh').hom ≫ pullback.fst (prj f hf) (fppfYoneda.map g) =
      (tr f (k ≫ g) q (by rw [Category.assoc, hh, hq]) hf hq').hom ≫
        pullback.fst (prj f hf) (fppfYoneda.map (k ≫ g)))

include trt in
/-- The transition isomorphism along an identity is the canonical isomorphism.  This is forced
by the cocycle condition: the composite below is an idempotent isomorphism. -/
lemma tr_id {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (e : 𝟙 X ≫ f = f) :
    (tr f (𝟙 X) f e hf hf).hom ≫ pullback.fst (prj f hf) (fppfYoneda.map (𝟙 X)) = 𝟙 _ := by
  have key := trt f (𝟙 X) (𝟙 X) f f e e hf hf hf
  have hcongr : (tr f (𝟙 X ≫ 𝟙 X) f (by simp) hf hf).hom ≫
      pullback.fst (prj f hf) (fppfYoneda.map (𝟙 X ≫ 𝟙 X)) =
        (tr f (𝟙 X) f e hf hf).hom ≫ pullback.fst (prj f hf) (fppfYoneda.map (𝟙 X)) :=
    tr_fst_congr tr f (Category.id_comp (𝟙 X)) f (by simp) e hf hf
  rw [hcongr] at key
  have hidem : ((tr f (𝟙 X) f e hf hf).hom ≫
        pullback.fst (prj f hf) (fppfYoneda.map (𝟙 X))) ≫
      ((tr f (𝟙 X) f e hf hf).hom ≫ pullback.fst (prj f hf) (fppfYoneda.map (𝟙 X))) =
      (tr f (𝟙 X) f e hf hf).hom ≫ pullback.fst (prj f hf) (fppfYoneda.map (𝟙 X)) := by
    simpa only [Category.assoc] using key
  have hiso : IsIso ((tr f (𝟙 X) f e hf hf).hom ≫
      pullback.fst (prj f hf) (fppfYoneda.map (𝟙 X))) := inferInstance
  exact (cancel_epi _).mp (hidem.trans (Category.comp_id _).symm)

/-- The morphism attached to a section of `sheaf f hf` over `W` lying over `b : W ⟶ X`,
transported to the member `c = b ≫ f` of the sieve. -/
noncomputable def toTotHom {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    (α : fppfYoneda.obj W ⟶ sheaf f hf) (hα : α ≫ prj f hf = fppfYoneda.map b)
    {c : W ⟶ S} (hc : R.arrows c) (e : b ≫ f = c) : fppfYoneda.obj W ⟶ sheaf c hc :=
  pullback.lift α (𝟙 _) (by rw [hα, Category.id_comp]) ≫ (tr f b c e hf hc).inv

include trp in
lemma toTotHom_proj {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    (α : fppfYoneda.obj W ⟶ sheaf f hf) (hα : α ≫ prj f hf = fppfYoneda.map b)
    {c : W ⟶ S} (hc : R.arrows c) (e : b ≫ f = c) :
    toTotHom tr f hf b α hα hc e ≫ prj c hc = 𝟙 _ := by
  rw [toTotHom, Category.assoc, ← trp f b c e hf hc, Iso.inv_hom_id_assoc]
  exact pullback.lift_snd _ _ _

lemma toTotHom_fst {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    (α : fppfYoneda.obj W ⟶ sheaf f hf) (hα : α ≫ prj f hf = fppfYoneda.map b)
    {c : W ⟶ S} (hc : R.arrows c) (e : b ≫ f = c) :
    toTotHom tr f hf b α hα hc e ≫ (tr f b c e hf hc).hom ≫
        pullback.fst (prj f hf) (fppfYoneda.map b) = α := by
  rw [toTotHom, Category.assoc, Iso.inv_hom_id_assoc]
  exact pullback.lift_fst _ _ _

lemma toTotHom_snd {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    (α : fppfYoneda.obj W ⟶ sheaf f hf) (hα : α ≫ prj f hf = fppfYoneda.map b)
    {c : W ⟶ S} (hc : R.arrows c) (e : b ≫ f = c) :
    toTotHom tr f hf b α hα hc e ≫ (tr f b c e hf hc).hom ≫
        pullback.snd (prj f hf) (fppfYoneda.map b) = 𝟙 _ := by
  rw [toTotHom, Category.assoc, Iso.inv_hom_id_assoc]
  exact pullback.lift_snd _ _ _

/-- The restriction map of the total presheaf, at the level of morphisms. -/
noncomputable def resAuxHom {V W : Scheme.{u}} (u : V ⟶ W) (c : {c : W ⟶ S // R.arrows c})
    {c' : V ⟶ S} (hc' : R.arrows c') (e : u ≫ c.1 = c') (x : Fib sheaf prj W c) :
    fppfYoneda.obj V ⟶ sheaf c' hc' :=
  toTotHom tr c.1 c.2 u (fppfYoneda.map u ≫ fibHom x)
    (by rw [Category.assoc, fibHom_comp, Category.comp_id]) hc' e

include trp in
/-- The restriction map of the total presheaf. -/
noncomputable def resAux {V W : Scheme.{u}} (u : V ⟶ W) (c : {c : W ⟶ S // R.arrows c})
    {c' : V ⟶ S} (hc' : R.arrows c') (e : u ≫ c.1 = c') (x : Fib sheaf prj W c) :
    Fib sheaf prj V ⟨c', hc'⟩ :=
  fibOfHom sheaf prj ⟨c', hc'⟩ (resAuxHom tr u c hc' e x) (toTotHom_proj tr trp _ _ _ _ _ _ _)

include trp in
@[simp]
lemma fibHom_resAux {V W : Scheme.{u}} (u : V ⟶ W) (c : {c : W ⟶ S // R.arrows c})
    {c' : V ⟶ S} (hc' : R.arrows c') (e : u ≫ c.1 = c') (x : Fib sheaf prj W c) :
    fibHom (resAux tr trp u c hc' e x) = resAuxHom tr u c hc' e x :=
  fibHom_fibOfHom _ _ _

include trt in
lemma tr_inv_id {W : Scheme.{u}} (c : W ⟶ S) (hc : R.arrows c) (e : 𝟙 W ≫ c = c) :
    (tr c (𝟙 W) c e hc hc).inv = pullback.fst (prj c hc) (fppfYoneda.map (𝟙 W)) := by
  have h := tr_id tr trt c hc e
  calc (tr c (𝟙 W) c e hc hc).inv
      = (tr c (𝟙 W) c e hc hc).inv ≫ ((tr c (𝟙 W) c e hc hc).hom ≫
          pullback.fst (prj c hc) (fppfYoneda.map (𝟙 W))) := by rw [h, Category.comp_id]
    _ = pullback.fst (prj c hc) (fppfYoneda.map (𝟙 W)) := by rw [Iso.inv_hom_id_assoc]

include trt in
lemma resAux_id {W : Scheme.{u}} (c : {c : W ⟶ S // R.arrows c}) (e : 𝟙 W ≫ c.1 = c.1)
    (x : Fib sheaf prj W c) : resAux tr trp (𝟙 W) c c.2 e x = x := by
  refine fib_ext ?_
  rw [fibHom_resAux, resAuxHom, toTotHom, tr_inv_id tr trt c.1 c.2 e, pullback.lift_fst,
    CategoryTheory.Functor.map_id, Category.id_comp]

include trt in
lemma resAux_comp {V' V W : Scheme.{u}} (w : V' ⟶ V) (u : V ⟶ W)
    (c : {c : W ⟶ S // R.arrows c}) {c' : V ⟶ S} (hc' : R.arrows c') (e : u ≫ c.1 = c')
    {c'' : V' ⟶ S} (hc'' : R.arrows c'') (e' : w ≫ c' = c'') (e'' : (w ≫ u) ≫ c.1 = c'')
    (x : Fib sheaf prj W c) :
    resAux tr trp w ⟨c', hc'⟩ hc'' e' (resAux tr trp u c hc' e x)
      = resAux tr trp (w ≫ u) c hc'' e'' x := by
  refine fib_ext ((cancel_mono (tr c.1 (w ≫ u) c'' e'' c.2 hc'').hom).mp ?_)
  simp only [fibHom_resAux, resAuxHom, toTotHom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst]
    rw [← trt c.1 u w c' c'' e e' c.2 hc' hc'']
    simp only [pullback.lift_fst_assoc, Category.assoc, Iso.inv_hom_id_assoc,
      pullback.lift_fst, ← CategoryTheory.Functor.map_comp_assoc]
  · simp only [Category.assoc, pullback.lift_snd]
    rw [trp c.1 (w ≫ u) c'' e'' c.2 hc'', ← trp c' w c'' e' hc' hc'']
    simp only [Iso.inv_hom_id_assoc, pullback.lift_snd]

lemma totMk_eq {W : Scheme.{u}} {c c' : {c : W ⟶ S // R.arrows c}} (hcc : c = c')
    {x : Fib sheaf prj W c} {x' : Fib sheaf prj W c'} (h : HEq x x') :
    (⟨c, x⟩ : Σ c : {c : W ⟶ S // R.arrows c}, Fib sheaf prj W c) = ⟨c', x'⟩ := by
  subst hcc
  exact congrArg (Sigma.mk c) (eq_of_heq h)

include trp in
lemma resAux_congr {V W : Scheme.{u}} (u : V ⟶ W) (c : {c : W ⟶ S // R.arrows c})
    {c₁ c₂ : V ⟶ S} (hc : c₁ = c₂) (h₁ : R.arrows c₁) (h₂ : R.arrows c₂)
    (e₁ : u ≫ c.1 = c₁) (e₂ : u ≫ c.1 = c₂) (x : Fib sheaf prj W c) :
    HEq (resAux tr trp u c h₁ e₁ x) (resAux tr trp u c h₂ e₂ x) := by
  subst hc; rfl

include trt in
/-- The total presheaf attached to a sieve-indexed descent datum. -/
noncomputable def tot : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj W := Σ c : {c : W.unop ⟶ S // R.arrows c}, Fib sheaf prj W.unop c
  map u := TypeCat.ofHom fun z =>
    ⟨⟨u.unop ≫ z.1.1, R.downward_closed z.1.2 u.unop⟩, resAux tr trp u.unop z.1 _ rfl z.2⟩
  map_id W := by
    apply TypeCat.homEquiv.injective
    funext z
    refine totMk_eq (Subtype.ext (Category.id_comp z.1.1)) ?_
    exact HEq.trans (resAux_congr tr trp (𝟙 W.unop) z.1 (Category.id_comp z.1.1) _ z.1.2 rfl
      (Category.id_comp z.1.1) z.2) (heq_of_eq (resAux_id tr trp trt z.1 _ z.2))
  map_comp p q := by
    apply TypeCat.homEquiv.injective
    funext z
    refine totMk_eq (Subtype.ext (Category.assoc q.unop p.unop z.1.1)) ?_
    refine HEq.trans (resAux_congr tr trp (q.unop ≫ p.unop) z.1
      (Category.assoc q.unop p.unop z.1.1) (R.downward_closed z.1.2 (q.unop ≫ p.unop))
      (R.downward_closed (R.downward_closed z.1.2 p.unop) q.unop) rfl
      (Category.assoc q.unop p.unop z.1.1) z.2) ?_
    exact heq_of_eq (resAux_comp tr trp trt q.unop p.unop z.1
      (R.downward_closed z.1.2 p.unop) rfl
      (R.downward_closed (R.downward_closed z.1.2 p.unop) q.unop) rfl
      (Category.assoc q.unop p.unop z.1.1) z.2).symm

include trt in
@[simp]
lemma tot_map {V W : Scheme.{u}} (u : V ⟶ W)
    (z : Σ c : {c : W ⟶ S // R.arrows c}, Fib sheaf prj W c) :
    (tot tr trp trt).map u.op z =
      ⟨⟨u ≫ z.1.1, R.downward_closed z.1.2 u⟩,
        resAux tr trp u z.1 (R.downward_closed z.1.2 u) rfl z.2⟩ :=
  rfl

include trt in
/-- The structure morphism of the total presheaf. -/
def totBase : tot tr trp trt ⟶ yoneda.obj S where
  app _ := TypeCat.ofHom fun z => z.1.1
  naturality _ _ _ := by ext z; rfl

/-- Evaluation of a section of the total presheaf, transported to a fixed member `c` of the
sieve through the transition isomorphisms. -/
noncomputable def ev {V W : Scheme.{u}} (c : W ⟶ S) (hc : R.arrows c)
    (z : Σ c : {c : V ⟶ S // R.arrows c}, Fib sheaf prj V c) (u : V ⟶ W)
    (h : z.1.1 = u ≫ c) : fppfYoneda.obj V ⟶ sheaf c hc :=
  fibHom z.2 ≫ (tr c u z.1.1 h.symm hc z.1.2).hom ≫
    pullback.fst (prj c hc) (fppfYoneda.map u)

lemma ev_congr {V W : Scheme.{u}} (c : W ⟶ S) (hc : R.arrows c)
    {z z' : Σ c : {c : V ⟶ S // R.arrows c}, Fib sheaf prj V c} (hz : z = z') (u : V ⟶ W)
    (h : z.1.1 = u ≫ c) (h' : z'.1.1 = u ≫ c) : ev tr c hc z u h = ev tr c hc z' u h' := by
  subst hz; rfl

include trp in
lemma ev_comp_prj {V W : Scheme.{u}} (c : W ⟶ S) (hc : R.arrows c)
    (z : Σ c : {c : V ⟶ S // R.arrows c}, Fib sheaf prj V c) (u : V ⟶ W)
    (h : z.1.1 = u ≫ c) : ev tr c hc z u h ≫ prj c hc = fppfYoneda.map u := by
  rw [ev]
  simp only [Category.assoc]
  rw [pullback.condition, ← Category.assoc ((tr c u z.1.1 h.symm hc z.1.2).hom) _ _,
    trp c u z.1.1 h.symm hc z.1.2, ← Category.assoc, fibHom_comp, Category.id_comp]

include trp in
lemma fibHom_eq_lift {V W : Scheme.{u}} (c : W ⟶ S) (hc : R.arrows c)
    (z : Σ c : {c : V ⟶ S // R.arrows c}, Fib sheaf prj V c) (u : V ⟶ W)
    (h : z.1.1 = u ≫ c) :
    fibHom z.2 = pullback.lift (ev tr c hc z u h) (𝟙 _)
        (by rw [ev_comp_prj tr trp c hc z u h, Category.id_comp]) ≫
      (tr c u z.1.1 h.symm hc z.1.2).inv := by
  refine (Iso.eq_comp_inv _).mpr (pullback.hom_ext ?_ ?_)
  · rw [pullback.lift_fst, ev, Category.assoc]
  · rw [pullback.lift_snd, Category.assoc, trp c u z.1.1 h.symm hc z.1.2, fibHom_comp]

include trp in
lemma tot_ext {V W : Scheme.{u}} (c : W ⟶ S) (hc : R.arrows c) (u : V ⟶ W)
    {z z' : Σ c : {c : V ⟶ S // R.arrows c}, Fib sheaf prj V c}
    (h : z.1.1 = u ≫ c) (h' : z'.1.1 = u ≫ c)
    (hev : ev tr c hc z u h = ev tr c hc z' u h') : z = z' := by
  obtain ⟨c₁, ξ₁⟩ := z
  obtain ⟨c₂, ξ₂⟩ := z'
  have hc12 : c₁ = c₂ := Subtype.ext (h.trans h'.symm)
  subst hc12
  refine congrArg (Sigma.mk c₁) (fib_ext ?_)
  rw [fibHom_eq_lift tr trp c hc ⟨c₁, ξ₁⟩ u h, fibHom_eq_lift tr trp c hc ⟨c₁, ξ₂⟩ u h']
  refine congrArg (fun L => L ≫ (tr c u c₁.1 h.symm hc c₁.2).inv) (pullback.hom_ext ?_ ?_)
  · rw [pullback.lift_fst, pullback.lift_fst, hev]
  · rw [pullback.lift_snd, pullback.lift_snd]

include trt in
lemma ev_resAux {V' V W : Scheme.{u}} (c : W ⟶ S) (hc : R.arrows c)
    (z : Σ c : {c : V ⟶ S // R.arrows c}, Fib sheaf prj V c) (u : V ⟶ W)
    (h : z.1.1 = u ≫ c) (w : V' ⟶ V) (h' : w ≫ z.1.1 = (w ≫ u) ≫ c) :
    fppfYoneda.map w ≫ ev tr c hc z u h
      = ev tr c hc ⟨⟨w ≫ z.1.1, R.downward_closed z.1.2 w⟩,
          resAux tr trp w z.1 (R.downward_closed z.1.2 w) rfl z.2⟩ (w ≫ u) h' := by
  rw [ev, ev, fibHom_resAux, resAuxHom, toTotHom,
    ← trt c u w z.1.1 (w ≫ z.1.1) h.symm rfl hc z.1.2 (R.downward_closed z.1.2 w)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_fst_assoc]

lemma ev_congr_u {V W : Scheme.{u}} (c : W ⟶ S) (hc : R.arrows c)
    (z : Σ c : {c : V ⟶ S // R.arrows c}, Fib sheaf prj V c) {u u' : V ⟶ W} (huu : u = u')
    (h : z.1.1 = u ≫ c) (h' : z.1.1 = u' ≫ c) : ev tr c hc z u h = ev tr c hc z u' h' := by
  subst huu; rfl

include trt in
/-- **The total presheaf is a sheaf over the sieve `R`.**  The base component of a compatible
family is forced, and the remaining data is a compatible family of sections of the single sheaf
`sheaf c hc`, transported through the transition isomorphisms. -/
theorem isSheafOver_tot : IsSheafOver Scheme.fppfTopology (totBase tr trp trt) R := by
  intro W c hc K hK x hb hcomp
  have hb' : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ W) (hu : K.arrows u), (x u hu).1.1 = u ≫ c :=
    fun _ u hu => hb u hu
  have hA : ∀ ⦃V : Scheme.{u}⦄ (u₁ u₂ : V ⟶ W) (_ : u₁ = u₂) (h₁ : K.arrows u₁)
      (h₂ : K.arrows u₂),
      ev tr c hc (x u₁ h₁) u₁ (hb' u₁ h₁) = ev tr c hc (x u₂ h₂) u₂ (hb' u₂ h₂) := by
    intro V u₁ u₂ huu h₁ h₂
    subst huu
    rfl
  have hres : ∀ ⦃V' V : Scheme.{u}⦄ (u : V ⟶ W) (hu : K.arrows u) (w : V' ⟶ V),
      fppfYoneda.map w ≫ ev tr c hc (x u hu) u (hb' u hu)
        = ev tr c hc (x (w ≫ u) (K.downward_closed hu w)) (w ≫ u) (hb' _ _) := by
    intro V' V u hu w
    have h' : w ≫ (x u hu).1.1 = (w ≫ u) ≫ c := by rw [hb' u hu, Category.assoc]
    rw [ev_resAux tr trp trt c hc (x u hu) u (hb' u hu) w h']
    exact ev_congr tr c hc (hcomp u hu w) (w ≫ u) h' (hb' _ _)
  obtain ⟨η, hη, huniqη⟩ := isSheafOfType (sheaf c hc) K hK
    (fun _ u hu => Scheme.fppfTopology.yonedaEquiv (ev tr c hc (x u hu) u (hb' u hu)))
    (by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hg
      rw [GrothendieckTopology.yonedaEquiv_naturality,
        GrothendieckTopology.yonedaEquiv_naturality, hres f₁ h₁ g₁, hres f₂ h₂ g₂]
      exact congrArg _ (hA _ _ hg _ _))
  have hηA : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ W) (hu : K.arrows u),
      fppfYoneda.map u ≫ Scheme.fppfTopology.yonedaEquiv.symm η
        = ev tr c hc (x u hu) u (hb' u hu) := by
    intro V u hu
    apply Scheme.fppfTopology.yonedaEquiv.injective
    rw [← GrothendieckTopology.yonedaEquiv_naturality, Equiv.apply_symm_apply]
    exact hη u hu
  have hAprj : Scheme.fppfTopology.yonedaEquiv.symm η ≫ prj c hc = 𝟙 _ := by
    apply Scheme.fppfTopology.yonedaEquiv.injective
    refine (isSheafOfType (fppfYoneda.obj W) K hK).isSeparatedFor.ext ?_
    intro V u hu
    rw [GrothendieckTopology.yonedaEquiv_naturality,
      GrothendieckTopology.yonedaEquiv_naturality, ← Category.assoc, hηA u hu,
      ev_comp_prj tr trp c hc (x u hu) u (hb' u hu), Category.comp_id]
  refine ⟨⟨⟨c, hc⟩, fibOfHom sheaf prj ⟨c, hc⟩ _ hAprj⟩, ⟨rfl, fun V u hu => ?_⟩, ?_⟩
  · refine tot_ext tr trp c hc u rfl (hb' u hu) ?_
    simp only [tot_map, ev, fibHom_resAux, resAuxHom, toTotHom, fibHom_fibOfHom,
      Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_fst]
    exact hηA u hu
  · rintro e' ⟨hbe', hme'⟩
    have hbe'' : e'.1.1 = c := hbe'
    have h0 : e'.1.1 = 𝟙 W ≫ c := by rw [hbe'', Category.id_comp]
    have h0e : ((⟨⟨c, hc⟩, fibOfHom sheaf prj ⟨c, hc⟩ _ hAprj⟩ :
        Σ c : {c : W ⟶ S // R.arrows c}, Fib sheaf prj W c)).1.1 = 𝟙 W ≫ c := by
      rw [Category.id_comp]
    refine tot_ext tr trp c hc (𝟙 W) h0 h0e ?_
    have hamalg : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ W) (hu : K.arrows u),
        (sheaf c hc).obj.map u.op
            (Scheme.fppfTopology.yonedaEquiv (ev tr c hc e' (𝟙 W) h0))
          = Scheme.fppfTopology.yonedaEquiv (ev tr c hc (x u hu) u (hb' u hu)) := by
      intro V u hu
      rw [GrothendieckTopology.yonedaEquiv_naturality]
      refine congrArg _ ?_
      have h'' : u ≫ e'.1.1 = (u ≫ 𝟙 W) ≫ c := by rw [h0]; simp
      have h''' : (x u hu).1.1 = (u ≫ 𝟙 W) ≫ c := by rw [hb' u hu]; simp
      rw [ev_resAux tr trp trt c hc e' (𝟙 W) h0 u h'']
      refine Eq.trans (ev_congr tr c hc (hme' u hu) (u ≫ 𝟙 W) h'' h''') ?_
      exact ev_congr_u tr c hc (x u hu) (Category.comp_id u) h''' (hb' u hu)
    have h2 : ev tr c hc e' (𝟙 W) h0 = Scheme.fppfTopology.yonedaEquiv.symm η := by
      rw [← huniqη _ hamalg, Equiv.symm_apply_apply]
    rw [h2, ev, fibHom_fibOfHom, tr_id tr trt c hc h0e.symm, Category.comp_id]

lemma yonedaEquiv_symm_map {V W : Scheme.{u}} (b : V ⟶ W) :
    Scheme.fppfTopology.yonedaEquiv.symm b = fppfYoneda.map b := by
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, GrothendieckTopology.yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_comp_prj {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f)
    (y : (sheaf f hf).obj.obj (op W)) :
    Scheme.fppfTopology.yonedaEquiv.symm y ≫ prj f hf
      = fppfYoneda.map (base (prj f hf) y) := by
  rw [GrothendieckTopology.yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_map]
  rfl

/-- The inverse construction to `toTotHom`: from a splitting of the projection of the fibre at
`c = b ≫ f` back to a section of `sheaf f hf` lying over `b`. -/
noncomputable def fromTotHom {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    {c : W ⟶ S} (hc : R.arrows c) (e : b ≫ f = c) (a : fppfYoneda.obj W ⟶ sheaf c hc) :
    fppfYoneda.obj W ⟶ sheaf f hf :=
  a ≫ (tr f b c e hf hc).hom ≫ pullback.fst (prj f hf) (fppfYoneda.map b)

include trp in
lemma fromTotHom_comp_prj {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    {c : W ⟶ S} (hc : R.arrows c) (e : b ≫ f = c) (a : fppfYoneda.obj W ⟶ sheaf c hc)
    (ha : a ≫ prj c hc = 𝟙 _) :
    fromTotHom tr f hf b hc e a ≫ prj f hf = fppfYoneda.map b := by
  rw [fromTotHom]
  simp only [Category.assoc]
  rw [pullback.condition, ← Category.assoc ((tr f b c e hf hc).hom) _ _, trp f b c e hf hc,
    ← Category.assoc, ha, Category.id_comp]

lemma fromTotHom_toTotHom {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    (α : fppfYoneda.obj W ⟶ sheaf f hf) (hα : α ≫ prj f hf = fppfYoneda.map b)
    {c : W ⟶ S} (hc : R.arrows c) (e : b ≫ f = c) :
    fromTotHom tr f hf b hc e (toTotHom tr f hf b α hα hc e) = α := by
  rw [fromTotHom, toTotHom, Category.assoc, Iso.inv_hom_id_assoc]
  exact pullback.lift_fst _ _ _

include trp in
lemma toTotHom_fromTotHom {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    {c : W ⟶ S} (hc : R.arrows c) (e : b ≫ f = c) (a : fppfYoneda.obj W ⟶ sheaf c hc)
    (ha : a ≫ prj c hc = 𝟙 _) :
    toTotHom tr f hf b (fromTotHom tr f hf b hc e a)
      (fromTotHom_comp_prj tr trp f hf b hc e a ha) hc e = a := by
  rw [toTotHom]
  refine (Iso.comp_inv_eq (tr f b c e hf hc)).mpr (pullback.hom_ext ?_ ?_)
  · rw [pullback.lift_fst, fromTotHom, Category.assoc]
  · rw [pullback.lift_snd, Category.assoc, trp f b c e hf hc, ha]

include trt in
/-- **Effectivity of descent for a sieve-indexed datum, fibrewise form.**  Combining
`isSheafOver_tot` with `exists_glue_of_sieve`: the descent datum glues to an fppf sheaf `A` over
`S`, together with a morphism `Φ` from the total presheaf which is bijective on the sections
whose base is a given member `c` of the sieve. -/
theorem exists_glue_fibrewise (hR : R ∈ Scheme.fppfTopology S) :
    ∃ (A : FppfSheaf.{u}) (π : A ⟶ fppfYoneda.obj S) (Φ : tot tr trp trt ⟶ A.obj),
      (∀ (W : Scheme.{u}) (z : Σ c : {c : W ⟶ S // R.arrows c}, Fib sheaf prj W c),
        base π (Φ.app (op W) z) = z.1.1) ∧
      ∀ (W : Scheme.{u}) (c : W ⟶ S), R.arrows c →
        (∀ z z' : Σ c : {c : W ⟶ S // R.arrows c}, Fib sheaf prj W c,
            z.1.1 = c → z'.1.1 = c → Φ.app (op W) z = Φ.app (op W) z' → z = z') ∧
          ∀ a : A.obj.obj (op W), base π a = c →
            ∃ z : Σ c : {c : W ⟶ S // R.arrows c}, Fib sheaf prj W c,
              z.1.1 = c ∧ Φ.app (op W) z = a :=
  exists_glue_of_sieve (totBase tr trp trt) hR (isSheafOver_tot tr trp trt)

/-- The section of the total presheaf attached to a section of `sheaf f hf` lying over `b`. -/
noncomputable def sectionTot {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    (y : {y : (sheaf f hf).obj.obj (op W) // base (prj f hf) y = b}) :
    Σ c : {c : W ⟶ S // R.arrows c}, Fib sheaf prj W c :=
  ⟨⟨b ≫ f, R.downward_closed hf b⟩,
    fibOfHom sheaf prj _ (toTotHom tr f hf b (Scheme.fppfTopology.yonedaEquiv.symm y.1)
        (by rw [yonedaEquiv_symm_comp_prj, y.2]) (R.downward_closed hf b) rfl)
      (toTotHom_proj tr trp f hf b _ _ (R.downward_closed hf b) rfl)⟩

include trp in
lemma sectionTot_fst {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    (y : {y : (sheaf f hf).obj.obj (op W) // base (prj f hf) y = b}) :
    (sectionTot tr trp f hf b y).1.1 = b ≫ f :=
  rfl

include trt in
lemma ev_sectionTot {X W : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (b : W ⟶ X)
    (y : {y : (sheaf f hf).obj.obj (op W) // base (prj f hf) y = b})
    (h : (sectionTot tr trp f hf b y).1.1 = 𝟙 W ≫ (b ≫ f)) :
    ev tr (b ≫ f) (R.downward_closed hf b) (sectionTot tr trp f hf b y) (𝟙 W) h
      = toTotHom tr f hf b (Scheme.fppfTopology.yonedaEquiv.symm y.1)
        (by rw [yonedaEquiv_symm_comp_prj, y.2]) (R.downward_closed hf b) rfl := by
  simp only [ev, sectionTot, fibHom_fibOfHom]
  rw [tr_id tr trt (b ≫ f) (R.downward_closed hf b) h.symm, Category.comp_id]

include tr trp trt in
/-- **Effectivity of descent for a sieve-indexed datum, sections form.**  The descent datum
glues to an fppf sheaf `A` over `S` such that, for every member `f : X ⟶ S` of the sieve and
every `b : W ⟶ X`, the sections of `sheaf f hf` over `W` lying over `b` are in bijection with
the sections of `A` over `W` lying over `b ≫ f`.  This is the elementwise form of the
isomorphism `sheaf f hf ≅ pullback π (fppfYoneda.map f)` over `fppfYoneda.obj X`. -/
theorem exists_glue_of_descentDatum (hR : R ∈ Scheme.fppfTopology S) :
    ∃ (A : FppfSheaf.{u}) (π : A ⟶ fppfYoneda.obj S),
      ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f) (W : Scheme.{u}) (b : W ⟶ X),
        Nonempty ({y : (sheaf f hf).obj.obj (op W) // base (prj f hf) y = b} ≃
          {a : A.obj.obj (op W) // base π a = b ≫ f}) := by
  obtain ⟨A, π, Φ, hΦbase, hΦbij⟩ := exists_glue_fibrewise tr trp trt hR
  refine ⟨A, π, fun {X} f hf W b => ⟨Equiv.ofBijective
    (fun y => ⟨Φ.app (op W) (sectionTot tr trp f hf b y), hΦbase W _⟩) ⟨?_, ?_⟩⟩⟩
  · intro y₁ y₂ hy
    have h2 : sectionTot tr trp f hf b y₁ = sectionTot tr trp f hf b y₂ :=
      (hΦbij W (b ≫ f) (R.downward_closed hf b)).1 _ _ rfl rfl (congrArg Subtype.val hy)
    have h3 := ev_congr tr (b ≫ f) (R.downward_closed hf b) h2 (𝟙 W)
      (by rw [sectionTot_fst tr trp, Category.id_comp])
      (by rw [sectionTot_fst tr trp, Category.id_comp])
    rw [ev_sectionTot tr trp trt f hf b y₁, ev_sectionTot tr trp trt f hf b y₂] at h3
    refine Subtype.ext (Scheme.fppfTopology.yonedaEquiv.symm.injective ?_)
    have e1 := fromTotHom_toTotHom tr f hf b (Scheme.fppfTopology.yonedaEquiv.symm y₁.1)
      (by rw [yonedaEquiv_symm_comp_prj, y₁.2]) (R.downward_closed hf b)
      (rfl : b ≫ f = b ≫ f)
    have e2 := fromTotHom_toTotHom tr f hf b (Scheme.fppfTopology.yonedaEquiv.symm y₂.1)
      (by rw [yonedaEquiv_symm_comp_prj, y₂.2]) (R.downward_closed hf b)
      (rfl : b ≫ f = b ≫ f)
    exact (e1.symm.trans
      (congrArg (fromTotHom tr f hf b (R.downward_closed hf b) rfl) h3)).trans e2
  · rintro ⟨a, ha⟩
    obtain ⟨⟨⟨c₀, hc₀⟩, ξ₀⟩, hz1, hz2⟩ :=
      (hΦbij W (b ≫ f) (R.downward_closed hf b)).2 a ha
    obtain rfl : c₀ = b ≫ f := hz1
    refine ⟨⟨Scheme.fppfTopology.yonedaEquiv
        (fromTotHom tr f hf b hc₀ rfl (fibHom ξ₀)), ?_⟩, ?_⟩
    · rw [base, ← GrothendieckTopology.yonedaEquiv_comp,
        fromTotHom_comp_prj tr trp f hf b hc₀ rfl _ (fibHom_comp ξ₀),
        GrothendieckTopology.yonedaEquiv_yoneda_map]
    · refine Subtype.ext (Eq.trans ?_ hz2)
      refine congrArg (Φ.app (op W)) (congrArg (Sigma.mk ⟨b ≫ f, hc₀⟩) (fib_ext ?_))
      simp only [fibHom_fibOfHom, Equiv.symm_apply_apply]
      exact toTotHom_fromTotHom tr trp f hf b hc₀ rfl _ (fibHom_comp ξ₀)

end GromovWitten.AlgebraicGeometry.SieveDescent
