/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Spaces.Representable

/-!
# Gluing of sheaves over a base

This file develops the sheaf theory needed to promote the quotient prestacks `[U/G]` to stacks:
morphisms of sheaves *over a fixed base* glue along covering sieves, and a sheaf over a base is
determined, up to a unique isomorphism over the base, by its restrictions to a covering sieve.

Throughout, `(C, J)` is a site with a subcanonical topology and all sheaves take values in
`Type v`, so that `J.yoneda : C ⥤ Sheaf J (Type v)` is available.  A *sheaf over `S`* is an
object `P : Sheaf J (Type v)` together with a structure morphism `p : P ⟶ J.yoneda.obj S`.  For
`W : C` and `x` a section of `P` over `W`, `base p x : W ⟶ S` is the induced map to the base.

The key elementary observation is that the fibre product `P ×_{y S} y T` of the structure
morphism `p` with `y f` for `f : T ⟶ S` has, as its sections over `W`, the pairs `(g, x)` with
`g : W ⟶ T`, `x` a section of `P` over `W` and `base p x = g ≫ f`.  Consequently a compatible
family of morphisms `P ×_{y S} y T ⟶ Q ×_{y S} y T` over `y T`, indexed by the members
`f : T ⟶ S` of a sieve `R`, is the same thing as a map defined on the sections of `P` whose base
lies in `R`; this is packaged as `PartialHom`.  Working with `PartialHom` avoids constructing any
fibre products of sheaves, and in particular avoids sheafification, which is unavailable for
`Sheaf Scheme.fppfTopology (Type u)` for universe reasons.

## Main declarations

* `GromovWitten.SheafGluing.base`: the base point `W ⟶ S` of a section of a sheaf over `S`.
* `GromovWitten.SheafGluing.SectionsOver`: sections of `P` whose base lies in a sieve `R`.
* `GromovWitten.SheafGluing.hom_ext_of_sieve`: a morphism of sheaves out of a sheaf over `S` is
  determined by its restriction to the sections whose base lies in a covering sieve.
* `GromovWitten.SheafGluing.PartialHom`: a morphism defined on the sections whose base lies in a
  sieve, equivalently a compatible family of morphisms after base change along the sieve.
* `GromovWitten.SheafGluing.PartialHom.glue` and
  `GromovWitten.SheafGluing.PartialHom.exists_unique_glue`: descent of arrows, i.e. such a
  partial morphism extends uniquely to a morphism of sheaves; `PartialHom.glue_comp` records
  that the extension lies over `S` when the partial morphism does.
* `GromovWitten.SheafGluing.FibSections`, `GromovWitten.SheafGluing.SieveHomFamily` and
  `SieveHomFamily.exists_unique_glue_hom`: the same statement in the literal fibre-product
  formulation, with the sections of `P ×_{y S} y T` described explicitly.
* `GromovWitten.SheafGluing.PartialIso` and `GromovWitten.SheafGluing.PartialIso.glue`:
  two sheaves over `S` whose restrictions to a covering sieve are compatibly isomorphic are
  isomorphic over `S` (uniqueness of the glued sheaf).
* `GromovWitten.SheafGluing.DescentDatum`, `GromovWitten.SheafGluing.glueSheaf`,
  `GromovWitten.SheafGluing.gluePresheaf_isSheaf` and
  `GromovWitten.SheafGluing.glueSheafFibreEquiv`: **effectivity of descent** along a morphism
  `f : X ⟶ S` in a category with pullbacks.  A descent datum consists of a sheaf `P` over `X`
  together with the fibrewise transition maps over `X ×_S X` and the cocycle condition; the
  glued presheaf sends `W` to the pairs of a morphism `s : W ⟶ S` and a section of `P` over
  `W ×_S X` satisfying the descent condition.  It is proved to be a sheaf and its fibres along
  `f` are identified with those of `P`.
* `GromovWitten.SheafGluing.relMap`, `GromovWitten.SheafGluing.hom_ext_of_cover`,
  `GromovWitten.SheafGluing.isIso_of_cover` and `GromovWitten.SheafGluing.CoverHomFamily`:
  the same results phrased with the actual fibre products `P ×_{y S} y X` in the category of
  sheaves (which requires pullbacks of sheaves, available for `FppfSheaf`).
-/

open CategoryTheory Opposite

namespace GromovWitten.SheafGluing

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A sheaf of types is a sheaf in the sense of presieves. -/
theorem isSheafOfType (F : Sheaf J (Type v)) : Presieve.IsSheaf J F.obj :=
  (isSheaf_iff_isSheaf_of_type J F.obj).1 F.property

/-- Functoriality of a presheaf of types, in elementwise form. -/
lemma map_comp_apply (F : Cᵒᵖ ⥤ Type v) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (x : F.obj X) :
    F.map (f ≫ g) x = F.map g (F.map f x) :=
  congrArg (fun (t : F.obj X ⟶ F.obj Z) => t x) (F.map_comp f g)

/-- Unitality of a presheaf of types, in elementwise form. -/
lemma map_id_apply (F : Cᵒᵖ ⥤ Type v) {X : Cᵒᵖ} (x : F.obj X) : F.map (𝟙 X) x = x :=
  congrArg (fun (t : F.obj X ⟶ F.obj X) => t x) (F.map_id X)

/-- Naturality of a morphism of presheaves of types, in elementwise form. -/
lemma nat_apply {F G : Cᵒᵖ ⥤ Type v} (σ : F ⟶ G) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X) :
    σ.app Y (F.map f x) = G.map f (σ.app X x) :=
  congrArg (fun (t : F.obj X ⟶ G.obj Y) => t x) (σ.naturality f)

variable [J.Subcanonical] {S : C} {P Q : Sheaf J (Type v)}

/-- The base point `W ⟶ S` of a section of a sheaf `P` equipped with a structure morphism
`p : P ⟶ J.yoneda.obj S`. -/
def base (p : P ⟶ J.yoneda.obj S) {W : C} (x : P.obj.obj (op W)) : W ⟶ S :=
  p.hom.app (op W) x

@[simp]
lemma base_map (p : P ⟶ J.yoneda.obj S) {V W : C} (u : V ⟶ W) (x : P.obj.obj (op W)) :
    base p (P.obj.map u.op x) = u ≫ base p x :=
  nat_apply p.hom u.op x

lemma base_comp {G : Sheaf J (Type v)} (φ : P ⟶ G) (q : G ⟶ J.yoneda.obj S) {W : C}
    (x : P.obj.obj (op W)) : base (φ ≫ q) x = base q (φ.hom.app (op W) x) :=
  rfl

/-- The sections of `P` over `W` whose base `W ⟶ S` belongs to the sieve `R`.  These are exactly
the sections of the fibre product of `p` with the sieve `R`. -/
abbrev SectionsOver (p : P ⟶ J.yoneda.obj S) (R : Sieve S) (W : C) : Type v :=
  {x : P.obj.obj (op W) // R (base p x)}

namespace SectionsOver

variable {p : P ⟶ J.yoneda.obj S} {R : Sieve S}

/-- Restriction of a section lying over the sieve `R` along a morphism of `C`. -/
def res {V W : C} (u : V ⟶ W) (x : SectionsOver p R W) : SectionsOver p R V :=
  ⟨P.obj.map u.op x.1, by rw [base_map]; exact R.downward_closed x.2 u⟩

@[simp]
lemma res_val {V W : C} (u : V ⟶ W) (x : SectionsOver p R W) :
    (res u x).1 = P.obj.map u.op x.1 :=
  rfl

lemma res_res {Z V W : C} (u : V ⟶ W) (w : Z ⟶ V) (x : SectionsOver p R W) :
    res w (res u x) = res (w ≫ u) x := by
  apply Subtype.ext
  rw [res_val, res_val, res_val, ← map_comp_apply, ← op_comp]

end SectionsOver

/-- **Separatedness of morphisms over a base.**  Two morphisms out of a sheaf `P` over `S` agree
as soon as they agree on the sections of `P` whose base lies in a covering sieve of `S`. -/
theorem hom_ext_of_sieve (p : P ⟶ J.yoneda.obj S) {R : Sieve S} (hR : R ∈ J S) {φ ψ : P ⟶ Q}
    (h : ∀ (W : C) (x : SectionsOver p R W), φ.hom.app (op W) x.1 = ψ.hom.app (op W) x.1) :
    φ = ψ := by
  apply ObjectProperty.hom_ext
  ext W x
  refine (isSheafOfType Q _
    (J.pullback_stable (base p (W := W.unop) x) hR)).isSeparatedFor.ext ?_
  intro V u hu
  have hu' : R (u ≫ base p (W := W.unop) x) := hu
  refine (nat_apply φ.hom u.op x).symm.trans (Eq.trans ?_ (nat_apply ψ.hom u.op x))
  exact h V ⟨P.obj.map u.op x, by rw [base_map]; exact hu'⟩

/-- A morphism from a sheaf `P` over `S` to a sheaf `G`, defined only on the sections of `P`
whose base lies in the sieve `R`.

Via the description of the sections of the fibre product `P ×_{y S} y T` recalled in the module
docstring, this is the same datum as a family of morphisms
`P ×_{y S} y T ⟶ G ×_{y S} y T` over `y T`, one for each `f : T ⟶ S` in `R`, compatible with
restriction along the morphisms of the sieve. -/
structure PartialHom (p : P ⟶ J.yoneda.obj S) (G : Sheaf J (Type v)) (R : Sieve S) where
  /-- The partially defined map on sections. -/
  app : ∀ {W : C}, SectionsOver p R W → G.obj.obj (op W)
  /-- Compatibility of `app` with the restriction maps of the sheaves. -/
  naturality : ∀ {V W : C} (u : V ⟶ W) (x : SectionsOver p R W),
    G.obj.map u.op (app x) = app (SectionsOver.res u x)

namespace PartialHom

variable {p : P ⟶ J.yoneda.obj S} {R : Sieve S} (Φ : PartialHom p Q R)

/-- The family of sections of `Q` over the pullback of `R` along the base of `x`, attached to an
arbitrary section `x` of `P`. -/
def family {W : C} (x : P.obj.obj (op W)) :
    Presieve.FamilyOfElements Q.obj (R.pullback (base p x)).arrows :=
  fun _ u hu => Φ.app ⟨P.obj.map u.op x, by rw [base_map]; exact hu⟩

lemma family_compatible {W : C} (x : P.obj.obj (op W)) : (Φ.family x).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hc
  have hval : P.obj.map g₁.op (P.obj.map f₁.op x) = P.obj.map g₂.op (P.obj.map f₂.op x) := by
    rw [← map_comp_apply, ← map_comp_apply, ← op_comp, ← op_comp, hc]
  dsimp only [family]
  rw [Φ.naturality, Φ.naturality]
  exact congrArg (Φ.app (W := Z)) (Subtype.ext hval)

/-- The value of the glued morphism on an arbitrary section of `P`. -/
noncomputable def glueApp (hR : R ∈ J S) {W : C} (x : P.obj.obj (op W)) : Q.obj.obj (op W) :=
  (isSheafOfType Q _ (J.pullback_stable (base p x) hR)).amalgamate _ (Φ.family_compatible x)

lemma glueApp_res (hR : R ∈ J S) {V W : C} (x : P.obj.obj (op W)) (u : V ⟶ W)
    (hu : R (u ≫ base p x)) :
    Q.obj.map u.op (Φ.glueApp hR x) = Φ.app ⟨P.obj.map u.op x, by rw [base_map]; exact hu⟩ :=
  (isSheafOfType Q _ (J.pullback_stable (base p x) hR)).valid_glue
    (Φ.family_compatible x) u hu

lemma glueApp_naturality (hR : R ∈ J S) {V W : C} (u : V ⟶ W) (x : P.obj.obj (op W)) :
    Q.obj.map u.op (Φ.glueApp hR x) = Φ.glueApp hR (P.obj.map u.op x) := by
  refine (isSheafOfType Q _
    (J.pullback_stable (base p (P.obj.map u.op x)) hR)).isSeparatedFor.ext ?_
  intro Z w hw
  have hw' : R (w ≫ base p (P.obj.map u.op x)) := hw
  rw [base_map] at hw'
  have hwu : R ((w ≫ u) ≫ base p x) := by rwa [Category.assoc]
  have hval : P.obj.map (w ≫ u).op x = P.obj.map w.op (P.obj.map u.op x) := by
    rw [← map_comp_apply, ← op_comp]
  rw [← map_comp_apply, ← op_comp, Φ.glueApp_res hR x (w ≫ u) hwu,
    Φ.glueApp_res hR (P.obj.map u.op x) w hw]
  exact congrArg (Φ.app (W := Z)) (Subtype.ext hval)

/-- **Descent of arrows.**  The morphism of sheaves glued from a partial morphism defined over a
covering sieve. -/
noncomputable def glue (hR : R ∈ J S) : P ⟶ Q :=
  ObjectProperty.homMk
    { app := fun W => TypeCat.ofHom fun (x : P.obj.obj W) => Φ.glueApp hR (W := W.unop) x
      naturality := fun _ _ f => by
        ext x
        exact (Φ.glueApp_naturality hR f.unop x).symm }

@[simp]
lemma glue_app (hR : R ∈ J S) {W : C} (x : SectionsOver p R W) :
    (Φ.glue hR).hom.app (op W) x.1 = Φ.app x := by
  have h1 : R (𝟙 W ≫ base p x.1) := by rw [Category.id_comp]; exact x.2
  have key := Φ.glueApp_res hR x.1 (𝟙 W) h1
  have e : Q.obj.map (𝟙 W).op (Φ.glueApp hR x.1) = Φ.glueApp hR x.1 := by
    rw [op_id, map_id_apply]
  rw [e] at key
  have hval : P.obj.map (𝟙 W).op x.1 = x.1 := by rw [op_id, map_id_apply]
  exact key.trans (congrArg (Φ.app (W := W)) (Subtype.ext hval))

/-- **Descent of arrows, uniqueness form.**  A partial morphism defined on the sections whose
base lies in a covering sieve extends to a morphism of sheaves in exactly one way. -/
theorem exists_unique_glue (hR : R ∈ J S) :
    ∃! φ : P ⟶ Q, ∀ (W : C) (x : SectionsOver p R W), φ.hom.app (op W) x.1 = Φ.app x :=
  ⟨Φ.glue hR, fun W x => Φ.glue_app hR x, fun _ hψ =>
    hom_ext_of_sieve p hR fun W x => by rw [hψ W x, Φ.glue_app hR x]⟩

/-- If a partial morphism is a morphism over `S`, then so is the glued morphism. -/
theorem glue_comp (hR : R ∈ J S) (q : Q ⟶ J.yoneda.obj S)
    (hq : ∀ (W : C) (x : SectionsOver p R W), base q (Φ.app x) = base p x.1) :
    Φ.glue hR ≫ q = p := by
  refine hom_ext_of_sieve p hR fun W x => ?_
  change q.hom.app (op W) ((Φ.glue hR).hom.app (op W) x.1) = base p x.1
  rw [Φ.glue_app hR x]
  exact hq W x

end PartialHom

/-- The sections over `W` of the fibre product `P ×_{y S} y T` of the structure morphism `p` of a
sheaf over `S` with `y f`, for `f : T ⟶ S`: a morphism `W ⟶ T` together with a section of `P`
over `W` having the same image in `S`. -/
abbrev FibSections (p : P ⟶ J.yoneda.obj S) {T : C} (f : T ⟶ S) (W : C) : Type v :=
  {z : (W ⟶ T) × P.obj.obj (op W) // base p z.2 = z.1 ≫ f}

namespace FibSections

variable {p : P ⟶ J.yoneda.obj S}

/-- Restriction of a section of `P ×_{y S} y T` along a morphism of `C`. -/
def res {T : C} {f : T ⟶ S} {V W : C} (u : V ⟶ W) (z : FibSections p f W) :
    FibSections p f V :=
  ⟨(u ≫ z.1.1, P.obj.map u.op z.1.2), by rw [base_map, z.2, Category.assoc]⟩

/-- Reindexing a section of `P ×_{y S} y T'` to a section of `P ×_{y S} y T` along a morphism
`k : T' ⟶ T` over `S`. -/
def along {T T' : C} {f : T ⟶ S} (k : T' ⟶ T) {W : C} (z : FibSections p (k ≫ f) W) :
    FibSections p f W :=
  ⟨(z.1.1 ≫ k, z.1.2), by rw [z.2, Category.assoc]⟩

end FibSections

/-- A compatible family of morphisms `P ×_{y S} y T ⟶ Q ×_{y S} y T` over `y T`, one for each
member `f : T ⟶ S` of the sieve `R`.  This is the literal fibre-product formulation of the
descent datum for arrows; see `SieveHomFamily.toPartialHom` for the translation into the
elementary formulation. -/
structure SieveHomFamily (p : P ⟶ J.yoneda.obj S) (q : Q ⟶ J.yoneda.obj S) (R : Sieve S) where
  /-- The morphism attached to a member of the sieve. -/
  app : ∀ {T : C} (f : T ⟶ S), R f → ∀ {W : C}, FibSections p f W → FibSections q f W
  /-- Each morphism of the family lies over `y T`. -/
  base_app : ∀ {T : C} (f : T ⟶ S) (hf : R f) {W : C} (z : FibSections p f W),
    (app f hf z).1.1 = z.1.1
  /-- Each morphism of the family is a morphism of sheaves. -/
  naturality : ∀ {T : C} (f : T ⟶ S) (hf : R f) {V W : C} (u : V ⟶ W) (z : FibSections p f W),
    app f hf (FibSections.res u z) = FibSections.res u (app f hf z)
  /-- The morphisms of the family agree on overlaps, i.e. after restriction along the morphisms
  of the sieve. -/
  compat : ∀ {T T' : C} (f : T ⟶ S) (hf : R f) (k : T' ⟶ T) {W : C}
      (z : FibSections p (k ≫ f) W),
    (app (k ≫ f) (R.downward_closed hf k) z).1.2 = (app f hf (FibSections.along k z)).1.2

namespace SieveHomFamily

variable {p : P ⟶ J.yoneda.obj S} {q : Q ⟶ J.yoneda.obj S} {R : Sieve S}
  (Φ : SieveHomFamily p q R)

lemma app_congr {T W : C} {f f' : T ⟶ S} (hff : f = f') (hf : R f) (hf' : R f')
    (z : FibSections p f W) (z' : FibSections p f' W) (hz : z.1 = z'.1) :
    (Φ.app f hf z).1.2 = (Φ.app f' hf' z').1.2 := by
  subst hff
  exact congrArg (fun w => (Φ.app f hf w).1.2) (Subtype.ext hz)

/-- The tautological section of `P ×_{y S} y (base p x)` attached to a section `x` of `P`. -/
def taut {W : C} (x : P.obj.obj (op W)) : FibSections p (base p x) W :=
  ⟨(𝟙 W, x), (Category.id_comp _).symm⟩

/-- The elementary partial morphism attached to a compatible family of morphisms over a sieve. -/
def toPartialHom : PartialHom p Q R where
  app x := (Φ.app (base p x.1) x.2 (taut x.1)).1.2
  naturality := fun {V W} u x => by
    have hb : base p (P.obj.map u.op x.1) = u ≫ base p x.1 := base_map p u x.1
    have hu : R (u ≫ base p x.1) := R.downward_closed x.2 u
    let z' : FibSections p (u ≫ base p x.1) V :=
      ⟨(𝟙 V, P.obj.map u.op x.1), by rw [hb]; exact (Category.id_comp _).symm⟩
    have e1 : (Φ.app (base p (P.obj.map u.op x.1)) (SectionsOver.res u x).2
          (taut (P.obj.map u.op x.1))).1.2 = (Φ.app (u ≫ base p x.1) hu z').1.2 :=
      Φ.app_congr hb _ _ _ _ rfl
    have e2 := Φ.compat (base p x.1) x.2 u z'
    have e3 := Φ.naturality (base p x.1) x.2 u (taut x.1)
    have e4 : (Φ.app (base p x.1) x.2 (FibSections.res u (taut x.1))).1.2
        = (Φ.app (base p x.1) x.2 (FibSections.along u z')).1.2 :=
      Φ.app_congr rfl _ _ _ _ (by simp [FibSections.res, FibSections.along, taut, z'])
    refine Eq.trans ?_ e1.symm
    refine Eq.trans ?_ e2.symm
    refine Eq.trans ?_ e4
    exact (congrArg (fun w : FibSections q (base p x.1) V => w.1.2) e3).symm

lemma toPartialHom_app {W : C} (x : SectionsOver p R W) :
    Φ.toPartialHom.app x = (Φ.app (base p x.1) x.2 (taut x.1)).1.2 :=
  rfl

lemma toPartialHom_base {W : C} (x : SectionsOver p R W) :
    base q (Φ.toPartialHom.app x) = base p x.1 := by
  have h := (Φ.app (base p x.1) x.2 (taut x.1)).2
  rw [Φ.base_app (base p x.1) x.2 (taut x.1)] at h
  rw [toPartialHom_app]
  refine h.trans ?_
  change 𝟙 W ≫ base p x.1 = base p x.1
  rw [Category.id_comp]

/-- **Descent of arrows, fibre-product formulation.**  The morphism `P ⟶ Q` glued from a
compatible family of morphisms after base change along a covering sieve. -/
noncomputable def glue (hR : R ∈ J S) : P ⟶ Q :=
  Φ.toPartialHom.glue hR

lemma glue_app_fib (hR : R ∈ J S) {T W : C} (f : T ⟶ S) (hf : R f) (z : FibSections p f W) :
    (Φ.glue hR).hom.app (op W) z.1.2 = (Φ.app f hf z).1.2 := by
  have hz : R (base p z.1.2) := by rw [z.2]; exact R.downward_closed hf z.1.1
  have key := Φ.toPartialHom.glue_app hR (⟨z.1.2, hz⟩ : SectionsOver p R W)
  refine key.trans ?_
  rw [toPartialHom_app]
  have e1 : (Φ.app (base p z.1.2) hz (taut z.1.2)).1.2
      = (Φ.app (z.1.1 ≫ f) (R.downward_closed hf z.1.1)
          (⟨(𝟙 W, z.1.2), by rw [z.2]; exact (Category.id_comp _).symm⟩ :
            FibSections p (z.1.1 ≫ f) W)).1.2 :=
    Φ.app_congr z.2 _ _ _ _ rfl
  have e2 := Φ.compat f hf z.1.1
    (⟨(𝟙 W, z.1.2), by rw [z.2]; exact (Category.id_comp _).symm⟩ :
      FibSections p (z.1.1 ≫ f) W)
  have e3 : (Φ.app f hf (FibSections.along z.1.1
        (⟨(𝟙 W, z.1.2), by rw [z.2]; exact (Category.id_comp _).symm⟩ :
          FibSections p (z.1.1 ≫ f) W))).1.2 = (Φ.app f hf z).1.2 :=
    Φ.app_congr rfl _ _ _ _ (by simp [FibSections.along])
  exact e1.trans (e2.trans e3)

/-- The glued morphism lies over `y S`. -/
theorem glue_comp (hR : R ∈ J S) : Φ.glue hR ≫ q = p :=
  Φ.toPartialHom.glue_comp hR q fun _ x => Φ.toPartialHom_base x

/-- **Descent of arrows, fibre-product formulation, uniqueness form.**  A compatible family of
morphisms `P ×_{y S} y T ⟶ Q ×_{y S} y T` over `y T`, indexed by the members of a covering sieve
of `S`, comes from a unique morphism `P ⟶ Q`, which moreover lies over `y S`. -/
theorem exists_unique_glue_hom (hR : R ∈ J S) :
    ∃! φ : P ⟶ Q, ∀ (T W : C) (f : T ⟶ S) (hf : R f) (z : FibSections p f W),
      φ.hom.app (op W) z.1.2 = (Φ.app f hf z).1.2 := by
  refine ⟨Φ.glue hR, fun T W f hf z => Φ.glue_app_fib hR f hf z, fun ψ hψ => ?_⟩
  refine hom_ext_of_sieve p hR fun W x => ?_
  exact (hψ W W (base p x.1) x.2 (taut x.1)).trans
    (Φ.glue_app_fib hR (base p x.1) x.2 (taut x.1)).symm

end SieveHomFamily

/-- Compatible isomorphism data between two sheaves `P` and `Q` over `S`, given over a sieve `R`.

This is the elementary form of the datum of isomorphisms
`P ×_{y S} y T ≅ Q ×_{y S} y T` over `y T`, one for each `f : T ⟶ S` in `R`, compatible with
restriction along the morphisms of the sieve. -/
structure PartialIso (p : P ⟶ J.yoneda.obj S) (q : Q ⟶ J.yoneda.obj S) (R : Sieve S) where
  /-- The partial morphism from `P` to `Q`. -/
  hom : PartialHom p Q R
  /-- The partial morphism from `Q` to `P`. -/
  inv : PartialHom q P R
  /-- `hom` is a morphism over `S`. -/
  base_hom : ∀ {W : C} (x : SectionsOver p R W), base q (hom.app x) = base p x.1
  /-- `inv` is a morphism over `S`. -/
  base_inv : ∀ {W : C} (y : SectionsOver q R W), base p (inv.app y) = base q y.1
  /-- `inv` is a left inverse of `hom`. -/
  hom_inv : ∀ {W : C} (x : SectionsOver p R W),
    inv.app ⟨hom.app x, by rw [base_hom]; exact x.2⟩ = x.1
  /-- `inv` is a right inverse of `hom`. -/
  inv_hom : ∀ {W : C} (y : SectionsOver q R W),
    hom.app ⟨inv.app y, by rw [base_inv]; exact y.2⟩ = y.1

namespace PartialIso

variable {p : P ⟶ J.yoneda.obj S} {q : Q ⟶ J.yoneda.obj S} {R : Sieve S}
  (e : PartialIso p q R)

/-- **Uniqueness of the glued sheaf.**  Two sheaves over `S` whose restrictions to a covering
sieve are compatibly isomorphic are isomorphic. -/
noncomputable def glue (hR : R ∈ J S) : P ≅ Q where
  hom := e.hom.glue hR
  inv := e.inv.glue hR
  hom_inv_id := by
    refine hom_ext_of_sieve p hR fun W x => ?_
    have hx : R (base q (e.hom.app x)) := by rw [e.base_hom]; exact x.2
    change (e.inv.glue hR).hom.app (op W) ((e.hom.glue hR).hom.app (op W) x.1) = x.1
    rw [e.hom.glue_app hR x, e.inv.glue_app hR ⟨e.hom.app x, hx⟩]
    exact e.hom_inv x
  inv_hom_id := by
    refine hom_ext_of_sieve q hR fun W y => ?_
    have hy : R (base p (e.inv.app y)) := by rw [e.base_inv]; exact y.2
    change (e.hom.glue hR).hom.app (op W) ((e.inv.glue hR).hom.app (op W) y.1) = y.1
    rw [e.inv.glue_app hR y, e.hom.glue_app hR ⟨e.inv.app y, hy⟩]
    exact e.inv_hom y

lemma glue_hom (hR : R ∈ J S) {W : C} (x : SectionsOver p R W) :
    (e.glue hR).hom.hom.app (op W) x.1 = e.hom.app x :=
  e.hom.glue_app hR x

lemma glue_inv (hR : R ∈ J S) {W : C} (y : SectionsOver q R W) :
    (e.glue hR).inv.hom.app (op W) y.1 = e.inv.app y :=
  e.inv.glue_app hR y

/-- The glued isomorphism is an isomorphism over `S`. -/
theorem glue_hom_comp (hR : R ∈ J S) : (e.glue hR).hom ≫ q = p :=
  e.hom.glue_comp hR q fun _ x => e.base_hom x

/-- The glued isomorphism is an isomorphism over `S`, in the other direction. -/
theorem glue_inv_comp (hR : R ∈ J S) : (e.glue hR).inv ≫ p = q :=
  e.inv.glue_comp hR p fun _ y => e.base_inv y

/-- **Uniqueness of the glued sheaf, existential form.** -/
theorem exists_iso_over (hR : R ∈ J S) :
    ∃ φ : P ≅ Q, φ.hom ≫ q = p ∧ φ.inv ≫ p = q ∧
      ∀ (W : C) (x : SectionsOver p R W), φ.hom.hom.app (op W) x.1 = e.hom.app x :=
  ⟨e.glue hR, e.glue_hom_comp hR, e.glue_inv_comp hR, fun _ x => e.glue_hom hR x⟩

end PartialIso

section EffectiveDescent

open CategoryTheory.Limits

variable {X : C} (f : X ⟶ S) (pX : P ⟶ J.yoneda.obj X)

/-- The fibre of a sheaf `P` over `X` at a morphism `a : W ⟶ X`: the sections of `P` over `W`
whose base is `a`.  These are the sections over `W` of the fibre product `P ×_{y X} y W`. -/
abbrev Fibre {W : C} (a : W ⟶ X) : Type v :=
  {x : P.obj.obj (op W) // base pX x = a}

/-- Restriction of an element of a fibre along a morphism of `C`. -/
def Fibre.restrict {V W : C} {a : W ⟶ X} (u : V ⟶ W) (x : Fibre pX a) : Fibre pX (u ≫ a) :=
  ⟨P.obj.map u.op x.1, by rw [base_map, x.2]⟩

@[simp]
lemma Fibre.restrict_val {V W : C} {a : W ⟶ X} (u : V ⟶ W) (x : Fibre pX a) :
    (Fibre.restrict pX u x).1 = P.obj.map u.op x.1 :=
  rfl

/-- A descent datum for the sheaf `P` over `X` along a morphism `f : X ⟶ S`: an isomorphism
between the two pullbacks of `P` to `X ×_S X`, given fibrewise, subject to the cocycle
condition.  Fibrewise, the two pullbacks of `P` along a morphism `W ⟶ X ×_S X` given by a pair
`(a, b)` are the fibres of `P` at `a` and at `b`. -/
structure DescentDatum where
  /-- The transition map between the fibres at two morphisms agreeing over `S`. -/
  θ : ∀ {W : C} {a b : W ⟶ X}, a ≫ f = b ≫ f → Fibre pX a → Fibre pX b
  /-- The transition maps are morphisms of sheaves. -/
  θ_restrict : ∀ {V W : C} (u : V ⟶ W) {a b : W ⟶ X} (h : a ≫ f = b ≫ f) (x : Fibre pX a),
    Fibre.restrict pX u (θ h x) =
      θ (by rw [Category.assoc, h, Category.assoc]) (Fibre.restrict pX u x)
  /-- The transition map along a trivial identification is the identity. -/
  θ_id : ∀ {W : C} {a : W ⟶ X} (x : Fibre pX a), θ (rfl : a ≫ f = a ≫ f) x = x
  /-- The cocycle condition. -/
  θ_comp : ∀ {W : C} {a b c : W ⟶ X} (hab : a ≫ f = b ≫ f) (hbc : b ≫ f = c ≫ f)
      (x : Fibre pX a), θ hbc (θ hab x) = θ (hab.trans hbc) x

variable [HasPullbacks C] {f pX}

/-- Evaluation of a section of `P` over `W ×_S X` at a test square. -/
noncomputable def evOf {W : C} {s : W ⟶ S} (ξ : Fibre pX (pullback.snd s f)) {Z : C} (c : Z ⟶ W)
    (d : Z ⟶ X) (h : c ≫ s = d ≫ f) : Fibre pX d :=
  ⟨P.obj.map (pullback.lift c d h).op ξ.1, by rw [base_map, ξ.2, pullback.lift_snd]⟩

lemma evOf_val {W : C} {s : W ⟶ S} (ξ : Fibre pX (pullback.snd s f)) {Z : C} (c : Z ⟶ W)
    (d : Z ⟶ X) (h : c ≫ s = d ≫ f) :
    (evOf ξ c d h).1 = P.obj.map (pullback.lift c d h).op ξ.1 :=
  rfl

lemma evOf_congr {W : C} {s : W ⟶ S} (ξ : Fibre pX (pullback.snd s f)) {Z : C} {c c' : Z ⟶ W}
    {d d' : Z ⟶ X} (hc : c = c') (hd : d = d') (h : c ≫ s = d ≫ f) (h' : c' ≫ s = d' ≫ f) :
    (evOf ξ c d h).1 = (evOf ξ c' d' h').1 := by
  subst hc; subst hd; rfl

lemma evOf_restrict {W : C} {s : W ⟶ S} (ξ : Fibre pX (pullback.snd s f)) {Z Z' : C}
    (w : Z' ⟶ Z) (c : Z ⟶ W) (d : Z ⟶ X) (h : c ≫ s = d ≫ f)
    (h' : (w ≫ c) ≫ s = (w ≫ d) ≫ f) :
    Fibre.restrict pX w (evOf ξ c d h) = evOf ξ (w ≫ c) (w ≫ d) h' := by
  apply Subtype.ext
  have hl : pullback.lift (w ≫ c) (w ≫ d) h' = w ≫ pullback.lift c d h := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]
  rw [Fibre.restrict_val, evOf_val, evOf_val, hl, op_comp, map_comp_apply]

lemma evOf_self {W : C} {s : W ⟶ S} (ξ : Fibre pX (pullback.snd s f)) :
    evOf ξ (pullback.fst s f) (pullback.snd s f) pullback.condition = ξ := by
  apply Subtype.ext
  rw [evOf_val]
  have hl : pullback.lift (pullback.fst s f) (pullback.snd s f) pullback.condition = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_
    · simp only [pullback.lift_fst, Category.id_comp]
    · simp only [pullback.lift_snd, Category.id_comp]
  rw [hl, op_id, map_id_apply]

/-- The descent (cocycle) condition on a section of `P` over `W ×_S X`. -/
def IsDescentSection (D : DescentDatum f pX) {W : C} {s : W ⟶ S}
    (ξ : Fibre pX (pullback.snd s f)) : Prop :=
  ∀ ⦃Z : C⦄ (c : Z ⟶ W) (d₁ d₂ : Z ⟶ X) (h₁ : c ≫ s = d₁ ≫ f) (h₂ : c ≫ s = d₂ ≫ f),
    D.θ (h₁.symm.trans h₂) (evOf ξ c d₁ h₁) = evOf ξ c d₂ h₂

/-- The sections over `W` of the sheaf glued from a descent datum: a morphism `s : W ⟶ S`
together with a section of `P` over `W ×_S X` satisfying the descent condition. -/
def GlueObj (D : DescentDatum f pX) (W : C) : Type v :=
  Σ s : W ⟶ S, {ξ : Fibre pX (pullback.snd s f) // IsDescentSection D ξ}

variable {D : DescentDatum f pX}

/-- Evaluation of a section of the glued object at a test square. -/
noncomputable def ev {W : C} (z : GlueObj D W) {Z : C} (c : Z ⟶ W) (d : Z ⟶ X)
    (h : c ≫ z.1 = d ≫ f) : Fibre pX d :=
  evOf z.2.1 c d h

lemma ev_congr' {W : C} (z : GlueObj D W) {Z : C} {c c' : Z ⟶ W} {d d' : Z ⟶ X}
    (hc : c = c') (hd : d = d') (h : c ≫ z.1 = d ≫ f) (h' : c' ≫ z.1 = d' ≫ f) :
    (ev z c d h).1 = (ev z c' d' h').1 :=
  evOf_congr _ hc hd h h'

lemma ev_congr {W : C} {z z' : GlueObj D W} (hz : z = z') {Z : C} (c : Z ⟶ W) (d : Z ⟶ X)
    (h : c ≫ z.1 = d ≫ f) (h' : c ≫ z'.1 = d ≫ f) : (ev z c d h).1 = (ev z' c d h').1 := by
  subst hz; rfl

lemma ev_restrict {W : C} (z : GlueObj D W) {Z Z' : C} (w : Z' ⟶ Z) (c : Z ⟶ W) (d : Z ⟶ X)
    (h : c ≫ z.1 = d ≫ f) (h' : (w ≫ c) ≫ z.1 = (w ≫ d) ≫ f) :
    Fibre.restrict pX w (ev z c d h) = ev z (w ≫ c) (w ≫ d) h' :=
  evOf_restrict _ w c d h h'

lemma ev_descent {W : C} (z : GlueObj D W) {Z : C} (c : Z ⟶ W) (d₁ d₂ : Z ⟶ X)
    (h₁ : c ≫ z.1 = d₁ ≫ f) (h₂ : c ≫ z.1 = d₂ ≫ f) :
    D.θ (h₁.symm.trans h₂) (ev z c d₁ h₁) = ev z c d₂ h₂ :=
  z.2.2 c d₁ d₂ h₁ h₂

lemma glueObj_ext {W : C} {z z' : GlueObj D W} (h1 : z.1 = z'.1)
    (h2 : ∀ {Z : C} (c : Z ⟶ W) (d : Z ⟶ X) (h : c ≫ z.1 = d ≫ f) (h' : c ≫ z'.1 = d ≫ f),
      (ev z c d h).1 = (ev z' c d h').1) : z = z' := by
  obtain ⟨s, ξ⟩ := z
  obtain ⟨s', ξ'⟩ := z'
  have h1' : s = s' := h1
  subst h1'
  refine congrArg (Sigma.mk s) (Subtype.ext (Subtype.ext ?_))
  have key := h2 (pullback.fst s f) (pullback.snd s f) pullback.condition pullback.condition
  rw [show (ev ⟨s, ξ⟩ (pullback.fst s f) (pullback.snd s f) pullback.condition).1 = ξ.1.1 from
      congrArg Subtype.val (evOf_self ξ.1),
    show (ev ⟨s, ξ'⟩ (pullback.fst s f) (pullback.snd s f) pullback.condition).1 = ξ'.1.1 from
      congrArg Subtype.val (evOf_self ξ'.1)] at key
  exact key

lemma glueMapCond {V W : C} (u : V ⟶ W) (z : GlueObj D W) :
    (pullback.fst (u ≫ z.1) f ≫ u) ≫ z.1 = pullback.snd (u ≫ z.1) f ≫ f := by
  rw [Category.assoc]; exact pullback.condition

/-- The section of `P` over `V ×_S X` obtained by restricting a section of the glued object
along `u : V ⟶ W`. -/
noncomputable def glueSectionAux {V W : C} (u : V ⟶ W) (z : GlueObj D W) :
    Fibre pX (pullback.snd (u ≫ z.1) f) :=
  evOf z.2.1 (pullback.fst (u ≫ z.1) f ≫ u) (pullback.snd (u ≫ z.1) f) (glueMapCond u z)

lemma evOf_glueSectionAux {V W : C} (u : V ⟶ W) (z : GlueObj D W) {Z : C} (c : Z ⟶ V)
    (d : Z ⟶ X) (h : c ≫ (u ≫ z.1) = d ≫ f) (h' : (c ≫ u) ≫ z.1 = d ≫ f) :
    (evOf (glueSectionAux u z) c d h).1 = (ev z (c ≫ u) d h').1 := by
  have hl : pullback.lift c d h ≫ pullback.lift (pullback.fst (u ≫ z.1) f ≫ u)
      (pullback.snd (u ≫ z.1) f) (glueMapCond u z) = pullback.lift (c ≫ u) d h' := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, pullback.lift_snd]
  dsimp only [glueSectionAux, ev]
  rw [evOf_val, evOf_val, evOf_val, ← map_comp_apply, ← op_comp, hl]

lemma isDescentSection_glueSectionAux {V W : C} (u : V ⟶ W) (z : GlueObj D W) :
    IsDescentSection D (glueSectionAux u z) := by
  intro Z c d₁ d₂ h₁ h₂
  have k₁ : (c ≫ u) ≫ z.1 = d₁ ≫ f := by rw [Category.assoc]; exact h₁
  have k₂ : (c ≫ u) ≫ z.1 = d₂ ≫ f := by rw [Category.assoc]; exact h₂
  have e₁ : evOf (glueSectionAux u z) c d₁ h₁ = ev z (c ≫ u) d₁ k₁ :=
    Subtype.ext (evOf_glueSectionAux u z c d₁ h₁ k₁)
  have e₂ : evOf (glueSectionAux u z) c d₂ h₂ = ev z (c ≫ u) d₂ k₂ :=
    Subtype.ext (evOf_glueSectionAux u z c d₂ h₂ k₂)
  rw [e₁, e₂]
  exact ev_descent z (c ≫ u) d₁ d₂ k₁ k₂

/-- The restriction map of the glued presheaf. -/
noncomputable def glueMap {V W : C} (u : V ⟶ W) (z : GlueObj D W) : GlueObj D V :=
  ⟨u ≫ z.1, ⟨glueSectionAux u z, isDescentSection_glueSectionAux u z⟩⟩

@[simp]
lemma glueMap_fst {V W : C} (u : V ⟶ W) (z : GlueObj D W) : (glueMap u z).1 = u ≫ z.1 :=
  rfl

lemma ev_glueMap {V W : C} (u : V ⟶ W) (z : GlueObj D W) {Z : C} (c : Z ⟶ V) (d : Z ⟶ X)
    (h : c ≫ (glueMap u z).1 = d ≫ f) (h' : (c ≫ u) ≫ z.1 = d ≫ f) :
    (ev (glueMap u z) c d h).1 = (ev z (c ≫ u) d h').1 :=
  evOf_glueSectionAux u z c d h h'

variable (D)

/-- The presheaf of types glued from a descent datum along `f : X ⟶ S`. -/
noncomputable def gluePresheaf : Cᵒᵖ ⥤ Type v where
  obj W := GlueObj D W.unop
  map u := TypeCat.ofHom (glueMap u.unop)
  map_id W := by
    ext z
    refine glueObj_ext (by simp) fun c d hh hh' => ?_
    exact (ev_glueMap _ z c d hh (by simpa using hh')).trans
      (ev_congr' z (Category.comp_id c) rfl _ hh')
  map_comp g h := by
    ext z
    refine glueObj_ext (by simp) fun c d hh hh' => ?_
    have hb : c ≫ ((h.unop ≫ g.unop) ≫ z.1) = d ≫ f := hh
    have h1 : (c ≫ h.unop ≫ g.unop) ≫ z.1 = d ≫ f := by
      simpa only [Category.assoc] using hb
    have h2 : ((c ≫ h.unop) ≫ g.unop) ≫ z.1 = d ≫ f := by
      simpa only [Category.assoc] using hb
    have h4 : (c ≫ h.unop) ≫ g.unop ≫ z.1 = d ≫ f := by
      simpa only [Category.assoc] using hb
    refine (ev_glueMap _ z c d hh h1).trans ?_
    refine (ev_congr' z (Category.assoc c h.unop g.unop).symm rfl h1 h2).trans ?_
    refine (ev_glueMap g.unop z (c ≫ h.unop) d h4 h2).symm.trans ?_
    exact (ev_glueMap h.unop (glueMap g.unop z) c d hh' h4).symm

/-- The structure morphism from the glued presheaf to the sheaf represented by `S`. -/
def glueBase : gluePresheaf D ⟶ (J.yoneda.obj S).obj where
  app _ := TypeCat.ofHom fun z => z.1
  naturality _ _ _ := by ext z; rfl

section SheafCondition

variable {D}

lemma glueObj_fst_congr {W : C} {z z' : GlueObj D W} (h : z = z') : z.1 = z'.1 := by rw [h]

variable {W : C} {K : Sieve W} (fam : Presieve.FamilyOfElements (gluePresheaf D) K.arrows)

/-- The value at a test point of a member of a family of sections of the glued presheaf. -/
noncomputable def famEv {Z : C} (a : Z ⟶ W) (ha : K a) (d : Z ⟶ X)
    (h : 𝟙 Z ≫ (fam a ha).1 = d ≫ f) : P.obj.obj (op Z) :=
  (ev (fam a ha) (𝟙 Z) d h).1

lemma base_famEv {Z : C} (a : Z ⟶ W) (ha : K a) (d : Z ⟶ X)
    (h : 𝟙 Z ≫ (fam a ha).1 = d ≫ f) : base pX (famEv fam a ha d h) = d :=
  (ev (fam a ha) (𝟙 Z) d h).2

lemma famEv_congr {Z : C} {a a' : Z ⟶ W} (haa : a = a') (ha : K a) (ha' : K a')
    {d d' : Z ⟶ X} (hdd : d = d') (h : 𝟙 Z ≫ (fam a ha).1 = d ≫ f)
    (h' : 𝟙 Z ≫ (fam a' ha').1 = d' ≫ f) :
    famEv fam a ha d h = famEv fam a' ha' d' h' := by
  subst haa; subst hdd; rfl

lemma ev_fam (hfam : fam.Compatible) {V Z : C} (u : V ⟶ W) (hu : K u) (g : Z ⟶ V)
    (d : Z ⟶ X) (h : g ≫ (fam u hu).1 = d ≫ f)
    (h' : 𝟙 Z ≫ (fam (g ≫ u) (K.downward_closed hu g)).1 = d ≫ f) :
    (ev (fam u hu) g d h).1 = famEv fam (g ≫ u) (K.downward_closed hu g) d h' := by
  have e : fam (g ≫ u) (K.downward_closed hu g) = glueMap g (fam u hu) :=
    (Presieve.compatible_iff_sieveCompatible fam).1 hfam u g hu
  have h2 : 𝟙 Z ≫ (glueMap g (fam u hu)).1 = d ≫ f := by rw [← e]; exact h'
  have h3 : (𝟙 Z ≫ g) ≫ (fam u hu).1 = d ≫ f := by rw [Category.id_comp]; exact h
  refine Eq.trans ?_ (ev_congr e.symm (𝟙 Z) d h2 h')
  refine Eq.trans ?_ (ev_glueMap g (fam u hu) (𝟙 Z) d h2 h3).symm
  exact ev_congr' (fam u hu) (Category.id_comp g).symm rfl h h3

lemma famEv_restrict (hfam : fam.Compatible) {Z Z' : C} (a : Z ⟶ W) (ha : K a) (d : Z ⟶ X)
    (h : 𝟙 Z ≫ (fam a ha).1 = d ≫ f) (g : Z' ⟶ Z)
    (h' : 𝟙 Z' ≫ (fam (g ≫ a) (K.downward_closed ha g)).1 = (g ≫ d) ≫ f) :
    P.obj.map g.op (famEv fam a ha d h)
      = famEv fam (g ≫ a) (K.downward_closed ha g) (g ≫ d) h' := by
  have h0 : (fam a ha).1 = d ≫ f := by rw [← Category.id_comp ((fam a ha).1)]; exact h
  have hg : g ≫ (fam a ha).1 = (g ≫ d) ≫ f := by rw [h0, Category.assoc]
  have h2 : (g ≫ 𝟙 Z) ≫ (fam a ha).1 = (g ≫ d) ≫ f := by rw [Category.comp_id]; exact hg
  refine (congrArg Subtype.val (ev_restrict (fam a ha) g (𝟙 Z) d h h2)).trans ?_
  refine (ev_congr' (fam a ha) (Category.comp_id g) rfl h2 hg).trans ?_
  exact ev_fam fam hfam a ha g (g ≫ d) hg h'

variable (sW : W ⟶ S) (hsW : ∀ ⦃V : C⦄ (u : V ⟶ W) (hu : K u), u ≫ sW = (fam u hu).1)

include hsW in
lemma descCond {Z : C} (w : Z ⟶ pullback sW f) (hw : K (w ≫ pullback.fst sW f)) :
    𝟙 Z ≫ (fam (w ≫ pullback.fst sW f) hw).1 = (w ≫ pullback.snd sW f) ≫ f := by
  rw [Category.id_comp, ← hsW _ hw, Category.assoc, Category.assoc, pullback.condition]

/-- The family of sections of `P` over the base change of a covering sieve, attached to a
compatible family of sections of the glued presheaf. -/
noncomputable def descFamily :
    Presieve.FamilyOfElements P.obj (K.pullback (pullback.fst sW f)).arrows :=
  fun _ w hw => famEv fam (w ≫ pullback.fst sW f) hw (w ≫ pullback.snd sW f)
    (descCond fam sW hsW w hw)

lemma descFamily_compatible (hfam : fam.Compatible) : (descFamily fam sW hsW).Compatible := by
  intro Z₁ Z₂ Z g₁ g₂ w₁ w₂ hw₁ hw₂ hc
  have hq : g₁ ≫ w₁ ≫ pullback.fst sW f = g₂ ≫ w₂ ≫ pullback.fst sW f := by
    rw [← Category.assoc, ← Category.assoc, hc]
  have hr : g₁ ≫ w₁ ≫ pullback.snd sW f = g₂ ≫ w₂ ≫ pullback.snd sW f := by
    rw [← Category.assoc, ← Category.assoc, hc]
  have hK₁ : K (g₁ ≫ w₁ ≫ pullback.fst sW f) := K.downward_closed hw₁ g₁
  have hK₂ : K (g₂ ≫ w₂ ≫ pullback.fst sW f) := K.downward_closed hw₂ g₂
  have he₁ : 𝟙 Z ≫ (fam _ hK₁).1 = (g₁ ≫ w₁ ≫ pullback.snd sW f) ≫ f := by
    rw [Category.id_comp, ← hsW _ hK₁, Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, pullback.condition]
  have he₂ : 𝟙 Z ≫ (fam _ hK₂).1 = (g₂ ≫ w₂ ≫ pullback.snd sW f) ≫ f := by
    rw [Category.id_comp, ← hsW _ hK₂, Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, pullback.condition]
  refine (famEv_restrict fam hfam _ hw₁ _ (descCond fam sW hsW w₁ hw₁) g₁ he₁).trans ?_
  refine Eq.trans ?_ (famEv_restrict fam hfam _ hw₂ _ (descCond fam sW hsW w₂ hw₂) g₂ he₂).symm
  exact famEv_congr fam hq hK₁ hK₂ hr he₁ he₂

end SheafCondition

/-- **The presheaf glued from a descent datum is a sheaf.**  Gluing the base component uses that
the topology is subcanonical; gluing the `P`-component uses that the base change of a covering
sieve of `W` along `W ×_S X ⟶ W` is again a covering sieve. -/
theorem gluePresheaf_isSheaf : Presieve.IsSheaf J (gluePresheaf D) := by
  intro W K hK fam hfam
  obtain ⟨sW, hsW0, -⟩ := isSheafOfType (J.yoneda.obj S) K hK
    (fun _ u hu => (fam u hu).1)
    (fun _ _ _ g₁ g₂ _ _ h₁ h₂ hc => glueObj_fst_congr (hfam g₁ g₂ h₁ h₂ hc))
  have hsW : ∀ ⦃V : C⦄ (u : V ⟶ W) (hu : K u), u ≫ sW = (fam u hu).1 := fun _ u hu => hsW0 u hu
  obtain ⟨ξ₀, hξ₀, -⟩ := isSheafOfType P _ (J.pullback_stable (pullback.fst sW f) hK)
    (descFamily fam sW hsW) (descFamily_compatible fam sW hsW hfam)
  have hbase : base pX ξ₀ = pullback.snd sW f := by
    refine (isSheafOfType (J.yoneda.obj X) _
      (J.pullback_stable (pullback.fst sW f) hK)).isSeparatedFor.ext ?_
    intro Z w hw
    have e : base pX (P.obj.map w.op ξ₀) = w ≫ pullback.snd sW f := by
      rw [hξ₀ w hw]
      exact base_famEv fam _ hw _ _
    rw [base_map] at e
    exact e
  have key : ∀ ⦃Z : C⦄ (c : Z ⟶ W) (hc : K c) (d : Z ⟶ X) (hd : c ≫ sW = d ≫ f)
      (hd' : 𝟙 Z ≫ (fam c hc).1 = d ≫ f),
      evOf (⟨ξ₀, hbase⟩ : Fibre pX (pullback.snd sW f)) c d hd = ev (fam c hc) (𝟙 Z) d hd' := by
    intro Z c hc d hd hd'
    apply Subtype.ext
    have hlift : K (pullback.lift c d hd ≫ pullback.fst sW f) := by
      rw [pullback.lift_fst]; exact hc
    refine (hξ₀ (pullback.lift c d hd) hlift).trans ?_
    exact famEv_congr fam (pullback.lift_fst _ _ _) hlift hc (pullback.lift_snd _ _ _) _ hd'
  have hdesc : IsDescentSection D (⟨ξ₀, hbase⟩ : Fibre pX (pullback.snd sW f)) := by
    intro Z c d₁ d₂ h₁ h₂
    apply Subtype.ext
    refine (isSheafOfType P _ (J.pullback_stable c hK)).isSeparatedFor.ext ?_
    intro Z' w hw
    have hw' : K (w ≫ c) := hw
    have hd₁ : (w ≫ c) ≫ sW = (w ≫ d₁) ≫ f := by rw [Category.assoc, Category.assoc, h₁]
    have hd₂ : (w ≫ c) ≫ sW = (w ≫ d₂) ≫ f := by rw [Category.assoc, Category.assoc, h₂]
    have hf₁ : 𝟙 Z' ≫ (fam (w ≫ c) hw').1 = (w ≫ d₁) ≫ f := by
      rw [Category.id_comp, ← hsW _ hw']; exact hd₁
    have hf₂ : 𝟙 Z' ≫ (fam (w ≫ c) hw').1 = (w ≫ d₂) ≫ f := by
      rw [Category.id_comp, ← hsW _ hw']; exact hd₂
    have e₁ : Fibre.restrict pX w (evOf (⟨ξ₀, hbase⟩ : Fibre pX (pullback.snd sW f)) c d₁ h₁)
        = ev (fam (w ≫ c) hw') (𝟙 Z') (w ≫ d₁) hf₁ :=
      (evOf_restrict _ w c d₁ h₁ hd₁).trans (key (w ≫ c) hw' (w ≫ d₁) hd₁ hf₁)
    have e₂ : Fibre.restrict pX w (evOf (⟨ξ₀, hbase⟩ : Fibre pX (pullback.snd sW f)) c d₂ h₂)
        = ev (fam (w ≫ c) hw') (𝟙 Z') (w ≫ d₂) hf₂ :=
      (evOf_restrict _ w c d₂ h₂ hd₂).trans (key (w ≫ c) hw' (w ≫ d₂) hd₂ hf₂)
    have H : (w ≫ d₁) ≫ f = (w ≫ d₂) ≫ f := hf₁.symm.trans hf₂
    refine Eq.trans (congrArg Subtype.val
      (D.θ_restrict w (h₁.symm.trans h₂) (evOf _ c d₁ h₁))) ?_
    refine Eq.trans (congrArg (fun t => (D.θ H t).1) e₁) ?_
    refine Eq.trans (congrArg Subtype.val
      (ev_descent (fam (w ≫ c) hw') (𝟙 Z') (w ≫ d₁) (w ≫ d₂) hf₁ hf₂)) ?_
    exact (congrArg Subtype.val e₂).symm
  refine ⟨⟨sW, ⟨⟨ξ₀, hbase⟩, hdesc⟩⟩, ?_, ?_⟩
  · intro V u hu
    refine glueObj_ext (hsW u hu) ?_
    intro Z c d hh hh'
    have h1 : (c ≫ u) ≫ sW = d ≫ f := by rw [Category.assoc]; exact hh
    have hcu : K (c ≫ u) := K.downward_closed hu c
    have h2 : 𝟙 Z ≫ (fam (c ≫ u) hcu).1 = d ≫ f := by
      rw [Category.id_comp, ← hsW _ hcu]; exact h1
    refine (ev_glueMap u _ c d hh h1).trans ?_
    refine Eq.trans (congrArg Subtype.val (key (c ≫ u) hcu d h1 h2)) ?_
    exact (ev_fam fam hfam u hu c d hh' h2).symm
  · intro t ht
    refine glueObj_ext ?_ ?_
    · refine (isSheafOfType (J.yoneda.obj S) K hK).isSeparatedFor.ext ?_
      intro V u hu
      exact (glueObj_fst_congr (ht u hu)).trans (hsW u hu).symm
    · intro Z c d hh hh'
      refine (isSheafOfType P _ (J.pullback_stable c hK)).isSeparatedFor.ext ?_
      intro Z' w hw
      have hw' : K (w ≫ c) := hw
      have ht1 : (w ≫ c) ≫ t.1 = (w ≫ d) ≫ f := by rw [Category.assoc, Category.assoc, hh]
      have hs1 : (w ≫ c) ≫ sW = (w ≫ d) ≫ f := by rw [Category.assoc, Category.assoc, hh']
      have hf : 𝟙 Z' ≫ (fam (w ≫ c) hw').1 = (w ≫ d) ≫ f := by
        rw [Category.id_comp, ← hsW _ hw']; exact hs1
      have hg : 𝟙 Z' ≫ (glueMap (w ≫ c) t).1 = (w ≫ d) ≫ f := by
        rw [Category.id_comp]; exact ht1
      have hg2 : (𝟙 Z' ≫ (w ≫ c)) ≫ t.1 = (w ≫ d) ≫ f := by
        rw [Category.id_comp]; exact ht1
      refine Eq.trans (congrArg Subtype.val (ev_restrict t w c d hh ht1)) ?_
      refine Eq.trans ((ev_glueMap (w ≫ c) t (𝟙 Z') (w ≫ d) hg hg2).trans
        (ev_congr' t (Category.id_comp (w ≫ c)) rfl hg2 ht1)).symm ?_
      refine Eq.trans (ev_congr (ht (w ≫ c) hw') (𝟙 Z') (w ≫ d) hg hf) ?_
      refine Eq.trans (congrArg Subtype.val (key (w ≫ c) hw' (w ≫ d) hs1 hf)).symm ?_
      exact (congrArg Subtype.val (evOf_restrict _ w c d hh' hs1)).symm

/-- The sheaf glued from a descent datum along `f : X ⟶ S`. -/
noncomputable def glueSheaf : Sheaf J (Type v) :=
  ⟨gluePresheaf D, (isSheaf_iff_isSheaf_of_type J _).2 (gluePresheaf_isSheaf D)⟩

/-- The structure morphism of the glued sheaf to the sheaf represented by `S`. -/
noncomputable def glueSheafBase : glueSheaf D ⟶ J.yoneda.obj S :=
  ObjectProperty.homMk (glueBase D)

omit [HasPullbacks C] in
lemma θ_congr {W : C} {a b a' b' : W ⟶ X} (ha : a = a') (hb : b = b')
    (h : a ≫ f = b ≫ f) (h' : a' ≫ f = b' ≫ f) (x : Fibre pX a) (x' : Fibre pX a')
    (hx : x.1 = x'.1) : (D.θ h x).1 = (D.θ h' x').1 := by
  subst ha; subst hb
  exact congrArg Subtype.val (congrArg (D.θ h) (Subtype.ext hx))

lemma ofFibreCond {W : C} (a : W ⟶ X) :
    (pullback.fst (a ≫ f) f ≫ a) ≫ f = pullback.snd (a ≫ f) f ≫ f := by
  rw [Category.assoc]; exact pullback.condition

/-- The section of `P` over `W ×_S X` attached, via the descent datum, to an element of the
fibre of `P` at a morphism `a : W ⟶ X`. -/
noncomputable def ofFibreSection {W : C} (a : W ⟶ X) (x : Fibre pX a) :
    Fibre pX (pullback.snd (a ≫ f) f) :=
  D.θ (ofFibreCond a) (Fibre.restrict pX (pullback.fst (a ≫ f) f) x)

lemma evOf_ofFibreSection {W : C} (a : W ⟶ X) (x : Fibre pX a) {Z : C} (c : Z ⟶ W)
    (d : Z ⟶ X) (h : c ≫ (a ≫ f) = d ≫ f) (h' : (c ≫ a) ≫ f = d ≫ f) :
    (evOf (ofFibreSection D a x) c d h).1 = (D.θ h' (Fibre.restrict pX c x)).1 := by
  have hl : pullback.lift c d h ≫ pullback.fst (a ≫ f) f = c := pullback.lift_fst _ _ _
  rw [evOf_val]
  refine Eq.trans (congrArg Subtype.val (D.θ_restrict (pullback.lift c d h) (ofFibreCond a)
    (Fibre.restrict pX (pullback.fst (a ≫ f) f) x))) ?_
  refine θ_congr D ?_ ?_ _ h' _ _ ?_
  · rw [← Category.assoc, hl]
  · exact pullback.lift_snd _ _ _
  · rw [Fibre.restrict_val, Fibre.restrict_val, Fibre.restrict_val, ← map_comp_apply,
      ← op_comp, hl]

lemma isDescentSection_ofFibreSection {W : C} (a : W ⟶ X) (x : Fibre pX a) :
    IsDescentSection D (ofFibreSection D a x) := by
  intro Z c d₁ d₂ h₁ h₂
  apply Subtype.ext
  have k₁ : (c ≫ a) ≫ f = d₁ ≫ f := by rw [Category.assoc]; exact h₁
  have k₂ : (c ≫ a) ≫ f = d₂ ≫ f := by rw [Category.assoc]; exact h₂
  have e₁ : evOf (ofFibreSection D a x) c d₁ h₁ = D.θ k₁ (Fibre.restrict pX c x) :=
    Subtype.ext (evOf_ofFibreSection D a x c d₁ h₁ k₁)
  have e₂ : evOf (ofFibreSection D a x) c d₂ h₂ = D.θ k₂ (Fibre.restrict pX c x) :=
    Subtype.ext (evOf_ofFibreSection D a x c d₂ h₂ k₂)
  rw [e₁, e₂]
  exact congrArg Subtype.val (D.θ_comp k₁ (h₁.symm.trans h₂) (Fibre.restrict pX c x))

/-- The section of the glued sheaf attached to an element of a fibre of `P`. -/
noncomputable def ofFibre {W : C} (a : W ⟶ X) (x : Fibre pX a) : GlueObj D W :=
  ⟨a ≫ f, ⟨ofFibreSection D a x, isDescentSection_ofFibreSection D a x⟩⟩

@[simp]
lemma ofFibre_fst {W : C} (a : W ⟶ X) (x : Fibre pX a) : (ofFibre D a x).1 = a ≫ f :=
  rfl

lemma ev_ofFibre {W : C} (a : W ⟶ X) (x : Fibre pX a)
    (h : 𝟙 W ≫ (ofFibre D a x).1 = a ≫ f) : (ev (ofFibre D a x) (𝟙 W) a h).1 = x.1 := by
  have h' : (𝟙 W ≫ a) ≫ f = a ≫ f := by rw [Category.id_comp]
  refine (evOf_ofFibreSection D a x (𝟙 W) a h h').trans ?_
  refine Eq.trans (θ_congr D (Category.id_comp a) rfl h' rfl _ x ?_) ?_
  · rw [Fibre.restrict_val, op_id, map_id_apply]
  · exact congrArg Subtype.val (D.θ_id x)

lemma ofFibre_ev {W : C} (a : W ⟶ X) (z : GlueObj D W) (hz : z.1 = a ≫ f)
    (h : 𝟙 W ≫ z.1 = a ≫ f) : ofFibre D a (ev z (𝟙 W) a h) = z := by
  refine glueObj_ext hz.symm ?_
  intro Z c d hh hh'
  have k : (c ≫ a) ≫ f = d ≫ f := by rw [Category.assoc]; exact hh
  have hca : c ≫ z.1 = (c ≫ a) ≫ f := by rw [hz, Category.assoc]
  have h₂ : (c ≫ 𝟙 W) ≫ z.1 = (c ≫ a) ≫ f := by rw [Category.comp_id]; exact hca
  refine (evOf_ofFibreSection D a (ev z (𝟙 W) a h) c d hh k).trans ?_
  refine Eq.trans (θ_congr D rfl rfl k k (Fibre.restrict pX c (ev z (𝟙 W) a h))
    (ev z c (c ≫ a) hca) ?_) ?_
  · exact (congrArg Subtype.val (ev_restrict z c (𝟙 W) a h h₂)).trans
      (ev_congr' z (Category.comp_id c) rfl h₂ hca)
  · exact congrArg Subtype.val (ev_descent z c (c ≫ a) d hca hh')

/-- **Effectivity of descent.**  The fibre of the glued sheaf at a morphism `a : W ⟶ X` of the
cover identifies with the fibre of `P` at `a`; equivalently, the base change of the glued sheaf
along `f` is `P`. -/
noncomputable def glueFibreEquiv {W : C} (a : W ⟶ X) :
    {z : GlueObj D W // z.1 = a ≫ f} ≃ Fibre pX a where
  toFun z := ev z.1 (𝟙 W) a (by rw [Category.id_comp]; exact z.2)
  invFun x := ⟨ofFibre D a x, rfl⟩
  left_inv z := Subtype.ext (ofFibre_ev D a z.1 z.2 _)
  right_inv x := Subtype.ext (ev_ofFibre D a x _)

/-- The identification of fibres is compatible with restriction along morphisms of `C`. -/
@[simp]
lemma base_glueSheafBase {W : C} (z : GlueObj D W) :
    base (glueSheafBase D) (z : (glueSheaf D).obj.obj (op W)) = z.1 :=
  rfl

/-- **Effective descent, sheaf form.**  The sections of the glued sheaf over `W` lying over
`a ≫ f` are in bijection with the fibre of `P` at `a : W ⟶ X`. -/
noncomputable def glueSheafFibreEquiv {W : C} (a : W ⟶ X) :
    {z : (glueSheaf D).obj.obj (op W) // base (glueSheafBase D) z = a ≫ f} ≃ Fibre pX a :=
  glueFibreEquiv D a

/-- The identification of fibres is compatible with restriction along morphisms of `C`. -/
lemma restrict_ev_of_base {V W : C} (u : V ⟶ W) (a : W ⟶ X) (z : GlueObj D W)
    (hz : z.1 = a ≫ f) (h : 𝟙 W ≫ z.1 = a ≫ f)
    (h' : 𝟙 V ≫ (glueMap u z).1 = (u ≫ a) ≫ f) :
    Fibre.restrict pX u (ev z (𝟙 W) a h) = ev (glueMap u z) (𝟙 V) (u ≫ a) h' := by
  apply Subtype.ext
  have h₃ : u ≫ z.1 = (u ≫ a) ≫ f := by rw [hz, Category.assoc]
  have h₂ : (u ≫ 𝟙 W) ≫ z.1 = (u ≫ a) ≫ f := by rw [Category.comp_id]; exact h₃
  have h₄ : (𝟙 V ≫ u) ≫ z.1 = (u ≫ a) ≫ f := by rw [Category.id_comp]; exact h₃
  refine (congrArg Subtype.val (ev_restrict z u (𝟙 W) a h h₂)).trans ?_
  refine (ev_congr' z (Category.comp_id u) rfl h₂ h₃).trans ?_
  refine Eq.trans ?_ (ev_glueMap u z (𝟙 V) (u ≫ a) h' h₄).symm
  exact ev_congr' z (Category.id_comp u).symm rfl h₃ h₄

end EffectiveDescent

section RelativePullback

open CategoryTheory.Limits

variable [HasPullbacks (Sheaf J (Type v))]

/-- The tautological section of the base change of `p : P ⟶ y S` along the base of a section
`x` of `P`. -/
noncomputable def tautLift (p : P ⟶ J.yoneda.obj S) {W : C} (x : P.obj.obj (op W))
    {g : W ⟶ S} (hx : base p x = g) :
    J.yoneda.obj W ⟶ pullback p (J.yoneda.map g) :=
  pullback.lift (J.yonedaEquiv.symm x) (𝟙 _) (by
    apply J.yonedaEquiv.injective
    rw [J.yonedaEquiv_comp, Equiv.apply_symm_apply, Category.id_comp,
      J.yonedaEquiv_yoneda_map]
    exact hx)

@[reassoc (attr := simp)]
lemma tautLift_fst (p : P ⟶ J.yoneda.obj S) {W : C} (x : P.obj.obj (op W)) {g : W ⟶ S}
    (hx : base p x = g) :
    tautLift p x hx ≫ pullback.fst p (J.yoneda.map g) = J.yonedaEquiv.symm x :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma tautLift_snd (p : P ⟶ J.yoneda.obj S) {W : C} (x : P.obj.obj (op W)) {g : W ⟶ S}
    (hx : base p x = g) :
    tautLift p x hx ≫ pullback.snd p (J.yoneda.map g) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- **Separatedness of morphisms over a base, fibre-product form.**  Two morphisms out of a
sheaf `P` over `S` agree as soon as they agree after base change to the members of a covering
sieve of `S`. -/
theorem hom_ext_of_cover (p : P ⟶ J.yoneda.obj S) {R : Sieve S} (hR : R ∈ J S) {φ ψ : P ⟶ Q}
    (h : ∀ ⦃X : C⦄ (g : X ⟶ S), R g →
      pullback.fst p (J.yoneda.map g) ≫ φ = pullback.fst p (J.yoneda.map g) ≫ ψ) :
    φ = ψ := by
  refine hom_ext_of_sieve p hR fun W x => ?_
  have e2 : J.yonedaEquiv (tautLift p x.1 (rfl : base p x.1 = base p x.1) ≫
        pullback.fst p (J.yoneda.map (base p x.1)) ≫ φ)
      = J.yonedaEquiv (tautLift p x.1 (rfl : base p x.1 = base p x.1) ≫
        pullback.fst p (J.yoneda.map (base p x.1)) ≫ ψ) := by
    rw [h (base p x.1) x.2]
  rwa [← Category.assoc, tautLift_fst, J.yonedaEquiv_comp, Equiv.apply_symm_apply,
    ← Category.assoc, tautLift_fst, J.yonedaEquiv_comp, Equiv.apply_symm_apply] at e2

/-- The base change along `g : X ⟶ S` of a morphism of sheaves over `S`. -/
noncomputable def relMap (p : P ⟶ J.yoneda.obj S) (q : Q ⟶ J.yoneda.obj S) (φ : P ⟶ Q)
    (hφ : φ ≫ q = p) {X : C} (g : X ⟶ S) :
    pullback p (J.yoneda.map g) ⟶ pullback q (J.yoneda.map g) :=
  pullback.lift (pullback.fst p (J.yoneda.map g) ≫ φ) (pullback.snd p (J.yoneda.map g))
    (by rw [Category.assoc, hφ]; exact pullback.condition)

@[reassoc (attr := simp)]
lemma relMap_fst (p : P ⟶ J.yoneda.obj S) (q : Q ⟶ J.yoneda.obj S) (φ : P ⟶ Q)
    (hφ : φ ≫ q = p) {X : C} (g : X ⟶ S) :
    relMap p q φ hφ g ≫ pullback.fst q (J.yoneda.map g) =
      pullback.fst p (J.yoneda.map g) ≫ φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma relMap_snd (p : P ⟶ J.yoneda.obj S) (q : Q ⟶ J.yoneda.obj S) (φ : P ⟶ Q)
    (hφ : φ ≫ q = p) {X : C} (g : X ⟶ S) :
    relMap p q φ hφ g ≫ pullback.snd q (J.yoneda.map g) = pullback.snd p (J.yoneda.map g) :=
  pullback.lift_snd _ _ _

omit [HasPullbacks (Sheaf J (Type v))] in
/-- A morphism of sheaves over `S` which is bijective on the sections whose base lies in a
covering sieve is an isomorphism. -/
theorem isIso_of_sections (p : P ⟶ J.yoneda.obj S) (q : Q ⟶ J.yoneda.obj S) {R : Sieve S}
    (hR : R ∈ J S) (φ : P ⟶ Q) (hφ : φ ≫ q = p)
    (h : ∀ (W : C) (y : SectionsOver q R W),
      ∃! x : P.obj.obj (op W), φ.hom.app (op W) x = y.1) : IsIso φ := by
  have hchoose : ∀ (W : C) (y : SectionsOver q R W),
      φ.hom.app (op W) (h W y).choose = y.1 := fun W y => (h W y).choose_spec.1
  have hunique : ∀ (W : C) (y : SectionsOver q R W) (x : P.obj.obj (op W)),
      φ.hom.app (op W) x = y.1 → x = (h W y).choose :=
    fun W y x hx => (h W y).choose_spec.2 x hx
  have hnat : ∀ {V W : C} (u : V ⟶ W) (y : SectionsOver q R W),
      P.obj.map u.op (h W y).choose = (h V (SectionsOver.res u y)).choose := by
    intro V W u y
    refine hunique V (SectionsOver.res u y) _ ?_
    rw [nat_apply, hchoose]
    rfl
  have hbase : ∀ (W : C) (x : P.obj.obj (op W)), base q (φ.hom.app (op W) x) = base p x := by
    intro W x
    rw [← base_comp φ q x, hφ]
  refine ⟨⟨(PartialHom.mk (fun {W} y => (h W y).choose) fun u y => hnat u y).glue hR, ?_, ?_⟩⟩
  · refine hom_ext_of_sieve p hR fun W x => ?_
    have hx : R (base q (φ.hom.app (op W) x.1)) := by rw [hbase]; exact x.2
    change ((PartialHom.mk _ _).glue hR).hom.app (op W) (φ.hom.app (op W) x.1) = x.1
    rw [PartialHom.glue_app _ hR (⟨φ.hom.app (op W) x.1, hx⟩ : SectionsOver q R W)]
    exact (hunique W ⟨φ.hom.app (op W) x.1, hx⟩ x.1 rfl).symm
  · refine hom_ext_of_sieve q hR fun W y => ?_
    change φ.hom.app (op W) (((PartialHom.mk _ _).glue hR).hom.app (op W) y.1) = y.1
    rw [PartialHom.glue_app _ hR y]
    exact hchoose W y

/-- **Descent of isomorphisms.**  A morphism of sheaves over `S` which becomes an isomorphism
after base change to every member of a covering sieve is an isomorphism. -/
theorem isIso_of_cover (p : P ⟶ J.yoneda.obj S) (q : Q ⟶ J.yoneda.obj S) (φ : P ⟶ Q)
    (hφ : φ ≫ q = p) {R : Sieve S} (hR : R ∈ J S)
    (h : ∀ ⦃X : C⦄ (g : X ⟶ S), R g → IsIso (relMap p q φ hφ g)) : IsIso φ := by
  refine isIso_of_sections p q hR φ hφ fun W y => ?_
  have hg : R (base q y.1) := y.2
  have _ := h (base q y.1) hg
  refine ⟨J.yonedaEquiv (tautLift q y.1 rfl ≫ inv (relMap p q φ hφ (base q y.1)) ≫
    pullback.fst p (J.yoneda.map (base q y.1))), ?_, ?_⟩
  · dsimp only
    rw [← J.yonedaEquiv_comp, Category.assoc, Category.assoc,
      ← relMap_fst p q φ hφ (base q y.1), IsIso.inv_hom_id_assoc, tautLift_fst,
      Equiv.apply_symm_apply]
  · intro x hx
    have hbx : base p x = base q y.1 := by rw [← hx, ← base_comp φ q x, hφ]
    have hlift : tautLift p x hbx ≫ relMap p q φ hφ (base q y.1) = tautLift q y.1 rfl := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, relMap_fst, ← Category.assoc, tautLift_fst, tautLift_fst,
          J.yonedaEquiv_symm_naturality_right, hx]
      · rw [Category.assoc, relMap_snd, tautLift_snd, tautLift_snd]
    rw [← hlift, Category.assoc, IsIso.hom_inv_id_assoc, tautLift_fst,
      Equiv.apply_symm_apply]

omit [HasPullbacks (Sheaf J (Type v))] in
lemma base_yonedaEquiv (p : P ⟶ J.yoneda.obj S) {W : C} (α : J.yoneda.obj W ⟶ P) :
    base p (J.yonedaEquiv α) = J.yonedaEquiv (α ≫ p) :=
  (J.yonedaEquiv_comp α p).symm

/-- The comparison morphism between the base change of `p` along `k ≫ g` and its base change
along `g`. -/
noncomputable def baseChangeMap (p : P ⟶ J.yoneda.obj S) {X Y : C} (g : X ⟶ S) (k : Y ⟶ X) :
    pullback p (J.yoneda.map (k ≫ g)) ⟶ pullback p (J.yoneda.map g) :=
  pullback.lift (pullback.fst p (J.yoneda.map (k ≫ g)))
    (pullback.snd p (J.yoneda.map (k ≫ g)) ≫ J.yoneda.map k)
    (by rw [pullback.condition, Category.assoc, ← CategoryTheory.Functor.map_comp])

@[reassoc (attr := simp)]
lemma baseChangeMap_fst (p : P ⟶ J.yoneda.obj S) {X Y : C} (g : X ⟶ S) (k : Y ⟶ X) :
    baseChangeMap p g k ≫ pullback.fst p (J.yoneda.map g) =
      pullback.fst p (J.yoneda.map (k ≫ g)) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeMap_snd (p : P ⟶ J.yoneda.obj S) {X Y : C} (g : X ⟶ S) (k : Y ⟶ X) :
    baseChangeMap p g k ≫ pullback.snd p (J.yoneda.map g) =
      pullback.snd p (J.yoneda.map (k ≫ g)) ≫ J.yoneda.map k :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma tautLift_baseChangeMap (p : P ⟶ J.yoneda.obj S) {V W : C} (u : V ⟶ W)
    (x : P.obj.obj (op W)) :
    tautLift p (P.obj.map u.op x) (base_map p u x) ≫ baseChangeMap p (base p x) u =
      J.yoneda.map u ≫ tautLift p x rfl := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, baseChangeMap_fst, tautLift_fst]
    exact (J.yonedaEquiv_symm_naturality_left u P x).symm
  · simp

/-- A compatible family of morphisms defined on the base changes of a sheaf `P` over `S` along
the members of a sieve `R`.  This is the literal fibre-product form of a descent datum for
arrows. -/
structure CoverHomFamily (p : P ⟶ J.yoneda.obj S) (G : Sheaf J (Type v)) (R : Sieve S) where
  /-- The morphism attached to a member of the sieve. -/
  app : ∀ {X : C} (g : X ⟶ S), R g → (pullback p (J.yoneda.map g) ⟶ G)
  /-- The morphisms of the family agree on overlaps. -/
  compat : ∀ {X Y : C} (g : X ⟶ S) (hg : R g) (k : Y ⟶ X),
    baseChangeMap p g k ≫ app g hg = app (k ≫ g) (R.downward_closed hg k)

namespace CoverHomFamily

variable {p : P ⟶ J.yoneda.obj S} {R : Sieve S} (Φ : CoverHomFamily p Q R)

lemma appLift_congr {W : C} (x : P.obj.obj (op W)) {g g' : W ⟶ S}
    (hg : base p x = g) (hg' : base p x = g') (h : R g) (h' : R g') :
    tautLift p x hg ≫ Φ.app g h = tautLift p x hg' ≫ Φ.app g' h' := by
  obtain rfl : g = g' := hg.symm.trans hg'
  rfl

/-- The elementary partial morphism attached to a compatible family of morphisms defined on the
base changes along a sieve. -/
noncomputable def toPartialHom : PartialHom p Q R where
  app x := J.yonedaEquiv (tautLift p x.1 rfl ≫ Φ.app (base p x.1) x.2)
  naturality := fun {V W} u x => by
    have hu : R (u ≫ base p x.1) := R.downward_closed x.2 u
    rw [J.yonedaEquiv_naturality]
    refine congrArg J.yonedaEquiv ?_
    refine Eq.trans ?_ (Φ.appLift_congr (P.obj.map u.op x.1) rfl (base_map p u x.1)
      (SectionsOver.res u x).2 hu).symm
    rw [← Φ.compat (base p x.1) x.2 u, tautLift_baseChangeMap_assoc]

lemma toPartialHom_app {W : C} (x : SectionsOver p R W) :
    Φ.toPartialHom.app x = J.yonedaEquiv (tautLift p x.1 rfl ≫ Φ.app (base p x.1) x.2) :=
  rfl

/-- **Descent of arrows, fibre-product form.**  The morphism glued from a compatible family of
morphisms defined on the base changes along a covering sieve. -/
noncomputable def glue (hR : R ∈ J S) : P ⟶ Q :=
  Φ.toPartialHom.glue hR

/-- The glued morphism restricts to the given morphism on each member of the cover. -/
theorem glue_spec (hR : R ∈ J S) {X : C} (g : X ⟶ S) (hg : R g) :
    pullback.fst p (J.yoneda.map g) ≫ Φ.glue hR = Φ.app g hg := by
  refine J.hom_ext_yoneda fun X' m => ?_
  obtain ⟨x, hx⟩ : ∃ x, J.yonedaEquiv (m ≫ pullback.fst p (J.yoneda.map g)) = x := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, J.yonedaEquiv (m ≫ pullback.snd p (J.yoneda.map g)) = k := ⟨_, rfl⟩
  have hms : m ≫ pullback.snd p (J.yoneda.map g) = J.yoneda.map k := by
    apply J.yonedaEquiv.injective
    rw [J.yonedaEquiv_yoneda_map]
    exact hk
  have hmf : m ≫ pullback.fst p (J.yoneda.map g) = J.yonedaEquiv.symm x := by
    rw [← hx, Equiv.symm_apply_apply]
  have hbase : base p x = k ≫ g := by
    rw [← hx, base_yonedaEquiv, Category.assoc, pullback.condition, ← Category.assoc, hms,
      ← CategoryTheory.Functor.map_comp, J.yonedaEquiv_yoneda_map]
  have hxR : R (base p x) := by rw [hbase]; exact R.downward_closed hg k
  have hm : tautLift p x hbase ≫ baseChangeMap p g k = m := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, baseChangeMap_fst, tautLift_fst]
      exact hmf.symm
    · rw [Category.assoc, baseChangeMap_snd, ← Category.assoc, tautLift_snd, Category.id_comp]
      exact hms.symm
  have step : (tautLift p x hbase ≫ baseChangeMap p g k) ≫
        (pullback.fst p (J.yoneda.map g) ≫ Φ.glue hR)
      = (tautLift p x hbase ≫ baseChangeMap p g k) ≫ Φ.app g hg := by
    simp only [Category.assoc]
    rw [Φ.compat g hg, baseChangeMap_fst_assoc, tautLift_fst_assoc,
      J.yonedaEquiv_symm_naturality_right, glue,
      PartialHom.glue_app _ hR (⟨x, hxR⟩ : SectionsOver p R X'), toPartialHom_app,
      Equiv.symm_apply_apply]
    exact Φ.appLift_congr x rfl hbase hxR (R.downward_closed hg k)
  calc m ≫ (pullback.fst p (J.yoneda.map g) ≫ Φ.glue hR)
      = (tautLift p x hbase ≫ baseChangeMap p g k) ≫
          (pullback.fst p (J.yoneda.map g) ≫ Φ.glue hR) := by rw [hm]
    _ = (tautLift p x hbase ≫ baseChangeMap p g k) ≫ Φ.app g hg := step
    _ = m ≫ Φ.app g hg := by rw [hm]

/-- **Descent of arrows, fibre-product form, uniqueness.**  A compatible family of morphisms
out of the base changes of `P` along the members of a covering sieve of `S` comes from a unique
morphism `P ⟶ Q`. -/
theorem exists_unique_glue (hR : R ∈ J S) :
    ∃! φ : P ⟶ Q, ∀ (X : C) (g : X ⟶ S) (hg : R g),
      pullback.fst p (J.yoneda.map g) ≫ φ = Φ.app g hg := by
  refine ⟨Φ.glue hR, fun X g hg => Φ.glue_spec hR g hg, fun ψ hψ => ?_⟩
  refine hom_ext_of_cover p hR fun X g hg => ?_
  rw [hψ X g hg, Φ.glue_spec hR g hg]

/-- If every member of the family lies over `S`, then so does the glued morphism. -/
theorem glue_comp (hR : R ∈ J S) (q : Q ⟶ J.yoneda.obj S)
    (hq : ∀ ⦃X : C⦄ (g : X ⟶ S) (hg : R g),
      Φ.app g hg ≫ q = pullback.fst p (J.yoneda.map g) ≫ p) :
    Φ.glue hR ≫ q = p := by
  refine hom_ext_of_cover p hR fun X g hg => ?_
  rw [← Category.assoc, Φ.glue_spec hR g hg, hq g hg]

end CoverHomFamily

end RelativePullback

end GromovWitten.SheafGluing

namespace GromovWitten.AlgebraicGeometry

open GromovWitten.SheafGluing _root_.AlgebraicGeometry

universe u

namespace FppfSheaf

variable {S : Scheme.{u}} {P Q : FppfSheaf.{u}}

/-- **Descent of arrows for fppf sheaves, separatedness, elementary form.**  A morphism of fppf
sheaves out of a sheaf `P` over `S` is determined by its values on the sections of `P` whose base
lies in a covering sieve of `S`. -/
theorem hom_ext_of_sections (p : P ⟶ fppfYoneda.obj S) {R : Sieve S}
    (hR : R ∈ Scheme.fppfTopology S) {φ ψ : P ⟶ Q}
    (h : ∀ (W : Scheme.{u}) (x : SectionsOver p R W),
      φ.hom.app (op W) x.1 = ψ.hom.app (op W) x.1) :
    φ = ψ :=
  hom_ext_of_sieve p hR h

/-- **Descent of arrows for fppf sheaves, separatedness.**  Two morphisms out of an fppf sheaf
`P` over `S` agree as soon as they agree after base change to the members of an fppf covering
sieve of `S`. -/
theorem hom_ext_of_cover (p : P ⟶ fppfYoneda.obj S) {R : Sieve S}
    (hR : R ∈ Scheme.fppfTopology S) {φ ψ : P ⟶ Q}
    (h : ∀ ⦃X : Scheme.{u}⦄ (g : X ⟶ S), R g →
      Limits.pullback.fst p (fppfYoneda.map g) ≫ φ =
        Limits.pullback.fst p (fppfYoneda.map g) ≫ ψ) :
    φ = ψ :=
  GromovWitten.SheafGluing.hom_ext_of_cover p hR h

/-- **Descent of isomorphisms for fppf sheaves.**  A morphism of fppf sheaves over `S` which
becomes an isomorphism after base change to the members of a covering sieve of `S` is an
isomorphism. -/
theorem isIso_of_cover (p : P ⟶ fppfYoneda.obj S) (q : Q ⟶ fppfYoneda.obj S) (φ : P ⟶ Q)
    (hφ : φ ≫ q = p) {R : Sieve S} (hR : R ∈ Scheme.fppfTopology S)
    (h : ∀ ⦃X : Scheme.{u}⦄ (g : X ⟶ S), R g → IsIso (relMap p q φ hφ g)) : IsIso φ :=
  GromovWitten.SheafGluing.isIso_of_cover p q φ hφ hR h

/-- **Descent of arrows for fppf sheaves.**  A morphism defined on the sections whose base lies
in an fppf covering sieve extends uniquely to a morphism of fppf sheaves. -/
theorem exists_unique_glue_hom {p : P ⟶ fppfYoneda.obj S} {R : Sieve S}
    (hR : R ∈ Scheme.fppfTopology S) (Φ : PartialHom p Q R) :
    ∃! φ : P ⟶ Q, ∀ (W : Scheme.{u}) (x : SectionsOver p R W),
      φ.hom.app (op W) x.1 = Φ.app x :=
  Φ.exists_unique_glue hR

/-- **Effective descent for fppf sheaves along a covering morphism.**  A descent datum for an
fppf sheaf `P` over `X` relative to `f : X ⟶ S` glues to an fppf sheaf over `S` whose fibres
along `f` are the fibres of `P`.  (The topology plays no role in the construction; it enters
through the uniqueness statement `exists_iso_over_of_partialIso`.) -/
theorem exists_glueSheaf {X : Scheme.{u}} (f : X ⟶ S) {P : FppfSheaf.{u}}
    (pX : P ⟶ fppfYoneda.obj X) (D : DescentDatum f pX) :
    ∃ (G : FppfSheaf.{u}) (π : G ⟶ fppfYoneda.obj S),
      ∀ (W : Scheme.{u}) (a : W ⟶ X),
        Nonempty ({z : G.obj.obj (op W) // base π z = a ≫ f} ≃ Fibre pX a) :=
  ⟨glueSheaf D, glueSheafBase D, fun _ a => ⟨glueSheafFibreEquiv D a⟩⟩

/-- **Uniqueness of the glued fppf sheaf.**  Two fppf sheaves over `S` whose restrictions to an
fppf covering sieve are compatibly isomorphic are isomorphic over `S`. -/
theorem exists_iso_over_of_partialIso {p : P ⟶ fppfYoneda.obj S} {q : Q ⟶ fppfYoneda.obj S}
    {R : Sieve S} (hR : R ∈ Scheme.fppfTopology S) (e : PartialIso p q R) :
    ∃ φ : P ≅ Q, φ.hom ≫ q = p ∧ φ.inv ≫ p = q ∧
      ∀ (W : Scheme.{u}) (x : SectionsOver p R W), φ.hom.hom.app (op W) x.1 = e.hom.app x :=
  e.exists_iso_over hR

end FppfSheaf

end GromovWitten.AlgebraicGeometry
