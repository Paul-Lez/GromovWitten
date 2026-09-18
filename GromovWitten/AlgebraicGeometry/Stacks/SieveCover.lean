/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.SheafGluing

/-!
# Descent along an fppf covering sieve

The effective descent statement proved in `Stacks/SheafGluing.lean` is indexed by a single
morphism `X ⟶ S`, and more generally any explicit gluing construction has to be indexed by a
`u`-small family: a compatible family indexed by a covering *sieve* is large (the sieve category
of `Scheme.{u}` has objects in `Type (u+1)`, so such a family does not live in `Type u`).

This file closes the gap between the two indexings for the fppf topology.

First, every fppf covering sieve of `S` contains a `u`-small jointly surjective family of flat
morphisms locally of finite presentation (indexed, concretely, by the points of `S`), and the
coproduct of such a family is a single flat, locally of finite presentation, surjective morphism
onto `S`.

Second, a descent datum indexed by a covering sieve `R` is *effective*.  The elementary form of
such a datum is a presheaf `t : T ⟶ yoneda.obj S` over `S` which satisfies the sheaf condition
for all families of sections whose base lies in `R` (`SieveGluing.IsSheafOver`); giving this is
the same as giving a sheaf `P_c` over `dom c` for every member `c` of `R` together with
compatible transition isomorphisms.  Out of such a datum and a `u`-small covering family
`g i : X i ⟶ S` contained in `R` we build the glued presheaf

`GlueObj W = Σ s : W ⟶ S, {ξ : ∀ i, T (W ×_S X i) // ξ lies over `S` and agrees on overlaps}`,

prove that it is a sheaf (`SieveGluing.gluePresheaf_isSheaf`), and prove that the canonical map
`ofFib` from the sections of `T` with base `c` to the sections of the glued sheaf with base `c`
is bijective for every member `c` of `R` (`SieveGluing.ofFib_bijective`).  This is exactly the
effectiveness of descent along `R`.

## Main declarations

* `GromovWitten.AlgebraicGeometry.exists_covering_family`: an fppf covering sieve contains a
  `u`-small covering family.
* `GromovWitten.AlgebraicGeometry.exists_covering_morphism`: the coproduct of such a family is a
  single fppf covering morphism `∐ X ⟶ S`, through which every member of the family factors.
  Note that this single morphism need *not* itself belong to the sieve: sieves are closed under
  precomposition, not under `Sigma.desc`.
* `GromovWitten.SieveGluing.IsSheafOver`: the elementary form of a descent datum indexed by a
  sieve.
* `GromovWitten.SieveGluing.gluePresheaf`, `glueBase`, `gluePresheaf_isSheaf`, `glueSheaf`: the
  glued sheaf over `S` and its structure morphism.
* `GromovWitten.SieveGluing.ofFib`, `toFib`, `ofFib_bijective`: the comparison with the given
  datum on the members of the sieve, and its bijectivity.
* `GromovWitten.AlgebraicGeometry.exists_glue_of_sieve`: the packaged statement for the fppf
  topology — every descent datum along an fppf covering sieve of `S` is effective.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace GromovWitten.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

/-- The fppf precoverage has pullbacks, since the category of schemes does. -/
instance : (Scheme.fppfPrecoverage.{u}).HasPullbacks :=
  inferInstanceAs (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)).HasPullbacks

/-- The fppf precoverage contains the isomorphisms. -/
instance : (Scheme.fppfPrecoverage.{u}).HasIsos where
  mem_coverings_of_isIso f := Scheme.Hom.singleton_mem_fppfPrecoverage f

/-- Membership in the fppf precoverage, unfolded to the underlying morphism property. -/
lemma mem_fppfPrecoverage_iff {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {g : ∀ i, X i ⟶ S} :
    Presieve.ofArrows X g ∈ Scheme.fppfPrecoverage S ↔
      (∀ x : S, ∃ i, x ∈ Set.range (g i)) ∧
        ∀ i, Flat (g i) ∧ LocallyOfFinitePresentation (g i) :=
  Scheme.ofArrows_mem_precoverage_iff (P := @Flat ⊓ @LocallyOfFinitePresentation)

/-- **Every fppf covering sieve contains a `u`-small covering family.**  The index type may be
taken to be the set of points of `S`. -/
theorem exists_covering_family {S : Scheme.{u}} {R : Sieve S}
    (hR : R ∈ Scheme.fppfTopology S) :
    ∃ (ι : Type u) (X : ι → Scheme.{u}) (g : ∀ i, X i ⟶ S),
      (∀ i, R.arrows (g i)) ∧ Presieve.ofArrows X g ∈ Scheme.fppfPrecoverage S := by
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hR
  obtain ⟨T, hT, hTR⟩ := hR
  obtain ⟨κ, Y, q, rfl⟩ := T.exists_eq_ofArrows
  rw [mem_fppfPrecoverage_iff] at hT
  obtain ⟨hsurj, hprop⟩ := hT
  choose k hk using hsurj
  refine ⟨↑S, fun x => Y (k x), fun x => q (k x), fun x => ?_, ?_⟩
  · apply hTR
    exact ⟨k x⟩
  · rw [mem_fppfPrecoverage_iff]
    exact ⟨fun x => ⟨x, hk x⟩, fun x => hprop (k x)⟩

/-- **Every fppf covering sieve contains a family whose coproduct is a single fppf covering
morphism.**  The morphism `∐ X ⟶ S` is flat, locally of finite presentation and surjective, and
every member `g i` of the family factors through it as `Sigma.ι X i ≫ f`.  Note that `f` itself
need not lie in the sieve. -/
theorem exists_covering_morphism {S : Scheme.{u}} {R : Sieve S}
    (hR : R ∈ Scheme.fppfTopology S) :
    ∃ (ι : Type u) (X : ι → Scheme.{u}) (g : ∀ i, X i ⟶ S) (f : (∐ X) ⟶ S),
      (∀ i, R.arrows (g i)) ∧ (∀ i, Sigma.ι X i ≫ f = g i) ∧
        Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f := by
  obtain ⟨ι, X, g, hgR, hmem⟩ := exists_covering_family hR
  rw [mem_fppfPrecoverage_iff] at hmem
  obtain ⟨hsurj, hprop⟩ := hmem
  refine ⟨ι, X, g, Sigma.desc g, hgR, fun i => Sigma.ι_desc _ _, ?_, ?_, ?_⟩
  · let _ := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
    exact IsZariskiLocalAtSource.sigmaDesc fun i => (hprop i).1
  · let _ := HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyOfFinitePresentation) (Q := RingHom.FinitePresentation)
    exact IsZariskiLocalAtSource.sigmaDesc fun i => (hprop i).2
  · refine Surjective.sigmaDesc_of_union_range_eq_univ ?_
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨i, hi⟩ := hsurj x
    exact Set.mem_iUnion.2 ⟨i, hi⟩

end GromovWitten.AlgebraicGeometry

namespace GromovWitten.SieveGluing

open GromovWitten.SheafGluing CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {S : C} {T : Cᵒᵖ ⥤ Type v}

/-- The base of a section of a presheaf equipped with a morphism to a representable presheaf. -/
def tbase (t : T ⟶ yoneda.obj S) {W : C} (x : T.obj (op W)) : W ⟶ S :=
  t.app (op W) x

@[simp]
lemma tbase_map (t : T ⟶ yoneda.obj S) {V W : C} (u : V ⟶ W) (x : T.obj (op W)) :
    tbase t (T.map u.op x) = u ≫ tbase t x :=
  nat_apply t u.op x

/-- A presheaf `T` over `S` is a *sheaf over the sieve `R`* if the sheaf condition holds for all
families of sections whose base lies in `R`.

This is the elementary form of a descent datum indexed by the sieve `R`: a family of sheaves
`P_c` over the members `c : W ⟶ S` of `R` with compatible transition isomorphisms is the same
datum as the presheaf `T` whose sections over `W` are the pairs of a member `c` of `R` and a
section of the fibre of `P_c`, together with this sheaf condition. -/
def IsSheafOver (J : GrothendieckTopology C) (t : T ⟶ yoneda.obj S) (R : Sieve S) : Prop :=
  ∀ ⦃W : C⦄ (c : W ⟶ S), R c → ∀ (K : Sieve W), K ∈ J W →
    ∀ (x : ∀ ⦃V : C⦄ (u : V ⟶ W), K u → T.obj (op V)),
      (∀ ⦃V : C⦄ (u : V ⟶ W) (hu : K u), tbase t (x u hu) = u ≫ c) →
      (∀ ⦃V' V : C⦄ (u : V ⟶ W) (hu : K u) (w : V' ⟶ V),
        T.map w.op (x u hu) = x (w ≫ u) (K.downward_closed hu w)) →
      ∃! e : T.obj (op W), tbase t e = c ∧
        ∀ ⦃V : C⦄ (u : V ⟶ W) (hu : K u), T.map u.op e = x u hu

/-- Separatedness for sections of `T` whose base lies in the sieve `R`. -/
theorem IsSheafOver.ext {t : T ⟶ yoneda.obj S} {R : Sieve S} (hT : IsSheafOver J t R)
    {W : C} {c : W ⟶ S} (hc : R c) {K : Sieve W} (hK : K ∈ J W) {e e' : T.obj (op W)}
    (he : tbase t e = c) (he' : tbase t e' = c)
    (h : ∀ ⦃V : C⦄ (u : V ⟶ W), K u → T.map u.op e = T.map u.op e') : e = e' := by
  obtain ⟨w₀, -, huniq⟩ := hT c hc K hK (fun _ u _ => T.map u.op e)
    (fun V u hu => by rw [tbase_map, he])
    (fun V' V u hu w => by rw [← map_comp_apply, ← op_comp])
  rw [huniq e ⟨he, fun _ _ _ => rfl⟩, huniq e' ⟨he', fun _ u hu => (h u hu).symm⟩]

section Glue

variable [HasPullbacks C] {ι : Type v} {X : ι → C}

/-- The raw data of a section of the glued presheaf over `W` with base `s`: a section of `T`
over each base change `W ×_S X i`. -/
noncomputable def GlueSection (g : ∀ i, X i ⟶ S) {W : C} (s : W ⟶ S) : Type v :=
  ∀ i, T.obj (op (pullback s (g i)))

variable {g : ∀ i, X i ⟶ S}

/-- Evaluation of the raw data at a test square. -/
noncomputable def evOf {W : C} {s : W ⟶ S} (ξ : GlueSection (T := T) g s) (i : ι) {Z : C}
    (c : Z ⟶ W)
    (d : Z ⟶ X i) (h : c ≫ s = d ≫ g i) : T.obj (op Z) :=
  T.map (pullback.lift c d h).op (ξ i)

lemma evOf_congr {W : C} {s : W ⟶ S} (ξ : GlueSection (T := T) g s) (i : ι) {Z : C}
    {c c' : Z ⟶ W} {d d' : Z ⟶ X i} (hc : c = c') (hd : d = d') (h : c ≫ s = d ≫ g i)
    (h' : c' ≫ s = d' ≫ g i) : evOf ξ i c d h = evOf ξ i c' d' h' := by
  subst hc; subst hd; rfl

lemma evOf_restrict {W : C} {s : W ⟶ S} (ξ : GlueSection (T := T) g s) (i : ι) {Z Z' : C}
    (w : Z' ⟶ Z) (c : Z ⟶ W) (d : Z ⟶ X i) (h : c ≫ s = d ≫ g i)
    (h' : (w ≫ c) ≫ s = (w ≫ d) ≫ g i) :
    T.map w.op (evOf ξ i c d h) = evOf ξ i (w ≫ c) (w ≫ d) h' := by
  have hl : pullback.lift (w ≫ c) (w ≫ d) h' = w ≫ pullback.lift c d h := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]
  rw [evOf, evOf, hl, op_comp, map_comp_apply]

lemma evOf_self {W : C} {s : W ⟶ S} (ξ : GlueSection (T := T) g s) (i : ι) :
    evOf ξ i (pullback.fst s (g i)) (pullback.snd s (g i)) pullback.condition = ξ i := by
  have hl : pullback.lift (pullback.fst s (g i)) (pullback.snd s (g i))
      pullback.condition = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_
    · simp only [pullback.lift_fst, Category.id_comp]
    · simp only [pullback.lift_snd, Category.id_comp]
  rw [evOf, hl, op_id, map_id_apply]

lemma evOf_of_hom {W : C} {s : W ⟶ S} (ξ : GlueSection (T := T) g s) (i : ι) {Z : C}
    (v : Z ⟶ pullback s (g i))
    (h : (v ≫ pullback.fst s (g i)) ≫ s = (v ≫ pullback.snd s (g i)) ≫ g i) :
    evOf ξ i (v ≫ pullback.fst s (g i)) (v ≫ pullback.snd s (g i)) h = T.map v.op (ξ i) := by
  rw [← evOf_restrict ξ i v _ _ pullback.condition h, evOf_self]

/-- The conditions cutting out the sections of the glued presheaf. -/
structure IsGlueSection (t : T ⟶ yoneda.obj S) (g : ∀ i, X i ⟶ S) {W : C} {s : W ⟶ S}
    (ξ : GlueSection (T := T) g s) : Prop where
  /-- Each component lies over the projection to `S`. -/
  base : ∀ i, tbase t (ξ i) = pullback.fst s (g i) ≫ s
  /-- The components agree on all test squares. -/
  descent : ∀ ⦃Z : C⦄ (c : Z ⟶ W) (i j : ι) (d₁ : Z ⟶ X i) (d₂ : Z ⟶ X j)
    (h₁ : c ≫ s = d₁ ≫ g i) (h₂ : c ≫ s = d₂ ≫ g j), evOf ξ i c d₁ h₁ = evOf ξ j c d₂ h₂

/-- The sections of the glued presheaf over `W`. -/
noncomputable def GlueObj (t : T ⟶ yoneda.obj S) (gg : ∀ i, X i ⟶ S) (W : C) : Type v :=
  Σ s : W ⟶ S, {ξ : GlueSection (T := T) gg s // IsGlueSection t gg ξ}

variable {t : T ⟶ yoneda.obj S}

/-- Evaluation of a section of the glued presheaf at a test square. -/
noncomputable def ev {W : C} (z : GlueObj t g W) (i : ι) {Z : C} (c : Z ⟶ W) (d : Z ⟶ X i)
    (h : c ≫ z.1 = d ≫ g i) : T.obj (op Z) :=
  evOf z.2.1 i c d h

lemma ev_congr' {W : C} (z : GlueObj t g W) (i : ι) {Z : C} {c c' : Z ⟶ W} {d d' : Z ⟶ X i}
    (hc : c = c') (hd : d = d') (h : c ≫ z.1 = d ≫ g i) (h' : c' ≫ z.1 = d' ≫ g i) :
    ev z i c d h = ev z i c' d' h' :=
  evOf_congr _ i hc hd h h'

lemma ev_congr {W : C} {z z' : GlueObj t g W} (hz : z = z') (i : ι) {Z : C} (c : Z ⟶ W)
    (d : Z ⟶ X i) (h : c ≫ z.1 = d ≫ g i) (h' : c ≫ z'.1 = d ≫ g i) :
    ev z i c d h = ev z' i c d h' := by
  subst hz; rfl

lemma ev_restrict {W : C} (z : GlueObj t g W) (i : ι) {Z Z' : C} (w : Z' ⟶ Z) (c : Z ⟶ W)
    (d : Z ⟶ X i) (h : c ≫ z.1 = d ≫ g i) (h' : (w ≫ c) ≫ z.1 = (w ≫ d) ≫ g i) :
    T.map w.op (ev z i c d h) = ev z i (w ≫ c) (w ≫ d) h' :=
  evOf_restrict _ i w c d h h'

lemma ev_descent {W : C} (z : GlueObj t g W) {Z : C} (c : Z ⟶ W) (i j : ι) (d₁ : Z ⟶ X i)
    (d₂ : Z ⟶ X j) (h₁ : c ≫ z.1 = d₁ ≫ g i) (h₂ : c ≫ z.1 = d₂ ≫ g j) :
    ev z i c d₁ h₁ = ev z j c d₂ h₂ :=
  z.2.2.descent c i j d₁ d₂ h₁ h₂

lemma ev_base {W : C} (z : GlueObj t g W) (i : ι) {Z : C} (c : Z ⟶ W) (d : Z ⟶ X i)
    (h : c ≫ z.1 = d ≫ g i) : tbase t (ev z i c d h) = c ≫ z.1 := by
  rw [ev, evOf, tbase_map, z.2.2.base i, ← Category.assoc, pullback.lift_fst]

lemma glueObj_ext {W : C} {z z' : GlueObj t g W} (h1 : z.1 = z'.1)
    (h2 : ∀ (i : ι) (Z : C) (c : Z ⟶ W) (d : Z ⟶ X i) (h : c ≫ z.1 = d ≫ g i)
      (h' : c ≫ z'.1 = d ≫ g i), ev z i c d h = ev z' i c d h') : z = z' := by
  obtain ⟨s, ξ⟩ := z
  obtain ⟨s', ξ'⟩ := z'
  have h1' : s = s' := h1
  subst h1'
  refine congrArg (Sigma.mk s) (Subtype.ext (funext fun i => ?_))
  have key := h2 i _ (pullback.fst s (g i)) (pullback.snd s (g i)) pullback.condition
    pullback.condition
  rwa [show ev ⟨s, ξ⟩ i (pullback.fst s (g i)) (pullback.snd s (g i)) pullback.condition
      = ξ.1 i from evOf_self ξ.1 i,
    show ev ⟨s, ξ'⟩ i (pullback.fst s (g i)) (pullback.snd s (g i)) pullback.condition
      = ξ'.1 i from evOf_self ξ'.1 i] at key

/-- The commutation relation needed to restrict a section of the glued presheaf. -/
lemma glueMapCond {V W : C} (u : V ⟶ W) (z : GlueObj t g W) (i : ι) :
    (pullback.fst (u ≫ z.1) (g i) ≫ u) ≫ z.1 = pullback.snd (u ≫ z.1) (g i) ≫ g i := by
  rw [Category.assoc]; exact pullback.condition

/-- The raw data of the restriction of a section of the glued presheaf. -/
noncomputable def glueSectionAux {V W : C} (u : V ⟶ W) (z : GlueObj t g W) :
    GlueSection (T := T) g (u ≫ z.1) :=
  fun i => ev z i (pullback.fst (u ≫ z.1) (g i) ≫ u) (pullback.snd (u ≫ z.1) (g i))
    (glueMapCond u z i)

lemma evOf_glueSectionAux {V W : C} (u : V ⟶ W) (z : GlueObj t g W) (i : ι) {Z : C}
    (c : Z ⟶ V) (d : Z ⟶ X i) (h : c ≫ (u ≫ z.1) = d ≫ g i)
    (h' : (c ≫ u) ≫ z.1 = d ≫ g i) :
    evOf (glueSectionAux u z) i c d h = ev z i (c ≫ u) d h' := by
  have hl : pullback.lift c d h ≫ pullback.lift (pullback.fst (u ≫ z.1) (g i) ≫ u)
      (pullback.snd (u ≫ z.1) (g i)) (glueMapCond u z i) = pullback.lift (c ≫ u) d h' := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, pullback.lift_snd]
  simp only [ev, evOf, glueSectionAux]
  rw [← map_comp_apply, ← op_comp, hl]

/-- The restriction map of the glued presheaf. -/
noncomputable def glueMap {V W : C} (u : V ⟶ W) (z : GlueObj t g W) : GlueObj t g V :=
  ⟨u ≫ z.1, ⟨glueSectionAux u z,
    { base := fun i => by
        rw [glueSectionAux, ev_base, Category.assoc]
      descent := fun {Z} c i j d₁ d₂ h₁ h₂ => by
        have k₁ : (c ≫ u) ≫ z.1 = d₁ ≫ g i := by rw [Category.assoc]; exact h₁
        have k₂ : (c ≫ u) ≫ z.1 = d₂ ≫ g j := by rw [Category.assoc]; exact h₂
        rw [evOf_glueSectionAux u z i c d₁ h₁ k₁, evOf_glueSectionAux u z j c d₂ h₂ k₂]
        exact ev_descent z (c ≫ u) i j d₁ d₂ k₁ k₂ }⟩⟩

@[simp]
lemma glueMap_fst {V W : C} (u : V ⟶ W) (z : GlueObj t g W) : (glueMap u z).1 = u ≫ z.1 :=
  rfl

lemma ev_glueMap {V W : C} (u : V ⟶ W) (z : GlueObj t g W) (i : ι) {Z : C} (c : Z ⟶ V)
    (d : Z ⟶ X i) (h : c ≫ (glueMap u z).1 = d ≫ g i) (h' : (c ≫ u) ≫ z.1 = d ≫ g i) :
    ev (glueMap u z) i c d h = ev z i (c ≫ u) d h' :=
  evOf_glueSectionAux u z i c d h h'

/-- The presheaf of types glued from a sieve-indexed descent datum along a covering family. -/
noncomputable def gluePresheaf (t : T ⟶ yoneda.obj S) (gg : ∀ i, X i ⟶ S) : Cᵒᵖ ⥤ Type v where
  obj W := GlueObj t gg W.unop
  map u := TypeCat.ofHom (glueMap u.unop)
  map_id W := by
    ext z
    refine glueObj_ext (by simp) fun i Z c d hh hh' => ?_
    exact (ev_glueMap _ z i c d hh (by simpa using hh')).trans
      (ev_congr' z i (Category.comp_id c) rfl _ hh')
  map_comp p q := by
    ext z
    refine glueObj_ext (by simp) fun i Z c d hh hh' => ?_
    have hb : c ≫ ((q.unop ≫ p.unop) ≫ z.1) = d ≫ gg i := hh
    have h1 : (c ≫ q.unop ≫ p.unop) ≫ z.1 = d ≫ gg i := by
      simpa only [Category.assoc] using hb
    have h2 : ((c ≫ q.unop) ≫ p.unop) ≫ z.1 = d ≫ gg i := by
      simpa only [Category.assoc] using hb
    have h4 : (c ≫ q.unop) ≫ p.unop ≫ z.1 = d ≫ gg i := by
      simpa only [Category.assoc] using hb
    refine (ev_glueMap _ z i c d hh h1).trans ?_
    refine (ev_congr' z i (Category.assoc c q.unop p.unop).symm rfl h1 h2).trans ?_
    refine (ev_glueMap p.unop z i (c ≫ q.unop) d h4 h2).symm.trans ?_
    exact (ev_glueMap q.unop (glueMap p.unop z) i c d hh' h4).symm

/-- The structure morphism from the glued presheaf to the presheaf represented by `S`. -/
def glueBase (t : T ⟶ yoneda.obj S) (gg : ∀ i, X i ⟶ S) : gluePresheaf t gg ⟶ yoneda.obj S where
  app _ := TypeCat.ofHom fun z => z.1
  naturality _ _ _ := by ext z; rfl

lemma tbase_evOf {W : C} {t : T ⟶ yoneda.obj S} {s : W ⟶ S} {ξ : GlueSection (T := T) g s}
    (hb : ∀ i, tbase t (ξ i) = pullback.fst s (g i) ≫ s) (i : ι) {Z : C} (c : Z ⟶ W)
    (d : Z ⟶ X i) (h : c ≫ s = d ≫ g i) : tbase t (evOf ξ i c d h) = c ≫ s := by
  rw [evOf, tbase_map, hb i, ← Category.assoc, pullback.lift_fst]

section SheafCondition

variable {t : T ⟶ yoneda.obj S}

lemma glueObj_fst_congr {V : C} {z z' : GlueObj t g V} (h : z = z') : z.1 = z'.1 := by rw [h]

variable {W : C} {K : Sieve W} (fam : Presieve.FamilyOfElements (gluePresheaf t g) K.arrows)

lemma fam_congr {V : C} {a b : V ⟶ W} (hab : a = b) (ha : K a) (hb : K b) :
    fam a ha = fam b hb := by
  subst hab; rfl

lemma ev_fam (hfam : fam.Compatible) {V Z : C} (u : V ⟶ W) (hu : K u) (w : Z ⟶ V) (i : ι)
    (d : Z ⟶ X i) (h : w ≫ (fam u hu).1 = d ≫ g i)
    (h' : 𝟙 Z ≫ (fam (w ≫ u) (K.downward_closed hu w)).1 = d ≫ g i) :
    ev (fam u hu) i w d h = ev (fam (w ≫ u) (K.downward_closed hu w)) i (𝟙 Z) d h' := by
  have e : fam (w ≫ u) (K.downward_closed hu w) = glueMap w (fam u hu) :=
    (Presieve.compatible_iff_sieveCompatible fam).1 hfam u w hu
  have h2 : 𝟙 Z ≫ (glueMap w (fam u hu)).1 = d ≫ g i := by rw [← e]; exact h'
  have h3 : (𝟙 Z ≫ w) ≫ (fam u hu).1 = d ≫ g i := by rw [Category.id_comp]; exact h
  refine Eq.trans ?_ (ev_congr e.symm i (𝟙 Z) d h2 h')
  refine Eq.trans ?_ (ev_glueMap w (fam u hu) i (𝟙 Z) d h2 h3).symm
  exact ev_congr' (fam u hu) i (Category.id_comp w).symm rfl h h3

variable (sW : W ⟶ S) (hsW : ∀ ⦃V : C⦄ (u : V ⟶ W) (hu : K u), u ≫ sW = (fam u hu).1)

include hsW in
lemma glueFamCond (i : ι) {Z : C} (w : Z ⟶ pullback sW (g i))
    (hw : K (w ≫ pullback.fst sW (g i))) :
    𝟙 Z ≫ (fam (w ≫ pullback.fst sW (g i)) hw).1 = (w ≫ pullback.snd sW (g i)) ≫ g i := by
  rw [Category.id_comp, ← hsW _ hw, Category.assoc, Category.assoc, pullback.condition]

/-- The family of sections of `T` attached to a compatible family of sections of the glued
presheaf. -/
noncomputable def glueFam (i : ι) ⦃Z : C⦄ (w : Z ⟶ pullback sW (g i))
    (hw : (K.pullback (pullback.fst sW (g i))).arrows w) : T.obj (op Z) :=
  ev (fam _ hw) i (𝟙 Z) (w ≫ pullback.snd sW (g i)) (glueFamCond fam sW hsW i w hw)

include hsW in
lemma tbase_glueFam (i : ι) {Z : C} (w : Z ⟶ pullback sW (g i))
    (hw : (K.pullback (pullback.fst sW (g i))).arrows w) :
    tbase t (glueFam fam sW hsW i w hw) = w ≫ pullback.fst sW (g i) ≫ sW := by
  refine Eq.trans (ev_base (fam _ hw) i (𝟙 Z) (w ≫ pullback.snd sW (g i))
    (glueFamCond fam sW hsW i w hw)) ?_
  rw [Category.id_comp, ← hsW _ hw, Category.assoc]

include hsW in
lemma glueFam_restrict (hfam : fam.Compatible) (i : ι) {Z Z' : C} (w : Z ⟶ pullback sW (g i))
    (hw : (K.pullback (pullback.fst sW (g i))).arrows w) (w' : Z' ⟶ Z) :
    T.map w'.op (glueFam fam sW hsW i w hw)
      = glueFam fam sW hsW i (w' ≫ w) ((K.pullback _).downward_closed hw w') := by
  have hu : K (w ≫ pullback.fst sW (g i)) := hw
  have hd2 : (w' ≫ 𝟙 Z) ≫ (fam (w ≫ pullback.fst sW (g i)) hu).1
      = (w' ≫ w ≫ pullback.snd sW (g i)) ≫ g i := by
    rw [Category.comp_id, ← hsW _ hu]
    simp only [Category.assoc]
    rw [pullback.condition]
  have hd : w' ≫ (fam (w ≫ pullback.fst sW (g i)) hu).1
      = ((w' ≫ w) ≫ pullback.snd sW (g i)) ≫ g i := by
    rw [← hsW _ hu]
    simp only [Category.assoc]
    rw [pullback.condition]
  have hd3 : 𝟙 Z' ≫ (fam (w' ≫ w ≫ pullback.fst sW (g i))
        (K.downward_closed hu w')).1 = ((w' ≫ w) ≫ pullback.snd sW (g i)) ≫ g i := by
    rw [Category.id_comp, ← hsW _ (K.downward_closed hu w')]
    simp only [Category.assoc]
    rw [pullback.condition]
  refine Eq.trans (ev_restrict (fam _ hu) i w' (𝟙 Z) (w ≫ pullback.snd sW (g i))
    (glueFamCond fam sW hsW i w hw) hd2) ?_
  refine Eq.trans (ev_congr' (fam _ hu) i (Category.comp_id w')
    (Category.assoc w' w (pullback.snd sW (g i))).symm hd2 hd) ?_
  refine Eq.trans (ev_fam fam hfam _ hu w' i _ hd hd3) ?_
  exact ev_congr (fam_congr fam (Category.assoc w' w (pullback.fst sW (g i))).symm _ _)
    i (𝟙 Z') _ hd3 _

end SheafCondition

section Sheaf

variable {t : T ⟶ yoneda.obj S} {R : Sieve S}

/-- **The presheaf glued from a sieve-indexed descent datum is a sheaf.**  The base component is
glued by subcanonicity of the topology, and the `i`-th component by the sheaf condition of `T`
over the sieve `R`, applied on the base change of the covering sieve. -/
theorem gluePresheaf_isSheaf [J.Subcanonical] (hT : IsSheafOver J t R) (hg : ∀ i, R (g i)) :
    Presieve.IsSheaf J (gluePresheaf t g) := by
  intro W K hK fam hfam
  obtain ⟨sW, hsW0, -⟩ := isSheafOfType (J.yoneda.obj S) K hK
    (fun _ u hu => (fam u hu).1)
    (fun _ _ _ p₁ p₂ _ _ h₁ h₂ hc => glueObj_fst_congr (hfam p₁ p₂ h₁ h₂ hc))
  have hsW : ∀ ⦃V : C⦄ (u : V ⟶ W) (hu : K u), u ≫ sW = (fam u hu).1 := fun _ u hu => hsW0 u hu
  have hRi : ∀ i, R (pullback.fst sW (g i) ≫ sW) := by
    intro i
    rw [pullback.condition]
    exact R.downward_closed (hg i) _
  have hex : ∀ i, ∃ e : T.obj (op (pullback sW (g i))),
      tbase t e = pullback.fst sW (g i) ≫ sW ∧
      ∀ ⦃Z : C⦄ (w : Z ⟶ pullback sW (g i))
        (hw : (K.pullback (pullback.fst sW (g i))).arrows w),
        T.map w.op e = glueFam fam sW hsW i w hw := fun i =>
    (hT (pullback.fst sW (g i) ≫ sW) (hRi i) (K.pullback (pullback.fst sW (g i)))
      (J.pullback_stable _ hK) (glueFam fam sW hsW i)
      (fun _ w hw => tbase_glueFam fam sW hsW i w hw)
      (fun _ _ w hw w' => glueFam_restrict fam sW hsW hfam i w hw w')).exists
  choose ξ hξb hξg using hex
  have key : ∀ ⦃Z : C⦄ (c : Z ⟶ W) (hc : K c) (i : ι) (d : Z ⟶ X i)
      (hd : c ≫ sW = d ≫ g i) (hd' : 𝟙 Z ≫ (fam c hc).1 = d ≫ g i),
      evOf ξ i c d hd = ev (fam c hc) i (𝟙 Z) d hd' := by
    intro Z c hc i d hd hd'
    have hlift : (K.pullback (pullback.fst sW (g i))).arrows (pullback.lift c d hd) := by
      have : K (pullback.lift c d hd ≫ pullback.fst sW (g i)) := by
        rw [pullback.lift_fst]; exact hc
      exact this
    refine (hξg i (pullback.lift c d hd) hlift).trans ?_
    refine Eq.trans (ev_congr (fam_congr fam (pullback.lift_fst c d hd) hlift hc) i (𝟙 Z)
      _ _ ?_) ?_
    · rw [Category.id_comp, ← hsW _ hc]
      simp only [pullback.lift_snd]
      exact hd
    · exact ev_congr' (fam c hc) i rfl (pullback.lift_snd c d hd) _ hd'
  have hgs : IsGlueSection t g ξ :=
    { base := hξb
      descent := by
        intro Z c i j d₁ d₂ h₁ h₂
        have hRc : R (c ≫ sW) := by rw [h₁]; exact R.downward_closed (hg i) _
        refine hT.ext hRc (J.pullback_stable c hK) (tbase_evOf hξb i c d₁ h₁)
          (tbase_evOf hξb j c d₂ h₂) ?_
        intro Z' w hw
        have hw' : K (w ≫ c) := hw
        have k₁ : (w ≫ c) ≫ sW = (w ≫ d₁) ≫ g i := by
          simp only [Category.assoc]; rw [h₁]
        have k₂ : (w ≫ c) ≫ sW = (w ≫ d₂) ≫ g j := by
          simp only [Category.assoc]; rw [h₂]
        have f₁ : 𝟙 Z' ≫ (fam (w ≫ c) hw').1 = (w ≫ d₁) ≫ g i := by
          rw [Category.id_comp, ← hsW _ hw']; exact k₁
        have f₂ : 𝟙 Z' ≫ (fam (w ≫ c) hw').1 = (w ≫ d₂) ≫ g j := by
          rw [Category.id_comp, ← hsW _ hw']; exact k₂
        rw [evOf_restrict ξ i w c d₁ h₁ k₁, evOf_restrict ξ j w c d₂ h₂ k₂,
          key (w ≫ c) hw' i (w ≫ d₁) k₁ f₁, key (w ≫ c) hw' j (w ≫ d₂) k₂ f₂]
        exact ev_descent (fam (w ≫ c) hw') (𝟙 Z') i j (w ≫ d₁) (w ≫ d₂) f₁ f₂ }
  refine ⟨⟨sW, ⟨ξ, hgs⟩⟩, ?_, ?_⟩
  · intro V u hu
    refine glueObj_ext (hsW u hu) fun i Z c d hh hh' => ?_
    have h1 : (c ≫ u) ≫ sW = d ≫ g i := by rw [Category.assoc]; exact hh
    have hcu : K (c ≫ u) := K.downward_closed hu c
    have h2 : 𝟙 Z ≫ (fam (c ≫ u) hcu).1 = d ≫ g i := by
      rw [Category.id_comp, ← hsW _ hcu]; exact h1
    refine (ev_glueMap u _ i c d hh h1).trans ?_
    refine (key (c ≫ u) hcu i d h1 h2).trans ?_
    exact (ev_fam fam hfam u hu c i d hh' h2).symm
  · intro z hz
    have hbase : z.1 = sW := by
      refine (isSheafOfType (J.yoneda.obj S) K hK).isSeparatedFor.ext ?_
      intro V u hu
      exact (glueObj_fst_congr (hz u hu)).trans (hsW u hu).symm
    refine glueObj_ext hbase fun i Z c d hh hh' => ?_
    have hRc : R (c ≫ z.1) := by rw [hh]; exact R.downward_closed (hg i) _
    refine hT.ext hRc (J.pullback_stable c hK) (ev_base z i c d hh)
      ((tbase_evOf hξb i c d hh').trans (by rw [hbase])) ?_
    intro Z' w hw
    have hw' : K (w ≫ c) := hw
    have k1 : (w ≫ c) ≫ z.1 = (w ≫ d) ≫ g i := by simp only [Category.assoc]; rw [hh]
    have k2 : (w ≫ c) ≫ sW = (w ≫ d) ≫ g i := by simp only [Category.assoc]; rw [hh']
    have f1 : 𝟙 Z' ≫ (fam (w ≫ c) hw').1 = (w ≫ d) ≫ g i := by
      rw [Category.id_comp, ← hsW _ hw']; exact k2
    have hg1 : 𝟙 Z' ≫ (glueMap (w ≫ c) z).1 = (w ≫ d) ≫ g i := by
      rw [Category.id_comp]; exact k1
    have hg2 : (𝟙 Z' ≫ (w ≫ c)) ≫ z.1 = (w ≫ d) ≫ g i := by
      rw [Category.id_comp]; exact k1
    refine Eq.trans (ev_restrict z i w c d hh k1) ?_
    refine Eq.trans ?_ (ev_restrict (⟨sW, ⟨ξ, hgs⟩⟩ : GlueObj t g W) i w c d hh' k2).symm
    refine Eq.trans ?_ (key (w ≫ c) hw' i (w ≫ d) k2 f1).symm
    refine Eq.trans ?_ (ev_congr (hz (w ≫ c) hw') i (𝟙 Z') (w ≫ d) hg1 f1)
    refine Eq.trans ?_ (ev_glueMap (w ≫ c) z i (𝟙 Z') (w ≫ d) hg1 hg2).symm
    exact ev_congr' z i (Category.id_comp (w ≫ c)).symm rfl k1 hg2

/-- The sheaf glued from a sieve-indexed descent datum along a covering family. -/
noncomputable def glueSheaf [J.Subcanonical] (hT : IsSheafOver J t R) (hg : ∀ i, R (g i)) :
    Sheaf J (Type v) :=
  ⟨gluePresheaf t g, (isSheaf_iff_isSheaf_of_type J _).2 (gluePresheaf_isSheaf hT hg)⟩

end Sheaf

section Fib

variable {t : T ⟶ yoneda.obj S} {R : Sieve S}

lemma ev_eq_map {W : C} (z : GlueObj t g W) (i j : ι) {V : C}
    (v : V ⟶ pullback z.1 (g i)) (u : V ⟶ W) (d : V ⟶ X j) (h : u ≫ z.1 = d ≫ g j)
    (hu : v ≫ pullback.fst z.1 (g i) = u) : ev z j u d h = T.map v.op (z.2.1 i) := by
  have h2 : (v ≫ pullback.fst z.1 (g i)) ≫ z.1 = (v ≫ pullback.snd z.1 (g i)) ≫ g i := by
    simp only [Category.assoc]; rw [pullback.condition]
  have h3 : u ≫ z.1 = (v ≫ pullback.snd z.1 (g i)) ≫ g i := by rw [← hu]; exact h2
  refine (ev_descent z u j i d (v ≫ pullback.snd z.1 (g i)) h h3).trans ?_
  refine (ev_congr' z i hu.symm rfl h3 h2).trans ?_
  exact evOf_of_hom z.2.1 i v h2

lemma evOf_const {W : C} {c : W ⟶ S} (x : T.obj (op W)) (k : ι) {Z : C} (c' : Z ⟶ W)
    (dd : Z ⟶ X k) (hh : c' ≫ c = dd ≫ g k) :
    evOf (T := T) (g := g) (fun i => T.map (pullback.fst c (g i)).op x) k c' dd hh
      = T.map c'.op x :=
  (map_comp_apply T (pullback.fst c (g k)).op (pullback.lift c' dd hh).op x).symm.trans
    (by rw [← op_comp, pullback.lift_fst])

/-- The section of the glued presheaf attached to a section of `T` over `W`. -/
noncomputable def ofFib {W : C} {c : W ⟶ S} (x : T.obj (op W)) (hx : tbase t x = c) :
    GlueObj t g W :=
  ⟨c, ⟨fun i => T.map (pullback.fst c (g i)).op x,
    { base := fun i => by rw [tbase_map, hx]
      descent := fun {Z} c' i j d₁ d₂ h₁ h₂ =>
        (evOf_const x i c' d₁ h₁).trans (evOf_const x j c' d₂ h₂).symm }⟩⟩

@[simp]
lemma ofFib_fst {W : C} {c : W ⟶ S} (x : T.obj (op W)) (hx : tbase t x = c) :
    (ofFib (g := g) x hx).1 = c :=
  rfl

lemma ofFib_congr {W : C} {c : W ⟶ S} (x : T.obj (op W)) (hx : tbase t x = c) :
    ofFib (t := t) (g := g) x hx = ofFib (t := t) (g := g) x rfl := by
  subst hx; rfl

lemma ev_ofFib {W : C} {c : W ⟶ S} (x : T.obj (op W)) (hx : tbase t x = c) (i : ι) {Z : C}
    (c' : Z ⟶ W) (d : Z ⟶ X i) (h : c' ≫ (ofFib (g := g) x hx).1 = d ≫ g i) :
    ev (ofFib (g := g) x hx) i c' d h = T.map c'.op x :=
  evOf_const x i c' d h

variable (hcov : ∀ ⦃W : C⦄ (c : W ⟶ S), Sieve.ofArrows (fun i => pullback c (g i))
  (fun i => pullback.fst c (g i)) ∈ J W)

include hcov in
/-- **Effectivity of descent, fibre form.**  A section of the glued presheaf over `W` whose base
lies in the sieve `R` comes from a unique section of `T`. -/
theorem exists_unique_toFib (hT : IsSheafOver J t R) {W : C} (z : GlueObj t g W) (hc : R z.1) :
    ∃! e : T.obj (op W), tbase t e = z.1 ∧
      ∀ i : ι, T.map (pullback.fst z.1 (g i)).op e = z.2.1 i := by
  have hfac : ∀ ⦃V : C⦄ (u : V ⟶ W),
      (Sieve.ofArrows (fun i => pullback z.1 (g i))
        (fun i => pullback.fst z.1 (g i))).arrows u →
      ∃ (i : ι) (v : V ⟶ pullback z.1 (g i)), v ≫ pullback.fst z.1 (g i) = u := by
    intro V u hu
    obtain ⟨Y, a, b, hb, rfl⟩ := hu
    obtain ⟨i⟩ := hb
    exact ⟨i, a, rfl⟩
  choose fi fv fh using hfac
  have hfc : ∀ ⦃V : C⦄ (u : V ⟶ W) (hu : (Sieve.ofArrows (fun i => pullback z.1 (g i))
        (fun i => pullback.fst z.1 (g i))).arrows u),
      u ≫ z.1 = (fv u hu ≫ pullback.snd z.1 (g (fi u hu))) ≫ g (fi u hu) := by
    intro V u hu
    have h2 : (fv u hu ≫ pullback.fst z.1 (g (fi u hu))) ≫ z.1
        = (fv u hu ≫ pullback.snd z.1 (g (fi u hu))) ≫ g (fi u hu) := by
      simp only [Category.assoc]; rw [pullback.condition]
    rw [fh u hu] at h2
    exact h2
  obtain ⟨e, ⟨he1, he2⟩, heu⟩ := hT z.1 hc _ (hcov z.1)
    (fun _ u hu => ev z (fi u hu) u (fv u hu ≫ pullback.snd z.1 (g (fi u hu))) (hfc u hu))
    (fun _ u hu => ev_base z (fi u hu) u _ (hfc u hu))
    (fun V' V u hu w => by
      have k : (w ≫ u) ≫ z.1
          = (w ≫ fv u hu ≫ pullback.snd z.1 (g (fi u hu))) ≫ g (fi u hu) := by
        simp only [Category.assoc]
        exact congrArg (fun m => w ≫ m) (by simpa only [Category.assoc] using hfc u hu)
      refine (ev_restrict z (fi u hu) w u _ (hfc u hu) k).trans ?_
      exact ev_descent z (w ≫ u) (fi u hu) (fi (w ≫ u) _) _ _ k
        (hfc (w ≫ u) ((Sieve.ofArrows _ _).downward_closed hu w)))
  refine ⟨e, ⟨he1, fun i => ?_⟩, ?_⟩
  · have hmem : (Sieve.ofArrows (fun i => pullback z.1 (g i))
        (fun i => pullback.fst z.1 (g i))).arrows (pullback.fst z.1 (g i)) :=
      Sieve.ofArrows_mk _ _ i
    refine (he2 _ hmem).trans ?_
    refine (ev_descent z (pullback.fst z.1 (g i)) (fi _ hmem) i _ (pullback.snd z.1 (g i))
      (hfc _ hmem) pullback.condition).trans ?_
    exact evOf_self z.2.1 i
  · rintro e' ⟨he1', he2'⟩
    refine heu e' ⟨he1', fun V u hu => ?_⟩
    refine Eq.trans ?_ (ev_eq_map z (fi u hu) (fi u hu) (fv u hu) u _ (hfc u hu)
      (fh u hu)).symm
    rw [← he2' (fi u hu), ← map_comp_apply, ← op_comp, fh u hu]

lemma map_of_glue_char {W : C} (z : GlueObj t g W) (e : T.obj (op W))
    (he : ∀ i, T.map (pullback.fst z.1 (g i)).op e = z.2.1 i) {V : C} (u : V ⟶ W) (i : ι)
    (d : V ⟶ X i) (h : u ≫ z.1 = d ≫ g i) : T.map u.op e = ev z i u d h := by
  have hu : T.map u.op e = T.map (pullback.lift u d h ≫ pullback.fst z.1 (g i)).op e := by
    rw [pullback.lift_fst]
  rw [hu, op_comp, map_comp_apply, he i]
  rfl

/-- The section of `T` glued from a section of the glued presheaf whose base lies in `R`. -/
noncomputable def toFib (hT : IsSheafOver J t R) {W : C} (z : GlueObj t g W) (hc : R z.1) :
    T.obj (op W) :=
  (exists_unique_toFib hcov hT z hc).exists.choose

lemma tbase_toFib (hT : IsSheafOver J t R) {W : C} (z : GlueObj t g W) (hc : R z.1) :
    tbase t (toFib hcov hT z hc) = z.1 :=
  (exists_unique_toFib hcov hT z hc).exists.choose_spec.1

lemma map_fst_toFib (hT : IsSheafOver J t R) {W : C} (z : GlueObj t g W) (hc : R z.1) (i : ι) :
    T.map (pullback.fst z.1 (g i)).op (toFib hcov hT z hc) = z.2.1 i :=
  (exists_unique_toFib hcov hT z hc).exists.choose_spec.2 i

lemma toFib_congr (hT : IsSheafOver J t R) {W : C} {z z' : GlueObj t g W} (h : z = z')
    (hc : R z.1) (hc' : R z'.1) : toFib hcov hT z hc = toFib hcov hT z' hc' := by
  subst h; rfl

lemma ofFib_toFib (hT : IsSheafOver J t R) {W : C} (z : GlueObj t g W) (hc : R z.1) :
    ofFib (g := g) (toFib hcov hT z hc) (tbase_toFib hcov hT z hc) = z := by
  refine glueObj_ext rfl fun i Z c' d h h' => ?_
  refine (ev_ofFib _ _ i c' d h).trans ?_
  exact map_of_glue_char z _ (map_fst_toFib hcov hT z hc) c' i d h'

lemma toFib_ofFib (hT : IsSheafOver J t R) {W : C} {c : W ⟶ S} (x : T.obj (op W))
    (hx : tbase t x = c) (hc : R (ofFib (g := g) x hx).1) :
    toFib hcov hT (ofFib (g := g) x hx) hc = x :=
  (exists_unique_toFib hcov hT (ofFib x hx) hc).unique
    ⟨tbase_toFib hcov hT _ hc, map_fst_toFib hcov hT _ hc⟩ ⟨hx, fun _ => rfl⟩

include hcov in
/-- **Effectivity of descent along a covering sieve.**  For every member `c` of the sieve `R`,
the assignment `x ↦ ofFib x` is a bijection from the sections of `T` over `W` with base `c` onto
the sections of the glued sheaf with base `c`. -/
theorem ofFib_bijective (hT : IsSheafOver J t R) {W : C} (c : W ⟶ S) (hc : R c) :
    Function.Bijective (fun x : {x : T.obj (op W) // tbase t x = c} =>
      (⟨ofFib (t := t) (g := g) x.1 rfl, x.2⟩ : {z : GlueObj t g W // z.1 = c})) := by
  constructor
  · intro x y hxy
    have e : ofFib (t := t) (g := g) x.1 rfl = ofFib (t := t) (g := g) y.1 rfl :=
      congrArg Subtype.val hxy
    have hcx : R (ofFib (t := t) (g := g) x.1 rfl).1 := by
      rw [ofFib_fst, x.2]; exact hc
    have hcy : R (ofFib (t := t) (g := g) y.1 rfl).1 := by
      rw [ofFib_fst, y.2]; exact hc
    refine Subtype.ext ?_
    rw [← toFib_ofFib hcov hT x.1 rfl hcx, ← toFib_ofFib hcov hT y.1 rfl hcy]
    exact toFib_congr hcov hT e hcx hcy
  · rintro ⟨z, hz⟩
    have hcz : R z.1 := by rw [hz]; exact hc
    refine ⟨⟨toFib hcov hT z hcz, (tbase_toFib hcov hT z hcz).trans hz⟩, Subtype.ext ?_⟩
    exact (ofFib_congr _ (tbase_toFib hcov hT z hcz)).symm.trans (ofFib_toFib hcov hT z hcz)

lemma ofFib_map {V W : C} (u : V ⟶ W) (x : T.obj (op W)) :
    ofFib (t := t) (g := g) (T.map u.op x) rfl
      = glueMap u (ofFib (t := t) (g := g) x rfl) := by
  refine glueObj_ext (tbase_map t u x) fun i Z c' d h h' => ?_
  refine (ev_ofFib _ _ i c' d h).trans ?_
  have h0 : c' ≫ (u ≫ tbase t x) = d ≫ g i := h'
  have h'' : (c' ≫ u) ≫ tbase t x = d ≫ g i := by rw [Category.assoc]; exact h0
  refine Eq.trans ?_ (ev_glueMap u (ofFib (t := t) (g := g) x rfl) i c' d h' h'').symm
  refine Eq.trans ?_ (ev_ofFib (t := t) x rfl i (c' ≫ u) d h'').symm
  rw [← map_comp_apply, ← op_comp]

end Fib

end Glue

end GromovWitten.SieveGluing


namespace GromovWitten.AlgebraicGeometry

open GromovWitten.SieveGluing GromovWitten.SheafGluing
open _root_.AlgebraicGeometry CategoryTheory.Limits

universe u

/-- The base change of a covering family of the fppf precoverage generates an fppf covering
sieve. -/
lemma sieve_ofArrows_pullback_mem {S : Scheme.{u}} {ι : Type u} {X : ι → Scheme.{u}}
    {g : ∀ i, X i ⟶ S} (hmem : Presieve.ofArrows X g ∈ Scheme.fppfPrecoverage S)
    {W : Scheme.{u}} (c : W ⟶ S) :
    Sieve.ofArrows (fun i => pullback c (g i)) (fun i => pullback.fst c (g i)) ∈
      Scheme.fppfTopology W := by
  refine Scheme.fppfTopology.superset_covering ?_
    (Scheme.fppfTopology.pullback_stable c (Precoverage.generate_mem_toGrothendieck hmem))
  rintro V u ⟨Y, a, b, ⟨i⟩, hab⟩
  exact ⟨pullback c (g i), pullback.lift u a hab.symm, pullback.fst c (g i),
    ⟨i⟩, pullback.lift_fst _ _ _⟩

/-- **Effective descent for fppf sheaves along a covering sieve.**

Let `t : T ⟶ yoneda.obj S` be a presheaf of types over `S` which satisfies the sheaf condition
for all families of sections whose base lies in an fppf covering sieve `R` of `S`
(`SieveGluing.IsSheafOver`; this is the elementary form of a descent datum indexed by `R`, see
the docstring of `IsSheafOver`).  Then there is an fppf sheaf `G` over `S` and a morphism
`Φ : T ⟶ G` over `S` which is bijective on the sections whose base lies in `R`.  In other words,
the descent datum is effective: `G` restricts to the given datum on every member of the sieve. -/
theorem exists_glue_of_sieve {S : Scheme.{u}} {T : Scheme.{u}ᵒᵖ ⥤ Type u}
    (t : T ⟶ yoneda.obj S) {R : Sieve S} (hR : R ∈ Scheme.fppfTopology S)
    (hT : IsSheafOver Scheme.fppfTopology t R) :
    ∃ (G : FppfSheaf.{u}) (π : G ⟶ fppfYoneda.obj S) (Φ : T ⟶ G.obj),
      (∀ (W : Scheme.{u}) (x : T.obj (op W)), base π (Φ.app (op W) x) = tbase t x) ∧
      ∀ (W : Scheme.{u}) (c : W ⟶ S), R c →
        (∀ x y : T.obj (op W), tbase t x = c → tbase t y = c →
            Φ.app (op W) x = Φ.app (op W) y → x = y) ∧
          ∀ z : G.obj.obj (op W), base π z = c →
            ∃ x : T.obj (op W), tbase t x = c ∧ Φ.app (op W) x = z := by
  obtain ⟨ι, X, g, hgR, hmem⟩ := exists_covering_family hR
  have hcov : ∀ ⦃W : Scheme.{u}⦄ (c : W ⟶ S),
      Sieve.ofArrows (fun i => pullback c (g i)) (fun i => pullback.fst c (g i)) ∈
        Scheme.fppfTopology W := fun _ c => sieve_ofArrows_pullback_mem hmem c
  refine ⟨glueSheaf hT hgR, ObjectProperty.homMk (glueBase t g),
    { app := fun _ => TypeCat.ofHom fun x => ofFib (t := t) (g := g) x rfl
      naturality := fun _ _ u => by ext x; exact ofFib_map u.unop x }, fun W x => rfl, ?_⟩
  intro W c hc
  obtain ⟨hinj, hsurj⟩ := ofFib_bijective hcov hT c hc
  refine ⟨fun x y hx hy hxy => ?_, fun z hz => ?_⟩
  · exact congrArg Subtype.val
      (hinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext hxy))
  · obtain ⟨x, hx⟩ := hsurj ⟨z, hz⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

end GromovWitten.AlgebraicGeometry
