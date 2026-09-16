/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableMaps.GluingData

/-!
# Constant marked maps

A section of the target over the base turns any marked source diagram into a constant map.
This construction is scheme-theoretic and feeds directly into the geometric stability layer.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap

universe u v w

variable {V S : Scheme.{u}} {q : V ⟶ S} {I : Type v} {J : Type w}

/-- Replace the target map by the constant family selected by a section `p : S ⟶ V`. -/
def constantAt (F : MarkedMap q I) (p : S ⟶ V) (hp : p ≫ q = 𝟙 S) : MarkedMap q I where
  source := F.source
  toBase := F.toBase
  marking := F.marking
  marking_toBase := F.marking_toBase
  map := F.toBase ≫ p
  map_toBase := by rw [Category.assoc, hp, Category.comp_id]

@[simp]
theorem constantAt_source (F : MarkedMap q I) (p : S ⟶ V) (hp : p ≫ q = 𝟙 S) :
    (F.constantAt p hp).source = F.source := rfl

@[simp]
theorem constantAt_toBase (F : MarkedMap q I) (p : S ⟶ V) (hp : p ≫ q = 𝟙 S) :
    (F.constantAt p hp).toBase = F.toBase := rfl

@[simp]
theorem constantAt_marking (F : MarkedMap q I) (p : S ⟶ V) (hp : p ≫ q = 𝟙 S)
    (i : I) : (F.constantAt p hp).marking i = F.marking i := rfl

@[simp]
theorem constantAt_map (F : MarkedMap q I) (p : S ⟶ V) (hp : p ≫ q = 𝟙 S) :
    (F.constantAt p hp).map = F.toBase ≫ p := rfl

/-- Every evaluation of a constant marked map is the chosen target section. -/
@[simp]
theorem evaluation_constantAt (F : MarkedMap q I) (p : S ⟶ V) (hp : p ≫ q = 𝟙 S)
    (i : I) : (F.constantAt p hp).evaluation i = p := by
  change F.marking i ≫ (F.toBase ≫ p) = p
  rw [← Category.assoc, F.marking_toBase, Category.id_comp]

/-- Making a map constant commutes strictly with restriction of its marking set. -/
@[simp]
theorem constantAt_restrictMarkings (F : MarkedMap q I) (p : S ⟶ V)
    (hp : p ≫ q = 𝟙 S) (ρ : J → I) :
    (F.constantAt p hp).restrictMarkings ρ =
      (F.restrictMarkings ρ).constantAt p hp := rfl

/-- Making a map constant commutes strictly with reindexing its markings. -/
@[simp]
theorem constantAt_reindex (F : MarkedMap q I) (p : S ⟶ V)
    (hp : p ≫ q = 𝟙 S) (e : J ≃ I) :
    (F.constantAt p hp).reindex e = (F.reindex e).constantAt p hp := rfl

/-- A morphism of marked maps remains a morphism after making both maps constant at the same
target section. -/
def constantAtHom {F G : MarkedMap q I} (f : F ⟶ G) (p : S ⟶ V)
    (hp : p ≫ q = 𝟙 S) : F.constantAt p hp ⟶ G.constantAt p hp where
  hom := f.hom
  over_base := f.over_base
  marking_comm := f.marking_comm
  map_comm := by
    change f.hom ≫ (G.toBase ≫ p) = F.toBase ≫ p
    rw [← Category.assoc, f.over_base]

/-- Making the target map constant is functorial on the marked-map category. -/
def constantAtFunctor (p : S ⟶ V) (hp : p ≫ q = 𝟙 S) :
    MarkedMap q I ⥤ MarkedMap q I where
  obj F := F.constantAt p hp
  map f := constantAtHom f p hp
  map_id _ := Hom.ext rfl
  map_comp _ _ := Hom.ext rfl

/-- Postcomposition of a constant map is constant at the postcomposed section.  The two
structures have associatively equal target maps, so the comparison is an identity-on-source
categorical isomorphism. -/
def constantAtPostcomposeIso {W : Scheme.{u}} {q' : W ⟶ S} (F : MarkedMap q I)
    (p : S ⟶ V) (hp : p ≫ q = 𝟙 S) (f : V ⟶ W) (hf : f ≫ q' = q) :
    (F.constantAt p hp).postcompose f hf ≅
      (F.postcompose f hf).constantAt (p ≫ f) (by
        rw [Category.assoc, hf, hp]) where
  hom :=
    { hom := 𝟙 _
      over_base := by
        change 𝟙 F.source ≫ F.toBase = F.toBase
        simp
      marking_comm := by
        intro i
        change F.marking i ≫ 𝟙 F.source = F.marking i
        simp
      map_comm := by
        change 𝟙 F.source ≫ (F.toBase ≫ (p ≫ f)) = (F.toBase ≫ p) ≫ f
        simp [Category.assoc] }
  inv :=
    { hom := 𝟙 _
      over_base := by
        change 𝟙 F.source ≫ F.toBase = F.toBase
        simp
      marking_comm := by
        intro i
        change F.marking i ≫ 𝟙 F.source = F.marking i
        simp
      map_comm := by
        change 𝟙 F.source ≫ ((F.toBase ≫ p) ≫ f) = F.toBase ≫ (p ≫ f)
        simp [Category.assoc] }
  hom_inv_id := by
    apply Hom.ext
    change 𝟙 F.source ≫ 𝟙 F.source = 𝟙 F.source
    simp
  inv_hom_id := by
    apply Hom.ext
    change 𝟙 F.source ≫ 𝟙 F.source = 𝟙 F.source
    simp

/-- Postcomposition and the constant-map functor commute naturally. -/
noncomputable def constantAtPostcomposeNatIso {W : Scheme.{u}} {q' : W ⟶ S}
    (p : S ⟶ V) (hp : p ≫ q = 𝟙 S) (f : V ⟶ W) (hf : f ≫ q' = q) :
    constantAtFunctor (I := I) p hp ⋙ postcomposeFunctor f hf ≅
      postcomposeFunctor f hf ⋙ constantAtFunctor (I := I) (p ≫ f) (by
        rw [Category.assoc, hf, hp]) :=
  NatIso.ofComponents (fun F ↦ constantAtPostcomposeIso F p hp f hf) (fun g ↦ by
    apply Hom.ext
    change g.hom ≫ 𝟙 _ = 𝟙 _ ≫ g.hom
    simp)

/-- The section of the pulled-back target induced by a section of the original target. -/
noncomputable def baseChangeSection (p : S ⟶ V) (hp : p ≫ q = 𝟙 S)
    {T : Scheme.{u}} (b : T ⟶ S) : T ⟶ pullback q b :=
  pullback.lift (b ≫ p) (𝟙 T) (by
    rw [Category.assoc, hp, Category.comp_id, Category.id_comp])

@[simp, reassoc]
lemma baseChangeSection_fst (p : S ⟶ V) (hp : p ≫ q = 𝟙 S)
    {T : Scheme.{u}} (b : T ⟶ S) :
    baseChangeSection p hp b ≫ pullback.fst q b = b ≫ p :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
lemma baseChangeSection_snd (p : S ⟶ V) (hp : p ≫ q = 𝟙 S)
    {T : Scheme.{u}} (b : T ⟶ S) :
    baseChangeSection p hp b ≫ pullback.snd q b = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- The two target maps obtained by making a map constant and then base changing, or base
changing and then making it constant at the pulled-back section, agree. -/
theorem baseChange_constantAt_map (F : MarkedMap q I) (p : S ⟶ V)
    (hp : p ≫ q = 𝟙 S) {T : Scheme.{u}} (b : T ⟶ S) :
    ((F.constantAt p hp).baseChange b).map =
      ((F.baseChange b).constantAt (baseChangeSection p hp b)
        (baseChangeSection_snd p hp b)).map := by
  apply pullback.hom_ext
  · simp only [baseChange, constantAt, Category.assoc, pullback.lift_fst,
      baseChangeSection_fst]
    rw [← Category.assoc, pullback.condition]
    exact Category.assoc _ _ _
  · simp only [baseChange, constantAt, Category.assoc, pullback.lift_snd,
      baseChangeSection_snd, Category.comp_id]

/-- Constant maps commute with chosen base change up to an identity-on-source categorical
isomorphism. -/
noncomputable def constantAtBaseChangeIso (F : MarkedMap q I) (p : S ⟶ V)
    (hp : p ≫ q = 𝟙 S) {T : Scheme.{u}} (b : T ⟶ S) :
    (F.constantAt p hp).baseChange b ≅
      (F.baseChange b).constantAt (baseChangeSection p hp b)
        (baseChangeSection_snd p hp b) where
  hom :=
    { hom := 𝟙 _
      over_base := by
        change 𝟙 _ ≫ pullback.snd F.toBase b = pullback.snd F.toBase b
        simp
      marking_comm := by
        intro i
        change (F.baseChange b).marking i ≫ 𝟙 _ = (F.baseChange b).marking i
        exact Category.comp_id _
      map_comm := by
        dsimp only [constantAt, baseChange]
        rw [Category.id_comp]
        exact (baseChange_constantAt_map F p hp b).symm }
  inv :=
    { hom := 𝟙 _
      over_base := by
        change 𝟙 _ ≫ pullback.snd F.toBase b = pullback.snd F.toBase b
        simp
      marking_comm := by
        intro i
        change (F.baseChange b).marking i ≫ 𝟙 _ = (F.baseChange b).marking i
        exact Category.comp_id _
      map_comm := by
        dsimp only [constantAt, baseChange]
        rw [Category.id_comp]
        exact baseChange_constantAt_map F p hp b }
  hom_inv_id := by
    apply Hom.ext
    change 𝟙 (pullback F.toBase b) ≫ 𝟙 (pullback F.toBase b) = 𝟙 _
    simp
  inv_hom_id := by
    apply Hom.ext
    change 𝟙 (pullback F.toBase b) ≫ 𝟙 (pullback F.toBase b) = 𝟙 _
    simp

/-- Chosen base change and the constant-map functor commute naturally. -/
noncomputable def constantAtBaseChangeNatIso (p : S ⟶ V) (hp : p ≫ q = 𝟙 S)
    {T : Scheme.{u}} (b : T ⟶ S) :
    constantAtFunctor (I := I) p hp ⋙ baseChangeFunctor b ≅
      baseChangeFunctor b ⋙
        constantAtFunctor (I := I) (baseChangeSection p hp b)
          (baseChangeSection_snd p hp b) :=
  NatIso.ofComponents (fun F ↦ constantAtBaseChangeIso F p hp b) (fun {F G} g ↦ by
    apply Hom.ext
    change (baseChangeHom g b).hom ≫ 𝟙 _ = 𝟙 _ ≫ (baseChangeHom g b).hom
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Restriction of markings and the constant-map functor commute naturally. -/
noncomputable def constantAtRestrictMarkingsNatIso (p : S ⟶ V)
    (hp : p ≫ q = 𝟙 S) (ρ : J → I) :
    constantAtFunctor (I := I) p hp ⋙ restrictMarkingsFunctor ρ ≅
      restrictMarkingsFunctor ρ ⋙ constantAtFunctor (I := J) p hp :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦ by
    apply Hom.ext
    change g.hom ≫ 𝟙 _ = 𝟙 _ ≫ g.hom
    simp)

/-- Any two constant maps at the same target section satisfy the external evaluation gate. -/
def constantExternalGluingData (F : MarkedMap q I) (G : MarkedMap q J)
    (p : S ⟶ V) (hp : p ≫ q = 𝟙 S) (i : I) (j : J) :
    ExternalGluingData (F.constantAt p hp) (G.constantAt p hp) where
  left := i
  right := j
  evaluation_eq := by simp

/-- Two distinct markings of a constant map satisfy the self-gluing gate. -/
def constantSelfGluingData (F : MarkedMap q I) (p : S ⟶ V)
    (hp : p ≫ q = 𝟙 S) (i j : I) (hij : i ≠ j) :
    SelfGluingData (F.constantAt p hp) where
  first := i
  second := j
  distinct := hij
  evaluation_eq := by simp

end GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap
