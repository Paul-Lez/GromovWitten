/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableMaps.Evaluation
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change of marked maps

Schemes have chosen pullbacks in Mathlib.  Pulling back both the source and target therefore gives
an honest functor on the category of marked maps.  The projection lemmas below expose the defining
universal-property equations, so downstream geometric predicates can prove base-change theorems
without unfolding this construction.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap

universe u v w

noncomputable section

variable {V S : Scheme.{u}} {q : V ⟶ S} {I : Type v}

/-- Base change a marked map along `b : T ⟶ S`, using Mathlib's chosen pullbacks for its source
and target. -/
@[simps]
def baseChange (F : MarkedMap q I) {T : Scheme.{u}} (b : T ⟶ S) :
    MarkedMap (pullback.snd q b) I where
  source := pullback F.toBase b
  toBase := pullback.snd F.toBase b
  marking i := pullback.lift (b ≫ F.marking i) (𝟙 T) (by
    simp only [Category.assoc, F.marking_toBase, Category.comp_id, Category.id_comp])
  marking_toBase i := pullback.lift_snd _ _ _
  map := pullback.lift (pullback.fst F.toBase b ≫ F.map) (pullback.snd F.toBase b) (by
    rw [Category.assoc, F.map_toBase]
    exact pullback.condition)
  map_toBase := pullback.lift_snd _ _ _

@[simp, reassoc]
lemma baseChange_marking_fst (F : MarkedMap q I) {T : Scheme.{u}} (b : T ⟶ S) (i : I) :
    (F.baseChange b).marking i ≫ pullback.fst F.toBase b = b ≫ F.marking i := by
  exact pullback.lift_fst _ _ _

@[simp, reassoc]
lemma baseChange_marking_snd (F : MarkedMap q I) {T : Scheme.{u}} (b : T ⟶ S) (i : I) :
    (F.baseChange b).marking i ≫ pullback.snd F.toBase b = 𝟙 T := by
  exact pullback.lift_snd _ _ _

@[simp, reassoc]
lemma baseChange_map_fst (F : MarkedMap q I) {T : Scheme.{u}} (b : T ⟶ S) :
    (F.baseChange b).map ≫ pullback.fst q b = pullback.fst F.toBase b ≫ F.map := by
  exact pullback.lift_fst _ _ _

@[simp, reassoc]
lemma baseChange_map_snd (F : MarkedMap q I) {T : Scheme.{u}} (b : T ⟶ S) :
    (F.baseChange b).map ≫ pullback.snd q b = pullback.snd F.toBase b := by
  exact pullback.lift_snd _ _ _

/-- The pullback of a morphism of marked maps. -/
@[simps]
def baseChangeHom {F G : MarkedMap q I} (f : F ⟶ G) {T : Scheme.{u}} (b : T ⟶ S) :
    F.baseChange b ⟶ G.baseChange b where
  hom := pullback.lift (pullback.fst F.toBase b ≫ f.hom) (pullback.snd F.toBase b) (by
    calc
      (pullback.fst F.toBase b ≫ f.hom) ≫ G.toBase =
          pullback.fst F.toBase b ≫ (f.hom ≫ G.toBase) := Category.assoc _ _ _
      _ = pullback.fst F.toBase b ≫ F.toBase := by rw [f.over_base]
      _ = pullback.snd F.toBase b ≫ b := pullback.condition)
  over_base := by
    exact pullback.lift_snd _ _ _
  marking_comm i := by
    apply pullback.hom_ext
    · simp only [baseChange, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, f.marking_comm]
    · simp only [baseChange, Category.assoc, pullback.lift_snd]
  map_comm := by
    apply pullback.hom_ext
    · simp only [baseChange, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, f.map_comm]
    · simp only [baseChange, Category.assoc, pullback.lift_snd]

@[simp, reassoc]
lemma baseChangeHom_fst {F G : MarkedMap q I} (f : F ⟶ G) {T : Scheme.{u}}
    (b : T ⟶ S) :
    (baseChangeHom f b).hom ≫ pullback.fst G.toBase b = pullback.fst F.toBase b ≫ f.hom := by
  exact pullback.lift_fst _ _ _

@[simp, reassoc]
lemma baseChangeHom_snd {F G : MarkedMap q I} (f : F ⟶ G) {T : Scheme.{u}}
    (b : T ⟶ S) :
    (baseChangeHom f b).hom ≫ pullback.snd G.toBase b = pullback.snd F.toBase b := by
  exact pullback.lift_snd _ _ _

/-- Chosen-pullback base change is functorial in morphisms of marked maps. -/
@[simps]
def baseChangeFunctor {T : Scheme.{u}} (b : T ⟶ S) :
    MarkedMap q I ⥤ MarkedMap (pullback.snd q b) I where
  obj F := F.baseChange b
  map f := baseChangeHom f b
  map_id F := by
    apply Hom.ext
    dsimp only [baseChange, baseChangeHom, id_hom]
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      simp
    · rw [pullback.lift_snd]
      simp
  map_comp f g := by
    apply Hom.ext
    dsimp only [baseChange, baseChangeHom, comp_hom]
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc]
    · simp only [pullback.lift_snd, Category.assoc]

/-- An isomorphism of marked maps induces the corresponding isomorphism between their chosen
source fibres after arbitrary base change. -/
def baseChangeSourceIso {F G : MarkedMap q I} (e : F ≅ G)
    {T : Scheme.{u}} (b : T ⟶ S) :
    pullback F.toBase b ≅ pullback G.toBase b where
  hom := (baseChangeHom e.hom b).hom
  inv := (baseChangeHom e.inv b).hom
  hom_inv_id := congrArg Hom.hom ((baseChangeFunctor b).mapIso e).hom_inv_id
  inv_hom_id := congrArg Hom.hom ((baseChangeFunctor b).mapIso e).inv_hom_id

@[simp]
lemma baseChangeSourceIso_hom {F G : MarkedMap q I} (e : F ≅ G)
    {T : Scheme.{u}} (b : T ⟶ S) :
    (baseChangeSourceIso e b).hom = (baseChangeHom e.hom b).hom := rfl

@[simp]
lemma baseChangeSourceIso_inv {F G : MarkedMap q I} (e : F ≅ G)
    {T : Scheme.{u}} (b : T ⟶ S) :
    (baseChangeSourceIso e b).inv = (baseChangeHom e.inv b).hom := rfl

@[simp]
lemma baseChange_restrictMarkings {J : Type w} (F : MarkedMap q I) (ρ : J → I)
    {T : Scheme.{u}} (b : T ⟶ S) :
    (F.restrictMarkings ρ).baseChange b = (F.baseChange b).restrictMarkings ρ := rfl

/-- Evaluation after base change, expressed directly as the section of the pulled-back target
selected by the universal property. -/
def baseChangedEvaluation (F : MarkedMap q I) (i : I) {T : Scheme.{u}} (b : T ⟶ S) :
    T ⟶ pullback q b :=
  pullback.lift (b ≫ F.evaluation i) (𝟙 T) (by
    simp only [Category.assoc, F.evaluation_toBase, Category.comp_id, Category.id_comp])

@[simp, reassoc]
lemma baseChangedEvaluation_fst (F : MarkedMap q I) (i : I) {T : Scheme.{u}}
    (b : T ⟶ S) :
    F.baseChangedEvaluation i b ≫ pullback.fst q b = b ≫ F.evaluation i := by
  exact pullback.lift_fst _ _ _

@[simp, reassoc]
lemma baseChangedEvaluation_snd (F : MarkedMap q I) (i : I) {T : Scheme.{u}}
    (b : T ⟶ S) :
    F.baseChangedEvaluation i b ≫ pullback.snd q b = 𝟙 T := by
  exact pullback.lift_snd _ _ _

/-- Evaluation commutes with chosen-pullback base change. -/
lemma evaluation_baseChange (F : MarkedMap q I) (i : I) {T : Scheme.{u}} (b : T ⟶ S) :
    (F.baseChange b).evaluation i = F.baseChangedEvaluation i b := by
  apply pullback.hom_ext
  · rw [baseChangedEvaluation_fst]
    change (((F.baseChange b).marking i ≫ (F.baseChange b).map) ≫
      pullback.fst q b) = b ≫ (F.marking i ≫ F.map)
    calc
      ((F.baseChange b).marking i ≫ (F.baseChange b).map) ≫ pullback.fst q b =
          (F.baseChange b).marking i ≫
            ((F.baseChange b).map ≫ pullback.fst q b) := Category.assoc _ _ _
      _ = (F.baseChange b).marking i ≫ (pullback.fst F.toBase b ≫ F.map) := by
        rw [baseChange_map_fst]
        rfl
      _ = ((F.baseChange b).marking i ≫ pullback.fst F.toBase b) ≫ F.map :=
        (Category.assoc _ _ _).symm
      _ = (b ≫ F.marking i) ≫ F.map := by rw [baseChange_marking_fst]
      _ = b ≫ (F.marking i ≫ F.map) := Category.assoc _ _ _
  · rw [baseChangedEvaluation_snd]
    change (((F.baseChange b).marking i ≫ (F.baseChange b).map) ≫
      pullback.snd q b) = 𝟙 T
    rw [Category.assoc, baseChange_map_snd, baseChange_marking_snd]

/-- A target morphism over `S` induces the corresponding target morphism after base change. -/
def baseChangeTargetMap {W : Scheme.{u}} {q' : W ⟶ S} (f : V ⟶ W) (hf : f ≫ q' = q)
    {T : Scheme.{u}} (b : T ⟶ S) : pullback q b ⟶ pullback q' b :=
  pullback.lift (pullback.fst q b ≫ f) (pullback.snd q b) (by
    rw [Category.assoc, hf]
    exact pullback.condition)

@[simp, reassoc]
lemma baseChangeTargetMap_fst {W : Scheme.{u}} {q' : W ⟶ S} (f : V ⟶ W)
    (hf : f ≫ q' = q) {T : Scheme.{u}} (b : T ⟶ S) :
    baseChangeTargetMap f hf b ≫ pullback.fst q' b = pullback.fst q b ≫ f := by
  exact pullback.lift_fst _ _ _

@[simp, reassoc]
lemma baseChangeTargetMap_snd {W : Scheme.{u}} {q' : W ⟶ S} (f : V ⟶ W)
    (hf : f ≫ q' = q) {T : Scheme.{u}} (b : T ⟶ S) :
    baseChangeTargetMap f hf b ≫ pullback.snd q' b = pullback.snd q b := by
  exact pullback.lift_snd _ _ _

/-- Base change and target postcomposition commute on the map to the pulled-back target. -/
lemma baseChange_postcompose_map {W : Scheme.{u}} {q' : W ⟶ S} (F : MarkedMap q I)
    (f : V ⟶ W) (hf : f ≫ q' = q) {T : Scheme.{u}} (b : T ⟶ S) :
    ((F.postcompose f hf).baseChange b).map =
      (F.baseChange b).map ≫ baseChangeTargetMap f hf b := by
  apply pullback.hom_ext
  · dsimp only [baseChange, postcompose]
    rw [pullback.lift_fst, Category.assoc, baseChangeTargetMap_fst,
      pullback.lift_fst_assoc]
    exact (Category.assoc _ _ _).symm
  · dsimp only [baseChange, postcompose]
    rw [pullback.lift_snd, Category.assoc, baseChangeTargetMap_snd,
      pullback.lift_snd]

/-- Chosen base change commutes with postcomposition by an arbitrary target morphism over the
base.  The two marked maps have the same chosen pullback as source, so their comparison is the
identity there; the target comparison is `baseChangeTargetMap`. -/
def baseChangePostcomposeIsoOfHom {W : Scheme.{u}} {q' : W ⟶ S} (F : MarkedMap q I)
    (f : V ⟶ W) (hf : f ≫ q' = q) {T : Scheme.{u}} (b : T ⟶ S) :
    ((F.baseChange b).postcompose (baseChangeTargetMap f hf b)
      (baseChangeTargetMap_snd f hf b)) ≅ (F.postcompose f hf).baseChange b where
  hom :=
    { hom := 𝟙 _
      over_base := by
        change 𝟙 _ ≫ pullback.snd F.toBase b = pullback.snd F.toBase b
        exact Category.id_comp _
      marking_comm := by
        intro i
        change (F.baseChange b).marking i ≫ 𝟙 _ = (F.baseChange b).marking i
        exact Category.comp_id _
      map_comm := by
        change 𝟙 _ ≫ ((F.postcompose f hf).baseChange b).map =
          (F.baseChange b).map ≫ baseChangeTargetMap f hf b
        rw [Category.id_comp]
        exact baseChange_postcompose_map F f hf b }
  inv :=
    { hom := 𝟙 _
      over_base := by
        change 𝟙 _ ≫ pullback.snd F.toBase b = pullback.snd F.toBase b
        exact Category.id_comp _
      marking_comm := by
        intro i
        change (F.baseChange b).marking i ≫ 𝟙 _ = (F.baseChange b).marking i
        exact Category.comp_id _
      map_comm := by
        change 𝟙 _ ≫ ((F.baseChange b).map ≫ baseChangeTargetMap f hf b) =
          ((F.postcompose f hf).baseChange b).map
        rw [Category.id_comp]
        exact (baseChange_postcompose_map F f hf b).symm }
  hom_inv_id := by
    apply Hom.ext
    change 𝟙 (pullback F.toBase b) ≫ 𝟙 (pullback F.toBase b) = 𝟙 _
    simp
  inv_hom_id := by
    apply Hom.ext
    change 𝟙 (pullback F.toBase b) ≫ 𝟙 (pullback F.toBase b) = 𝟙 _
    simp

/-- Functor-level naturality of the comparison between target postcomposition and chosen base
change.  No invertibility hypothesis is imposed on the target morphism. -/
noncomputable def baseChangePostcomposeNatIso {W : Scheme.{u}} {q' : W ⟶ S}
    (f : V ⟶ W) (hf : f ≫ q' = q) {T : Scheme.{u}} (b : T ⟶ S) :
    baseChangeFunctor (I := I) b ⋙
        postcomposeFunctor (baseChangeTargetMap f hf b) (baseChangeTargetMap_snd f hf b) ≅
      postcomposeFunctor f hf ⋙ baseChangeFunctor b :=
  NatIso.ofComponents (fun F ↦ baseChangePostcomposeIsoOfHom F f hf b) (fun {F G} g ↦ by
    apply Hom.ext
    change (baseChangeHom g b).hom ≫ 𝟙 _ = 𝟙 _ ≫ (baseChangeHom g b).hom
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Restriction of markings commutes naturally with chosen base change. -/
noncomputable def baseChangeRestrictMarkingsNatIso {J : Type w} (ρ : J → I)
    {T : Scheme.{u}} (b : T ⟶ S) :
    baseChangeFunctor (q := q) (I := I) b ⋙
        restrictMarkingsFunctor (q := pullback.snd q b) ρ ≅
      restrictMarkingsFunctor (q := q) ρ ⋙ baseChangeFunctor (q := q) b :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦ by
    apply Hom.ext
    change (baseChangeHom g b).hom ≫ 𝟙 _ = 𝟙 _ ≫ (baseChangeHom g b).hom
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Restriction of markings commutes naturally with target postcomposition. -/
noncomputable def postcomposeRestrictMarkingsNatIso {J : Type w} {W : Scheme.{u}}
    {q' : W ⟶ S} (ρ : J → I) (f : V ⟶ W) (hf : f ≫ q' = q) :
    postcomposeFunctor (I := I) f hf ⋙ restrictMarkingsFunctor (q := q') ρ ≅
      restrictMarkingsFunctor (q := q) ρ ⋙ postcomposeFunctor f hf :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦ by
    apply Hom.ext
    change g.hom ≫ 𝟙 _ = 𝟙 _ ≫ g.hom
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- An isomorphism of marked-map diagrams which is allowed to change the target, but not the
base or marking type.  This is the appropriate comparison object for chosen pullbacks: neither
the pulled-back source nor the pulled-back target is expected to be literally equal to another
choice of pullback. -/
structure TargetedIso {W : Scheme.{u}} {q' : W ⟶ S} (F : MarkedMap q I)
    (G : MarkedMap q' I) where
  targetIso : V ≅ W
  targetIso_toBase : targetIso.hom ≫ q' = q
  sourceIso : F.source ≅ G.source
  sourceIso_toBase : sourceIso.hom ≫ G.toBase = F.toBase
  marking_comm : ∀ i, F.marking i ≫ sourceIso.hom = G.marking i
  map_comm : F.map ≫ targetIso.hom = sourceIso.hom ≫ G.map

namespace TargetedIso

/-- Targeted isomorphisms are determined by their target and source isomorphisms; all remaining
fields are propositions. -/
@[ext]
lemma ext {W : Scheme.{u}} {q' : W ⟶ S} {F : MarkedMap q I} {G : MarkedMap q' I}
    {e f : TargetedIso F G} (htarget : e.targetIso = f.targetIso)
    (hsource : e.sourceIso = f.sourceIso) : e = f := by
  cases e
  cases f
  cases htarget
  cases hsource
  rfl

/-- A target-changing isomorphism transports every evaluation morphism through its target
isomorphism. -/
@[reassoc]
lemma evaluation_targetIso {W : Scheme.{u}} {q' : W ⟶ S} {F : MarkedMap q I}
    {G : MarkedMap q' I} (e : TargetedIso F G) (i : I) :
    F.evaluation i ≫ e.targetIso.hom = G.evaluation i := by
  rw [evaluation, evaluation, Category.assoc, e.map_comm, ← Category.assoc,
    e.marking_comm]

/-- The identity targeted isomorphism. -/
def refl (F : MarkedMap q I) : TargetedIso F F where
  targetIso := Iso.refl _
  targetIso_toBase := Category.id_comp _
  sourceIso := Iso.refl _
  sourceIso_toBase := Category.id_comp _
  marking_comm _ := Category.comp_id _
  map_comm := (Category.comp_id _).trans (Category.id_comp _).symm

/-- Reverse a targeted isomorphism. -/
def symm {W : Scheme.{u}} {q' : W ⟶ S} {F : MarkedMap q I} {G : MarkedMap q' I}
    (e : TargetedIso F G) : TargetedIso G F where
  targetIso := e.targetIso.symm
  targetIso_toBase := by
    change e.targetIso.inv ≫ q = q'
    calc
      e.targetIso.inv ≫ q = e.targetIso.inv ≫ (e.targetIso.hom ≫ q') :=
        congrArg (e.targetIso.inv ≫ ·) e.targetIso_toBase.symm
      _ = (e.targetIso.inv ≫ e.targetIso.hom) ≫ q' := (Category.assoc _ _ _).symm
      _ = q' := by rw [e.targetIso.inv_hom_id, Category.id_comp]
  sourceIso := e.sourceIso.symm
  sourceIso_toBase := by
    change e.sourceIso.inv ≫ F.toBase = G.toBase
    calc
      e.sourceIso.inv ≫ F.toBase =
          e.sourceIso.inv ≫ (e.sourceIso.hom ≫ G.toBase) :=
        congrArg (e.sourceIso.inv ≫ ·) e.sourceIso_toBase.symm
      _ = (e.sourceIso.inv ≫ e.sourceIso.hom) ≫ G.toBase :=
        (Category.assoc _ _ _).symm
      _ = G.toBase := by rw [e.sourceIso.inv_hom_id, Category.id_comp]
  marking_comm i := by
    change G.marking i ≫ e.sourceIso.inv = F.marking i
    calc
      G.marking i ≫ e.sourceIso.inv =
          (F.marking i ≫ e.sourceIso.hom) ≫ e.sourceIso.inv :=
        congrArg (· ≫ e.sourceIso.inv) (e.marking_comm i).symm
      _ = F.marking i := by
        rw [Category.assoc, e.sourceIso.hom_inv_id, Category.comp_id]
  map_comm := by
    change G.map ≫ e.targetIso.inv = e.sourceIso.inv ≫ F.map
    apply (cancel_mono e.targetIso.hom).1
    calc
      (G.map ≫ e.targetIso.inv) ≫ e.targetIso.hom = G.map := by simp
      _ = (e.sourceIso.inv ≫ e.sourceIso.hom) ≫ G.map := by simp
      _ = e.sourceIso.inv ≫ (e.sourceIso.hom ≫ G.map) := Category.assoc _ _ _
      _ = e.sourceIso.inv ≫ (F.map ≫ e.targetIso.hom) :=
        congrArg (e.sourceIso.inv ≫ ·) e.map_comm.symm
      _ = (e.sourceIso.inv ≫ F.map) ≫ e.targetIso.hom :=
        (Category.assoc _ _ _).symm

/-- Compose targeted isomorphisms over the fixed base and marking type. -/
def trans {W Z : Scheme.{u}} {q' : W ⟶ S} {q'' : Z ⟶ S} {F : MarkedMap q I}
    {G : MarkedMap q' I} {H : MarkedMap q'' I} (e : TargetedIso F G)
    (f : TargetedIso G H) : TargetedIso F H where
  targetIso := e.targetIso ≪≫ f.targetIso
  targetIso_toBase := by
    rw [Iso.trans_hom, Category.assoc, f.targetIso_toBase, e.targetIso_toBase]
  sourceIso := e.sourceIso ≪≫ f.sourceIso
  sourceIso_toBase := by
    rw [Iso.trans_hom, Category.assoc, f.sourceIso_toBase, e.sourceIso_toBase]
  marking_comm i := by
    rw [Iso.trans_hom, ← Category.assoc, e.marking_comm, f.marking_comm]
  map_comm := by
    change F.map ≫ (e.targetIso.hom ≫ f.targetIso.hom) =
      (e.sourceIso.hom ≫ f.sourceIso.hom) ≫ H.map
    rw [← Category.assoc, e.map_comm, Category.assoc, f.map_comm, ← Category.assoc]

@[simp]
lemma refl_targetIso (F : MarkedMap q I) : (refl F).targetIso = Iso.refl _ := rfl

@[simp]
lemma refl_sourceIso (F : MarkedMap q I) : (refl F).sourceIso = Iso.refl _ := rfl

@[simp]
lemma symm_targetIso {W : Scheme.{u}} {q' : W ⟶ S} {F : MarkedMap q I}
    {G : MarkedMap q' I} (e : TargetedIso F G) :
    e.symm.targetIso = e.targetIso.symm := rfl

@[simp]
lemma symm_sourceIso {W : Scheme.{u}} {q' : W ⟶ S} {F : MarkedMap q I}
    {G : MarkedMap q' I} (e : TargetedIso F G) :
    e.symm.sourceIso = e.sourceIso.symm := rfl

@[simp]
lemma trans_targetIso {W Z : Scheme.{u}} {q' : W ⟶ S} {q'' : Z ⟶ S}
    {F : MarkedMap q I} {G : MarkedMap q' I} {H : MarkedMap q'' I}
    (e : TargetedIso F G) (f : TargetedIso G H) :
    (e.trans f).targetIso = e.targetIso ≪≫ f.targetIso := rfl

@[simp]
lemma trans_sourceIso {W Z : Scheme.{u}} {q' : W ⟶ S} {q'' : Z ⟶ S}
    {F : MarkedMap q I} {G : MarkedMap q' I} {H : MarkedMap q'' I}
    (e : TargetedIso F G) (f : TargetedIso G H) :
    (e.trans f).sourceIso = e.sourceIso ≪≫ f.sourceIso := rfl

@[simp]
lemma symm_symm {W : Scheme.{u}} {q' : W ⟶ S} {F : MarkedMap q I}
    {G : MarkedMap q' I} (e : TargetedIso F G) : e.symm.symm = e := by
  apply ext <;> simp

@[simp]
lemma refl_trans {W : Scheme.{u}} {q' : W ⟶ S} {F : MarkedMap q I}
    {G : MarkedMap q' I} (e : TargetedIso F G) : (refl F).trans e = e := by
  apply ext <;> simp

@[simp]
lemma trans_refl {W : Scheme.{u}} {q' : W ⟶ S} {F : MarkedMap q I}
    {G : MarkedMap q' I} (e : TargetedIso F G) : e.trans (refl G) = e := by
  apply ext <;> simp

@[simp]
lemma trans_assoc {W Z T : Scheme.{u}} {q' : W ⟶ S} {q'' : Z ⟶ S}
    {q''' : T ⟶ S} {F : MarkedMap q I} {G : MarkedMap q' I} {H : MarkedMap q'' I}
    {K : MarkedMap q''' I} (e : TargetedIso F G) (f : TargetedIso G H)
    (g : TargetedIso H K) : (e.trans f).trans g = e.trans (f.trans g) := by
  apply ext <;> simp

@[simp]
lemma trans_symm {W : Scheme.{u}} {q' : W ⟶ S} {F : MarkedMap q I}
    {G : MarkedMap q' I} (e : TargetedIso F G) : e.trans e.symm = refl F := by
  apply ext <;> simp

@[simp]
lemma symm_trans {W : Scheme.{u}} {q' : W ⟶ S} {F : MarkedMap q I}
    {G : MarkedMap q' I} (e : TargetedIso F G) : e.symm.trans e = refl G := by
  apply ext <;> simp

/-- After transporting the target, a targeted isomorphism becomes an ordinary categorical
isomorphism of marked maps. -/
def toIso {W : Scheme.{u}} {q' : W ⟶ S} {F : MarkedMap q I} {G : MarkedMap q' I}
    (e : TargetedIso F G) : F.postcompose e.targetIso.hom e.targetIso_toBase ≅ G where
  hom :=
    { hom := e.sourceIso.hom
      over_base := e.sourceIso_toBase
      marking_comm := e.marking_comm
      map_comm := e.map_comm.symm }
  inv :=
    { hom := e.sourceIso.inv
      over_base := by
        change e.sourceIso.inv ≫ F.toBase = G.toBase
        rw [← e.sourceIso_toBase, ← Category.assoc, e.sourceIso.inv_hom_id,
          Category.id_comp]
      marking_comm := by
        intro i
        change G.marking i ≫ e.sourceIso.inv = F.marking i
        rw [← e.marking_comm i, Category.assoc, e.sourceIso.hom_inv_id,
          Category.comp_id]
      map_comm := by
        change e.sourceIso.inv ≫ (F.map ≫ e.targetIso.hom) = G.map
        rw [e.map_comm, ← Category.assoc, e.sourceIso.inv_hom_id, Category.id_comp] }
  hom_inv_id := by
    apply Hom.ext
    exact e.sourceIso.hom_inv_id
  inv_hom_id := by
    apply Hom.ext
    exact e.sourceIso.inv_hom_id

@[simp]
lemma toIso_hom_hom {W : Scheme.{u}} {q' : W ⟶ S} {F : MarkedMap q I}
    {G : MarkedMap q' I} (e : TargetedIso F G) : e.toIso.hom.hom = e.sourceIso.hom := rfl

@[simp]
lemma toIso_inv_hom {W : Scheme.{u}} {q' : W ⟶ S} {F : MarkedMap q I}
    {G : MarkedMap q' I} (e : TargetedIso F G) : e.toIso.inv.hom = e.sourceIso.inv := rfl

end TargetedIso

/-- The target comparison for base change along the identity. -/
def baseChangeIdTargetIso (q : V ⟶ S) : pullback q (𝟙 S) ≅ V :=
  asIso (pullback.fst q (𝟙 S))

/-- The source comparison for base change along the identity. -/
def baseChangeIdSourceIso (F : MarkedMap q I) : pullback F.toBase (𝟙 S) ≅ F.source :=
  asIso (pullback.fst F.toBase (𝟙 S))

/-- Base change along the identity is canonically isomorphic to the original marked map. -/
def baseChangeIdComparison (F : MarkedMap q I) : TargetedIso (F.baseChange (𝟙 S)) F where
  targetIso := baseChangeIdTargetIso q
  targetIso_toBase := by
    dsimp only [baseChangeIdTargetIso]
    simpa using pullback.condition (f := q) (g := 𝟙 S)
  sourceIso := baseChangeIdSourceIso F
  sourceIso_toBase := by
    change pullback.fst F.toBase (𝟙 S) ≫ F.toBase = pullback.snd F.toBase (𝟙 S)
    simpa using pullback.condition (f := F.toBase) (g := 𝟙 S)
  marking_comm i := by
    dsimp only [baseChangeIdSourceIso]
    simpa using baseChange_marking_fst F (𝟙 S) i
  map_comm := by
    dsimp only [baseChangeIdTargetIso, baseChangeIdSourceIso]
    exact baseChange_map_fst F (𝟙 S)

/-- The ordinary categorical identity-base-change isomorphism after transporting its target. -/
def baseChangeIdIso (F : MarkedMap q I) :
    (F.baseChange (𝟙 S)).postcompose (baseChangeIdTargetIso q).hom
      (baseChangeIdComparison F).targetIso_toBase ≅ F :=
  (baseChangeIdComparison F).toIso

/-- The canonical target comparison between iterated and direct chosen base change. -/
def iteratedBaseChangeTargetIso (q : V ⟶ S) {T U : Scheme.{u}} (b : T ⟶ S)
    (c : U ⟶ T) : pullback (pullback.snd q b) c ≅ pullback q (c ≫ b) :=
  pullbackLeftPullbackSndIso q b c

/-- The canonical source comparison between iterated and direct chosen base change. -/
def iteratedBaseChangeSourceIso (F : MarkedMap q I) {T U : Scheme.{u}} (b : T ⟶ S)
    (c : U ⟶ T) : pullback (pullback.snd F.toBase b) c ≅ pullback F.toBase (c ≫ b) :=
  pullbackLeftPullbackSndIso F.toBase b c

/-- Iterated chosen base change is canonically isomorphic to direct base change. -/
def iteratedBaseChangeComparison (F : MarkedMap q I) {T U : Scheme.{u}} (b : T ⟶ S)
    (c : U ⟶ T) :
    TargetedIso ((F.baseChange b).baseChange c) (F.baseChange (c ≫ b)) where
  targetIso := iteratedBaseChangeTargetIso q b c
  targetIso_toBase := pullbackLeftPullbackSndIso_hom_snd q b c
  sourceIso := iteratedBaseChangeSourceIso F b c
  sourceIso_toBase := pullbackLeftPullbackSndIso_hom_snd F.toBase b c
  marking_comm i := by
    dsimp only [baseChange, iteratedBaseChangeSourceIso]
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst]
      rw [← Category.assoc, pullback.lift_fst]
      simp only [Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
      simp only [pullback.lift_snd]
  map_comm := by
    dsimp only [baseChange, iteratedBaseChangeTargetIso, iteratedBaseChangeSourceIso]
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst]
      rw [← Category.assoc, pullback.lift_fst]
      rw [Category.assoc, pullback.lift_fst]
      rw [Category.assoc, pullback.lift_fst]
      exact (pullbackLeftPullbackSndIso_hom_fst_assoc F.toBase b c F.map).symm
    · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
      rw [pullback.lift_snd]
      rw [Category.assoc, pullback.lift_snd]
      rw [pullbackLeftPullbackSndIso_hom_snd]

/-- The ordinary categorical iterated-base-change isomorphism after transporting its target. -/
def iteratedBaseChangeIso (F : MarkedMap q I) {T U : Scheme.{u}} (b : T ⟶ S)
    (c : U ⟶ T) :
    (((F.baseChange b).baseChange c).postcompose
      (iteratedBaseChangeTargetIso q b c).hom
      (iteratedBaseChangeComparison F b c).targetIso_toBase) ≅
      F.baseChange (c ≫ b) :=
  (iteratedBaseChangeComparison F b c).toIso

/-- The inverse of a target isomorphism over the base is again over the base. -/
lemma targetIso_inv_toBase {W : Scheme.{u}} {q' : W ⟶ S} (e : V ≅ W)
    (h : e.hom ≫ q' = q) : e.inv ≫ q = q' := by
  rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- An isomorphism of targets over the base induces an isomorphism of their chosen pullbacks. -/
def baseChangeTargetIso {W : Scheme.{u}} {q' : W ⟶ S} (e : V ≅ W)
    (h : e.hom ≫ q' = q) {T : Scheme.{u}} (b : T ⟶ S) :
    pullback q b ≅ pullback q' b where
  hom := baseChangeTargetMap e.hom h b
  inv := baseChangeTargetMap e.inv (targetIso_inv_toBase e h) b
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, baseChangeTargetMap_fst_assoc,
        baseChangeTargetMap_fst, e.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, baseChangeTargetMap_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, baseChangeTargetMap_fst_assoc,
        baseChangeTargetMap_fst, e.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, baseChangeTargetMap_snd, Category.id_comp]

/-- Base change commutes with transport across an isomorphism of targets. -/
def baseChangePostcomposeComparison {W : Scheme.{u}} {q' : W ⟶ S} (F : MarkedMap q I)
    (e : V ≅ W) (h : e.hom ≫ q' = q) {T : Scheme.{u}} (b : T ⟶ S) :
    TargetedIso (F.baseChange b) ((F.postcompose e.hom h).baseChange b) where
  targetIso := baseChangeTargetIso e h b
  targetIso_toBase := baseChangeTargetMap_snd e.hom h b
  sourceIso := Iso.refl _
  sourceIso_toBase := by
    change 𝟙 _ ≫ pullback.snd F.toBase b = pullback.snd F.toBase b
    exact Category.id_comp _
  marking_comm i := by
    change (F.baseChange b).marking i ≫ 𝟙 _ = (F.baseChange b).marking i
    exact Category.comp_id _
  map_comm := by
    change (F.baseChange b).map ≫ baseChangeTargetMap e.hom h b =
      ((F.postcompose e.hom h).baseChange b).map
    exact (baseChange_postcompose_map F e.hom h b).symm

/-- The categorical target-transport comparison after chosen base change. -/
def baseChangePostcomposeIso {W : Scheme.{u}} {q' : W ⟶ S} (F : MarkedMap q I)
    (e : V ≅ W) (h : e.hom ≫ q' = q) {T : Scheme.{u}} (b : T ⟶ S) :
    ((F.baseChange b).postcompose (baseChangeTargetIso e h b).hom
      (baseChangePostcomposeComparison F e h b).targetIso_toBase) ≅
      (F.postcompose e.hom h).baseChange b :=
  (baseChangePostcomposeComparison F e h b).toIso

end

end GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap
