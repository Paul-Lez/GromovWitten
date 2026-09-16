/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableMaps.GluingData

/-!
# Gluing marked maps along a supplied scheme pushout

The roadmap ultimately requires constructing scheme pushouts that identify smooth sections.
That geometric existence theorem is not available in the pinned dependencies.  This file proves
the complementary universal-property statement without adding an existence assumption to the
definition of marked maps: whenever a particular section span is supplied with a colimit cocone,
equal evaluations descend the target map uniquely and produce the externally glued marked-map
diagram.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap

universe u v w

noncomputable section

variable {V S : Scheme.{u}} {q : V ⟶ S}
variable {I : Type v} {J : Type w}
variable {F : MarkedMap q I} {G : MarkedMap q J}

namespace ExternalGluingData

/-- Swap the two inputs of external gluing data. -/
def swap (D : ExternalGluingData F G) : ExternalGluingData G F where
  left := D.right
  right := D.left
  evaluation_eq := D.evaluation_eq.symm

@[simp]
lemma swap_left (D : ExternalGluingData F G) : D.swap.left = D.right := rfl

@[simp]
lemma swap_right (D : ExternalGluingData F G) : D.swap.right = D.left := rfl

@[simp]
lemma swap_swap (D : ExternalGluingData F G) : D.swap.swap = D := by
  ext <;> rfl

end ExternalGluingData

namespace SelfGluingData

/-- Swap the two selected branches of self-gluing data. -/
def swap (D : SelfGluingData F) : SelfGluingData F where
  first := D.second
  second := D.first
  distinct := fun h ↦ D.distinct h.symm
  evaluation_eq := D.evaluation_eq.symm

@[simp]
lemma swap_first (D : SelfGluingData F) : D.swap.first = D.second := rfl

@[simp]
lemma swap_second (D : SelfGluingData F) : D.swap.second = D.first := rfl

@[simp]
lemma swap_swap (D : SelfGluingData F) : D.swap.swap = D := by
  ext <;> rfl

end SelfGluingData

/-- A chosen categorical pushout of the two source schemes along the selected sections. -/
structure ExternalPushout (D : ExternalGluingData F G) where
  cocone : PushoutCocone (F.marking D.left) (G.marking D.right)
  isColimit : IsColimit cocone

namespace ExternalPushout

variable {D : ExternalGluingData F G} (P : ExternalPushout D)

/-- Swapping the two inputs flips a supplied pushout cocone. -/
def swap : ExternalPushout D.swap where
  cocone := P.cocone.flip
  isColimit := PushoutCocone.flipIsColimit P.isColimit

/-- The target map descends because the selected evaluation maps agree. -/
def targetMap : P.cocone.pt ⟶ V :=
  PushoutCocone.IsColimit.desc P.isColimit F.map G.map D.evaluation_eq

/-- The source structure maps descend because both selected markings are sections. -/
def toBase : P.cocone.pt ⟶ S :=
  PushoutCocone.IsColimit.desc P.isColimit F.toBase G.toBase (by
    rw [F.marking_toBase D.left, G.marking_toBase D.right])

@[reassoc (attr := simp)]
theorem inl_targetMap : P.cocone.inl ≫ P.targetMap = F.map :=
  PushoutCocone.IsColimit.inl_desc P.isColimit _ _ _

@[reassoc (attr := simp)]
theorem inr_targetMap : P.cocone.inr ≫ P.targetMap = G.map :=
  PushoutCocone.IsColimit.inr_desc P.isColimit _ _ _

@[reassoc (attr := simp)]
theorem inl_toBase : P.cocone.inl ≫ P.toBase = F.toBase :=
  PushoutCocone.IsColimit.inl_desc P.isColimit _ _ _

@[reassoc (attr := simp)]
theorem inr_toBase : P.cocone.inr ≫ P.toBase = G.toBase :=
  PushoutCocone.IsColimit.inr_desc P.isColimit _ _ _

/-- The descended target map remains a morphism over the base. -/
@[reassoc]
theorem targetMap_toBase : P.targetMap ≫ q = P.toBase := by
  apply PushoutCocone.IsColimit.hom_ext P.isColimit
  · rw [← Category.assoc, P.inl_targetMap, F.map_toBase, P.inl_toBase]
  · rw [← Category.assoc, P.inr_targetMap, G.map_toBase, P.inr_toBase]

/-- The marking set left after removing the two markings used for gluing. -/
abbrev RemainingIndex (_P : ExternalPushout D) :=
  { i : I // i ≠ D.left } ⊕ { j : J // j ≠ D.right }

/-- Retained markings map into the chosen pushout through the corresponding inclusion. -/
def remainingMarking : P.RemainingIndex → (S ⟶ P.cocone.pt)
  | Sum.inl i => F.marking i.1 ≫ P.cocone.inl
  | Sum.inr j => G.marking j.1 ≫ P.cocone.inr

@[reassoc (attr := simp)]
theorem remainingMarking_toBase (i : P.RemainingIndex) :
    P.remainingMarking i ≫ P.toBase = 𝟙 S := by
  cases i with
  | inl i => simpa [remainingMarking] using F.marking_toBase i.1
  | inr j => simpa [remainingMarking] using G.marking_toBase j.1

/-- External gluing as a marked-map diagram, conditional only on the supplied categorical
pushout.  All scheme-geometric properties of the pushout remain separate. -/
def markedMap : MarkedMap q P.RemainingIndex where
  source := P.cocone.pt
  toBase := P.toBase
  marking := P.remainingMarking
  marking_toBase := P.remainingMarking_toBase
  map := P.targetMap
  map_toBase := P.targetMap_toBase

@[simp]
theorem markedMap_source : P.markedMap.source = P.cocone.pt := rfl

@[simp]
theorem markedMap_map : P.markedMap.map = P.targetMap := rfl

@[simp]
theorem markedMap_toBase : P.markedMap.toBase = P.toBase := rfl

@[simp]
theorem markedMap_evaluation_inl (i : { i : I // i ≠ D.left }) :
    P.markedMap.evaluation (Sum.inl i) = F.evaluation i.1 := by
  simp only [MarkedMap.evaluation, markedMap, remainingMarking, Category.assoc,
    P.inl_targetMap]

@[simp]
theorem markedMap_evaluation_inr (j : { j : J // j ≠ D.right }) :
    P.markedMap.evaluation (Sum.inr j) = G.evaluation j.1 := by
  simp only [MarkedMap.evaluation, markedMap, remainingMarking, Category.assoc,
    P.inr_targetMap]

/-- The descended target map is uniquely characterized by its restrictions to both sources. -/
theorem targetMap_unique (f : P.cocone.pt ⟶ V) (hF : P.cocone.inl ≫ f = F.map)
    (hG : P.cocone.inr ≫ f = G.map) : f = P.targetMap := by
  apply PushoutCocone.IsColimit.hom_ext P.isColimit
  · rw [hF, P.inl_targetMap]
  · rw [hG, P.inr_targetMap]

/-- The descended structure map is uniquely characterized by its restrictions to both sources. -/
theorem toBase_unique (f : P.cocone.pt ⟶ S) (hF : P.cocone.inl ≫ f = F.toBase)
    (hG : P.cocone.inr ≫ f = G.toBase) : f = P.toBase := by
  apply PushoutCocone.IsColimit.hom_ext P.isColimit
  · rw [hF, P.inl_toBase]
  · rw [hG, P.inr_toBase]

/-- Swapping the two inputs leaves the descended target map unchanged. -/
@[simp]
lemma swap_targetMap : P.swap.targetMap = P.targetMap := by
  apply P.targetMap_unique
  · exact P.swap.inr_targetMap
  · exact P.swap.inl_targetMap

/-- Swapping the two inputs leaves the descended structure map unchanged. -/
@[simp]
lemma swap_toBase : P.swap.toBase = P.toBase := by
  apply PushoutCocone.IsColimit.hom_ext P.isColimit
  · change P.swap.cocone.inr ≫ P.swap.toBase = P.cocone.inl ≫ P.toBase
    rw [P.swap.inr_toBase, P.inl_toBase]
  · change P.swap.cocone.inl ≫ P.swap.toBase = P.cocone.inr ≫ P.toBase
    rw [P.swap.inl_toBase, P.inr_toBase]

/-- Swapping the two inputs swaps the two summands of the retained marking type. -/
def swapRemainingIndexEquiv : P.RemainingIndex ≃ P.swap.RemainingIndex where
  toFun
    | Sum.inl i => Sum.inr ⟨i.1, by simpa using i.2⟩
    | Sum.inr j => Sum.inl ⟨j.1, by simpa using j.2⟩
  invFun
    | Sum.inl j => Sum.inr ⟨j.1, by simpa using j.2⟩
    | Sum.inr i => Sum.inl ⟨i.1, by simpa using i.2⟩
  left_inv i := by cases i <;> rfl
  right_inv i := by cases i <;> rfl

@[simp]
lemma swapRemainingIndexEquiv_apply_inl (i : { i : I // i ≠ D.left }) :
    P.swapRemainingIndexEquiv (Sum.inl i) =
      Sum.inr ⟨i.1, by simpa using i.2⟩ := rfl

@[simp]
lemma swapRemainingIndexEquiv_apply_inr (j : { j : J // j ≠ D.right }) :
    P.swapRemainingIndexEquiv (Sum.inr j) =
      Sum.inl ⟨j.1, by simpa using j.2⟩ := rfl

/-- After the canonical reindexing of retained markings, swapping the two inputs does not
change the supplied externally glued marked map. -/
def swapMarkedMapIso :
    P.markedMap ≅ P.swap.markedMap.reindex P.swapRemainingIndexEquiv where
  hom :=
    { hom := 𝟙 _
      over_base := by
        change 𝟙 _ ≫ P.swap.toBase = P.toBase
        rw [Category.id_comp, swap_toBase]
      marking_comm := by
        intro i
        change P.remainingMarking i ≫ 𝟙 _ =
          P.swap.remainingMarking (P.swapRemainingIndexEquiv i)
        rw [Category.comp_id]
        cases i <;> rfl
      map_comm := by
        change 𝟙 _ ≫ P.swap.targetMap = P.targetMap
        rw [Category.id_comp, swap_targetMap] }
  inv :=
    { hom := 𝟙 _
      over_base := by
        change 𝟙 _ ≫ P.toBase = P.swap.toBase
        rw [Category.id_comp, swap_toBase]
      marking_comm := by
        intro i
        change P.swap.remainingMarking (P.swapRemainingIndexEquiv i) ≫ 𝟙 _ =
          P.remainingMarking i
        rw [Category.comp_id]
        cases i <;> rfl
      map_comm := by
        change 𝟙 _ ≫ P.targetMap = P.swap.targetMap
        rw [Category.id_comp, swap_targetMap] }
  hom_inv_id := by
    apply Hom.ext
    exact Category.id_comp _
  inv_hom_id := by
    apply Hom.ext
    exact Category.comp_id _

/-- Swapping external gluing inputs preserves every retained evaluation after the canonical
reindexing. -/
@[simp]
lemma swapMarkedMap_evaluation (i : P.RemainingIndex) :
    (P.swap.markedMap.reindex P.swapRemainingIndexEquiv).evaluation i =
      P.markedMap.evaluation i :=
  (evaluation_naturality P.swapMarkedMapIso.hom i).symm

/-- The canonical isomorphism between the vertices of two supplied pushout witnesses. -/
def comparisonIso (P Q : ExternalPushout D) : P.cocone.pt ≅ Q.cocone.pt :=
  P.isColimit.coconePointUniqueUpToIso Q.isColimit

@[reassoc (attr := simp)]
lemma inl_comparisonIso_hom (P Q : ExternalPushout D) :
    P.cocone.inl ≫ (comparisonIso P Q).hom = Q.cocone.inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom P.isColimit Q.isColimit WalkingSpan.left

@[reassoc (attr := simp)]
lemma inr_comparisonIso_hom (P Q : ExternalPushout D) :
    P.cocone.inr ≫ (comparisonIso P Q).hom = Q.cocone.inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom P.isColimit Q.isColimit WalkingSpan.right

/-- The canonical comparison intertwines the descended target maps. -/
@[reassoc]
lemma comparisonIso_hom_targetMap (P Q : ExternalPushout D) :
    (comparisonIso P Q).hom ≫ Q.targetMap = P.targetMap := by
  apply P.targetMap_unique
  · rw [inl_comparisonIso_hom_assoc, Q.inl_targetMap]
  · rw [inr_comparisonIso_hom_assoc, Q.inr_targetMap]

/-- The canonical comparison intertwines the descended structure maps. -/
@[reassoc]
lemma comparisonIso_hom_toBase (P Q : ExternalPushout D) :
    (comparisonIso P Q).hom ≫ Q.toBase = P.toBase := by
  apply P.toBase_unique
  · rw [inl_comparisonIso_hom_assoc, Q.inl_toBase]
  · rw [inr_comparisonIso_hom_assoc, Q.inr_toBase]

/-- The canonical comparison carries every retained marking to the corresponding marking. -/
@[reassoc]
lemma remainingMarking_comparisonIso_hom (P Q : ExternalPushout D)
    (i : P.RemainingIndex) :
    P.remainingMarking i ≫ (comparisonIso P Q).hom = Q.remainingMarking i := by
  cases i with
  | inl i => simp [remainingMarking, Category.assoc]
  | inr i => simp [remainingMarking, Category.assoc]

/-- The marked maps obtained from any two supplied pushout witnesses are canonically
isomorphic. -/
def markedMapIso (P Q : ExternalPushout D) : P.markedMap ≅ Q.markedMap where
  hom :=
    { hom := (comparisonIso P Q).hom
      over_base := comparisonIso_hom_toBase P Q
      marking_comm := remainingMarking_comparisonIso_hom P Q
      map_comm := comparisonIso_hom_targetMap P Q }
  inv :=
    { hom := (comparisonIso P Q).inv
      over_base := by
        change (comparisonIso P Q).inv ≫ P.toBase = Q.toBase
        rw [← comparisonIso_hom_toBase P Q, ← Category.assoc,
          (comparisonIso P Q).inv_hom_id, Category.id_comp]
      marking_comm := by
        intro i
        change Q.remainingMarking i ≫ (comparisonIso P Q).inv = P.remainingMarking i
        rw [← remainingMarking_comparisonIso_hom P Q i, Category.assoc,
          (comparisonIso P Q).hom_inv_id, Category.comp_id]
      map_comm := by
        change (comparisonIso P Q).inv ≫ P.targetMap = Q.targetMap
        rw [← comparisonIso_hom_targetMap P Q, ← Category.assoc,
          (comparisonIso P Q).inv_hom_id, Category.id_comp] }
  hom_inv_id := by
    apply Hom.ext
    exact (comparisonIso P Q).hom_inv_id
  inv_hom_id := by
    apply Hom.ext
    exact (comparisonIso P Q).inv_hom_id

@[reassoc (attr := simp)]
lemma inl_comparisonIso_inv (P Q : ExternalPushout D) :
    Q.cocone.inl ≫ (comparisonIso P Q).inv = P.cocone.inl :=
  IsColimit.comp_coconePointUniqueUpToIso_inv P.isColimit Q.isColimit WalkingSpan.left

@[reassoc (attr := simp)]
lemma inr_comparisonIso_inv (P Q : ExternalPushout D) :
    Q.cocone.inr ≫ (comparisonIso P Q).inv = P.cocone.inr :=
  IsColimit.comp_coconePointUniqueUpToIso_inv P.isColimit Q.isColimit WalkingSpan.right

@[simp]
lemma comparisonIso_refl_hom (P : ExternalPushout D) :
    (comparisonIso P P).hom = 𝟙 P.cocone.pt := by
  apply PushoutCocone.IsColimit.hom_ext P.isColimit
  · rw [inl_comparisonIso_hom, Category.comp_id]
  · rw [inr_comparisonIso_hom, Category.comp_id]

@[simp]
lemma comparisonIso_refl_inv (P : ExternalPushout D) :
    (comparisonIso P P).inv = 𝟙 P.cocone.pt := by
  change (comparisonIso P P).inv = (Iso.refl P.cocone.pt).inv
  rw [Iso.inv_eq_inv]
  exact comparisonIso_refl_hom P

lemma comparisonIso_symm_hom (P Q : ExternalPushout D) :
    (comparisonIso Q P).hom = (comparisonIso P Q).inv := by
  apply PushoutCocone.IsColimit.hom_ext Q.isColimit
  · rw [inl_comparisonIso_hom, inl_comparisonIso_inv]
  · rw [inr_comparisonIso_hom, inr_comparisonIso_inv]

lemma comparisonIso_trans_hom (P Q R : ExternalPushout D) :
    (comparisonIso P Q).hom ≫ (comparisonIso Q R).hom =
      (comparisonIso P R).hom := by
  apply PushoutCocone.IsColimit.hom_ext P.isColimit
  · simp
  · simp

@[simp]
lemma comparisonIso_refl (P : ExternalPushout D) :
    comparisonIso P P = Iso.refl P.cocone.pt :=
  Iso.ext (comparisonIso_refl_hom P)

lemma comparisonIso_symm (P Q : ExternalPushout D) :
    (comparisonIso P Q).symm = comparisonIso Q P :=
  Iso.ext (comparisonIso_symm_hom P Q).symm

lemma comparisonIso_trans (P Q R : ExternalPushout D) :
    comparisonIso P Q ≪≫ comparisonIso Q R = comparisonIso P R :=
  Iso.ext (comparisonIso_trans_hom P Q R)

@[reassoc]
lemma comparisonIso_inv_targetMap (P Q : ExternalPushout D) :
    (comparisonIso P Q).inv ≫ P.targetMap = Q.targetMap := by
  rw [← comparisonIso_hom_targetMap P Q, ← Category.assoc,
    (comparisonIso P Q).inv_hom_id, Category.id_comp]

@[reassoc]
lemma comparisonIso_inv_toBase (P Q : ExternalPushout D) :
    (comparisonIso P Q).inv ≫ P.toBase = Q.toBase := by
  rw [← comparisonIso_hom_toBase P Q, ← Category.assoc,
    (comparisonIso P Q).inv_hom_id, Category.id_comp]

@[reassoc]
lemma remainingMarking_comparisonIso_inv (P Q : ExternalPushout D)
    (i : P.RemainingIndex) :
    Q.remainingMarking i ≫ (comparisonIso P Q).inv = P.remainingMarking i := by
  rw [← remainingMarking_comparisonIso_hom P Q i, Category.assoc,
    (comparisonIso P Q).hom_inv_id, Category.comp_id]

@[simp]
lemma markedMapIso_hom_hom (P Q : ExternalPushout D) :
    (markedMapIso P Q).hom.hom = (comparisonIso P Q).hom := rfl

@[simp]
lemma markedMapIso_inv_hom (P Q : ExternalPushout D) :
    (markedMapIso P Q).inv.hom = (comparisonIso P Q).inv := rfl

@[simp]
lemma markedMapIso_refl_hom (P : ExternalPushout D) :
    (markedMapIso P P).hom = 𝟙 P.markedMap := by
  apply Hom.ext
  exact comparisonIso_refl_hom P

lemma markedMapIso_symm_hom (P Q : ExternalPushout D) :
    (markedMapIso Q P).hom = (markedMapIso P Q).inv := by
  apply Hom.ext
  exact comparisonIso_symm_hom P Q

lemma markedMapIso_trans_hom (P Q R : ExternalPushout D) :
    (markedMapIso P Q).hom ≫ (markedMapIso Q R).hom =
      (markedMapIso P R).hom := by
  apply Hom.ext
  exact comparisonIso_trans_hom P Q R

@[simp]
lemma markedMapIso_refl (P : ExternalPushout D) :
    markedMapIso P P = Iso.refl P.markedMap :=
  Iso.ext (markedMapIso_refl_hom P)

lemma markedMapIso_symm (P Q : ExternalPushout D) :
    (markedMapIso P Q).symm = markedMapIso Q P :=
  Iso.ext (markedMapIso_symm_hom P Q).symm

lemma markedMapIso_trans (P Q R : ExternalPushout D) :
    markedMapIso P Q ≪≫ markedMapIso Q R = markedMapIso P R :=
  Iso.ext (markedMapIso_trans_hom P Q R)

end ExternalPushout

/-- A chosen categorical coequalizer identifying the two selected sections of one source. -/
structure SelfCoequalizer (D : SelfGluingData F) where
  cofork : Cofork (F.marking D.first) (F.marking D.second)
  isColimit : IsColimit cofork

namespace SelfCoequalizer

variable {D : SelfGluingData F} (P : SelfCoequalizer D)

/-- Swapping the two branches keeps the supplied coequalizer map and reverses its equation. -/
def swap : SelfCoequalizer D.swap where
  cofork := Cofork.ofπ P.cofork.π P.cofork.condition.symm
  isColimit := Cofork.IsColimit.mk _
    (fun s ↦ P.isColimit.desc (Cofork.ofπ s.π s.condition.symm))
    (fun s ↦ P.isColimit.fac (Cofork.ofπ s.π s.condition.symm) WalkingParallelPair.one)
    (fun s m hm ↦ by
      apply Cofork.IsColimit.hom_ext P.isColimit
      exact hm.trans
        (P.isColimit.fac (Cofork.ofπ s.π s.condition.symm) WalkingParallelPair.one).symm)

/-- Equal evaluations descend the source map through the chosen coequalizer. -/
def targetMap : P.cofork.pt ⟶ V :=
  Cofork.IsColimit.desc P.isColimit F.map D.evaluation_eq

/-- The structure map descends because both selected markings are sections. -/
def toBase : P.cofork.pt ⟶ S :=
  Cofork.IsColimit.desc P.isColimit F.toBase (by
    rw [F.marking_toBase D.first, F.marking_toBase D.second])

@[reassoc (attr := simp)]
theorem π_targetMap : P.cofork.π ≫ P.targetMap = F.map :=
  Cofork.IsColimit.π_desc' P.isColimit _ _

@[reassoc (attr := simp)]
theorem π_toBase : P.cofork.π ≫ P.toBase = F.toBase :=
  Cofork.IsColimit.π_desc' P.isColimit _ _

/-- The self-glued target map is still over the base. -/
@[reassoc]
theorem targetMap_toBase : P.targetMap ≫ q = P.toBase := by
  apply Cofork.IsColimit.hom_ext P.isColimit
  rw [← Category.assoc, P.π_targetMap, F.map_toBase, P.π_toBase]

/-- Markings retained after the two self-glued markings are removed. -/
abbrev RemainingIndex (_P : SelfCoequalizer D) :=
  { i : I // i ≠ D.first ∧ i ≠ D.second }

def remainingMarking (i : P.RemainingIndex) : S ⟶ P.cofork.pt :=
  F.marking i.1 ≫ P.cofork.π

@[reassoc (attr := simp)]
theorem remainingMarking_toBase (i : P.RemainingIndex) :
    P.remainingMarking i ≫ P.toBase = 𝟙 S := by
  simpa [remainingMarking] using F.marking_toBase i.1

/-- Self-gluing as a marked-map diagram, conditional on a supplied categorical coequalizer. -/
def markedMap : MarkedMap q P.RemainingIndex where
  source := P.cofork.pt
  toBase := P.toBase
  marking := P.remainingMarking
  marking_toBase := P.remainingMarking_toBase
  map := P.targetMap
  map_toBase := P.targetMap_toBase

@[simp]
theorem markedMap_source : P.markedMap.source = P.cofork.pt := rfl

@[simp]
theorem markedMap_map : P.markedMap.map = P.targetMap := rfl

@[simp]
theorem markedMap_toBase : P.markedMap.toBase = P.toBase := rfl

@[simp]
theorem markedMap_evaluation (i : P.RemainingIndex) :
    P.markedMap.evaluation i = F.evaluation i.1 := by
  simp only [MarkedMap.evaluation, markedMap, remainingMarking, Category.assoc, P.π_targetMap]

/-- The self-glued target map is uniquely determined by its pullback to the old source. -/
theorem targetMap_unique (f : P.cofork.pt ⟶ V) (hF : P.cofork.π ≫ f = F.map) :
    f = P.targetMap := by
  apply Cofork.IsColimit.hom_ext P.isColimit
  rw [hF, P.π_targetMap]

/-- The descended structure map is uniquely determined by its pullback to the old source. -/
theorem toBase_unique (f : P.cofork.pt ⟶ S) (hF : P.cofork.π ≫ f = F.toBase) :
    f = P.toBase := by
  apply Cofork.IsColimit.hom_ext P.isColimit
  rw [hF, P.π_toBase]

/-- Swapping the two branches leaves the descended target map unchanged. -/
@[simp]
lemma swap_targetMap : P.swap.targetMap = P.targetMap := by
  apply P.targetMap_unique
  exact P.swap.π_targetMap

/-- Swapping the two branches leaves the descended structure map unchanged. -/
@[simp]
lemma swap_toBase : P.swap.toBase = P.toBase := by
  apply Cofork.IsColimit.hom_ext P.isColimit
  change P.swap.cofork.π ≫ P.swap.toBase = P.cofork.π ≫ P.toBase
  rw [P.swap.π_toBase, P.π_toBase]

/-- Swapping the two branches exchanges the two exclusion proofs but leaves each retained
marking itself fixed. -/
def swapRemainingIndexEquiv : P.RemainingIndex ≃ P.swap.RemainingIndex where
  toFun i := ⟨i.1, i.2.2, i.2.1⟩
  invFun i := ⟨i.1, i.2.2, i.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma swapRemainingIndexEquiv_apply (i : P.RemainingIndex) :
    (P.swapRemainingIndexEquiv i).1 = i.1 := rfl

/-- After the canonical reindexing of retained markings, swapping the two branches does not
change the supplied self-glued marked map. -/
def swapMarkedMapIso :
    P.markedMap ≅ P.swap.markedMap.reindex P.swapRemainingIndexEquiv where
  hom :=
    { hom := 𝟙 _
      over_base := by
        change 𝟙 _ ≫ P.swap.toBase = P.toBase
        rw [Category.id_comp, swap_toBase]
      marking_comm := by
        intro i
        change P.remainingMarking i ≫ 𝟙 _ =
          P.swap.remainingMarking (P.swapRemainingIndexEquiv i)
        rw [Category.comp_id]
        rfl
      map_comm := by
        change 𝟙 _ ≫ P.swap.targetMap = P.targetMap
        rw [Category.id_comp, swap_targetMap] }
  inv :=
    { hom := 𝟙 _
      over_base := by
        change 𝟙 _ ≫ P.toBase = P.swap.toBase
        rw [Category.id_comp, swap_toBase]
      marking_comm := by
        intro i
        change P.swap.remainingMarking (P.swapRemainingIndexEquiv i) ≫ 𝟙 _ =
          P.remainingMarking i
        rw [Category.comp_id]
        rfl
      map_comm := by
        change 𝟙 _ ≫ P.targetMap = P.swap.targetMap
        rw [Category.id_comp, swap_targetMap] }
  hom_inv_id := by
    apply Hom.ext
    exact Category.id_comp _
  inv_hom_id := by
    apply Hom.ext
    exact Category.comp_id _

/-- Swapping self-gluing branches preserves every retained evaluation after the canonical
reindexing. -/
@[simp]
lemma swapMarkedMap_evaluation (i : P.RemainingIndex) :
    (P.swap.markedMap.reindex P.swapRemainingIndexEquiv).evaluation i =
      P.markedMap.evaluation i :=
  (evaluation_naturality P.swapMarkedMapIso.hom i).symm

/-- The canonical isomorphism between the vertices of two supplied coequalizer witnesses. -/
def comparisonIso (P Q : SelfCoequalizer D) : P.cofork.pt ≅ Q.cofork.pt :=
  P.isColimit.coconePointUniqueUpToIso Q.isColimit

@[reassoc (attr := simp)]
lemma π_comparisonIso_hom (P Q : SelfCoequalizer D) :
    P.cofork.π ≫ (comparisonIso P Q).hom = Q.cofork.π :=
  IsColimit.comp_coconePointUniqueUpToIso_hom P.isColimit Q.isColimit
    WalkingParallelPair.one

/-- The canonical comparison intertwines the descended target maps. -/
@[reassoc]
lemma comparisonIso_hom_targetMap (P Q : SelfCoequalizer D) :
    (comparisonIso P Q).hom ≫ Q.targetMap = P.targetMap := by
  apply P.targetMap_unique
  rw [π_comparisonIso_hom_assoc, Q.π_targetMap]

/-- The canonical comparison intertwines the descended structure maps. -/
@[reassoc]
lemma comparisonIso_hom_toBase (P Q : SelfCoequalizer D) :
    (comparisonIso P Q).hom ≫ Q.toBase = P.toBase := by
  apply P.toBase_unique
  rw [π_comparisonIso_hom_assoc, Q.π_toBase]

/-- The canonical comparison carries every retained marking to the corresponding marking. -/
@[reassoc]
lemma remainingMarking_comparisonIso_hom (P Q : SelfCoequalizer D)
    (i : P.RemainingIndex) :
    P.remainingMarking i ≫ (comparisonIso P Q).hom = Q.remainingMarking i := by
  simp [remainingMarking, Category.assoc]

/-- The marked maps obtained from any two supplied coequalizer witnesses are canonically
isomorphic. -/
def markedMapIso (P Q : SelfCoequalizer D) : P.markedMap ≅ Q.markedMap where
  hom :=
    { hom := (comparisonIso P Q).hom
      over_base := comparisonIso_hom_toBase P Q
      marking_comm := remainingMarking_comparisonIso_hom P Q
      map_comm := comparisonIso_hom_targetMap P Q }
  inv :=
    { hom := (comparisonIso P Q).inv
      over_base := by
        change (comparisonIso P Q).inv ≫ P.toBase = Q.toBase
        rw [← comparisonIso_hom_toBase P Q, ← Category.assoc,
          (comparisonIso P Q).inv_hom_id, Category.id_comp]
      marking_comm := by
        intro i
        change Q.remainingMarking i ≫ (comparisonIso P Q).inv = P.remainingMarking i
        rw [← remainingMarking_comparisonIso_hom P Q i, Category.assoc,
          (comparisonIso P Q).hom_inv_id, Category.comp_id]
      map_comm := by
        change (comparisonIso P Q).inv ≫ P.targetMap = Q.targetMap
        rw [← comparisonIso_hom_targetMap P Q, ← Category.assoc,
          (comparisonIso P Q).inv_hom_id, Category.id_comp] }
  hom_inv_id := by
    apply Hom.ext
    exact (comparisonIso P Q).hom_inv_id
  inv_hom_id := by
    apply Hom.ext
    exact (comparisonIso P Q).inv_hom_id

@[reassoc (attr := simp)]
lemma π_comparisonIso_inv (P Q : SelfCoequalizer D) :
    Q.cofork.π ≫ (comparisonIso P Q).inv = P.cofork.π :=
  IsColimit.comp_coconePointUniqueUpToIso_inv P.isColimit Q.isColimit
    WalkingParallelPair.one

@[simp]
lemma comparisonIso_refl_hom (P : SelfCoequalizer D) :
    (comparisonIso P P).hom = 𝟙 P.cofork.pt := by
  apply Cofork.IsColimit.hom_ext P.isColimit
  rw [π_comparisonIso_hom, Category.comp_id]

@[simp]
lemma comparisonIso_refl_inv (P : SelfCoequalizer D) :
    (comparisonIso P P).inv = 𝟙 P.cofork.pt := by
  change (comparisonIso P P).inv = (Iso.refl P.cofork.pt).inv
  rw [Iso.inv_eq_inv]
  exact comparisonIso_refl_hom P

lemma comparisonIso_symm_hom (P Q : SelfCoequalizer D) :
    (comparisonIso Q P).hom = (comparisonIso P Q).inv := by
  apply Cofork.IsColimit.hom_ext Q.isColimit
  rw [π_comparisonIso_hom, π_comparisonIso_inv]

lemma comparisonIso_trans_hom (P Q R : SelfCoequalizer D) :
    (comparisonIso P Q).hom ≫ (comparisonIso Q R).hom =
      (comparisonIso P R).hom := by
  apply Cofork.IsColimit.hom_ext P.isColimit
  simp

@[simp]
lemma comparisonIso_refl (P : SelfCoequalizer D) :
    comparisonIso P P = Iso.refl P.cofork.pt :=
  Iso.ext (comparisonIso_refl_hom P)

lemma comparisonIso_symm (P Q : SelfCoequalizer D) :
    (comparisonIso P Q).symm = comparisonIso Q P :=
  Iso.ext (comparisonIso_symm_hom P Q).symm

lemma comparisonIso_trans (P Q R : SelfCoequalizer D) :
    comparisonIso P Q ≪≫ comparisonIso Q R = comparisonIso P R :=
  Iso.ext (comparisonIso_trans_hom P Q R)

@[reassoc]
lemma comparisonIso_inv_targetMap (P Q : SelfCoequalizer D) :
    (comparisonIso P Q).inv ≫ P.targetMap = Q.targetMap := by
  rw [← comparisonIso_hom_targetMap P Q, ← Category.assoc,
    (comparisonIso P Q).inv_hom_id, Category.id_comp]

@[reassoc]
lemma comparisonIso_inv_toBase (P Q : SelfCoequalizer D) :
    (comparisonIso P Q).inv ≫ P.toBase = Q.toBase := by
  rw [← comparisonIso_hom_toBase P Q, ← Category.assoc,
    (comparisonIso P Q).inv_hom_id, Category.id_comp]

@[reassoc]
lemma remainingMarking_comparisonIso_inv (P Q : SelfCoequalizer D)
    (i : P.RemainingIndex) :
    Q.remainingMarking i ≫ (comparisonIso P Q).inv = P.remainingMarking i := by
  rw [← remainingMarking_comparisonIso_hom P Q i, Category.assoc,
    (comparisonIso P Q).hom_inv_id, Category.comp_id]

@[simp]
lemma markedMapIso_hom_hom (P Q : SelfCoequalizer D) :
    (markedMapIso P Q).hom.hom = (comparisonIso P Q).hom := rfl

@[simp]
lemma markedMapIso_inv_hom (P Q : SelfCoequalizer D) :
    (markedMapIso P Q).inv.hom = (comparisonIso P Q).inv := rfl

@[simp]
lemma markedMapIso_refl_hom (P : SelfCoequalizer D) :
    (markedMapIso P P).hom = 𝟙 P.markedMap := by
  apply Hom.ext
  exact comparisonIso_refl_hom P

lemma markedMapIso_symm_hom (P Q : SelfCoequalizer D) :
    (markedMapIso Q P).hom = (markedMapIso P Q).inv := by
  apply Hom.ext
  exact comparisonIso_symm_hom P Q

lemma markedMapIso_trans_hom (P Q R : SelfCoequalizer D) :
    (markedMapIso P Q).hom ≫ (markedMapIso Q R).hom =
      (markedMapIso P R).hom := by
  apply Hom.ext
  exact comparisonIso_trans_hom P Q R

@[simp]
lemma markedMapIso_refl (P : SelfCoequalizer D) :
    markedMapIso P P = Iso.refl P.markedMap :=
  Iso.ext (markedMapIso_refl_hom P)

lemma markedMapIso_symm (P Q : SelfCoequalizer D) :
    (markedMapIso P Q).symm = markedMapIso Q P :=
  Iso.ext (markedMapIso_symm_hom P Q).symm

lemma markedMapIso_trans (P Q R : SelfCoequalizer D) :
    markedMapIso P Q ≪≫ markedMapIso Q R = markedMapIso P R :=
  Iso.ext (markedMapIso_trans_hom P Q R)

end SelfCoequalizer

end

end GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap
