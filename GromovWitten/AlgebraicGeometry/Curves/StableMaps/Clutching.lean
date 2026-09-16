/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableMaps.DecoratedGraph

/-!
# Clutching decorated dual graphs

This file gives the graph-level counterparts of the two clutching operations.  External gluing
joins two graphs at a chosen leg of each graph.  Self-gluing joins two distinct legs of one graph
and may therefore create a loop.  In both constructions the chosen legs are consumed and replaced
by the two half-edges of one new edge.
-/

namespace GromovWitten.AlgebraicGeometry.Curves.StableMaps

open GromovWitten.AlgebraicGeometry.Curves
open scoped BigOperators

universe u

namespace DecoratedGraph

private abbrev ExternalVertex (G H : DecoratedGraph.{u}) :=
  G.toDualGraph.Vertex ⊕ H.toDualGraph.Vertex

private abbrev ExternalEdge (G H : DecoratedGraph.{u}) :=
  (G.toDualGraph.Edge ⊕ H.toDualGraph.Edge) ⊕ Unit

private def externalEndpoint (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg) :
    ExternalEdge G H → Fin 2 → ExternalVertex G H
  | .inl (.inl e), k => .inl (G.toDualGraph.endpoint e k)
  | .inl (.inr e), k => .inr (H.toDualGraph.endpoint e k)
  | .inr _, k => if k = 0 then .inl (G.legVertex i) else .inr (H.legVertex j)

private def externalAdjacent (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg)
    (v w : ExternalVertex G H) : Prop :=
  ∃ e, (externalEndpoint G H i j e 0 = v ∧ externalEndpoint G H i j e 1 = w) ∨
    (externalEndpoint G H i j e 0 = w ∧ externalEndpoint G H i j e 1 = v)

private lemma externalConnected (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg) :
    ∀ v w, Relation.ReflTransGen (externalAdjacent G H i j) v w := by
  have liftG : ∀ a b, Relation.ReflTransGen (externalAdjacent G H i j) (.inl a) (.inl b) := by
    intro a b
    apply (G.toDualGraph.connected a b).lift Sum.inl
    intro x y hxy
    rcases hxy with ⟨e, h | h⟩
    · exact ⟨.inl (.inl e), Or.inl (by simpa [externalEndpoint] using h)⟩
    · exact ⟨.inl (.inl e), Or.inr (by simpa [externalEndpoint] using h)⟩
  have liftH : ∀ a b, Relation.ReflTransGen (externalAdjacent G H i j) (.inr a) (.inr b) := by
    intro a b
    apply (H.toDualGraph.connected a b).lift Sum.inr
    intro x y hxy
    rcases hxy with ⟨e, h | h⟩
    · exact ⟨.inl (.inr e), Or.inl (by simpa [externalEndpoint] using h)⟩
    · exact ⟨.inl (.inr e), Or.inr (by simpa [externalEndpoint] using h)⟩
  have bridge : externalAdjacent G H i j (.inl (G.legVertex i)) (.inr (H.legVertex j)) := by
    refine ⟨.inr (), Or.inl ⟨?_, ?_⟩⟩ <;> simp [externalEndpoint]
  intro v w
  rcases v with a | a <;> rcases w with b | b
  · exact liftG a b
  · exact (liftG a (G.legVertex i)).trans <|
      (Relation.ReflTransGen.single bridge).trans (liftH (H.legVertex j) b)
  · exact (liftH a (H.legVertex j)).trans <|
      (Relation.ReflTransGen.single (by
        refine ⟨.inr (), Or.inr ⟨?_, ?_⟩⟩ <;> simp [externalEndpoint])).trans
        (liftG (G.legVertex i) b)
  · exact liftH a b

/-- External clutching: consume `i` and `j` and add one edge between their incident vertices. -/
def externalGlue (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg) : DecoratedGraph.{u} where
  toDualGraph :=
    { Vertex := ExternalVertex G H
      Edge := ExternalEdge G H
      endpoint := externalEndpoint G H i j
      genus := Sum.elim G.toDualGraph.genus H.toDualGraph.genus
      connected := externalConnected G H i j }
  Leg := { k : G.Leg // k ≠ i } ⊕ { k : H.Leg // k ≠ j }
  legVertex := Sum.elim (fun k ↦ .inl (G.legVertex k)) (fun k ↦ .inr (H.legVertex k))
  degree := Sum.elim G.degree H.degree

private abbrev SelfEdge (G : DecoratedGraph.{u}) := G.toDualGraph.Edge ⊕ Unit

private def selfEndpoint (G : DecoratedGraph.{u}) (i j : G.Leg) :
    SelfEdge G → Fin 2 → G.toDualGraph.Vertex
  | .inl e, k => G.toDualGraph.endpoint e k
  | .inr _, k => if k = 0 then G.legVertex i else G.legVertex j

private def selfAdjacent (G : DecoratedGraph.{u}) (i j : G.Leg)
    (v w : G.toDualGraph.Vertex) : Prop :=
  ∃ e, (selfEndpoint G i j e 0 = v ∧ selfEndpoint G i j e 1 = w) ∨
    (selfEndpoint G i j e 0 = w ∧ selfEndpoint G i j e 1 = v)

private lemma selfConnected (G : DecoratedGraph.{u}) (i j : G.Leg) :
    ∀ v w, Relation.ReflTransGen (selfAdjacent G i j) v w := by
  intro v w
  apply (G.toDualGraph.connected v w).lift id
  intro x y hxy
  rcases hxy with ⟨e, h | h⟩
  · exact ⟨.inl e, Or.inl (by simpa [selfEndpoint] using h)⟩
  · exact ⟨.inl e, Or.inr (by simpa [selfEndpoint] using h)⟩

/-- Self-clutching: consume two distinct legs and add an edge between their incident vertices.
The endpoints may lie on the same vertex, in which case this edge is a loop. -/
def selfGlue (G : DecoratedGraph.{u}) (i j : G.Leg) (_hij : i ≠ j) : DecoratedGraph.{u} where
  toDualGraph :=
    { Vertex := G.toDualGraph.Vertex
      Edge := SelfEdge G
      endpoint := selfEndpoint G i j
      genus := G.toDualGraph.genus
      connected := selfConnected G i j }
  Leg := { k : G.Leg // k ≠ i ∧ k ≠ j }
  legVertex k := G.legVertex k
  degree := G.degree

@[simp]
lemma externalGlue_newEdge_endpoint_zero (G H : DecoratedGraph.{u})
    (i : G.Leg) (j : H.Leg) :
    (externalGlue G H i j).toDualGraph.endpoint (.inr ()) 0 = .inl (G.legVertex i) := by
  simp [externalGlue, externalEndpoint]

@[simp]
lemma externalGlue_newEdge_endpoint_one (G H : DecoratedGraph.{u})
    (i : G.Leg) (j : H.Leg) :
    (externalGlue G H i j).toDualGraph.endpoint (.inr ()) 1 = .inr (H.legVertex j) := by
  simp [externalGlue, externalEndpoint]

@[simp]
lemma selfGlue_newEdge_endpoint_zero (G : DecoratedGraph.{u})
    (i j : G.Leg) (hij : i ≠ j) :
    (selfGlue G i j hij).toDualGraph.endpoint (.inr ()) 0 = G.legVertex i := by
  simp [selfGlue, selfEndpoint]

@[simp]
lemma selfGlue_newEdge_endpoint_one (G : DecoratedGraph.{u})
    (i j : G.Leg) (hij : i ≠ j) :
    (selfGlue G i j hij).toDualGraph.endpoint (.inr ()) 1 = G.legVertex j := by
  simp [selfGlue, selfEndpoint]

/-- The new self-gluing edge is a loop exactly when the two consumed legs lie on one vertex. -/
theorem selfGlue_newEdge_isLoop_iff (G : DecoratedGraph.{u})
    (i j : G.Leg) (hij : i ≠ j) :
    (selfGlue G i j hij).toDualGraph.endpoint (.inr ()) 0 =
      (selfGlue G i j hij).toDualGraph.endpoint (.inr ()) 1 ↔
      G.legVertex i = G.legVertex j := by
  rw [selfGlue_newEdge_endpoint_zero, selfGlue_newEdge_endpoint_one]
  rfl

@[simp]
lemma externalGlue_degree_inl (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg)
    (v : G.toDualGraph.Vertex) : (externalGlue G H i j).degree (.inl v) = G.degree v := rfl

@[simp]
lemma externalGlue_degree_inr (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg)
    (v : H.toDualGraph.Vertex) : (externalGlue G H i j).degree (.inr v) = H.degree v := rfl

@[simp]
lemma selfGlue_degree (G : DecoratedGraph.{u}) (i j : G.Leg) (hij : i ≠ j)
    (v : G.toDualGraph.Vertex) : (selfGlue G i j hij).degree v = G.degree v := rfl

@[simp]
lemma externalGlue_legVertex_inl (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg)
    (k : { k : G.Leg // k ≠ i }) :
    (externalGlue G H i j).legVertex (.inl k) = .inl (G.legVertex k) := rfl

@[simp]
lemma externalGlue_legVertex_inr (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg)
    (k : { k : H.Leg // k ≠ j }) :
    (externalGlue G H i j).legVertex (.inr k) = .inr (H.legVertex k) := rfl

@[simp]
lemma selfGlue_legVertex (G : DecoratedGraph.{u}) (i j : G.Leg) (hij : i ≠ j)
    (k : { k : G.Leg // k ≠ i ∧ k ≠ j }) :
    (selfGlue G i j hij).legVertex k = G.legVertex k := rfl

private abbrev Flag (G : DecoratedGraph.{u}) := G.toDualGraph.HalfEdge ⊕ G.Leg

private def flagVertex (G : DecoratedGraph.{u}) : Flag G → G.toDualGraph.Vertex
  | .inl h => h.vertex G.toDualGraph
  | .inr i => G.legVertex i

private def externalFlagTo (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg) :
    Flag (externalGlue G H i j) → Flag G ⊕ Flag H
  | .inl (.inl (.inl e), k) => .inl (.inl (e, k))
  | .inl (.inl (.inr e), k) => .inr (.inl (e, k))
  | .inl (.inr _, k) => if k = 0 then .inl (.inr i) else .inr (.inr j)
  | .inr (.inl k) => .inl (.inr k)
  | .inr (.inr k) => .inr (.inr k)

private def externalFlagInv (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg) :
    Flag G ⊕ Flag H → Flag (externalGlue G H i j)
  | .inl (.inl (e, k)) => .inl (.inl (.inl e), k)
  | .inr (.inl (e, k)) => .inl (.inl (.inr e), k)
  | .inl (.inr k) => if h : k = i then .inl (.inr (), 0) else .inr (.inl ⟨k, h⟩)
  | .inr (.inr k) => if h : k = j then .inl (.inr (), 1) else .inr (.inr ⟨k, h⟩)

private def externalFlagEquiv (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg) :
    Flag (externalGlue G H i j) ≃ Flag G ⊕ Flag H where
  toFun := externalFlagTo G H i j
  invFun := externalFlagInv G H i j
  left_inv x := by
    rcases x with h | k
    · rcases h with ⟨e, k⟩
      rcases e with (e | _)
      · rcases e with e | e <;> rfl
      · fin_cases k <;> simp [externalFlagTo, externalFlagInv]
    · rcases k with k | k
      · simp [externalFlagTo, externalFlagInv, k.property]
      · simp [externalFlagTo, externalFlagInv, k.property]
  right_inv x := by
    rcases x with x | x
    · rcases x with h | k
      · rfl
      · by_cases hk : k = i
        · subst k
          simp [externalFlagTo, externalFlagInv]
        · simp [externalFlagTo, externalFlagInv, hk]
    · rcases x with h | k
      · rfl
      · by_cases hk : k = j
        · subst k
          simp [externalFlagTo, externalFlagInv]
        · simp [externalFlagTo, externalFlagInv, hk]

@[simp]
private lemma externalFlagEquiv_apply (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg)
    (x : Flag (externalGlue G H i j)) :
    externalFlagEquiv G H i j x = externalFlagTo G H i j x := rfl

private def selfFlagTo (G : DecoratedGraph.{u}) (i j : G.Leg) (hij : i ≠ j) :
    Flag (selfGlue G i j hij) → Flag G
  | .inl (.inl e, k) => .inl (e, k)
  | .inl (.inr _, k) => if k = 0 then .inr i else .inr j
  | .inr k => .inr k.1

private def selfFlagInv (G : DecoratedGraph.{u}) (i j : G.Leg) (hij : i ≠ j) :
    Flag G → Flag (selfGlue G i j hij)
  | .inl (e, k) => .inl (.inl e, k)
  | .inr k => if hi : k = i then .inl (.inr (), 0) else
      if hj : k = j then .inl (.inr (), 1) else .inr ⟨k, hi, hj⟩

private def selfFlagEquiv (G : DecoratedGraph.{u}) (i j : G.Leg) (hij : i ≠ j) :
    Flag (selfGlue G i j hij) ≃ Flag G where
  toFun := selfFlagTo G i j hij
  invFun := selfFlagInv G i j hij
  left_inv x := by
    rcases x with h | k
    · rcases h with ⟨e, k⟩
      rcases e with e | _
      · rfl
      · fin_cases k
        · simp [selfFlagTo, selfFlagInv]
        · have hji : j ≠ i := Ne.symm hij
          simp [selfFlagTo, selfFlagInv, hji]
    · change selfFlagInv G i j hij (.inr k.1) = .inr k
      simp only [selfFlagInv, dif_neg k.property.1, dif_neg k.property.2]
      apply congrArg Sum.inr
      exact Subtype.ext rfl
  right_inv x := by
    rcases x with h | k
    · rfl
    · by_cases hi : k = i
      · subst k
        simp [selfFlagTo, selfFlagInv]
      · by_cases hj : k = j
        · subst k
          simp [selfFlagTo, selfFlagInv, hi]
        · simp [selfFlagTo, selfFlagInv, hi, hj]

@[simp]
private lemma selfFlagEquiv_apply (G : DecoratedGraph.{u}) (i j : G.Leg) (hij : i ≠ j)
    (x : Flag (selfGlue G i j hij)) :
    selfFlagEquiv G i j hij x = selfFlagTo G i j hij x := rfl

private lemma externalFlagEquiv_vertex (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg)
    (x : Flag (externalGlue G H i j)) :
    (externalGlue G H i j).flagVertex x =
      Sum.elim (fun y ↦ .inl (G.flagVertex y)) (fun y ↦ .inr (H.flagVertex y))
        (externalFlagTo G H i j x) := by
  rcases x with h | k
  · rcases h with ⟨e, k⟩
    rcases e with (e | _)
    · rcases e with e | e <;> rfl
    · fin_cases k <;>
        simp [flagVertex, externalFlagTo, externalGlue, externalEndpoint,
          DualGraph.HalfEdge.vertex]
  · rcases k with k | k <;> rfl

private lemma selfFlagEquiv_vertex (G : DecoratedGraph.{u}) (i j : G.Leg) (hij : i ≠ j)
    (x : Flag (selfGlue G i j hij)) :
    (selfGlue G i j hij).flagVertex x = G.flagVertex (selfFlagTo G i j hij x) := by
  rcases x with h | k
  · rcases h with ⟨e, k⟩
    rcases e with e | _
    · rfl
    · fin_cases k <;>
        simp [flagVertex, selfFlagTo, selfGlue, selfEndpoint,
          DualGraph.HalfEdge.vertex]
  · simp [flagVertex, selfFlagTo, selfGlue]

private abbrev FlagsAt (G : DecoratedGraph.{u}) (v : G.toDualGraph.Vertex) :=
  { x : Flag G // G.flagVertex x = v }

private noncomputable instance flagsAtFintype (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) : Fintype (FlagsAt G v) := Fintype.ofFinite _

private noncomputable def flagCard (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) : ℕ := Fintype.card (FlagsAt G v)

private lemma specialFlagCount_eq_card_flagsAt (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) :
    G.specialFlagCount v = flagCard G v := by
  unfold flagCard
  rw [specialFlagCount, DualGraph.valence, markingCount, DualGraph.incident, markingsAt]
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  rw [← Fintype.card_sum]
  exact (Fintype.card_congr (Equiv.subtypeSum (p := fun x : Flag G ↦ G.flagVertex x = v))).symm

private lemma flagCard_congr {G H : DecoratedGraph.{u}} {v : G.toDualGraph.Vertex}
    {w : H.toDualGraph.Vertex} (e : FlagsAt G v ≃ FlagsAt H w) :
    flagCard G v = flagCard H w := by
  unfold flagCard
  exact Fintype.card_congr e

private def sumFlagVertex (G H : DecoratedGraph.{u}) :
    Flag G ⊕ Flag H → G.toDualGraph.Vertex ⊕ H.toDualGraph.Vertex :=
  Sum.elim (fun x ↦ .inl (G.flagVertex x)) (fun x ↦ .inr (H.flagVertex x))

private abbrev ExternalFlagsAt (G H : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex ⊕ H.toDualGraph.Vertex) :=
  { x : Flag G ⊕ Flag H // sumFlagVertex G H x = v }

private def externalFlagsAtEquiv (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg)
    (v : G.toDualGraph.Vertex ⊕ H.toDualGraph.Vertex) :
    FlagsAt (externalGlue G H i j) v ≃ ExternalFlagsAt G H v where
  toFun x := ⟨externalFlagEquiv G H i j x, by
    rw [externalFlagEquiv_apply]
    change Sum.elim (fun y ↦ .inl (G.flagVertex y)) (fun y ↦ .inr (H.flagVertex y))
      (externalFlagTo G H i j x) = v
    exact (externalFlagEquiv_vertex G H i j x).symm.trans x.property⟩
  invFun x := ⟨(externalFlagEquiv G H i j).symm x, by
    rw [externalFlagEquiv_vertex]
    change sumFlagVertex G H (externalFlagEquiv G H i j
      ((externalFlagEquiv G H i j).symm x)) = v
    rw [(externalFlagEquiv G H i j).apply_symm_apply]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    change (externalFlagEquiv G H i j).symm (externalFlagTo G H i j x) = x
    rw [← externalFlagEquiv_apply]
    exact (externalFlagEquiv G H i j).symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    exact (externalFlagEquiv G H i j).apply_symm_apply x

private def externalFlagsAtInlEquiv (G H : DecoratedGraph.{u}) (v : G.toDualGraph.Vertex) :
    ExternalFlagsAt G H (.inl v) ≃ FlagsAt G v where
  toFun x := by
    rcases x with ⟨x | x, hx⟩
    · exact ⟨x, Sum.inl.inj hx⟩
    · cases hx
  invFun x := ⟨.inl x, congrArg Sum.inl x.property⟩
  left_inv x := by
    rcases x with ⟨x | x, hx⟩
    · rfl
    · cases hx
  right_inv _ := rfl

private def externalFlagsAtInrEquiv (G H : DecoratedGraph.{u}) (v : H.toDualGraph.Vertex) :
    ExternalFlagsAt G H (.inr v) ≃ FlagsAt H v where
  toFun x := by
    rcases x with ⟨x | x, hx⟩
    · cases hx
    · exact ⟨x, Sum.inr.inj hx⟩
  invFun x := ⟨.inr x, congrArg Sum.inr x.property⟩
  left_inv x := by
    rcases x with ⟨x | x, hx⟩
    · cases hx
    · rfl
  right_inv _ := rfl

private def selfFlagsAtEquiv (G : DecoratedGraph.{u}) (i j : G.Leg) (hij : i ≠ j)
    (v : G.toDualGraph.Vertex) : FlagsAt (selfGlue G i j hij) v ≃ FlagsAt G v where
  toFun x := ⟨selfFlagEquiv G i j hij x, by
    rw [selfFlagEquiv_apply, ← selfFlagEquiv_vertex]
    exact x.property⟩
  invFun x := ⟨(selfFlagEquiv G i j hij).symm x, by
    rw [selfFlagEquiv_vertex]
    change G.flagVertex (selfFlagEquiv G i j hij
      ((selfFlagEquiv G i j hij).symm x)) = v
    rw [(selfFlagEquiv G i j hij).apply_symm_apply]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    change (selfFlagEquiv G i j hij).symm (selfFlagTo G i j hij x) = x
    rw [← selfFlagEquiv_apply]
    exact (selfFlagEquiv G i j hij).symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    exact (selfFlagEquiv G i j hij).apply_symm_apply x

lemma externalGlue_specialFlagCount_inl (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg)
    (v : G.toDualGraph.Vertex) :
    (externalGlue G H i j).specialFlagCount (.inl v) = G.specialFlagCount v := by
  classical
  calc
    (externalGlue G H i j).specialFlagCount (.inl v) =
        flagCard (externalGlue G H i j) (.inl v) :=
      specialFlagCount_eq_card_flagsAt _ _
    _ = flagCard G v := flagCard_congr <|
      (externalFlagsAtEquiv G H i j (.inl v)).trans (externalFlagsAtInlEquiv G H v)
    _ = G.specialFlagCount v := (specialFlagCount_eq_card_flagsAt G v).symm

lemma externalGlue_specialFlagCount_inr (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg)
    (v : H.toDualGraph.Vertex) :
    (externalGlue G H i j).specialFlagCount (.inr v) = H.specialFlagCount v := by
  classical
  calc
    (externalGlue G H i j).specialFlagCount (.inr v) =
        flagCard (externalGlue G H i j) (.inr v) :=
      specialFlagCount_eq_card_flagsAt _ _
    _ = flagCard H v := flagCard_congr <|
      (externalFlagsAtEquiv G H i j (.inr v)).trans (externalFlagsAtInrEquiv G H v)
    _ = H.specialFlagCount v := (specialFlagCount_eq_card_flagsAt H v).symm

lemma selfGlue_specialFlagCount (G : DecoratedGraph.{u}) (i j : G.Leg) (hij : i ≠ j)
    (v : G.toDualGraph.Vertex) :
    (selfGlue G i j hij).specialFlagCount v = G.specialFlagCount v := by
  classical
  calc
    (selfGlue G i j hij).specialFlagCount v =
        flagCard (selfGlue G i j hij) v := specialFlagCount_eq_card_flagsAt _ _
    _ = flagCard G v := flagCard_congr (selfFlagsAtEquiv G i j hij v)
    _ = G.specialFlagCount v := (specialFlagCount_eq_card_flagsAt G v).symm

lemma externalGlue_logCanonicalDegree_inl (G H : DecoratedGraph.{u})
    (i : G.Leg) (j : H.Leg) (v : G.toDualGraph.Vertex) :
    (externalGlue G H i j).logCanonicalDegree (.inl v) = G.logCanonicalDegree v := by
  simp only [logCanonicalDegree, externalGlue_specialFlagCount_inl]
  rfl

lemma externalGlue_logCanonicalDegree_inr (G H : DecoratedGraph.{u})
    (i : G.Leg) (j : H.Leg) (v : H.toDualGraph.Vertex) :
    (externalGlue G H i j).logCanonicalDegree (.inr v) = H.logCanonicalDegree v := by
  simp only [logCanonicalDegree, externalGlue_specialFlagCount_inr]
  rfl

lemma selfGlue_logCanonicalDegree (G : DecoratedGraph.{u}) (i j : G.Leg) (hij : i ≠ j)
    (v : G.toDualGraph.Vertex) :
    (selfGlue G i j hij).logCanonicalDegree v = G.logCanonicalDegree v := by
  simp only [logCanonicalDegree, selfGlue_specialFlagCount]
  rfl

theorem externalGlue_isStableVertex_inl_iff (G H : DecoratedGraph.{u})
    (i : G.Leg) (j : H.Leg) (v : G.toDualGraph.Vertex) :
    (externalGlue G H i j).IsStableVertex (.inl v) ↔ G.IsStableVertex v := by
  simp only [IsStableVertex, externalGlue_degree_inl, externalGlue_logCanonicalDegree_inl]

theorem externalGlue_isStableVertex_inr_iff (G H : DecoratedGraph.{u})
    (i : G.Leg) (j : H.Leg) (v : H.toDualGraph.Vertex) :
    (externalGlue G H i j).IsStableVertex (.inr v) ↔ H.IsStableVertex v := by
  simp only [IsStableVertex, externalGlue_degree_inr, externalGlue_logCanonicalDegree_inr]

theorem selfGlue_isStableVertex_iff (G : DecoratedGraph.{u})
    (i j : G.Leg) (hij : i ≠ j) (v : G.toDualGraph.Vertex) :
    (selfGlue G i j hij).IsStableVertex v ↔ G.IsStableVertex v := by
  simp only [IsStableVertex, selfGlue_degree, selfGlue_logCanonicalDegree]

theorem externalGlue_isStable_iff (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg) :
    (externalGlue G H i j).IsStable ↔ G.IsStable ∧ H.IsStable := by
  constructor
  · intro h
    exact ⟨fun v ↦ (externalGlue_isStableVertex_inl_iff G H i j v).mp (h (.inl v)),
      fun v ↦ (externalGlue_isStableVertex_inr_iff G H i j v).mp (h (.inr v))⟩
  · rintro ⟨hG, hH⟩ (v | v)
    · exact (externalGlue_isStableVertex_inl_iff G H i j v).mpr (hG v)
    · exact (externalGlue_isStableVertex_inr_iff G H i j v).mpr (hH v)

theorem selfGlue_isStable_iff (G : DecoratedGraph.{u})
    (i j : G.Leg) (hij : i ≠ j) :
    (selfGlue G i j hij).IsStable ↔ G.IsStable := by
  constructor
  · intro h v
    exact (selfGlue_isStableVertex_iff G i j hij v).mp (h v)
  · intro h v
    exact (selfGlue_isStableVertex_iff G i j hij v).mpr (h v)

theorem externalGlue_totalDegree (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg) :
    (externalGlue G H i j).totalDegree = G.totalDegree + H.totalDegree := by
  change (∑ v : G.toDualGraph.Vertex ⊕ H.toDualGraph.Vertex,
    Sum.elim G.degree H.degree v) = (∑ v, G.degree v) + ∑ v, H.degree v
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]

theorem selfGlue_totalDegree (G : DecoratedGraph.{u}) (i j : G.Leg) (hij : i ≠ j) :
    (selfGlue G i j hij).totalDegree = G.totalDegree := rfl

/-- External gluing adds no graph genus.  Connectedness supplies the inequalities needed to remove
the truncated natural-number subtractions in the definition of `firstBetti`. -/
theorem externalGlue_arithmeticGenus (G H : DecoratedGraph.{u}) (i : G.Leg) (j : H.Leg) :
    (externalGlue G H i j).toDualGraph.arithmeticGenus =
      G.toDualGraph.arithmeticGenus + H.toDualGraph.arithmeticGenus := by
  have hG := G.toDualGraph.card_vertex_le_card_edge_add_one
  have hH := H.toDualGraph.card_vertex_le_card_edge_add_one
  change (∑ v : G.toDualGraph.Vertex ⊕ H.toDualGraph.Vertex,
      Sum.elim G.toDualGraph.genus H.toDualGraph.genus v) +
      (Fintype.card ((G.toDualGraph.Edge ⊕ H.toDualGraph.Edge) ⊕ Unit) + 1 -
        Fintype.card (G.toDualGraph.Vertex ⊕ H.toDualGraph.Vertex)) =
    ((∑ v, G.toDualGraph.genus v) +
      (Fintype.card G.toDualGraph.Edge + 1 - Fintype.card G.toDualGraph.Vertex)) +
    ((∑ v, H.toDualGraph.genus v) +
      (Fintype.card H.toDualGraph.Edge + 1 - Fintype.card H.toDualGraph.Vertex))
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.card_sum, Fintype.card_unique]
  omega

/-- Self-gluing adds one to graph genus. -/
theorem selfGlue_arithmeticGenus (G : DecoratedGraph.{u}) (i j : G.Leg) (hij : i ≠ j) :
    (selfGlue G i j hij).toDualGraph.arithmeticGenus =
      G.toDualGraph.arithmeticGenus + 1 := by
  have hG := G.toDualGraph.card_vertex_le_card_edge_add_one
  change (∑ v, G.toDualGraph.genus v) +
      (Fintype.card (G.toDualGraph.Edge ⊕ Unit) + 1 -
        Fintype.card G.toDualGraph.Vertex) =
    ((∑ v, G.toDualGraph.genus v) +
      (Fintype.card G.toDualGraph.Edge + 1 - Fintype.card G.toDualGraph.Vertex)) + 1
  simp only [Fintype.card_sum, Fintype.card_unique]
  omega

end DecoratedGraph

end GromovWitten.AlgebraicGeometry.Curves.StableMaps
