/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib

/-!
# Dual graphs of nodal curves

The graph stores half-edges explicitly through a two-ended edge map.  Consequently a loop
contributes two to valence.  Vertices are required to be nonempty, preventing the empty graph
from masquerading as a genus-one connected curve through Euler characteristic arithmetic.
-/

namespace GromovWitten.AlgebraicGeometry.Curves

universe u v

noncomputable section

open scoped Sym2

/-- A finite connected dual graph with a normalization genus at each vertex. -/
structure DualGraph where
  Vertex : Type u
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  [vertexNonempty : Nonempty Vertex]
  Edge : Type u
  [edgeFintype : Fintype Edge]
  [edgeDecidableEq : DecidableEq Edge]
  endpoint : Edge → Fin 2 → Vertex
  genus : Vertex → ℕ
  connected : ∀ v w, Relation.ReflTransGen
    (fun v w ↦ ∃ e, (endpoint e 0 = v ∧ endpoint e 1 = w) ∨
      (endpoint e 0 = w ∧ endpoint e 1 = v)) v w

namespace DualGraph

instance (G : DualGraph) : Fintype G.Vertex := G.vertexFintype
instance (G : DualGraph) : DecidableEq G.Vertex := G.vertexDecidableEq
instance (G : DualGraph) : Nonempty G.Vertex := G.vertexNonempty
instance (G : DualGraph) : Fintype G.Edge := G.edgeFintype
instance (G : DualGraph) : DecidableEq G.Edge := G.edgeDecidableEq

/-- The underlying simple graph, obtained by discarding loops and forgetting parallel-edge
multiplicities.  This graph is used only for connectivity and cardinality arguments; valence
continues to be computed from half-edges in the original multigraph. -/
def underlyingSimpleGraph (G : DualGraph.{u}) : SimpleGraph G.Vertex where
  Adj v w := v ≠ w ∧ ∃ e, (G.endpoint e 0 = v ∧ G.endpoint e 1 = w) ∨
    (G.endpoint e 0 = w ∧ G.endpoint e 1 = v)
  symm := Std.Symm.mk fun (v w : G.Vertex)
      (h : v ≠ w ∧ ∃ e, (G.endpoint e 0 = v ∧ G.endpoint e 1 = w) ∨
        (G.endpoint e 0 = w ∧ G.endpoint e 1 = v)) ↦ by
    refine ⟨h.1.symm, ?_⟩
    obtain ⟨e, h | h⟩ := h.2
    · exact ⟨e, Or.inr h⟩
    · exact ⟨e, Or.inl h⟩
  loopless := Std.Irrefl.mk fun (v : G.Vertex)
      (h : v ≠ v ∧ ∃ e, (G.endpoint e 0 = v ∧ G.endpoint e 1 = v) ∨
        (G.endpoint e 0 = v ∧ G.endpoint e 1 = v)) ↦ by
    exact h.1 rfl

/-- Forgetting loops and parallel-edge multiplicities preserves connectivity. -/
theorem underlyingSimpleGraph_connected (G : DualGraph.{u}) :
    G.underlyingSimpleGraph.Connected := by
  let _ : Nonempty G.Vertex := G.vertexNonempty
  constructor
  intro v w
  rw [SimpleGraph.reachable_iff_reflTransGen]
  apply (G.connected v w).trans_induction_on
    (motive := fun {x y} _ ↦
      Relation.ReflTransGen G.underlyingSimpleGraph.Adj x y)
  · intro x
    exact Relation.ReflTransGen.refl
  · intro x y hxy
    by_cases h : x = y
    · subst y
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨h, hxy⟩
  · intro x y z hxy hyz ihxy ihyz
    exact ihxy.trans ihyz

private abbrev NonLoopEdge (G : DualGraph.{u}) :=
  { e : G.Edge // G.endpoint e 0 ≠ G.endpoint e 1 }

private def nonLoopEdgeToEdgeSet (G : DualGraph.{u}) :
    NonLoopEdge G → G.underlyingSimpleGraph.edgeSet := fun e ↦
  ⟨s(G.endpoint e 0, G.endpoint e 1), by
    rw [SimpleGraph.mem_edgeSet]
    simp only [underlyingSimpleGraph]
    exact ⟨e.2, e, Or.inl ⟨rfl, rfl⟩⟩⟩

private theorem nonLoopEdgeToEdgeSet_surjective (G : DualGraph.{u}) :
    Function.Surjective G.nonLoopEdgeToEdgeSet := by
  intro x
  rcases x with ⟨x, hx⟩
  induction x using Sym2.inductionOn with
  | _ v w =>
    rw [SimpleGraph.mem_edgeSet] at hx
    simp only [underlyingSimpleGraph] at hx
    obtain ⟨hvw, e, h | h⟩ := hx
    · refine ⟨⟨e, ?_⟩, ?_⟩
      · rw [h.1, h.2]
        exact hvw
      · apply Subtype.ext
        simp only [nonLoopEdgeToEdgeSet]
        rw [h.1, h.2]
    · refine ⟨⟨e, ?_⟩, ?_⟩
      · rw [h.1, h.2]
        exact hvw.symm
      · apply Subtype.ext
        simp only [nonLoopEdgeToEdgeSet]
        rw [h.1, h.2, Sym2.eq_swap]

/-- A finite connected multigraph has at least `|V| - 1` edges.  Loops and parallel edges can
only increase the edge count, so the standard simple-graph estimate applies. -/
theorem card_vertex_le_card_edge_add_one (G : DualGraph.{u}) :
    Fintype.card G.Vertex ≤ Fintype.card G.Edge + 1 := by
  have hconnected := G.underlyingSimpleGraph_connected
  have hsimple := hconnected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at hsimple
  have hsub : Nat.card (NonLoopEdge G) ≤ Nat.card G.Edge := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  apply hsimple.trans
  simpa only [Nat.card_eq_fintype_card] using Nat.add_le_add_right
    ((Nat.card_le_card_of_surjective G.nonLoopEdgeToEdgeSet
      G.nonLoopEdgeToEdgeSet_surjective).trans hsub) 1

/-- Reindex vertices and edges without changing the graph. -/
abbrev reindex (G : DualGraph.{u}) {V E : Type v}
    (vertexEquiv : G.Vertex ≃ V) (edgeEquiv : G.Edge ≃ E) : DualGraph.{v} := by
  let _ : Fintype V := Fintype.ofEquiv G.Vertex vertexEquiv
  let _ : DecidableEq V := Classical.decEq V
  let _ : Nonempty V := ⟨vertexEquiv (Classical.choice G.vertexNonempty)⟩
  let _ : Fintype E := Fintype.ofEquiv G.Edge edgeEquiv
  let _ : DecidableEq E := Classical.decEq E
  exact
    { Vertex := V
      Edge := E
      endpoint e k := vertexEquiv (G.endpoint (edgeEquiv.symm e) k)
      genus v := G.genus (vertexEquiv.symm v)
      connected v w := by
        let r : V → V → Prop := fun a b ↦ ∃ e : E,
          (vertexEquiv (G.endpoint (edgeEquiv.symm e) 0) = a ∧
              vertexEquiv (G.endpoint (edgeEquiv.symm e) 1) = b) ∨
            (vertexEquiv (G.endpoint (edgeEquiv.symm e) 0) = b ∧
              vertexEquiv (G.endpoint (edgeEquiv.symm e) 1) = a)
        change Relation.ReflTransGen r v w
        have h := (G.connected (vertexEquiv.symm v) (vertexEquiv.symm w)).lift
          vertexEquiv (p := r) (by
            intro a b hab
            obtain ⟨e, he⟩ := hab
            refine ⟨edgeEquiv e, ?_⟩
            rcases he with he | he
            · left
              constructor
              · simpa only [edgeEquiv.symm_apply_apply] using congrArg vertexEquiv he.1
              · simpa only [edgeEquiv.symm_apply_apply] using congrArg vertexEquiv he.2
            · right
              constructor
              · simpa only [edgeEquiv.symm_apply_apply] using congrArg vertexEquiv he.1
              · simpa only [edgeEquiv.symm_apply_apply] using congrArg vertexEquiv he.2)
        change Relation.ReflTransGen r
          (vertexEquiv (vertexEquiv.symm v)) (vertexEquiv (vertexEquiv.symm w)) at h
        simpa only [vertexEquiv.apply_symm_apply] using h }

@[simp]
lemma reindex_genus (G : DualGraph.{u}) {V E : Type v}
    (vertexEquiv : G.Vertex ≃ V) (edgeEquiv : G.Edge ≃ E) (x : V) :
    (G.reindex vertexEquiv edgeEquiv).genus x = G.genus (vertexEquiv.symm x) := rfl

/-- A half-edge is an edge together with one of its two ends. -/
abbrev HalfEdge (G : DualGraph) := G.Edge × Fin 2

/-- The vertex incident to a half-edge. -/
def HalfEdge.vertex (G : DualGraph) (h : G.HalfEdge) : G.Vertex := G.endpoint h.1 h.2

/-- Half-edges incident to a vertex.  A loop contributes both of its ends. -/
def incident (G : DualGraph) (v : G.Vertex) : Finset G.HalfEdge :=
  Finset.univ.filter fun h ↦ h.vertex G = v

/-- Valence, counted using half-edges so that a loop has contribution two. -/
def valence (G : DualGraph) (v : G.Vertex) : ℕ := (G.incident v).card

/-- An endpoint of an edge has positive valence. -/
theorem valence_pos_of_endpoint_eq (G : DualGraph) (e : G.Edge) (k : Fin 2)
    (v : G.Vertex) (h : G.endpoint e k = v) : 0 < G.valence v := by
  rw [valence, Finset.card_pos]
  refine ⟨(e, k), ?_⟩
  unfold incident
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, h⟩

/-- In a connected graph, a zero-valence vertex is the only vertex. -/
theorem eq_of_valence_eq_zero (G : DualGraph) (v : G.Vertex) (hv : G.valence v = 0)
    (w : G.Vertex) : w = v := by
  rcases (G.connected v w).cases_head with hvw | ⟨c, hvc, _⟩
  · exact hvw.symm
  · obtain ⟨e, h | h⟩ := hvc
    · have := G.valence_pos_of_endpoint_eq e 0 v h.1
      omega
    · have := G.valence_pos_of_endpoint_eq e 1 v h.2
      omega

/-- Relabelling vertices and edges preserves valence. -/
theorem valence_reindex (G : DualGraph.{u}) {V E : Type v}
    (vertexEquiv : G.Vertex ≃ V) (edgeEquiv : G.Edge ≃ E) (x : G.Vertex) :
    (G.reindex vertexEquiv edgeEquiv).valence (vertexEquiv x) = G.valence x := by
  classical
  unfold valence
  apply Finset.card_equiv (edgeEquiv.symm.prodCongr (Equiv.refl (Fin 2)))
  intro h
  change h ∈ (G.reindex vertexEquiv edgeEquiv).incident (vertexEquiv x) ↔
    (edgeEquiv.symm h.1, h.2) ∈ G.incident x
  unfold incident
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, HalfEdge.vertex]
  exact vertexEquiv.injective.eq_iff

/-- The handshaking identity for a dual multigraph.  It is phrased directly in terms of
half-edges, so loops contribute two exactly as required by the nodal normalization formula. -/
theorem sum_valence (G : DualGraph.{u}) :
    ∑ v, G.valence v = 2 * Fintype.card G.Edge := by
  change (∑ v, (Finset.univ.filter fun h : G.HalfEdge ↦ h.vertex G = v).card) = _
  rw [← Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset G.HalfEdge))
    (t := (Finset.univ : Finset G.Vertex)) (f := fun h ↦ h.vertex G) (by simp)]
  simp [Fintype.card_prod, Nat.mul_comm]

/-- A finite graph in which every vertex has valence two has equally many edges and vertices.
This is the numerical cycle condition, derived from the handshaking identity rather than
assumed separately. -/
theorem card_edge_eq_card_vertex_of_valence_eq_two (G : DualGraph)
    (hvalence : ∀ v, G.valence v = 2) :
    Fintype.card G.Edge = Fintype.card G.Vertex := by
  have hsum := G.sum_valence
  have hleft : ∑ v, G.valence v = 2 * Fintype.card G.Vertex := by
    simp [hvalence, Nat.mul_comm]
  rw [hleft] at hsum
  omega

/-- First Betti number of a finite connected graph, by Euler characteristic. -/
def firstBetti (G : DualGraph) : ℕ := Fintype.card G.Edge + 1 - Fintype.card G.Vertex

/-- Euler characteristic without truncated-subtraction ambiguity. -/
theorem firstBetti_add_card_vertex (G : DualGraph) :
    G.firstBetti + Fintype.card G.Vertex = Fintype.card G.Edge + 1 := by
  exact Nat.sub_add_cancel G.card_vertex_le_card_edge_add_one

/-- Arithmetic genus encoded by a connected genus-decorated dual graph. -/
def arithmeticGenus (G : DualGraph) : ℕ := ∑ v, G.genus v + G.firstBetti

/-- A connected graph with an isolated vertex has no other vertices or edges, so its
arithmetic genus is the genus decorating that vertex. -/
theorem arithmeticGenus_eq_genus_of_valence_eq_zero (G : DualGraph) (v : G.Vertex)
    (hv : G.valence v = 0) : G.arithmeticGenus = G.genus v := by
  have hvert : ∀ w : G.Vertex, w = v := G.eq_of_valence_eq_zero v hv
  have hedge : IsEmpty G.Edge := ⟨fun e ↦ by
    have he := G.valence_pos_of_endpoint_eq e 0 v (hvert (G.endpoint e 0))
    omega⟩
  have hcardE : Fintype.card G.Edge = 0 := @Fintype.card_eq_zero G.Edge _ hedge
  have hcardV : Fintype.card G.Vertex = 1 := Fintype.card_eq_one_iff.mpr ⟨v, hvert⟩
  have hsum : ∑ w, G.genus w = G.genus v := by
    rw [Finset.sum_eq_single v]
    · intro w _ hw
      exact (hw (hvert w)).elim
    · simp
  rw [arithmeticGenus, firstBetti, hsum, hcardE, hcardV]
  norm_num

@[simp]
theorem arithmeticGenus_reindex (G : DualGraph.{u}) {V E : Type v}
    (vertexEquiv : G.Vertex ≃ V) (edgeEquiv : G.Edge ≃ E) :
    (G.reindex vertexEquiv edgeEquiv).arithmeticGenus = G.arithmeticGenus := by
  let _ : Fintype V := Fintype.ofEquiv G.Vertex vertexEquiv
  let _ : Fintype E := Fintype.ofEquiv G.Edge edgeEquiv
  change (∑ x : V, G.genus (vertexEquiv.symm x)) +
      (Fintype.card E + 1 - Fintype.card V) =
    (∑ x : G.Vertex, G.genus x) +
      (Fintype.card G.Edge + 1 - Fintype.card G.Vertex)
  rw [vertexEquiv.symm.sum_comp]
  rw [Fintype.card_congr vertexEquiv, Fintype.card_congr edgeEquiv]

lemma arithmeticGenus_eq_sum_add (G : DualGraph) :
    G.arithmeticGenus = ∑ v, G.genus v + G.firstBetti := rfl

/-- A connected graph with equally many vertices and edges has first Betti number one. -/
lemma firstBetti_eq_one_of_card_eq (G : DualGraph)
    (h : Fintype.card G.Edge = Fintype.card G.Vertex) : G.firstBetti = 1 := by
  simp [firstBetti, h]

/-- A cycle of rational components has arithmetic genus one.  The hypotheses isolate the
two numerical facts supplied by the normalization graph of a cycle. -/
lemma arithmeticGenus_eq_one_of_cycle (G : DualGraph)
    (hcard : Fintype.card G.Edge = Fintype.card G.Vertex)
    (hgenus : ∀ v, G.genus v = 0) : G.arithmeticGenus = 1 := by
  simp [arithmeticGenus, firstBetti_eq_one_of_card_eq G hcard, hgenus]

/-- Joining two components by one transverse node does not add graph genus. -/
lemma arithmeticGenus_two_vertices_one_edge (G : DualGraph)
    (hv : Fintype.card G.Vertex = 2) (he : Fintype.card G.Edge = 1) :
    G.arithmeticGenus = ∑ v, G.genus v := by
  simp [arithmeticGenus, firstBetti, hv, he]

/-- The explicit dual graph of two components meeting transversely in one node. -/
abbrev twoVerticesOneEdge (g₀ g₁ : ℕ) : DualGraph.{0} where
  Vertex := Fin 2
  Edge := Fin 1
  endpoint := fun _ k ↦ k
  genus := ![g₀, g₁]
  connected := by
    intro v w
    by_cases h : v = w
    · subst w
      exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.single
      refine ⟨0, ?_⟩
      fin_cases v <;> fin_cases w <;> simp_all

@[simp] theorem twoVerticesOneEdge_valence_zero (g₀ g₁ : ℕ) :
    (twoVerticesOneEdge g₀ g₁).valence 0 = 1 := by rfl

@[simp] theorem twoVerticesOneEdge_valence_one (g₀ g₁ : ℕ) :
    (twoVerticesOneEdge g₀ g₁).valence 1 = 1 := by rfl

/-- A single separating node adds no graph genus: the arithmetic genus is the sum of the
two component genera. -/
@[simp] theorem twoVerticesOneEdge_arithmeticGenus (g₀ g₁ : ℕ) :
    (twoVerticesOneEdge g₀ g₁).arithmeticGenus = g₀ + g₁ := by
  simp [arithmeticGenus, firstBetti, twoVerticesOneEdge, Fin.sum_univ_two]

/-- The one-vertex, one-loop rational dual graph. -/
abbrev oneLoop : DualGraph.{0} where
  Vertex := Fin 1
  Edge := Fin 1
  endpoint := fun _ _ ↦ 0
  genus := fun _ ↦ 0
  connected := by
    intro v w
    fin_cases v
    fin_cases w
    exact Relation.ReflTransGen.refl

/-- Both ends of a loop are counted in its valence. -/
theorem oneLoop_valence : oneLoop.valence 0 = 2 := by decide

/-- A rational self-node contributes one to arithmetic genus. -/
theorem oneLoop_arithmeticGenus : oneLoop.arithmeticGenus = 1 := by decide

end DualGraph

end

end GromovWitten.AlgebraicGeometry.Curves
