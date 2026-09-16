/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.DualGraph

/-!
# Combinatorial stability of unpointed nodal curves

These definitions state the dual-graph criteria that the geometric stability theory must
eventually be proved equivalent to.  Component genus is normalization genus and valence counts
branches, including both branches of a self-node.
-/

namespace GromovWitten.AlgebraicGeometry.Curves

namespace DualGraph

open scoped BigOperators

/-- Degree of the dualizing sheaf on a geometric component. -/
def canonicalDegree (G : DualGraph) (v : G.Vertex) : ℤ :=
  2 * (G.genus v : ℤ) - 2 + G.valence v

/-- A rational tail is a genus-zero component with one node branch. -/
def IsRationalTail (G : DualGraph) (v : G.Vertex) : Prop :=
  G.genus v = 0 ∧ G.valence v = 1

/-- A rational bridge is a genus-zero component with two node branches. -/
def IsRationalBridge (G : DualGraph) (v : G.Vertex) : Prop :=
  G.genus v = 0 ∧ G.valence v = 2

/-- Combinatorial semistability in the unpointed convention of the roadmap. -/
def IsSemistable (G : DualGraph) : Prop :=
  1 ≤ G.arithmeticGenus ∧ ∀ v, ¬ G.IsRationalTail v

/-- Combinatorial stability in the unpointed convention of the roadmap. -/
def IsStable (G : DualGraph) : Prop :=
  2 ≤ G.arithmeticGenus ∧ ∀ v, ¬ G.IsRationalTail v ∧ ¬ G.IsRationalBridge v

theorem canonicalDegree_eq_neg_one_of_isRationalTail (G : DualGraph) (v : G.Vertex)
    (h : G.IsRationalTail v) : G.canonicalDegree v = -1 := by
  simp [canonicalDegree, h.1, h.2]

theorem canonicalDegree_eq_zero_of_isRationalBridge (G : DualGraph) (v : G.Vertex)
    (h : G.IsRationalBridge v) : G.canonicalDegree v = 0 := by
  simp [canonicalDegree, h.1, h.2]

/-- The total canonical degree is `2g - 2`, expressed entirely in terms of the dual graph. -/
theorem sum_canonicalDegree (G : DualGraph) :
    ∑ v, G.canonicalDegree v = 2 * (G.arithmeticGenus : ℤ) - 2 := by
  have hEuler := G.firstBetti_add_card_vertex
  have hValence := G.sum_valence
  have hEulerZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hEuler
  have hValenceZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hValence
  simp only [canonicalDegree, arithmeticGenus]
  push_cast
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast at hEulerZ hValenceZ
  omega

@[simp]
theorem canonicalDegree_reindex (G : DualGraph.{u}) {V E : Type v}
    (vertexEquiv : G.Vertex ≃ V) (edgeEquiv : G.Edge ≃ E) (x : G.Vertex) :
    (G.reindex vertexEquiv edgeEquiv).canonicalDegree (vertexEquiv x) =
      G.canonicalDegree x := by
  simp [canonicalDegree, G.valence_reindex vertexEquiv edgeEquiv x]

@[simp]
theorem isRationalTail_reindex_iff (G : DualGraph.{u}) {V E : Type v}
    (vertexEquiv : G.Vertex ≃ V) (edgeEquiv : G.Edge ≃ E) (x : G.Vertex) :
    (G.reindex vertexEquiv edgeEquiv).IsRationalTail (vertexEquiv x) ↔
      G.IsRationalTail x := by
  simp [IsRationalTail, G.valence_reindex vertexEquiv edgeEquiv x]

@[simp]
theorem isRationalBridge_reindex_iff (G : DualGraph.{u}) {V E : Type v}
    (vertexEquiv : G.Vertex ≃ V) (edgeEquiv : G.Edge ≃ E) (x : G.Vertex) :
    (G.reindex vertexEquiv edgeEquiv).IsRationalBridge (vertexEquiv x) ↔
      G.IsRationalBridge x := by
  simp [IsRationalBridge, G.valence_reindex vertexEquiv edgeEquiv x]

@[simp]
theorem isSemistable_reindex_iff (G : DualGraph.{u}) {V E : Type v}
    (vertexEquiv : G.Vertex ≃ V) (edgeEquiv : G.Edge ≃ E) :
    (G.reindex vertexEquiv edgeEquiv).IsSemistable ↔ G.IsSemistable := by
  constructor
  · rintro ⟨hgenus, htail⟩
    refine ⟨?_, fun x hx ↦ ?_⟩
    · simpa using hgenus
    · exact htail (vertexEquiv x)
        ((G.isRationalTail_reindex_iff vertexEquiv edgeEquiv x).2 hx)
  · rintro ⟨hgenus, htail⟩
    refine ⟨?_, fun x hx ↦ ?_⟩
    · simpa using hgenus
    · obtain ⟨x, rfl⟩ := vertexEquiv.surjective x
      exact htail x ((G.isRationalTail_reindex_iff vertexEquiv edgeEquiv x).1 hx)

@[simp]
theorem isStable_reindex_iff (G : DualGraph.{u}) {V E : Type v}
    (vertexEquiv : G.Vertex ≃ V) (edgeEquiv : G.Edge ≃ E) :
    (G.reindex vertexEquiv edgeEquiv).IsStable ↔ G.IsStable := by
  constructor
  · rintro ⟨hgenus, hbad⟩
    refine ⟨?_, fun x ↦ ?_⟩
    · simpa using hgenus
    · constructor
      · intro hx
        exact (hbad (vertexEquiv x)).1
          ((G.isRationalTail_reindex_iff vertexEquiv edgeEquiv x).2 hx)
      · intro hx
        exact (hbad (vertexEquiv x)).2
          ((G.isRationalBridge_reindex_iff vertexEquiv edgeEquiv x).2 hx)
  · rintro ⟨hgenus, hbad⟩
    refine ⟨?_, fun x ↦ ?_⟩
    · simpa using hgenus
    · obtain ⟨x, rfl⟩ := vertexEquiv.surjective x
      constructor
      · intro hx
        exact (hbad x).1
          ((G.isRationalTail_reindex_iff vertexEquiv edgeEquiv x).1 hx)
      · intro hx
        exact (hbad x).2
          ((G.isRationalBridge_reindex_iff vertexEquiv edgeEquiv x).1 hx)

/-- For a connected unpointed dual graph in the stable genus range, excluding rational tails
and bridges is equivalent to positivity of the canonical degree on every component. -/
theorem isStable_iff_canonicalDegree_pos (G : DualGraph) :
    G.IsStable ↔ 2 ≤ G.arithmeticGenus ∧ ∀ v, 0 < G.canonicalDegree v := by
  constructor
  · rintro ⟨hgenus, hstable⟩
    refine ⟨hgenus, fun v ↦ ?_⟩
    by_cases hv0 : G.valence v = 0
    · have harith := G.arithmeticGenus_eq_genus_of_valence_eq_zero v hv0
      rw [harith] at hgenus
      simp only [canonicalDegree, hv0]
      omega
    · by_cases hg : G.genus v = 0
      · have ht := (hstable v).1
        have hb := (hstable v).2
        have hv1 : G.valence v ≠ 1 := fun hv ↦ ht ⟨hg, hv⟩
        have hv2 : G.valence v ≠ 2 := fun hv ↦ hb ⟨hg, hv⟩
        simp only [canonicalDegree, hg]
        omega
      · simp only [canonicalDegree]
        omega
  · rintro ⟨hgenus, hdegree⟩
    refine ⟨hgenus, fun v ↦ ⟨?_, ?_⟩⟩
    · intro ht
      have hv := hdegree v
      rw [G.canonicalDegree_eq_neg_one_of_isRationalTail v ht] at hv
      omega
    · intro hb
      have hv := hdegree v
      rw [G.canonicalDegree_eq_zero_of_isRationalBridge v hb] at hv
      omega

/-- Likewise, semistability is equivalent to nonnegative canonical degree in arithmetic
genus at least one. -/
theorem isSemistable_iff_canonicalDegree_nonneg (G : DualGraph) :
    G.IsSemistable ↔ 1 ≤ G.arithmeticGenus ∧ ∀ v, 0 ≤ G.canonicalDegree v := by
  constructor
  · rintro ⟨hgenus, hstable⟩
    refine ⟨hgenus, fun v ↦ ?_⟩
    by_cases hv0 : G.valence v = 0
    · have harith := G.arithmeticGenus_eq_genus_of_valence_eq_zero v hv0
      rw [harith] at hgenus
      simp only [canonicalDegree, hv0]
      omega
    · by_cases hg : G.genus v = 0
      · have hv1 : G.valence v ≠ 1 := fun hv ↦ hstable v ⟨hg, hv⟩
        simp only [canonicalDegree, hg]
        omega
      · simp only [canonicalDegree]
        omega
  · rintro ⟨hgenus, hdegree⟩
    refine ⟨hgenus, fun v ht ↦ ?_⟩
    have hv := hdegree v
    rw [G.canonicalDegree_eq_neg_one_of_isRationalTail v ht] at hv
    omega

/-- The dual graph of a smooth connected curve of genus `g`. -/
abbrev smooth (g : ℕ) : DualGraph.{0} where
  Vertex := Fin 1
  Edge := Fin 0
  endpoint := Fin.elim0
  genus := fun _ ↦ g
  connected := by
    intro v w
    fin_cases v
    fin_cases w
    exact Relation.ReflTransGen.refl

@[simp]
theorem smooth_arithmeticGenus (g : ℕ) : (smooth g).arithmeticGenus = g := by
  simp [arithmeticGenus, firstBetti, smooth]

/-- A smooth connected unpointed curve has a stable graph exactly in genus at least two. -/
theorem smooth_isStable_iff (g : ℕ) : (smooth g).IsStable ↔ 2 ≤ g := by
  rw [IsStable, smooth_arithmeticGenus]
  constructor
  · exact fun h ↦ h.1
  · intro hg
    refine ⟨hg, fun v ↦ ?_⟩
    fin_cases v
    constructor
    · rintro ⟨h, _⟩
      simp at h
      omega
    · rintro ⟨_, h⟩
      simp [valence, incident, smooth] at h

/-- A smooth genus-two curve is stable. -/
theorem smooth_genusTwo_stable : (smooth 2).IsStable := by
  constructor
  · simp
  · intro v
    fin_cases v
    constructor <;> simp [IsRationalTail, IsRationalBridge, valence, incident, smooth]

/-- For two components meeting in one node, unpointed stability holds exactly when neither
component is rational.  A rational component would be a rational tail. -/
theorem twoVerticesOneEdge_isStable_iff (g₀ g₁ : ℕ) :
    (twoVerticesOneEdge g₀ g₁).IsStable ↔ 0 < g₀ ∧ 0 < g₁ := by
  constructor
  · intro h
    constructor
    · apply Nat.pos_of_ne_zero
      intro hg
      exact (h.2 0).1 ⟨by simp [hg], by simp⟩
    · apply Nat.pos_of_ne_zero
      intro hg
      exact (h.2 1).1 ⟨by simp [hg], by simp⟩
  · rintro ⟨hg₀, hg₁⟩
    constructor
    · rw [twoVerticesOneEdge_arithmeticGenus]
      omega
    · intro v
      fin_cases v
      · constructor
        · rintro ⟨h, _⟩
          simp at h
          omega
        · rintro ⟨_, h⟩
          simp at h
      · constructor
        · rintro ⟨h, _⟩
          simp at h
          omega
        · rintro ⟨_, h⟩
          simp at h

/-- A rational cycle is semistable: every component has valence two, so there are no tails,
and equal vertex/edge counts give arithmetic genus one. -/
theorem rationalCycle_semistable (G : DualGraph)
    (hgenus : ∀ v, G.genus v = 0) (hvalence : ∀ v, G.valence v = 2)
    (hcard : Fintype.card G.Edge = Fintype.card G.Vertex) : G.IsSemistable := by
  constructor
  · rw [G.arithmeticGenus_eq_one_of_cycle hcard hgenus]
  · intro v htail
    rcases htail with ⟨_, hv⟩
    rw [hvalence v] at hv
    omega

/-- The same rational cycle is not an unpointed stable curve. -/
theorem rationalCycle_not_stable (G : DualGraph)
    (hgenus : ∀ v, G.genus v = 0)
    (hcard : Fintype.card G.Edge = Fintype.card G.Vertex) : ¬ G.IsStable := by
  intro h
  have hg := G.arithmeticGenus_eq_one_of_cycle hcard hgenus
  have htwo := h.1
  rw [hg] at htwo
  omega

/-- Full graph-level acceptance statement for a cycle of rational components.  The vertex
carrier is nonempty by the definition of `DualGraph`; valence two forces equal edge and vertex
counts, so the cycle has arithmetic genus one, is semistable, and is not stable. -/
theorem rationalCycle_acceptance (G : DualGraph)
    (hgenus : ∀ v, G.genus v = 0) (hvalence : ∀ v, G.valence v = 2) :
    G.arithmeticGenus = 1 ∧
      G.IsSemistable ∧
      ¬ G.IsStable ∧
      ∀ v, G.canonicalDegree v = 0 := by
  have hcard := G.card_edge_eq_card_vertex_of_valence_eq_two hvalence
  have harith := G.arithmeticGenus_eq_one_of_cycle hcard hgenus
  refine ⟨harith, G.rationalCycle_semistable hgenus hvalence hcard,
    G.rationalCycle_not_stable hgenus hcard, ?_⟩
  intro v
  simp [canonicalDegree, hgenus v, hvalence v]

theorem oneLoop_semistable : oneLoop.IsSemistable := by
  apply rationalCycle_semistable
  · simp [oneLoop]
  · intro v
    fin_cases v
    exact oneLoop_valence
  · decide

theorem oneLoop_not_stable : ¬ oneLoop.IsStable := by
  apply rationalCycle_not_stable
  · simp [oneLoop]
  · decide

end DualGraph

end GromovWitten.AlgebraicGeometry.Curves
