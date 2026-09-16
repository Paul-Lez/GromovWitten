/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.DualGraph

/-!
# Decorated dual graphs for stable maps

This file implements the combinatorial part of Layers 10--11.  Degrees are degrees with
respect to a fixed polarization.  A vertex of degree zero represents a contracted component;
only such vertices must have positive log-canonical degree.  The equivalent polarized
inequality uses the standard coefficient three.
-/

namespace GromovWitten.AlgebraicGeometry.Curves.StableMaps

open GromovWitten.AlgebraicGeometry.Curves

universe u v

noncomputable section

/-- A dual graph decorated by marking legs and nonnegative polarization degrees. -/
structure DecoratedGraph where
  toDualGraph : DualGraph.{u}
  Leg : Type u
  [legFintype : Fintype Leg]
  [legDecidableEq : DecidableEq Leg]
  legVertex : Leg → toDualGraph.Vertex
  degree : toDualGraph.Vertex → ℕ

namespace DecoratedGraph

instance (G : DecoratedGraph) : Fintype G.Leg := G.legFintype
instance (G : DecoratedGraph) : DecidableEq G.Leg := G.legDecidableEq

/-- Simultaneously relabel vertices, edges, and marking legs. -/
abbrev reindex (G : DecoratedGraph.{u}) {V E L : Type v}
    (vertexEquiv : G.toDualGraph.Vertex ≃ V) (edgeEquiv : G.toDualGraph.Edge ≃ E)
    (legEquiv : G.Leg ≃ L) : DecoratedGraph.{v} := by
  let _ : Fintype L := Fintype.ofEquiv G.Leg legEquiv
  let _ : DecidableEq L := Classical.decEq L
  exact
    { toDualGraph := G.toDualGraph.reindex vertexEquiv edgeEquiv
      Leg := L
      legVertex l := vertexEquiv (G.legVertex (legEquiv.symm l))
      degree v := G.degree (vertexEquiv.symm v) }

@[simp]
theorem reindex_degree (G : DecoratedGraph.{u}) {V E L : Type v}
    (vertexEquiv : G.toDualGraph.Vertex ≃ V) (edgeEquiv : G.toDualGraph.Edge ≃ E)
    (legEquiv : G.Leg ≃ L) (x : G.toDualGraph.Vertex) :
    (G.reindex vertexEquiv edgeEquiv legEquiv).degree (vertexEquiv x) = G.degree x := by
  simp

/-- Marking legs incident to `v`. -/
def markingsAt (G : DecoratedGraph) (v : G.toDualGraph.Vertex) : Finset G.Leg :=
  Finset.univ.filter fun i ↦ G.legVertex i = v

/-- Number of markings on `v`. -/
def markingCount (G : DecoratedGraph) (v : G.toDualGraph.Vertex) : ℕ :=
  (G.markingsAt v).card

/-- Relabelling all three finite carriers preserves the number of markings at a vertex. -/
theorem markingCount_reindex (G : DecoratedGraph.{u}) {V E L : Type v}
    (vertexEquiv : G.toDualGraph.Vertex ≃ V) (edgeEquiv : G.toDualGraph.Edge ≃ E)
    (legEquiv : G.Leg ≃ L) (x : G.toDualGraph.Vertex) :
    (G.reindex vertexEquiv edgeEquiv legEquiv).markingCount (vertexEquiv x) =
      G.markingCount x := by
  classical
  let _ : Fintype L := Fintype.ofEquiv G.Leg legEquiv
  let _ : DecidableEq L := Classical.decEq L
  unfold markingCount markingsAt
  apply Finset.card_bij (fun l _ ↦ legEquiv.symm l)
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact vertexEquiv.injective hl
  · intro a ha b hb hab
    exact legEquiv.symm.injective hab
  · intro i hi
    refine ⟨legEquiv i, ?_, by simp⟩
    simp only [EmbeddingLike.apply_eq_iff_eq, Finset.mem_filter, Finset.mem_univ,
      Equiv.symm_apply_apply, true_and] at hi ⊢
    exact hi

/-- Every marking is incident to exactly one vertex. -/
theorem sum_markingCount (G : DecoratedGraph) :
    ∑ v, G.markingCount v = Fintype.card G.Leg := by
  change (∑ v, (Finset.univ.filter fun i : G.Leg ↦ G.legVertex i = v).card) = _
  rw [← Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset G.Leg))
    (t := (Finset.univ : Finset G.toDualGraph.Vertex))
    (f := G.legVertex) (by simp)]
  simp

/-- Node branches and markings on the normalized component. -/
def specialFlagCount (G : DecoratedGraph) (v : G.toDualGraph.Vertex) : ℕ :=
  G.toDualGraph.valence v + G.markingCount v

/-- Degree of the logarithmic dualizing sheaf on the normalized component. -/
def logCanonicalDegree (G : DecoratedGraph) (v : G.toDualGraph.Vertex) : ℤ :=
  2 * (G.toDualGraph.genus v : ℤ) - 2 + G.specialFlagCount v

/-- Degree of `ω(log markings) ⊗ F⁺L³` on a component. -/
def polarizedDegree (G : DecoratedGraph) (v : G.toDualGraph.Vertex) : ℤ :=
  G.logCanonicalDegree v + 3 * (G.degree v : ℤ)

/-- Log-canonical component degrees are invariant under relabelling. -/
theorem logCanonicalDegree_reindex (G : DecoratedGraph.{u}) {V E L : Type v}
    (vertexEquiv : G.toDualGraph.Vertex ≃ V) (edgeEquiv : G.toDualGraph.Edge ≃ E)
    (legEquiv : G.Leg ≃ L) (x : G.toDualGraph.Vertex) :
    (G.reindex vertexEquiv edgeEquiv legEquiv).logCanonicalDegree (vertexEquiv x) =
      G.logCanonicalDegree x := by
  simp only [logCanonicalDegree, specialFlagCount, Equiv.symm_apply_apply,
    DualGraph.valence_reindex, markingCount_reindex]

/-- Polarized component degrees are invariant under relabelling. -/
theorem polarizedDegree_reindex (G : DecoratedGraph.{u}) {V E L : Type v}
    (vertexEquiv : G.toDualGraph.Vertex ≃ V) (edgeEquiv : G.toDualGraph.Edge ≃ E)
    (legEquiv : G.Leg ≃ L) (x : G.toDualGraph.Vertex) :
    (G.reindex vertexEquiv edgeEquiv legEquiv).polarizedDegree (vertexEquiv x) =
      G.polarizedDegree x := by
  simp [polarizedDegree, logCanonicalDegree_reindex]

/-- Componentwise stable-map condition: contracted components have positive log degree. -/
def IsStableVertex (G : DecoratedGraph) (v : G.toDualGraph.Vertex) : Prop :=
  G.degree v = 0 → 0 < G.logCanonicalDegree v

/-- The abstract decorated graph of a stable map. -/
def IsStable (G : DecoratedGraph) : Prop := ∀ v, G.IsStableVertex v

/-- Stability of the pointed source, independent of map degree. -/
def IsPointedStable (G : DecoratedGraph) : Prop :=
  ∀ v, 0 < G.logCanonicalDegree v

lemma logCanonicalDegree_lowerBound (G : DecoratedGraph) (v : G.toDualGraph.Vertex) :
    -2 ≤ G.logCanonicalDegree v := by
  simp only [logCanonicalDegree]
  omega

lemma polarizedDegree_eq_logCanonicalDegree_of_degree_eq_zero
    (G : DecoratedGraph) (v : G.toDualGraph.Vertex) (h : G.degree v = 0) :
    G.polarizedDegree v = G.logCanonicalDegree v := by
  simp [polarizedDegree, h]

lemma polarizedDegree_pos_of_degree_pos (G : DecoratedGraph) (v : G.toDualGraph.Vertex)
    (h : 0 < G.degree v) : 0 < G.polarizedDegree v := by
  have hlog := G.logCanonicalDegree_lowerBound v
  simp only [polarizedDegree]
  exact_mod_cast (show 0 < G.logCanonicalDegree v + 3 * (G.degree v : ℤ) by omega)

/-- The component criterion agrees with positivity after adding three times map degree. -/
theorem isStableVertex_iff_polarizedDegree_pos (G : DecoratedGraph)
    (v : G.toDualGraph.Vertex) : G.IsStableVertex v ↔ 0 < G.polarizedDegree v := by
  by_cases hdegree : G.degree v = 0
  · simp [IsStableVertex, hdegree,
      G.polarizedDegree_eq_logCanonicalDegree_of_degree_eq_zero v hdegree]
  · constructor
    · intro _
      exact G.polarizedDegree_pos_of_degree_pos v (Nat.pos_of_ne_zero hdegree)
    · intro _ _
      contradiction

theorem isStable_iff_forall_polarizedDegree_pos (G : DecoratedGraph) :
    G.IsStable ↔ ∀ v, 0 < G.polarizedDegree v := by
  simp only [IsStable, G.isStableVertex_iff_polarizedDegree_pos]

/-- Stable-map graph stability is invariant under relabelling. -/
theorem isStable_reindex_iff (G : DecoratedGraph.{u}) {V E L : Type v}
    (vertexEquiv : G.toDualGraph.Vertex ≃ V) (edgeEquiv : G.toDualGraph.Edge ≃ E)
    (legEquiv : G.Leg ≃ L) :
    (G.reindex vertexEquiv edgeEquiv legEquiv).IsStable ↔ G.IsStable := by
  rw [isStable_iff_forall_polarizedDegree_pos, isStable_iff_forall_polarizedDegree_pos]
  constructor
  · intro h x
    rw [← G.polarizedDegree_reindex vertexEquiv edgeEquiv legEquiv x]
    exact h (vertexEquiv x)
  · intro h y
    have hy := h (vertexEquiv.symm y)
    have heq := G.polarizedDegree_reindex vertexEquiv edgeEquiv legEquiv
      (vertexEquiv.symm y)
    rw [vertexEquiv.apply_symm_apply] at heq
    rwa [heq]

lemma isStableVertex_of_degree_pos (G : DecoratedGraph) (v : G.toDualGraph.Vertex)
    (h : 0 < G.degree v) : G.IsStableVertex v := by
  intro hzero
  omega

theorem isStable_of_pointedStable (G : DecoratedGraph) (h : G.IsPointedStable) : G.IsStable :=
  fun v _ ↦ h v

theorem isStable_iff_pointedStable_of_degree_zero (G : DecoratedGraph)
    (hdegree : ∀ v, G.degree v = 0) : G.IsStable ↔ G.IsPointedStable := by
  simp [IsStable, IsStableVertex, IsPointedStable, hdegree]

/-- Replace the polarization degrees while leaving the pointed dual graph unchanged. -/
abbrev withDegree (G : DecoratedGraph) (d : G.toDualGraph.Vertex → ℕ) : DecoratedGraph :=
  { G with degree := d }

/-- Graph stability depends only on which components have degree zero.  Geometrically, ample
polarizations detect exactly the contracted components, so this is the combinatorial core of
independence from the chosen polarization. -/
theorem isStable_withDegree_iff (G : DecoratedGraph)
    (d : G.toDualGraph.Vertex → ℕ) (hzero : ∀ v, d v = 0 ↔ G.degree v = 0) :
    (G.withDegree d).IsStable ↔ G.IsStable := by
  simp only [IsStable, IsStableVertex]
  constructor
  · intro h v hv
    exact h v ((hzero v).2 hv)
  · intro h v hv
    exact h v ((hzero v).1 hv)

/-- Sharp graph-level criterion after a target operation changes component degrees: stability is
exactly positivity of the log-canonical degree on the new zero-degree locus.  This statement does
not assert that an arbitrary numerical degree function is induced by a target morphism. -/
theorem isStable_withDegree_iff_forall_zero_degree (G : DecoratedGraph)
    (d : G.toDualGraph.Vertex → ℕ) :
    (G.withDegree d).IsStable ↔
      ∀ v, d v = 0 → 0 < G.logCanonicalDegree v := by
  rfl

/-- If `G` is already stable, only components newly assigned degree zero can obstruct stability.
This is the sharp combinatorial criterion relevant to target postcomposition, which may contract
additional components. -/
theorem isStable_withDegree_iff_of_isStable (G : DecoratedGraph) (hG : G.IsStable)
    (d : G.toDualGraph.Vertex → ℕ) :
    (G.withDegree d).IsStable ↔
      ∀ v, d v = 0 → G.degree v ≠ 0 → 0 < G.logCanonicalDegree v := by
  rw [G.isStable_withDegree_iff_forall_zero_degree]
  constructor
  · intro h v hv _
    exact h v hv
  · intro h v hv
    by_cases hold : G.degree v = 0
    · exact hG v hold
    · exact h v hv hold

/-- Stability is preserved whenever the new zero-degree locus is contained in the old one.  In
particular, a target operation that does not contract any additional component preserves graph
stability. -/
theorem isStable_withDegree_of_zero_locus_subset (G : DecoratedGraph)
    (d : G.toDualGraph.Vertex → ℕ) (hzero : ∀ v, d v = 0 → G.degree v = 0)
    (hG : G.IsStable) : (G.withDegree d).IsStable := by
  rw [G.isStable_withDegree_iff_forall_zero_degree]
  intro v hv
  exact hG v (hzero v hv)

/-- Total polarization degree, as the sum of component degrees. -/
def totalDegree (G : DecoratedGraph) : ℕ := ∑ v, G.degree v

/-- Since component degrees are nonnegative, total degree vanishes exactly when every
component degree vanishes. -/
@[simp]
theorem totalDegree_eq_zero_iff (G : DecoratedGraph) :
    G.totalDegree = 0 ↔ ∀ v, G.degree v = 0 := by
  simp [totalDegree]

/-- In total degree zero, stable-map graph stability is exactly stability of the pointed
source graph. -/
theorem isStable_iff_pointedStable_of_totalDegree_zero (G : DecoratedGraph)
    (hdegree : G.totalDegree = 0) : G.IsStable ↔ G.IsPointedStable :=
  G.isStable_iff_pointedStable_of_degree_zero (G.totalDegree_eq_zero_iff.mp hdegree)

/-- Total degree is invariant under relabelling. -/
@[simp]
theorem totalDegree_reindex (G : DecoratedGraph.{u}) {V E L : Type v}
    (vertexEquiv : G.toDualGraph.Vertex ≃ V) (edgeEquiv : G.toDualGraph.Edge ≃ E)
    (legEquiv : G.Leg ≃ L) :
    (G.reindex vertexEquiv edgeEquiv legEquiv).totalDegree = G.totalDegree := by
  let _ : Fintype V := Fintype.ofEquiv G.toDualGraph.Vertex vertexEquiv
  change (∑ x : V, G.degree (vertexEquiv.symm x)) = ∑ x, G.degree x
  rw [vertexEquiv.symm.sum_comp]

/-- Summing the componentwise log-canonical formula gives the global pointed numerical
quantity `2g - 2 + n`. -/
theorem sum_logCanonicalDegree (G : DecoratedGraph) :
    ∑ v, G.logCanonicalDegree v =
      2 * (G.toDualGraph.arithmeticGenus : ℤ) - 2 + Fintype.card G.Leg := by
  have hEuler := G.toDualGraph.firstBetti_add_card_vertex
  have hValence := G.toDualGraph.sum_valence
  have hMarking := G.sum_markingCount
  have hEulerZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hEuler
  have hValenceZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hValence
  have hMarkingZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hMarking
  simp only [logCanonicalDegree, specialFlagCount, DualGraph.arithmeticGenus]
  push_cast
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast at hEulerZ hValenceZ hMarkingZ
  omega

/-- Summing polarized component degrees gives `2g - 2 + n + 3d`. -/
theorem sum_polarizedDegree (G : DecoratedGraph) :
    ∑ v, G.polarizedDegree v =
      2 * (G.toDualGraph.arithmeticGenus : ℤ) - 2 +
        Fintype.card G.Leg + 3 * G.totalDegree := by
  simp only [polarizedDegree, Finset.sum_add_distrib]
  rw [G.sum_logCanonicalDegree]
  rw [← Finset.mul_sum]
  simp [totalDegree]

/-- Pointed stability forces the roadmap's numerical non-emptiness condition. -/
theorem pointedStable_numerical_nonempty (G : DecoratedGraph) (h : G.IsPointedStable) :
    0 < 2 * (G.toDualGraph.arithmeticGenus : ℤ) - 2 + Fintype.card G.Leg := by
  rw [← G.sum_logCanonicalDegree]
  exact Finset.sum_pos (fun v _ ↦ h v) Finset.univ_nonempty

/-- Stable-map graph stability forces `2g - 2 + n + 3d > 0`. -/
theorem stable_numerical_nonempty (G : DecoratedGraph) (h : G.IsStable) :
    0 < 2 * (G.toDualGraph.arithmeticGenus : ℤ) - 2 +
      Fintype.card G.Leg + 3 * G.totalDegree := by
  rw [← G.sum_polarizedDegree]
  rw [G.isStable_iff_forall_polarizedDegree_pos] at h
  exact Finset.sum_pos (fun v _ ↦ h v) Finset.univ_nonempty

/-- There is no stable degree-zero genus-zero type with at most two markings. -/
theorem not_stable_of_genus_zero_degree_zero_card_legs_le_two (G : DecoratedGraph)
    (hgenus : G.toDualGraph.arithmeticGenus = 0) (hdegree : G.totalDegree = 0)
    (hlegs : Fintype.card G.Leg ≤ 2) : ¬ G.IsStable := by
  intro h
  have hn := G.stable_numerical_nonempty h
  rw [hgenus, hdegree] at hn
  norm_num at hn
  omega

/-- There is no stable degree-zero unmarked genus-one type. -/
theorem not_stable_of_genus_one_degree_zero_no_legs (G : DecoratedGraph)
    (hgenus : G.toDualGraph.arithmeticGenus = 1) (hdegree : G.totalDegree = 0)
    (hlegs : Fintype.card G.Leg = 0) : ¬ G.IsStable := by
  intro h
  have hn := G.stable_numerical_nonempty h
  rw [hgenus, hdegree, hlegs] at hn
  norm_num at hn

/-- Restrict or reindex the marking legs along a function. -/
abbrev restrictLegs (G : DecoratedGraph) (J : Type u) [Fintype J] [DecidableEq J]
    (f : J → G.Leg) : DecoratedGraph where
  toDualGraph := G.toDualGraph
  Leg := J
  legVertex := G.legVertex ∘ f
  degree := G.degree

/-- Forget a single marking leg without changing the underlying dual graph or map degrees. -/
abbrev forgetLeg (G : DecoratedGraph.{u}) (forgotten : G.Leg) : DecoratedGraph.{u} :=
  G.restrictLegs {i : G.Leg // i ≠ forgotten} Subtype.val

/-- The new marking count plus the indicator of the component carrying the forgotten marking is
the old marking count. -/
theorem markingCount_forgetLeg_add_indicator (G : DecoratedGraph.{u})
    (forgotten : G.Leg) (v : G.toDualGraph.Vertex) :
    (G.forgetLeg forgotten).markingCount v +
        (if G.legVertex forgotten = v then 1 else 0) = G.markingCount v := by
  classical
  let s : Finset {i : G.Leg // i ≠ forgotten} :=
    Finset.univ.filter fun i ↦ G.legVertex i = v
  have hcard : s.card = ((G.markingsAt v).erase forgotten).card := by
    apply Finset.card_bij (fun i _ ↦ i.1)
    · intro i hi
      exact Finset.mem_erase.mpr ⟨i.2, by
        simpa [markingsAt] using (Finset.mem_filter.mp hi).2⟩
    · intro i hi j hj hij
      exact Subtype.ext hij
    · intro i hi
      refine ⟨⟨i, (Finset.mem_erase.mp hi).1⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [markingsAt] using (Finset.mem_erase.mp hi).2⟩
  change s.card + (if G.legVertex forgotten = v then 1 else 0) =
    (G.markingsAt v).card
  rw [hcard]
  by_cases h : G.legVertex forgotten = v
  · have hmem : forgotten ∈ G.markingsAt v := by simp [markingsAt, h]
    rw [if_pos h, Finset.card_erase_of_mem hmem]
    exact Nat.sub_add_cancel (Finset.one_le_card.mpr ⟨forgotten, hmem⟩)
  · have hmem : forgotten ∉ G.markingsAt v := by simp [markingsAt, h]
    simp [h, hmem]

@[simp]
theorem degree_forgetLeg (G : DecoratedGraph.{u}) (forgotten : G.Leg)
    (v : G.toDualGraph.Vertex) :
    (G.forgetLeg forgotten).degree v = G.degree v := rfl

/-- Forgetting one marking lowers the log-canonical degree by one on its component and leaves all
other component degrees unchanged. -/
theorem logCanonicalDegree_forgetLeg_add_indicator (G : DecoratedGraph.{u})
    (forgotten : G.Leg) (v : G.toDualGraph.Vertex) :
    (G.forgetLeg forgotten).logCanonicalDegree v +
        (if G.legVertex forgotten = v then 1 else 0) =
      G.logCanonicalDegree v := by
  have hcount := G.markingCount_forgetLeg_add_indicator forgotten v
  simp only [logCanonicalDegree, specialFlagCount]
  by_cases h : G.legVertex forgotten = v
  · simp [h] at hcount ⊢
    omega
  · simp [h] at hcount ⊢
    omega

/-- Forgetting one marking makes the log-canonical degree nef when the original pointed graph
was stable. -/
theorem logCanonicalDegree_forgetLeg_nonneg (G : DecoratedGraph.{u})
    (forgotten : G.Leg) (hG : G.IsPointedStable) (v : G.toDualGraph.Vertex) :
    0 ≤ (G.forgetLeg forgotten).logCanonicalDegree v := by
  have hold := hG v
  have hdegree := G.logCanonicalDegree_forgetLeg_add_indicator forgotten v
  split at hdegree <;> omega

/-- Away from the component carrying the forgotten marking, log-canonical degree is unchanged. -/
theorem logCanonicalDegree_forgetLeg_of_ne (G : DecoratedGraph.{u})
    (forgotten : G.Leg) (v : G.toDualGraph.Vertex)
    (h : G.legVertex forgotten ≠ v) :
    (G.forgetLeg forgotten).logCanonicalDegree v = G.logCanonicalDegree v := by
  have hdegree := G.logCanonicalDegree_forgetLeg_add_indicator forgotten v
  simpa only [if_neg h, add_zero] using hdegree

/-- The component carrying the forgotten marking loses exactly one unit of log-canonical
degree. -/
theorem logCanonicalDegree_forgetLeg_at (G : DecoratedGraph.{u})
    (forgotten : G.Leg) :
    (G.forgetLeg forgotten).logCanonicalDegree (G.legVertex forgotten) + 1 =
      G.logCanonicalDegree (G.legVertex forgotten) := by
  simpa using G.logCanonicalDegree_forgetLeg_add_indicator forgotten
    (G.legVertex forgotten)

/-- Any zero log-canonical degree created by forgetting one marking lies on the unique component
that carried that marking. -/
theorem eq_legVertex_of_logCanonicalDegree_forgetLeg_eq_zero (G : DecoratedGraph.{u})
    (forgotten : G.Leg) (hG : G.IsPointedStable) (v : G.toDualGraph.Vertex)
    (hzero : (G.forgetLeg forgotten).logCanonicalDegree v = 0) :
    v = G.legVertex forgotten := by
  by_contra hne
  have heq := G.logCanonicalDegree_forgetLeg_of_ne forgotten v (Ne.symm hne)
  have hpos := hG v
  rw [hzero] at heq
  omega

/-- After one marking is forgotten, pointed stability survives exactly when the old degree on
its component was at least two. -/
theorem forgetLeg_isPointedStable_iff (G : DecoratedGraph.{u})
    (forgotten : G.Leg) (hG : G.IsPointedStable) :
    (G.forgetLeg forgotten).IsPointedStable ↔
      1 < G.logCanonicalDegree (G.legVertex forgotten) := by
  constructor
  · intro h
    have hnew := h (G.legVertex forgotten)
    have hat := G.logCanonicalDegree_forgetLeg_at forgotten
    omega
  · intro h v
    by_cases hv : G.legVertex forgotten = v
    · subst v
      have hat := G.logCanonicalDegree_forgetLeg_at forgotten
      omega
    · rw [G.logCanonicalDegree_forgetLeg_of_ne forgotten v hv]
      exact hG v

/-- If forgetting one marking destabilizes a pointed-stable graph, the resulting nef
log-canonical degree has exactly one zero-degree component. -/
theorem existsUnique_logCanonicalDegree_forgetLeg_eq_zero (G : DecoratedGraph.{u})
    (forgotten : G.Leg) (hG : G.IsPointedStable)
    (hunstable : ¬(G.forgetLeg forgotten).IsPointedStable) :
    ∃! v, (G.forgetLeg forgotten).logCanonicalDegree v = 0 := by
  have hnot : ¬1 < G.logCanonicalDegree (G.legVertex forgotten) := by
    exact fun h ↦ hunstable ((G.forgetLeg_isPointedStable_iff forgotten hG).2 h)
  have hpos := hG (G.legVertex forgotten)
  have hat := G.logCanonicalDegree_forgetLeg_at forgotten
  have hzero : (G.forgetLeg forgotten).logCanonicalDegree
      (G.legVertex forgotten) = 0 := by omega
  refine ⟨G.legVertex forgotten, hzero, ?_⟩
  intro v hv
  exact G.eq_legVertex_of_logCanonicalDegree_forgetLeg_eq_zero forgotten hG v hv

/-- The decorated graph of the normalization of the component indexed by `v`.

The normalized component has no internal edges.  Every branch of a node incident to `v`
becomes a marking leg, alongside the original marking legs lying on `v`.  Its genus and map
degree are inherited from `v`.  Using the actual finite fibres as the new leg types retains the
individual flags, rather than merely retaining their cardinality. -/
abbrev componentNormalization (G : DecoratedGraph.{u}) (v : G.toDualGraph.Vertex) :
    DecoratedGraph.{u} where
  toDualGraph :=
    { Vertex := {w : G.toDualGraph.Vertex // w = v}
      Edge := {e : G.toDualGraph.Edge // False}
      endpoint := fun e _ ↦ e.2.elim
      genus := fun _ ↦ G.toDualGraph.genus v
      connected := by
        intro w₀ w₁
        have hw : w₀ = w₁ := Subtype.ext (w₀.2.trans w₁.2.symm)
        subst w₁
        exact Relation.ReflTransGen.refl }
  Leg := (G.toDualGraph.incident v : Type u) ⊕ (G.markingsAt v : Type u)
  legVertex := fun _ ↦ ⟨v, rfl⟩
  degree := fun _ ↦ G.degree v

/-- The unique vertex of the normalized component graph. -/
abbrev componentNormalizationVertex (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) :
    (G.componentNormalization v).toDualGraph.Vertex := ⟨v, rfl⟩

@[simp]
theorem componentNormalization_genus (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) :
    (G.componentNormalization v).toDualGraph.genus (G.componentNormalizationVertex v) =
      G.toDualGraph.genus v := rfl

@[simp]
theorem componentNormalization_degree (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) :
    (G.componentNormalization v).degree (G.componentNormalizationVertex v) = G.degree v := rfl

@[simp]
theorem componentNormalization_valence (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) :
    (G.componentNormalization v).toDualGraph.valence (G.componentNormalizationVertex v) = 0 := by
  rw [DualGraph.valence, Finset.card_eq_zero]
  ext h
  simp only [Finset.notMem_empty, iff_false]
  intro _
  exact h.1.2.elim

/-- The marking legs on the normalized component are precisely its node branches and original
markings. -/
@[simp]
theorem componentNormalization_markingCount (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) :
    (G.componentNormalization v).markingCount (G.componentNormalizationVertex v) =
      G.specialFlagCount v := by
  classical
  have hall : (G.componentNormalization v).markingsAt
      (G.componentNormalizationVertex v) = Finset.univ := by
    ext i
    simp [markingsAt, componentNormalization, componentNormalizationVertex]
  rw [markingCount, hall, Finset.card_univ]
  unfold specialFlagCount DualGraph.valence
  calc
    Fintype.card (G.componentNormalization v).Leg =
        Fintype.card ((G.toDualGraph.incident v : Type u) ⊕
          (G.markingsAt v : Type u)) :=
      Fintype.card_congr (Equiv.refl _)
    _ = (G.toDualGraph.incident v).card + (G.markingsAt v).card := by
      rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]

/-- Normalizing a component reconstructs its logarithmic dualizing degree exactly. -/
@[simp]
theorem componentNormalization_logCanonicalDegree (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) :
    (G.componentNormalization v).logCanonicalDegree (G.componentNormalizationVertex v) =
      G.logCanonicalDegree v := by
  rw [logCanonicalDegree, logCanonicalDegree,
    G.componentNormalization_genus v]
  simp only [specialFlagCount]
  rw [G.componentNormalization_markingCount v, G.componentNormalization_valence v]
  simp [specialFlagCount]

/-- Normalizing a component reconstructs its polarized degree exactly. -/
@[simp]
theorem componentNormalization_polarizedDegree (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) :
    (G.componentNormalization v).polarizedDegree (G.componentNormalizationVertex v) =
      G.polarizedDegree v := by
  simp [polarizedDegree]

/-- The normalized component graph has the same total map degree as the original component. -/
@[simp]
theorem componentNormalization_totalDegree (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) :
    (G.componentNormalization v).totalDegree = G.degree v := by
  rw [totalDegree]
  change ∑ _ : {w : G.toDualGraph.Vertex // w = v}, G.degree v = G.degree v
  have hcard : Fintype.card {w : G.toDualGraph.Vertex // w = v} = 1 :=
    Fintype.card_eq_one_iff.mpr
      ⟨⟨v, rfl⟩, fun w ↦ Subtype.ext w.2⟩
  rw [Finset.sum_const, Finset.card_univ, hcard]
  simp

/-- The arithmetic genus of the normalized component graph is its normalization genus. -/
@[simp]
theorem componentNormalization_arithmeticGenus (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) :
    (G.componentNormalization v).toDualGraph.arithmeticGenus = G.toDualGraph.genus v := by
  apply DualGraph.arithmeticGenus_eq_genus_of_valence_eq_zero _
    (G.componentNormalizationVertex v)
  exact G.componentNormalization_valence v

/-- Componentwise stability is equivalent to stability of the corresponding normalized
one-component decorated graph. -/
theorem componentNormalization_isStable_iff (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) :
    (G.componentNormalization v).IsStable ↔ G.IsStableVertex v := by
  constructor
  · intro h hv
    have hn := h (G.componentNormalizationVertex v) (by simpa using hv)
    simpa using hn
  · intro h w hw
    have hwv : w = G.componentNormalizationVertex v := Subtype.ext w.2
    subst w
    have hn := h (by simpa using hw)
    simpa using hn

/-- A decorated graph is stable exactly when every normalized component graph is stable. -/
theorem isStable_iff_forall_componentNormalization (G : DecoratedGraph.{u}) :
    G.IsStable ↔ ∀ v, (G.componentNormalization v).IsStable := by
  constructor
  · intro h v
    exact (G.componentNormalization_isStable_iff v).2 (h v)
  · intro h v
    exact (G.componentNormalization_isStable_iff v).1 (h v)

/-- The total degree is reconstructed by summing the degrees of all normalized components. -/
theorem sum_componentNormalization_totalDegree (G : DecoratedGraph.{u}) :
    ∑ v, (G.componentNormalization v).totalDegree = G.totalDegree := by
  simp [totalDegree]

/-- The arithmetic genus is reconstructed from the genera of the normalized components and
the first Betti number of the original dual graph. -/
theorem arithmeticGenus_eq_sum_componentNormalization_add_firstBetti
    (G : DecoratedGraph.{u}) :
    G.toDualGraph.arithmeticGenus =
      ∑ v, (G.componentNormalization v).toDualGraph.arithmeticGenus +
        G.toDualGraph.firstBetti := by
  calc
    G.toDualGraph.arithmeticGenus =
        ∑ v, G.toDualGraph.genus v + G.toDualGraph.firstBetti := rfl
    _ = ∑ v, (G.componentNormalization v).toDualGraph.arithmeticGenus +
        G.toDualGraph.firstBetti := by
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      exact (G.componentNormalization_arithmeticGenus v).symm

/-! ## Whole-graph normalization and reassembly -/

/-- The normalization forest is the family of normalized one-component graphs indexed by the
vertices of the original graph.  A separate family is used because `DualGraph` deliberately
requires connectedness, whereas normalization generally disconnects a nodal curve. -/
abbrev normalizationForest (G : DecoratedGraph.{u})
    (v : G.toDualGraph.Vertex) : DecoratedGraph.{u} :=
  G.componentNormalization v

/-- All flags on all components of the normalization forest.  Each flag is either one branch
of an original node or one original marking. -/
abbrev NormalizedFlag (G : DecoratedGraph.{u}) :=
  Σ v : G.toDualGraph.Vertex, (G.normalizationForest v).Leg

/-- The node-branch part of the normalization forest. -/
abbrev NormalizedNodeBranch (G : DecoratedGraph.{u}) :=
  Σ v : G.toDualGraph.Vertex, (G.toDualGraph.incident v : Type u)

/-- The original-marking part of the normalization forest. -/
abbrev NormalizedMarking (G : DecoratedGraph.{u}) :=
  Σ v : G.toDualGraph.Vertex, (G.markingsAt v : Type u)

/-- Membership in the incident-half-edge finset is the corresponding fibre equation. -/
def incidentEquivFiber (G : DecoratedGraph.{u}) (v : G.toDualGraph.Vertex) :
    (G.toDualGraph.incident v : Type u) ≃
      {h : G.toDualGraph.HalfEdge // h.vertex G.toDualGraph = v} :=
  Equiv.subtypeEquivRight fun h ↦ by simp [DualGraph.incident]

/-- Membership in the marking finset at a vertex is the corresponding fibre equation. -/
def markingsAtEquivFiber (G : DecoratedGraph.{u}) (v : G.toDualGraph.Vertex) :
    (G.markingsAt v : Type u) ≃ {i : G.Leg // G.legVertex i = v} :=
  Equiv.subtypeEquivRight fun i ↦ by simp [markingsAt]

/-- The node branches in the normalization are canonically the half-edges of the original
dual graph. -/
def normalizedNodeBranchesEquiv (G : DecoratedGraph.{u}) :
    G.NormalizedNodeBranch ≃ G.toDualGraph.HalfEdge :=
  (Equiv.sigmaCongrRight fun v ↦ G.incidentEquivFiber v).trans
    (Equiv.sigmaFiberEquiv fun h : G.toDualGraph.HalfEdge ↦ h.vertex G.toDualGraph)

/-- The marking flags in the normalization are canonically the original marking legs. -/
def normalizedMarkingsEquiv (G : DecoratedGraph.{u}) :
    G.NormalizedMarking ≃ G.Leg :=
  (Equiv.sigmaCongrRight fun v ↦ G.markingsAtEquivFiber v).trans
    (Equiv.sigmaFiberEquiv G.legVertex)

/-- Reassembling all normalized flags recovers exactly the original half-edges and markings.
This is the finite-set form of identifying the two branches over every node while retaining
the marked sections. -/
def normalizedFlagsEquiv (G : DecoratedGraph.{u}) :
    G.NormalizedFlag ≃ G.toDualGraph.HalfEdge ⊕ G.Leg :=
  (Equiv.sigmaSumDistrib
    (fun v ↦ (G.toDualGraph.incident v : Type u))
    (fun v ↦ (G.markingsAt v : Type u))).trans
      (Equiv.sumCongr G.normalizedNodeBranchesEquiv G.normalizedMarkingsEquiv)

/-- The original edge underlying a normalized node branch. -/
def NormalizedNodeBranch.edge (G : DecoratedGraph.{u})
    (b : G.NormalizedNodeBranch) : G.toDualGraph.Edge :=
  (G.normalizedNodeBranchesEquiv b).1

/-- Which of the two original edge ends a normalized node branch represents. -/
def NormalizedNodeBranch.end (G : DecoratedGraph.{u})
    (b : G.NormalizedNodeBranch) : Fin 2 :=
  (G.normalizedNodeBranchesEquiv b).2

/-- The component carrying a normalized node branch is the corresponding endpoint of the
original edge. -/
theorem NormalizedNodeBranch.endpoint_eq (G : DecoratedGraph.{u})
    (b : G.NormalizedNodeBranch) :
    G.toDualGraph.endpoint (b.edge G) (b.end G) = b.1 := by
  change G.toDualGraph.endpoint b.2.1.1 b.2.1.2 = b.1
  have hmem := b.2.2
  unfold DualGraph.incident at hmem
  rw [Finset.mem_filter] at hmem
  exact hmem.2

/-- The half-edges over a fixed edge are exactly its two ends. -/
def halfEdgesOverEdgeEquiv (G : DecoratedGraph.{u}) (e : G.toDualGraph.Edge) :
    {h : G.toDualGraph.HalfEdge // h.1 = e} ≃ Fin 2 where
  toFun h := h.1.2
  invFun k := ⟨(e, k), rfl⟩
  left_inv := by
    rintro ⟨⟨e', k⟩, he⟩
    apply Subtype.ext
    exact Prod.ext he.symm rfl
  right_inv _ := rfl

/-- The two normalized branches lying over an original edge are indexed by its two ends. -/
def normalizedBranchesOverEdgeEquiv (G : DecoratedGraph.{u})
    (e : G.toDualGraph.Edge) :
    {b : G.NormalizedNodeBranch // b.edge G = e} ≃ Fin 2 :=
  ((G.normalizedNodeBranchesEquiv).subtypeEquiv (fun _ ↦ Iff.rfl)).trans
    (G.halfEdgesOverEdgeEquiv e)

/-- Every original node has exactly two branches on the normalization forest. -/
theorem card_normalizedBranchesOverEdge (G : DecoratedGraph.{u})
    (e : G.toDualGraph.Edge) :
    Fintype.card {b : G.NormalizedNodeBranch // b.edge G = e} = 2 := by
  rw [Fintype.card_congr (G.normalizedBranchesOverEdgeEquiv e)]
  decide

/-- Counting all flags on the normalization gives two branches per node plus one flag per
original marking. -/
theorem card_normalizedFlags (G : DecoratedGraph.{u}) :
    Fintype.card G.NormalizedFlag =
      2 * Fintype.card G.toDualGraph.Edge + Fintype.card G.Leg := by
  rw [Fintype.card_congr G.normalizedFlagsEquiv, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin]
  omega

/-- Counting the component flags directly recovers the sum of the original special-flag
counts. -/
theorem card_normalizedFlags_eq_sum_specialFlagCount (G : DecoratedGraph.{u}) :
    Fintype.card G.NormalizedFlag = ∑ v, G.specialFlagCount v := by
  rw [G.card_normalizedFlags]
  simp only [specialFlagCount, Finset.sum_add_distrib]
  rw [G.toDualGraph.sum_valence, G.sum_markingCount]

/-- An unmarked rational component carrying a map of degree `d`. -/
abbrev unmarkedRationalMapGraph (d : ℕ) : DecoratedGraph.{0} where
  toDualGraph :=
    { Vertex := Fin 1
      Edge := Fin 0
      endpoint := Fin.elim0
      genus := fun _ ↦ 0
      connected := by
        intro v w
        fin_cases v
        fin_cases w
        exact Relation.ReflTransGen.refl }
  Leg := Fin 0
  legVertex := Fin.elim0
  degree := fun _ ↦ d

/-- The identity of `ℙ¹` has the graph-level stability inequality. -/
theorem unmarkedRationalMapGraph_one_stable : (unmarkedRationalMapGraph 1).IsStable := by
  intro v
  exact (unmarkedRationalMapGraph 1).isStableVertex_of_degree_pos v (by simp)

/-- An unmarked rational one-component map graph is stable exactly when its map degree is
positive. -/
theorem unmarkedRationalMapGraph_isStable_iff (d : ℕ) :
    (unmarkedRationalMapGraph d).IsStable ↔ 0 < d := by
  constructor
  · intro h
    apply Nat.pos_of_ne_zero
    intro hd
    subst d
    have h₀ := h (0 : Fin 1) rfl
    norm_num [logCanonicalDegree, specialFlagCount, DualGraph.valence, DualGraph.incident,
      markingCount, markingsAt] at h₀
  · intro hd v
    exact (unmarkedRationalMapGraph d).isStableVertex_of_degree_pos v (by simpa)

/-- Its unmarked rational source is not stable as a pointed curve. -/
theorem unmarkedRationalMapGraph_one_source_not_stable :
    ¬ (unmarkedRationalMapGraph 1).IsPointedStable := by
  intro h
  have := h (0 : Fin 1)
  norm_num [logCanonicalDegree, specialFlagCount, DualGraph.valence, DualGraph.incident,
    markingCount, markingsAt] at this

/-- The constant map from the same unmarked rational source is unstable. -/
theorem unmarkedRationalMapGraph_zero_not_stable :
    ¬ (unmarkedRationalMapGraph 0).IsStable := by
  intro h
  have := h (0 : Fin 1) rfl
  norm_num [logCanonicalDegree, specialFlagCount, DualGraph.valence, DualGraph.incident,
    markingCount, markingsAt] at this

/-- The constant three-pointed rational curve. -/
abbrev threePointedRationalGraph : DecoratedGraph.{0} where
  toDualGraph :=
    { Vertex := Fin 1
      Edge := Fin 0
      endpoint := Fin.elim0
      genus := fun _ ↦ 0
      connected := by
        intro v w
        fin_cases v
        fin_cases w
        exact Relation.ReflTransGen.refl }
  Leg := Fin 3
  legVertex := fun _ ↦ 0
  degree := fun _ ↦ 0

/-- `(P¹; 0,1,∞)` has log-canonical degree one and is stable. -/
theorem threePointedRationalGraph_stable : threePointedRationalGraph.IsStable := by
  intro v _
  fin_cases v
  change 0 < (1 : ℤ)
  norm_num

/-- The same graph is stable already as a pointed source, as expected for
`(ℙ¹; 0,1,∞)`. -/
theorem threePointedRationalGraph_pointedStable :
    threePointedRationalGraph.IsPointedStable :=
  (threePointedRationalGraph.isStable_iff_pointedStable_of_degree_zero
    (by simp [threePointedRationalGraph])).mp threePointedRationalGraph_stable

/-- A genus-two component with an unmarked rational tail of degree `d`. -/
abbrev rationalTailGraph (d : ℕ) : DecoratedGraph.{0} where
  toDualGraph :=
    { Vertex := Fin 2
      Edge := Fin 1
      endpoint := fun _ end_ ↦ if end_ = 0 then 0 else 1
      genus := ![2, 0]
      connected := by
        intro v w
        by_cases h : v = w
        · subst w
          exact Relation.ReflTransGen.refl
        · apply Relation.ReflTransGen.single
          refine ⟨0, ?_⟩
          fin_cases v <;> fin_cases w <;> simp_all }
  Leg := Fin 0
  legVertex := Fin.elim0
  degree := ![0, d]

theorem rationalTailGraph_tail_logCanonicalDegree (d : ℕ) :
    (rationalTailGraph d).logCanonicalDegree 1 = -1 := by
  change (-1 : ℤ) = -1
  rfl

/-- A contracted unmarked rational tail makes the map unstable. -/
theorem rationalTailGraph_zero_not_stable : ¬ (rationalTailGraph 0).IsStable := by
  intro h
  have := h (1 : Fin 2) rfl
  rw [rationalTailGraph_tail_logCanonicalDegree] at this
  omega

/-- An unmarked rational tail is stable for a map exactly when it has positive map degree. -/
theorem rationalTailGraph_isStable_iff (d : ℕ) :
    (rationalTailGraph d).IsStable ↔ 0 < d := by
  constructor
  · intro h
    apply Nat.pos_of_ne_zero
    intro hd
    subst d
    exact rationalTailGraph_zero_not_stable h
  · intro hd v hv
    fin_cases v
    · change 0 < (3 : ℤ)
      norm_num
    · norm_num at hv
      omega

/-- Positive map degree protects the rational tail from contraction. -/
theorem rationalTailGraph_one_stable : (rationalTailGraph 1).IsStable := by
  intro v h
  fin_cases v
  · change 0 < (3 : ℤ)
    norm_num
  · norm_num at h

theorem rationalTailGraph_one_tail_polarizedDegree :
    (rationalTailGraph 1).polarizedDegree 1 = 2 := by
  norm_num [polarizedDegree, rationalTailGraph_tail_logCanonicalDegree]

/-- The graph of two rational components meeting in one node, with two markings on each.
The two parameters are their map degrees. -/
abbrev twoLineFourPointGraph (d₀ d₁ : ℕ) : DecoratedGraph.{0} where
  toDualGraph :=
    { Vertex := Fin 2
      Edge := Fin 1
      endpoint := fun _ end_ ↦ if end_ = 0 then 0 else 1
      genus := fun _ ↦ 0
      connected := by
        intro v w
        by_cases h : v = w
        · subst w
          exact Relation.ReflTransGen.refl
        · apply Relation.ReflTransGen.single
          refine ⟨0, ?_⟩
          fin_cases v <;> fin_cases w <;> simp_all }
  Leg := Fin 4
  legVertex := ![0, 0, 1, 1]
  degree := ![d₀, d₁]

/-- The two-line, four-point graph is stable for arbitrary component degrees: each rational
component already has one node branch and two markings. -/
theorem twoLineFourPointGraph_isStable (d₀ d₁ : ℕ) :
    (twoLineFourPointGraph d₀ d₁).IsStable := by
  intro v _
  fin_cases v
  · change 0 < (1 : ℤ)
    norm_num
  · change 0 < (1 : ℤ)
    norm_num

theorem twoLineFourPointGraph_stable : (twoLineFourPointGraph 0 0).IsStable := by
  intro v _
  fin_cases v
  · change 0 < (1 : ℤ)
    norm_num
  · change 0 < (1 : ℤ)
    norm_num

/-- Retain one marking on the first component and both markings on the second. -/
abbrev afterForgettingFirstComponentMarking (d₀ d₁ : ℕ) : DecoratedGraph.{0} :=
  (twoLineFourPointGraph d₀ d₁).restrictLegs (Fin 3) ![0, 2, 3]

/-- After forgetting one marking on the first component, stability is equivalent to that
component having positive degree; the second component remains stable with any degree. -/
theorem afterForgettingFirstComponentMarking_isStable_iff (d₀ d₁ : ℕ) :
    (afterForgettingFirstComponentMarking d₀ d₁).IsStable ↔ 0 < d₀ := by
  constructor
  · intro h
    apply Nat.pos_of_ne_zero
    intro hd
    have h₀ := h (0 : Fin 2) hd
    change 0 < (0 : ℤ) at h₀
    omega
  · intro hd v hv
    fin_cases v
    · change d₀ = 0 at hv
      omega
    · change 0 < (1 : ℤ)
      norm_num

theorem afterForgetting_constant_firstComponent_logCanonicalDegree :
    (afterForgettingFirstComponentMarking 0 0).logCanonicalDegree 0 = 0 := by
  rfl

/-- After forgetting one of its markings, a constant rational component has only two flags
and must be contracted by map-aware stabilization. -/
theorem afterForgetting_constant_not_stable :
    ¬ (afterForgettingFirstComponentMarking 0 0).IsStable := by
  intro h
  have h₀ := h (0 : Fin 2) rfl
  rw [afterForgetting_constant_firstComponent_logCanonicalDegree] at h₀
  omega

/-- The same component survives forgetting when it carries positive map degree. -/
theorem afterForgetting_positiveDegree_stable :
    (afterForgettingFirstComponentMarking 1 0).IsStable := by
  intro v h
  fin_cases v
  · norm_num at h
  · change 0 < (1 : ℤ)
    norm_num

theorem afterForgetting_positiveDegree_firstComponent_polarizedDegree :
    (afterForgettingFirstComponentMarking 1 0).polarizedDegree 0 = 3 := by
  rfl

end DecoratedGraph

end

end GromovWitten.AlgebraicGeometry.Curves.StableMaps
