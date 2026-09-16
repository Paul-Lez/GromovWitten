/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableMaps.Clutching

/-!
# Worked decorated-graph examples

These examples exercise the iterative part of stabilization: flags must be recomputed after
each contraction.  They are the combinatorial shadows of the corresponding family-level
constructions, not substitutes for those later geometric theorems.
-/

namespace GromovWitten.AlgebraicGeometry.Curves.StableMaps

open GromovWitten.AlgebraicGeometry.Curves

namespace DecoratedGraph

/-- Endpoint table for the three edges in the iterated-tail example. -/
abbrev iteratedTailEndpoint : Fin 3 → Fin 2 → Fin 4 :=
  ![![0, 1], ![1, 2], ![1, 3]]

/-- A genus-two component `0`, a rational component `1`, and two rational leaves `2,3`.
All three attached rational components have map degree zero. -/
abbrev iteratedTailInitial : DecoratedGraph.{0} where
  toDualGraph :=
    { Vertex := Fin 4
      Edge := Fin 3
      endpoint := iteratedTailEndpoint
      genus := ![2, 0, 0, 0]
      connected := by
        let adjacent := fun v w : Fin 4 ↦ ∃ e : Fin 3,
          iteratedTailEndpoint e 0 = v ∧ iteratedTailEndpoint e 1 = w ∨
            iteratedTailEndpoint e 0 = w ∧ iteratedTailEndpoint e 1 = v
        have toCenter : ∀ v : Fin 4, Relation.ReflTransGen adjacent v 1 := by
          intro v
          fin_cases v
          · apply Relation.ReflTransGen.single
            refine ⟨0, ?_⟩
            decide
          · exact Relation.ReflTransGen.refl
          · apply Relation.ReflTransGen.single
            refine ⟨1, ?_⟩
            decide
          · apply Relation.ReflTransGen.single
            refine ⟨2, ?_⟩
            decide
        have fromCenter : ∀ v : Fin 4, Relation.ReflTransGen adjacent 1 v := by
          intro v
          fin_cases v
          · apply Relation.ReflTransGen.single
            refine ⟨0, ?_⟩
            decide
          · exact Relation.ReflTransGen.refl
          · apply Relation.ReflTransGen.single
            refine ⟨1, ?_⟩
            decide
          · apply Relation.ReflTransGen.single
            refine ⟨2, ?_⟩
            decide
        intro v w
        exact (toCenter v).trans (fromCenter w) }
  Leg := Fin 0
  legVertex := Fin.elim0
  degree := fun _ ↦ 0

/-- The intermediate graph after deleting the two rational leaves. -/
abbrev iteratedTailAfterLeaves : DecoratedGraph.{0} := rationalTailGraph 0

/-- The final graph after the newly-created rational tail has also been contracted. -/
abbrev iteratedTailStable : DecoratedGraph.{0} where
  toDualGraph :=
    { Vertex := Fin 1
      Edge := Fin 0
      endpoint := Fin.elim0
      genus := fun _ ↦ 2
      connected := by
        intro v w
        fin_cases v
        fin_cases w
        exact Relation.ReflTransGen.refl }
  Leg := Fin 0
  legVertex := Fin.elim0
  degree := fun _ ↦ 0

theorem iteratedTail_initial_central_degree : iteratedTailInitial.logCanonicalDegree 1 = 1 := by
  change (1 : ℤ) = 1
  rfl

theorem iteratedTail_initial_firstLeaf_degree :
    iteratedTailInitial.logCanonicalDegree 2 = -1 := by
  change (-1 : ℤ) = -1
  rfl

theorem iteratedTail_initial_secondLeaf_degree :
    iteratedTailInitial.logCanonicalDegree 3 = -1 := by
  change (-1 : ℤ) = -1
  rfl

theorem iteratedTail_afterLeaves_central_degree :
    iteratedTailAfterLeaves.logCanonicalDegree 1 = -1 :=
  rationalTailGraph_tail_logCanonicalDegree 0

theorem iteratedTail_final_stable : iteratedTailStable.IsStable := by
  intro v _
  fin_cases v
  change 0 < (2 : ℤ)
  norm_num

/-- Kernel-checked numerical trace of the iterated contraction.  The middle component starts
with positive canonical degree, becomes a tail after both leaves are removed, and then becomes
contractible; the final genus-two component is stable. -/
theorem iteratedTail_requires_recomputed_flags :
    0 < iteratedTailInitial.logCanonicalDegree 1 ∧
      iteratedTailInitial.logCanonicalDegree 2 ≤ 0 ∧
      iteratedTailInitial.logCanonicalDegree 3 ≤ 0 ∧
      iteratedTailAfterLeaves.logCanonicalDegree 1 ≤ 0 ∧
      iteratedTailStable.IsStable := by
  rw [iteratedTail_initial_central_degree, iteratedTail_initial_firstLeaf_degree,
    iteratedTail_initial_secondLeaf_degree, iteratedTail_afterLeaves_central_degree]
  exact ⟨by omega, by omega, by omega, by omega, iteratedTail_final_stable⟩

/-- Retained markings on the genus-two component do not change the attached tree's degrees. -/
abbrev iteratedTailWithRetainedBaseMarkings : DecoratedGraph.{0} :=
  { toDualGraph := iteratedTailInitial.toDualGraph
    Leg := Fin 2
    legVertex := fun _ ↦ 0
    degree := iteratedTailInitial.degree }

theorem iteratedTail_marked_central_degree :
    iteratedTailWithRetainedBaseMarkings.logCanonicalDegree 1 = 1 := by
  change (1 : ℤ) = 1
  rfl

theorem iteratedTail_marked_firstLeaf_degree :
    iteratedTailWithRetainedBaseMarkings.logCanonicalDegree 2 = -1 := by
  change (-1 : ℤ) = -1
  rfl

theorem iteratedTail_marked_secondLeaf_degree :
    iteratedTailWithRetainedBaseMarkings.logCanonicalDegree 3 = -1 := by
  change (-1 : ℤ) = -1
  rfl

/-- Carrier-level bookkeeping for deleting the two leaves: both leaves map to their attachment
vertex, while the genus-two vertex and the central rational vertex remain distinct.  This is not
a claim that a geometric contraction of curves has been constructed. -/
abbrev iteratedTailContractLeavesVertex : Fin 4 → Fin 2 := ![0, 1, 1, 1]

/-- Carrier-level bookkeeping for the second step, which contracts the newly exposed rational
tail to the genus-two vertex. -/
abbrev iteratedTailContractCenterVertex : Fin 2 → Fin 1 := ![0, 0]

theorem iteratedTail_firstStage_vertex_bookkeeping :
    iteratedTailContractLeavesVertex 0 = 0 ∧
      iteratedTailContractLeavesVertex 1 = 1 ∧
      iteratedTailContractLeavesVertex 2 = 1 ∧
      iteratedTailContractLeavesVertex 3 = 1 := by
  decide

/-- Every vertex in the attached tree lands at the unique final vertex after the two abstract
bookkeeping steps. -/
theorem iteratedTail_entire_attachedTree_collapses :
    ∀ v : Fin 4, v ≠ 0 →
      iteratedTailContractCenterVertex (iteratedTailContractLeavesVertex v) = 0 := by
  intro v _
  fin_cases v <;> rfl

theorem iteratedTail_component_count_bookkeeping :
    Fintype.card iteratedTailInitial.toDualGraph.Vertex = 4 ∧
      Fintype.card iteratedTailAfterLeaves.toDualGraph.Vertex = 2 ∧
      Fintype.card iteratedTailStable.toDualGraph.Vertex = 1 ∧
      Fintype.card iteratedTailInitial.toDualGraph.Edge = 3 ∧
      Fintype.card iteratedTailAfterLeaves.toDualGraph.Edge = 1 ∧
      Fintype.card iteratedTailStable.toDualGraph.Edge = 0 := by
  decide

/-- All components have degree zero in this example, so in particular the whole attached tree is
constant.  Total degree and arithmetic genus remain unchanged through both bookkeeping stages. -/
theorem iteratedTail_constantTree_stage_invariants :
    (∀ v, iteratedTailInitial.degree v = 0) ∧
      iteratedTailInitial.totalDegree = 0 ∧
      iteratedTailAfterLeaves.totalDegree = 0 ∧
      iteratedTailStable.totalDegree = 0 ∧
      iteratedTailInitial.toDualGraph.arithmeticGenus = 2 ∧
      iteratedTailAfterLeaves.toDualGraph.arithmeticGenus = 2 ∧
      iteratedTailStable.toDualGraph.arithmeticGenus = 2 := by
  decide

/-- Intermediate marked graph after the leaves are removed, retaining the two markings on the
genus-two component. -/
abbrev iteratedTailAfterLeavesWithRetainedBaseMarkings : DecoratedGraph.{0} :=
  { toDualGraph := iteratedTailAfterLeaves.toDualGraph
    Leg := Fin 2
    legVertex := fun _ ↦ 0
    degree := iteratedTailAfterLeaves.degree }

/-- Final marked graph after the central rational tail is also removed. -/
abbrev iteratedTailStableWithRetainedBaseMarkings : DecoratedGraph.{0} :=
  { toDualGraph := iteratedTailStable.toDualGraph
    Leg := Fin 2
    legVertex := fun _ ↦ 0
    degree := iteratedTailStable.degree }

theorem iteratedTail_marked_afterLeaves_central_degree :
    iteratedTailAfterLeavesWithRetainedBaseMarkings.logCanonicalDegree 1 = -1 := by
  change (-1 : ℤ) = -1
  rfl

theorem iteratedTail_marked_final_stable :
    iteratedTailStableWithRetainedBaseMarkings.IsStable := by
  intro v _
  fin_cases v
  change 0 < (4 : ℤ)
  norm_num

/-- Retaining markings on the untouched genus-two component preserves their number throughout
the two combinatorial stages and does not prevent the whole constant attached tree from becoming
unstable and disappearing from the final vertex set. -/
theorem iteratedTail_retainedMarkings_bookkeeping :
    Fintype.card iteratedTailWithRetainedBaseMarkings.Leg = 2 ∧
      Fintype.card iteratedTailAfterLeavesWithRetainedBaseMarkings.Leg = 2 ∧
      Fintype.card iteratedTailStableWithRetainedBaseMarkings.Leg = 2 ∧
      0 < iteratedTailWithRetainedBaseMarkings.logCanonicalDegree 1 ∧
      iteratedTailAfterLeavesWithRetainedBaseMarkings.logCanonicalDegree 1 ≤ 0 ∧
      iteratedTailStableWithRetainedBaseMarkings.IsStable := by
  rw [iteratedTail_marked_central_degree, iteratedTail_marked_afterLeaves_central_degree]
  exact ⟨by decide, by decide, by decide, by omega, by omega,
    iteratedTail_marked_final_stable⟩

/-! ## Forgetting a marking: the full degree-zero/positive-degree contrast -/

/-- Forget both markings on the first component, retaining the two on the second component. -/
abbrev afterForgettingAllFirstComponentMarkings (d₀ d₁ : ℕ) : DecoratedGraph.{0} :=
  (twoLineFourPointGraph d₀ d₁).restrictLegs (Fin 2) ![2, 3]

/-- After forgetting both markings on the first component, stability is equivalent exactly to
positive map degree on that component.  The other component still has two markings and needs no
degree hypothesis. -/
theorem afterForgettingAllFirstComponentMarkings_isStable_iff (d₀ d₁ : ℕ) :
    (afterForgettingAllFirstComponentMarkings d₀ d₁).IsStable ↔ 0 < d₀ := by
  constructor
  · intro h
    apply Nat.pos_of_ne_zero
    intro hd
    have h₀ := h (0 : Fin 2) hd
    change 0 < (-1 : ℤ) at h₀
    omega
  · intro hd v hv
    fin_cases v
    · change d₀ = 0 at hv
      omega
    · change 0 < (1 : ℤ)
      norm_num

theorem afterForgettingAll_constant_firstComponent_logCanonicalDegree :
    (afterForgettingAllFirstComponentMarkings 0 0).logCanonicalDegree 0 = -1 := by
  rfl

theorem afterForgettingAll_constant_not_stable :
    ¬ (afterForgettingAllFirstComponentMarkings 0 0).IsStable := by
  intro h
  have h₀ := h (0 : Fin 2) rfl
  rw [afterForgettingAll_constant_firstComponent_logCanonicalDegree] at h₀
  omega

theorem twoLineFourPointGraph_positiveFirstComponent_stable :
    (twoLineFourPointGraph 1 0).IsStable := by
  intro v h
  fin_cases v
  · norm_num at h
  · change 0 < (1 : ℤ)
    norm_num

/-- Positive degree protects the first component even after its last marking is forgotten. -/
theorem afterForgettingAll_positiveDegree_stable :
    (afterForgettingAllFirstComponentMarkings 1 0).IsStable := by
  intro v h
  fin_cases v
  · norm_num at h
  · change 0 < (1 : ℤ)
    norm_num

theorem afterForgettingAll_positiveDegree_firstComponent_logCanonicalDegree :
    (afterForgettingAllFirstComponentMarkings 1 0).logCanonicalDegree 0 = -1 := by
  rfl

theorem afterForgettingAll_positiveDegree_firstComponent_polarizedDegree :
    (afterForgettingAllFirstComponentMarkings 1 0).polarizedDegree 0 = 2 := by
  rfl

/-- Complete kernel-checked contrast for the roadmap's forgetting example.  The constant
component becomes unstable after one marking is removed, whereas a positive-degree component
remains stable even after both of its markings have been removed. -/
theorem forgetting_marking_constant_vs_positiveDegree :
    (twoLineFourPointGraph 0 0).IsStable ∧
      ¬ (afterForgettingFirstComponentMarking 0 0).IsStable ∧
      (twoLineFourPointGraph 1 0).IsStable ∧
      (afterForgettingFirstComponentMarking 1 0).IsStable ∧
      (afterForgettingAllFirstComponentMarkings 1 0).IsStable ∧
      (afterForgettingAllFirstComponentMarkings 1 0).logCanonicalDegree 0 ≤ 0 ∧
      0 < (afterForgettingAllFirstComponentMarkings 1 0).polarizedDegree 0 := by
  exact ⟨twoLineFourPointGraph_stable, afterForgetting_constant_not_stable,
    twoLineFourPointGraph_positiveFirstComponent_stable,
    afterForgetting_positiveDegree_stable, afterForgettingAll_positiveDegree_stable,
    by rw [afterForgettingAll_positiveDegree_firstComponent_logCanonicalDegree]; omega,
    by rw [afterForgettingAll_positiveDegree_firstComponent_polarizedDegree]; omega⟩

/-- Numerical shadow of a target postcomposition that contracts the formerly positive-degree
rational tail.  No target morphism is asserted to realize this degree change. -/
abbrev rationalTailAfterDegreeCollapse : DecoratedGraph.{0} :=
  (rationalTailGraph 1).withDegree ![0, 0]

theorem rationalTailAfterDegreeCollapse_not_stable :
    ¬ rationalTailAfterDegreeCollapse.IsStable := by
  intro h
  have htail :=
    ((rationalTailGraph 1).isStable_withDegree_iff_forall_zero_degree _).mp h 1 rfl
  rw [rationalTailGraph_tail_logCanonicalDegree] at htail
  omega

/-- The sharp postcomposition contrast: the positive-degree tail starts stable, but becomes
unstable exactly when the changed degree makes it a new zero-degree vertex of nonpositive
log-canonical degree. -/
theorem rationalTail_degreeCollapse_sharp_contrast :
    (rationalTailGraph 1).IsStable ∧
      ¬ rationalTailAfterDegreeCollapse.IsStable ∧
      (rationalTailGraph 1).degree 1 ≠ 0 ∧
      rationalTailAfterDegreeCollapse.degree 1 = 0 ∧
      rationalTailAfterDegreeCollapse.logCanonicalDegree 1 ≤ 0 := by
  exact ⟨rationalTailGraph_one_stable, rationalTailAfterDegreeCollapse_not_stable,
    by decide, rfl, by rw [rationalTailGraph_tail_logCanonicalDegree]; omega⟩

/-! ## Unpointed graph-level examples -/

/-- A rational bridge between two genus-two components. -/
abbrev rationalBridgeEndpoint : Fin 2 → Fin 2 → Fin 3 := ![![0, 1], ![1, 2]]

abbrev rationalBridgeGraph : DecoratedGraph.{0} where
  toDualGraph :=
    { Vertex := Fin 3
      Edge := Fin 2
      endpoint := rationalBridgeEndpoint
      genus := ![2, 0, 2]
      connected := by
        let adjacent := fun v w : Fin 3 ↦ ∃ e : Fin 2,
          rationalBridgeEndpoint e 0 = v ∧ rationalBridgeEndpoint e 1 = w ∨
            rationalBridgeEndpoint e 0 = w ∧ rationalBridgeEndpoint e 1 = v
        have toCenter : ∀ v : Fin 3, Relation.ReflTransGen adjacent v 1 := by
          intro v
          fin_cases v
          · apply Relation.ReflTransGen.single
            exact ⟨0, by decide⟩
          · exact Relation.ReflTransGen.refl
          · apply Relation.ReflTransGen.single
            exact ⟨1, by decide⟩
        have fromCenter : ∀ v : Fin 3, Relation.ReflTransGen adjacent 1 v := by
          intro v
          fin_cases v
          · apply Relation.ReflTransGen.single
            exact ⟨0, by decide⟩
          · exact Relation.ReflTransGen.refl
          · apply Relation.ReflTransGen.single
            exact ⟨1, by decide⟩
        intro v w
        exact (toCenter v).trans (fromCenter w) }
  Leg := Fin 0
  legVertex := Fin.elim0
  degree := fun _ ↦ 0

theorem rationalBridgeGraph_bridge_logCanonicalDegree :
    rationalBridgeGraph.logCanonicalDegree 1 = 0 := by
  rfl

theorem rationalBridgeGraph_not_pointedStable : ¬ rationalBridgeGraph.IsPointedStable := by
  intro h
  have h₁ := h (1 : Fin 3)
  rw [rationalBridgeGraph_bridge_logCanonicalDegree] at h₁
  omega

/-- A rational one-component cycle, represented by one vertex and one loop. -/
abbrev rationalLoopGraph : DecoratedGraph.{0} where
  toDualGraph := DualGraph.oneLoop
  Leg := Fin 0
  legVertex := Fin.elim0
  degree := fun _ ↦ 0

theorem rationalLoopGraph_arithmeticGenus :
    rationalLoopGraph.toDualGraph.arithmeticGenus = 1 := DualGraph.oneLoop_arithmeticGenus

theorem rationalLoopGraph_logCanonicalDegree_zero (v : rationalLoopGraph.toDualGraph.Vertex) :
    rationalLoopGraph.logCanonicalDegree v = 0 := by
  fin_cases v
  change (0 : ℤ) = 0
  rfl

/-- The loop graph satisfies the nonnegative canonical-degree condition expected of a
genus-one semistable cycle, but it fails strict unpointed stability. -/
theorem rationalLoopGraph_numericallySemistable_not_pointedStable :
    (∀ v, 0 ≤ rationalLoopGraph.logCanonicalDegree v) ∧
      ¬ rationalLoopGraph.IsPointedStable := by
  constructor
  · intro v
    rw [rationalLoopGraph_logCanonicalDegree_zero]
  · intro h
    have h₀ := h (0 : Fin 1)
    rw [rationalLoopGraph_logCanonicalDegree_zero] at h₀
    omega

/-- The zero-edge genus-two graph is the graph-level smooth genus-two example. -/
theorem smoothGenusTwoGraph_acceptance :
    Fintype.card iteratedTailStable.toDualGraph.Edge = 0 ∧
      iteratedTailStable.toDualGraph.arithmeticGenus = 2 ∧
      iteratedTailStable.IsPointedStable := by
  refine ⟨by decide, by decide, ?_⟩
  intro v
  fin_cases v
  change 0 < (2 : ℤ)
  norm_num

/-! ## Concrete decorated-graph clutching checks -/

abbrev externalThreePointedRationalGlue : DecoratedGraph.{0} :=
  externalGlue threePointedRationalGraph threePointedRationalGraph 0 0

theorem externalThreePointedRationalGlue_stable : externalThreePointedRationalGlue.IsStable :=
  (externalGlue_isStable_iff _ _ _ _).2
    ⟨threePointedRationalGraph_stable, threePointedRationalGraph_stable⟩

theorem externalThreePointedRationalGlue_invariants :
    externalThreePointedRationalGlue.toDualGraph.arithmeticGenus = 0 ∧
      externalThreePointedRationalGlue.totalDegree = 0 ∧
      Fintype.card externalThreePointedRationalGlue.Leg = 4 := by
  constructor
  · rw [externalGlue_arithmeticGenus]
    decide
  · constructor
    · rw [externalGlue_totalDegree]
      decide
    · decide

abbrev selfThreePointedRationalGlue : DecoratedGraph.{0} :=
  selfGlue threePointedRationalGraph 0 1 (by decide)

theorem selfThreePointedRationalGlue_stable : selfThreePointedRationalGlue.IsStable :=
  (selfGlue_isStable_iff _ _ _ (by decide)).2 threePointedRationalGraph_stable

theorem selfThreePointedRationalGlue_newEdge_isLoop :
    selfThreePointedRationalGlue.toDualGraph.endpoint (.inr ()) 0 =
      selfThreePointedRationalGlue.toDualGraph.endpoint (.inr ()) 1 := by
  apply (selfGlue_newEdge_isLoop_iff threePointedRationalGraph 0 1 (by decide)).2
  rfl

theorem selfThreePointedRationalGlue_invariants :
    selfThreePointedRationalGlue.toDualGraph.arithmeticGenus = 1 ∧
      selfThreePointedRationalGlue.totalDegree = 0 ∧
      Fintype.card selfThreePointedRationalGlue.Leg = 1 := by
  constructor
  · rw [selfGlue_arithmeticGenus]
    decide
  · constructor
    · rw [selfGlue_totalDegree]
      decide
    · decide

end DecoratedGraph

end GromovWitten.AlgebraicGeometry.Curves.StableMaps
