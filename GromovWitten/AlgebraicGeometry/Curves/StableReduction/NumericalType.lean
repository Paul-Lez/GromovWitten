/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib

/-!
# Numerical types of regular models

This is the abstract combinatorial object from Stacks Project tags 0C6Z and 0C7H.  The
Picard relations divide the `j`th coordinate of a matrix row by the *destination* weight
`wⱼ`; using the raw rows introduces spurious torsion.
-/

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u v w

noncomputable section

/-- The numerical type of the special fibre of a regular model. -/
structure NumericalType where
  Component : Type u
  [componentFintype : Fintype Component]
  [componentDecidableEq : DecidableEq Component]
  [componentNonempty : Nonempty Component]
  multiplicity : Component → ℕ+
  weight : Component → ℕ+
  intersection : Matrix Component Component ℤ
  intersection_symm : ∀ i j, intersection i j = intersection j i
  offDiagonal_nonnegative : ∀ i j, i ≠ j → 0 ≤ intersection i j
  connected : ∀ i j, Relation.ReflTransGen
    (fun i j ↦ i ≠ j ∧ 0 < intersection i j) i j
  fiber_relation : ∀ i, ∑ j, (multiplicity j : ℤ) * intersection i j = 0
  weight_dvd : ∀ i j, (weight i : ℤ) ∣ intersection i j
  genus : Component → ℕ

namespace NumericalType

instance (T : NumericalType) : Fintype T.Component := T.componentFintype
instance (T : NumericalType) : DecidableEq T.Component := T.componentDecidableEq
instance (T : NumericalType) : Nonempty T.Component := T.componentNonempty

/-- The simple graph whose edges are the positive off-diagonal intersection numbers. -/
def intersectionGraph (T : NumericalType) : SimpleGraph T.Component where
  Adj i j := i ≠ j ∧ 0 < T.intersection i j
  symm.symm i j hij := ⟨hij.1.symm, (T.intersection_symm i j) ▸ hij.2⟩

instance intersectionGraphAdjDecidable (T : NumericalType) :
    DecidableRel T.intersectionGraph.Adj := fun i j ↦ by
  change Decidable (i ≠ j ∧ 0 < T.intersection i j)
  infer_instance

@[simp] theorem intersectionGraph_adj (T : NumericalType) (i j : T.Component) :
    T.intersectionGraph.Adj i j ↔ i ≠ j ∧ 0 < T.intersection i j := Iff.rfl

/-- Stacks Project tag 0C6Z's no-disconnected-cut condition: every nonempty proper collection
of components has a nonzero intersection with its complement. -/
def NoDisconnectedCut (T : NumericalType) : Prop :=
  ∀ s : Finset T.Component, s.Nonempty → s ≠ Finset.univ →
    ∃ i ∈ s, ∃ j ∉ s, T.intersection i j ≠ 0

private lemma ReflTransGen.exists_crossing {I : Type*} {r : I → I → Prop}
    {s : Set I} {a b : I} (ha : a ∈ s) (hb : b ∉ s) (h : Relation.ReflTransGen r a b) :
    ∃ i ∈ s, ∃ j ∉ s, r i j := by
  induction h with
  | refl => exact (hb ha).elim
  | @tail b c h hij ih =>
      by_cases hi : b ∈ s
      · exact ⟨b, hi, c, hb, hij⟩
      · exact ih hi

/-- Graph connectedness is equivalent to the no-disconnected-cut condition. -/
theorem intersectionGraph_connected_iff_noDisconnectedCut (T : NumericalType) :
    T.intersectionGraph.Connected ↔ T.NoDisconnectedCut := by
  classical
  constructor
  · intro hconn s hs hproper
    obtain ⟨i, hi⟩ := hs
    have hnotmem : ∃ j, j ∉ s := by
      by_contra h
      apply hproper
      apply Finset.eq_univ_iff_forall.mpr
      intro j
      by_contra hj
      exact h ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hnotmem
    have hpath : Relation.ReflTransGen T.intersectionGraph.Adj i j :=
      (T.intersectionGraph.reachable_iff_reflTransGen i j).mp (hconn i j)
    obtain ⟨a, ha, b, hb, hab⟩ :=
      ReflTransGen.exists_crossing (s := (s : Set T.Component)) hi hj hpath
    exact ⟨a, ha, b, hb, ne_of_gt hab.2⟩
  · intro hcut
    refine ⟨?_⟩
    intro a b
    rw [T.intersectionGraph.reachable_iff_reflTransGen]
    by_contra hab
    let s : Finset T.Component := Finset.univ.filter fun j ↦
      Relation.ReflTransGen T.intersectionGraph.Adj a j
    have ha : a ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      exact .refl
    have hb : b ∉ s := by simpa [s] using hab
    have hs : s.Nonempty := ⟨a, ha⟩
    have hproper : s ≠ Finset.univ := by
      intro h
      have : b ∈ s := by rw [h]; simp
      exact hb this
    obtain ⟨i, hi, j, hj, hij⟩ := hcut s hs hproper
    have hne : i ≠ j := fun h ↦ hj (h ▸ hi)
    have hpos : 0 < T.intersection i j :=
      lt_of_le_of_ne (T.offDiagonal_nonnegative i j hne) hij.symm
    have hai : Relation.ReflTransGen T.intersectionGraph.Adj a i := by simpa [s] using hi
    have haj := hai.tail (show T.intersectionGraph.Adj i j from ⟨hne, hpos⟩)
    exact hj (by simpa [s] using haj)

/-- Relation-theoretic form of the connectedness/no-cut equivalence, matching the type of the
`NumericalType.connected` field exactly. -/
theorem connected_iff_noDisconnectedCut (T : NumericalType) :
    (∀ i j, Relation.ReflTransGen
      (fun i j ↦ i ≠ j ∧ 0 < T.intersection i j) i j) ↔ T.NoDisconnectedCut := by
  rw [← T.intersectionGraph_connected_iff_noDisconnectedCut]
  constructor
  · intro h
    refine ⟨fun i j ↦ (T.intersectionGraph.reachable_iff_reflTransGen i j).mpr ?_⟩
    exact h i j
  · intro h i j
    exact (T.intersectionGraph.reachable_iff_reflTransGen i j).mp (h i j)

/-- The bundled connectedness field supplies the graph-theoretic connectedness statement. -/
theorem intersectionGraph_connected (T : NumericalType) : T.intersectionGraph.Connected := by
  refine ⟨fun i j ↦ (T.intersectionGraph.reachable_iff_reflTransGen i j).mpr ?_⟩
  exact T.connected i j

/-- Every numerical type satisfies the equivalent no-disconnected-cut formulation. -/
theorem noDisconnectedCut (T : NumericalType) : T.NoDisconnectedCut :=
  T.intersectionGraph_connected_iff_noDisconnectedCut.mp T.intersectionGraph_connected

/-- The first Betti number of the (simple) intersection graph.  This is the
`1 - n + e` topological genus of Stacks Project tag `0C79`; subtraction is in `ℕ`, and
connectedness proves that it does not truncate a negative integer. -/
def topologicalGenus (T : NumericalType) : ℕ :=
  Nat.card T.intersectionGraph.edgeSet + 1 - Nat.card T.Component

/-- A connected numerical type has enough intersection edges for its topological genus to
be a genuine nonnegative difference. -/
theorem card_component_le_card_edge_add_one (T : NumericalType) :
    Nat.card T.Component ≤ Nat.card T.intersectionGraph.edgeSet + 1 :=
  T.intersectionGraph_connected.card_vert_le_card_edgeSet_add_one

/-- Euler's formula for the topological genus of the intersection graph. -/
theorem card_component_add_topologicalGenus (T : NumericalType) :
    Nat.card T.Component + T.topologicalGenus =
      Nat.card T.intersectionGraph.edgeSet + 1 := by
  exact Nat.add_sub_of_le T.card_component_le_card_edge_add_one

/-- The unoriented edges of the intersection graph. -/
abbrev IntersectionEdge (T : NumericalType) := T.intersectionGraph.edgeSet

/-- The two representatives chosen for an intersection edge are adjacent. -/
lemma intersectionEdge_out_adj (T : NumericalType) (e : T.IntersectionEdge) :
    T.intersectionGraph.Adj e.1.out.1 e.1.out.2 := by
  rw [← SimpleGraph.mem_edgeSet]
  simpa only [e.1.out_eq] using e.2

/-- Edges incident to a vertex are naturally indexed by its adjacent vertices. -/
def incidentEdgeEquiv (T : NumericalType.{u}) (i : T.Component) :
    {e : T.IntersectionEdge // i ∈ (e.1 : Sym2 T.Component)} ≃
      T.intersectionGraph.neighborSet i := by
  let e₁ : {e : T.IntersectionEdge // i ∈ (e.1 : Sym2 T.Component)} ≃
      T.intersectionGraph.incidenceSet i :=
    { toFun := fun e => ⟨e.1.1, show e.1.1 ∈ T.intersectionGraph.incidenceSet i from
          ⟨e.1.2, e.2⟩⟩
      invFun := fun e => ⟨⟨e.1, e.2.1⟩, e.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact e₁.trans (T.intersectionGraph.incidenceSetEquivNeighborSet i)

/-- An arbitrarily oriented incidence matrix for the intersection graph.  Changing the
orientation only negates rows, so its rank and boundary kernel are canonical. -/
def incidenceMatrix (T : NumericalType) (F : Type*) [Ring F] :
    Matrix T.IntersectionEdge T.Component F := fun e i ↦
  if i = e.1.out.1 then 1 else if i = e.1.out.2 then -1 else 0

/-- Applying the incidence matrix subtracts the values at the chosen endpoints. -/
lemma incidenceMatrix_mulVec_apply (T : NumericalType) (F : Type*) [Field F]
    (x : T.Component → F) (e : T.IntersectionEdge) :
    Matrix.mulVec (T.incidenceMatrix F) x e = x e.1.out.1 - x e.1.out.2 := by
  classical
  have hne : e.1.out.1 ≠ e.1.out.2 := (T.intersectionEdge_out_adj e).ne
  rw [Matrix.mulVec, dotProduct]
  simp only [incidenceMatrix, ite_mul, one_mul, neg_mul, zero_mul]
  calc
    (∑ i, if i = e.1.out.1 then x i else if i = e.1.out.2 then -x i else 0) =
        (∑ i, if i = e.1.out.1 then x i else 0) +
          ∑ i, if i = e.1.out.2 then -x i else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = e.1.out.1
      · subst i
        simp [hne]
      · simp [hi]
    _ = x e.1.out.1 - x e.1.out.2 := by
      simp [sub_eq_add_neg]

private lemma eq_of_incidence_mulVec_eq_zero (T : NumericalType) (F : Type*) [Field F]
    (x : T.Component → F) (hx : Matrix.mulVec (T.incidenceMatrix F) x = 0)
    (i j : T.Component) : x i = x j := by
  induction T.connected i j with
  | refl => rfl
  | @tail j k h hjk ih =>
      let e : T.IntersectionEdge := ⟨s(j, k), by
        rw [SimpleGraph.mem_edgeSet]
        exact hjk⟩
      have he := congrFun hx e
      rw [T.incidenceMatrix_mulVec_apply F x e] at he
      simp only [Pi.zero_apply] at he
      have hout :
          e.1.out.1 = j ∧ e.1.out.2 = k ∨ e.1.out.1 = k ∧ e.1.out.2 = j := by
        exact Sym2.eq_iff.mp e.1.out_eq
      rcases hout with hout | hout
      · rw [hout.1, hout.2] at he
        exact ih.trans (sub_eq_zero.mp he)
      · rw [hout.1, hout.2] at he
        exact ih.trans (sub_eq_zero.mp he).symm

/-- On a connected graph, the kernel of the incidence matrix consists of the constant
functions and is one-dimensional. -/
theorem incidenceMatrix_ker_finrank (T : NumericalType) (F : Type*) [Field F] :
    Module.finrank F (LinearMap.ker (T.incidenceMatrix F).mulVecLin) = 1 := by
  let a : T.Component := Classical.choice T.componentNonempty
  let ev : LinearMap.ker (T.incidenceMatrix F).mulVecLin →ₗ[F] F :=
    (LinearMap.proj a).comp (LinearMap.ker (T.incidenceMatrix F).mulVecLin).subtype
  have hev : Function.Injective ev := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hxa := T.eq_of_incidence_mulVec_eq_zero F x.1
      (LinearMap.mem_ker.mp x.2) i a
    have hya := T.eq_of_incidence_mulVec_eq_zero F y.1
      (LinearMap.mem_ker.mp y.2) i a
    change x.1 a = y.1 a at hxy
    exact hxa.trans (hxy.trans hya.symm)
  have hle : Module.finrank F (LinearMap.ker (T.incidenceMatrix F).mulVecLin) ≤ 1 := by
    calc
      _ = Module.finrank F (LinearMap.range ev) :=
        (LinearMap.finrank_range_of_inj hev).symm
      _ ≤ Module.finrank F F := (LinearMap.range ev).finrank_le
      _ = 1 := Module.finrank_self F
  let oneKer : LinearMap.ker (T.incidenceMatrix F).mulVecLin :=
    ⟨fun _ ↦ 1, by
      rw [LinearMap.mem_ker]
      funext e
      rw [Matrix.mulVecLin_apply, T.incidenceMatrix_mulVec_apply]
      simp⟩
  have hone : oneKer ≠ 0 := by
    intro h
    have hvalue := congrArg
      (fun z : LinearMap.ker (T.incidenceMatrix F).mulVecLin ↦ z.1 a) h
    simp [oneKer] at hvalue
  let _ : Nontrivial (LinearMap.ker (T.incidenceMatrix F).mulVecLin) :=
    ⟨⟨oneKer, 0, hone⟩⟩
  have hpos : 0 < Module.finrank F
      (LinearMap.ker (T.incidenceMatrix F).mulVecLin) := Module.finrank_pos
  omega

/-- The incidence matrix of a connected graph on `n` vertices has rank `n - 1`. -/
theorem incidenceMatrix_rank (T : NumericalType) (F : Type*) [Field F] :
    (T.incidenceMatrix F).rank + 1 = Nat.card T.Component := by
  rw [Matrix.rank]
  have h := (T.incidenceMatrix F).mulVecLin.finrank_range_add_finrank_ker
  rw [T.incidenceMatrix_ker_finrank F, Module.finrank_pi] at h
  rw [Nat.card_eq_fintype_card]
  exact h

/-- The kernel of the transpose incidence matrix is the graph cycle space; its dimension is
the topological genus. -/
theorem boundaryMatrix_ker_finrank (T : NumericalType) (F : Type*) [Field F] :
    Module.finrank F (LinearMap.ker (T.incidenceMatrix F).transpose.mulVecLin) =
      T.topologicalGenus := by
  have h := (T.incidenceMatrix F).transpose.mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank, Matrix.rank_transpose, Module.finrank_pi] at h
  have hrank := T.incidenceMatrix_rank F
  have hedge : Fintype.card T.IntersectionEdge = Nat.card T.intersectionGraph.edgeSet := by
    exact (Nat.card_eq_fintype_card).symm
  rw [topologicalGenus]
  omega

/-- The rational quadratic form associated with the symmetric intersection matrix. -/
def intersectionQuadratic (T : NumericalType) (x : T.Component → ℚ) : ℚ :=
  ∑ i, ∑ j, (T.intersection i j : ℚ) * x i * x j

/-- The intersection form is a negative weighted graph Laplacian.  This is the
quadratic-form identity underlying Stacks Project's recurring-matrix lemma. -/
lemma intersectionQuadratic_identity (T : NumericalType) (x : T.Component → ℚ) :
    2 * T.intersectionQuadratic x =
      -∑ i, ∑ j, (T.intersection i j : ℚ) *
        (T.multiplicity i : ℚ) * (T.multiplicity j : ℚ) *
          (x i / (T.multiplicity i : ℚ) -
            x j / (T.multiplicity j : ℚ)) ^ 2 := by
  classical
  let m : T.Component → ℚ := fun i => T.multiplicity i
  let y : T.Component → ℚ := fun i => x i / m i
  have hxy (i : T.Component) : x i = m i * y i := by
    dsimp [m, y]
    field_simp
  have hrow (i : T.Component) :
      ∑ j, (T.intersection i j : ℚ) * m j = 0 := by
    have h := T.fiber_relation i
    have h' : ∑ j, (T.multiplicity j : ℚ) * (T.intersection i j : ℚ) = 0 := by
      exact_mod_cast h
    calc
      _ = ∑ j, (T.multiplicity j : ℚ) * (T.intersection i j : ℚ) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [m]
        ring
      _ = 0 := h'
  have hcol (j : T.Component) :
      ∑ i, (T.intersection i j : ℚ) * m i = 0 := by
    calc
      ∑ i, (T.intersection i j : ℚ) * m i =
          ∑ i, (T.intersection j i : ℚ) * m i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [T.intersection_symm i j]
      _ = 0 := hrow j
  have hfirst :
      (∑ i, ∑ j, (T.intersection i j : ℚ) * m i * m j * y i ^ 2) = 0 := by
    calc
      _ = ∑ i, (m i * y i ^ 2) *
          (∑ j, (T.intersection i j : ℚ) * m j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by simp [hrow]
  have hsecond :
      (∑ i, ∑ j, (T.intersection i j : ℚ) * m i * m j * y j ^ 2) = 0 := by
    calc
      _ = ∑ j, ∑ i, (T.intersection i j : ℚ) * m i * m j * y j ^ 2 :=
        Finset.sum_comm
      _ = ∑ j, (m j * y j ^ 2) *
          (∑ i, (T.intersection i j : ℚ) * m i) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by simp [hcol]
  change 2 * (∑ i, ∑ j, (T.intersection i j : ℚ) * x i * x j) = _
  change _ = -∑ i, ∑ j, (T.intersection i j : ℚ) * m i * m j * (y i - y j) ^ 2
  simp_rw [hxy]
  have hexpand (i j : T.Component) :
      (T.intersection i j : ℚ) * m i * m j * (y i - y j) ^ 2 =
        (T.intersection i j : ℚ) * m i * m j * y i ^ 2 +
        (T.intersection i j : ℚ) * m i * m j * y j ^ 2 -
        2 * ((T.intersection i j : ℚ) * (m i * y i) * (m j * y j)) := by
    ring
  simp_rw [hexpand, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum]
  rw [hfirst, hsecond]
  ring

/-- The rational intersection form is negative semidefinite. -/
lemma intersectionQuadratic_nonpos (T : NumericalType) (x : T.Component → ℚ) :
    T.intersectionQuadratic x ≤ 0 := by
  classical
  have hid := T.intersectionQuadratic_identity x
  have hsum : 0 ≤ ∑ i, ∑ j, (T.intersection i j : ℚ) *
      (T.multiplicity i : ℚ) * (T.multiplicity j : ℚ) *
        (x i / (T.multiplicity i : ℚ) -
          x j / (T.multiplicity j : ℚ)) ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i = j
    · subst j
      simp
    · have hA : 0 ≤ (T.intersection i j : ℚ) := by
        exact_mod_cast T.offDiagonal_nonnegative i j hij
      positivity
  linarith

/-- Equality in the negative-semidefinite intersection form forces the coefficient divided
by the fibre multiplicity to be constant. -/
lemma ratio_eq_of_intersectionQuadratic_eq_zero (T : NumericalType)
    (x : T.Component → ℚ) (hx : T.intersectionQuadratic x = 0)
    (i j : T.Component) :
    x i / (T.multiplicity i : ℚ) = x j / (T.multiplicity j : ℚ) := by
  classical
  have hid := T.intersectionQuadratic_identity x
  rw [hx, mul_zero] at hid
  have hsum : ∑ i, ∑ j, (T.intersection i j : ℚ) *
      (T.multiplicity i : ℚ) * (T.multiplicity j : ℚ) *
        (x i / (T.multiplicity i : ℚ) -
          x j / (T.multiplicity j : ℚ)) ^ 2 = 0 := by
    linarith
  have hterm (a b : T.Component) (hab : T.intersectionGraph.Adj a b) :
      (T.intersection a b : ℚ) *
          (T.multiplicity a : ℚ) * (T.multiplicity b : ℚ) *
            (x a / (T.multiplicity a : ℚ) -
              x b / (T.multiplicity b : ℚ)) ^ 2 = 0 := by
    have hnonneg (r s : T.Component) :
        0 ≤ (T.intersection r s : ℚ) *
          (T.multiplicity r : ℚ) * (T.multiplicity s : ℚ) *
            (x r / (T.multiplicity r : ℚ) -
              x s / (T.multiplicity s : ℚ)) ^ 2 := by
      by_cases hrs : r = s
      · subst s
        simp
      · have hA : 0 ≤ (T.intersection r s : ℚ) := by
          exact_mod_cast T.offDiagonal_nonnegative r s hrs
        positivity
    have hrow :
        ∑ s, (T.intersection a s : ℚ) *
          (T.multiplicity a : ℚ) * (T.multiplicity s : ℚ) *
            (x a / (T.multiplicity a : ℚ) -
              x s / (T.multiplicity s : ℚ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun r _ => Finset.sum_nonneg fun s _ =>
        hnonneg r s).mp hsum a (Finset.mem_univ a)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun s _ => hnonneg a s).mp hrow b
      (Finset.mem_univ b)
  have hedge (a b : T.Component) (hab : T.intersectionGraph.Adj a b) :
      x a / (T.multiplicity a : ℚ) = x b / (T.multiplicity b : ℚ) := by
    have hz := hterm a b hab
    have hA : (0 : ℚ) < (T.intersection a b : ℚ) := by exact_mod_cast hab.2
    have hcoeff : (T.intersection a b : ℚ) *
        (T.multiplicity a : ℚ) * (T.multiplicity b : ℚ) ≠ 0 := by
      positivity
    have hsquare : (x a / (T.multiplicity a : ℚ) -
        x b / (T.multiplicity b : ℚ)) ^ 2 = 0 :=
      (mul_eq_zero.mp hz).resolve_left hcoeff
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  induction T.connected i j with
  | refl => rfl
  | tail h hab ih => exact ih.trans (hedge _ _ hab)

/-- The only vector of zero intersection square that vanishes at one component is zero. -/
lemma eq_zero_of_intersectionQuadratic_eq_zero_of_apply_eq_zero
    (T : NumericalType) (x : T.Component → ℚ)
    (hx : T.intersectionQuadratic x = 0) (a : T.Component) (ha : x a = 0) :
    x = 0 := by
  funext i
  have hratio := T.ratio_eq_of_intersectionQuadratic_eq_zero x hx i a
  rw [ha, zero_div] at hratio
  have hm : (T.multiplicity i : ℚ) ≠ 0 := by positivity
  exact (div_eq_zero_iff.mp hratio).resolve_right hm

/-- Extend a coefficient vector on a finite collection of components by zero. -/
def extendByZero (T : NumericalType) (s : Finset T.Component)
    (x : {i // i ∈ s} → ℚ) : T.Component → ℚ := fun i =>
  if hi : i ∈ s then x ⟨i, hi⟩ else 0

@[simp] lemma extendByZero_apply_mem (T : NumericalType) (s : Finset T.Component)
    (x : {i // i ∈ s} → ℚ) (i : {i // i ∈ s}) :
    T.extendByZero s x i = x i := by
  simp [extendByZero, i.2]

/-- The principal-submatrix quadratic form on a finite collection of components. -/
def subsetIntersectionQuadratic (T : NumericalType) (s : Finset T.Component)
    (x : {i // i ∈ s} → ℚ) : ℚ :=
  T.intersectionQuadratic (T.extendByZero s x)

/-- Every proper principal submatrix of the intersection matrix is negative definite.
This is the strict form of the recurring-matrix lemma used throughout the classification
in Stacks Project Section 55.5. -/
lemma subsetIntersectionQuadratic_neg (T : NumericalType)
    (s : Finset T.Component) (hs : s ≠ Finset.univ)
    (x : {i // i ∈ s} → ℚ) (hx : x ≠ 0) :
    T.subsetIntersectionQuadratic s x < 0 := by
  classical
  have hnonpos := T.intersectionQuadratic_nonpos (T.extendByZero s x)
  change T.subsetIntersectionQuadratic s x ≤ 0 at hnonpos
  by_contra hnot
  have hzero : T.subsetIntersectionQuadratic s x = 0 := by linarith
  obtain ⟨a, ha⟩ : ∃ a, a ∉ s := by
    by_contra h
    apply hs
    apply Finset.eq_univ_iff_forall.mpr
    intro a
    by_contra ha
    exact h ⟨a, ha⟩
  have hextzero : T.extendByZero s x = 0 := by
    have hquad : T.intersectionQuadratic (T.extendByZero s x) = 0 := hzero
    exact T.eq_zero_of_intersectionQuadratic_eq_zero_of_apply_eq_zero
      (T.extendByZero s x) hquad a (by simp [extendByZero, ha])
  apply hx
  funext i
  have hi := congrFun hextzero i.1
  simpa using hi

/-- Sum the coefficients of a finite indexed family over each component. -/
def indexedVector (T : NumericalType) {ι : Type*} [Fintype ι]
    (v : ι → T.Component) (a : ι → ℚ) : T.Component → ℚ := fun k =>
  ∑ r, if k = v r then a r else 0

/-- An injectively indexed coefficient family evaluates to its unique coefficient. -/
lemma indexedVector_apply_of_injective (T : NumericalType) {ι : Type*}
    [Fintype ι] {v : ι → T.Component} (hv : Function.Injective v)
    (a : ι → ℚ) (r : ι) : T.indexedVector v a (v r) = a r := by
  classical
  simp [indexedVector, hv.eq_iff]

private lemma sum_mul_indexedVector (T : NumericalType) {ι : Type*}
    [Fintype ι] (v : ι → T.Component) (a : ι → ℚ) (f : T.Component → ℚ) :
    ∑ k, f k * T.indexedVector v a k = ∑ r, f (v r) * a r := by
  classical
  simp only [indexedVector, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp

/-- The intersection square of a finite indexed family is its pulled-back double sum. -/
lemma intersectionQuadratic_indexedVector (T : NumericalType) {ι : Type*}
    [Fintype ι] (v : ι → T.Component) (a : ι → ℚ) :
    T.intersectionQuadratic (T.indexedVector v a) =
      ∑ r, ∑ s, (T.intersection (v r) (v s) : ℚ) * a r * a s := by
  classical
  rw [intersectionQuadratic]
  calc
    (∑ i, ∑ j, (T.intersection i j : ℚ) *
        T.indexedVector v a i * T.indexedVector v a j) =
        ∑ i, T.indexedVector v a i *
          (∑ j, (T.intersection i j : ℚ) * T.indexedVector v a j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ r, (∑ j, (T.intersection (v r) j : ℚ) *
          T.indexedVector v a j) * a r := by
      rw [show (∑ i, T.indexedVector v a i *
          (∑ j, (T.intersection i j : ℚ) * T.indexedVector v a j)) =
          ∑ i, (∑ j, (T.intersection i j : ℚ) * T.indexedVector v a j) *
            T.indexedVector v a i by
        apply Finset.sum_congr rfl
        intro i _
        ring]
      exact T.sum_mul_indexedVector v a
        (fun i => ∑ j, (T.intersection i j : ℚ) * T.indexedVector v a j)
    _ = ∑ r, (∑ s, (T.intersection (v r) (v s) : ℚ) * a s) * a r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [T.sum_mul_indexedVector v a
        (fun j => (T.intersection (v r) j : ℚ))]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      ring

/-- An injectively indexed family with proper support and a nonzero coefficient has
strictly negative intersection square. -/
lemma intersectionQuadratic_indexedVector_neg (T : NumericalType)
    {ι : Type*} [Fintype ι] {v : ι → T.Component}
    (hv : Function.Injective v) (hproper : ∃ k, ∀ r, k ≠ v r)
    (a : ι → ℚ) {r : ι} (hr : a r ≠ 0) :
    ∑ p, ∑ q, (T.intersection (v p) (v q) : ℚ) * a p * a q < 0 := by
  let x := T.indexedVector v a
  have hxne : x ≠ 0 := by
    intro hx
    have hrzero := congrFun hx (v r)
    change T.indexedVector v a (v r) = 0 at hrzero
    rw [T.indexedVector_apply_of_injective hv a r] at hrzero
    exact hr hrzero
  have hnonpos := T.intersectionQuadratic_nonpos x
  have hform : T.intersectionQuadratic x =
      ∑ p, ∑ q, (T.intersection (v p) (v q) : ℚ) * a p * a q := by
    dsimp [x]
    exact T.intersectionQuadratic_indexedVector v a
  rw [hform] at hnonpos
  by_contra hnot
  have hsumzero : (∑ p, ∑ q, (T.intersection (v p) (v q) : ℚ) * a p * a q) = 0 :=
    le_antisymm hnonpos (le_of_not_gt hnot)
  have hzero : T.intersectionQuadratic x = 0 := by
    exact hform.trans hsumzero
  obtain ⟨k, hk⟩ := hproper
  have hxk : x k = 0 := by
    dsimp [x, indexedVector]
    apply Finset.sum_eq_zero
    intro s _
    rw [if_neg (hk s)]
  have := T.eq_zero_of_intersectionQuadratic_eq_zero_of_apply_eq_zero x hzero k hxk
  exact hxne this

/-- A proper principal submatrix admits no nonzero nonnegative vector whose
matrix product is coordinatewise nonnegative. -/
lemma no_proper_subharmonic_indexedVector (T : NumericalType)
    {ι : Type*} [Fintype ι] (v : ι → T.Component)
    (hv : Function.Injective v) (hproper : ∃ x, ∀ r, x ≠ v r)
    (a : ι → ℚ) (ha : ∀ r, 0 ≤ a r) (r : ι) (hr : a r ≠ 0)
    (hrow : ∀ i, 0 ≤ ∑ j, (T.intersection (v i) (v j) : ℚ) * a j) : False := by
  have hneg := T.intersectionQuadratic_indexedVector_neg hv hproper a (r := r) hr
  have hrearrange :
      (∑ i, ∑ j, (T.intersection (v i) (v j) : ℚ) * a i * a j) =
        ∑ i, a i * ∑ j, (T.intersection (v i) (v j) : ℚ) * a j := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hrearrange] at hneg
  have hnonneg :
      0 ≤ ∑ i, a i * ∑ j, (T.intersection (v i) (v j) : ℚ) * a j := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (ha i) (hrow i)
  linarith

/-- A numerical type is minimal when it has no genus-zero component of self-intersection
`-wᵢ`, equivalently no `(-1)`-index in the terminology of Stacks Project tag `0C7A`. -/
def IsMinimal (T : NumericalType) : Prop :=
  ¬ ∃ i, T.genus i = 0 ∧ T.intersection i i = -(T.weight i : ℤ)

/-- If a connected numerical type has more than one component, every diagonal
intersection number is negative.  This is Stacks Project tag `0C74`. -/
theorem selfIntersection_neg_of_one_lt_card (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) (i : T.Component) :
    T.intersection i i < 0 := by
  classical
  have hsingleton : ({i} : Finset T.Component) ≠ Finset.univ := by
    intro h
    have hcard_one : Nat.card T.Component = 1 := by
      rw [Nat.card_eq_fintype_card]
      have := congrArg Finset.card h
      simpa using this.symm
    omega
  obtain ⟨a, ha, j, hj, haj⟩ :=
    T.noDisconnectedCut {i} (by simp) hsingleton
  have hai : a = i := by simpa using ha
  subst a
  have hji : j ≠ i := by
    intro h
    subst j
    exact hj (by simp)
  have hij_nonneg : 0 ≤ T.intersection i j :=
    T.offDiagonal_nonnegative i j hji.symm
  have hij_pos : 0 < T.intersection i j := lt_of_le_of_ne hij_nonneg haj.symm
  have hm_pos : 0 < (T.multiplicity j : ℤ) := by
    exact_mod_cast (T.multiplicity j).pos
  have hterm_pos : 0 < (T.multiplicity j : ℤ) * T.intersection i j :=
    mul_pos hm_pos hij_pos
  by_contra hnot
  have hii_nonneg : 0 ≤ T.intersection i i := le_of_not_gt hnot
  have hterms : ∀ k : T.Component,
      0 ≤ (T.multiplicity k : ℤ) * T.intersection i k := by
    intro k
    have hmk : 0 ≤ (T.multiplicity k : ℤ) := by positivity
    by_cases hki : k = i
    · subst k
      exact mul_nonneg hmk hii_nonneg
    · exact mul_nonneg hmk (T.offDiagonal_nonnegative i k (Ne.symm hki))
  have hsum_pos : 0 < ∑ k, (T.multiplicity k : ℤ) * T.intersection i k := by
    exact Finset.sum_pos' (fun k _ ↦ hterms k) ⟨j, Finset.mem_univ _, hterm_pos⟩
  rw [T.fiber_relation i] at hsum_pos
  omega

/-- Transport a numerical type along an equivalence of its finite component set. -/
abbrev reindex (T : NumericalType.{u}) {J : Type v} (e : T.Component ≃ J) : NumericalType.{v} := by
  let _ : Fintype J := Fintype.ofEquiv T.Component e
  let _ : DecidableEq J := Classical.decEq J
  letI : Nonempty J := ⟨e (Classical.choice T.componentNonempty)⟩
  exact
    { Component := J
      componentFintype := inferInstance
      componentDecidableEq := inferInstance
      componentNonempty := inferInstance
      multiplicity j := T.multiplicity (e.symm j)
      weight j := T.weight (e.symm j)
      intersection i j := T.intersection (e.symm i) (e.symm j)
      intersection_symm i j := T.intersection_symm (e.symm i) (e.symm j)
      offDiagonal_nonnegative i j hij := T.offDiagonal_nonnegative _ _ fun h ↦
        hij (e.symm.injective h)
      connected i j := by
        let r : J → J → Prop := fun a b ↦
          a ≠ b ∧ 0 < T.intersection (e.symm a) (e.symm b)
        change Relation.ReflTransGen r i j
        have h := (T.connected (e.symm i) (e.symm j)).lift e (p := r) (by
          intro a b hab
          change e a ≠ e b ∧ 0 < T.intersection (e.symm (e a)) (e.symm (e b))
          simpa only [e.symm_apply_apply] using
            (show e a ≠ e b ∧ 0 < T.intersection a b from
              ⟨fun h ↦ hab.1 (e.injective h), hab.2⟩))
        change Relation.ReflTransGen r (e (e.symm i)) (e (e.symm j)) at h
        simpa only [e.apply_symm_apply] using h
      fiber_relation i := by
        calc
          ∑ j : J, (T.multiplicity (e.symm j) : ℤ) *
              T.intersection (e.symm i) (e.symm j) =
              ∑ j : T.Component, (T.multiplicity j : ℤ) *
                T.intersection (e.symm i) j := by
            exact e.symm.sum_comp fun j ↦
              (T.multiplicity j : ℤ) * T.intersection (e.symm i) j
          _ = 0 := T.fiber_relation (e.symm i)
      weight_dvd i j := T.weight_dvd (e.symm i) (e.symm j)
      genus j := T.genus (e.symm j) }

@[simp] lemma reindex_multiplicity (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) (j : J) :
    (T.reindex e).multiplicity j = T.multiplicity (e.symm j) := rfl

@[simp] lemma reindex_weight (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) (j : J) :
    (T.reindex e).weight j = T.weight (e.symm j) := rfl

@[simp] lemma reindex_intersection (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) (i j : J) :
    (T.reindex e).intersection i j = T.intersection (e.symm i) (e.symm j) := rfl

@[simp] lemma reindex_genus (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) (j : J) :
    (T.reindex e).genus j = T.genus (e.symm j) := rfl

/-- Reindexing gives an isomorphism of intersection graphs. -/
def intersectionGraphReindexIso (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) :
    T.intersectionGraph ≃g (T.reindex e).intersectionGraph where
  toEquiv := e
  map_rel_iff' := by
    intro i j
    simp

/-- Reindexing preserves the topological genus. -/
@[simp] theorem topologicalGenus_reindex (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) :
    (T.reindex e).topologicalGenus = T.topologicalGenus := by
  rw [topologicalGenus, topologicalGenus,
    Nat.card_congr (T.intersectionGraphReindexIso e).symm.mapEdgeSet,
    Nat.card_congr e.symm]

/-- Reindexing preserves minimality. -/
@[simp] theorem isMinimal_reindex_iff (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) : (T.reindex e).IsMinimal ↔ T.IsMinimal := by
  simp only [IsMinimal, not_exists]
  constructor
  · intro h i
    simpa using h (e i)
  · intro h j
    exact h (e.symm j)

/-- Equivalence of numerical types in the sense of Stacks Project tag 0C70: a bijection of
components preserving all numerical data. -/
structure Equiv (T : NumericalType.{u}) (U : NumericalType.{v}) where
  componentEquiv : T.Component ≃ U.Component
  multiplicity_eq : ∀ i, U.multiplicity (componentEquiv i) = T.multiplicity i
  weight_eq : ∀ i, U.weight (componentEquiv i) = T.weight i
  intersection_eq : ∀ i j,
    U.intersection (componentEquiv i) (componentEquiv j) = T.intersection i j
  genus_eq : ∀ i, U.genus (componentEquiv i) = T.genus i

namespace Equiv

/-- Identity equivalence of a numerical type. -/
@[refl] def refl (T : NumericalType) : T.Equiv T where
  componentEquiv := _root_.Equiv.refl _
  multiplicity_eq _ := rfl
  weight_eq _ := rfl
  intersection_eq _ _ := rfl
  genus_eq _ := rfl

/-- Inverse of an equivalence of numerical types. -/
@[symm] def symm {T : NumericalType.{u}} {U : NumericalType.{v}} (e : T.Equiv U) : U.Equiv T where
  componentEquiv := e.componentEquiv.symm
  multiplicity_eq j := by
    simpa using (e.multiplicity_eq (e.componentEquiv.symm j)).symm
  weight_eq j := by
    simpa using (e.weight_eq (e.componentEquiv.symm j)).symm
  intersection_eq i j := by
    simpa using (e.intersection_eq (e.componentEquiv.symm i) (e.componentEquiv.symm j)).symm
  genus_eq j := by
    simpa using (e.genus_eq (e.componentEquiv.symm j)).symm

/-- Composition of equivalences of numerical types. -/
@[trans] def trans {T : NumericalType.{u}} {U : NumericalType.{v}} {V : NumericalType.{w}}
    (e : T.Equiv U) (f : U.Equiv V) : T.Equiv V where
  componentEquiv := e.componentEquiv.trans f.componentEquiv
  multiplicity_eq i := (f.multiplicity_eq (e.componentEquiv i)).trans (e.multiplicity_eq i)
  weight_eq i := (f.weight_eq (e.componentEquiv i)).trans (e.weight_eq i)
  intersection_eq i j :=
    (f.intersection_eq (e.componentEquiv i) (e.componentEquiv j)).trans (e.intersection_eq i j)
  genus_eq i := (f.genus_eq (e.componentEquiv i)).trans (e.genus_eq i)

/-- An equivalence of numerical types induces an isomorphism of intersection graphs. -/
def intersectionGraphIso {T : NumericalType.{u}} {U : NumericalType.{v}} (e : T.Equiv U) :
    T.intersectionGraph ≃g U.intersectionGraph where
  toEquiv := e.componentEquiv
  map_rel_iff' := by
    intro i j
    rw [T.intersectionGraph_adj, U.intersectionGraph_adj, e.intersection_eq]
    exact and_congr e.componentEquiv.injective.eq_iff.not (Iff.refl _)

/-- Equivalent numerical types have the same graph-theoretic topological genus. -/
theorem topologicalGenus_eq {T : NumericalType.{u}} {U : NumericalType.{v}}
    (e : T.Equiv U) : T.topologicalGenus = U.topologicalGenus := by
  rw [topologicalGenus, topologicalGenus,
    Nat.card_congr e.intersectionGraphIso.mapEdgeSet,
    Nat.card_congr e.componentEquiv]

/-- Minimality is invariant under equivalence of numerical types. -/
theorem isMinimal_iff {T : NumericalType.{u}} {U : NumericalType.{v}}
    (e : T.Equiv U) : T.IsMinimal ↔ U.IsMinimal := by
  simp only [IsMinimal, not_exists]
  constructor
  · intro h j hj
    apply h (e.componentEquiv.symm j)
    constructor
    · rw [← e.genus_eq, e.componentEquiv.apply_symm_apply]
      exact hj.1
    · rw [← e.intersection_eq, ← e.weight_eq,
        e.componentEquiv.apply_symm_apply]
      exact hj.2
  · intro h i hi
    apply h (e.componentEquiv i)
    constructor
    · rw [e.genus_eq]
      exact hi.1
    · rw [e.intersection_eq, e.weight_eq]
      exact hi.2

end Equiv

/-- The canonical equivalence from a numerical type to any reindexing of it. -/
def reindexEquiv (T : NumericalType.{u}) {J : Type v} (e : T.Component ≃ J) :
    T.Equiv (T.reindex e) where
  componentEquiv := e
  multiplicity_eq i := by simp
  weight_eq i := by simp
  intersection_eq i j := by simp
  genus_eq i := by simp

/-- The signed genus.  Division happens after summing all diagonal contributions; individual
diagonal terms need not be even, and abstract numerical types may have negative genus. -/
def arithmeticGenus (T : NumericalType) : ℤ :=
  1 + (∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) * ((T.genus i : ℤ) - 1)) -
    (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) / 2

/-- Reindexing the components does not change the signed arithmetic genus. -/
@[simp] theorem arithmeticGenus_reindex (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) : (T.reindex e).arithmeticGenus = T.arithmeticGenus := by
  let _ : Fintype J := Fintype.ofEquiv T.Component e
  let _ : DecidableEq J := Classical.decEq J
  change
    1 + (∑ j : J, (T.multiplicity (e.symm j) : ℤ) *
      (T.weight (e.symm j) : ℤ) * ((T.genus (e.symm j) : ℤ) - 1)) -
        (∑ j : J, (T.multiplicity (e.symm j) : ℤ) *
          T.intersection (e.symm j) (e.symm j)) / 2 = T.arithmeticGenus
  have hmain :
      (∑ j : J, (T.multiplicity (e.symm j) : ℤ) *
        (T.weight (e.symm j) : ℤ) * ((T.genus (e.symm j) : ℤ) - 1)) =
        ∑ i : T.Component, (T.multiplicity i : ℤ) *
          (T.weight i : ℤ) * ((T.genus i : ℤ) - 1) :=
    e.symm.sum_comp fun i ↦ (T.multiplicity i : ℤ) *
      (T.weight i : ℤ) * ((T.genus i : ℤ) - 1)
  have hdiag :
      (∑ j : J, (T.multiplicity (e.symm j) : ℤ) *
        T.intersection (e.symm j) (e.symm j)) =
        ∑ i : T.Component, (T.multiplicity i : ℤ) * T.intersection i i :=
    e.symm.sum_comp fun i ↦ (T.multiplicity i : ℤ) * T.intersection i i
  rw [hmain, hdiag]
  rfl

/-- Equivalent numerical types have the same signed arithmetic genus. -/
theorem Equiv.arithmeticGenus_eq {T : NumericalType.{u}} {U : NumericalType.{v}}
    (e : T.Equiv U) : T.arithmeticGenus = U.arithmeticGenus := by
  have hmain :
      (∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) * ((T.genus i : ℤ) - 1)) =
        ∑ j, (U.multiplicity j : ℤ) * (U.weight j : ℤ) * ((U.genus j : ℤ) - 1) := by
    calc
      _ = ∑ i, (U.multiplicity (e.componentEquiv i) : ℤ) *
          (U.weight (e.componentEquiv i) : ℤ) *
            ((U.genus (e.componentEquiv i) : ℤ) - 1) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [e.multiplicity_eq, e.weight_eq, e.genus_eq]
      _ = _ := e.componentEquiv.sum_comp fun j ↦
        (U.multiplicity j : ℤ) * (U.weight j : ℤ) * ((U.genus j : ℤ) - 1)
  have hdiag :
      (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) =
        ∑ j, (U.multiplicity j : ℤ) * U.intersection j j := by
    calc
      _ = ∑ i, (U.multiplicity (e.componentEquiv i) : ℤ) *
          U.intersection (e.componentEquiv i) (e.componentEquiv i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [e.multiplicity_eq, e.intersection_eq]
      _ = _ := e.componentEquiv.sum_comp fun j ↦
        (U.multiplicity j : ℤ) * U.intersection j j
  simp only [arithmeticGenus, hmain, hdiag]

private lemma even_finset_sum {I : Type*} (s : Finset I) (f : I → ℤ)
    (hf : ∀ i ∈ s, Even (f i)) : Even (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self _ _)).add
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

private lemma even_sum_offDiag_of_symmetric {I : Type*} (s : Finset I)
    (f : I → I → ℤ) (hf : ∀ i ∈ s, ∀ j ∈ s, f i j = f j i) :
    Even (∑ p ∈ s.offDiag, f p.1 p.2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hleft : Disjoint s.offDiag ({a} ×ˢ s) := by
        rw [Finset.disjoint_left]
        intro p hp hpa
        rw [Finset.mem_offDiag] at hp
        simp only [Finset.mem_product, Finset.mem_singleton] at hpa
        exact ha (hpa.1 ▸ hp.1)
      have hright : Disjoint (s.offDiag ∪ ({a} ×ˢ s)) (s ×ˢ {a}) := by
        rw [Finset.disjoint_left]
        intro p hp hpa
        simp only [Finset.mem_union] at hp
        simp only [Finset.mem_product, Finset.mem_singleton] at hpa
        rcases hp with hp | hp
        · rw [Finset.mem_offDiag] at hp
          exact ha (hpa.2 ▸ hp.2.1)
        · simp only [Finset.mem_product, Finset.mem_singleton] at hp
          exact ha (hp.1 ▸ hpa.1)
      have hcross : (∑ b ∈ s, f b a) = ∑ b ∈ s, f a b := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hf b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self _ _)
      obtain ⟨k, hk⟩ := ih fun i hi j hj ↦
        hf i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
      refine ⟨k + ∑ b ∈ s, f a b, ?_⟩
      rw [Finset.offDiag_insert ha, Finset.sum_union hright, Finset.sum_union hleft]
      simp only [Finset.sum_product, Finset.sum_singleton]
      rw [hcross, hk]
      ring

/-- The total multiplicity-weighted diagonal intersection is even.  This is the
integrality input in Stacks Project tag 0C71; no individual diagonal term is asserted even. -/
theorem diagonalSum_even (T : NumericalType) :
    Even (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) := by
  let m : T.Component → ℤ := fun i ↦ T.multiplicity i
  let f : T.Component → T.Component → ℤ := fun i j ↦
    m i * m j * T.intersection i j
  have hsymm : ∀ i ∈ (Finset.univ : Finset T.Component),
      ∀ j ∈ (Finset.univ : Finset T.Component), f i j = f j i := by
    intro i _ j _
    dsimp only [f]
    rw [T.intersection_symm i j]
    ring
  have hoff : Even (∑ p ∈ (Finset.univ : Finset T.Component).offDiag, f p.1 p.2) :=
    even_sum_offDiag_of_symmetric Finset.univ f hsymm
  have htotal :
      (∑ p ∈ (Finset.univ : Finset T.Component) ×ˢ Finset.univ, f p.1 p.2) = 0 := by
    rw [Finset.sum_product]
    apply Finset.sum_eq_zero
    intro i _
    calc
      ∑ j ∈ Finset.univ, f i j =
          m i * ∑ j, (T.multiplicity j : ℤ) * T.intersection i j := by
        simp only [f, m, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [T.fiber_relation i, mul_zero]
  have hsplit :
      (∑ p ∈ (Finset.univ : Finset T.Component) ×ˢ Finset.univ, f p.1 p.2) =
        (∑ i, m i * m i * T.intersection i i) +
          ∑ p ∈ (Finset.univ : Finset T.Component).offDiag, f p.1 p.2 := by
    rw [← Finset.diag_union_offDiag (s := (Finset.univ : Finset T.Component)),
      Finset.sum_union (Finset.disjoint_diag_offDiag Finset.univ)]
    simp only [Finset.sum_diag, f]
  have hdiag_sq : Even (∑ i, m i * m i * T.intersection i i) := by
    obtain ⟨k, hk⟩ := hoff
    refine ⟨-k, ?_⟩
    have hz := htotal
    rw [hsplit, hk] at hz
    omega
  have hdiff : Even
      (∑ i, ((m i * T.intersection i i) -
        (m i * m i * T.intersection i i))) := by
    apply even_finset_sum Finset.univ
    intro i _
    have hi := (Int.even_mul_pred_self (m i)).mul_right (T.intersection i i)
    rw [show m i * T.intersection i i - m i * m i * T.intersection i i =
      -(m i * (m i - 1) * T.intersection i i) by ring]
    exact hi.neg
  have hsum :
      (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) =
        (∑ i, ((m i * T.intersection i i) -
          (m i * m i * T.intersection i i))) +
          ∑ i, m i * m i * T.intersection i i := by
    simp only [m, Finset.sum_sub_distrib]
    ring
  rw [hsum]
  exact hdiff.add hdiag_sq

/-- A division-free form of the signed-genus formula. -/
theorem two_mul_arithmeticGenus (T : NumericalType) :
    2 * T.arithmeticGenus =
      2 + 2 * (∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
        ((T.genus i : ℤ) - 1)) -
          ∑ i, (T.multiplicity i : ℤ) * T.intersection i i := by
  rw [arithmeticGenus]
  have he := T.diagonalSum_even
  calc
    2 * (1 + (∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
      ((T.genus i : ℤ) - 1)) -
        (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) / 2) =
        2 + 2 * (∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.genus i : ℤ) - 1)) -
            2 * ((∑ i, (T.multiplicity i : ℤ) * T.intersection i i) / 2) := by ring
    _ = _ := by rw [Int.two_mul_ediv_two_of_even he]

/-- Twice the contribution of one component to the signed arithmetic genus. -/
def twiceComponentContribution (T : NumericalType) (i : T.Component) : ℤ :=
  2 * (T.multiplicity i : ℤ) * (T.weight i : ℤ) * ((T.genus i : ℤ) - 1) -
    (T.multiplicity i : ℤ) * T.intersection i i

/-- The division-free genus formula, split into component contributions. -/
theorem two_mul_arithmeticGenus_eq_sum_twiceComponentContribution (T : NumericalType) :
    2 * T.arithmeticGenus = 2 + ∑ i, T.twiceComponentContribution i := by
  rw [T.two_mul_arithmeticGenus]
  simp only [twiceComponentContribution, Finset.sum_sub_distrib, Finset.mul_sum]
  ring_nf

/-- On a genus-zero component of a minimal type with at least two components, the negative
self-intersection is at least twice the component weight. -/
theorem two_weight_le_neg_selfIntersection_of_minimal (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component) (i : T.Component)
    (hgenus : T.genus i = 0) :
    2 * (T.weight i : ℤ) ≤ -T.intersection i i := by
  have hneg := T.selfIntersection_neg_of_one_lt_card hcard i
  obtain ⟨k, hk⟩ := T.weight_dvd i i
  have hw : 0 < (T.weight i : ℤ) := by exact_mod_cast (T.weight i).pos
  have hkneg : k < 0 := by
    rw [hk] at hneg
    nlinarith
  have hk_ne : k ≠ -1 := by
    intro heq
    apply hmin
    refine ⟨i, hgenus, ?_⟩
    rw [hk, heq]
    ring
  have hk_le : k ≤ -2 := by omega
  rw [hk]
  nlinarith

/-- Every component contribution to the genus of a minimal type with more than one
component is nonnegative. -/
theorem twiceComponentContribution_nonnegative_of_minimal (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component) (i : T.Component) :
    0 ≤ T.twiceComponentContribution i := by
  have hm : 0 < (T.multiplicity i : ℤ) := by
    exact_mod_cast (T.multiplicity i).pos
  by_cases hg : T.genus i = 0
  · have hbound := T.two_weight_le_neg_selfIntersection_of_minimal hmin hcard i hg
    simp only [twiceComponentContribution, hg, Nat.cast_zero]
    nlinarith
  · have hgNat : 1 ≤ T.genus i := by omega
    have hgIntOne : (1 : ℤ) ≤ (T.genus i : ℤ) := by exact_mod_cast hgNat
    have hgInt : 0 ≤ (T.genus i : ℤ) - 1 := by omega
    have hw : 0 ≤ (T.weight i : ℤ) := by positivity
    have hfirst : 0 ≤
        2 * (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.genus i : ℤ) - 1) := by positivity
    have hdiag := T.selfIntersection_neg_of_one_lt_card hcard i
    have hprod : (T.multiplicity i : ℤ) * T.intersection i i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm) (le_of_lt hdiag)
    have hsecond : 0 ≤ -((T.multiplicity i : ℤ) * T.intersection i i) :=
      neg_nonneg.mpr hprod
    dsimp only [twiceComponentContribution]
    nlinarith

/-- A minimal numerical type with more than one component has arithmetic genus at least
one.  This is Stacks Project tag `0C7B`. -/
theorem one_le_arithmeticGenus_of_minimal (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component) :
    1 ≤ T.arithmeticGenus := by
  have hsum : 0 ≤ ∑ i, T.twiceComponentContribution i :=
    Finset.sum_nonneg fun i _ ↦
      T.twiceComponentContribution_nonnegative_of_minimal hmin hcard i
  have hformula := T.two_mul_arithmeticGenus_eq_sum_twiceComponentContribution
  omega

/-- Twice the local graph-theoretic contribution of a component to the topological genus. -/
def twiceTopologicalContribution (T : NumericalType) (i : T.Component) : ℤ :=
  (Nat.card (T.intersectionGraph.neighborSet i) : ℤ) - 2

/-- The handshaking formula expresses twice the topological genus as a sum of local
contributions. -/
theorem two_mul_topologicalGenus (T : NumericalType) :
    2 * (T.topologicalGenus : ℤ) =
      2 + ∑ i, T.twiceTopologicalContribution i := by
  classical
  have heuler := T.card_component_add_topologicalGenus
  have hdegrees := T.intersectionGraph.sum_degrees_eq_twice_card_edges
  have hdegreesNat :
      (∑ i, Nat.card (T.intersectionGraph.neighborSet i)) =
        2 * Nat.card T.intersectionGraph.edgeSet := by
    calc
      (∑ i, Nat.card (T.intersectionGraph.neighborSet i)) =
          ∑ i, T.intersectionGraph.degree i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.card_eq_fintype_card, T.intersectionGraph.card_neighborSet_eq_degree]
      _ = 2 * T.intersectionGraph.edgeFinset.card := hdegrees
      _ = 2 * Nat.card T.intersectionGraph.edgeSet := by
        congr 1
        rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  have heulerZ : (Nat.card T.Component : ℤ) + (T.topologicalGenus : ℤ) =
      (Nat.card T.intersectionGraph.edgeSet : ℤ) + 1 := by
    exact_mod_cast heuler
  have hdegreesZ :
      (∑ i, (Nat.card (T.intersectionGraph.neighborSet i) : ℤ)) =
        2 * (Nat.card T.intersectionGraph.edgeSet : ℤ) := by
    exact_mod_cast hdegreesNat
  simp only [twiceTopologicalContribution, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  omega

/-- The sum of the off-diagonal entries in one row of the intersection matrix. -/
def offDiagonalSum (T : NumericalType) (i : T.Component) : ℤ :=
  ∑ j, if i = j then 0 else T.intersection i j

/-- Twice the local discrepancy between the arithmetic-genus and graph-genus
contributions used in Stacks Project tag `0C7C`. -/
def twiceGenusDiscrepancy (T : NumericalType) (i : T.Component) : ℤ :=
  2 * (T.multiplicity i : ℤ) * (T.weight i : ℤ) * ((T.genus i : ℤ) - 1) +
    (T.multiplicity i : ℤ) * T.offDiagonalSum i -
      T.twiceTopologicalContribution i

/-- After summing over all components, symmetry and the fibre relation replace the weighted
diagonal sum by the multiplicity-weighted off-diagonal sum. -/
theorem sum_offDiagonalSum_weighted (T : NumericalType) :
    ∑ i, (T.multiplicity i : ℤ) * T.offDiagonalSum i =
      -∑ i, (T.multiplicity i : ℤ) * T.intersection i i := by
  classical
  let m : T.Component → ℤ := fun i ↦ T.multiplicity i
  let a : T.Component → T.Component → ℤ := T.intersection
  have hleft :
      (∑ i, m i * T.offDiagonalSum i) =
        ∑ i, ∑ j, if i = j then 0 else m i * a i j := by
    simp only [offDiagonalSum, m, a, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> simp [hij]
  have hswap :
      (∑ i, ∑ j, if i = j then 0 else m i * a i j) =
        ∑ i, ∑ j, if i = j then 0 else m j * a i j := by
    calc
      (∑ i, ∑ j, if i = j then 0 else m i * a i j) =
          ∑ j, ∑ i, if i = j then 0 else m i * a i j := Finset.sum_comm
      _ = ∑ i, ∑ j, if i = j then 0 else m j * a i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j
        · subst j
          simp
        · rw [if_neg hij, if_neg (Ne.symm hij)]
          change m j * T.intersection j i = m j * T.intersection i j
          rw [T.intersection_symm]
  rw [hleft, hswap]
  have hrow : ∀ i : T.Component,
      (∑ j, if i = j then 0 else m j * a i j) = -(m i * a i i) := by
    intro i
    have hfiber := T.fiber_relation i
    change ∑ j, m j * a i j = 0 at hfiber
    have hsplit :
        (∑ j, m j * a i j) =
          m i * a i i + ∑ j, if i = j then 0 else m j * a i j := by
      calc
        (∑ j, m j * a i j) =
            ∑ j, ((if i = j then m i * a i i else 0) +
              (if i = j then 0 else m j * a i j)) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hij : i = j
          · subst j
            simp
          · simp [hij]
        _ = (∑ j, if i = j then m i * a i i else 0) +
            ∑ j, if i = j then 0 else m j * a i j := Finset.sum_add_distrib
        _ = _ := by simp
    rw [hsplit] at hfiber
    omega
  simp only [hrow, Finset.sum_neg_distrib, m, a]

/-- The global arithmetic/topological genus gap is the sum of the local discrepancies. -/
theorem two_mul_arithmeticGenus_sub_topologicalGenus (T : NumericalType) :
    2 * (T.arithmeticGenus - (T.topologicalGenus : ℤ)) =
      ∑ i, T.twiceGenusDiscrepancy i := by
  rw [mul_sub, T.two_mul_arithmeticGenus_eq_sum_twiceComponentContribution,
    T.two_mul_topologicalGenus]
  have hcancel : 2 + (∑ i, T.twiceComponentContribution i) -
      (2 + ∑ i, T.twiceTopologicalContribution i) =
      (∑ i, T.twiceComponentContribution i) -
        ∑ i, T.twiceTopologicalContribution i := by ring
  rw [hcancel]
  simp only [twiceComponentContribution, twiceGenusDiscrepancy,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [T.sum_offDiagonalSum_weighted]
  ring

/-- The intersection index seen from the source component, divided by its weight. -/
def normalizedIntersection (T : NumericalType) (i j : T.Component) : ℤ :=
  T.intersection i j / (T.weight i : ℤ)

/-- Division by the source weight in `normalizedIntersection` is exact. -/
lemma normalizedIntersection_mul_weight (T : NumericalType) (i j : T.Component) :
    T.normalizedIntersection i j * (T.weight i : ℤ) = T.intersection i j := by
  apply Int.ediv_mul_cancel
  exact T.weight_dvd i j

/-- A positive off-diagonal intersection has positive normalized intersection index. -/
lemma normalizedIntersection_pos_of_adj (T : NumericalType) {i j : T.Component}
    (hij : T.intersectionGraph.Adj i j) :
    0 < T.normalizedIntersection i j := by
  have hw : 0 < (T.weight i : ℤ) := by exact_mod_cast (T.weight i).pos
  have hexact := T.normalizedIntersection_mul_weight i j
  have hnonneg : 0 ≤ T.normalizedIntersection i j :=
    Int.ediv_nonneg (le_of_lt hij.2) (le_of_lt hw)
  have hne : T.normalizedIntersection i j ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hexact
    exact (ne_of_gt hij.2) hexact.symm
  omega

/-- A positive off-diagonal entry is at least the source component weight. -/
lemma weight_le_intersection_of_adj (T : NumericalType) {i j : T.Component}
    (hij : T.intersectionGraph.Adj i j) :
    (T.weight i : ℤ) ≤ T.intersection i j := by
  have hnorm : 1 ≤ T.normalizedIntersection i j :=
    T.normalizedIntersection_pos_of_adj hij
  have hw : (0 : ℤ) < T.weight i := by positivity
  rw [← T.normalizedIntersection_mul_weight i j]
  nlinarith

/-- Sum of the source-normalized off-diagonal intersection indices in one row. -/
def normalizedOffDiagonalSum (T : NumericalType) (i : T.Component) : ℤ :=
  ∑ j, if i = j then 0 else T.normalizedIntersection i j

/-- Clearing the source weight recovers the ordinary off-diagonal row sum. -/
lemma weight_mul_normalizedOffDiagonalSum (T : NumericalType) (i : T.Component) :
    (T.weight i : ℤ) * T.normalizedOffDiagonalSum i = T.offDiagonalSum i := by
  classical
  simp only [normalizedOffDiagonalSum, offDiagonalSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · rw [if_neg hij, if_neg hij]
    rw [mul_comm, T.normalizedIntersection_mul_weight]

/-- A nonadjacent off-diagonal normalized intersection index vanishes. -/
lemma normalizedIntersection_eq_zero_of_not_adj (T : NumericalType)
    {i j : T.Component} (hne : i ≠ j) (hnot : ¬ T.intersectionGraph.Adj i j) :
    T.normalizedIntersection i j = 0 := by
  have hnonneg := T.offDiagonal_nonnegative i j hne
  have hnotpos : ¬ 0 < T.intersection i j := fun hpos ↦ hnot ⟨hne, hpos⟩
  have hzero : T.intersection i j = 0 := by omega
  simp [normalizedIntersection, hzero]

/-- The normalized off-diagonal sum may be taken over the graph neighbors. -/
lemma normalizedOffDiagonalSum_eq_neighborSum (T : NumericalType) (i : T.Component) :
    T.normalizedOffDiagonalSum i =
      ∑ j : T.intersectionGraph.neighborSet i,
        T.normalizedIntersection i (j : T.Component) := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun j : T.Component ↦ T.intersectionGraph.Adj i j)
    (by simp) (fun j ↦ T.normalizedIntersection i j)]
  simp only [normalizedOffDiagonalSum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hadj : T.intersectionGraph.Adj i j
  · rw [if_neg hadj.ne, if_pos hadj]
  · by_cases hji : i = j
    · subst j
      simp
    · rw [if_neg hji, if_neg hadj]
      exact T.normalizedIntersection_eq_zero_of_not_adj hji hadj

/-- Each neighbor contributes at least one to the normalized off-diagonal sum. -/
lemma neighborCount_le_normalizedOffDiagonalSum (T : NumericalType) (i : T.Component) :
    (Nat.card (T.intersectionGraph.neighborSet i) : ℤ) ≤
      T.normalizedOffDiagonalSum i := by
  rw [T.normalizedOffDiagonalSum_eq_neighborSum]
  rw [Nat.card_eq_fintype_card]
  calc
    (Fintype.card (T.intersectionGraph.neighborSet i) : ℤ) =
        ∑ _j : T.intersectionGraph.neighborSet i, (1 : ℤ) := by simp
    _ ≤ ∑ j : T.intersectionGraph.neighborSet i,
        T.normalizedIntersection i (j : T.Component) := by
      apply Finset.sum_le_sum
      intro j _
      have := T.normalizedIntersection_pos_of_adj j.2
      omega

/-- Product of the multiplicity and weight of a component. -/
def vertexMass (T : NumericalType) (i : T.Component) : ℤ :=
  (T.multiplicity i : ℤ) * (T.weight i : ℤ)

lemma vertexMass_pos (T : NumericalType) (i : T.Component) :
    0 < T.vertexMass i := by
  dsimp only [vertexMass]
  positivity

/-- Local discrepancy in terms of the normalized intersection indices. -/
lemma twiceGenusDiscrepancy_eq (T : NumericalType) (i : T.Component) :
    T.twiceGenusDiscrepancy i =
      T.vertexMass i *
        (2 * (T.genus i : ℤ) - 2 + T.normalizedOffDiagonalSum i) -
          T.twiceTopologicalContribution i := by
  have hexact := T.weight_mul_normalizedOffDiagonalSum i
  simp only [twiceGenusDiscrepancy, vertexMass]
  nlinarith

/-- The vertices with negative local discrepancy in the proof of `g_top ≤ g`. -/
def IsBadVertex (T : NumericalType) (i : T.Component) : Prop :=
  T.genus i = 0 ∧
    Nat.card (T.intersectionGraph.neighborSet i) = 1 ∧
    1 < T.vertexMass i ∧
    T.normalizedOffDiagonalSum i = 1

/-- In a connected numerical type with more than one component, every component has a
neighbor. -/
lemma neighborCount_pos_of_one_lt_card (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) (i : T.Component) :
    0 < Nat.card (T.intersectionGraph.neighborSet i) := by
  classical
  have hsingleton : ({i} : Finset T.Component) ≠ Finset.univ := by
    intro h
    have hcard_one : Nat.card T.Component = 1 := by
      rw [Nat.card_eq_fintype_card]
      have := congrArg Finset.card h
      simpa using this.symm
    omega
  obtain ⟨a, ha, k, hk, hak⟩ :=
    T.noDisconnectedCut {i} (by simp) hsingleton
  have hai : a = i := by simpa using ha
  subst a
  have hki : k ≠ i := by
    intro h
    subst k
    exact hk (by simp)
  have hnonneg := T.offDiagonal_nonnegative i k hki.symm
  have hpos : 0 < T.intersection i k := lt_of_le_of_ne hnonneg hak.symm
  let _ : Nonempty (T.intersectionGraph.neighborSet i) :=
    ⟨⟨k, ⟨hki.symm, hpos⟩⟩⟩
  exact Nat.card_pos

/-- Exact classification of negative local discrepancies: they occur precisely at the
bad leaves described in Stacks Project tag `0C7C`. -/
lemma twiceGenusDiscrepancy_neg_iff (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) (i : T.Component) :
    T.twiceGenusDiscrepancy i < 0 ↔ T.IsBadVertex i := by
  have hp := T.vertexMass_pos i
  have hdNat := T.neighborCount_pos_of_one_lt_card hcard i
  have hsum := T.neighborCount_le_normalizedOffDiagonalSum i
  rw [T.twiceGenusDiscrepancy_eq]
  simp only [twiceTopologicalContribution]
  constructor
  · intro hneg
    have hg : T.genus i = 0 := by
      by_contra hg
      have hgNat : 1 ≤ T.genus i := by omega
      have hgInt : (1 : ℤ) ≤ (T.genus i : ℤ) := by exact_mod_cast hgNat
      nlinarith
    have hd : Nat.card (T.intersectionGraph.neighborSet i) = 1 := by
      by_contra hd
      have : 2 ≤ Nat.card (T.intersectionGraph.neighborSet i) := by omega
      have hdInt : (2 : ℤ) ≤
          (Nat.card (T.intersectionGraph.neighborSet i) : ℤ) := by exact_mod_cast this
      simp only [hg, Nat.cast_zero] at hneg
      nlinarith
    have hs : T.normalizedOffDiagonalSum i = 1 := by
      have hdInt : (Nat.card (T.intersectionGraph.neighborSet i) : ℤ) = 1 := by
        exact_mod_cast hd
      by_contra hs
      have hsInt : 2 ≤ T.normalizedOffDiagonalSum i := by omega
      simp only [hg, Nat.cast_zero] at hneg
      nlinarith
    have hmass : 1 < T.vertexMass i := by
      by_contra hm
      have hmle : T.vertexMass i ≤ 1 := le_of_not_gt hm
      have hpone : T.vertexMass i = 1 := by omega
      simp only [hg, Nat.cast_zero, hd, Nat.cast_one, hs, hpone] at hneg
      omega
    exact ⟨hg, hd, hmass, hs⟩
  · rintro ⟨hg, hd, hmass, hs⟩
    simp only [hg, Nat.cast_zero, hd, Nat.cast_one, hs]
    nlinarith

/-- A bad vertex has a unique graph neighbor. -/
lemma IsBadVertex.existsUnique_neighbor (T : NumericalType) {i : T.Component}
    (hbad : T.IsBadVertex i) :
    ∃! j : T.Component, T.intersectionGraph.Adj i j := by
  obtain ⟨j, hj⟩ := Nat.card_eq_one_iff_exists.mp hbad.2.1
  refine ⟨j.1, j.2, ?_⟩
  intro k hk
  exact congrArg Subtype.val (hj ⟨k, hk⟩)

/-- The unique neighbor of a bad vertex. -/
noncomputable def badNeighbor (T : NumericalType) {i : T.Component}
    (hbad : T.IsBadVertex i) : T.Component :=
  Classical.choose (hbad.existsUnique_neighbor T)

lemma badNeighbor_adj (T : NumericalType) {i : T.Component}
    (hbad : T.IsBadVertex i) :
    T.intersectionGraph.Adj i (T.badNeighbor hbad) :=
  (Classical.choose_spec (hbad.existsUnique_neighbor T)).1

lemma eq_badNeighbor_of_adj (T : NumericalType) {i j : T.Component}
    (hbad : T.IsBadVertex i) (hij : T.intersectionGraph.Adj i j) :
    j = T.badNeighbor hbad :=
  (Classical.choose_spec (hbad.existsUnique_neighbor T)).2 j hij

/-- Every edge leaving a bad vertex has normalized intersection index one. -/
lemma normalizedIntersection_eq_one_of_bad (T : NumericalType) {i j : T.Component}
    (hbad : T.IsBadVertex i) (hij : T.intersectionGraph.Adj i j) :
    T.normalizedIntersection i j = 1 := by
  have hpos := T.normalizedIntersection_pos_of_adj hij
  have hle : T.normalizedIntersection i j ≤ T.normalizedOffDiagonalSum i := by
    rw [T.normalizedOffDiagonalSum_eq_neighborSum]
    simpa using (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun k : T.intersectionGraph.neighborSet i ↦
        T.normalizedIntersection i (k : T.Component))
      (fun k _ ↦ le_of_lt (T.normalizedIntersection_pos_of_adj k.2))
      (Finset.mem_univ ⟨j, hij⟩))
  rw [hbad.2.2.2] at hle
  omega

/-- Every edge leaving a bad vertex has intersection number equal to the bad vertex's
weight. -/
lemma intersection_eq_weight_of_bad (T : NumericalType) {i j : T.Component}
    (hbad : T.IsBadVertex i) (hij : T.intersectionGraph.Adj i j) :
    T.intersection i j = (T.weight i : ℤ) := by
  have hexact := T.normalizedIntersection_mul_weight i j
  rw [T.normalizedIntersection_eq_one_of_bad hbad hij] at hexact
  simpa using hexact.symm

/-- At a bad leaf, the fibre relation has only its diagonal and unique-neighbor terms. -/
lemma fiber_relation_of_bad_leaf (T : NumericalType) {i j : T.Component}
    (hbad : T.IsBadVertex i) (hij : T.intersectionGraph.Adj i j) :
    (T.multiplicity i : ℤ) * T.intersection i i +
      (T.multiplicity j : ℤ) * T.intersection i j = 0 := by
  classical
  have hfiber := T.fiber_relation i
  have hreduce :
      (∑ k, (T.multiplicity k : ℤ) * T.intersection i k) =
        (T.multiplicity i : ℤ) * T.intersection i i +
          (T.multiplicity j : ℤ) * T.intersection i j := by
    calc
      (∑ k, (T.multiplicity k : ℤ) * T.intersection i k) =
          ∑ k, ((if k = i then (T.multiplicity i : ℤ) * T.intersection i i else 0) +
            (if k = j then (T.multiplicity j : ℤ) * T.intersection i j else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hki : k = i
        · subst k
          simp [hij.ne]
        · by_cases hkj : k = j
          · subst k
            simp [hki]
          · have hnotadj : ¬ T.intersectionGraph.Adj i k := by
              intro hik
              exact hkj ((T.eq_badNeighbor_of_adj hbad hik).trans
                (T.eq_badNeighbor_of_adj hbad hij).symm)
            have hzero : T.intersection i k = 0 := by
              have hnonneg := T.offDiagonal_nonnegative i k (Ne.symm hki)
              have hnotpos : ¬ 0 < T.intersection i k := fun hpos ↦
                hnotadj ⟨Ne.symm hki, hpos⟩
              omega
            simp [hki, hkj, hzero]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hreduce] at hfiber
  exact hfiber

/-- Along the unique edge leaving a bad vertex of a minimal type, the neighboring
multiplicity is at least twice the leaf multiplicity. -/
lemma two_mul_multiplicity_le_of_bad (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component) {i j : T.Component}
    (hbad : T.IsBadVertex i) (hij : T.intersectionGraph.Adj i j) :
    2 * (T.multiplicity i : ℤ) ≤ (T.multiplicity j : ℤ) := by
  have hdiag := T.two_weight_le_neg_selfIntersection_of_minimal
    hmin hcard i hbad.1
  have hedge := T.intersection_eq_weight_of_bad hbad hij
  have hfiber := T.fiber_relation_of_bad_leaf hbad hij
  have hm : 0 ≤ (T.multiplicity i : ℤ) := by positivity
  have hw : 0 < (T.weight i : ℤ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdiag hm
  rw [hedge] at hfiber
  have hweighted :
      (2 * (T.multiplicity i : ℤ)) * (T.weight i : ℤ) ≤
        (T.multiplicity j : ℤ) * (T.weight i : ℤ) := by
    calc
      (2 * (T.multiplicity i : ℤ)) * (T.weight i : ℤ) =
          (T.multiplicity i : ℤ) * (2 * (T.weight i : ℤ)) := by ring
      _ ≤ (T.multiplicity i : ℤ) * (-T.intersection i i) := hmul
      _ = (T.multiplicity j : ℤ) * (T.weight i : ℤ) := by nlinarith
  exact (Int.mul_le_mul_right hw).mp hweighted

/-- A neutral vertex in the `0C7C` discharging argument: it has genus zero, exactly two
neighbors, and both normalized edge indices are forced to be one. -/
def IsNeutralVertex (T : NumericalType) (i : T.Component) : Prop :=
  T.genus i = 0 ∧
    Nat.card (T.intersectionGraph.neighborSet i) = 2 ∧
    T.normalizedOffDiagonalSum i = 2

lemma IsBadVertex.not_neutral (T : NumericalType) {i : T.Component}
    (hbad : T.IsBadVertex i) : ¬ T.IsNeutralVertex i := by
  intro hneutral
  have hbadDegree := hbad.2.1
  have hneutralDegree := hneutral.2.1
  omega

/-- A neutral vertex has zero local genus discrepancy. -/
lemma twiceGenusDiscrepancy_eq_zero_of_neutral (T : NumericalType)
    {i : T.Component} (hneutral : T.IsNeutralVertex i) :
    T.twiceGenusDiscrepancy i = 0 := by
  rw [T.twiceGenusDiscrepancy_eq]
  rcases hneutral with ⟨hg, hd, hs⟩
  have hdZ : (Nat.card (T.intersectionGraph.neighborSet i) : ℤ) = 2 := by
    exact_mod_cast hd
  simp only [twiceTopologicalContribution, hg, Nat.cast_zero, hs, hdZ]
  ring

/-- Every edge leaving a neutral vertex has normalized intersection index one. -/
lemma normalizedIntersection_eq_one_of_neutral (T : NumericalType)
    {i j : T.Component} (hneutral : T.IsNeutralVertex i)
    (hij : T.intersectionGraph.Adj i j) :
    T.normalizedIntersection i j = 1 := by
  have hsum := T.normalizedOffDiagonalSum_eq_neighborSum i
  have hcard : Fintype.card (T.intersectionGraph.neighborSet i) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hneutral.2.1
  have htotal :
      (∑ k : T.intersectionGraph.neighborSet i,
        T.normalizedIntersection i (k : T.Component)) = 2 := by
    rw [← hsum]
    exact hneutral.2.2
  have hdiff :
      (∑ k : T.intersectionGraph.neighborSet i,
        (T.normalizedIntersection i (k : T.Component) - 1)) = 0 := by
    rw [Finset.sum_sub_distrib, htotal]
    simp [hcard]
  have hnonneg : ∀ k : T.intersectionGraph.neighborSet i,
      0 ≤ T.normalizedIntersection i (k : T.Component) - 1 := by
    intro k
    have := T.normalizedIntersection_pos_of_adj k.2
    omega
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ ↦ hnonneg k)).mp hdiff ⟨j, hij⟩ (Finset.mem_univ _)
  change T.normalizedIntersection i j - 1 = 0 at hzero
  omega

/-- Every edge leaving a neutral vertex has intersection number equal to the neutral
vertex's weight. -/
lemma intersection_eq_weight_of_neutral (T : NumericalType)
    {i j : T.Component} (hneutral : T.IsNeutralVertex i)
    (hij : T.intersectionGraph.Adj i j) :
    T.intersection i j = (T.weight i : ℤ) := by
  have hexact := T.normalizedIntersection_mul_weight i j
  rw [T.normalizedIntersection_eq_one_of_neutral hneutral hij] at hexact
  simpa using hexact.symm

/-- If an edge equals both endpoint weights, those weights agree. -/
lemma weight_eq_of_intersection_eq_endpoint_weights (T : NumericalType) {i j : T.Component}
    (hi : T.intersection i j = (T.weight i : ℤ))
    (hj : T.intersection j i = (T.weight j : ℤ)) :
    T.weight i = T.weight j := by
  apply PNat.eq
  exact_mod_cast hi.symm.trans ((T.intersection_symm i j).trans hj)

/-- Once one incident edge of a neutral vertex is designated as incoming, there is a unique
other neighbor. -/
lemma IsNeutralVertex.existsUnique_otherNeighbor (T : NumericalType)
    {i p : T.Component} (hneutral : T.IsNeutralVertex i)
    (hpi : T.intersectionGraph.Adj i p) :
    ∃! q : T.Component, T.intersectionGraph.Adj i q ∧ q ≠ p := by
  let pp : T.intersectionGraph.neighborSet i := ⟨p, hpi⟩
  have hcard : Nat.card (T.intersectionGraph.neighborSet i) = 2 := hneutral.2.1
  obtain ⟨q, hq⟩ := (Nat.card_eq_two_iff' pp).mp hcard
  refine ⟨q.1, ⟨q.2, ?_⟩, ?_⟩
  · intro h
    apply hq.1
    apply Subtype.ext
    exact h
  · intro r hr
    exact congrArg Subtype.val (hq.2 ⟨r, hr.1⟩ (by
      intro h
      apply hr.2
      exact congrArg Subtype.val h))

/-- The unique outgoing neighbor of a neutral vertex after selecting an incoming neighbor. -/
noncomputable def neutralOtherNeighbor (T : NumericalType) {i p : T.Component}
    (hneutral : T.IsNeutralVertex i) (hpi : T.intersectionGraph.Adj i p) :
    T.Component :=
  Classical.choose (hneutral.existsUnique_otherNeighbor T hpi)

lemma neutralOtherNeighbor_spec (T : NumericalType) {i p : T.Component}
    (hneutral : T.IsNeutralVertex i) (hpi : T.intersectionGraph.Adj i p) :
    T.intersectionGraph.Adj i (T.neutralOtherNeighbor hneutral hpi) ∧
      T.neutralOtherNeighbor hneutral hpi ≠ p :=
  (Classical.choose_spec (hneutral.existsUnique_otherNeighbor T hpi)).1

/-- The fibre relation at a neutral vertex consists of its diagonal and its two incident
edge terms. -/
lemma fiber_relation_of_neutral (T : NumericalType) {i p q : T.Component}
    (hneutral : T.IsNeutralVertex i) (hpi : T.intersectionGraph.Adj i p)
    (hqi : T.intersectionGraph.Adj i q) (hpq : p ≠ q) :
    (T.multiplicity i : ℤ) * T.intersection i i +
      (T.multiplicity p : ℤ) * T.intersection i p +
      (T.multiplicity q : ℤ) * T.intersection i q = 0 := by
  classical
  have hfiber := T.fiber_relation i
  have hreduce :
      (∑ k, (T.multiplicity k : ℤ) * T.intersection i k) =
        (T.multiplicity i : ℤ) * T.intersection i i +
          (T.multiplicity p : ℤ) * T.intersection i p +
          (T.multiplicity q : ℤ) * T.intersection i q := by
    calc
      (∑ k, (T.multiplicity k : ℤ) * T.intersection i k) =
          ∑ k, ((if k = i then (T.multiplicity i : ℤ) * T.intersection i i else 0) +
            (if k = p then (T.multiplicity p : ℤ) * T.intersection i p else 0) +
            (if k = q then (T.multiplicity q : ℤ) * T.intersection i q else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hki : k = i
        · subst k
          simp [hpi.ne, hqi.ne]
        · by_cases hkp : k = p
          · subst k
            simp [hki, hpq]
          · by_cases hkq : k = q
            · subst k
              simp [hki, hkp]
            · have hnotadj : ¬ T.intersectionGraph.Adj i k := by
                intro hik
                have hkother : k ≠ p := hkp
                have hqother : q ≠ p := hpq.symm
                have hk_eq_q : k = q :=
                  (hneutral.existsUnique_otherNeighbor T hpi).unique
                    ⟨hik, hkother⟩ ⟨hqi, hqother⟩
                exact hkq hk_eq_q
              have hzero : T.intersection i k = 0 := by
                have hnonneg := T.offDiagonal_nonnegative i k (Ne.symm hki)
                have hnotpos : ¬ 0 < T.intersection i k := fun hpos ↦
                  hnotadj ⟨Ne.symm hki, hpos⟩
                omega
              simp [hki, hkp, hkq, hzero]
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hreduce] at hfiber
  exact hfiber

/-- At a neutral vertex of a minimal type, twice the central multiplicity is bounded by
the sum of the two neighboring multiplicities. -/
lemma two_mul_multiplicity_le_neighbor_sum_of_neutral (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component) {i p q : T.Component}
    (hneutral : T.IsNeutralVertex i) (hpi : T.intersectionGraph.Adj i p)
    (hqi : T.intersectionGraph.Adj i q) (hpq : p ≠ q) :
    2 * (T.multiplicity i : ℤ) ≤
      (T.multiplicity p : ℤ) + (T.multiplicity q : ℤ) := by
  have hdiag := T.two_weight_le_neg_selfIntersection_of_minimal
    hmin hcard i hneutral.1
  have hpEdge := T.intersection_eq_weight_of_neutral hneutral hpi
  have hqEdge := T.intersection_eq_weight_of_neutral hneutral hqi
  have hfiber := T.fiber_relation_of_neutral hneutral hpi hqi hpq
  rw [hpEdge, hqEdge] at hfiber
  have hm : 0 ≤ (T.multiplicity i : ℤ) := by positivity
  have hw : 0 < (T.weight i : ℤ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdiag hm
  apply (Int.mul_le_mul_right hw).mp
  calc
    (2 * (T.multiplicity i : ℤ)) * (T.weight i : ℤ) =
        (T.multiplicity i : ℤ) * (2 * (T.weight i : ℤ)) := by ring
    _ ≤ (T.multiplicity i : ℤ) * (-T.intersection i i) := hmul
    _ = ((T.multiplicity p : ℤ) + (T.multiplicity q : ℤ)) *
        (T.weight i : ℤ) := by nlinarith

private lemma convex_sequence_bounds (m : ℕ → ℤ) (n : ℕ)
    (hpos : 0 < m 0) (hbase : 2 * m 0 ≤ m 1)
    (hconvex : ∀ r < n, 2 * m (r + 1) ≤ m r + m (r + 2)) :
    m 0 ≤ m (n + 1) - m n ∧ 2 * m 0 ≤ m (n + 1) := by
  induction n with
  | zero =>
      simp only [Nat.zero_add]
      constructor <;> omega
  | succ n ih =>
      have ih' := ih (fun r hr ↦ hconvex r (lt_trans hr (Nat.lt_succ_self n)))
      have hstep := hconvex n (Nat.lt_succ_self n)
      change m 0 ≤ m (n + 2) - m (n + 1) ∧ 2 * m 0 ≤ m (n + 2)
      have hstep' : 2 * m (n + 1) ≤ m n + m (n + 2) := by
        simpa only [Nat.succ_eq_add_one] using hstep
      constructor <;> omega

/-- A simple path from `source` to `target` whose internal vertices are neutral.  Its
`length` is the number of internal neutral vertices, so the vertex array has two more entries. -/
structure NeutralCorridor (T : NumericalType) (source target : T.Component) where
  length : ℕ
  vertex : Fin (length + 2) → T.Component
  vertex_injective : Function.Injective vertex
  source_eq : vertex ⟨0, by omega⟩ = source
  target_eq : vertex ⟨length + 1, by omega⟩ = target
  adjacent : ∀ r : Fin (length + 1),
    T.intersectionGraph.Adj (vertex r.castSucc) (vertex r.succ)
  neutral : ∀ r : Fin length, T.IsNeutralVertex (vertex r.succ.castSucc)

namespace NeutralCorridor

variable {T : NumericalType} {source target : T.Component}

/-- A nontrivial simple graph walk with neutral internal vertices determines a neutral
corridor. -/
noncomputable def ofWalk
    (p : T.intersectionGraph.Walk source target) (hp : p.IsPath) (hlen : 0 < p.length)
    (hinner : ∀ r, 0 < r → r < p.length → T.IsNeutralVertex (p.getVert r)) :
    T.NeutralCorridor source target where
  length := p.length - 1
  vertex r := p.getVert r
  vertex_injective := by
    intro a b hab
    apply Fin.ext
    exact hp.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hab
  source_eq := p.getVert_zero
  target_eq := by
    have hidx : p.length - 1 + 1 = p.length := Nat.sub_add_cancel (by omega)
    simpa only [hidx] using p.getVert_length
  adjacent r := by
    apply p.adj_getVert_succ
    have hidx : p.length - 1 + 1 = p.length := Nat.sub_add_cancel (by omega)
    have hr : r.val < p.length := by
      simpa only [hidx] using r.isLt
    exact hr
  neutral r := by
    apply hinner (r + 1) (by omega)
    have hsub : p.length - 1 < p.length := Nat.sub_lt hlen (by omega)
    omega

def multiplicitySequence (C : T.NeutralCorridor source target) (r : ℕ) : ℤ :=
  if h : r < C.length + 2 then (T.multiplicity (C.vertex ⟨r, h⟩) : ℤ) else 0

@[simp] lemma multiplicitySequence_of_lt
    (C : T.NeutralCorridor source target) (r : ℕ) (hr : r < C.length + 2) :
    C.multiplicitySequence r = (T.multiplicity (C.vertex ⟨r, hr⟩) : ℤ) := by
  simp only [multiplicitySequence, dif_pos hr]

/-- Multiplicity at the target of a neutral corridor is at least twice the multiplicity of
its bad source. -/
lemma two_mul_sourceMultiplicity_le_targetMultiplicity
    (C : T.NeutralCorridor source target) (hmin : T.IsMinimal)
    (hcard : 1 < Nat.card T.Component) (hbad : T.IsBadVertex source) :
    2 * (T.multiplicity source : ℤ) ≤ (T.multiplicity target : ℤ) := by
  let m : ℕ → ℤ := C.multiplicitySequence
  have hm0 : m 0 = (T.multiplicity source : ℤ) := by
    rw [show m 0 = (T.multiplicity (C.vertex ⟨0, by omega⟩) : ℤ) by
      exact C.multiplicitySequence_of_lt 0 (by omega)]
    rw [C.source_eq]
  have hmTarget : m (C.length + 1) = (T.multiplicity target : ℤ) := by
    rw [show m (C.length + 1) =
        (T.multiplicity (C.vertex ⟨C.length + 1, by omega⟩) : ℤ) by
      exact C.multiplicitySequence_of_lt _ (by omega)]
    rw [C.target_eq]
  have hpos : 0 < m 0 := by rw [hm0]; positivity
  have hbase : 2 * m 0 ≤ m 1 := by
    let e0 : Fin (C.length + 1) := ⟨0, by omega⟩
    have hadj := C.adjacent e0
    have hv0 : C.vertex e0.castSucc = source := by
      simpa [e0] using C.source_eq
    have hleaf : T.intersectionGraph.Adj source (C.vertex e0.succ) := by
      rw [hv0] at hadj
      exact hadj
    have h := T.two_mul_multiplicity_le_of_bad hmin hcard hbad hleaf
    rw [hm0]
    rw [show m 1 = (T.multiplicity (C.vertex e0.succ) : ℤ) by
      exact C.multiplicitySequence_of_lt 1 (by omega)]
    exact h
  have hconvex : ∀ r < C.length,
      2 * m (r + 1) ≤ m r + m (r + 2) := by
    intro r hr
    let fr : Fin C.length := ⟨r, hr⟩
    have hprev := C.adjacent fr.castSucc
    have hnext := C.adjacent fr.succ
    have hneFin : fr.castSucc.castSucc ≠ fr.succ.succ := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have hneVertex : C.vertex fr.castSucc.castSucc ≠ C.vertex fr.succ.succ :=
      fun h ↦ hneFin (C.vertex_injective h)
    have hrec := T.two_mul_multiplicity_le_neighbor_sum_of_neutral hmin hcard
      (C.neutral fr) hprev.symm hnext hneVertex
    change 2 * (T.multiplicity (C.vertex fr.succ.castSucc) : ℤ) ≤
      (T.multiplicity (C.vertex fr.castSucc.castSucc) : ℤ) +
        (T.multiplicity (C.vertex fr.succ.succ) : ℤ) at hrec
    rw [show m (r + 1) = (T.multiplicity (C.vertex fr.succ.castSucc) : ℤ) by
      exact C.multiplicitySequence_of_lt _ (by omega)]
    rw [show m r = (T.multiplicity (C.vertex fr.castSucc.castSucc) : ℤ) by
      exact C.multiplicitySequence_of_lt _ (by omega)]
    rw [show m (r + 2) = (T.multiplicity (C.vertex fr.succ.succ) : ℤ) by
      exact C.multiplicitySequence_of_lt _ (by omega)]
    exact hrec
  have hbound := convex_sequence_bounds m C.length hpos hbase hconvex
  rw [hm0, hmTarget] at hbound
  exact hbound.2

/-- Every internal neutral vertex has the same weight as the bad source. -/
lemma internal_weight_eq_source (C : T.NeutralCorridor source target)
    (hbad : T.IsBadVertex source) :
    ∀ r (hr : r < C.length),
      T.weight (C.vertex ⟨r + 1, by omega⟩) = T.weight source := by
  intro r
  induction r with
  | zero =>
      intro hr
      have hadj : T.intersectionGraph.Adj
          (C.vertex ⟨0, by omega⟩) (C.vertex ⟨1, by omega⟩) :=
        C.adjacent ⟨0, by omega⟩
      have hv0 : C.vertex ⟨0, by omega⟩ = source := C.source_eq
      rw [hv0] at hadj
      have hsource := T.intersection_eq_weight_of_bad hbad hadj
      have hneutral := C.neutral ⟨0, hr⟩
      change T.IsNeutralVertex (C.vertex ⟨1, by omega⟩) at hneutral
      have htarget := T.intersection_eq_weight_of_neutral hneutral hadj.symm
      exact (T.weight_eq_of_intersection_eq_endpoint_weights hsource htarget).symm
  | succ r ih =>
      intro hr
      have hrPrev : r < C.length := by omega
      have hweightPrev := ih hrPrev
      have hadj : T.intersectionGraph.Adj
          (C.vertex ⟨r + 1, by omega⟩) (C.vertex ⟨r + 2, by omega⟩) :=
        C.adjacent ⟨r + 1, by omega⟩
      have hneutralPrev := C.neutral ⟨r, hrPrev⟩
      change T.IsNeutralVertex (C.vertex ⟨r + 1, by omega⟩) at hneutralPrev
      have hneutralNext := C.neutral ⟨r + 1, hr⟩
      change T.IsNeutralVertex (C.vertex ⟨r + 2, by omega⟩) at hneutralNext
      have hprev := T.intersection_eq_weight_of_neutral hneutralPrev hadj
      have hnext := T.intersection_eq_weight_of_neutral hneutralNext hadj.symm
      have heq := T.weight_eq_of_intersection_eq_endpoint_weights hprev hnext
      exact heq.symm.trans hweightPrev

/-- The vertex immediately before the target of a neutral corridor. -/
def preterminal (C : T.NeutralCorridor source target) : T.Component :=
  C.vertex ⟨C.length, by omega⟩

lemma preterminal_adj_target (C : T.NeutralCorridor source target) :
    T.intersectionGraph.Adj C.preterminal target := by
  have hadj := C.adjacent ⟨C.length, by omega⟩
  have htarget : C.vertex ⟨C.length + 1, by omega⟩ = target := C.target_eq
  change T.intersectionGraph.Adj C.preterminal
    (C.vertex ⟨C.length + 1, by omega⟩) at hadj
  rw [htarget] at hadj
  exact hadj

/-- The incoming edge at a corridor target has intersection number equal to the bad source
weight. -/
lemma intersection_target_preterminal_eq_sourceWeight
    (C : T.NeutralCorridor source target) (hbad : T.IsBadVertex source) :
    T.intersection target C.preterminal = (T.weight source : ℤ) := by
  obtain hlen | hlen := C.length.eq_zero_or_pos
  · have hadj := C.preterminal_adj_target
    have hpre : C.preterminal = source := by
      dsimp only [preterminal]
      have hfin : (⟨C.length, by omega⟩ : Fin (C.length + 2)) = ⟨0, by omega⟩ := by
        apply Fin.ext
        simp [hlen]
      exact (congrArg C.vertex hfin).trans C.source_eq
    have hsourceEdge := T.intersection_eq_weight_of_bad hbad (hpre ▸ hadj)
    rw [T.intersection_symm]
    simpa [hpre] using hsourceEdge
  · have hlastNeutral := C.neutral ⟨C.length - 1, by omega⟩
    have hvLast : C.vertex ((⟨C.length - 1, by omega⟩ : Fin C.length).succ.castSucc) =
        C.preterminal := by
      dsimp only [preterminal]
      apply congrArg C.vertex
      apply Fin.ext
      simp
      omega
    rw [hvLast] at hlastNeutral
    have hlastEdge := T.intersection_eq_weight_of_neutral hlastNeutral
      C.preterminal_adj_target
    have hweight := C.internal_weight_eq_source hbad (C.length - 1) (by omega)
    have hvWeight : C.vertex ⟨C.length - 1 + 1, by omega⟩ = C.preterminal := by
      dsimp only [preterminal]
      apply congrArg C.vertex
      apply Fin.ext
      simp
      omega
    rw [hvWeight] at hweight
    rw [T.intersection_symm, hlastEdge, hweight]

/-- Remove the last edge of a nonempty neutral corridor. -/
noncomputable def dropLast (C : T.NeutralCorridor source target)
    (hlen : 0 < C.length) : T.NeutralCorridor source C.preterminal where
  length := C.length - 1
  vertex r := C.vertex ⟨r, by omega⟩
  vertex_injective := by
    intro a b h
    have hc : (⟨a.val, by omega⟩ : Fin (C.length + 2)) =
        ⟨b.val, by omega⟩ := C.vertex_injective h
    apply Fin.ext
    exact congrArg (fun x : Fin (C.length + 2) => x.val) hc
  source_eq := C.source_eq
  target_eq := by
    dsimp only [preterminal]
    apply congrArg C.vertex
    apply Fin.ext
    simp
    omega
  adjacent r := C.adjacent ⟨r, by omega⟩
  neutral r := C.neutral ⟨r, by omega⟩

lemma preterminal_neutral (C : T.NeutralCorridor source target)
    (hlen : 0 < C.length) : T.IsNeutralVertex C.preterminal := by
  have hlast := C.neutral ⟨C.length - 1, by omega⟩
  change T.IsNeutralVertex
    (C.vertex ((⟨C.length - 1, by omega⟩ : Fin C.length).succ.castSucc)) at hlast
  convert hlast using 1
  dsimp only [preterminal]
  apply congrArg C.vertex
  apply Fin.ext
  simp
  omega

@[simp] lemma dropLast_preterminal (C : T.NeutralCorridor source target)
    (hlen : 0 < C.length) :
    (C.dropLast hlen).preterminal = C.vertex ⟨C.length - 1, by omega⟩ := rfl

/-- Change a corridor's propositionally equal terminal without altering its vertices. -/
noncomputable def copyTarget {target' : T.Component}
    (C : T.NeutralCorridor source target) (h : target = target') :
    T.NeutralCorridor source target' where
  length := C.length
  vertex := C.vertex
  vertex_injective := C.vertex_injective
  source_eq := C.source_eq
  target_eq := C.target_eq.trans h
  adjacent := C.adjacent
  neutral := C.neutral

@[simp] lemma copyTarget_preterminal {target' : T.Component}
    (C : T.NeutralCorridor source target) (h : target = target') :
    (C.copyTarget h).preterminal = C.preterminal := rfl

lemma dropLast_preterminal_ne_target (C : T.NeutralCorridor source target)
    (hlen : 0 < C.length) : (C.dropLast hlen).preterminal ≠ target := by
  intro heq
  have htarget := C.target_eq
  have hv : C.vertex ⟨C.length - 1, by omega⟩ = target := by
    simpa only [dropLast_preterminal] using heq
  have hindices := C.vertex_injective (hv.trans htarget.symm)
  have := congrArg Fin.val hindices
  simp at this

/-- Neutral corridors entering the same terminal through the same vertex have the same
bad source.  This is the pairwise-distinctness input in the `0C7C` grouping argument. -/
lemma source_eq_of_preterminal_eq
    {source₁ source₂ target : T.Component}
    (C₁ : T.NeutralCorridor source₁ target)
    (C₂ : T.NeutralCorridor source₂ target)
    (hbad₁ : T.IsBadVertex source₁) (hbad₂ : T.IsBadVertex source₂)
    (hpre : C₁.preterminal = C₂.preterminal) : source₁ = source₂ := by
  by_cases hC₁ : C₁.length = 0
  · by_cases hC₂ : C₂.length = 0
    · have hpre₁ : C₁.preterminal = source₁ := by
        dsimp only [preterminal]
        have hfin : (⟨C₁.length, by omega⟩ : Fin (C₁.length + 2)) = ⟨0, by omega⟩ := by
          apply Fin.ext
          simp [hC₁]
        exact (congrArg C₁.vertex hfin).trans C₁.source_eq
      have hpre₂ : C₂.preterminal = source₂ := by
        dsimp only [preterminal]
        have hfin : (⟨C₂.length, by omega⟩ : Fin (C₂.length + 2)) = ⟨0, by omega⟩ := by
          apply Fin.ext
          simp [hC₂]
        exact (congrArg C₂.vertex hfin).trans C₂.source_eq
      exact hpre₁.symm.trans (hpre.trans hpre₂)
    · have hpos₂ : 0 < C₂.length := Nat.pos_of_ne_zero hC₂
      have hneutral₂ := C₂.preterminal_neutral hpos₂
      have hpre₁ : C₁.preterminal = source₁ := by
        dsimp only [preterminal]
        have hfin : (⟨C₁.length, by omega⟩ : Fin (C₁.length + 2)) = ⟨0, by omega⟩ := by
          apply Fin.ext
          simp [hC₁]
        exact (congrArg C₁.vertex hfin).trans C₁.source_eq
      exact ((hbad₁.not_neutral T) (hpre₁ ▸ hpre ▸ hneutral₂)).elim
  · have hpos₁ : 0 < C₁.length := Nat.pos_of_ne_zero hC₁
    by_cases hC₂ : C₂.length = 0
    · have hneutral₁ := C₁.preterminal_neutral hpos₁
      have hpre₂ : C₂.preterminal = source₂ := by
        dsimp only [preterminal]
        have hfin : (⟨C₂.length, by omega⟩ : Fin (C₂.length + 2)) = ⟨0, by omega⟩ := by
          apply Fin.ext
          simp [hC₂]
        exact (congrArg C₂.vertex hfin).trans C₂.source_eq
      exact ((hbad₂.not_neutral T) (hpre₂ ▸ hpre.symm ▸ hneutral₁)).elim
    · have hpos₂ : 0 < C₂.length := Nat.pos_of_ne_zero hC₂
      let P₁ := C₁.dropLast hpos₁
      let P₂ := C₂.dropLast hpos₂
      let P₂' := P₂.copyTarget hpre.symm
      have hneutral : T.IsNeutralVertex C₁.preterminal :=
        C₁.preterminal_neutral hpos₁
      have hadjTarget : T.intersectionGraph.Adj C₁.preterminal target :=
        C₁.preterminal_adj_target
      have hadjPrev₁ : T.intersectionGraph.Adj C₁.preterminal P₁.preterminal :=
        P₁.preterminal_adj_target.symm
      have hadjPrev₂ : T.intersectionGraph.Adj C₁.preterminal P₂'.preterminal := by
        simpa only [P₂', copyTarget_preterminal, hpre] using
          P₂.preterminal_adj_target.symm
      have hnePrev₁ : P₁.preterminal ≠ target :=
        C₁.dropLast_preterminal_ne_target hpos₁
      have hnePrev₂ : P₂'.preterminal ≠ target := by
        simpa only [P₂', copyTarget_preterminal] using
          C₂.dropLast_preterminal_ne_target hpos₂
      have hprev : P₁.preterminal = P₂'.preterminal :=
        (hneutral.existsUnique_otherNeighbor T hadjTarget).unique
          ⟨hadjPrev₁, hnePrev₁⟩ ⟨hadjPrev₂, hnePrev₂⟩
      exact source_eq_of_preterminal_eq P₁ P₂' hbad₁ hbad₂ hprev
termination_by C₁.length
decreasing_by
  dsimp only [P₁, dropLast]
  omega

end NeutralCorridor

/-- A bad leaf is not the only non-neutral vertex: the handshaking lemma supplies a
distinct odd-degree vertex, while every neutral vertex has degree two. -/
lemma exists_ne_not_neutral_of_bad (T : NumericalType) {source : T.Component}
    (hbad : T.IsBadVertex source) :
    ∃ target : T.Component, target ≠ source ∧ ¬ T.IsNeutralVertex target := by
  have hdegree : T.intersectionGraph.degree source = 1 := by
    rw [← T.intersectionGraph.card_neighborSet_eq_degree]
    rw [← Nat.card_eq_fintype_card]
    exact hbad.2.1
  obtain ⟨target, hne, hodd⟩ :=
    T.intersectionGraph.exists_ne_odd_degree_of_exists_odd_degree source (by
      rw [hdegree]
      exact odd_one)
  refine ⟨target, hne, ?_⟩
  intro hneutral
  have hdegreeTarget : T.intersectionGraph.degree target = 2 := by
    rw [← T.intersectionGraph.card_neighborSet_eq_degree]
    rw [← Nat.card_eq_fintype_card]
    exact hneutral.2.1
  rw [hdegreeTarget] at hodd
  norm_num [Odd] at hodd

/-- The finite set of non-neutral vertices distinct from a selected source. -/
def nonneutralOtherVertices (T : NumericalType) (source : T.Component) :
    Finset T.Component :=
  by
    classical
    exact Finset.univ.filter fun target => target ≠ source ∧ ¬ T.IsNeutralVertex target

lemma nonneutralOtherVertices_nonempty (T : NumericalType) {source : T.Component}
    (hbad : T.IsBadVertex source) :
    (T.nonneutralOtherVertices source).Nonempty := by
  obtain ⟨target, hne, hneutral⟩ := T.exists_ne_not_neutral_of_bad hbad
  exact ⟨target, by simp [nonneutralOtherVertices, hne, hneutral]⟩

/-- A closest non-neutral vertex to a bad source. -/
noncomputable def nearestNonneutral (T : NumericalType) (source : T.Component)
    (hbad : T.IsBadVertex source) : T.Component :=
  Classical.choose (Finset.exists_min_image
    (T.nonneutralOtherVertices source)
    (fun target => T.intersectionGraph.dist source target)
    (T.nonneutralOtherVertices_nonempty hbad))

lemma nearestNonneutral_mem (T : NumericalType) {source : T.Component}
    (hbad : T.IsBadVertex source) :
    T.nearestNonneutral source hbad ∈ T.nonneutralOtherVertices source :=
  (Classical.choose_spec (Finset.exists_min_image
    (T.nonneutralOtherVertices source)
    (fun target => T.intersectionGraph.dist source target)
    (T.nonneutralOtherVertices_nonempty hbad))).1

lemma nearestNonneutral_dist_le (T : NumericalType) {source target : T.Component}
    (hbad : T.IsBadVertex source) (htarget : target ≠ source)
    (hnonneutral : ¬ T.IsNeutralVertex target) :
    T.intersectionGraph.dist source (T.nearestNonneutral source hbad) ≤
      T.intersectionGraph.dist source target := by
  exact (Classical.choose_spec (Finset.exists_min_image
    (T.nonneutralOtherVertices source)
    (fun target => T.intersectionGraph.dist source target)
    (T.nonneutralOtherVertices_nonempty hbad))).2 target (by
      simp [nonneutralOtherVertices, htarget, hnonneutral])

lemma nearestNonneutral_ne (T : NumericalType) {source : T.Component}
    (hbad : T.IsBadVertex source) :
    T.nearestNonneutral source hbad ≠ source := by
  have hmem := T.nearestNonneutral_mem hbad
  have hmem' : T.nearestNonneutral source hbad ≠ source ∧
      ¬ T.IsNeutralVertex (T.nearestNonneutral source hbad) := by
    simpa [nonneutralOtherVertices] using hmem
  exact hmem'.1

lemma nearestNonneutral_not_neutral (T : NumericalType) {source : T.Component}
    (hbad : T.IsBadVertex source) :
    ¬ T.IsNeutralVertex (T.nearestNonneutral source hbad) := by
  have hmem := T.nearestNonneutral_mem hbad
  have hmem' : T.nearestNonneutral source hbad ≠ source ∧
      ¬ T.IsNeutralVertex (T.nearestNonneutral source hbad) := by
    simpa [nonneutralOtherVertices] using hmem
  exact hmem'.2

/-- A shortest graph walk from a bad source to its closest distinct non-neutral vertex. -/
noncomputable def corridorWalk (T : NumericalType) (source : T.Component)
    (hbad : T.IsBadVertex source) :
    T.intersectionGraph.Walk source (T.nearestNonneutral source hbad) :=
  Classical.choose (T.intersectionGraph_connected.exists_path_of_dist
    source (T.nearestNonneutral source hbad))

lemma corridorWalk_isPath (T : NumericalType) {source : T.Component}
    (hbad : T.IsBadVertex source) :
    (T.corridorWalk source hbad).IsPath :=
  (Classical.choose_spec (T.intersectionGraph_connected.exists_path_of_dist
    source (T.nearestNonneutral source hbad))).1

lemma corridorWalk_length_eq_dist (T : NumericalType) {source : T.Component}
    (hbad : T.IsBadVertex source) :
    (T.corridorWalk source hbad).length =
      T.intersectionGraph.dist source (T.nearestNonneutral source hbad) :=
  (Classical.choose_spec (T.intersectionGraph_connected.exists_path_of_dist
    source (T.nearestNonneutral source hbad))).2

lemma corridorWalk_length_pos (T : NumericalType) {source : T.Component}
    (hbad : T.IsBadVertex source) :
    0 < (T.corridorWalk source hbad).length := by
  by_contra h
  have hzero : (T.corridorWalk source hbad).length = 0 := by omega
  exact T.nearestNonneutral_ne hbad
    ((T.corridorWalk source hbad).eq_of_length_eq_zero hzero).symm

lemma corridorWalk_internal_neutral (T : NumericalType) {source : T.Component}
    (hbad : T.IsBadVertex source) :
    ∀ r, 0 < r → r < (T.corridorWalk source hbad).length →
      T.IsNeutralVertex ((T.corridorWalk source hbad).getVert r) := by
  intro r hr0 hrlen
  by_contra hneutral
  let p := T.corridorWalk source hbad
  change r < p.length at hrlen
  change ¬ T.IsNeutralVertex (p.getVert r) at hneutral
  have hp : p.IsPath := T.corridorWalk_isPath hbad
  have hpLength : p.length =
      T.intersectionGraph.dist source (T.nearestNonneutral source hbad) :=
    T.corridorWalk_length_eq_dist hbad
  have hneSource : p.getVert r ≠ source := by
    intro heq
    have hzeroVert : p.getVert 0 = source := p.getVert_zero
    have hre : r = 0 := hp.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega)
      (heq.trans hzeroVert.symm)
    omega
  have hprefix := SimpleGraph.length_eq_dist_of_subwalk hpLength (p.isSubwalk_take r)
  have htakeLength : (p.take r).length = r := by
    rw [p.take_length]
    omega
  have hdist : T.intersectionGraph.dist source (p.getVert r) = r := by
    rw [htakeLength] at hprefix
    exact hprefix.symm
  have hmin := T.nearestNonneutral_dist_le hbad hneSource hneutral
  rw [← hpLength, hdist] at hmin
  omega

/-- Every bad source canonically determines a finite neutral corridor ending at a
distinct non-neutral vertex. -/
noncomputable def corridorOfBad (T : NumericalType) (source : T.Component)
    (hbad : T.IsBadVertex source) :
    T.NeutralCorridor source (T.nearestNonneutral source hbad) :=
  NeutralCorridor.ofWalk (T.corridorWalk source hbad)
    (T.corridorWalk_isPath hbad) (T.corridorWalk_length_pos hbad)
    (T.corridorWalk_internal_neutral hbad)

/-- Bad components, bundled with the proof that their local discrepancy is negative. -/
abbrev BadComponent (T : NumericalType) := {i : T.Component // T.IsBadVertex i}

namespace BadComponent

variable {T : NumericalType}

/-- The first non-neutral terminal reached from a bad component. -/
def terminal (source : T.BadComponent) : T.Component :=
  T.nearestNonneutral source.1 source.2

/-- The canonical neutral corridor from a bad component to its terminal. -/
def corridor (source : T.BadComponent) : T.NeutralCorridor source.1 source.terminal :=
  T.corridorOfBad source.1 source.2

/-- The vertex through which the bad component's corridor enters its terminal. -/
def preterminal (source : T.BadComponent) : T.Component := source.corridor.preterminal

lemma preterminal_adj_terminal (source : T.BadComponent) :
    T.intersectionGraph.Adj source.preterminal source.terminal :=
  source.corridor.preterminal_adj_target

lemma terminal_not_neutral (source : T.BadComponent) :
    ¬ T.IsNeutralVertex source.terminal := T.nearestNonneutral_not_neutral source.2

end BadComponent

/-- The bad components whose canonical corridors end at `target`. -/
def badSourcesAt (T : NumericalType) (target : T.Component) :
    Finset T.BadComponent := by
  classical
  exact Finset.univ.filter fun source => source.terminal = target

lemma mem_badSourcesAt_iff {T : NumericalType} {target : T.Component}
    {source : T.BadComponent} :
    source ∈ T.badSourcesAt target ↔ source.terminal = target := by
  classical
  simp [badSourcesAt]

/-- The distinct neighbors through which bad corridors enter a fixed terminal. -/
def incomingPreterminals (T : NumericalType) (target : T.Component) :
    Finset T.Component :=
  (T.badSourcesAt target).image fun source => source.preterminal

lemma preterminal_injectiveOn_badSourcesAt (T : NumericalType) (target : T.Component) :
    Set.InjOn (fun source : T.BadComponent => source.preterminal)
      (T.badSourcesAt target) := by
  intro source hsource source' hsource' heq
  have hterminal := mem_badSourcesAt_iff.mp hsource
  have hterminal' := mem_badSourcesAt_iff.mp hsource'
  let C := source.corridor.copyTarget hterminal
  let C' := source'.corridor.copyTarget hterminal'
  apply Subtype.ext
  apply NeutralCorridor.source_eq_of_preterminal_eq C C' source.2 source'.2
  simpa only [C, C', NeutralCorridor.copyTarget_preterminal,
    BadComponent.preterminal] using heq

lemma card_incomingPreterminals (T : NumericalType) (target : T.Component) :
    (T.incomingPreterminals target).card = (T.badSourcesAt target).card := by
  classical
  exact Finset.card_image_iff.mpr (T.preterminal_injectiveOn_badSourcesAt target)

lemma incomingPreterminals_subset_neighborFinset (T : NumericalType)
    (target : T.Component) :
    T.incomingPreterminals target ⊆ T.intersectionGraph.neighborFinset target := by
  intro pre hpre
  rw [incomingPreterminals, Finset.mem_image] at hpre
  obtain ⟨source, hsource, rfl⟩ := hpre
  rw [T.intersectionGraph.mem_neighborFinset]
  have hterminal := mem_badSourcesAt_iff.mp hsource
  rw [← hterminal]
  exact source.preterminal_adj_terminal.symm

/-- The terminal's neighbors not used by incoming bad corridors. -/
def externalNeighbors (T : NumericalType) (target : T.Component) :
    Finset T.Component :=
  T.intersectionGraph.neighborFinset target \ T.incomingPreterminals target

lemma neighborFinset_eq_union (T : NumericalType) (target : T.Component) :
    T.intersectionGraph.neighborFinset target =
      T.incomingPreterminals target ∪ T.externalNeighbors target := by
  rw [externalNeighbors]
  exact (Finset.union_sdiff_of_subset
    (T.incomingPreterminals_subset_neighborFinset target)).symm

lemma disjoint_incoming_external (T : NumericalType) (target : T.Component) :
    Disjoint (T.incomingPreterminals target) (T.externalNeighbors target) :=
  Finset.disjoint_sdiff

lemma card_neighborFinset_grouped (T : NumericalType) (target : T.Component) :
    (T.intersectionGraph.neighborFinset target).card =
      (T.badSourcesAt target).card + (T.externalNeighbors target).card := by
  rw [T.neighborFinset_eq_union target,
    Finset.card_union_of_disjoint (T.disjoint_incoming_external target),
    T.card_incomingPreterminals target]

lemma normalizedOffDiagonalSum_eq_grouped (T : NumericalType) (target : T.Component) :
    T.normalizedOffDiagonalSum target =
      (∑ source ∈ T.badSourcesAt target,
        T.normalizedIntersection target source.preterminal) +
      ∑ other ∈ T.externalNeighbors target,
        T.normalizedIntersection target other := by
  classical
  rw [T.normalizedOffDiagonalSum_eq_neighborSum]
  rw [← Finset.sum_subtype (T.intersectionGraph.neighborFinset target)
    (by simp [T.intersectionGraph.mem_neighborFinset])
    (fun j => T.normalizedIntersection target j)]
  rw [T.neighborFinset_eq_union target,
    Finset.sum_union (T.disjoint_incoming_external target)]
  congr 1
  rw [incomingPreterminals]
  rw [Finset.sum_image]
  exact T.preterminal_injectiveOn_badSourcesAt target

/-- The portion of a terminal's normalized edge contribution remaining after paying the
mass of one bad source. -/
def groupDelta (T : NumericalType) (target : T.Component)
    (source : T.BadComponent) : ℤ :=
  T.vertexMass target * T.normalizedIntersection target source.preterminal -
    T.vertexMass source.1

lemma twiceGenusDiscrepancy_of_bad {T : NumericalType}
    (source : T.BadComponent) :
    T.twiceGenusDiscrepancy source.1 = 1 - T.vertexMass source.1 := by
  rw [T.twiceGenusDiscrepancy_eq]
  rcases source.2 with ⟨hg, hd, _hmass, hs⟩
  simp only [hg, Nat.cast_zero, hs, twiceTopologicalContribution, hd, Nat.cast_one]
  ring

lemma groupCorridor_intersection (T : NumericalType) {target : T.Component}
    {source : T.BadComponent} (hsource : source ∈ T.badSourcesAt target) :
    T.intersection target source.preterminal = (T.weight source.1 : ℤ) := by
  have hterminal := mem_badSourcesAt_iff.mp hsource
  let C := source.corridor.copyTarget hterminal
  simpa only [C, NeutralCorridor.copyTarget_preterminal,
    BadComponent.preterminal] using
      C.intersection_target_preterminal_eq_sourceWeight source.2

lemma groupCorridor_multiplicity (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component)
    {target : T.Component} {source : T.BadComponent}
    (hsource : source ∈ T.badSourcesAt target) :
    2 * (T.multiplicity source.1 : ℤ) ≤ (T.multiplicity target : ℤ) := by
  have hterminal := mem_badSourcesAt_iff.mp hsource
  let C := source.corridor.copyTarget hterminal
  exact C.two_mul_sourceMultiplicity_le_targetMultiplicity hmin hcard source.2

lemma two_mul_groupDelta_ge_targetMass (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component)
    {target : T.Component} {source : T.BadComponent}
    (hsource : source ∈ T.badSourcesAt target) :
    T.vertexMass target ≤ 2 * T.groupDelta target source := by
  let mt : ℤ := T.multiplicity target
  let ms : ℤ := T.multiplicity source.1
  let wt : ℤ := T.weight target
  let ws : ℤ := T.weight source.1
  let q : ℤ := T.normalizedIntersection target source.preterminal
  have hadj : T.intersectionGraph.Adj target source.preterminal := by
    have hmem := T.incomingPreterminals_subset_neighborFinset target
      (by rw [incomingPreterminals, Finset.mem_image]
          exact ⟨source, hsource, rfl⟩)
    simpa only [SimpleGraph.mem_neighborFinset] using hmem
  have hq : 0 < q := T.normalizedIntersection_pos_of_adj hadj
  have hnorm : q * wt = ws := by
    change T.normalizedIntersection target source.preterminal * (T.weight target : ℤ) = _
    rw [T.normalizedIntersection_mul_weight]
    exact T.groupCorridor_intersection hsource
  have hmult : 2 * ms ≤ mt := T.groupCorridor_multiplicity hmin hcard hsource
  have hwt : 0 < wt := by dsimp only [wt]; positivity
  have hws : 0 < ws := by dsimp only [ws]; positivity
  have hwtws : wt ≤ ws := by nlinarith
  have hdiff : mt ≤ 2 * (mt - ms) := by omega
  have hdelta : T.groupDelta target source = (mt - ms) * ws := by
    dsimp only [groupDelta, vertexMass, mt, ms, wt, ws, q]
    nlinarith
  rw [hdelta]
  calc
    T.vertexMass target = mt * wt := by rfl
    _ ≤ (2 * (mt - ms)) * wt :=
      mul_le_mul_of_nonneg_right hdiff (le_of_lt hwt)
    _ ≤ (2 * (mt - ms)) * ws :=
      mul_le_mul_of_nonneg_left hwtws (by omega)
    _ = 2 * ((mt - ms) * ws) := by ring

lemma targetMass_le_groupDelta_of_weight_lt (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component)
    {target : T.Component} {source : T.BadComponent}
    (hsource : source ∈ T.badSourcesAt target)
    (hweight : T.weight target < T.weight source.1) :
    T.vertexMass target ≤ T.groupDelta target source := by
  let mt : ℤ := T.multiplicity target
  let ms : ℤ := T.multiplicity source.1
  let wt : ℤ := T.weight target
  let ws : ℤ := T.weight source.1
  let q : ℤ := T.normalizedIntersection target source.preterminal
  have hnorm : q * wt = ws := by
    change T.normalizedIntersection target source.preterminal * (T.weight target : ℤ) = _
    rw [T.normalizedIntersection_mul_weight]
    exact T.groupCorridor_intersection hsource
  have hmult : 2 * ms ≤ mt := T.groupCorridor_multiplicity hmin hcard hsource
  have hwt : 0 < wt := by dsimp only [wt]; positivity
  have hweightZ : wt < ws := by
    change (T.weight target : ℤ) < (T.weight source.1 : ℤ)
    exact_mod_cast hweight
  have hq : 2 ≤ q := by nlinarith
  have htwoweight : 2 * wt ≤ ws := by nlinarith
  have hdiff : mt ≤ 2 * (mt - ms) := by omega
  have hnonnegDiff : 0 ≤ mt - ms := by omega
  have hdelta : T.groupDelta target source = (mt - ms) * ws := by
    dsimp only [groupDelta, vertexMass, mt, ms, wt, ws, q]
    nlinarith
  rw [hdelta]
  calc
    T.vertexMass target = mt * wt := by rfl
    _ ≤ (2 * (mt - ms)) * wt :=
      mul_le_mul_of_nonneg_right hdiff (le_of_lt hwt)
    _ = (mt - ms) * (2 * wt) := by ring
    _ ≤ (mt - ms) * ws :=
      mul_le_mul_of_nonneg_left htwoweight hnonnegDiff

lemma targetMass_le_externalContribution (T : NumericalType)
    {target other : T.Component} (hother : other ∈ T.externalNeighbors target) :
    T.vertexMass target ≤
      T.vertexMass target * T.normalizedIntersection target other := by
  have hmem : other ∈ T.intersectionGraph.neighborFinset target :=
    (Finset.mem_sdiff.mp hother).1
  have hadj : T.intersectionGraph.Adj target other := by
    simpa only [SimpleGraph.mem_neighborFinset] using hmem
  have hq := T.normalizedIntersection_pos_of_adj hadj
  have hmass := T.vertexMass_pos target
  nlinarith

/-- Exact discrepancy formula for a terminal together with all bad corridors entering it. -/
lemma grouped_discrepancy_eq (T : NumericalType) (target : T.Component) :
    T.twiceGenusDiscrepancy target +
        ∑ source ∈ T.badSourcesAt target,
          T.twiceGenusDiscrepancy source.1 =
      T.vertexMass target * (2 * (T.genus target : ℤ) - 2) +
        ∑ source ∈ T.badSourcesAt target, T.groupDelta target source +
        ∑ other ∈ T.externalNeighbors target,
          T.vertexMass target * T.normalizedIntersection target other -
        (T.externalNeighbors target).card + 2 := by
  rw [T.twiceGenusDiscrepancy_eq]
  simp_rw [twiceGenusDiscrepancy_of_bad]
  rw [T.normalizedOffDiagonalSum_eq_grouped target]
  simp only [twiceTopologicalContribution]
  have hcard := T.card_neighborFinset_grouped target
  have hdegree : Nat.card (T.intersectionGraph.neighborSet target) =
      (T.badSourcesAt target).card + (T.externalNeighbors target).card := by
    rw [Nat.card_eq_fintype_card, T.intersectionGraph.card_neighborSet_eq_degree,
      ← T.intersectionGraph.card_neighborFinset_eq_degree]
    exact hcard
  rw [hdegree]
  push_cast
  ring_nf
  simp_rw [Finset.mul_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, groupDelta]
  ring

lemma targetWeight_le_sourceWeight (T : NumericalType)
    {target : T.Component} {source : T.BadComponent}
    (hsource : source ∈ T.badSourcesAt target) :
    T.weight target ≤ T.weight source.1 := by
  have hadj : T.intersectionGraph.Adj target source.preterminal := by
    have hmem := T.incomingPreterminals_subset_neighborFinset target
      (by rw [incomingPreterminals, Finset.mem_image]
          exact ⟨source, hsource, rfl⟩)
    simpa only [SimpleGraph.mem_neighborFinset] using hmem
  have hq := T.normalizedIntersection_pos_of_adj hadj
  have hnorm := T.normalizedIntersection_mul_weight target source.preterminal
  have hinter := T.groupCorridor_intersection hsource
  exact_mod_cast (show (T.weight target : ℤ) ≤ (T.weight source.1 : ℤ) by
    rw [← hinter, ← hnorm]
    have hwt : 0 < (T.weight target : ℤ) := by positivity
    nlinarith)

lemma externalNormalized_pos (T : NumericalType) {target other : T.Component}
    (hother : other ∈ T.externalNeighbors target) :
    0 < T.normalizedIntersection target other := by
  have hmem : other ∈ T.intersectionGraph.neighborFinset target :=
    (Finset.mem_sdiff.mp hother).1
  apply T.normalizedIntersection_pos_of_adj
  simpa only [SimpleGraph.mem_neighborFinset] using hmem

/-- The local surplus at a non-isolated terminal absorbs the deficits of all bad
corridors entering it.  This is the numerical borrowing estimate in tag `0C7C`. -/
lemma grouped_discrepancy_nonnegative (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component)
    (target : T.Component) (hbad : (T.badSourcesAt target).Nonempty)
    (hext : (T.externalNeighbors target).Nonempty) :
    0 ≤ T.twiceGenusDiscrepancy target +
      ∑ source ∈ T.badSourcesAt target,
        T.twiceGenusDiscrepancy source.1 := by
  let B := T.badSourcesAt target
  let E := T.externalNeighbors target
  let M : ℤ := T.vertexMass target
  let SD : ℤ := ∑ source ∈ B, T.groupDelta target source
  let SE : ℤ := ∑ other ∈ E,
    T.vertexMass target * T.normalizedIntersection target other
  let b : ℤ := B.card
  let e : ℤ := E.card
  have hM : 0 < M := T.vertexMass_pos target
  have hb : 0 < b := by
    dsimp only [b]
    exact_mod_cast (Finset.card_pos.mpr hbad)
  have he : 0 < e := by
    dsimp only [e]
    exact_mod_cast (Finset.card_pos.mpr hext)
  have hSD2 : M * b ≤ 2 * SD := by
    calc
      M * b = ∑ source ∈ B, M := by simp [b]; ring
      _ ≤ ∑ source ∈ B, 2 * T.groupDelta target source := by
        apply Finset.sum_le_sum
        intro source hsource
        exact T.two_mul_groupDelta_ge_targetMass hmin hcard hsource
      _ = 2 * SD := by simp [SD, Finset.mul_sum]
  have hSE : M * e ≤ SE := by
    calc
      M * e = ∑ other ∈ E, M := by simp [e]; ring
      _ ≤ ∑ other ∈ E,
          T.vertexMass target * T.normalizedIntersection target other := by
        apply Finset.sum_le_sum
        intro other hother
        exact T.targetMass_le_externalContribution hother
      _ = SE := rfl
  have hformula := T.grouped_discrepancy_eq target
  change T.twiceGenusDiscrepancy target +
      ∑ source ∈ B, T.twiceGenusDiscrepancy source.1 =
    M * (2 * (T.genus target : ℤ) - 2) + SD + SE - e + 2 at hformula
  rw [hformula]
  by_cases hg : T.genus target = 0
  · simp only [hg, Nat.cast_zero]
    by_cases hbTwo : 2 ≤ b
    · have hMleSD : M ≤ SD := by nlinarith
      have hSEstrong : M + e - 1 ≤ SE := by
        have hprod : 0 ≤ (M - 1) * (e - 1) := mul_nonneg (by omega) (by omega)
        nlinarith
      omega
    · have hbOne : b = 1 := by omega
      by_cases heTwo : 2 ≤ e
      · have haux : 3 * M + 2 * e - 4 ≤ 2 * M * e := by
          have hprod : 0 ≤ (2 * e - 3) * (M - 1) :=
            mul_nonneg (by omega) (by omega)
          nlinarith
        nlinarith
      · have heOne : e = 1 := by omega
        have hBcard : B.card = 1 := by
          change (B.card : ℤ) = 1 at hbOne
          exact_mod_cast hbOne
        have hEcard : E.card = 1 := by
          change (E.card : ℤ) = 1 at heOne
          exact_mod_cast heOne
        obtain ⟨source, hB⟩ := Finset.card_eq_one.mp hBcard
        obtain ⟨other, hE⟩ := Finset.card_eq_one.mp hEcard
        have hsource : source ∈ B := by simp [hB]
        have hother : other ∈ E := by simp [hE]
        have hweightLe := T.targetWeight_le_sourceWeight hsource
        by_cases hweight : T.weight target < T.weight source.1
        · have hDeltaStrong := T.targetMass_le_groupDelta_of_weight_lt
            hmin hcard hsource hweight
          have hSD : SD = T.groupDelta target source := by simp [SD, hB]
          have hSEone : M ≤ SE := by
            rw [heOne] at hSE
            simpa using hSE
          rw [hSD]
          omega
        · have hweightEq : T.weight target = T.weight source.1 :=
            le_antisymm hweightLe (le_of_not_gt hweight)
          let q := T.normalizedIntersection target other
          have hqpos : 0 < q := T.externalNormalized_pos hother
          by_cases hqTwo : 2 ≤ q
          · have hSEtwo : 2 * M ≤ SE := by
              have hterm : 2 * M ≤
                  T.vertexMass target * T.normalizedIntersection target other := by
                change 2 * M ≤ M * q
                nlinarith
              have hSEeq : SE =
                  T.vertexMass target * T.normalizedIntersection target other := by
                simp [SE, hE]
              rw [hSEeq]
              exact hterm
            nlinarith
          · have hqOne : q = 1 := by omega
            have hterminal : source.terminal = target := mem_badSourcesAt_iff.mp hsource
            have hnotNeutral : ¬ T.IsNeutralVertex target := by
              rw [← hterminal]
              exact source.terminal_not_neutral
            apply (hnotNeutral ?_).elim
            refine ⟨hg, ?_, ?_⟩
            · have hdegree := T.card_neighborFinset_grouped target
              rw [hBcard, hEcard] at hdegree
              rw [Nat.card_eq_fintype_card,
                T.intersectionGraph.card_neighborSet_eq_degree,
                ← T.intersectionGraph.card_neighborFinset_eq_degree]
              omega
            · rw [T.normalizedOffDiagonalSum_eq_grouped target]
              have hsourceNorm :
                  T.normalizedIntersection target source.preterminal = 1 := by
                have hnorm := T.normalizedIntersection_mul_weight
                  target source.preterminal
                have hinter := T.groupCorridor_intersection hsource
                rw [hinter, ← hweightEq] at hnorm
                have hwt : 0 < (T.weight target : ℤ) := by positivity
                nlinarith
              have hsumB :
                  (∑ source' ∈ B,
                    T.normalizedIntersection target source'.preterminal) = 1 := by
                rw [hB]
                simp [hsourceNorm]
              have hsumE :
                  (∑ other' ∈ E,
                    T.normalizedIntersection target other') = 1 := by
                rw [hE]
                simp only [Finset.sum_singleton, q, hqOne]
              change (∑ source' ∈ B,
                  T.normalizedIntersection target source'.preterminal) +
                (∑ other' ∈ E,
                  T.normalizedIntersection target other') = 2
              rw [hsumB, hsumE]
              norm_num
  · have hgOne : 1 ≤ (T.genus target : ℤ) := by
      exact_mod_cast (show 1 ≤ T.genus target by omega)
    have hSEstrong : e ≤ SE := by
      have hprod : 0 ≤ (M - 1) * e := mul_nonneg (by omega) (by omega)
      nlinarith
    have hSDnonneg : 0 ≤ SD := by nlinarith
    nlinarith

/-- The union of all bad corridors entering `target`, including the terminal itself. -/
def InTerminalCluster (T : NumericalType) (target v : T.Component) : Prop :=
  v = target ∨ ∃ source ∈ T.badSourcesAt target,
    ∃ r : Fin (source.corridor.length + 1), source.corridor.vertex r.castSucc = v

lemma terminalCluster_target (T : NumericalType) (target : T.Component) :
    T.InTerminalCluster target target := Or.inl rfl

/-- If there is no external edge at a terminal, its corridor cluster is closed under
graph adjacency. -/
lemma terminalCluster_closed (T : NumericalType) (target : T.Component)
    (hext : T.externalNeighbors target = ∅) {x y : T.Component}
    (hx : T.InTerminalCluster target x)
    (hxy : T.intersectionGraph.Adj x y) :
    T.InTerminalCluster target y := by
  rcases hx with hxt | ⟨source, hsource, r, hr⟩
  · subst x
    have hneighbor : y ∈ T.intersectionGraph.neighborFinset target := by
      simpa only [SimpleGraph.mem_neighborFinset] using hxy
    have hneighbors := T.neighborFinset_eq_union target
    rw [hext, Finset.union_empty] at hneighbors
    rw [hneighbors, incomingPreterminals, Finset.mem_image] at hneighbor
    obtain ⟨source, hsource, hy⟩ := hneighbor
    right
    refine ⟨source, hsource, ⟨source.corridor.length, by omega⟩, ?_⟩
    change source.preterminal = y
    exact hy
  · have hterminal := mem_badSourcesAt_iff.mp hsource
    let C := source.corridor.copyTarget hterminal
    have hClength : C.length = source.corridor.length := rfl
    change C.vertex r.castSucc = x at hr
    by_cases hrzero : r.val = 0
    · have hxsource : x = source.1 := by
        rw [← hr]
        have hfin : r.castSucc = (⟨0, by omega⟩ : Fin (C.length + 2)) := by
          apply Fin.ext
          exact hrzero
        rw [hfin, C.source_eq]
      have hsourceY : T.intersectionGraph.Adj source.1 y := hxsource ▸ hxy
      have hfirst := C.adjacent ⟨0, by omega⟩
      have hfirst' : T.intersectionGraph.Adj source.1
          (C.vertex ⟨1, by omega⟩) := by
        have hleft : C.vertex (⟨0, by omega⟩ : Fin (C.length + 1)).castSucc =
            source.1 := C.source_eq
        have hright : C.vertex (⟨0, by omega⟩ : Fin (C.length + 1)).succ =
            C.vertex ⟨1, by omega⟩ := by
          apply congrArg C.vertex
          apply Fin.ext
          rfl
        rw [hleft, hright] at hfirst
        exact hfirst
      have hy : y = C.vertex ⟨1, by omega⟩ :=
        (T.eq_badNeighbor_of_adj source.2 hsourceY).trans
          (T.eq_badNeighbor_of_adj source.2 hfirst').symm
      by_cases hlen : C.length = 0
      · left
        rw [hy]
        have htarget := C.target_eq
        simpa only [hlen, Nat.zero_add] using htarget
      · right
        refine ⟨source, hsource, ⟨1, by omega⟩, ?_⟩
        exact hy.symm
    · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hrzero
      have hrle : r.val ≤ C.length := by omega
      let rp : Fin C.length := ⟨r.val - 1, by omega⟩
      have hneutral := C.neutral rp
      have hcurrent : C.vertex rp.succ.castSucc = x := by
        rw [← hr]
        apply congrArg C.vertex
        apply Fin.ext
        dsimp only [rp]
        simp
        omega
      rw [hcurrent] at hneutral
      let prev : T.Component := C.vertex ⟨r.val - 1, by omega⟩
      let next : T.Component := C.vertex ⟨r.val + 1, by omega⟩
      have hprev : T.intersectionGraph.Adj x prev := by
        have hadj := C.adjacent ⟨r.val - 1, by omega⟩
        have hleft : C.vertex
            (⟨r.val - 1, by omega⟩ : Fin (C.length + 1)).castSucc = prev := rfl
        have hright : C.vertex
            (⟨r.val - 1, by omega⟩ : Fin (C.length + 1)).succ = x := by
          simpa only [hcurrent]
        rw [hleft, hright] at hadj
        exact hadj.symm
      have hnext : T.intersectionGraph.Adj x next := by
        have hadj := C.adjacent ⟨r.val, by omega⟩
        have hleft : C.vertex
            (⟨r.val, by omega⟩ : Fin (C.length + 1)).castSucc = x := by
          rw [← hr]
          apply congrArg C.vertex
          apply Fin.ext
          rfl
        have hright : C.vertex
            (⟨r.val, by omega⟩ : Fin (C.length + 1)).succ = next := rfl
        rw [hleft, hright] at hadj
        exact hadj
      by_cases hyPrev : y = prev
      · right
        refine ⟨source, hsource, ⟨r.val - 1, by omega⟩, ?_⟩
        exact hyPrev.symm
      · have hyNext : y = next :=
          (hneutral.existsUnique_otherNeighbor T hprev).unique
            ⟨hxy, hyPrev⟩ ⟨hnext, ?_⟩
        · by_cases hrlast : r.val = C.length
          · left
            rw [hyNext]
            have htarget := C.target_eq
            simpa only [next, hrlast] using htarget
          · right
            refine ⟨source, hsource, ⟨r.val + 1, by omega⟩, ?_⟩
            exact hyNext.symm
        · intro h
          have hindices := C.vertex_injective h
          have := congrArg Fin.val hindices
          dsimp only [prev, next] at this
          omega

lemma every_vertex_in_terminalCluster (T : NumericalType) (target : T.Component)
    (hext : T.externalNeighbors target = ∅) (v : T.Component) :
    T.InTerminalCluster target v := by
  induction T.connected target v with
  | refl => exact T.terminalCluster_target target
  | @tail y z _ hyz ih =>
      exact T.terminalCluster_closed target hext ih hyz

lemma bad_or_neutral_of_ne_target (T : NumericalType) (target : T.Component)
    (hext : T.externalNeighbors target = ∅) {v : T.Component} (hv : v ≠ target) :
    T.IsBadVertex v ∨ T.IsNeutralVertex v := by
  obtain htarget | ⟨source, hsource, r, hr⟩ :=
    T.every_vertex_in_terminalCluster target hext v
  · exact (hv htarget).elim
  · by_cases hrzero : r.val = 0
    · left
      have hfin : r.castSucc = (⟨0, by omega⟩ :
          Fin (source.corridor.length + 2)) := by
        apply Fin.ext
        exact hrzero
      rw [hfin, source.corridor.source_eq] at hr
      simpa [← hr] using source.2
    · right
      let rp : Fin source.corridor.length := ⟨r.val - 1, by
        have hrnotlast : r.val ≠ source.corridor.length + 1 := by
          intro hlast
          have htarget := source.corridor.target_eq
          have hterminal := mem_badSourcesAt_iff.mp hsource
          have hr' : source.corridor.vertex r.castSucc = target := by
            rw [show r.castSucc =
                (⟨source.corridor.length + 1, by omega⟩ :
                  Fin (source.corridor.length + 2)) by
              apply Fin.ext
              exact hlast]
            rw [htarget]
            exact hterminal
          exact hv (hr.symm.trans hr')
        omega⟩
      have hneutral := source.corridor.neutral rp
      convert hneutral using 1
      rw [← hr]
      apply congrArg source.corridor.vertex
      apply Fin.ext
      dsimp only [rp]
      simp
      omega

lemma badComponent_mem_badSourcesAt_of_ne_target (T : NumericalType)
    (target : T.Component) (hext : T.externalNeighbors target = ∅)
    {v : T.Component} (hbad : T.IsBadVertex v) (hv : v ≠ target) :
    (⟨v, hbad⟩ : T.BadComponent) ∈ T.badSourcesAt target := by
  obtain htarget | ⟨source, hsource, r, hr⟩ :=
    T.every_vertex_in_terminalCluster target hext v
  · exact (hv htarget).elim
  · by_cases hrzero : r.val = 0
    · have hfin : r.castSucc =
          (⟨0, by omega⟩ : Fin (source.corridor.length + 2)) := by
        apply Fin.ext
        exact hrzero
      have hvsource : v = source.1 := by
        rw [hfin, source.corridor.source_eq] at hr
        exact hr.symm
      have heq : (⟨v, hbad⟩ : T.BadComponent) = source := by
        apply Subtype.ext
        exact hvsource
      rw [heq]
      exact hsource
    · have hneutral : T.IsNeutralVertex v := by
        let rp : Fin source.corridor.length := ⟨r.val - 1, by
          have hrnotlast : r.val ≠ source.corridor.length + 1 := by
            intro hlast
            have hterminal := mem_badSourcesAt_iff.mp hsource
            have hr' : source.corridor.vertex r.castSucc = target := by
              rw [show r.castSucc =
                  (⟨source.corridor.length + 1, by omega⟩ :
                    Fin (source.corridor.length + 2)) by
                apply Fin.ext
                exact hlast]
              exact source.corridor.target_eq.trans hterminal
            exact hv (hr.symm.trans hr')
          omega⟩
        have hneutral := source.corridor.neutral rp
        convert hneutral using 1
        rw [← hr]
        apply congrArg source.corridor.vertex
        apply Fin.ext
        dsimp only [rp]
        simp
        omega
      exact ((hbad.not_neutral T) hneutral).elim

/-- Underlying vertices of the bad sources entering a fixed terminal. -/
def sourceVertices (T : NumericalType) (target : T.Component) :
    Finset T.Component :=
  (T.badSourcesAt target).image Subtype.val

lemma card_sourceVertices (T : NumericalType) (target : T.Component) :
    (T.sourceVertices target).card = (T.badSourcesAt target).card := by
  classical
  rw [sourceVertices, Finset.card_image_iff]
  intro a _ b _ h
  exact Subtype.ext h

lemma mem_sourceVertices_iff (T : NumericalType) {target v : T.Component} :
    v ∈ T.sourceVertices target ↔
      ∃ hbad : T.IsBadVertex v, (⟨v, hbad⟩ : T.BadComponent) ∈ T.badSourcesAt target := by
  classical
  constructor
  · intro hv
    rw [sourceVertices, Finset.mem_image] at hv
    obtain ⟨source, hsource, hs⟩ := hv
    subst v
    exact ⟨source.2, hsource⟩
  · rintro ⟨hbad, hv⟩
    rw [sourceVertices, Finset.mem_image]
    exact ⟨⟨v, hbad⟩, hv, rfl⟩

lemma target_not_mem_sourceVertices (T : NumericalType) (target : T.Component) :
    target ∉ T.sourceVertices target := by
  intro htarget
  obtain ⟨hbad, hmem⟩ := T.mem_sourceVertices_iff.mp htarget
  have hterminal := mem_badSourcesAt_iff.mp hmem
  exact T.nearestNonneutral_ne hbad hterminal

lemma degree_eq_one_of_bad (T : NumericalType) {v : T.Component}
    (hbad : T.IsBadVertex v) : T.intersectionGraph.degree v = 1 := by
  rw [← T.intersectionGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card]
  exact hbad.2.1

lemma degree_eq_two_of_neutral (T : NumericalType) {v : T.Component}
    (hneutral : T.IsNeutralVertex v) : T.intersectionGraph.degree v = 2 := by
  rw [← T.intersectionGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card]
  exact hneutral.2.1

/-- Vertices in a closed terminal cluster other than its terminal and bad sources. -/
def remainingVertices (T : NumericalType) (target : T.Component) :
    Finset T.Component :=
  Finset.univ \ insert target (T.sourceVertices target)

lemma degree_eq_two_of_mem_remaining (T : NumericalType) (target : T.Component)
    (hext : T.externalNeighbors target = ∅) {v : T.Component}
    (hv : v ∈ T.remainingVertices target) :
    T.intersectionGraph.degree v = 2 := by
  have hv' := Finset.mem_sdiff.mp hv
  have hvNot : v ≠ target ∧ v ∉ T.sourceVertices target := by
    simpa using hv'.2
  have hvTarget : v ≠ target := hvNot.1
  rcases T.bad_or_neutral_of_ne_target target hext hvTarget with hbad | hneutral
  · have hsource := T.badComponent_mem_badSourcesAt_of_ne_target target hext hbad hvTarget
    have hmem : v ∈ T.sourceVertices target :=
      T.mem_sourceVertices_iff.mpr ⟨hbad, hsource⟩
    exact (hv'.2 (Finset.mem_insert_of_mem hmem)).elim
  · exact T.degree_eq_two_of_neutral hneutral

lemma sum_degrees_of_externalNeighbors_eq_empty (T : NumericalType)
    (target : T.Component) (hext : T.externalNeighbors target = ∅) :
    ∑ v, T.intersectionGraph.degree v = 2 * (Fintype.card T.Component - 1) := by
  classical
  let S := T.sourceVertices target
  let R := T.remainingVertices target
  have htargetS : target ∉ S := T.target_not_mem_sourceVertices target
  have hinsertSubset : insert target S ⊆ (Finset.univ : Finset T.Component) := by simp
  have hdisjoint : Disjoint (insert target S) R := Finset.disjoint_sdiff
  have huniv : (Finset.univ : Finset T.Component) = insert target S ∪ R := by
    dsimp only [R, remainingVertices]
    exact (Finset.union_sdiff_of_subset hinsertSubset).symm
  have hdegreeTarget : T.intersectionGraph.degree target = S.card := by
    have hcard := T.card_neighborFinset_grouped target
    rw [hext, Finset.card_empty, Nat.add_zero,
      ← T.card_sourceVertices target] at hcard
    rw [← T.intersectionGraph.card_neighborFinset_eq_degree]
    exact hcard
  have hdegreeS : ∀ v ∈ S, T.intersectionGraph.degree v = 1 := by
    intro v hv
    obtain ⟨hbad, _⟩ := T.mem_sourceVertices_iff.mp hv
    exact T.degree_eq_one_of_bad hbad
  have hdegreeR : ∀ v ∈ R, T.intersectionGraph.degree v = 2 := by
    intro v hv
    exact T.degree_eq_two_of_mem_remaining target hext hv
  change (∑ v ∈ (Finset.univ : Finset T.Component),
    T.intersectionGraph.degree v) = _
  rw [huniv, Finset.sum_union hdisjoint, Finset.sum_insert htargetS]
  have hsumS : (∑ v ∈ S, T.intersectionGraph.degree v) = S.card := by
    calc
      _ = ∑ _v ∈ S, 1 := by
        apply Finset.sum_congr rfl
        exact hdegreeS
      _ = S.card := by simp
  have hsumR : (∑ v ∈ R, T.intersectionGraph.degree v) = 2 * R.card := by
    calc
      _ = ∑ _v ∈ R, 2 := by
        apply Finset.sum_congr rfl
        exact hdegreeR
      _ = 2 * R.card := by simp; omega
  rw [hdegreeTarget, hsumS, hsumR]
  have hcardUniv := congrArg Finset.card huniv
  rw [Finset.card_union_of_disjoint hdisjoint,
    Finset.card_insert_of_notMem htargetS] at hcardUniv
  rw [Finset.card_univ] at hcardUniv
  omega

/-- If a terminal has no neighbor outside its incoming bad corridors, the whole connected
graph is a subdivided tree and its topological genus is zero. -/
lemma topologicalGenus_eq_zero_of_externalNeighbors_eq_empty
    (T : NumericalType) (target : T.Component)
    (hext : T.externalNeighbors target = ∅) : T.topologicalGenus = 0 := by
  have hsum := T.sum_degrees_of_externalNeighbors_eq_empty target hext
  have hhandshake := T.intersectionGraph.sum_degrees_eq_twice_card_edges
  rw [hsum] at hhandshake
  have hedge : T.intersectionGraph.edgeFinset.card = Fintype.card T.Component - 1 := by
    omega
  have hedgeCard : Nat.card T.intersectionGraph.edgeSet =
      T.intersectionGraph.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  have hcomponentCard : Nat.card T.Component = Fintype.card T.Component :=
    Nat.card_eq_fintype_card
  rw [topologicalGenus, hedgeCard, hcomponentCard, hedge]
  have hpos : 0 < Fintype.card T.Component := Fintype.card_pos_iff.mpr inferInstance
  omega

/-- The finite set of all bundled bad components. -/
def badComponents (T : NumericalType) : Finset T.BadComponent := by
  classical
  exact Finset.univ

lemma mem_badComponents (T : NumericalType) (source : T.BadComponent) :
    source ∈ T.badComponents := by
  classical
  simp [badComponents]

lemma badSourcesAt_eq_filter (T : NumericalType) (target : T.Component) :
    T.badSourcesAt target = T.badComponents.filter fun source => source.terminal = target := by
  classical
  ext source
  simp [badSourcesAt, badComponents]

/-- Underlying vertices of all bad components. -/
def badVertices (T : NumericalType) : Finset T.Component :=
  T.badComponents.image Subtype.val

lemma mem_badVertices_iff (T : NumericalType) {v : T.Component} :
    v ∈ T.badVertices ↔ T.IsBadVertex v := by
  classical
  constructor
  · intro hv
    rw [badVertices, Finset.mem_image] at hv
    obtain ⟨source, _, hs⟩ := hv
    subst v
    exact source.2
  · intro hv
    rw [badVertices, Finset.mem_image]
    exact ⟨⟨v, hv⟩, T.mem_badComponents _, rfl⟩

/-- Terminals that receive at least one bad corridor. -/
def activeTerminals (T : NumericalType) : Finset T.Component := by
  classical
  exact Finset.univ.filter fun target => (T.badSourcesAt target).Nonempty

lemma mem_activeTerminals_iff (T : NumericalType) {target : T.Component} :
    target ∈ T.activeTerminals ↔ (T.badSourcesAt target).Nonempty := by
  classical
  simp [activeTerminals]

lemma activeTerminal_not_bad (T : NumericalType)
    (hgt : 0 < T.topologicalGenus) {target : T.Component}
    (htarget : target ∈ T.activeTerminals) : ¬ T.IsBadVertex target := by
  intro hbad
  have hsources := T.mem_activeTerminals_iff.mp htarget
  have hext : (T.externalNeighbors target).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hzero := T.topologicalGenus_eq_zero_of_externalNeighbors_eq_empty target hempty
    omega
  have hcard := T.card_neighborFinset_grouped target
  have hdegree : (T.intersectionGraph.neighborFinset target).card = 1 := by
    rw [T.intersectionGraph.card_neighborFinset_eq_degree]
    exact T.degree_eq_one_of_bad hbad
  have hbpos := Finset.card_pos.mpr hsources
  have hepos := Finset.card_pos.mpr hext
  omega

lemma disjoint_badVertices_activeTerminals (T : NumericalType)
    (hgt : 0 < T.topologicalGenus) :
    Disjoint T.badVertices T.activeTerminals := by
  rw [Finset.disjoint_left]
  intro v hvbad hvactive
  exact T.activeTerminal_not_bad hgt hvactive (T.mem_badVertices_iff.mp hvbad)

/-- The grouped charge assigned to one possible terminal. -/
def groupedSummand (T : NumericalType) (target : T.Component) : ℤ :=
  if (T.badSourcesAt target).Nonempty then
    T.twiceGenusDiscrepancy target +
      ∑ source ∈ T.badSourcesAt target, T.twiceGenusDiscrepancy source.1
  else 0

lemma groupedSummand_nonnegative (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component)
    (hgt : 0 < T.topologicalGenus) (target : T.Component) :
    0 ≤ T.groupedSummand target := by
  classical
  by_cases hsources : (T.badSourcesAt target).Nonempty
  · rw [groupedSummand, if_pos hsources]
    apply T.grouped_discrepancy_nonnegative hmin hcard target hsources
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hzero := T.topologicalGenus_eq_zero_of_externalNeighbors_eq_empty target hempty
    omega
  · rw [groupedSummand, if_neg hsources]

lemma sum_badComponent_eq_sum_badVertices (T : NumericalType) :
    (∑ source ∈ T.badComponents, T.twiceGenusDiscrepancy source.1) =
      ∑ v ∈ T.badVertices, T.twiceGenusDiscrepancy v := by
  classical
  rw [badVertices, Finset.sum_image]
  intro a _ b _ h
  exact Subtype.ext h

/-- Summing the grouped charges counts every active terminal and every bad component
exactly once. -/
lemma sum_groupedSummand (T : NumericalType) :
    (∑ target, T.groupedSummand target) =
      (∑ target ∈ T.activeTerminals, T.twiceGenusDiscrepancy target) +
        ∑ v ∈ T.badVertices, T.twiceGenusDiscrepancy v := by
  classical
  simp only [groupedSummand]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
  have hactive :
      (∑ x ∈ Finset.univ with (T.badSourcesAt x).Nonempty,
          T.twiceGenusDiscrepancy x) =
        ∑ x ∈ T.activeTerminals, T.twiceGenusDiscrepancy x := by
    rfl
  rw [hactive]
  have hfibers := Finset.sum_fiberwise T.badComponents
    BadComponent.terminal (fun source => T.twiceGenusDiscrepancy source.1)
  have hfiltered :
      (∑ target ∈ Finset.univ with (T.badSourcesAt target).Nonempty,
        ∑ source ∈ T.badSourcesAt target, T.twiceGenusDiscrepancy source.1) =
      ∑ target, ∑ source ∈ T.badSourcesAt target,
        T.twiceGenusDiscrepancy source.1 := by
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro target _
    by_cases h : (T.badSourcesAt target).Nonempty
    · rw [if_pos h]
    · rw [if_neg h]
      rw [Finset.not_nonempty_iff_eq_empty.mp h]
      simp
  rw [hfiltered]
  have hfibers' :
      (∑ target, ∑ source ∈ T.badSourcesAt target,
          T.twiceGenusDiscrepancy source.1) =
        ∑ source ∈ T.badComponents, T.twiceGenusDiscrepancy source.1 := by
    simpa only [badSourcesAt_eq_filter, Finset.mem_filter] using hfibers
  rw [hfibers', T.sum_badComponent_eq_sum_badVertices]

/-- Vertices paid for by the grouped borrowing argument. -/
def coveredVertices (T : NumericalType) : Finset T.Component :=
  T.badVertices ∪ T.activeTerminals

/-- Vertices outside all bad-source/terminal groups. -/
def unchargedVertices (T : NumericalType) : Finset T.Component :=
  Finset.univ \ T.coveredVertices

lemma univ_eq_covered_union_uncharged (T : NumericalType) :
    (Finset.univ : Finset T.Component) =
      T.coveredVertices ∪ T.unchargedVertices := by
  rw [unchargedVertices]
  exact (Finset.union_sdiff_of_subset (Finset.subset_univ _)).symm

lemma disjoint_covered_uncharged (T : NumericalType) :
    Disjoint T.coveredVertices T.unchargedVertices :=
  Finset.disjoint_sdiff

lemma sum_covered_eq (T : NumericalType) (hgt : 0 < T.topologicalGenus) :
    (∑ v ∈ T.coveredVertices, T.twiceGenusDiscrepancy v) =
      ∑ target, T.groupedSummand target := by
  rw [coveredVertices,
    Finset.sum_union (T.disjoint_badVertices_activeTerminals hgt),
    T.sum_groupedSummand]
  ring

lemma uncharged_discrepancy_nonnegative (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) {v : T.Component}
    (hv : v ∈ T.unchargedVertices) : 0 ≤ T.twiceGenusDiscrepancy v := by
  by_contra hneg
  have hbad := (T.twiceGenusDiscrepancy_neg_iff hcard v).mp (by omega)
  have hvbad : v ∈ T.badVertices := T.mem_badVertices_iff.mpr hbad
  have hvnot := (Finset.mem_sdiff.mp hv).2
  exact hvnot (Finset.mem_union_left _ hvbad)

/-- The sum of the local discrepancies is nonnegative for every minimal numerical type
with more than one component. -/
lemma sum_twiceGenusDiscrepancy_nonnegative (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component) :
    0 ≤ ∑ v, T.twiceGenusDiscrepancy v := by
  by_cases hgt : T.topologicalGenus = 0
  · have harith := T.one_le_arithmeticGenus_of_minimal hmin hcard
    rw [← T.two_mul_arithmeticGenus_sub_topologicalGenus]
    rw [hgt]
    norm_num
    omega
  · have hgtpos : 0 < T.topologicalGenus := Nat.pos_of_ne_zero hgt
    have hgroup : 0 ≤ ∑ target, T.groupedSummand target :=
      Finset.sum_nonneg fun target _ =>
        T.groupedSummand_nonnegative hmin hcard hgtpos target
    have hcovered : 0 ≤
        ∑ v ∈ T.coveredVertices, T.twiceGenusDiscrepancy v := by
      rw [T.sum_covered_eq hgtpos]
      exact hgroup
    have huncharged : 0 ≤
        ∑ v ∈ T.unchargedVertices, T.twiceGenusDiscrepancy v :=
      Finset.sum_nonneg fun v hv => T.uncharged_discrepancy_nonnegative hcard hv
    change 0 ≤ ∑ v ∈ (Finset.univ : Finset T.Component),
      T.twiceGenusDiscrepancy v
    rw [T.univ_eq_covered_union_uncharged,
      Finset.sum_union T.disjoint_covered_uncharged]
    omega

/-- Stacks Project tag `0C7C`: the graph-theoretic topological genus of a minimal
numerical type is at most its arithmetic genus. -/
theorem topologicalGenus_le_arithmeticGenus (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component) :
    (T.topologicalGenus : ℤ) ≤ T.arithmeticGenus := by
  have hsum := T.sum_twiceGenusDiscrepancy_nonnegative hmin hcard
  rw [← T.two_mul_arithmeticGenus_sub_topologicalGenus] at hsum
  omega

/-- A `(-2)`-vertex is a rational component whose self-intersection is twice the
negative component weight, in the terminology of Stacks Project tag `0C7E`. -/
def IsMinusTwoVertex (T : NumericalType) (i : T.Component) : Prop :=
  T.genus i = 0 ∧ T.intersection i i = -2 * (T.weight i : ℤ)

/-- It suffices to balance the positive off-diagonal contribution against the
`(-2)` diagonal on every indexed vertex. -/
lemma no_proper_balanced_minusTwo_subgraph (T : NumericalType)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → T.Component)
    (hv : Function.Injective v) (hproper : ∃ x, ∀ r, x ≠ v r)
    (hminus : ∀ r, T.IsMinusTwoVertex (v r))
    (a : ι → ℚ) (ha : ∀ r, 0 ≤ a r) (r : ι) (hr : a r ≠ 0)
    (hbalance : ∀ i,
      2 * (T.weight (v i) : ℚ) * a i ≤
        ∑ j ∈ Finset.univ.erase i,
          (T.intersection (v i) (v j) : ℚ) * a j) : False := by
  apply T.no_proper_subharmonic_indexedVector v hv hproper a ha r hr
  intro i
  have hdiag : (T.intersection (v i) (v i) : ℚ) =
      -2 * (T.weight (v i) : ℚ) := by
    exact_mod_cast (hminus i).2
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun j => (T.intersection (v i) (v j) : ℚ) * a j)
    (Finset.mem_univ i)
  rw [← hsplit, hdiag]
  linarith [hbalance i]

/-- A finite collection of selected off-diagonal entries that balances every
`(-2)` diagonal already supplies the forbidden subharmonic vector. -/
lemma no_proper_balanced_minusTwo_configuration (T : NumericalType)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → T.Component)
    (hv : Function.Injective v) (hproper : ∃ x, ∀ r, x ≠ v r)
    (hminus : ∀ r, T.IsMinusTwoVertex (v r))
    (a : ι → ℚ) (ha : ∀ r, 0 ≤ a r) (r : ι) (hr : a r ≠ 0)
    (neighbors : ι → Finset ι)
    (hneighbors : ∀ i, neighbors i ⊆ Finset.univ.erase i)
    (hbalance : ∀ i,
      2 * (T.weight (v i) : ℚ) * a i =
        ∑ j ∈ neighbors i, (T.intersection (v i) (v j) : ℚ) * a j) : False := by
  apply T.no_proper_balanced_minusTwo_subgraph v hv hproper hminus a ha r hr
  intro i
  rw [hbalance i]
  apply Finset.sum_le_sum_of_subset_of_nonneg (hneighbors i)
  intro j hj _
  have hji : j ≠ i := by simpa using hj
  have hvji : v i ≠ v j := hv.ne hji.symm
  have hA : (0 : ℚ) ≤ T.intersection (v i) (v j) := by
    exact_mod_cast T.offDiagonal_nonnegative (v i) (v j) hvji
  exact mul_nonneg hA (ha j)

/-- Any proper `(-2)` configuration containing a positive affine root is impossible.
Only adjacency is required: every selected positive intersection is at least its
source weight, while additional chords contribute nonnegatively. -/
lemma no_proper_affineDiagram_configuration (T : NumericalType)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → T.Component)
    (hv : Function.Injective v) (hproper : ∃ x, ∀ r, x ≠ v r)
    (hminus : ∀ r, T.IsMinusTwoVertex (v r))
    (a : ι → ℚ) (ha : ∀ r, 0 ≤ a r) (r : ι) (hr : a r ≠ 0)
    (neighbors : ι → Finset ι)
    (hneighbors : ∀ i, neighbors i ⊆ Finset.univ.erase i)
    (hcoeff : ∀ i, ∑ j ∈ neighbors i, a j = 2 * a i)
    (hadj : ∀ i j, j ∈ neighbors i → T.intersectionGraph.Adj (v i) (v j)) : False := by
  apply T.no_proper_balanced_minusTwo_subgraph v hv hproper hminus a ha r hr
  intro i
  calc
    2 * (T.weight (v i) : ℚ) * a i =
        (T.weight (v i) : ℚ) * (2 * a i) := by ring
    _ = (T.weight (v i) : ℚ) * ∑ j ∈ neighbors i, a j := by rw [hcoeff i]
    _ = ∑ j ∈ neighbors i, (T.weight (v i) : ℚ) * a j := by
      rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ neighbors i, (T.intersection (v i) (v j) : ℚ) * a j := by
      apply Finset.sum_le_sum
      intro j hj
      have hweight : (T.weight (v i) : ℚ) ≤ T.intersection (v i) (v j) := by
        exact_mod_cast T.weight_le_intersection_of_adj (hadj i j hj)
      exact mul_le_mul_of_nonneg_right hweight (ha j)
    _ ≤ ∑ j ∈ Finset.univ.erase i,
        (T.intersection (v i) (v j) : ℚ) * a j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (hneighbors i)
      intro j hj _
      have hji : j ≠ i := by simpa using hj
      have hvji : v i ≠ v j := hv.ne hji.symm
      have hA : (0 : ℚ) ≤ T.intersection (v i) (v j) := by
        exact_mod_cast T.offDiagonal_nonnegative (v i) (v j) hvji
      exact mul_nonneg hA (ha j)

/-- A proper family of `(-2)` vertices cannot contain an affine `A` cycle. -/
lemma no_affineA_configuration (T : NumericalType) (n : ℕ) (hn : 3 ≤ n)
    (v : Fin n → T.Component) (hv : Function.Injective v)
    (hproper : ∃ x, ∀ r, x ≠ v r)
    (hminus : ∀ r, T.IsMinusTwoVertex (v r))
    (hadj : ∀ i j, (SimpleGraph.cycleGraph n).Adj i j →
      T.intersectionGraph.Adj (v i) (v j)) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  apply T.no_proper_affineDiagram_configuration v hv hproper hminus
    (fun _ ↦ 1) (fun _ ↦ by norm_num) 0 (by norm_num)
    (fun i ↦ (SimpleGraph.cycleGraph (m + 3)).neighborFinset i)
  · intro i j hj
    rw [SimpleGraph.mem_neighborFinset] at hj
    exact Finset.mem_erase.mpr ⟨hj.ne.symm, Finset.mem_univ j⟩
  · intro i
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    change ((SimpleGraph.cycleGraph (m + 3)).degree i : ℚ) = 2
    have hdegree : (SimpleGraph.cycleGraph (m + 3)).degree i = 2 :=
      SimpleGraph.cycleGraph_degree_three_le
    norm_num [hdegree]
  · intro i j hj
    exact hadj i j
      (((SimpleGraph.cycleGraph (m + 3)).mem_neighborFinset i j).mp hj)

/-- Indices for the affine `D` tree: a nonempty spine and four side leaves. -/
abbrev AffineDIndex (n : ℕ) := Fin (n + 1) ⊕ Fin 4

/-- The standard positive null-root coefficients of an affine `D` tree. -/
def affineDCoeff (n : ℕ) : AffineDIndex n → ℚ
  | .inl _ => 2
  | .inr _ => 1

/-- The selected tree neighbors in an affine `D` diagram. -/
def affineDNeighbors (n : ℕ) (hn : 0 < n) :
    AffineDIndex n → Finset (AffineDIndex n)
  | .inl i =>
      if hi0 : i.val = 0 then
        {Sum.inl ⟨1, by omega⟩, Sum.inr 0, Sum.inr 1}
      else if hin : i.val = n then
        {Sum.inl ⟨n - 1, by omega⟩, Sum.inr 2, Sum.inr 3}
      else
        {Sum.inl ⟨i.val - 1, by omega⟩, Sum.inl ⟨i.val + 1, by omega⟩}
  | .inr k =>
      if k.val < 2 then {Sum.inl (0 : Fin (n + 1))}
      else {Sum.inl ⟨n, by omega⟩}

lemma affineDNeighbors_subset_erase (n : ℕ) (hn : 0 < n)
    (i : AffineDIndex n) :
    affineDNeighbors n hn i ⊆ Finset.univ.erase i := by
  rcases i with i | k
  · by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      rw [hi]
      intro j hj
      have hj' : j = Sum.inl (⟨1, by omega⟩ : Fin (n + 1)) ∨
          j = Sum.inr 0 ∨ j = Sum.inr 1 := by
        simpa [affineDNeighbors] using hj
      rcases hj' with rfl | rfl | rfl
      · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        intro heq
        have := congrArg (fun z : AffineDIndex n => match z with
          | .inl x => x.val
          | .inr _ => 0) heq
        norm_num at this
      · simp
      · simp
    · by_cases hin : i.val = n
      · have hi : i = ⟨n, by omega⟩ := Fin.ext hin
        rw [hi]
        intro j hj
        have hj' : j = Sum.inl (⟨n - 1, by omega⟩ : Fin (n + 1)) ∨
            j = Sum.inr 2 ∨ j = Sum.inr 3 := by
          simpa [affineDNeighbors, hn.ne'] using hj
        rcases hj' with rfl | rfl | rfl
        · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          intro heq
          have := congrArg (fun z : AffineDIndex n => match z with
            | .inl x => x.val
            | .inr _ => 0) heq
          simp only at this
          omega
        · simp
        · simp
      · intro j hj
        have hj' : j = Sum.inl (⟨i.val - 1, by omega⟩ : Fin (n + 1)) ∨
            j = Sum.inl (⟨i.val + 1, by omega⟩ : Fin (n + 1)) := by
          simpa [affineDNeighbors, hi0, hin] using hj
        rcases hj' with rfl | rfl
        · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          intro heq
          have := congrArg (fun z : AffineDIndex n => match z with
            | .inl x => x.val
            | .inr _ => 0) heq
          simp only at this
          omega
        · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          intro heq
          have := congrArg (fun z : AffineDIndex n => match z with
            | .inl x => x.val
            | .inr _ => 0) heq
          simp only at this
          omega
  · fin_cases k <;> simp [affineDNeighbors]

lemma sum_affineDCoeff_neighbors (n : ℕ) (hn : 0 < n)
    (i : AffineDIndex n) :
    ∑ j ∈ affineDNeighbors n hn i, affineDCoeff n j =
      2 * affineDCoeff n i := by
  rcases i with i | k
  · by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      rw [hi]
      simp [affineDNeighbors, affineDCoeff]
      norm_num
    · by_cases hin : i.val = n
      · have hi : i = ⟨n, by omega⟩ := Fin.ext hin
        rw [hi]
        simp [affineDNeighbors, affineDCoeff, hn.ne']
        norm_num
      · have hpredne : i.val - 1 ≠ i.val + 1 := by omega
        norm_num [affineDNeighbors, affineDCoeff, hi0, hin, hpredne]
  · fin_cases k <;> norm_num [affineDNeighbors, affineDCoeff]

/-- A proper family of `(-2)` vertices cannot contain an affine `D` diagram. -/
lemma no_affineD_configuration (T : NumericalType) (n : ℕ) (hn : 0 < n)
    (v : AffineDIndex n → T.Component) (hv : Function.Injective v)
    (hproper : ∃ x, ∀ r, x ≠ v r)
    (hminus : ∀ r, T.IsMinusTwoVertex (v r))
    (hadj : ∀ i j, j ∈ affineDNeighbors n hn i →
      T.intersectionGraph.Adj (v i) (v j)) : False := by
  exact T.no_proper_affineDiagram_configuration v hv hproper hminus
    (affineDCoeff n) (fun i => by rcases i with i | i <;> simp [affineDCoeff])
    (Sum.inl 0) (by simp [affineDCoeff]) (affineDNeighbors n hn)
    (affineDNeighbors_subset_erase n hn) (sum_affineDCoeff_neighbors n hn) hadj

/-- Standard null-root coefficients for affine `E₇`, with arm lengths `(1,3,3)`. -/
def affineE7Coeff (i : Fin 8) : ℚ :=
  match i.val with
  | 0 => 4
  | 1 => 2
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 2
  | _ => 1

/-- Selected neighbors for affine `E₇`; vertex `0` is the trivalent center. -/
def affineE7Neighbors : Fin 8 → Finset (Fin 8) :=
  ![{1, 2, 5}, {0}, {0, 3}, {2, 4}, {3}, {0, 6}, {5, 7}, {6}]

lemma affineE7Neighbors_subset_erase (i : Fin 8) :
    affineE7Neighbors i ⊆ Finset.univ.erase i := by
  fin_cases i <;> decide

lemma sum_affineE7Coeff_neighbors (i : Fin 8) :
    ∑ j ∈ affineE7Neighbors i, affineE7Coeff j = 2 * affineE7Coeff i := by
  fin_cases i <;> simp [affineE7Neighbors, affineE7Coeff, Finset.sum_insert] <;>
    norm_num

/-- A proper family of `(-2)` vertices cannot contain the affine `E₇` diagram. -/
lemma no_affineE7_configuration (T : NumericalType)
    (v : Fin 8 → T.Component) (hv : Function.Injective v)
    (hproper : ∃ x, ∀ r, x ≠ v r)
    (hminus : ∀ r, T.IsMinusTwoVertex (v r))
    (hadj : ∀ i j, j ∈ affineE7Neighbors i →
      T.intersectionGraph.Adj (v i) (v j)) : False := by
  exact T.no_proper_affineDiagram_configuration v hv hproper hminus
    affineE7Coeff (fun i => by fin_cases i <;> norm_num [affineE7Coeff])
    0 (by norm_num [affineE7Coeff]) affineE7Neighbors
    affineE7Neighbors_subset_erase sum_affineE7Coeff_neighbors hadj

/-- Standard null-root coefficients for affine `E₈`, with arm lengths `(1,2,5)`. -/
def affineE8Coeff (i : Fin 9) : ℚ :=
  match i.val with
  | 0 => 6
  | 1 => 3
  | 2 => 4
  | 3 => 2
  | 4 => 5
  | 5 => 4
  | 6 => 3
  | 7 => 2
  | _ => 1

/-- Selected neighbors for affine `E₈`; vertex `0` is the trivalent center. -/
def affineE8Neighbors : Fin 9 → Finset (Fin 9) :=
  ![{1, 2, 4}, {0}, {0, 3}, {2}, {0, 5}, {4, 6}, {5, 7}, {6, 8}, {7}]

lemma affineE8Neighbors_subset_erase (i : Fin 9) :
    affineE8Neighbors i ⊆ Finset.univ.erase i := by
  fin_cases i <;> decide

lemma sum_affineE8Coeff_neighbors (i : Fin 9) :
    ∑ j ∈ affineE8Neighbors i, affineE8Coeff j = 2 * affineE8Coeff i := by
  fin_cases i <;> simp [affineE8Neighbors, affineE8Coeff, Finset.sum_insert] <;>
    norm_num

/-- A proper family of `(-2)` vertices cannot contain the affine `E₈` diagram. -/
lemma no_affineE8_configuration (T : NumericalType)
    (v : Fin 9 → T.Component) (hv : Function.Injective v)
    (hproper : ∃ x, ∀ r, x ≠ v r)
    (hminus : ∀ r, T.IsMinusTwoVertex (v r))
    (hadj : ∀ i j, j ∈ affineE8Neighbors i →
      T.intersectionGraph.Adj (v i) (v j)) : False := by
  exact T.no_proper_affineDiagram_configuration v hv hproper hminus
    affineE8Coeff (fun i => by fin_cases i <;> norm_num [affineE8Coeff])
    0 (by norm_num [affineE8Coeff]) affineE8Neighbors
    affineE8Neighbors_subset_erase sum_affineE8Coeff_neighbors hadj

/-- A rational coefficient vector supported on two distinct components. -/
def pairVector (T : NumericalType) (i j : T.Component) (a b : ℚ) :
    T.Component → ℚ := fun k => if k = i then a else if k = j then b else 0

private lemma sum_mul_pairVector (T : NumericalType) {i j : T.Component}
    (hij : i ≠ j) (f : T.Component → ℚ) (a b : ℚ) :
    ∑ k, f k * T.pairVector i j a b k = f i * a + f j * b := by
  classical
  calc
    _ = ∑ k, ((if k = i then f k * a else 0) +
        (if k = j then f k * b else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k = i
      · simp [pairVector, hki, hij]
      · by_cases hkj : k = j
        · subst k
          simp [pairVector, hij.symm]
        · simp [pairVector, hki, hkj]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp

/-- Evaluation of the intersection form on a vector supported at two components. -/
lemma intersectionQuadratic_pair (T : NumericalType) {i j : T.Component}
    (hij : i ≠ j) (a b : ℚ) :
    T.intersectionQuadratic (T.pairVector i j a b) =
      (T.intersection i i : ℚ) * a ^ 2 +
        2 * (T.intersection i j : ℚ) * a * b +
          (T.intersection j j : ℚ) * b ^ 2 := by
  classical
  rw [intersectionQuadratic]
  have hinner (k : T.Component) :
      ∑ l, (T.intersection k l : ℚ) * T.pairVector i j a b l =
        (T.intersection k i : ℚ) * a + (T.intersection k j : ℚ) * b := by
    exact T.sum_mul_pairVector hij (fun l => (T.intersection k l : ℚ)) a b
  calc
    (∑ k, ∑ l, (T.intersection k l : ℚ) *
        T.pairVector i j a b k * T.pairVector i j a b l) =
        ∑ k, T.pairVector i j a b k *
          (∑ l, (T.intersection k l : ℚ) * T.pairVector i j a b l) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = ∑ k, T.pairVector i j a b k *
        ((T.intersection k i : ℚ) * a + (T.intersection k j : ℚ) * b) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hinner]
    _ = ((T.intersection i i : ℚ) * a + (T.intersection i j : ℚ) * b) * a +
        ((T.intersection j i : ℚ) * a + (T.intersection j j : ℚ) * b) * b := by
      rw [show (∑ k, T.pairVector i j a b k *
          ((T.intersection k i : ℚ) * a + (T.intersection k j : ℚ) * b)) =
          ∑ k, ((T.intersection k i : ℚ) * a +
            (T.intersection k j : ℚ) * b) * T.pairVector i j a b k by
        apply Finset.sum_congr rfl
        intro k _
        ring]
      exact T.sum_mul_pairVector hij
        (fun k => (T.intersection k i : ℚ) * a + (T.intersection k j : ℚ) * b) a b
    _ = _ := by
      rw [T.intersection_symm j i]
      ring

/-- A nonzero vector on two components has strictly negative intersection square when the
numerical type has at least one further component. -/
lemma twoVertexQuadratic_neg (T : NumericalType) {i j : T.Component}
    (hcard : 2 < Nat.card T.Component) (hij : i ≠ j) {a b : ℚ}
    (hne : a ≠ 0 ∨ b ≠ 0) :
    (T.intersection i i : ℚ) * a ^ 2 +
        2 * (T.intersection i j : ℚ) * a * b +
          (T.intersection j j : ℚ) * b ^ 2 < 0 := by
  classical
  let s : Finset T.Component := {i, j}
  have hs : s ≠ Finset.univ := by
    intro hs
    have hc := congrArg Finset.card hs
    have hsCard : s.card ≤ 2 := by
      dsimp [s]
      exact Finset.card_insert_le i {j}
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hc
    omega
  let x : {k // k ∈ s} → ℚ := fun k => if k.1 = i then a else b
  have hx : x ≠ 0 := by
    intro hzero
    rcases hne with ha | hb
    · have hi := congrFun hzero ⟨i, by simp [s]⟩
      change (if i = i then a else b) = 0 at hi
      rw [if_pos rfl] at hi
      exact ha hi
    · have hj := congrFun hzero ⟨j, by simp [s]⟩
      change (if j = i then a else b) = 0 at hj
      rw [if_neg hij.symm] at hj
      exact hb hj
  have hneg := T.subsetIntersectionQuadratic_neg s hs x hx
  have hext : T.extendByZero s x = T.pairVector i j a b := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [extendByZero, pairVector, s, x]
    · by_cases hkj : k = j
      · subst k
        simp [extendByZero, pairVector, s, x]
      · simp [extendByZero, pairVector, s, hki, hkj]
  change T.intersectionQuadratic (T.extendByZero s x) < 0 at hneg
  rw [hext, T.intersectionQuadratic_pair hij] at hneg
  exact hneg

/-- Two adjacent `(-2)` vertices in a proper subgraph have edge square strictly smaller
than four times the product of their weights. -/
lemma edge_square_lt_four_weight_product (T : NumericalType)
    (hcard : 2 < Nat.card T.Component) {i j : T.Component}
    (hi : T.IsMinusTwoVertex i) (hj : T.IsMinusTwoVertex j)
    (hij : T.intersectionGraph.Adj i j) :
    T.intersection i j ^ 2 <
      4 * (T.weight i : ℤ) * (T.weight j : ℤ) := by
  have hdiagI : T.intersection i i = -2 * (T.weight i : ℤ) := hi.2
  have hdiagJ : T.intersection j j = -2 * (T.weight j : ℤ) := hj.2
  have hneg := T.twoVertexQuadratic_neg hcard hij.ne
    (a := (T.intersection i j : ℚ))
    (b := 2 * (T.weight i : ℚ)) (Or.inl (by exact_mod_cast ne_of_gt hij.2))
  rw [hdiagI, hdiagJ] at hneg
  norm_num at hneg
  have hw : (0 : ℚ) < (T.weight i : ℚ) := by positivity
  have hq : (T.intersection i j : ℚ) ^ 2 <
      4 * (T.weight i : ℚ) * (T.weight j : ℚ) := by
    nlinarith
  exact_mod_cast hq

/-- The product of the two directed normalized indices of an edge. -/
def edgeIndexProduct (T : NumericalType) (i j : T.Component) : ℤ :=
  T.normalizedIntersection i j * T.normalizedIntersection j i

@[simp] lemma edgeIndexProduct_symm (T : NumericalType) (i j : T.Component) :
    T.edgeIndexProduct i j = T.edgeIndexProduct j i := by
  simp only [edgeIndexProduct]
  ring

/-- Clearing the two component weights turns the directed index product into the square
of the intersection entry. -/
lemma edgeIndexProduct_mul_weights (T : NumericalType) (i j : T.Component) :
    T.edgeIndexProduct i j * (T.weight i : ℤ) * (T.weight j : ℤ) =
      T.intersection i j ^ 2 := by
  dsimp [edgeIndexProduct]
  have hi := T.normalizedIntersection_mul_weight i j
  have hj := T.normalizedIntersection_mul_weight j i
  rw [T.intersection_symm j i] at hj
  calc
    _ = (T.normalizedIntersection i j * (T.weight i : ℤ)) *
        (T.normalizedIntersection j i * (T.weight j : ℤ)) := by ring
    _ = T.intersection i j * T.intersection i j := by rw [hi, hj]
    _ = _ := by ring

/-- The directed index product of an edge in a proper connected `(-2)` subgraph is one,
two, or three. -/
lemma edgeIndexProduct_mem (T : NumericalType)
    (hcard : 2 < Nat.card T.Component) {i j : T.Component}
    (hi : T.IsMinusTwoVertex i) (hj : T.IsMinusTwoVertex j)
    (hij : T.intersectionGraph.Adj i j) :
    T.edgeIndexProduct i j = 1 ∨ T.edgeIndexProduct i j = 2 ∨
      T.edgeIndexProduct i j = 3 := by
  have hqi := T.normalizedIntersection_pos_of_adj hij
  have hqj := T.normalizedIntersection_pos_of_adj hij.symm
  have hprodpos : 0 < T.edgeIndexProduct i j := by
    dsimp [edgeIndexProduct]
    positivity
  have hsquare := T.edge_square_lt_four_weight_product hcard hi hj hij
  have hexact := T.edgeIndexProduct_mul_weights i j
  have hwi : 0 < (T.weight i : ℤ) := by positivity
  have hwj : 0 < (T.weight j : ℤ) := by positivity
  have hprodlt : T.edgeIndexProduct i j < 4 := by nlinarith
  omega

/-- Stacks Project's two-vertex classification: after orienting an edge between `(-2)`
vertices, its two normalized indices are `(1,1)`, `(1,2)`, `(2,1)`, `(1,3)`, or `(3,1)`. -/
lemma edgeIndex_pair_classification (T : NumericalType)
    (hcard : 2 < Nat.card T.Component) {i j : T.Component}
    (hi : T.IsMinusTwoVertex i) (hj : T.IsMinusTwoVertex j)
    (hij : T.intersectionGraph.Adj i j) :
    (T.normalizedIntersection i j = 1 ∧ T.normalizedIntersection j i = 1) ∨
    (T.normalizedIntersection i j = 1 ∧ T.normalizedIntersection j i = 2) ∨
    (T.normalizedIntersection i j = 2 ∧ T.normalizedIntersection j i = 1) ∨
    (T.normalizedIntersection i j = 1 ∧ T.normalizedIntersection j i = 3) ∨
    (T.normalizedIntersection i j = 3 ∧ T.normalizedIntersection j i = 1) := by
  have hqi := T.normalizedIntersection_pos_of_adj hij
  have hqj := T.normalizedIntersection_pos_of_adj hij.symm
  have hp := T.edgeIndexProduct_mem hcard hi hj hij
  dsimp [edgeIndexProduct] at hp
  have hqile : T.normalizedIntersection i j ≤ 3 := by
    rcases hp with hp | hp | hp <;> nlinarith
  have hqjle : T.normalizedIntersection j i ≤ 3 := by
    rcases hp with hp | hp | hp <;> nlinarith
  interval_cases hqiCase : T.normalizedIntersection i j <;>
    interval_cases hqjCase : T.normalizedIntersection j i <;> simp_all

/-- A coefficient vector supported on three distinguished components. -/
def tripleVector (T : NumericalType) (i j k : T.Component) (a b c : ℚ) :
    T.Component → ℚ := fun l =>
  if l = i then a else if l = j then b else if l = k then c else 0

private lemma sum_mul_tripleVector (T : NumericalType) {i j k : T.Component}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (f : T.Component → ℚ) (a b c : ℚ) :
    ∑ l, f l * T.tripleVector i j k a b c l =
      f i * a + f j * b + f k * c := by
  classical
  calc
    _ = ∑ l, ((if l = i then f l * a else 0) +
        (if l = j then f l * b else 0) +
        (if l = k then f l * c else 0)) := by
      apply Finset.sum_congr rfl
      intro l _
      by_cases hli : l = i
      · subst l
        simp [tripleVector, hij, hik]
      · by_cases hlj : l = j
        · subst l
          simp [tripleVector, hij.symm, hjk]
        · by_cases hlk : l = k
          · subst l
            simp [tripleVector, hik.symm, hjk.symm]
          · simp [tripleVector, hli, hlj, hlk]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The intersection quadratic form evaluated on a vector supported on three components. -/
lemma intersectionQuadratic_triple (T : NumericalType) {i j k : T.Component}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b c : ℚ) :
    T.intersectionQuadratic (T.tripleVector i j k a b c) =
      (T.intersection i i : ℚ) * a ^ 2 +
      (T.intersection j j : ℚ) * b ^ 2 +
      (T.intersection k k : ℚ) * c ^ 2 +
      2 * (T.intersection i j : ℚ) * a * b +
      2 * (T.intersection i k : ℚ) * a * c +
      2 * (T.intersection j k : ℚ) * b * c := by
  classical
  rw [intersectionQuadratic]
  have hinner (l : T.Component) :
      ∑ r, (T.intersection l r : ℚ) * T.tripleVector i j k a b c r =
        (T.intersection l i : ℚ) * a + (T.intersection l j : ℚ) * b +
          (T.intersection l k : ℚ) * c := by
    exact T.sum_mul_tripleVector hij hik hjk
      (fun r => (T.intersection l r : ℚ)) a b c
  calc
    (∑ l, ∑ r, (T.intersection l r : ℚ) *
        T.tripleVector i j k a b c l * T.tripleVector i j k a b c r) =
        ∑ l, T.tripleVector i j k a b c l *
          (∑ r, (T.intersection l r : ℚ) * T.tripleVector i j k a b c r) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ∑ l, T.tripleVector i j k a b c l *
        ((T.intersection l i : ℚ) * a + (T.intersection l j : ℚ) * b +
          (T.intersection l k : ℚ) * c) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [hinner]
    _ = ((T.intersection i i : ℚ) * a + (T.intersection i j : ℚ) * b +
          (T.intersection i k : ℚ) * c) * a +
        ((T.intersection j i : ℚ) * a + (T.intersection j j : ℚ) * b +
          (T.intersection j k : ℚ) * c) * b +
        ((T.intersection k i : ℚ) * a + (T.intersection k j : ℚ) * b +
          (T.intersection k k : ℚ) * c) * c := by
      rw [show (∑ l, T.tripleVector i j k a b c l *
          ((T.intersection l i : ℚ) * a + (T.intersection l j : ℚ) * b +
            (T.intersection l k : ℚ) * c)) =
          ∑ l, ((T.intersection l i : ℚ) * a + (T.intersection l j : ℚ) * b +
            (T.intersection l k : ℚ) * c) * T.tripleVector i j k a b c l by
        apply Finset.sum_congr rfl
        intro l _
        ring]
      exact T.sum_mul_tripleVector hij hik hjk
        (fun l => (T.intersection l i : ℚ) * a + (T.intersection l j : ℚ) * b +
          (T.intersection l k : ℚ) * c) a b c
    _ = _ := by
      rw [T.intersection_symm j i, T.intersection_symm k i,
        T.intersection_symm k j]
      ring

/-- A nonzero vector on three components has strictly negative intersection square when
the numerical type has at least one further component. -/
lemma threeVertexQuadratic_neg (T : NumericalType) {i j k : T.Component}
    (hcard : 3 < Nat.card T.Component)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {a b c : ℚ}
    (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (T.intersection i i : ℚ) * a ^ 2 +
      (T.intersection j j : ℚ) * b ^ 2 +
      (T.intersection k k : ℚ) * c ^ 2 +
      2 * (T.intersection i j : ℚ) * a * b +
      2 * (T.intersection i k : ℚ) * a * c +
      2 * (T.intersection j k : ℚ) * b * c < 0 := by
  classical
  let s : Finset T.Component := {i, j, k}
  have hs : s ≠ Finset.univ := by
    intro hs
    have hc := congrArg Finset.card hs
    have hsCard : s.card ≤ 3 := by
      dsimp [s]
      calc
        ({i, j, k} : Finset T.Component).card ≤ ({j, k} : Finset T.Component).card + 1 :=
          Finset.card_insert_le i {j, k}
        _ ≤ 3 := by
          have := Finset.card_insert_le j ({k} : Finset T.Component)
          simp only [Finset.card_singleton] at this
          omega
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hc
    omega
  let x : {l // l ∈ s} → ℚ := fun l =>
    if l.1 = i then a else if l.1 = j then b else c
  have hx : x ≠ 0 := by
    intro hzero
    rcases hne with ha | hb | hc
    · have hi := congrFun hzero ⟨i, by simp [s]⟩
      change (if i = i then a else if i = j then b else c) = 0 at hi
      rw [if_pos rfl] at hi
      exact ha hi
    · have hj := congrFun hzero ⟨j, by simp [s]⟩
      change (if j = i then a else if j = j then b else c) = 0 at hj
      rw [if_neg hij.symm, if_pos rfl] at hj
      exact hb hj
    · have hk := congrFun hzero ⟨k, by simp [s]⟩
      change (if k = i then a else if k = j then b else c) = 0 at hk
      rw [if_neg hik.symm, if_neg hjk.symm] at hk
      exact hc hk
  have hneg := T.subsetIntersectionQuadratic_neg s hs x hx
  have hext : T.extendByZero s x = T.tripleVector i j k a b c := by
    funext l
    by_cases hli : l = i
    · subst l
      simp [extendByZero, tripleVector, s, x]
    · by_cases hlj : l = j
      · subst l
        simp [extendByZero, tripleVector, s, x, hij.symm]
      · by_cases hlk : l = k
        · subst l
          simp [extendByZero, tripleVector, s, x, hik.symm, hjk.symm]
        · simp [extendByZero, tripleVector, s, hli, hlj, hlk]
  change T.intersectionQuadratic (T.extendByZero s x) < 0 at hneg
  rw [hext, T.intersectionQuadratic_triple hij hik hjk] at hneg
  exact hneg

/-- At three consecutive distinct `(-2)` vertices in a proper subgraph, the sum of the
two edge-index products is strictly smaller than four. -/
lemma consecutive_edgeIndexProducts_lt_four (T : NumericalType)
    (hcard : 3 < Nat.card T.Component) {i j k : T.Component}
    (hi : T.IsMinusTwoVertex i) (hj : T.IsMinusTwoVertex j)
    (hk : T.IsMinusTwoVertex k)
    (hij : T.intersectionGraph.Adj i j) (hjk : T.intersectionGraph.Adj j k)
    (hik : i ≠ k) :
    T.edgeIndexProduct i j + T.edgeIndexProduct j k < 4 := by
  have hneg := T.threeVertexQuadratic_neg hcard hij.ne hik hjk.ne
    (a := (T.intersection i j : ℚ) * (T.weight k : ℚ))
    (b := 2 * (T.weight i : ℚ) * (T.weight k : ℚ))
    (c := (T.intersection j k : ℚ) * (T.weight i : ℚ))
    (Or.inl (mul_ne_zero (by exact_mod_cast ne_of_gt hij.2) (by positivity)))
  rw [hi.2, hj.2, hk.2] at hneg
  norm_num at hneg
  have hAij : (0 : ℚ) < (T.intersection i j : ℚ) := by exact_mod_cast hij.2
  have hAjk : (0 : ℚ) < (T.intersection j k : ℚ) := by exact_mod_cast hjk.2
  have hcross : 0 ≤ 2 * (T.intersection i k : ℚ) *
      ((T.intersection i j : ℚ) * (T.weight k : ℚ)) *
      ((T.intersection j k : ℚ) * (T.weight i : ℚ)) := by
    have hAik : 0 ≤ (T.intersection i k : ℚ) := by
      exact_mod_cast T.offDiagonal_nonnegative i k hik
    positivity
  have hrearrange :
      -(2 * (T.weight i : ℚ) *
            ((T.intersection i j : ℚ) * (T.weight k : ℚ)) ^ 2) +
          -(2 * (T.weight j : ℚ) *
            (2 * (T.weight i : ℚ) * (T.weight k : ℚ)) ^ 2) +
          -(2 * (T.weight k : ℚ) *
            ((T.intersection j k : ℚ) * (T.weight i : ℚ)) ^ 2) +
          2 * (T.intersection i j : ℚ) *
            ((T.intersection i j : ℚ) * (T.weight k : ℚ)) *
            (2 * (T.weight i : ℚ) * (T.weight k : ℚ)) +
          2 * (T.intersection i k : ℚ) *
            ((T.intersection i j : ℚ) * (T.weight k : ℚ)) *
            ((T.intersection j k : ℚ) * (T.weight i : ℚ)) +
          2 * (T.intersection j k : ℚ) *
            (2 * (T.weight i : ℚ) * (T.weight k : ℚ)) *
            ((T.intersection j k : ℚ) * (T.weight i : ℚ)) =
        2 * (T.weight i : ℚ) * (T.weight k : ℚ) *
          ((T.intersection i j : ℚ) ^ 2 * (T.weight k : ℚ) +
            (T.intersection j k : ℚ) ^ 2 * (T.weight i : ℚ) -
            4 * (T.weight i : ℚ) * (T.weight j : ℚ) * (T.weight k : ℚ)) +
          2 * (T.intersection i k : ℚ) *
            ((T.intersection i j : ℚ) * (T.weight k : ℚ)) *
            ((T.intersection j k : ℚ) * (T.weight i : ℚ)) := by ring
  rw [hrearrange] at hneg
  have hbase : (T.intersection i j : ℚ) ^ 2 * (T.weight k : ℚ) +
      (T.intersection j k : ℚ) ^ 2 * (T.weight i : ℚ) <
      4 * (T.weight i : ℚ) * (T.weight j : ℚ) * (T.weight k : ℚ) := by
    by_contra hnot
    have hbracket : 0 ≤
        (T.intersection i j : ℚ) ^ 2 * (T.weight k : ℚ) +
          (T.intersection j k : ℚ) ^ 2 * (T.weight i : ℚ) -
          4 * (T.weight i : ℚ) * (T.weight j : ℚ) * (T.weight k : ℚ) := by
      linarith
    have hmain : 0 ≤ 2 * (T.weight i : ℚ) * (T.weight k : ℚ) *
        ((T.intersection i j : ℚ) ^ 2 * (T.weight k : ℚ) +
          (T.intersection j k : ℚ) ^ 2 * (T.weight i : ℚ) -
          4 * (T.weight i : ℚ) * (T.weight j : ℚ) * (T.weight k : ℚ)) := by
      positivity
    linarith
  have hp := T.edgeIndexProduct_mul_weights i j
  have hq := T.edgeIndexProduct_mul_weights j k
  have hpQ : (T.edgeIndexProduct i j : ℚ) * (T.weight i : ℚ) *
      (T.weight j : ℚ) = (T.intersection i j : ℚ) ^ 2 := by exact_mod_cast hp
  have hqQ : (T.edgeIndexProduct j k : ℚ) * (T.weight j : ℚ) *
      (T.weight k : ℚ) = (T.intersection j k : ℚ) ^ 2 := by exact_mod_cast hq
  have hfactor :
      ((T.edgeIndexProduct i j + T.edgeIndexProduct j k : ℤ) : ℚ) *
        (T.weight i : ℚ) * (T.weight j : ℚ) * (T.weight k : ℚ) =
      (T.intersection i j : ℚ) ^ 2 * (T.weight k : ℚ) +
        (T.intersection j k : ℚ) ^ 2 * (T.weight i : ℚ) := by
    push_cast
    rw [← hpQ, ← hqQ]
    ring
  rw [← hfactor] at hbase
  have hprod : 0 < (T.weight i : ℚ) * (T.weight j : ℚ) *
      (T.weight k : ℚ) := by positivity
  have hrat : ((T.edgeIndexProduct i j + T.edgeIndexProduct j k : ℤ) : ℚ) < 4 := by
    nlinarith
  exact_mod_cast hrat

/-- Stacks Project's three-vertex local classification: consecutive edge-index products
are `(1,1)`, `(1,2)`, or `(2,1)`. -/
lemma consecutive_edgeIndexProducts_classification (T : NumericalType)
    (hcard : 3 < Nat.card T.Component) {i j k : T.Component}
    (hi : T.IsMinusTwoVertex i) (hj : T.IsMinusTwoVertex j)
    (hk : T.IsMinusTwoVertex k)
    (hij : T.intersectionGraph.Adj i j) (hjk : T.intersectionGraph.Adj j k)
    (hik : i ≠ k) :
    (T.edgeIndexProduct i j = 1 ∧ T.edgeIndexProduct j k = 1) ∨
    (T.edgeIndexProduct i j = 1 ∧ T.edgeIndexProduct j k = 2) ∨
    (T.edgeIndexProduct i j = 2 ∧ T.edgeIndexProduct j k = 1) := by
  have hp := T.edgeIndexProduct_mem (by omega) hi hj hij
  have hq := T.edgeIndexProduct_mem (by omega) hj hk hjk
  have hsum := T.consecutive_edgeIndexProducts_lt_four hcard hi hj hk hij hjk hik
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;> simp_all

/-- An edge-index product equal to one forces both directed normalized indices to be one. -/
lemma normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one
    (T : NumericalType) {i j : T.Component}
    (hij : T.intersectionGraph.Adj i j) (hprod : T.edgeIndexProduct i j = 1) :
    T.normalizedIntersection i j = 1 ∧ T.normalizedIntersection j i = 1 := by
  have hqi := T.normalizedIntersection_pos_of_adj hij
  have hqj := T.normalizedIntersection_pos_of_adj hij.symm
  dsimp [edgeIndexProduct] at hprod
  constructor <;> nlinarith

/-- The endpoint weights of an edge with index product one agree. -/
lemma weights_eq_of_edgeIndexProduct_eq_one (T : NumericalType)
    {i j : T.Component} (hij : T.intersectionGraph.Adj i j)
    (hprod : T.edgeIndexProduct i j = 1) : T.weight i = T.weight j := by
  have hq := T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one hij hprod
  have hi := T.normalizedIntersection_mul_weight i j
  have hj := T.normalizedIntersection_mul_weight j i
  rw [T.intersection_symm j i] at hj
  rw [hq.1] at hi
  rw [hq.2] at hj
  norm_num at hi hj
  exact_mod_cast hi.trans hj.symm

/-- On an edge with index product one, its intersection entry is its source weight. -/
lemma intersection_eq_weight_of_edgeIndexProduct_eq_one (T : NumericalType)
    {i j : T.Component} (hij : T.intersectionGraph.Adj i j)
    (hprod : T.edgeIndexProduct i j = 1) :
    T.intersection i j = (T.weight i : ℤ) := by
  have hq := T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one hij hprod
  have hi := T.normalizedIntersection_mul_weight i j
  rw [hq.1] at hi
  simpa using hi.symm

/-- An edge-index product of two makes one endpoint weight exactly twice the other. -/
lemma weights_ratio_of_edgeIndexProduct_eq_two (T : NumericalType)
    (hcard : 2 < Nat.card T.Component) {i j : T.Component}
    (hi : T.IsMinusTwoVertex i) (hj : T.IsMinusTwoVertex j)
    (hij : T.intersectionGraph.Adj i j) (hprod : T.edgeIndexProduct i j = 2) :
    (T.weight i : ℕ) = 2 * T.weight j ∨ (T.weight j : ℕ) = 2 * T.weight i := by
  have hclass := T.edgeIndex_pair_classification hcard hi hj hij
  have hnormi := T.normalizedIntersection_mul_weight i j
  have hnormj := T.normalizedIntersection_mul_weight j i
  rw [T.intersection_symm j i] at hnormj
  rcases hclass with h | h | h | h | h
  all_goals dsimp [edgeIndexProduct] at hprod
  · rw [h.1, h.2] at hprod
    norm_num at hprod
  · left
    rw [h.1] at hnormi
    rw [h.2] at hnormj
    norm_num at hnormi hnormj
    exact_mod_cast hnormi.trans hnormj.symm
  · right
    rw [h.1] at hnormi
    rw [h.2] at hnormj
    norm_num at hnormi hnormj
    exact_mod_cast hnormj.trans hnormi.symm
  · rw [h.1, h.2] at hprod
    norm_num at hprod
  · rw [h.1, h.2] at hprod
    norm_num at hprod

/-- Across an edge of index product one or two, either endpoint weight is at most twice
the other. -/
lemma weight_le_two_mul_of_edgeIndexProduct_eq_one_or_two (T : NumericalType)
    (hcard : 2 < Nat.card T.Component) {i j : T.Component}
    (hi : T.IsMinusTwoVertex i) (hj : T.IsMinusTwoVertex j)
    (hij : T.intersectionGraph.Adj i j)
    (hprod : T.edgeIndexProduct i j = 1 ∨ T.edgeIndexProduct i j = 2) :
    (T.weight i : ℕ) ≤ 2 * T.weight j := by
  rcases hprod with hprod | hprod
  · have hw := T.weights_eq_of_edgeIndexProduct_eq_one hij hprod
    have hwNat : (T.weight i : ℕ) = T.weight j := congrArg Subtype.val hw
    omega
  · rcases T.weights_ratio_of_edgeIndexProduct_eq_two hcard hi hj hij hprod with hw | hw
    · omega
    · omega


/-- Dividing a fibre row by its component weight gives the normalized fibre relation. -/
lemma normalized_fiber_relation (T : NumericalType) (i : T.Component) :
    ∑ j, (T.multiplicity j : ℤ) * T.normalizedIntersection i j = 0 := by
  have hw : (T.weight i : ℤ) ≠ 0 := by positivity
  apply (mul_eq_zero.mp ?_).resolve_right hw
  calc
    (∑ j, (T.multiplicity j : ℤ) * T.normalizedIntersection i j) *
        (T.weight i : ℤ) =
        ∑ j, (T.multiplicity j : ℤ) *
          (T.normalizedIntersection i j * (T.weight i : ℤ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j, (T.multiplicity j : ℤ) * T.intersection i j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [T.normalizedIntersection_mul_weight]
    _ = 0 := T.fiber_relation i

/-- The normalized diagonal entry of a `(-2)` component is `-2`. -/
lemma normalizedIntersection_self_eq_neg_two (T : NumericalType)
    {i : T.Component} (hi : T.IsMinusTwoVertex i) :
    T.normalizedIntersection i i = -2 := by
  have heq := T.normalizedIntersection_mul_weight i i
  rw [hi.2] at heq
  have hw : (0 : ℤ) < (T.weight i : ℤ) := by positivity
  nlinarith

/-- Every normalized off-diagonal intersection index is nonnegative. -/
lemma normalizedIntersection_nonnegative (T : NumericalType)
    {i j : T.Component} (hij : i ≠ j) : 0 ≤ T.normalizedIntersection i j := by
  by_cases hadj : T.intersectionGraph.Adj i j
  · exact le_of_lt (T.normalizedIntersection_pos_of_adj hadj)
  · rw [T.normalizedIntersection_eq_zero_of_not_adj hij hadj]

/-- Any two distinct neighbors consume at most the full normalized fibre balance at a
`(-2)` vertex. -/
lemma minusTwo_two_neighbor_multiplicity_le (T : NumericalType)
    {i j k : T.Component} (hj : T.IsMinusTwoVertex j)
    (hij : T.intersectionGraph.Adj j i) (hjk : T.intersectionGraph.Adj j k)
    (hik : i ≠ k) :
    (T.multiplicity i : ℤ) * T.normalizedIntersection j i +
      (T.multiplicity k : ℤ) * T.normalizedIntersection j k ≤
        2 * (T.multiplicity j : ℤ) := by
  classical
  have hrow := T.normalized_fiber_relation j
  have hdiag := T.normalizedIntersection_self_eq_neg_two hj
  have hsumOff :
      ∑ r ∈ Finset.univ.erase j,
          (T.multiplicity r : ℤ) * T.normalizedIntersection j r =
        2 * (T.multiplicity j : ℤ) := by
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun r => (T.multiplicity r : ℤ) * T.normalizedIntersection j r)
      (Finset.mem_univ j)
    rw [hrow, hdiag] at hsplit
    nlinarith
  rw [← hsumOff]
  have hsubset : ({i, k} : Finset T.Component) ⊆ Finset.univ.erase j := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · simp [hij.ne.symm]
    · simp [hjk.ne.symm]
  calc
    (T.multiplicity i : ℤ) * T.normalizedIntersection j i +
        (T.multiplicity k : ℤ) * T.normalizedIntersection j k =
        ∑ r ∈ ({i, k} : Finset T.Component),
          (T.multiplicity r : ℤ) * T.normalizedIntersection j r := by
      simp [hik]
    _ ≤ ∑ r ∈ Finset.univ.erase j,
          (T.multiplicity r : ℤ) * T.normalizedIntersection j r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro r hr _
      have hrj : r ≠ j := by simpa using hr
      exact mul_nonneg (by positivity) (T.normalizedIntersection_nonnegative hrj.symm)

/-- Multiplicities are concave across two unit-index edges through a `(-2)` vertex. -/
lemma minusTwo_multiplicity_concave_of_unit_edges (T : NumericalType)
    {i j k : T.Component} (hj : T.IsMinusTwoVertex j)
    (hij : T.intersectionGraph.Adj j i) (hjk : T.intersectionGraph.Adj j k)
    (hik : i ≠ k) (hleft : T.edgeIndexProduct j i = 1)
    (hright : T.edgeIndexProduct j k = 1) :
    (T.multiplicity i : ℤ) + (T.multiplicity k : ℤ) ≤
      2 * (T.multiplicity j : ℤ) := by
  have hni := (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one hij hleft).1
  have hnk := (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one hjk hright).1
  simpa [hni, hnk] using T.minusTwo_two_neighbor_multiplicity_le hj hij hjk hik

/-- At a `(-2)` vertex with exactly two possible `(-2)` neighbors, a strict deficit
across two unit-index edges must be supplied by an edge to the non-`(-2)` heart. -/
lemma exists_heart_neighbor_of_strict_unit_neighbors (T : NumericalType)
    {i j k : T.Component} (hj : T.IsMinusTwoVertex j)
    (hji : T.intersectionGraph.Adj j i) (hjk : T.intersectionGraph.Adj j k)
    (hik : i ≠ k) (hleft : T.edgeIndexProduct j i = 1)
    (hright : T.edgeIndexProduct j k = 1)
    (hstrict : (T.multiplicity i : ℤ) + (T.multiplicity k : ℤ) <
      2 * (T.multiplicity j : ℤ))
    (hneighbors : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj j r → r = i ∨ r = k) :
    ∃ source, ¬ T.IsMinusTwoVertex source ∧
      T.intersectionGraph.Adj j source := by
  classical
  by_contra hno
  push Not at hno
  have hni := (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one
    hji hleft).1
  have hnk := (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one
    hjk hright).1
  let pair : Finset T.Component := {i, k}
  let off : Finset T.Component := Finset.univ.erase j
  have hsubset : pair ⊆ off := by
    intro r hr
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · simp [off, hji.ne.symm]
    · simp [off, hjk.ne.symm]
  have hzero : ∀ r ∈ off, r ∉ pair →
      (T.multiplicity r : ℤ) * T.normalizedIntersection j r = 0 := by
    intro r hroff hrpair
    have hrj : r ≠ j := by simpa [off] using hroff
    have hnotAdj : ¬ T.intersectionGraph.Adj j r := by
      intro hadj
      have hrminus : T.IsMinusTwoVertex r := by
        by_contra hrheart
        exact hno r hrheart hadj
      rcases hneighbors r hrminus hadj with rfl | rfl <;>
        exact hrpair (by simp [pair])
    rw [T.normalizedIntersection_eq_zero_of_not_adj hrj.symm hnotAdj]
    ring
  have hsums :
      ∑ r ∈ pair, (T.multiplicity r : ℤ) * T.normalizedIntersection j r =
        ∑ r ∈ off, (T.multiplicity r : ℤ) * T.normalizedIntersection j r := by
    exact Finset.sum_subset hsubset hzero
  have hpair :
      ∑ r ∈ pair, (T.multiplicity r : ℤ) * T.normalizedIntersection j r =
        (T.multiplicity i : ℤ) + T.multiplicity k := by
    simp [pair, hik, hni, hnk]
  have hrow := T.normalized_fiber_relation j
  have hdiag := T.normalizedIntersection_self_eq_neg_two hj
  have hoff :
      ∑ r ∈ off, (T.multiplicity r : ℤ) * T.normalizedIntersection j r =
        2 * (T.multiplicity j : ℤ) := by
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun r => (T.multiplicity r : ℤ) * T.normalizedIntersection j r)
      (Finset.mem_univ j)
    change (∑ r ∈ off,
      (T.multiplicity r : ℤ) * T.normalizedIntersection j r) +
      (T.multiplicity j : ℤ) * T.normalizedIntersection j j =
        ∑ r, (T.multiplicity r : ℤ) * T.normalizedIntersection j r at hsplit
    rw [hrow, hdiag] at hsplit
    nlinarith
  rw [hpair, hoff] at hsums
  omega

/-- If a `(-2)` vertex has only one possible `(-2)` neighbor and that neighbor does not
fill the normalized fibre balance, some heart edge supplies the deficit. -/
lemma exists_heart_neighbor_of_strict_single_neighbor (T : NumericalType)
    {i j : T.Component} (hj : T.IsMinusTwoVertex j)
    (hji : T.intersectionGraph.Adj j i)
    (hstrict : (T.multiplicity i : ℤ) * T.normalizedIntersection j i <
      2 * (T.multiplicity j : ℤ))
    (hneighbors : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj j r → r = i) :
    ∃ source, ¬ T.IsMinusTwoVertex source ∧
      T.intersectionGraph.Adj j source := by
  classical
  by_contra hno
  push Not at hno
  let one : Finset T.Component := {i}
  let off : Finset T.Component := Finset.univ.erase j
  have hsubset : one ⊆ off := by
    intro r hr
    simp only [one, Finset.mem_singleton] at hr
    subst r
    simp [off, hji.ne.symm]
  have hzero : ∀ r ∈ off, r ∉ one →
      (T.multiplicity r : ℤ) * T.normalizedIntersection j r = 0 := by
    intro r hroff hrone
    have hrj : r ≠ j := by simpa [off] using hroff
    have hnotAdj : ¬ T.intersectionGraph.Adj j r := by
      intro hadj
      have hrminus : T.IsMinusTwoVertex r := by
        by_contra hrheart
        exact hno r hrheart hadj
      have hri := hneighbors r hrminus hadj
      subst r
      exact hrone (by simp [one])
    rw [T.normalizedIntersection_eq_zero_of_not_adj hrj.symm hnotAdj]
    ring
  have hsums :
      ∑ r ∈ one, (T.multiplicity r : ℤ) * T.normalizedIntersection j r =
        ∑ r ∈ off, (T.multiplicity r : ℤ) * T.normalizedIntersection j r :=
    Finset.sum_subset hsubset hzero
  have hone :
      ∑ r ∈ one, (T.multiplicity r : ℤ) * T.normalizedIntersection j r =
        (T.multiplicity i : ℤ) * T.normalizedIntersection j i := by simp [one]
  have hrow := T.normalized_fiber_relation j
  have hdiag := T.normalizedIntersection_self_eq_neg_two hj
  have hoff :
      ∑ r ∈ off, (T.multiplicity r : ℤ) * T.normalizedIntersection j r =
        2 * (T.multiplicity j : ℤ) := by
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun r => (T.multiplicity r : ℤ) * T.normalizedIntersection j r)
      (Finset.mem_univ j)
    change (∑ r ∈ off,
      (T.multiplicity r : ℤ) * T.normalizedIntersection j r) +
      (T.multiplicity j : ℤ) * T.normalizedIntersection j j =
        ∑ r, (T.multiplicity r : ℤ) * T.normalizedIntersection j r at hsplit
    rw [hrow, hdiag] at hsplit
    nlinarith
  rw [hone, hoff] at hsums
  omega

/-- If every graph neighbor of a `(-2)` vertex outside a specified finite set would
have to lie in the heart, and there are no heart edges, that set accounts for the
entire normalized fibre balance. -/
lemma normalized_neighbor_balance_eq_of_no_heart (T : NumericalType)
    {j : T.Component} (hj : T.IsMinusTwoVertex j) (s : Finset T.Component)
    (hnotself : ∀ r ∈ s, r ≠ j)
    (hneighbors : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj j r → r ∈ s)
    (hnoHeart : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj j source) :
    ∑ r ∈ s, (T.multiplicity r : ℤ) * T.normalizedIntersection j r =
      2 * (T.multiplicity j : ℤ) := by
  classical
  let off : Finset T.Component := Finset.univ.erase j
  have hsubset : s ⊆ off := by
    intro r hr
    simp [off, hnotself r hr]
  have hzero : ∀ r ∈ off, r ∉ s →
      (T.multiplicity r : ℤ) * T.normalizedIntersection j r = 0 := by
    intro r hroff hrs
    have hrj : r ≠ j := by simpa [off] using hroff
    have hnotAdj : ¬ T.intersectionGraph.Adj j r := by
      intro hadj
      have hrminus : T.IsMinusTwoVertex r := by
        by_contra hrheart
        exact hnoHeart r hrheart hadj
      exact hrs (hneighbors r hrminus hadj)
    rw [T.normalizedIntersection_eq_zero_of_not_adj hrj.symm hnotAdj]
    ring
  have hsums :
      ∑ r ∈ s, (T.multiplicity r : ℤ) * T.normalizedIntersection j r =
        ∑ r ∈ off, (T.multiplicity r : ℤ) * T.normalizedIntersection j r :=
    Finset.sum_subset hsubset hzero
  have hrow := T.normalized_fiber_relation j
  have hdiag := T.normalizedIntersection_self_eq_neg_two hj
  have hoff :
      ∑ r ∈ off, (T.multiplicity r : ℤ) * T.normalizedIntersection j r =
        2 * (T.multiplicity j : ℤ) := by
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun r => (T.multiplicity r : ℤ) * T.normalizedIntersection j r)
      (Finset.mem_univ j)
    change (∑ r ∈ off,
      (T.multiplicity r : ℤ) * T.normalizedIntersection j r) +
      (T.multiplicity j : ℤ) * T.normalizedIntersection j j =
        ∑ r, (T.multiplicity r : ℤ) * T.normalizedIntersection j r at hsplit
    rw [hrow, hdiag] at hsplit
    nlinarith
  exact hsums.trans hoff

lemma normalized_single_neighbor_balance_eq_of_no_heart (T : NumericalType)
    {i j : T.Component} (hj : T.IsMinusTwoVertex j)
    (hji : T.intersectionGraph.Adj j i)
    (hneighbors : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj j r → r = i)
    (hnoHeart : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj j source) :
    (T.multiplicity i : ℤ) * T.normalizedIntersection j i =
      2 * (T.multiplicity j : ℤ) := by
  have h := T.normalized_neighbor_balance_eq_of_no_heart hj {i}
    (by simpa using hji.ne.symm)
    (fun r hr hadj => by simp [hneighbors r hr hadj]) hnoHeart
  simpa using h

lemma normalized_two_neighbor_balance_eq_of_no_heart (T : NumericalType)
    {i j k : T.Component} (hj : T.IsMinusTwoVertex j)
    (hji : T.intersectionGraph.Adj j i) (hjk : T.intersectionGraph.Adj j k)
    (hik : i ≠ k)
    (hneighbors : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj j r → r = i ∨ r = k)
    (hnoHeart : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj j source) :
    (T.multiplicity i : ℤ) * T.normalizedIntersection j i +
        (T.multiplicity k : ℤ) * T.normalizedIntersection j k =
      2 * (T.multiplicity j : ℤ) := by
  have h := T.normalized_neighbor_balance_eq_of_no_heart hj {i, k}
    (by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hji.ne.symm
      · exact hjk.ne.symm)
    (fun r hr hadj => by rcases hneighbors r hr hadj with rfl | rfl <;> simp)
    hnoHeart
  simpa [hik] using h


/-- In a triangular configuration, two edges of index product one force the third to
have index product one as well. -/
lemma edgeIndexProduct_eq_one_of_two_adjacent_products_eq_one
    (T : NumericalType) (hcard : 3 < Nat.card T.Component)
    {i j k : T.Component} (hi : T.IsMinusTwoVertex i)
    (_hj : T.IsMinusTwoVertex j) (hk : T.IsMinusTwoVertex k)
    (hij : T.intersectionGraph.Adj i j) (hjk : T.intersectionGraph.Adj j k)
    (hki : T.intersectionGraph.Adj k i)
    (hp : T.edgeIndexProduct i j = 1) (hq : T.edgeIndexProduct j k = 1) :
    T.edgeIndexProduct k i = 1 := by
  have hwji := (T.weights_eq_of_edgeIndexProduct_eq_one hij hp).symm
  have hwjk := T.weights_eq_of_edgeIndexProduct_eq_one hjk hq
  have hwki : T.weight k = T.weight i := hwjk.symm.trans hwji
  have hnormki := T.normalizedIntersection_mul_weight k i
  have hnormik := T.normalizedIntersection_mul_weight i k
  have hwkiZ : (T.weight k : ℤ) = (T.weight i : ℤ) := by exact_mod_cast hwki
  rw [T.intersection_symm i k, ← hwkiZ] at hnormik
  have hweight : (0 : ℤ) < (T.weight k : ℤ) := by positivity
  have hnormalized : T.normalizedIntersection k i = T.normalizedIntersection i k := by
    nlinarith
  have hr := T.edgeIndexProduct_mem (by omega) hk hi hki
  have hpos := T.normalizedIntersection_pos_of_adj hki
  dsimp [edgeIndexProduct] at hr ⊢
  rw [hnormalized]
  rcases hr with hr | hr | hr
  · simpa [hnormalized] using hr
  · rw [hnormalized] at hr
    have hlt : T.normalizedIntersection i k < 2 := by nlinarith
    have hone : T.normalizedIntersection i k = 1 := by omega
    simp [hone] at hr
  · rw [hnormalized] at hr
    have hlt : T.normalizedIntersection i k < 2 := by nlinarith
    have hone : T.normalizedIntersection i k = 1 := by omega
    simp [hone] at hr

/-- If three `(-2)` vertices formed a triangle, all three edge-index products would be
one. -/
lemma minusTwo_triangle_products_eq_one (T : NumericalType)
    (hcard : 3 < Nat.card T.Component) {i j k : T.Component}
    (hi : T.IsMinusTwoVertex i) (hj : T.IsMinusTwoVertex j)
    (hk : T.IsMinusTwoVertex k)
    (hij : T.intersectionGraph.Adj i j) (hjk : T.intersectionGraph.Adj j k)
    (hki : T.intersectionGraph.Adj k i) :
    T.edgeIndexProduct i j = 1 ∧ T.edgeIndexProduct j k = 1 ∧
      T.edgeIndexProduct k i = 1 := by
  have hpq := T.consecutive_edgeIndexProducts_classification hcard hi hj hk
    hij hjk hki.ne.symm
  have hqr := T.consecutive_edgeIndexProducts_classification hcard hj hk hi
    hjk hki hij.ne.symm
  have hrp := T.consecutive_edgeIndexProducts_classification hcard hk hi hj
    hki hij hjk.ne.symm
  rcases hpq with hpq | hpq | hpq
  · refine ⟨hpq.1, hpq.2, ?_⟩
    exact T.edgeIndexProduct_eq_one_of_two_adjacent_products_eq_one hcard
      hi hj hk hij hjk hki hpq.1 hpq.2
  · have hr : T.edgeIndexProduct k i = 1 := by
      rcases hqr with hqr | hqr | hqr <;> simp_all
    have hq := T.edgeIndexProduct_eq_one_of_two_adjacent_products_eq_one hcard
      hk hi hj hki hij hjk hr hpq.1
    omega
  · rcases hqr with hqr | hqr | hqr
    · have hp := T.edgeIndexProduct_eq_one_of_two_adjacent_products_eq_one hcard
        hj hk hi hjk hki hij hqr.1 hqr.2
      omega
    · have hbad := hrp
      rcases hbad with hbad | hbad | hbad <;> omega
    · omega

/-- A proper `(-2)` subgraph contains no triangle. -/
lemma no_minusTwo_triangle (T : NumericalType)
    (hcard : 3 < Nat.card T.Component) {i j k : T.Component}
    (hi : T.IsMinusTwoVertex i) (hj : T.IsMinusTwoVertex j)
    (hk : T.IsMinusTwoVertex k)
    (hij : T.intersectionGraph.Adj i j) (hjk : T.intersectionGraph.Adj j k)
    (hki : T.intersectionGraph.Adj k i) : False := by
  have hp := T.minusTwo_triangle_products_eq_one hcard hi hj hk hij hjk hki
  have hwij := T.weights_eq_of_edgeIndexProduct_eq_one hij hp.1
  have hwjk := T.weights_eq_of_edgeIndexProduct_eq_one hjk hp.2.1
  have haij := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hij hp.1
  have hajk := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hjk hp.2.1
  have haki := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hki hp.2.2
  have hneg := T.threeVertexQuadratic_neg hcard hij.ne hki.ne.symm hjk.ne
    (a := 1) (b := 1) (c := 1) (Or.inl one_ne_zero)
  rw [hi.2, hj.2, hk.2, haij, hajk, T.intersection_symm i k, haki] at hneg
  norm_num at hneg
  linarith

/-- A coefficient vector supported on four distinguished components. -/
def quadrupleVector (T : NumericalType) (i j k l : T.Component)
    (a b c d : ℚ) : T.Component → ℚ := fun r =>
  if r = i then a else if r = j then b else if r = k then c else if r = l then d else 0

private lemma sum_mul_quadrupleVector (T : NumericalType) {i j k l : T.Component}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) (f : T.Component → ℚ) (a b c d : ℚ) :
    ∑ r, f r * T.quadrupleVector i j k l a b c d r =
      f i * a + f j * b + f k * c + f l * d := by
  classical
  calc
    _ = ∑ r, ((if r = i then f r * a else 0) +
        (if r = j then f r * b else 0) +
        (if r = k then f r * c else 0) +
        (if r = l then f r * d else 0)) := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hri : r = i
      · subst r
        simp [quadrupleVector, hij, hik, hil]
      · by_cases hrj : r = j
        · subst r
          simp [quadrupleVector, hij.symm, hjk, hjl]
        · by_cases hrk : r = k
          · subst r
            simp [quadrupleVector, hik.symm, hjk.symm, hkl]
          · by_cases hrl : r = l
            · subst r
              simp [quadrupleVector, hil.symm, hjl.symm, hkl.symm]
            · simp [quadrupleVector, hri, hrj, hrk, hrl]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The intersection quadratic form evaluated on a vector supported on four components. -/
lemma intersectionQuadratic_quadruple (T : NumericalType) {i j k l : T.Component}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) (a b c d : ℚ) :
    T.intersectionQuadratic (T.quadrupleVector i j k l a b c d) =
      (T.intersection i i : ℚ) * a ^ 2 +
      (T.intersection j j : ℚ) * b ^ 2 +
      (T.intersection k k : ℚ) * c ^ 2 +
      (T.intersection l l : ℚ) * d ^ 2 +
      2 * (T.intersection i j : ℚ) * a * b +
      2 * (T.intersection i k : ℚ) * a * c +
      2 * (T.intersection i l : ℚ) * a * d +
      2 * (T.intersection j k : ℚ) * b * c +
      2 * (T.intersection j l : ℚ) * b * d +
      2 * (T.intersection k l : ℚ) * c * d := by
  classical
  rw [intersectionQuadratic]
  have hinner (r : T.Component) :
      ∑ s, (T.intersection r s : ℚ) * T.quadrupleVector i j k l a b c d s =
        (T.intersection r i : ℚ) * a + (T.intersection r j : ℚ) * b +
        (T.intersection r k : ℚ) * c + (T.intersection r l : ℚ) * d := by
    exact T.sum_mul_quadrupleVector hij hik hil hjk hjl hkl
      (fun s => (T.intersection r s : ℚ)) a b c d
  calc
    (∑ r, ∑ s, (T.intersection r s : ℚ) *
        T.quadrupleVector i j k l a b c d r *
        T.quadrupleVector i j k l a b c d s) =
        ∑ r, T.quadrupleVector i j k l a b c d r *
          (∑ s, (T.intersection r s : ℚ) *
            T.quadrupleVector i j k l a b c d s) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = ∑ r, T.quadrupleVector i j k l a b c d r *
        ((T.intersection r i : ℚ) * a + (T.intersection r j : ℚ) * b +
          (T.intersection r k : ℚ) * c + (T.intersection r l : ℚ) * d) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [hinner]
    _ = ((T.intersection i i : ℚ) * a + (T.intersection i j : ℚ) * b +
          (T.intersection i k : ℚ) * c + (T.intersection i l : ℚ) * d) * a +
        ((T.intersection j i : ℚ) * a + (T.intersection j j : ℚ) * b +
          (T.intersection j k : ℚ) * c + (T.intersection j l : ℚ) * d) * b +
        ((T.intersection k i : ℚ) * a + (T.intersection k j : ℚ) * b +
          (T.intersection k k : ℚ) * c + (T.intersection k l : ℚ) * d) * c +
        ((T.intersection l i : ℚ) * a + (T.intersection l j : ℚ) * b +
          (T.intersection l k : ℚ) * c + (T.intersection l l : ℚ) * d) * d := by
      rw [show (∑ r, T.quadrupleVector i j k l a b c d r *
          ((T.intersection r i : ℚ) * a + (T.intersection r j : ℚ) * b +
            (T.intersection r k : ℚ) * c + (T.intersection r l : ℚ) * d)) =
          ∑ r, ((T.intersection r i : ℚ) * a + (T.intersection r j : ℚ) * b +
            (T.intersection r k : ℚ) * c + (T.intersection r l : ℚ) * d) *
              T.quadrupleVector i j k l a b c d r by
        apply Finset.sum_congr rfl
        intro r _
        ring]
      exact T.sum_mul_quadrupleVector hij hik hil hjk hjl hkl
        (fun r => (T.intersection r i : ℚ) * a + (T.intersection r j : ℚ) * b +
          (T.intersection r k : ℚ) * c + (T.intersection r l : ℚ) * d) a b c d
    _ = _ := by
      rw [T.intersection_symm j i, T.intersection_symm k i,
        T.intersection_symm k j, T.intersection_symm l i,
        T.intersection_symm l j, T.intersection_symm l k]
      ring

/-- A nonzero vector on four components has strictly negative intersection square when
there is at least one further component. -/
lemma fourVertexQuadratic_neg (T : NumericalType) {i j k l : T.Component}
    (hcard : 4 < Nat.card T.Component)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) {a b c d : ℚ}
    (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    (T.intersection i i : ℚ) * a ^ 2 +
      (T.intersection j j : ℚ) * b ^ 2 +
      (T.intersection k k : ℚ) * c ^ 2 +
      (T.intersection l l : ℚ) * d ^ 2 +
      2 * (T.intersection i j : ℚ) * a * b +
      2 * (T.intersection i k : ℚ) * a * c +
      2 * (T.intersection i l : ℚ) * a * d +
      2 * (T.intersection j k : ℚ) * b * c +
      2 * (T.intersection j l : ℚ) * b * d +
      2 * (T.intersection k l : ℚ) * c * d < 0 := by
  classical
  let s : Finset T.Component := {i, j, k, l}
  have hs : s ≠ Finset.univ := by
    intro hs
    have hc := congrArg Finset.card hs
    have hsCard : s.card ≤ 4 := by
      dsimp [s]
      have htail : ({j, k, l} : Finset T.Component).card ≤ 3 := by
        calc
          ({j, k, l} : Finset T.Component).card ≤
              ({k, l} : Finset T.Component).card + 1 := Finset.card_insert_le j {k, l}
          _ ≤ 3 := by
            have := Finset.card_insert_le k ({l} : Finset T.Component)
            simp only [Finset.card_singleton] at this
            omega
      calc
        ({i, j, k, l} : Finset T.Component).card ≤
            ({j, k, l} : Finset T.Component).card + 1 := Finset.card_insert_le i {j, k, l}
        _ ≤ 4 := by omega
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hc
    omega
  let x : {r // r ∈ s} → ℚ := fun r =>
    if r.1 = i then a else if r.1 = j then b else if r.1 = k then c else d
  have hx : x ≠ 0 := by
    intro hzero
    rcases hne with ha | hb | hc | hd
    · have hi := congrFun hzero ⟨i, by simp [s]⟩
      change (if i = i then a else if i = j then b else if i = k then c else d) = 0 at hi
      rw [if_pos rfl] at hi
      exact ha hi
    · have hj := congrFun hzero ⟨j, by simp [s]⟩
      change (if j = i then a else if j = j then b else if j = k then c else d) = 0 at hj
      rw [if_neg hij.symm, if_pos rfl] at hj
      exact hb hj
    · have hk := congrFun hzero ⟨k, by simp [s]⟩
      change (if k = i then a else if k = j then b else if k = k then c else d) = 0 at hk
      rw [if_neg hik.symm, if_neg hjk.symm, if_pos rfl] at hk
      exact hc hk
    · have hl := congrFun hzero ⟨l, by simp [s]⟩
      change (if l = i then a else if l = j then b else if l = k then c else d) = 0 at hl
      rw [if_neg hil.symm, if_neg hjl.symm, if_neg hkl.symm] at hl
      exact hd hl
  have hneg := T.subsetIntersectionQuadratic_neg s hs x hx
  have hext : T.extendByZero s x = T.quadrupleVector i j k l a b c d := by
    funext r
    by_cases hri : r = i
    · subst r
      simp [extendByZero, quadrupleVector, s, x]
    · by_cases hrj : r = j
      · subst r
        simp [extendByZero, quadrupleVector, s, x, hij.symm]
      · by_cases hrk : r = k
        · subst r
          simp [extendByZero, quadrupleVector, s, x, hik.symm, hjk.symm]
        · by_cases hrl : r = l
          · subst r
            simp [extendByZero, quadrupleVector, s, x, hil.symm, hjl.symm, hkl.symm]
          · simp [extendByZero, quadrupleVector, s, hri, hrj, hrk, hrl]
  change T.intersectionQuadratic (T.extendByZero s x) < 0 at hneg
  rw [hext, T.intersectionQuadratic_quadruple hij hik hil hjk hjl hkl] at hneg
  exact hneg

/-- Four consecutive distinct `(-2)` vertices in a proper subgraph cannot have edge-index
products `(2,1,2)`. -/
lemma no_two_one_two_path (T : NumericalType)
    (hcard : 4 < Nat.card T.Component) {i j k l : T.Component}
    (hi : T.IsMinusTwoVertex i) (hj : T.IsMinusTwoVertex j)
    (hk : T.IsMinusTwoVertex k) (hl : T.IsMinusTwoVertex l)
    (hij : T.intersectionGraph.Adj i j) (hjk : T.intersectionGraph.Adj j k)
    (hkl : T.intersectionGraph.Adj k l)
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l)
    (hp : T.edgeIndexProduct i j = 2) (hq : T.edgeIndexProduct j k = 1)
    (hr : T.edgeIndexProduct k l = 2) : False := by
  have hnotik : ¬ T.intersectionGraph.Adj i k := by
    intro hadj
    exact T.no_minusTwo_triangle (by omega) hi hj hk hij hjk hadj.symm
  have hnotjl : ¬ T.intersectionGraph.Adj j l := by
    intro hadj
    exact T.no_minusTwo_triangle (by omega) hj hk hl hjk hkl hadj.symm
  have hAik0 : T.intersection i k = 0 := by
    have hnonneg := T.offDiagonal_nonnegative i k hik
    by_contra hne
    have hpos : 0 < T.intersection i k := by omega
    exact hnotik ⟨hik, hpos⟩
  have hAjl0 : T.intersection j l = 0 := by
    have hnonneg := T.offDiagonal_nonnegative j l hjl
    by_contra hne
    have hpos : 0 < T.intersection j l := by omega
    exact hnotjl ⟨hjl, hpos⟩
  let x : ℚ := (T.normalizedIntersection i j : ℚ)
  let z : ℚ := (T.normalizedIntersection l k : ℚ)
  have hxpos : 0 < x := by
    dsimp [x]
    exact_mod_cast T.normalizedIntersection_pos_of_adj hij
  have hzpos : 0 < z := by
    dsimp [z]
    exact_mod_cast T.normalizedIntersection_pos_of_adj hkl.symm
  have hnormij : x * (T.weight i : ℚ) = (T.intersection i j : ℚ) := by
    dsimp [x]
    exact_mod_cast T.normalizedIntersection_mul_weight i j
  have hnormji : (T.normalizedIntersection j i : ℚ) * (T.weight j : ℚ) =
      (T.intersection i j : ℚ) := by
    have h := T.normalizedIntersection_mul_weight j i
    rw [T.intersection_symm j i] at h
    exact_mod_cast h
  have hpNorm : x * (T.normalizedIntersection j i : ℚ) = 2 := by
    dsimp [edgeIndexProduct, x] at hp ⊢
    exact_mod_cast hp
  have hx2 : x ^ 2 * (T.weight i : ℚ) = 2 * (T.weight j : ℚ) := by
    calc
      x ^ 2 * (T.weight i : ℚ) = x * (x * (T.weight i : ℚ)) := by ring
      _ = x * (T.intersection i j : ℚ) := by rw [hnormij]
      _ = x * ((T.normalizedIntersection j i : ℚ) * (T.weight j : ℚ)) := by
        rw [hnormji]
      _ = (x * (T.normalizedIntersection j i : ℚ)) * (T.weight j : ℚ) := by ring
      _ = 2 * (T.weight j : ℚ) := by rw [hpNorm]
  have hwjk := T.weights_eq_of_edgeIndexProduct_eq_one hjk hq
  have hwjkQ : (T.weight j : ℚ) = (T.weight k : ℚ) := by exact_mod_cast hwjk
  have hAjk := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hjk hq
  have hAjkQ : (T.intersection j k : ℚ) = (T.weight j : ℚ) := by exact_mod_cast hAjk
  have hnormlk : z * (T.weight l : ℚ) = (T.intersection k l : ℚ) := by
    have h := T.normalizedIntersection_mul_weight l k
    rw [T.intersection_symm l k] at h
    dsimp [z]
    exact_mod_cast h
  have hnormkl : (T.normalizedIntersection k l : ℚ) * (T.weight k : ℚ) =
      (T.intersection k l : ℚ) := by
    exact_mod_cast T.normalizedIntersection_mul_weight k l
  have hrNorm : z * (T.normalizedIntersection k l : ℚ) = 2 := by
    dsimp [edgeIndexProduct, z] at hr ⊢
    rw [mul_comm]
    exact_mod_cast hr
  have hz2 : z ^ 2 * (T.weight l : ℚ) = 2 * (T.weight k : ℚ) := by
    calc
      z ^ 2 * (T.weight l : ℚ) = z * (z * (T.weight l : ℚ)) := by ring
      _ = z * (T.intersection k l : ℚ) := by rw [hnormlk]
      _ = z * ((T.normalizedIntersection k l : ℚ) * (T.weight k : ℚ)) := by
        rw [hnormkl]
      _ = (z * (T.normalizedIntersection k l : ℚ)) * (T.weight k : ℚ) := by ring
      _ = 2 * (T.weight k : ℚ) := by rw [hrNorm]
  have hAil : 0 ≤ (T.intersection i l : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative i l hil
  have hcross : 0 ≤ 2 * (T.intersection i l : ℚ) * x * z := by positivity
  have hneg := T.fourVertexQuadratic_neg hcard hij.ne hik hil hjk.ne hjl hkl.ne
    (a := x) (b := 2) (c := 2) (d := z) (Or.inl (ne_of_gt hxpos))
  rw [hi.2, hj.2, hk.2, hl.2, hAik0, hAjl0] at hneg
  norm_num at hneg
  rw [← hnormij, ← hnormlk, hAjkQ] at hneg
  ring_nf at hneg hx2 hz2
  nlinarith

/-- Stacks Project's four-vertex path classification: the consecutive edge-index
products are `(1,1,1)`, `(1,1,2)`, `(1,2,1)`, or `(2,1,1)`. -/
lemma fourPath_edgeIndexProducts_classification (T : NumericalType)
    (hcard : 4 < Nat.card T.Component) {i j k l : T.Component}
    (hi : T.IsMinusTwoVertex i) (hj : T.IsMinusTwoVertex j)
    (hk : T.IsMinusTwoVertex k) (hl : T.IsMinusTwoVertex l)
    (hij : T.intersectionGraph.Adj i j) (hjk : T.intersectionGraph.Adj j k)
    (hkl : T.intersectionGraph.Adj k l)
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l) :
    (T.edgeIndexProduct i j = 1 ∧ T.edgeIndexProduct j k = 1 ∧
      T.edgeIndexProduct k l = 1) ∨
    (T.edgeIndexProduct i j = 1 ∧ T.edgeIndexProduct j k = 1 ∧
      T.edgeIndexProduct k l = 2) ∨
    (T.edgeIndexProduct i j = 1 ∧ T.edgeIndexProduct j k = 2 ∧
      T.edgeIndexProduct k l = 1) ∨
    (T.edgeIndexProduct i j = 2 ∧ T.edgeIndexProduct j k = 1 ∧
      T.edgeIndexProduct k l = 1) := by
  have hpq := T.consecutive_edgeIndexProducts_classification (by omega) hi hj hk hij hjk hik
  have hqr := T.consecutive_edgeIndexProducts_classification (by omega) hj hk hl hjk hkl hjl
  rcases hpq with hpq | hpq | hpq <;> rcases hqr with hqr | hqr | hqr
  all_goals try {simp_all}
  exfalso
  exact T.no_two_one_two_path hcard hi hj hk hl hij hjk hkl hik hil hjl
    hpq.1 hpq.2 hqr.2

/-- Five consecutive distinct `(-2)` vertices in a proper subgraph cannot have edge-index
products `(2,1,1,2)`. -/
lemma no_two_one_one_two_path (T : NumericalType)
    (hcard : 5 < Nat.card T.Component) {h i j k l : T.Component}
    (hh : T.IsMinusTwoVertex h) (hi : T.IsMinusTwoVertex i)
    (hj : T.IsMinusTwoVertex j) (hk : T.IsMinusTwoVertex k)
    (hl : T.IsMinusTwoVertex l)
    (hhi : T.intersectionGraph.Adj h i) (hij : T.intersectionGraph.Adj i j)
    (hjk : T.intersectionGraph.Adj j k) (hkl : T.intersectionGraph.Adj k l)
    (h_hj : h ≠ j) (h_hk : h ≠ k) (h_hl : h ≠ l)
    (h_ik : i ≠ k) (h_il : i ≠ l) (h_jl : j ≠ l)
    (hp : T.edgeIndexProduct h i = 2) (hq : T.edgeIndexProduct i j = 1)
    (hr : T.edgeIndexProduct j k = 1) (hs : T.edgeIndexProduct k l = 2) : False := by
  let v : Fin 5 → T.Component := ![h, i, j, k, l]
  have hv : Function.Injective v := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [v]
  have hproper : ∃ c, ∀ r, c ≠ v r := by
    by_contra hnot
    push Not at hnot
    have hsurj : Function.Surjective v := by
      intro c
      obtain ⟨r, hr⟩ := hnot c
      exact ⟨r, hr.symm⟩
    have hle := Fintype.card_le_of_surjective v hsurj
    change Fintype.card T.Component ≤ 5 at hle
    have heq : Fintype.card T.Component = Nat.card T.Component :=
      Nat.card_eq_fintype_card.symm
    rw [heq] at hle
    omega
  let x : ℚ := (T.normalizedIntersection h i : ℚ)
  let z : ℚ := (T.normalizedIntersection l k : ℚ)
  let a : Fin 5 → ℚ := ![x, 2, 2, 2, z]
  have hxpos : 0 < x := by
    dsimp [x]
    exact_mod_cast T.normalizedIntersection_pos_of_adj hhi
  have hzpos : 0 < z := by
    dsimp [z]
    exact_mod_cast T.normalizedIntersection_pos_of_adj hkl.symm
  have hnormhi : x * (T.weight h : ℚ) = (T.intersection h i : ℚ) := by
    dsimp [x]
    exact_mod_cast T.normalizedIntersection_mul_weight h i
  have hnormih : (T.normalizedIntersection i h : ℚ) * (T.weight i : ℚ) =
      (T.intersection h i : ℚ) := by
    have heq := T.normalizedIntersection_mul_weight i h
    rw [T.intersection_symm i h] at heq
    exact_mod_cast heq
  have hpNorm : x * (T.normalizedIntersection i h : ℚ) = 2 := by
    dsimp [edgeIndexProduct, x] at hp ⊢
    exact_mod_cast hp
  have hx2 : x ^ 2 * (T.weight h : ℚ) = 2 * (T.weight i : ℚ) := by
    calc
      x ^ 2 * (T.weight h : ℚ) = x * (x * (T.weight h : ℚ)) := by ring
      _ = x * (T.intersection h i : ℚ) := by rw [hnormhi]
      _ = x * ((T.normalizedIntersection i h : ℚ) * (T.weight i : ℚ)) := by
        rw [hnormih]
      _ = (x * (T.normalizedIntersection i h : ℚ)) * (T.weight i : ℚ) := by ring
      _ = 2 * (T.weight i : ℚ) := by rw [hpNorm]
  have hwij := T.weights_eq_of_edgeIndexProduct_eq_one hij hq
  have hwjk := T.weights_eq_of_edgeIndexProduct_eq_one hjk hr
  have hwijQ : (T.weight i : ℚ) = (T.weight j : ℚ) := by exact_mod_cast hwij
  have hwjkQ : (T.weight j : ℚ) = (T.weight k : ℚ) := by exact_mod_cast hwjk
  have hAij := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hij hq
  have hAjk := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hjk hr
  have hAijQ : (T.intersection i j : ℚ) = (T.weight i : ℚ) := by exact_mod_cast hAij
  have hAjkQ : (T.intersection j k : ℚ) = (T.weight j : ℚ) := by exact_mod_cast hAjk
  have hnormlk : z * (T.weight l : ℚ) = (T.intersection k l : ℚ) := by
    have heq := T.normalizedIntersection_mul_weight l k
    rw [T.intersection_symm l k] at heq
    dsimp [z]
    exact_mod_cast heq
  have hnormkl : (T.normalizedIntersection k l : ℚ) * (T.weight k : ℚ) =
      (T.intersection k l : ℚ) := by exact_mod_cast T.normalizedIntersection_mul_weight k l
  have hsNorm : z * (T.normalizedIntersection k l : ℚ) = 2 := by
    dsimp [edgeIndexProduct, z] at hs ⊢
    rw [mul_comm]
    exact_mod_cast hs
  have hz2 : z ^ 2 * (T.weight l : ℚ) = 2 * (T.weight k : ℚ) := by
    calc
      z ^ 2 * (T.weight l : ℚ) = z * (z * (T.weight l : ℚ)) := by ring
      _ = z * (T.intersection k l : ℚ) := by rw [hnormlk]
      _ = z * ((T.normalizedIntersection k l : ℚ) * (T.weight k : ℚ)) := by rw [hnormkl]
      _ = (z * (T.normalizedIntersection k l : ℚ)) * (T.weight k : ℚ) := by ring
      _ = 2 * (T.weight k : ℚ) := by rw [hsNorm]
  have hchord_hj : 0 ≤ (T.intersection h j : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative h j h_hj
  have hchord_hk : 0 ≤ (T.intersection h k : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative h k h_hk
  have hchord_hl : 0 ≤ (T.intersection h l : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative h l h_hl
  have hchord_ik : 0 ≤ (T.intersection i k : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative i k h_ik
  have hchord_il : 0 ≤ (T.intersection i l : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative i l h_il
  have hchord_jl : 0 ≤ (T.intersection j l : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative j l h_jl
  have hneg := T.intersectionQuadratic_indexedVector_neg hv hproper a
    (r := (0 : Fin 5)) (by simpa [a] using ne_of_gt hxpos)
  dsimp [v, a] at hneg
  norm_num [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    hh.2, hi.2, hj.2, hk.2, hl.2] at hneg
  rw [T.intersection_symm i h, T.intersection_symm j h, T.intersection_symm k h,
    T.intersection_symm l h, T.intersection_symm j i, T.intersection_symm k i,
    T.intersection_symm l i, T.intersection_symm k j, T.intersection_symm l j,
    T.intersection_symm l k] at hneg
  rw [← hnormhi, hAijQ, hAjkQ, ← hnormlk] at hneg
  ring_nf at hneg hx2 hz2
  have hrest : 0 ≤
      x * (T.intersection h j : ℚ) * 4 +
      x * (T.intersection h k : ℚ) * 4 +
      x * (T.intersection h l : ℚ) * z * 2 +
      z * (T.intersection i l : ℚ) * 4 +
      z * (T.intersection j l : ℚ) * 4 +
      (T.intersection i k : ℚ) * 8 := by positivity
  nlinarith

/-- Five consecutive distinct `(-2)` vertices in a proper subgraph cannot have edge-index
products `(1,2,1,1)`; reversal also excludes `(1,1,2,1)`. -/
lemma no_one_two_one_one_path (T : NumericalType)
    (hcard : 5 < Nat.card T.Component) {h i j k l : T.Component}
    (hh : T.IsMinusTwoVertex h) (hi : T.IsMinusTwoVertex i)
    (hj : T.IsMinusTwoVertex j) (hk : T.IsMinusTwoVertex k)
    (hl : T.IsMinusTwoVertex l)
    (hhi : T.intersectionGraph.Adj h i) (hij : T.intersectionGraph.Adj i j)
    (hjk : T.intersectionGraph.Adj j k) (hkl : T.intersectionGraph.Adj k l)
    (h_hj : h ≠ j) (h_hk : h ≠ k) (h_hl : h ≠ l)
    (h_ik : i ≠ k) (h_il : i ≠ l) (h_jl : j ≠ l)
    (hp : T.edgeIndexProduct h i = 1) (hq : T.edgeIndexProduct i j = 2)
    (hr : T.edgeIndexProduct j k = 1) (hs : T.edgeIndexProduct k l = 1) : False := by
  let v : Fin 5 → T.Component := ![h, i, j, k, l]
  have hv : Function.Injective v := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [v]
  have hproper : ∃ c, ∀ r, c ≠ v r := by
    by_contra hnot
    push Not at hnot
    have hsurj : Function.Surjective v := by
      intro c
      obtain ⟨r, hr⟩ := hnot c
      exact ⟨r, hr.symm⟩
    have hle := Fintype.card_le_of_surjective v hsurj
    change Fintype.card T.Component ≤ 5 at hle
    have heq : Fintype.card T.Component = Nat.card T.Component :=
      Nat.card_eq_fintype_card.symm
    rw [heq] at hle
    omega
  let x : ℚ := (T.normalizedIntersection i j : ℚ)
  let a : Fin 5 → ℚ := ![x, 2 * x, 3, 2, 1]
  have hxpos : 0 < x := by
    dsimp [x]
    exact_mod_cast T.normalizedIntersection_pos_of_adj hij
  have hwhi := T.weights_eq_of_edgeIndexProduct_eq_one hhi hp
  have hwhiQ : (T.weight h : ℚ) = (T.weight i : ℚ) := by exact_mod_cast hwhi
  have hAhi := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hhi hp
  have hAhiQ : (T.intersection h i : ℚ) = (T.weight h : ℚ) := by exact_mod_cast hAhi
  have hnormij : x * (T.weight i : ℚ) = (T.intersection i j : ℚ) := by
    dsimp [x]
    exact_mod_cast T.normalizedIntersection_mul_weight i j
  have hnormji : (T.normalizedIntersection j i : ℚ) * (T.weight j : ℚ) =
      (T.intersection i j : ℚ) := by
    have heq := T.normalizedIntersection_mul_weight j i
    rw [T.intersection_symm j i] at heq
    exact_mod_cast heq
  have hqNorm : x * (T.normalizedIntersection j i : ℚ) = 2 := by
    dsimp [edgeIndexProduct, x] at hq ⊢
    exact_mod_cast hq
  have hx2 : x ^ 2 * (T.weight i : ℚ) = 2 * (T.weight j : ℚ) := by
    calc
      x ^ 2 * (T.weight i : ℚ) = x * (x * (T.weight i : ℚ)) := by ring
      _ = x * (T.intersection i j : ℚ) := by rw [hnormij]
      _ = x * ((T.normalizedIntersection j i : ℚ) * (T.weight j : ℚ)) := by
        rw [hnormji]
      _ = (x * (T.normalizedIntersection j i : ℚ)) * (T.weight j : ℚ) := by ring
      _ = 2 * (T.weight j : ℚ) := by rw [hqNorm]
  have hwjk := T.weights_eq_of_edgeIndexProduct_eq_one hjk hr
  have hwkl := T.weights_eq_of_edgeIndexProduct_eq_one hkl hs
  have hwjkQ : (T.weight j : ℚ) = (T.weight k : ℚ) := by exact_mod_cast hwjk
  have hwklQ : (T.weight k : ℚ) = (T.weight l : ℚ) := by exact_mod_cast hwkl
  have hAjk := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hjk hr
  have hAkl := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hkl hs
  have hAjkQ : (T.intersection j k : ℚ) = (T.weight j : ℚ) := by exact_mod_cast hAjk
  have hAklQ : (T.intersection k l : ℚ) = (T.weight k : ℚ) := by exact_mod_cast hAkl
  have hchord_hj : 0 ≤ (T.intersection h j : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative h j h_hj
  have hchord_hk : 0 ≤ (T.intersection h k : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative h k h_hk
  have hchord_hl : 0 ≤ (T.intersection h l : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative h l h_hl
  have hchord_ik : 0 ≤ (T.intersection i k : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative i k h_ik
  have hchord_il : 0 ≤ (T.intersection i l : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative i l h_il
  have hchord_jl : 0 ≤ (T.intersection j l : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative j l h_jl
  have hneg := T.intersectionQuadratic_indexedVector_neg hv hproper a
    (r := (0 : Fin 5)) (by simpa [a] using ne_of_gt hxpos)
  dsimp [v, a] at hneg
  norm_num [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    hh.2, hi.2, hj.2, hk.2, hl.2] at hneg
  rw [T.intersection_symm i h, T.intersection_symm j h, T.intersection_symm k h,
    T.intersection_symm l h, T.intersection_symm j i, T.intersection_symm k i,
    T.intersection_symm l i, T.intersection_symm k j, T.intersection_symm l j,
    T.intersection_symm l k] at hneg
  rw [hAhiQ, ← hnormij, hAjkQ, hAklQ] at hneg
  ring_nf at hneg hx2
  have hrest : 0 ≤
      x * (T.intersection h j : ℚ) * 6 +
      x * (T.intersection h k : ℚ) * 4 +
      x * (T.intersection h l : ℚ) * 2 +
      x * (T.intersection i k : ℚ) * 8 +
      x * (T.intersection i l : ℚ) * 4 +
      (T.intersection j l : ℚ) * 12 := by positivity
  nlinarith

/-- Stacks Project's five-vertex path classification: every edge-index product is one,
except possibly the first or the last, which may be two. -/
lemma fivePath_edgeIndexProducts_classification (T : NumericalType)
    (hcard : 5 < Nat.card T.Component) {h i j k l : T.Component}
    (hh : T.IsMinusTwoVertex h) (hi : T.IsMinusTwoVertex i)
    (hj : T.IsMinusTwoVertex j) (hk : T.IsMinusTwoVertex k)
    (hl : T.IsMinusTwoVertex l)
    (hhi : T.intersectionGraph.Adj h i) (hij : T.intersectionGraph.Adj i j)
    (hjk : T.intersectionGraph.Adj j k) (hkl : T.intersectionGraph.Adj k l)
    (h_hj : h ≠ j) (h_hk : h ≠ k) (h_hl : h ≠ l)
    (h_ik : i ≠ k) (h_il : i ≠ l) (h_jl : j ≠ l) :
    (T.edgeIndexProduct h i = 1 ∧ T.edgeIndexProduct i j = 1 ∧
      T.edgeIndexProduct j k = 1 ∧ T.edgeIndexProduct k l = 1) ∨
    (T.edgeIndexProduct h i = 2 ∧ T.edgeIndexProduct i j = 1 ∧
      T.edgeIndexProduct j k = 1 ∧ T.edgeIndexProduct k l = 1) ∨
    (T.edgeIndexProduct h i = 1 ∧ T.edgeIndexProduct i j = 1 ∧
      T.edgeIndexProduct j k = 1 ∧ T.edgeIndexProduct k l = 2) := by
  have hfirst := T.fourPath_edgeIndexProducts_classification (by omega)
    hh hi hj hk hhi hij hjk h_hj h_hk h_ik
  have hlast := T.fourPath_edgeIndexProducts_classification (by omega)
    hi hj hk hl hij hjk hkl h_ik h_il h_jl
  have hcases :
      ((T.edgeIndexProduct h i = 1 ∧ T.edgeIndexProduct i j = 1 ∧
          T.edgeIndexProduct j k = 1 ∧ T.edgeIndexProduct k l = 1) ∨
        (T.edgeIndexProduct h i = 2 ∧ T.edgeIndexProduct i j = 1 ∧
          T.edgeIndexProduct j k = 1 ∧ T.edgeIndexProduct k l = 1) ∨
        (T.edgeIndexProduct h i = 1 ∧ T.edgeIndexProduct i j = 1 ∧
          T.edgeIndexProduct j k = 1 ∧ T.edgeIndexProduct k l = 2)) ∨
      (T.edgeIndexProduct h i = 2 ∧ T.edgeIndexProduct i j = 1 ∧
        T.edgeIndexProduct j k = 1 ∧ T.edgeIndexProduct k l = 2) ∨
      (T.edgeIndexProduct h i = 1 ∧ T.edgeIndexProduct i j = 2 ∧
        T.edgeIndexProduct j k = 1 ∧ T.edgeIndexProduct k l = 1) ∨
      (T.edgeIndexProduct h i = 1 ∧ T.edgeIndexProduct i j = 1 ∧
        T.edgeIndexProduct j k = 2 ∧ T.edgeIndexProduct k l = 1) := by
    rcases hfirst with hfirst | hfirst | hfirst | hfirst <;>
      rcases hlast with hlast | hlast | hlast | hlast <;> simp_all
  rcases hcases with hgood | hbad | hbad | hbad
  · exact hgood
  · exact (T.no_two_one_one_two_path hcard hh hi hj hk hl hhi hij hjk hkl
      h_hj h_hk h_hl h_ik h_il h_jl hbad.1 hbad.2.1 hbad.2.2.1 hbad.2.2.2).elim
  · exact (T.no_one_two_one_one_path hcard hh hi hj hk hl hhi hij hjk hkl
      h_hj h_hk h_hl h_ik h_il h_jl hbad.1 hbad.2.1 hbad.2.2.1 hbad.2.2.2).elim
  · have hfalse := T.no_one_two_one_one_path hcard hl hk hj hi hh hkl.symm
      hjk.symm hij.symm hhi.symm h_jl.symm h_il.symm h_hl.symm h_ik.symm h_hk.symm
      h_hj.symm (by simpa using hbad.2.2.2) (by simpa using hbad.2.2.1)
      (by simpa using hbad.2.1) (by simpa using hbad.1)
    exact hfalse.elim



/-- Squaring a directed normalized index transfers its source weight by the undirected
edge-index product. -/
lemma normalizedIntersection_sq_mul_weight (T : NumericalType) (i j : T.Component) :
    (T.normalizedIntersection i j : ℚ) ^ 2 * (T.weight i : ℚ) =
      (T.edgeIndexProduct i j : ℚ) * (T.weight j : ℚ) := by
  have hi : (T.normalizedIntersection i j : ℚ) * (T.weight i : ℚ) =
      (T.intersection i j : ℚ) := by exact_mod_cast T.normalizedIntersection_mul_weight i j
  have hj : (T.normalizedIntersection j i : ℚ) * (T.weight j : ℚ) =
      (T.intersection i j : ℚ) := by
    have h := T.normalizedIntersection_mul_weight j i
    rw [T.intersection_symm j i] at h
    exact_mod_cast h
  calc
    (T.normalizedIntersection i j : ℚ) ^ 2 * (T.weight i : ℚ) =
        (T.normalizedIntersection i j : ℚ) *
          ((T.normalizedIntersection i j : ℚ) * (T.weight i : ℚ)) := by ring
    _ = (T.normalizedIntersection i j : ℚ) * (T.intersection i j : ℚ) := by rw [hi]
    _ = (T.normalizedIntersection i j : ℚ) *
        ((T.normalizedIntersection j i : ℚ) * (T.weight j : ℚ)) := by rw [hj]
    _ = (T.edgeIndexProduct i j : ℚ) * (T.weight j : ℚ) := by
      dsimp [edgeIndexProduct]
      push_cast
      ring

/-- Three distinct `(-2)` arms at a `(-2)` center cannot have edge-index products
summing to four in a proper subgraph. -/
lemma no_three_minusTwo_neighbors_edgeIndexProduct_sum_four (T : NumericalType)
    (hcard : 4 < Nat.card T.Component) {c i j k : T.Component}
    (hc : T.IsMinusTwoVertex c) (hi : T.IsMinusTwoVertex i)
    (hj : T.IsMinusTwoVertex j) (hk : T.IsMinusTwoVertex k)
    (hci : T.intersectionGraph.Adj c i) (hcj : T.intersectionGraph.Adj c j)
    (hck : T.intersectionGraph.Adj c k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hsum : T.edgeIndexProduct c i + T.edgeIndexProduct c j +
      T.edgeIndexProduct c k = 4) : False := by
  have hnotij : ¬ T.intersectionGraph.Adj i j := by
    intro hadj
    exact T.no_minusTwo_triangle (by omega) hi hc hj hci.symm hcj hadj.symm
  have hnotik : ¬ T.intersectionGraph.Adj i k := by
    intro hadj
    exact T.no_minusTwo_triangle (by omega) hi hc hk hci.symm hck hadj.symm
  have hnotjk : ¬ T.intersectionGraph.Adj j k := by
    intro hadj
    exact T.no_minusTwo_triangle (by omega) hj hc hk hcj.symm hck hadj.symm
  have hAij : T.intersection i j = 0 := by
    have hnonneg := T.offDiagonal_nonnegative i j hij
    by_contra hne
    exact hnotij ⟨hij, by omega⟩
  have hAik : T.intersection i k = 0 := by
    have hnonneg := T.offDiagonal_nonnegative i k hik
    by_contra hne
    exact hnotik ⟨hik, by omega⟩
  have hAjk : T.intersection j k = 0 := by
    have hnonneg := T.offDiagonal_nonnegative j k hjk
    by_contra hne
    exact hnotjk ⟨hjk, by omega⟩
  let x : ℚ := (T.normalizedIntersection i c : ℚ)
  let y : ℚ := (T.normalizedIntersection j c : ℚ)
  let z : ℚ := (T.normalizedIntersection k c : ℚ)
  have hx : 0 < x := by dsimp [x]; exact_mod_cast T.normalizedIntersection_pos_of_adj hci.symm
  have hy : 0 < y := by dsimp [y]; exact_mod_cast T.normalizedIntersection_pos_of_adj hcj.symm
  have hz : 0 < z := by dsimp [z]; exact_mod_cast T.normalizedIntersection_pos_of_adj hck.symm
  have hxi := T.normalizedIntersection_sq_mul_weight i c
  have hyj := T.normalizedIntersection_sq_mul_weight j c
  have hzk := T.normalizedIntersection_sq_mul_weight k c
  have hsumQ : (T.edgeIndexProduct i c : ℚ) + (T.edgeIndexProduct j c : ℚ) +
      (T.edgeIndexProduct k c : ℚ) = 4 := by
    rw [← T.edgeIndexProduct_symm c i, ← T.edgeIndexProduct_symm c j,
      ← T.edgeIndexProduct_symm c k]
    exact_mod_cast hsum
  have hnormic : x * (T.weight i : ℚ) = (T.intersection c i : ℚ) := by
    have h := T.normalizedIntersection_mul_weight i c
    rw [T.intersection_symm i c] at h
    dsimp [x]
    exact_mod_cast h
  have hnormjc : y * (T.weight j : ℚ) = (T.intersection c j : ℚ) := by
    have h := T.normalizedIntersection_mul_weight j c
    rw [T.intersection_symm j c] at h
    dsimp [y]
    exact_mod_cast h
  have hnormkc : z * (T.weight k : ℚ) = (T.intersection c k : ℚ) := by
    have h := T.normalizedIntersection_mul_weight k c
    rw [T.intersection_symm k c] at h
    dsimp [z]
    exact_mod_cast h
  have hneg := T.fourVertexQuadratic_neg hcard hci.ne hcj.ne hck.ne
    hij hik hjk (a := 2) (b := x) (c := y) (d := z)
    (Or.inl (by norm_num))
  rw [hc.2, hi.2, hj.2, hk.2, hAij, hAik, hAjk] at hneg
  norm_num at hneg
  rw [← hnormic, ← hnormjc, ← hnormkc] at hneg
  ring_nf at hneg hxi hyj hzk
  nlinarith

/-- Stacks Project's weighted `D₄` local classification: all three arms at a `(-2)`
branch vertex have edge-index product one. -/
lemma three_minusTwo_neighbors_edgeIndexProducts_eq_one (T : NumericalType)
    (hcard : 4 < Nat.card T.Component) {c i j k : T.Component}
    (hc : T.IsMinusTwoVertex c) (hi : T.IsMinusTwoVertex i)
    (hj : T.IsMinusTwoVertex j) (hk : T.IsMinusTwoVertex k)
    (hci : T.intersectionGraph.Adj c i) (hcj : T.intersectionGraph.Adj c j)
    (hck : T.intersectionGraph.Adj c k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    T.edgeIndexProduct c i = 1 ∧ T.edgeIndexProduct c j = 1 ∧
      T.edgeIndexProduct c k = 1 := by
  have hpq := T.consecutive_edgeIndexProducts_classification (by omega) hi hc hj
    hci.symm hcj hij
  have hqr := T.consecutive_edgeIndexProducts_classification (by omega) hj hc hk
    hcj.symm hck hjk
  have hpr := T.consecutive_edgeIndexProducts_classification (by omega) hi hc hk
    hci.symm hck hik
  have hp : 0 < T.edgeIndexProduct c i := by
    dsimp [edgeIndexProduct]
    have h1 := T.normalizedIntersection_pos_of_adj hci
    have h2 := T.normalizedIntersection_pos_of_adj hci.symm
    positivity
  have hq : 0 < T.edgeIndexProduct c j := by
    dsimp [edgeIndexProduct]
    have h1 := T.normalizedIntersection_pos_of_adj hcj
    have h2 := T.normalizedIntersection_pos_of_adj hcj.symm
    positivity
  have hr : 0 < T.edgeIndexProduct c k := by
    dsimp [edgeIndexProduct]
    have h1 := T.normalizedIntersection_pos_of_adj hck
    have h2 := T.normalizedIntersection_pos_of_adj hck.symm
    positivity
  have hle : T.edgeIndexProduct c i + T.edgeIndexProduct c j +
      T.edgeIndexProduct c k ≤ 4 := by
    rcases hpq with hpq | hpq | hpq <;> rcases hqr with hqr | hqr | hqr <;>
      rcases hpr with hpr | hpr | hpr <;> simp_all
  have hne : T.edgeIndexProduct c i + T.edgeIndexProduct c j +
      T.edgeIndexProduct c k ≠ 4 := by
    intro hsum
    exact T.no_three_minusTwo_neighbors_edgeIndexProduct_sum_four hcard hc hi hj hk
      hci hcj hck hij hik hjk hsum
  omega

/-- Distinct `(-2)` neighbors of the same `(-2)` center do not meet each other. -/
lemma intersection_eq_zero_between_minusTwo_neighbors (T : NumericalType)
    (hcard : 3 < Nat.card T.Component) {c i j : T.Component}
    (hc : T.IsMinusTwoVertex c) (hi : T.IsMinusTwoVertex i)
    (hj : T.IsMinusTwoVertex j) (hci : T.intersectionGraph.Adj c i)
    (hcj : T.intersectionGraph.Adj c j) (hij : i ≠ j) :
    T.intersection i j = 0 := by
  have hnot : ¬ T.intersectionGraph.Adj i j := by
    intro hadj
    exact T.no_minusTwo_triangle hcard hi hc hj hci.symm hcj hadj.symm
  have hnonneg := T.offDiagonal_nonnegative i j hij
  by_contra hne
  exact hnot ⟨hij, by omega⟩

/-- A proper connected `(-2)` subgraph has no vertex with four distinct `(-2)`
neighbors. -/
lemma no_four_minusTwo_neighbors (T : NumericalType)
    (hcard : 5 < Nat.card T.Component) {c i j k l : T.Component}
    (hc : T.IsMinusTwoVertex c) (hi : T.IsMinusTwoVertex i)
    (hj : T.IsMinusTwoVertex j) (hk : T.IsMinusTwoVertex k)
    (hl : T.IsMinusTwoVertex l)
    (hci : T.intersectionGraph.Adj c i) (hcj : T.intersectionGraph.Adj c j)
    (hck : T.intersectionGraph.Adj c k) (hcl : T.intersectionGraph.Adj c l)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : False := by
  have hprod := T.three_minusTwo_neighbors_edgeIndexProducts_eq_one (by omega)
    hc hi hj hk hci hcj hck hij hik hjk
  have hprod' := T.three_minusTwo_neighbors_edgeIndexProducts_eq_one (by omega)
    hc hi hj hl hci hcj hcl hij hil hjl
  have hAij := T.intersection_eq_zero_between_minusTwo_neighbors (by omega)
    hc hi hj hci hcj hij
  have hAik := T.intersection_eq_zero_between_minusTwo_neighbors (by omega)
    hc hi hk hci hck hik
  have hAil := T.intersection_eq_zero_between_minusTwo_neighbors (by omega)
    hc hi hl hci hcl hil
  have hAjk := T.intersection_eq_zero_between_minusTwo_neighbors (by omega)
    hc hj hk hcj hck hjk
  have hAjl := T.intersection_eq_zero_between_minusTwo_neighbors (by omega)
    hc hj hl hcj hcl hjl
  have hAkl := T.intersection_eq_zero_between_minusTwo_neighbors (by omega)
    hc hk hl hck hcl hkl
  have hwci := T.weights_eq_of_edgeIndexProduct_eq_one hci hprod.1
  have hwcj := T.weights_eq_of_edgeIndexProduct_eq_one hcj hprod.2.1
  have hwck := T.weights_eq_of_edgeIndexProduct_eq_one hck hprod.2.2
  have hwcl := T.weights_eq_of_edgeIndexProduct_eq_one hcl hprod'.2.2
  have hAci := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hci hprod.1
  have hAcj := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hcj hprod.2.1
  have hAck := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hck hprod.2.2
  have hAcl := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hcl hprod'.2.2
  let v : Fin 5 → T.Component := ![c, i, j, k, l]
  have hv : Function.Injective v := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [v]
  have hproper : ∃ x, ∀ r, x ≠ v r := by
    by_contra hnot
    push Not at hnot
    have hsurj : Function.Surjective v := by
      intro x
      obtain ⟨r, hr⟩ := hnot x
      exact ⟨r, hr.symm⟩
    have hle := Fintype.card_le_of_surjective v hsurj
    change Fintype.card T.Component ≤ 5 at hle
    have heq : Fintype.card T.Component = Nat.card T.Component :=
      Nat.card_eq_fintype_card.symm
    rw [heq] at hle
    omega
  let a : Fin 5 → ℚ := ![2, 1, 1, 1, 1]
  have hneg := T.intersectionQuadratic_indexedVector_neg hv hproper a
    (r := (0 : Fin 5)) (by norm_num [a])
  dsimp [v, a] at hneg
  norm_num [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    hc.2, hi.2, hj.2, hk.2, hl.2] at hneg
  rw [T.intersection_symm i c, T.intersection_symm j c, T.intersection_symm k c,
    T.intersection_symm l c, T.intersection_symm j i, T.intersection_symm k i,
    T.intersection_symm l i, T.intersection_symm k j, T.intersection_symm l j,
    T.intersection_symm l k, hAij, hAik, hAil, hAjk, hAjl, hAkl,
    hAci, hAcj, hAck, hAcl] at hneg
  norm_num at hneg
  have hwciQ : (T.weight c : ℚ) = (T.weight i : ℚ) := by exact_mod_cast hwci
  have hwcjQ : (T.weight c : ℚ) = (T.weight j : ℚ) := by exact_mod_cast hwcj
  have hwckQ : (T.weight c : ℚ) = (T.weight k : ℚ) := by exact_mod_cast hwck
  have hwclQ : (T.weight c : ℚ) = (T.weight l : ℚ) := by exact_mod_cast hwcl
  nlinarith


/-- Extending one arm of a proper weighted `D₄` fork cannot introduce an edge-index
product of two. -/
lemma no_extended_D4_edgeIndexProduct_two (T : NumericalType)
    (hcard : 5 < Nat.card T.Component) {h i c j k : T.Component}
    (hh : T.IsMinusTwoVertex h) (hi : T.IsMinusTwoVertex i)
    (hc : T.IsMinusTwoVertex c) (hj : T.IsMinusTwoVertex j)
    (hk : T.IsMinusTwoVertex k)
    (hhi : T.intersectionGraph.Adj h i) (hic : T.intersectionGraph.Adj i c)
    (hcj : T.intersectionGraph.Adj c j) (hck : T.intersectionGraph.Adj c k)
    (h_hc : h ≠ c) (h_hj : h ≠ j) (h_hk : h ≠ k)
    (h_ij : i ≠ j) (h_ik : i ≠ k) (h_jk : j ≠ k)
    (hp : T.edgeIndexProduct h i = 2) : False := by
  have harms := T.three_minusTwo_neighbors_edgeIndexProducts_eq_one (by omega)
    hc hi hj hk hic.symm hcj hck h_ij h_ik h_jk
  let x : ℚ := (T.normalizedIntersection h i : ℚ)
  have hxpos : 0 < x := by
    dsimp [x]
    exact_mod_cast T.normalizedIntersection_pos_of_adj hhi
  have hx2 := T.normalizedIntersection_sq_mul_weight h i
  have hpQ : (T.edgeIndexProduct h i : ℚ) = 2 := by exact_mod_cast hp
  rw [hpQ] at hx2
  have hnormhi : x * (T.weight h : ℚ) = (T.intersection h i : ℚ) := by
    dsimp [x]
    exact_mod_cast T.normalizedIntersection_mul_weight h i
  have hwic := T.weights_eq_of_edgeIndexProduct_eq_one hic.symm harms.1
  have hwcj := T.weights_eq_of_edgeIndexProduct_eq_one hcj harms.2.1
  have hwck := T.weights_eq_of_edgeIndexProduct_eq_one hck harms.2.2
  have hAic := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hic.symm harms.1
  have hAcj := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hcj harms.2.1
  have hAck := T.intersection_eq_weight_of_edgeIndexProduct_eq_one hck harms.2.2
  have hwicQ : (T.weight i : ℚ) = (T.weight c : ℚ) := by exact_mod_cast hwic.symm
  have hwcjQ : (T.weight c : ℚ) = (T.weight j : ℚ) := by exact_mod_cast hwcj
  have hwckQ : (T.weight c : ℚ) = (T.weight k : ℚ) := by exact_mod_cast hwck
  have hAicQ : (T.intersection i c : ℚ) = (T.weight c : ℚ) := by
    rw [T.intersection_symm i c]
    exact_mod_cast hAic
  have hAcjQ : (T.intersection c j : ℚ) = (T.weight c : ℚ) := by exact_mod_cast hAcj
  have hAckQ : (T.intersection c k : ℚ) = (T.weight c : ℚ) := by exact_mod_cast hAck
  have hchord_hc : 0 ≤ (T.intersection h c : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative h c h_hc
  have hchord_hj : 0 ≤ (T.intersection h j : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative h j h_hj
  have hchord_hk : 0 ≤ (T.intersection h k : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative h k h_hk
  have hchord_ij : 0 ≤ (T.intersection i j : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative i j h_ij
  have hchord_ik : 0 ≤ (T.intersection i k : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative i k h_ik
  have hchord_jk : 0 ≤ (T.intersection j k : ℚ) := by
    exact_mod_cast T.offDiagonal_nonnegative j k h_jk
  let v : Fin 5 → T.Component := ![h, i, c, j, k]
  have hv : Function.Injective v := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [v]
  have hproper : ∃ y, ∀ r, y ≠ v r := by
    by_contra hnot
    push Not at hnot
    have hsurj : Function.Surjective v := by
      intro y
      obtain ⟨r, hr⟩ := hnot y
      exact ⟨r, hr.symm⟩
    have hle := Fintype.card_le_of_surjective v hsurj
    change Fintype.card T.Component ≤ 5 at hle
    have heq : Fintype.card T.Component = Nat.card T.Component :=
      Nat.card_eq_fintype_card.symm
    rw [heq] at hle
    omega
  let a : Fin 5 → ℚ := ![x, 2, 2, 1, 1]
  have hneg := T.intersectionQuadratic_indexedVector_neg hv hproper a
    (r := (0 : Fin 5)) (by simpa [a] using ne_of_gt hxpos)
  dsimp [v, a] at hneg
  norm_num [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    hh.2, hi.2, hc.2, hj.2, hk.2] at hneg
  rw [T.intersection_symm i h, T.intersection_symm c h, T.intersection_symm j h,
    T.intersection_symm k h, T.intersection_symm c i, T.intersection_symm j i,
    T.intersection_symm k i, T.intersection_symm j c, T.intersection_symm k c,
    T.intersection_symm k j] at hneg
  rw [← hnormhi, hAicQ, hAcjQ, hAckQ] at hneg
  ring_nf at hneg hx2
  have hrest : 0 ≤
      x * (T.intersection h c : ℚ) * 4 +
      x * (T.intersection h j : ℚ) * 2 +
      x * (T.intersection h k : ℚ) * 2 +
      (T.intersection i j : ℚ) * 4 +
      (T.intersection i k : ℚ) * 4 +
      (T.intersection j k : ℚ) * 2 := by positivity
  nlinarith

/-- Stacks Project's weighted `D₅` local classification: an edge extending one arm of a
proper `D₄` fork has index product one. -/
lemma extended_D4_edgeIndexProduct_eq_one (T : NumericalType)
    (hcard : 5 < Nat.card T.Component) {h i c j k : T.Component}
    (hh : T.IsMinusTwoVertex h) (hi : T.IsMinusTwoVertex i)
    (hc : T.IsMinusTwoVertex c) (hj : T.IsMinusTwoVertex j)
    (hk : T.IsMinusTwoVertex k)
    (hhi : T.intersectionGraph.Adj h i) (hic : T.intersectionGraph.Adj i c)
    (hcj : T.intersectionGraph.Adj c j) (hck : T.intersectionGraph.Adj c k)
    (h_hc : h ≠ c) (h_hj : h ≠ j) (h_hk : h ≠ k)
    (h_ij : i ≠ j) (h_ik : i ≠ k) (h_jk : j ≠ k) :
    T.edgeIndexProduct h i = 1 := by
  have hclass := T.fourPath_edgeIndexProducts_classification (by omega)
    hh hi hc hj hhi hic hcj h_hc h_hj h_ij
  rcases hclass with hclass | hclass | hclass | hclass
  · exact hclass.1
  · exact hclass.1
  · exact hclass.1
  · exact (T.no_extended_D4_edgeIndexProduct_two hcard hh hi hc hj hk
      hhi hic hcj hck h_hc h_hj h_hk h_ij h_ik h_jk hclass.1).elim

/-- A proper `(-2)` cluster cannot contain the affine `E₆` tree with three arms of
length two. -/
lemma no_affine_E6_subgraph (T : NumericalType)
    (hcard : 7 < Nat.card T.Component)
    (v : Fin 7 → T.Component) (hv : Function.Injective v)
    (hminus : ∀ r, T.IsMinusTwoVertex (v r))
    (h01 : T.intersectionGraph.Adj (v 0) (v 1))
    (h12 : T.intersectionGraph.Adj (v 1) (v 2))
    (h03 : T.intersectionGraph.Adj (v 0) (v 3))
    (h34 : T.intersectionGraph.Adj (v 3) (v 4))
    (h05 : T.intersectionGraph.Adj (v 0) (v 5))
    (h56 : T.intersectionGraph.Adj (v 5) (v 6)) : False := by
  have hne (i j : Fin 7) (hij : i ≠ j) : v i ≠ v j := hv.ne hij
  have hD4 := T.three_minusTwo_neighbors_edgeIndexProducts_eq_one (by omega)
    (hminus 0) (hminus 1) (hminus 3) (hminus 5) h01 h03 h05
    (hne 1 3 (by decide)) (hne 1 5 (by decide)) (hne 3 5 (by decide))
  have h12prod := T.extended_D4_edgeIndexProduct_eq_one (by omega)
    (hminus 2) (hminus 1) (hminus 0) (hminus 3) (hminus 5)
    h12.symm h01.symm h03 h05
    (hne 2 0 (by decide)) (hne 2 3 (by decide)) (hne 2 5 (by decide))
    (hne 1 3 (by decide)) (hne 1 5 (by decide)) (hne 3 5 (by decide))
  have h34prod := T.extended_D4_edgeIndexProduct_eq_one (by omega)
    (hminus 4) (hminus 3) (hminus 0) (hminus 1) (hminus 5)
    h34.symm h03.symm h01 h05
    (hne 4 0 (by decide)) (hne 4 1 (by decide)) (hne 4 5 (by decide))
    (hne 3 1 (by decide)) (hne 3 5 (by decide)) (hne 1 5 (by decide))
  have h56prod := T.extended_D4_edgeIndexProduct_eq_one (by omega)
    (hminus 6) (hminus 5) (hminus 0) (hminus 1) (hminus 3)
    h56.symm h05.symm h01 h03
    (hne 6 0 (by decide)) (hne 6 1 (by decide)) (hne 6 3 (by decide))
    (hne 5 1 (by decide)) (hne 5 3 (by decide)) (hne 1 3 (by decide))
  have hw01 := T.weights_eq_of_edgeIndexProduct_eq_one h01 hD4.1
  have hw03 := T.weights_eq_of_edgeIndexProduct_eq_one h03 hD4.2.1
  have hw05 := T.weights_eq_of_edgeIndexProduct_eq_one h05 hD4.2.2
  have hw21 := T.weights_eq_of_edgeIndexProduct_eq_one h12.symm h12prod
  have hw43 := T.weights_eq_of_edgeIndexProduct_eq_one h34.symm h34prod
  have hw65 := T.weights_eq_of_edgeIndexProduct_eq_one h56.symm h56prod
  have hA01 := T.intersection_eq_weight_of_edgeIndexProduct_eq_one h01 hD4.1
  have hA03 := T.intersection_eq_weight_of_edgeIndexProduct_eq_one h03 hD4.2.1
  have hA05 := T.intersection_eq_weight_of_edgeIndexProduct_eq_one h05 hD4.2.2
  have hA21 := T.intersection_eq_weight_of_edgeIndexProduct_eq_one h12.symm h12prod
  have hA43 := T.intersection_eq_weight_of_edgeIndexProduct_eq_one h34.symm h34prod
  have hA65 := T.intersection_eq_weight_of_edgeIndexProduct_eq_one h56.symm h56prod
  let w : Fin 7 → T.Component :=
    ![v 0, v 1, v 2, v 3, v 4, v 5, v 6]
  have hw : w = v := by
    funext r
    fin_cases r <;> rfl
  have hwinj : Function.Injective w := by
    rw [hw]
    exact hv
  have hproper : ∃ x, ∀ r, x ≠ w r := by
    by_contra hnot
    push Not at hnot
    have hsurj : Function.Surjective w := by
      intro x
      obtain ⟨r, hr⟩ := hnot x
      exact ⟨r, hr.symm⟩
    have hle := Fintype.card_le_of_surjective w hsurj
    change Fintype.card T.Component ≤ 7 at hle
    rw [← Nat.card_eq_fintype_card] at hle
    omega
  let a : Fin 7 → ℚ := ![3, 2, 1, 2, 1, 2, 1]
  have hneg := T.intersectionQuadratic_indexedVector_neg hwinj hproper a
    (r := (0 : Fin 7)) (by norm_num [a])
  dsimp [w, a] at hneg
  norm_num [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    (hminus 0).2, (hminus 1).2, (hminus 2).2, (hminus 3).2,
    (hminus 4).2, (hminus 5).2, (hminus 6).2] at hneg
  have hA12 : T.intersection (v 1) (v 2) = T.weight (v 2) := by
    calc
      T.intersection (v 1) (v 2) = T.intersection (v 2) (v 1) :=
        T.intersection_symm _ _
      _ = T.weight (v 2) := hA21
  have hA34 : T.intersection (v 3) (v 4) = T.weight (v 4) := by
    calc
      T.intersection (v 3) (v 4) = T.intersection (v 4) (v 3) :=
        T.intersection_symm _ _
      _ = T.weight (v 4) := hA43
  have hA56 : T.intersection (v 5) (v 6) = T.weight (v 6) := by
    calc
      T.intersection (v 5) (v 6) = T.intersection (v 6) (v 5) :=
        T.intersection_symm _ _
      _ = T.weight (v 6) := hA65
  rw [hA01, hA12, hA03, hA34, hA05, hA56] at hneg
  have hA10 : T.intersection (v 1) (v 0) = T.weight (v 0) := by
    calc
      T.intersection (v 1) (v 0) = T.intersection (v 0) (v 1) :=
        T.intersection_symm _ _
      _ = T.weight (v 0) := hA01
  have hA30 : T.intersection (v 3) (v 0) = T.weight (v 0) := by
    calc
      T.intersection (v 3) (v 0) = T.intersection (v 0) (v 3) :=
        T.intersection_symm _ _
      _ = T.weight (v 0) := hA03
  have hA50 : T.intersection (v 5) (v 0) = T.weight (v 0) := by
    calc
      T.intersection (v 5) (v 0) = T.intersection (v 0) (v 5) :=
        T.intersection_symm _ _
      _ = T.weight (v 0) := hA05
  rw [hA10, hA21, hA30, hA43, hA50, hA65] at hneg
  have hw2 : ((T.weight (v 2) : ℤ) : ℚ) = ((T.weight (v 0) : ℤ) : ℚ) := by
    exact_mod_cast hw21.trans hw01.symm
  have hw4 : ((T.weight (v 4) : ℤ) : ℚ) = ((T.weight (v 0) : ℤ) : ℚ) := by
    exact_mod_cast hw43.trans hw03.symm
  have hw6 : ((T.weight (v 6) : ℤ) : ℚ) = ((T.weight (v 0) : ℤ) : ℚ) := by
    exact_mod_cast hw65.trans hw05.symm
  rw [hw2, hw4, hw6] at hneg
  have hw1' : (T.weight (v 1) : ℚ) = T.weight (v 0) := by
    exact_mod_cast hw01.symm
  have hw2' : (T.weight (v 2) : ℚ) = T.weight (v 0) := by
    exact_mod_cast hw21.trans hw01.symm
  have hw3' : (T.weight (v 3) : ℚ) = T.weight (v 0) := by
    exact_mod_cast hw03.symm
  have hw4' : (T.weight (v 4) : ℚ) = T.weight (v 0) := by
    exact_mod_cast hw43.trans hw03.symm
  have hw5' : (T.weight (v 5) : ℚ) = T.weight (v 0) := by
    exact_mod_cast hw05.symm
  have hw6' : (T.weight (v 6) : ℚ) = T.weight (v 0) := by
    exact_mod_cast hw65.trans hw05.symm
  rw [hw1', hw2', hw3', hw4', hw5', hw6'] at hneg
  have hcast : ((T.weight (v 0) : ℤ) : ℚ) = (T.weight (v 0) : ℚ) := by
    norm_num
  rw [hcast] at hneg
  ring_nf at hneg
  have hoff (i j : Fin 7) (hij : i ≠ j) :
      (0 : ℚ) ≤ T.intersection (v i) (v j) := by
    exact_mod_cast T.offDiagonal_nonnegative (v i) (v j) (hne i j hij)
  have h02 := hoff 0 2 (by decide)
  have h04 := hoff 0 4 (by decide)
  have h06 := hoff 0 6 (by decide)
  have h13 := hoff 1 3 (by decide)
  have h14 := hoff 1 4 (by decide)
  have h15 := hoff 1 5 (by decide)
  have h16 := hoff 1 6 (by decide)
  have h23 := hoff 2 3 (by decide)
  have h24 := hoff 2 4 (by decide)
  have h25 := hoff 2 5 (by decide)
  have h26 := hoff 2 6 (by decide)
  have h35 := hoff 3 5 (by decide)
  have h36 := hoff 3 6 (by decide)
  have h45 := hoff 4 5 (by decide)
  have h46 := hoff 4 6 (by decide)
  have h20 := hoff 2 0 (by decide)
  have h40 := hoff 4 0 (by decide)
  have h60 := hoff 6 0 (by decide)
  have h31 := hoff 3 1 (by decide)
  have h41 := hoff 4 1 (by decide)
  have h51 := hoff 5 1 (by decide)
  have h61 := hoff 6 1 (by decide)
  have h32 := hoff 3 2 (by decide)
  have h42 := hoff 4 2 (by decide)
  have h52 := hoff 5 2 (by decide)
  have h62 := hoff 6 2 (by decide)
  have h53 := hoff 5 3 (by decide)
  have h63 := hoff 6 3 (by decide)
  have h54 := hoff 5 4 (by decide)
  have h64 := hoff 6 4 (by decide)
  have hrest : 0 ≤
      3 * (T.intersection (v 0) (v 2) : ℚ) +
      3 * (T.intersection (v 0) (v 4) : ℚ) +
      3 * (T.intersection (v 0) (v 6) : ℚ) +
      4 * (T.intersection (v 1) (v 3) : ℚ) +
      2 * (T.intersection (v 1) (v 4) : ℚ) +
      4 * (T.intersection (v 1) (v 5) : ℚ) +
      2 * (T.intersection (v 1) (v 6) : ℚ) +
      2 * (T.intersection (v 2) (v 3) : ℚ) +
      (T.intersection (v 2) (v 4) : ℚ) +
      2 * (T.intersection (v 2) (v 5) : ℚ) +
      (T.intersection (v 2) (v 6) : ℚ) +
      4 * (T.intersection (v 3) (v 5) : ℚ) +
      2 * (T.intersection (v 3) (v 6) : ℚ) +
      2 * (T.intersection (v 4) (v 5) : ℚ) +
      (T.intersection (v 4) (v 6) : ℚ) := by
    positivity
  have hrest' : 0 ≤
      3 * (T.intersection (v 2) (v 0) : ℚ) +
      3 * (T.intersection (v 4) (v 0) : ℚ) +
      3 * (T.intersection (v 6) (v 0) : ℚ) +
      4 * (T.intersection (v 3) (v 1) : ℚ) +
      2 * (T.intersection (v 4) (v 1) : ℚ) +
      4 * (T.intersection (v 5) (v 1) : ℚ) +
      2 * (T.intersection (v 6) (v 1) : ℚ) +
      2 * (T.intersection (v 3) (v 2) : ℚ) +
      (T.intersection (v 4) (v 2) : ℚ) +
      2 * (T.intersection (v 5) (v 2) : ℚ) +
      (T.intersection (v 6) (v 2) : ℚ) +
      4 * (T.intersection (v 5) (v 3) : ℚ) +
      2 * (T.intersection (v 6) (v 3) : ℚ) +
      2 * (T.intersection (v 5) (v 4) : ℚ) +
      (T.intersection (v 6) (v 4) : ℚ) := by
    positivity
  linarith


/-- An injective finite path all of whose vertices are `(-2)` components. -/
structure SimpleMinusTwoPath (T : NumericalType) where
  length : ℕ
  vertex : Fin (length + 1) → T.Component
  injective : Function.Injective vertex
  adjacent : ∀ r : Fin length,
    T.intersectionGraph.Adj (vertex r.castSucc) (vertex r.succ)
  minusTwo : ∀ r, T.IsMinusTwoVertex (vertex r)

lemma SimpleMinusTwoPath.adjacent_nat {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (r : ℕ) (hr : r < P.length) :
    T.intersectionGraph.Adj (P.vertex ⟨r, by omega⟩)
      (P.vertex ⟨r + 1, by omega⟩) := by
  convert P.adjacent ⟨r, hr⟩ using 1 <;> congr

/-- The edge-index product at one step of a simple `(-2)` path. -/
def SimpleMinusTwoPath.edgeIndexProductAt {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (r : Fin P.length) : ℤ :=
  T.edgeIndexProduct (P.vertex r.castSucc) (P.vertex r.succ)

/-- Every five-vertex window in a proper simple `(-2)` path has the classified edge
pattern. -/
lemma SimpleMinusTwoPath.fiveWindow_classification {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (hcard : 5 < Nat.card T.Component)
    (s : ℕ) (hs : s + 4 ≤ P.length) :
    (P.edgeIndexProductAt ⟨s, by omega⟩ = 1 ∧
      P.edgeIndexProductAt ⟨s + 1, by omega⟩ = 1 ∧
      P.edgeIndexProductAt ⟨s + 2, by omega⟩ = 1 ∧
      P.edgeIndexProductAt ⟨s + 3, by omega⟩ = 1) ∨
    (P.edgeIndexProductAt ⟨s, by omega⟩ = 2 ∧
      P.edgeIndexProductAt ⟨s + 1, by omega⟩ = 1 ∧
      P.edgeIndexProductAt ⟨s + 2, by omega⟩ = 1 ∧
      P.edgeIndexProductAt ⟨s + 3, by omega⟩ = 1) ∨
    (P.edgeIndexProductAt ⟨s, by omega⟩ = 1 ∧
      P.edgeIndexProductAt ⟨s + 1, by omega⟩ = 1 ∧
      P.edgeIndexProductAt ⟨s + 2, by omega⟩ = 1 ∧
      P.edgeIndexProductAt ⟨s + 3, by omega⟩ = 2) := by
  have hneq (a b : ℕ) (ha : a ≤ P.length) (hb : b ≤ P.length) (hab : a ≠ b) :
      P.vertex ⟨a, by omega⟩ ≠ P.vertex ⟨b, by omega⟩ := by
    intro heq
    have hfin := P.injective heq
    exact hab (congrArg Fin.val hfin)
  have h := T.fivePath_edgeIndexProducts_classification hcard
    (P.minusTwo ⟨s, by omega⟩)
    (P.minusTwo ⟨s + 1, by omega⟩)
    (P.minusTwo ⟨s + 2, by omega⟩)
    (P.minusTwo ⟨s + 3, by omega⟩)
    (P.minusTwo ⟨s + 4, by omega⟩)
    (P.adjacent ⟨s, by omega⟩)
    (P.adjacent ⟨s + 1, by omega⟩)
    (P.adjacent ⟨s + 2, by omega⟩)
    (P.adjacent ⟨s + 3, by omega⟩)
    (hneq s (s + 2) (by omega) (by omega) (by omega))
    (hneq s (s + 3) (by omega) (by omega) (by omega))
    (hneq s (s + 4) (by omega) (by omega) (by omega))
    (hneq (s + 1) (s + 3) (by omega) (by omega) (by omega))
    (hneq (s + 1) (s + 4) (by omega) (by omega) (by omega))
    (hneq (s + 2) (s + 4) (by omega) (by omega) (by omega))
  simpa [SimpleMinusTwoPath.edgeIndexProductAt] using h

/-- The second edge in a proper five-vertex path window has index product one. -/
lemma SimpleMinusTwoPath.fiveWindow_second_eq_one {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (hcard : 5 < Nat.card T.Component)
    (s : ℕ) (hs : s + 4 ≤ P.length) :
    P.edgeIndexProductAt ⟨s + 1, by omega⟩ = 1 := by
  rcases P.fiveWindow_classification hcard s hs with h | h | h <;> simp_all

/-- The third edge in a proper five-vertex path window has index product one. -/
lemma SimpleMinusTwoPath.fiveWindow_third_eq_one {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (hcard : 5 < Nat.card T.Component)
    (s : ℕ) (hs : s + 4 ≤ P.length) :
    P.edgeIndexProductAt ⟨s + 2, by omega⟩ = 1 := by
  rcases P.fiveWindow_classification hcard s hs with h | h | h <;> simp_all

/-- Every non-end edge of a simple `(-2)` path with at least four edges has index
product one. -/
lemma SimpleMinusTwoPath.interior_edgeIndexProduct_eq_one {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (hcard : 5 < Nat.card T.Component)
    (hlen : 4 ≤ P.length) (r : ℕ) (hrpos : 0 < r) (hrlast : r + 1 < P.length) :
    P.edgeIndexProductAt ⟨r, by omega⟩ = 1 := by
  by_cases hroom : r + 2 < P.length
  · have hwindow := P.fiveWindow_second_eq_one hcard (r - 1) (by omega)
    convert hwindow using 1
    congr
    omega
  · have hwindow := P.fiveWindow_third_eq_one hcard (r - 2) (by omega)
    convert hwindow using 1
    congr
    omega

/-- A maximal simple path in a finite connected graph of maximum degree two
visits every vertex. -/
lemma maximalPath_isHamiltonian_of_degree_le_two
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hconn : G.Connected)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ (u' v' : V) (q : G.Walk u' v'),
      q.IsPath → q.length ≤ p.length)
    (hdegree : ∀ x, G.degree x ≤ 2) : p.IsHamiltonian := by
  apply hp.isHamiltonian_of_mem
  intro x
  by_contra hx
  obtain ⟨Q, _hQ⟩ := hconn.exists_isPath u x
  obtain ⟨d, _hd, hy, hz⟩ :=
    Q.exists_boundary_dart {y | y ∈ p.support} p.start_mem_support hx
  let y := d.fst
  let z := d.snd
  have hy' : y ∈ p.support := hy
  have hz' : z ∉ p.support := hz
  have hyz : G.Adj y z := by
    dsimp [y, z]
    exact d.adj
  by_cases hyu : y = u
  · have hzu : G.Adj z u := by simpa [hyu] using hyz.symm
    have hext : (p.cons hzu).IsPath := hp.cons hz'
    have hle := hmax z v (p.cons hzu) hext
    simp at hle
  by_cases hyv : y = v
  · have hvz : G.Adj v z := by simpa [hyv] using hyz
    have hext := hp.concat hz' hvz
    have hle := hmax u z (p.concat hvz) hext
    simp at hle
  obtain ⟨r, hry, hrle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy'
  have hrpos : 0 < r := by
    by_contra hr
    have hrzero : r = 0 := by omega
    apply hyu
    rw [← hry, hrzero]
    simp
  have hrlt : r < p.length := by
    by_contra hr
    have hreq : r = p.length := by omega
    apply hyv
    rw [← hry, hreq]
    simp
  let prev := p.getVert (r - 1)
  let next := p.getVert (r + 1)
  have hprev : G.Adj y prev := by
    have h := (p.adj_getVert_succ (i := r - 1) (by omega)).symm
    have hr : r - 1 + 1 = r := by omega
    rw [hr, hry] at h
    exact h
  have hnext : G.Adj y next := by
    have h := p.adj_getVert_succ (i := r) hrlt
    rw [hry] at h
    exact h
  have hprevNext : prev ≠ next := by
    intro heq
    have hindex := hp.getVert_injOn (by simp; omega) (by simp; omega) heq
    omega
  have hprevZ : prev ≠ z := by
    intro heq
    apply hz'
    rw [← heq]
    exact p.getVert_mem_support (r - 1)
  have hnextZ : next ≠ z := by
    intro heq
    apply hz'
    rw [← heq]
    exact p.getVert_mem_support (r + 1)
  have hsubset : ({prev, next, z} : Finset V) ⊆ G.neighborFinset y := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [G.mem_neighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact hprev
    · exact hnext
    · exact hyz
  have hthree : ({prev, next, z} : Finset V).card = 3 := by
    simp [hprevNext, hprevZ, hnextZ]
  have hthreeDegree : 3 ≤ G.degree y := by
    rw [← hthree]
    exact Finset.card_le_card hsubset
  have hdegreeY := hdegree y
  omega

/-- Along a simple path in an acyclic graph, distance from the initial vertex
equals the path index. -/
lemma dist_start_getVert_eq_of_isAcyclic
    {V : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (r : ℕ) (hr : r ≤ p.length) : G.dist u (p.getVert r) = r := by
  have hreach : G.Reachable u (p.getVert r) := ⟨p.take r⟩
  obtain ⟨q, hq, hqLength⟩ := hreach.exists_path_of_dist
  have heq : p.take r = q := by
    exact congrArg Subtype.val
      (hG.subsingleton_path u (p.getVert r) |>.elim
        ⟨p.take r, hp.take r⟩ ⟨q, hq⟩)
  calc
    G.dist u (p.getVert r) = q.length := hqLength.symm
    _ = (p.take r).length := by rw [heq]
    _ = r := by simp [hr]

/-- Two indexed vertices of a simple path in an acyclic graph are adjacent only
when their indices differ by one. -/
lemma index_adjacent_of_isAcyclic
    {V : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (r s : ℕ) (hr : r ≤ p.length) (hs : s ≤ p.length)
    (hadj : G.Adj (p.getVert r) (p.getVert s)) :
    r = s + 1 ∨ s = r + 1 := by
  have hreach : G.Reachable u (p.getVert r) := ⟨p.take r⟩
  have hdist := hG.dist_eq_dist_add_one_of_adj_of_reachable u hadj hreach
  rw [dist_start_getVert_eq_of_isAcyclic hG hp r hr,
    dist_start_getVert_eq_of_isAcyclic hG hp s hs] at hdist
  exact hdist

/-- Simple paths in an acyclic graph that leave a common initial vertex through
different first edges do not meet again. -/
lemma getVert_ne_getVert_of_snd_ne_of_isAcyclic
    {V : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic)
    {c u v : V} {p : G.Walk c u} {q : G.Walk c v}
    (hp : p.IsPath) (hq : q.IsPath) (hsnd : p.snd ≠ q.snd)
    (r s : ℕ) (hrpos : 0 < r) (hspos : 0 < s) :
    p.getVert r ≠ q.getVert s := by
  intro heq
  have hpaths : p.take r = (q.take s).copy rfl heq.symm := by
    exact congrArg Subtype.val
      (hG.subsingleton_path c (p.getVert r) |>.elim
        ⟨p.take r, hp.take r⟩ ⟨(q.take s).copy rfl heq.symm, by simpa using hq.take s⟩)
  have hsndEq := congrArg (fun W ↦ W.getVert 1) hpaths
  have hpSnd : (p.take r).getVert 1 = p.snd := by
    rw [p.take_getVert]
    simp [Nat.one_le_iff_ne_zero.mpr (by omega : r ≠ 0)]
  have hqSnd : ((q.take s).copy rfl heq.symm).getVert 1 = q.snd := by
    rw [SimpleGraph.Walk.getVert_copy, q.take_getVert]
    simp [Nat.one_le_iff_ne_zero.mpr (by omega : s ≠ 0)]
  rw [hpSnd, hqSnd] at hsndEq
  exact hsnd hsndEq

/-- An edge leaving a globally maximal path in a graph of maximum degree three
leaves at a trivalent vertex. -/
lemma boundary_degree_eq_three_of_maximalPath
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ (u' v' : V) (q : G.Walk u' v'),
      q.IsPath → q.length ≤ p.length)
    (hdegree : ∀ x, G.degree x ≤ 3) (d : G.Dart)
    (hy : d.fst ∈ p.support) (hz : d.snd ∉ p.support) :
    G.degree d.fst = 3 := by
  classical
  have hyz : G.Adj d.fst d.snd := d.adj
  have hyu : d.fst ≠ u := by
    intro heq
    have hext : (p.cons (heq ▸ hyz.symm)).IsPath := hp.cons hz
    have hle := hmax d.snd v (p.cons (heq ▸ hyz.symm)) hext
    simp at hle
  have hyv : d.fst ≠ v := by
    intro heq
    have hext : (p.concat (heq ▸ hyz)).IsPath := hp.concat hz (heq ▸ hyz)
    have hle := hmax u d.snd (p.concat (heq ▸ hyz)) hext
    simp at hle
  obtain ⟨r, hry, hrle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
  have hrpos : 0 < r := by
    by_contra hr
    have hrzero : r = 0 := by omega
    apply hyu
    rw [← hry, hrzero]
    simp
  have hrlt : r < p.length := by
    by_contra hr
    have hreq : r = p.length := by omega
    apply hyv
    rw [← hry, hreq]
    simp
  let prev := p.getVert (r - 1)
  let next := p.getVert (r + 1)
  have hprev : G.Adj d.fst prev := by
    have h := (p.adj_getVert_succ (i := r - 1) (by omega)).symm
    rw [show r - 1 + 1 = r by omega, hry] at h
    exact h
  have hnext : G.Adj d.fst next := by
    have h := p.adj_getVert_succ (i := r) hrlt
    rw [hry] at h
    exact h
  have hprevNext : prev ≠ next := by
    intro heq
    have hindex := hp.getVert_injOn (by simp; omega) (by simp; omega) heq
    omega
  have hprevZ : prev ≠ d.snd := by
    intro heq
    apply hz
    rw [← heq]
    exact p.getVert_mem_support (r - 1)
  have hnextZ : next ≠ d.snd := by
    intro heq
    apply hz
    rw [← heq]
    exact p.getVert_mem_support (r + 1)
  have hsubset : ({prev, next, d.snd} : Finset V) ⊆ G.neighborFinset d.fst := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [G.mem_neighborFinset]
    rcases hx with rfl | rfl | rfl
    · exact hprev
    · exact hnext
    · exact hyz
  have hthree : ({prev, next, d.snd} : Finset V).card = 3 := by
    simp [hprevNext, hprevZ, hnextZ]
  have hthreeDegree : 3 ≤ G.degree d.fst := by
    rw [← hthree]
    exact Finset.card_le_card hsubset
  exact Nat.le_antisymm (hdegree d.fst) hthreeDegree

/-- The initial vertex of a globally maximal path in an acyclic graph has degree
at most one. -/
lemma maximalPath_start_degree_le_one
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : G.IsAcyclic)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ (u' v' : V) (q : G.Walk u' v'),
      q.IsPath → q.length ≤ p.length) :
    G.degree u ≤ 1 := by
  classical
  have hsubset : G.neighborFinset u ⊆ {p.snd} := by
    intro x hx
    have hux : G.Adj u x := (G.mem_neighborFinset u x).mp hx
    have hxSupport : x ∈ p.support := by
      by_contra hxNot
      have hext : (p.cons hux.symm).IsPath := hp.cons hxNot
      have hle := hmax x v (p.cons hux.symm) hext
      simp at hle
    simpa using hG.eq_snd_of_adj_start hp hux hxSupport
  rw [SimpleGraph.degree]
  exact (Finset.card_le_card hsubset).trans (by simp)

/-- The terminal vertex of a globally maximal path in an acyclic graph has degree
at most one. -/
lemma maximalPath_end_degree_le_one
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : G.IsAcyclic)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ (u' v' : V) (q : G.Walk u' v'),
      q.IsPath → q.length ≤ p.length) :
    G.degree v ≤ 1 := by
  simpa using maximalPath_start_degree_le_one hG hp.reverse
    (fun u' v' q hq ↦ by simpa using hmax v' u' q.reverse hq.reverse)


/-- A neighbor of the initial vertex of a shortest walk cannot reappear after
the first step. -/
lemma shortestWalk_endpoint_neighbor_ne_getVert {V : Type*} {G : SimpleGraph V}
    {u v x : V} (W : G.Walk u v) (hlen : W.length = G.dist u v)
    (hx : G.Adj u x) (r : ℕ) (hr : 1 < r) (hrle : r ≤ W.length) :
    x ≠ W.getVert r := by
  intro heq
  let Q : G.Walk u v := (W.drop r).cons (heq ▸ hx)
  have hdist := G.dist_le Q
  rw [← hlen] at hdist
  have hQ : Q.length = W.length - r + 1 := by simp [Q]
  rw [hQ] at hdist
  omega

/-- The target-end counterpart of `shortestWalk_endpoint_neighbor_ne_getVert`. -/
lemma shortestWalk_target_neighbor_ne_getVert {V : Type*} {G : SimpleGraph V}
    {u v x : V} (W : G.Walk u v) (hlen : W.length = G.dist u v)
    (hx : G.Adj v x) (r : ℕ) (hr : r + 1 < W.length) :
    x ≠ W.getVert r := by
  have hlenRev : W.reverse.length = G.dist v u := by
    rw [W.length_reverse, G.dist_comm]
    exact hlen
  have hne := shortestWalk_endpoint_neighbor_ne_getVert W.reverse hlenRev hx
    (W.length - r) (by omega) (by simp)
  have hindex : W.length - (W.length - r) = r := by omega
  have hrevVert : W.reverse.getVert (W.length - r) = W.getVert r := by
    rw [W.getVert_reverse, hindex]
  intro heq
  apply hne
  exact heq.trans hrevVert.symm

/-- A nontrivial simple `(-2)` path cannot have two further `(-2)` neighbors at each
endpoint: those vertices would form a proper affine `D` diagram. -/
lemma no_doubleFork_subgraph (T : NumericalType)
    (hcard : 5 < Nat.card T.Component)
    (P : T.SimpleMinusTwoPath) (hlen : 0 < P.length)
    (side : Fin 4 → T.Component)
    (hv : Function.Injective (Sum.elim P.vertex side))
    (hproper : ∃ x, ∀ r, x ≠ Sum.elim P.vertex side r)
    (hsideMinus : ∀ k, T.IsMinusTwoVertex (side k))
    (hleft0 : T.intersectionGraph.Adj (P.vertex 0) (side 0))
    (hleft1 : T.intersectionGraph.Adj (P.vertex 0) (side 1))
    (hright2 : T.intersectionGraph.Adj
      (P.vertex ⟨P.length, by omega⟩) (side 2))
    (hright3 : T.intersectionGraph.Adj
      (P.vertex ⟨P.length, by omega⟩) (side 3)) : False := by
  let v : AffineDIndex P.length → T.Component := Sum.elim P.vertex side
  have hv' : Function.Injective v := hv
  have hne (i j : AffineDIndex P.length) (hij : i ≠ j) : v i ≠ v j := hv'.ne hij
  have hleftStar := T.three_minusTwo_neighbors_edgeIndexProducts_eq_one (by omega)
    (P.minusTwo 0) (P.minusTwo ⟨1, by omega⟩) (hsideMinus 0) (hsideMinus 1)
    (P.adjacent ⟨0, by omega⟩) hleft0 hleft1
    (hne (Sum.inl ⟨1, by omega⟩) (Sum.inr 0) (by simp))
    (hne (Sum.inl ⟨1, by omega⟩) (Sum.inr 1) (by simp))
    (hne (Sum.inr 0) (Sum.inr 1) (by
      intro heq
      have := congrArg (fun z : AffineDIndex P.length => match z with
        | .inl _ => 0
        | .inr k => k.val) heq
      norm_num at this))
  have hrightSpine : T.intersectionGraph.Adj
      (P.vertex ⟨P.length, by omega⟩) (P.vertex ⟨P.length - 1, by omega⟩) := by
    convert (P.adjacent ⟨P.length - 1, by omega⟩).symm using 1 <;> (congr <;> omega)
  have hrightStar := T.three_minusTwo_neighbors_edgeIndexProducts_eq_one (by omega)
    (P.minusTwo ⟨P.length, by omega⟩)
    (P.minusTwo ⟨P.length - 1, by omega⟩) (hsideMinus 2) (hsideMinus 3)
    hrightSpine hright2 hright3
    (hne (Sum.inl ⟨P.length - 1, by omega⟩) (Sum.inr 2) (by simp))
    (hne (Sum.inl ⟨P.length - 1, by omega⟩) (Sum.inr 3) (by simp))
    (hne (Sum.inr 2) (Sum.inr 3) (by
      intro heq
      have := congrArg (fun z : AffineDIndex P.length => match z with
        | .inl _ => 0
        | .inr k => k.val) heq
      norm_num at this))
  have hspine (r : Fin P.length) : P.edgeIndexProductAt r = 1 := by
    by_cases hr0 : r.val = 0
    · have hcast : r.castSucc = (0 : Fin (P.length + 1)) := by
        apply Fin.ext
        simpa using hr0
      have hsucc : r.succ = ⟨1, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      dsimp [SimpleMinusTwoPath.edgeIndexProductAt]
      rw [hcast, hsucc]
      exact hleftStar.1
    · by_cases hrlast : r.val + 1 = P.length
      · have hcast : r.castSucc = ⟨P.length - 1, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_castSucc]
          omega
        have hsucc : r.succ = ⟨P.length, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_succ]
          omega
        dsimp [SimpleMinusTwoPath.edgeIndexProductAt]
        rw [hcast, hsucc, T.edgeIndexProduct_symm]
        exact hrightStar.1
      · by_cases hlong : 4 ≤ P.length
        · exact P.interior_edgeIndexProduct_eq_one hcard hlong r.val (by omega) (by omega)
        · have hlength : P.length = 3 := by omega
          have hmiddle := T.extended_D4_edgeIndexProduct_eq_one hcard
            (P.minusTwo ⟨2, by omega⟩) (P.minusTwo ⟨1, by omega⟩)
            (P.minusTwo 0) (hsideMinus 0) (hsideMinus 1)
            (P.adjacent ⟨1, by omega⟩).symm
            (P.adjacent ⟨0, by omega⟩).symm hleft0 hleft1
            (hne (Sum.inl ⟨2, by omega⟩) (Sum.inl 0) (by simp))
            (hne (Sum.inl ⟨2, by omega⟩) (Sum.inr 0) (by simp))
            (hne (Sum.inl ⟨2, by omega⟩) (Sum.inr 1) (by simp))
            (hne (Sum.inl ⟨1, by omega⟩) (Sum.inr 0) (by simp))
            (hne (Sum.inl ⟨1, by omega⟩) (Sum.inr 1) (by simp))
            (hne (Sum.inr 0) (Sum.inr 1) (by
              intro heq
              have := congrArg (fun z : AffineDIndex P.length => match z with
                | .inl _ => 0
                | .inr k => k.val) heq
              norm_num at this))
          have hrval : r.val = 1 := by omega
          have hcast : r.castSucc = ⟨1, by omega⟩ := by
            apply Fin.ext
            simpa using hrval
          have hsucc : r.succ = ⟨2, by omega⟩ := by
            apply Fin.ext
            simp only [Fin.val_succ]
            omega
          dsimp [SimpleMinusTwoPath.edgeIndexProductAt]
          rw [hcast, hsucc, T.edgeIndexProduct_symm]
          exact hmiddle
  have hminus : ∀ r, T.IsMinusTwoVertex (v r) := by
    rintro (r | k)
    · exact P.minusTwo r
    · exact hsideMinus k
  have hproper' : ∃ x, ∀ r, x ≠ v r := hproper
  apply T.no_affineD_configuration P.length (by omega) v hv' hproper' hminus
  intro i j hj
  rcases i with i | k
  · by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      rw [hi] at hj ⊢
      have hj' : j = Sum.inl (⟨1, by omega⟩ : Fin (P.length + 1)) ∨
          j = Sum.inr 0 ∨ j = Sum.inr 1 := by
        simpa [affineDNeighbors] using hj
      rcases hj' with rfl | rfl | rfl
      · simpa [v] using P.adjacent_nat 0 (by omega)
      · simpa [v] using hleft0
      · simpa [v] using hleft1
    · by_cases hin : i.val = P.length
      · have hi : i = ⟨P.length, by omega⟩ := Fin.ext hin
        rw [hi] at hj ⊢
        have hj' :
            j = Sum.inl (⟨P.length - 1, by omega⟩ : Fin (P.length + 1)) ∨
            j = Sum.inr 2 ∨ j = Sum.inr 3 := by
          simpa [affineDNeighbors, show P.length ≠ 0 by omega] using hj
        rcases hj' with rfl | rfl | rfl
        · simpa [v] using hrightSpine
        · simpa [v] using hright2
        · simpa [v] using hright3
      · have hj' :
            j = Sum.inl (⟨i.val - 1, by omega⟩ : Fin (P.length + 1)) ∨
            j = Sum.inl (⟨i.val + 1, by omega⟩ : Fin (P.length + 1)) := by
          simpa [affineDNeighbors, hi0, hin] using hj
        rcases hj' with rfl | rfl
        · change T.intersectionGraph.Adj (P.vertex i)
              (P.vertex ⟨i.val - 1, by omega⟩)
          have hsucc :
              (⟨(i.val - 1) + 1, by omega⟩ : Fin (P.length + 1)) = i := by
            apply Fin.ext
            change (i.val - 1) + 1 = i.val
            omega
          have hadj0 := P.adjacent_nat (i.val - 1) (by omega)
          rw [hsucc] at hadj0
          have hadj : T.intersectionGraph.Adj (P.vertex i)
              (P.vertex ⟨i.val - 1, by omega⟩) := hadj0.symm
          simpa [v] using hadj
        · change T.intersectionGraph.Adj (P.vertex i)
              (P.vertex ⟨i.val + 1, by omega⟩)
          simpa [v] using P.adjacent_nat i.val (by omega)
  · fin_cases k
    · have hj' : j = Sum.inl (0 : Fin (P.length + 1)) := by
        simpa [affineDNeighbors] using hj
      rw [hj']
      simpa [v] using hleft0.symm
    · have hj' : j = Sum.inl (0 : Fin (P.length + 1)) := by
        simpa [affineDNeighbors] using hj
      rw [hj']
      simpa [v] using hleft1.symm
    · have hj' : j = Sum.inl (⟨P.length, by omega⟩ : Fin (P.length + 1)) := by
        simpa [affineDNeighbors] using hj
      rw [hj']
      simpa [v] using hright2.symm
    · have hj' : j = Sum.inl (⟨P.length, by omega⟩ : Fin (P.length + 1)) := by
        simpa [affineDNeighbors] using hj
      rw [hj']
      simpa [v] using hright3.symm

/-- The first edge of a long simple `(-2)` path has index product one or two. -/
lemma SimpleMinusTwoPath.first_edgeIndexProduct_eq_one_or_two {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (hcard : 5 < Nat.card T.Component)
    (hlen : 4 ≤ P.length) :
    P.edgeIndexProductAt ⟨0, by omega⟩ = 1 ∨
      P.edgeIndexProductAt ⟨0, by omega⟩ = 2 := by
  rcases P.fiveWindow_classification hcard 0 hlen with h | h | h
  · exact Or.inl h.1
  · exact Or.inr h.1
  · exact Or.inl h.1

/-- The last edge of a long simple `(-2)` path has index product one or two. -/
lemma SimpleMinusTwoPath.last_edgeIndexProduct_eq_one_or_two {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (hcard : 5 < Nat.card T.Component)
    (hlen : 4 ≤ P.length) :
    P.edgeIndexProductAt ⟨P.length - 1, by omega⟩ = 1 ∨
      P.edgeIndexProductAt ⟨P.length - 1, by omega⟩ = 2 := by
  have hwindow := P.fiveWindow_classification hcard (P.length - 4) (by omega)
  rcases hwindow with h | h | h
  · left
    convert h.2.2.2 using 1
    congr
    omega
  · left
    convert h.2.2.2 using 1
    congr
    omega
  · right
    convert h.2.2.2 using 1
    congr
    omega

/-- All non-endpoint weights along a long simple `(-2)` path are equal. -/
lemma SimpleMinusTwoPath.interior_vertex_weight_eq_second {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (hcard : 5 < Nat.card T.Component)
    (hlen : 4 ≤ P.length) (r : ℕ) (hrpos : 0 < r) (hrlt : r < P.length) :
    T.weight (P.vertex ⟨r, by omega⟩) = T.weight (P.vertex ⟨1, by omega⟩) := by
  induction r with
  | zero => omega
  | succ r ih =>
      by_cases hrzero : r = 0
      · subst r
        rfl
      · have ih' := ih (by omega) (by omega)
        have hprod := P.interior_edgeIndexProduct_eq_one hcard hlen r (by omega) (by omega)
        have hadj := P.adjacent ⟨r, by omega⟩
        have hw := T.weights_eq_of_edgeIndexProduct_eq_one hadj hprod
        exact hw.symm.trans ih'

/-- Every component weight on a long simple `(-2)` path is at most twice its common
interior weight. -/
lemma SimpleMinusTwoPath.vertex_weight_le_two_mul_second {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (hcard : 5 < Nat.card T.Component)
    (hlen : 4 ≤ P.length) (r : ℕ) (hr : r ≤ P.length) :
    (T.weight (P.vertex ⟨r, by omega⟩) : ℕ) ≤
      2 * T.weight (P.vertex ⟨1, by omega⟩) := by
  by_cases hrzero : r = 0
  · subst r
    have hprod := P.first_edgeIndexProduct_eq_one_or_two hcard hlen
    exact T.weight_le_two_mul_of_edgeIndexProduct_eq_one_or_two (by omega)
      (P.minusTwo ⟨0, by omega⟩) (P.minusTwo ⟨1, by omega⟩)
      (P.adjacent ⟨0, by omega⟩) hprod
  · by_cases hrlast : r = P.length
    · subst r
      have hprod := P.last_edgeIndexProduct_eq_one_or_two hcard hlen
      have hadj : T.intersectionGraph.Adj
          (P.vertex ⟨P.length, by omega⟩) (P.vertex ⟨P.length - 1, by omega⟩) := by
        convert (P.adjacent ⟨P.length - 1, by omega⟩).symm using 1
        all_goals congr <;> omega
      have hprod' :
          T.edgeIndexProduct (P.vertex ⟨P.length, by omega⟩)
              (P.vertex ⟨P.length - 1, by omega⟩) = 1 ∨
            T.edgeIndexProduct (P.vertex ⟨P.length, by omega⟩)
              (P.vertex ⟨P.length - 1, by omega⟩) = 2 := by
        rcases hprod with hprod | hprod
        · left
          rw [T.edgeIndexProduct_symm]
          convert hprod using 1
          congr
          omega
        · right
          rw [T.edgeIndexProduct_symm]
          convert hprod using 1
          congr
          omega
      have hlast := T.weight_le_two_mul_of_edgeIndexProduct_eq_one_or_two (by omega)
        (P.minusTwo ⟨P.length, by omega⟩) (P.minusTwo ⟨P.length - 1, by omega⟩)
        hadj hprod'
      have hinterior := P.interior_vertex_weight_eq_second hcard hlen
        (P.length - 1) (by omega) (by omega)
      simpa [hinterior] using hlast
    · have hinterior := P.interior_vertex_weight_eq_second hcard hlen r (by omega) (by omega)
      have hwNat : (T.weight (P.vertex ⟨r, by omega⟩) : ℕ) =
          T.weight (P.vertex ⟨1, by omega⟩) := congrArg Subtype.val hinterior
      omega


/-- Multiplicities form a concave integer sequence along the unit-index core of a long
simple `(-2)` path. -/
lemma SimpleMinusTwoPath.multiplicity_concave_at_core {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (hcard : 5 < Nat.card T.Component)
    (hlen : 4 ≤ P.length) (r : ℕ) (hrleft : 1 < r) (hrright : r + 1 < P.length) :
    (T.multiplicity (P.vertex ⟨r - 1, by omega⟩) : ℤ) +
        (T.multiplicity (P.vertex ⟨r + 1, by omega⟩) : ℤ) ≤
      2 * (T.multiplicity (P.vertex ⟨r, by omega⟩) : ℤ) := by
  have hleftProduct := P.interior_edgeIndexProduct_eq_one hcard hlen
    (r - 1) (by omega) (by omega)
  have hrightProduct := P.interior_edgeIndexProduct_eq_one hcard hlen
    r (by omega) (by omega)
  have hleft : T.intersectionGraph.Adj
      (P.vertex ⟨r, by omega⟩) (P.vertex ⟨r - 1, by omega⟩) := by
    have hcenter : (⟨r, by omega⟩ : Fin (P.length + 1)) =
        (⟨r - 1, by omega⟩ : Fin P.length).succ := by ext; simp; omega
    have hprev : (⟨r - 1, by omega⟩ : Fin (P.length + 1)) =
        (⟨r - 1, by omega⟩ : Fin P.length).castSucc := by rfl
    rw [hcenter, hprev]
    exact (P.adjacent ⟨r - 1, by omega⟩).symm
  have hright : T.intersectionGraph.Adj
      (P.vertex ⟨r, by omega⟩) (P.vertex ⟨r + 1, by omega⟩) := by
    have hcenter : (⟨r, by omega⟩ : Fin (P.length + 1)) =
        (⟨r, by omega⟩ : Fin P.length).castSucc := by rfl
    have hnext : (⟨r + 1, by omega⟩ : Fin (P.length + 1)) =
        (⟨r, by omega⟩ : Fin P.length).succ := by rfl
    rw [hcenter, hnext]
    exact P.adjacent ⟨r, by omega⟩
  have hdistinct : P.vertex ⟨r - 1, by omega⟩ ≠ P.vertex ⟨r + 1, by omega⟩ := by
    intro heq
    have hfin := P.injective heq
    have hval : r - 1 = r + 1 := by simpa using congrArg Fin.val hfin
    omega
  apply T.minusTwo_multiplicity_concave_of_unit_edges
    (P.minusTwo ⟨r, by omega⟩) hleft hright hdistinct
  · rw [T.edgeIndexProduct_symm]
    convert hleftProduct using 1
    congr
    omega
  · convert hrightProduct using 1
    congr


/-- The common interior weight is at most twice any vertex weight on the path. -/
lemma SimpleMinusTwoPath.second_weight_le_two_mul_vertex {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (hcard : 5 < Nat.card T.Component)
    (hlen : 4 ≤ P.length) (r : ℕ) (hr : r ≤ P.length) :
    (T.weight (P.vertex ⟨1, by omega⟩) : ℕ) ≤
      2 * T.weight (P.vertex ⟨r, by omega⟩) := by
  by_cases hrzero : r = 0
  · subst r
    have hprod := P.first_edgeIndexProduct_eq_one_or_two hcard hlen
    have hprod' :
        T.edgeIndexProduct (P.vertex ⟨1, by omega⟩) (P.vertex ⟨0, by omega⟩) = 1 ∨
          T.edgeIndexProduct (P.vertex ⟨1, by omega⟩) (P.vertex ⟨0, by omega⟩) = 2 := by
      simpa [SimpleMinusTwoPath.edgeIndexProductAt] using hprod
    exact T.weight_le_two_mul_of_edgeIndexProduct_eq_one_or_two (by omega)
      (P.minusTwo ⟨1, by omega⟩) (P.minusTwo ⟨0, by omega⟩)
      (P.adjacent ⟨0, by omega⟩).symm hprod'
  · by_cases hrlast : r = P.length
    · subst r
      have hprod := P.last_edgeIndexProduct_eq_one_or_two hcard hlen
      have hadj : T.intersectionGraph.Adj
          (P.vertex ⟨P.length - 1, by omega⟩) (P.vertex ⟨P.length, by omega⟩) := by
        convert P.adjacent ⟨P.length - 1, by omega⟩ using 1
        all_goals congr <;> omega
      have hprod' :
          T.edgeIndexProduct (P.vertex ⟨P.length - 1, by omega⟩)
              (P.vertex ⟨P.length, by omega⟩) = 1 ∨
            T.edgeIndexProduct (P.vertex ⟨P.length - 1, by omega⟩)
              (P.vertex ⟨P.length, by omega⟩) = 2 := by
        rcases hprod with hprod | hprod
        · left
          convert hprod using 1
          congr
          omega
        · right
          convert hprod using 1
          congr
          omega
      have hlast := T.weight_le_two_mul_of_edgeIndexProduct_eq_one_or_two (by omega)
        (P.minusTwo ⟨P.length - 1, by omega⟩) (P.minusTwo ⟨P.length, by omega⟩)
        hadj hprod'
      have hinterior := P.interior_vertex_weight_eq_second hcard hlen
        (P.length - 1) (by omega) (by omega)
      have hinteriorNat : (T.weight (P.vertex ⟨P.length - 1, by omega⟩) : ℕ) =
          T.weight (P.vertex ⟨1, by omega⟩) := congrArg Subtype.val hinterior
      omega
    · have hinterior := P.interior_vertex_weight_eq_second hcard hlen r (by omega) (by omega)
      have hwNat : (T.weight (P.vertex ⟨r, by omega⟩) : ℕ) =
          T.weight (P.vertex ⟨1, by omega⟩) := congrArg Subtype.val hinterior
      omega

/-- Any two component weights on a long simple `(-2)` path differ by at most a factor
of four. -/
lemma SimpleMinusTwoPath.vertex_weight_le_four_mul_vertex {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (hcard : 5 < Nat.card T.Component)
    (hlen : 4 ≤ P.length) (r s : ℕ) (hr : r ≤ P.length) (hs : s ≤ P.length) :
    (T.weight (P.vertex ⟨r, by omega⟩) : ℕ) ≤
      4 * T.weight (P.vertex ⟨s, by omega⟩) := by
  have hrw := P.vertex_weight_le_two_mul_second hcard hlen r hr
  have hsw := P.second_weight_le_two_mul_vertex hcard hlen s hs
  omega

/-- For a numerical type with more than one component, the zero component contributions
are exactly the `(-2)`-vertices.  This is Stacks Project tag `0C7D`. -/
lemma twiceComponentContribution_eq_zero_iff (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) (i : T.Component) :
    T.twiceComponentContribution i = 0 ↔ T.IsMinusTwoVertex i := by
  have hm : 0 < (T.multiplicity i : ℤ) := by positivity
  have hw : 0 < (T.weight i : ℤ) := by positivity
  have hdiag := T.selfIntersection_neg_of_one_lt_card hcard i
  constructor
  · intro hzero
    have hg : T.genus i = 0 := by
      by_contra hg
      have hgNat : 1 ≤ T.genus i := by omega
      have hgInt : (1 : ℤ) ≤ T.genus i := by exact_mod_cast hgNat
      dsimp [twiceComponentContribution] at hzero
      have hfirst : 0 ≤ 2 * (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.genus i : ℤ) - 1) := by positivity
      have hsecond : 0 < -((T.multiplicity i : ℤ) * T.intersection i i) := by
        exact neg_pos.mpr (mul_neg_of_pos_of_neg hm hdiag)
      nlinarith
    refine ⟨hg, ?_⟩
    simp only [twiceComponentContribution, hg, Nat.cast_zero] at hzero
    nlinarith
  · rintro ⟨hg, hdiagEq⟩
    simp only [twiceComponentContribution, hg, Nat.cast_zero, hdiagEq]
    ring

/-- The finite set of components that consume positive genus budget. -/
def nonMinusTwoVertices (T : NumericalType) : Finset T.Component := by
  classical
  exact Finset.univ.filter fun i => ¬ T.IsMinusTwoVertex i

@[simp] lemma mem_nonMinusTwoVertices_iff (T : NumericalType) (i : T.Component) :
    i ∈ T.nonMinusTwoVertices ↔ ¬ T.IsMinusTwoVertex i := by
  simp [nonMinusTwoVertices]

/-- A non-`(-2)` component of a minimal numerical type consumes a strictly positive
integer amount of the doubled genus budget. -/
lemma twiceComponentContribution_pos_of_nonMinusTwo (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component) {i : T.Component}
    (hi : ¬ T.IsMinusTwoVertex i) :
    0 < T.twiceComponentContribution i := by
  have hnonneg := T.twiceComponentContribution_nonnegative_of_minimal hmin hcard i
  have hne : T.twiceComponentContribution i ≠ 0 := by
    intro hzero
    exact hi ((T.twiceComponentContribution_eq_zero_iff hcard i).mp hzero)
  omega

/-- The total doubled component contribution is twice `g - 1`. -/
lemma sum_twiceComponentContribution (T : NumericalType) :
    ∑ i, T.twiceComponentContribution i = 2 * (T.arithmeticGenus - 1) := by
  have h := T.two_mul_arithmeticGenus_eq_sum_twiceComponentContribution
  omega

/-- A numerical type of arithmetic genus at least two has a non-`(-2)` component. -/
lemma exists_nonMinusTwo_of_two_le_arithmeticGenus (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus) :
    ∃ i, ¬ T.IsMinusTwoVertex i := by
  by_contra hnone
  push Not at hnone
  have hzero : ∀ i, T.twiceComponentContribution i = 0 := by
    intro i
    exact (T.twiceComponentContribution_eq_zero_iff hcard i).mpr (hnone i)
  have hsum := T.sum_twiceComponentContribution
  simp only [hzero, Finset.sum_const_zero] at hsum
  omega

/-- Every nonempty collection closed under `(-2)` adjacency meets a non-`(-2)` heart
component. -/
lemma closed_minusTwo_cluster_meets_heart (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    (s : Finset T.Component) (hs : s.Nonempty)
    (hminus : ∀ i ∈ s, T.IsMinusTwoVertex i)
    (hclosed : ∀ i ∈ s, ∀ j, T.intersectionGraph.Adj i j →
      T.IsMinusTwoVertex j → j ∈ s) :
    ∃ i ∈ s, ∃ j, ¬ T.IsMinusTwoVertex j ∧ T.intersectionGraph.Adj i j := by
  obtain ⟨heart, hheart⟩ := T.exists_nonMinusTwo_of_two_le_arithmeticGenus hcard hgenus
  have hheartNotMem : heart ∉ s := by
    intro hmem
    exact hheart (hminus heart hmem)
  have hproper : s ≠ Finset.univ := by
    intro hall
    exact hheartNotMem (by rw [hall]; simp)
  obtain ⟨i, hi, j, hj, hne⟩ := T.noDisconnectedCut s hs hproper
  have hij : i ≠ j := by
    intro heq
    subst j
    exact hj hi
  have hnonneg := T.offDiagonal_nonnegative i j hij
  have hadj : T.intersectionGraph.Adj i j := ⟨hij, lt_of_le_of_ne hnonneg hne.symm⟩
  have hjheart : ¬ T.IsMinusTwoVertex j := by
    intro hjminus
    exact hj (hclosed i hi j hadj hjminus)
  exact ⟨i, hi, j, hjheart, hadj⟩


/-- A nonempty collection containing every `(-2)` component adjacent to one of its
vertices. -/
structure MinusTwoCluster (T : NumericalType) where
  vertices : Finset T.Component
  nonempty : vertices.Nonempty
  minusTwo : ∀ i ∈ vertices, T.IsMinusTwoVertex i
  closed : ∀ i ∈ vertices, ∀ j, T.intersectionGraph.Adj i j →
    T.IsMinusTwoVertex j → j ∈ vertices

/-- The neighbors of a component that lie inside a closed `(-2)` cluster. -/
def MinusTwoCluster.internalNeighbors {T : NumericalType}
    (C : T.MinusTwoCluster) (i : T.Component) : Finset T.Component :=
  C.vertices.filter fun j => T.intersectionGraph.Adj i j

@[simp] lemma MinusTwoCluster.mem_internalNeighbors_iff {T : NumericalType}
    (C : T.MinusTwoCluster) (i j : T.Component) :
    j ∈ C.internalNeighbors i ↔ j ∈ C.vertices ∧ T.intersectionGraph.Adj i j := by
  simp [MinusTwoCluster.internalNeighbors]

/-- Every closed `(-2)` cluster in genus at least two meets the non-`(-2)` heart. -/
lemma MinusTwoCluster.meets_heart {T : NumericalType} (C : T.MinusTwoCluster)
    (hcard : 1 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus) :
    ∃ i ∈ C.vertices, ∃ j, ¬ T.IsMinusTwoVertex j ∧ T.intersectionGraph.Adj i j := by
  exact T.closed_minusTwo_cluster_meets_heart hcard hgenus C.vertices C.nonempty
    C.minusTwo C.closed

/-- Every vertex of a proper closed `(-2)` cluster has internal degree at most three. -/
lemma MinusTwoCluster.internalNeighbors_card_le_three {T : NumericalType}
    (C : T.MinusTwoCluster) (hcard : 5 < Nat.card T.Component)
    {c : T.Component} (hc : c ∈ C.vertices) :
    (C.internalNeighbors c).card ≤ 3 := by
  by_contra hnot
  have hlt : 3 < (C.internalNeighbors c).card := by omega
  obtain ⟨i, hi, j, hj, k, hk, l, hl, hij, hik, hil, hjk, hjl, hkl⟩ :=
    Finset.three_lt_card.mp hlt
  have hci := (C.mem_internalNeighbors_iff c i).mp hi
  have hcj := (C.mem_internalNeighbors_iff c j).mp hj
  have hck := (C.mem_internalNeighbors_iff c k).mp hk
  have hcl := (C.mem_internalNeighbors_iff c l).mp hl
  exact T.no_four_minusTwo_neighbors hcard (C.minusTwo c hc)
    (C.minusTwo i hci.1) (C.minusTwo j hcj.1) (C.minusTwo k hck.1)
    (C.minusTwo l hcl.1) hci.2 hcj.2 hck.2 hcl.2 hij hik hil hjk hjl hkl

/-- An internal degree-three vertex has exactly the unit-index weighted `D₄` star. -/
lemma MinusTwoCluster.exists_three_neighbors_unit_index {T : NumericalType}
    (C : T.MinusTwoCluster) (hcard : 5 < Nat.card T.Component)
    {c : T.Component} (hc : c ∈ C.vertices) (hdegree : (C.internalNeighbors c).card = 3) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      C.internalNeighbors c = {i, j, k} ∧
      T.edgeIndexProduct c i = 1 ∧ T.edgeIndexProduct c j = 1 ∧
        T.edgeIndexProduct c k = 1 := by
  obtain ⟨i, j, k, hij, hik, hjk, hneighbors⟩ :=
    Finset.card_eq_three.mp hdegree
  have hi : i ∈ C.internalNeighbors c := by rw [hneighbors]; simp
  have hj : j ∈ C.internalNeighbors c := by rw [hneighbors]; simp
  have hk : k ∈ C.internalNeighbors c := by rw [hneighbors]; simp
  have hci := (C.mem_internalNeighbors_iff c i).mp hi
  have hcj := (C.mem_internalNeighbors_iff c j).mp hj
  have hck := (C.mem_internalNeighbors_iff c k).mp hk
  have hprod := T.three_minusTwo_neighbors_edgeIndexProducts_eq_one (by omega)
    (C.minusTwo c hc) (C.minusTwo i hci.1) (C.minusTwo j hcj.1)
    (C.minusTwo k hck.1) hci.2 hcj.2 hck.2 hij hik hjk
  exact ⟨i, j, k, hij, hik, hjk, hneighbors, hprod⟩

/-- Removing one member from a three-element internal neighborhood leaves two
distinct neighbors away from the removed vertex. -/
lemma MinusTwoCluster.exists_two_internalNeighbors_away {T : NumericalType}
    (C : T.MinusTwoCluster) {c next : T.Component}
    (hdegree : (C.internalNeighbors c).card = 3)
    (hnext : next ∈ C.internalNeighbors c) :
    ∃ a b, a ≠ b ∧ a ∈ C.internalNeighbors c ∧ b ∈ C.internalNeighbors c ∧
      a ≠ next ∧ b ≠ next := by
  have hcard : ((C.internalNeighbors c).erase next).card = 2 := by
    rw [Finset.card_erase_of_mem hnext, hdegree]
  obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp hcard
  have haErase : a ∈ (C.internalNeighbors c).erase next := by rw [heq]; simp
  have hbErase : b ∈ (C.internalNeighbors c).erase next := by rw [heq]; simp
  exact ⟨a, b, hab, (Finset.mem_erase.mp haErase).2,
    (Finset.mem_erase.mp hbErase).2, (Finset.mem_erase.mp haErase).1,
    (Finset.mem_erase.mp hbErase).1⟩

/-- The graph obtained by retaining exactly the edges whose two endpoints are `(-2)`
vertices. -/
def minusTwoGraph (T : NumericalType) : SimpleGraph T.Component where
  Adj i j := T.IsMinusTwoVertex i ∧ T.IsMinusTwoVertex j ∧
    T.intersectionGraph.Adj i j
  symm.symm i j hij := ⟨hij.2.1, hij.1, hij.2.2.symm⟩

instance minusTwoGraphAdjDecidable (T : NumericalType) :
    DecidableRel T.minusTwoGraph.Adj := fun i j ↦ by
  classical
  change Decidable (T.IsMinusTwoVertex i ∧ T.IsMinusTwoVertex j ∧
    T.intersectionGraph.Adj i j)
  infer_instance

@[simp] lemma minusTwoGraph_adj (T : NumericalType) (i j : T.Component) :
    T.minusTwoGraph.Adj i j ↔ T.IsMinusTwoVertex i ∧
      T.IsMinusTwoVertex j ∧ T.intersectionGraph.Adj i j := Iff.rfl

/-- In arithmetic genus at least two, the graph of `(-2)` vertices is acyclic.
A hypothetical cycle is a proper affine `A` configuration, because a non-`(-2)`
component lies outside it. -/
lemma minusTwoGraph_isAcyclic (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus) :
    T.minusTwoGraph.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_free_cycleGraph]
  intro n hn hcycle
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rcases hcycle with ⟨copy⟩
  obtain ⟨heart, hheart⟩ :=
    T.exists_nonMinusTwo_of_two_le_arithmeticGenus hcard hgenus
  have hminusCopy (i : Fin (m + 3)) : T.IsMinusTwoVertex (copy i) := by
    have hadjCycle :
        (SimpleGraph.cycleGraph (m + 3)).Adj i (i + 1) := by
      rw [SimpleGraph.cycleGraph_adj]
      right
      simp
    exact (copy.toHom.map_rel hadjCycle).1
  apply T.no_affineA_configuration (m + 3) hn copy copy.injective
  · exact ⟨heart, fun i heq ↦ hheart (heq ▸ hminusCopy i)⟩
  · exact hminusCopy
  · intro i j hij
    exact (copy.toHom.map_rel hij).2.2

/-- The vertices in the connected `(-2)` component containing a root. -/
def minusTwoClusterVertices (T : NumericalType) (root : T.Component) :
    Finset T.Component :=
  Finset.univ.filter fun i => T.minusTwoGraph.Reachable root i

@[simp] lemma mem_minusTwoClusterVertices_iff (T : NumericalType)
    (root i : T.Component) :
    i ∈ T.minusTwoClusterVertices root ↔ T.minusTwoGraph.Reachable root i := by
  simp [minusTwoClusterVertices]

lemma minusTwo_of_minusTwoGraph_reachable (T : NumericalType)
    {root i : T.Component} (hroot : T.IsMinusTwoVertex root)
    (hreach : T.minusTwoGraph.Reachable root i) : T.IsMinusTwoVertex i := by
  rw [T.minusTwoGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact hroot
  | tail _ hij ih => exact hij.2.1

/-- The connected `(-2)` component through any `(-2)` root is a closed cluster. -/
def minusTwoClusterAt (T : NumericalType) (root : T.Component)
    (hroot : T.IsMinusTwoVertex root) : T.MinusTwoCluster where
  vertices := T.minusTwoClusterVertices root
  nonempty := ⟨root, by simp⟩
  minusTwo i hi := T.minusTwo_of_minusTwoGraph_reachable hroot
    ((T.mem_minusTwoClusterVertices_iff root i).mp hi)
  closed i hi j hij hj := by
    rw [T.mem_minusTwoClusterVertices_iff]
    have hireach := (T.mem_minusTwoClusterVertices_iff root i).mp hi
    have hiMinus := T.minusTwo_of_minusTwoGraph_reachable hroot hireach
    exact hireach.trans
      (show T.minusTwoGraph.Adj i j from ⟨hiMinus, hj, hij⟩).reachable

/-- Any two vertices of the canonical cluster are connected by a path consisting only
of `(-2)` vertices. -/
lemma minusTwoClusterAt_reachable (T : NumericalType) {root i j : T.Component}
    (hroot : T.IsMinusTwoVertex root)
    (hi : i ∈ (T.minusTwoClusterAt root hroot).vertices)
    (hj : j ∈ (T.minusTwoClusterAt root hroot).vertices) :
    T.minusTwoGraph.Reachable i j := by
  have hir : T.minusTwoGraph.Reachable root i := by
    exact (T.mem_minusTwoClusterVertices_iff root i).mp hi
  have hjr : T.minusTwoGraph.Reachable root j := by
    exact (T.mem_minusTwoClusterVertices_iff root j).mp hj
  exact hir.symm.trans hjr

/-- The graph internal to a closed `(-2)` cluster. -/
def MinusTwoCluster.internalGraph {T : NumericalType} (C : T.MinusTwoCluster) :
    SimpleGraph {i // i ∈ C.vertices} :=
  T.minusTwoGraph.induce {i | i ∈ C.vertices}

@[simp] lemma MinusTwoCluster.internalGraph_adj {T : NumericalType}
    (C : T.MinusTwoCluster) (i j : {i // i ∈ C.vertices}) :
    C.internalGraph.Adj i j ↔ T.intersectionGraph.Adj i.1 j.1 := by
  constructor
  · exact fun h ↦ h.2.2
  · intro h
    exact ⟨C.minusTwo i.1 i.2, C.minusTwo j.1 j.2, h⟩

instance MinusTwoCluster.internalGraphAdjDecidable {T : NumericalType}
    (C : T.MinusTwoCluster) : DecidableRel C.internalGraph.Adj := fun i j ↦ by
  rw [C.internalGraph_adj]
  infer_instance

/-- A walk in the `(-2)` graph that starts in a closed cluster stays in that cluster. -/
lemma MinusTwoCluster.walk_support_subset {T : NumericalType}
    (C : T.MinusTwoCluster) {i j : T.Component} (hi : i ∈ C.vertices)
    (W : T.minusTwoGraph.Walk i j) : ∀ x ∈ W.support, x ∈ C.vertices := by
  induction W with
  | nil => simpa using hi
  | @cons u v w huv p ih =>
      intro x hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hi
      · exact ih (C.closed u hi v huv.2.2 huv.2.1) x hx

/-- The internal graph of a canonical cluster is connected. -/
lemma minusTwoClusterAt_internalGraph_connected (T : NumericalType)
    {target : T.Component} (htarget : T.IsMinusTwoVertex target) :
    (T.minusTwoClusterAt target htarget).internalGraph.Connected := by
  let C := T.minusTwoClusterAt target htarget
  rw [SimpleGraph.connected_iff]
  constructor
  · intro i j
    have hreach : T.minusTwoGraph.Reachable i.1 j.1 :=
      T.minusTwoClusterAt_reachable htarget i.2 j.2
    rcases hreach with ⟨W⟩
    have hall := C.walk_support_subset i.2 W
    let W' := W.induce {x | x ∈ C.vertices} hall
    refine ⟨W'.copy ?_ ?_⟩
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  · exact ⟨⟨target, by simp [minusTwoClusterAt]⟩⟩

/-- Internal graph degree is the cardinality of the cluster's internal-neighbor set. -/
lemma MinusTwoCluster.degree_internalGraph_eq_card_internalNeighbors
    {T : NumericalType} (C : T.MinusTwoCluster)
    (i : {i // i ∈ C.vertices}) :
    C.internalGraph.degree i = (C.internalNeighbors i.1).card := by
  rw [SimpleGraph.degree]
  apply Finset.card_bij (fun j _ ↦ j.1)
  · intro j hj
    rw [C.mem_internalNeighbors_iff]
    exact ⟨j.2, (C.internalGraph_adj i j).mp
      ((C.internalGraph.mem_neighborFinset i j).mp hj)⟩
  · intro j _ k _ hjk
    exact Subtype.ext hjk
  · intro j hj
    have hjData := (C.mem_internalNeighbors_iff i.1 j).mp hj
    let j' : {i // i ∈ C.vertices} := ⟨j, hjData.1⟩
    refine ⟨j', ?_, rfl⟩
    rw [C.internalGraph.mem_neighborFinset, C.internalGraph_adj]
    exact hjData.2

/-- Walk forward through `n` consecutive edges of a simple `(-2)` path. -/
def SimpleMinusTwoPath.forwardWalk {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (b n : ℕ) (h : b + n ≤ P.length) :
    T.minusTwoGraph.Walk (P.vertex ⟨b, by omega⟩)
      (P.vertex ⟨b + n, by omega⟩) := by
  let f : Fin (n + 1) → T.Component := fun r => P.vertex ⟨b + r.val, by omega⟩
  let l : List T.Component := List.ofFn f
  have hl : l ≠ [] := by simp [l]
  have hchain : l.IsChain T.minusTwoGraph.Adj := by
    change (List.ofFn f).IsChain T.minusTwoGraph.Adj
    rw [List.isChain_ofFn]
    intro i hi
    dsimp [f]
    exact ⟨P.minusTwo _, P.minusTwo _, P.adjacent_nat (b + i) (by omega)⟩
  have W := SimpleGraph.Walk.ofSupport l hl hchain
  refine W.copy ?_ ?_
  · simp [l, f]
  · change (List.ofFn f).getLast _ = P.vertex ⟨b + n, by omega⟩
    rw [List.getLast_ofFn_succ]
    dsimp [f]

@[simp] lemma SimpleMinusTwoPath.length_forwardWalk {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (b n : ℕ) (h : b + n ≤ P.length) :
    (P.forwardWalk b n h).length = n := by
  simp [SimpleMinusTwoPath.forwardWalk]

/-- Walk between any two indices of a simple `(-2)` path. -/
def SimpleMinusTwoPath.walkBetween {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (b s : ℕ) (hb : b ≤ P.length)
    (hs : s ≤ P.length) :
    T.minusTwoGraph.Walk (P.vertex ⟨b, by omega⟩)
      (P.vertex ⟨s, by omega⟩) := by
  by_cases hbs : b ≤ s
  · have W := P.forwardWalk b (s - b) (by omega)
    refine W.copy rfl ?_
    congr
    omega
  · have W := P.forwardWalk s (b - s) (by omega)
    refine W.reverse.copy ?_ rfl
    congr
    omega

@[simp] lemma SimpleMinusTwoPath.length_walkBetween {T : NumericalType}
    (P : T.SimpleMinusTwoPath) (b s : ℕ) (hb : b ≤ P.length)
    (hs : s ≤ P.length) :
    (P.walkBetween b s hb hs).length = b.dist s := by
  unfold SimpleMinusTwoPath.walkBetween
  split
  · rename_i hbs
    simp only [SimpleGraph.Walk.length_copy,
      SimpleMinusTwoPath.length_forwardWalk]
    rw [Nat.dist_eq_sub_of_le hbs]
  · rename_i hbs
    simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse,
      SimpleMinusTwoPath.length_forwardWalk]
    rw [Nat.dist_eq_sub_of_le_right (le_of_not_ge hbs)]

/-- Stacks Project tag `0C9V`, part (1): a minimal type has at most `2g - 2`
non-`(-2)` vertices. -/
lemma nonMinusTwoVertices_card_le (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component) :
    (T.nonMinusTwoVertices.card : ℤ) ≤ 2 * (T.arithmeticGenus - 1) := by
  have htotal := T.sum_twiceComponentContribution
  have hrestrict :
      ∑ i ∈ T.nonMinusTwoVertices, T.twiceComponentContribution i ≤
        ∑ i, T.twiceComponentContribution i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => T.twiceComponentContribution_nonnegative_of_minimal hmin hcard i)
  calc
    (T.nonMinusTwoVertices.card : ℤ) =
        ∑ _i ∈ T.nonMinusTwoVertices, (1 : ℤ) := by simp
    _ ≤ ∑ i ∈ T.nonMinusTwoVertices, T.twiceComponentContribution i := by
      apply Finset.sum_le_sum
      intro i hi
      have hpos := T.twiceComponentContribution_pos_of_nonMinusTwo hmin hcard
        ((T.mem_nonMinusTwoVertices_iff i).mp hi)
      omega
    _ ≤ ∑ i, T.twiceComponentContribution i := hrestrict
    _ = 2 * (T.arithmeticGenus - 1) := htotal

/-- One component contribution is bounded by the entire genus budget. -/
lemma componentContribution_le_total (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component) (i : T.Component) :
    T.twiceComponentContribution i ≤ 2 * (T.arithmeticGenus - 1) := by
  rw [← T.sum_twiceComponentContribution]
  exact Finset.single_le_sum
    (fun j _ => T.twiceComponentContribution_nonnegative_of_minimal hmin hcard j)
    (Finset.mem_univ i)

/-- Stacks Project tag `0C9V`, part (2): the geometric genus decorating a non-`(-2)`
component is strictly smaller than the total arithmetic genus. -/
lemma componentGenus_lt_arithmeticGenus_of_nonMinusTwo (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component) {i : T.Component}
    (hi : ¬ T.IsMinusTwoVertex i) :
    (T.genus i : ℤ) < T.arithmeticGenus := by
  have hpos := T.twiceComponentContribution_pos_of_nonMinusTwo hmin hcard hi
  have hle := T.componentContribution_le_total hmin hcard i
  have hm : 1 ≤ (T.multiplicity i : ℤ) := by
    have : 0 < (T.multiplicity i : ℤ) := by positivity
    omega
  have hw : 1 ≤ (T.weight i : ℤ) := by
    have : 0 < (T.weight i : ℤ) := by positivity
    omega
  have hdiag := T.selfIntersection_neg_of_one_lt_card hcard i
  dsimp [twiceComponentContribution] at hpos hle
  nlinarith [mul_le_mul_of_nonneg_right hm (show 0 ≤ (T.weight i : ℤ) by positivity)]

/-- Stacks Project tag `0C9V`, part (3): the multiplicity-weighted diagonal at a
non-`(-2)` vertex is bounded by `6(g - 1)`. -/
lemma diagonalProduct_le_six_genus_sub_one (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component) {i : T.Component}
    (hi : ¬ T.IsMinusTwoVertex i) :
    (T.multiplicity i : ℤ) * |T.intersection i i| ≤
      6 * (T.arithmeticGenus - 1) := by
  have hdiag := T.selfIntersection_neg_of_one_lt_card hcard i
  have habs : |T.intersection i i| = -T.intersection i i := abs_of_neg hdiag
  rw [habs]
  have hle := T.componentContribution_le_total hmin hcard i
  have hm : 0 < (T.multiplicity i : ℤ) := by positivity
  have hw : 0 < (T.weight i : ℤ) := by positivity
  by_cases hg : T.genus i = 0
  · obtain ⟨k, hk⟩ := T.weight_dvd i i
    have hkneg : k < 0 := by rw [hk] at hdiag; nlinarith
    have hk_ne_one : k ≠ -1 := by
      intro heq
      apply hmin
      refine ⟨i, hg, ?_⟩
      rw [hk, heq]
      ring
    have hk_ne_two : k ≠ -2 := by
      intro heq
      apply hi
      refine ⟨hg, ?_⟩
      rw [hk, heq]
      ring
    have hk_le : k ≤ -3 := by omega
    simp only [twiceComponentContribution, hg, Nat.cast_zero] at hle
    rw [hk]
    nlinarith [mul_pos hm hw]
  · have hgNat : 1 ≤ T.genus i := by omega
    have hgInt : (1 : ℤ) ≤ T.genus i := by exact_mod_cast hgNat
    dsimp [twiceComponentContribution] at hle
    nlinarith [mul_nonneg (le_of_lt hm) (le_of_lt hw)]

/-- Stacks Project tag `0C9U`: along an edge, the entry weighted by the source
multiplicity is controlled by the target's weighted diagonal. -/
lemma edgeProduct_le_diagonalProduct (T : NumericalType) {i j : T.Component}
    (hij : T.intersectionGraph.Adj i j) :
    (T.multiplicity i : ℤ) * T.intersection i j ≤
      (T.multiplicity j : ℤ) * |T.intersection j j| := by
  classical
  have hdiag : T.intersection j j < 0 := by
    have hcard : 1 < Nat.card T.Component := by
      rw [Nat.card_eq_fintype_card, Fintype.one_lt_card_iff]
      exact ⟨i, j, hij.ne⟩
    exact T.selfIntersection_neg_of_one_lt_card hcard j
  rw [abs_of_neg hdiag]
  have hrow := T.fiber_relation j
  have hsumOff :
      ∑ k ∈ Finset.univ.erase j,
          (T.multiplicity k : ℤ) * T.intersection j k =
        -(T.multiplicity j : ℤ) * T.intersection j j := by
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun k => (T.multiplicity k : ℤ) * T.intersection j k) (Finset.mem_univ j)
    rw [hrow] at hsplit
    nlinarith
  have hterm :
      (T.multiplicity i : ℤ) * T.intersection j i ≤
        ∑ k ∈ Finset.univ.erase j,
          (T.multiplicity k : ℤ) * T.intersection j k := by
    apply Finset.single_le_sum
      (s := Finset.univ.erase j)
      (f := fun k => (T.multiplicity k : ℤ) * T.intersection j k)
    · intro k hk
      have hkj : k ≠ j := by simpa using hk
      exact mul_nonneg (by positivity) (T.offDiagonal_nonnegative j k hkj.symm)
    · simp [hij.ne]
  calc
    (T.multiplicity i : ℤ) * T.intersection i j =
        (T.multiplicity i : ℤ) * T.intersection j i := by
      rw [T.intersection_symm i j]
    _ ≤ ∑ k ∈ Finset.univ.erase j,
          (T.multiplicity k : ℤ) * T.intersection j k := hterm
    _ = (T.multiplicity j : ℤ) * -T.intersection j j := by
      rw [hsumOff]
      ring

/-- The second estimate of tag `0C9U`: the source multiplicity times its weight is
controlled by the target's weighted diagonal. -/
lemma vertexMass_le_diagonalProduct (T : NumericalType) {i j : T.Component}
    (hij : T.intersectionGraph.Adj i j) :
    T.vertexMass i ≤ (T.multiplicity j : ℤ) * |T.intersection j j| := by
  have hweight : (T.weight i : ℤ) ≤ T.intersection i j := by
    have hnorm := T.normalizedIntersection_pos_of_adj hij
    have hexact := T.normalizedIntersection_mul_weight i j
    have hw : 0 < (T.weight i : ℤ) := by positivity
    nlinarith
  have hm : 0 ≤ (T.multiplicity i : ℤ) := by positivity
  calc
    T.vertexMass i ≤ (T.multiplicity i : ℤ) * T.intersection i j := by
      dsimp [vertexMass]
      exact mul_le_mul_of_nonneg_left hweight hm
    _ ≤ _ := T.edgeProduct_le_diagonalProduct hij

/-- Multiplicity times the absolute self-intersection. -/
def diagonalProduct (T : NumericalType) (i : T.Component) : ℤ :=
  (T.multiplicity i : ℤ) * |T.intersection i i|

/-- At a `(-2)` vertex, the diagonal product is twice the vertex mass. -/
lemma diagonalProduct_eq_two_vertexMass_of_minusTwo (T : NumericalType)
    {i : T.Component} (hi : T.IsMinusTwoVertex i) :
    T.diagonalProduct i = 2 * T.vertexMass i := by
  dsimp [diagonalProduct, vertexMass]
  rw [hi.2]
  have hw : (0 : ℤ) ≤ (T.weight i : ℤ) := by positivity
  rw [abs_of_nonpos (by nlinarith : -2 * (T.weight i : ℤ) ≤ 0)]
  ring

lemma diagonalProduct_nonnegative (T : NumericalType) (i : T.Component) :
    0 ≤ T.diagonalProduct i := by
  dsimp [diagonalProduct]
  positivity

/-- Crossing an edge into a `(-2)` vertex increases the diagonal bound by at most a
factor of two. -/
lemma diagonalProduct_le_two_mul_of_adj_minusTwo (T : NumericalType)
    {i j : T.Component} (hi : T.IsMinusTwoVertex i)
    (hij : T.intersectionGraph.Adj i j) :
    T.diagonalProduct i ≤ 2 * T.diagonalProduct j := by
  rw [T.diagonalProduct_eq_two_vertexMass_of_minusTwo hi]
  dsimp [diagonalProduct]
  exact mul_le_mul_of_nonneg_left (T.vertexMass_le_diagonalProduct hij) (by norm_num)

/-- A finite edge chain that starts at an arbitrary component and thereafter consists of
`(-2)` vertices. -/
structure MinusTwoChain (T : NumericalType) (source target : T.Component) where
  length : ℕ
  vertex : Fin (length + 1) → T.Component
  source_eq : vertex 0 = source
  target_eq : vertex ⟨length, by omega⟩ = target
  adjacent : ∀ r : Fin length,
    T.intersectionGraph.Adj (vertex r.castSucc) (vertex r.succ)
  minusTwo : ∀ r : Fin length, T.IsMinusTwoVertex (vertex r.succ)

lemma minusTwo_of_getVert_minusTwoWalk (T : NumericalType)
    {start target : T.Component}
    (W : T.minusTwoGraph.Walk start target)
    (hstart : T.IsMinusTwoVertex start) (n : ℕ) :
    T.IsMinusTwoVertex (W.getVert n) := by
  induction W generalizing n with
  | nil => simpa using hstart
  | @cons u v w huv p ih =>
      cases n with
      | zero => exact huv.1
      | succ n =>
          rw [SimpleGraph.Walk.getVert_cons_succ]
          exact ih huv.2.1 n

/-- A simple walk in the `(-2)` graph gives an indexed simple `(-2)` path. -/
def simpleMinusTwoPathOfWalk (T : NumericalType)
    {start target : T.Component}
    (W : T.minusTwoGraph.Walk start target) (hW : W.IsPath)
    (hstart : T.IsMinusTwoVertex start) : T.SimpleMinusTwoPath :=
  { length := W.length
    vertex := fun r => W.getVert r
    injective := by
      intro r s hrs
      apply Fin.ext
      apply hW.getVert_injOn
      · simp only [Set.mem_ofPred_eq]
        omega
      · simp only [Set.mem_ofPred_eq]
        omega
      · exact hrs
    adjacent := by
      intro r
      exact (W.adj_getVert_succ r.isLt).2.2
    minusTwo := by
      intro r
      exact T.minusTwo_of_getVert_minusTwoWalk W hstart r.val }

@[simp] lemma simpleMinusTwoPathOfWalk_vertex_zero (T : NumericalType)
    {start target : T.Component}
    (W : T.minusTwoGraph.Walk start target) (hW : W.IsPath)
    (hstart : T.IsMinusTwoVertex start) :
    (T.simpleMinusTwoPathOfWalk W hW hstart).vertex 0 = start := by
  simp [simpleMinusTwoPathOfWalk]

@[simp] lemma simpleMinusTwoPathOfWalk_vertex_last (T : NumericalType)
    {start target : T.Component}
    (W : T.minusTwoGraph.Walk start target) (hW : W.IsPath)
    (hstart : T.IsMinusTwoVertex start) :
    (T.simpleMinusTwoPathOfWalk W hW hstart).vertex
      ⟨W.length, by change W.length < W.length + 1; omega⟩ = target := by
  change W.getVert W.length = target
  simp

/-- A canonical `(-2)` cluster has at most one internal degree-three vertex.
Two such vertices would supply two extra arms at both ends of their unique
connecting path, hence a forbidden affine `D` configuration. -/
lemma minusTwoClusterAt_degree_three_unique (T : NumericalType)
    (hcard : 5 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    {target : T.Component} (htarget : T.IsMinusTwoVertex target)
    {c d : T.Component}
    (hc : c ∈ (T.minusTwoClusterAt target htarget).vertices)
    (hd : d ∈ (T.minusTwoClusterAt target htarget).vertices)
    (hdegreeC :
      ((T.minusTwoClusterAt target htarget).internalNeighbors c).card = 3)
    (hdegreeD :
      ((T.minusTwoClusterAt target htarget).internalNeighbors d).card = 3) :
    c = d := by
  by_contra hcd
  let C := T.minusTwoClusterAt target htarget
  have hreach : T.minusTwoGraph.Reachable c d :=
    T.minusTwoClusterAt_reachable htarget hc hd
  obtain ⟨W, hW⟩ := hreach.exists_isPath
  have hlen : 0 < W.length := by
    by_contra hzero
    exact hcd (W.eq_of_length_eq_zero (by omega))
  have hWnotnil : ¬ W.Nil := by
    rw [← SimpleGraph.Walk.length_eq_zero_iff]
    omega
  have hacyclic := T.minusTwoGraph_isAcyclic (by omega) hgenus
  have hcnextGraph : T.minusTwoGraph.Adj c W.snd := W.adj_snd hWnotnil
  have hnextMem : W.snd ∈ C.internalNeighbors c := by
    rw [C.mem_internalNeighbors_iff]
    exact ⟨C.closed c hc W.snd hcnextGraph.2.2 hcnextGraph.2.1,
      hcnextGraph.2.2⟩
  have hdprevGraph : T.minusTwoGraph.Adj d W.penultimate :=
    (W.adj_penultimate hWnotnil).symm
  have hprevMem : W.penultimate ∈ C.internalNeighbors d := by
    rw [C.mem_internalNeighbors_iff]
    exact ⟨C.closed d hd W.penultimate hdprevGraph.2.2 hdprevGraph.2.1,
      hdprevGraph.2.2⟩
  obtain ⟨a, b, hab, ha, hb, haNext, hbNext⟩ :=
    C.exists_two_internalNeighbors_away hdegreeC hnextMem
  obtain ⟨x, y, hxy, hx, hy, hxPrev, hyPrev⟩ :=
    C.exists_two_internalNeighbors_away hdegreeD hprevMem
  have haData := (C.mem_internalNeighbors_iff c a).mp ha
  have hbData := (C.mem_internalNeighbors_iff c b).mp hb
  have hxData := (C.mem_internalNeighbors_iff d x).mp hx
  have hyData := (C.mem_internalNeighbors_iff d y).mp hy
  have hcaGraph : T.minusTwoGraph.Adj c a :=
    ⟨C.minusTwo c hc, C.minusTwo a haData.1, haData.2⟩
  have hcbGraph : T.minusTwoGraph.Adj c b :=
    ⟨C.minusTwo c hc, C.minusTwo b hbData.1, hbData.2⟩
  have hdxGraph : T.minusTwoGraph.Adj d x :=
    ⟨C.minusTwo d hd, C.minusTwo x hxData.1, hxData.2⟩
  have hdyGraph : T.minusTwoGraph.Adj d y :=
    ⟨C.minusTwo d hd, C.minusTwo y hyData.1, hyData.2⟩
  have haNot : a ∉ W.support := by
    intro haMem
    exact haNext (hacyclic.eq_snd_of_adj_start hW hcaGraph haMem)
  have hbNot : b ∉ W.support := by
    intro hbMem
    exact hbNext (hacyclic.eq_snd_of_adj_start hW hcbGraph hbMem)
  have hxNot : x ∉ W.support := by
    intro hxMem
    exact hxPrev (hacyclic.eq_penultimate_of_adj_end hW hdxGraph hxMem)
  have hyNot : y ∉ W.support := by
    intro hyMem
    exact hyPrev (hacyclic.eq_penultimate_of_adj_end hW hdyGraph hyMem)
  have cross_ne {z w : T.Component} (hzNot : z ∉ W.support)
      (hcz : T.minusTwoGraph.Adj c z) (hdw : T.minusTwoGraph.Adj d w) :
      z ≠ w := by
    intro hzw
    have hdz : T.minusTwoGraph.Adj d z := by simpa [hzw] using hdw
    have hdc : d ≠ c := Ne.symm hcd
    have hdNot : d ∉ hcz.toWalk.support := by
      simp [hdc, hdz.ne]
    have hzMem := hacyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
      hW hcz.isPath_toWalk hdz hdNot
    exact hzNot hzMem
  have hax : a ≠ x := cross_ne haNot hcaGraph hdxGraph
  have hay : a ≠ y := cross_ne haNot hcaGraph hdyGraph
  have hbx : b ≠ x := cross_ne hbNot hcbGraph hdxGraph
  have hby : b ≠ y := cross_ne hbNot hcbGraph hdyGraph
  let P := T.simpleMinusTwoPathOfWalk W hW (C.minusTwo c hc)
  let side : Fin 4 → T.Component := ![a, b, x, y]
  have hsideInj : Function.Injective side := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [side] at hij ⊢ <;> aesop
  have hpathSide (r : Fin (P.length + 1)) (k : Fin 4) :
      P.vertex r ≠ side k := by
    have hmem : P.vertex r ∈ W.support := by
      dsimp [P, simpleMinusTwoPathOfWalk]
      exact W.getVert_mem_support r.val
    intro heq
    fin_cases k
    · apply haNot
      have heq' : P.vertex r = a := by simpa [side] using heq
      rw [← heq']
      exact hmem
    · apply hbNot
      have heq' : P.vertex r = b := by simpa [side] using heq
      rw [← heq']
      exact hmem
    · apply hxNot
      have heq' : P.vertex r = x := by simpa [side] using heq
      rw [← heq']
      exact hmem
    · apply hyNot
      have heq' : P.vertex r = y := by simpa [side] using heq
      rw [← heq']
      exact hmem
  have hsideMinus : ∀ k, T.IsMinusTwoVertex (side k) := by
    intro k
    fin_cases k
    · exact C.minusTwo a haData.1
    · exact C.minusTwo b hbData.1
    · exact C.minusTwo x hxData.1
    · exact C.minusTwo y hyData.1
  obtain ⟨heart, hheart⟩ :=
    T.exists_nonMinusTwo_of_two_le_arithmeticGenus (by omega) hgenus
  have hproper : ∃ heart, ∀ r, heart ≠ Sum.elim P.vertex side r := by
    refine ⟨heart, ?_⟩
    rintro (r | k) heq
    · apply hheart
      rw [heq]
      exact P.minusTwo r
    · apply hheart
      rw [heq]
      exact hsideMinus k
  have hPlen : 0 < P.length := by
    change 0 < W.length
    exact hlen
  have hPzero : P.vertex 0 = c := by
    change W.getVert 0 = c
    simp
  have hPlast : P.vertex ⟨P.length, by omega⟩ = d := by
    change W.getVert W.length = d
    simp
  apply T.no_doubleFork_subgraph hcard P hPlen side
    (P.injective.sumElim hsideInj hpathSide) hproper hsideMinus
  · simpa [hPzero, side] using haData.2
  · simpa [hPzero, side] using hbData.2
  · simpa [hPlast, side] using hxData.2
  · simpa [hPlast, side] using hyData.2

/-- A closed `(-2)` cluster has a heart-exposed multiplicity maximum if one of its
maximum-multiplicity vertices is adjacent to a non-`(-2)` component. -/
def MinusTwoCluster.HasHeartMaximum {T : NumericalType}
    (C : T.MinusTwoCluster) : Prop :=
  ∃ peak ∈ C.vertices,
    (∀ i ∈ C.vertices, T.multiplicity i ≤ T.multiplicity peak) ∧
      ∃ source, ¬ T.IsMinusTwoVertex source ∧
        T.intersectionGraph.Adj peak source

/-- A closed `(-2)` cluster has a near-heart maximum if a maximum-multiplicity vertex
can be reached from the non-`(-2)` heart in at most four edges. -/
def MinusTwoCluster.HasNearHeartMaximum {T : NumericalType}
    (C : T.MinusTwoCluster) : Prop :=
  ∃ peak ∈ C.vertices,
    (∀ i ∈ C.vertices, T.multiplicity i ≤ T.multiplicity peak) ∧
      ∃ source, ¬ T.IsMinusTwoVertex source ∧
        ∃ chain : T.MinusTwoChain source peak, chain.length ≤ 4

/-- An exact path presentation of a closed `(-2)` cluster. The neighbor condition
excludes chords and records that the displayed consecutive edges are all its internal
edges. -/
structure MinusTwoCluster.PathShape {T : NumericalType}
    (C : T.MinusTwoCluster) where
  path : T.SimpleMinusTwoPath
  length_four : 4 ≤ path.length
  mem_vertices : ∀ r, path.vertex r ∈ C.vertices
  covers : ∀ i ∈ C.vertices, ∃ r, path.vertex r = i
  neighbors : ∀ (r : Fin (path.length + 1)) (i : T.Component),
    T.IsMinusTwoVertex i → T.intersectionGraph.Adj (path.vertex r) i →
      (0 < r.val ∧
        path.vertex ⟨r.val - 1, by have := r.isLt; omega⟩ = i) ∨
      (r.val < path.length ∧ ∃ s : Fin (path.length + 1),
        s.val = r.val + 1 ∧ path.vertex s = i)

/-- A large canonical cluster with no trivalent vertex is exactly a path. -/
lemma minusTwoClusterAt_pathShape_of_no_degree_three (T : NumericalType)
    (hcard : 5 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    {target : T.Component} (htarget : T.IsMinusTwoVertex target)
    (hlarge : 7 < (T.minusTwoClusterAt target htarget).vertices.card)
    (hbranch : ∀ c ∈ (T.minusTwoClusterAt target htarget).vertices,
      ((T.minusTwoClusterAt target htarget).internalNeighbors c).card ≠ 3) :
    Nonempty (T.minusTwoClusterAt target htarget).PathShape := by
  let C := T.minusTwoClusterAt target htarget
  let G := C.internalGraph
  change Nonempty C.PathShape
  let _ : Nonempty {i // i ∈ C.vertices} :=
    ⟨⟨target, by simp [C, minusTwoClusterAt]⟩⟩
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hconn : G.Connected := T.minusTwoClusterAt_internalGraph_connected htarget
  have hdegree : ∀ i, G.degree i ≤ 2 := by
    intro i
    rw [C.degree_internalGraph_eq_card_internalNeighbors]
    have hle := C.internalNeighbors_card_le_three hcard i.2
    have hne : (C.internalNeighbors i.1).card ≠ 3 := by
      simpa [C] using hbranch i.1 i.2
    omega
  have hham : p.IsHamiltonian :=
    maximalPath_isHamiltonian_of_degree_le_two hconn hp hmax hdegree
  let ι : G →g T.minusTwoGraph :=
    (SimpleGraph.Embedding.induce {i | i ∈ C.vertices}).toHom
  let W : T.minusTwoGraph.Walk u.1 v.1 := p.map ι
  have hι : Function.Injective ι := by
    intro i j hij
    exact Subtype.ext hij
  have hW : W.IsPath := hp.map hι
  let P := T.simpleMinusTwoPathOfWalk W hW (C.minusTwo u.1 u.2)
  have hWlength : W.length = p.length := by
    change (p.map ι).length = p.length
    exact p.length_map ι
  have hPlength : P.length = W.length := rfl
  have hPvertex (r : Fin (P.length + 1)) : P.vertex r = W.getVert r.val := rfl
  have hWget (n : ℕ) : W.getVert n = (p.getVert n).1 := by
    change (p.map ι).getVert n = (p.getVert n).1
    rw [SimpleGraph.Walk.getVert_map]
    rfl
  have hlength : 4 ≤ P.length := by
    have hpLength := hham.length_eq
    have hcardEq : Fintype.card {i // i ∈ C.vertices} = C.vertices.card := by
      simp [Fintype.card_coe]
    have hlargeC : 7 < C.vertices.card := by simpa [C] using hlarge
    rw [hPlength, hWlength, hpLength, hcardEq]
    omega
  refine ⟨{
    path := P
    length_four := hlength
    mem_vertices := ?_
    covers := ?_
    neighbors := ?_ }⟩
  · intro r
    rw [hPvertex, hWget]
    exact (p.getVert r.val).2
  · intro i hi
    have hiSupport : (⟨i, hi⟩ : {i // i ∈ C.vertices}) ∈ p.support :=
      hham.mem_support ⟨i, hi⟩
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hiSupport
    let r : Fin (P.length + 1) := ⟨n, by
      rw [hPlength, hWlength]
      omega⟩
    refine ⟨r, ?_⟩
    rw [hPvertex, hWget]
    exact congrArg Subtype.val hn
  · intro r i hi hadj
    have hrMem : P.vertex r ∈ C.vertices := by
      rw [hPvertex, hWget]
      exact (p.getVert r.val).2
    have hiMem : i ∈ C.vertices := C.closed (P.vertex r) hrMem i hadj hi
    have hiSupport : (⟨i, hiMem⟩ : {i // i ∈ C.vertices}) ∈ p.support :=
      hham.mem_support ⟨i, hiMem⟩
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hiSupport
    have hadjW : T.minusTwoGraph.Adj (W.getVert r.val) (W.getVert n) := by
      rw [← hPvertex r, hWget, hn]
      exact ⟨P.minusTwo r, hi, hadj⟩
    have hindices := index_adjacent_of_isAcyclic
      (T.minusTwoGraph_isAcyclic (by omega) hgenus) hW r.val n
      (by
        calc
          r.val ≤ P.length := by omega
          _ = W.length := hPlength)
      (by rw [hWlength]; exact hnle) hadjW
    rcases hindices with hprev | hnext
    · left
      refine ⟨by omega, ?_⟩
      change W.getVert (r.val - 1) = i
      rw [show r.val - 1 = n by omega, hWget]
      exact congrArg Subtype.val hn
    · right
      have hnleP : n ≤ P.length := by
        calc
          n ≤ p.length := hnle
          _ = W.length := hWlength.symm
          _ = P.length := hPlength.symm
      refine ⟨by omega, ?_⟩
      let s : Fin (P.length + 1) := ⟨n, by
        rw [hPlength, hWlength]
        omega⟩
      refine ⟨s, by simpa [s] using hnext, ?_⟩
      change W.getVert n = i
      rw [hWget]
      exact congrArg Subtype.val hn

lemma MinusTwoCluster.PathShape.left_endpoint_neighbor_eq {T : NumericalType}
    {C : T.MinusTwoCluster} (S : C.PathShape) {i : T.Component}
    (hi : T.IsMinusTwoVertex i)
    (hadj : T.intersectionGraph.Adj (S.path.vertex 0) i) :
    i = S.path.vertex ⟨1, by have := S.length_four; omega⟩ := by
  rcases S.neighbors (0 : Fin (S.path.length + 1)) i hi hadj with h | h
  · have : ¬ (0 : ℕ) < 0 := by omega
    exact (this h.1).elim
  · obtain ⟨s, hs, hsi⟩ := h.2
    have hs' : s = ⟨1, by have := S.length_four; omega⟩ := by ext; simpa using hs
    rw [← hs']
    exact hsi.symm

lemma MinusTwoCluster.PathShape.right_endpoint_neighbor_eq {T : NumericalType}
    {C : T.MinusTwoCluster} (S : C.PathShape) {i : T.Component}
    (hi : T.IsMinusTwoVertex i)
    (hadj : T.intersectionGraph.Adj
      (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩) i) :
    i = S.path.vertex ⟨S.path.length - 1, by omega⟩ := by
  rcases S.neighbors ⟨S.path.length, Nat.lt_succ_self _⟩ i hi hadj with h | h
  · exact h.2.symm
  · exact (Nat.lt_irrefl _ h.1).elim

lemma MinusTwoCluster.PathShape.internal_neighbor_eq {T : NumericalType}
    {C : T.MinusTwoCluster} (S : C.PathShape) (r : ℕ)
    (hrleft : 0 < r) (hrright : r < S.path.length) {i : T.Component}
    (hi : T.IsMinusTwoVertex i)
    (hadj : T.intersectionGraph.Adj (S.path.vertex ⟨r, by omega⟩) i) :
    i = S.path.vertex ⟨r - 1, by omega⟩ ∨
      i = S.path.vertex ⟨r + 1, by omega⟩ := by
  rcases S.neighbors ⟨r, by omega⟩ i hi hadj with h | h
  · exact Or.inl h.2.symm
  · obtain ⟨s, hs, hsi⟩ := h.2
    have hs' : s = ⟨r + 1, by omega⟩ := by ext; simpa using hs
    right
    rw [← hs']
    exact hsi.symm

/-- At a central maximum of an exact long path, absence of a heart edge propagates the
maximum to both neighboring vertices. -/
lemma MinusTwoCluster.PathShape.central_neighbors_eq_of_maximum_no_heart
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.PathShape)
    (hcard : 5 < Nat.card T.Component) (s : ℕ)
    (hsleft : 1 < s) (hsright : s + 1 < S.path.length)
    (hmax : ∀ i ∈ C.vertices,
      T.multiplicity i ≤ T.multiplicity (S.path.vertex ⟨s, by omega⟩))
    (hnoHeart : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj (S.path.vertex ⟨s, by omega⟩) source) :
    T.multiplicity (S.path.vertex ⟨s - 1, by omega⟩) =
        T.multiplicity (S.path.vertex ⟨s, by omega⟩) ∧
      T.multiplicity (S.path.vertex ⟨s + 1, by omega⟩) =
        T.multiplicity (S.path.vertex ⟨s, by omega⟩) := by
  let left := S.path.vertex ⟨s - 1, by omega⟩
  let peak := S.path.vertex ⟨s, by omega⟩
  let right := S.path.vertex ⟨s + 1, by omega⟩
  have hleftAdj : T.intersectionGraph.Adj peak left := by
    dsimp [peak, left]
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ s)] using
      (S.path.adjacent_nat (s - 1) (by omega)).symm
  have hrightAdj : T.intersectionGraph.Adj peak right := by
    dsimp [peak, right]
    exact S.path.adjacent_nat s (by omega)
  have hleftProd : T.edgeIndexProduct peak left = 1 := by
    have hsPrevPos : 0 < s - 1 := by omega
    have hsPrevLast : (s - 1) + 1 < S.path.length := by omega
    rw [T.edgeIndexProduct_symm]
    have h := S.path.interior_edgeIndexProduct_eq_one hcard S.length_four
      (s - 1) hsPrevPos hsPrevLast
    simpa [SimpleMinusTwoPath.edgeIndexProductAt, left, peak,
      Nat.sub_add_cancel (by omega : 1 ≤ s)] using h
  have hrightProd : T.edgeIndexProduct peak right = 1 := by
    convert S.path.interior_edgeIndexProduct_eq_one hcard S.length_four
      s (by omega) (by omega) using 1
    all_goals congr
  have hleftNorm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one hleftAdj hleftProd).1
  have hrightNorm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one hrightAdj hrightProd).1
  have hneighbors : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj peak r → r = left ∨ r = right := by
    intro r hr hadj
    simpa [peak, left, right] using S.internal_neighbor_eq s (by omega) (by omega) hr hadj
  have hbalance :
      (T.multiplicity left : ℤ) * T.normalizedIntersection peak left +
          (T.multiplicity right : ℤ) * T.normalizedIntersection peak right =
        2 * (T.multiplicity peak : ℤ) :=
    T.normalized_two_neighbor_balance_eq_of_no_heart
    (S.path.minusTwo ⟨s, by omega⟩) hleftAdj hrightAdj
    (by
      dsimp [left, right]
      intro heq
      have hfin := S.path.injective heq
      have hval := congrArg Fin.val hfin
      change s - 1 = s + 1 at hval
      omega)
    hneighbors hnoHeart
  rw [hleftNorm, hrightNorm] at hbalance
  have hleftMax : T.multiplicity left ≤ T.multiplicity peak := by
    simpa [peak] using hmax left (by dsimp [left]; exact S.mem_vertices _)
  have hrightMax : T.multiplicity right ≤ T.multiplicity peak := by
    simpa [peak] using hmax right (by dsimp [right]; exact S.mem_vertices _)
  have hleftMaxInt : (T.multiplicity left : ℤ) ≤ T.multiplicity peak := by
    exact_mod_cast hleftMax
  have hrightMaxInt : (T.multiplicity right : ℤ) ≤ T.multiplicity peak := by
    exact_mod_cast hrightMax
  constructor
  · exact_mod_cast (by omega : (T.multiplicity left : ℤ) = T.multiplicity peak)
  · exact_mod_cast (by omega : (T.multiplicity right : ℤ) = T.multiplicity peak)

/-- A finite nonempty `(-2)` cluster has a vertex of maximum multiplicity. -/
lemma MinusTwoCluster.exists_multiplicity_maximum {T : NumericalType}
    (C : T.MinusTwoCluster) :
    ∃ peak ∈ C.vertices,
      ∀ i ∈ C.vertices, T.multiplicity i ≤ T.multiplicity peak := by
  exact Finset.exists_max_image C.vertices T.multiplicity C.nonempty

/-- Two known internal neighbors exhaust an internal neighbor set of cardinality at
most two. -/
lemma MinusTwoCluster.minusTwo_neighbor_eq_of_card_le_two {T : NumericalType}
    (C : T.MinusTwoCluster) {c i k : T.Component}
    (hc : c ∈ C.vertices) (hi : T.IsMinusTwoVertex i)
    (hk : T.IsMinusTwoVertex k) (hci : T.intersectionGraph.Adj c i)
    (hck : T.intersectionGraph.Adj c k) (hik : i ≠ k)
    (hdegree : (C.internalNeighbors c).card ≤ 2) {r : T.Component}
    (hr : T.IsMinusTwoVertex r) (hcr : T.intersectionGraph.Adj c r) :
    r = i ∨ r = k := by
  have hiMem : i ∈ C.vertices := C.closed c hc i hci hi
  have hkMem : k ∈ C.vertices := C.closed c hc k hck hk
  have hiInternal : i ∈ C.internalNeighbors c :=
    (C.mem_internalNeighbors_iff c i).mpr ⟨hiMem, hci⟩
  have hkInternal : k ∈ C.internalNeighbors c :=
    (C.mem_internalNeighbors_iff c k).mpr ⟨hkMem, hck⟩
  have hsubset : ({i, k} : Finset T.Component) ⊆ C.internalNeighbors c := by
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      ⟨hiInternal, hkInternal⟩
  have heq : ({i, k} : Finset T.Component) = C.internalNeighbors c := by
    apply Finset.eq_of_subset_of_card_le hsubset
    simpa [hik] using hdegree
  have hrMem : r ∈ C.vertices := C.closed c hc r hcr hr
  have hrInternal : r ∈ C.internalNeighbors c :=
    (C.mem_internalNeighbors_iff c r).mpr ⟨hrMem, hcr⟩
  rw [← heq] at hrInternal
  simpa [hik] using hrInternal

/-- A cluster on which all multiplicities are equal has a heart-exposed maximum. -/
lemma MinusTwoCluster.hasHeartMaximum_of_constant_multiplicity {T : NumericalType}
    (C : T.MinusTwoCluster) (hcard : 1 < Nat.card T.Component)
    (hgenus : 2 ≤ T.arithmeticGenus) (m : ℕ+)
    (hm : ∀ i ∈ C.vertices, T.multiplicity i = m) : C.HasHeartMaximum := by
  obtain ⟨peak, hpeak, source, hsource, hadj⟩ := C.meets_heart hcard hgenus
  refine ⟨peak, hpeak, ?_, source, hsource, hadj⟩
  intro i hi
  rw [hm i hi, hm peak hpeak]

/-- A maximum with a strict deficit between its two unit-index cluster neighbors is
heart-exposed. -/
lemma MinusTwoCluster.hasHeartMaximum_of_strict_unit_neighbors {T : NumericalType}
    (C : T.MinusTwoCluster) {peak i k : T.Component}
    (hpeak : peak ∈ C.vertices)
    (hmax : ∀ r ∈ C.vertices, T.multiplicity r ≤ T.multiplicity peak)
    (hi : T.IsMinusTwoVertex i) (hk : T.IsMinusTwoVertex k)
    (hpi : T.intersectionGraph.Adj peak i)
    (hpk : T.intersectionGraph.Adj peak k) (hik : i ≠ k)
    (hleft : T.edgeIndexProduct peak i = 1)
    (hright : T.edgeIndexProduct peak k = 1)
    (hdegree : (C.internalNeighbors peak).card ≤ 2)
    (hstrict : (T.multiplicity i : ℤ) + (T.multiplicity k : ℤ) <
      2 * (T.multiplicity peak : ℤ)) : C.HasHeartMaximum := by
  obtain ⟨source, hsource, hadj⟩ :=
    T.exists_heart_neighbor_of_strict_unit_neighbors (C.minusTwo peak hpeak)
      hpi hpk hik hleft hright hstrict (fun r hr hpr =>
        C.minusTwo_neighbor_eq_of_card_le_two hpeak hi hk hpi hpk hik hdegree hr hpr)
  exact ⟨peak, hpeak, hmax, source, hsource, hadj⟩

/-- At a maximum with two unit-index cluster neighbors, absence of a heart edge forces
both neighbors to have the same maximum multiplicity. -/
lemma MinusTwoCluster.neighbor_multiplicities_eq_of_maximum_unit_neighbors
    {T : NumericalType} (C : T.MinusTwoCluster) {peak i k : T.Component}
    (hpeak : peak ∈ C.vertices)
    (hmax : ∀ r ∈ C.vertices, T.multiplicity r ≤ T.multiplicity peak)
    (hi : T.IsMinusTwoVertex i) (hk : T.IsMinusTwoVertex k)
    (hpi : T.intersectionGraph.Adj peak i)
    (hpk : T.intersectionGraph.Adj peak k) (hik : i ≠ k)
    (hleft : T.edgeIndexProduct peak i = 1)
    (hright : T.edgeIndexProduct peak k = 1)
    (hdegree : (C.internalNeighbors peak).card ≤ 2)
    (hnoHeart : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj peak source) :
    T.multiplicity i = T.multiplicity peak ∧
      T.multiplicity k = T.multiplicity peak := by
  have hiMem := C.closed peak hpeak i hpi hi
  have hkMem := C.closed peak hpeak k hpk hk
  have himax := hmax i hiMem
  have hkmax := hmax k hkMem
  have hnotStrict : ¬ ((T.multiplicity i : ℤ) + (T.multiplicity k : ℤ) <
      2 * (T.multiplicity peak : ℤ)) := by
    intro hstrict
    obtain ⟨source, hsource, hadj⟩ :=
      T.exists_heart_neighbor_of_strict_unit_neighbors (C.minusTwo peak hpeak)
        hpi hpk hik hleft hright hstrict (fun r hr hpr =>
          C.minusTwo_neighbor_eq_of_card_le_two hpeak hi hk hpi hpk hik hdegree hr hpr)
    exact hnoHeart source hsource hadj
  have hiInt : (T.multiplicity i : ℤ) ≤ T.multiplicity peak := by exact_mod_cast himax
  have hkInt : (T.multiplicity k : ℤ) ≤ T.multiplicity peak := by exact_mod_cast hkmax
  have heqs :
      (T.multiplicity i : ℤ) = T.multiplicity peak ∧
        (T.multiplicity k : ℤ) = T.multiplicity peak := by omega
  constructor
  · exact_mod_cast heqs.1
  · exact_mod_cast heqs.2

/-- At an endpoint maximum with a unique `(-2)` neighbor and normalized index at most
two, absence of a heart edge forces that neighbor to have the same multiplicity. -/
lemma MinusTwoCluster.neighbor_multiplicity_eq_of_maximum_single_neighbor
    {T : NumericalType} (C : T.MinusTwoCluster) {peak i : T.Component}
    (hpeak : peak ∈ C.vertices)
    (hmax : ∀ r ∈ C.vertices, T.multiplicity r ≤ T.multiplicity peak)
    (hi : T.IsMinusTwoVertex i) (hpi : T.intersectionGraph.Adj peak i)
    (hnormle : T.normalizedIntersection peak i ≤ 2)
    (hneighbors : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj peak r → r = i)
    (hnoHeart : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj peak source) :
    T.multiplicity i = T.multiplicity peak := by
  have hiMem := C.closed peak hpeak i hpi hi
  have himax := hmax i hiMem
  have himaxInt : (T.multiplicity i : ℤ) ≤ T.multiplicity peak := by exact_mod_cast himax
  have hqpos := T.normalizedIntersection_pos_of_adj hpi
  have htermLe :
      (T.multiplicity i : ℤ) * T.normalizedIntersection peak i ≤
        2 * (T.multiplicity peak : ℤ) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ T.multiplicity i by positivity)
      (le_of_lt hqpos)]
  have hnotStrict : ¬ ((T.multiplicity i : ℤ) *
      T.normalizedIntersection peak i < 2 * (T.multiplicity peak : ℤ)) := by
    intro hstrict
    obtain ⟨source, hsource, hadj⟩ :=
      T.exists_heart_neighbor_of_strict_single_neighbor
        (C.minusTwo peak hpeak) hpi hstrict hneighbors
    exact hnoHeart source hsource hadj
  have htermEq : (T.multiplicity i : ℤ) * T.normalizedIntersection peak i =
      2 * (T.multiplicity peak : ℤ) := by omega
  have hq : T.normalizedIntersection peak i = 1 ∨
      T.normalizedIntersection peak i = 2 := by omega
  rcases hq with hq | hq
  · rw [hq] at htermEq
    have hpeakPos : (0 : ℤ) < T.multiplicity peak := by positivity
    omega
  · rw [hq] at htermEq
    exact_mod_cast (by omega : (T.multiplicity i : ℤ) = T.multiplicity peak)

/-- A maximum at the left endpoint of an exact long path propagates one step inward
unless that endpoint meets the heart. -/
lemma MinusTwoCluster.PathShape.left_neighbor_eq_of_endpoint_maximum_no_heart
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.PathShape)
    (hcard : 5 < Nat.card T.Component)
    (hmax : ∀ i ∈ C.vertices,
      T.multiplicity i ≤ T.multiplicity (S.path.vertex 0))
    (hnoHeart : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj (S.path.vertex 0) source) :
    T.multiplicity (S.path.vertex ⟨1, by have := S.length_four; omega⟩) =
      T.multiplicity (S.path.vertex 0) := by
  let endpoint := S.path.vertex 0
  let next := S.path.vertex ⟨1, by have := S.length_four; omega⟩
  have hadj : T.intersectionGraph.Adj endpoint next := by
    dsimp [endpoint, next]
    exact S.path.adjacent_nat 0 (by have := S.length_four; omega)
  have hprodLe : T.edgeIndexProduct endpoint next ≤ 2 := by
    have hp := S.path.first_edgeIndexProduct_eq_one_or_two hcard S.length_four
    have hpLe : S.path.edgeIndexProductAt
        ⟨0, by have := S.length_four; omega⟩ ≤ 2 := by
      rcases hp with hp | hp <;> omega
    change T.edgeIndexProduct (S.path.vertex 0)
      (S.path.vertex ⟨1, by have := S.length_four; omega⟩) ≤ 2 at hpLe
    simpa [endpoint, next] using hpLe
  have hforwardPos := T.normalizedIntersection_pos_of_adj hadj
  have hrevPos := T.normalizedIntersection_pos_of_adj hadj.symm
  have hnormLe : T.normalizedIntersection endpoint next ≤ 2 := by
    dsimp [edgeIndexProduct] at hprodLe
    nlinarith
  apply C.neighbor_multiplicity_eq_of_maximum_single_neighbor
    (S.mem_vertices 0) (by simpa [endpoint] using hmax)
    (S.path.minusTwo ⟨1, by have := S.length_four; omega⟩) hadj hnormLe
  · intro r hr hendpoint
    exact S.left_endpoint_neighbor_eq hr hendpoint
  · exact hnoHeart

/-- A maximum at the right endpoint of an exact long path propagates one step inward
unless that endpoint meets the heart. -/
lemma MinusTwoCluster.PathShape.right_neighbor_eq_of_endpoint_maximum_no_heart
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.PathShape)
    (hcard : 5 < Nat.card T.Component)
    (hmax : ∀ i ∈ C.vertices,
      T.multiplicity i ≤
        T.multiplicity (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩))
    (hnoHeart : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj
        (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩) source) :
    T.multiplicity (S.path.vertex
      ⟨S.path.length - 1, by have := S.length_four; omega⟩) =
      T.multiplicity (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩) := by
  let endpoint := S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩
  let prev := S.path.vertex
    ⟨S.path.length - 1, by have := S.length_four; omega⟩
  have hadj : T.intersectionGraph.Adj endpoint prev := by
    dsimp [endpoint, prev]
    simpa [Nat.sub_add_cancel (by have := S.length_four; omega : 1 ≤ S.path.length)] using
      (S.path.adjacent_nat (S.path.length - 1)
        (by have := S.length_four; omega)).symm
  have hprodLe : T.edgeIndexProduct endpoint prev ≤ 2 := by
    have hp := S.path.last_edgeIndexProduct_eq_one_or_two hcard S.length_four
    have hpLe : S.path.edgeIndexProductAt
        ⟨S.path.length - 1, by have := S.length_four; omega⟩ ≤ 2 := by
      rcases hp with hp | hp <;> omega
    calc
      T.edgeIndexProduct endpoint prev = T.edgeIndexProduct prev endpoint :=
        T.edgeIndexProduct_symm endpoint prev
      _ ≤ 2 := by
        change T.edgeIndexProduct
          (S.path.vertex ⟨S.path.length - 1, by have := S.length_four; omega⟩)
          (S.path.vertex ⟨S.path.length - 1 + 1,
            by have := S.length_four; omega⟩) ≤ 2 at hpLe
        change T.edgeIndexProduct
          (S.path.vertex ⟨S.path.length - 1, by have := S.length_four; omega⟩)
          (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩) ≤ 2
        have hfin :
            (⟨S.path.length - 1 + 1,
              by have := S.length_four; omega⟩ : Fin (S.path.length + 1)) =
              ⟨S.path.length, Nat.lt_succ_self _⟩ := by
          apply Fin.ext
          exact Nat.sub_add_cancel (by have := S.length_four; omega)
        rw [hfin] at hpLe
        exact hpLe
  have hrevPos := T.normalizedIntersection_pos_of_adj hadj.symm
  have hforwardPos := T.normalizedIntersection_pos_of_adj hadj
  have hnormLe : T.normalizedIntersection endpoint prev ≤ 2 := by
    dsimp [edgeIndexProduct] at hprodLe
    nlinarith
  apply C.neighbor_multiplicity_eq_of_maximum_single_neighbor
    (S.mem_vertices ⟨S.path.length, Nat.lt_succ_self _⟩)
    (by simpa [endpoint] using hmax) (S.path.minusTwo
      ⟨S.path.length - 1, by have := S.length_four; omega⟩)
    hadj hnormLe
  · intro r hr hendpoint
    exact S.right_endpoint_neighbor_eq hr hendpoint
  · exact hnoHeart

/-- If the second vertex is maximal and neither it nor the left endpoint meets the
heart, the maximum propagates to the third vertex. This handles the possible doubled
first edge in a long `B/C` path. -/
lemma MinusTwoCluster.PathShape.second_neighbor_eq_of_maximum_no_heart
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.PathShape)
    (hcard : 5 < Nat.card T.Component)
    (hmax : ∀ i ∈ C.vertices,
      T.multiplicity i ≤ T.multiplicity
        (S.path.vertex ⟨1, by have := S.length_four; omega⟩))
    (hnoHeartSecond : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj
        (S.path.vertex ⟨1, by have := S.length_four; omega⟩) source)
    (hnoHeartEndpoint : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj (S.path.vertex 0) source) :
    T.multiplicity (S.path.vertex
        ⟨2, by have := S.length_four; omega⟩) =
      T.multiplicity (S.path.vertex
        ⟨1, by have := S.length_four; omega⟩) := by
  let v0 := S.path.vertex 0
  let v1 := S.path.vertex ⟨1, by have := S.length_four; omega⟩
  let v2 := S.path.vertex ⟨2, by have := S.length_four; omega⟩
  change T.multiplicity v2 = T.multiplicity v1
  have h01 : T.intersectionGraph.Adj v0 v1 := by
    dsimp [v0, v1]
    exact S.path.adjacent_nat 0 (by have := S.length_four; omega)
  have h12 : T.intersectionGraph.Adj v1 v2 := by
    dsimp [v1, v2]
    exact S.path.adjacent_nat 1 (by have := S.length_four; omega)
  have h12prod : T.edgeIndexProduct v1 v2 = 1 := by
    have h := S.path.interior_edgeIndexProduct_eq_one hcard S.length_four
      1 (by omega) (by have := S.length_four; omega)
    simpa [SimpleMinusTwoPath.edgeIndexProductAt, v1, v2] using h
  have h12norm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one h12 h12prod).1
  have hneighbors0 : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj v0 r → r = v1 := by
    intro r hr hadj
    simpa [v0, v1] using S.left_endpoint_neighbor_eq hr hadj
  have hneighbors1 : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj v1 r → r = v0 ∨ r = v2 := by
    intro r hr hadj
    simpa [v0, v1, v2] using S.internal_neighbor_eq 1 (by omega)
      (by have := S.length_four; omega) hr hadj
  have hbalance0 := T.normalized_single_neighbor_balance_eq_of_no_heart
    (S.path.minusTwo 0) h01 hneighbors0 hnoHeartEndpoint
  change (T.multiplicity v1 : ℤ) * T.normalizedIntersection v0 v1 =
    2 * (T.multiplicity v0 : ℤ) at hbalance0
  have hv0v2 : v0 ≠ v2 := by
    dsimp [v0, v2]
    exact S.path.injective.ne (by
      intro h
      have h' := congrArg Fin.val h
      change (0 : ℕ) = 2 at h'
      omega)
  have hbalance1 := T.normalized_two_neighbor_balance_eq_of_no_heart
    (S.path.minusTwo ⟨1, by have := S.length_four; omega⟩) h01.symm h12 hv0v2
    hneighbors1 hnoHeartSecond
  change (T.multiplicity v0 : ℤ) * T.normalizedIntersection v1 v0 +
    (T.multiplicity v2 : ℤ) * T.normalizedIntersection v1 v2 =
      2 * (T.multiplicity v1 : ℤ) at hbalance1
  rw [h12norm] at hbalance1
  have hmax0 : (T.multiplicity v0 : ℤ) ≤ T.multiplicity v1 := by
    exact_mod_cast (show T.multiplicity v0 ≤ T.multiplicity v1 by
      simpa [v1] using hmax v0 (by dsimp [v0]; exact S.mem_vertices 0))
  have hmax2 : (T.multiplicity v2 : ℤ) ≤ T.multiplicity v1 := by
    exact_mod_cast (show T.multiplicity v2 ≤ T.multiplicity v1 by
      simpa [v1] using hmax v2 (by dsimp [v2]; exact S.mem_vertices _))
  have hp := S.path.first_edgeIndexProduct_eq_one_or_two hcard S.length_four
  have hclass := T.edgeIndex_pair_classification (by omega)
    (S.path.minusTwo 0) (S.path.minusTwo
      ⟨1, by have := S.length_four; omega⟩) h01
  rcases hclass with hclass | hclass | hclass | hclass | hclass
  · rw [hclass.1] at hbalance0
    rw [hclass.2] at hbalance1
    have hm0 : (0 : ℤ) < T.multiplicity v0 := by positivity
    have hm2 : (0 : ℤ) < T.multiplicity v2 := by positivity
    nlinarith
  · rw [hclass.1] at hbalance0
    rw [hclass.2] at hbalance1
    exact_mod_cast (by omega : (T.multiplicity v2 : ℤ) = T.multiplicity v1)
  · rw [hclass.1] at hbalance0
    rw [hclass.2] at hbalance1
    exact_mod_cast (by omega : (T.multiplicity v2 : ℤ) = T.multiplicity v1)
  · have hpbad : S.path.edgeIndexProductAt
        ⟨0, by have := S.length_four; omega⟩ = 3 := by
      change T.edgeIndexProduct v0 v1 = 3
      dsimp [edgeIndexProduct]
      rw [hclass.1, hclass.2]
      norm_num
    rcases hp with hp | hp <;> omega
  · have hpbad : S.path.edgeIndexProductAt
        ⟨0, by have := S.length_four; omega⟩ = 3 := by
      change T.edgeIndexProduct v0 v1 = 3
      dsimp [edgeIndexProduct]
      rw [hclass.1, hclass.2]
      norm_num
    rcases hp with hp | hp <;> omega

/-- Symmetrically, if the penultimate vertex is maximal and neither it nor the right
endpoint meets the heart, the maximum propagates one step left. -/
lemma MinusTwoCluster.PathShape.penultimate_neighbor_eq_of_maximum_no_heart
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.PathShape)
    (hcard : 5 < Nat.card T.Component)
    (hmax : ∀ i ∈ C.vertices,
      T.multiplicity i ≤ T.multiplicity
        (S.path.vertex ⟨S.path.length - 1,
          by have := S.length_four; omega⟩))
    (hnoHeartPenultimate : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj
        (S.path.vertex ⟨S.path.length - 1,
          by have := S.length_four; omega⟩) source)
    (hnoHeartEndpoint : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj
        (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩) source) :
    T.multiplicity (S.path.vertex
        ⟨S.path.length - 2, by have := S.length_four; omega⟩) =
      T.multiplicity (S.path.vertex
        ⟨S.path.length - 1, by have := S.length_four; omega⟩) := by
  let v0 := S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩
  let v1 := S.path.vertex
    ⟨S.path.length - 1, by have := S.length_four; omega⟩
  let v2 := S.path.vertex
    ⟨S.path.length - 2, by have := S.length_four; omega⟩
  have hstep : S.path.length - 2 + 1 = S.path.length - 1 := by
    have := S.length_four
    omega
  have hback : S.path.length - 1 - 1 = S.path.length - 2 := by
    have := S.length_four
    omega
  have hlast : S.path.length - 1 + 1 = S.path.length := by
    exact Nat.sub_add_cancel (by have := S.length_four; omega)
  change T.multiplicity v2 = T.multiplicity v1
  have h01 : T.intersectionGraph.Adj v0 v1 := by
    dsimp [v0, v1]
    simpa [Nat.sub_add_cancel
      (by have := S.length_four; omega : 1 ≤ S.path.length)] using
      (S.path.adjacent_nat (S.path.length - 1)
        (by have := S.length_four; omega)).symm
  have h12 : T.intersectionGraph.Adj v1 v2 := by
    dsimp [v1, v2]
    have hadj := (S.path.adjacent_nat (S.path.length - 2)
      (by have := S.length_four; omega)).symm
    simpa [hstep] using hadj
  have h12prod : T.edgeIndexProduct v1 v2 = 1 := by
    rw [T.edgeIndexProduct_symm]
    have h := S.path.interior_edgeIndexProduct_eq_one hcard S.length_four
      (S.path.length - 2) (by have := S.length_four; omega)
      (by have := S.length_four; omega)
    simpa [SimpleMinusTwoPath.edgeIndexProductAt, v1, v2, hstep] using h
  have h12norm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one h12 h12prod).1
  have hneighbors0 : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj v0 r → r = v1 := by
    intro r hr hadj
    simpa [v0, v1] using S.right_endpoint_neighbor_eq hr hadj
  have hneighbors1 : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj v1 r → r = v0 ∨ r = v2 := by
    intro r hr hadj
    rcases S.internal_neighbor_eq (S.path.length - 1)
      (by have := S.length_four; omega) (by have := S.length_four; omega) hr
      (by simpa [v1] using hadj) with h | h
    · exact Or.inr (by simpa [v2, hback] using h)
    · exact Or.inl (by
        simpa [v0, Nat.sub_add_cancel
          (by have := S.length_four; omega : 1 ≤ S.path.length)] using h)
  have hbalance0 := T.normalized_single_neighbor_balance_eq_of_no_heart
    (S.path.minusTwo ⟨S.path.length, Nat.lt_succ_self _⟩) h01 hneighbors0
    hnoHeartEndpoint
  change (T.multiplicity v1 : ℤ) * T.normalizedIntersection v0 v1 =
    2 * (T.multiplicity v0 : ℤ) at hbalance0
  have hv0v2 : v0 ≠ v2 := by
    dsimp [v0, v2]
    exact S.path.injective.ne (by
      intro h
      have h' := congrArg Fin.val h
      change S.path.length = S.path.length - 2 at h'
      have := S.length_four
      omega)
  have hbalance1 := T.normalized_two_neighbor_balance_eq_of_no_heart
    (S.path.minusTwo ⟨S.path.length - 1,
      by have := S.length_four; omega⟩) h01.symm h12 hv0v2 hneighbors1
    hnoHeartPenultimate
  change (T.multiplicity v0 : ℤ) * T.normalizedIntersection v1 v0 +
    (T.multiplicity v2 : ℤ) * T.normalizedIntersection v1 v2 =
      2 * (T.multiplicity v1 : ℤ) at hbalance1
  rw [h12norm] at hbalance1
  have hmax0 : (T.multiplicity v0 : ℤ) ≤ T.multiplicity v1 := by
    exact_mod_cast (show T.multiplicity v0 ≤ T.multiplicity v1 by
      simpa [v1] using hmax v0 (by dsimp [v0]; exact S.mem_vertices _))
  have hmax2 : (T.multiplicity v2 : ℤ) ≤ T.multiplicity v1 := by
    exact_mod_cast (show T.multiplicity v2 ≤ T.multiplicity v1 by
      simpa [v1] using hmax v2 (by dsimp [v2]; exact S.mem_vertices _))
  have hp := S.path.last_edgeIndexProduct_eq_one_or_two hcard S.length_four
  have hp' : T.edgeIndexProduct v1 v0 = 1 ∨ T.edgeIndexProduct v1 v0 = 2 := by
    change T.edgeIndexProduct
      (S.path.vertex ⟨S.path.length - 1, by have := S.length_four; omega⟩)
      (S.path.vertex ⟨S.path.length - 1 + 1,
        by have := S.length_four; omega⟩) = 1 ∨
      T.edgeIndexProduct
        (S.path.vertex ⟨S.path.length - 1, by have := S.length_four; omega⟩)
        (S.path.vertex ⟨S.path.length - 1 + 1,
          by have := S.length_four; omega⟩) = 2 at hp
    have hfin :
        (⟨S.path.length - 1 + 1,
          by have := S.length_four; omega⟩ : Fin (S.path.length + 1)) =
          ⟨S.path.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      exact hlast
    rw [hfin] at hp
    exact hp
  have hclass := T.edgeIndex_pair_classification (by omega)
    (S.path.minusTwo ⟨S.path.length, Nat.lt_succ_self _⟩)
    (S.path.minusTwo ⟨S.path.length - 1,
      by have := S.length_four; omega⟩) h01
  rcases hclass with hclass | hclass | hclass | hclass | hclass
  · rw [hclass.1] at hbalance0
    rw [hclass.2] at hbalance1
    have hm0 : (0 : ℤ) < T.multiplicity v0 := by positivity
    have hm2 : (0 : ℤ) < T.multiplicity v2 := by positivity
    nlinarith
  · rw [hclass.1] at hbalance0
    rw [hclass.2] at hbalance1
    exact_mod_cast (by omega : (T.multiplicity v2 : ℤ) = T.multiplicity v1)
  · rw [hclass.1] at hbalance0
    rw [hclass.2] at hbalance1
    exact_mod_cast (by omega : (T.multiplicity v2 : ℤ) = T.multiplicity v1)
  · have hpbad : T.edgeIndexProduct v1 v0 = 3 := by
      rw [T.edgeIndexProduct_symm]
      dsimp [edgeIndexProduct]
      rw [hclass.1, hclass.2]
      norm_num
    rcases hp' with hp' | hp' <;> omega
  · have hpbad : T.edgeIndexProduct v1 v0 = 3 := by
      rw [T.edgeIndexProduct_symm]
      dsimp [edgeIndexProduct]
      rw [hclass.1, hclass.2]
      norm_num
    rcases hp' with hp' | hp' <;> omega

/-- Prepending one edge from an arbitrary source to a walk in the `(-2)` graph
produces a `MinusTwoChain`. -/
def minusTwoChainOfWalk (T : NumericalType)
    {source start target : T.Component}
    (hsourceStart : T.intersectionGraph.Adj source start)
    (hstart : T.IsMinusTwoVertex start)
    (W : T.minusTwoGraph.Walk start target) :
    T.MinusTwoChain source target := by
  have hle : T.minusTwoGraph ≤ T.intersectionGraph := fun _ _ h => h.2.2
  let q : T.intersectionGraph.Walk source target := (W.mapLe hle).cons hsourceStart
  refine
    { length := W.length + 1
      vertex := fun r => q.getVert r
      source_eq := ?_
      target_eq := ?_
      adjacent := ?_
      minusTwo := ?_ }
  · simp [q]
  · simp [q]
  · intro r
    apply q.adj_getVert_succ
    simpa [q] using r.isLt
  · intro r
    change T.IsMinusTwoVertex (q.getVert (r.val + 1))
    simpa [q] using T.minusTwo_of_getVert_minusTwoWalk W hstart r.val

/-- A walk wholly inside the `(-2)` graph is a `MinusTwoChain` without prepending an
external edge. -/
def minusTwoChainOfMinusTwoWalk (T : NumericalType)
    {source target : T.Component} (W : T.minusTwoGraph.Walk source target)
    (hsource : T.IsMinusTwoVertex source) : T.MinusTwoChain source target where
  length := W.length
  vertex r := W.getVert r
  source_eq := by simp
  target_eq := by simp
  adjacent r := (W.adj_getVert_succ r.isLt).2.2
  minusTwo r := T.minusTwo_of_getVert_minusTwoWalk W hsource r.succ.val

lemma MinusTwoCluster.hasNearHeartMaximum_of_hasHeartMaximum {T : NumericalType}
    (C : T.MinusTwoCluster) (h : C.HasHeartMaximum) : C.HasNearHeartMaximum := by
  obtain ⟨peak, hpeak, hmax, source, hsource, hadj⟩ := h
  let chain := T.minusTwoChainOfWalk hadj.symm (C.minusTwo peak hpeak)
    (SimpleGraph.Walk.nil : T.minusTwoGraph.Walk peak peak)
  exact ⟨peak, hpeak, hmax, source, hsource, chain,
    by simp [chain, minusTwoChainOfWalk]⟩

/-- A path-shape maximum lying within three internal edges of a heart-exposed path
vertex is a near-heart maximum. -/
lemma MinusTwoCluster.PathShape.hasNearHeartMaximum_of_dist_le_three
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.PathShape)
    (b s : ℕ) (hb : b ≤ S.path.length) (hs : s ≤ S.path.length)
    (hmax : ∀ i ∈ C.vertices,
      T.multiplicity i ≤ T.multiplicity (S.path.vertex ⟨s, by omega⟩))
    {source : T.Component} (hsource : ¬ T.IsMinusTwoVertex source)
    (hadj : T.intersectionGraph.Adj (S.path.vertex ⟨b, by omega⟩) source)
    (hdist : b.dist s ≤ 3) : C.HasNearHeartMaximum := by
  let W := S.path.walkBetween b s hb hs
  let chain := T.minusTwoChainOfWalk hadj.symm (S.path.minusTwo ⟨b, by omega⟩) W
  refine ⟨S.path.vertex ⟨s, by omega⟩, S.mem_vertices _, hmax,
    source, hsource, chain, ?_⟩
  simp [chain, minusTwoChainOfWalk, W]
  omega

private lemma dist_pred_lt_of_lt {b s : ℕ} (h : b < s) :
    b.dist (s - 1) < b.dist s := by
  rw [Nat.dist_eq_sub_of_le (by omega : b ≤ s - 1),
    Nat.dist_eq_sub_of_le (le_of_lt h)]
  omega

private lemma dist_succ_lt_of_lt {b s : ℕ} (h : s < b) :
    b.dist (s + 1) < b.dist s := by
  rw [Nat.dist_eq_sub_of_le_right (by omega : s + 1 ≤ b),
    Nat.dist_eq_sub_of_le_right (le_of_lt h)]
  omega

/-- Every exact long path cluster has a maximum-multiplicity vertex within four edges
of the heart. This is the plateau argument for the long `A/B/C` cases of tag `0C9W`. -/
lemma MinusTwoCluster.PathShape.hasNearHeartMaximum
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.PathShape)
    (hcard : 5 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus) :
    C.HasNearHeartMaximum := by
  classical
  obtain ⟨boundary, hboundary, source, hsource, hboundarySource⟩ :=
    C.meets_heart (by omega) hgenus
  obtain ⟨b, hb⟩ := S.covers boundary hboundary
  have hsourceAdj : T.intersectionGraph.Adj (S.path.vertex b) source := by
    rw [hb]
    exact hboundarySource
  obtain ⟨peak, hpeak, hmaxPeak⟩ := C.exists_multiplicity_maximum
  obtain ⟨s, hs⟩ := S.covers peak hpeak
  have hmax : ∀ i ∈ C.vertices,
      T.multiplicity i ≤ T.multiplicity (S.path.vertex s) := by
    simpa [hs] using hmaxPeak
  clear hmaxPeak hpeak hs peak
  generalize hd : b.val.dist s.val = d
  induction d using Nat.strong_induction_on generalizing s with
  | h d ih =>
      by_cases hnear : b.val.dist s.val ≤ 3
      · exact S.hasNearHeartMaximum_of_dist_le_three b.val s.val
          (by omega) (by omega) (by simpa using hmax) hsource hsourceAdj hnear
      by_cases hheart : ∃ heart, ¬ T.IsMinusTwoVertex heart ∧
          T.intersectionGraph.Adj (S.path.vertex s) heart
      · obtain ⟨heart, hheartNon, hheartAdj⟩ := hheart
        apply C.hasNearHeartMaximum_of_hasHeartMaximum
        exact ⟨S.path.vertex s, S.mem_vertices s, hmax, heart, hheartNon, hheartAdj⟩
      have hnoHeart : ∀ heart, ¬ T.IsMinusTwoVertex heart →
          ¬ T.intersectionGraph.Adj (S.path.vertex s) heart := by
        intro heart hheartNon hheartAdj
        exact hheart ⟨heart, hheartNon, hheartAdj⟩
      by_cases hszero : s.val = 0
      · have hsEq : s = 0 := Fin.ext hszero
        rw [hsEq] at hmax hnoHeart hd hnear
        have heq := S.left_neighbor_eq_of_endpoint_maximum_no_heart hcard
          (by simpa using hmax) hnoHeart
        let s' : Fin (S.path.length + 1) :=
          ⟨1, by have := S.length_four; omega⟩
        have hmax' : ∀ i ∈ C.vertices,
            T.multiplicity i ≤ T.multiplicity (S.path.vertex s') := by
          intro i hi
          simpa [s', heq] using hmax i hi
        have hbpos : 0 < b.val := by
          by_contra hbnot
          have hbzero : b.val = 0 := by omega
          exact hnear (by simp [hbzero])
        exact ih (b.val.dist s'.val)
          (by
            calc
              b.val.dist s'.val = b.val.dist 1 := by simp [s']
              _ < b.val.dist 0 := dist_succ_lt_of_lt hbpos
              _ = d := hd)
          s' hmax' rfl
      by_cases hslast : s.val = S.path.length
      · let last : Fin (S.path.length + 1) :=
          ⟨S.path.length, Nat.lt_succ_self _⟩
        have hsEq : s = last := Fin.ext hslast
        rw [hsEq] at hmax hnoHeart hd hnear
        have heq := S.right_neighbor_eq_of_endpoint_maximum_no_heart hcard
          (by simpa [last] using hmax) (by simpa [last] using hnoHeart)
        let s' : Fin (S.path.length + 1) :=
          ⟨S.path.length - 1, by have := S.length_four; omega⟩
        have hmax' : ∀ i ∈ C.vertices,
            T.multiplicity i ≤ T.multiplicity (S.path.vertex s') := by
          intro i hi
          simpa [s', heq] using hmax i hi
        have hblt : b.val < S.path.length := by
          by_contra hbnot
          have hbeq : b.val = S.path.length := by omega
          exact hnear (by simp [last, hbeq])
        exact ih (b.val.dist s'.val)
          (by
            calc
              b.val.dist s'.val = b.val.dist (S.path.length - 1) := by simp [s']
              _ < b.val.dist S.path.length := dist_pred_lt_of_lt hblt
              _ = d := hd)
          s' hmax' rfl
      by_cases hsone : s.val = 1
      · let one : Fin (S.path.length + 1) :=
          ⟨1, by have := S.length_four; omega⟩
        have hsEq : s = one := Fin.ext hsone
        rw [hsEq] at hmax hnoHeart hd hnear
        have hbgt : 1 < b.val := by
          by_contra hbnot
          apply hnear
          simp [one, Nat.dist]
          omega
        by_cases hheart0 : ∃ heart, ¬ T.IsMinusTwoVertex heart ∧
            T.intersectionGraph.Adj (S.path.vertex 0) heart
        · obtain ⟨heart, hheartNon, hheartAdj⟩ := hheart0
          exact S.hasNearHeartMaximum_of_dist_le_three 0 one.val
            (by omega) (by omega) (by simpa using hmax) hheartNon
            hheartAdj (by norm_num [one, Nat.dist])
        · have hnoHeart0 : ∀ heart, ¬ T.IsMinusTwoVertex heart →
              ¬ T.intersectionGraph.Adj (S.path.vertex 0) heart := by
            intro heart hheartNon hheartAdj
            exact hheart0 ⟨heart, hheartNon, hheartAdj⟩
          have heq := S.second_neighbor_eq_of_maximum_no_heart hcard
            (by simpa [one] using hmax) (by simpa [one] using hnoHeart) hnoHeart0
          let s' : Fin (S.path.length + 1) :=
            ⟨2, by have := S.length_four; omega⟩
          have hmax' : ∀ i ∈ C.vertices,
              T.multiplicity i ≤ T.multiplicity (S.path.vertex s') := by
            intro i hi
            simpa [s', heq, one] using hmax i hi
          exact ih (b.val.dist s'.val)
            (by
              calc
                b.val.dist s'.val = b.val.dist 2 := by simp [s']
                _ < b.val.dist 1 := dist_succ_lt_of_lt hbgt
                _ = d := hd)
            s' hmax' rfl
      by_cases hspenultimate : s.val = S.path.length - 1
      · let penultimate : Fin (S.path.length + 1) :=
          ⟨S.path.length - 1, by have := S.length_four; omega⟩
        have hsEq : s = penultimate := Fin.ext hspenultimate
        rw [hsEq] at hmax hnoHeart hd hnear
        have hblt : b.val < S.path.length - 1 := by
          by_contra hbnot
          have hbLower : S.path.length - 1 ≤ b.val := by omega
          have hbUpper : b.val ≤ S.path.length := by omega
          apply hnear
          simp [penultimate, Nat.dist]
          omega
        by_cases hheartLast : ∃ heart, ¬ T.IsMinusTwoVertex heart ∧
            T.intersectionGraph.Adj
              (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩) heart
        · obtain ⟨heart, hheartNon, hheartAdj⟩ := hheartLast
          exact S.hasNearHeartMaximum_of_dist_le_three S.path.length penultimate.val
            (by omega) (by omega) (by simpa using hmax) hheartNon
            hheartAdj (by simp [penultimate, Nat.dist]; omega)
        · have hnoHeartLast : ∀ heart, ¬ T.IsMinusTwoVertex heart →
              ¬ T.intersectionGraph.Adj
                (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩) heart := by
            intro heart hheartNon hheartAdj
            exact hheartLast ⟨heart, hheartNon, hheartAdj⟩
          have heq := S.penultimate_neighbor_eq_of_maximum_no_heart hcard
            (by simpa [penultimate] using hmax)
            (by simpa [penultimate] using hnoHeart) hnoHeartLast
          let s' : Fin (S.path.length + 1) :=
            ⟨S.path.length - 2, by have := S.length_four; omega⟩
          have hmax' : ∀ i ∈ C.vertices,
              T.multiplicity i ≤ T.multiplicity (S.path.vertex s') := by
            intro i hi
            simpa [s', heq, penultimate] using hmax i hi
          exact ih (b.val.dist s'.val)
            (by
              calc
                b.val.dist s'.val = b.val.dist (S.path.length - 2) := by simp [s']
                _ < b.val.dist (S.path.length - 1) := dist_pred_lt_of_lt hblt
                _ = d := hd)
            s' hmax' rfl
      have hsleft : 1 < s.val := by omega
      have hsright : s.val + 1 < S.path.length := by omega
      have heq := S.central_neighbors_eq_of_maximum_no_heart hcard s.val
        hsleft hsright (by simpa using hmax) (by simpa using hnoHeart)
      by_cases hbs : b.val < s.val
      · let s' : Fin (S.path.length + 1) :=
          ⟨s.val - 1, by omega⟩
        have hmax' : ∀ i ∈ C.vertices,
            T.multiplicity i ≤ T.multiplicity (S.path.vertex s') := by
          intro i hi
          simpa [s', heq.1] using hmax i hi
        exact ih (b.val.dist s'.val)
          (by
            calc
              b.val.dist s'.val = b.val.dist (s.val - 1) := by simp [s']
              _ < b.val.dist s.val := dist_pred_lt_of_lt hbs
              _ = d := hd)
          s' hmax' rfl
      · have hsb : s.val < b.val := by
          have hsne : s.val ≠ b.val := by
            intro heqSB
            have : b.val.dist s.val = 0 := by rw [heqSB]; simp
            omega
          omega
        let s' : Fin (S.path.length + 1) := ⟨s.val + 1, by omega⟩
        have hmax' : ∀ i ∈ C.vertices,
            T.multiplicity i ≤ T.multiplicity (S.path.vertex s') := by
          intro i hi
          simpa [s', heq.2] using hmax i hi
        exact ih (b.val.dist s'.val)
          (by
            calc
              b.val.dist s'.val = b.val.dist (s.val + 1) := by simp [s']
              _ < b.val.dist s.val := dist_succ_lt_of_lt hsb
              _ = d := hd)
          s' hmax' rfl

/-- An exact long `D`-shaped cluster: a simple path with one additional leaf at its
penultimate vertex. -/
structure MinusTwoCluster.EndForkShape {T : NumericalType}
    (C : T.MinusTwoCluster) where
  path : T.SimpleMinusTwoPath
  length_four : 4 ≤ path.length
  extra : T.Component
  extra_ne : ∀ r, extra ≠ path.vertex r
  extra_minusTwo : T.IsMinusTwoVertex extra
  extra_adjacent : T.intersectionGraph.Adj
    (path.vertex ⟨path.length - 1, by omega⟩) extra
  mem_path : ∀ r, path.vertex r ∈ C.vertices
  mem_extra : extra ∈ C.vertices
  covers : ∀ i ∈ C.vertices, (∃ r, path.vertex r = i) ∨ i = extra
  path_neighbors : ∀ (r : Fin (path.length + 1)) (i : T.Component),
    T.IsMinusTwoVertex i → T.intersectionGraph.Adj (path.vertex r) i →
      (∃ s : Fin (path.length + 1), s.val + 1 = r.val ∧ i = path.vertex s) ∨
      (∃ s : Fin (path.length + 1), r.val + 1 = s.val ∧ i = path.vertex s) ∨
      (r.val = path.length - 1 ∧ i = extra)
  extra_neighbor : ∀ i, T.IsMinusTwoVertex i →
    T.intersectionGraph.Adj extra i →
      i = path.vertex ⟨path.length - 1, by omega⟩

lemma MinusTwoCluster.EndForkShape.left_endpoint_neighbor_eq
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.EndForkShape)
    {i : T.Component} (hi : T.IsMinusTwoVertex i)
    (hadj : T.intersectionGraph.Adj (S.path.vertex 0) i) :
    i = S.path.vertex ⟨1, by have := S.length_four; omega⟩ := by
  rcases S.path_neighbors 0 i hi hadj with h | h | h
  · obtain ⟨s, hs, _⟩ := h
    change s.val + 1 = 0 at hs
    omega
  · obtain ⟨s, hs, his⟩ := h
    change 0 + 1 = s.val at hs
    have hsEq : s = ⟨1, by have := S.length_four; omega⟩ := by
      apply Fin.ext
      change s.val = 1
      omega
    simpa [hsEq] using his
  · have := S.length_four
    have heq := h.1
    change 0 = S.path.length - 1 at heq
    omega

lemma MinusTwoCluster.EndForkShape.internal_neighbor_eq
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.EndForkShape)
    (r : ℕ) (hr0 : 0 < r) (hrlast : r < S.path.length - 1)
    {i : T.Component} (hi : T.IsMinusTwoVertex i)
    (hadj : T.intersectionGraph.Adj (S.path.vertex ⟨r, by omega⟩) i) :
    i = S.path.vertex ⟨r - 1, by omega⟩ ∨
      i = S.path.vertex ⟨r + 1, by omega⟩ := by
  rcases S.path_neighbors ⟨r, by omega⟩ i hi hadj with h | h | h
  · obtain ⟨s, hs, his⟩ := h
    left
    change s.val + 1 = r at hs
    have hsEq : s = ⟨r - 1, by omega⟩ := by
      apply Fin.ext
      change s.val = r - 1
      omega
    simpa [hsEq] using his
  · obtain ⟨s, hs, his⟩ := h
    right
    change r + 1 = s.val at hs
    have hsEq : s = ⟨r + 1, by omega⟩ := by
      apply Fin.ext
      change s.val = r + 1
      omega
    simpa [hsEq] using his
  · have heq := h.1
    change r = S.path.length - 1 at heq
    omega

lemma MinusTwoCluster.EndForkShape.right_endpoint_neighbor_eq
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.EndForkShape)
    {i : T.Component} (hi : T.IsMinusTwoVertex i)
    (hadj : T.intersectionGraph.Adj
      (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩) i) :
    i = S.path.vertex ⟨S.path.length - 1, by omega⟩ := by
  rcases S.path_neighbors ⟨S.path.length, Nat.lt_succ_self _⟩ i hi hadj with h | h | h
  · obtain ⟨s, hs, his⟩ := h
    change s.val + 1 = S.path.length at hs
    have hsEq : s = ⟨S.path.length - 1, by omega⟩ := by
      apply Fin.ext
      change s.val = S.path.length - 1
      omega
    simpa [hsEq] using his
  · obtain ⟨s, hs, _⟩ := h
    change S.path.length + 1 = s.val at hs
    omega
  · have heq := h.1
    change S.path.length = S.path.length - 1 at heq
    have := S.length_four
    omega

lemma MinusTwoCluster.EndForkShape.branch_neighbor_eq
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.EndForkShape)
    {i : T.Component} (hi : T.IsMinusTwoVertex i)
    (hadj : T.intersectionGraph.Adj
      (S.path.vertex ⟨S.path.length - 1, by omega⟩) i) :
    i = S.path.vertex ⟨S.path.length - 2, by omega⟩ ∨
      i = S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩ ∨
      i = S.extra := by
  rcases S.path_neighbors ⟨S.path.length - 1, by omega⟩ i hi hadj with h | h | h
  · obtain ⟨s, hs, his⟩ := h
    left
    change s.val + 1 = S.path.length - 1 at hs
    have hsEq : s = ⟨S.path.length - 2, by omega⟩ := by
      apply Fin.ext
      change s.val = S.path.length - 2
      omega
    simpa [hsEq] using his
  · obtain ⟨s, hs, his⟩ := h
    right; left
    change S.path.length - 1 + 1 = s.val at hs
    have hsEq : s = ⟨S.path.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      change s.val = S.path.length
      omega
    simpa [hsEq] using his
  · exact Or.inr (Or.inr h.2)

lemma normalized_three_neighbor_balance_eq_of_no_heart (T : NumericalType)
    {i j k l : T.Component} (hj : T.IsMinusTwoVertex j)
    (hji : T.intersectionGraph.Adj j i) (hjk : T.intersectionGraph.Adj j k)
    (hjl : T.intersectionGraph.Adj j l)
    (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l)
    (hneighbors : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj j r → r = i ∨ r = k ∨ r = l)
    (hnoHeart : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj j source) :
    (T.multiplicity i : ℤ) * T.normalizedIntersection j i +
        (T.multiplicity k : ℤ) * T.normalizedIntersection j k +
        (T.multiplicity l : ℤ) * T.normalizedIntersection j l =
      2 * (T.multiplicity j : ℤ) := by
  have h := T.normalized_neighbor_balance_eq_of_no_heart hj {i, k, l}
    (by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact hji.ne.symm
      · exact hjk.ne.symm
      · exact hjl.ne.symm)
    (fun r hr hadj => by
      rcases hneighbors r hr hadj with rfl | rfl | rfl <;> simp)
    hnoHeart
  simpa [hik, hil, hkl, add_assoc] using h

lemma MinusTwoCluster.EndForkShape.branch_edgeIndexProducts_eq_one
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.EndForkShape)
    (hcard : 5 < Nat.card T.Component) :
    T.edgeIndexProduct
        (S.path.vertex ⟨S.path.length - 1, by omega⟩)
        (S.path.vertex ⟨S.path.length - 2, by omega⟩) = 1 ∧
      T.edgeIndexProduct
        (S.path.vertex ⟨S.path.length - 1, by omega⟩)
        (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩) = 1 ∧
      T.edgeIndexProduct
        (S.path.vertex ⟨S.path.length - 1, by omega⟩) S.extra = 1 := by
  let branch := S.path.vertex ⟨S.path.length - 1, by omega⟩
  let prev := S.path.vertex ⟨S.path.length - 2, by omega⟩
  let last := S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩
  have hprev : T.intersectionGraph.Adj branch prev := by
    dsimp [branch, prev]
    have hadj := (S.path.adjacent_nat (S.path.length - 2)
      (by have := S.length_four; omega)).symm
    have heq : S.path.length - 2 + 1 = S.path.length - 1 := by
      have := S.length_four
      omega
    simpa [heq] using hadj
  have hlast : T.intersectionGraph.Adj branch last := by
    dsimp [branch, last]
    have hadj := S.path.adjacent_nat (S.path.length - 1)
      (by have := S.length_four; omega)
    have heq : S.path.length - 1 + 1 = S.path.length := by
      have := S.length_four
      omega
    simpa [heq] using hadj
  have hprevLast : prev ≠ last := by
    dsimp [prev, last]
    exact S.path.injective.ne (by
      intro h
      have hval := congrArg Fin.val h
      change S.path.length - 2 = S.path.length at hval
      have := S.length_four
      omega)
  have hprevExtra : prev ≠ S.extra := (S.extra_ne _).symm
  have hlastExtra : last ≠ S.extra := (S.extra_ne _).symm
  have hprod := T.three_minusTwo_neighbors_edgeIndexProducts_eq_one (by omega)
      (S.path.minusTwo ⟨S.path.length - 1, by omega⟩)
      (S.path.minusTwo ⟨S.path.length - 2, by omega⟩)
      (S.path.minusTwo ⟨S.path.length, Nat.lt_succ_self _⟩)
      S.extra_minusTwo hprev hlast S.extra_adjacent
      hprevLast hprevExtra hlastExtra
  change T.edgeIndexProduct branch prev = 1 ∧
    T.edgeIndexProduct branch last = 1 ∧ T.edgeIndexProduct branch S.extra = 1
  exact hprod

lemma MinusTwoCluster.EndForkShape.branch_prev_eq_of_maximum_no_heart
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.EndForkShape)
    (hcard : 5 < Nat.card T.Component)
    (hmax : ∀ i ∈ C.vertices,
      T.multiplicity i ≤ T.multiplicity
        (S.path.vertex ⟨S.path.length - 1, by omega⟩))
    (hnoHeartBranch : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj
        (S.path.vertex ⟨S.path.length - 1, by omega⟩) source)
    (hnoHeartLast : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj
        (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩) source)
    (hnoHeartExtra : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj S.extra source) :
    T.multiplicity (S.path.vertex ⟨S.path.length - 2, by omega⟩) =
      T.multiplicity (S.path.vertex ⟨S.path.length - 1, by omega⟩) := by
  let branch := S.path.vertex ⟨S.path.length - 1, by omega⟩
  let prev := S.path.vertex ⟨S.path.length - 2, by omega⟩
  let last := S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩
  have hprev : T.intersectionGraph.Adj branch prev := by
    dsimp [branch, prev]
    have hadj := (S.path.adjacent_nat (S.path.length - 2)
      (by have := S.length_four; omega)).symm
    have heq : S.path.length - 2 + 1 = S.path.length - 1 := by
      have := S.length_four
      omega
    simpa [heq] using hadj
  have hlast : T.intersectionGraph.Adj branch last := by
    dsimp [branch, last]
    have hadj := S.path.adjacent_nat (S.path.length - 1)
      (by have := S.length_four; omega)
    have heq : S.path.length - 1 + 1 = S.path.length := by
      have := S.length_four
      omega
    simpa [heq] using hadj
  have hprod := S.branch_edgeIndexProducts_eq_one hcard
  have hprevNorm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one hprev hprod.1).1
  have hlastNorm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one hlast hprod.2.1).1
  have hextraNorm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one
      S.extra_adjacent hprod.2.2).1
  have hlastBranchNorm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one
      hlast.symm (by simpa [T.edgeIndexProduct_symm] using hprod.2.1)).1
  have hextraBranchNorm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one
      S.extra_adjacent.symm
      (by simpa [T.edgeIndexProduct_symm] using hprod.2.2)).1
  have hlastBalance := T.normalized_single_neighbor_balance_eq_of_no_heart
    (S.path.minusTwo ⟨S.path.length, Nat.lt_succ_self _⟩) hlast.symm
    (fun r hr hadj => S.right_endpoint_neighbor_eq hr hadj) hnoHeartLast
  have hextraBalance := T.normalized_single_neighbor_balance_eq_of_no_heart
    S.extra_minusTwo S.extra_adjacent.symm S.extra_neighbor hnoHeartExtra
  change (T.multiplicity branch : ℤ) * T.normalizedIntersection last branch =
    2 * (T.multiplicity last : ℤ) at hlastBalance
  change (T.multiplicity branch : ℤ) * T.normalizedIntersection S.extra branch =
    2 * (T.multiplicity S.extra : ℤ) at hextraBalance
  rw [hlastBranchNorm] at hlastBalance
  rw [hextraBranchNorm] at hextraBalance
  have hneighbors : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj branch r → r = prev ∨ r = last ∨ r = S.extra := by
    intro r hr hadj
    simpa [branch, prev, last] using S.branch_neighbor_eq hr hadj
  have hprevLast : prev ≠ last := by
    dsimp [prev, last]
    exact S.path.injective.ne (by
      intro h
      have hval := congrArg Fin.val h
      change S.path.length - 2 = S.path.length at hval
      have := S.length_four
      omega)
  have hprevExtra : prev ≠ S.extra := (S.extra_ne _).symm
  have hlastExtra : last ≠ S.extra := (S.extra_ne _).symm
  have hbranchBalance := T.normalized_three_neighbor_balance_eq_of_no_heart
    (S.path.minusTwo ⟨S.path.length - 1, by omega⟩)
    hprev hlast S.extra_adjacent hprevLast hprevExtra hlastExtra
    hneighbors hnoHeartBranch
  change (T.multiplicity prev : ℤ) * T.normalizedIntersection branch prev +
      (T.multiplicity last : ℤ) * T.normalizedIntersection branch last +
      (T.multiplicity S.extra : ℤ) * T.normalizedIntersection branch S.extra =
    2 * (T.multiplicity branch : ℤ) at hbranchBalance
  rw [hprevNorm, hlastNorm, hextraNorm] at hbranchBalance
  have hprevMax : (T.multiplicity prev : ℤ) ≤ T.multiplicity branch := by
    exact_mod_cast (show T.multiplicity prev ≤ T.multiplicity branch by
      simpa [branch] using hmax prev (by dsimp [prev]; exact S.mem_path _))
  have hlastMax : (T.multiplicity last : ℤ) ≤ T.multiplicity branch := by
    exact_mod_cast (show T.multiplicity last ≤ T.multiplicity branch by
      simpa [branch] using hmax last (by dsimp [last]; exact S.mem_path _))
  have hextraMax : (T.multiplicity S.extra : ℤ) ≤ T.multiplicity branch := by
    exact_mod_cast (show T.multiplicity S.extra ≤ T.multiplicity branch by
      simpa [branch] using hmax S.extra S.mem_extra)
  exact_mod_cast (by omega : (T.multiplicity prev : ℤ) = T.multiplicity branch)

lemma MinusTwoCluster.EndForkShape.left_neighbor_eq_of_endpoint_maximum_no_heart
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.EndForkShape)
    (hcard : 5 < Nat.card T.Component)
    (hmax : ∀ i ∈ C.vertices,
      T.multiplicity i ≤ T.multiplicity (S.path.vertex 0))
    (hnoHeart : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj (S.path.vertex 0) source) :
    T.multiplicity (S.path.vertex ⟨1, by have := S.length_four; omega⟩) =
      T.multiplicity (S.path.vertex 0) := by
  let endpoint := S.path.vertex 0
  let next := S.path.vertex ⟨1, by have := S.length_four; omega⟩
  have hadj : T.intersectionGraph.Adj endpoint next := by
    dsimp [endpoint, next]
    exact S.path.adjacent_nat 0 (by have := S.length_four; omega)
  have hprodLe : T.edgeIndexProduct endpoint next ≤ 2 := by
    have hp := S.path.first_edgeIndexProduct_eq_one_or_two hcard S.length_four
    have hpLe : S.path.edgeIndexProductAt
        ⟨0, by have := S.length_four; omega⟩ ≤ 2 := by
      rcases hp with hp | hp <;> omega
    change T.edgeIndexProduct (S.path.vertex 0)
      (S.path.vertex ⟨1, by have := S.length_four; omega⟩) ≤ 2 at hpLe
    simpa [endpoint, next] using hpLe
  have hforwardPos := T.normalizedIntersection_pos_of_adj hadj
  have hrevPos := T.normalizedIntersection_pos_of_adj hadj.symm
  have hnormLe : T.normalizedIntersection endpoint next ≤ 2 := by
    dsimp [edgeIndexProduct] at hprodLe
    nlinarith
  apply C.neighbor_multiplicity_eq_of_maximum_single_neighbor
    (S.mem_path 0) (by simpa [endpoint] using hmax)
    (S.path.minusTwo ⟨1, by have := S.length_four; omega⟩) hadj hnormLe
  · intro r hr hendpoint
    exact S.left_endpoint_neighbor_eq hr hendpoint
  · exact hnoHeart

lemma MinusTwoCluster.EndForkShape.right_neighbor_eq_of_endpoint_maximum_no_heart
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.EndForkShape)
    (hcard : 5 < Nat.card T.Component)
    (hmax : ∀ i ∈ C.vertices,
      T.multiplicity i ≤
        T.multiplicity (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩))
    (hnoHeart : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj
        (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩) source) :
    T.multiplicity (S.path.vertex ⟨S.path.length - 1, by omega⟩) =
      T.multiplicity (S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩) := by
  let endpoint := S.path.vertex ⟨S.path.length, Nat.lt_succ_self _⟩
  let prev := S.path.vertex ⟨S.path.length - 1, by omega⟩
  have hadj : T.intersectionGraph.Adj endpoint prev := by
    dsimp [endpoint, prev]
    simpa [Nat.sub_add_cancel (by have := S.length_four; omega : 1 ≤ S.path.length)] using
      (S.path.adjacent_nat (S.path.length - 1)
        (by have := S.length_four; omega)).symm
  have hprod := (S.branch_edgeIndexProducts_eq_one hcard).2.1
  have hnorm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one hadj
      (by simpa [T.edgeIndexProduct_symm, endpoint, prev] using hprod)).1
  apply C.neighbor_multiplicity_eq_of_maximum_single_neighbor
    (S.mem_path ⟨S.path.length, Nat.lt_succ_self _⟩)
    (by simpa [endpoint] using hmax) (S.path.minusTwo
      ⟨S.path.length - 1, by omega⟩) hadj (by rw [hnorm]; norm_num)
  · intro r hr hendpoint
    exact S.right_endpoint_neighbor_eq hr hendpoint
  · exact hnoHeart

lemma MinusTwoCluster.EndForkShape.extra_neighbor_eq_of_maximum_no_heart
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.EndForkShape)
    (hcard : 5 < Nat.card T.Component)
    (hmax : ∀ i ∈ C.vertices, T.multiplicity i ≤ T.multiplicity S.extra)
    (hnoHeart : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj S.extra source) :
    T.multiplicity (S.path.vertex ⟨S.path.length - 1, by omega⟩) =
      T.multiplicity S.extra := by
  let branch := S.path.vertex ⟨S.path.length - 1, by omega⟩
  have hadj : T.intersectionGraph.Adj S.extra branch := by
    simpa [branch] using S.extra_adjacent.symm
  have hprod := (S.branch_edgeIndexProducts_eq_one hcard).2.2
  have hnorm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one hadj
      (by simpa [T.edgeIndexProduct_symm, branch] using hprod)).1
  apply C.neighbor_multiplicity_eq_of_maximum_single_neighbor
    S.mem_extra hmax (S.path.minusTwo ⟨S.path.length - 1, by omega⟩)
    hadj (by rw [hnorm]; norm_num)
  · exact S.extra_neighbor
  · exact hnoHeart

lemma MinusTwoCluster.EndForkShape.second_neighbor_eq_of_maximum_no_heart
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.EndForkShape)
    (hcard : 5 < Nat.card T.Component)
    (hmax : ∀ i ∈ C.vertices,
      T.multiplicity i ≤ T.multiplicity
        (S.path.vertex ⟨1, by have := S.length_four; omega⟩))
    (hnoHeartSecond : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj
        (S.path.vertex ⟨1, by have := S.length_four; omega⟩) source)
    (hnoHeartEndpoint : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj (S.path.vertex 0) source) :
    T.multiplicity (S.path.vertex
        ⟨2, by have := S.length_four; omega⟩) =
      T.multiplicity (S.path.vertex
        ⟨1, by have := S.length_four; omega⟩) := by
  let v0 := S.path.vertex 0
  let v1 := S.path.vertex ⟨1, by have := S.length_four; omega⟩
  let v2 := S.path.vertex ⟨2, by have := S.length_four; omega⟩
  change T.multiplicity v2 = T.multiplicity v1
  have h01 : T.intersectionGraph.Adj v0 v1 := by
    dsimp [v0, v1]
    exact S.path.adjacent_nat 0 (by have := S.length_four; omega)
  have h12 : T.intersectionGraph.Adj v1 v2 := by
    dsimp [v1, v2]
    exact S.path.adjacent_nat 1 (by have := S.length_four; omega)
  have h12prod : T.edgeIndexProduct v1 v2 = 1 := by
    have h := S.path.interior_edgeIndexProduct_eq_one hcard S.length_four
      1 (by omega) (by have := S.length_four; omega)
    simpa [SimpleMinusTwoPath.edgeIndexProductAt, v1, v2] using h
  have h12norm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one h12 h12prod).1
  have hneighbors0 : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj v0 r → r = v1 := by
    intro r hr hadj
    simpa [v0, v1] using S.left_endpoint_neighbor_eq hr hadj
  have hneighbors1 : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj v1 r → r = v0 ∨ r = v2 := by
    intro r hr hadj
    simpa [v0, v1, v2] using S.internal_neighbor_eq 1 (by omega)
      (by have := S.length_four; omega) hr hadj
  have hbalance0 := T.normalized_single_neighbor_balance_eq_of_no_heart
    (S.path.minusTwo 0) h01 hneighbors0 hnoHeartEndpoint
  change (T.multiplicity v1 : ℤ) * T.normalizedIntersection v0 v1 =
    2 * (T.multiplicity v0 : ℤ) at hbalance0
  have hv0v2 : v0 ≠ v2 := by
    dsimp [v0, v2]
    exact S.path.injective.ne (by
      intro h
      have h' := congrArg Fin.val h
      change (0 : ℕ) = 2 at h'
      omega)
  have hbalance1 := T.normalized_two_neighbor_balance_eq_of_no_heart
    (S.path.minusTwo ⟨1, by have := S.length_four; omega⟩) h01.symm h12 hv0v2
    hneighbors1 hnoHeartSecond
  change (T.multiplicity v0 : ℤ) * T.normalizedIntersection v1 v0 +
    (T.multiplicity v2 : ℤ) * T.normalizedIntersection v1 v2 =
      2 * (T.multiplicity v1 : ℤ) at hbalance1
  rw [h12norm] at hbalance1
  have hmax0 : (T.multiplicity v0 : ℤ) ≤ T.multiplicity v1 := by
    exact_mod_cast (show T.multiplicity v0 ≤ T.multiplicity v1 by
      simpa [v1] using hmax v0 (by dsimp [v0]; exact S.mem_path 0))
  have hmax2 : (T.multiplicity v2 : ℤ) ≤ T.multiplicity v1 := by
    exact_mod_cast (show T.multiplicity v2 ≤ T.multiplicity v1 by
      simpa [v1] using hmax v2 (by dsimp [v2]; exact S.mem_path _))
  have hp := S.path.first_edgeIndexProduct_eq_one_or_two hcard S.length_four
  have hclass := T.edgeIndex_pair_classification (by omega)
    (S.path.minusTwo 0) (S.path.minusTwo
      ⟨1, by have := S.length_four; omega⟩) h01
  rcases hclass with hclass | hclass | hclass | hclass | hclass
  · rw [hclass.1] at hbalance0
    rw [hclass.2] at hbalance1
    have hm0 : (0 : ℤ) < T.multiplicity v0 := by positivity
    have hm2 : (0 : ℤ) < T.multiplicity v2 := by positivity
    nlinarith
  · rw [hclass.1] at hbalance0
    rw [hclass.2] at hbalance1
    exact_mod_cast (by omega : (T.multiplicity v2 : ℤ) = T.multiplicity v1)
  · rw [hclass.1] at hbalance0
    rw [hclass.2] at hbalance1
    exact_mod_cast (by omega : (T.multiplicity v2 : ℤ) = T.multiplicity v1)
  · have hpbad : S.path.edgeIndexProductAt
        ⟨0, by have := S.length_four; omega⟩ = 3 := by
      change T.edgeIndexProduct v0 v1 = 3
      dsimp [edgeIndexProduct]
      rw [hclass.1, hclass.2]
      norm_num
    rcases hp with hp | hp <;> omega
  · have hpbad : S.path.edgeIndexProductAt
        ⟨0, by have := S.length_four; omega⟩ = 3 := by
      change T.edgeIndexProduct v0 v1 = 3
      dsimp [edgeIndexProduct]
      rw [hclass.1, hclass.2]
      norm_num
    rcases hp with hp | hp <;> omega

lemma MinusTwoCluster.EndForkShape.central_neighbors_eq_of_maximum_no_heart
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.EndForkShape)
    (hcard : 5 < Nat.card T.Component) (s : ℕ)
    (hsleft : 1 < s) (hsright : s < S.path.length - 1)
    (hmax : ∀ i ∈ C.vertices,
      T.multiplicity i ≤ T.multiplicity (S.path.vertex ⟨s, by omega⟩))
    (hnoHeart : ∀ source, ¬ T.IsMinusTwoVertex source →
      ¬ T.intersectionGraph.Adj (S.path.vertex ⟨s, by omega⟩) source) :
    T.multiplicity (S.path.vertex ⟨s - 1, by omega⟩) =
        T.multiplicity (S.path.vertex ⟨s, by omega⟩) ∧
      T.multiplicity (S.path.vertex ⟨s + 1, by omega⟩) =
        T.multiplicity (S.path.vertex ⟨s, by omega⟩) := by
  let left := S.path.vertex ⟨s - 1, by omega⟩
  let peak := S.path.vertex ⟨s, by omega⟩
  let right := S.path.vertex ⟨s + 1, by omega⟩
  have hleftAdj : T.intersectionGraph.Adj peak left := by
    dsimp [peak, left]
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ s)] using
      (S.path.adjacent_nat (s - 1) (by omega)).symm
  have hrightAdj : T.intersectionGraph.Adj peak right := by
    dsimp [peak, right]
    exact S.path.adjacent_nat s (by omega)
  have hleftProd : T.edgeIndexProduct peak left = 1 := by
    rw [T.edgeIndexProduct_symm]
    have h := S.path.interior_edgeIndexProduct_eq_one hcard S.length_four
      (s - 1) (by omega) (by omega)
    simpa [SimpleMinusTwoPath.edgeIndexProductAt, left, peak,
      Nat.sub_add_cancel (by omega : 1 ≤ s)] using h
  have hrightProd : T.edgeIndexProduct peak right = 1 := by
    convert S.path.interior_edgeIndexProduct_eq_one hcard S.length_four
      s (by omega) (by omega) using 1
    all_goals congr
  have hleftNorm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one hleftAdj hleftProd).1
  have hrightNorm :=
    (T.normalizedIntersections_eq_one_of_edgeIndexProduct_eq_one hrightAdj hrightProd).1
  have hneighbors : ∀ r, T.IsMinusTwoVertex r →
      T.intersectionGraph.Adj peak r → r = left ∨ r = right := by
    intro r hr hadj
    simpa [peak, left, right] using S.internal_neighbor_eq s (by omega) hsright hr hadj
  have hbalance := T.normalized_two_neighbor_balance_eq_of_no_heart
    (S.path.minusTwo ⟨s, by omega⟩) hleftAdj hrightAdj
    (by
      dsimp [left, right]
      intro heq
      have hfin := S.path.injective heq
      have hval := congrArg Fin.val hfin
      change s - 1 = s + 1 at hval
      omega)
    hneighbors hnoHeart
  rw [hleftNorm, hrightNorm] at hbalance
  have hbalance' : (T.multiplicity left : ℤ) + T.multiplicity right =
      2 * (T.multiplicity peak : ℤ) := by
    simpa [peak] using hbalance
  have hleftMax : T.multiplicity left ≤ T.multiplicity peak := by
    simpa [peak] using hmax left (by dsimp [left]; exact S.mem_path _)
  have hrightMax : T.multiplicity right ≤ T.multiplicity peak := by
    simpa [peak] using hmax right (by dsimp [right]; exact S.mem_path _)
  have hleftMaxInt : (T.multiplicity left : ℤ) ≤ T.multiplicity peak := by
    exact_mod_cast hleftMax
  have hrightMaxInt : (T.multiplicity right : ℤ) ≤ T.multiplicity peak := by
    exact_mod_cast hrightMax
  constructor
  · exact_mod_cast (by omega : (T.multiplicity left : ℤ) = T.multiplicity peak)
  · exact_mod_cast (by omega : (T.multiplicity right : ℤ) = T.multiplicity peak)

lemma MinusTwoCluster.EndForkShape.hasNearHeartMaximum_of_prefix_dist
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.EndForkShape)
    (b s : ℕ) (hb : b ≤ S.path.length) (hs : s ≤ S.path.length)
    (hmax : ∀ i ∈ C.vertices,
      T.multiplicity i ≤ T.multiplicity (S.path.vertex ⟨s, by omega⟩))
    {source start : T.Component} (hsource : ¬ T.IsMinusTwoVertex source)
    (hsourceStart : T.intersectionGraph.Adj source start)
    (hstart : T.IsMinusTwoVertex start)
    (stem : T.minusTwoGraph.Walk start (S.path.vertex ⟨b, by omega⟩))
    (hdist : stem.length + b.dist s ≤ 3) : C.HasNearHeartMaximum := by
  let W := stem.append (S.path.walkBetween b s hb hs)
  let chain := T.minusTwoChainOfWalk hsourceStart hstart W
  refine ⟨S.path.vertex ⟨s, by omega⟩, S.mem_path _, hmax,
    source, hsource, chain, ?_⟩
  simp [chain, minusTwoChainOfWalk, W]
  omega

private lemma endFork_dist_pred_lt_of_lt {b s : ℕ} (h : b < s) :
    b.dist (s - 1) < b.dist s := by
  rw [Nat.dist_eq_sub_of_le (by omega : b ≤ s - 1),
    Nat.dist_eq_sub_of_le (le_of_lt h)]
  omega

private lemma endFork_dist_succ_lt_of_lt {b s : ℕ} (h : s < b) :
    b.dist (s + 1) < b.dist s := by
  rw [Nat.dist_eq_sub_of_le_right (by omega : s + 1 ≤ b),
    Nat.dist_eq_sub_of_le_right (le_of_lt h)]
  omega

/-- Every exact long end-fork cluster has a maximum-multiplicity vertex within four
edges of the heart. This is the plateau argument for the unbounded `D` family. -/
lemma MinusTwoCluster.EndForkShape.hasNearHeartMaximum
    {T : NumericalType} {C : T.MinusTwoCluster} (S : C.EndForkShape)
    (hcard : 5 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus) :
    C.HasNearHeartMaximum := by
  classical
  obtain ⟨boundary, hboundary, source, hsource, hboundarySource⟩ :=
    C.meets_heart (by omega) hgenus
  obtain ⟨b, start, hstart, hsourceStart, stem, hstem⟩ :
      ∃ (b : Fin (S.path.length + 1)) (start : T.Component),
        T.IsMinusTwoVertex start ∧ T.intersectionGraph.Adj source start ∧
        ∃ stem : T.minusTwoGraph.Walk start (S.path.vertex b),
          stem.length ≤ 1 := by
    rcases S.covers boundary hboundary with ⟨b, hb⟩ | hb
    · refine ⟨b, S.path.vertex b, S.path.minusTwo b, ?_,
        SimpleGraph.Walk.nil, by simp⟩
      rw [hb]
      exact hboundarySource.symm
    · subst boundary
      let branch := S.path.vertex ⟨S.path.length - 1, by omega⟩
      have hextraBranch : T.minusTwoGraph.Adj S.extra branch := by
        exact ⟨S.extra_minusTwo, S.path.minusTwo _, S.extra_adjacent.symm⟩
      let stem : T.minusTwoGraph.Walk S.extra branch :=
        (SimpleGraph.Walk.nil : T.minusTwoGraph.Walk branch branch).cons hextraBranch
      refine ⟨⟨S.path.length - 1, by omega⟩, S.extra, S.extra_minusTwo,
        hboundarySource.symm, stem, ?_⟩
      simp [stem]
  have pathMaximumNear (s : Fin (S.path.length + 1))
      (hmax : ∀ i ∈ C.vertices,
        T.multiplicity i ≤ T.multiplicity (S.path.vertex s)) :
      C.HasNearHeartMaximum := by
    generalize hd : b.val.dist s.val = d
    induction d using Nat.strong_induction_on generalizing s with
    | h d ih =>
        by_cases hnear : stem.length + b.val.dist s.val ≤ 3
        · exact S.hasNearHeartMaximum_of_prefix_dist b.val s.val
            (by omega) (by omega) (by simpa using hmax) hsource hsourceStart
            hstart stem hnear
        by_cases hheart : ∃ heart, ¬ T.IsMinusTwoVertex heart ∧
            T.intersectionGraph.Adj (S.path.vertex s) heart
        · obtain ⟨heart, hheartNon, hheartAdj⟩ := hheart
          apply C.hasNearHeartMaximum_of_hasHeartMaximum
          exact ⟨S.path.vertex s, S.mem_path s, hmax,
            heart, hheartNon, hheartAdj⟩
        have hnoHeart : ∀ heart, ¬ T.IsMinusTwoVertex heart →
            ¬ T.intersectionGraph.Adj (S.path.vertex s) heart := by
          intro heart hheartNon hheartAdj
          exact hheart ⟨heart, hheartNon, hheartAdj⟩
        by_cases hszero : s.val = 0
        · have hsEq : s = 0 := Fin.ext hszero
          rw [hsEq] at hmax hnoHeart hd hnear
          have heq := S.left_neighbor_eq_of_endpoint_maximum_no_heart hcard
            (by simpa using hmax) hnoHeart
          let s' : Fin (S.path.length + 1) :=
            ⟨1, by have := S.length_four; omega⟩
          have hmax' : ∀ i ∈ C.vertices,
              T.multiplicity i ≤ T.multiplicity (S.path.vertex s') := by
            intro i hi
            simpa [s', heq] using hmax i hi
          have hbpos : 0 < b.val := by
            by_contra hbnot
            have hbzero : b.val = 0 := by omega
            exact hnear (by
              have hp : stem.length ≤ 1 := hstem
              simp [hbzero]
              omega)
          exact ih (b.val.dist s'.val)
            (by
              calc
                b.val.dist s'.val = b.val.dist 1 := by simp [s']
                _ < b.val.dist 0 := endFork_dist_succ_lt_of_lt hbpos
                _ = d := hd)
            s' hmax' rfl
        by_cases hslast : s.val = S.path.length
        · let last : Fin (S.path.length + 1) :=
            ⟨S.path.length, Nat.lt_succ_self _⟩
          have hsEq : s = last := Fin.ext hslast
          rw [hsEq] at hmax hnoHeart hd hnear
          have heq := S.right_neighbor_eq_of_endpoint_maximum_no_heart hcard
            (by simpa [last] using hmax) (by simpa [last] using hnoHeart)
          let s' : Fin (S.path.length + 1) :=
            ⟨S.path.length - 1, by omega⟩
          have hmax' : ∀ i ∈ C.vertices,
              T.multiplicity i ≤ T.multiplicity (S.path.vertex s') := by
            intro i hi
            simpa [s', heq] using hmax i hi
          have hblt : b.val < S.path.length := by
            by_contra hbnot
            have hbeq : b.val = S.path.length := by omega
            exact hnear (by
              have hp : stem.length ≤ 1 := hstem
              simp [last, hbeq]
              omega)
          exact ih (b.val.dist s'.val)
            (by
              calc
                b.val.dist s'.val = b.val.dist (S.path.length - 1) := by simp [s']
                _ < b.val.dist S.path.length := endFork_dist_pred_lt_of_lt hblt
                _ = d := hd)
            s' hmax' rfl
        by_cases hsone : s.val = 1
        · let one : Fin (S.path.length + 1) :=
            ⟨1, by have := S.length_four; omega⟩
          have hsEq : s = one := Fin.ext hsone
          rw [hsEq] at hmax hnoHeart hd hnear
          have hbgt : 1 < b.val := by
            by_contra hbnot
            apply hnear
            have hp : stem.length ≤ 1 := hstem
            simp [one, Nat.dist]
            omega
          by_cases hheart0 : ∃ heart, ¬ T.IsMinusTwoVertex heart ∧
              T.intersectionGraph.Adj (S.path.vertex 0) heart
          · obtain ⟨heart, hheartNon, hheartAdj⟩ := hheart0
            exact S.hasNearHeartMaximum_of_prefix_dist 0 one.val
              (by omega) (by omega) (by simpa using hmax) hheartNon
              hheartAdj.symm (S.path.minusTwo 0) SimpleGraph.Walk.nil
              (by simp [one, Nat.dist])
          · have hnoHeart0 : ∀ heart, ¬ T.IsMinusTwoVertex heart →
                ¬ T.intersectionGraph.Adj (S.path.vertex 0) heart := by
              intro heart hheartNon hheartAdj
              exact hheart0 ⟨heart, hheartNon, hheartAdj⟩
            have heq := S.second_neighbor_eq_of_maximum_no_heart hcard
              (by simpa [one] using hmax) (by simpa [one] using hnoHeart)
              hnoHeart0
            let s' : Fin (S.path.length + 1) :=
              ⟨2, by have := S.length_four; omega⟩
            have hmax' : ∀ i ∈ C.vertices,
                T.multiplicity i ≤ T.multiplicity (S.path.vertex s') := by
              intro i hi
              simpa [s', heq, one] using hmax i hi
            exact ih (b.val.dist s'.val)
              (by
                calc
                  b.val.dist s'.val = b.val.dist 2 := by simp [s']
                  _ < b.val.dist 1 := endFork_dist_succ_lt_of_lt hbgt
                  _ = d := hd)
              s' hmax' rfl
        by_cases hsbranch : s.val = S.path.length - 1
        · let branch : Fin (S.path.length + 1) :=
            ⟨S.path.length - 1, by omega⟩
          have hsEq : s = branch := Fin.ext hsbranch
          rw [hsEq] at hmax hnoHeart hd hnear
          have hblt : b.val < S.path.length - 1 := by
            by_contra hbnot
            have hbUpper : b.val ≤ S.path.length := by omega
            apply hnear
            have hp : stem.length ≤ 1 := hstem
            simp [branch, Nat.dist]
            omega
          let last : Fin (S.path.length + 1) :=
            ⟨S.path.length, Nat.lt_succ_self _⟩
          by_cases hheartLast : ∃ heart, ¬ T.IsMinusTwoVertex heart ∧
              T.intersectionGraph.Adj (S.path.vertex last) heart
          · obtain ⟨heart, hheartNon, hheartAdj⟩ := hheartLast
            exact S.hasNearHeartMaximum_of_prefix_dist last.val branch.val
              (by omega) (by omega) (by simpa using hmax) hheartNon
              hheartAdj.symm (S.path.minusTwo last) SimpleGraph.Walk.nil
              (by
                have := S.length_four
                simp [last, branch, Nat.dist]
                omega)
          by_cases hheartExtra : ∃ heart, ¬ T.IsMinusTwoVertex heart ∧
              T.intersectionGraph.Adj S.extra heart
          · obtain ⟨heart, hheartNon, hheartAdj⟩ := hheartExtra
            have hextraBranch : T.minusTwoGraph.Adj S.extra
                (S.path.vertex branch) := by
              exact ⟨S.extra_minusTwo, S.path.minusTwo branch,
                by simpa [branch] using S.extra_adjacent.symm⟩
            let extraPrefix : T.minusTwoGraph.Walk S.extra (S.path.vertex branch) :=
              (SimpleGraph.Walk.nil : T.minusTwoGraph.Walk
                (S.path.vertex branch) (S.path.vertex branch)).cons hextraBranch
            exact S.hasNearHeartMaximum_of_prefix_dist branch.val branch.val
              (by omega) (by omega) (by simpa using hmax) hheartNon
              hheartAdj.symm S.extra_minusTwo extraPrefix (by simp [extraPrefix])
          · have hnoHeartLast : ∀ heart, ¬ T.IsMinusTwoVertex heart →
                ¬ T.intersectionGraph.Adj (S.path.vertex last) heart := by
              intro heart hheartNon hheartAdj
              exact hheartLast ⟨heart, hheartNon, hheartAdj⟩
            have hnoHeartExtra : ∀ heart, ¬ T.IsMinusTwoVertex heart →
                ¬ T.intersectionGraph.Adj S.extra heart := by
              intro heart hheartNon hheartAdj
              exact hheartExtra ⟨heart, hheartNon, hheartAdj⟩
            have heq := S.branch_prev_eq_of_maximum_no_heart hcard
              (by simpa [branch] using hmax) (by simpa [branch] using hnoHeart)
              (by simpa [last] using hnoHeartLast) hnoHeartExtra
            let s' : Fin (S.path.length + 1) :=
              ⟨S.path.length - 2, by omega⟩
            have hmax' : ∀ i ∈ C.vertices,
                T.multiplicity i ≤ T.multiplicity (S.path.vertex s') := by
              intro i hi
              simpa [s', heq, branch] using hmax i hi
            exact ih (b.val.dist s'.val)
              (by
                calc
                  b.val.dist s'.val = b.val.dist (S.path.length - 2) := by simp [s']
                  _ < b.val.dist (S.path.length - 1) :=
                    endFork_dist_pred_lt_of_lt hblt
                  _ = d := hd)
              s' hmax' rfl
        have hsleft : 1 < s.val := by omega
        have hsright : s.val < S.path.length - 1 := by omega
        have heq := S.central_neighbors_eq_of_maximum_no_heart hcard s.val
          hsleft hsright (by simpa using hmax) (by simpa using hnoHeart)
        by_cases hbs : b.val < s.val
        · let s' : Fin (S.path.length + 1) := ⟨s.val - 1, by omega⟩
          have hmax' : ∀ i ∈ C.vertices,
              T.multiplicity i ≤ T.multiplicity (S.path.vertex s') := by
            intro i hi
            simpa [s', heq.1] using hmax i hi
          exact ih (b.val.dist s'.val)
            (by
              calc
                b.val.dist s'.val = b.val.dist (s.val - 1) := by simp [s']
                _ < b.val.dist s.val := endFork_dist_pred_lt_of_lt hbs
                _ = d := hd)
            s' hmax' rfl
        · have hsb : s.val < b.val := by
            have hsne : s.val ≠ b.val := by
              intro heqSB
              apply hnear
              have hp : stem.length ≤ 1 := hstem
              rw [heqSB]
              simp
              omega
            omega
          let s' : Fin (S.path.length + 1) := ⟨s.val + 1, by omega⟩
          have hmax' : ∀ i ∈ C.vertices,
              T.multiplicity i ≤ T.multiplicity (S.path.vertex s') := by
            intro i hi
            simpa [s', heq.2] using hmax i hi
          exact ih (b.val.dist s'.val)
            (by
              calc
                b.val.dist s'.val = b.val.dist (s.val + 1) := by simp [s']
                _ < b.val.dist s.val := endFork_dist_succ_lt_of_lt hsb
                _ = d := hd)
            s' hmax' rfl
  obtain ⟨peak, hpeak, hmaxPeak⟩ := C.exists_multiplicity_maximum
  rcases S.covers peak hpeak with ⟨s, hs⟩ | hs
  · apply pathMaximumNear s
    simpa [hs] using hmaxPeak
  · subst peak
    by_cases hheartExtra : ∃ heart, ¬ T.IsMinusTwoVertex heart ∧
        T.intersectionGraph.Adj S.extra heart
    · obtain ⟨heart, hheartNon, hheartAdj⟩ := hheartExtra
      apply C.hasNearHeartMaximum_of_hasHeartMaximum
      exact ⟨S.extra, S.mem_extra, hmaxPeak, heart, hheartNon, hheartAdj⟩
    · have hnoHeartExtra : ∀ heart, ¬ T.IsMinusTwoVertex heart →
          ¬ T.intersectionGraph.Adj S.extra heart := by
        intro heart hheartNon hheartAdj
        exact hheartExtra ⟨heart, hheartNon, hheartAdj⟩
      have heq := S.extra_neighbor_eq_of_maximum_no_heart hcard hmaxPeak hnoHeartExtra
      let branch : Fin (S.path.length + 1) :=
        ⟨S.path.length - 1, by omega⟩
      apply pathMaximumNear branch
      intro i hi
      simpa [branch, heq] using hmaxPeak i hi

/-- Every pair of vertices in a closed `(-2)` cluster can be joined internally using
at most `diameter` edges. -/
def MinusTwoCluster.HasInternalDiameterAtMost {T : NumericalType}
    (C : T.MinusTwoCluster) (diameter : ℕ) : Prop :=
  ∀ i ∈ C.vertices, ∀ j ∈ C.vertices,
    ∃ W : T.minusTwoGraph.Walk i j, W.length ≤ diameter

lemma exists_heart_chain_length_le_of_cluster_diameter (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    {target : T.Component} (htarget : T.IsMinusTwoVertex target) {diameter : ℕ}
    (hdiameter : (T.minusTwoClusterAt target htarget).HasInternalDiameterAtMost
      diameter) :
    ∃ source, ¬ T.IsMinusTwoVertex source ∧
      ∃ chain : T.MinusTwoChain source target, chain.length ≤ diameter + 1 := by
  let C := T.minusTwoClusterAt target htarget
  obtain ⟨start, hstartMem, source, hsource, hstartSource⟩ :=
    C.meets_heart hcard hgenus
  have htargetMem : target ∈ C.vertices := by simp [C, minusTwoClusterAt]
  obtain ⟨W, hW⟩ := hdiameter start hstartMem target htargetMem
  let chain := T.minusTwoChainOfWalk hstartSource.symm
    (C.minusTwo start hstartMem) W
  refine ⟨source, hsource, chain, ?_⟩
  simp [chain, minusTwoChainOfWalk]
  omega

/-- Every `(-2)` target is connected to the non-`(-2)` heart by a simple chain whose
length is at most the total number of components. -/
lemma exists_heart_chain_length_le_card (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    {target : T.Component} (htarget : T.IsMinusTwoVertex target) :
    ∃ source, ¬ T.IsMinusTwoVertex source ∧
      ∃ C : T.MinusTwoChain source target, C.length ≤ Nat.card T.Component := by
  let C := T.minusTwoClusterAt target htarget
  obtain ⟨start, hstartMem, source, hsource, hstartSource⟩ :=
    C.meets_heart hcard hgenus
  have htargetMem : target ∈ C.vertices := by
    simp [C, minusTwoClusterAt]
  have hreach : T.minusTwoGraph.Reachable start target := by
    exact T.minusTwoClusterAt_reachable htarget hstartMem htargetMem
  obtain ⟨W, hW⟩ := hreach.exists_isPath
  let chain := T.minusTwoChainOfWalk hstartSource.symm
    (C.minusTwo start hstartMem) W
  refine ⟨source, hsource, chain, ?_⟩
  change W.length + 1 ≤ Nat.card T.Component
  rw [Nat.card_eq_fintype_card]
  exact Nat.succ_le_iff.mpr hW.length_lt

/-- The canonical heart-to-target chain uses no more edges than there are vertices in
the target's connected `(-2)` cluster. -/
lemma exists_heart_chain_length_le_cluster_card (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    {target : T.Component} (htarget : T.IsMinusTwoVertex target) :
    ∃ source, ¬ T.IsMinusTwoVertex source ∧
      ∃ chain : T.MinusTwoChain source target,
        chain.length ≤ (T.minusTwoClusterAt target htarget).vertices.card := by
  let C := T.minusTwoClusterAt target htarget
  obtain ⟨start, hstartMem, source, hsource, hstartSource⟩ :=
    C.meets_heart hcard hgenus
  have htargetMem : target ∈ C.vertices := by simp [C, minusTwoClusterAt]
  have hreach : T.minusTwoGraph.Reachable start target :=
    T.minusTwoClusterAt_reachable htarget hstartMem htargetMem
  obtain ⟨W, hW⟩ := hreach.exists_isPath
  have hrootStart : T.minusTwoGraph.Reachable target start :=
    (T.mem_minusTwoClusterVertices_iff target start).mp hstartMem
  let f : Fin (W.length + 1) → {i // i ∈ C.vertices} := fun r =>
    ⟨W.getVert r.val, (T.mem_minusTwoClusterVertices_iff target _).mpr <|
      hrootStart.trans ⟨W.take r.val⟩⟩
  have hf : Function.Injective f := by
    intro r s hrs
    apply Fin.ext
    apply hW.getVert_injOn
    · simp only [Set.mem_ofPred_eq]
      omega
    · simp only [Set.mem_ofPred_eq]
      omega
    · exact congrArg Subtype.val hrs
  have hpathCard := Fintype.card_le_of_injective f hf
  have hpathCard' : W.length + 1 ≤ C.vertices.card := by
    simpa [Fintype.card_coe] using hpathCard
  let chain := T.minusTwoChainOfWalk hstartSource.symm
    (C.minusTwo start hstartMem) W
  refine ⟨source, hsource, chain, ?_⟩
  simpa [chain, minusTwoChainOfWalk] using hpathCard'

/-- Iterating the edge estimate along a `(-2)` chain costs at most one factor of two per
edge. -/
lemma MinusTwoChain.diagonalProduct_vertex_le {T : NumericalType}
    {source target : T.Component} (C : T.MinusTwoChain source target)
    (k : ℕ) (hk : k ≤ C.length) :
    T.diagonalProduct (C.vertex ⟨k, by omega⟩) ≤
      (2 : ℤ) ^ k * T.diagonalProduct source := by
  induction k with
  | zero =>
      rw [pow_zero, one_mul]
      rw [Fin.zero_eta, C.source_eq]
  | succ k ih =>
      have hklt : k < C.length := by omega
      let r : Fin C.length := ⟨k, hklt⟩
      have hstep := T.diagonalProduct_le_two_mul_of_adj_minusTwo
        (C.minusTwo r) (C.adjacent r).symm
      have hprev := ih (by omega)
      change T.diagonalProduct (C.vertex r.succ) ≤
        (2 : ℤ) ^ (k + 1) * T.diagonalProduct source
      calc
        T.diagonalProduct (C.vertex r.succ) ≤
            2 * T.diagonalProduct (C.vertex r.castSucc) := hstep
        _ ≤ 2 * ((2 : ℤ) ^ k * T.diagonalProduct source) :=
          mul_le_mul_of_nonneg_left hprev (by norm_num)
        _ = (2 : ℤ) ^ (k + 1) * T.diagonalProduct source := by
          rw [pow_succ]
          ring

lemma MinusTwoChain.diagonalProduct_target_le {T : NumericalType}
    {source target : T.Component} (C : T.MinusTwoChain source target) :
    T.diagonalProduct target ≤
      (2 : ℤ) ^ C.length * T.diagonalProduct source := by
  have h := C.diagonalProduct_vertex_le C.length le_rfl
  calc
    T.diagonalProduct target =
        T.diagonalProduct (C.vertex ⟨C.length, by omega⟩) := by rw [C.target_eq]
    _ ≤ _ := h

/-- The short-chain part of Stacks Project tag `0C9W`: every `(-2)` component reached
from a non-`(-2)` component in at most seven edges satisfies the `768g` bound. -/
lemma diagonalProduct_le_768_genus_of_short_chain (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component)
    (hgenus : 2 ≤ T.arithmeticGenus) {source target : T.Component}
    (hsource : ¬ T.IsMinusTwoVertex source)
    (C : T.MinusTwoChain source target) (hlen : C.length ≤ 7) :
    T.diagonalProduct target ≤ 768 * T.arithmeticGenus := by
  have hsourceBound := T.diagonalProduct_le_six_genus_sub_one hmin hcard hsource
  change T.diagonalProduct source ≤ 6 * (T.arithmeticGenus - 1) at hsourceBound
  have hchain := C.diagonalProduct_target_le
  have hpow : ((2 : ℤ) ^ C.length) ≤ 128 := by
    interval_cases C.length <;> norm_num
  have hgenusNonneg : 0 ≤ T.arithmeticGenus := by omega
  have hbudgetNonneg : 0 ≤ T.arithmeticGenus - 1 := by omega
  have hsourceNonneg := T.diagonalProduct_nonnegative source
  calc
    T.diagonalProduct target ≤
        (2 : ℤ) ^ C.length * T.diagonalProduct source := hchain
    _ ≤ (2 : ℤ) ^ C.length * (6 * (T.arithmeticGenus - 1)) :=
      mul_le_mul_of_nonneg_left hsourceBound (by positivity)
    _ ≤ 128 * (6 * (T.arithmeticGenus - 1)) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ 768 * T.arithmeticGenus := by nlinarith

/-- A canonical `(-2)` cluster of internal diameter at most six satisfies the global
`768g` bound. This is the short-chain bridge for the finite `E₆/E₇/E₈` cases. -/
lemma diagonalProduct_le_768_genus_of_cluster_diameter_le_six
    (T : NumericalType) (hmin : T.IsMinimal)
    (hcard : 1 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    {target : T.Component} (htarget : T.IsMinusTwoVertex target)
    (hdiameter : (T.minusTwoClusterAt target htarget).HasInternalDiameterAtMost 6) :
    T.diagonalProduct target ≤ 768 * T.arithmeticGenus := by
  obtain ⟨source, hsource, chain, hchain⟩ :=
    T.exists_heart_chain_length_le_of_cluster_diameter hcard hgenus htarget hdiameter
  exact T.diagonalProduct_le_768_genus_of_short_chain hmin hcard hgenus hsource chain
    (by omega)

/-- If the entire numerical type has at most seven components, every component obeys
the global `768g` diagonal bound. -/
lemma diagonalProduct_le_768_genus_of_card_le_seven (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component)
    (hcardUpper : Nat.card T.Component ≤ 7) (hgenus : 2 ≤ T.arithmeticGenus)
    (target : T.Component) :
    T.diagonalProduct target ≤ 768 * T.arithmeticGenus := by
  by_cases htarget : T.IsMinusTwoVertex target
  · obtain ⟨source, hsource, C, hlength⟩ :=
      T.exists_heart_chain_length_le_card hcard hgenus htarget
    exact T.diagonalProduct_le_768_genus_of_short_chain hmin hcard hgenus hsource C
      (hlength.trans hcardUpper)
  · have htargetBound := T.diagonalProduct_le_six_genus_sub_one hmin hcard htarget
    change T.diagonalProduct target ≤ 6 * (T.arithmeticGenus - 1) at htargetBound
    have hgenusNonneg : 0 ≤ T.arithmeticGenus := by omega
    nlinarith

/-- Every target in a canonical `(-2)` cluster of at most seven vertices satisfies the
`768g` bound, irrespective of the size of the ambient numerical type. -/
lemma diagonalProduct_le_768_genus_of_cluster_card_le_seven (T : NumericalType)
    (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component)
    (hgenus : 2 ≤ T.arithmeticGenus) {target : T.Component}
    (htarget : T.IsMinusTwoVertex target)
    (hclusterCard : (T.minusTwoClusterAt target htarget).vertices.card ≤ 7) :
    T.diagonalProduct target ≤ 768 * T.arithmeticGenus := by
  obtain ⟨source, hsource, chain, hchain⟩ :=
    T.exists_heart_chain_length_le_cluster_card hcard hgenus htarget
  exact T.diagonalProduct_le_768_genus_of_short_chain hmin hcard hgenus hsource chain
    (hchain.trans hclusterCard)

/-- On a long simple `(-2)` path, a multiplicity maximum controls every diagonal
product up to the factor four coming from the endpoint weights. -/
lemma SimpleMinusTwoPath.diagonalProduct_le_four_mul_of_multiplicity_maximum
    {T : NumericalType} (P : T.SimpleMinusTwoPath)
    (hcard : 5 < Nat.card T.Component) (hlen : 4 ≤ P.length)
    (peak target : Fin (P.length + 1))
    (hmax : ∀ r, (T.multiplicity (P.vertex r) : ℤ) ≤
      (T.multiplicity (P.vertex peak) : ℤ)) :
    T.diagonalProduct (P.vertex target) ≤ 4 * T.diagonalProduct (P.vertex peak) := by
  have hweightNat := P.vertex_weight_le_four_mul_vertex hcard hlen
    target.val peak.val (by omega) (by omega)
  have hweight : (T.weight (P.vertex target) : ℤ) ≤
      4 * (T.weight (P.vertex peak) : ℤ) := by exact_mod_cast hweightNat
  have hmult := hmax target
  have hmultNonneg : (0 : ℤ) ≤ (T.multiplicity (P.vertex target) : ℤ) := by positivity
  have hmultPeakNonneg : (0 : ℤ) ≤ (T.multiplicity (P.vertex peak) : ℤ) := by positivity
  have hweightNonneg : (0 : ℤ) ≤ (T.weight (P.vertex target) : ℤ) := by positivity
  have hmass : T.vertexMass (P.vertex target) ≤ 4 * T.vertexMass (P.vertex peak) := by
    dsimp [vertexMass]
    calc
      (T.multiplicity (P.vertex target) : ℤ) * (T.weight (P.vertex target) : ℤ) ≤
          (T.multiplicity (P.vertex peak) : ℤ) *
            (T.weight (P.vertex target) : ℤ) :=
        mul_le_mul_of_nonneg_right hmult hweightNonneg
      _ ≤ (T.multiplicity (P.vertex peak) : ℤ) *
            (4 * (T.weight (P.vertex peak) : ℤ)) :=
        mul_le_mul_of_nonneg_left hweight hmultPeakNonneg
      _ = 4 * T.vertexMass (P.vertex peak) := by simp [vertexMass]; ring
  rw [T.diagonalProduct_eq_two_vertexMass_of_minusTwo (P.minusTwo target),
    T.diagonalProduct_eq_two_vertexMass_of_minusTwo (P.minusTwo peak)]
  nlinarith

/-- The long-path part of the `768g` estimate, assuming a maximum-multiplicity path
vertex meets the bounded non-`(-2)` heart. -/
lemma SimpleMinusTwoPath.diagonalProduct_le_768_genus_of_maximum_adjacent_heart
    {T : NumericalType} (P : T.SimpleMinusTwoPath)
    (hmin : T.IsMinimal) (hcard : 5 < Nat.card T.Component)
    (hgenus : 2 ≤ T.arithmeticGenus) (hlen : 4 ≤ P.length)
    (peak target : Fin (P.length + 1))
    (hmax : ∀ r, (T.multiplicity (P.vertex r) : ℤ) ≤
      (T.multiplicity (P.vertex peak) : ℤ))
    {source : T.Component} (hsource : ¬ T.IsMinusTwoVertex source)
    (hadj : T.intersectionGraph.Adj (P.vertex peak) source) :
    T.diagonalProduct (P.vertex target) ≤ 768 * T.arithmeticGenus := by
  have hsourceBound := T.diagonalProduct_le_six_genus_sub_one hmin (by omega) hsource
  change T.diagonalProduct source ≤ 6 * (T.arithmeticGenus - 1) at hsourceBound
  have hpeakMass : T.vertexMass (P.vertex peak) ≤ T.diagonalProduct source :=
    T.vertexMass_le_diagonalProduct hadj
  have hweightNat := P.vertex_weight_le_four_mul_vertex hcard hlen
    target.val peak.val (by omega) (by omega)
  have hweight : (T.weight (P.vertex target) : ℤ) ≤
      4 * (T.weight (P.vertex peak) : ℤ) := by exact_mod_cast hweightNat
  have hmult := hmax target
  have hmultNonneg : (0 : ℤ) ≤ (T.multiplicity (P.vertex target) : ℤ) := by positivity
  have hmultPeakNonneg : (0 : ℤ) ≤ (T.multiplicity (P.vertex peak) : ℤ) := by positivity
  have hweightNonneg : (0 : ℤ) ≤ (T.weight (P.vertex target) : ℤ) := by positivity
  have hweightPeakNonneg : (0 : ℤ) ≤ (T.weight (P.vertex peak) : ℤ) := by positivity
  have hmass : T.vertexMass (P.vertex target) ≤ 4 * T.vertexMass (P.vertex peak) := by
    dsimp [vertexMass]
    calc
      (T.multiplicity (P.vertex target) : ℤ) * (T.weight (P.vertex target) : ℤ) ≤
          (T.multiplicity (P.vertex peak) : ℤ) *
            (T.weight (P.vertex target) : ℤ) :=
        mul_le_mul_of_nonneg_right hmult hweightNonneg
      _ ≤ (T.multiplicity (P.vertex peak) : ℤ) *
            (4 * (T.weight (P.vertex peak) : ℤ)) :=
        mul_le_mul_of_nonneg_left hweight hmultPeakNonneg
      _ = 4 * ((T.multiplicity (P.vertex peak) : ℤ) *
            (T.weight (P.vertex peak) : ℤ)) := by ring
  rw [T.diagonalProduct_eq_two_vertexMass_of_minusTwo (P.minusTwo target)]
  have hgenusNonneg : 0 ≤ T.arithmeticGenus := by omega
  calc
    2 * T.vertexMass (P.vertex target) ≤ 8 * T.vertexMass (P.vertex peak) := by
      nlinarith
    _ ≤ 8 * T.diagonalProduct source := mul_le_mul_of_nonneg_left hpeakMass (by norm_num)
    _ ≤ 8 * (6 * (T.arithmeticGenus - 1)) :=
      mul_le_mul_of_nonneg_left hsourceBound (by norm_num)
    _ ≤ 768 * T.arithmeticGenus := by nlinarith

/-- Once a canonical `(-2)` cluster has a heart-exposed maximum, its target satisfies
the `768g` bound. This isolates the remaining structural content of tag `0C9W`. -/
lemma diagonalProduct_le_768_genus_of_cluster_hasHeartMaximum
    (T : NumericalType) (hmin : T.IsMinimal)
    (hcard : 5 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    {target : T.Component} (htarget : T.IsMinusTwoVertex target)
    (hcluster : (T.minusTwoClusterAt target htarget).HasHeartMaximum) :
    T.diagonalProduct target ≤ 768 * T.arithmeticGenus := by
  let C := T.minusTwoClusterAt target htarget
  obtain ⟨peak, hpeakMem, hmax, source, hsource, hpeakSource⟩ := hcluster
  have htargetMem : target ∈ C.vertices := by
    simp [C, minusTwoClusterAt]
  have hreach : T.minusTwoGraph.Reachable peak target := by
    exact T.minusTwoClusterAt_reachable htarget hpeakMem htargetMem
  obtain ⟨W, hW⟩ := hreach.exists_isPath
  by_cases hlength : 4 ≤ W.length
  · let P := T.simpleMinusTwoPathOfWalk W hW (C.minusTwo peak hpeakMem)
    have hPmax : ∀ r,
        (T.multiplicity (P.vertex r) : ℤ) ≤
          (T.multiplicity (P.vertex 0) : ℤ) := by
      intro r
      have hrReach : T.minusTwoGraph.Reachable target (W.getVert r.val) := by
        have hrootPeak : T.minusTwoGraph.Reachable target peak := by
          exact (T.mem_minusTwoClusterVertices_iff target peak).mp hpeakMem
        have hpeakR : T.minusTwoGraph.Reachable peak (W.getVert r.val) := by
          refine ⟨?_⟩
          exact W.take r.val
        exact hrootPeak.trans hpeakR
      have hrMem : W.getVert r.val ∈ C.vertices := by
        exact (T.mem_minusTwoClusterVertices_iff target _).mpr hrReach
      have hmaxNat := hmax (W.getVert r.val) hrMem
      change (T.multiplicity (W.getVert r.val) : ℤ) ≤
        (T.multiplicity (W.getVert 0) : ℤ)
      simpa using hmaxNat
    let last : Fin (P.length + 1) := ⟨W.length, by
      change W.length < W.length + 1
      omega⟩
    have hbound := P.diagonalProduct_le_768_genus_of_maximum_adjacent_heart
      hmin hcard hgenus hlength (0 : Fin (P.length + 1))
      last hPmax hsource
      (by simpa [P] using hpeakSource)
    change T.diagonalProduct (W.getVert W.length) ≤ 768 * T.arithmeticGenus at hbound
    simpa using hbound
  · let chain := T.minusTwoChainOfWalk hpeakSource.symm
      (C.minusTwo peak hpeakMem) W
    exact T.diagonalProduct_le_768_genus_of_short_chain hmin (by omega) hgenus
      hsource chain (by simp [chain, minusTwoChainOfWalk]; omega)

/-- A near-heart multiplicity maximum suffices for the full cluster `768g` estimate. -/
lemma diagonalProduct_le_768_genus_of_cluster_hasNearHeartMaximum
    (T : NumericalType) (hmin : T.IsMinimal)
    (hcard : 5 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    {target : T.Component} (htarget : T.IsMinusTwoVertex target)
    (hcluster : (T.minusTwoClusterAt target htarget).HasNearHeartMaximum) :
    T.diagonalProduct target ≤ 768 * T.arithmeticGenus := by
  let C := T.minusTwoClusterAt target htarget
  obtain ⟨peak, hpeakMem, hmax, source, hsource, peakChain, hpeakLength⟩ := hcluster
  have hsourceBound := T.diagonalProduct_le_six_genus_sub_one hmin (by omega) hsource
  change T.diagonalProduct source ≤ 6 * (T.arithmeticGenus - 1) at hsourceBound
  have hpeakProp := peakChain.diagonalProduct_target_le
  have hpeakPow : ((2 : ℤ) ^ peakChain.length) ≤ 16 := by
    interval_cases peakChain.length <;> norm_num
  have hpeakBound : T.diagonalProduct peak ≤ 96 * (T.arithmeticGenus - 1) := by
    calc
      T.diagonalProduct peak ≤
          (2 : ℤ) ^ peakChain.length * T.diagonalProduct source := hpeakProp
      _ ≤ (2 : ℤ) ^ peakChain.length * (6 * (T.arithmeticGenus - 1)) :=
        mul_le_mul_of_nonneg_left hsourceBound (by positivity)
      _ ≤ 16 * (6 * (T.arithmeticGenus - 1)) :=
        mul_le_mul_of_nonneg_right hpeakPow (by omega)
      _ = 96 * (T.arithmeticGenus - 1) := by ring
  have htargetMem : target ∈ C.vertices := by simp [C, minusTwoClusterAt]
  have hreach : T.minusTwoGraph.Reachable peak target :=
    T.minusTwoClusterAt_reachable htarget hpeakMem htargetMem
  obtain ⟨W, hW⟩ := hreach.exists_isPath
  have hPmax (r : ℕ) :
      (T.multiplicity (W.getVert r) : ℤ) ≤ (T.multiplicity peak : ℤ) := by
    have hrReach : T.minusTwoGraph.Reachable target (W.getVert r) := by
      have hrootPeak : T.minusTwoGraph.Reachable target peak :=
        (T.mem_minusTwoClusterVertices_iff target peak).mp hpeakMem
      exact hrootPeak.trans ⟨W.take r⟩
    have hrMem : W.getVert r ∈ C.vertices :=
      (T.mem_minusTwoClusterVertices_iff target _).mpr hrReach
    exact_mod_cast hmax (W.getVert r) hrMem
  by_cases hlength : 4 ≤ W.length
  · let P := T.simpleMinusTwoPathOfWalk W hW (C.minusTwo peak hpeakMem)
    have hPmax' : ∀ r,
        (T.multiplicity (P.vertex r) : ℤ) ≤
          (T.multiplicity (P.vertex 0) : ℤ) := by
      intro r
      change (T.multiplicity (W.getVert r.val) : ℤ) ≤
        (T.multiplicity (W.getVert 0) : ℤ)
      simpa using hPmax r.val
    let last : Fin (P.length + 1) := ⟨W.length, by
      change W.length < W.length + 1
      omega⟩
    have hpath := P.diagonalProduct_le_four_mul_of_multiplicity_maximum
      hcard hlength (0 : Fin (P.length + 1)) last hPmax'
    change T.diagonalProduct (W.getVert W.length) ≤
      4 * T.diagonalProduct (W.getVert 0) at hpath
    have hgenusNonneg : 0 ≤ T.arithmeticGenus := by omega
    simpa using (show T.diagonalProduct target ≤ 768 * T.arithmeticGenus by
      rw [W.getVert_length] at hpath
      simpa using (calc
        T.diagonalProduct target ≤ 4 * T.diagonalProduct peak := by simpa using hpath
        _ ≤ 4 * (96 * (T.arithmeticGenus - 1)) :=
          mul_le_mul_of_nonneg_left hpeakBound (by norm_num)
        _ ≤ 768 * T.arithmeticGenus := by nlinarith))
  · let targetChain := T.minusTwoChainOfMinusTwoWalk W (C.minusTwo peak hpeakMem)
    have htargetProp := targetChain.diagonalProduct_target_le
    have htargetLength : targetChain.length < 4 := by
      simpa [targetChain, minusTwoChainOfMinusTwoWalk] using lt_of_not_ge hlength
    have htargetPow : ((2 : ℤ) ^ targetChain.length) ≤ 8 := by
      interval_cases targetChain.length <;> norm_num
    have hgenusNonneg : 0 ≤ T.arithmeticGenus := by omega
    calc
      T.diagonalProduct target ≤
          (2 : ℤ) ^ targetChain.length * T.diagonalProduct peak := htargetProp
      _ ≤ (2 : ℤ) ^ targetChain.length * (96 * (T.arithmeticGenus - 1)) :=
        mul_le_mul_of_nonneg_left hpeakBound (by positivity)
      _ ≤ 8 * (96 * (T.arithmeticGenus - 1)) :=
        mul_le_mul_of_nonneg_right htargetPow (by omega)
      _ ≤ 768 * T.arithmeticGenus := by nlinarith

/-- Every target in an exact long path-shaped canonical `(-2)` cluster satisfies the
global `768g` bound. This closes the long `A/B/C` families in tag `0C9W`. -/
lemma diagonalProduct_le_768_genus_of_cluster_pathShape
    (T : NumericalType) (hmin : T.IsMinimal)
    (hcard : 5 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    {target : T.Component} (htarget : T.IsMinusTwoVertex target)
    (S : (T.minusTwoClusterAt target htarget).PathShape) :
    T.diagonalProduct target ≤ 768 * T.arithmeticGenus := by
  exact T.diagonalProduct_le_768_genus_of_cluster_hasNearHeartMaximum
    hmin hcard hgenus htarget (S.hasNearHeartMaximum hcard hgenus)

/-- Every target in an exact long end-fork canonical `(-2)` cluster satisfies the
global `768g` bound. This closes the unbounded `D` family in tag `0C9W`. -/
lemma diagonalProduct_le_768_genus_of_cluster_endForkShape
    (T : NumericalType) (hmin : T.IsMinimal)
    (hcard : 5 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    {target : T.Component} (htarget : T.IsMinusTwoVertex target)
    (S : (T.minusTwoClusterAt target htarget).EndForkShape) :
    T.diagonalProduct target ≤ 768 * T.arithmeticGenus := by
  exact T.diagonalProduct_le_768_genus_of_cluster_hasNearHeartMaximum
    hmin hcard hgenus htarget (S.hasNearHeartMaximum hcard hgenus)

set_option maxHeartbeats 800000 in
-- The explicit injectivity check enumerates all pairs of eight diagram vertices.
/-- Three disjoint paths of lengths at least `1`, `3`, and `3` from a common
`(-2)` center would contain the forbidden affine `E₇` diagram. -/
lemma no_affineE7_of_three_paths (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    {c u v w : T.Component} {p : T.minusTwoGraph.Walk c u}
    {q : T.minusTwoGraph.Walk c v} {r : T.minusTwoGraph.Walk c w}
    (hc : T.IsMinusTwoVertex c) (hp : p.IsPath) (hq : q.IsPath)
    (hr : r.IsPath) (hpLength : 1 ≤ p.length) (hqLength : 3 ≤ q.length)
    (hrLength : 3 ≤ r.length) (hpq : p.snd ≠ q.snd)
    (hpr : p.snd ≠ r.snd) (hqr : q.snd ≠ r.snd) : False := by
  let copy : Fin 8 → T.Component :=
    ![c, p.getVert 1, q.getVert 1, q.getVert 2, q.getVert 3,
      r.getVert 1, r.getVert 2, r.getVert 3]
  have hpathStart {x y : T.Component} {a : T.minusTwoGraph.Walk x y}
      (ha : a.IsPath) (i : ℕ) (hi : 0 < i) (hile : i ≤ a.length) :
      x ≠ a.getVert i := by
    intro heq
    have hindex := ha.getVert_injOn (by simp) (by simp; omega)
      (a.getVert_zero.trans heq)
    omega
  have hpathNe {x y : T.Component} {a : T.minusTwoGraph.Walk x y}
      (ha : a.IsPath) (i j : ℕ) (hi : i ≤ a.length) (hj : j ≤ a.length)
      (hij : i ≠ j) : a.getVert i ≠ a.getVert j := by
    intro heq
    exact hij (ha.getVert_injOn (by simp; omega) (by simp; omega) heq)
  have hpq' (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
      p.getVert i ≠ q.getVert j := getVert_ne_getVert_of_snd_ne_of_isAcyclic
        (T.minusTwoGraph_isAcyclic hcard hgenus) hp hq hpq i j hi hj
  have hpr' (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
      p.getVert i ≠ r.getVert j := getVert_ne_getVert_of_snd_ne_of_isAcyclic
        (T.minusTwoGraph_isAcyclic hcard hgenus) hp hr hpr i j hi hj
  have hqr' (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
      q.getVert i ≠ r.getVert j := getVert_ne_getVert_of_snd_ne_of_isAcyclic
        (T.minusTwoGraph_isAcyclic hcard hgenus) hq hr hqr i j hi hj
  have hcopy : Function.Injective copy := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, zero_ne_one,
        Fin.reduceFinMk, Fin.reduceEq] at hij ⊢
    all_goals first
      | exact (hpathStart hp _ (by omega) (by omega)) hij
      | exact (hpathStart hp _ (by omega) (by omega)) hij.symm
      | exact (hpathStart hq _ (by omega) (by omega)) hij
      | exact (hpathStart hq _ (by omega) (by omega)) hij.symm
      | exact (hpathStart hr _ (by omega) (by omega)) hij
      | exact (hpathStart hr _ (by omega) (by omega)) hij.symm
      | exact (hpathNe hq _ _ (by omega) (by omega) (by omega)) hij
      | exact (hpathNe hr _ _ (by omega) (by omega) (by omega)) hij
      | exact (hpq' _ _ (by omega) (by omega)) hij
      | exact (hpq' _ _ (by omega) (by omega)) hij.symm
      | exact (hpr' _ _ (by omega) (by omega)) hij
      | exact (hpr' _ _ (by omega) (by omega)) hij.symm
      | exact (hqr' _ _ (by omega) (by omega)) hij
      | exact (hqr' _ _ (by omega) (by omega)) hij.symm
  have hminus (i : Fin 8) : T.IsMinusTwoVertex (copy i) := by
    fin_cases i
    · exact hc
    · exact T.minusTwo_of_getVert_minusTwoWalk p hc 1
    · exact T.minusTwo_of_getVert_minusTwoWalk q hc 1
    · exact T.minusTwo_of_getVert_minusTwoWalk q hc 2
    · exact T.minusTwo_of_getVert_minusTwoWalk q hc 3
    · exact T.minusTwo_of_getVert_minusTwoWalk r hc 1
    · exact T.minusTwo_of_getVert_minusTwoWalk r hc 2
    · exact T.minusTwo_of_getVert_minusTwoWalk r hc 3
  obtain ⟨heart, hheart⟩ :=
    T.exists_nonMinusTwo_of_two_le_arithmeticGenus hcard hgenus
  apply T.no_affineE7_configuration copy hcopy
    ⟨heart, fun i heq ↦ hheart (heq ▸ hminus i)⟩ hminus
  intro i j hj
  fin_cases i <;> fin_cases j <;> simp [affineE7Neighbors] at hj
  all_goals first
    | simpa [copy] using (p.adj_getVert_succ (i := 0) (by omega)).2.2
    | simpa [copy] using (p.adj_getVert_succ (i := 0) (by omega)).2.2.symm
    | simpa [copy] using (q.adj_getVert_succ (i := 0) (by omega)).2.2
    | simpa [copy] using (q.adj_getVert_succ (i := 0) (by omega)).2.2.symm
    | simpa [copy] using (q.adj_getVert_succ (i := 1) (by omega)).2.2
    | simpa [copy] using (q.adj_getVert_succ (i := 1) (by omega)).2.2.symm
    | simpa [copy] using (q.adj_getVert_succ (i := 2) (by omega)).2.2
    | simpa [copy] using (q.adj_getVert_succ (i := 2) (by omega)).2.2.symm
    | simpa [copy] using (r.adj_getVert_succ (i := 0) (by omega)).2.2
    | simpa [copy] using (r.adj_getVert_succ (i := 0) (by omega)).2.2.symm
    | simpa [copy] using (r.adj_getVert_succ (i := 1) (by omega)).2.2
    | simpa [copy] using (r.adj_getVert_succ (i := 1) (by omega)).2.2.symm
    | simpa [copy] using (r.adj_getVert_succ (i := 2) (by omega)).2.2
    | simpa [copy] using (r.adj_getVert_succ (i := 2) (by omega)).2.2.symm

set_option maxHeartbeats 800000 in
-- The explicit injectivity check enumerates all pairs of nine diagram vertices.
/-- Three disjoint paths of lengths at least `1`, `2`, and `5` from a common
`(-2)` center would contain the forbidden affine `E₈` diagram. -/
lemma no_affineE8_of_three_paths (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    {c u v w : T.Component} {p : T.minusTwoGraph.Walk c u}
    {q : T.minusTwoGraph.Walk c v} {r : T.minusTwoGraph.Walk c w}
    (hc : T.IsMinusTwoVertex c) (hp : p.IsPath) (hq : q.IsPath)
    (hr : r.IsPath) (hpLength : 1 ≤ p.length) (hqLength : 2 ≤ q.length)
    (hrLength : 5 ≤ r.length) (hpq : p.snd ≠ q.snd)
    (hpr : p.snd ≠ r.snd) (hqr : q.snd ≠ r.snd) : False := by
  let copy : Fin 9 → T.Component :=
    ![c, p.getVert 1, q.getVert 1, q.getVert 2, r.getVert 1,
      r.getVert 2, r.getVert 3, r.getVert 4, r.getVert 5]
  have hpathStart {x y : T.Component} {a : T.minusTwoGraph.Walk x y}
      (ha : a.IsPath) (i : ℕ) (hi : 0 < i) (hile : i ≤ a.length) :
      x ≠ a.getVert i := by
    intro heq
    have hindex := ha.getVert_injOn (by simp) (by simp; omega)
      (a.getVert_zero.trans heq)
    omega
  have hpathNe {x y : T.Component} {a : T.minusTwoGraph.Walk x y}
      (ha : a.IsPath) (i j : ℕ) (hi : i ≤ a.length) (hj : j ≤ a.length)
      (hij : i ≠ j) : a.getVert i ≠ a.getVert j := by
    intro heq
    exact hij (ha.getVert_injOn (by simp; omega) (by simp; omega) heq)
  have hpq' (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
      p.getVert i ≠ q.getVert j := getVert_ne_getVert_of_snd_ne_of_isAcyclic
        (T.minusTwoGraph_isAcyclic hcard hgenus) hp hq hpq i j hi hj
  have hpr' (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
      p.getVert i ≠ r.getVert j := getVert_ne_getVert_of_snd_ne_of_isAcyclic
        (T.minusTwoGraph_isAcyclic hcard hgenus) hp hr hpr i j hi hj
  have hqr' (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
      q.getVert i ≠ r.getVert j := getVert_ne_getVert_of_snd_ne_of_isAcyclic
        (T.minusTwoGraph_isAcyclic hcard hgenus) hq hr hqr i j hi hj
  have hcopy : Function.Injective copy := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, zero_ne_one,
        Fin.reduceFinMk, Fin.reduceEq] at hij ⊢
    all_goals first
      | exact (hpathStart hp _ (by omega) (by omega)) hij
      | exact (hpathStart hp _ (by omega) (by omega)) hij.symm
      | exact (hpathStart hq _ (by omega) (by omega)) hij
      | exact (hpathStart hq _ (by omega) (by omega)) hij.symm
      | exact (hpathStart hr _ (by omega) (by omega)) hij
      | exact (hpathStart hr _ (by omega) (by omega)) hij.symm
      | exact (hpathNe hq _ _ (by omega) (by omega) (by omega)) hij
      | exact (hpathNe hr _ _ (by omega) (by omega) (by omega)) hij
      | exact (hpq' _ _ (by omega) (by omega)) hij
      | exact (hpq' _ _ (by omega) (by omega)) hij.symm
      | exact (hpr' _ _ (by omega) (by omega)) hij
      | exact (hpr' _ _ (by omega) (by omega)) hij.symm
      | exact (hqr' _ _ (by omega) (by omega)) hij
      | exact (hqr' _ _ (by omega) (by omega)) hij.symm
  have hminus (i : Fin 9) : T.IsMinusTwoVertex (copy i) := by
    fin_cases i
    · exact hc
    · exact T.minusTwo_of_getVert_minusTwoWalk p hc 1
    · exact T.minusTwo_of_getVert_minusTwoWalk q hc 1
    · exact T.minusTwo_of_getVert_minusTwoWalk q hc 2
    · exact T.minusTwo_of_getVert_minusTwoWalk r hc 1
    · exact T.minusTwo_of_getVert_minusTwoWalk r hc 2
    · exact T.minusTwo_of_getVert_minusTwoWalk r hc 3
    · exact T.minusTwo_of_getVert_minusTwoWalk r hc 4
    · exact T.minusTwo_of_getVert_minusTwoWalk r hc 5
  obtain ⟨heart, hheart⟩ :=
    T.exists_nonMinusTwo_of_two_le_arithmeticGenus hcard hgenus
  apply T.no_affineE8_configuration copy hcopy
    ⟨heart, fun i heq ↦ hheart (heq ▸ hminus i)⟩ hminus
  intro i j hj
  fin_cases i <;> fin_cases j <;> simp [affineE8Neighbors] at hj
  all_goals first
    | simpa [copy] using (p.adj_getVert_succ (i := 0) (by omega)).2.2
    | simpa [copy] using (p.adj_getVert_succ (i := 0) (by omega)).2.2.symm
    | simpa [copy] using (q.adj_getVert_succ (i := 0) (by omega)).2.2
    | simpa [copy] using (q.adj_getVert_succ (i := 0) (by omega)).2.2.symm
    | simpa [copy] using (q.adj_getVert_succ (i := 1) (by omega)).2.2
    | simpa [copy] using (q.adj_getVert_succ (i := 1) (by omega)).2.2.symm
    | simpa [copy] using (r.adj_getVert_succ (i := 0) (by omega)).2.2
    | simpa [copy] using (r.adj_getVert_succ (i := 0) (by omega)).2.2.symm
    | simpa [copy] using (r.adj_getVert_succ (i := 1) (by omega)).2.2
    | simpa [copy] using (r.adj_getVert_succ (i := 1) (by omega)).2.2.symm
    | simpa [copy] using (r.adj_getVert_succ (i := 2) (by omega)).2.2
    | simpa [copy] using (r.adj_getVert_succ (i := 2) (by omega)).2.2.symm
    | simpa [copy] using (r.adj_getVert_succ (i := 3) (by omega)).2.2
    | simpa [copy] using (r.adj_getVert_succ (i := 3) (by omega)).2.2.symm
    | simpa [copy] using (r.adj_getVert_succ (i := 4) (by omega)).2.2
    | simpa [copy] using (r.adj_getVert_succ (i := 4) (by omega)).2.2.symm

/-- The four cluster alternatives needed from the remaining `0C8Q` classification.
Each alternative already has an unconditional numerical bound. -/
def MinusTwoCluster.HasBoundedShape {T : NumericalType}
    (C : T.MinusTwoCluster) : Prop :=
  C.vertices.card ≤ 7 ∨ C.HasInternalDiameterAtMost 6 ∨
    Nonempty C.PathShape ∨ Nonempty C.EndForkShape

/-- Every canonical `(-2)` cluster has one of the four bounded shapes needed for
the global `768g` estimate. This is the finite-tree extraction step of `0C8Q`. -/
lemma minusTwoClusterAt_hasBoundedShape (T : NumericalType)
    (hcard : 5 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    {target : T.Component} (htarget : T.IsMinusTwoVertex target) :
    (T.minusTwoClusterAt target htarget).HasBoundedShape := by
  let C := T.minusTwoClusterAt target htarget
  by_cases hsmall : C.vertices.card ≤ 7
  · exact Or.inl hsmall
  right
  let G := C.internalGraph
  let _ : Nonempty {i // i ∈ C.vertices} :=
    ⟨⟨target, by simp [C, minusTwoClusterAt]⟩⟩
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hconn : G.Connected := T.minusTwoClusterAt_internalGraph_connected htarget
  let ι : G →g T.minusTwoGraph :=
    (SimpleGraph.Embedding.induce {i | i ∈ C.vertices}).toHom
  have hι : Function.Injective ι := by
    intro i j hij
    exact Subtype.ext hij
  have hacyclicMinus : T.minusTwoGraph.IsAcyclic :=
    T.minusTwoGraph_isAcyclic (by omega) hgenus
  have hacyclic : G.IsAcyclic := hacyclicMinus.induce {i | i ∈ C.vertices}
  have hdegree : ∀ i, G.degree i ≤ 3 := by
    intro i
    rw [C.degree_internalGraph_eq_card_internalNeighbors]
    exact C.internalNeighbors_card_le_three hcard i.2
  by_cases hlength : p.length ≤ 6
  · left
    intro i hi j hj
    let i' : {i // i ∈ C.vertices} := ⟨i, hi⟩
    let j' : {i // i ∈ C.vertices} := ⟨j, hj⟩
    obtain ⟨q, hq⟩ := (hconn i' j').exists_isPath
    let W : T.minusTwoGraph.Walk i j := (q.map ι).copy rfl rfl
    refine ⟨W, ?_⟩
    have hqle := hmax i' j' q hq
    change (q.map ι).length ≤ 6
    rw [q.length_map ι]
    omega
  right
  by_cases hbranch : ∃ c ∈ C.vertices, (C.internalNeighbors c).card = 3
  · obtain ⟨c, hcMem, hcDegree⟩ := hbranch
    let c' : {i // i ∈ C.vertices} := ⟨c, hcMem⟩
    have hcDegreeG : G.degree c' = 3 := by
      rw [C.degree_internalGraph_eq_card_internalNeighbors]
      exact hcDegree
    have hdegreeUnique {x : {i // i ∈ C.vertices}} (hx : G.degree x = 3) :
        x = c' := by
      apply Subtype.ext
      apply T.minusTwoClusterAt_degree_three_unique hcard hgenus htarget x.2 hcMem
      · rw [← C.degree_internalGraph_eq_card_internalNeighbors]
        exact hx
      · exact hcDegree
    have hcSupport : c' ∈ p.support := by
      by_contra hcNot
      obtain ⟨q, _hq⟩ := (hconn u c').exists_isPath
      obtain ⟨d, _hd, hy, hz⟩ :=
        q.exists_boundary_dart {x | x ∈ p.support} p.start_mem_support hcNot
      have hdDegree := boundary_degree_eq_three_of_maximalPath hp hmax hdegree d hy hz
      have hdc : d.fst = c' := hdegreeUnique hdDegree
      exact hcNot (hdc ▸ hy)
    obtain ⟨k, hk, hkle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hcSupport
    have hkpos : 0 < k := by
      by_contra hknot
      have hkzero : k = 0 := by omega
      have hcu : u = c' := by simpa [hkzero] using hk
      have hstart := maximalPath_start_degree_le_one hacyclic hp hmax
      rw [hcu] at hstart
      omega
    have hklt : k < p.length := by
      by_contra hknot
      have hkeq : k = p.length := by omega
      have hcv : v = c' := by simpa [hkeq] using hk
      have hend := maximalPath_end_degree_le_one hacyclic hp hmax
      rw [hcv] at hend
      omega
    let prev := p.getVert (k - 1)
    let next := p.getVert (k + 1)
    have hprevAdj : G.Adj c' prev := by
      have h := (p.adj_getVert_succ (i := k - 1) (by omega)).symm
      rw [show k - 1 + 1 = k by omega, hk] at h
      exact h
    have hnextAdj : G.Adj c' next := by
      have h := p.adj_getVert_succ (i := k) hklt
      rw [hk] at h
      exact h
    have hprevNext : prev ≠ next := by
      intro heq
      have hindex := hp.getVert_injOn (by simp; omega) (by simp; omega) heq
      omega
    have hpairCard : ({prev, next} : Finset {i // i ∈ C.vertices}).card = 2 := by
      simp [hprevNext]
    obtain ⟨z, hzNeighbor, hzPair⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card
        (s := ({prev, next} : Finset {i // i ∈ C.vertices}))
        (t := G.neighborFinset c') (by
          rw [hpairCard, ← SimpleGraph.degree, hcDegreeG]
          omega)
    have hcz : G.Adj c' z := (G.mem_neighborFinset c' z).mp hzNeighbor
    have hzPrev : z ≠ prev := by
      intro heq
      apply hzPair
      simp [heq]
    have hzNext : z ≠ next := by
      intro heq
      apply hzPair
      simp [heq]
    have hzNotSupport : z ∉ p.support := by
      intro hzSupport
      obtain ⟨n, hn, hnle⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzSupport
      have hindices := index_adjacent_of_isAcyclic hacyclic hp k n hkle hnle (by
        rw [hk, hn]
        exact hcz)
      rcases hindices with hprev | hnext
      · apply hzPrev
        dsimp [prev]
        rw [show k - 1 = n by omega]
        exact hn.symm
      · apply hzNext
        dsimp [next]
        rw [← hnext]
        exact hn.symm
    have hneighbors : G.neighborFinset c' = {prev, next, z} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [G.mem_neighborFinset]
        rcases hx with rfl | rfl | rfl
        · exact hprevAdj
        · exact hnextAdj
        · exact hcz
      · rw [← SimpleGraph.degree, hcDegreeG]
        have htriple : ({prev, next, z} :
            Finset {i // i ∈ C.vertices}).card = 3 := by
          have hprevNot : prev ∉ ({next, z} :
              Finset {i // i ∈ C.vertices}) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hprevNext, hzPrev.symm⟩
          have hnextNot : next ∉ ({z} :
              Finset {i // i ∈ C.vertices}) := by
            simpa only [Finset.mem_singleton] using hzNext.symm
          rw [Finset.card_insert_of_notMem hprevNot,
            Finset.card_insert_of_notMem hnextNot]
          simp
        rw [htriple]
    have houtsideNeighbor {x : {i // i ∈ C.vertices}}
        (hx : G.Adj c' x) (hxNot : x ∉ p.support) : x = z := by
      have hxMem : x ∈ G.neighborFinset c' := (G.mem_neighborFinset c' x).mpr hx
      rw [hneighbors] at hxMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxMem
      rcases hxMem with rfl | rfl | rfl
      · exact (hxNot (p.getVert_mem_support (k - 1))).elim
      · exact (hxNot (p.getVert_mem_support (k + 1))).elim
      · rfl
    let left : G.Walk c' u := (p.take k).reverse.copy hk rfl
    let right : G.Walk c' v := (p.drop k).copy hk rfl
    let extra : G.Walk c' z := hcz.toWalk
    have hleftPath : left.IsPath := by
      simpa [left] using (hp.take k).reverse
    have hrightPath : right.IsPath := by
      simpa [right] using hp.drop k
    have hextraPath : extra.IsPath := by
      exact SimpleGraph.Walk.IsPath.of_adj hcz
    have hleftLength : left.length = k := by simp [left, hkle]
    have hrightLength : right.length = p.length - k := by simp [right]
    have hextraLength : extra.length = 1 := by simp [extra]
    have hleftSnd : left.snd = prev := by
      simp [left, prev, SimpleGraph.Walk.snd_reverse, hkle]
    have hrightSnd : right.snd = next := by
      simp [right, next]
    have hextraSnd : extra.snd = z := by simp [extra]
    let leftM := left.map ι
    let rightM := right.map ι
    let extraM := extra.map ι
    have hleftMPath : leftM.IsPath := hleftPath.map hι
    have hrightMPath : rightM.IsPath := hrightPath.map hι
    have hextraMPath : extraM.IsPath := hextraPath.map hι
    have hleftMLength : leftM.length = k := by
      rw [show leftM.length = left.length by simp [leftM], hleftLength]
    have hrightMLength : rightM.length = p.length - k := by
      rw [show rightM.length = right.length by simp [rightM], hrightLength]
    have hextraMLength : extraM.length = 1 := by
      rw [show extraM.length = extra.length by simp [extraM], hextraLength]
    have hcM : T.IsMinusTwoVertex (ι c') :=
      (extraM.adj_getVert_succ (i := 0) (by rw [hextraMLength]; omega)).1
    have hleftRight : leftM.snd ≠ rightM.snd := by
      intro hsnd
      apply hprevNext
      rw [← hleftSnd, ← hrightSnd]
      apply hι
      simpa [leftM, rightM] using hsnd
    have hextraLeft : extraM.snd ≠ leftM.snd := by
      intro hsnd
      apply hzPrev
      rw [← hextraSnd, ← hleftSnd]
      apply hι
      simpa [extraM, leftM] using hsnd
    have hextraRight : extraM.snd ≠ rightM.snd := by
      intro hsnd
      apply hzNext
      rw [← hextraSnd, ← hrightSnd]
      apply hι
      simpa [extraM, rightM] using hsnd
    have hshortSide : k = 1 ∨ p.length - k = 1 := by
      by_contra hnot
      have hkTwo : 2 ≤ k := by omega
      have hrightTwo : 2 ≤ p.length - k := by omega
      by_cases hkThree : 3 ≤ k
      · by_cases hrightThree : 3 ≤ p.length - k
        · exact T.no_affineE7_of_three_paths (by omega) hgenus
            hcM hextraMPath hleftMPath hrightMPath
            (by rw [hextraMLength]) (by rw [hleftMLength]; omega)
            (by rw [hrightMLength]; omega) hextraLeft hextraRight hleftRight
        · exact T.no_affineE8_of_three_paths (by omega) hgenus
            hcM hextraMPath hrightMPath hleftMPath
            (by rw [hextraMLength]) (by rw [hrightMLength]; omega)
            (by rw [hleftMLength]; omega) hextraRight hextraLeft hleftRight.symm
      · exact T.no_affineE8_of_three_paths (by omega) hgenus
          hcM hextraMPath hleftMPath hrightMPath
          (by rw [hextraMLength]) (by rw [hleftMLength]; omega)
          (by rw [hrightMLength]; omega) hextraLeft hextraRight hleftRight
    have hboundary {d : G.Dart} (hy : d.fst ∈ p.support)
        (hzOut : d.snd ∉ p.support) : d.fst = c' := by
      exact hdegreeUnique
        (boundary_degree_eq_three_of_maximalPath hp hmax hdegree d hy hzOut)
    have hcomplement {x : {i // i ∈ C.vertices}} (hx : x ∉ p.support) : x = z := by
      by_contra hxz
      obtain ⟨q, hq⟩ := (hconn c' x).exists_isPath
      obtain ⟨d, hd, hy, hzOut⟩ :=
        q.exists_boundary_dart {y | y ∈ p.support} hcSupport hx
      have hdc : d.fst = c' := hboundary hy hzOut
      have hdsndSupport : d.snd ∈ q.support :=
        q.dart_snd_mem_support_of_mem_darts hd
      have hdsnd : d.snd = q.snd :=
        hacyclic.eq_snd_of_adj_start hq (hdc ▸ d.adj) hdsndSupport
      have hqSndOut : q.snd ∉ p.support := by simpa [← hdsnd] using hzOut
      have hqSndZ : q.snd = z :=
        houtsideNeighbor (hdsnd ▸ hdc ▸ d.adj) hqSndOut
      have hcx : c' ≠ x := by
        intro heq
        apply hx
        rw [← heq]
        exact hcSupport
      have hqPos : 0 < q.length := by
        by_contra hzero
        exact hcx (q.eq_of_length_eq_zero (by omega))
      have hqLength : 2 ≤ q.length := by
        by_contra hnot
        have hqOne : q.length = 1 := by omega
        apply hxz
        calc
          x = q.getVert q.length := q.getVert_length.symm
          _ = q.getVert 1 := by rw [hqOne]
          _ = q.snd := rfl
          _ = z := hqSndZ
      let qM := q.map ι
      have hqMPath : qM.IsPath := hq.map hι
      have hqMLength : qM.length = q.length := by simp [qM]
      have hqLeft : qM.snd ≠ leftM.snd := by
        intro hsnd
        apply hzPrev
        rw [← hqSndZ, ← hleftSnd]
        apply hι
        simpa [qM, leftM] using hsnd
      have hqRight : qM.snd ≠ rightM.snd := by
        intro hsnd
        apply hzNext
        rw [← hqSndZ, ← hrightSnd]
        apply hι
        simpa [qM, rightM] using hsnd
      rcases hshortSide with hleftShort | hrightShort
      · exact T.no_affineE8_of_three_paths (by omega) hgenus hcM
          hleftMPath hqMPath hrightMPath
          (by rw [hleftMLength, hleftShort])
          (by rw [hqMLength]; omega) (by rw [hrightMLength]; omega)
          hqLeft.symm hleftRight hqRight
      · exact T.no_affineE8_of_three_paths (by omega) hgenus hcM
          hrightMPath hqMPath hleftMPath
          (by rw [hrightMLength, hrightShort])
          (by rw [hqMLength]; omega) (by rw [hleftMLength]; omega)
          hqRight.symm hleftRight.symm hqLeft
    obtain ⟨a, b, d, hd, hdLength, hdSupport, hdBranch, hdMax⟩ :
        ∃ (a b : {i // i ∈ C.vertices}) (d : G.Walk a b),
          d.IsPath ∧ d.length = p.length ∧
          (∀ x, x ∈ d.support ↔ x ∈ p.support) ∧
          d.getVert (d.length - 1) = c' ∧
          ∀ (a' b' : {i // i ∈ C.vertices}) (q : G.Walk a' b'),
            q.IsPath → q.length ≤ d.length := by
      rcases hshortSide with hleftShort | hrightShort
      · refine ⟨v, u, p.reverse, hp.reverse, by simp, ?_, ?_, ?_⟩
        · intro x
          simp
        · rw [SimpleGraph.Walk.getVert_reverse,
            SimpleGraph.Walk.length_reverse]
          have hindex : p.length - (p.length - 1) = k := by omega
          rw [hindex, hk]
        · intro a' b' q hq
          simpa using hmax a' b' q hq
      · refine ⟨u, v, p, hp, rfl, fun _ ↦ Iff.rfl, ?_, hmax⟩
        have hkLast : k = p.length - 1 := by omega
        rw [← hkLast, hk]
    have hzNotD : z ∉ d.support := by
      rw [hdSupport]
      exact hzNotSupport
    have hcomplementD {x : {i // i ∈ C.vertices}} (hx : x ∉ d.support) :
        x = z := by
      apply hcomplement
      rwa [← hdSupport]
    let W := d.map ι
    have hW : W.IsPath := hd.map hι
    have hWLength : W.length = p.length := by simp [W, hdLength]
    have hWpos : 0 < W.length := by rw [hWLength]; omega
    have hWstart : T.IsMinusTwoVertex (W.getVert 0) :=
      (W.adj_getVert_succ (i := 0) hWpos).1
    have hWstart' : T.IsMinusTwoVertex (ι a) := by simpa using hWstart
    let P := T.simpleMinusTwoPathOfWalk W hW hWstart'
    have hPLength : P.length = W.length := rfl
    have hPdLength : P.length = d.length := by
      rw [hPLength, show W.length = d.length by simp [W]]
    have hPvertex (r : Fin (P.length + 1)) :
        P.vertex r = W.getVert r.val := rfl
    have hWget (n : ℕ) : W.getVert n = (d.getVert n).1 := by
      change (d.map ι).getVert n = (d.getVert n).1
      rw [SimpleGraph.Walk.getVert_map]
      rfl
    have hPbranch :
        P.vertex ⟨P.length - 1, by have := hWpos; omega⟩ = c := by
      have hindex : P.length - 1 = d.length - 1 := by rw [hPdLength]
      calc
        P.vertex ⟨P.length - 1, by have := hWpos; omega⟩ =
            (d.getVert (P.length - 1)).1 := by rw [hPvertex, hWget]
        _ = (d.getVert (d.length - 1)).1 := by rw [hindex]
        _ = c'.1 := congrArg Subtype.val hdBranch
        _ = c := rfl
    right
    refine ⟨{
      path := P
      length_four := by rw [hPLength, hWLength]; omega
      extra := z.1
      extra_ne := ?_
      extra_minusTwo := C.minusTwo z.1 z.2
      extra_adjacent := ?_
      mem_path := ?_
      mem_extra := z.2
      covers := ?_
      path_neighbors := ?_
      extra_neighbor := ?_ }⟩
    · intro r heq
      apply hzNotD
      have hzEq : z = d.getVert r.val := by
        apply Subtype.ext
        calc
          z.1 = P.vertex r := heq
          _ = W.getVert r.val := hPvertex r
          _ = (d.getVert r.val).1 := hWget r.val
      rw [hzEq]
      exact d.getVert_mem_support r.val
    · rw [hPbranch]
      exact (C.internalGraph_adj c' z).mp hcz
    · intro r
      rw [hPvertex, hWget]
      exact (d.getVert r.val).2
    · intro i hi
      let x : {i // i ∈ C.vertices} := ⟨i, hi⟩
      by_cases hx : x ∈ d.support
      · obtain ⟨n, hn, hnle⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
        let r : Fin (P.length + 1) := ⟨n, by rw [hPdLength]; omega⟩
        left
        refine ⟨r, ?_⟩
        rw [hPvertex, hWget]
        exact congrArg Subtype.val hn
      · right
        exact congrArg Subtype.val (hcomplementD hx)
    · intro r i hi hadj
      have hrMem : P.vertex r ∈ C.vertices := by
        rw [hPvertex, hWget]
        exact (d.getVert r.val).2
      have hiMem : i ∈ C.vertices := C.closed (P.vertex r) hrMem i hadj hi
      let x : {i // i ∈ C.vertices} := ⟨i, hiMem⟩
      have hadjG : G.Adj (d.getVert r.val) x := by
        rw [C.internalGraph_adj]
        change T.intersectionGraph.Adj (d.getVert r.val).1 i
        rw [← hWget, ← hPvertex]
        exact hadj
      by_cases hxSupport : x ∈ d.support
      · obtain ⟨n, hn, hnle⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxSupport
        have hindices := index_adjacent_of_isAcyclic hacyclic hd r.val n
          (by rw [← hPdLength]; omega) hnle (by simpa [hn] using hadjG)
        rcases hindices with hprev | hnext
        · left
          let s : Fin (P.length + 1) := ⟨n, by rw [hPdLength]; omega⟩
          refine ⟨s, by simpa [s] using hprev.symm, ?_⟩
          rw [hPvertex, hWget]
          exact (congrArg Subtype.val hn).symm
        · right
          left
          let s : Fin (P.length + 1) := ⟨n, by rw [hPdLength]; omega⟩
          refine ⟨s, by simpa [s] using hnext.symm, ?_⟩
          rw [hPvertex, hWget]
          exact (congrArg Subtype.val hn).symm
      · right
        right
        let e : G.Dart := ⟨(d.getVert r.val, x), hadjG⟩
        have heDegree := boundary_degree_eq_three_of_maximalPath hd hdMax hdegree e
          (by
            dsimp [e]
            exact d.getVert_mem_support r.val)
          (by simpa [e] using hxSupport)
        have heCenter : d.getVert r.val = c' := hdegreeUnique heDegree
        have hindex : r.val = d.length - 1 := hd.getVert_injOn
          (by change r.val ≤ d.length; rw [← hPdLength]; omega)
          (Nat.sub_le _ _)
          (heCenter.trans hdBranch.symm)
        refine ⟨by omega, ?_⟩
        exact congrArg Subtype.val (hcomplementD hxSupport)
    · intro i hi hadj
      have hiMem : i ∈ C.vertices := C.closed z.1 z.2 i hadj hi
      let x : {i // i ∈ C.vertices} := ⟨i, hiMem⟩
      by_cases hxSupport : x ∈ d.support
      · have hadjG : G.Adj x z := by
          rw [C.internalGraph_adj]
          exact hadj.symm
        let e : G.Dart := ⟨(x, z), hadjG⟩
        have heDegree := boundary_degree_eq_three_of_maximalPath hd hdMax hdegree e
          (by simpa [e] using hxSupport) (by simpa [e] using hzNotD)
        have hxCenter : x = c' := hdegreeUnique heDegree
        calc
          i = x.1 := rfl
          _ = c'.1 := congrArg Subtype.val hxCenter
          _ = c := rfl
          _ = P.vertex ⟨P.length - 1, by have := hWpos; omega⟩ := hPbranch.symm
      · have hxz : x = z := hcomplementD hxSupport
        exact ((T.intersectionGraph.ne_of_adj hadj)
          (congrArg Subtype.val hxz).symm).elim
  · left
    apply T.minusTwoClusterAt_pathShape_of_no_degree_three hcard hgenus htarget
    · simpa [C] using lt_of_not_ge hsmall
    · intro c hc hdegreeThree
      exact hbranch ⟨c, hc, hdegreeThree⟩

/-- The isolated output of the remaining cluster classification implies the `768g`
bound for every component of a minimal numerical type. -/
lemma diagonalProduct_le_768_genus_of_bounded_cluster_shapes
    (T : NumericalType) (hmin : T.IsMinimal)
    (hcard : 5 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    (hshapes : ∀ (root : T.Component) (hroot : T.IsMinusTwoVertex root),
      (T.minusTwoClusterAt root hroot).HasBoundedShape)
    (target : T.Component) :
    T.diagonalProduct target ≤ 768 * T.arithmeticGenus := by
  by_cases htarget : T.IsMinusTwoVertex target
  · rcases hshapes target htarget with hsmall | hdiameter | hshape
    · exact T.diagonalProduct_le_768_genus_of_cluster_card_le_seven
        hmin (by omega) hgenus htarget hsmall
    · exact T.diagonalProduct_le_768_genus_of_cluster_diameter_le_six
        hmin (by omega) hgenus htarget hdiameter
    · rcases hshape with hpath | hendFork
      · rcases hpath with ⟨S⟩
        exact T.diagonalProduct_le_768_genus_of_cluster_pathShape
          hmin hcard hgenus htarget S
      · rcases hendFork with ⟨S⟩
        exact T.diagonalProduct_le_768_genus_of_cluster_endForkShape
          hmin hcard hgenus htarget S
  · have hbound := T.diagonalProduct_le_six_genus_sub_one hmin (by omega) htarget
    change T.diagonalProduct target ≤ 6 * (T.arithmeticGenus - 1) at hbound
    have hgenusNonneg : 0 ≤ T.arithmeticGenus := by omega
    nlinarith

/-- The large-component case of Stacks Project tag `0C9W`. -/
lemma diagonalProduct_le_768_genus_of_five_lt_card
    (T : NumericalType) (hmin : T.IsMinimal)
    (hcard : 5 < Nat.card T.Component) (hgenus : 2 ≤ T.arithmeticGenus)
    (target : T.Component) :
    T.diagonalProduct target ≤ 768 * T.arithmeticGenus := by
  exact T.diagonalProduct_le_768_genus_of_bounded_cluster_shapes
    hmin hcard hgenus
    (fun root hroot ↦ T.minusTwoClusterAt_hasBoundedShape hcard hgenus hroot) target

/-- A one-component fibre has zero self-intersection. -/
lemma selfIntersection_eq_zero_of_card_eq_one
    (T : NumericalType) (hcard : Nat.card T.Component = 1) (i : T.Component) :
    T.intersection i i = 0 := by
  let _ : Subsingleton T.Component := (Nat.card_eq_one_iff_unique.mp hcard).1
  have huniv : (Finset.univ : Finset T.Component) = {i} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  have hfiber := T.fiber_relation i
  rw [huniv, Finset.sum_singleton] at hfiber
  exact mul_left_cancel₀
    (by positivity : (T.multiplicity i : ℤ) ≠ 0) hfiber

/-- Stacks Project tag `0C9W`: every diagonal product of every minimal numerical type of
arithmetic genus at least two is at most `768g`, including the one-component and small-cardinality
cases. -/
theorem diagonalProduct_le_768_genus (T : NumericalType) (hmin : T.IsMinimal)
    (hgenus : 2 ≤ T.arithmeticGenus) (target : T.Component) :
    T.diagonalProduct target ≤ 768 * T.arithmeticGenus := by
  by_cases hone : Nat.card T.Component = 1
  · have hintersection := T.selfIntersection_eq_zero_of_card_eq_one hone target
    have hnonnegative : 0 ≤ T.arithmeticGenus := by omega
    simp [diagonalProduct, hintersection, hnonnegative]
  · have hcard : 1 < Nat.card T.Component := by
      have hpositive : 0 < Nat.card T.Component := Nat.card_pos
      omega
    by_cases hsmall : Nat.card T.Component ≤ 7
    · exact T.diagonalProduct_le_768_genus_of_card_le_seven
        hmin hcard hsmall hgenus target
    · exact T.diagonalProduct_le_768_genus_of_five_lt_card
        hmin (by omega) hgenus target


/-- Divisors supported on the components. -/
abbrev Divisor (T : NumericalType) := T.Component → ℤ

/-- Reindex component divisors by the same equivalence used for a numerical type. -/
def divisorReindex (T : NumericalType.{u}) {J : Type v} (e : T.Component ≃ J) :
    T.Divisor ≃+ (T.reindex e).Divisor where
  toFun D j := D (e.symm j)
  invFun D i := D (e i)
  left_inv D := by ext i; simp
  right_inv D := by ext j; simp
  map_add' _ _ := rfl

@[simp] lemma divisorReindex_apply (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) (D : T.Divisor) (j : J) :
    T.divisorReindex e D j = D (e.symm j) := rfl

/-- An equivalence of numerical types reindexes their component divisors. -/
def Equiv.divisorEquiv {T : NumericalType.{u}} {U : NumericalType.{v}} (e : T.Equiv U) :
    T.Divisor ≃+ U.Divisor where
  toFun D j := D (e.componentEquiv.symm j)
  invFun D i := D (e.componentEquiv i)
  left_inv D := by ext i; simp
  right_inv D := by ext j; simp
  map_add' _ _ := rfl

@[simp] lemma Equiv.divisorEquiv_apply {T : NumericalType.{u}} {U : NumericalType.{v}}
    (e : T.Equiv U) (D : T.Divisor) (j : U.Component) :
    e.divisorEquiv D j = D (e.componentEquiv.symm j) := rfl

/-- The weighted relation associated to a component `i`. -/
def principalDivisor (T : NumericalType) (i : T.Component) : T.Divisor :=
  fun j ↦ T.intersection i j / (T.weight j : ℤ)

/-- Every weighted principal relation vanishes on a one-component fibre. -/
lemma principalDivisor_eq_zero_of_card_eq_one
    (T : NumericalType) (hcard : Nat.card T.Component = 1) (i : T.Component) :
    T.principalDivisor i = 0 := by
  let _ : Subsingleton T.Component := (Nat.card_eq_one_iff_unique.mp hcard).1
  funext j
  have hji : j = i := Subsingleton.elim _ _
  subst j
  simp [principalDivisor, T.selfIntersection_eq_zero_of_card_eq_one hcard i]

/-- Coordinate division in `principalDivisor` is exact. -/
lemma principalDivisor_mul_weight (T : NumericalType) (i j : T.Component) :
    T.principalDivisor i j * (T.weight j : ℤ) = T.intersection i j := by
  apply Int.ediv_mul_cancel
  rw [T.intersection_symm i j]
  exact T.weight_dvd j i

/-- The subgroup generated by the weighted relations. -/
def principalDivisors (T : NumericalType) : AddSubgroup T.Divisor :=
  AddSubgroup.closure (Set.range T.principalDivisor)

/-- The subgroup of weighted principal relations is zero on a one-component fibre. -/
lemma principalDivisors_eq_bot_of_card_eq_one
    (T : NumericalType) (hcard : Nat.card T.Component = 1) :
    T.principalDivisors = ⊥ := by
  rw [principalDivisors]
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro x ⟨i, rfl⟩
    rw [T.principalDivisor_eq_zero_of_card_eq_one hcard i]
    exact AddSubgroup.zero_mem ⊥
  · exact bot_le

/-- The matrix whose rows are the weighted principal relations. -/
def principalMatrix (T : NumericalType) : Matrix T.Component T.Component ℤ :=
  fun i ↦ T.principalDivisor i

/-- Linear combinations of the weighted principal relations. -/
abbrev principalLinearMap (T : NumericalType) : T.Divisor →ₗ[ℤ] T.Divisor :=
  T.principalMatrix.vecMulLinear

/-- The range of `principalLinearMap` is the integral submodule underlying the subgroup of
principal divisors. -/
theorem principalLinearMap_range (T : NumericalType) :
    LinearMap.range T.principalLinearMap = T.principalDivisors.toIntSubmodule := by
  rw [range_vecMulLinear, principalDivisors, AddSubgroup.toIntSubmodule_closure]
  rfl

lemma ratio_eq_of_intersection_mulVec_eq_zero (T : NumericalType)
    (x : T.Divisor) (hx : Matrix.mulVec T.intersection x = 0) (i j : T.Component) :
    (x i : ℚ) / (T.multiplicity i : ℚ) =
      (x j : ℚ) / (T.multiplicity j : ℚ) := by
  classical
  let q : T.Component → ℚ := fun k ↦ (x k : ℚ) / (T.multiplicity k : ℚ)
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ q Finset.univ_nonempty
  have hmax (k : T.Component) : q k ≤ q a := ha k (Finset.mem_univ k)
  have hstep (k l : T.Component) (hk : q k = q a)
      (hkl : k ≠ l ∧ 0 < T.intersection k l) : q l = q a := by
    have hrowZ : ∑ r, T.intersection k r * x r = 0 := congrFun hx k
    have hrowQ : ∑ r, (T.intersection k r : ℚ) * (x r : ℚ) = 0 := by
      exact_mod_cast hrowZ
    have hfiberQ : ∑ r, (T.multiplicity r : ℚ) * (T.intersection k r : ℚ) = 0 := by
      exact_mod_cast T.fiber_relation k
    have hxq (r : T.Component) :
        (x r : ℚ) = (T.multiplicity r : ℚ) * q r := by
      dsimp [q]
      field_simp
    have hsum :
        ∑ r, ((T.intersection k r : ℚ) * (T.multiplicity r : ℚ)) *
          (q r - q k) = 0 := by
      calc
        _ = (∑ r, (T.intersection k r : ℚ) * (T.multiplicity r : ℚ) * q r) -
            (∑ r, (T.intersection k r : ℚ) * (T.multiplicity r : ℚ)) * q k := by
              simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
        _ = (∑ r, (T.intersection k r : ℚ) * (x r : ℚ)) -
            (∑ r, (T.multiplicity r : ℚ) * (T.intersection k r : ℚ)) * q k := by
              congr 1
              · apply Finset.sum_congr rfl
                intro r _
                rw [hxq]
                ring
              · apply congrArg (fun z : ℚ ↦ z * q k)
                apply Finset.sum_congr rfl
                intro r _
                ring
        _ = 0 := by rw [hrowQ, hfiberQ]; ring
    have hnonpos (r : T.Component) :
        ((T.intersection k r : ℚ) * (T.multiplicity r : ℚ)) * (q r - q k) ≤ 0 := by
      by_cases hr : k = r
      · subst r
        simp
      · have hA : 0 ≤ (T.intersection k r : ℚ) := by
          exact_mod_cast T.offDiagonal_nonnegative k r hr
        have hm : 0 ≤ (T.multiplicity r : ℚ) := by positivity
        have hq : q r - q k ≤ 0 := sub_nonpos.mpr (by rw [hk]; exact hmax r)
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hA hm) hq
    have hterm :
        ((T.intersection k l : ℚ) * (T.multiplicity l : ℚ)) * (q l - q k) = 0 :=
      ((Finset.sum_eq_zero_iff_of_nonpos
        (fun r _ ↦ hnonpos r)).mp hsum) l (Finset.mem_univ l)
    have hcoeff : (T.intersection k l : ℚ) * (T.multiplicity l : ℚ) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast ne_of_gt hkl.2) (by positivity)
    have : q l = q k := sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left hcoeff)
    exact this.trans hk
  have hall (k : T.Component) : q k = q a := by
    induction T.connected a k with
    | refl => rfl
    | tail h hkl ih => exact hstep _ _ ih hkl
  exact (hall i).trans (hall j).symm

lemma intersection_mulVec_eq_zero_of_principalLinearMap_eq_zero (T : NumericalType)
    (x : T.Divisor) (hx : T.principalLinearMap x = 0) :
    Matrix.mulVec T.intersection x = 0 := by
  funext j
  have hdiv : ∑ i, x i * T.principalDivisor i j = 0 := congrFun hx j
  have hmul := congrArg (fun z : ℤ ↦ z * (T.weight j : ℤ)) hdiv
  rw [zero_mul, Finset.sum_mul] at hmul
  simp_rw [mul_assoc, T.principalDivisor_mul_weight] at hmul
  calc
    ∑ i, T.intersection j i * x i = ∑ i, x i * T.intersection i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [T.intersection_symm j i]
      ring
    _ = 0 := hmul

/-- The multiplicities, regarded as a divisor, give a dependence among the weighted principal
rows. -/
def multiplicityDivisor (T : NumericalType) : T.Divisor :=
  fun i ↦ (T.multiplicity i : ℤ)

@[simp] theorem principalLinearMap_multiplicityDivisor (T : NumericalType) :
    T.principalLinearMap T.multiplicityDivisor = 0 := by
  funext j
  apply mul_right_cancel₀ (by positivity : (T.weight j : ℤ) ≠ 0)
  rw [Pi.zero_apply, zero_mul]
  change (∑ i, (T.multiplicity i : ℤ) * T.principalDivisor i j) *
    (T.weight j : ℤ) = 0
  rw [Finset.sum_mul]
  simp_rw [mul_assoc, T.principalDivisor_mul_weight]
  calc
    ∑ i, (T.multiplicity i : ℤ) * T.intersection i j =
        ∑ i, (T.multiplicity i : ℤ) * T.intersection j i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [T.intersection_symm i j]
    _ = 0 := T.fiber_relation j

private lemma eq_zero_of_principalLinearMap_eq_zero_of_apply_eq_zero (T : NumericalType)
    (x : T.Divisor) (hx : T.principalLinearMap x = 0) (a : T.Component) (ha : x a = 0) :
    x = 0 := by
  have hAx := T.intersection_mulVec_eq_zero_of_principalLinearMap_eq_zero x hx
  funext i
  have hratio := ratio_eq_of_intersection_mulVec_eq_zero T x hAx i a
  have hiQ : (x i : ℚ) / (T.multiplicity i : ℚ) = 0 := by
    simpa [ha] using hratio
  have : (x i : ℚ) = 0 :=
    (div_eq_zero_iff.mp hiQ).resolve_right (by positivity)
  exact_mod_cast this

/-- Connectedness makes the space of dependencies among the weighted principal rows
one-dimensional. -/
theorem principalLinearMap_ker_finrank (T : NumericalType) :
    Module.finrank ℤ (LinearMap.ker T.principalLinearMap) = 1 := by
  classical
  let a : T.Component := Classical.choice T.componentNonempty
  let ev : LinearMap.ker T.principalLinearMap →ₗ[ℤ] ℤ :=
    (LinearMap.proj a).comp (LinearMap.ker T.principalLinearMap).subtype
  have hev : Function.Injective ev := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply T.eq_zero_of_principalLinearMap_eq_zero_of_apply_eq_zero (x.1 - y.1) _ a
    · change x.1 a = y.1 a at hxy
      exact sub_eq_zero.mpr hxy
    · simp only [map_sub, LinearMap.mem_ker.mp x.2, LinearMap.mem_ker.mp y.2, sub_zero]
  have hle : Module.finrank ℤ (LinearMap.ker T.principalLinearMap) ≤ 1 := by
    calc
      _ = Module.finrank ℤ (LinearMap.range ev) :=
        (LinearMap.finrank_range_of_inj hev).symm
      _ ≤ Module.finrank ℤ ℤ := (LinearMap.range ev).finrank_le
      _ = 1 := Module.finrank_self ℤ
  let m : LinearMap.ker T.principalLinearMap :=
    ⟨T.multiplicityDivisor, LinearMap.mem_ker.mpr T.principalLinearMap_multiplicityDivisor⟩
  have hm : m ≠ 0 := by
    intro h
    have ha := congrArg (fun z : LinearMap.ker T.principalLinearMap ↦ z.1 a) h
    change (T.multiplicity a : ℤ) = 0 at ha
    have hpos : (0 : ℤ) < T.multiplicity a := by positivity
    omega
  let _ : Nontrivial (LinearMap.ker T.principalLinearMap) := ⟨⟨m, 0, hm⟩⟩
  have hpos : 0 < Module.finrank ℤ (LinearMap.ker T.principalLinearMap) :=
    Module.finrank_pos
  omega

/-- The weighted principal relations have corank one. -/
theorem principalDivisors_finrank_add_one (T : NumericalType) :
    Module.finrank ℤ T.principalDivisors.toIntSubmodule + 1 = Fintype.card T.Component := by
  have h := (LinearMap.ker T.principalLinearMap).finrank_quotient_add_finrank
  rw [LinearEquiv.finrank_eq T.principalLinearMap.quotKerEquivRange,
    T.principalLinearMap_ker_finrank, Module.finrank_pi, T.principalLinearMap_range] at h
  exact h

@[simp] theorem divisorReindex_principalDivisor (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) (i : T.Component) :
    T.divisorReindex e (T.principalDivisor i) =
      (T.reindex e).principalDivisor (e i) := by
  ext j
  simp [divisorReindex, principalDivisor]

/-- Reindexing takes the subgroup of weighted principal relations onto the corresponding
subgroup for the reindexed numerical type. -/
theorem principalDivisors_map_divisorReindex (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) :
    T.principalDivisors.map (T.divisorReindex e).toAddMonoidHom =
      (T.reindex e).principalDivisors := by
  apply le_antisymm
  · rw [AddSubgroup.map_le_iff_le_comap, principalDivisors, AddSubgroup.closure_le]
    rintro D ⟨i, rfl⟩
    change T.divisorReindex e (T.principalDivisor i) ∈ (T.reindex e).principalDivisors
    rw [T.divisorReindex_principalDivisor e i]
    exact AddSubgroup.subset_closure (Set.mem_range_self (e i))
  · rw [principalDivisors, AddSubgroup.closure_le]
    rintro D ⟨j, rfl⟩
    refine ⟨T.principalDivisor (e.symm j),
      AddSubgroup.subset_closure (Set.mem_range_self (e.symm j)), ?_⟩
    change T.divisorReindex e (T.principalDivisor (e.symm j)) =
      (T.reindex e).principalDivisor j
    rw [T.divisorReindex_principalDivisor, e.apply_symm_apply]

@[simp] theorem Equiv.divisorEquiv_principalDivisor
    {T : NumericalType.{u}} {U : NumericalType.{v}} (e : T.Equiv U) (i : T.Component) :
    e.divisorEquiv (T.principalDivisor i) = U.principalDivisor (e.componentEquiv i) := by
  ext j
  change T.intersection i (e.componentEquiv.symm j) /
      (T.weight (e.componentEquiv.symm j) : ℤ) =
    U.intersection (e.componentEquiv i) j / (U.weight j : ℤ)
  rw [← e.intersection_eq i (e.componentEquiv.symm j),
    ← e.weight_eq (e.componentEquiv.symm j)]
  simp

/-- Equivalent numerical types have corresponding weighted relation subgroups. -/
theorem Equiv.principalDivisors_map {T : NumericalType.{u}} {U : NumericalType.{v}}
    (e : T.Equiv U) :
    T.principalDivisors.map e.divisorEquiv.toAddMonoidHom = U.principalDivisors := by
  apply le_antisymm
  · rw [AddSubgroup.map_le_iff_le_comap, principalDivisors, AddSubgroup.closure_le]
    rintro D ⟨i, rfl⟩
    change e.divisorEquiv (T.principalDivisor i) ∈ U.principalDivisors
    rw [e.divisorEquiv_principalDivisor]
    exact AddSubgroup.subset_closure (Set.mem_range_self (e.componentEquiv i))
  · rw [principalDivisors, AddSubgroup.closure_le]
    rintro D ⟨j, rfl⟩
    refine ⟨T.principalDivisor (e.componentEquiv.symm j),
      AddSubgroup.subset_closure (Set.mem_range_self (e.componentEquiv.symm j)), ?_⟩
    change e.divisorEquiv (T.principalDivisor (e.componentEquiv.symm j)) = U.principalDivisor j
    rw [e.divisorEquiv_principalDivisor, e.componentEquiv.apply_symm_apply]

/-- The weighted numerical Picard group. -/
abbrev Pic (T : NumericalType) := T.Divisor ⧸ T.principalDivisors

/-- The weighted numerical Picard group is finitely generated over `ℤ`. -/
instance pic_moduleFinite (T : NumericalType) : Module.Finite ℤ T.Pic :=
  Module.Finite.quotient ℤ T.principalDivisors.toIntSubmodule

/-- The weighted numerical Picard group has `ℤ`-finrank one. -/
theorem pic_finrank (T : NumericalType) : Module.finrank ℤ T.Pic = 1 := by
  change Module.finrank ℤ (T.Divisor ⧸ T.principalDivisors.toIntSubmodule) = 1
  have hquot := T.principalDivisors.toIntSubmodule.finrank_quotient_add_finrank
  have hrel := T.principalDivisors_finrank_add_one
  rw [Module.finrank_pi] at hquot
  omega

/-- Cardinal-valued form of the rank-one theorem. -/
theorem pic_rank (T : NumericalType) : Module.rank ℤ T.Pic = 1 := by
  rw [← Module.finrank_eq_rank, T.pic_finrank]
  simp

/-- An equivalence of numerical types induces an additive equivalence of their weighted
numerical Picard groups. -/
noncomputable def Equiv.picAddEquiv {T : NumericalType.{u}} {U : NumericalType.{v}}
    (e : T.Equiv U) : T.Pic ≃+ U.Pic where
  toFun := QuotientAddGroup.map T.principalDivisors U.principalDivisors
    e.divisorEquiv.toAddMonoidHom (by
      rw [← AddSubgroup.map_le_iff_le_comap, e.principalDivisors_map])
  invFun := QuotientAddGroup.map U.principalDivisors T.principalDivisors
    e.divisorEquiv.symm.toAddMonoidHom (by
      rw [principalDivisors, AddSubgroup.closure_le]
      rintro D ⟨j, rfl⟩
      change e.divisorEquiv.symm (U.principalDivisor j) ∈ T.principalDivisors
      have hrel := e.divisorEquiv_principalDivisor (e.componentEquiv.symm j)
      rw [e.componentEquiv.apply_symm_apply] at hrel
      rw [← hrel, e.divisorEquiv.symm_apply_apply]
      exact AddSubgroup.subset_closure (Set.mem_range_self (e.componentEquiv.symm j)))
  left_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | _ D => simp
  right_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | _ D => simp
  map_add' x y := AddMonoidHom.map_add _ x y

@[simp] theorem Equiv.picAddEquiv_mk {T : NumericalType.{u}} {U : NumericalType.{v}}
    (e : T.Equiv U) (D : T.Divisor) :
    e.picAddEquiv (QuotientAddGroup.mk D : T.Pic) =
      (QuotientAddGroup.mk (e.divisorEquiv D) : U.Pic) := rfl

/-- Reindexing components induces an additive equivalence of weighted numerical Picard groups. -/
noncomputable def picReindexEquiv (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) : T.Pic ≃+ (T.reindex e).Pic where
  toFun := QuotientAddGroup.map T.principalDivisors (T.reindex e).principalDivisors
    (T.divisorReindex e).toAddMonoidHom (by
      rw [← AddSubgroup.map_le_iff_le_comap, T.principalDivisors_map_divisorReindex e])
  invFun := QuotientAddGroup.map (T.reindex e).principalDivisors T.principalDivisors
    (T.divisorReindex e).symm.toAddMonoidHom (by
      rw [principalDivisors, AddSubgroup.closure_le]
      rintro D ⟨j, rfl⟩
      change (T.divisorReindex e).symm ((T.reindex e).principalDivisor j) ∈
        T.principalDivisors
      have hrel := T.divisorReindex_principalDivisor e (e.symm j)
      rw [e.apply_symm_apply] at hrel
      rw [← hrel, (T.divisorReindex e).symm_apply_apply]
      exact AddSubgroup.subset_closure (Set.mem_range_self (e.symm j)))
  left_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | _ D => simp
  right_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | _ D => simp
  map_add' x y := AddMonoidHom.map_add _ x y

@[simp] theorem picReindexEquiv_mk (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) (D : T.Divisor) :
    T.picReindexEquiv e (QuotientAddGroup.mk D : T.Pic) =
      (QuotientAddGroup.mk (T.divisorReindex e D) : (T.reindex e).Pic) := rfl

/-- The `ℓ`-torsion subgroup of the numerical Picard group. -/
def torsion (T : NumericalType) (ℓ : ℕ) : AddSubgroup T.Pic :=
  AddSubgroup.torsionBy T.Pic (ℓ : ℤ)

/-- Membership in numerical Picard `ℓ`-torsion means annihilation by `ℓ`. -/
@[simp] theorem mem_torsion_iff (T : NumericalType) (ℓ : ℕ) (x : T.Pic) :
    x ∈ T.torsion ℓ ↔ ℓ • x = 0 := by
  unfold torsion
  exact AddSubgroup.torsionBy.nsmul_iff

/-- A divisor represents an `ℓ`-torsion Picard class exactly when its `ℓ`-multiple is a
weighted principal divisor. -/
@[simp] theorem mk_mem_torsion_iff (T : NumericalType) (ℓ : ℕ) (D : T.Divisor) :
    (QuotientAddGroup.mk D : T.Pic) ∈ T.torsion ℓ ↔
      ℓ • D ∈ T.principalDivisors := by
  rw [T.mem_torsion_iff, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]

/-- A one-component numerical Picard group has no nonzero integer torsion. -/
lemma torsion_eq_bot_of_card_eq_one
    (T : NumericalType) (hcard : Nat.card T.Component = 1)
    (ℓ : ℕ) (hℓ : ℓ ≠ 0) :
    T.torsion ℓ = ⊥ := by
  ext x
  constructor
  · intro hx
    rw [AddSubgroup.mem_bot]
    induction x using QuotientAddGroup.induction_on with
    | _ D =>
      rw [T.mk_mem_torsion_iff, T.principalDivisors_eq_bot_of_card_eq_one hcard,
        AddSubgroup.mem_bot] at hx
      have hD : D = 0 := by
        funext i
        have hi := congrFun hx i
        simp only [Pi.smul_apply, nsmul_eq_mul] at hi
        exact (mul_eq_zero.mp hi).resolve_left (Int.ofNat_ne_zero.mpr hℓ)
      rw [hD]
      rfl
  · rintro rfl
    simp

/-- Matrix form of the representative criterion for numerical Picard torsion. -/
theorem mk_mem_torsion_iff_exists (T : NumericalType) (ℓ : ℕ) (D : T.Divisor) :
    (QuotientAddGroup.mk D : T.Pic) ∈ T.torsion ℓ ↔
      ∃ c : T.Divisor, T.principalLinearMap c = ℓ • D := by
  rw [T.mk_mem_torsion_iff]
  change ℓ • D ∈ T.principalDivisors.toIntSubmodule ↔ _
  rw [← T.principalLinearMap_range]
  exact LinearMap.mem_range

/-- Numerical Picard `ℓ`-torsion is naturally a module over `ZMod ℓ`. -/
instance torsion_zmodModule (T : NumericalType) (ℓ : ℕ) :
    Module (ZMod ℓ) (T.torsion ℓ) := by
  unfold torsion
  exact AddSubgroup.torsionBy.zmodModule

/-- Numerical Picard `ℓ`-torsion is finitely generated as an abelian group. -/
instance torsion_intModuleFinite (T : NumericalType) (ℓ : ℕ) :
    Module.Finite ℤ (T.torsion ℓ) := by
  change Module.Finite ℤ (Submodule.torsionBy ℤ T.Pic (ℓ : ℤ))
  rw [Module.Finite.iff_fg]
  exact Submodule.FG.of_le Module.Finite.fg_top le_top

/-- For prime `ℓ`, numerical Picard `ℓ`-torsion is a finite set. -/
instance primeTorsion_finite (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime] :
    Finite (T.torsion ℓ) := by
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(ℓ : ℤ), ?_⟩, ?_⟩
  · simpa using (Fact.out : ℓ.Prime).ne_zero
  · exact AddSubgroup.torsionBy.nsmul x

/-- For prime `ℓ`, numerical Picard `ℓ`-torsion is finite-dimensional over `ZMod ℓ`. -/
instance primeTorsion_moduleFinite (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.Finite (ZMod ℓ) (T.torsion ℓ) := by
  infer_instance

/-- Torsion subgroups are invariant under equivalence of numerical types. -/
theorem Equiv.torsion_map {T : NumericalType.{u}} {U : NumericalType.{v}}
    (e : T.Equiv U) (ℓ : ℕ) :
    (T.torsion ℓ).map e.picAddEquiv.toAddMonoidHom = U.torsion ℓ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (ℓ : ℤ) • x = 0 at hx
    change (ℓ : ℤ) • e.picAddEquiv x = 0
    rw [← map_zsmul, hx, map_zero]
  · intro hy
    refine ⟨e.picAddEquiv.symm y, ?_, by simp⟩
    change (ℓ : ℤ) • y = 0 at hy
    change (ℓ : ℤ) • e.picAddEquiv.symm y = 0
    rw [← map_zsmul, hy, map_zero]

/-- Prime-power and, more generally, `ℓ`-torsion is invariant under reindexing. -/
theorem torsion_map_picReindexEquiv (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) (ℓ : ℕ) :
    (T.torsion ℓ).map (T.picReindexEquiv e).toAddMonoidHom =
      (T.reindex e).torsion ℓ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (ℓ : ℤ) • x = 0 at hx
    change (ℓ : ℤ) • T.picReindexEquiv e x = 0
    rw [← map_zsmul, hx, map_zero]
  · intro hy
    refine ⟨(T.picReindexEquiv e).symm y, ?_, by simp⟩
    change (ℓ : ℤ) • y = 0 at hy
    change (ℓ : ℤ) • (T.picReindexEquiv e).symm y = 0
    rw [← map_zsmul, hy, map_zero]

private noncomputable def torsionAddEquivOfAddEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A ≃+ B) (ℓ : ℕ) :
    AddSubgroup.torsionBy A (ℓ : ℤ) ≃+ AddSubgroup.torsionBy B (ℓ : ℤ) where
  toFun x := ⟨f x, by
    change (ℓ : ℤ) • f (x : A) = 0
    rw [← map_zsmul]
    have hx : (ℓ : ℤ) • (x : A) = 0 := x.property
    rw [hx, map_zero]⟩
  invFun y := ⟨f.symm y, by
    change (ℓ : ℤ) • f.symm (y : B) = 0
    rw [← map_zsmul]
    have hy : (ℓ : ℤ) • (y : B) = 0 := y.property
    rw [hy, map_zero]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp

/-- An equivalence of numerical types induces an additive equivalence on `ℓ`-torsion. -/
noncomputable def Equiv.torsionAddEquiv
    {T : NumericalType.{u}} {U : NumericalType.{v}} (e : T.Equiv U) (ℓ : ℕ) :
    T.torsion ℓ ≃+ U.torsion ℓ := by
  unfold torsion
  exact torsionAddEquivOfAddEquiv e.picAddEquiv ℓ

@[simp] theorem Equiv.torsionAddEquiv_coe
    {T : NumericalType.{u}} {U : NumericalType.{v}} (e : T.Equiv U) (ℓ : ℕ)
    (x : T.torsion ℓ) :
    (e.torsionAddEquiv ℓ x : U.Pic) = e.picAddEquiv x := rfl

/-- The induced equivalence on `ℓ`-torsion is `ZMod ℓ`-linear. -/
noncomputable def Equiv.torsionLinearEquiv
    {T : NumericalType.{u}} {U : NumericalType.{v}} (e : T.Equiv U) (ℓ : ℕ) :
    T.torsion ℓ ≃ₗ[ZMod ℓ] U.torsion ℓ :=
  { e.torsionAddEquiv ℓ with
    map_smul' := fun c x ↦ ZMod.map_smul (e.torsionAddEquiv ℓ) c x }

/-- Reindexing components induces an additive equivalence on numerical Picard torsion. -/
noncomputable def torsionReindexAddEquiv (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) (ℓ : ℕ) : T.torsion ℓ ≃+ (T.reindex e).torsion ℓ := by
  unfold torsion
  exact torsionAddEquivOfAddEquiv (T.picReindexEquiv e) ℓ

@[simp] theorem torsionReindexAddEquiv_coe (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) (ℓ : ℕ) (x : T.torsion ℓ) :
    (T.torsionReindexAddEquiv e ℓ x : (T.reindex e).Pic) = T.picReindexEquiv e x := rfl

-- Typeclass search does not unfold the proof-producing `reindex` abbreviation reliably here.
instance torsionReindex_zmodModule (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) (ℓ : ℕ) : Module (ZMod ℓ) ((T.reindex e).torsion ℓ) :=
  torsion_zmodModule (T.reindex e) ℓ

/-- Reindexing components induces a `ZMod ℓ`-linear equivalence on numerical Picard torsion. -/
noncomputable def torsionReindexLinearEquiv (T : NumericalType.{u}) {J : Type v}
    (e : T.Component ≃ J) (ℓ : ℕ) :
    T.torsion ℓ ≃ₗ[ZMod ℓ] (T.reindex e).torsion ℓ :=
  { T.torsionReindexAddEquiv e ℓ with
    map_smul' := fun c x ↦ ZMod.map_smul (T.torsionReindexAddEquiv e ℓ) c x }

/-- The dimension of numerical Picard prime torsion over its prime field. -/
def primeTorsionDimension (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime] : ℕ :=
  Module.finrank (ZMod ℓ) (T.torsion ℓ)

/-- Prime torsion has dimension zero on a one-component fibre. -/
theorem primeTorsionDimension_eq_zero_of_card_eq_one
    (T : NumericalType) (hcard : Nat.card T.Component = 1)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    T.primeTorsionDimension ℓ = 0 := by
  rw [primeTorsionDimension]
  have ht := T.torsion_eq_bot_of_card_eq_one hcard ℓ (Fact.out : ℓ.Prime).ne_zero
  rw [Module.finrank_eq_zero_iff]
  intro x
  refine ⟨1, one_ne_zero, ?_⟩
  have hx : (x : T.Pic) = 0 := by
    rw [← AddSubgroup.mem_bot, ← ht]
    exact x.property
  apply Subtype.ext
  simp [hx]

/-- Numerical Picard prime torsion has the cardinality prescribed by its vector-space
dimension. -/
theorem primeTorsion_natCard (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime] :
    Nat.card (T.torsion ℓ) = ℓ ^ T.primeTorsionDimension ℓ := by
  rw [primeTorsionDimension,
    Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := T.torsion ℓ), Nat.card_zmod]

/-- Equivalent numerical types have prime-torsion spaces of the same dimension. -/
theorem Equiv.primeTorsionDimension_eq
    {T : NumericalType.{u}} {U : NumericalType.{v}} (e : T.Equiv U) (ℓ : ℕ)
    [Fact ℓ.Prime] :
    T.primeTorsionDimension ℓ = U.primeTorsionDimension ℓ := by
  exact LinearEquiv.finrank_eq (e.torsionLinearEquiv ℓ)

/-- Reindexing components preserves the dimension of prime torsion. -/
@[simp] theorem primeTorsionDimension_reindex
    (T : NumericalType.{u}) {J : Type v} (e : T.Component ≃ J) (ℓ : ℕ)
    [Fact ℓ.Prime] :
    (T.reindex e).primeTorsionDimension ℓ = T.primeTorsionDimension ℓ := by
  exact (LinearEquiv.finrank_eq (T.torsionReindexLinearEquiv e ℓ)).symm

/-- The rank-one numerical Picard group is not annihilated by any nonzero integer. -/
theorem torsion_ne_top (T : NumericalType) {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    T.torsion ℓ ≠ ⊤ := by
  intro htop
  have ht : Module.IsTorsion ℤ T.Pic := by
    intro x
    refine ⟨⟨(ℓ : ℤ), ?_⟩, ?_⟩
    · simpa using hℓ
    · have hx : x ∈ T.torsion ℓ := by rw [htop]; simp
      change (ℓ : ℤ) • x = 0 at hx
      exact hx
  have hr := ht.rank_eq_zero
  rw [T.pic_rank] at hr
  simp at hr

/-- Equivalently, for every nonzero `ℓ` there is a numerical Picard class not killed by `ℓ`. -/
theorem exists_not_torsion (T : NumericalType) {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    ∃ x : T.Pic, ℓ • x ≠ 0 := by
  by_contra h
  push Not at h
  apply T.torsion_ne_top hℓ
  ext x
  simp [T.mem_torsion_iff, h]

/-- The subgroup generated by the unweighted intersection rows.  This is deliberately
separate from `principalDivisors`: its quotient can contain torsion that is absent from the
weighted numerical Picard group. -/
def rawPrincipalDivisors (T : NumericalType) : AddSubgroup T.Divisor :=
  AddSubgroup.closure (Set.range T.intersection)

/-- Integral linear combinations of the raw intersection rows. -/
abbrev rawLinearMap (T : NumericalType) : T.Divisor →ₗ[ℤ] T.Divisor :=
  T.intersection.vecMulLinear

/-- The raw row subgroup is the range of the raw intersection linear map. -/
theorem rawLinearMap_range (T : NumericalType) :
    LinearMap.range T.rawLinearMap = T.rawPrincipalDivisors.toIntSubmodule := by
  rw [range_vecMulLinear, rawPrincipalDivisors, AddSubgroup.toIntSubmodule_closure]
  rfl

/-- The multiplicity-scaled antisymmetric flux attached to an integral row coefficient vector. -/
def rawEdgeFlux (T : NumericalType) (c : T.Divisor) (e : T.IntersectionEdge) : ℤ :=
  T.intersection (e.1.out).1 (e.1.out).2 *
    ((T.multiplicity (e.1.out).2 : ℤ) * c (e.1.out).1 -
      (T.multiplicity (e.1.out).1 : ℤ) * c (e.1.out).2)

/-- At an incident vertex, the oriented edge flux is the intrinsic flux toward the other
endpoint. -/
lemma incidence_mul_rawEdgeFlux_of_mem (T : NumericalType) (c : T.Divisor)
    (i : T.Component) (e : T.IntersectionEdge) (hi : i ∈ (e.1 : Sym2 T.Component)) :
    T.incidenceMatrix ℤ e i * T.rawEdgeFlux c e =
      T.intersection i (T.intersectionGraph.otherVertexOfIncident
          (show e.1 ∈ T.intersectionGraph.incidenceSet i from ⟨e.2, hi⟩)) *
        ((T.multiplicity (T.intersectionGraph.otherVertexOfIncident
            (show e.1 ∈ T.intersectionGraph.incidenceSet i from ⟨e.2, hi⟩)) : ℤ) * c i -
          (T.multiplicity i : ℤ) *
            c (T.intersectionGraph.otherVertexOfIncident
              (show e.1 ∈ T.intersectionGraph.incidenceSet i from ⟨e.2, hi⟩))) := by
  let hinc : e.1 ∈ T.intersectionGraph.incidenceSet i := ⟨e.2, hi⟩
  have hout :
      ((e.1.out).1 = i ∧ (e.1.out).2 =
          T.intersectionGraph.otherVertexOfIncident hinc) ∨
        ((e.1.out).2 = i ∧ (e.1.out).1 =
          T.intersectionGraph.otherVertexOfIncident hinc) := by
    have hpair := Sym2.eq_iff.mp
      (e.1.out_eq.trans (Sym2.other_spec' hi).symm)
    rcases hpair with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩
  rcases hout with hout | hout
  · rw [incidenceMatrix, if_pos hout.1.symm]
    simp only [one_mul, rawEdgeFlux]
    rw [hout.1, hout.2]
  · have hne : i ≠ e.1.out.1 := by
      intro h
      exact (T.intersectionEdge_out_adj e).ne (h.symm.trans hout.1.symm)
    rw [incidenceMatrix, if_neg hne, if_pos hout.1.symm]
    simp only [neg_mul, one_mul, rawEdgeFlux]
    rw [hout.1, hout.2, T.intersection_symm]
    ring

/-- The boundary sum of the edge flux is the sum of the intrinsic fluxes to adjacent
vertices. -/
lemma sum_incidence_mul_rawEdgeFlux (T : NumericalType) (c : T.Divisor)
    (i : T.Component) :
    (∑ e : T.IntersectionEdge, T.incidenceMatrix ℤ e i * T.rawEdgeFlux c e) =
      ∑ j : T.intersectionGraph.neighborSet i,
        (fun k : T.intersectionGraph.neighborSet i =>
          T.intersection i (k : T.Component) *
            ((T.multiplicity (k : T.Component) : ℤ) * c i -
              (T.multiplicity i : ℤ) * c (k : T.Component))) j := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype
    (p := fun e : T.IntersectionEdge => i ∈ (e.1 : Sym2 T.Component))]
  have hzero : (∑ e : {e : T.IntersectionEdge // ¬ i ∈ (e.1 : Sym2 T.Component)},
      T.incidenceMatrix ℤ e.1 i * T.rawEdgeFlux c e.1) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    rw [incidenceMatrix]
    have hfirst : i ≠ (e.1.1.out).1 := by
      intro h
      apply e.2
      rw [← e.1.1.out_eq, Sym2.mem_iff]
      exact Or.inl h
    have hsecond : i ≠ (e.1.1.out).2 := by
      intro h
      apply e.2
      rw [← e.1.1.out_eq, Sym2.mem_iff]
      exact Or.inr h
    simp [hfirst, hsecond]
  rw [hzero, add_zero]
  apply Fintype.sum_equiv (T.incidentEdgeEquiv i)
  intro e
  rw [T.incidence_mul_rawEdgeFlux_of_mem c i e.1 e.2]
  congr 2

private lemma sum_neighbor_flux_eq_all (T : NumericalType) (c : T.Divisor)
    (i : T.Component) :
    (∑ j : T.intersectionGraph.neighborSet i,
        (fun k : T.intersectionGraph.neighborSet i =>
          T.intersection i (k : T.Component) *
            ((T.multiplicity (k : T.Component) : ℤ) * c i -
              (T.multiplicity i : ℤ) * c (k : T.Component))) j) =
      ∑ j : T.Component, T.intersection i j *
        ((T.multiplicity j : ℤ) * c i - (T.multiplicity i : ℤ) * c j) := by
  classical
  let flux : T.Component → ℤ := fun j => T.intersection i j *
    ((T.multiplicity j : ℤ) * c i - (T.multiplicity i : ℤ) * c j)
  change (∑ j : T.intersectionGraph.neighborSet i,
    (fun k : T.intersectionGraph.neighborSet i => flux (k : T.Component)) j) =
    ∑ j, flux j
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun j : T.Component => T.intersectionGraph.Adj i j)
    (by simp) flux]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j _ hj
  have hjnot : ¬ T.intersectionGraph.Adj i j := by simpa using hj
  by_cases hji : j = i
  · dsimp only [flux]
    rw [hji]
    ring
  · have hne : i ≠ j := fun h ↦ hji h.symm
    have hnonneg := T.offDiagonal_nonnegative i j hne
    have hnotpos : ¬ 0 < T.intersection i j := fun hpos =>
      hjnot ⟨hne, hpos⟩
    have hentry : T.intersection i j = 0 := by omega
    dsimp only [flux]
    rw [hentry, zero_mul]

/-- The divergence of the multiplicity-scaled edge flux is minus multiplicity times the raw
intersection relation. -/
lemma sum_incidence_mul_rawEdgeFlux_eq (T : NumericalType) (c : T.Divisor)
    (i : T.Component) :
    (∑ e : T.IntersectionEdge, T.incidenceMatrix ℤ e i * T.rawEdgeFlux c e) =
      -(T.multiplicity i : ℤ) * T.rawLinearMap c i := by
  rw [T.sum_incidence_mul_rawEdgeFlux c i, sum_neighbor_flux_eq_all T c i]
  calc
    (∑ j, T.intersection i j *
      ((T.multiplicity j : ℤ) * c i - (T.multiplicity i : ℤ) * c j)) =
        c i * (∑ j, (T.multiplicity j : ℤ) * T.intersection i j) -
          (T.multiplicity i : ℤ) * ∑ j, c j * T.intersection i j := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
    _ = -(T.multiplicity i : ℤ) * T.rawLinearMap c i := by
      rw [T.fiber_relation i, mul_zero, zero_sub]
      have hsum : (∑ j, c j * T.intersection i j) = T.rawLinearMap c i := by
        change (∑ j, c j * T.intersection i j) = ∑ j, c j * T.intersection j i
        apply Finset.sum_congr rfl
        intro j _
        rw [T.intersection_symm i j]
      rw [hsum]
      ring

/-- Cokernel of the raw intersection matrix. -/
abbrev RawCoker (T : NumericalType) := T.Divisor ⧸ T.rawPrincipalDivisors

/-- The `ℓ`-torsion subgroup of the raw intersection cokernel. -/
def rawTorsion (T : NumericalType) (ℓ : ℕ) : AddSubgroup T.RawCoker :=
  AddSubgroup.torsionBy T.RawCoker (ℓ : ℤ)

instance rawTorsion_zmodModule (T : NumericalType) (ℓ : ℕ) :
    Module (ZMod ℓ) (T.rawTorsion ℓ) := by
  unfold rawTorsion
  exact AddSubgroup.torsionBy.zmodModule

instance rawCoker_moduleFinite (T : NumericalType) : Module.Finite ℤ T.RawCoker :=
  Module.Finite.quotient ℤ T.rawPrincipalDivisors.toIntSubmodule

instance rawTorsion_intModuleFinite (T : NumericalType) (ℓ : ℕ) :
    Module.Finite ℤ (T.rawTorsion ℓ) := by
  change Module.Finite ℤ (Submodule.torsionBy ℤ T.RawCoker (ℓ : ℤ))
  rw [Module.Finite.iff_fg]
  exact Submodule.FG.of_le Module.Finite.fg_top le_top

instance rawPrimeTorsion_finite (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime] :
    Finite (T.rawTorsion ℓ) := by
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(ℓ : ℤ), ?_⟩, ?_⟩
  · simpa using (Fact.out : ℓ.Prime).ne_zero
  · exact AddSubgroup.torsionBy.nsmul x

instance rawPrimeTorsion_moduleFinite (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.Finite (ZMod ℓ) (T.rawTorsion ℓ) := by
  infer_instance

/-- A raw divisor represents an `ℓ`-torsion class exactly when its `ℓ`-multiple is an
integral linear combination of the raw intersection rows. -/
theorem raw_mk_mem_torsion_iff_exists (T : NumericalType) (ℓ : ℕ) (D : T.Divisor) :
    (QuotientAddGroup.mk D : T.RawCoker) ∈ T.rawTorsion ℓ ↔
      ∃ c : T.Divisor, T.rawLinearMap c = ℓ • D := by
  change (ℓ : ℤ) • (QuotientAddGroup.mk D : T.RawCoker) = 0 ↔ _
  rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
  change (ℓ : ℤ) • D ∈ T.rawPrincipalDivisors.toIntSubmodule ↔ _
  rw [← T.rawLinearMap_range]
  exact LinearMap.mem_range

/-- A raw `ℓ`-torsion presentation determines a cycle in the intersection graph. -/
def rawCycleOfRelation (T : NumericalType) (ℓ : ℕ)
    (c D : T.Divisor) (hc : T.rawLinearMap c = ℓ • D) :
    LinearMap.ker (T.incidenceMatrix (ZMod ℓ)).transpose.mulVecLin := by
  refine ⟨fun e ↦ (T.rawEdgeFlux c e : ZMod ℓ), ?_⟩
  rw [LinearMap.mem_ker]
  funext i
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  simp only [Matrix.transpose_apply, Pi.zero_apply]
  simp_rw [show ∀ e : T.IntersectionEdge,
      T.incidenceMatrix (ZMod ℓ) e i = (T.incidenceMatrix ℤ e i : ZMod ℓ) by
        intro e
        simp [incidenceMatrix]]
  simp_rw [← Int.cast_mul]
  rw [← Int.cast_sum]
  change (∑ e : T.IntersectionEdge,
    (T.incidenceMatrix ℤ e i * T.rawEdgeFlux c e : ℤ)) = (0 : ZMod ℓ)
  rw [T.sum_incidence_mul_rawEdgeFlux_eq c i, congrFun hc i]
  simp

lemma intersection_mulVec_eq_zero_of_rawLinearMap_eq_zero
    (T : NumericalType) (c : T.Divisor) (hc : T.rawLinearMap c = 0) :
    Matrix.mulVec T.intersection c = 0 := by
  funext i
  have hi := congrFun hc i
  change ∑ j, c j * T.intersection j i = 0 at hi
  change ∑ j, T.intersection i j * c j = 0
  calc
    _ = ∑ j, c j * T.intersection j i := by
      apply Finset.sum_congr rfl
      intro j _
      rw [T.intersection_symm i j]
      ring
    _ = 0 := hi

lemma rawEdgeFlux_eq_zero_of_rawLinearMap_eq_zero
    (T : NumericalType) (c : T.Divisor) (hc : T.rawLinearMap c = 0)
    (e : T.IntersectionEdge) : T.rawEdgeFlux c e = 0 := by
  have hratio := ratio_eq_of_intersection_mulVec_eq_zero T c
    (T.intersection_mulVec_eq_zero_of_rawLinearMap_eq_zero c hc)
      (e.1.out).1 (e.1.out).2
  have hs : (T.multiplicity (e.1.out).1 : ℚ) ≠ 0 := by positivity
  have ht : (T.multiplicity (e.1.out).2 : ℚ) ≠ 0 := by positivity
  have hcross := (div_eq_div_iff hs ht).mp hratio
  have hcrossZ :
      c (e.1.out).1 * (T.multiplicity (e.1.out).2 : ℤ) =
        c (e.1.out).2 * (T.multiplicity (e.1.out).1 : ℤ) := by
    exact_mod_cast hcross
  rw [rawEdgeFlux]
  have hzero :
      (T.multiplicity (e.1.out).2 : ℤ) * c (e.1.out).1 -
        (T.multiplicity (e.1.out).1 : ℤ) * c (e.1.out).2 = 0 := by
    rw [mul_comm (T.multiplicity (e.1.out).2 : ℤ),
      mul_comm (T.multiplicity (e.1.out).1 : ℤ), hcrossZ, sub_self]
  rw [hzero, mul_zero]

/-- The cycle attached to a raw torsion class is independent of its integral presentation. -/
lemma rawCycleOfRelation_eq (T : NumericalType) (ℓ : ℕ)
    (c D c' D' : T.Divisor) (hc : T.rawLinearMap c = ℓ • D)
    (hc' : T.rawLinearMap c' = ℓ • D')
    (hD : (QuotientAddGroup.mk D : T.RawCoker) = QuotientAddGroup.mk D') :
    T.rawCycleOfRelation ℓ c D hc = T.rawCycleOfRelation ℓ c' D' hc' := by
  have hmem : D - D' ∈ T.rawPrincipalDivisors.toIntSubmodule :=
    QuotientAddGroup.eq_iff_sub_mem.mp hD
  rw [← T.rawLinearMap_range] at hmem
  obtain ⟨z, hz⟩ := hmem
  let r : T.Divisor := c - c' - ℓ • z
  have hr : T.rawLinearMap r = 0 := by
    dsimp only [r]
    rw [map_sub, map_sub, map_nsmul, hc, hc', hz, nsmul_sub]
    abel
  apply Subtype.ext
  funext e
  have hre := T.rawEdgeFlux_eq_zero_of_rawLinearMap_eq_zero r hr e
  have hexpand : T.rawEdgeFlux r e =
      T.rawEdgeFlux c e - T.rawEdgeFlux c' e - (ℓ : ℤ) * T.rawEdgeFlux z e := by
    simp only [r, rawEdgeFlux, Pi.sub_apply, Pi.smul_apply]
    ring
  rw [hexpand] at hre
  have hcast := congrArg (fun a : ℤ ↦ (a : ZMod ℓ)) hre
  change (T.rawEdgeFlux c e : ZMod ℓ) = (T.rawEdgeFlux c' e : ZMod ℓ)
  simpa [sub_eq_zero] using hcast

private noncomputable def rawTorsionRepresentative
    (T : NumericalType) (ℓ : ℕ) (x : T.rawTorsion ℓ) : T.Divisor :=
  Classical.choose (QuotientAddGroup.mk_surjective (x : T.RawCoker))

private lemma rawTorsionRepresentative_spec
    (T : NumericalType) (ℓ : ℕ) (x : T.rawTorsion ℓ) :
    (QuotientAddGroup.mk (T.rawTorsionRepresentative ℓ x) : T.RawCoker) = x :=
  Classical.choose_spec (QuotientAddGroup.mk_surjective (x : T.RawCoker))

private noncomputable def rawTorsionCoefficient
    (T : NumericalType) (ℓ : ℕ) (x : T.rawTorsion ℓ) : T.Divisor := by
  let D := T.rawTorsionRepresentative ℓ x
  have hx : (QuotientAddGroup.mk D : T.RawCoker) ∈ T.rawTorsion ℓ := by
    rw [T.rawTorsionRepresentative_spec ℓ x]
    exact x.property
  exact Classical.choose ((T.raw_mk_mem_torsion_iff_exists ℓ D).mp hx)

private lemma rawTorsionCoefficient_spec
    (T : NumericalType) (ℓ : ℕ) (x : T.rawTorsion ℓ) :
    T.rawLinearMap (T.rawTorsionCoefficient ℓ x) =
      ℓ • T.rawTorsionRepresentative ℓ x := by
  let D := T.rawTorsionRepresentative ℓ x
  have hx : (QuotientAddGroup.mk D : T.RawCoker) ∈ T.rawTorsion ℓ := by
    rw [T.rawTorsionRepresentative_spec ℓ x]
    exact x.property
  exact Classical.choose_spec ((T.raw_mk_mem_torsion_iff_exists ℓ D).mp hx)

/-- The connecting map from raw cokernel `ℓ`-torsion to the graph cycle space. -/
noncomputable def rawTorsionToCycle (T : NumericalType) (ℓ : ℕ) :
    T.rawTorsion ℓ →
      LinearMap.ker (T.incidenceMatrix (ZMod ℓ)).transpose.mulVecLin := fun x ↦
  T.rawCycleOfRelation ℓ (T.rawTorsionCoefficient ℓ x)
    (T.rawTorsionRepresentative ℓ x) (T.rawTorsionCoefficient_spec ℓ x)

lemma rawTorsionToCycle_eq_of_presentation
    (T : NumericalType) (ℓ : ℕ) (x : T.rawTorsion ℓ)
    (c D : T.Divisor) (hc : T.rawLinearMap c = ℓ • D)
    (hD : (QuotientAddGroup.mk D : T.RawCoker) = x) :
    T.rawTorsionToCycle ℓ x = T.rawCycleOfRelation ℓ c D hc := by
  apply T.rawCycleOfRelation_eq
  exact (T.rawTorsionRepresentative_spec ℓ x).trans hD.symm

lemma rawTorsionToCycle_zero (T : NumericalType) (ℓ : ℕ) :
    T.rawTorsionToCycle ℓ 0 = 0 := by
  have hc : T.rawLinearMap (0 : T.Divisor) = ℓ • (0 : T.Divisor) := by simp
  rw [T.rawTorsionToCycle_eq_of_presentation ℓ 0 0 0 hc (by simp)]
  apply Subtype.ext
  funext e
  simp [rawCycleOfRelation, rawEdgeFlux]

lemma rawTorsionToCycle_add (T : NumericalType) (ℓ : ℕ) (x y : T.rawTorsion ℓ) :
    T.rawTorsionToCycle ℓ (x + y) =
      T.rawTorsionToCycle ℓ x + T.rawTorsionToCycle ℓ y := by
  let cx := T.rawTorsionCoefficient ℓ x
  let cy := T.rawTorsionCoefficient ℓ y
  let Dx := T.rawTorsionRepresentative ℓ x
  let Dy := T.rawTorsionRepresentative ℓ y
  have hc : T.rawLinearMap (cx + cy) = ℓ • (Dx + Dy) := by
    rw [map_add, T.rawTorsionCoefficient_spec ℓ x,
      T.rawTorsionCoefficient_spec ℓ y, nsmul_add]
  have hD : (QuotientAddGroup.mk (Dx + Dy) : T.RawCoker) = x + y := by
    rw [QuotientAddGroup.mk_add, T.rawTorsionRepresentative_spec ℓ x,
      T.rawTorsionRepresentative_spec ℓ y]
  rw [T.rawTorsionToCycle_eq_of_presentation ℓ (x + y) (cx + cy) (Dx + Dy) hc hD]
  apply Subtype.ext
  funext e
  change (T.rawEdgeFlux (cx + cy) e : ZMod ℓ) =
    (T.rawEdgeFlux cx e : ZMod ℓ) + (T.rawEdgeFlux cy e : ZMod ℓ)
  have hflux : T.rawEdgeFlux (cx + cy) e =
      T.rawEdgeFlux cx e + T.rawEdgeFlux cy e := by
    simp only [rawEdgeFlux, Pi.add_apply]
    ring
  rw [hflux]
  push_cast
  rfl

/-- The raw-torsion connecting map as an additive homomorphism. -/
noncomputable def rawTorsionToCycleAdd (T : NumericalType) (ℓ : ℕ) :
    T.rawTorsion ℓ →+
      LinearMap.ker (T.incidenceMatrix (ZMod ℓ)).transpose.mulVecLin where
  toFun := T.rawTorsionToCycle ℓ
  map_zero' := T.rawTorsionToCycle_zero ℓ
  map_add' := T.rawTorsionToCycle_add ℓ

/-- The raw-torsion connecting map is linear over `ZMod ℓ`. -/
noncomputable def rawTorsionToCycleLinear (T : NumericalType) (ℓ : ℕ) :
    T.rawTorsion ℓ →ₗ[ZMod ℓ]
      LinearMap.ker (T.incidenceMatrix (ZMod ℓ)).transpose.mulVecLin :=
  { T.rawTorsionToCycleAdd ℓ with
    map_smul' := fun c x ↦ ZMod.map_smul (T.rawTorsionToCycleAdd ℓ) c x }

@[simp] lemma rawLinearMap_multiplicityDivisor (T : NumericalType) :
    T.rawLinearMap T.multiplicityDivisor = 0 := by
  funext j
  change ∑ i, (T.multiplicity i : ℤ) * T.intersection i j = 0
  calc
    _ = ∑ i, (T.multiplicity i : ℤ) * T.intersection j i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [T.intersection_symm i j]
    _ = 0 := T.fiber_relation j

lemma ratio_mod_eq_of_rawEdgeFlux_eq_zero
    (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime]
    (c : T.Divisor) (e : T.IntersectionEdge)
    (hm : ∀ i, IsUnit (T.multiplicity i : ZMod ℓ))
    (he : IsUnit (T.intersection (e.1.out).1 (e.1.out).2 : ZMod ℓ))
    (hflux : (T.rawEdgeFlux c e : ZMod ℓ) = 0) :
    (c (e.1.out).1 : ZMod ℓ) / (T.multiplicity (e.1.out).1 : ZMod ℓ) =
      (c (e.1.out).2 : ZMod ℓ) / (T.multiplicity (e.1.out).2 : ZMod ℓ) := by
  have hs : (T.multiplicity (e.1.out).1 : ZMod ℓ) ≠ 0 := (hm _).ne_zero
  have ht : (T.multiplicity (e.1.out).2 : ZMod ℓ) ≠ 0 := (hm _).ne_zero
  apply (div_eq_div_iff hs ht).mpr
  have hbracket :
      (T.multiplicity (e.1.out).2 : ZMod ℓ) * (c (e.1.out).1 : ZMod ℓ) -
        (T.multiplicity (e.1.out).1 : ZMod ℓ) * (c (e.1.out).2 : ZMod ℓ) = 0 := by
    rw [rawEdgeFlux] at hflux
    push_cast at hflux
    exact (mul_eq_zero.mp hflux).resolve_left he.ne_zero
  rw [sub_eq_zero] at hbracket
  calc
    (c (e.1.out).1 : ZMod ℓ) * (T.multiplicity (e.1.out).2 : ZMod ℓ) =
        (T.multiplicity (e.1.out).2 : ZMod ℓ) * (c (e.1.out).1 : ZMod ℓ) := mul_comm _ _
    _ = (T.multiplicity (e.1.out).1 : ZMod ℓ) *
        (c (e.1.out).2 : ZMod ℓ) := hbracket
    _ = (c (e.1.out).2 : ZMod ℓ) *
        (T.multiplicity (e.1.out).1 : ZMod ℓ) := mul_comm _ _

lemma ratio_mod_eq_of_adj (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime]
    (c : T.Divisor) (hm : ∀ i, IsUnit (T.multiplicity i : ZMod ℓ))
    (ha : ∀ i j, T.intersectionGraph.Adj i j →
      IsUnit (T.intersection i j : ZMod ℓ))
    (D : T.Divisor) (hc : T.rawLinearMap c = ℓ • D)
    (hcycle : T.rawCycleOfRelation ℓ c D hc = 0)
    {i j : T.Component} (hij : T.intersectionGraph.Adj i j) :
    (c i : ZMod ℓ) / (T.multiplicity i : ZMod ℓ) =
      (c j : ZMod ℓ) / (T.multiplicity j : ZMod ℓ) := by
  let e : T.IntersectionEdge := ⟨s(i, j), by
    rw [SimpleGraph.mem_edgeSet]
    exact hij⟩
  have hflux : (T.rawEdgeFlux c e : ZMod ℓ) = 0 := by
    have he := congrArg
      (fun z : LinearMap.ker (T.incidenceMatrix (ZMod ℓ)).transpose.mulVecLin ↦ z.1 e) hcycle
    exact he
  have hedge : IsUnit (T.intersection (e.1.out).1 (e.1.out).2 : ZMod ℓ) :=
    ha _ _ (T.intersectionEdge_out_adj e)
  have hratio := T.ratio_mod_eq_of_rawEdgeFlux_eq_zero ℓ c e hm hedge hflux
  have hout :
      ((e.1.out).1 = i ∧ (e.1.out).2 = j) ∨
        ((e.1.out).1 = j ∧ (e.1.out).2 = i) := Sym2.eq_iff.mp e.1.out_eq
  rcases hout with hout | hout
  · simpa [hout.1, hout.2] using hratio
  · simpa [hout.1, hout.2] using hratio.symm

lemma ratio_mod_eq_of_rawCycle_eq_zero
    (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime]
    (c D : T.Divisor) (hc : T.rawLinearMap c = ℓ • D)
    (hm : ∀ i, IsUnit (T.multiplicity i : ZMod ℓ))
    (ha : ∀ i j, T.intersectionGraph.Adj i j →
      IsUnit (T.intersection i j : ZMod ℓ))
    (hcycle : T.rawCycleOfRelation ℓ c D hc = 0) (i j : T.Component) :
    (c i : ZMod ℓ) / (T.multiplicity i : ZMod ℓ) =
      (c j : ZMod ℓ) / (T.multiplicity j : ZMod ℓ) := by
  induction T.connected i j with
  | refl => rfl
  | @tail j k _ hjk ih =>
      exact ih.trans (T.ratio_mod_eq_of_adj ℓ c hm ha D hc hcycle hjk)

lemma rawTorsionToCycle_eq_zero_iff
    (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime]
    (hm : ∀ i, IsUnit (T.multiplicity i : ZMod ℓ))
    (ha : ∀ i j, T.intersectionGraph.Adj i j →
      IsUnit (T.intersection i j : ZMod ℓ))
    (x : T.rawTorsion ℓ) : T.rawTorsionToCycle ℓ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    let c := T.rawTorsionCoefficient ℓ x
    let D := T.rawTorsionRepresentative ℓ x
    have hc : T.rawLinearMap c = ℓ • D := T.rawTorsionCoefficient_spec ℓ x
    have hcycle : T.rawCycleOfRelation ℓ c D hc = 0 := by
      rw [← T.rawTorsionToCycle_eq_of_presentation ℓ x c D hc
        (T.rawTorsionRepresentative_spec ℓ x)]
      exact hx
    let a : T.Component := Classical.choice T.componentNonempty
    let q : ZMod ℓ := (c a : ZMod ℓ) / (T.multiplicity a : ZMod ℓ)
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective q
    have hcoord (i : T.Component) :
        ((c i - k * (T.multiplicity i : ℤ) : ℤ) : ZMod ℓ) = 0 := by
      have hratio := T.ratio_mod_eq_of_rawCycle_eq_zero ℓ c D hc hm ha hcycle i a
      have hmi : (T.multiplicity i : ZMod ℓ) ≠ 0 := (hm i).ne_zero
      have hci : (c i : ZMod ℓ) = q * (T.multiplicity i : ZMod ℓ) := by
        apply (div_eq_iff hmi).mp
        exact hratio
      push_cast
      rw [hci, hk]
      ring
    have hdvd (i : T.Component) : (ℓ : ℤ) ∣ c i - k * (T.multiplicity i : ℤ) :=
      (CharP.intCast_eq_zero_iff (ZMod ℓ) ℓ _).mp (hcoord i)
    choose z hz using hdvd
    have hc_decomp : c = k • T.multiplicityDivisor + ℓ • z := by
      funext i
      change c i = k * (T.multiplicity i : ℤ) + ℓ * z i
      have hi := hz i
      omega
    have hscaled : ℓ • T.rawLinearMap z = ℓ • D := by
      calc
        ℓ • T.rawLinearMap z = T.rawLinearMap (ℓ • z) := by rw [map_nsmul]
        _ = T.rawLinearMap c := by
          rw [hc_decomp, map_add, map_zsmul, T.rawLinearMap_multiplicityDivisor,
            smul_zero, zero_add]
        _ = ℓ • D := hc
    have hzD : T.rawLinearMap z = D := by
      funext i
      have hi := congrFun hscaled i
      change (ℓ : ℤ) * T.rawLinearMap z i = (ℓ : ℤ) * D i at hi
      exact mul_left_cancel₀ (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero) hi
    apply Subtype.ext
    change (x : T.RawCoker) = 0
    rw [← T.rawTorsionRepresentative_spec ℓ x]
    change (QuotientAddGroup.mk D : T.RawCoker) = 0
    rw [← hzD, QuotientAddGroup.eq_zero_iff]
    change T.rawLinearMap z ∈ T.rawPrincipalDivisors.toIntSubmodule
    rw [← T.rawLinearMap_range]
    exact ⟨z, rfl⟩
  · rintro rfl
    exact T.rawTorsionToCycle_zero ℓ

/-- If the prime is invertible on all multiplicities and nonzero off-diagonal intersections,
the raw-torsion connecting map is injective. -/
theorem rawTorsionToCycle_injective
    (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime]
    (hm : ∀ i, IsUnit (T.multiplicity i : ZMod ℓ))
    (ha : ∀ i j, T.intersectionGraph.Adj i j →
      IsUnit (T.intersection i j : ZMod ℓ)) :
    Function.Injective (T.rawTorsionToCycleLinear ℓ) := by
  rw [← LinearMap.ker_eq_bot]
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_bot]
  change T.rawTorsionToCycle ℓ x = 0 ↔ x = 0
  exact T.rawTorsionToCycle_eq_zero_iff ℓ hm ha x

/-- Raw intersection-cokernel prime torsion is bounded by the first Betti number of the
intersection graph. -/
theorem rawPrimeTorsion_finrank_le_topologicalGenus
    (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime]
    (hm : ∀ i, IsUnit (T.multiplicity i : ZMod ℓ))
    (ha : ∀ i j, T.intersectionGraph.Adj i j →
      IsUnit (T.intersection i j : ZMod ℓ)) :
    Module.finrank (ZMod ℓ) (T.rawTorsion ℓ) ≤ T.topologicalGenus := by
  calc
    _ ≤ Module.finrank (ZMod ℓ)
        (LinearMap.ker (T.incidenceMatrix (ZMod ℓ)).transpose.mulVecLin) :=
      LinearMap.finrank_le_finrank_of_injective (T.rawTorsionToCycle_injective ℓ hm ha)
    _ = T.topologicalGenus := T.boundaryMatrix_ker_finrank (ZMod ℓ)

/-- Stacks Project tag `0C6X`, in coprimality form. -/
theorem rawPrimeTorsion_finrank_le_topologicalGenus_of_coprime
    (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime]
    (hm : ∀ i, Nat.Coprime ℓ (T.multiplicity i : ℕ))
    (ha : ∀ i j, T.intersectionGraph.Adj i j →
      Nat.Coprime ℓ (T.intersection i j).natAbs) :
    Module.finrank (ZMod ℓ) (T.rawTorsion ℓ) ≤ T.topologicalGenus := by
  apply T.rawPrimeTorsion_finrank_le_topologicalGenus ℓ
  · intro i
    exact (ZMod.isUnit_iff_coprime (T.multiplicity i : ℕ) ℓ).mpr (hm i).symm
  · intro i j hij
    have hunit : IsUnit ((T.intersection i j).natAbs : ZMod ℓ) :=
      (ZMod.isUnit_iff_coprime (T.intersection i j).natAbs ℓ).mpr (ha i j hij).symm
    have hnonneg : 0 ≤ T.intersection i j := le_of_lt hij.2
    have habs : ((T.intersection i j).natAbs : ℤ) = T.intersection i j :=
      Int.natAbs_of_nonneg hnonneg
    have hcast : ((T.intersection i j).natAbs : ZMod ℓ) =
        (T.intersection i j : ZMod ℓ) := by
      rw [← Int.cast_natCast, habs]
    rw [hcast] at hunit
    exact hunit

/-- Multiply the coefficient at component `j` by its constant-field weight `wⱼ`. -/
def weightScale (T : NumericalType) : T.Divisor →+ T.Divisor where
  toFun D j := (T.weight j : ℤ) * D j
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [mul_add]

lemma weightScale_principalDivisor (T : NumericalType) (i : T.Component) :
    T.weightScale (T.principalDivisor i) = T.intersection i := by
  funext j
  rw [weightScale]
  simpa [mul_comm] using T.principalDivisor_mul_weight i j

lemma weightScale_injective (T : NumericalType) : Function.Injective T.weightScale := by
  intro D E h
  funext j
  have hj := congrFun h j
  dsimp [weightScale] at hj
  exact mul_left_cancel₀ (by positivity : (T.weight j : ℤ) ≠ 0) hj

/-- Scaling weighted relations by the destination weights gives exactly the raw rows. -/
lemma rawPrincipalDivisors_eq_map (T : NumericalType) :
    T.rawPrincipalDivisors = T.principalDivisors.map T.weightScale := by
  apply le_antisymm
  · rw [rawPrincipalDivisors, AddSubgroup.closure_le]
    rintro D ⟨i, rfl⟩
    rw [← T.weightScale_principalDivisor i]
    exact ⟨T.principalDivisor i,
      AddSubgroup.subset_closure (Set.mem_range_self i), rfl⟩
  · rw [AddSubgroup.map_le_iff_le_comap, principalDivisors, AddSubgroup.closure_le]
    rintro D ⟨i, rfl⟩
    change T.weightScale (T.principalDivisor i) ∈ T.rawPrincipalDivisors
    rw [T.weightScale_principalDivisor i]
    exact AddSubgroup.subset_closure (Set.mem_range_self i)

/-- The canonical map from the weighted Picard group to the raw cokernel. -/
def toRawCoker (T : NumericalType) : T.Pic →+ T.RawCoker :=
  QuotientAddGroup.map T.principalDivisors T.rawPrincipalDivisors T.weightScale (by
    rw [← AddSubgroup.map_le_iff_le_comap, ← T.rawPrincipalDivisors_eq_map])

/-- The weighted numerical Picard group injects into the raw cokernel. -/
theorem toRawCoker_injective (T : NumericalType) : Function.Injective T.toRawCoker := by
  rw [← AddMonoidHom.ker_eq_bot_iff]
  ext x
  constructor
  · intro hx
    induction x using QuotientAddGroup.induction_on with
    | _ D =>
      rw [AddMonoidHom.mem_ker] at hx
      rw [toRawCoker, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff] at hx
      rw [rawPrincipalDivisors_eq_map, AddSubgroup.mem_map] at hx
      obtain ⟨P, hP, hscale⟩ := hx
      rw [AddSubgroup.mem_bot, QuotientAddGroup.eq_zero_iff]
      have hPD : P = D := T.weightScale_injective hscale
      rwa [← hPD]
  · rintro rfl
    exact AddMonoidHom.map_zero _

/-- The injection into the raw cokernel restricts to an additive map on `ℓ`-torsion. -/
def torsionToRaw (T : NumericalType) (ℓ : ℕ) : T.torsion ℓ →+ T.rawTorsion ℓ where
  toFun x := ⟨T.toRawCoker x, by
    change (ℓ : ℤ) • T.toRawCoker (x : T.Pic) = 0
    rw [← map_zsmul]
    have hx : (ℓ : ℤ) • (x : T.Pic) = 0 := x.property
    rw [hx, map_zero]⟩
  map_zero' := by ext; simp
  map_add' x y := by
    apply Subtype.ext
    exact T.toRawCoker.map_add (x : T.Pic) (y : T.Pic)

/-- The torsion comparison map is linear over `ZMod ℓ`. -/
def torsionToRawLinear (T : NumericalType) (ℓ : ℕ) :
    T.torsion ℓ →ₗ[ZMod ℓ] T.rawTorsion ℓ :=
  { T.torsionToRaw ℓ with
    map_smul' := fun c x ↦ ZMod.map_smul (T.torsionToRaw ℓ) c x }

/-- Weighted numerical Picard torsion injects into raw intersection-cokernel torsion. -/
theorem torsionToRaw_injective (T : NumericalType) (ℓ : ℕ) :
    Function.Injective (T.torsionToRaw ℓ) := by
  intro x y hxy
  apply Subtype.ext
  apply T.toRawCoker_injective
  exact congrArg Subtype.val hxy

/-- The prime-torsion dimension of the weighted Picard group is at most that of the raw
intersection cokernel. -/
theorem primeTorsionDimension_le_raw (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime] :
    T.primeTorsionDimension ℓ ≤ Module.finrank (ZMod ℓ) (T.rawTorsion ℓ) := by
  apply LinearMap.finrank_le_finrank_of_injective (f := T.torsionToRawLinear ℓ)
  exact T.torsionToRaw_injective ℓ

/-- Under the coprimality hypotheses of Stacks Project tag `0C6X`, weighted numerical Picard
prime torsion has dimension at most the graph's topological genus. -/
theorem primeTorsionDimension_le_topologicalGenus_of_coprime
    (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime]
    (hm : ∀ i, Nat.Coprime ℓ (T.multiplicity i : ℕ))
    (ha : ∀ i j, T.intersectionGraph.Adj i j →
      Nat.Coprime ℓ (T.intersection i j).natAbs) :
    T.primeTorsionDimension ℓ ≤ T.topologicalGenus :=
  (T.primeTorsionDimension_le_raw ℓ).trans
    (T.rawPrimeTorsion_finrank_le_topologicalGenus_of_coprime ℓ hm ha)

/-- A prime exceeding every diagonal product is coprime to every component multiplicity. -/
lemma multiplicity_coprime_of_diagonalProduct_lt_prime (T : NumericalType)
    (hcard : 1 < Nat.card T.Component) (ℓ : ℕ) (hprime : ℓ.Prime)
    (hbound : ∀ i, T.diagonalProduct i < (ℓ : ℤ)) (i : T.Component) :
    Nat.Coprime ℓ (T.multiplicity i : ℕ) := by
  have hdiag := T.selfIntersection_neg_of_one_lt_card hcard i
  have habs : (1 : ℤ) ≤ |T.intersection i i| := by
    rw [abs_of_neg hdiag]
    omega
  have hmpos : (0 : ℤ) < (T.multiplicity i : ℤ) := by positivity
  have hmle : (T.multiplicity i : ℤ) ≤ T.diagonalProduct i := by
    dsimp [diagonalProduct]
    nlinarith [mul_nonneg (le_of_lt hmpos) (sub_nonneg.mpr habs)]
  have hmltZ : (T.multiplicity i : ℤ) < (ℓ : ℤ) := lt_of_le_of_lt hmle (hbound i)
  have hmlt : (T.multiplicity i : ℕ) < ℓ := by exact_mod_cast hmltZ
  apply hprime.coprime_iff_not_dvd.mpr
  intro hdvd
  have hle := Nat.le_of_dvd (by positivity : 0 < (T.multiplicity i : ℕ)) hdvd
  omega

/-- A prime exceeding every diagonal product is coprime to every nonzero edge entry. -/
lemma intersection_coprime_of_diagonalProduct_lt_prime (T : NumericalType)
    (ℓ : ℕ) (hprime : ℓ.Prime) (hbound : ∀ i, T.diagonalProduct i < (ℓ : ℤ))
    {i j : T.Component} (hij : T.intersectionGraph.Adj i j) :
    Nat.Coprime ℓ (T.intersection i j).natAbs := by
  have hedge := T.edgeProduct_le_diagonalProduct hij
  have hm : (1 : ℤ) ≤ (T.multiplicity i : ℤ) := by
    have : (0 : ℤ) < (T.multiplicity i : ℤ) := by positivity
    omega
  have ha : (0 : ℤ) < T.intersection i j := hij.2
  have hale : T.intersection i j ≤
      (T.multiplicity i : ℤ) * T.intersection i j := by nlinarith
  have haltZ : T.intersection i j < (ℓ : ℤ) :=
    lt_of_le_of_lt (hale.trans hedge) (hbound j)
  have halt : (T.intersection i j).natAbs < ℓ := by
    have haltCast : ((T.intersection i j).natAbs : ℤ) < (ℓ : ℤ) := by
      rw [Int.natAbs_of_nonneg (le_of_lt ha)]
      exact haltZ
    exact_mod_cast haltCast
  apply hprime.coprime_iff_not_dvd.mpr
  intro hdvd
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr (ne_of_gt ha)) hdvd
  omega

/-- The diagonal bound supplies the exact coprimality hypotheses needed for the numerical
Picard prime-torsion bound. -/
theorem primeTorsionDimension_le_topologicalGenus_of_diagonalProduct_bound
    (T : NumericalType) (hcard : 1 < Nat.card T.Component)
    (ℓ : ℕ) [Fact ℓ.Prime] (hbound : ∀ i, T.diagonalProduct i < (ℓ : ℤ)) :
    T.primeTorsionDimension ℓ ≤ T.topologicalGenus := by
  apply T.primeTorsionDimension_le_topologicalGenus_of_coprime ℓ
  · exact T.multiplicity_coprime_of_diagonalProduct_lt_prime hcard ℓ Fact.out hbound
  · intro i j hij
    exact T.intersection_coprime_of_diagonalProduct_lt_prime ℓ Fact.out hbound hij

/-- For a minimal type, the diagonal-bound torsion estimate is at most arithmetic genus. -/
theorem primeTorsionDimension_le_arithmeticGenus_of_diagonalProduct_bound
    (T : NumericalType) (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component)
    (ℓ : ℕ) [Fact ℓ.Prime] (hbound : ∀ i, T.diagonalProduct i < (ℓ : ℤ)) :
    (T.primeTorsionDimension ℓ : ℤ) ≤ T.arithmeticGenus := by
  have htop := T.primeTorsionDimension_le_topologicalGenus_of_diagonalProduct_bound
    hcard ℓ hbound
  have hgenus := T.topologicalGenus_le_arithmeticGenus hmin hcard
  have htopZ : (T.primeTorsionDimension ℓ : ℤ) ≤ (T.topologicalGenus : ℤ) := by
    exact_mod_cast htop
  exact htopZ.trans hgenus

/-- The downstream conclusion of the global `768g` estimate: a larger prime gives the
topological-genus bound on numerical Picard torsion. -/
theorem primeTorsionDimension_le_topologicalGenus_of_bound_768
    (T : NumericalType) (hcard : 1 < Nat.card T.Component)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hglobal : ∀ i, T.diagonalProduct i ≤ 768 * T.arithmeticGenus)
    (hlarge : 768 * T.arithmeticGenus < (ℓ : ℤ)) :
    T.primeTorsionDimension ℓ ≤ T.topologicalGenus := by
  apply T.primeTorsionDimension_le_topologicalGenus_of_diagonalProduct_bound hcard ℓ
  intro i
  exact (hglobal i).trans_lt hlarge

/-- For minimal types, the `768g` estimate and a larger prime bound numerical Picard
torsion by arithmetic genus. -/
theorem primeTorsionDimension_le_arithmeticGenus_of_bound_768
    (T : NumericalType) (hmin : T.IsMinimal) (hcard : 1 < Nat.card T.Component)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hglobal : ∀ i, T.diagonalProduct i ≤ 768 * T.arithmeticGenus)
    (hlarge : 768 * T.arithmeticGenus < (ℓ : ℤ)) :
    (T.primeTorsionDimension ℓ : ℤ) ≤ T.arithmeticGenus := by
  apply T.primeTorsionDimension_le_arithmeticGenus_of_diagonalProduct_bound hmin hcard ℓ
  intro i
  exact (hglobal i).trans_lt hlarge

/-- For a minimal numerical type of genus at least two, every prime larger than
`768g` gives the topological-genus bound on numerical Picard torsion. -/
theorem primeTorsionDimension_le_topologicalGenus_of_large_prime
    (T : NumericalType) (hmin : T.IsMinimal)
    (hgenus : 2 ≤ T.arithmeticGenus)
    (ℓ : ℕ) [Fact ℓ.Prime] (hlarge : 768 * T.arithmeticGenus < (ℓ : ℤ)) :
    T.primeTorsionDimension ℓ ≤ T.topologicalGenus := by
  by_cases hone : Nat.card T.Component = 1
  · rw [T.primeTorsionDimension_eq_zero_of_card_eq_one hone ℓ]
    exact Nat.zero_le _
  · have hcard : 1 < Nat.card T.Component := by
      have hpositive : 0 < Nat.card T.Component := Nat.card_pos
      omega
    apply T.primeTorsionDimension_le_topologicalGenus_of_bound_768 hcard ℓ
    · exact T.diagonalProduct_le_768_genus hmin hgenus
    · exact hlarge

/-- For a minimal numerical type of genus at least two, every prime larger than
`768g` bounds numerical Picard torsion by arithmetic genus. -/
theorem primeTorsionDimension_le_arithmeticGenus_of_large_prime
    (T : NumericalType) (hmin : T.IsMinimal)
    (hgenus : 2 ≤ T.arithmeticGenus)
    (ℓ : ℕ) [Fact ℓ.Prime] (hlarge : 768 * T.arithmeticGenus < (ℓ : ℤ)) :
    (T.primeTorsionDimension ℓ : ℤ) ≤ T.arithmeticGenus := by
  by_cases hone : Nat.card T.Component = 1
  · rw [T.primeTorsionDimension_eq_zero_of_card_eq_one hone ℓ]
    exact_mod_cast (show 0 ≤ T.arithmeticGenus from by omega)
  · have hcard : 1 < Nat.card T.Component := by
      have hpositive : 0 < Nat.card T.Component := Nat.card_pos
      omega
    apply T.primeTorsionDimension_le_arithmeticGenus_of_bound_768 hmin hcard ℓ
    · exact T.diagonalProduct_le_768_genus hmin hgenus
    · exact hlarge

/-- The roadmap's weighted test case. -/
abbrev weightedExample : NumericalType.{0} where
  Component := Fin 2
  multiplicity := fun _ ↦ 1
  weight := fun _ ↦ 2
  intersection := !![-2, 2; 2, -2]
  intersection_symm := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  offDiagonal_nonnegative := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at *
  connected := by
    intro i j
    by_cases h : i = j
    · subst j
      exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.single
      exact ⟨h, by fin_cases i <;> fin_cases j <;> norm_num at *⟩
  fiber_relation := by intro i; fin_cases i <;> norm_num [Fin.sum_univ_two]
  weight_dvd := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  genus := fun _ ↦ 1

theorem weightedExample_arithmeticGenus : weightedExample.arithmeticGenus = 3 := by decide

/-- The two invariants of a raw divisor in the weighted example: total degree and the parity
of its first coefficient. -/
def weightedExampleRawInvariant : weightedExample.Divisor →+ ℤ × ZMod 2 where
  toFun D := (D 0 + D 1, (D 0 : ZMod 2))
  map_zero' := by ext <;> simp
  map_add' D E := by ext <;> simp [add_assoc, add_left_comm, add_comm]

theorem weightedExampleRawInvariant_surjective :
    Function.Surjective weightedExampleRawInvariant := by
  rintro ⟨z, a⟩
  refine ⟨![(ZMod.cast a : ℤ), z - ZMod.cast a], ?_⟩
  ext <;> simp [weightedExampleRawInvariant]

/-- The raw row subgroup in the weighted example is precisely the kernel of total degree
together with parity of the first coefficient. -/
theorem weightedExample_rawPrincipalDivisors_eq_ker :
    weightedExample.rawPrincipalDivisors = weightedExampleRawInvariant.ker := by
  apply le_antisymm
  · rw [rawPrincipalDivisors, AddSubgroup.closure_le]
    rintro D ⟨i, rfl⟩
    change weightedExampleRawInvariant (weightedExample.intersection i) = 0
    fin_cases i <;> ext <;> norm_num [weightedExampleRawInvariant, weightedExample] <;> decide
  · intro D hD
    rw [AddMonoidHom.mem_ker] at hD
    have hsum := congrArg Prod.fst hD
    have hparity := congrArg Prod.snd hD
    change D 0 + D 1 = 0 at hsum
    change (D 0 : ZMod 2) = 0 at hparity
    rw [ZMod.intCast_eq_zero_iff_even] at hparity
    obtain ⟨k, hk⟩ := hparity
    have hrepr : D = k • weightedExample.intersection 1 := by
      funext j
      fin_cases j
      · simp [weightedExample]
        omega
      · simp [weightedExample] at hsum ⊢
        omega
    rw [hrepr]
    exact AddSubgroup.zsmul_mem _
      (AddSubgroup.subset_closure (Set.mem_range_self (1 : Fin 2))) _

/-- The raw cokernel in the roadmap's weighted example has the spurious `ZMod 2` summand. -/
noncomputable def weightedExampleRawCokerEquiv :
    weightedExample.RawCoker ≃+ ℤ × ZMod 2 :=
  AddEquiv.trans (QuotientAddGroup.quotientAddEquivOfEq
      weightedExample_rawPrincipalDivisors_eq_ker)
    (QuotientAddGroup.quotientKerEquivOfSurjective weightedExampleRawInvariant
      weightedExampleRawInvariant_surjective)

@[simp] theorem weightedExampleRawCokerEquiv_mk (D : weightedExample.Divisor) :
    weightedExampleRawCokerEquiv
      (QuotientAddGroup.mk D : weightedExample.RawCoker) =
        (D 0 + D 1, (D 0 : ZMod 2)) := by
  rw [weightedExampleRawCokerEquiv, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  rfl

theorem weightedExample_principalDivisor_zero :
    weightedExample.principalDivisor 0 = ![-1, 1] := by
  ext j
  fin_cases j <;> norm_num [principalDivisor, weightedExample]

theorem weightedExample_principalDivisor_one :
    weightedExample.principalDivisor 1 = ![1, -1] := by
  ext j
  fin_cases j <;> norm_num [principalDivisor, weightedExample]

/-- Sum of the two component coefficients.  Its kernel is exactly the weighted relation
subgroup in the example. -/
def weightedExampleSum : weightedExample.Divisor →+ ℤ where
  toFun D := D 0 + D 1
  map_zero' := by simp
  map_add' _ _ := by simp [add_assoc, add_left_comm]

theorem weightedExample_principalDivisors_eq_ker :
    weightedExample.principalDivisors = weightedExampleSum.ker := by
  apply le_antisymm
  · rw [principalDivisors, AddSubgroup.closure_le]
    rintro D ⟨i, rfl⟩
    change weightedExampleSum (weightedExample.principalDivisor i) = 0
    fin_cases i
    · norm_num [weightedExampleSum, principalDivisor, weightedExample]
    · norm_num [weightedExampleSum, principalDivisor, weightedExample]
  · intro D hD
    rw [AddMonoidHom.mem_ker] at hD
    have hrepr : D = (-D 0) • weightedExample.principalDivisor 0 := by
      funext j
      fin_cases j
      · norm_num [weightedExampleSum, principalDivisor, weightedExample] at hD ⊢
      · norm_num [weightedExampleSum, principalDivisor, weightedExample] at hD ⊢
        omega
    rw [hrepr]
    exact AddSubgroup.zsmul_mem _
      (AddSubgroup.subset_closure (Set.mem_range_self (0 : Fin 2))) _

theorem weightedExampleSum_surjective : Function.Surjective weightedExampleSum := by
  intro z
  refine ⟨![z, 0], ?_⟩
  simp [weightedExampleSum]

/-- The weighted Picard group in the roadmap's example is infinite cyclic. -/
noncomputable def weightedExamplePicEquivInt : weightedExample.Pic ≃+ ℤ :=
  AddEquiv.trans (QuotientAddGroup.quotientAddEquivOfEq
      weightedExample_principalDivisors_eq_ker)
    (QuotientAddGroup.quotientKerEquivOfSurjective weightedExampleSum
      weightedExampleSum_surjective)

@[simp]
theorem weightedExamplePicEquivInt_mk (D : weightedExample.Divisor) :
    weightedExamplePicEquivInt
      (QuotientAddGroup.mk D : weightedExample.Pic) = D 0 + D 1 := by
  rw [weightedExamplePicEquivInt, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  rfl

/-- In particular, the weighted Picard group has no spurious two-torsion. -/
theorem weightedExample_torsionBy_two_eq_bot : weightedExample.torsion 2 = ⊥ := by
  ext x
  constructor
  · intro hx
    change 2 • x = 0 at hx
    rw [AddSubgroup.mem_bot, ← weightedExamplePicEquivInt.map_eq_zero_iff]
    have h := congrArg weightedExamplePicEquivInt hx
    simpa using h
  · rintro rfl
    change 0 ∈ AddSubgroup.torsionBy weightedExample.Pic 2
    simp

/-- A mixed-weight test proving division uses the destination weight. -/
abbrev mixedWeightExample : NumericalType.{0} :=
  { weightedExample with
    weight := ![1, 2]
    weight_dvd := by
      intro i j
      fin_cases i
      · exact one_dvd _
      · simpa [weightedExample] using weightedExample.weight_dvd (1 : Fin 2) j }

theorem mixedWeightExample_principalDivisor_zero :
    mixedWeightExample.principalDivisor 0 = ![-2, 1] := by
  ext j
  fin_cases j <;> norm_num [principalDivisor, mixedWeightExample, weightedExample]

/-- An odd-diagonal test for the half-diagonal sum. -/
abbrev oddDiagonalExample : NumericalType.{0} where
  Component := Fin 2
  multiplicity := fun _ ↦ 1
  weight := fun _ ↦ 1
  intersection := !![-1, 1; 1, -1]
  intersection_symm := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  offDiagonal_nonnegative := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at *
  connected := by
    intro i j
    by_cases h : i = j
    · subst j
      exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.single
      exact ⟨h, by fin_cases i <;> fin_cases j <;> norm_num at *⟩
  fiber_relation := by intro i; fin_cases i <;> norm_num [Fin.sum_univ_two]
  weight_dvd := by intro i j; exact one_dvd _
  genus := fun _ ↦ 1

theorem oddDiagonalExample_arithmeticGenus : oddDiagonalExample.arithmeticGenus = 2 := by decide

theorem weightedExample_signedGenus :
    ({ weightedExample with genus := fun _ ↦ 0 } : NumericalType).arithmeticGenus = -1 := by
  decide

end NumericalType

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
