/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Curves.Prestable
import GromovWitten.AlgebraicGeometry.Curves.DualGraph
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNodeBaseChange

/-!
# The geometric dual graph of a nodal curve over a field

For a nodal curve `X` over a field `K` (a geometric fibre of a prestable family), this file
constructs a dual graph from the geometry of `X` rather than supplying it as data:

* the vertices are the irreducible components of `X`, finitely many since `X` is Noetherian;
* the node set `nodeSet f` consists of the points of `X` admitting no smooth étale chart; it is
  closed, discrete, and hence finite, and it lies in the complement of Mathlib's smooth locus;
* the edges are the pairs of distinct components meeting at a point together with the nodes
  lying on a single component (the loops);
* the connectivity of the graph is derived from the connectedness of `X`.

The finiteness of the set of points lying on two distinct components uses that `X` has
topological Krull dimension at most one: a non-closed point of such an intersection would
produce a chain of three irreducible closed subsets.

The vertex genera (the geometric genera of the normalized components) are not computed
here and remain an explicit parameter of the construction.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Topology

open scoped Sym2

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

open StableReduction

/-! ### Topological preliminaries -/

section Topology

variable {T : Type*} [TopologicalSpace T]

/-- In a Noetherian quasi-sober space, a closed set all of whose points are closed is
finite. -/
theorem finite_of_isClosed_of_forall_isClosed_singleton [NoetherianSpace T] [QuasiSober T]
    {s : Set T} (hs : IsClosed s) (h : ∀ x ∈ s, IsClosed ({x} : Set T)) : s.Finite := by
  obtain ⟨S, hSfin, hScl, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  refine Set.Finite.sUnion hSfin fun t ht ↦ ?_
  have hgen := (hSirr t ht).isGenericPoint_genericPoint (hScl t ht)
  set z := (hSirr t ht).genericPoint with hzdef
  have hz : z ∈ t := hgen.mem
  have hcl : IsClosed ({z} : Set T) := h _ (Set.subset_sUnion_of_mem ht hz)
  have ht' : t = {z} :=
    calc t = closure {z} := hgen.def.symm
      _ = {z} := hcl.closure_eq
  exact (Set.finite_singleton z).subset ht'.le

/-- In a space of topological Krull dimension at most one, a point lying on two distinct
irreducible components is closed. -/
theorem isClosed_singleton_of_mem_of_mem [T0Space T] (hdim : topologicalKrullDim T ≤ 1)
    {C D : Set T} (hC : C ∈ irreducibleComponents T) (hD : D ∈ irreducibleComponents T)
    (hCD : C ≠ D) {x : T} (hxC : x ∈ C) (hxD : x ∈ D) : IsClosed ({x} : Set T) := by
  by_contra hx
  have hne : closure ({x} : Set T) ≠ {x} := fun h ↦ hx (h ▸ isClosed_closure)
  obtain ⟨c, hc, hcx⟩ : ∃ c ∈ closure ({x} : Set T), c ≠ x := by
    by_contra hcon
    exact hne (Set.Subset.antisymm
      (fun c hc ↦ by_contra fun h ↦ hcon ⟨c, hc, h⟩) subset_closure)
  let Z₀ : IrreducibleCloseds T := ⟨closure {c}, isIrreducible_singleton.closure, isClosed_closure⟩
  let Z₁ : IrreducibleCloseds T := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let Z₂ : IrreducibleCloseds T := ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩
  have h01 : Z₀ < Z₁ := by
    rw [← SetLike.coe_ssubset_coe]
    refine ⟨closure_minimal (Set.singleton_subset_iff.mpr hc) isClosed_closure, fun hsub ↦ ?_⟩
    have hxc : x ∈ closure ({c} : Set T) := hsub (subset_closure (Set.mem_singleton x))
    exact hcx ((specializes_iff_mem_closure.mpr hxc).antisymm
      (specializes_iff_mem_closure.mpr hc)).eq
  have h12 : Z₁ < Z₂ := by
    rw [← SetLike.coe_ssubset_coe]
    refine ⟨closure_minimal (Set.singleton_subset_iff.mpr hxC)
      (isClosed_of_mem_irreducibleComponents C hC), fun hsub ↦ ?_⟩
    have hCD' : C ⊆ D := hsub.trans (closure_minimal (Set.singleton_subset_iff.mpr hxD)
      (isClosed_of_mem_irreducibleComponents D hD))
    exact hCD (hC.eq_of_le hD.1 hCD')
  let p : LTSeries (IrreducibleCloseds T) :=
    { length := 2
      toFun := ![Z₀, Z₁, Z₂]
      step := fun i ↦ by
        fin_cases i
        · exact h01
        · exact h12 }
  have hlen : ((p.length : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim T :=
    Order.LTSeries.length_le_krullDim p
  have h2 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ 1 := hlen.trans hdim
  have h2' : (2 : ℕ∞) ≤ 1 := by exact_mod_cast h2
  exact absurd h2' (by decide)

end Topology

/-! ### Irreducible components -/

variable (X : Scheme.{u})

/-- The irreducible components of a scheme, as a type. -/
abbrev Component : Type u := ↥(irreducibleComponents X)

variable {X}

/-- The irreducible component through a point. -/
def componentOf (x : X) : Component X :=
  ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩

theorem mem_componentOf (x : X) : x ∈ (componentOf x : Set X) := mem_irreducibleComponent

theorem componentOf_eq_of_mem {x : X} {C : Component X}
    (h : ∀ C D : Component X, x ∈ (C : Set X) → x ∈ (D : Set X) → C = D)
    (hx : x ∈ (C : Set X)) : componentOf x = C :=
  h _ _ (mem_componentOf x) hx

/-- A Noetherian scheme has finitely many irreducible components. -/
theorem finite_component [IsNoetherian X] : Finite (Component X) :=
  finite_irreducibleComponents_of_isNoetherian.to_subtype

/-- A nonempty scheme has an irreducible component. -/
theorem nonempty_component [Nonempty X] : Nonempty (Component X) :=
  ⟨componentOf (Classical.arbitrary X)⟩

/-- The set of points lying on two distinct irreducible components. -/
def multiSet : Set X :=
  {x | ∃ C D : Component X, C ≠ D ∧ x ∈ (C : Set X) ∧ x ∈ (D : Set X)}

/-- Two distinct irreducible components of a one-dimensional Noetherian scheme meet in
finitely many points. -/
theorem finite_inter_of_ne [IsNoetherian X] (hdim : topologicalKrullDim X ≤ 1)
    {C D : Component X} (hCD : C ≠ D) : ((C : Set X) ∩ D).Finite :=
  finite_of_isClosed_of_forall_isClosed_singleton
    ((isClosed_of_mem_irreducibleComponents _ C.2).inter
      (isClosed_of_mem_irreducibleComponents _ D.2))
    fun _ hx ↦ isClosed_singleton_of_mem_of_mem hdim C.2 D.2
      (fun h ↦ hCD (Subtype.ext h)) hx.1 hx.2

/-- A one-dimensional Noetherian scheme has finitely many points lying on two distinct
irreducible components. -/
theorem multiSet_finite [IsNoetherian X] (hdim : topologicalKrullDim X ≤ 1) :
    (multiSet (X := X)).Finite := by
  have := finite_component (X := X)
  refine (Set.finite_iUnion (ι := {p : Component X × Component X // p.1 ≠ p.2})
    (f := fun p ↦ (p.1.1 : Set X) ∩ p.1.2) fun p ↦ finite_inter_of_ne hdim p.2).subset ?_
  rintro x ⟨C, D, hCD, hxC, hxD⟩
  exact Set.mem_iUnion.mpr ⟨⟨(C, D), hCD⟩, hxC, hxD⟩

/-! ### The node set -/

variable {K : Type u} [Field K] (f : X ⟶ Spec (.of K))

/-- The points of a curve over a field admitting no smooth étale chart. -/
def nodeSet : Set X := {x | ¬ Nonempty (SmoothChartAt f x)}

/-- The points with a smooth chart form an open set. -/
theorem isOpen_compl_nodeSet : IsOpen (nodeSet f)ᶜ := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  have hx' : Nonempty (SmoothChartAt f x) := not_not.mp hx
  obtain ⟨c⟩ := hx'
  have : Etale c.toCurve := c.etale_toCurve
  refine ⟨Set.range c.toCurve, ?_, c.toCurve.isOpenMap.isOpen_range, ⟨c.point, c.mapsToPoint⟩⟩
  rintro _ ⟨q, rfl⟩
  exact fun h ↦ h ⟨{ c with point := q, mapsToPoint := rfl }⟩

/-- The node set is closed. -/
theorem isClosed_nodeSet : IsClosed (nodeSet f) := by
  simpa using (isOpen_compl_nodeSet f).isClosed_compl

/-- Every node lies outside the smooth locus. -/
theorem nodeSet_subset_compl_smoothLocus [LocallyOfFinitePresentation f] :
    nodeSet f ⊆ (f.smoothLocus : Set X)ᶜ := by
  intro x hx hxs
  apply hx
  refine ⟨{
    source := f.smoothLocus.toScheme,
    point := ⟨x, hxs⟩,
    toCurve := f.smoothLocus.ι,
    etale_toCurve := inferInstance,
    mapsToPoint := rfl,
    smooth_toBase := ?_ }⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
    Scheme.Opens.ι_preimage_self]

/-! ### The origin of the standard node -/

/-- The closed origin `(x, y)` of the standard node `xy = 0` over a field. -/
def standardNodeOrigin (K : Type u) [Field K] : Spec (.of (LocalNode.Ring K 0 1)) :=
  (⟨RingHom.ker (LocalNode.nodeOrigin K 1 one_ne_zero).toRingHom,
    (RingHom.ker_isMaximal_of_surjective _
      (LocalNode.nodeOrigin_surjective K 1 one_ne_zero)).isPrime⟩ :
    PrimeSpectrum (LocalNode.Ring K 0 1))

/-- A prime of the standard node containing both coordinates is the origin. -/
theorem eq_standardNodeOrigin_of_mem (p : Spec (.of (LocalNode.Ring K 0 1)))
    (hx : LocalNode.x K 0 1 ∈ p.asIdeal) (hy : LocalNode.y K 0 1 ∈ p.asIdeal) :
    p = standardNodeOrigin K := by
  have hmax : (RingHom.ker (LocalNode.nodeOrigin K 1 one_ne_zero).toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (LocalNode.nodeOrigin_surjective K 1 one_ne_zero)
  have hle : RingHom.ker (LocalNode.nodeOrigin K 1 one_ne_zero).toRingHom ≤ p.asIdeal := by
    rw [LocalNode.nodeOrigin_ker, Ideal.span_le]
    rintro z (rfl | rfl)
    · exact hx
    · exact hy
  exact PrimeSpectrum.ext (hmax.eq_of_le p.isPrime.ne_top hle).symm

/-- The `x`-away chart of the standard node is smooth over the field. -/
theorem smooth_xAwayToBaseSpec : Smooth (LocalNode.xAwayToBaseSpec K 0 1) := by
  rw [LocalNode.xAwayToBaseSpec, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr (LocalNode.xAway_smooth K 0 1)

/-- The `y`-away chart of the standard node is smooth over the field. -/
theorem smooth_yAwayToBaseSpec : Smooth (LocalNode.yAwayToBaseSpec K 0 1) := by
  rw [LocalNode.yAwayToBaseSpec, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr (LocalNode.yAway_smooth K 0 1)

/-- A point of a node chart lying over the locus where `x` is invertible has a smooth
chart. -/
theorem smoothChart_of_xAway {x : X} (c : NodeChartAt f x) (q : c.source)
    (hq : LocalNode.x K 0 1 ∉ (c.toNode q).asIdeal) :
    Nonempty (SmoothChartAt f (c.toCurve q)) := by
  have hmem : c.toNode q ∈ Set.range (LocalNode.xAwaySpec K 0 1) := by
    rw [LocalNode.range_xAwaySpec]
    exact hq
  obtain ⟨r, hr⟩ := hmem
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := c.toNode)
    (g := LocalNode.xAwaySpec K 0 1) q r hr.symm
  have hEn : Etale c.toNode := c.etale_toNode
  have hEc : Etale c.toCurve := c.etale_toCurve
  have hsm := smooth_xAwayToBaseSpec (K := K)
  refine ⟨{
    source := pullback c.toNode (LocalNode.xAwaySpec K 0 1),
    point := z,
    toCurve := pullback.fst c.toNode (LocalNode.xAwaySpec K 0 1) ≫ c.toCurve,
    etale_toCurve := inferInstance,
    mapsToPoint := by rw [Scheme.Hom.comp_apply, hz1],
    smooth_toBase := ?_ }⟩
  rw [Category.assoc, c.overBase, ← Category.assoc, pullback.condition, Category.assoc,
    LocalNode.xAwaySpec_toBaseSpec]
  infer_instance

/-- A point of a node chart lying over the locus where `y` is invertible has a smooth
chart. -/
theorem smoothChart_of_yAway {x : X} (c : NodeChartAt f x) (q : c.source)
    (hq : LocalNode.y K 0 1 ∉ (c.toNode q).asIdeal) :
    Nonempty (SmoothChartAt f (c.toCurve q)) := by
  have hmem : c.toNode q ∈ Set.range (LocalNode.yAwaySpec K 0 1) := by
    rw [LocalNode.range_yAwaySpec]
    exact hq
  obtain ⟨r, hr⟩ := hmem
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := c.toNode)
    (g := LocalNode.yAwaySpec K 0 1) q r hr.symm
  have hEn : Etale c.toNode := c.etale_toNode
  have hEc : Etale c.toCurve := c.etale_toCurve
  have hsm := smooth_yAwayToBaseSpec (K := K)
  refine ⟨{
    source := pullback c.toNode (LocalNode.yAwaySpec K 0 1),
    point := z,
    toCurve := pullback.fst c.toNode (LocalNode.yAwaySpec K 0 1) ≫ c.toCurve,
    etale_toCurve := inferInstance,
    mapsToPoint := by rw [Scheme.Hom.comp_apply, hz1],
    smooth_toBase := ?_ }⟩
  rw [Category.assoc, c.overBase, ← Category.assoc, pullback.condition, Category.assoc,
    LocalNode.yAwaySpec_toBaseSpec]
  infer_instance

/-- A point of a node chart not lying over the origin has a smooth chart. -/
theorem smoothChart_of_nodeChart {x : X} (c : NodeChartAt f x) (q : c.source)
    (hq : c.toNode q ≠ standardNodeOrigin K) : Nonempty (SmoothChartAt f (c.toCurve q)) := by
  by_cases hx : LocalNode.x K 0 1 ∈ (c.toNode q).asIdeal
  · by_cases hy : LocalNode.y K 0 1 ∈ (c.toNode q).asIdeal
    · exact absurd (eq_standardNodeOrigin_of_mem _ hx hy) hq
    · exact smoothChart_of_yAway f c q hy
  · exact smoothChart_of_xAway f c q hx

/-- On a nodal curve, the chart point of a node chart at a node lies over the origin. -/
theorem nodeChart_toNode_point {x : X} (hx : x ∈ nodeSet f) (c : NodeChartAt f x) :
    c.toNode c.point = standardNodeOrigin K := by
  by_contra hne
  have h := smoothChart_of_nodeChart f c c.point hne
  rw [c.mapsToPoint] at h
  exact hx h

/-- The node set of a nodal curve is discrete. -/
theorem nodeSet_isDiscrete (hf : IsNodalCurveOverField f) : _root_.IsDiscrete (nodeSet f) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  rcases hf x with hsm | hnd
  · exact absurd hsm hx
  obtain ⟨c⟩ := hnd
  have hEc : Etale c.toCurve := c.etale_toCurve
  have hEn : Etale c.toNode := c.etale_toNode
  have hLQ := locallyQuasiFinite_of_etale c.toNode
  have hdisc := c.toNode.isDiscrete_preimage_singleton (c.toNode c.point)
  rw [isDiscrete_iff_forall_mem_exists_isOpen] at hdisc
  obtain ⟨W, hWopen, hW⟩ := hdisc c.point rfl
  have hpt : c.point ∈ W := by
    have : c.point ∈ W ∩ c.toNode ⁻¹' {c.toNode c.point} := by
      rw [hW]
      exact Set.mem_singleton _
    exact this.1
  refine ⟨c.toCurve '' W, c.toCurve.isOpenMap W hWopen, ?_⟩
  ext z
  constructor
  · rintro ⟨⟨q, hqW, rfl⟩, hz⟩
    have hq : c.toNode q = c.toNode c.point := by
      rw [nodeChart_toNode_point f hx c]
      by_contra hne
      exact hz (smoothChart_of_nodeChart f c q hne)
    have hmem : q ∈ W ∩ c.toNode ⁻¹' {c.toNode c.point} := ⟨hqW, hq⟩
    rw [hW] at hmem
    rw [hmem, c.mapsToPoint]
    rfl
  · rintro rfl
    exact ⟨⟨c.point, hpt, c.mapsToPoint⟩, hx⟩

/-- The node set of a nodal curve over a field is finite. -/
theorem nodeSet_finite [CompactSpace X] (hf : IsNodalCurveOverField f) : (nodeSet f).Finite := by
  have hdisc := nodeSet_isDiscrete f hf
  rw [isDiscrete_iff_discreteTopology] at hdisc
  have : CompactSpace (nodeSet f) := isCompact_iff_compactSpace.mp (isClosed_nodeSet f).isCompact
  have : Finite (nodeSet f) := finite_of_compact_of_discrete
  exact Set.toFinite _

/-! ### Curves over a field arising as geometric fibres -/

/-- A curve at worst nodal over a field is a nodal curve over that field. -/
theorem isNodalCurveOverField_of_atWorstNodal [AtWorstNodal f] : IsNodalCurveOverField f := by
  have hsq : CommSq (𝟙 X) f f (𝟙 (Spec (.of K))) := ⟨by simp⟩
  exact AtWorstNodal.geometricFibers K (𝟙 _) X (𝟙 X) f (IsPullback.of_horiz_isIso hsq)

/-- A geometrically connected curve over a field is connected. -/
theorem connectedSpace_of_geometricallyConnected [GeometricallyConnected f] :
    ConnectedSpace X := by
  have hsq : CommSq (𝟙 X) f f (𝟙 (Spec (.of K))) := ⟨by simp⟩
  exact GeometricallyConnected.geometrically_connectedSpace (𝟙 _) (𝟙 X) f
    (IsPullback.of_horiz_isIso hsq)

/-- A quasi-compact locally finite-type curve over a field is Noetherian. -/
theorem isNoetherian_of_quasiCompact [LocallyOfFiniteType f] [QuasiCompact f] :
    IsNoetherian X := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

/-- A curve of relative dimension at most one over a field has topological Krull dimension
at most one. -/
theorem topologicalKrullDim_le_one (hdim : RelativeDimensionLE 1 f) :
    topologicalKrullDim X ≤ 1 := by
  obtain ⟨_, h⟩ := hdim
  let s : Spec (.of K) := default
  have huniv : f ⁻¹' {s} = Set.univ := Set.eq_univ_of_forall fun x ↦ Subsingleton.elim _ _
  have e1 : topologicalKrullDim (f.fiber s) = topologicalKrullDim (f ⁻¹' {s}) :=
    IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo s).isHomeomorph
  have e2 : topologicalKrullDim (Set.univ : Set X) = topologicalKrullDim X :=
    IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph
  rw [huniv] at e1
  rw [← e2, ← e1]
  exact h s

/-! ### Edges and the graph -/

/-- The nodes lying on a single irreducible component: the loops of the dual graph. -/
def loopEdges : Set X :=
  {x | x ∈ nodeSet f ∧ ∀ C D : Component X, x ∈ (C : Set X) → x ∈ (D : Set X) → C = D}

/-- The pairs of distinct irreducible components together with a common point. -/
def multiEdges : Set (X × Sym2 (Component X)) :=
  {p | ¬ p.2.IsDiag ∧ ∀ C ∈ p.2, p.1 ∈ (C : Set X)}

/-- The loops of a nodal curve over a field are finite. -/
theorem loopEdges_finite [CompactSpace X] (hf : IsNodalCurveOverField f) :
    (loopEdges f).Finite :=
  (nodeSet_finite f hf).subset fun _ hx ↦ hx.1

/-- The multi-edges of a one-dimensional Noetherian scheme are finite. -/
theorem multiEdges_finite [IsNoetherian X] (hdim : topologicalKrullDim X ≤ 1) :
    (multiEdges (X := X)).Finite := by
  have := finite_component (X := X)
  refine ((multiSet_finite hdim).prod (Set.finite_univ (α := Sym2 (Component X)))).subset ?_
  rintro ⟨x, e⟩ ⟨hdiag, hmem⟩
  refine ⟨?_, Set.mem_univ _⟩
  induction e using Sym2.ind with
  | _ C D =>
    exact ⟨C, D, fun h ↦ hdiag (Sym2.mk_isDiag_iff.mpr h),
      hmem C (Sym2.mem_iff.mpr (Or.inl rfl)), hmem D (Sym2.mem_iff.mpr (Or.inr rfl))⟩

/-- The edges of the geometric dual graph: loops and multi-edges. -/
abbrev Edge : Type u := ↥(loopEdges f) ⊕ ↥(multiEdges (X := X))

/-- The endpoints of an edge: a loop is attached to the component through its node, and a
multi-edge to the two components it records. -/
def endpoint : Edge f → Fin 2 → Component X
  | Sum.inl e, _ => componentOf e.1
  | Sum.inr e, 0 => e.1.2.out.1
  | Sum.inr e, 1 => e.1.2.out.2

/-- Adjacency in the geometric dual graph. -/
abbrev Adj (v w : Component X) : Prop :=
  ∃ e : Edge f, (endpoint f e 0 = v ∧ endpoint f e 1 = w) ∨
    (endpoint f e 0 = w ∧ endpoint f e 1 = v)

/-- Two distinct components meeting at a point are adjacent. -/
theorem adj_of_mem_of_mem {C D : Component X} (hCD : C ≠ D) {x : X}
    (hxC : x ∈ (C : Set X)) (hxD : x ∈ (D : Set X)) : Adj f C D := by
  refine ⟨Sum.inr ⟨(x, s(C, D)), fun h ↦ hCD (Sym2.mk_isDiag_iff.mp h), fun E hE ↦ ?_⟩, ?_⟩
  · rcases Sym2.mem_iff.mp hE with rfl | rfl
    · exact hxC
    · exact hxD
  · have h' : s((Quot.out s(C, D)).1, (Quot.out s(C, D)).2) = s(C, D) := Quot.out_eq _
    change ((Quot.out s(C, D)).1 = C ∧ (Quot.out s(C, D)).2 = D) ∨
      ((Quot.out s(C, D)).1 = D ∧ (Quot.out s(C, D)).2 = C)
    exact Sym2.eq_iff.mp h'

/-- The geometric dual graph of a connected curve is connected. -/
theorem reflTransGen_adj [ConnectedSpace X] [IsNoetherian X] (v w : Component X) :
    Relation.ReflTransGen (Adj f) v w := by
  classical
  have := finite_component (X := X)
  let R : Set (Component X) := {C | Relation.ReflTransGen (Adj f) v C}
  let A : Set X := ⋃ C ∈ R, (C : Set X)
  let B : Set X := ⋃ C ∈ Rᶜ, (C : Set X)
  have hAcl : IsClosed A :=
    (Set.toFinite R).isClosed_biUnion fun C _ ↦ isClosed_of_mem_irreducibleComponents _ C.2
  have hBcl : IsClosed B :=
    (Set.toFinite Rᶜ).isClosed_biUnion fun C _ ↦ isClosed_of_mem_irreducibleComponents _ C.2
  have hcompl : Aᶜ = B := by
    ext x
    constructor
    · intro hxA
      have hx : x ∈ ⋃₀ irreducibleComponents X := by
        rw [sUnion_irreducibleComponents]
        exact Set.mem_univ x
      obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp hx
      have hR : (⟨C, hC⟩ : Component X) ∉ R := fun hR ↦ hxA (Set.mem_biUnion hR hxC)
      exact Set.mem_biUnion hR hxC
    · intro hxB hxA
      obtain ⟨C, hCR, hxC⟩ := Set.mem_iUnion₂.mp hxA
      obtain ⟨D, hDR, hxD⟩ := Set.mem_iUnion₂.mp hxB
      have hCD : C ≠ D := fun h ↦ hDR (h ▸ hCR)
      exact hDR (hCR.tail (adj_of_mem_of_mem f hCD hxC hxD))
  have hclopen : IsClopen A := ⟨hAcl, by rw [← isClosed_compl_iff, hcompl]; exact hBcl⟩
  obtain ⟨x₀, hx₀⟩ := v.2.1.nonempty
  have hAuniv : A = Set.univ :=
    hclopen.eq_univ ⟨x₀, Set.mem_biUnion (Relation.ReflTransGen.refl) hx₀⟩
  obtain ⟨x, hx⟩ := w.2.1.nonempty
  have hxA : x ∈ A := hAuniv ▸ Set.mem_univ x
  obtain ⟨C, hCR, hxC⟩ := Set.mem_iUnion₂.mp hxA
  by_cases hCw : C = w
  · exact hCw ▸ hCR
  · exact hCR.tail (adj_of_mem_of_mem f hCw hxC hx)

/-- The geometric dual graph of a nodal curve over a field: vertices are the irreducible
components, edges are the pairs of distinct components meeting at a point together with the
nodes lying on a single component, and the vertex genera are supplied as a parameter. -/
def geometricDualGraph [PrestableFamily f] (genus : Component X → ℕ) : DualGraph.{u} :=
  have _hN : IsNoetherian X := isNoetherian_of_quasiCompact f
  have _hC : ConnectedSpace X := connectedSpace_of_geometricallyConnected f
  have _hfin : Finite (Component X) := finite_component
  have hnod : IsNodalCurveOverField f := isNodalCurveOverField_of_atWorstNodal f
  have hdim : topologicalKrullDim X ≤ 1 :=
    topologicalKrullDim_le_one f (FamilyOfCurves.relativeDimensionLE f)
  have _hloop : Finite (loopEdges f) := (loopEdges_finite f hnod).to_subtype
  have _hmulti : Finite (multiEdges (X := X)) := (multiEdges_finite hdim).to_subtype
  { Vertex := Component X
    vertexFintype := Fintype.ofFinite _
    vertexDecidableEq := Classical.decEq _
    vertexNonempty := nonempty_component
    Edge := Edge f
    edgeFintype := Fintype.ofFinite _
    edgeDecidableEq := Classical.decEq _
    endpoint := endpoint f
    genus := genus
    connected := reflTransGen_adj f }

/-- The vertices of the geometric dual graph are the irreducible components. -/
theorem geometricDualGraph_vertex [PrestableFamily f] (genus : Component X → ℕ) :
    (geometricDualGraph f genus).Vertex = Component X := rfl

/-- The edges of the geometric dual graph are the loops and multi-edges. -/
theorem geometricDualGraph_edge [PrestableFamily f] (genus : Component X → ℕ) :
    (geometricDualGraph f genus).Edge = Edge f := rfl

/-- A loop is attached to the unique component through its node. -/
theorem endpoint_inl (e : loopEdges f) (i : Fin 2) :
    endpoint f (Sum.inl e) i = componentOf e.1 := by
  cases i using Fin.cases <;> rfl

/-- The endpoints of a multi-edge are its two recorded components. -/
theorem endpoint_inr (e : multiEdges (X := X)) :
    s(endpoint f (Sum.inr e) 0, endpoint f (Sum.inr e) 1) = e.1.2 := by
  change s((Quot.out e.1.2).1, (Quot.out e.1.2).2) = e.1.2
  exact Quot.out_eq _

/-- The point of a loop lies outside the smooth locus. -/
theorem loopEdges_subset_compl_smoothLocus [LocallyOfFinitePresentation f] :
    loopEdges f ⊆ (f.smoothLocus : Set X)ᶜ :=
  fun _ hx ↦ nodeSet_subset_compl_smoothLocus f hx.1

end

end GromovWitten.AlgebraicGeometry.Curves
