/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Curves.Prestable
import GromovWitten.AlgebraicGeometry.Curves.DualGraph
import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenus
import GromovWitten.AlgebraicGeometry.Curves.Normalization
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

The general graph constructor remains available for clients that already have a genus function.
The canonical constructor `geometricDualGraphOfNormalization` computes each vertex genus from the
first cohomology of the structure sheaf of the actual reduced normalization of that component.
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

namespace SmoothChartAt

/-- A smooth chart transports along an isomorphism of its ambient curve over the field. -/
def postcompIso {Y : Scheme.{u}} {K : Type u} [Field K]
    {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)} {x : X}
    (c : SmoothChartAt f x) (e : X ≅ Y) (he : e.hom ≫ g = f) :
    SmoothChartAt g (e.hom x) where
  source := c.source
  point := c.point
  toCurve := c.toCurve ≫ e.hom
  etale_toCurve := by
    let _ : Etale c.toCurve := c.etale_toCurve
    let _ : Etale e.hom := by infer_instance
    infer_instance
  mapsToPoint := by
    simp only [Scheme.Hom.comp_apply, c.mapsToPoint]
  smooth_toBase := by
    rw [Category.assoc, he]
    exact c.smooth_toBase

end SmoothChartAt

/-- Nonsmooth points are preserved by an isomorphism over the field. -/
theorem nodeSet_mem_of_iso {Y : Scheme.{u}} {K : Type u} [Field K]
    {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)}
    (e : X ≅ Y) (he : e.hom ≫ g = f) {x : X} (hx : x ∈ nodeSet f) :
    e.hom x ∈ nodeSet g := by
  intro h
  apply hx
  obtain ⟨c⟩ := h
  have he_inv : e.inv ≫ f = g := by
    rw [← he]
    simp
  have hc := c.postcompIso e.symm he_inv
  change SmoothChartAt f (e.inv (e.hom x)) at hc
  have hex : e.inv (e.hom x) = x := congrArg (fun k : X ⟶ X => k x) e.hom_inv_id
  rw [hex] at hc
  exact ⟨hc⟩

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

/-- Both node coordinates lie in the ideal of the origin of the standard node: the converse of
`eq_standardNodeOrigin_of_mem`. -/
theorem mem_asIdeal_standardNodeOrigin (K : Type u) [Field K] :
    LocalNode.x K 0 1 ∈ (standardNodeOrigin K).asIdeal ∧
      LocalNode.y K 0 1 ∈ (standardNodeOrigin K).asIdeal := by
  have hker : (standardNodeOrigin K).asIdeal =
      Ideal.span ({LocalNode.x K 0 1, LocalNode.y K 0 1} : Set (LocalNode.Ring K 0 1)) := by
    change RingHom.ker (LocalNode.nodeOrigin K 1 one_ne_zero).toRingHom = _
    exact LocalNode.nodeOrigin_ker K 1 one_ne_zero
  rw [hker]
  exact ⟨Ideal.subset_span (Set.mem_insert _ _),
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)⟩

/-- The chart point of a node chart is the origin of the standard node: the new `mapsToOrigin`
field of `NodeChartAt`, identified with the named point `standardNodeOrigin`. -/
theorem NodeChartAt.toNode_point_eq_standardNodeOrigin {x : X} (c : NodeChartAt f x) :
    c.toNode c.point = standardNodeOrigin K :=
  eq_standardNodeOrigin_of_mem _ c.mapsToOrigin.1 c.mapsToOrigin.2

/-- **Sanity check.** The origin of the standard node admits a node chart: the identity is
simultaneously an étale chart onto the curve and onto the node itself. -/
theorem nonempty_nodeChartAt_standardNodeOrigin (K : Type u) [Field K] :
    Nonempty (NodeChartAt (standardNodeToSpec K) (standardNodeOrigin K)) :=
  ⟨{ source := Spec (.of (LocalNode.Ring K 0 1))
     point := standardNodeOrigin K
     toCurve := 𝟙 _
     toNode := 𝟙 _
     etale_toCurve := inferInstance
     etale_toNode := inferInstance
     mapsToPoint := rfl
     overBase := rfl
     mapsToOrigin := mem_asIdeal_standardNodeOrigin K }⟩

/-- **Sanity check.** The standard node over a field is at worst nodal, with the origin's chart
a node chart and every other point's a smooth chart, via `of_overIso_standardNode` applied to the
identity isomorphism.  This does not yet show that an arbitrary `NodeChartAt` of the standard
node (with any étale legs) can only sit at the origin; that converse remains open. -/
theorem isNodalCurveOverField_standardNodeToSpec (K : Type u) [Field K] :
    IsNodalCurveOverField (standardNodeToSpec K) :=
  IsNodalCurveOverField.of_overIso_standardNode _ (Iso.refl _)

/-- A point of a node chart lying over the locus where `x` is invertible has a smooth
chart. -/
theorem smoothChart_of_xAway {x : X} (c : NodeChartAt f x) (q : c.source)
    (hq : LocalNode.x K 0 1 ∉ (c.toNode q).asIdeal) :
    Nonempty (SmoothChartAt f (c.toCurve q)) := by
  let _ : Etale c.toCurve := c.etale_toCurve
  let _ : Etale c.toNode := c.etale_toNode
  exact smoothChartAt_of_not_mem_asIdeal_x c.toCurve c.toNode c.overBase q hq

/-- A point of a node chart lying over the locus where `y` is invertible has a smooth
chart. -/
theorem smoothChart_of_yAway {x : X} (c : NodeChartAt f x) (q : c.source)
    (hq : LocalNode.y K 0 1 ∉ (c.toNode q).asIdeal) :
    Nonempty (SmoothChartAt f (c.toCurve q)) := by
  let _ : Etale c.toCurve := c.etale_toCurve
  let _ : Etale c.toNode := c.etale_toNode
  exact smoothChartAt_of_not_mem_asIdeal_y c.toCurve c.toNode c.overBase q hq

/-- A point of a node chart not lying over the origin has a smooth chart. -/
theorem smoothChart_of_nodeChart {x : X} (c : NodeChartAt f x) (q : c.source)
    (hq : c.toNode q ≠ standardNodeOrigin K) : Nonempty (SmoothChartAt f (c.toCurve q)) := by
  by_cases hx : LocalNode.x K 0 1 ∈ (c.toNode q).asIdeal
  · by_cases hy : LocalNode.y K 0 1 ∈ (c.toNode q).asIdeal
    · exact absurd (eq_standardNodeOrigin_of_mem _ hx hy) hq
    · exact smoothChart_of_yAway f c q hy
  · exact smoothChart_of_xAway f c q hx

/-- On a nodal curve, the chart point of a node chart at a node lies over the origin.  This now
holds unconditionally on any curve, by `mapsToOrigin`; the hypothesis `_hx` is kept for backward
compatibility with call sites. -/
theorem nodeChart_toNode_point {x : X} (_hx : x ∈ nodeSet f) (c : NodeChartAt f x) :
    c.toNode c.point = standardNodeOrigin K :=
  c.toNode_point_eq_standardNodeOrigin

/-- Every point of a node chart mapping to the distinguished node has the distinguished
standard-node coordinate.  This is the fibrewise form of `nodeChart_toNode_point`; it is the
local input needed before transporting the two standard axes through normalization pullback. -/
theorem nodeChart_toNode_eq_of_map_eq {x : X} (hx : x ∈ nodeSet f)
    (c : NodeChartAt f x) {q : c.source} (hq : c.toCurve q = x) :
    c.toNode q = standardNodeOrigin K := by
  by_contra hne
  have h := smoothChart_of_nodeChart f c q hne
  rw [hq] at h
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

/-! ### Normalized components -/

/- A component is represented by Mathlib's scheme-theoretic irreducible-component
subscheme.  The Noetherian instance is obtained from the prestable fibre, rather than
being supplied as part of the graph data. -/

/-- The scheme-theoretic irreducible component of a prestable geometric fibre. -/
noncomputable def componentScheme [PrestableFamily f] (C : Component X) : Scheme.{u} := by
  letI : IsNoetherian X := isNoetherian_of_quasiCompact f
  exact (X.irreducibleComponentIdeal C C.2).radical.subscheme

/-- The closed immersion of a fibre component into the fibre. -/
noncomputable def componentInclusion [PrestableFamily f] (C : Component X) :
    componentScheme f C ⟶ X := by
  letI : IsNoetherian X := isNoetherian_of_quasiCompact f
  exact (X.irreducibleComponentIdeal C C.2).radical.subschemeι

/- The reduced induced component is reduced, proved affine-locally from the radical ideal. -/
theorem componentScheme_isReduced [PrestableFamily f] (C : Component X) :
    IsReduced (componentScheme f C) := by
  let _ : IsNoetherian X := isNoetherian_of_quasiCompact f
  let I := (X.irreducibleComponentIdeal C C.2).radical
  change IsReduced I.subscheme
  let _ : ∀ i : I.subschemeCover.openCover.I₀,
      IsReduced (I.subschemeCover.openCover.X i) := by
    intro i
    let U : I.subschemeCover.I₀ := i
    have hr : _root_.IsReduced ((I.subschemeCover.X U : CommRingCat) : Type u) := by
      dsimp [Scheme.IdealSheafData.subschemeCover] at U ⊢
      let V : X.affineOpens := U
      change _root_.IsReduced ((X.presheaf.obj (Opposite.op (V : X.Opens))) ⧸ I.ideal V)
      apply (Ideal.isRadical_iff_quotient_reduced _).mp
      exact Ideal.radical_isRadical _
    let _ := hr
    change IsReduced (Spec (I.subschemeCover.X U))
    infer_instance
  exact IsReduced.of_openCover I.subscheme I.subschemeCover.openCover

/- The reduced component has the irreducible topological space of its support. -/
theorem componentScheme_isIrreducibleSpace [PrestableFamily f] (C : Component X) :
    IrreducibleSpace (componentScheme f C) := by
  let _ : IsNoetherian X := isNoetherian_of_quasiCompact f
  let I := (X.irreducibleComponentIdeal C C.2).radical
  let e₀ := I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph
  let e : I.subscheme ≃ₜ (I.support : Set X) :=
    e₀.trans (Homeomorph.setCongr I.range_subschemeι)
  apply (Homeomorph.irreducibleSpace_iff e).mpr
  apply Subtype.irreducibleSpace
  have hsupport : I.support = (C : Set X) := by
    change ((X.irreducibleComponentIdeal C C.2).radical.support : Set X) = (C : Set X)
    rw [Scheme.IdealSheafData.support_radical]
    rfl
  rw [hsupport]
  exact C.2.1

/- The reduced component is integral, with no integrality witness supplied by callers. -/
theorem componentScheme_isIntegral [PrestableFamily f] (C : Component X) :
    IsIntegral (componentScheme f C) := by
  let _ := componentScheme_isReduced f C
  let _ := componentScheme_isIrreducibleSpace f C
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The structure morphism of a fibre component over the ground field. -/
noncomputable def componentToBase [PrestableFamily f] (C : Component X) :
    componentScheme f C ⟶ Spec (.of K) :=
  componentInclusion f C ≫ f

/-! ### Canonical normalized components

The normalization is canonical once the reduced integral component has been fixed. -/

/-- The canonical normalization scheme of a component. -/
noncomputable def normalizedComponentScheme [PrestableFamily f] (C : Component X) :
    Scheme.{u} :=
  letI := componentScheme_isIntegral f C
  Normalization.scheme (componentScheme f C)

/-- The canonical normalization morphism into the fibre. -/
noncomputable def normalizedComponentToCurve [PrestableFamily f] (C : Component X) :
    normalizedComponentScheme f C ⟶ X := by
  letI := componentScheme_isIntegral f C
  exact Normalization.toCurve (componentScheme f C) ≫ componentInclusion f C

/-- The structure morphism of a normalized component over the ground field. -/
noncomputable def normalizedComponentToBase [PrestableFamily f] (C : Component X) :
    normalizedComponentScheme f C ⟶ Spec (.of K) :=
  normalizedComponentToCurve f C ≫ f

/-- The arithmetic (equivalently geometric, after the normalization comparison) genus of a
normalized component.  It is the dimension of the first cohomology of its actual structure
sheaf, so no graph genus label is supplied independently. -/
noncomputable def normalizedComponentGenus [PrestableFamily f] (C : Component X) : ℕ :=
  arithmeticGenus K (normalizedComponentToBase f C)

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

/-- The point of the fibre represented by an edge. -/
def edgePoint : Edge f → X
  | Sum.inl e => e.1
  | Sum.inr e => e.1.1

/-- Every nonsmooth point of a nodal fibre is represented by an edge.  The proof first checks
whether all components through the point coincide; otherwise the point and the two distinct
components form the separating edge. -/
theorem exists_edgePoint_eq_of_mem_nodeSet [PrestableFamily f]
    {x : X} (hx : x ∈ nodeSet f) : ∃ e : Edge f, edgePoint f e = x := by
  classical
  by_cases hsame : ∀ D : Component X, x ∈ (D : Set X) → D = componentOf x
  · exact ⟨Sum.inl ⟨x, hx, by
      intro C D hxC hxD
      exact (hsame C hxC).trans (hsame D hxD).symm⟩, rfl⟩
  · push Not at hsame
    obtain ⟨D, hxD, hCD⟩ := hsame
    let C := componentOf x
    refine ⟨Sum.inr ⟨(x, s(C, D)), ?_, ?_⟩, rfl⟩
    · intro hdiag
      exact hCD (Sym2.mk_isDiag_iff.mp hdiag).symm
    · intro E hE
      rcases Sym2.mem_iff.mp hE with rfl | rfl
      · exact mem_componentOf x
      · exact hxD

/- Every point of `nodeSet` has a node chart, by the nodal fibre axiom. -/
theorem nodeChart_nonempty_of_mem_nodeSet [PrestableFamily f]
    {x : X} (hx : x ∈ nodeSet f) : Nonempty (NodeChartAt f x) := by
  let _ : AtWorstNodal f := PrestableFamily.nodal
  rcases (isNodalCurveOverField_of_atWorstNodal f x) with hsm | hnode
  · exact False.elim (hx hsm)
  · exact hnode

@[simp] theorem edgePoint_inl (e : loopEdges f) :
    edgePoint f (Sum.inl e) = e.1 := rfl

@[simp] theorem edgePoint_inr (e : multiEdges (X := X)) :
    edgePoint f (Sum.inr e) = e.1.1 := rfl

namespace NormalizedComponents

variable [PrestableFamily f]

/-- A point on a normalized component, retaining the component it belongs to. -/
abbrev Point := Σ C : Component X, normalizedComponentScheme f C

/-- The image in the fibre of a point on a normalized component. -/
def pointToCurve (p : Point (f := f)) : X :=
  normalizedComponentToCurve f p.1 p.2

end NormalizedComponents

/- A normalized point maps into the component that indexes it. -/
theorem normalizedPointToCurve_mem_component [PrestableFamily f]
    (p : NormalizedComponents.Point (f := f)) :
    NormalizedComponents.pointToCurve (f := f) p ∈ (p.1 : Set X) := by
  let _ : IsNoetherian X := isNoetherian_of_quasiCompact f
  let _ := componentScheme_isIntegral f p.1
  have hrange : Set.range (componentInclusion f p.1) = (p.1 : Set X) := by
    change Set.range (X.irreducibleComponentIdeal p.1 p.1.2).radical.subschemeι =
      (p.1 : Set X)
    rw [Scheme.IdealSheafData.range_subschemeι]
    change _ = ((X.irreducibleComponentIdeal p.1 p.1.2).radical.support : Set X)
    rw [Scheme.IdealSheafData.support_radical]
  rw [← hrange]
  exact ⟨Normalization.toCurve (componentScheme f p.1) p.2, rfl⟩

/- Every point of a component has a preimage on its actual normalization. -/
theorem exists_normalizedPoint_over_of_mem [PrestableFamily f]
    (C : Component X) {x : X} (hx : x ∈ (C : Set X)) :
    ∃ p : NormalizedComponents.Point (f := f), p.1 = C ∧
      NormalizedComponents.pointToCurve (f := f) p = x := by
  let _ : IsNoetherian X := isNoetherian_of_quasiCompact f
  let _ := componentScheme_isIntegral f C
  have hrange : Set.range (componentInclusion f C) = (C : Set X) := by
    change Set.range (X.irreducibleComponentIdeal C C.2).radical.subschemeι = (C : Set X)
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.support_radical]
    rfl
  obtain ⟨z, hz⟩ : ∃ z : componentScheme f C, componentInclusion f C z = x := by
    have hx' : x ∈ Set.range (componentInclusion f C) := hrange ▸ hx
    exact hx'
  obtain ⟨p, hp⟩ := Scheme.Hom.surjective (Normalization.toCurve (componentScheme f C)) z
  refine ⟨⟨C, p⟩, rfl, ?_⟩
  change componentInclusion f C (Normalization.toCurve (componentScheme f C) p) = x
  rw [hp, hz]

/-- Actual branches of every geometric edge on the canonical normalizations.

The component and node equations make this a witness about the normalization maps themselves;
the endpoint pair is consequently obtained from the two normalized points, rather than being an
independent incidence label. -/
structure NormalizedBranchData [PrestableFamily f] [IsAlgClosed K]
    where
  point : Edge f → Fin 2 → NormalizedComponents.Point (f := f)
  point_to_node : ∀ e j, NormalizedComponents.pointToCurve (f := f) (point e j) = edgePoint f e
  point_injective : ∀ e, Function.Injective (point e)
  /-- Every normalized point above a node is one of the two local branches.

  The algebraic-closure hypothesis is essential here: over a non-algebraically-closed field a
  node can have a single topological normalization point of residue degree two. -/
  point_fibre_surjective : ∀ e (p : NormalizedComponents.Point (f := f)),
    NormalizedComponents.pointToCurve (f := f) p = edgePoint f e →
      p = point e 0 ∨ p = point e 1

namespace NormalizedBranchData

variable [PrestableFamily f] [IsAlgClosed K]
  (B : NormalizedBranchData (f := f))

/-- The actual fibre of a normalized component over the point represented by an edge. -/
abbrev nodeFibre (e : Edge f) :=
  {p : NormalizedComponents.Point (f := f) //
    NormalizedComponents.pointToCurve (f := f) p = edgePoint f e}

/-- The selected branch pair is an equivalence with the entire normalization fibre over the node.
This packages both injectivity and the all-points exhaustion statement. -/
def branchFibreEquiv (e : Edge f) : Fin 2 ≃ nodeFibre (f := f) e :=
  Equiv.ofBijective (fun j ↦
      (⟨B.point e j, B.point_to_node e j⟩ : nodeFibre (f := f) e)) ⟨by
    intro i j h
    apply B.point_injective e
    exact congrArg (fun z : nodeFibre (f := f) e ↦ z.1) h
  , by
    intro p
    rcases B.point_fibre_surjective e p.1 p.2 with h | h
    · exact ⟨0, Subtype.ext h.symm⟩
    · exact ⟨1, Subtype.ext h.symm⟩⟩

theorem branch_points_ne (e : Edge f) : B.point e 0 ≠ B.point e 1 := by
  intro h
  have hz : (0 : Fin 2) = 1 := B.point_injective e h
  exact Fin.zero_ne_one hz

omit [IsAlgClosed K] in
theorem endpoint_pair_of_normalized_fibre (e : Edge f)
    (p : Fin 2 → NormalizedComponents.Point (f := f))
    (hp : ∀ j, NormalizedComponents.pointToCurve (f := f) (p j) = edgePoint f e)
    (hs : ∀ q : NormalizedComponents.Point (f := f),
      NormalizedComponents.pointToCurve (f := f) q = edgePoint f e →
        q = p 0 ∨ q = p 1) :
    s(endpoint f e 0, endpoint f e 1) = s((p 0).1, (p 1).1) := by
  have hmem (j : Fin 2) : edgePoint f e ∈ ((p j).1 : Set X) := by
    rw [← hp j]
    exact normalizedPointToCurve_mem_component f (p j)
  cases e with
  | inl e =>
      have heq (j : Fin 2) : componentOf e.1 = (p j).1 :=
        e.2.2 _ _ (mem_componentOf _) (hmem j)
      exact Sym2.eq_iff.mpr (Or.inl ⟨heq 0, heq 1⟩)
  | inr e =>
      have hC := e.2.2 _ (Sym2.out_fst_mem e.1.2)
      have hD := e.2.2 _ (Sym2.out_snd_mem e.1.2)
      obtain ⟨qC, hqC, hqCx⟩ := exists_normalizedPoint_over_of_mem f e.1.2.out.1 hC
      obtain ⟨qD, hqD, hqDx⟩ := exists_normalizedPoint_over_of_mem f e.1.2.out.2 hD
      have hC' : e.1.2.out.1 = (p 0).1 ∨ e.1.2.out.1 = (p 1).1 := by
        rcases hs qC hqCx with h | h
        · exact Or.inl (hqC.symm.trans (congrArg Sigma.fst h))
        · exact Or.inr (hqC.symm.trans (congrArg Sigma.fst h))
      have hD' : e.1.2.out.2 = (p 0).1 ∨ e.1.2.out.2 = (p 1).1 := by
        rcases hs qD hqDx with h | h
        · exact Or.inl (hqD.symm.trans (congrArg Sigma.fst h))
        · exact Or.inr (hqD.symm.trans (congrArg Sigma.fst h))
      have hne : e.1.2.out.1 ≠ e.1.2.out.2 := by
        intro h
        apply e.2.1
        rw [← Quot.out_eq e.1.2]
        exact Sym2.mk_isDiag_iff.mpr h
      apply Sym2.eq_iff.mpr
      rcases hC' with hC' | hC' <;> rcases hD' with hD' | hD'
      · exact False.elim (hne (hC'.trans hD'.symm))
      · exact Or.inl ⟨hC', hD'⟩
      · exact Or.inr ⟨hC', hD'⟩
      · exact False.elim (hne (hC'.trans hD'.symm))

end NormalizedBranchData


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

/-- The geometric dual graph with vertex genera computed from canonical normalized components. -/
def geometricDualGraphOfNormalization [PrestableFamily f] : DualGraph.{u} :=
  geometricDualGraph f (normalizedComponentGenus f)

@[simp]
theorem geometricDualGraphOfNormalization_genus [PrestableFamily f]
    (C : Component X) :
    (geometricDualGraphOfNormalization f).genus C =
      arithmeticGenus K (normalizedComponentToBase f C) := rfl

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

/-- A separating node has two distinct component endpoints. -/
theorem endpoint_ne_of_multi (e : multiEdges (X := X)) :
    endpoint f (Sum.inr e) 0 ≠ endpoint f (Sum.inr e) 1 := by
  intro h
  apply e.2.1
  rw [← endpoint_inr (f := f) e, Sym2.mk_isDiag_iff]
  exact h

/-- An edge joining distinct components cannot be represented by a loop at that node. -/
theorem multi_edge_not_loop (e : multiEdges (X := X)) :
    ¬ edgePoint f (Sum.inr e) ∈ loopEdges f := by
  intro h
  have hmem₀ (z : Sym2 (Component X)) : z.out.1 ∈ z := by
    have hz : s(z.out.1, z.out.2) = z := Quot.out_eq z
    have hm : z.out.1 ∈ s(z.out.1, z.out.2) := Sym2.mem_iff.mpr (Or.inl rfl)
    rw [hz] at hm
    exact hm
  have hmem₁ (z : Sym2 (Component X)) : z.out.2 ∈ z := by
    have hz : s(z.out.1, z.out.2) = z := Quot.out_eq z
    have hm : z.out.2 ∈ s(z.out.1, z.out.2) := Sym2.mem_iff.mpr (Or.inr rfl)
    rw [hz] at hm
    exact hm
  have h₀ : e.1.1 ∈ (e.1.2.out.1 : Set X) := e.2.2 _ (hmem₀ e.1.2)
  have h₁ : e.1.1 ∈ (e.1.2.out.2 : Set X) := e.2.2 _ (hmem₁ e.1.2)
  exact endpoint_ne_of_multi (f := f) e (h.2 _ _ h₀ h₁)

/-- The point of a loop lies outside the smooth locus. -/
theorem loopEdges_subset_compl_smoothLocus [LocallyOfFinitePresentation f] :
    loopEdges f ⊆ (f.smoothLocus : Set X)ᶜ :=
  fun _ hx ↦ nodeSet_subset_compl_smoothLocus f hx.1

end

end GromovWitten.AlgebraicGeometry.Curves
