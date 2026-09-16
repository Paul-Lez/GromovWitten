/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.Algebra.StandardSmoothKrullDimension
import GromovWitten.AlgebraicGeometry.Curves.RelativeDimension
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.JacobsonSpace

/-!
# Relative dimension of the smooth locus of a family of curves

Let `f : X ⟶ S` be locally of finite presentation with geometric pure relative dimension one.
This file proves that every smooth chart of `f` is standard smooth of relative dimension exactly
one, so the smooth locus of `f` is `SmoothOfRelativeDimension 1` over `S`
(`smoothLocus_smoothOfRelativeDimension_one`), and a smooth family of geometric pure relative
dimension one is itself `SmoothOfRelativeDimension 1`
(`SmoothOfRelativeDimension.of_smooth_of_geometricPureRelativeDimension`).

## Strategy

Take an affine chart `Spec T → Spec R` of `f` at `x` which is standard smooth of relative
dimension `n`, and let `s = f x`.  The fibre of the chart over `s` is `Spec (T ⊗_R κ(s))`, an
open subscheme of the scheme-theoretic fibre `F = f.fiber s`, and
`ringKrullDim_eq_of_isStandardSmoothOfRelativeDimension` identifies its dimension with `n`.

On the other hand this open subscheme has dimension exactly one:

* at most one, because every irreducible component of `F` has dimension one
  (`topologicalKrullDim_le_of_forall_irreducibleComponents`);
* at least one, because `F` is a Jacobson space (it is locally of finite type over a field),
  so a closed point `w` of the affine open is closed in `F`; the generic point of the
  one-dimensional component through `w` lies in the open and is a proper generalization of `w`
  (`one_le_topologicalKrullDim_of_isClosed_singleton`).

No dimension theory beyond the Jacobson property of finite-type schemes over a field is used.
-/

open CategoryTheory Limits Topology TopologicalSpace
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

/-! ### Topological preliminaries -/

section Topology

variable {T : Type*} [TopologicalSpace T]

/-- The preimage under the inclusion of a closed set `Z` of an irreducible set contained in `Z`
is irreducible. -/
theorem isIrreducible_preimage_val_of_subset {Z A : Set T} (hA : IsIrreducible A)
    (hAZ : A ⊆ Z) : IsIrreducible ((Subtype.val : Z → T) ⁻¹' A) := by
  have hrange : (Subtype.val : Z → T) ⁻¹' A = Set.range (Set.inclusion hAZ) := by
    rw [Set.range_inclusion]
    rfl
  rw [hrange, ← Set.image_univ]
  have : IrreducibleSpace A := Subtype.irreducibleSpace hA
  exact (IrreducibleSpace.isIrreducible_univ A).image _ (continuous_inclusion hAZ).continuousOn

/-- If every irreducible component of a space has dimension at most `d`, so does the space. -/
theorem topologicalKrullDim_le_of_forall_irreducibleComponents {d : WithBot ℕ∞}
    (h : ∀ Z ∈ irreducibleComponents T, topologicalKrullDim Z ≤ d) :
    topologicalKrullDim T ≤ d := by
  unfold topologicalKrullDim Order.krullDim
  refine iSup_le fun p ↦ ?_
  obtain ⟨Z, hZ, hsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ p.last.isIrreducible
  have hmem : ∀ i, (p i : Set T) ⊆ Z := fun i ↦
    (SetLike.coe_subset_coe.mpr (p.monotone (Fin.le_last i))).trans hsub
  let q : LTSeries (IrreducibleCloseds Z) :=
    { length := p.length
      toFun := fun i ↦
        ⟨Subtype.val ⁻¹' (p i : Set T),
          isIrreducible_preimage_val_of_subset (p i).isIrreducible (hmem i),
          (p i).isClosed.preimage continuous_subtype_val⟩
      step := fun i ↦ by
        have hlt : p.toFun i.castSucc < p.toFun i.succ := p.step i
        change (⟨Subtype.val ⁻¹' (p i.castSucc : Set T), _, _⟩ : IrreducibleCloseds Z) <
          ⟨Subtype.val ⁻¹' (p i.succ : Set T), _, _⟩
        rw [← SetLike.coe_ssubset_coe] at hlt ⊢
        change Subtype.val ⁻¹' (p i.castSucc : Set T) ⊂ Subtype.val ⁻¹' (p i.succ : Set T)
        refine ⟨Set.preimage_mono hlt.1, fun hcontra ↦ hlt.2 fun x hx ↦ ?_⟩
        have hx' : x ∈ (Subtype.val : Z → T) '' ((Subtype.val : Z → T) ⁻¹' (p i.succ : Set T)) := by
          rw [Subtype.image_preimage_coe]
          exact ⟨hmem _ hx, hx⟩
        obtain ⟨y, hy, rfl⟩ := hx'
        exact hcontra hy }
  calc ((p.length : ℕ∞) : WithBot ℕ∞) = q.length := rfl
    _ ≤ topologicalKrullDim Z := Order.LTSeries.length_le_krullDim q
    _ ≤ d := h Z hZ

/-- A space of pure dimension `d` has dimension at most `d`. -/
theorem topologicalKrullDim_le_of_pure {d : ℕ}
    (h : ∀ Z ∈ irreducibleComponents T, topologicalKrullDim Z = d) :
    topologicalKrullDim T ≤ d :=
  topologicalKrullDim_le_of_forall_irreducibleComponents fun Z hZ ↦ (h Z hZ).le

/-- A nonempty subsingleton space has topological Krull dimension at most zero. -/
theorem topologicalKrullDim_le_zero_of_subsingleton [Subsingleton T] :
    topologicalKrullDim T ≤ 0 := by
  have : Subsingleton (IrreducibleCloseds T) := ⟨fun A B ↦ by
    apply IrreducibleCloseds.ext
    obtain ⟨a, ha⟩ := A.isIrreducible.nonempty
    obtain ⟨b, hb⟩ := B.isIrreducible.nonempty
    ext z
    constructor
    · intro _
      rwa [Subsingleton.elim z b]
    · intro _
      rwa [Subsingleton.elim z a]⟩
  exact Order.krullDim_nonpos_of_subsingleton

end Topology

/-! ### Closed points of open subschemes of a pure one-dimensional Jacobson scheme -/

/-- In a Jacobson scheme all of whose irreducible components have dimension one, an open
subscheme containing a closed point has dimension at least one: the generic point of the
component through the point is a proper generalization inside the open subscheme. -/
theorem one_le_topologicalKrullDim_of_isClosed_singleton {F W : Scheme.{u}} [JacobsonSpace F]
    (hF : PureTopologicalDimension 1 F) (j : W ⟶ F) [IsOpenImmersion j] (w : W)
    (hw : IsClosed ({w} : Set W)) : 1 ≤ topologicalKrullDim W := by
  have hj := j.isOpenEmbedding
  have hjw : IsClosed ({j w} : Set F) := by
    have hpre := hj.preimage_closedPoints
    have hw' : w ∈ closedPoints W := hw
    rw [← hpre] at hw'
    exact hw'
  have hZirr : IsIrreducible (irreducibleComponent (j w)) := isIrreducible_irreducibleComponent
  have hZcl : IsClosed (irreducibleComponent (j w)) := isClosed_irreducibleComponent
  have hZdim : topologicalKrullDim (irreducibleComponent (j w)) = 1 :=
    hF _ (irreducibleComponent_mem_irreducibleComponents _)
  obtain ⟨ξ, hξ⟩ : ∃ ξ, IsGenericPoint ξ (irreducibleComponent (j w)) :=
    ⟨_, hZirr.isGenericPoint_genericPoint hZcl⟩
  have hξmem : ξ ∈ Set.range j :=
    (hξ.mem_open_set_iff hj.isOpen_range).mpr ⟨j w, mem_irreducibleComponent, ⟨w, rfl⟩⟩
  obtain ⟨ξ', hξ'⟩ := hξmem
  have hspec : ξ' ⤳ w := by
    rw [← hj.specializes_iff, hξ']
    exact hξ.specializes mem_irreducibleComponent
  have hne : ξ' ≠ w := by
    intro h
    subst h
    have hZeq : irreducibleComponent (j ξ') = {j ξ'} := by
      rw [← hξ.def, ← hξ', hjw.closure_eq]
    have hsub : Subsingleton (irreducibleComponent (j ξ')) := by
      rw [hZeq]
      exact Set.subsingleton_singleton.coe_sort
    have h0 : topologicalKrullDim (irreducibleComponent (j ξ')) ≤ 0 :=
      topologicalKrullDim_le_zero_of_subsingleton
    rw [hZdim] at h0
    exact absurd h0 (not_le.mpr zero_lt_one)
  rw [topologicalKrullDim, Order.one_le_krullDim_iff]
  refine ⟨⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩,
    ⟨closure {ξ'}, isIrreducible_singleton.closure, isClosed_closure⟩, ?_⟩
  rw [← SetLike.coe_ssubset_coe]
  refine ⟨specializes_iff_closure_subset.mp hspec, fun hcontra ↦ hne ?_⟩
  have hspec' : w ⤳ ξ' := specializes_iff_closure_subset.mpr hcontra
  exact (hspec.antisymm hspec').eq

/-! ### The affine fibre of a chart -/

/-- The fibre of `Spec T → Spec R` over a prime `p` is homeomorphic to the spectrum of the fibre
ring `κ(p) ⊗[R] T`. -/
def specFiberHomeomorph (R T : Type u) [CommRing R] [CommRing T] [Algebra R T]
    (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R T))).fiber p ≃ₜ
      PrimeSpectrum (p.asIdeal.Fiber T) :=
  (Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso R T p)).hom.homeomorph

/-- The fibre of a standard-smooth affine chart of relative dimension `n` over a point of an
open subscheme of the fibre, together with its dimension identification.  This is the
technical core: a chart `(U, V)` of `g = j ≫ f` at `y`, standard smooth of relative dimension
`n`, has `n = 1` as soon as the scheme-theoretic fibre of `f` through `j y` has pure
dimension one. -/
theorem relativeDimension_eq_one_of_chart {X Y S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (j : Y ⟶ X) [IsOpenImmersion j] (g : Y ⟶ S) (hg : j ≫ f = g)
    {U : S.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (e : V ≤ g ⁻¹ᵁ U) {y : Y} (hy : y ∈ V)
    (hpure : PureTopologicalDimension 1 (f.fiber (f (j y))))
    {n : ℕ} (hn : (g.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n) : n = 1 := by
  subst hg
  -- The scheme-theoretic fibre of `f` through `j y` is a Jacobson space.
  have hlft : LocallyOfFiniteType (f.fiberToSpecResidueField (f (j y))) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (f (j y)))))
  have hJ : JacobsonSpace (f.fiber (f (j y))) :=
    LocallyOfFiniteType.jacobsonSpace (f.fiberToSpecResidueField (f (j y)))
  -- The chart as an affine open immersion into `X`.
  let κ : Spec Γ(Y, V) ⟶ X := hV.fromSpec ≫ j
  let ι : Spec Γ(S, U) ⟶ S := hU.fromSpec
  have hcomm : Spec.map ((j ≫ f).appLE U V e) ≫ ι = κ ≫ f := by
    dsimp only [κ, ι]
    rw [Category.assoc]
    exact hU.SpecMap_appLE_fromSpec (j ≫ f) hV e
  have hsU : f (j y) ∈ U := e hy
  obtain ⟨s', hs'⟩ : ∃ s' : PrimeSpectrum Γ(S, U), ι s' = f (j y) :=
    ⟨hU.primeIdealOf ⟨f (j y), hsU⟩, hU.fromSpec_primeIdealOf ⟨f (j y), hsU⟩⟩
  -- The fibre of the chart over `s`, as an open subscheme of the fibre of `f`.
  let φ : Γ(S, U) →+* Γ(Y, V) := ((j ≫ f).appLE U V e).hom
  let _ : Algebra Γ(S, U) Γ(Y, V) := φ.toAlgebra
  have hφ : CommRingCat.ofHom (algebraMap Γ(S, U) Γ(Y, V)) = (j ≫ f).appLE U V e := by
    change CommRingCat.ofHom ((j ≫ f).appLE U V e).hom = _
    exact CommRingCat.ofHom_hom _
  have hset : (κ ≫ f) ⁻¹' {f (j y)} =
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) Γ(Y, V)))) ⁻¹' {s'} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hz : ι (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) Γ(Y, V))) z) = (κ ≫ f) z := by
      rw [hφ, ← Scheme.Hom.comp_apply, hcomm]
    rw [← hz, ← hs']
    exact ι.isOpenEmbedding.injective.eq_iff
  let eW : (κ ≫ f).fiber (f (j y)) ≃ₜ PrimeSpectrum (s'.asIdeal.Fiber Γ(Y, V)) :=
    ((κ ≫ f).fiberHomeo (f (j y))).trans <| (Homeomorph.setCongr hset).trans <|
      ((Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) Γ(Y, V)))).fiberHomeo s').symm.trans
        (specFiberHomeomorph Γ(S, U) Γ(Y, V) s')
  -- The fibre of the chart is nonempty, so the fibre ring is nontrivial.
  have hyV : (y : Y) ∈ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    exact hy
  obtain ⟨y', hy'⟩ := hyV
  have hpt : Nonempty ((κ ≫ f).fiber (f (j y))) := by
    refine ⟨((κ ≫ f).fiberHomeo (f (j y))).symm ⟨y', ?_⟩⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, κ, Scheme.Hom.comp_apply, hy']
  have hnontriv : Nontrivial (s'.asIdeal.Fiber Γ(Y, V)) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨eW hpt.some⟩
  -- The fibre ring is standard smooth of relative dimension `n` over `κ(s')`.
  have hss : Algebra.IsStandardSmoothOfRelativeDimension n Γ(S, U) Γ(Y, V) := hn
  have hfib := Algebra.IsStandardSmoothOfRelativeDimension.baseChange n (R := Γ(S, U))
    (S := Γ(Y, V)) (Ideal.ResidueField s'.asIdeal)
  have hdimW : topologicalKrullDim ((κ ≫ f).fiber (f (j y))) = n := by
    rw [IsHomeomorph.topologicalKrullDim_eq eW eW.isHomeomorph,
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      GromovWitten.Algebra.ringKrullDim_eq_of_isStandardSmoothOfRelativeDimension
        (k := s'.asIdeal.ResidueField) n]
  -- Upper bound: the fibre of the chart is an open subscheme of the pure one-dimensional fibre.
  have hle : topologicalKrullDim ((κ ≫ f).fiber (f (j y))) ≤ 1 := by
    have h1 : topologicalKrullDim (f.fiber (f (j y))) ≤ 1 := topologicalKrullDim_le_of_pure hpure
    have h2 := (fiberMapPrecomp κ f (f (j y))).isOpenEmbedding.isInducing.topologicalKrullDim_le
    exact h2.trans h1
  -- Lower bound: the fibre ring has a maximal ideal, which is a closed point.
  have hge : 1 ≤ topologicalKrullDim ((κ ≫ f).fiber (f (j y))) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (s'.asIdeal.Fiber Γ(Y, V))
    let w : (κ ≫ f).fiber (f (j y)) := eW.symm ⟨m, hm.isPrime⟩
    have hw : IsClosed ({w} : Set ((κ ≫ f).fiber (f (j y)))) := by
      have hclosed : IsClosed ({(⟨m, hm.isPrime⟩ : PrimeSpectrum (s'.asIdeal.Fiber Γ(Y, V)))} :
          Set (PrimeSpectrum (s'.asIdeal.Fiber Γ(Y, V)))) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hm
      have := (eW.symm.isClosed_image (s := {(⟨m, hm.isPrime⟩ :
        PrimeSpectrum (s'.asIdeal.Fiber Γ(Y, V)))})).mpr hclosed
      rwa [Set.image_singleton] at this
    exact one_le_topologicalKrullDim_of_isClosed_singleton hpure (fiberMapPrecomp κ f (f (j y)))
      w hw
  have hn1 : (n : WithBot ℕ∞) = 1 := by
    rw [← hdimW]
    exact le_antisymm hle hge
  exact_mod_cast hn1

/-! ### Main results -/

/-- A standard smooth ring map is standard smooth of some relative dimension. -/
theorem _root_.RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension
    {R T : Type u} [CommRing R] [CommRing T] {f : R →+* T} (hf : f.IsStandardSmooth) :
    ∃ n, f.IsStandardSmoothOfRelativeDimension n := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := hf
  let _ := f.toAlgebra
  exact ⟨_, ⟨_, _, _, ‹_›, P, rfl⟩⟩

/-- A smooth morphism of geometric pure relative dimension one is smooth of relative dimension
one: every standard-smooth chart has relative dimension exactly one. -/
theorem SmoothOfRelativeDimension.of_smooth_of_geometricPureRelativeDimension
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (h : GeometricPureRelativeDimension 1 f) :
    SmoothOfRelativeDimension 1 f := by
  have : LocallyOfFiniteType f := h.1
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hsm⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, hn⟩ := hsm.exists_isStandardSmoothOfRelativeDimension
  have hpure : PureTopologicalDimension 1 (f.fiber (f x)) := fiber_of_geometrically h.2 (f x)
  have h1 := relativeDimension_eq_one_of_chart f (𝟙 X) f (Category.id_comp f) hU hV e hx
    (by simpa using hpure) hn
  exact ⟨U, hU, V, hV, hx, e, h1 ▸ hn⟩

/-- The smooth locus of a locally finitely presented family of geometric pure relative
dimension one is smooth of relative dimension one over the base. -/
theorem smoothLocus_smoothOfRelativeDimension_one {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (h : GeometricPureRelativeDimension 1 f) :
    SmoothOfRelativeDimension 1 (f.smoothLocus.ι ≫ f) := by
  have : LocallyOfFiniteType f := h.1
  have hsm : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    ext x
    simp
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hsm'⟩ := Smooth.exists_isStandardSmooth (f.smoothLocus.ι ≫ f) x
  obtain ⟨n, hn⟩ := hsm'.exists_isStandardSmoothOfRelativeDimension
  have hpure : PureTopologicalDimension 1 (f.fiber (f (f.smoothLocus.ι x))) :=
    fiber_of_geometrically h.2 _
  have h1 := relativeDimension_eq_one_of_chart f f.smoothLocus.ι _ rfl hU hV e hx hpure hn
  exact ⟨U, hU, V, hV, hx, e, h1 ▸ hn⟩

end

end GromovWitten.AlgebraicGeometry.Curves
