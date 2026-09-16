/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Topology.KrullDimension
import GromovWitten.AlgebraicGeometry.Morphisms.Syntomic

/-!
# Relative dimension and families of curves

Relative dimension is defined from the Krull dimensions of scheme-theoretic fibres.  The
field-valued geometric refinements quantify over arbitrary Cartesian geometric fibres, which
makes their arbitrary-base-change stability a formal pullback-pasting theorem.

## Descent along surjective étale covers of the source

Two independent descent statements are proved here, both for a surjective étale `e : Y ⟶ X` and
`f : X ⟶ S`.

* Topological: `pureTopologicalDimension_of_surjective_of_generalizingMap` shows that pure
  topological dimension descends along any continuous surjection which is generalizing and
  injective on specializations inside its fibres.  An étale morphism has both properties (it is
  flat, hence generalizing, and locally quasi-finite, hence has discrete fibres), whence
  `pureTopologicalDimension_of_surjective_etale` and
  `GeometricPureRelativeDimension.of_precomp_surjective_etale`.

* Ring-theoretic: `of_etale_of_surjective` proves descent along a surjective étale ring map for
  any ring-hom property satisfying five closure conditions, and
  `locallyOfFinitePresentation_of_precomp_surjective_etale` and
  `locallyOfFiniteType_of_precomp_surjective_etale` are the resulting scheme-level statements.
  This is descent along a *source* cover (Stacks 02JS, 036M), which the pinned Mathlib does not
  provide: `MorphismProperty.DescendsAlong` is descent along a *base change*, a different
  statement.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X S : Scheme.{u}}

/-- A locally finite-type morphism has relative dimension at most `d` when every
scheme-theoretic fibre has topological Krull dimension at most `d`. -/
def RelativeDimensionLE (d : ℕ) (f : X ⟶ S) : Prop :=
  LocallyOfFiniteType f ∧ ∀ s : S, topologicalKrullDim (f.fiber s) ≤ d

/-- A locally finite-type morphism has pure relative dimension `d` when every irreducible
component of every fibre has dimension `d`. -/
def PureRelativeDimension (d : ℕ) (f : X ⟶ S) : Prop :=
  LocallyOfFiniteType f ∧ ∀ s : S, ∀ Z ∈ irreducibleComponents (f.fiber s),
    topologicalKrullDim Z = d

/-- Precomposition by an isomorphism gives homeomorphic scheme-theoretic fibres.  This is a
topological comparison; it does not invoke invariance under extension of residue fields. -/
noncomputable def fiberHomeomorphPrecompIso {Y : Scheme.{u}} (e : X ≅ Y)
    (f : Y ⟶ S) (s : S) : (e.hom ≫ f).fiber s ≃ₜ f.fiber s :=
  (e.hom ≫ f).fiberHomeo s |>.trans <|
    (Homeomorph.setCongr (by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
      change f (e.hom x) = s ↔ f (e.hom x) = s
      rfl)) |>.trans <|
      (e.schemeIsoToHomeo.isEmbedding.homeomorphOfSubsetRange (by
        intro y _
        refine ⟨e.inv y, ?_⟩
        change e.hom (e.inv y) = y
        have h := congrArg (fun k : Y ⟶ Y ↦ k y) e.inv_hom_id
        have hid : (𝟙 Y : Y ⟶ Y) y = y := rfl
        have hi : e.hom (e.inv y) = (𝟙 Y : Y ⟶ Y) y := by
          simpa only [Scheme.Hom.comp_apply] using h
        exact hi.trans hid)) |>.trans
        (f.fiberHomeo s).symm

/-- Postcomposition by an isomorphism merely relabels the base point of a fibre. -/
noncomputable def fiberHomeomorphPostcompIso {Y : Scheme.{u}} (f : X ⟶ Y)
    (e : Y ≅ S) (s : S) : (f ≫ e.hom).fiber s ≃ₜ f.fiber (e.inv s) :=
  (f ≫ e.hom).fiberHomeo s |>.trans <|
    (Homeomorph.setCongr (by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
      change e.hom (f x) = s ↔ f x = e.inv s
      constructor
      · intro h
        rw [← h]
        have hi := congrArg (fun k : Y ⟶ Y ↦ k (f x)) e.hom_inv_id
        have hid : (𝟙 Y : Y ⟶ Y) (f x) = f x := rfl
        exact hid.symm.trans (by simpa only [Scheme.Hom.comp_apply] using hi.symm)
      · intro h
        rw [h]
        have hi := congrArg (fun k : S ⟶ S ↦ k s) e.inv_hom_id
        have hid : (𝟙 S : S ⟶ S) s = s := rfl
        have hi' : e.hom (e.inv s) = (𝟙 S : S ⟶ S) s := by
          simpa only [Scheme.Hom.comp_apply] using hi
        exact hi'.trans hid)) |>.trans
      (f.fiberHomeo (e.inv s)).symm

/-- Restricting the target to an open neighbourhood does not change the corresponding fibre. -/
noncomputable def fiberHomeomorphRestrict (f : X ⟶ S) (U : S.Opens) (s : U) :
    (f ∣_ U).fiber s ≃ₜ f.fiber (U.ι s) :=
  (f ∣_ U).fiberHomeo s |>.trans <|
    (Homeomorph.setCongr (by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      have hcomm := congrArg (fun k : (f ⁻¹ᵁ U).toScheme ⟶ S ↦ k x)
        (morphismRestrict_ι f U)
      simp only [Scheme.Hom.comp_apply] at hcomm
      constructor
      · intro h
        rw [← hcomm, h]
      · intro h
        apply U.ι.isOpenEmbedding.injective
        rw [hcomm]
        exact h)) |>.trans <|
      ((f ⁻¹ᵁ U).ι.isOpenEmbedding.isEmbedding.homeomorphOfSubsetRange (by
        intro x hx
        refine ⟨⟨x, ?_⟩, rfl⟩
        change f x ∈ U
        rw [hx]
        exact s.property)) |>.trans
        (f.fiberHomeo (U.ι s)).symm

/-- The map from a fibre after precomposition to the original fibre.  For an open
immersion `j`, this realizes the former fibre as a locally closed subspace of the latter. -/
noncomputable def fiberMapPrecomp {Y : Scheme.{u}} (j : Y ⟶ X) (f : X ⟶ S) (s : S) :
    (j ≫ f).fiber s ⟶ f.fiber s :=
  pullback.lift ((j ≫ f).fiberι s ≫ j) ((j ≫ f).fiberToSpecResidueField s) (by
    rw [Category.assoc, Scheme.Hom.fiber_fac])

@[reassoc (attr := simp)]
lemma fiberMapPrecomp_fiberι {Y : Scheme.{u}} (j : Y ⟶ X) (f : X ⟶ S) (s : S) :
    fiberMapPrecomp j f s ≫ f.fiberι s = (j ≫ f).fiberι s ≫ j :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
lemma fiberMapPrecomp_fiberToSpecResidueField {Y : Scheme.{u}}
    (j : Y ⟶ X) (f : X ⟶ S) (s : S) :
    fiberMapPrecomp j f s ≫ f.fiberToSpecResidueField s =
      (j ≫ f).fiberToSpecResidueField s :=
  pullback.lift_snd ..

set_option backward.isDefEq.respectTransparency false in
/-- The fibre map induced by precomposition is the base change of the source map. -/
lemma fiberMapPrecomp_isPullback {Y : Scheme.{u}}
    (j : Y ⟶ X) (f : X ⟶ S) (s : S) :
    IsPullback (fiberMapPrecomp j f s) ((j ≫ f).fiberι s) (f.fiberι s) j := by
  refine IsPullback.mk (toCommSq := ⟨fiberMapPrecomp_fiberι j f s⟩) ⟨?_⟩
  refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
  · intro t
    exact pullback.lift t.snd (t.fst ≫ f.fiberToSpecResidueField s) (by
      rw [← Category.assoc, ← t.condition, Category.assoc, Scheme.Hom.fiber_fac]
      exact (Category.assoc _ _ _).symm)
  · intro t
    apply pullback.hom_ext
    · suffices t.snd ≫ j = t.fst ≫ f.fiberι s by
        simpa [fiberMapPrecomp, Scheme.Hom.fiberι,
          Scheme.Hom.fiberToSpecResidueField, Category.assoc]
      exact t.condition.symm
    · simp [fiberMapPrecomp, Scheme.Hom.fiberι,
        Scheme.Hom.fiberToSpecResidueField, Category.assoc]
  · intro t
    exact pullback.lift_fst ..
  · intro t m hfst hsnd
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact hsnd
    · rw [pullback.lift_snd]
      calc
        m ≫ (j ≫ f).fiberToSpecResidueField s =
            m ≫ (fiberMapPrecomp j f s ≫ f.fiberToSpecResidueField s) := by
              rw [fiberMapPrecomp_fiberToSpecResidueField]
        _ = (m ≫ fiberMapPrecomp j f s) ≫ f.fiberToSpecResidueField s :=
          (Category.assoc _ _ _).symm
        _ = t.fst ≫ f.fiberToSpecResidueField s := by rw [hfst]

instance fiberMapPrecomp_isOpenImmersion {Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (f : X ⟶ S) (s : S) :
    IsOpenImmersion (fiberMapPrecomp j f s) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (fiberMapPrecomp_isPullback j f s).flip inferInstance

instance fiberMapPrecomp_isPreimmersion {Y : Scheme.{u}} (j : Y ⟶ X) [IsPreimmersion j]
    (f : X ⟶ S) (s : S) : IsPreimmersion (fiberMapPrecomp j f s) := by
  let hcomp : IsPreimmersion (fiberMapPrecomp j f s ≫ f.fiberι s) := by
    rw [fiberMapPrecomp_fiberι]
    infer_instance
  exact @IsPreimmersion.of_comp _ _ _ (fiberMapPrecomp j f s) (f.fiberι s)
    inferInstance hcomp

set_option backward.isDefEq.respectTransparency false in
/-- On points, the fibre of a source-open restriction is the corresponding open subset of the
original fibre. -/
lemma fiberMapPrecomp_range {Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (f : X ⟶ S) (s : S) :
    Set.range (fiberMapPrecomp j f s) = (f.fiberι s) ⁻¹' Set.range j := by
  let e : (j ≫ f).fiber s ≅ pullback (f.fiberι s) j :=
    (fiberMapPrecomp_isPullback j f s).isoIsPullback _ _
      (IsPullback.of_hasPullback (f.fiberι s) j)
  have he : e.hom ≫ pullback.fst (f.fiberι s) j = fiberMapPrecomp j f s :=
    (fiberMapPrecomp_isPullback j f s).isoIsPullback_hom_fst _ _
      (IsPullback.of_hasPullback (f.fiberι s) j)
  rw [← he, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr e.hom.surjective, Set.image_univ,
    Scheme.Pullback.range_fst]

/-- A preimmersion induces an isomorphism on residue fields. -/
lemma residueFieldMap_isIso_of_isPreimmersion {T S : Scheme.{u}}
    (b : T ⟶ S) [IsPreimmersion b] (t : T) : IsIso (b.residueFieldMap t) := by
  have hsurjective : Function.Surjective (b.residueFieldMap t) := by
    intro x
    obtain ⟨x, rfl⟩ := T.residue_surjective t x
    obtain ⟨x, rfl⟩ := b.stalkMap_surjective t x
    refine ⟨S.residue (b t) x, ?_⟩
    exact congrArg (fun q ↦ q x) (Scheme.residue_residueFieldMap b t)
  exact (RingEquiv.ofBijective (b.residueFieldMap t).hom
    ⟨RingHom.injective _, hsurjective⟩).toCommRingCatIso.isIso_hom

/-- A morphism preserves residue fields when its map on residue fields is an isomorphism at
every point.  This isolates the exact hypothesis under which fibres before and after base
change are isomorphic, without requiring the base map to be a preimmersion. -/
class PreservesResidueFields {T S : Scheme.{u}} (b : T ⟶ S) : Prop where
  isIso_residueFieldMap (t : T) : IsIso (b.residueFieldMap t)

/-- Preimmersions preserve residue fields. -/
instance {T S : Scheme.{u}} (b : T ⟶ S) [IsPreimmersion b] :
    PreservesResidueFields b where
  isIso_residueFieldMap := residueFieldMap_isIso_of_isPreimmersion b

/-- The canonical map from a fibre after chosen base change to the corresponding original
fibre. -/
noncomputable def fiberMapBaseChange {X T S : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) (t : T) :
    (pullback.snd f b).fiber t ⟶ f.fiber (b t) :=
  pullback.map (pullback.snd f b) (T.fromSpecResidueField t)
    f (S.fromSpecResidueField (b t)) (pullback.fst f b)
    (Spec.map (b.residueFieldMap t)) b
    (IsPullback.of_hasPullback f b).w.symm (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The fibre comparison map is obtained by base change along the induced residue-field map. -/
lemma fiberMapBaseChange_isPullback {X T S : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) (t : T) :
    IsPullback (fiberMapBaseChange f b t)
      ((pullback.snd f b).fiberToSpecResidueField t)
      (f.fiberToSpecResidueField (b t)) (Spec.map (b.residueFieldMap t)) := by
  simpa only [fiberMapBaseChange] using
    isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f b) t

/-- If the base map preserves residue fields, corresponding scheme-theoretic fibres are
isomorphic. -/
lemma fiberMapBaseChange_isIso_of_preservesResidueFields {X T S : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) [PreservesResidueFields b] (t : T) :
    IsIso (fiberMapBaseChange f b t) := by
  let _ : IsIso (b.residueFieldMap t) :=
    PreservesResidueFields.isIso_residueFieldMap (b := b) t
  have hspec : IsIso (Spec.map (b.residueFieldMap t)) := by infer_instance
  exact (fiberMapBaseChange_isPullback f b t).isIso_fst_of_isIso hspec

/-- After base change along a preimmersion, corresponding scheme-theoretic fibres are
isomorphic. -/
lemma fiberMapBaseChange_isIso_of_isPreimmersion {X T S : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) [IsPreimmersion b] (t : T) :
    IsIso (fiberMapBaseChange f b t) :=
  fiberMapBaseChange_isIso_of_preservesResidueFields f b t

attribute [local instance] specializationOrder in
/-- Topological Krull dimension is bounded if it is bounded on an open cover. -/
private theorem topologicalKrullDim_le_of_openCover
    {T : Type u} [TopologicalSpace T] [QuasiSober T] [T0Space T]
    {I : Type u} {Y : I → Type u} [∀ i, TopologicalSpace (Y i)]
    [∀ i, QuasiSober (Y i)] [∀ i, T0Space (Y i)]
    (g : ∀ i, Y i → T) (hg : ∀ i, Topology.IsOpenEmbedding (g i))
    (hcover : ⋃ i, Set.range (g i) = Set.univ) {n : WithBot ℕ∞}
    (hd : ∀ i, topologicalKrullDim (Y i) ≤ n) :
    topologicalKrullDim T ≤ n := by
  have hT : topologicalKrullDim T = Order.krullDim T := by
    change Order.krullDim (TopologicalSpace.IrreducibleCloseds T) = Order.krullDim T
    exact Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := T))
  rw [hT, Order.krullDim_eq_iSup_coheight, iSup_le_iff]
  intro x
  have hx : x ∈ ⋃ i, Set.range (g i) := by rw [hcover]; trivial
  obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
  have hY : topologicalKrullDim (Y i) = Order.krullDim (Y i) := by
    change Order.krullDim (TopologicalSpace.IrreducibleCloseds (Y i)) =
      Order.krullDim (Y i)
    exact Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y i))
  calc
    (↑(Order.coheight (g i y)) : WithBot ℕ∞) = ↑(Order.coheight y) := by
      exact congrArg (fun z : ℕ∞ ↦ (z : WithBot ℕ∞))
        (Topology.IsOpenEmbedding.coheight_eq (x := y) (g i) (hg i))
    _ ≤ Order.krullDim (Y i) := Order.coheight_le_krullDim y
    _ = topologicalKrullDim (Y i) := hY.symm
    _ ≤ n := hd i

/-- Pure component dimension is invariant under homeomorphism. -/
theorem pureTopologicalDimensionOfHomeomorph
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) {d : ℕ}
    (h : ∀ Z ∈ irreducibleComponents B, topologicalKrullDim Z = d) :
    ∀ Z ∈ irreducibleComponents A, topologicalKrullDim Z = d := by
  intro Z hZ
  let c := irreducibleComponentsEquivOfIsPreirreducibleFiber e e.continuous e.isOpenMap
    (fun _ ↦ (Set.subsingleton_singleton.preimage e.injective).isPreirreducible) e.surjective
  have himage : e '' Z ∈ irreducibleComponents B := (c.symm ⟨Z, hZ⟩).property
  rw [(e.isEmbedding.homeomorphImage Z).isHomeomorph.topologicalKrullDim_eq]
  exact h (e '' Z) himage

/-! ### Descent of pure topological dimension along source covers

An étale surjection is generalizing (being flat) and injective on specializations inside a
fibre (being locally quasi-finite, so having discrete fibres).  Those two properties already
force pure topological dimension to descend, and the proof below is purely topological: no
dimension theory over a field is used. -/

section PureTopologicalDimensionDescent

open Topology

attribute [local instance] specializationOrder

/-- On a subspace, the order induced by the ambient specialization order agrees with the
specialization order of the subspace, so the two order-theoretic Krull dimensions agree. -/
private lemma krullDim_specializationOrder_eq {A : Type*} [TopologicalSpace A] [T0Space A]
    (s : Set A) :
    @Order.krullDim ↥s (specializationOrder ↥s).toPreorder = Order.krullDim ↥s :=
  @Order.krullDim_eq_of_orderIso ↥s ↥s (specializationOrder ↥s).toPreorder _
    { toEquiv := Equiv.refl _
      map_rel_iff' := fun {_ _} ↦ Topology.IsInducing.subtypeVal.specializes_iff }

/-- The topological Krull dimension of a closed subspace of a sober space is the
order-theoretic Krull dimension of the induced specialization order. -/
private lemma topologicalKrullDim_eq_krullDim {A : Type*} [TopologicalSpace A] [T0Space A]
    [QuasiSober A] {s : Set A} (hs : IsClosed s) :
    topologicalKrullDim ↥s = Order.krullDim ↥s := by
  have : QuasiSober ↥s := hs.isClosedEmbedding_subtypeVal.quasiSober
  rw [← krullDim_specializationOrder_eq s]
  exact @Order.krullDim_eq_of_orderIso (TopologicalSpace.IrreducibleCloseds ↥s) ↥s _
    (specializationOrder ↥s).toPreorder (irreducibleSetEquivPoints (α := ↥s))

/-- A chain of specializations lifts along a surjective generalizing map: the bottom point is
lifted by surjectivity and every further generization is lifted by the generalizing property. -/
private theorem exists_ltSeries_of_generalizingMap
    {W Z : Type*} [TopologicalSpace W] [TopologicalSpace Z] [T0Space W] [T0Space Z]
    {q : W → Z} (hsurj : Function.Surjective q) (hgen : GeneralizingMap q) (p : LTSeries Z) :
    ∃ p' : LTSeries W, p'.length = p.length ∧ q p'.last = p.last := by
  induction p using RelSeries.inductionOn' with
  | singleton z =>
      obtain ⟨w, hw⟩ := hsurj z
      exact ⟨RelSeries.singleton _ w, rfl, by simpa using hw⟩
  | snoc p z hz ih =>
      obtain ⟨p', hlen, hlast⟩ := ih
      have hspec : z ⤳ q p'.last := by rw [hlast]; exact hz.le
      obtain ⟨w', hw'spec, hw'⟩ := hgen hspec
      have hlt : p'.last < w' := by
        refine lt_of_le_of_ne hw'spec ?_
        intro h
        rw [h, hw'] at hlast
        exact absurd hlast.symm hz.ne
      exact ⟨p'.snoc w' hlt, by simp [hlen], by simpa using hw'⟩

/-- Pure topological dimension descends along a continuous surjection which is generalizing
and injective on specializations inside its fibres.

The upper bound lifts a chain in a component of the target to a chain in the source, which is
then contained in a single component of the source.  The lower bound produces a maximal point
of the source over the generic point of the given component, and pushes its chains forward. -/
theorem pureTopologicalDimension_of_surjective_of_generalizingMap
    {W Z : Type*} [TopologicalSpace W] [TopologicalSpace Z] [T0Space W] [T0Space Z]
    [QuasiSober W] [QuasiSober Z] {q : W → Z} (hq : Continuous q)
    (hsurj : Function.Surjective q) (hgen : GeneralizingMap q)
    (hinj : ∀ ⦃w w' : W⦄, w ⤳ w' → q w = q w' → w = w') {d : ℕ}
    (hW : ∀ C ∈ irreducibleComponents W, topologicalKrullDim C = d) :
    ∀ T ∈ irreducibleComponents Z, topologicalKrullDim T = d := by
  intro T hT
  have hTcl : IsClosed T := isClosed_of_mem_irreducibleComponents T hT
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η T := QuasiSober.sober hT.1 hTcl
  -- the generic point of a component has no proper generization
  have hmax : ∀ z : Z, η ≤ z → z = η := by
    intro z hz
    have h1 : T ⊆ closure ({z} : Set Z) := by
      rw [← hη.def]
      exact closure_minimal (by simpa using specializes_iff_mem_closure.mp hz) isClosed_closure
    have h3 : z ∈ T := hT.2 isIrreducible_singleton.closure h1 (subset_closure rfl)
    exact ((hη.specializes h3).antisymm hz).eq.symm
  rw [topologicalKrullDim_eq_krullDim hTcl]
  refine le_antisymm ?_ ?_
  · -- every chain in `T` lifts to a chain inside one component of `W`
    rw [Order.krullDim]
    refine iSup_le fun p ↦ ?_
    obtain ⟨p', hlen, -⟩ :=
      exists_ltSeries_of_generalizingMap hsurj hgen (p.map (fun x ↦ (x : Z)) (fun _ _ h ↦ h))
    obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({p'.last} : Set W)) isIrreducible_singleton.closure
    have hmem : ∀ i, p' i ∈ C := fun i ↦
      hsub (specializes_iff_mem_closure.mp (p'.strictMono.monotone (Fin.le_last i)))
    let p'' : LTSeries ↥C :=
      { length := p'.length, toFun := fun i ↦ ⟨p' i, hmem i⟩, step := fun i ↦ p'.step i }
    have h1 : ((p''.length : ℕ) : WithBot ℕ∞) ≤ Order.krullDim ↥C :=
      Order.le_krullDim_iff.mpr ⟨p'', rfl⟩
    have h2 : Order.krullDim ↥C = d := by
      rw [← topologicalKrullDim_eq_krullDim (isClosed_of_mem_irreducibleComponents C hC)]
      exact hW C hC
    calc (p.length : WithBot ℕ∞) = ((p''.length : ℕ) : WithBot ℕ∞) := by
          change ((p.length : ℕ) : WithBot ℕ∞) = ((p'.length : ℕ) : WithBot ℕ∞)
          rw [hlen]
          rfl
      _ ≤ Order.krullDim ↥C := h1
      _ = d := h2
  · -- a point over the generic point of `T` generates a component of `W`
    obtain ⟨w, hw⟩ := hsurj η
    obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({w} : Set W)) isIrreducible_singleton.closure
    have hCcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
    obtain ⟨ζ, hζ⟩ : ∃ ζ, IsGenericPoint ζ C := QuasiSober.sober hC.1 hCcl
    have hζw : ζ ⤳ w := hζ.specializes (hsub (subset_closure rfl))
    have hqζ : q ζ = q w := by
      have h := hζw.map hq
      rw [hw] at h
      rw [hw]
      exact hmax _ h
    have hCeq : C = closure ({w} : Set W) := by
      rw [← hζ.def, hinj hζw hqζ]
    have hdim : Order.krullDim ↥C = d := by
      rw [← topologicalKrullDim_eq_krullDim hCcl]
      exact hW C hC
    have hmaps : ∀ x : ↥C, q x ∈ T := by
      intro x
      have hx : (x : W) ∈ closure ({w} : Set W) := hCeq ▸ x.2
      have h1 : w ⤳ (x : W) := specializes_iff_mem_closure.mpr hx
      have h2 : η ⤳ q x := by rw [← hw]; exact h1.map hq
      exact hη.specializes_iff_mem.mp h2
    rw [← hdim]
    refine Order.krullDim_le_of_strictMono (fun x ↦ ⟨q x, hmaps x⟩) ?_
    intro x y hxy
    have hspec : (y : W) ⤳ (x : W) := hxy.le
    have hle : (q x : Z) ≤ q y := hspec.map hq
    refine lt_of_le_of_ne hle ?_
    intro hEq
    exact absurd (hinj hspec (Subtype.ext_iff.mp hEq).symm)
      (fun h ↦ hxy.ne (Subtype.ext h.symm))

end PureTopologicalDimensionDescent

/-! ## Geometric relative dimension

The original fibre predicates above quantify over scheme-theoretic residue-field fibres.  For
base-change-stable curve geometry one must quantify over *all* field-valued points.  The two
object properties below let Mathlib's `geometrically` construction perform exactly that
quantification, so arbitrary base change is formal and does not depend on a missing theorem
about Krull dimension after extending a residue field.
-/

/-- The isomorphism-invariant object property of having topological Krull dimension at most
`d`. -/
def TopologicalDimensionLE (d : ℕ) : ObjectProperty Scheme.{u} :=
  fun X ↦ topologicalKrullDim X ≤ d

instance topologicalDimensionLE_isClosedUnderIsomorphisms (d : ℕ) :
    (TopologicalDimensionLE d).IsClosedUnderIsomorphisms where
  of_iso := by
    intro X Y e hX
    change topologicalKrullDim Y ≤ d
    change topologicalKrullDim X ≤ d at hX
    rw [← e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
    exact hX

/-- The isomorphism-invariant object property that every irreducible component has
topological Krull dimension exactly `d`. -/
def PureTopologicalDimension (d : ℕ) : ObjectProperty Scheme.{u} :=
  fun X ↦ ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d

instance pureTopologicalDimension_isClosedUnderIsomorphisms (d : ℕ) :
    (PureTopologicalDimension d).IsClosedUnderIsomorphisms where
  of_iso := by
    intro X Y e hX
    change ∀ Z ∈ irreducibleComponents Y, topologicalKrullDim Z = d
    change ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d at hX
    exact pureTopologicalDimensionOfHomeomorph e.symm.schemeIsoToHomeo hX


section EtaleDimensionDescent

open Topology

/-- An étale morphism is locally quasi-finite: on affine charts it is of finite type and
formally unramified, and such a ring map is quasi-finite. -/
theorem locallyQuasiFinite_of_etale {W Z : Scheme.{u}} (q : W ⟶ Z) [Etale q] :
    LocallyQuasiFinite q := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h1 : RingHom.FormallyUnramified (q.appLE U V e).hom :=
    HasRingHomProperty.appLE (P := @FormallyUnramified) (f := q) inferInstance U V e
  have h2 : RingHom.FiniteType (q.appLE U V e).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (f := q) inferInstance U V e
  algebraize [(q.appLE U V e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

/-- Two points of the source of an étale morphism which lie in the same fibre and are related
by a specialization coincide: the fibres of a locally quasi-finite morphism are discrete. -/
theorem eq_of_specializes_of_etale {W Z : Scheme.{u}} (q : W ⟶ Z) [Etale q]
    {w w' : W} (h : w ⤳ w') (hq : q w = q w') : w = w' := by
  have := locallyQuasiFinite_of_etale q
  have hdisc : _root_.IsDiscrete (q.base ⁻¹' {q.base w}) := q.isDiscrete_preimage_singleton _
  have hsub : ({w, w'} : Set W) ⊆ q.base ⁻¹' {q.base w} := by
    rintro x (rfl | rfl)
    · exact rfl
    · exact hq.symm
  have hpre : IsPreirreducible ({w, w'} : Set W) := by
    rintro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
    refine ⟨w, by simp, ?_, ?_⟩
    · rcases ha with rfl | rfl
      · exact hau
      · exact (specializes_iff_forall_open.mp h) u hu hau
    · rcases hb with rfl | rfl
      · exact hbv
      · exact (specializes_iff_forall_open.mp h) v hv hbv
  exact (hdisc.mono hsub).subsingleton_of_isPreirreducible hpre (by simp) (by simp)

/-- Pure topological dimension descends along a surjective étale morphism of schemes.  Étale
morphisms are flat, hence generalizing, and locally quasi-finite, hence injective on
specializations inside a fibre. -/
theorem pureTopologicalDimension_of_surjective_etale {W Z : Scheme.{u}} (q : W ⟶ Z)
    [Etale q] [Surjective q] {d : ℕ} (h : PureTopologicalDimension d W) :
    PureTopologicalDimension d Z :=
  pureTopologicalDimension_of_surjective_of_generalizingMap q.continuous q.surjective
    (Flat.generalizingMap q) (fun _ _ hs hqe ↦ eq_of_specializes_of_etale q hs hqe) h

end EtaleDimensionDescent


/-! ### Descent of finite presentation along surjective étale source covers

The pinned Mathlib provides descent of finite presentation along a *base change*
(`MorphismProperty.DescendsAlong @LocallyOfFinitePresentation
(@Surjective ⊓ @Flat ⊓ @QuasiCompact)`), but not along a cover of the *source*
(Stacks 02JS, 036M).  The ring-theoretic content of the latter is proved here for étale covers:
if `B → C` is étale and surjective on spectra and `A → C` is of finite presentation, then so is
`A → B`.

The proof spreads the standard étale presentation of `C` over `B` out to a finitely presented
`A`-algebra `B₀` (`exists_standardEtalePair_spread`: the coefficients of the defining polynomials
and of the witnesses for the invertibility of the derivative generate such a `B₀`), localizes so
that the spread-out cover becomes faithfully flat, and then applies Mathlib's faithfully flat
descent of finite presentation along a base change
(`RingHom.FinitePresentation.codescendsAlong_faithfullyFlat`).  Since the localization is only
possible near a given prime, the statement is glued from basic opens through
`RingHom.finitePresentation_ofLocalizationSpanTarget`. -/

section StandardEtaleSpreadOut

open Polynomial Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

private lemma standardEtalePair_ext {R : Type*} [CommRing R] {P Q : StandardEtalePair R}
    (hf : P.f = Q.f) (hg : P.g = Q.g) : P = Q := by
  cases P; cases Q; subst hf; subst hg; rfl

open Classical in
/-- Every standard étale pair over `B` is the image of a standard étale pair over a finitely
presented `A`-algebra mapping to `B`. -/
theorem exists_standardEtalePair_spread (P : StandardEtalePair B) :
    ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A B₀) (_ : Algebra.FinitePresentation A B₀)
      (φ : B₀ →ₐ[A] B) (P₀ : StandardEtalePair B₀), P₀.map φ.toRingHom = P := by
  classical
  obtain ⟨p₁, p₂, n, hcond⟩ := P.cond
  set d := P.f.natDegree with hd
  set N := max (max P.g.natDegree p₁.natDegree) p₂.natDegree + 1 with hNdef
  have hgN : P.g.natDegree < N := by lia
  have hp₁N : p₁.natDegree < N := by lia
  have hp₂N : p₂.natDegree < N := by lia
  let ι : Type := Fin d ⊕ Fin N ⊕ Fin N ⊕ Fin N
  let cf : ι → B := Sum.elim (fun i ↦ P.f.coeff i) (Sum.elim (fun i ↦ P.g.coeff i)
    (Sum.elim (fun i ↦ p₁.coeff i) (fun i ↦ p₂.coeff i)))
  let ψ : MvPolynomial ι A →ₐ[A] B := MvPolynomial.aeval cf
  let 𝔣 : (MvPolynomial ι A)[X] :=
    X ^ d + ofFn d (fun i ↦ MvPolynomial.X (Sum.inl i))
  let 𝔤 : (MvPolynomial ι A)[X] := ofFn N (fun i ↦ MvPolynomial.X (Sum.inr (Sum.inl i)))
  let 𝔭₁ : (MvPolynomial ι A)[X] := ofFn N (fun i ↦ MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl i))))
  let 𝔭₂ : (MvPolynomial ι A)[X] := ofFn N (fun i ↦ MvPolynomial.X (Sum.inr (Sum.inr (Sum.inr i))))
  have hmonic : 𝔣.Monic :=
    monic_X_pow_add
      (ofFn_degree_lt (fun i : Fin d ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial ι A)))
  have h𝔤 : 𝔤.map ψ.toRingHom = P.g := by
    ext i
    rw [coeff_map]
    by_cases hi : i < N
    · simp [𝔤, ofFn_coeff_eq_val_of_lt _ hi, ψ, cf]
    · rw [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_lt hi)]
      simp only [map_zero]
      exact (coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hgN (Nat.le_of_not_lt hi))).symm
  have hcoeff𝔣 : ∀ i : ℕ, 𝔣.coeff i = if i = d then 1 else
      if h : i < d then MvPolynomial.X (Sum.inl (⟨i, h⟩ : Fin d)) else 0 := by
    intro i
    rcases lt_trichotomy i d with hi | hi | hi
    · rw [if_neg hi.ne, dif_pos hi]
      simp [𝔣, coeff_X_pow, hi.ne, ofFn_coeff_eq_val_of_lt _ hi]
    · subst hi
      rw [if_pos rfl]
      simp [𝔣, coeff_X_pow, ofFn_coeff_eq_zero_of_ge _ (le_refl _)]
    · rw [if_neg hi.ne', dif_neg (not_lt_of_gt hi)]
      simp [𝔣, coeff_X_pow, hi.ne', ofFn_coeff_eq_zero_of_ge _ (le_of_lt hi)]
  have h𝔣 : 𝔣.map ψ.toRingHom = P.f := by
    ext i
    rw [coeff_map, hcoeff𝔣]
    rcases lt_trichotomy i d with hi | hi | hi
    · rw [if_neg hi.ne, dif_pos hi]
      simp [ψ, cf]
    · subst hi
      rw [if_pos rfl, map_one]
      exact (P.monic_f).coeff_natDegree.symm
    · rw [if_neg hi.ne', dif_neg (not_lt_of_gt hi), map_zero]
      exact (coeff_eq_zero_of_natDegree_lt hi).symm
  -- the auxiliary polynomials
  have hofFn : ∀ (p : B[X]) (_ : p.natDegree < N) (v : Fin N → ι)
      (_ : ∀ i : Fin N, cf (v i) = p.coeff i),
      (ofFn N (fun i ↦ (MvPolynomial.X (v i) : MvPolynomial ι A))).map ψ.toRingHom = p := by
    intro p hp v hv
    ext i
    rw [coeff_map]
    by_cases hi : i < N
    · rw [ofFn_coeff_eq_val_of_lt _ hi]
      simpa [ψ] using hv ⟨i, hi⟩
    · rw [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_lt hi), map_zero]
      exact (coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hp (Nat.le_of_not_lt hi))).symm
  have h𝔭₁ : 𝔭₁.map ψ.toRingHom = p₁ :=
    hofFn p₁ hp₁N _ (fun i ↦ rfl)
  have h𝔭₂ : 𝔭₂.map ψ.toRingHom = p₂ :=
    hofFn p₂ hp₂N _ (fun i ↦ rfl)
  -- the universal relation and the ideal it generates
  set D : (MvPolynomial ι A)[X] := derivative 𝔣 * 𝔭₁ + 𝔣 * 𝔭₂ - 𝔤 ^ n with hDdef
  have hD : D.map ψ.toRingHom = 0 := by
    rw [hDdef]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      ← derivative_map, h𝔣, h𝔤, h𝔭₁, h𝔭₂, hcond, sub_self]
  set J : Ideal (MvPolynomial ι A) :=
    Ideal.span (((Finset.range (D.natDegree + 1)).image D.coeff : Finset (MvPolynomial ι A)) :
      Set (MvPolynomial ι A)) with hJdef
  have hJfg : J.FG := ⟨(Finset.range (D.natDegree + 1)).image D.coeff, rfl⟩
  have hmem : ∀ i, D.coeff i ∈ J := by
    intro i
    by_cases hi : i ≤ D.natDegree
    · refine Ideal.subset_span ?_
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      exact ⟨i, by lia, rfl⟩
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi)]
      exact J.zero_mem
  have hJker : ∀ x ∈ J, ψ x = 0 := by
    intro x hx
    rw [hJdef, Ideal.span, Submodule.mem_span_set'] at hx
    obtain ⟨m, g, w, rfl⟩ := hx
    have : ∀ j, ψ (w j : MvPolynomial ι A) = 0 := by
      intro j
      obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.range (D.natDegree + 1), D.coeff i = (w j : _) := by
        simpa [Finset.coe_image] using (w j).2
      have h0 : ψ.toRingHom (D.coeff i) = 0 := by rw [← coeff_map, hD, coeff_zero]
      rw [← hi]
      simpa using h0
    simp [map_sum, this]
  -- the finitely presented base
  let q : MvPolynomial ι A →ₐ[A] (MvPolynomial ι A ⧸ J) := Ideal.Quotient.mkₐ A J
  have hDq : D.map q.toRingHom = 0 := by
    ext i
    rw [coeff_map, coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)
  refine ⟨MvPolynomial ι A ⧸ J, inferInstance, inferInstance,
    Algebra.FinitePresentation.quotient hJfg, Ideal.Quotient.liftₐ J ψ hJker,
    { f := 𝔣.map q.toRingHom
      monic_f := hmonic.map _
      g := 𝔤.map q.toRingHom
      cond := ⟨𝔭₁.map q.toRingHom, 𝔭₂.map q.toRingHom, n, ?_⟩ }, ?_⟩
  · have := hDq
    rw [hDdef] at this
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      ← derivative_map, sub_eq_zero] at this
    exact this
  · have hcomp : (Ideal.Quotient.liftₐ J ψ hJker).toRingHom.comp q.toRingHom = ψ.toRingHom := by
      refine RingHom.ext fun y ↦ ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, q,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.liftₐ_apply]
      rfl
    apply standardEtalePair_ext <;>
      simp only [StandardEtalePair.map_f, StandardEtalePair.map_g, Polynomial.map_map, hcomp,
        h𝔣, h𝔤]



end StandardEtaleSpreadOut
section FinitePresentationDescent

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private lemma tmul_algebraMap_comm {R A D : Type*} [CommRing R] [CommRing A] [CommRing D]
    [Algebra R A] [Algebra R D] (r : R) :
    (algebraMap R A r) ⊗ₜ[R] (1 : D) = (1 : A) ⊗ₜ[R] (algebraMap R D r) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

/-- The key local step.  The property `Q` is assumed to be respected by isomorphisms, stable under
composition, implied by finite presentation, right-cancellable along finite-type maps, and to
codescend along faithfully flat maps; both `RingHom.FiniteType` and `RingHom.FinitePresentation`
satisfy all five.

If `C` is standard étale over `B`, satisfies `Q` over `A`, and carries a prime lying over `p`,
then `A → B` satisfies `Q` after localizing away from a suitable element outside `p`. -/
theorem exists_away_of_standardEtale
    (hQiso : RingHom.RespectsIso Q) (hQcomp : RingHom.StableUnderComposition Q)
    (hQfp : ∀ {R S : Type u} [CommRing R] [CommRing S] {g : R →+* S},
      g.FinitePresentation → Q g)
    (hQcancel : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {g₁ : R →+* S}
      {g₂ : S →+* T}, Q (g₂.comp g₁) → g₁.FiniteType → Q g₂)
    (hQdescends : RingHom.CodescendsAlong Q RingHom.FaithfullyFlat)
    (hQC : Q (algebraMap A C))
    (P : StandardEtalePair B) (eC : C ≃ₐ[B] P.Ring)
    (p : Ideal B) [p.IsPrime] (hp : ∃ q : PrimeSpectrum C,
      PrimeSpectrum.comap (algebraMap B C) q = ⟨p, inferInstance⟩) :
    ∃ b ∉ p, Q (algebraMap A (Localization.Away b)) := by
  obtain ⟨B₀, _, _, hB₀fp, φ, P₀, hP₀⟩ := exists_standardEtalePair_spread (A := A) P
  subst hP₀
  -- the algebra structure on `B` over `B₀`
  let : Algebra B₀ B := φ.toRingHom.toAlgebra
  have : IsScalarTower A B₀ B := IsScalarTower.of_algebraMap_eq (fun x ↦ (φ.commutes x).symm)
  -- the standard étale algebra over the finitely presented base
  let Q₀ : StandardEtalePresentation B₀ P₀.Ring :=
    ⟨P₀, P₀.X, P₀.hasMap_X, by
      simpa [StandardEtalePair.lift_X_left] using Function.bijective_id⟩
  have hiso : B ⊗[B₀] P₀.Ring ≃ₐ[B] C := (Q₀.baseChange (T := B)).equivRing.trans eC.symm
  -- the induced map `C₀ ⟶ C` and its compatibility
  let ρ : P₀.Ring →+* C :=
    hiso.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := B₀) (A := B)).toRingHom
  have hρ : ρ.comp (algebraMap B₀ P₀.Ring) = (algebraMap B C).comp (algebraMap B₀ B) := by
    ext x
    have h1 : (Algebra.TensorProduct.includeRight (R := B₀) (A := B) (B := P₀.Ring))
        (algebraMap B₀ P₀.Ring x) = algebraMap B (B ⊗[B₀] P₀.Ring) (algebraMap B₀ B x) := by
      rw [AlgHom.commutes]
      exact IsScalarTower.algebraMap_apply B₀ B (B ⊗[B₀] P₀.Ring) x
    simp only [ρ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_ringEquiv, h1]
    exact hiso.commutes _
  -- the image of `Spec C₀ ⟶ Spec B₀` is open and contains the image of `p`
  obtain ⟨q, hq⟩ := hp
  have hmem : PrimeSpectrum.comap (algebraMap B₀ B) (⟨p, inferInstance⟩ : PrimeSpectrum B) ∈
      Set.range (PrimeSpectrum.comap (algebraMap B₀ P₀.Ring)) := by
    refine ⟨PrimeSpectrum.comap ρ q, ?_⟩
    rw [← hq, ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, hρ]
  have hEt : Algebra.Etale B₀ P₀.Ring := inferInstance
  have hFlat : Module.Flat B₀ P₀.Ring := inferInstance
  have hGD : Algebra.HasGoingDown B₀ P₀.Ring := inferInstance
  have hFP : Algebra.FinitePresentation B₀ P₀.Ring := inferInstance
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap B₀ P₀.Ring))) :=
    (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := B₀) (S := P₀.Ring)).isOpen_range
  obtain ⟨v, ⟨a, rfl⟩, hpa, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem hopen
  -- localize so that the spread-out cover becomes faithfully flat
  set b : B := algebraMap B₀ B a with hb
  have hbp : b ∉ p := by
    simpa [hb, PrimeSpectrum.mem_basicOpen, Ideal.mem_comap] using hpa
  refine ⟨b, hbp, ?_⟩
  set B₀' := Localization.Away a with hB₀'
  set B' := B₀' ⊗[B₀] B with hB'
  set C₀' := B₀' ⊗[B₀] P₀.Ring with hC₀'
  -- `B'` and `C₀'` are the corresponding localizations
  have hawayB : IsLocalization.Away b B' := by
    have := IsLocalization.tensorRight (R := B₀) (S := B) B₀' (Submonoid.powers a)
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at this
  have hawayC₀ : IsLocalization.Away (algebraMap B₀ P₀.Ring a) C₀' := by
    have := IsLocalization.tensorRight (R := B₀) (S := P₀.Ring) B₀' (Submonoid.powers a)
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at this
  -- the localized cover is surjective on spectra
  have hsurj' : Function.Surjective (PrimeSpectrum.comap (algebraMap B₀' C₀')) := by
    intro P'
    have haP'' : PrimeSpectrum.comap (algebraMap B₀ B₀') P' ∈
        (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum B₀)) := by
      rw [← PrimeSpectrum.localization_away_comap_range B₀' a]
      exact ⟨P', rfl⟩
    obtain ⟨Q, hQ⟩ := hsub haP''
    have haQ : (algebraMap B₀ P₀.Ring a) ∉ Q.asIdeal := by
      intro hcon
      have h2 : a ∈ (PrimeSpectrum.comap (algebraMap B₀ B₀') P').asIdeal := by
        rw [← hQ]; exact hcon
      exact (PrimeSpectrum.mem_basicOpen a _).mp haP'' h2
    obtain ⟨Q', hQ'⟩ : Q ∈ Set.range (PrimeSpectrum.comap (algebraMap P₀.Ring C₀')) := by
      rw [PrimeSpectrum.localization_away_comap_range C₀' (algebraMap B₀ P₀.Ring a)]
      exact haQ
    refine ⟨Q', ?_⟩
    apply PrimeSpectrum.localization_comap_injective (S := B₀') (Submonoid.powers a)
    rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq B₀ P₀.Ring C₀', PrimeSpectrum.comap_comp_apply, hQ', hQ]
  -- the algebra structures coming from the spread-out data
  let : Algebra B₀ C := ((algebraMap B C).comp (algebraMap B₀ B)).toAlgebra
  have : IsScalarTower B₀ B C := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let : Algebra P₀.Ring C := ρ.toAlgebra
  have : IsScalarTower B₀ P₀.Ring C :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ congrFun (congrArg _ hρ.symm) x)
  set C' := B' ⊗[B] C with hC'def
  let : Algebra P₀.Ring C' := ((algebraMap C C').comp (algebraMap P₀.Ring C)).toAlgebra
  have : IsScalarTower P₀.Ring C C' := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  -- faithful flatness of the localized cover
  have hFF : RingHom.FaithfullyFlat (algebraMap B₀' C₀') :=
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
      ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, hsurj'⟩
  -- the pushout squares
  have hpo₀ : Algebra.IsPushout B₀ B P₀.Ring C :=
    Algebra.IsPushout.of_equiv (R := B₀) (R' := B) (S := P₀.Ring) hiso (by ext x; rfl)
  have : IsScalarTower B₀ P₀.Ring C' :=
    @IsScalarTower.of_algebraMap_eq B₀ P₀.Ring C' _ _ _ _ _ _ fun x ↦ by
    change (algebraMap B₀ B' x) ⊗ₜ[B] (1 : C) = (1 : B') ⊗ₜ[B] (algebraMap P₀.Ring C
      (algebraMap B₀ P₀.Ring x))
    rw [← IsScalarTower.algebraMap_apply B₀ P₀.Ring C,
      IsScalarTower.algebraMap_apply B₀ B C, IsScalarTower.algebraMap_apply B₀ B B',
      tmul_algebraMap_comm]
  let fB : B₀' →ₐ[B₀] C' := IsScalarTower.toAlgHom B₀ B₀' C'
  let gC : P₀.Ring →ₐ[B₀] C' := IsScalarTower.toAlgHom B₀ P₀.Ring C'
  have hcomm : ∀ (x : B₀') (y : P₀.Ring), fB x * gC y = gC y * fB x := fun x y ↦ by
    exact mul_comm (fB x) (gC y)
  let ξ : C₀' →ₐ[B₀] C' := Algebra.pushoutDesc (R := B₀) (S := B₀') (R' := P₀.Ring) C₀' fB gC hcomm
  let : Algebra C₀' C' := @RingHom.toAlgebra C₀' C' _ _ (by exact ξ.toRingHom)
  have htow1 : IsScalarTower B₀' C₀' C' :=
    @IsScalarTower.of_algebraMap_eq B₀' C₀' C' _ _ _ _ _ _ fun x ↦
      (Algebra.pushoutDesc_left (R := B₀) (S := B₀') (R' := P₀.Ring) C₀' fB gC hcomm x).symm
  have htow2 : IsScalarTower P₀.Ring C₀' C' :=
    @IsScalarTower.of_algebraMap_eq P₀.Ring C₀' C' _ _ _ _ _ _ fun x ↦
      (Algebra.pushoutDesc_right (R := B₀) (S := B₀') (R' := P₀.Ring) C₀' fB gC hcomm x).symm
  -- the pushout chain
  have : IsScalarTower B₀ C C' :=
    @IsScalarTower.of_algebraMap_eq B₀ C C' _ _ _ _ _ _ fun x ↦ by
    change (algebraMap B₀ B' x) ⊗ₜ[B] (1 : C) = (1 : B') ⊗ₜ[B] (algebraMap B₀ C x)
    rw [IsScalarTower.algebraMap_apply B₀ B C, IsScalarTower.algebraMap_apply B₀ B B',
      tmul_algebraMap_comm]
  have hpoB : Algebra.IsPushout B₀ B' P₀.Ring C' := by
    rw [Algebra.IsPushout.comp_iff B₀ B P₀.Ring (S' := C) (T := B') (T' := C')]
    infer_instance
  have hpoC : Algebra.IsPushout B₀' B' C₀' C' := by
    rw [← Algebra.IsPushout.comp_iff B₀ B₀' P₀.Ring (S' := C₀') (T := B') (T' := C')]
    exact hpoB
  -- `C'` is a localization of `C`, hence of finite presentation over `A`
  have hawayC' : IsLocalization.Away (algebraMap B C b) C' := by
    have := IsLocalization.tensorRight (R := B) (S := C) B' (Submonoid.powers b)
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at this
  have hfpCC' : Algebra.FinitePresentation C C' := by
    have : IsLocalization.Away (algebraMap B C b) C' := hawayC'
    exact IsLocalization.Away.finitePresentation (S := C') (algebraMap B C b)
  have : IsScalarTower A B B' :=
    @IsScalarTower.of_algebraMap_eq A B B' _ _ _ _ _ _ fun x ↦ by
    change (algebraMap A B₀' x) ⊗ₜ[B₀] (1 : B) = (1 : B₀') ⊗ₜ[B₀] (algebraMap A B x)
    rw [IsScalarTower.algebraMap_apply A B₀ B, IsScalarTower.algebraMap_apply A B₀ B₀',
      tmul_algebraMap_comm]
  have : IsScalarTower A C C' :=
    @IsScalarTower.of_algebraMap_eq A C C' _ _ _ _ _ _ fun x ↦ by
    change (algebraMap A B' x) ⊗ₜ[B] (1 : C) = (1 : B') ⊗ₜ[B] (algebraMap A C x)
    rw [IsScalarTower.algebraMap_apply A B C, IsScalarTower.algebraMap_apply A B B',
      tmul_algebraMap_comm]
  have hQAC' : Q (algebraMap A C') := by
    rw [IsScalarTower.algebraMap_eq A C C']
    exact hQcomp _ _ hQC (hQfp (RingHom.finitePresentation_algebraMap.mpr hfpCC'))
  -- `C₀'` is of finite type over `A`
  have hfpAB₀' : Algebra.FinitePresentation A B₀' := Algebra.FinitePresentation.trans A B₀ B₀'
  have hfpB₀'C₀' : Algebra.FinitePresentation B₀' C₀' := by exact inferInstance
  have hfpAC₀' : Algebra.FinitePresentation A C₀' := Algebra.FinitePresentation.trans A B₀' C₀'
  -- finite presentation of `C₀' ⟶ C'`
  have : IsScalarTower A C₀' C' :=
    @IsScalarTower.of_algebraMap_eq A C₀' C' _ _ _ _ _ _ fun x ↦ by
      rw [IsScalarTower.algebraMap_apply A B₀' C₀', ← IsScalarTower.algebraMap_apply B₀' C₀' C',
        ← IsScalarTower.algebraMap_apply A B₀' C']
  have hQC₀'C' : Q (algebraMap C₀' C') := by
    refine hQcancel (g₁ := algebraMap A C₀') ?_ ?_
    · rw [← IsScalarTower.algebraMap_eq A C₀' C']
      exact hQAC'
    · rw [RingHom.finiteType_algebraMap]
      exact Algebra.FiniteType.of_finitePresentation
  -- the descent step
  have := hpoC
  have hQB₀'B' : Q (algebraMap B₀' B') := hQdescends hFF hQC₀'C'
  have hQAB' : Q (algebraMap A B') := by
    rw [IsScalarTower.algebraMap_eq A B₀' B']
    exact hQcomp _ _ (hQfp (RingHom.finitePresentation_algebraMap.mpr hfpAB₀')) hQB₀'B'
  let eB' : B' ≃ₐ[A] Localization.Away b :=
    (IsLocalization.algEquiv (Submonoid.powers b) B' (Localization.Away b)).restrictScalars A
  have hcompeq : eB'.toRingEquiv.toRingHom.comp (algebraMap A B') =
      algebraMap A (Localization.Away b) := RingHom.ext fun x ↦ eB'.commutes x
  rw [← hcompeq]
  exact hQiso.1 _ _ hQAB'

/-- The key local step for an étale (not necessarily standard étale) cover: localize the cover so
that it becomes standard étale, then apply `exists_away_of_standardEtale`. -/
theorem exists_away_of_etale
    (hQiso : RingHom.RespectsIso Q) (hQcomp : RingHom.StableUnderComposition Q)
    (hQfp : ∀ {R S : Type u} [CommRing R] [CommRing S] {g : R →+* S},
      g.FinitePresentation → Q g)
    (hQcancel : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {g₁ : R →+* S}
      {g₂ : S →+* T}, Q (g₂.comp g₁) → g₁.FiniteType → Q g₂)
    (hQdescends : RingHom.CodescendsAlong Q RingHom.FaithfullyFlat)
    (hQC : Q (algebraMap A C)) [Algebra.Etale B C]
    (p : Ideal B) [p.IsPrime] (q : PrimeSpectrum C)
    (hq : PrimeSpectrum.comap (algebraMap B C) q = ⟨p, inferInstance⟩) :
    ∃ b ∉ p, Q (algebraMap A (Localization.Away b)) := by
  classical
  have : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨s, hsq, hst⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := B) q.asIdeal
  set Cs := Localization.Away s with hCs
  have hQCs : Q (algebraMap A Cs) := by
    have hfp : Algebra.FinitePresentation C Cs := IsLocalization.Away.finitePresentation s
    rw [IsScalarTower.algebraMap_eq A C Cs]
    exact hQcomp _ _ hQC (hQfp (RingHom.finitePresentation_algebraMap.mpr hfp))
  obtain ⟨Ps⟩ := hst.nonempty_standardEtalePresentation
  refine exists_away_of_standardEtale (A := A) (B := B) (C := Cs) hQiso hQcomp hQfp hQcancel
    hQdescends hQCs Ps.P Ps.equivRing p ?_
  obtain ⟨q', hq'⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C Cs)) := by
    rw [PrimeSpectrum.localization_away_comap_range Cs s]
    exact hsq
  refine ⟨q', ?_⟩
  rw [IsScalarTower.algebraMap_eq B C Cs, PrimeSpectrum.comap_comp_apply, hq', hq]

/-- A property which is local on the target glues from a covering family of basic opens. -/
theorem of_forall_exists_away (hQlocal : RingHom.OfLocalizationSpanTarget Q)
    (h : ∀ p : PrimeSpectrum B, ∃ b ∉ p.asIdeal, Q (algebraMap A (Localization.Away b))) :
    Q (algebraMap A B) := by
  classical
  choose b hb hfp using h
  refine hQlocal (algebraMap A B) (Set.range b) ?_ ?_
  · by_contra hcon
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hcon
    exact hb ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨⟨m, hm.isPrime⟩, rfl⟩))
  · rintro ⟨r, p, rfl⟩
    rw [← IsScalarTower.algebraMap_eq A B (Localization.Away (b p))]
    exact hfp p

/-- Source descent along a surjective étale ring map for any property `Q` as above. -/
theorem of_etale_of_surjective
    (hQiso : RingHom.RespectsIso Q) (hQcomp : RingHom.StableUnderComposition Q)
    (hQfp : ∀ {R S : Type u} [CommRing R] [CommRing S] {g : R →+* S},
      g.FinitePresentation → Q g)
    (hQcancel : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {g₁ : R →+* S}
      {g₂ : S →+* T}, Q (g₂.comp g₁) → g₁.FiniteType → Q g₂)
    (hQdescends : RingHom.CodescendsAlong Q RingHom.FaithfullyFlat)
    (hQlocal : RingHom.OfLocalizationSpanTarget Q)
    (hQC : Q (algebraMap A C)) [Algebra.Etale B C]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B C))) :
    Q (algebraMap A B) := by
  refine of_forall_exists_away (A := A) (B := B) hQlocal fun p ↦ ?_
  obtain ⟨q, hq⟩ := hsurj p
  have : p.asIdeal.IsPrime := p.isPrime
  exact exists_away_of_etale (C := C) hQiso hQcomp hQfp hQcancel hQdescends hQC p.asIdeal q hq

/-- Finite presentation descends along a surjective étale ring map. -/
theorem finitePresentation_of_etale_of_surjective
    [Algebra.Etale B C] [Algebra.FinitePresentation A C]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B C))) :
    Algebra.FinitePresentation A B := by
  rw [← RingHom.finitePresentation_algebraMap]
  exact of_etale_of_surjective (C := C) RingHom.finitePresentation_respectsIso
    RingHom.finitePresentation_stableUnderComposition (fun h ↦ h)
    (fun h h₁ ↦ RingHom.FinitePresentation.of_comp_finiteType _ h h₁)
    RingHom.FinitePresentation.codescendsAlong_faithfullyFlat
    RingHom.finitePresentation_ofLocalizationSpanTarget
    (RingHom.finitePresentation_algebraMap.mpr inferInstance) hsurj

/-- Finite type descends along a surjective étale ring map. -/
theorem finiteType_of_etale_of_surjective
    [Algebra.Etale B C] [Algebra.FiniteType A C]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B C))) :
    Algebra.FiniteType A B := by
  rw [← RingHom.finiteType_algebraMap]
  exact of_etale_of_surjective (C := C) RingHom.finiteType_respectsIso
    RingHom.finiteType_stableUnderComposition (fun h ↦ RingHom.FiniteType.of_finitePresentation h)
    (fun h _ ↦ RingHom.FiniteType.of_comp_finiteType h)
    RingHom.FiniteType.codescendsAlong_faithfullyFlat
    RingHom.finiteType_ofLocalizationSpanTarget
    (RingHom.finiteType_algebraMap.mpr inferInstance) hsurj

/-- Source descent along a surjective étale morphism of schemes, for a morphism property `P`
induced by a ring-hom property `Q` satisfying the five closure conditions of
`exists_away_of_standardEtale`.

Affine-locally, a point of the source is covered by an affine open of `Y` whose coordinate ring is
an étale `Γ(X, V)`-algebra carrying a prime over the given one, and `exists_away_of_etale`
supplies a basic open of `Spec Γ(X, V)` on which `Q` holds; these glue by
`of_forall_exists_away`. -/
theorem of_precomp_surjective_etale_of_hasRingHomProperty
    {P : MorphismProperty Scheme.{u}} [HasRingHomProperty P Q]
    (hQiso : RingHom.RespectsIso Q) (hQcomp : RingHom.StableUnderComposition Q)
    (hQfp : ∀ {R S : Type u} [CommRing R] [CommRing S] {g : R →+* S},
      g.FinitePresentation → Q g)
    (hQcancel : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {g₁ : R →+* S}
      {g₂ : S →+* T}, Q (g₂.comp g₁) → g₁.FiniteType → Q g₂)
    (hQdescends : RingHom.CodescendsAlong Q RingHom.FaithfullyFlat)
    (hQlocal : RingHom.OfLocalizationSpanTarget Q)
    {X S Y : Scheme.{u}}
    (e : Y ⟶ X) (f : X ⟶ S) (he : Etale e) (hsurj : Surjective e)
    (hcomp : P (e ≫ f)) : P f := by
  let _ : Etale e := he
  let _ : Surjective e := hsurj
  let _ : P (e ≫ f) := hcomp
  rw [HasRingHomProperty.iff_appLE (P := P)]
  rintro ⟨U, hU⟩ ⟨V, hV⟩ hVU
  algebraize [(f.appLE U V hVU).hom]
  apply of_forall_exists_away hQlocal
  intro p
  -- the point of `V` corresponding to the prime `p`
  set x := hV.isoSpec.inv p with hxdef
  have hpx : hV.primeIdealOf x = p := by
    change hV.isoSpec.hom (hV.isoSpec.inv p) = p
    have h2 : (hV.isoSpec.inv ≫ hV.isoSpec.hom) p = hV.isoSpec.hom (hV.isoSpec.inv p) :=
      Scheme.Hom.comp_apply _ _ _
    rw [← h2, hV.isoSpec.inv_hom_id]
    rfl
  obtain ⟨y, hy⟩ := e.surjective x.1
  have hyV : y ∈ e ⁻¹ᵁ (V : X.Opens) := by
    change e.base y ∈ (V : X.Opens)
    rw [hy]
    exact x.2
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset hyV
  have hWV' : W ≤ e ⁻¹ᵁ (V : X.Opens) := hWV
  have hWU : W ≤ (e ≫ f) ⁻¹ᵁ (U : S.Opens) := fun z hz ↦ hVU (hWV' hz)
  have hetale : RingHom.Etale (e.appLE (V : X.Opens) W hWV').hom :=
    HasRingHomProperty.appLE (P := @Etale) (f := e) inferInstance ⟨V, hV⟩ ⟨W, hW⟩ hWV'
  have hfpC : Q ((e ≫ f).appLE (U : S.Opens) W hWU).hom :=
    HasRingHomProperty.appLE (P := P) (f := e ≫ f) hcomp ⟨U, hU⟩ ⟨W, hW⟩ hWU
  have hcompLE : ((e ≫ f).appLE (U : S.Opens) W hWU).hom =
      (e.appLE (V : X.Opens) W hWV').hom.comp (f.appLE (U : S.Opens) (V : X.Opens) hVU).hom := by
    rw [← Scheme.Hom.appLE_comp_appLE e f (U : S.Opens) (V : X.Opens) W hVU hWV']
    rfl
  rw [hcompLE] at hfpC
  algebraize [(e.appLE (V : X.Opens) W hWV').hom,
    ((e.appLE (V : X.Opens) W hWV').hom.comp (f.appLE (U : S.Opens) (V : X.Opens) hVU).hom)]
  refine exists_away_of_etale (C := Γ(Y, W)) hQiso hQcomp hQfp hQcancel hQdescends hfpC p.asIdeal
    (hW.primeIdealOf ⟨y, hyW⟩) ?_
  have := IsAffineOpen.comap_primeIdealOf_appLE (f := e) (x := y) (V : X.Opens) hV W hW hWV' hyW
  rw [show (algebraMap Γ(X, (V : X.Opens)) Γ(Y, W)) = (e.appLE (V : X.Opens) W hWV').hom from rfl,
    this]
  have hxy : (⟨e.base y, hWV' hyW⟩ : (V : X.Opens)) = x := Subtype.ext hy
  rw [hxy, hpx]

/-- Finite presentation descends along a surjective étale cover of the source: this is descent of
finite presentation along a *source* cover (Stacks 02JS, 036M), which the pinned Mathlib does not
provide, proved here for étale covers. -/
theorem locallyOfFinitePresentation_of_precomp_surjective_etale {X S Y : Scheme.{u}}
    (e : Y ⟶ X) (f : X ⟶ S) (he : Etale e) (hsurj : Surjective e)
    (hcomp : LocallyOfFinitePresentation (e ≫ f)) : LocallyOfFinitePresentation f :=
  of_precomp_surjective_etale_of_hasRingHomProperty RingHom.finitePresentation_respectsIso
    RingHom.finitePresentation_stableUnderComposition (fun h ↦ h)
    (fun h h₁ ↦ RingHom.FinitePresentation.of_comp_finiteType _ h h₁)
    RingHom.FinitePresentation.codescendsAlong_faithfullyFlat
    RingHom.finitePresentation_ofLocalizationSpanTarget e f he hsurj hcomp

/-- Local finite typeness descends along a surjective étale cover of the source. -/
theorem locallyOfFiniteType_of_precomp_surjective_etale {X S Y : Scheme.{u}}
    (e : Y ⟶ X) (f : X ⟶ S) (he : Etale e) (hsurj : Surjective e)
    (hcomp : LocallyOfFiniteType (e ≫ f)) : LocallyOfFiniteType f :=
  of_precomp_surjective_etale_of_hasRingHomProperty RingHom.finiteType_respectsIso
    RingHom.finiteType_stableUnderComposition (fun h ↦ RingHom.FiniteType.of_finitePresentation h)
    (fun h _ ↦ RingHom.FiniteType.of_comp_finiteType h)
    RingHom.FiniteType.codescendsAlong_faithfullyFlat
    RingHom.finiteType_ofLocalizationSpanTarget e f he hsurj hcomp

end FinitePresentationDescent


/-- A locally finite-type morphism has geometric relative dimension at most `d` when every
base change along every field-valued point has topological dimension at most `d`. -/
def GeometricRelativeDimensionLE (d : ℕ) (f : X ⟶ S) : Prop :=
  LocallyOfFiniteType f ∧ geometrically (TopologicalDimensionLE d) f

/-- A locally finite-type morphism has geometric pure relative dimension `d` when every
irreducible component after every field-valued base change has dimension `d`. -/
def GeometricPureRelativeDimension (d : ℕ) (f : X ⟶ S) : Prop :=
  LocallyOfFiniteType f ∧ geometrically (PureTopologicalDimension d) f

namespace GeometricRelativeDimensionLE

theorem precomp_iso {Y : Scheme.{u}} {d : ℕ} (e : X ≅ Y) (f : Y ⟶ S)
    (h : GeometricRelativeDimensionLE d f) :
    GeometricRelativeDimensionLE d (e.hom ≫ f) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, ?_⟩
  let a : Arrow.mk (e.hom ≫ f) ≅ Arrow.mk f :=
    Arrow.isoMk e (Iso.refl _) (by simp)
  exact (MorphismProperty.arrow_mk_iso_iff
    (P := geometrically (TopologicalDimensionLE d)) a).mpr h.2

theorem postcomp_iso {Y : Scheme.{u}} {d : ℕ} (f : X ⟶ Y) (e : Y ≅ S)
    (h : GeometricRelativeDimensionLE d f) :
    GeometricRelativeDimensionLE d (f ≫ e.hom) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, ?_⟩
  let a : Arrow.mk (f ≫ e.hom) ≅ Arrow.mk f :=
    Arrow.isoMk (Iso.refl _) e.symm (by simp)
  exact (MorphismProperty.arrow_mk_iso_iff
    (P := geometrically (TopologicalDimensionLE d)) a).mpr h.2

instance (d : ℕ) : MorphismProperty.RespectsIso (C := Scheme.{u})
    (fun {_ _} f ↦ GeometricRelativeDimensionLE d f) :=
  MorphismProperty.RespectsIso.mk _
    (fun e f h ↦ precomp_iso e f h)
    (fun e f h ↦ postcomp_iso f e h)

theorem locallyOfFiniteType {d : ℕ} {f : X ⟶ S} (h : GeometricRelativeDimensionLE d f) :
    LocallyOfFiniteType f := h.1

/-- Geometric relative dimension implies the corresponding residue-fibre bound. -/
theorem toRelativeDimensionLE {d : ℕ} {f : X ⟶ S}
    (h : GeometricRelativeDimensionLE d f) : RelativeDimensionLE d f :=
  ⟨h.1, fun s ↦ fiber_of_geometrically h.2 s⟩

/-- Geometric relative dimension is preserved by arbitrary chosen base change. -/
theorem pullback_snd {d : ℕ} {f : X ⟶ S} (h : GeometricRelativeDimensionLE d f)
    {T : Scheme.{u}} (b : T ⟶ S) :
    GeometricRelativeDimensionLE d (pullback.snd f b) := by
  let _ : LocallyOfFiniteType f := h.1
  exact ⟨by infer_instance, (geometrically (TopologicalDimensionLE d)).pullback_snd f b h.2⟩

/-- Precomposition by an immersion does not increase geometric relative dimension.  This is
the relative-dimension composition bound in the zero-dimensional immersion case. -/
theorem precomp_immersion {Y : Scheme.{u}} {d : ℕ}
    (j : Y ⟶ X) [IsImmersion j] (f : X ⟶ S)
    (h : GeometricRelativeDimensionLE d f) :
    GeometricRelativeDimensionLE d (j ≫ f) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, ?_⟩
  intro K _ y Z fst snd hsquare
  let P := pullback f y
  let p : Z ⟶ P := pullback.lift (fst ≫ j) snd (by
    rw [Category.assoc]
    exact hsquare.w)
  have hpFst : p ≫ pullback.fst f y = fst ≫ j := pullback.lift_fst _ _ _
  have hpSnd : p ≫ pullback.snd f y = snd := pullback.lift_snd _ _ _
  have houter : IsPullback fst (p ≫ pullback.snd f y) (j ≫ f) y := by
    simpa only [hpSnd] using hsquare
  have htop : IsPullback fst p j (pullback.fst f y) :=
    IsPullback.of_bot houter hpFst.symm (IsPullback.of_hasPullback f y)
  have hpImmersion : IsImmersion p :=
    MorphismProperty.of_isPullback (P := @IsImmersion) htop inferInstance
  let _ : IsImmersion p := hpImmersion
  exact p.isEmbedding.isInducing.topologicalKrullDim_le.trans
    (pullback_of_geometrically h.2 K y)

/-- In particular, restricting the source to an open subscheme preserves geometric relative
dimension. -/
theorem precomp_openImmersion {Y : Scheme.{u}} {d : ℕ}
    (j : Y ⟶ X) [IsOpenImmersion j] (f : X ⟶ S)
    (h : GeometricRelativeDimensionLE d f) :
    GeometricRelativeDimensionLE d (j ≫ f) :=
  precomp_immersion j f h

/-- The source-open form of `precomp_openImmersion`. -/
theorem restrictSource {d : ℕ} (f : X ⟶ S) (U : X.Opens)
    (h : GeometricRelativeDimensionLE d f) :
    GeometricRelativeDimensionLE d (U.ι ≫ f) :=
  precomp_openImmersion U.ι f h

/-- Geometric relative dimension can be checked on an open cover of the source. -/
theorem of_source_iSup_eq_top {d : ℕ} (f : X ⟶ S) {I : Type u}
    (U : I → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, GeometricRelativeDimensionLE d ((U i).ι ≫ f)) :
    GeometricRelativeDimensionLE d f := by
  let _ : IsZariskiLocalAtSource (fun {_ _} g ↦ LocallyOfFiniteType g) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource
  have hlft : LocallyOfFiniteType f :=
    IsZariskiLocalAtSource.of_iSup_eq_top U hU (fun i ↦ (h i).1)
  refine ⟨hlft, ?_⟩
  intro K _ y Z fst snd hsquare
  apply topologicalKrullDim_le_of_openCover
    (g := fun i ↦ (fst ⁻¹ᵁ U i).ι)
    (hg := fun i ↦ (fst ⁻¹ᵁ U i).ι.isOpenEmbedding)
    (hd := fun i ↦ ?_)
  · apply Set.eq_univ_iff_forall.mpr
    intro z
    have hz : fst z ∈ (⨆ i, U i : X.Opens) := by rw [hU]; trivial
    obtain ⟨i, hzi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    apply Set.mem_iUnion.mpr
    exact ⟨i, ⟨⟨z, hzi⟩, rfl⟩⟩
  · exact (h i).2 y (fst ∣_ U i) ((fst ⁻¹ᵁ U i).ι ≫ snd)
      ((isPullback_morphismRestrict fst (U i)).paste_vert hsquare)

/-- Geometric relative dimension at most `d` holds exactly when it holds on every member of a
source-open cover. -/
theorem iff_of_source_iSup_eq_top {d : ℕ} (f : X ⟶ S) {I : Type u}
    (U : I → X.Opens) (hU : iSup U = ⊤) :
    GeometricRelativeDimensionLE d f ↔
      ∀ i, GeometricRelativeDimensionLE d ((U i).ι ≫ f) :=
  ⟨fun h i ↦ restrictSource f (U i) h, of_source_iSup_eq_top f U hU⟩

instance (d : ℕ) :
    IsZariskiLocalAtSource (fun {_ _} f ↦ GeometricRelativeDimensionLE d f) := by
  apply IsZariskiLocalAtSource.mk'
  · exact fun f U h ↦ restrictSource f U h
  · exact of_source_iSup_eq_top

/-- Geometric relative dimension is preserved by restricting the target to an open
subscheme. -/
theorem restrict {d : ℕ} (f : X ⟶ S) (U : S.Opens)
    (h : GeometricRelativeDimensionLE d f) :
    GeometricRelativeDimensionLE d (f ∣_ U) := by
  let _ : LocallyOfFiniteType f := h.1
  exact ⟨by infer_instance, IsZariskiLocalAtTarget.restrict h.2 U⟩

/-- Geometric relative dimension can be checked on an open cover of the target. -/
theorem of_iSup_eq_top {d : ℕ} (f : X ⟶ S) {ι : Type u} (U : ι → S.Opens)
    (hU : iSup U = ⊤) (h : ∀ i, GeometricRelativeDimensionLE d (f ∣_ U i)) :
    GeometricRelativeDimensionLE d f := by
  let _ : IsZariskiLocalAtTarget (fun {_ _} g ↦ LocallyOfFiniteType g) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact
    ⟨IsZariskiLocalAtTarget.of_iSup_eq_top U hU (fun i ↦ (h i).1),
      IsZariskiLocalAtTarget.of_iSup_eq_top U hU (fun i ↦ (h i).2)⟩

instance (d : ℕ) :
    IsZariskiLocalAtTarget (fun {_ _} f ↦ GeometricRelativeDimensionLE d f) := by
  apply IsZariskiLocalAtTarget.mk'
  · exact restrict
  · exact of_iSup_eq_top

instance (d : ℕ) : MorphismProperty.IsStableUnderBaseChange
    (fun {_ _} f ↦ GeometricRelativeDimensionLE d f) := by
  constructor
  intro X Y Y' S f g f' g' h hf
  show GeometricRelativeDimensionLE d g'
  have hc := pullback_snd hf f
  have hi := precomp_iso h.isoPullback (pullback.snd g f) hc
  simpa only [h.isoPullback_hom_snd] using hi

end GeometricRelativeDimensionLE

namespace GeometricPureRelativeDimension

theorem precomp_iso {Y : Scheme.{u}} {d : ℕ} (e : X ≅ Y) (f : Y ⟶ S)
    (h : GeometricPureRelativeDimension d f) :
    GeometricPureRelativeDimension d (e.hom ≫ f) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, ?_⟩
  let a : Arrow.mk (e.hom ≫ f) ≅ Arrow.mk f :=
    Arrow.isoMk e (Iso.refl _) (by simp)
  exact (MorphismProperty.arrow_mk_iso_iff
    (P := geometrically (PureTopologicalDimension d)) a).mpr h.2

theorem postcomp_iso {Y : Scheme.{u}} {d : ℕ} (f : X ⟶ Y) (e : Y ≅ S)
    (h : GeometricPureRelativeDimension d f) :
    GeometricPureRelativeDimension d (f ≫ e.hom) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, ?_⟩
  let a : Arrow.mk (f ≫ e.hom) ≅ Arrow.mk f :=
    Arrow.isoMk (Iso.refl _) e.symm (by simp)
  exact (MorphismProperty.arrow_mk_iso_iff
    (P := geometrically (PureTopologicalDimension d)) a).mpr h.2

instance (d : ℕ) : MorphismProperty.RespectsIso (C := Scheme.{u})
    (fun {_ _} f ↦ GeometricPureRelativeDimension d f) :=
  MorphismProperty.RespectsIso.mk _
    (fun e f h ↦ precomp_iso e f h)
    (fun e f h ↦ postcomp_iso f e h)

theorem locallyOfFiniteType {d : ℕ} {f : X ⟶ S}
    (h : GeometricPureRelativeDimension d f) : LocallyOfFiniteType f := h.1

/-- Geometric pure relative dimension implies the corresponding residue-fibre assertion. -/
theorem toPureRelativeDimension {d : ℕ} {f : X ⟶ S}
    (h : GeometricPureRelativeDimension d f) : PureRelativeDimension d f :=
  ⟨h.1, fun s ↦ fiber_of_geometrically h.2 s⟩

/-- Geometric pure relative dimension is preserved by arbitrary chosen base change. -/
theorem pullback_snd {d : ℕ} {f : X ⟶ S} (h : GeometricPureRelativeDimension d f)
    {T : Scheme.{u}} (b : T ⟶ S) :
    GeometricPureRelativeDimension d (pullback.snd f b) := by
  let _ : LocallyOfFiniteType f := h.1
  exact ⟨by infer_instance, (geometrically (PureTopologicalDimension d)).pullback_snd f b h.2⟩

/-- Geometric pure relative dimension is preserved by restricting the target to an open
subscheme. -/
theorem restrict {d : ℕ} (f : X ⟶ S) (U : S.Opens)
    (h : GeometricPureRelativeDimension d f) :
    GeometricPureRelativeDimension d (f ∣_ U) := by
  let _ : LocallyOfFiniteType f := h.1
  exact ⟨by infer_instance, IsZariskiLocalAtTarget.restrict h.2 U⟩

/-- Geometric pure relative dimension can be checked on an open cover of the target. -/
theorem of_iSup_eq_top {d : ℕ} (f : X ⟶ S) {ι : Type u} (U : ι → S.Opens)
    (hU : iSup U = ⊤) (h : ∀ i, GeometricPureRelativeDimension d (f ∣_ U i)) :
    GeometricPureRelativeDimension d f := by
  let _ : IsZariskiLocalAtTarget (fun {_ _} g ↦ LocallyOfFiniteType g) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact
    ⟨IsZariskiLocalAtTarget.of_iSup_eq_top U hU (fun i ↦ (h i).1),
      IsZariskiLocalAtTarget.of_iSup_eq_top U hU (fun i ↦ (h i).2)⟩

instance (d : ℕ) :
    IsZariskiLocalAtTarget (fun {_ _} f ↦ GeometricPureRelativeDimension d f) := by
  apply IsZariskiLocalAtTarget.mk'
  · exact restrict
  · exact of_iSup_eq_top

instance (d : ℕ) : MorphismProperty.IsStableUnderBaseChange
    (fun {_ _} f ↦ GeometricPureRelativeDimension d f) := by
  constructor
  intro X Y Y' S f g f' g' h hf
  show GeometricPureRelativeDimension d g'
  have hc := pullback_snd hf f
  have hi := precomp_iso h.isoPullback (pullback.snd g f) hc
  simpa only [h.isoPullback_hom_snd] using hi

/-- Geometric pure relative dimension descends along a surjective étale cover of the source.

Both halves descend: local finite typeness by
`locallyOfFiniteType_of_precomp_surjective_etale`, and the geometric clause by pulling the cover
back into each chosen geometric fibre, where `pureTopologicalDimension_of_surjective_etale`
applies. -/
theorem of_precomp_surjective_etale {Y : Scheme.{u}} {d : ℕ}
    (e : Y ⟶ X) (f : X ⟶ S) (he : Etale e) (hsurj : Surjective e)
    (h : GeometricPureRelativeDimension d (e ≫ f)) :
    GeometricPureRelativeDimension d f := by
  let _ : Etale e := he
  let _ : Surjective e := hsurj
  refine ⟨locallyOfFiniteType_of_precomp_surjective_etale e f he hsurj h.1, ?_⟩
  intro K _ y Z fst snd hsquare
  let q : pullback e fst ⟶ Z := pullback.snd e fst
  have hqEtale : Etale q := by
    dsimp [q]
    infer_instance
  have hqSurjective : Surjective q := by
    dsimp [q]
    infer_instance
  have hcovered : PureTopologicalDimension d (pullback e fst) :=
    h.2 y (pullback.fst e fst) (q ≫ snd)
      ((IsPullback.of_hasPullback e fst).paste_vert hsquare)
  exact pureTopologicalDimension_of_surjective_etale q hcovered

end GeometricPureRelativeDimension

namespace RelativeDimensionLE

theorem locallyOfFiniteType {d : ℕ} {f : X ⟶ S} (h : RelativeDimensionLE d f) :
    LocallyOfFiniteType f := h.1

theorem fiber_le {d : ℕ} {f : X ⟶ S} (h : RelativeDimensionLE d f) (s : S) :
    topologicalKrullDim (f.fiber s) ≤ d := h.2 s

theorem mono {d e : ℕ} {f : X ⟶ S} (h : RelativeDimensionLE d f) (hde : d ≤ e) :
    RelativeDimensionLE e f := by
  refine ⟨h.1, fun s ↦ (h.2 s).trans ?_⟩
  exact_mod_cast hde

/-- Relative dimension at most `d` is invariant under an isomorphism of sources. -/
theorem precomp_iso {Y : Scheme.{u}} {d : ℕ} (e : X ≅ Y) (f : Y ⟶ S)
    (h : RelativeDimensionLE d f) : RelativeDimensionLE d (e.hom ≫ f) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, fun s ↦ ?_⟩
  rw [(fiberHomeomorphPrecompIso e f s).isHomeomorph.topologicalKrullDim_eq]
  exact h.2 s

/-- Relative dimension at most `d` is invariant under an isomorphism of targets. -/
theorem postcomp_iso {Y : Scheme.{u}} {d : ℕ} (f : X ⟶ Y) (e : Y ≅ S)
    (h : RelativeDimensionLE d f) : RelativeDimensionLE d (f ≫ e.hom) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, fun s ↦ ?_⟩
  rw [(fiberHomeomorphPostcompIso f e s).isHomeomorph.topologicalKrullDim_eq]
  exact h.2 (e.inv s)

instance (d : ℕ) : MorphismProperty.RespectsIso (C := Scheme.{u})
    (fun {_ _} f ↦ RelativeDimensionLE d f) :=
  MorphismProperty.RespectsIso.mk _
    (fun e f h ↦ precomp_iso e f h)
    (fun e f h ↦ postcomp_iso f e h)

/-- The identity has relative dimension zero. -/
theorem id_zero (X : Scheme.{u}) : RelativeDimensionLE 0 (𝟙 X) := by
  refine ⟨by infer_instance, fun x ↦ ?_⟩
  let e := Scheme.Hom.fiberHomeo (𝟙 X) x
  rw [e.isHomeomorph.topologicalKrullDim_eq]
  let _ : Subsingleton ((𝟙 X : X ⟶ X) ⁻¹' {x}) := by
    constructor
    intro a b
    apply Subtype.ext
    have ha : (𝟙 X : X ⟶ X) (a : X) = a := rfl
    have hb : (𝟙 X : X ⟶ X) (b : X) = b := rfl
    exact ha.symm.trans (a.property.trans b.property.symm) |>.trans hb
  exact topologicalKrullDim_zero_of_discreteTopology _

/-- The identity has relative dimension at most every natural number. -/
theorem id (d : ℕ) (X : Scheme.{u}) : RelativeDimensionLE d (𝟙 X) :=
  (id_zero X).mono (Nat.zero_le d)

/-- Base change along an isomorphism preserves the relative-dimension bound.  Unlike arbitrary
base change, this needs no theorem about Krull dimension after extending residue fields. -/
theorem pullback_snd_of_isIso {d : ℕ} {f : X ⟶ S} (h : RelativeDimensionLE d f)
    {T : Scheme.{u}} (b : T ⟶ S) [IsIso b] :
    RelativeDimensionLE d (pullback.snd f b) := by
  let e : Arrow.mk (pullback.snd f b) ≅ Arrow.mk f :=
    Arrow.isoMk (asIso (pullback.fst f b)) (asIso b) pullback.condition
  exact (MorphismProperty.arrow_mk_iso_iff
    (P := fun {_ _} g ↦ RelativeDimensionLE d g) e).mpr h

/-- The bound is preserved by restricting the target to an open subscheme. -/
theorem restrict {d : ℕ} (f : X ⟶ S) (U : S.Opens) (h : RelativeDimensionLE d f) :
    RelativeDimensionLE d (f ∣_ U) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, fun s ↦ ?_⟩
  rw [(fiberHomeomorphRestrict f U s).isHomeomorph.topologicalKrullDim_eq]
  exact h.2 (U.ι s)

/-- Precomposition by an immersion cannot increase relative dimension. -/
theorem precomp_immersion {Y : Scheme.{u}} {d : ℕ} (j : Y ⟶ X) [IsImmersion j]
    (f : X ⟶ S) (h : RelativeDimensionLE d f) : RelativeDimensionLE d (j ≫ f) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, fun s ↦ ?_⟩
  exact (fiberMapPrecomp j f s).isEmbedding.isInducing.topologicalKrullDim_le.trans (h.2 s)

/-- Restricting the source to an open subscheme cannot increase relative dimension. -/
theorem precomp_openImmersion {Y : Scheme.{u}} {d : ℕ} (j : Y ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ S) (h : RelativeDimensionLE d f) : RelativeDimensionLE d (j ≫ f) :=
  precomp_immersion j f h

/-- The source-open form of `precomp_openImmersion`. -/
theorem restrictSource {d : ℕ} (f : X ⟶ S) (U : X.Opens) (h : RelativeDimensionLE d f) :
    RelativeDimensionLE d (U.ι ≫ f) :=
  precomp_openImmersion U.ι f h

/-- The relative-dimension bound can be checked on an open cover of the source. -/
theorem of_source_iSup_eq_top {d : ℕ} (f : X ⟶ S) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, RelativeDimensionLE d ((U i).ι ≫ f)) :
    RelativeDimensionLE d f := by
  let _ : IsZariskiLocalAtSource (fun {_ _} g ↦ LocallyOfFiniteType g) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource
  have hlft : LocallyOfFiniteType f :=
    IsZariskiLocalAtSource.of_iSup_eq_top U hU (fun i ↦ (h i).1)
  refine ⟨hlft, fun s ↦ ?_⟩
  apply topologicalKrullDim_le_of_openCover
    (g := fun i ↦ fiberMapPrecomp (U i).ι f s)
    (hg := fun i ↦ (fiberMapPrecomp (U i).ι f s).isOpenEmbedding)
    (hd := fun i ↦ (h i).2 s)
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hx : f.fiberι s x ∈ (⨆ i, U i : X.Opens) := by rw [hU]; trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [fiberMapPrecomp_range]
  exact ⟨⟨f.fiberι s x, hxi⟩, rfl⟩

/-- Relative dimension at most `d` holds exactly when it holds on every member of a source-open
cover. -/
theorem iff_of_source_iSup_eq_top {d : ℕ} (f : X ⟶ S) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) :
    RelativeDimensionLE d f ↔ ∀ i, RelativeDimensionLE d ((U i).ι ≫ f) :=
  ⟨fun h i ↦ restrictSource f (U i) h, of_source_iSup_eq_top f U hU⟩

instance (d : ℕ) :
    IsZariskiLocalAtSource (fun {_ _} f ↦ RelativeDimensionLE d f) := by
  apply IsZariskiLocalAtSource.mk'
  · exact fun f U h ↦ restrictSource f U h
  · exact of_source_iSup_eq_top

/-- The relative-dimension bound can be checked on an open cover of the target. -/
theorem of_iSup_eq_top {d : ℕ} (f : X ⟶ S) {ι : Type u} (U : ι → S.Opens)
    (hU : iSup U = ⊤) (h : ∀ i, RelativeDimensionLE d (f ∣_ U i)) :
    RelativeDimensionLE d f := by
  let _ : IsZariskiLocalAtTarget (fun {_ _} g ↦ LocallyOfFiniteType g) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget _
  have hlft : LocallyOfFiniteType f :=
    IsZariskiLocalAtTarget.of_iSup_eq_top U hU (fun i ↦ (h i).1)
  refine ⟨hlft, fun s ↦ ?_⟩
  have hs : s ∈ (⨆ i, U i : S.Opens) := by rw [hU]; trivial
  obtain ⟨i, hsi⟩ := TopologicalSpace.Opens.mem_iSup.mp hs
  let sU : U i := ⟨s, hsi⟩
  have hd := (h i).2 sU
  rw [(fiberHomeomorphRestrict f (U i) sU).isHomeomorph.topologicalKrullDim_eq] at hd
  exact hd

instance (d : ℕ) :
    IsZariskiLocalAtTarget (fun {_ _} f ↦ RelativeDimensionLE d f) := by
  apply IsZariskiLocalAtTarget.mk'
  · exact restrict
  · exact of_iSup_eq_top

/-- Chosen base change along a residue-field-preserving map preserves the relative-dimension
bound. -/
theorem pullback_snd_of_preservesResidueFields {d : ℕ} {f : X ⟶ S}
    (h : RelativeDimensionLE d f) {T : Scheme.{u}} (b : T ⟶ S)
    [PreservesResidueFields b] :
    RelativeDimensionLE d (pullback.snd f b) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, fun t ↦ ?_⟩
  let k := fiberMapBaseChange f b t
  have hk : IsIso k := fiberMapBaseChange_isIso_of_preservesResidueFields f b t
  rw [(asIso k).schemeIsoToHomeo.isHomeomorph.topologicalKrullDim_eq]
  exact h.2 (b t)

/-- Chosen base change along a preimmersion preserves the relative-dimension bound. -/
theorem pullback_snd_of_isPreimmersion {d : ℕ} {f : X ⟶ S}
    (h : RelativeDimensionLE d f) {T : Scheme.{u}} (b : T ⟶ S) [IsPreimmersion b] :
    RelativeDimensionLE d (pullback.snd f b) :=
  pullback_snd_of_preservesResidueFields h b

/-- The fibre over a point, viewed over its residue field, retains the relative-dimension
bound. -/
theorem fiberToSpecResidueField {d : ℕ} {f : X ⟶ S}
    (h : RelativeDimensionLE d f) (s : S) :
    RelativeDimensionLE d (f.fiberToSpecResidueField s) :=
  pullback_snd_of_isPreimmersion h (S.fromSpecResidueField s)

/-- Relative dimension at most `d` is stable under every Cartesian base-change square whose
base map preserves residue fields. -/
instance (d : ℕ) {T S : Scheme.{u}} (b : T ⟶ S) [PreservesResidueFields b] :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (fun {_ _} f ↦ RelativeDimensionLE d f) b where
  of_isPullback h hf := by
    have hc := pullback_snd_of_preservesResidueFields hf b
    have hi := precomp_iso h.isoPullback (pullback.snd _ b) hc
    simpa only [h.isoPullback_hom_snd] using hi

/-- Chosen-pullback base change along an open immersion preserves the relative-dimension
bound. -/
theorem pullback_snd_of_isOpenImmersion {d : ℕ} {f : X ⟶ S}
    (h : RelativeDimensionLE d f) {T : Scheme.{u}} (b : T ⟶ S) [IsOpenImmersion b] :
    RelativeDimensionLE d (pullback.snd f b) :=
  pullback_snd_of_isPreimmersion h b

end RelativeDimensionLE

namespace PureRelativeDimension

theorem locallyOfFiniteType {d : ℕ} {f : X ⟶ S} (h : PureRelativeDimension d f) :
    LocallyOfFiniteType f := h.1

theorem component_dimension {d : ℕ} {f : X ⟶ S} (h : PureRelativeDimension d f)
    (s : S) (Z : Set (f.fiber s)) (hZ : Z ∈ irreducibleComponents (f.fiber s)) :
    topologicalKrullDim Z = d := h.2 s Z hZ

/-- Pure relative dimension is invariant under an isomorphism of sources. -/
theorem precomp_iso {Y : Scheme.{u}} {d : ℕ} (e : X ≅ Y) (f : Y ⟶ S)
    (h : PureRelativeDimension d f) : PureRelativeDimension d (e.hom ≫ f) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, fun s ↦ ?_⟩
  exact pureTopologicalDimensionOfHomeomorph (fiberHomeomorphPrecompIso e f s) (h.2 s)

/-- Pure relative dimension is invariant under an isomorphism of targets. -/
theorem postcomp_iso {Y : Scheme.{u}} {d : ℕ} (f : X ⟶ Y) (e : Y ≅ S)
    (h : PureRelativeDimension d f) : PureRelativeDimension d (f ≫ e.hom) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, fun s ↦ ?_⟩
  exact pureTopologicalDimensionOfHomeomorph
    (fiberHomeomorphPostcompIso f e s) (h.2 (e.inv s))

instance (d : ℕ) : MorphismProperty.RespectsIso (C := Scheme.{u})
    (fun {_ _} f ↦ PureRelativeDimension d f) :=
  MorphismProperty.RespectsIso.mk _
    (fun e f h ↦ precomp_iso e f h)
    (fun e f h ↦ postcomp_iso f e h)

/-- Base change along an isomorphism preserves pure relative dimension. -/
theorem pullback_snd_of_isIso {d : ℕ} {f : X ⟶ S} (h : PureRelativeDimension d f)
    {T : Scheme.{u}} (b : T ⟶ S) [IsIso b] :
    PureRelativeDimension d (pullback.snd f b) := by
  let e : Arrow.mk (pullback.snd f b) ≅ Arrow.mk f :=
    Arrow.isoMk (asIso (pullback.fst f b)) (asIso b) pullback.condition
  exact (MorphismProperty.arrow_mk_iso_iff
    (P := fun {_ _} g ↦ PureRelativeDimension d g) e).mpr h

/-- Pure relative dimension is preserved by target-open restriction. -/
theorem restrict {d : ℕ} (f : X ⟶ S) (U : S.Opens) (h : PureRelativeDimension d f) :
    PureRelativeDimension d (f ∣_ U) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, fun s ↦ ?_⟩
  exact pureTopologicalDimensionOfHomeomorph
    (fiberHomeomorphRestrict f U s) (h.2 (U.ι s))

/-- Pure relative dimension can be checked on an open cover of the target. -/
theorem of_iSup_eq_top {d : ℕ} (f : X ⟶ S) {ι : Type u} (U : ι → S.Opens)
    (hU : iSup U = ⊤) (h : ∀ i, PureRelativeDimension d (f ∣_ U i)) :
    PureRelativeDimension d f := by
  let _ : IsZariskiLocalAtTarget (fun {_ _} g ↦ LocallyOfFiniteType g) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget _
  have hlft : LocallyOfFiniteType f :=
    IsZariskiLocalAtTarget.of_iSup_eq_top U hU (fun i ↦ (h i).1)
  refine ⟨hlft, fun s ↦ ?_⟩
  have hs : s ∈ (⨆ i, U i : S.Opens) := by rw [hU]; trivial
  obtain ⟨i, hsi⟩ := TopologicalSpace.Opens.mem_iSup.mp hs
  let sU : U i := ⟨s, hsi⟩
  exact pureTopologicalDimensionOfHomeomorph
    (fiberHomeomorphRestrict f (U i) sU).symm ((h i).2 sU)

instance (d : ℕ) :
    IsZariskiLocalAtTarget (fun {_ _} f ↦ PureRelativeDimension d f) := by
  apply IsZariskiLocalAtTarget.mk'
  · exact restrict
  · exact of_iSup_eq_top

/-- Chosen base change along a residue-field-preserving map preserves pure relative
dimension. -/
theorem pullback_snd_of_preservesResidueFields {d : ℕ} {f : X ⟶ S}
    (h : PureRelativeDimension d f) {T : Scheme.{u}} (b : T ⟶ S)
    [PreservesResidueFields b] :
    PureRelativeDimension d (pullback.snd f b) := by
  let _ : LocallyOfFiniteType f := h.1
  refine ⟨by infer_instance, fun t ↦ ?_⟩
  let k := fiberMapBaseChange f b t
  have hk : IsIso k := fiberMapBaseChange_isIso_of_preservesResidueFields f b t
  exact pureTopologicalDimensionOfHomeomorph
    (asIso k).schemeIsoToHomeo (h.2 (b t))

/-- Chosen base change along a preimmersion preserves pure relative dimension. -/
theorem pullback_snd_of_isPreimmersion {d : ℕ} {f : X ⟶ S}
    (h : PureRelativeDimension d f) {T : Scheme.{u}} (b : T ⟶ S) [IsPreimmersion b] :
    PureRelativeDimension d (pullback.snd f b) :=
  pullback_snd_of_preservesResidueFields h b

/-- The fibre over a point, viewed over its residue field, retains pure relative dimension. -/
theorem fiberToSpecResidueField {d : ℕ} {f : X ⟶ S}
    (h : PureRelativeDimension d f) (s : S) :
    PureRelativeDimension d (f.fiberToSpecResidueField s) :=
  pullback_snd_of_isPreimmersion h (S.fromSpecResidueField s)

/-- Pure relative dimension `d` is stable under every Cartesian base-change square whose base
map preserves residue fields. -/
instance (d : ℕ) {T S : Scheme.{u}} (b : T ⟶ S) [PreservesResidueFields b] :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (fun {_ _} f ↦ PureRelativeDimension d f) b where
  of_isPullback h hf := by
    have hc := pullback_snd_of_preservesResidueFields hf b
    have hi := precomp_iso h.isoPullback (pullback.snd _ b) hc
    simpa only [h.isoPullback_hom_snd] using hi

/-- Chosen-pullback base change along an open immersion preserves pure relative dimension. -/
theorem pullback_snd_of_isOpenImmersion {d : ℕ} {f : X ⟶ S}
    (h : PureRelativeDimension d f) {T : Scheme.{u}} (b : T ⟶ S) [IsOpenImmersion b] :
    PureRelativeDimension d (pullback.snd f b) :=
  pullback_snd_of_isPreimmersion h b

end PureRelativeDimension

/-- A syntomic morphism of geometric pure relative dimension `d`.  Keeping the dimension
assertion as a separate field makes the ordinary syntomic property reusable for morphisms whose
geometric fibre dimension is not constant. -/
class SyntomicOfRelativeDimension (d : ℕ) (f : X ⟶ S) : Prop where
  syntomic : GromovWitten.AlgebraicGeometry.Syntomic f
  geometricPureRelativeDimension : GeometricPureRelativeDimension d f

namespace SyntomicOfRelativeDimension

variable {d : ℕ}

/-- Forgetting the relative-dimension assertion gives an ordinary syntomic morphism. -/
theorem toSyntomic {f : X ⟶ S} (h : SyntomicOfRelativeDimension d f) :
    GromovWitten.AlgebraicGeometry.Syntomic f := h.syntomic

/-- The underlying geometric pure-relative-dimension assertion. -/
theorem toGeometricPureRelativeDimension {f : X ⟶ S}
    (h : SyntomicOfRelativeDimension d f) : GeometricPureRelativeDimension d f :=
  h.geometricPureRelativeDimension

/-- The induced residue-fibre pure-relative-dimension assertion. -/
theorem toPureRelativeDimension {f : X ⟶ S} (h : SyntomicOfRelativeDimension d f) :
    PureRelativeDimension d f := h.geometricPureRelativeDimension.toPureRelativeDimension

/-- Syntomic morphisms of pure relative dimension `d` are invariant under source
isomorphisms. -/
theorem precomp_iso {Y : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ S)
    (h : SyntomicOfRelativeDimension d f) :
  SyntomicOfRelativeDimension d (e.hom ≫ f) :=
  { syntomic := GromovWitten.AlgebraicGeometry.Syntomic.precomp_iso e f h.syntomic
    geometricPureRelativeDimension :=
      GeometricPureRelativeDimension.precomp_iso e f h.geometricPureRelativeDimension }

/-- Syntomic morphisms of pure relative dimension `d` are invariant under target
isomorphisms. -/
theorem postcomp_iso {Y : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ S)
    (h : SyntomicOfRelativeDimension d f) :
  SyntomicOfRelativeDimension d (f ≫ e.hom) :=
  { syntomic := GromovWitten.AlgebraicGeometry.Syntomic.postcomp_iso f e h.syntomic
    geometricPureRelativeDimension :=
      GeometricPureRelativeDimension.postcomp_iso f e h.geometricPureRelativeDimension }

instance : MorphismProperty.RespectsIso
    (fun {_ _} g ↦ SyntomicOfRelativeDimension d g) :=
  MorphismProperty.RespectsIso.mk _ precomp_iso (fun e f h ↦ postcomp_iso f e h)

/-- The fixed-relative-dimension syntomic predicate is invariant under an isomorphism in the
arrow category. -/
theorem iff_of_arrow_iso {X' S' : Scheme.{u}} {f : X ⟶ S} {g : X' ⟶ S'}
    (e : Arrow.mk f ≅ Arrow.mk g) :
    SyntomicOfRelativeDimension d f ↔ SyntomicOfRelativeDimension d g :=
  MorphismProperty.arrow_mk_iso_iff
    (P := fun {_ _} k ↦ SyntomicOfRelativeDimension d k) e

end SyntomicOfRelativeDimension

/-- A scheme-level family of curves is proper, flat, finitely presented, and of geometric
relative dimension at most one.  Geometric connectedness and exact genus remain separate
properties. -/
class FamilyOfCurves (f : X ⟶ S) : Prop where
  proper : IsProper f
  flat : Flat f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  quasiCompact : QuasiCompact f
  geometricRelativeDimensionLE_one : GeometricRelativeDimensionLE 1 f

namespace FamilyOfCurves

variable (f : X ⟶ S) [h : FamilyOfCurves f]

instance : IsProper f := h.proper
instance : Flat f := h.flat
instance : LocallyOfFinitePresentation f := h.locallyOfFinitePresentation
instance : QuasiCompact f := h.quasiCompact
instance : LocallyOfFiniteType f := inferInstance

theorem geometricRelativeDimensionLE : GeometricRelativeDimensionLE 1 f :=
  h.geometricRelativeDimensionLE_one

/-- The geometric dimension bound in particular controls every residue-field fibre. -/
theorem relativeDimensionLE : RelativeDimensionLE 1 f :=
  h.geometricRelativeDimensionLE_one.toRelativeDimensionLE

/-- Families of curves are invariant under an isomorphism of sources. -/
theorem precomp_iso {Y : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ S) (h : FamilyOfCurves f) :
    FamilyOfCurves (e.hom ≫ f) := by
  let _ : IsProper f := h.proper
  let _ : Flat f := h.flat
  let _ : LocallyOfFinitePresentation f := h.locallyOfFinitePresentation
  let _ : QuasiCompact f := h.quasiCompact
  exact
    { proper := by infer_instance
      flat := by infer_instance
      locallyOfFinitePresentation := by infer_instance
      quasiCompact := by infer_instance
      geometricRelativeDimensionLE_one :=
        GeometricRelativeDimensionLE.precomp_iso e f h.geometricRelativeDimensionLE_one }

/-- Families of curves are invariant under an isomorphism of targets. -/
theorem postcomp_iso {Y : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ S) (h : FamilyOfCurves f) :
    FamilyOfCurves (f ≫ e.hom) := by
  let _ : IsProper f := h.proper
  let _ : Flat f := h.flat
  let _ : LocallyOfFinitePresentation f := h.locallyOfFinitePresentation
  let _ : QuasiCompact f := h.quasiCompact
  exact
    { proper := by infer_instance
      flat := by infer_instance
      locallyOfFinitePresentation := by infer_instance
      quasiCompact := by infer_instance
      geometricRelativeDimensionLE_one :=
        GeometricRelativeDimensionLE.postcomp_iso f e h.geometricRelativeDimensionLE_one }

instance : MorphismProperty.RespectsIso (C := Scheme.{u})
    (fun {_ _} f ↦ FamilyOfCurves f) :=
  MorphismProperty.RespectsIso.mk _ precomp_iso (fun e f h ↦ postcomp_iso f e h)

/-- The family-of-curves predicate is invariant under an isomorphism in the arrow category. -/
theorem iff_of_arrow_iso {X' S' : Scheme.{u}} {f : X ⟶ S} {g : X' ⟶ S'}
    (e : Arrow.mk f ≅ Arrow.mk g) : FamilyOfCurves f ↔ FamilyOfCurves g :=
  MorphismProperty.arrow_mk_iso_iff (P := fun {_ _} k ↦ FamilyOfCurves k) e

/-- Chosen-pullback base change along an isomorphism preserves a family of curves. -/
theorem pullback_snd_of_isIso (f : X ⟶ S) (h : FamilyOfCurves f)
    {T : Scheme.{u}} (b : T ⟶ S) [IsIso b] : FamilyOfCurves (pullback.snd f b) := by
  let e : Arrow.mk (pullback.snd f b) ≅ Arrow.mk f :=
    Arrow.isoMk (asIso (pullback.fst f b)) (asIso b) pullback.condition
  exact (iff_of_arrow_iso e).mpr h

/-- Restricting a family of curves to an open subscheme of the base is again a family of curves. -/
theorem restrict (f : X ⟶ S) (U : S.Opens) (h : FamilyOfCurves f) :
    FamilyOfCurves (f ∣_ U) := by
  let _ : IsProper f := h.proper
  let _ : Flat f := h.flat
  let _ : LocallyOfFinitePresentation f := h.locallyOfFinitePresentation
  let _ : QuasiCompact f := h.quasiCompact
  exact
    { proper := by infer_instance
      flat := by infer_instance
      locallyOfFinitePresentation := by infer_instance
      quasiCompact := by infer_instance
      geometricRelativeDimensionLE_one :=
        GeometricRelativeDimensionLE.restrict f U h.geometricRelativeDimensionLE_one }

/-- Being a family of curves can be checked on an open cover of the base. -/
theorem of_iSup_eq_top (f : X ⟶ S) {ι : Type u} (U : ι → S.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, FamilyOfCurves (f ∣_ U i)) : FamilyOfCurves f := by
  let _ : IsZariskiLocalAtTarget (fun {_ _} g ↦ Flat g) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget _
  let _ : IsZariskiLocalAtTarget (fun {_ _} g ↦ LocallyOfFinitePresentation g) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget _
  have hp : IsProper f :=
    IsZariskiLocalAtTarget.of_iSup_eq_top U hU (fun i ↦ (h i).proper)
  let _ : IsProper f := hp
  exact
    { proper := hp
      flat := IsZariskiLocalAtTarget.of_iSup_eq_top U hU (fun i ↦ (h i).flat)
      locallyOfFinitePresentation :=
        IsZariskiLocalAtTarget.of_iSup_eq_top U hU
          (fun i ↦ (h i).locallyOfFinitePresentation)
      quasiCompact := by infer_instance
      geometricRelativeDimensionLE_one :=
        GeometricRelativeDimensionLE.of_iSup_eq_top f U hU
          (fun i ↦ (h i).geometricRelativeDimensionLE_one) }

instance : IsZariskiLocalAtTarget (fun {_ _} f ↦ FamilyOfCurves f) := by
  apply IsZariskiLocalAtTarget.mk'
  · exact restrict
  · exact of_iSup_eq_top

/-- Arbitrary chosen base change preserves a family of curves. -/
theorem pullback_snd (f : X ⟶ S) (h : FamilyOfCurves f)
    {T : Scheme.{u}} (b : T ⟶ S) :
    FamilyOfCurves (pullback.snd f b) := by
  let _ : IsProper f := h.proper
  let _ : Flat f := h.flat
  let _ : LocallyOfFinitePresentation f := h.locallyOfFinitePresentation
  let _ : QuasiCompact f := h.quasiCompact
  exact
    { proper := by infer_instance
      flat := by infer_instance
      locallyOfFinitePresentation := by infer_instance
      quasiCompact := by infer_instance
      geometricRelativeDimensionLE_one :=
        GeometricRelativeDimensionLE.pullback_snd h.geometricRelativeDimensionLE_one b }

/-- The residue-field-preserving specialization of arbitrary base-change stability. -/
theorem pullback_snd_of_preservesResidueFields (f : X ⟶ S) (h : FamilyOfCurves f)
    {T : Scheme.{u}} (b : T ⟶ S) [PreservesResidueFields b] :
    FamilyOfCurves (pullback.snd f b) :=
  pullback_snd f h b

/-- Chosen base change along a preimmersion preserves a family of curves. -/
theorem pullback_snd_of_isPreimmersion (f : X ⟶ S) (h : FamilyOfCurves f)
    {T : Scheme.{u}} (b : T ⟶ S) [IsPreimmersion b] :
    FamilyOfCurves (pullback.snd f b) :=
  pullback_snd f h b

/-- Every scheme-theoretic fibre of a family of curves is again a family over its residue
field. -/
theorem fiberToSpecResidueField (f : X ⟶ S) (h : FamilyOfCurves f) (s : S) :
    FamilyOfCurves (f.fiberToSpecResidueField s) :=
  pullback_snd_of_isPreimmersion f h (S.fromSpecResidueField s)

/-- Families of curves are stable under every Cartesian base-change square. -/
instance : MorphismProperty.IsStableUnderBaseChange
    (fun {_ _} f ↦ FamilyOfCurves f) := by
  constructor
  intro X Y Y' S f g f' g' h hf
  show FamilyOfCurves g'
  have hc := pullback_snd g hf f
  have hi := precomp_iso h.isoPullback (pullback.snd g f) hc
  simpa only [h.isoPullback_hom_snd] using hi

/-- Chosen-pullback base change along an open immersion preserves a family of curves. -/
theorem pullback_snd_of_isOpenImmersion (f : X ⟶ S) (h : FamilyOfCurves f)
    {T : Scheme.{u}} (b : T ⟶ S) [IsOpenImmersion b] :
    FamilyOfCurves (pullback.snd f b) :=
  pullback_snd f h b

end FamilyOfCurves

end


end GromovWitten.AlgebraicGeometry.Curves
