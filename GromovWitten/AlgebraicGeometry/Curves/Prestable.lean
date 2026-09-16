/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.Nodal
import GromovWitten.AlgebraicGeometry.Curves.Sections
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Prestable and pointed prestable families

A prestable family is a proper family of geometrically connected, pure one-dimensional nodal
curves.  This file keeps that scheme-level notion independent of maps to a target and of any
choice of dualizing sheaf or polarization.

A pointed prestable family adds indexed sections, their section equations, pairwise disjointness,
and the condition that every marked point lies in the relative smooth locus.  The latter is stated
through the stalk criterion defining `Scheme.Hom.smoothLocus`, so it does not replace geometric
smoothness by a combinatorial flag.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u v

noncomputable section

variable {X S T : Scheme.{u}}

/-- The inverse image of the smooth locus is contained in the smooth locus after arbitrary base
change.  This is the pointwise direction needed to pull back marked sections. -/
theorem smoothLocus_pullback_le (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (b : T ⟶ S) :
    (pullback.fst f b) ⁻¹ᵁ f.smoothLocus ≤ (pullback.snd f b).smoothLocus := by
  let U := f.smoothLocus
  have hfU : Smooth (U.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff]
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    ext x
    simp [U]
  let _ : Smooth (U.ι ≫ f) := hfU
  let e : pullback U.ι (pullback.fst f b) ≅ pullback (U.ι ≫ f) b :=
    pullbackRightPullbackFstIso f b U.ι
  let j : pullback U.ι (pullback.fst f b) ⟶ pullback f b :=
    pullback.snd U.ι (pullback.fst f b)
  let _ : IsOpenImmersion j := by
    dsimp [j]
    infer_instance
  have hjSmooth : Smooth (j ≫ pullback.snd f b) := by
    have h : Smooth (e.hom ≫ pullback.snd (U.ι ≫ f) b) := by infer_instance
    simpa only [e, j, pullbackRightPullbackFstIso_hom_snd] using h
  intro x hx
  have hxrange : x ∈ Set.range j := by
    change x ∈ Set.range (pullback.snd U.ι (pullback.fst f b))
    rw [Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
    exact hx
  obtain ⟨z, rfl⟩ := hxrange
  let _ : Smooth (j ≫ pullback.snd f b) := hjSmooth
  have hz : z ∈ (j ≫ pullback.snd f b).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  have hz' : z ∈ j ⁻¹ᵁ (pullback.snd f b).smoothLocus := by
    rw [Scheme.Hom.preimage_smoothLocus_eq]
    exact hz
  exact hz'

/-- A proper family of geometrically connected nodal curves of pure relative dimension one. -/
class PrestableFamily (f : X ⟶ S) : Prop where
  family : FamilyOfCurves f
  nodal : AtWorstNodal f
  geometricallyConnected : GeometricallyConnected f

namespace PrestableFamily

variable (f : X ⟶ S) [h : PrestableFamily f]

instance : FamilyOfCurves f := h.family
instance : AtWorstNodal f := h.nodal
instance : GeometricallyConnected f := h.geometricallyConnected
instance : IsProper f := h.family.proper
instance : Flat f := h.nodal.flat
instance : LocallyOfFinitePresentation f := h.nodal.locallyOfFinitePresentation
instance : LocallyOfFiniteType f := inferInstance

/-- A prestable family has geometric pure relative dimension one. -/
theorem geometricPureRelativeDimension : GeometricPureRelativeDimension 1 f :=
  h.nodal.geometricPureRelativeDimension

/-- Prestable families transport across arbitrary Cartesian base-change squares. -/
theorem of_isPullback {Y Y' T : Scheme.{u}} {g : Y ⟶ S} {b : T ⟶ S}
    {fst : Y' ⟶ Y} {g' : Y' ⟶ T} (sq : IsPullback fst g' g b)
    (hg : PrestableFamily g) : PrestableFamily g' where
  family := MorphismProperty.of_isPullback
    (P := fun {_ _} q ↦ FamilyOfCurves q) sq hg.family
  nodal := AtWorstNodal.of_isPullback sq hg.nodal
  geometricallyConnected := MorphismProperty.of_isPullback
    (P := @GeometricallyConnected) sq hg.geometricallyConnected

/-- Arbitrary chosen base change preserves prestability. -/
theorem pullback_snd (b : T ⟶ S) : PrestableFamily (pullback.snd f b) :=
  of_isPullback (IsPullback.of_hasPullback f b) h

instance : MorphismProperty.IsStableUnderBaseChange (@PrestableFamily) where
  of_isPullback sq hg := of_isPullback sq hg

instance : MorphismProperty.RespectsIso (@PrestableFamily) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- Prestable families are invariant under an isomorphism in the arrow category. -/
theorem iff_of_arrow_iso {X' S' : Scheme.{u}} {f : X ⟶ S} {g : X' ⟶ S'}
    (e : Arrow.mk f ≅ Arrow.mk g) :
    PrestableFamily f ↔ PrestableFamily g :=
  MorphismProperty.arrow_mk_iso_iff (P := @PrestableFamily) e

/-- Restriction to an open subscheme of the base preserves prestability. -/
theorem restrict (U : S.Opens) : PrestableFamily (f ∣_ U) := by
  apply of_isPullback (isPullback_morphismRestrict f U).flip h

/-- Every geometric fibre of a prestable family is connected. -/
instance geometricFiber_connected {K : Type u} [Field K]
    (y : Spec (.of K) ⟶ S) :
    ConnectedSpace (CategoryTheory.Limits.pullback f y : Scheme.{u}) := by
  let _ : GeometricallyConnected f := h.geometricallyConnected
  exact GeometricallyConnected.geometrically_connectedSpace y
    (pullback.fst f y) (pullback.snd f y) (IsPullback.of_hasPullback f y)

end PrestableFamily

/-- An indexed pointed prestable curve family.  The family contains no target map, genus,
polarization, or stability assertion. -/
structure PointedPrestableFamily (S : Scheme.{u}) (I : Type v) where
  total : Scheme.{u}
  toBase : total ⟶ S
  prestable : PrestableFamily toBase
  marking : I → (S ⟶ total)
  marking_toBase : ∀ i, marking i ≫ toBase = 𝟙 S
  markings_disjoint : ∀ i j, i ≠ j → ∀ s : S, marking i s ≠ marking j s
  markings_smooth : ∀ i (s : S),
    (toBase.stalkMap (marking i s)).hom.FormallySmooth

namespace PointedPrestableFamily

variable {I : Type v} (C : PointedPrestableFamily S I)

instance : PrestableFamily C.toBase := C.prestable
instance : FamilyOfCurves C.toBase := C.prestable.family
instance : AtWorstNodal C.toBase := C.prestable.nodal
instance : GeometricallyConnected C.toBase := C.prestable.geometricallyConnected

/-- Every marking of a pointed prestable family is a closed immersion.  Indeed, its composite
with the proper (hence separated) structure morphism is the identity of the base. -/
instance marking_isClosedImmersion (i : I) : IsClosedImmersion (C.marking i) := by
  exact isClosedImmersion_of_section_of_separated C.toBase (C.marking i)
    (C.marking_toBase i)

/-- The canonical ideal sheaf cutting out a marking in the total space. -/
def markingIdealSheaf (i : I) : C.total.IdealSheafData :=
  (C.marking i).ker

/-- The canonical closed subscheme cut out by a marking. -/
abbrev markingSubscheme (i : I) : Scheme.{u} :=
  (C.markingIdealSheaf i).subscheme

/-- A marking is canonically isomorphic to the closed subscheme cut out by its kernel ideal. -/
def markingSubschemeIso (i : I) : S ≅ C.markingSubscheme i :=
  let hClosed : IsClosedImmersion (C.marking i) := C.marking_isClosedImmersion i
  let hIso : IsIso (C.marking i).toImage :=
    @IsClosedImmersion.instIsIsoSchemeToImage _ _ (C.marking i) hClosed
  @asIso _ _ _ _ (C.marking i).toImage hIso

@[reassoc (attr := simp)]
theorem markingSubschemeIso_hom_subschemeι (i : I) :
    (C.markingSubschemeIso i).hom ≫ (C.markingIdealSheaf i).subschemeι = C.marking i :=
  by
    unfold markingSubschemeIso
    change (C.marking i).toImage ≫ (C.marking i).imageι = C.marking i
    exact Scheme.Hom.toImage_imageι (C.marking i)

/-- The support of the canonical marking ideal is exactly the image of the section. -/
theorem markingIdealSheaf_support (i : I) :
    ((C.markingIdealSheaf i).support : Set C.total) = Set.range (C.marking i) := by
  let _ : IsClosedImmersion (C.marking i) := C.marking_isClosedImmersion i
  rw [markingIdealSheaf, Scheme.Hom.support_ker]
  exact (C.marking i).isClosedEmbedding.isClosed_range.closure_eq

/-- Distinct markings have disjoint scheme-theoretic supports. -/
theorem markingIdealSheaf_support_disjoint {i j : I} (hij : i ≠ j) :
    Disjoint ((C.markingIdealSheaf i).support : Set C.total)
      ((C.markingIdealSheaf j).support : Set C.total) := by
  rw [C.markingIdealSheaf_support i, C.markingIdealSheaf_support j]
  refine Set.disjoint_left.mpr ?_
  rintro x ⟨s, rfl⟩ ⟨t, hst⟩
  have hbase := congrArg (fun x : C.total ↦ C.toBase x) hst
  have hst' : t = s := by
    rw [← Scheme.Hom.comp_apply, C.marking_toBase,
      ← Scheme.Hom.comp_apply, C.marking_toBase] at hbase
    exact hbase
  subst t
  exact C.markings_disjoint i j hij s hst.symm

/-- Each marking lands in the actual relative smooth locus. -/
theorem marking_mem_smoothLocus (i : I) (s : S) :
    C.marking i s ∈ C.toBase.smoothLocus :=
  C.markings_smooth i s

/-- The relative smooth locus, regarded as an open subscheme of the total space. -/
abbrev smoothPart : Scheme.{u} := C.toBase.smoothLocus

/-- The structure morphism restricted to the relative smooth locus. -/
def smoothPartToBase : C.smoothPart ⟶ S :=
  C.toBase.smoothLocus.ι ≫ C.toBase

/-- By construction, the restriction of the family to its relative smooth locus is smooth. -/
instance smoothPart_smooth : Smooth C.smoothPartToBase := by
  let _ : LocallyOfFinitePresentation C.toBase := C.prestable.nodal.locallyOfFinitePresentation
  let _ : LocallyOfFinitePresentation C.smoothPartToBase := by
    unfold smoothPartToBase
    infer_instance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  unfold smoothPartToBase
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  ext x
  simp

/-- Every marking factors canonically through the relative smooth locus. -/
def markingToSmoothPart (i : I) : S ⟶ C.smoothPart :=
  IsOpenImmersion.lift C.toBase.smoothLocus.ι (C.marking i) (by
    rintro _ ⟨s, rfl⟩
    exact ⟨⟨C.marking i s, C.marking_mem_smoothLocus i s⟩, rfl⟩)

@[reassoc (attr := simp)]
theorem markingToSmoothPart_toTotal (i : I) :
    C.markingToSmoothPart i ≫ C.toBase.smoothLocus.ι = C.marking i :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem markingToSmoothPart_toBase (i : I) :
    C.markingToSmoothPart i ≫ C.smoothPartToBase = 𝟙 S := by
  rw [smoothPartToBase, ← Category.assoc, C.markingToSmoothPart_toTotal,
    C.marking_toBase]

/-- The factored marking is a closed section of the smooth part of the family. -/
instance markingToSmoothPart_isClosedImmersion (i : I) :
    IsClosedImmersion (C.markingToSmoothPart i) := by
  have hSeparated : IsSeparated C.smoothPartToBase := by
    unfold smoothPartToBase
    infer_instance
  have hcomp : IsClosedImmersion (C.markingToSmoothPart i ≫ C.smoothPartToBase) := by
    rw [C.markingToSmoothPart_toBase i]
    infer_instance
  exact @IsClosedImmersion.of_comp _ _ _ (C.markingToSmoothPart i)
    C.smoothPartToBase hcomp hSeparated

/-- The section induced on a chosen pullback family. -/
def baseChangeMarking (b : T ⟶ S) (i : I) :
    T ⟶ pullback C.toBase b :=
  pullback.lift (b ≫ C.marking i) (𝟙 T) (by
    rw [Category.assoc, C.marking_toBase]
    simp)

@[reassoc (attr := simp)]
theorem baseChangeMarking_fst (b : T ⟶ S) (i : I) :
    C.baseChangeMarking b i ≫ pullback.fst C.toBase b = b ≫ C.marking i :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
theorem baseChangeMarking_snd (b : T ⟶ S) (i : I) :
    C.baseChangeMarking b i ≫ pullback.snd C.toBase b = 𝟙 T :=
  pullback.lift_snd ..

/-- Pull back a pointed prestable family along an arbitrary base morphism. -/
def baseChange (b : T ⟶ S) : PointedPrestableFamily T I where
  total := pullback C.toBase b
  toBase := pullback.snd C.toBase b
  prestable := PrestableFamily.of_isPullback
    (IsPullback.of_hasPullback C.toBase b) C.prestable
  marking := C.baseChangeMarking b
  marking_toBase := C.baseChangeMarking_snd b
  markings_disjoint := by
    intro i j hij t h
    have h' := congrArg (pullback.fst C.toBase b) h
    apply C.markings_disjoint i j hij (b t)
    have hi : pullback.fst C.toBase b (C.baseChangeMarking b i t) =
        C.marking i (b t) := by
      change (C.baseChangeMarking b i ≫ pullback.fst C.toBase b) t =
        (b ≫ C.marking i) t
      rw [C.baseChangeMarking_fst]
    have hj : pullback.fst C.toBase b (C.baseChangeMarking b j t) =
        C.marking j (b t) := by
      change (C.baseChangeMarking b j ≫ pullback.fst C.toBase b) t =
        (b ≫ C.marking j) t
      rw [C.baseChangeMarking_fst]
    exact hi.symm.trans (h'.trans hj)
  markings_smooth := by
    intro i t
    apply smoothLocus_pullback_le C.toBase b
    change pullback.fst C.toBase b (C.baseChangeMarking b i t) ∈ C.toBase.smoothLocus
    rw [← Scheme.Hom.comp_apply, C.baseChangeMarking_fst, Scheme.Hom.comp_apply]
    exact C.marking_mem_smoothLocus i (b t)

@[simp]
theorem baseChange_total (b : T ⟶ S) :
    (C.baseChange b).total = pullback C.toBase b := rfl

@[simp]
theorem baseChange_toBase (b : T ⟶ S) :
    (C.baseChange b).toBase = pullback.snd C.toBase b := rfl

@[simp]
theorem baseChange_marking (b : T ⟶ S) (i : I) :
    (C.baseChange b).marking i = C.baseChangeMarking b i := rfl

/-- Restrict the marking set along an injection. -/
def restrictMarkings {J : Type*} (ρ : J → I) (hρ : Function.Injective ρ) :
    PointedPrestableFamily S J where
  total := C.total
  toBase := C.toBase
  prestable := C.prestable
  marking j := C.marking (ρ j)
  marking_toBase j := C.marking_toBase (ρ j)
  markings_disjoint i j hij s :=
    C.markings_disjoint (ρ i) (ρ j) (fun h ↦ hij (hρ h)) s
  markings_smooth i s := C.markings_smooth (ρ i) s

/-- Reindex the markings by an equivalence. -/
abbrev reindex {J : Type*} (e : J ≃ I) : PointedPrestableFamily S J :=
  C.restrictMarkings e e.injective

@[simp]
theorem restrictMarkings_total {J : Type*} (ρ : J → I) (hρ : Function.Injective ρ) :
    (C.restrictMarkings ρ hρ).total = C.total := rfl

@[simp]
theorem restrictMarkings_marking {J : Type*} (ρ : J → I)
    (hρ : Function.Injective ρ) (j : J) :
    (C.restrictMarkings ρ hρ).marking j = C.marking (ρ j) := rfl

/-- A morphism of pointed prestable families over a fixed base preserves every marking. -/
structure Hom (C D : PointedPrestableFamily S I) where
  hom : C.total ⟶ D.total
  over_base : hom ≫ D.toBase = C.toBase
  marking_comm : ∀ i, C.marking i ≫ hom = D.marking i

@[ext]
theorem Hom.ext {C D : PointedPrestableFamily S I} {f g : Hom C D}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Pointed prestable families over a fixed base and with a fixed marking type form a category. -/
instance : Category (PointedPrestableFamily S I) where
  Hom := Hom
  id C :=
    { hom := 𝟙 C.total
      over_base := by simp
      marking_comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      over_base := by rw [Category.assoc, g.over_base, f.over_base]
      marking_comm := by
        intro i
        rw [← Category.assoc, f.marking_comm, g.marking_comm] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

@[simp]
theorem id_hom (C : PointedPrestableFamily S I) : Hom.hom (𝟙 C) = 𝟙 C.total := rfl

@[simp]
theorem comp_hom {C D E : PointedPrestableFamily S I} (f : C ⟶ D) (g : D ⟶ E) :
    Hom.hom (f ≫ g) = f.hom ≫ g.hom := rfl

/-- Forget a pointed family to its total scheme. -/
@[simps]
def sourceFunctor : PointedPrestableFamily S I ⥤ Scheme where
  obj C := C.total
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Isomorphisms and automorphisms are categorical, hence carry the expected identity,
composition, and inverse operations without identifying isomorphic total schemes literally. -/
abbrev Iso (C D : PointedPrestableFamily S I) := C ≅ D

abbrev Aut (C : PointedPrestableFamily S I) := CategoryTheory.Aut C

end PointedPrestableFamily

end

end GromovWitten.AlgebraicGeometry.Curves
