/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.Prestable
import GromovWitten.AlgebraicGeometry.Curves.RelativeLineBundles
import GromovWitten.AlgebraicGeometry.Curves.GeometricDualGraph
import GromovWitten.AlgebraicGeometry.Curves.GeometricGraphIso
import GromovWitten.AlgebraicGeometry.Curves.NormalizedComponentIso
import GromovWitten.AlgebraicGeometry.Curves.SchemeIsoGenus
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.NodeNormalization
import GromovWitten.AlgebraicGeometry.Curves.StableMaps.DecoratedGraph
import GromovWitten.AlgebraicGeometry.Curves.StableMaps.GraphTransport
import GromovWitten.AlgebraicGeometry.Curves.StableMaps.Pushout

/-!
# Geometric stable maps, stabilization, forgetting, and gluing

This file upgrades the existing marked-map diagrams and categorical colimits to geometric curve
families.  Prestable maps are proper nodal families with disjoint markings through the smooth
locus.  Polarization degrees come from an actual pulled-back line bundle, and degree zero is tied
to actual constancy of the map on a geometric irreducible component.

Fibre graphs enumerate the genuine irreducible components, nodes, and markings of each geometric
fibre.  Stability is therefore the compiled decorated-graph inequality applied to geometric data,
not an unrelated flag.  A stabilization contains an actual proper marked-map contraction, its
base changes, and the expected universal factorization through every stable target.  Forgetting a
marking is restriction followed by this stabilization.  Finally, geometric external and self
gluing attach nodal geometry and arbitrary-base-change comparisons to the categorical pushouts
already constructed in `Pushout`.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

namespace AlgebraicGeometry

/-- A field-valued point whose image lies in a closed subscheme lifts to that subscheme.  This
uses the fact that a closed immersion induces an isomorphism on residue fields at corresponding
points. -/
lemma IsClosedImmersion.exists_lift_spec_of_mem_range
    {V W : Scheme.{u}} (a : V ⟶ W) [IsClosedImmersion a]
    {K : Type u} [Field K] (p : Spec (.of K) ⟶ W)
    (hp : p default ∈ Set.range a) :
    ∃ p' : Spec (.of K) ⟶ V, p' ≫ a = p := by
  let pb := Scheme.SpecToEquivOfField K W p
  have hp' : pb.1 ∈ Set.range a := by
    have hpoint : pb.1 = p default := by
      change p _ = p default
      exact congrArg p (Subsingleton.elim _ _)
    rw [hpoint]
    exact hp
  obtain ⟨v, hv⟩ := hp'
  have hbij : Function.Bijective (a.residueFieldMap v) := by
    constructor
    · exact RingHom.injective _
    · intro z
      obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨r, rfl⟩ := a.stalkMap_surjective v s
      exact ⟨IsLocalRing.residue _ r, rfl⟩
  have : IsIso (a.residueFieldMap v) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  let b' : V.residueField v ⟶ .of K :=
    inv (a.residueFieldMap v) ≫ (W.residueFieldCongr hv).hom ≫ pb.2
  let p' : Spec (.of K) ⟶ V := Spec.map b' ≫ V.fromSpecResidueField v
  refine ⟨p', ?_⟩
  have hpb : (Scheme.SpecToEquivOfField K W).symm pb = p := by
    exact (Scheme.SpecToEquivOfField K W).symm_apply_apply p
  rw [← hpb]
  dsimp only [p']
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  dsimp only [b']
  rw [← Spec.map_comp_assoc]
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
  rfl

end AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap

universe u v w

noncomputable section

variable {V S : Scheme.{u}} {q : V ⟶ S}
variable {I : Type v} {J : Type w}

/-- The chosen geometric source fibre of a marked map. -/
abbrev sourceFiber (F : MarkedMap q I) {K : Type u} [Field K]
    (y : Spec (.of K) ⟶ S) : Scheme.{u} :=
  CategoryTheory.Limits.pullback F.toBase y

/-- The chosen geometric fibre of the target family. -/
abbrev targetFiber (q : V ⟶ S) {K : Type u} [Field K]
    (y : Spec (.of K) ⟶ S) : Scheme.{u} :=
  CategoryTheory.Limits.pullback q y

/-- A marked map whose source is a genuine prestable curve family and whose sections are
pairwise disjoint and lie in the smooth locus of the structural morphism. -/
structure Prestable (F : MarkedMap q I) : Prop where
  sourceFamily : PrestableFamily F.toBase
  markings_disjoint : ∀ i j, i ≠ j → ∀ s : S, F.marking i s ≠ F.marking j s
  markings_smooth : ∀ i (s : S),
    (F.toBase.stalkMap (F.marking i s)).hom.FormallySmooth

namespace Prestable

/-- The underlying source is a family of curves. -/
theorem family {F : MarkedMap q I} (hF : Prestable F) : FamilyOfCurves F.toBase :=
  hF.sourceFamily.family

/-- The structural morphism of a prestable map is proper. -/
theorem proper {F : MarkedMap q I} (hF : Prestable F) : IsProper F.toBase :=
  hF.sourceFamily.family.proper

/-- The structural morphism of a prestable map is at worst nodal. -/
theorem nodal {F : MarkedMap q I} (hF : Prestable F) : AtWorstNodal F.toBase :=
  hF.sourceFamily.nodal

/-- The geometric fibres of a prestable map's source are connected. -/
theorem geometricallyConnected {F : MarkedMap q I} (hF : Prestable F) :
    GeometricallyConnected F.toBase :=
  hF.sourceFamily.geometricallyConnected

/-- Forgetting the target map gives the underlying pointed prestable family. -/
def toPointedPrestableFamily {F : MarkedMap q I} (hF : Prestable F) :
    PointedPrestableFamily S I where
  total := F.source
  toBase := F.toBase
  prestable := hF.sourceFamily
  marking := F.marking
  marking_toBase := F.marking_toBase
  markings_disjoint := hF.markings_disjoint
  markings_smooth := hF.markings_smooth

/-- Restricting the marking set preserves prestability. -/
theorem restrictMarkings {F : MarkedMap q I} (hF : Prestable F) (ρ : J → I)
    (hρ : Function.Injective ρ) : Prestable (F.restrictMarkings ρ) where
  sourceFamily := hF.sourceFamily
  markings_disjoint i j hij s := hF.markings_disjoint (ρ i) (ρ j) (fun h ↦ hij (hρ h)) s
  markings_smooth i s := hF.markings_smooth (ρ i) s

/-- Prestability of marked maps is preserved by arbitrary base change. -/
theorem baseChange {F : MarkedMap q I} (hF : Prestable F)
    {T : Scheme.{u}} (b : T ⟶ S) : Prestable (F.baseChange b) := by
  let C : PointedPrestableFamily S I := hF.toPointedPrestableFamily
  let C' : PointedPrestableFamily T I := C.baseChange b
  exact
    { sourceFamily := C'.prestable
      markings_disjoint := C'.markings_disjoint
      markings_smooth := C'.markings_smooth }

/-- Postcomposition on the target does not alter the prestable pointed source. -/
theorem postcompose {F : MarkedMap q I} (hF : Prestable F)
    {W : Scheme.{u}} {q' : W ⟶ S} (a : V ⟶ W) (ha : a ≫ q' = q) :
    Prestable (F.postcompose a ha) := by
  exact
    { sourceFamily := hF.sourceFamily
      markings_disjoint := hF.markings_disjoint
      markings_smooth := hF.markings_smooth }

/-- Prestability is invariant under an isomorphism of marked maps. -/
theorem of_iso {F G : MarkedMap q I} (e : F ≅ G) (hF : Prestable F) : Prestable G := by
  let sourceIso : F.source ≅ G.source :=
    (sourceFunctor (q := q) (I := I)).mapIso e
  let arrowIso : Arrow.mk F.toBase ≅ Arrow.mk G.toBase :=
    Arrow.isoMk sourceIso (Iso.refl S) e.hom.over_base
  let hGsource : PrestableFamily G.toBase :=
    (PrestableFamily.iff_of_arrow_iso arrowIso).mp hF.sourceFamily
  let _ : LocallyOfFinitePresentation F.toBase :=
    hF.sourceFamily.nodal.locallyOfFinitePresentation
  let _ : LocallyOfFinitePresentation G.toBase :=
    hGsource.nodal.locallyOfFinitePresentation
  let _ : IsIso e.hom.hom := by
    change IsIso sourceIso.hom
    infer_instance
  let _ : IsOpenImmersion e.hom.hom := by infer_instance
  refine
    { sourceFamily := hGsource
      markings_disjoint := ?_
      markings_smooth := ?_ }
  · intro i j hij s h
    apply hF.markings_disjoint i j hij s
    apply sourceIso.hom.injective
    change e.hom.hom (F.marking i s) = e.hom.hom (F.marking j s)
    change (F.marking i ≫ e.hom.hom) s = (F.marking j ≫ e.hom.hom) s
    rw [e.hom.marking_comm, e.hom.marking_comm]
    exact h
  · intro i s
    have hx : F.marking i s ∈ F.toBase.smoothLocus := hF.markings_smooth i s
    have hx' : F.marking i s ∈ e.hom.hom ⁻¹ᵁ G.toBase.smoothLocus := by
      rw [Scheme.Hom.preimage_smoothLocus_eq]
      simpa only [e.hom.over_base] using hx
    change G.marking i s ∈ G.toBase.smoothLocus
    have hmark := congrArg (fun k : S ⟶ G.source ↦ k s) (e.hom.marking_comm i)
    change e.hom.hom (F.marking i s) = G.marking i s at hmark
    rw [← hmark]
    exact hx'

/-- Isomorphic marked maps are prestable simultaneously. -/
theorem iso_iff {F G : MarkedMap q I} (e : F ≅ G) : Prestable F ↔ Prestable G :=
  ⟨of_iso e, of_iso e.symm⟩

end Prestable

/-- Polarization degree of a mapped family.  `degreeLine` is a genuine relative line bundle
whose underlying sheaf is the pullback of the target polarization.  The zero-degree criterion is
expressed by actual constancy of the fibre map on the selected component. -/
structure PolarizedDegree (F : MarkedMap q I) (H : LineBundle V) where
  degreeLine : RelativeLineBundle F.toBase
  lineIso : degreeLine.line.Iso (H.pullback F.map)
  nonnegative : degreeLine.FiberwiseNef
  degree_eq_zero_iff : ∀ (K : Type u) [Field K]
    (y : Spec (.of K) ⟶ S)
    (component : irreducibleComponents (F.sourceFiber y)),
    degreeLine.degree y component = 0 ↔
      ∃ p : Spec (.of K) ⟶ targetFiber q y,
        p ≫ CategoryTheory.Limits.pullback.snd q y = 𝟙 (Spec (.of K)) ∧
        ∀ z : F.sourceFiber y, z ∈ (component : Set _) →
          (F.baseChange y).map z = p (genericPoint (Spec (.of K)))

/-- Transport polarization-degree data through an isomorphism of marked maps with fixed target.
The relative line is pulled back along the inverse source isomorphism, and component degrees are
transported through the induced isomorphism of every chosen geometric source fibre. -/
def PolarizedDegree.ofIso {F G : MarkedMap q I} (e : F ≅ G)
    (H : LineBundle V) (D : PolarizedDegree F H) : PolarizedDegree G H where
  degreeLine :=
    { line := D.degreeLine.line.pullback
        ((sourceFunctor (q := q) (I := I)).mapIso e).inv
      componentDegree := by
        intro K _ y C
        exact D.degreeLine.degree y
          ((irreducibleComponentsEquivOfSchemeIso
            (baseChangeSourceIso e y)).symm C) }
  lineIso := by
    let E := (sourceFunctor (q := q) (I := I)).mapIso e
    exact ((Scheme.Modules.pullback E.inv).mapIso D.lineIso).trans
      ((H.pullbackPullbackIso F.map E.inv).trans (eqToIso (by
        change (H.pullback (e.inv.hom ≫ F.map)).obj = (H.pullback G.map).obj
        rw [e.inv.map_comm])))
  nonnegative := by
    intro K _ y C
    exact D.nonnegative K y
      ((irreducibleComponentsEquivOfSchemeIso
        (baseChangeSourceIso e y)).symm C)
  degree_eq_zero_iff := by
    intro K _ y C
    let eFiber := (baseChangeFunctor y).mapIso e
    let E := baseChangeSourceIso e y
    let c := irreducibleComponentsEquivOfSchemeIso E
    change D.degreeLine.degree y (c.symm C) = 0 ↔ _
    rw [D.degree_eq_zero_iff K y (c.symm C)]
    constructor
    · rintro ⟨p, hp, hconstant⟩
      refine ⟨p, hp, ?_⟩
      intro z hz
      have hz' : E.inv z ∈ (c.symm C : Set _) := by
        change E.hom (E.inv z) ∈ (C : Set _)
        have heq : E.hom (E.inv z) = z := congrArg
          (fun k : G.sourceFiber y ⟶ G.sourceFiber y ↦ k z) E.inv_hom_id
        rw [heq]
        exact hz
      change (G.baseChange y).map z = p (genericPoint (Spec (.of K)))
      calc
        (G.baseChange y).map z =
            (G.baseChange y).map (E.hom (E.inv z)) := by
              congr 1
              exact (congrArg
                (fun k : G.sourceFiber y ⟶ G.sourceFiber y ↦ k z)
                E.inv_hom_id).symm
        _ = (F.baseChange y).map (E.inv z) := by
              exact congrArg (fun k ↦ k (E.inv z)) eFiber.hom.map_comm
        _ = p (genericPoint (Spec (.of K))) := hconstant (E.inv z) hz'
    · rintro ⟨p, hp, hconstant⟩
      refine ⟨p, hp, ?_⟩
      intro z hz
      have hz' : E.hom z ∈ (C : Set _) :=
        (mem_irreducibleComponentsEquivOfSchemeIso_symm E C z).mp hz
      change (F.baseChange y).map z = p (genericPoint (Spec (.of K)))
      exact (congrArg (fun k ↦ k z) eFiber.hom.map_comm).symm.trans
        (hconstant (E.hom z) hz')

/-- Transport polarization-degree data through an isomorphism of targets.  The new polarization
is the pullback along the inverse isomorphism, so its pullback to the source is canonically the
old one. -/
def PolarizedDegree.postcomposeIso {W : Scheme.{u}} {q' : W ⟶ S}
    (F : MarkedMap q I) (H : LineBundle V) (D : PolarizedDegree F H)
    (e : V ≅ W) (he : e.hom ≫ q' = q) :
    PolarizedDegree (F.postcompose e.hom he) (H.pullback e.inv) where
  degreeLine := D.degreeLine
  lineIso := by
    let hcomp : (F.map ≫ e.hom) ≫ e.inv = F.map := by simp
    let canon : ((H.pullback e.inv).pullback (F.map ≫ e.hom)).Iso
        (H.pullback F.map) :=
      (H.pullbackPullbackIso e.inv (F.map ≫ e.hom)).trans (eqToIso (by rw [hcomp]))
    exact D.lineIso.trans canon.symm
  nonnegative := D.nonnegative
  degree_eq_zero_iff := by
    intro K _ y component
    change D.degreeLine.degree y
        (show irreducibleComponents (F.sourceFiber y) from component) = 0 ↔ _
    rw [D.degree_eq_zero_iff K y
      (show irreducibleComponents (F.sourceFiber y) from component)]
    let E := baseChangeTargetIso e he y
    have hhomInv (x : targetFiber q y) : E.inv (E.hom x) = x := by
      have hx := congrArg
        (fun k : targetFiber q y ⟶ targetFiber q y ↦ k x) E.hom_inv_id
      change E.inv (E.hom x) = (𝟙 (targetFiber q y) :
        targetFiber q y ⟶ targetFiber q y) x at hx
      exact hx.trans rfl
    have hinvHom (x : targetFiber q' y) : E.hom (E.inv x) = x := by
      have hx := congrArg
        (fun k : targetFiber q' y ⟶ targetFiber q' y ↦ k x) E.inv_hom_id
      change E.hom (E.inv x) = (𝟙 (targetFiber q' y) :
        targetFiber q' y ⟶ targetFiber q' y) x at hx
      exact hx.trans rfl
    have hmap : (F.baseChange y).map ≫ E.hom =
        ((F.postcompose e.hom he).baseChange y).map := by
      have hraw := (baseChange_postcompose_map F e.hom he y).symm
      change (F.baseChange y).map ≫ E.hom =
        ((F.postcompose e.hom he).baseChange y).map at hraw
      exact hraw
    constructor
    · rintro ⟨p, hp, hconstant⟩
      refine ⟨p ≫ E.hom, ?_, ?_⟩
      · have hsnd : E.hom ≫ pullback.snd q' y = pullback.snd q y := by
          exact (baseChangePostcomposeComparison F e he y).targetIso_toBase
        rw [Category.assoc, hsnd, hp]
      · intro z hz
        change ((F.postcompose e.hom he).baseChange y).map z =
          (p ≫ E.hom) (genericPoint (Spec (.of K)))
        rw [← hmap]
        change E.hom ((F.baseChange y).map z) =
          E.hom (p (genericPoint (Spec (.of K))))
        exact congrArg E.hom (hconstant z hz)
    · rintro ⟨p, hp, hconstant⟩
      refine ⟨p ≫ E.inv, ?_, ?_⟩
      · rw [Category.assoc]
        have hsnd : E.inv ≫ pullback.snd q y = pullback.snd q' y := by
          exact baseChangeTargetMap_snd e.inv (targetIso_inv_toBase e he) y
        rw [hsnd, hp]
      · intro z hz
        have heq : E.hom ((F.baseChange y).map z) =
            E.hom ((p ≫ E.inv) (genericPoint (Spec (.of K)))) := by
          rw [Scheme.Hom.comp_apply, hinvHom]
          change ((F.baseChange y).map ≫ E.hom) z =
            p (genericPoint (Spec (.of K)))
          rw [hmap]
          exact hconstant z hz
        calc
          (F.baseChange y).map z = E.inv (E.hom ((F.baseChange y).map z)) :=
            (hhomInv _).symm
          _ = E.inv (E.hom ((p ≫ E.inv) (genericPoint (Spec (.of K))))) :=
            congrArg E.inv heq
          _ = (p ≫ E.inv) (genericPoint (Spec (.of K))) :=
            hhomInv _

/-- A target-changing isomorphism of marked maps transports polarization-degree data, including
both the target polarization and the geometric source components. -/
def PolarizedDegree.ofTargetedIso {W : Scheme.{u}} {q' : W ⟶ S}
    {F : MarkedMap q I} {G : MarkedMap q' I} (e : TargetedIso F G)
    (H : LineBundle V) (D : PolarizedDegree F H) :
    PolarizedDegree G (H.pullback e.targetIso.inv) :=
  PolarizedDegree.ofIso e.toIso (H.pullback e.targetIso.inv)
    (D.postcomposeIso F H e.targetIso e.targetIso_toBase)

/-- Polarization-degree data pull back along an arbitrary base morphism.  The zero-degree
criterion is transported through the canonical targeted isomorphism between iterated and direct
chosen pullbacks. -/
def PolarizedDegree.baseChange (F : MarkedMap q I) (H : LineBundle V)
    (D : PolarizedDegree F H) {T : Scheme.{u}} (b : T ⟶ S) :
    PolarizedDegree (F.baseChange b) (H.pullback (pullback.fst q b)) where
  degreeLine := D.degreeLine.pullback b
  lineIso := by
    let sourceFst := pullback.fst F.toBase b
    let targetFst := pullback.fst q b
    exact ((Scheme.Modules.pullback sourceFst).mapIso D.lineIso).trans
      ((H.pullbackPullbackIso F.map sourceFst).trans
        ((eqToIso (by
          dsimp only [sourceFst, targetFst]
          rw [baseChange_map_fst]
          rfl)).trans
          (H.pullbackPullbackIso targetFst (F.baseChange b).map).symm))
  nonnegative := D.degreeLine.pullback_fiberwiseNef b D.nonnegative
  degree_eq_zero_iff := by
    intro K _ y C
    let E := iteratedBaseChangeComparison F b y
    let c := irreducibleComponentsEquivOfSchemeIso E.sourceIso
    change D.degreeLine.degree (y ≫ b) (c C) = 0 ↔ _
    rw [D.degree_eq_zero_iff K (y ≫ b) (c C)]
    constructor
    · rintro ⟨p, hp, hconstant⟩
      refine ⟨p ≫ E.targetIso.inv, ?_, ?_⟩
      · have hinv : E.targetIso.inv ≫ pullback.snd (pullback.snd q b) y =
            pullback.snd q (y ≫ b) := E.symm.targetIso_toBase
        rw [Category.assoc, hinv, hp]
      · intro z hz
        apply E.targetIso.hom.injective
        change E.targetIso.hom (((F.baseChange b).baseChange y).map z) =
          E.targetIso.hom ((p ≫ E.targetIso.inv)
            (genericPoint (Spec (.of K))))
        have hright : E.targetIso.hom ((p ≫ E.targetIso.inv)
            (genericPoint (Spec (.of K)))) =
            p (genericPoint (Spec (.of K))) := by
          change (E.targetIso.inv ≫ E.targetIso.hom)
            (p (genericPoint (Spec (.of K)))) = _
          exact congrArg
            (fun k : targetFiber q (y ≫ b) ⟶ targetFiber q (y ≫ b) ↦
              k (p (genericPoint (Spec (.of K))))) E.targetIso.inv_hom_id
        rw [hright]
        change (((F.baseChange b).baseChange y).map ≫ E.targetIso.hom) z = _
        rw [E.map_comm]
        apply hconstant
        change E.sourceIso.hom z ∈
          E.sourceIso.hom '' (C : Set ((F.baseChange b).sourceFiber y))
        exact ⟨z, hz, rfl⟩
    · rintro ⟨p, hp, hconstant⟩
      refine ⟨p ≫ E.targetIso.hom, ?_, ?_⟩
      · rw [Category.assoc, E.targetIso_toBase, hp]
      · intro z hz
        change z ∈ E.sourceIso.hom ''
          (C : Set ((F.baseChange b).sourceFiber y)) at hz
        obtain ⟨z', hz', rfl⟩ := hz
        change (F.baseChange (y ≫ b)).map (E.sourceIso.hom z') =
          (p ≫ E.targetIso.hom) (genericPoint (Spec (.of K)))
        change (E.sourceIso.hom ≫ (F.baseChange (y ≫ b)).map) z' =
          E.targetIso.hom (p (genericPoint (Spec (.of K))))
        rw [← E.map_comm]
        exact congrArg E.targetIso.hom (hconstant z' hz')

/-- Postcomposition reflects componentwise constancy when a component whose composite map is
constant was already constant before postcomposition.  The opposite implication always holds;
this predicate isolates the exact additional geometric condition needed by stability. -/
def ReflectsComponentConstancy {W : Scheme.{u}} {q' : W ⟶ S}
    (F : MarkedMap q I) (a : V ⟶ W) (ha : a ≫ q' = q) : Prop :=
  ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
    (component : irreducibleComponents (F.sourceFiber y)),
    (∃ p : Spec (.of K) ⟶ targetFiber q' y,
        p ≫ pullback.snd q' y = 𝟙 (Spec (.of K)) ∧
        ∀ z : F.sourceFiber y, z ∈ (component : Set _) →
          ((F.postcompose a ha).baseChange y).map z =
            p (genericPoint (Spec (.of K)))) →
      ∃ p : Spec (.of K) ⟶ targetFiber q y,
        p ≫ pullback.snd q y = 𝟙 (Spec (.of K)) ∧
        ∀ z : F.sourceFiber y, z ∈ (component : Set _) →
          (F.baseChange y).map z = p (genericPoint (Spec (.of K)))

/-- The map between target fibres induced by postcomposition is the pullback of the target map. -/
lemma baseChangeTargetMap_isPullback {W : Scheme.{u}} {q' : W ⟶ S}
    (a : V ⟶ W) (ha : a ≫ q' = q)
    {K : Type u} [Field K] (y : Spec (.of K) ⟶ S) :
    IsPullback (baseChangeTargetMap a ha y) (pullback.fst q y)
      (pullback.fst q' y) a := by
  apply IsPullback.mk'
  · exact baseChangeTargetMap_fst a ha y
  · intro T φ φ' hA hV
    apply pullback.hom_ext
    · exact hV
    · have h := congrArg (fun k ↦ k ≫ pullback.snd q' y) hA
      simpa only [Category.assoc, baseChangeTargetMap_snd] using h
  · intro T h k hcomm
    let l : T ⟶ pullback q y := pullback.lift k (h ≫ pullback.snd q' y) (by
      calc
        k ≫ q = (k ≫ a) ≫ q' := by rw [Category.assoc, ha]
        _ = (h ≫ pullback.fst q' y) ≫ q' := by rw [hcomm]
        _ = h ≫ (pullback.snd q' y ≫ y) := by
          rw [Category.assoc, pullback.condition]
        _ = (h ≫ pullback.snd q' y) ≫ y := (Category.assoc _ _ _).symm)
    refine ⟨l, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp only [Category.assoc, baseChangeTargetMap_fst, l,
          pullback.lift_fst_assoc, hcomm]
      · simp only [Category.assoc, baseChangeTargetMap_snd, l,
          pullback.lift_snd]
    · exact pullback.lift_fst _ _ _

/-- Closed immersions reflect the pointwise component-constancy condition. -/
theorem reflectsComponentConstancy_of_isClosedImmersion
    {W : Scheme.{u}} {q' : W ⟶ S} (F : MarkedMap q I)
    (a : V ⟶ W) (ha : a ≫ q' = q) [IsClosedImmersion a] :
    ReflectsComponentConstancy F a ha := by
  intro K _ y component hconstantAfter
  obtain ⟨p, hp, hconstant⟩ := hconstantAfter
  let A := baseChangeTargetMap a ha y
  have : IsClosedImmersion A := MorphismProperty.of_isPullback
    (baseChangeTargetMap_isPullback a ha y).flip inferInstance
  obtain ⟨z₀, hz₀⟩ := component.2.1.nonempty
  have hpRange : p default ∈ Set.range A := by
    refine ⟨(F.baseChange y).map z₀, ?_⟩
    calc
      A ((F.baseChange y).map z₀) =
          ((F.postcompose a ha).baseChange y).map z₀ := by
        change ((F.baseChange y).map ≫ A) z₀ = _
        rw [← baseChange_postcompose_map]
        rfl
      _ = p (genericPoint (Spec (.of K))) := hconstant z₀ hz₀
      _ = p default := congrArg p (Subsingleton.elim _ _)
  obtain ⟨p', hp'⟩ :=
    IsClosedImmersion.exists_lift_spec_of_mem_range A p hpRange
  refine ⟨p', ?_, ?_⟩
  · rw [← baseChangeTargetMap_snd a ha y, ← Category.assoc, hp', hp]
  · intro z hz
    apply A.isClosedEmbedding.injective
    change A ((F.baseChange y).map z) =
      A (p' (genericPoint (Spec (.of K))))
    change ((F.baseChange y).map ≫ A) z =
      (p' ≫ A) (genericPoint (Spec (.of K)))
    rw [← baseChange_postcompose_map, hp']
    exact hconstant z hz

/-- If postcomposition reflects componentwise constancy, degree data for the pulled-back target
polarization become degree data for the postcomposed map. -/
def PolarizedDegree.postcomposeOfReflectsConstancy
    {W : Scheme.{u}} {q' : W ⟶ S} (F : MarkedMap q I) (H : LineBundle W)
    (a : V ⟶ W) (ha : a ≫ q' = q) (D : PolarizedDegree F (H.pullback a))
    (hreflect : ReflectsComponentConstancy F a ha) :
    PolarizedDegree (F.postcompose a ha) H where
  degreeLine := D.degreeLine
  lineIso := D.lineIso.trans (H.pullbackPullbackIso a F.map)
  nonnegative := D.nonnegative
  degree_eq_zero_iff := by
    intro K _ y component
    change D.degreeLine.degree y
        (show irreducibleComponents (F.sourceFiber y) from component) = 0 ↔ _
    rw [D.degree_eq_zero_iff K y
      (show irreducibleComponents (F.sourceFiber y) from component)]
    constructor
    · rintro ⟨p, hp, hconstant⟩
      let A := baseChangeTargetMap a ha y
      refine ⟨p ≫ A, ?_, ?_⟩
      · rw [Category.assoc, baseChangeTargetMap_snd, hp]
      · intro z hz
        rw [baseChange_postcompose_map]
        change A ((F.baseChange y).map z) = A (p (genericPoint (Spec (.of K))))
        exact congrArg A (hconstant z hz)
    · exact hreflect K y
        (show irreducibleComponents (F.sourceFiber y) from component)

/-- Polarized degree data descend through a closed immersion of targets. -/
def PolarizedDegree.postcomposeClosedImmersion
    {W : Scheme.{u}} {q' : W ⟶ S} (F : MarkedMap q I) (H : LineBundle W)
    (a : V ⟶ W) (ha : a ≫ q' = q) [IsClosedImmersion a]
    (D : PolarizedDegree F (H.pullback a)) :
    PolarizedDegree (F.postcompose a ha) H :=
  D.postcomposeOfReflectsConstancy F H a ha
    (reflectsComponentConstancy_of_isClosedImmersion F a ha)

/-! ### The decorated graph forced by normalized fibre geometry -/

/-- The component carrying a marked point of a geometric source fibre. -/
noncomputable def normalizedMarkingVertex
    {K : Type u} [Field K] (F : MarkedMap q I) (y : Spec (.of K) ⟶ S) (i : I) :
    Component (F.sourceFiber y) :=
  componentOf ((F.baseChange y).marking i (genericPoint (Spec (.of K))))

/-- The decorated graph whose dual graph, genera, and endpoints are all read from the actual
normalized component normalizations and their node branch fibres. -/
noncomputable def normalizedVertexLift
    (F : MarkedMap q I) {K : Type u} [Field K]
    (y : Spec (.of K) ⟶ S) :
    Component (F.sourceFiber y) ≃ ULift.{max u v} (Component (F.sourceFiber y)) :=
  Equiv.ulift.symm

noncomputable def normalizedEdgeLift
    (F : MarkedMap q I) {K : Type u} [Field K]
    (y : Spec (.of K) ⟶ S) :
    Edge (f := pullback.snd F.toBase y) ≃
      ULift.{max u v} (Edge (f := pullback.snd F.toBase y)) :=
  Equiv.ulift.symm

noncomputable def normalizedDecoratedGraph
    (F : MarkedMap q I) [Fintype I] [DecidableEq I]
    [PrestableFamily F.toBase]
    {H : LineBundle V} (D : PolarizedDegree F H)
    (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
    [PrestableFamily (pullback.snd F.toBase y)] : DecoratedGraph.{max u v} := by
  let V := ULift.{max u v} (Component (F.sourceFiber y))
  let E := ULift.{max u v} (Edge (f := pullback.snd F.toBase y))
  let L := ULift.{max u v} I
  let cv : Component (F.sourceFiber y) ≃ V := normalizedVertexLift F y
  let ce : Edge (f := pullback.snd F.toBase y) ≃ E := normalizedEdgeLift F y
  let base : DualGraph :=
    geometricDualGraphOfNormalization (pullback.snd F.toBase y)
  let cb := base.reindex cv ce
  exact
    { toDualGraph := cb
      Leg := L
      legVertex := fun i ↦ cv (normalizedMarkingVertex F y (Equiv.ulift i))
      degree := fun C ↦ (D.degreeLine.degree y (cv.symm C)).toNat }

@[simp]
theorem normalizedDecoratedGraph_degree_eq
    (F : MarkedMap q I) [Fintype I] [DecidableEq I]
    [PrestableFamily F.toBase] {H : LineBundle V} (D : PolarizedDegree F H)
    (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
    [PrestableFamily (pullback.snd F.toBase y)]
    (C : Component (F.sourceFiber y)) :
    D.degreeLine.degree y C =
      (normalizedDecoratedGraph F D K y).degree
        ((normalizedVertexLift F y) C) := by
  change D.degreeLine.degree y C = (D.degreeLine.degree y C).toNat
  exact (Int.toNat_of_nonneg (D.nonnegative K y C)).symm

@[simp]
theorem normalizedDecoratedGraph_endpoint_pair_eq
    (F : MarkedMap q I) [Fintype I] [DecidableEq I]
    [PrestableFamily F.toBase] {H : LineBundle V} (D : PolarizedDegree F H)
    (K : Type u) [Field K] [IsAlgClosed K] (y : Spec (.of K) ⟶ S)
    [PrestableFamily (pullback.snd F.toBase y)]
    (B : NormalizedBranchData (pullback.snd F.toBase y)) (e : Edge (f := pullback.snd F.toBase y)) :
    s((normalizedDecoratedGraph F D K y).toDualGraph.endpoint
        ((normalizedEdgeLift F y) e) 0,
      (normalizedDecoratedGraph F D K y).toDualGraph.endpoint
        ((normalizedEdgeLift F y) e) 1) =
      s((normalizedVertexLift F y) ((B.point e 0).1),
        (normalizedVertexLift F y) ((B.point e 1).1)) := by
  simp only [normalizedDecoratedGraph, DualGraph.reindex]
  change Sym2.map (normalizedVertexLift F y)
      (s(endpoint (pullback.snd F.toBase y) e 0, endpoint (pullback.snd F.toBase y) e 1)) =
    Sym2.map (normalizedVertexLift F y) (s((B.point e 0).1, (B.point e 1).1))
  apply congrArg (Sym2.map (normalizedVertexLift F y))
  exact NormalizedBranchData.endpoint_pair_of_normalized_fibre
    (pullback.snd F.toBase y) e
    (fun j ↦ B.point e j) (fun j ↦ B.point_to_node e j)
    (fun q hq ↦ B.point_fibre_surjective e q hq)

/-- The canonical decorated graph of a geometric fibre.  Its vertex genus and endpoint map come
from `geometricDualGraphOfNormalization`; a branch witness is not part of this graph's data. -/
noncomputable def normalizedDecoratedGraphOfNormalization
    (F : MarkedMap q I) [Fintype I] [DecidableEq I]
    [PrestableFamily F.toBase]
    {H : LineBundle V} (D : PolarizedDegree F H)
    (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
    [PrestableFamily (pullback.snd F.toBase y)] : DecoratedGraph.{max u v} :=
  normalizedDecoratedGraph F D K y

@[simp]
theorem normalizedDecoratedGraphOfNormalization_degree_eq
    (F : MarkedMap q I) [Fintype I] [DecidableEq I]
    [PrestableFamily F.toBase] {H : LineBundle V} (D : PolarizedDegree F H)
    (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
    [PrestableFamily (pullback.snd F.toBase y)]
    (C : Component (F.sourceFiber y)) :
    D.degreeLine.degree y C =
      (normalizedDecoratedGraphOfNormalization F D K y).degree
        ((normalizedVertexLift F y) C) := by
  change D.degreeLine.degree y C = (D.degreeLine.degree y C).toNat
  exact (Int.toNat_of_nonneg (D.nonnegative K y C)).symm

/-- Numerical stability of the canonical normalized graph is exactly the geometric positivity
condition on its contracted normalized components. -/
theorem normalizedDecoratedGraphOfNormalization_isStable
    (F : MarkedMap q I) [Fintype I] [DecidableEq I]
    [PrestableFamily F.toBase] {H : LineBundle V} (D : PolarizedDegree F H)
    (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
    [PrestableFamily (pullback.snd F.toBase y)]
    (hstable : ∀ C : Component (F.sourceFiber y),
      D.degreeLine.degree y C = 0 →
        0 < (normalizedDecoratedGraphOfNormalization F D K y).logCanonicalDegree
          ((normalizedVertexLift F y) C)) :
    (normalizedDecoratedGraphOfNormalization F D K y).IsStable := by
  intro vertex hdegree
  apply hstable ((normalizedVertexLift F y).symm vertex)
  calc
    D.degreeLine.degree y ((normalizedVertexLift F y).symm vertex) =
        ((normalizedDecoratedGraphOfNormalization F D K y).degree vertex : ℤ) := by
      rw [← (normalizedVertexLift F y).apply_symm_apply vertex]
      exact normalizedDecoratedGraphOfNormalization_degree_eq F D K y
        ((normalizedVertexLift F y).symm vertex)
    _ = 0 := by simp [hdegree]

/-! A geometric fibre graph is the canonical graph read from the normalized fibre.  In
particular, callers cannot replace its vertices, edges, endpoint map, or genera by supplied
data.  Stability is the numerical predicate on this canonical graph. -/
def GeometricFiberGraph (F : MarkedMap q I) [Fintype I] [DecidableEq I]
    [PrestableFamily F.toBase] {H : LineBundle V} (D : PolarizedDegree F H)
    (K : Type u) [Field K] [IsAlgClosed K] (y : Spec (.of K) ⟶ S)
    [PrestableFamily (pullback.snd F.toBase y)] : Prop :=
  (normalizedDecoratedGraph F D K y).IsStable

/-! Stability transports through the actual source-fibre isomorphism.  The only extra equation
needed by the decorated graph transport is the component carrying each smooth marking; the shared
smooth-point component lemma supplies this equation when constructing map-level transport. -/
theorem normalizedDecoratedGraph_isStable_of_iso
    {F G : MarkedMap q I} [Fintype I] [DecidableEq I]
    {H : LineBundle V} (e : F ≅ G) (D : PolarizedDegree F H)
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (.of K) ⟶ S)
    [PrestableFamily F.toBase] [PrestableFamily G.toBase]
    [PrestableFamily (pullback.snd F.toBase y)]
    [PrestableFamily (pullback.snd G.toBase y)]
    (hmark : ∀ i : I,
      normalizedMarkingVertex G y i =
        irreducibleComponentsEquivOfSchemeIso (baseChangeSourceIso e y)
          (normalizedMarkingVertex F y i)) :
    (normalizedDecoratedGraph G (D.ofIso e H) K y).IsStable ↔
      (normalizedDecoratedGraph F D K y).IsStable := by
  classical
  let E := baseChangeSourceIso e y
  let he' : E.inv ≫ pullback.snd F.toBase y = pullback.snd G.toBase y :=
    baseChangeHom_snd e.inv y
  let _ : LocallyOfFiniteType (pullback.snd F.toBase y) := inferInstance
  let _ : LocallyOfFiniteType (pullback.snd G.toBase y) := inferInstance
  let _ : QuasiCompact (pullback.snd F.toBase y) := inferInstance
  let _ : QuasiCompact (pullback.snd G.toBase y) := inferInstance
  let _ : IsNoetherian (pullback F.toBase y) :=
    isNoetherian_of_quasiCompact (f := pullback.snd F.toBase y)
  let _ : IsNoetherian (pullback G.toBase y) :=
    isNoetherian_of_quasiCompact (f := pullback.snd G.toBase y)
  let c := irreducibleComponentsEquivOfSchemeIso E
  have hc : c.symm = irreducibleComponentsEquivOfSchemeIso E.symm := by
    ext C x
    change x ∈ (c.symm C : Set _) ↔
      x ∈ (irreducibleComponentsEquivOfSchemeIso E.symm C : Set _)
    change E.hom x ∈ (C : Set _) ↔
      x ∈ (transportedComponent E.symm C : Set _)
    have ht := transportedComponent_mem E.symm C (E.hom x)
    have hx : E.symm.hom (E.hom x) = x := congrArg (fun k ↦ k x) E.hom_inv_id
    rw [hx] at ht
    exact ht
  have hgenus : ∀ C : Component (G.sourceFiber y),
      arithmeticGenus K
          (normalizedComponentToBase (pullback.snd F.toBase y) (c.symm C)) =
        arithmeticGenus K
          (normalizedComponentToBase (pullback.snd G.toBase y) C) := by
    intro C
    let iso := normalizedComponentSchemeIso (f := pullback.snd G.toBase y)
      (g := pullback.snd F.toBase y) E.symm C
    have hgen := arithmeticGenus_eq_of_scheme_iso iso
      (normalizedComponentToBase (pullback.snd F.toBase y)
        (transportedComponent E.symm C))
    rw [normalizedComponentSchemeIso_hom_toBase E.symm C he'] at hgen
    have hce : c.symm C = irreducibleComponentsEquivOfSchemeIso E.symm C := by
      ext x
      change x ∈ (c.symm C : Set _) ↔
        x ∈ (transportedComponent E.symm C : Set _)
      exact (transportedComponent_mem E.symm C (E.hom x)).trans (by simp)
    rw [hce]
    exact hgen.symm
  let cv : (normalizedDecoratedGraph G (D.ofIso e H) K y).toDualGraph.Vertex ≃
      (normalizedDecoratedGraph F D K y).toDualGraph.Vertex :=
    (normalizedVertexLift G y).symm.trans (c.symm.trans (normalizedVertexLift F y))
  let ce : (normalizedDecoratedGraph G (D.ofIso e H) K y).toDualGraph.Edge ≃
      (normalizedDecoratedGraph F D K y).toDualGraph.Edge :=
    (normalizedEdgeLift G y).symm.trans
      ((edgesEquivOfIso E.symm he').trans (normalizedEdgeLift F y))
  let cl : (normalizedDecoratedGraph G (D.ofIso e H) K y).Leg ≃
      (normalizedDecoratedGraph F D K y).Leg := Equiv.refl _
  symm
  apply StableMaps.DecoratedGraph.isStable_iff_of_endpoint_pairs
    (normalizedDecoratedGraph G (D.ofIso e H) K y)
    (normalizedDecoratedGraph F D K y) cv ce cl
  · intro edge
    let eg := (normalizedEdgeLift G y).symm edge
    change Sym2.map (normalizedVertexLift F y)
        (s(endpoint (pullback.snd F.toBase y) (edgesEquivOfIso E.symm he' eg) 0,
          endpoint (pullback.snd F.toBase y) (edgesEquivOfIso E.symm he' eg) 1)) =
      Sym2.map (normalizedVertexLift F y)
        (s(c.symm (endpoint (pullback.snd G.toBase y) eg 0),
          c.symm (endpoint (pullback.snd G.toBase y) eg 1)))
    rw [hc]
    exact congrArg (Sym2.map (normalizedVertexLift F y))
      (endpoints_edgesEquivOfIso E.symm he' eg)
  · intro leg
    let i : I := Equiv.ulift leg
    change (normalizedVertexLift F y) (normalizedMarkingVertex F y i) =
      cv ((normalizedVertexLift G y) (normalizedMarkingVertex G y i))
    have hm : c.symm (normalizedMarkingVertex G y i) =
        normalizedMarkingVertex F y i := by
      rw [hmark i, c.symm_apply_apply]
    change (normalizedVertexLift F y) (normalizedMarkingVertex F y i) =
      (normalizedVertexLift F y) (c.symm (normalizedMarkingVertex G y i))
    exact congrArg (normalizedVertexLift F y) hm.symm
  · intro vertex
    let C : Component (G.sourceFiber y) := (normalizedVertexLift G y).symm vertex
    let C' : Component (F.sourceFiber y) := c.symm C
    change arithmeticGenus K (normalizedComponentToBase (pullback.snd F.toBase y) C') =
      arithmeticGenus K (normalizedComponentToBase (pullback.snd G.toBase y) C)
    exact hgenus C
  · intro vertex
    let C : Component (G.sourceFiber y) := (normalizedVertexLift G y).symm vertex
    change (D.degreeLine.degree y (c.symm C)).toNat =
      ((D.ofIso e H).degreeLine.degree y C).toNat
    rfl

/-- A geometric stable map: every geometric fibre has a fully anchored stable decorated graph. -/
structure Stable (F : MarkedMap q I) [Fintype I] [DecidableEq I]
    (H : LineBundle V) : Type (max (u + 2) (v + 1)) where
  prestable : Prestable F
  polarizedDegree : PolarizedDegree F H
  fiberGraph : ∀ (K : Type u) [Field K] [IsAlgClosed K] (y : Spec (.of K) ⟶ S),
    letI := prestable.sourceFamily
    letI := PrestableFamily.pullback_snd F.toBase y
    GeometricFiberGraph F polarizedDegree K y

/-! This intermediate transport theorem isolates the sole geometric fact needed to transport
stability through a source isomorphism: a smooth marking has the component transported by the
source-fibre isomorphism.  The smooth-point component lemma supplies this equation for the public
map-level transport API. -/
def Stable.ofIso_of_normalizedMarkingVertex_eq
    {F G : MarkedMap q I} [Fintype I] [DecidableEq I]
    (e : F ≅ G) (H : LineBundle V) (hF : Stable F H)
    (hmark : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (y : Spec (.of K) ⟶ S) (i : I),
      normalizedMarkingVertex G y i =
        irreducibleComponentsEquivOfSchemeIso (baseChangeSourceIso e y)
          (normalizedMarkingVertex F y i)) :
    Stable G H where
  prestable := hF.prestable.of_iso e
  polarizedDegree := hF.polarizedDegree.ofIso e H
  fiberGraph := by
    intro K _ _ y
    let hFsource : PrestableFamily F.toBase := hF.prestable.sourceFamily
    let _ : PrestableFamily F.toBase := hFsource
    let hGsource : PrestableFamily G.toBase := (hF.prestable.of_iso e).sourceFamily
    let _ : PrestableFamily G.toBase := hGsource
    let hFy : PrestableFamily (pullback.snd F.toBase y) :=
      PrestableFamily.pullback_snd F.toBase y
    let _ : PrestableFamily (pullback.snd F.toBase y) := hFy
    let hGy : PrestableFamily (pullback.snd G.toBase y) :=
      PrestableFamily.pullback_snd G.toBase y
    let _ : PrestableFamily (pullback.snd G.toBase y) := hGy
    apply (normalizedDecoratedGraph_isStable_of_iso e hF.polarizedDegree y
      (fun i ↦ hmark K y i)).mpr
    exact hF.fiberGraph K y

/-! Target postcomposition leaves the normalized source graph unchanged.  The polarization degree
construction above carries the genuine constancy criterion to the new target, while its relative
line is the same source line, so the canonical fibre-graph proposition is transported directly. -/
def Stable.postcomposeOfReflectsConstancy
    {W : Scheme.{u}} {q' : W ⟶ S} [Fintype I] [DecidableEq I]
    (F : MarkedMap q I) (H : LineBundle W) (a : V ⟶ W) (ha : a ≫ q' = q)
    [Mono a] (hF : Stable F (H.pullback a))
    (hreflect : ReflectsComponentConstancy F a ha) :
    Stable (F.postcompose a ha) H where
  prestable := hF.prestable.postcompose a ha
  polarizedDegree :=
    hF.polarizedDegree.postcomposeOfReflectsConstancy F H a ha hreflect
  fiberGraph := by
    intro K _ _ y
    exact hF.fiberGraph K y

def Stable.postcomposeClosedImmersion
    {W : Scheme.{u}} {q' : W ⟶ S} [Fintype I] [DecidableEq I]
    (F : MarkedMap q I) (H : LineBundle W) (a : V ⟶ W) (ha : a ≫ q' = q)
    [IsClosedImmersion a] (hF : Stable F (H.pullback a)) :
    Stable (F.postcompose a ha) H :=
  hF.postcomposeOfReflectsConstancy F H a ha
    (reflectsComponentConstancy_of_isClosedImmersion F a ha)


/-- A proper contraction between marked maps, with a genuine isomorphism on the complements of
closed exceptional loci and connected point fibres. -/
structure Contraction (F G : MarkedMap q I) where
  hom : F ⟶ G
  proper : IsProper hom.hom
  sourceLocus : Set F.source
  targetLocus : Set G.source
  sourceLocus_isClosed : IsClosed sourceLocus
  targetLocus_isClosed : IsClosed targetLocus
  sourceComplement : Scheme.{u}
  targetComplement : Scheme.{u}
  sourceOpen : sourceComplement ⟶ F.source
  targetOpen : targetComplement ⟶ G.source
  sourceOpen_isOpen : IsOpenImmersion sourceOpen
  targetOpen_isOpen : IsOpenImmersion targetOpen
  sourceOpen_range : Set.range sourceOpen = sourceLocusᶜ
  targetOpen_range : Set.range targetOpen = targetLocusᶜ
  complementIso : sourceComplement ≅ targetComplement
  complement_commutes : complementIso.hom ≫ targetOpen = sourceOpen ≫ hom.hom
  contracts : Set.MapsTo hom.hom sourceLocus targetLocus
  connectedFibers : ∀ y : G.source, _root_.IsConnected (hom.hom ⁻¹' {y})

namespace Contraction

variable {F G : MarkedMap q I} (c : Contraction F G)

/-- A contraction agrees with its displayed complement isomorphism away from the exceptional
locus. -/
theorem hom_sourceOpen (x : c.sourceComplement) :
    c.hom.hom (c.sourceOpen x) = c.targetOpen (c.complementIso.hom x) := by
  rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply,
    ← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, c.complement_commutes]

/-- Stability of a contraction under arbitrary base change. -/
structure BaseChangeStable : Type (max (u + 2) (v + 1)) where
  pullbackContraction : ∀ {T : Scheme.{u}} (b : T ⟶ S),
    Contraction (F.baseChange b) (G.baseChange b)
  hom_eq : ∀ {T : Scheme.{u}} (b : T ⟶ S),
    (pullbackContraction b).hom = baseChangeHom c.hom b
  sourceLocus_eq : ∀ {T : Scheme.{u}} (b : T ⟶ S),
    (pullbackContraction b).sourceLocus =
      (CategoryTheory.Limits.pullback.fst F.toBase b) ⁻¹' c.sourceLocus
  targetLocus_eq : ∀ {T : Scheme.{u}} (b : T ⟶ S),
    (pullbackContraction b).targetLocus =
      (CategoryTheory.Limits.pullback.fst G.toBase b) ⁻¹' c.targetLocus

end Contraction

/-- Universal map-aware stabilization of a prestable marked map. -/
structure Stabilization (F : MarkedMap q I) [Fintype I] [DecidableEq I]
    (H : LineBundle V) : Type (max (u + 2) (v + 1)) where
  stabilized : MarkedMap q I
  stable : Stable stabilized H
  contraction : Contraction F stabilized
  baseChangeStable : contraction.BaseChangeStable
  stableAfterBaseChange : ∀ {T : Scheme.{u}} (b : T ⟶ S),
    Stable (stabilized.baseChange b)
      (H.pullback (CategoryTheory.Limits.pullback.fst q b))
  factor : ∀ (Z : MarkedMap q I) [Fintype I] [DecidableEq I], Stable Z H →
    (f : F ⟶ Z) → ∃! g : stabilized ⟶ Z, contraction.hom ≫ g = f

/-- A construction engine for universal stabilization. -/
structure StabilizationEngine (q : V ⟶ S) : Type (max (u + 2) (v + 1)) where
  stabilize : ∀ {A : Type v} [Fintype A] [DecidableEq A]
    (F : MarkedMap q A) (H : LineBundle V),
    Prestable F → PolarizedDegree F H → Stabilization F H

/-- The diagram obtained by forgetting one marking before stabilization. -/
abbrev forgetMarking (F : MarkedMap q I) (forgotten : I) :
    MarkedMap q {i : I // i ≠ forgotten} :=
  F.restrictMarkings Subtype.val

/-- Prestability after forgetting a marking. -/
theorem Prestable.forgetMarking {F : MarkedMap q I} (hF : Prestable F) (forgotten : I) :
    Prestable (F.forgetMarking forgotten) :=
  hF.restrictMarkings Subtype.val Subtype.val_injective

/-- Polarization degree is unchanged when a marking is forgotten. -/
def PolarizedDegree.forgetMarking {F : MarkedMap q I} {H : LineBundle V}
    (D : PolarizedDegree F H) (forgotten : I) :
    PolarizedDegree (F.forgetMarking forgotten) H where
  degreeLine := D.degreeLine
  lineIso := D.lineIso
  nonnegative := D.nonnegative
  degree_eq_zero_iff := D.degree_eq_zero_iff

/-- Forget one marking and perform the required map-aware stabilization. -/
def StabilizationEngine.forget
    (engine : StabilizationEngine q)
    {F : MarkedMap q I} [Fintype I] [DecidableEq I]
    (H : LineBundle V) (prestable : Prestable F) (degree : PolarizedDegree F H)
    (forgotten : I) : Stabilization (F.forgetMarking forgotten) H :=
  engine.stabilize (F.forgetMarking forgotten) H
    (prestable.forgetMarking forgotten) (degree.forgetMarking forgotten)

/-- Scheme-theoretic geometry of an external gluing pushout. -/
structure ExternalGluingGeometry {F : MarkedMap q I} {G : MarkedMap q J}
    {D : ExternalGluingData F G} (P : ExternalPushout D) :
    Type (max (u + 2) (v + 1) (w + 1)) where
  prestable : Prestable P.markedMap
  seam : S ⟶ P.cocone.pt
  seam_eq : seam = F.marking D.left ≫ P.cocone.inl
  seam_toBase : seam ≫ P.toBase = 𝟙 S
  seamPoint : ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S),
    P.markedMap.sourceFiber y
  seamPoint_fst : ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S),
    CategoryTheory.Limits.pullback.fst P.toBase y (seamPoint K y) =
      seam (y (genericPoint (Spec (.of K))))
  seamPoint_snd : ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S),
    CategoryTheory.Limits.pullback.snd P.toBase y (seamPoint K y) =
      genericPoint (Spec (.of K))
  seam_node : ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S),
    Nonempty (NodeChartAt (CategoryTheory.Limits.pullback.snd P.toBase y) (seamPoint K y))
  baseChangePushout : ∀ {T : Scheme.{u}} (b : T ⟶ S),
    ExternalPushout (D.baseChange b)
  baseChangeComparison : ∀ {T : Scheme.{u}} (b : T ⟶ S),
    (P.markedMap.baseChange b) ≅ (baseChangePushout b).markedMap

/-- Scheme-theoretic geometry of a self-gluing coequalizer. -/
structure SelfGluingGeometry {F : MarkedMap q I} {D : SelfGluingData F}
    (P : SelfCoequalizer D) : Type (max (u + 2) (v + 1)) where
  prestable : Prestable P.markedMap
  seam : S ⟶ P.cofork.pt
  seam_eq : seam = F.marking D.first ≫ P.cofork.π
  seam_toBase : seam ≫ P.toBase = 𝟙 S
  seamPoint : ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S),
    P.markedMap.sourceFiber y
  seamPoint_fst : ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S),
    CategoryTheory.Limits.pullback.fst P.toBase y (seamPoint K y) =
      seam (y (genericPoint (Spec (.of K))))
  seamPoint_snd : ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S),
    CategoryTheory.Limits.pullback.snd P.toBase y (seamPoint K y) =
      genericPoint (Spec (.of K))
  seam_node : ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S),
    Nonempty (NodeChartAt (CategoryTheory.Limits.pullback.snd P.toBase y) (seamPoint K y))
  baseChangeCoequalizer : ∀ {T : Scheme.{u}} (b : T ⟶ S),
    SelfCoequalizer (D.baseChange b)
  baseChangeComparison : ∀ {T : Scheme.{u}} (b : T ⟶ S),
    (P.markedMap.baseChange b) ≅ (baseChangeCoequalizer b).markedMap

/-- Stable geometric external gluing. -/
structure StableExternalGluing {F : MarkedMap q I} {G : MarkedMap q J}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (H : LineBundle V) (D : ExternalGluingData F G) :
    Type (max (u + 2) (v + 1) (w + 1)) where
  pushout : ExternalPushout D
  geometry : ExternalGluingGeometry pushout
  stable : Stable pushout.markedMap H

/-- Stable geometric self-gluing. -/
structure StableSelfGluing {F : MarkedMap q I} [Fintype I] [DecidableEq I]
    (H : LineBundle V) (D : SelfGluingData F) : Type (max (u + 2) (v + 1)) where
  coequalizer : SelfCoequalizer D
  geometry : SelfGluingGeometry coequalizer
  stable : Stable coequalizer.markedMap H

set_option linter.checkUnivs false in
/-- Construction interface for base-change-compatible stable external and self gluing. -/
structure StableGluingEngine (q : V ⟶ S) :
    Type (max (u + 2) (v + 1) (w + 1)) where
  external : ∀ {A : Type v} {B : Type w}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {F : MarkedMap q A} {G : MarkedMap q B} (H : LineBundle V),
    Stable F H → Stable G H → (D : ExternalGluingData F G) →
      StableExternalGluing H D
  self : ∀ {A : Type v} [Fintype A] [DecidableEq A]
    {F : MarkedMap q A} (H : LineBundle V), Stable F H →
    (D : SelfGluingData F) → StableSelfGluing H D

end

end GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap
