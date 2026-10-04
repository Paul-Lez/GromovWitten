/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.CechGroupoidChow
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperPushforwardDivisor
import GromovWitten.AlgebraicGeometry.Stacks.EtaleAtlasDiagonal
import GromovWitten.AlgebraicGeometry.Stacks.EtaleSliceLocalSlicing

/-!
# The groupoid of an étale chart and the Isom groupoid over a refinement

Let `C` be an étale surjective chart of an fppf stack `X` (`C.IsEtaleSurjective`), whose scheme is
locally of finite type over a field `k` (structure morphism `sC`). Its scheme-level self-overlap
`C.selfOverlapScheme` (a chosen scheme representing `C.scheme ×_X C.scheme`) has étale surjective
projections, so `C` defines an étale presentation groupoid `C.etaleGroupoid hC sC`, graded by the
canonical dimension functions (transcendence degree of residue fields over `k`), and hence the
genuine Vistoli rational Chow group `C.vistoliChow hC sC i` of round 23.

Given an étale morphism `hom : P ⟶ C.scheme` from a scheme, the Isom scheme of the two chart
objects pulled back to `P ⨯ P` (the ordinary fibre product of `P ⨯ P ⟶ C.scheme ⨯ C.scheme`
with the self-overlap pairing) is the arrow scheme of a second étale presentation groupoid
`C.isomGroupoid hC hom sC` with atlas `P`. When `hom` is moreover surjective, `hom` and the
projection of the Isom scheme to the self-overlap form a Morita map
`C.moritaToChart hC hom sC` to the chart groupoid. Everything in this file is scheme-level: no
2-cells of the stack are used beyond the existence of the self-overlap and its unit section.

## Main results

* `StackChart.selfOverlapScheme_fst_etale`, `_fst_surjective`, `_snd_etale`, `_snd_surjective`:
  the legs of the self-overlap scheme of an étale surjective chart are étale and surjective;
  `_fst_quasiCompact`, `_snd_quasiCompact`: they are quasi-compact when the chart is representably
  quasi-compact.
* `StackChart.etaleGroupoid`, `StackChart.vistoliChow`: the étale presentation groupoid of a chart
  and its Vistoli rational Chow group.
* `StackChart.isPullback_isomToFirst`: the Isom scheme is the iterated fibre product
  `(P ×_C R) ×_C P`; consequently `isomSrc_etale`, `isomTgt_etale` (for `hom` étale) and
  `isomSrc_quasiCompact`, `isomTgt_quasiCompact` (for `hom` quasi-compact and `C` representably
  quasi-compact).
* `StackChart.isomGroupoid`: the Isom groupoid over `P`.
* `StackChart.exists_isomPoint`: points of the self-overlap together with points of `P` over its
  two legs lift to points of the Isom scheme.
* `StackChart.unitW`, `StackChart.residueFieldMap_unitW_eq`, `StackChart.residueFieldMap_unit_eq`:
  the unit section of the Isom groupoid; along a unit arrow the residue field maps of source and
  target agree.
* `StackChart.moritaToChart`: for `hom` étale surjective, the Morita map from the Isom groupoid
  to the chart groupoid, with all conditions (F0)–(F3) proved.

The generic residue-field lemmas `ChartGroupoid.residueFieldMap_eq_of_comp_eq` and
`ChartGroupoid.residueFieldMap_comp_apply_congr` live in the namespace
`GromovWitten.AlgebraicGeometry.IntersectionTheory`; the chart constructions live in
`GromovWitten.AlgebraicGeometry.StackChart` so that dot notation `C.etaleGroupoid` applies.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace ChartGroupoid

/-- **Residue maps of two morphisms agreeing after a section.** If `φ ≫ f = φ ≫ g`, then at a
point `φ t` the residue field maps of `f` and `g` agree (after identifying `f (φ t) = g (φ t)`):
both become equal after composing with the injective field map `φ.residueFieldMap t`. -/
theorem residueFieldMap_eq_of_comp_eq {T Y Z : Scheme.{u}} (φ : T ⟶ Y) (f g : Y ⟶ Z)
    (e : φ ≫ f = φ ≫ g) (t : T) (h : f.base (φ.base t) = g.base (φ.base t)) :
    f.residueFieldMap (φ.base t) =
      (Z.residueFieldCongr h).hom ≫ g.residueFieldMap (φ.base t) := by
  have key : f.residueFieldMap (φ.base t) ≫ φ.residueFieldMap t =
      ((Z.residueFieldCongr h).hom ≫ g.residueFieldMap (φ.base t)) ≫ φ.residueFieldMap t := by
    rw [← Scheme.residueFieldMap_comp, Category.assoc, ← Scheme.residueFieldMap_comp]
    exact Scheme.Hom.residueFieldMap_congr e t
  ext a
  exact (φ.residueFieldMap t).hom.injective (congrArg (fun m ↦ m.hom a) key)

/-- Residue maps along a composite `φ ≫ f = f'`, with the base points identified through
`residueFieldCongr`. -/
theorem residueFieldMap_comp_apply_congr {T Y Z : Scheme.{u}} (φ : T ⟶ Y) (f : Y ⟶ Z)
    (f' : T ⟶ Z) (e : φ ≫ f = f') (t : T) {z : Z} (h₁ : f.base (φ.base t) = z)
    (h₂ : f'.base t = z) (a : Z.residueField z) :
    φ.residueFieldMap t (f.residueFieldMap (φ.base t) ((Z.residueFieldCongr h₁).inv a)) =
      f'.residueFieldMap t ((Z.residueFieldCongr h₂).inv a) := by
  subst e h₁
  rw [Scheme.residueFieldMap_comp]
  rfl

end ChartGroupoid

end GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace GromovWitten.AlgebraicGeometry.StackChart

open IntersectionTheory IntersectionTheory.ChartGroupoid FiniteTypeDimension CechGroupoidChow
  ProperPushforwardDivisor

variable {X : FppfStack.{u}} (C : StackChart X)

/-! ## The legs of the self-overlap scheme -/

/-- An étale surjective chart is representable.  (A named form of
`isRepresentable_of_hasRepresentableProperty`, used so that the representability proof inside
the self-overlap scheme does not mention the morphism property `Etale ⊓ Surjective`.) -/
theorem isRepresentable_of_isEtaleSurjective (hC : C.IsEtaleSurjective) : C.IsRepresentable :=
  C.isRepresentable_of_hasRepresentableProperty _ hC

section SelfOverlap

variable (hC' : C.IsRepresentable)

/-- The first projection of the self-overlap scheme of an étale surjective chart is étale. -/
theorem selfOverlapScheme_fst_etale (hC : C.IsEtaleSurjective) :
    Etale (C.selfOverlapScheme hC').fst :=
  (C.selfOverlapScheme_fst_prop hC' hC).1

/-- The first projection of the self-overlap scheme of an étale surjective chart is
surjective. -/
theorem selfOverlapScheme_fst_surjective (hC : C.IsEtaleSurjective) :
    Surjective (C.selfOverlapScheme hC').fst :=
  (C.selfOverlapScheme_fst_prop hC' hC).2

/-- The second projection of the self-overlap scheme of an étale surjective chart is étale
(apply the chart condition to the leg-swapped presentation). -/
theorem selfOverlapScheme_snd_etale (hC : C.IsEtaleSurjective) :
    Etale (C.selfOverlapScheme hC').snd :=
  (hC.2 C.scheme C.tautObj (C.selfOverlapScheme hC').selfSwap).1

/-- The second projection of the self-overlap scheme of an étale surjective chart is
surjective. -/
theorem selfOverlapScheme_snd_surjective (hC : C.IsEtaleSurjective) :
    Surjective (C.selfOverlapScheme hC').snd :=
  (hC.2 C.scheme C.tautObj (C.selfOverlapScheme hC').selfSwap).2

/-- The first projection of the self-overlap scheme of a representably quasi-compact chart is
quasi-compact. -/
theorem selfOverlapScheme_fst_quasiCompact
    (hCq : C.HasRepresentableProperty @QuasiCompact) :
    QuasiCompact (C.selfOverlapScheme hC').fst :=
  hCq.2 C.scheme C.tautObj (C.selfOverlapScheme hC')

/-- The second projection of the self-overlap scheme of a representably quasi-compact chart is
quasi-compact. -/
theorem selfOverlapScheme_snd_quasiCompact
    (hCq : C.HasRepresentableProperty @QuasiCompact) :
    QuasiCompact (C.selfOverlapScheme hC').snd :=
  hCq.2 C.scheme C.tautObj (C.selfOverlapScheme hC').selfSwap

end SelfOverlap

/-! ## The étale presentation groupoid of a chart -/

section EtaleGroupoid

variable {k : Type u} [Field k]

/-- **The étale presentation groupoid of an étale surjective chart** `C` whose scheme is locally
of finite type over a field `k` (structure morphism `sC`): the atlas is `C.scheme`, the arrows are
the scheme-level self-overlap `C.selfOverlapScheme`, source and target are its two projections,
and both schemes carry the canonical dimension functions (transcendence degree of residue fields
over `k`). -/
noncomputable abbrev etaleGroupoid (hC : C.IsEtaleSurjective)
    (sC : C.scheme ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sC] :
    EtalePresentationGroupoid.{u} where
  base := C.scheme
  arrows := (C.selfOverlapScheme (C.isRepresentable_of_isEtaleSurjective hC)).space
  baseDim := dimensionFunction sC
  arrowsDim :=
    haveI := C.selfOverlapScheme_fst_etale (C.isRepresentable_of_isEtaleSurjective hC) hC
    dimensionFunction
      ((C.selfOverlapScheme (C.isRepresentable_of_isEtaleSurjective hC)).fst ≫ sC)
  src := (C.selfOverlapScheme (C.isRepresentable_of_isEtaleSurjective hC)).fst
  tgt := (C.selfOverlapScheme (C.isRepresentable_of_isEtaleSurjective hC)).snd
  src_etale := C.selfOverlapScheme_fst_etale _ hC
  tgt_etale := C.selfOverlapScheme_snd_etale _ hC
  src_dim r := by
    have := C.selfOverlapScheme_fst_etale (C.isRepresentable_of_isEtaleSurjective hC) hC
    exact dimensionFunction_comp_etale sC _ r
  tgt_dim r := by
    have := C.selfOverlapScheme_fst_etale (C.isRepresentable_of_isEtaleSurjective hC) hC
    have := C.selfOverlapScheme_snd_etale (C.isRepresentable_of_isEtaleSurjective hC) hC
    have h := congrArg (fun d : DimensionFunction _ ↦ d r) (dimensionFunction_eq
      (dimensionFunction
        ((C.selfOverlapScheme (C.isRepresentable_of_isEtaleSurjective hC)).fst ≫ sC))
      (dimensionFunction
        ((C.selfOverlapScheme (C.isRepresentable_of_isEtaleSurjective hC)).snd ≫ sC)))
    exact h.trans (dimensionFunction_comp_etale sC _ r)

variable (hC : C.IsEtaleSurjective) (sC : C.scheme ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType sC]

/-- The atlas of the chart groupoid is the chart scheme. -/
@[simp] theorem etaleGroupoid_base : (C.etaleGroupoid hC sC).base = C.scheme := rfl

/-- The arrows of the chart groupoid form the self-overlap scheme. -/
@[simp] theorem etaleGroupoid_arrows :
    (C.etaleGroupoid hC sC).arrows =
      (C.selfOverlapScheme (C.isRepresentable_of_isEtaleSurjective hC)).space := rfl

/-- The source map of the chart groupoid is the first self-overlap projection. -/
@[simp] theorem etaleGroupoid_src :
    (C.etaleGroupoid hC sC).src =
      (C.selfOverlapScheme (C.isRepresentable_of_isEtaleSurjective hC)).fst := rfl

/-- The target map of the chart groupoid is the second self-overlap
projection. -/
@[simp] theorem etaleGroupoid_tgt :
    (C.etaleGroupoid hC sC).tgt =
      (C.selfOverlapScheme (C.isRepresentable_of_isEtaleSurjective hC)).snd := rfl

/-- The atlas of the chart groupoid carries the canonical dimension function of
`sC`. -/
@[simp] theorem etaleGroupoid_baseDim :
    (C.etaleGroupoid hC sC).baseDim = dimensionFunction sC := rfl

/-- **The Vistoli rational Chow group of an étale surjective chart**: the genuine Vistoli group
`EtalePresentationGroupoid.vistoliChow` (invariant cycles modulo divisors of invariant systems)
of the chart groupoid `C.etaleGroupoid hC sC`. -/
noncomputable abbrev vistoliChow (i : ℤ) : Type u := (C.etaleGroupoid hC sC).vistoliChow i

end EtaleGroupoid

/-! ## The Isom groupoid over an étale cover of the chart scheme -/

section IsomGroupoid

variable (hC : C.IsEtaleSurjective) {P : Scheme.{u}} (hom : P ⟶ C.scheme)

set_option hygiene false in
/-- The scheme-level self-overlap of the chart `C`. -/
local notation "𝓟" => C.selfOverlapScheme (C.isRepresentable_of_isEtaleSurjective hC)

/-- **The Isom scheme over `P ⨯ P`**: the Isom scheme of the two chart objects of `C` obtained
by pulling back along `prod.fst ≫ hom` and `prod.snd ≫ hom`, i.e. the ordinary fibre product of
`P ⨯ P ⟶ C.scheme ⨯ C.scheme` with the self-overlap pairing. -/
noncomputable abbrev isomArrows : Scheme.{u} :=
  C.isomScheme (C.isRepresentable_of_isEtaleSurjective hC)
    ((prod.fst : P ⨯ P ⟶ P) ≫ hom) ((prod.snd : P ⨯ P ⟶ P) ≫ hom)

/-- The map from the Isom scheme to the self-overlap scheme of the chart. -/
noncomputable abbrev isomToOverlap : C.isomArrows hC hom ⟶ (𝓟).space :=
  C.isomScheme_toOverlap _ _ _

/-- The source map of the Isom groupoid. -/
noncomputable abbrev isomSrc : C.isomArrows hC hom ⟶ P :=
  C.isomScheme_map _ _ _ ≫ prod.fst

/-- The target map of the Isom groupoid. -/
noncomputable abbrev isomTgt : C.isomArrows hC hom ⟶ P :=
  C.isomScheme_map _ _ _ ≫ prod.snd

/-- The source of an Isom arrow lies over the first leg of its image in the self-overlap. -/
theorem isomSrc_comp : C.isomSrc hC hom ≫ hom = C.isomToOverlap hC hom ≫ (𝓟).fst := by
  rw [Category.assoc]
  exact C.isomScheme_fst_eq _ _ _

/-- The target of an Isom arrow lies over the second leg of its image in the self-overlap. -/
theorem isomTgt_comp : C.isomTgt hC hom ≫ hom = C.isomToOverlap hC hom ≫ (𝓟).snd := by
  rw [Category.assoc]
  exact C.isomScheme_snd_eq _ _ _

/-- The map from the Isom scheme to `P ×_{C.scheme} (self-overlap)` (via the first leg) given by
the source and the image in the self-overlap. -/
noncomputable abbrev isomToFirst : C.isomArrows hC hom ⟶ pullback hom (𝓟).fst :=
  pullback.lift (C.isomSrc hC hom) (C.isomToOverlap hC hom) (C.isomSrc_comp hC hom)

/-- The first component of `isomToFirst` is the source map. -/
theorem isomToFirst_fst : C.isomToFirst hC hom ≫ pullback.fst _ _ = C.isomSrc hC hom :=
  pullback.lift_fst _ _ _

/-- The second component of `isomToFirst` is the map to the self-overlap. -/
theorem isomToFirst_snd :
    C.isomToFirst hC hom ≫ pullback.snd _ _ = C.isomToOverlap hC hom :=
  pullback.lift_snd _ _ _

/-- **(D.1.1) The Isom scheme as an iterated fibre product.** The square
`W ⟶ P ×_{C} R`, `W ⟶ P` (target), `P ×_{C} R ⟶ R ⟶ C` (second leg), `P ⟶ C` (`hom`) is a
pullback square, where `R` is the self-overlap scheme and `W` the Isom scheme. -/
theorem isPullback_isomToFirst :
    IsPullback (C.isomToFirst hC hom) (C.isomTgt hC hom) (pullback.snd hom (𝓟).fst ≫ (𝓟).snd)
      hom := by
  have w : C.isomToFirst hC hom ≫ pullback.snd hom (𝓟).fst ≫ (𝓟).snd = C.isomTgt hC hom ≫ hom := by
    rw [reassoc_of% (C.isomToFirst_snd hC hom), isomTgt_comp]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w (fun s ↦ pullback.lift
      (prod.lift (s.fst ≫ pullback.fst _ _) s.snd) (s.fst ≫ pullback.snd _ _) ?_) ?_ ?_ ?_)
  · apply prod.hom_ext
    · simp only [isomPair, selfOverlapPair, Category.assoc, prod.lift_fst, prod.lift_fst_assoc]
      rw [pullback.condition]
    · simp only [isomPair, selfOverlapPair, Category.assoc, prod.lift_snd, prod.lift_snd_assoc]
      exact s.condition.symm
  · intro s
    apply pullback.hom_ext
    · rw [Category.assoc, isomToFirst_fst]
      simp only [isomSrc, isomScheme_map, pullback.lift_fst_assoc, prod.lift_fst]
    · rw [Category.assoc, isomToFirst_snd]
      simp only [isomToOverlap, isomScheme_toOverlap, pullback.lift_snd]
  · intro s
    simp only [isomTgt, isomScheme_map, pullback.lift_fst_assoc, prod.lift_snd]
  · intro s m h₁ h₂
    apply pullback.hom_ext
    · apply prod.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, prod.lift_fst]
        rw [← h₁, Category.assoc, isomToFirst_fst]
      · simp only [Category.assoc, pullback.lift_fst, prod.lift_snd]
        rw [← h₂]
    · simp only [pullback.lift_snd]
      rw [← h₁, Category.assoc, isomToFirst_snd]

/-- The source map of the Isom groupoid is étale. -/
theorem isomSrc_etale [Etale hom] : Etale (C.isomSrc hC hom) := by
  have := C.selfOverlapScheme_fst_etale (C.isRepresentable_of_isEtaleSurjective hC) hC
  have : Etale (C.isomToFirst hC hom) :=
    MorphismProperty.of_isPullback (P := @Etale) (C.isPullback_isomToFirst hC hom).flip
      inferInstance
  rw [← C.isomToFirst_fst hC hom]
  infer_instance

/-- The target map of the Isom groupoid is étale. -/
theorem isomTgt_etale [Etale hom] : Etale (C.isomTgt hC hom) := by
  have := C.selfOverlapScheme_snd_etale (C.isRepresentable_of_isEtaleSurjective hC) hC
  exact MorphismProperty.of_isPullback (P := @Etale) (C.isPullback_isomToFirst hC hom)
    inferInstance

/-- The source map of the Isom groupoid is quasi-compact. -/
theorem isomSrc_quasiCompact (hCq : C.HasRepresentableProperty @QuasiCompact)
    [QuasiCompact hom] : QuasiCompact (C.isomSrc hC hom) := by
  have := C.selfOverlapScheme_fst_quasiCompact
    (C.isRepresentable_of_isEtaleSurjective hC) hCq
  have : QuasiCompact (C.isomToFirst hC hom) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (C.isPullback_isomToFirst hC hom).flip
      inferInstance
  rw [← C.isomToFirst_fst hC hom]
  infer_instance

/-- The target map of the Isom groupoid is quasi-compact. -/
theorem isomTgt_quasiCompact (hCq : C.HasRepresentableProperty @QuasiCompact)
    [QuasiCompact hom] : QuasiCompact (C.isomTgt hC hom) := by
  have := C.selfOverlapScheme_snd_quasiCompact
    (C.isRepresentable_of_isEtaleSurjective hC) hCq
  exact MorphismProperty.of_isPullback (P := @QuasiCompact) (C.isPullback_isomToFirst hC hom)
    inferInstance

/-- **(D.1.3) Points of the Isom scheme from compatible points.** Given a point `r` of the
self-overlap scheme and points `u'`, `v'` of `P` over its two legs, there is a point of the Isom
scheme with source `u'`, target `v'` and image `r` in the self-overlap. -/
theorem exists_isomPoint (r : (𝓟).space) (u' v' : P) (hu : hom.base u' = (𝓟).fst.base r)
    (hv : hom.base v' = (𝓟).snd.base r) :
    ∃ w : C.isomArrows hC hom, (C.isomSrc hC hom).base w = u' ∧
      (C.isomTgt hC hom).base w = v' ∧ (C.isomToOverlap hC hom).base w = r := by
  obtain ⟨z₁, hz₁, hz₁'⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := hom) (g := (𝓟).fst) u' r hu
  obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd hom (𝓟).fst ≫ (𝓟).snd) (g := hom) z₁ v'
    (by rw [Scheme.Hom.comp_apply, hz₁', hv])
  have h := C.isPullback_isomToFirst hC hom
  have e₁ : h.isoPullback.inv ≫ C.isomToFirst hC hom = pullback.fst _ _ := h.isoPullback_inv_fst
  have e₂ : h.isoPullback.inv ≫ C.isomTgt hC hom = pullback.snd _ _ := h.isoPullback_inv_snd
  have hΦ : (C.isomToFirst hC hom).base (h.isoPullback.inv.base z) = z₁ := by
    rw [← Scheme.Hom.comp_apply, e₁, hz]
  refine ⟨h.isoPullback.inv.base z, ?_, ?_, ?_⟩
  · rw [← C.isomToFirst_fst hC hom, Scheme.Hom.comp_apply, hΦ, hz₁]
  · rw [← Scheme.Hom.comp_apply, e₂, hz']
  · rw [← C.isomToFirst_snd hC hom, Scheme.Hom.comp_apply, hΦ, hz₁']

/-- **(D.1.4) The unit section of the Isom groupoid**: the arrow over `(u', u')` given by the
unit of the self-overlap at `hom u'`. -/
noncomputable def unitW : P ⟶ C.isomArrows hC hom :=
  pullback.lift (prod.lift (𝟙 P) (𝟙 P)) (hom ≫ C.selfOverlapUnit (𝓟)) (by
    apply prod.hom_ext
    · simp only [isomPair, selfOverlapPair, Category.assoc, prod.lift_fst, prod.lift_fst_assoc,
        selfOverlapUnit_fst, Category.id_comp, Category.comp_id]
    · simp only [isomPair, selfOverlapPair, Category.assoc, prod.lift_snd, prod.lift_snd_assoc,
        selfOverlapUnit_snd, Category.id_comp, Category.comp_id])

/-- The unit section is a section of the source map. -/
theorem unitW_src : C.unitW hC hom ≫ C.isomSrc hC hom = 𝟙 P := by
  simp only [unitW, isomSrc, isomScheme_map, pullback.lift_fst_assoc, prod.lift_fst]

/-- The unit section is a section of the target map. -/
theorem unitW_tgt : C.unitW hC hom ≫ C.isomTgt hC hom = 𝟙 P := by
  simp only [unitW, isomTgt, isomScheme_map, pullback.lift_fst_assoc, prod.lift_snd]

/-- The unit section lies over the unit section of the self-overlap. -/
theorem unitW_toOverlap :
    C.unitW hC hom ≫ C.isomToOverlap hC hom = hom ≫ C.selfOverlapUnit (𝓟) :=
  pullback.lift_snd _ _ _

/-- The source of the unit arrow at `u'` is `u'`. -/
@[simp] theorem unitW_src_apply (u' : P) :
    (C.isomSrc hC hom).base ((C.unitW hC hom).base u') = u' := by
  rw [← Scheme.Hom.comp_apply, unitW_src]
  rfl

/-- The target of the unit arrow at `u'` is `u'`. -/
@[simp] theorem unitW_tgt_apply (u' : P) :
    (C.isomTgt hC hom).base ((C.unitW hC hom).base u') = u' := by
  rw [← Scheme.Hom.comp_apply, unitW_tgt]
  rfl

/-- The unit arrow at `u'` is a self-arrow of `u'` along which the residue field maps of source
and target agree. -/
theorem residueFieldMap_unitW_eq (u' : P)
    (h : (C.isomSrc hC hom).base ((C.unitW hC hom).base u') =
      (C.isomTgt hC hom).base ((C.unitW hC hom).base u')) :
    (C.isomSrc hC hom).residueFieldMap ((C.unitW hC hom).base u') =
      (P.residueFieldCongr h).hom ≫
        (C.isomTgt hC hom).residueFieldMap ((C.unitW hC hom).base u') :=
  residueFieldMap_eq_of_comp_eq _ _ _ (by rw [unitW_src, unitW_tgt]) u' h

/-- **(D.1.4) Residue compatibility of the unit arrows**, in the shape of
`MoritaMap.exists_arrow_over_identity`: the two residue field maps `κ(hom u') → κ(unitW u')`
induced by `isomSrc ≫ hom` and `isomTgt ≫ hom` agree. -/
theorem residueFieldMap_unit_eq (u' : P)
    (h : (C.isomSrc hC hom ≫ hom).base ((C.unitW hC hom).base u') =
      (C.isomTgt hC hom ≫ hom).base ((C.unitW hC hom).base u')) :
    (C.isomSrc hC hom ≫ hom).residueFieldMap ((C.unitW hC hom).base u') =
      (C.scheme.residueFieldCongr h).hom ≫
        (C.isomTgt hC hom ≫ hom).residueFieldMap ((C.unitW hC hom).base u') :=
  residueFieldMap_eq_of_comp_eq _ _ _
    (by rw [← Category.assoc, unitW_src, ← Category.assoc, unitW_tgt]) u' h

/-- The map from the Čech scheme `P ×_{C.scheme} P` to the Isom scheme: a pair of points of `P`
with the same image `c` in the chart scheme goes to the Isom arrow given by the unit at `c`. -/
noncomputable def cechToIsom : pullback hom hom ⟶ C.isomArrows hC hom :=
  pullback.lift (prod.lift (pullback.fst hom hom) (pullback.snd hom hom))
    (pullback.fst hom hom ≫ hom ≫ C.selfOverlapUnit (𝓟)) (by
    apply prod.hom_ext
    · simp only [isomPair, selfOverlapPair, Category.assoc, prod.lift_fst, prod.lift_fst_assoc,
        selfOverlapUnit_fst, Category.comp_id]
    · simp only [isomPair, selfOverlapPair, Category.assoc, prod.lift_snd, prod.lift_snd_assoc,
        selfOverlapUnit_snd, Category.comp_id]
      exact pullback.condition.symm)

/-- The source of `cechToIsom z` is the first projection of `z`. -/
theorem cechToIsom_src : C.cechToIsom hC hom ≫ C.isomSrc hC hom = pullback.fst hom hom := by
  simp only [cechToIsom, isomSrc, isomScheme_map, pullback.lift_fst_assoc, prod.lift_fst]

/-- The target of `cechToIsom z` is the second projection of `z`. -/
theorem cechToIsom_tgt : C.cechToIsom hC hom ≫ C.isomTgt hC hom = pullback.snd hom hom := by
  simp only [cechToIsom, isomTgt, isomScheme_map, pullback.lift_fst_assoc, prod.lift_snd]

section Groupoid

variable {k : Type u} [Field k]

/-- **(D.1.2) The Isom groupoid over an étale cover of the chart scheme.** For an étale
surjective chart `C` with scheme locally of finite type over `k` (structure morphism `sC`) and an
étale morphism `hom : P ⟶ C.scheme`: the atlas is `P`, the arrows are the Isom scheme
`C.isomArrows hC hom` over `P ⨯ P`, source and target are its two projections to `P` (étale by
`isomSrc_etale`, `isomTgt_etale`), and both schemes carry the canonical dimension functions
over `k` (for the structure morphism `hom ≫ sC` of `P`). -/
noncomputable abbrev isomGroupoid [Etale hom] (sC : C.scheme ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sC] : EtalePresentationGroupoid.{u} where
  base := P
  arrows := C.isomArrows hC hom
  baseDim := dimensionFunction (hom ≫ sC)
  arrowsDim :=
    haveI := C.isomSrc_etale hC hom
    dimensionFunction (C.isomSrc hC hom ≫ hom ≫ sC)
  src := C.isomSrc hC hom
  tgt := C.isomTgt hC hom
  src_etale := C.isomSrc_etale hC hom
  tgt_etale := C.isomTgt_etale hC hom
  src_dim r := by
    have := C.isomSrc_etale hC hom
    exact dimensionFunction_comp_etale (hom ≫ sC) _ r
  tgt_dim r := by
    have := C.isomSrc_etale hC hom
    have := C.isomTgt_etale hC hom
    have h := congrArg (fun d : DimensionFunction _ ↦ d r) (dimensionFunction_eq
      (dimensionFunction (C.isomSrc hC hom ≫ hom ≫ sC))
      (dimensionFunction (C.isomTgt hC hom ≫ hom ≫ sC)))
    exact h.trans (dimensionFunction_comp_etale (hom ≫ sC) _ r)

variable [Etale hom] (sC : C.scheme ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sC]

/-- The atlas of the Isom groupoid is `P`. -/
@[simp] theorem isomGroupoid_base : (C.isomGroupoid hC hom sC).base = P := rfl

/-- The arrows of the Isom groupoid form the Isom scheme. -/
@[simp] theorem isomGroupoid_arrows :
    (C.isomGroupoid hC hom sC).arrows = C.isomArrows hC hom := rfl

/-- The source map of the Isom groupoid is `isomSrc`. -/
@[simp] theorem isomGroupoid_src : (C.isomGroupoid hC hom sC).src = C.isomSrc hC hom := rfl

/-- The target map of the Isom groupoid is `isomTgt`. -/
@[simp] theorem isomGroupoid_tgt : (C.isomGroupoid hC hom sC).tgt = C.isomTgt hC hom := rfl

/-- The atlas of the Isom groupoid carries the canonical dimension function of
`hom ≫ sC`. -/
@[simp] theorem isomGroupoid_baseDim :
    (C.isomGroupoid hC hom sC).baseDim = dimensionFunction (hom ≫ sC) := rfl

/-- **(D.1.5) The Morita map from the Isom groupoid to the chart groupoid.** For an étale
surjective chart `C` and an étale surjective morphism `hom : P ⟶ C.scheme`, the maps `hom` on
atlases and `isomToOverlap` on arrows form a Morita map from `C.isomGroupoid hC hom sC` to
`C.etaleGroupoid hC sC`.  All conditions are proved: (F0) is the surjectivity of `hom`; (F1) uses
the arrows `cechToIsom z` attached to points `z` of `P ×_{C.scheme} P` (residue compatibility by
`residueFieldMap_eq_of_comp_eq`); (F2) is Galois descent in the fibres of `hom`
(`CechGroupoidChow.residue_descent_of_etale`), transported along `cechToIsom`; (F3) is
`exists_isomPoint`. -/
noncomputable def moritaToChart [Surjective hom] :
    MoritaMap (C.isomGroupoid hC hom sC) (C.etaleGroupoid hC sC) where
  onBase := hom
  onArrows := C.isomToOverlap hC hom
  onBase_etale := inferInstance
  onBase_dim u := dimensionFunction_comp_etale sC hom u
  src_comm := (C.isomSrc_comp hC hom).symm
  tgt_comm := (C.isomTgt_comp hC hom).symm
  onBase_surjective := hom.surjective
  exists_arrow_over_identity u' v' h := by
    obtain ⟨z, hz, hz'⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := hom) (g := hom) u' v' h
    have e : C.cechToIsom hC hom ≫ (C.isomSrc hC hom ≫ hom) =
        C.cechToIsom hC hom ≫ (C.isomTgt hC hom ≫ hom) := by
      rw [← Category.assoc, cechToIsom_src, ← Category.assoc, cechToIsom_tgt,
        pullback.condition]
    have hpt : (C.isomSrc hC hom ≫ hom).base ((C.cechToIsom hC hom).base z) =
        (C.isomTgt hC hom ≫ hom).base ((C.cechToIsom hC hom).base z) :=
      congrArg (fun f ↦ f.base z) e
    refine ⟨(C.cechToIsom hC hom).base z, hpt, ?_, ?_,
      residueFieldMap_eq_of_comp_eq _ _ _ e z hpt⟩
    · change (C.isomSrc hC hom).base ((C.cechToIsom hC hom).base z) = u'
      rw [← Scheme.Hom.comp_apply, cechToIsom_src, hz]
    · change (C.isomTgt hC hom).base ((C.cechToIsom hC hom).base z) = v'
      rw [← Scheme.Hom.comp_apply, cechToIsom_tgt, hz']
  residue_descent u' a h := by
    refine residue_descent_of_etale hom u' a fun z hs ht ↦ ?_
    have hs' : (C.isomSrc hC hom).base ((C.cechToIsom hC hom).base z) = u' := by
      rw [← Scheme.Hom.comp_apply, cechToIsom_src, hs]
    have ht' : (C.isomTgt hC hom).base ((C.cechToIsom hC hom).base z) = u' := by
      rw [← Scheme.Hom.comp_apply, cechToIsom_tgt, ht]
    have key := congrArg ((C.cechToIsom hC hom).residueFieldMap z).hom (h _ hs' ht')
    exact (residueFieldMap_comp_apply_congr _ _ _ (C.cechToIsom_src hC hom) z hs' hs a).symm.trans
      (key.trans (residueFieldMap_comp_apply_congr _ _ _ (C.cechToIsom_tgt hC hom) z ht' ht a))
  full r u' v' hu hv := C.exists_isomPoint hC hom r u' v' hu hv

end Groupoid

end IsomGroupoid

end GromovWitten.AlgebraicGeometry.StackChart
