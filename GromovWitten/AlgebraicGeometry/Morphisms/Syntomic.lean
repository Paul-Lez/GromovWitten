/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.CompleteIntersection
import GromovWitten.AlgebraicGeometry.Morphisms.Unramified
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Syntomic morphisms

This file supplies the scheme-level locally-complete-intersection and syntomic vocabulary
needed for nodal curves.  A locally complete-intersection morphism has, around every point of
its source, an affine chart whose ring map is isomorphic to a finite polynomial presentation
by a regular sequence.  A syntomic morphism is flat, locally of finite presentation, and
locally complete intersection.
-/

open CategoryTheory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

/-- A morphism has complete-intersection charts when every source point has an affine chart whose
induced ring map is a global complete intersection. -/
def HasCompleteIntersectionCharts {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ x : X,
    ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1)
      (e : V.1 ≤ f ⁻¹ᵁ U.1),
      RingHom.IsCompleteIntersection (f.appLE U V e).hom

/-- A morphism is locally complete intersection when it is isomorphic as a scheme arrow to a
morphism having complete-intersection affine charts.

Taking the isomorphism closure makes the definition independent of all chosen scheme and section
ring identifications. -/
class LocallyCompleteIntersection {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  exists_chart_model : ∃ (X' Y' : Scheme.{u}) (g : X' ⟶ Y'),
    HasCompleteIntersectionCharts g ∧ Nonempty (Arrow.mk f ≅ Arrow.mk g)

namespace LocallyCompleteIntersection

/-- A morphism with complete-intersection charts is locally complete intersection. -/
theorem of_completeIntersectionCharts {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : HasCompleteIntersectionCharts f) : LocallyCompleteIntersection f :=
  ⟨⟨X, Y, f, h, ⟨Iso.refl _⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The identity of a scheme is locally complete intersection.  Around a point, choose an
affine neighbourhood; its section ring is nontrivial because the neighbourhood contains that
point, and the identity map has the empty complete-intersection presentation. -/
theorem id (X : Scheme.{u}) : LocallyCompleteIntersection (𝟙 X) := by
  apply of_completeIntersectionCharts
  intro x
  obtain ⟨_, ⟨U, hUaffine : IsAffine _, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  let V : X.Opens := (𝟙 X : X ⟶ X) ⁻¹ᵁ U
  have hVU : V = U := by ext; simp [V]
  have hVaffine : IsAffineOpen V := by
    rw [hVU]
    exact hUaffine
  have hxV : x ∈ V := by rwa [hVU]
  let _ : Nonempty U := ⟨⟨x, hxU⟩⟩
  let _ : Nonempty V := ⟨⟨x, hxV⟩⟩
  refine ⟨⟨U, hUaffine⟩, ⟨V, hVaffine⟩, hxV, le_rfl, ?_⟩
  let q : Γ(X, U) ⟶ Γ(X, V) := (𝟙 X : X ⟶ X).appLE U V le_rfl
  have hq : q = (𝟙 X : X ⟶ X).app U :=
    Scheme.Hom.appLE_eq_app (𝟙 X : X ⟶ X)
  let _ : IsIso q := by
    rw [hq, Scheme.Hom.id_app]
    infer_instance
  have hid : RingHom.IsCompleteIntersection (RingHom.id Γ(X, U)) := by
    simpa [Algebra.algebraMap_self] using
      (RingHom.IsCompleteIntersection.of_algebraMap
        (R := Γ(X, U)) (S := Γ(X, U)))
  have hcomp := (RingHom.IsCompleteIntersection.respectsIso.cancel_right_isIso
    (𝟙 Γ(X, U)) q).mpr hid
  simpa [q, CommRingCat.hom_comp] using hcomp

/-- An affine morphism whose map on global sections is a complete intersection is locally
complete intersection. -/
theorem of_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    (h : RingHom.IsCompleteIntersection f.appTop.hom) :
    LocallyCompleteIntersection f := by
  apply of_completeIntersectionCharts
  intro x
  refine ⟨⟨⊤, isAffineOpen_top Y⟩,
    ⟨f ⁻¹ᵁ (⊤ : Y.Opens), ?_⟩,
    by simp, le_rfl, ?_⟩
  · change IsAffineOpen (f ⁻¹ᵁ (⊤ : Y.Opens))
    rw [f.preimage_top]
    exact isAffineOpen_top X
  rw [f.appLE_eq_app]
  exact h

/-- Locally complete-intersection morphisms are invariant under isomorphisms of their sources. -/
theorem precomp_iso {X Y Z : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Z)
    (h : LocallyCompleteIntersection f) :
    LocallyCompleteIntersection (e.hom ≫ f) := by
  obtain ⟨X', Y', g, hg, hi⟩ := h.exists_chart_model
  refine ⟨⟨X', Y', g, hg, ?_⟩⟩
  exact hi.map fun i ↦
    (Arrow.isoMk' (e.hom ≫ f) f e (Iso.refl _) (by simp)).trans i

/-- Locally complete-intersection morphisms are invariant under isomorphisms of their targets. -/
theorem postcomp_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z)
    (h : LocallyCompleteIntersection f) :
    LocallyCompleteIntersection (f ≫ e.hom) := by
  obtain ⟨X', Y', g, hg, hi⟩ := h.exists_chart_model
  refine ⟨⟨X', Y', g, hg, ?_⟩⟩
  exact hi.map fun i ↦
    (Arrow.isoMk' (f ≫ e.hom) f (Iso.refl _) e.symm (by simp)).trans i

instance : MorphismProperty.RespectsIso (@LocallyCompleteIntersection) :=
  MorphismProperty.RespectsIso.mk _ precomp_iso (fun e f h ↦ postcomp_iso f e h)

/-- The locally complete-intersection predicate is invariant under an isomorphism in the arrow
category. -/
theorem iff_of_arrow_iso {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) :
    LocallyCompleteIntersection f ↔ LocallyCompleteIntersection g :=
  MorphismProperty.arrow_mk_iso_iff (P := @LocallyCompleteIntersection) e

/-- A map of affine spectra is locally complete intersection when its defining ring map is a
global complete intersection. -/
theorem specMap {R S : CommRingCat.{u}} (f : R ⟶ S)
    (h : RingHom.IsCompleteIntersection f.hom) :
    LocallyCompleteIntersection (Spec.map f) := by
  apply of_appTop
  have hP := RingHom.IsCompleteIntersection.respectsIso
  rw [← hP.cancel_right_isIso _ (Scheme.ΓSpecIso _).hom,
    ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp,
    hP.cancel_left_isIso]
  exact h

/-- The spectrum map of a displayed complete-intersection algebra is locally complete
intersection. -/
theorem specMap_algebraMap {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsCompleteIntersection R S] :
    LocallyCompleteIntersection
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  specMap _ RingHom.IsCompleteIntersection.of_algebraMap

end LocallyCompleteIntersection

/-- A scheme morphism is syntomic when it is flat, locally of finite presentation, and locally
complete intersection. -/
@[mk_iff]
class Syntomic {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  flat : _root_.AlgebraicGeometry.Flat f := by infer_instance
  locallyOfFinitePresentation : _root_.AlgebraicGeometry.LocallyOfFinitePresentation f := by
    infer_instance
  locallyCompleteIntersection : LocallyCompleteIntersection f := by infer_instance

namespace Syntomic

attribute [instance] flat locallyOfFinitePresentation locallyCompleteIntersection

/-- Syntomic morphisms are invariant under isomorphisms of their sources. -/
theorem precomp_iso {X Y Z : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Z)
    (h : Syntomic f) : Syntomic (e.hom ≫ f) := by
  let _ : _root_.AlgebraicGeometry.Flat f := h.flat
  let _ : _root_.AlgebraicGeometry.LocallyOfFinitePresentation f :=
    h.locallyOfFinitePresentation
  exact
    { flat := by infer_instance
      locallyOfFinitePresentation := by infer_instance
      locallyCompleteIntersection :=
        LocallyCompleteIntersection.precomp_iso e f h.locallyCompleteIntersection }

/-- Syntomic morphisms are invariant under isomorphisms of their targets. -/
theorem postcomp_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z)
    (h : Syntomic f) : Syntomic (f ≫ e.hom) := by
  let _ : _root_.AlgebraicGeometry.Flat f := h.flat
  let _ : _root_.AlgebraicGeometry.LocallyOfFinitePresentation f :=
    h.locallyOfFinitePresentation
  exact
    { flat := by infer_instance
      locallyOfFinitePresentation := by infer_instance
      locallyCompleteIntersection :=
        LocallyCompleteIntersection.postcomp_iso f e h.locallyCompleteIntersection }

instance : MorphismProperty.RespectsIso (@Syntomic) :=
  MorphismProperty.RespectsIso.mk _ precomp_iso (fun e f h ↦ postcomp_iso f e h)

/-- The syntomic predicate is invariant under an isomorphism in the arrow category. -/
theorem iff_of_arrow_iso {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) : Syntomic f ↔ Syntomic g :=
  MorphismProperty.arrow_mk_iso_iff (P := @Syntomic) e

/-- A flat affine complete-intersection algebra defines a syntomic map of spectra. -/
theorem specMap_algebraMap {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.IsCompleteIntersection R S] :
    Syntomic (Spec.map (CommRingCat.ofHom (algebraMap R S))) where
  flat := by
    rw [_root_.AlgebraicGeometry.Flat.SpecMap_iff]
    change (algebraMap R S).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  locallyOfFinitePresentation := by
    rw [_root_.AlgebraicGeometry.LocallyOfFinitePresentation.SpecMap_iff]
    change (algebraMap R S).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr
      Algebra.IsCompleteIntersection.finitePresentation
  locallyCompleteIntersection := LocallyCompleteIntersection.specMap_algebraMap

/-- A syntomic and unramified morphism is étale. Syntomicity supplies flatness and finite
presentation; unramifiedness supplies formal unramifiedness. -/
theorem etale_of_unramified {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hs : Syntomic f) (hu : Unramified f) : Etale f := by
  let _ : Flat f := hs.flat
  let _ : LocallyOfFinitePresentation f := hs.locallyOfFinitePresentation
  let _ : FormallyUnramified f := hu.formallyUnramified
  exact Etale.of_formallyUnramified_of_flat f

/-- On a syntomic morphism, unramifiedness is equivalent to étaleness. -/
theorem unramified_iff_etale {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hs : Syntomic f) : Unramified f ↔ Etale f := by
  constructor
  · exact etale_of_unramified hs
  · intro he
    let _ : Etale f := he
    exact
      { formallyUnramified := by infer_instance
        locallyOfFiniteType := by infer_instance }

/-- For a syntomic morphism, the finite-type clause in unramifiedness is automatic, so only
formal unramifiedness remains to be checked. -/
theorem unramified_iff_formallyUnramified {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hs : Syntomic f) : Unramified f ↔ FormallyUnramified f := by
  constructor
  · exact fun h ↦ h.formallyUnramified
  · intro h
    let _ : LocallyOfFinitePresentation f := hs.locallyOfFinitePresentation
    exact
      { formallyUnramified := h
        locallyOfFiniteType := by infer_instance }

/-- A syntomic unramified morphism is smooth (in fact, étale). -/
theorem smooth_of_unramified {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hs : Syntomic f) (hu : Unramified f) : Smooth f := by
  let _ : Etale f := etale_of_unramified hs hu
  infer_instance

end Syntomic

end GromovWitten.AlgebraicGeometry
