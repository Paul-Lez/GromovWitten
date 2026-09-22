/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Morphisms.ClosedImmersionDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.MorphismProperty.Descent
import Mathlib.Topology.LocallyClosed

/-!
# Fppf descent for immersions of schemes

An immersion is locally closed on the underlying topological space.  For a surjective flat
locally finitely presented cover, local closedness of the range descends because the cover is an
open quotient map.  We factor through the resulting coborder open and descend the closed factor
using the closed-immersion descent theorem.
-/

public section

open CategoryTheory CategoryTheory.Limits MorphismProperty
open scoped Set.Notation

universe u

namespace AlgebraicGeometry

/-! ## Topological descent of local closedness -/

lemma isLocallyClosed_of_isPullback_fppf
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    [IsImmersion (pullback.fst f g)] :
    IsLocallyClosed (Set.range g) := by
  have hopen : IsOpen (coborder (Set.range (pullback.fst f g))) :=
    IsImmersion.isLocallyClosed_range.isOpen_coborder
  have hpre : coborder (Set.range (pullback.fst f g)) =
      f ⁻¹' coborder (Set.range g) := by
    rw [Scheme.Pullback.range_fst]
    exact coborder_preimage f.isOpenMap f.continuous _
  have hpreopen : IsOpen (f ⁻¹' coborder (Set.range g)) := hpre.symm ▸ hopen
  have hfq : IsOpenQuotientMap f.base :=
    ⟨f.surjective, f.continuous, f.isOpenMap⟩
  exact isLocallyClosed_iff_isOpen_coborder.mpr
    (hfq.isQuotientMap.isOpen_preimage.mp hpreopen)

/-! ## Descent instances -/

set_option backward.isDefEq.respectTransparency false in
instance immersion_descendsAlong_fppf :
    DescendsAlong (@IsImmersion : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  apply DescendsAlong.mk'
  introv hf hfst
  let _ : Surjective f := hf.1.1
  let _ : Flat f := hf.1.2
  let _ : LocallyOfFinitePresentation f := hf.2
  let _ : IsImmersion (pullback.fst f g) := hfst
  have hloc : IsLocallyClosed (Set.range g) :=
    isLocallyClosed_of_isPullback_fppf f g
  let U : Z.Opens := ⟨coborder (Set.range g), hloc.isOpen_coborder⟩
  let h : Y ⟶ U.toScheme := IsOpenImmersion.lift U.ι g (by
    simpa [U] using (subset_coborder : Set.range g ⊆ coborder (Set.range g)))
  have hι : h ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  let fU : pullback f U.ι ⟶ U.toScheme := pullback.snd f U.ι
  let q : pullback f g ⟶ pullback f U.ι :=
    pullback.lift (pullback.fst f g) (pullback.snd f g ≫ h) (by
      rw [Category.assoc, hι, pullback.condition])
  have hq : q ≫ pullback.fst f U.ι = pullback.fst f g := by
    exact pullback.lift_fst _ _ _
  have hq' : q ≫ fU = pullback.snd f g ≫ h := by
    exact pullback.lift_snd _ _ _
  have hsq : IsPullback q (pullback.snd f g) fU h := by
    have hs : IsPullback (pullback.fst f g) (pullback.snd f g) f (h ≫ U.ι) := by
      simpa [hι] using (IsPullback.of_hasPullback f g)
    let t := IsPullback.of_hasPullback f U.ι
    have hqt : q = t.lift (pullback.fst f g) (pullback.snd f g ≫ h) (by
        simpa only [Category.assoc] using hs.w) := by
      apply pullback.hom_ext
      · simp [q]
      · simp [q]
    rw [hqt]
    exact IsPullback.of_right' hs t
  have hpq : IsPreimmersion q := by
    have : IsPreimmersion (q ≫ pullback.fst f U.ι) := by
      rw [hq]
      infer_instance
    exact IsPreimmersion.of_comp q (pullback.fst f U.ι)
  have hrange : Set.range h = (U : Set Z) ↓∩ Set.range g := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, by
        change g.base x = U.ι.base (h.base x)
        simpa only [Scheme.Hom.comp_apply] using congrArg (fun k => k.base x) hι.symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply U.ι.injective
      calc
        U.ι.base (h.base x) = g.base x := by
          simpa only [Scheme.Hom.comp_apply] using congrArg (fun k => k.base x) hι
        _ = U.ι.base y := hx
  have hclosed : IsClosed (Set.range h) := by
    rw [hrange]
    simpa [U] using (isClosed_preimage_val_coborder (s := Set.range g))
  have hrangeq : Set.range q = fU ⁻¹' Set.range h := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨pullback.snd f g a, ?_⟩
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun k => k.base a) hq'.symm
    · intro hx
      change ∃ y, h.base y = fU.base x at hx
      obtain ⟨y, hy⟩ := hx
      have hy' : fU.base x = h.base y := hy.symm
      obtain ⟨a, haq, has⟩ := Scheme.exists_preimage_of_isPullback hsq x y hy'
      exact ⟨a, haq⟩
  have hqclosed : IsClosed (Set.range q) := by
    rw [hrangeq]
    exact hclosed.preimage fU.continuous
  let _ : IsClosedImmersion q := IsClosedImmersion.of_isPreimmersion q hqclosed
  have hcover : ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :
      MorphismProperty Scheme.{u}) fU := MorphismProperty.pullback_snd _ _ hf
  have hqcanon : IsClosedImmersion (pullback.fst fU h) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := @IsClosedImmersion) hsq.isoPullback.hom,
      hsq.isoPullback_hom_fst]
    infer_instance
  have : IsClosedImmersion h :=
    MorphismProperty.of_pullback_fst_of_descendsAlong hcover hqcanon
  let _ : IsClosedImmersion h := this
  rw [← hι]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance immersion_descendsAlong_smooth :
    DescendsAlong (@IsImmersion : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Smooth) := by
  apply DescendsAlong.of_le
    (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation))
  rintro X Y f ⟨hs, hsm⟩
  exact ⟨⟨hs, inferInstance⟩, inferInstance⟩

end AlgebraicGeometry
