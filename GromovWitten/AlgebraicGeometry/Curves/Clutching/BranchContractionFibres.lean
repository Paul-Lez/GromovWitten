/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.Curves.Clutching.BranchContraction

/-!
# Fibres of the affine branch contraction

This file computes the fibres of `contractBranchB` (`Curves/Clutching/BranchContraction.lean`)
point by point, and records connectedness, completing the affine-local model of
`Curves.StableMaps.Contraction`'s `connectedFibers` field (`Curves/StableMaps/Geometry.lean:802`).

* `contractBranchB_surjective` : `contractBranchB` is surjective on points (`specFst` is a
  section).
* `contractBranchB_fiber_subsingleton_of_notMem` : off the augmentation locus, the fibre of
  `contractBranchB` over a point is a subsingleton (it lies entirely in the open complement of
  the `B`-branch, where `contractBranchB` is injective by `contractBranchB_bijOn`).
* `contractBranchB_fiber_eq_of_mem` : *assuming `Subsingleton (Spec R)`* (i.e. the
  augmentation locus is at most a single point, the standard situation for a nodal contraction),
  the fibre of `contractBranchB` over a point of the augmentation locus is exactly the whole
  `B`-branch `Set.range (specSnd εA εB).base`. Without this hypothesis the fibre over a single
  point of the augmentation locus is in general only a fibre of the *structure map*
  `Spec B → Spec R`, not all of `Spec B`, since `specSnd ≫ contractBranchB` factors through
  `Spec B → Spec R → Spec A` (`contractBranchB_specSnd`); the hypothesis collapses `Spec R` to
  (at most) one point so this factoring is vacuous.
* `contractBranchB_fibers_connected` : *assuming* `Subsingleton (Spec R)` *and*
  `ConnectedSpace (Spec B)`, every fibre of `contractBranchB` is connected: over the augmentation
  locus it is the whole `B`-branch, connected because `Spec B` is (via the closed immersion
  `specSnd`, using `isConnected_range`); elsewhere it is a nonempty singleton
  (`isConnected_singleton`), nonempty by `contractBranchB_surjective`.
* `contractBranchB_isContractionModel` : packages the three main results above (the scheme
  isomorphism away from the exceptional locus, the exact fibre over the augmentation locus, and
  connectedness of every fibre) as a single conjunction, under the hypotheses used, as the
  affine-local model of the geometric fields of `Curves.StableMaps.Contraction` other than
  properness.
-/

open _root_.AlgebraicGeometry
open CategoryTheory

namespace GromovWitten
namespace AlgebraicGeometry
namespace Curves
namespace Clutching
namespace fiberProduct

universe u

noncomputable section

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (εA : A →ₐ[R] R) (εB : B →ₐ[R] R)

/-- `contractBranchB` is surjective on points: `specFst` is a section of it
(`contractBranchB_specFst`), giving a right inverse. -/
theorem contractBranchB_surjective :
    Function.Surjective (contractBranchB εA εB).base := by
  intro a
  refine ⟨(specFst εA εB).base a, ?_⟩
  rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, contractBranchB_specFst]
  rfl

/-- Off the augmentation locus, the fibre of `contractBranchB` over a point is a subsingleton:
any point of the fibre must lie in the open complement of the `B`-branch (else
`contractBranchB_contracts` would put its image in the augmentation locus), where
`contractBranchB` is injective by `contractBranchB_bijOn`. -/
theorem contractBranchB_fiber_subsingleton_of_notMem {a : PrimeSpectrum A}
    (ha : a ∉ Set.range (sectionA εA).base) :
    Set.Subsingleton ((contractBranchB εA εB).base ⁻¹' {a}) := by
  intro p hp q hq
  simp only [Set.mem_preimage] at hp hq
  have hpB : p ∈ (branchOpen εA εB).1 := fun hmem =>
    ha (hp ▸ contractBranchB_contracts εA εB hmem)
  have hqB : q ∈ (branchOpen εA εB).1 := fun hmem =>
    ha (hq ▸ contractBranchB_contracts εA εB hmem)
  exact (contractBranchB_bijOn εA εB).2.1 hpB hqB (hp.trans hq.symm)

/-- Assuming the augmentation locus is at most a single point (`Subsingleton
(PrimeSpectrum R)`, the standard situation for a nodal contraction where `Spec R` is a single
point), the fibre of `contractBranchB` over a point `a` of the augmentation locus is exactly the
whole `B`-branch: since the locus is a subsingleton and `a` lies in it, the locus is exactly
`{a}`, so the preimage of `{a}` equals the preimage of the whole locus, computed exactly by
`contractBranchB_fiber_augmentation`. -/
theorem contractBranchB_fiber_eq_of_mem [Subsingleton (Spec (.of R))]
    {a : PrimeSpectrum A} (ha : a ∈ Set.range (sectionA εA).base) :
    (contractBranchB εA εB).base ⁻¹' {a} = Set.range (specSnd εA εB).base := by
  have hrange : Set.range (sectionA εA).base = {a} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨ha, by
      rintro b ⟨r, rfl⟩
      obtain ⟨r', rfl⟩ := ha
      exact congrArg (sectionA εA).base (Subsingleton.elim r r')⟩
  rw [← hrange]
  exact contractBranchB_fiber_augmentation εA εB

/-- Every fibre of `contractBranchB` is connected: over the augmentation locus (assuming
`Subsingleton (Spec R)`) it is the whole `B`-branch, connected because `Spec B` is
(assuming `ConnectedSpace (Spec B)`), via the closed immersion `specSnd`
(`contractBranchB_fiber_eq_of_mem` + `isConnected_range`); elsewhere it is a nonempty singleton
(`contractBranchB_fiber_subsingleton_of_notMem` + `contractBranchB_surjective`, closed by
`isConnected_singleton`). -/
theorem contractBranchB_fibers_connected [Subsingleton (Spec (.of R))]
    [ConnectedSpace (Spec (.of B))] (a : PrimeSpectrum A) :
    _root_.IsConnected ((contractBranchB εA εB).base ⁻¹' {a}) := by
  by_cases ha : a ∈ Set.range (sectionA εA).base
  · rw [contractBranchB_fiber_eq_of_mem εA εB ha]
    exact isConnected_range (specSnd εA εB).continuous
  · obtain ⟨p, hp⟩ := contractBranchB_surjective εA εB a
    have hmem : p ∈ (contractBranchB εA εB).base ⁻¹' {a} := hp
    rw [(contractBranchB_fiber_subsingleton_of_notMem εA εB ha).eq_singleton_of_mem hmem]
    exact isConnected_singleton

/-- The affine-local model of the geometric fields of `Curves.StableMaps.Contraction`
(`Curves/StableMaps/Geometry.lean:802`), other than properness: `contractBranchB` restricted to
the open complement of the `B`-branch is a genuine scheme isomorphism onto `augmentationOpen`
(`isIso_morphismRestrict_contractBranchB`, modelling `complementIso`), its fibre over the
augmentation locus is exactly the `B`-branch (`contractBranchB_fiber_augmentation`, modelling
`contracts` exactly rather than only as a `MapsTo`), and every fibre is connected
(`contractBranchB_fibers_connected`, modelling `connectedFibers`), under the hypotheses
`Subsingleton (Spec R)` and `ConnectedSpace (Spec B)` used by the last statement.
Properness of `contractBranchB` is not addressed here. -/
theorem contractBranchB_isContractionModel [Subsingleton (Spec (.of R))]
    [ConnectedSpace (Spec (.of B))] :
    IsIso (contractBranchB εA εB ∣_ augmentationOpen εA) ∧
      (contractBranchB εA εB).base ⁻¹' Set.range (sectionA εA).base
        = Set.range (specSnd εA εB).base ∧
      ∀ a : PrimeSpectrum A, _root_.IsConnected ((contractBranchB εA εB).base ⁻¹' {a}) :=
  ⟨isIso_morphismRestrict_contractBranchB εA εB, contractBranchB_fiber_augmentation εA εB,
    contractBranchB_fibers_connected εA εB⟩

end

end fiberProduct
end Clutching
end Curves
end AlgebraicGeometry
end GromovWitten
