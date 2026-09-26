/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Limits

/-!
# Gluing etale slices of a smooth groupoid

Let `t s : R ⟶ U` be two morphisms of schemes (in the application `R = U ×_X U` is the
self-overlap of a smooth atlas `U → X` of an algebraic stack, `s` and `t` its two projections).
A *slice* is a morphism of schemes `g : W ⟶ U`; the associated morphism is

`pullback.snd g s ≫ t : s⁻¹(W) ⟶ U`.

The converse Deligne--Mumford criterion produces slices for which this morphism is etale only
locally on `U`, so the slices have to be glued.  This file performs the gluing: for a family
`g i : W i ⟶ U` with all `pullback.snd (g i) s ≫ t` etale and with jointly surjective `g i`, the
single slice `Sigma.desc g : ∐ W ⟶ U` is surjective and its associated morphism is again etale
(`AlgebraicGeometry.exists_surjective_etale_slice_of_family`).

The proof is Zariski-locality of `Etale` on the source: the family of open subschemes
`s⁻¹(W i) ⊆ s⁻¹(∐ W)` obtained by pulling back the coproduct cover of `∐ W` is an open cover,
and each member is identified with `s⁻¹(W i)` by pasting the two pullback squares.

## Main results

* `AlgebraicGeometry.surjective_sigmaDesc`: `Sigma.desc g` is surjective as soon as the `g i` are
  jointly surjective on points.
* `AlgebraicGeometry.etale_slice_sigmaDesc`: the slice attached to `Sigma.desc g` is etale as soon
  as each slice attached to `g i` is.
* `AlgebraicGeometry.exists_surjective_etale_slice_of_family`: the two combined, in the exact
  shape consumed by `AlgebraicStack.exists_etaleChart_of_exists_slice`.

Nothing here produces the local slices themselves; that step (cutting an affine chart of `U` by
functions whose differentials generate the relative cotangent module, see
`GromovWitten/AlgebraicGeometry/Stacks/EtaleSlice.lean`) is still missing.
-/

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {R U : Scheme.{u}} (t s : R ⟶ U) {σ : Type u} (W : σ → Scheme.{u})
  (g : ∀ i, W i ⟶ U)

/-- A jointly surjective family of morphisms into `U` induces a surjective morphism from the
coproduct. -/
theorem surjective_sigmaDesc (h : ∀ u : U, ∃ (i : σ) (w : W i), (g i) w = u) :
    Surjective (Sigma.desc g) := by
  refine ⟨fun u ↦ ?_⟩
  obtain ⟨i, w, hw⟩ := h u
  refine ⟨Sigma.ι W i w, ?_⟩
  rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  exact hw

/-- **The slice of `s` over `W i` is the `i`-th member of the coproduct cover of the slice of `s`
over `∐ W`.**  Pasting the pullback square of `pullback.fst (Sigma.desc g) s` against
`Sigma.ι W i` with the defining pullback square of the slice. -/
theorem isPullback_slice_sigmaι (i : σ) :
    IsPullback (pullback.snd (pullback.fst (Sigma.desc g) s) (Sigma.ι W i))
      (pullback.fst (pullback.fst (Sigma.desc g) s) (Sigma.ι W i) ≫
        pullback.snd (Sigma.desc g) s) (g i) s := by
  have h := (IsPullback.of_hasPullback (pullback.fst (Sigma.desc g) s)
    (Sigma.ι W i)).flip.paste_vert (IsPullback.of_hasPullback (Sigma.desc g) s)
  rwa [Sigma.ι_desc] at h

/-- **Etaleness of a slice is stable under taking coproducts of slices.**  If every
`s⁻¹(W i) ⟶ U` is etale through `t`, then so is `s⁻¹(∐ W) ⟶ U`. -/
theorem etale_slice_sigmaDesc (hEt : ∀ i, Etale (pullback.snd (g i) s ≫ t)) :
    Etale (pullback.snd (Sigma.desc g) s ≫ t) := by
  let _ := HasRingHomProperty.instIsZariskiLocalAtSource
    (P := (@Etale : MorphismProperty Scheme.{u})) (Q := @RingHom.Etale)
  have _inst : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := (@Etale : MorphismProperty Scheme.{u}))
    ((sigmaOpenCover W).pullback₁ (pullback.fst (Sigma.desc g) s))]
  intro i
  change Etale (pullback.fst (pullback.fst (Sigma.desc g) s) (Sigma.ι W i) ≫
    pullback.snd (Sigma.desc g) s ≫ t)
  have key := (isPullback_slice_sigmaι s W g i).isoPullback_hom_snd
  rw [← Category.assoc, ← key, Category.assoc]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@Etale : MorphismProperty Scheme.{u}) _ _).2 (hEt i)

/-- **A jointly surjective family of etale slices glues to a single surjective etale slice.**
This is the exact shape of the hypothesis of
`GromovWitten.AlgebraicGeometry.AlgebraicStack.exists_etaleChart_of_exists_slice`. -/
theorem exists_surjective_etale_slice_of_family
    (hEt : ∀ i, Etale (pullback.snd (g i) s ≫ t))
    (hcov : ∀ u : U, ∃ (i : σ) (w : W i), (g i) w = u) :
    ∃ (W' : Scheme.{u}) (g' : W' ⟶ U), Surjective g' ∧ Etale (pullback.snd g' s ≫ t) :=
  ⟨∐ W, Sigma.desc g, surjective_sigmaDesc W g hcov, etale_slice_sigmaDesc t s W g hEt⟩

end AlgebraicGeometry
