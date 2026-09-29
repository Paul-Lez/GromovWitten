/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Geometry for finite affine-open induction

For a finite affine-open cover, the tail union and the head--tail overlap inherit finite
affine-open covers after restriction.  The overlap affineness uses separatedness of the
ambient scheme.
-/

open CategoryTheory Limits AlgebraicGeometry
open _root_.AlgebraicGeometry
open TopologicalSpace
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry

variable {X : Scheme.{u}} {n : ℕ}

/-- The union of the opens after the first member of a finite cover. -/
def finiteCoverTail (U : Fin (n + 1) → X.Opens) : X.Opens :=
  ⨆ i : Fin n, U i.succ

/-- The intersection of the first member with the union of the remaining members. -/
def finiteCoverHeadTail (U : Fin (n + 1) → X.Opens) : X.Opens :=
  U 0 ⊓ finiteCoverTail U

/-- The tail affine opens cover the tail union after restriction to that union. -/
lemma finiteCover_tail_preimage_cover (U : Fin (n + 1) → X.Opens) :
    ⨆ i : Fin n, (finiteCoverTail U).ι ⁻¹ᵁ U i.succ = ⊤ := by
  calc
    ⨆ i : Fin n, (finiteCoverTail U).ι ⁻¹ᵁ U i.succ =
        (finiteCoverTail U).ι ⁻¹ᵁ (⨆ i : Fin n, U i.succ) :=
      ((finiteCoverTail U).ι.preimage_iSup _).symm
    _ = (finiteCoverTail U).ι ⁻¹ᵁ finiteCoverTail U := by rfl
    _ = ⊤ := (finiteCoverTail U).ι_preimage_self

/-- Each tail open remains affine after restriction to the tail union. -/
lemma finiteCover_tail_preimage_affine
    (U : Fin (n + 1) → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (i : Fin n) :
    IsAffineOpen ((finiteCoverTail U).ι ⁻¹ᵁ U i.succ) :=
  (hU i.succ).preimage_of_isOpenImmersion (finiteCoverTail U).ι
    (by simpa [finiteCoverTail] using le_iSup (fun j : Fin n => U j.succ) i)

/-- The tail opens cover the head--tail overlap after restricting to that overlap. -/
lemma finiteCover_headTail_preimage_cover (U : Fin (n + 1) → X.Opens) :
    ⨆ i : Fin n, (finiteCoverHeadTail U).ι ⁻¹ᵁ U i.succ = ⊤ := by
  calc
    ⨆ i : Fin n, (finiteCoverHeadTail U).ι ⁻¹ᵁ U i.succ =
        (finiteCoverHeadTail U).ι ⁻¹ᵁ (⨆ i : Fin n, U i.succ) :=
      ((finiteCoverHeadTail U).ι.preimage_iSup _).symm
    _ = (finiteCoverHeadTail U).ι ⁻¹ᵁ finiteCoverTail U := by rfl
    _ = ⊤ := by
      apply le_antisymm le_top
      rw [← (finiteCoverHeadTail U).ι_preimage_self]
      exact (finiteCoverHeadTail U).ι.preimage_mono inf_le_right

/-- Each tail open remains affine after restriction to the head--tail overlap. -/
lemma finiteCover_headTail_preimage_affine
    (U : Fin (n + 1) → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hX : X.IsSeparated) (i : Fin n) :
    IsAffineOpen ((finiteCoverHeadTail U).ι ⁻¹ᵁ U i.succ) := by
  let _ : X.IsSeparated := hX
  have hInf : IsAffineOpen (U 0 ⊓ U i.succ) := (hU 0).inf (hU i.succ)
  have hImage : IsAffineOpen
      ((finiteCoverHeadTail U).ι ''ᵁ
        ((finiteCoverHeadTail U).ι ⁻¹ᵁ U i.succ)) := by
    rw [(finiteCoverHeadTail U).ι.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    have hle : U i.succ ≤ finiteCoverTail U :=
      le_iSup (fun j : Fin n => U j.succ) i
    simpa only [finiteCoverHeadTail, inf_assoc, inf_eq_right.mpr hle] using hInf
  exact (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (finiteCoverHeadTail U).ι).mp hImage

/-- A compact scheme has a finite affine-open cover indexed by a finite type. -/
lemma exists_fin_affine_cover [CompactSpace X] :
    ∃ m : ℕ, ∃ U : Fin m → X.Opens,
      (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ := by
  let 𝒰 := X.affineCover.finiteSubcover
  let e : 𝒰.I₀ ≃ Fin (Fintype.card 𝒰.I₀) := Fintype.equivFin _
  let U : Fin (Fintype.card 𝒰.I₀) → X.Opens :=
    fun i => (𝒰.f (e.symm i)).opensRange
  refine ⟨Fintype.card 𝒰.I₀, U, ?_, ?_⟩
  · intro i
    exact isAffineOpen_opensRange _
  · change ⨆ i : Fin (Fintype.card 𝒰.I₀),
      (𝒰.f (e.symm i)).opensRange = ⊤
    rw [← e.iSup_comp]
    exact (iSup_congr (fun x => congrArg (fun j => (𝒰.f j).opensRange)
      (e.symm_apply_apply x))).trans 𝒰.iSup_opensRange

end GromovWitten.AlgebraicGeometry
