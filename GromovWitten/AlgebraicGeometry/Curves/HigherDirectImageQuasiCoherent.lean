/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineHigherDirectImage
import GromovWitten.AlgebraicGeometry.Curves.HigherOpenBaseChange
import GromovWitten.AlgebraicGeometry.FiniteAffineCover
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechHigherQuasiCoherent

/-!
# Quasicoherence of higher direct images

Finite affine-cover induction gives all-degree quasicoherence over an affine
locally Noetherian base.  Open base change then gives the same conclusion for
quasi-compact separated morphisms between locally Noetherian schemes.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open _root_.AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves

set_option backward.isDefEq.respectTransparency false in
/-- A finite affine cover of a separated locally Noetherian source over an
affine locally Noetherian base gives quasicoherent higher direct images of a
quasicoherent module in every degree. -/
lemma isQuasicoherent_higherDirectImageModule_of_finiteAffineCover
    {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
    (m : ℕ) {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsSeparated]
    (s : X ⟶ S) (U : Fin m → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : iSup U = ⊤) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (higherDirectImageModule s M n).IsQuasicoherent := by
  induction m generalizing X n with
  | zero =>
    have htop : IsAffineOpen (⊤ : X.Opens) := by
      rw [← hcover]
      have hbot : iSup U = ⊥ := le_antisymm (iSup_le fun i => Fin.elim0 i) bot_le
      rw [hbot]
      exact isAffineOpen_bot X
    let _ : IsAffine (⊤ : X.Opens).toScheme := htop
    let _ : IsAffine X := IsAffine.of_isIso X.topIso.inv
    exact isQuasicoherent_higherDirectImageModule_affine s M n
  | succ m ih =>
    let V := finiteCoverTail U
    let W := finiteCoverHeadTail U
    have hsep (A : X.Opens) : A.toScheme.IsSeparated := by
      constructor
      rw [← terminal.comp_from A.ι]
      infer_instance
    let _ : V.toScheme.IsSeparated := hsep V
    let _ : W.toScheme.IsSeparated := hsep W
    let _ : IsAffine (U 0).toScheme := hU 0
    have hUV : U 0 ⊔ V = ⊤ := by
      rw [← hcover]
      apply le_antisymm
      · exact sup_le (le_iSup U 0) (iSup_le fun i => le_iSup U i.succ)
      · refine iSup_le fun i => ?_
        refine Fin.cases le_sup_left (fun j => ?_) i
        exact le_sup_of_le_right (le_iSup (fun k : Fin m => U k.succ) j)
    apply isQuasicoherent_higherDirectImageModule_of_twoOpen s M (U 0) V hUV
    · intro k
      exact isQuasicoherent_higherDirectImageModule_affine ((U 0).ι ≫ s)
        (M.restrict (U 0).ι) k
    · intro k
      exact ih (V.ι ≫ s) (fun i => V.ι ⁻¹ᵁ U i.succ)
        (finiteCover_tail_preimage_affine U hU) (finiteCover_tail_preimage_cover U)
        (M.restrict V.ι) k
    · intro k
      exact ih (W.ι ≫ s) (fun i => W.ι ⁻¹ᵁ U i.succ)
        (finiteCover_headTail_preimage_affine U hU inferInstance)
        (finiteCover_headTail_preimage_cover U) (M.restrict W.ι) k

/-- A compact separated locally Noetherian source over an affine locally
Noetherian base has quasicoherent higher direct images of quasicoherent modules. -/
lemma isQuasicoherent_higherDirectImageModule_of_compact_toAffine
    {X S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
    [CompactSpace X] [IsLocallyNoetherian X] [X.IsSeparated]
    (s : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (higherDirectImageModule s M n).IsQuasicoherent := by
  obtain ⟨m, U, hU, hcover⟩ := exists_fin_affine_cover (X := X)
  exact isQuasicoherent_higherDirectImageModule_of_finiteAffineCover m s U hU hcover M n

set_option backward.isDefEq.respectTransparency false in
/-- If a morphism is quasi-compact and separated between locally Noetherian
schemes, every higher direct image of a quasicoherent module is quasicoherent. -/
lemma isQuasicoherent_higherDirectImageModule_of_quasiCompact_separated
    {X S : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian S]
    (s : X ⟶ S) [QuasiCompact s] [IsSeparated s]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (higherDirectImageModule s M n).IsQuasicoherent := by
  apply SheafCohomology.isQuasicoherent_of_affine_pullback
  intro U
  let _ : IsAffine U.1.toScheme := U.2
  let _ : CompactSpace (s ⁻¹ᵁ U.1).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (s ∣_ U.1)
  let _ : (s ⁻¹ᵁ U.1).toScheme.IsSeparated := by
    constructor
    rw [← terminal.comp_from (s ∣_ U.1)]
    infer_instance
  have hQ := isQuasicoherent_higherDirectImageModule_of_compact_toAffine
    (s ∣_ U.1) ((Scheme.Modules.pullback (s ⁻¹ᵁ U.1).ι).obj M) n
  have := moduleHigherBaseChange_open_isIso s U.1 M n
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    (asIso ((moduleHigherBaseChangeNatTrans s U.1.ι (s ⁻¹ᵁ U.1).ι
      (s ∣_ U.1) (isPullback_morphismRestrict s U.1).flip n).app M)).symm hQ
end GromovWitten.AlgebraicGeometry.Curves
