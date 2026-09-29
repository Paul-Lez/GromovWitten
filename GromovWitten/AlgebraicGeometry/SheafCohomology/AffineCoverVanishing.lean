/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineQuasiCoherent
import GromovWitten.AlgebraicGeometry.SheafCohomology.SectionsMayerVietoris

/-!
# Vanishing from affine covers

This file derives higher cohomology vanishing from actual affine acyclicity and the
Mayer--Vietoris sequence for right-derived sections.  The hypotheses record geometric
affineness and separatedness; no cohomological vanishing is supplied as data.
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

/-! The affine-open case of the arbitrary-affine theorem, transported back to `X`. -/
theorem isZero_rightDerived_sections_affineOpen_succ {X : Scheme.{u}}
    [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((sections U).rightDerived (n + 1)).obj ((moduleToSheafAb X).obj M)) := by
  have hUI : IsAffine U.toScheme := hU
  have hUring : IsNoetherianRing (affineGlobalRing U.toScheme) :=
    @IsLocallyNoetherian.component_noetherian U.toScheme inferInstance
      ⟨⊤, @isAffineOpen_top U.toScheme hUI⟩
  let N := (Scheme.Modules.restrictFunctor U.ι).obj M
  let hN : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor U.ι M
  have htop : IsZero (((sections (⊤ : Opens U.toScheme)).rightDerived (n + 1)).obj
      ((moduleToSheafAb U.toScheme).obj N)) := by
    exact @isZero_affine_sections_rightDerived_succ U.toScheme hUI hUring N hN n
  have hopen := derivedSectionsOpenIso U.ι.isOpenEmbedding
    ((moduleToSheafAb X).obj M) (n + 1)
  have himage : U.ι.isOpenEmbedding.functor.obj (⊤ : Opens U.toScheme) = U := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by trivial⟩
  rw [himage] at hopen
  have hmodule :
      ((moduleToSheafAb U.toScheme).obj N) ≅
        ((U.ι.isOpenEmbedding.sheafPullback Ab).obj ((moduleToSheafAb X).obj M)) := by
    rfl
  have hopen' :
      (((sections U).rightDerived (n + 1)).obj ((moduleToSheafAb X).obj M)) ≅
        (((sections (⊤ : Opens U.toScheme)).rightDerived (n + 1)).obj
          ((moduleToSheafAb U.toScheme).obj N)) := by
    exact hopen ≪≫
      (((sections (⊤ : Opens U.toScheme)).rightDerived (n + 1)).mapIso hmodule.symm)
  exact IsZero.of_iso htop hopen'

/-! A two-affine-open cover gives vanishing from degree two onwards. -/
theorem isZero_rightDerived_sections_twoAffine {X : Scheme.{u}}
    [IsLocallyNoetherian X] [X.IsSeparated] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((sections (U ⊔ V)).rightDerived (n + 2)).obj ((moduleToSheafAb X).obj M)) := by
  apply isZero_rightDerived_sections_sup ((moduleToSheafAb X).obj M) U V (n + 1)
  · exact isZero_rightDerived_sections_affineOpen_succ U hU M (n + 1)
  · exact isZero_rightDerived_sections_affineOpen_succ V hV M (n + 1)
  · exact isZero_rightDerived_sections_affineOpen_succ (U ⊓ V) (hU.inf hV) M n

/-! The union of a nonempty finite list of affine opens has the expected dimension bound. -/
def affineUnion {X : Scheme.{u}} : List X.Opens → X.Opens
  | [] => ⊥
  | U :: Us => U ⊔ affineUnion Us

lemma affineUnion_inf {X : Scheme.{u}} (U : X.Opens) (Us : List X.Opens) :
    U ⊓ affineUnion Us = affineUnion (Us.map (fun V => U ⊓ V)) := by
  induction Us with
  | nil => simp [affineUnion]
  | cons V Vs ih =>
    simp only [affineUnion, List.map_cons, inf_sup_left, ih]

/-- The affine union of the entries of a finite function is their indexed supremum. -/
lemma affineUnion_ofFn {X : Scheme.{u}} {m : ℕ} (U : Fin m → X.Opens) :
    affineUnion (List.ofFn U) = ⨆ i : Fin m, U i := by
  induction m with
  | zero => simp [List.ofFn_zero, affineUnion, iSup_of_empty]
  | succ m ih =>
    rw [List.ofFn_succ, affineUnion, ih]
    apply le_antisymm
    · exact sup_le (le_iSup U 0) (iSup_le fun i => le_iSup U i.succ)
    · apply iSup_le
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact le_sup_left
      · exact (le_iSup (fun j : Fin m => U j.succ) j).trans le_sup_right

theorem isZero_rightDerived_sections_finiteAffine {X : Scheme.{u}}
    [IsLocallyNoetherian X] [X.IsSeparated] (Us : List X.Opens)
    (hUs : ∀ U ∈ Us, IsAffineOpen U) (hne : Us ≠ []) (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((sections (affineUnion Us)).rightDerived (n + Us.length)).obj
      ((moduleToSheafAb X).obj M)) := by
  cases Us with
  | nil => exact False.elim (hne rfl)
  | cons U Us =>
    by_cases htail : Us = []
    · subst Us
      simpa [affineUnion] using
        (isZero_rightDerived_sections_affineOpen_succ U (hUs U (by simp)) M n)
    · have hU : IsAffineOpen U := hUs U (by simp)
      have htailUs : ∀ V ∈ Us, IsAffineOpen V := by
        intro V hV
        exact hUs V (by simp [hV])
      have htailzero := isZero_rightDerived_sections_finiteAffine Us htailUs htail M (n + 1)
      have hmap : ∀ V ∈ Us.map (fun W => U ⊓ W), IsAffineOpen V := by
        intro V hV
        obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hV
        exact hU.inf (htailUs W hW)
      have hmapne : Us.map (fun W => U ⊓ W) ≠ [] := by
        simpa using htail
      have hinter := isZero_rightDerived_sections_finiteAffine
        (Us.map (fun W => U ⊓ W)) hmap hmapne M n
      apply isZero_rightDerived_sections_sup ((moduleToSheafAb X).obj M) U
        (affineUnion Us) (n + Us.length)
      · exact isZero_rightDerived_sections_affineOpen_succ U hU M (n + Us.length)
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htailzero
      · rw [affineUnion_inf]
        simpa using hinter
termination_by Us.length

theorem isZero_rightDerived_sections_finiteAffineCover
    {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsSeparated] (Us : List X.Opens)
    (hUs : ∀ U ∈ Us, IsAffineOpen U) (hcover : affineUnion Us = ⊤) (hne : Us ≠ [])
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((sections (⊤ : Opens X)).rightDerived (n + Us.length)).obj
      ((moduleToSheafAb X).obj M)) := by
  rw [← hcover]
  exact isZero_rightDerived_sections_finiteAffine Us hUs hne M n

end GromovWitten.AlgebraicGeometry.SheafCohomology
