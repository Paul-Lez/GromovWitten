/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Homotopy transfer for complex base-change maps

This transfers a quasi-isomorphism across homotopic choices of the source and
target complex maps. It is the formal comparison needed when a flasque
resolution is replaced by a canonical injective resolution.
-/

open CategoryTheory Limits
open HomologicalComplex

noncomputable section
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace CategoryTheory.NatTrans

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable {E : Type u₃} [Category.{v₃} E] [Abelian E]
variable {H : Type u₄} [Category.{v₄} H] [Abelian H]

variable (Q : C ⥤ D) (F : D ⥤ H) (L : C ⥤ E) (P : E ⥤ H)
variable [Q.Additive] [F.Additive] [L.Additive] [P.Additive]

set_option backward.isDefEq.respectTransparency false in
/-- The chain map induced by a natural base-change map and a complex map. -/
def complexBaseChangeMap
    {K : CochainComplex C ℕ} {J : CochainComplex E ℕ}
    (α : Q ⋙ F ⟶ L ⋙ P)
    (φ : (L.mapHomologicalComplex (.up ℕ)).obj K ⟶ J) :
    (F.mapHomologicalComplex (.up ℕ)).obj
        ((Q.mapHomologicalComplex (.up ℕ)).obj K) ⟶
      (P.mapHomologicalComplex (.up ℕ)).obj J :=
  by
    let a : (F.mapHomologicalComplex (.up ℕ)).obj
        ((Q.mapHomologicalComplex (.up ℕ)).obj K) ⟶
        (P.mapHomologicalComplex (.up ℕ)).obj
          ((L.mapHomologicalComplex (.up ℕ)).obj K) :=
      (NatTrans.mapHomologicalComplex α (.up ℕ)).app K
    exact a ≫ (P.mapHomologicalComplex (.up ℕ)).map φ

set_option backward.isDefEq.respectTransparency false in
/-- Homotopic choices of the complex map have the same quasi-isomorphism status. -/
lemma complexBaseChangeMap_quasiIso_of_homotopy
    [F.PreservesHomology]
    {K K' : CochainComplex C ℕ} {J J' : CochainComplex E ℕ}
    (α : Q ⋙ F ⟶ L ⋙ P) (u : K ⟶ K') (v : J ⟶ J')
    (φ : (L.mapHomologicalComplex (.up ℕ)).obj K ⟶ J)
    (ψ : (L.mapHomologicalComplex (.up ℕ)).obj K' ⟶ J')
    (hhom : Homotopy
      ((L.mapHomologicalComplex (.up ℕ)).map u ≫ ψ) (φ ≫ v))
    [QuasiIso ((Q.mapHomologicalComplex (.up ℕ)).map u)]
    [QuasiIso ((P.mapHomologicalComplex (.up ℕ)).map v)]
    [QuasiIso (complexBaseChangeMap Q F L P α ψ)] :
    QuasiIso (complexBaseChangeMap Q F L P α φ) := by
  let Qₕ := Q.mapHomologicalComplex (.up ℕ)
  let Fₕ := F.mapHomologicalComplex (.up ℕ)
  let Lₕ := L.mapHomologicalComplex (.up ℕ)
  let Pₕ := P.mapHomologicalComplex (.up ℕ)
  let αₕ := NatTrans.mapHomologicalComplex α (.up ℕ)
  let aK : (F.mapHomologicalComplex (.up ℕ)).obj (Qₕ.obj K) ⟶
      (P.mapHomologicalComplex (.up ℕ)).obj (Lₕ.obj K) := αₕ.app K
  let aK' : (F.mapHomologicalComplex (.up ℕ)).obj (Qₕ.obj K') ⟶
      (P.mapHomologicalComplex (.up ℕ)).obj (Lₕ.obj K') := αₕ.app K'
  let βφ := complexBaseChangeMap Q F L P α φ
  let βψ := complexBaseChangeMap Q F L P α ψ
  let _ : QuasiIso (Fₕ.map (Qₕ.map u)) := by infer_instance
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hFQ : IsIso (homologyMap (Fₕ.map (Qₕ.map u)) n) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  have hPv : IsIso (homologyMap (Pₕ.map v) n) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  have hβψ : IsIso (homologyMap βψ n) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  let hsq :
    homologyMap (Fₕ.map (Qₕ.map u)) n ≫ homologyMap βψ n =
        homologyMap βφ n ≫ homologyMap (Pₕ.map v) n := by
    rw [← homologyMap_comp, ← homologyMap_comp]
    have hnat : Fₕ.map (Qₕ.map u) ≫ aK' = aK ≫ Pₕ.map (Lₕ.map u) := by
      apply HomologicalComplex.Hom.ext
      funext i
      exact α.naturality (u.f i)
    change homologyMap (Fₕ.map (Qₕ.map u) ≫ aK' ≫ Pₕ.map ψ) n =
      homologyMap ((aK ≫ Pₕ.map φ) ≫ Pₕ.map v) n
    rw [← Category.assoc, hnat]
    simp only [Category.assoc, ← Pₕ.map_comp]
    rw [homologyMap_comp, homologyMap_comp,
      Homotopy.homologyMap_eq (P.mapHomotopy hhom) n]
  have hcomp : IsIso (homologyMap βφ n ≫ homologyMap (Pₕ.map v) n) := by
    rw [← hsq]
    exact IsIso.comp_isIso
  let _ : IsIso (homologyMap (Pₕ.map v) n) := hPv
  let _ : IsIso (homologyMap βφ n ≫ homologyMap (Pₕ.map v) n) := hcomp
  change IsIso (homologyMap βφ n)
  exact IsIso.of_isIso_comp_right (homologyMap βφ n) (homologyMap (Pₕ.map v) n)

end CategoryTheory.NatTrans
