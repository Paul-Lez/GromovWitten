/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.FlasqueComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
/-!
# Flasque resolutions indexed by natural numbers

The comparison theorem for bounded-below flasque complexes applies to the
natural-number indexing of injective resolutions after extension by zero to the
integers. We construct the compatibility of additive functors with that extension
and then transfer the quasi-isomorphism theorem.
-/

open CategoryTheory Limits HomologicalComplex
open ComplexShape CochainComplex CategoryTheory.Functor
universe u v u' v'
noncomputable section
namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ)

private def mapCochainExtendXIso (n : ℤ) :
    F.obj ((K.extend embeddingUpNat).X n) ≅
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extend embeddingUpNat).X n := by
  by_cases hn : 0 ≤ n
  · let h : embeddingUpNat.f n.toNat = n := by simpa using Int.toNat_of_nonneg hn
    exact F.mapIso (K.extendXIso embeddingUpNat h) ≪≫
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso embeddingUpNat h).symm
  · exact IsZero.iso (F.map_isZero (K.isZero_extend_X embeddingUpNat n
      (by intro i; change (i : ℤ) ≠ n; omega)))
      (((F.mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X embeddingUpNat n
        (by intro i; change (i : ℤ) ≠ n; omega))

private lemma mapCochainExtendXIso_nat (n : ℕ) :
    mapCochainExtendXIso F K n = F.mapIso (K.extendXIso embeddingUpNat (i := n) rfl) ≪≫
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso embeddingUpNat (i := n) rfl).symm := by
  simp only [mapCochainExtendXIso, Nat.cast_nonneg, dif_pos, Int.toNat_natCast]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- An additive functor commutes with extension by zero from natural to integer cochains. -/
def mapCochainExtendIso :
    (F.mapHomologicalComplex (.up ℤ)).obj (K.extend embeddingUpNat) ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj K).extend embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents (mapCochainExtendXIso F K) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    by_cases hi : 0 ≤ i
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp]
      simp only [mapCochainExtendXIso_nat, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
      change _ = F.map ((K.extend embeddingUpNat).d (n : ℤ) ((n + 1 : ℕ) : ℤ)) ≫ _
      rw [K.extend_d_eq embeddingUpNat (i := n) (j := n + 1)
          (i' := (n : ℤ)) (j' := ((n + 1 : ℕ) : ℤ)) rfl rfl,
        (((F.mapHomologicalComplex (.up ℕ)).obj K).extend_d_eq embeddingUpNat
          (i := n) (j := n + 1)
          (i' := (n : ℤ)) (j' := ((n + 1 : ℕ) : ℤ)) rfl rfl)]
      simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
      have hf := (F.mapIso (K.extendXIso embeddingUpNat (i := n + 1) rfl)).inv_hom_id
      change F.map (K.extendXIso embeddingUpNat (i := n + 1) rfl).inv ≫
        F.map (K.extendXIso embeddingUpNat (i := n + 1) rfl).hom = 𝟙 _ at hf
      rw [reassoc_of% hf]
      rfl
    · exact (F.map_isZero (K.isZero_extend_X embeddingUpNat i
        (by intro n; change (n : ℤ) ≠ i; omega))).eq_of_src _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Extension compatibility is natural in the cochain complex. -/
lemma mapCochainExtendIso_hom_naturality {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).map (extendMap φ embeddingUpNat) ≫
        (mapCochainExtendIso F L).hom =
      (mapCochainExtendIso F K).hom ≫
        extendMap ((F.mapHomologicalComplex (.up ℕ)).map φ) embeddingUpNat := by
  ext i
  by_cases hi : 0 ≤ i
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    change F.map ((extendMap φ embeddingUpNat).f n) ≫ (mapCochainExtendXIso F L n).hom =
      (mapCochainExtendXIso F K n).hom ≫
        (extendMap ((F.mapHomologicalComplex (.up ℕ)).map φ) embeddingUpNat).f n
    rw [mapCochainExtendXIso_nat, mapCochainExtendXIso_nat,
      extendMap_f φ embeddingUpNat (i := n) (i' := (n : ℤ)) rfl,
      extendMap_f ((F.mapHomologicalComplex (.up ℕ)).map φ) embeddingUpNat
        (i := n) (i' := (n : ℤ)) rfl]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc, Iso.inv_hom_id_assoc]
    have hf := (F.mapIso (L.extendXIso embeddingUpNat (i := n) rfl)).inv_hom_id
    change F.map (L.extendXIso embeddingUpNat (i := n) rfl).inv ≫
      F.map (L.extendXIso embeddingUpNat (i := n) rfl).hom = 𝟙 _ at hf
    rw [reassoc_of% hf]
    rfl
  · exact (F.map_isZero (K.isZero_extend_X embeddingUpNat i
      (by intro n; change (n : ℤ) ≠ i; omega))).eq_of_src _ _

end CategoryTheory.Functor

namespace TopCat.Sheaf
universe w
variable {X Y : TopCat.{w}} (f : X ⟶ Y)
variable [(pushforward AddCommGrpCat.{w} f).Additive]
/-- Pushforward preserves quasi-isomorphisms between flasque resolutions indexed by `ℕ`. -/
lemma pushforward_quasiIso_of_flasque
    {K L : CochainComplex (Sheaf AddCommGrpCat.{w} X) ℕ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ n, IsFlasque (K.X n)) (hL : ∀ n, IsFlasque (L.X n)) :
    QuasiIso (((pushforward AddCommGrpCat f).mapHomologicalComplex (.up ℕ)).map φ) := by
  let P := pushforward AddCommGrpCat.{w} f
  have hf {M : CochainComplex (Sheaf AddCommGrpCat.{w} X) ℕ}
      (hM : ∀ n, IsFlasque (M.X n)) (i : ℤ) : IsFlasque ((M.extend embeddingUpNat).X i) := by
    by_cases hi : 0 ≤ i
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      have := hM n
      exact isFlasque_of_iso (M.extendXIso embeddingUpNat (i := n) rfl).symm
    · exact isFlasque_of_isZero _ (M.isZero_extend_X embeddingUpNat i
        (by intro n; change (n : ℤ) ≠ i; omega))
  have he := pushforward_quasiIso_of_boundedBelow_flasque f (extendMap φ embeddingUpNat)
    (hf hK) (hf hL) 0 0
  apply (quasiIso_extendMap_iff _ embeddingUpNat).mp
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (mapCochainExtendIso P K) (mapCochainExtendIso P L)
      (mapCochainExtendIso_hom_naturality P φ).symm)).mp he
end TopCat.Sheaf

end
