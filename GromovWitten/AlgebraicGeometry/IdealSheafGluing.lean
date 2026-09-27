/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import GromovWitten.AlgebraicGeometry.LocalizationIdealPullback
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
/-!
# Gluing ideal sheaves from locally represented stalk ideals

A family of stalk ideals which is represented by an ideal on an affine neighborhood
of each point determines an ideal sheaf. The proof glues over finite principal
covers using localization, then applies the affine communication lemma. No
quasi-separatedness hypothesis is needed.
-/

open CategoryTheory Opposite
open AlgebraicGeometry
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u})
/-- Restriction to a principal open commutes with contraction of an affine ideal. -/
lemma map_comap_basicOpen (U V : X.affineOpens) (h : V ≤ U)
    (r : Γ(X, U.1)) (J : Ideal Γ(X, V.1)) :
    (J.comap (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom).map
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
    (J.map (X.presheaf.map (homOfLE
      (X.basicOpen_le (X.presheaf.map (homOfLE (X := X.Opens) h).op r))).op).hom).comap
      (X.presheaf.map (homOfLE (X.basicOpen_restrict (homOfLE (X := X.Opens) h) r)).op).hom := by
  let s := X.presheaf.map (homOfLE (X := X.Opens) h).op r
  let iRS : Algebra Γ(X, U.1) Γ(X, V.1) :=
    (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  let iAB : Algebra Γ(X, X.basicOpen r) Γ(X, X.basicOpen s) :=
    (X.presheaf.map (homOfLE (X.basicOpen_restrict (homOfLE (X := X.Opens) h) r)).op).hom.toAlgebra
  let iRB : Algebra Γ(X, U.1) Γ(X, X.basicOpen s) :=
    (X.presheaf.map (homOfLE ((X.basicOpen_le s).trans h)).op).hom.toAlgebra
  have htS : IsScalarTower Γ(X, U.1) Γ(X, V.1) Γ(X, X.basicOpen s) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change _ = (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom.comp
      (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom
    rw [← CommRingCat.hom_comp, ← X.presheaf.map_comp]
    rfl
  have htA : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen r) Γ(X, X.basicOpen s) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change _ = (X.presheaf.map
      (homOfLE (X.basicOpen_restrict (homOfLE (X := X.Opens) h) r)).op).hom.comp
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
    rw [← CommRingCat.hom_comp, ← X.presheaf.map_comp]
    rfl
  have hA := U.2.isLocalization_basicOpen r
  have hB := V.2.isLocalization_basicOpen s
  exact IsLocalization.ideal_map_comap_away Γ(X, U.1) Γ(X, V.1)
    Γ(X, X.basicOpen r) Γ(X, X.basicOpen s) r J


/-- A local ideal realizes the prescribed stalk ideals. -/
def RepresentsStalkIdeals (Z : ∀ x : X, Ideal (X.presheaf.stalk x))
    (U : X.affineOpens) (I : Ideal Γ(X, U.1)) : Prop :=
  ∀ (x : X) (hx : x ∈ U.1), I.map (X.presheaf.germ U.1 x hx).hom = Z x

/-- Restriction preserves the represented stalk ideals. -/
lemma representsStalkIdeals_map {Z : ∀ x : X, Ideal (X.presheaf.stalk x)}
    {U V : X.affineOpens} (h : V ≤ U) {I : Ideal Γ(X, U.1)}
    (hI : X.RepresentsStalkIdeals Z U I) :
    X.RepresentsStalkIdeals Z V
      (I.map (X.presheaf.map (homOfLE h).op).hom) := by
  intro x hx
  simpa only [Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res']
    using hI x (h hx)

/-- Ideals on an affine open are determined by their stalk ideals. -/
lemma representsStalkIdeals_unique {Z : ∀ x : X, Ideal (X.presheaf.stalk x)}
    {U : X.affineOpens} {I J : Ideal Γ(X, U.1)}
    (hI : X.RepresentsStalkIdeals Z U I) (hJ : X.RepresentsStalkIdeals Z U J) : I = J := by
  rw [U.2.ideal_ext_iff]
  exact fun x hx => (hI x hx).trans (hJ x hx).symm


/-- Two representatives of the same stalk ideals agree on affine overlaps. -/
lemma representsStalkIdeals_overlap
    {Z : ∀ x : X, Ideal (X.presheaf.stalk x)} {U V W : X.affineOpens}
    (hU : W ≤ U) (hV : W ≤ V) {I : Ideal Γ(X, U.1)} {J : Ideal Γ(X, V.1)}
    (hI : X.RepresentsStalkIdeals Z U I) (hJ : X.RepresentsStalkIdeals Z V J) :
    I.map (X.presheaf.map (homOfLE (X := X.Opens) hU).op).hom =
      J.map (X.presheaf.map (homOfLE (X := X.Opens) hV).op).hom :=
  X.representsStalkIdeals_unique (U := W)
    (X.representsStalkIdeals_map (U := U) (V := W) hU hI)
    (X.representsStalkIdeals_map (U := V) (V := W) hV hJ)

/-- Ideals with the same stalk data glue over a finite principal cover. -/
lemma exists_ideal_of_basicOpen_cover
    (Z : ∀ x : X, Ideal (X.presheaf.stalk x)) (U : X.affineOpens)
    (s : Finset Γ(X, U.1)) (hs : Ideal.span (s : Set Γ(X, U.1)) = ⊤)
    (hlocal : ∀ r : s, ∃ J : Ideal Γ(X, X.basicOpen r.1),
      X.RepresentsStalkIdeals Z (X.affineBasicOpen r.1) J) :
    ∃ I : Ideal Γ(X, U.1), X.RepresentsStalkIdeals Z U I := by
  classical
  choose J hJ using hlocal
  let I : Ideal Γ(X, U.1) := ⨅ r : s,
    (J r).comap (X.presheaf.map (homOfLE (X.basicOpen_le r.1)).op).hom
  have hmap (r : s) :
      I.map (X.presheaf.map (homOfLE (X.basicOpen_le r.1)).op).hom = J r := by
    have hloc := U.2.isLocalization_basicOpen r.1
    apply le_antisymm
    · calc
        _ ≤ ((J r).comap (X.presheaf.map (homOfLE (X.basicOpen_le r.1)).op).hom).map
            (X.presheaf.map (homOfLE (X.basicOpen_le r.1)).op).hom :=
          Ideal.map_mono (iInf_le _ r)
        _ = J r := IsLocalization.map_under (.powers r.1) Γ(X, X.basicOpen r.1) (J r)
    · change J r ≤ Ideal.map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r.1)) I
      dsimp only [I]
      rw [IsLocalization.ideal_map_iInf_finite _ (.powers r.1)]
      refine le_iInf fun t => ?_
      change J r ≤ Ideal.map
        (X.presheaf.map (homOfLE (X.basicOpen_le r.1)).op).hom _
      refine le_trans ?_
        (X.map_comap_basicOpen U (X.affineBasicOpen t.1)
          (X.basicOpen_le t.1) r.1 (J t)).symm.le
      apply Ideal.map_le_iff_le_comap.mp
      apply le_of_eq
      let v := X.presheaf.map (homOfLE (X.basicOpen_le t.1)).op r.1
      exact X.representsStalkIdeals_overlap
        (U := X.affineBasicOpen r.1) (V := X.affineBasicOpen t.1)
        (W := X.affineBasicOpen (U := X.affineBasicOpen t.1) v)
        (X.basicOpen_restrict (homOfLE (X.basicOpen_le t.1)) r.1)
        (X.basicOpen_le v) (hJ r) (hJ t)
  refine ⟨I, fun x hx => ?_⟩
  have hcov : (⨆ r : s, X.basicOpen r.1) = U.1 := U.2.iSup_basicOpen_eq_self_iff.mpr hs
  obtain ⟨r, hr⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.symm ▸ hx)
  have he := congrArg (Ideal.map (X.presheaf.germ (X.basicOpen r.1) x hr).hom) (hmap r)
  have he' : I.map (X.presheaf.germ U.1 x hx).hom =
      (J r).map (X.presheaf.germ (X.basicOpen r.1) x hr).hom := by
    simpa only [Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res'] using he
  exact he'.trans (hJ r x hr)


/-- Locally represented stalk ideals have an ideal representative on every affine open. -/
lemma exists_ideal_of_locally_represented_stalkIdeals
    (Z : ∀ x : X, Ideal (X.presheaf.stalk x))
    (hZ : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ I : Ideal Γ(X, U.1), X.RepresentsStalkIdeals Z U I)
    (U : X.affineOpens) : ∃ I : Ideal Γ(X, U.1), X.RepresentsStalkIdeals Z U I := by
  let ι := {V : X.affineOpens // ∃ I : Ideal Γ(X, V.1), X.RepresentsStalkIdeals Z V I}
  have hcover : (⨆ V : ι, V.1.1) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨V, hxV, hV⟩ := hZ x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩
  refine of_affine_open_cover (fun V : ι => V.1) hcover U ?_ ?_ (fun V => V.2)
  · intro V r hV
    obtain ⟨I, hI⟩ := hV
    exact ⟨_, X.representsStalkIdeals_map (X.basicOpen_le r) hI⟩
  · exact fun V s hs hlocal => X.exists_ideal_of_basicOpen_cover Z V s hs hlocal

/-- Glue locally represented stalk ideals to an ideal sheaf. -/
def idealSheafOfStalkIdeals
    (Z : ∀ x : X, Ideal (X.presheaf.stalk x))
    (hZ : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ I : Ideal Γ(X, U.1), X.RepresentsStalkIdeals Z U I) : X.IdealSheafData where
  ideal U := (X.exists_ideal_of_locally_represented_stalkIdeals Z hZ U).choose
  map_ideal_basicOpen U r := X.representsStalkIdeals_unique
    (X.representsStalkIdeals_map (X.basicOpen_le r)
      (X.exists_ideal_of_locally_represented_stalkIdeals Z hZ U).choose_spec)
    (X.exists_ideal_of_locally_represented_stalkIdeals Z hZ (X.affineBasicOpen r)).choose_spec

/-- The glued ideal sheaf agrees with every affine representative of the stalk data. -/
lemma idealSheafOfStalkIdeals_ideal
    (Z : ∀ x : X, Ideal (X.presheaf.stalk x))
    (hZ : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ I : Ideal Γ(X, U.1), X.RepresentsStalkIdeals Z U I)
    (U : X.affineOpens) (I : Ideal Γ(X, U.1))
    (hI : X.RepresentsStalkIdeals Z U I) :
    (X.idealSheafOfStalkIdeals Z hZ).ideal U = I :=
  X.representsStalkIdeals_unique
    (X.exists_ideal_of_locally_represented_stalkIdeals Z hZ U).choose_spec hI

/-- Equality of ideal sheaves can be checked on an affine neighborhood of each point. -/
lemma IdealSheafData.ext_of_locally_eq {I J : X.IdealSheafData}
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ I.ideal U = J.ideal U) : I = J := by
  choose U hx hIJ using h
  apply IdealSheafData.ext_of_iSup_eq_top U _ hIJ
  apply top_unique
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
end AlgebraicGeometry.Scheme
