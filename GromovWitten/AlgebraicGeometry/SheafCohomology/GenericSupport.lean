/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Topology.Sheaves.Flasque
import GromovWitten.Topology.DimensionOne
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Flasqueness from vanishing generic stalks

On a Noetherian sober space of dimension at most one, a sheaf with zero generic
stalks is flasque. Each local section has finite closed support, so it extends
by zero across the complement of that support.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

attribute [local instance] Classical.propDecidable

private def sectionSupport {Y : TopCat.{u}} (F : Y.Sheaf AddCommGrpCat.{u})
    (U : Opens Y) (s : F.obj.obj (op U)) : Set U :=
  {x | F.presheaf.germ U x.1 x.2 s ≠ 0}

private theorem isOpen_compl_sectionSupport {Y : TopCat.{u}}
    (F : Y.Sheaf AddCommGrpCat.{u}) (U : Opens Y) (s : F.obj.obj (op U)) :
    IsOpen (sectionSupport F U s)ᶜ := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hxzero : F.presheaf.germ U x.1 x.2 s = 0 := by
    exact not_ne_iff.mp hx
  obtain ⟨W, hxW, iWU, iVU, heq⟩ :=
    F.presheaf.germ_eq x.1 x.2 x.2 s 0 (by simp [hxzero])
  have hWzero : F.presheaf.map iWU.op s = 0 := by
    simpa using heq
  let N : Set U := {y | y.1 ∈ W}
  refine mem_nhds_iff.mpr ⟨N, ?_, isOpen_induced W.2, hxW⟩
  intro y hy
  have hyW : y.1 ∈ W := hy
  have hyzero : F.presheaf.germ U y.1 y.2 s = 0 := by
    rw [← F.presheaf.germ_res_apply iWU y.1 hyW s, hWzero, map_zero]
  exact not_ne_iff.mpr hyzero

private theorem isClosed_sectionSupport {Y : TopCat.{u}}
    (F : Y.Sheaf AddCommGrpCat.{u}) (U : Opens Y) (s : F.obj.obj (op U)) :
    IsClosed (sectionSupport F U s) :=
  isOpen_compl_iff.mp (isOpen_compl_sectionSupport F U s)

private theorem finite_sectionSupport {Y : TopCat.{u}}
    [T0Space (Y : Type u)]
    [NoetherianSpace (Y : Type u)] [QuasiSober (Y : Type u)]
    (hd : topologicalKrullDim (Y : Type u) ≤ 1)
    (F : Y.Sheaf AddCommGrpCat.{u})
    (hgen : ∀ x : Y, x ∈ genericPoints (Y : Type u) →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.1))
    (U : Opens Y) (s : F.obj.obj (op U)) :
    (sectionSupport F U s).Finite := by
  have hNoetherian : NoetherianSpace (U : Type u) :=
    TopologicalSpace.NoetherianSpace.set (U : Set (Y : Type u))
  have hQuasiSober : QuasiSober (U : Type u) := U.isOpenEmbedding'.quasiSober
  apply GromovWitten.Topology.finite_of_isClosed_of_closed_points
    (sectionSupport F U s) (isClosed_sectionSupport F U s)
  intro x hx
  have hxngen : x.1 ∉ genericPoints (Y : Type u) := by
    intro hxgen
    have hz := hgen x.1 hxgen
    have hsub : Subsingleton ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x.1).obj F.1) :=
      AddCommGrpCat.subsingleton_of_isZero hz
    have hzero : F.presheaf.germ U x.1 x.2 s = 0 :=
      @Subsingleton.elim _ hsub _ _
    exact hx hzero
  have hamb : IsClosed ({x.1} : Set (Y : Type u)) :=
    GromovWitten.Topology.isClosed_singleton_of_not_genericPoints hd x.1 hxngen
  have hpre : Subtype.val ⁻¹' ({x.1} : Set (Y : Type u)) = ({x} : Set U) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact Subtype.ext_iff.symm
  rw [← hpre]
  exact isClosed_induced hamb

private theorem finite_closed_section_support {Y : TopCat.{u}}
    [T0Space (Y : Type u)]
    [NoetherianSpace (Y : Type u)] [QuasiSober (Y : Type u)]
    (hd : topologicalKrullDim (Y : Type u) ≤ 1)
    (F : Y.Sheaf AddCommGrpCat.{u})
    (hgen : ∀ x : Y, x ∈ genericPoints (Y : Type u) →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.1))
    (U : Opens Y) (s : F.obj.obj (op U)) :
    ∃ S : Set (Y : Type u), S.Finite ∧ IsClosed S ∧ S ⊆ U ∧
      ∀ x (hx : x ∈ U), x ∈ S ↔ F.presheaf.germ U x hx s ≠ 0 := by
  let T := sectionSupport F U s
  have hTfinite : T.Finite := finite_sectionSupport hd F hgen U s
  let S : Set (Y : Type u) := (fun x : U => (x : Y)) '' T
  have hSfinite : S.Finite := hTfinite.image fun x : U => (x : Y)
  have hSclosed : IsClosed S := by
    rw [← Set.biUnion_of_singleton S]
    apply hSfinite.isClosed_biUnion
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    change F.presheaf.germ U z.1 z.2 s ≠ 0 at hz
    have hzngen : z.1 ∉ genericPoints (Y : Type u) := by
      intro hzgen
      have hsub : Subsingleton ((TopCat.Presheaf.stalkFunctor AddCommGrpCat z.1).obj F.1) :=
        AddCommGrpCat.subsingleton_of_isZero (hgen z.1 hzgen)
      have hzero : F.presheaf.germ U z.1 z.2 s = 0 :=
        @Subsingleton.elim _ hsub _ _
      exact hz hzero
    exact GromovWitten.Topology.isClosed_singleton_of_not_genericPoints
      hd z.1 hzngen
  have hSsub : S ⊆ U := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact z.2
  refine ⟨S, hSfinite, hSclosed, hSsub, ?_⟩
  intro x hx
  constructor
  · rintro ⟨z, hz, hzx⟩
    change F.presheaf.germ U z.1 z.2 s ≠ 0 at hz
    subst x
    simpa using hz
  · intro hxne
    exact ⟨⟨x, hx⟩, hxne, rfl⟩

/-- A sheaf with zero stalks at all generic points of a noetherian curve is flasque.

The extension of a section over `U` is obtained by gluing it with zero on the
complement in the larger open of its finite closed support.
-/
theorem isFlasque_of_zero_generic_stalks {Y : TopCat.{u}}
    [T0Space (Y : Type u)]
    [NoetherianSpace (Y : Type u)] [QuasiSober (Y : Type u)]
    (hd : topologicalKrullDim (Y : Type u) ≤ 1)
    (F : Y.Sheaf AddCommGrpCat.{u})
    (hgen : ∀ x : Y, x ∈ genericPoints (Y : Type u) →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.1)) :
    TopCat.Sheaf.IsFlasque F where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨S, hSfinite, hSclosed, hSsub, hSiff⟩ :=
      finite_closed_section_support hd F hgen V.unop s
    let W : Opens Y := Opens.mk (U.unop \ S) (U.unop.2.sdiff hSclosed)
    have hWle : W ≤ U.unop := by
      intro x hx
      exact hx.1
    have hcover : U.unop ≤ V.unop ⊔ W := by
      intro x hx
      change x ∈ (V.unop : Set (Y : Type u)) ∪ (W : Set (Y : Type u))
      rw [Opens.coe_mk, Set.mem_union]
      by_cases hxS : x ∈ S
      · left
        exact hSsub hxS
      · right
        exact ⟨hx, hxS⟩
    have hs0 : s |_ (V.unop ⊓ W) = 0 := by
      apply TopCat.Presheaf.section_ext F (V.unop ⊓ W)
      intro x hx
      have hxU : x ∈ V.unop := hx.1
      have hxW : x ∈ W := hx.2
      have hxnotS : x ∉ S := hxW.2
      have hxzero : F.presheaf.germ V.unop x hxU s = 0 := by
        apply Classical.byContradiction
        intro hne
        exact hxnotS ((hSiff x hxU).mpr hne)
      change F.presheaf.germ (V.unop ⊓ W) x hx
          (F.presheaf.map (Opens.infLELeft V.unop W).op s) =
        F.presheaf.germ (V.unop ⊓ W) x hx 0
      rw [F.presheaf.germ_res_apply (Opens.infLELeft V.unop W) x hx s,
        hxzero, map_zero]
    have hs0rev : s |_ (W ⊓ V.unop) = 0 := by
      have h := congrArg (fun z => TopCat.Presheaf.restrictOpen z
          (W ⊓ V.unop) (le_of_eq (inf_comm _ _))) hs0
      rw [TopCat.Presheaf.restrict_restrict] at h
      simpa [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] using h
    have hL : Opens.infLELeft V.unop W = homOfLE inf_le_left := by
      subsingleton
    have hR : Opens.infLERight V.unop W = homOfLE inf_le_right := by
      subsingleton
    have hLrev : Opens.infLELeft W V.unop = homOfLE inf_le_left := by
      subsingleton
    have hRrev : Opens.infLERight W V.unop = homOfLE inf_le_right := by
      subsingleton
    let f : Fin 2 → Opens Y := ![V.unop, W]
    let sf : (j : Fin 2) → F.obj.obj (op (f j))
      | 0 => s
      | 1 => 0
    have hcomp : TopCat.Presheaf.IsCompatible F.1 f sf := by
      simp only [TopCat.Presheaf.IsCompatible, Fin.forall_fin_two]
      refine ⟨⟨rfl, ?_⟩, Eq.symm ?_, rfl⟩
      · dsimp [f, sf]
        rw [hL, hR]
        change F.presheaf.map (homOfLE inf_le_left).op s =
          F.presheaf.map (homOfLE inf_le_right).op 0
        rw [map_zero]
        exact hs0
      · dsimp [f, sf]
        rw [hRrev, hLrev]
        change F.presheaf.map (homOfLE inf_le_right).op s =
          F.presheaf.map (homOfLE inf_le_left).op 0
        rw [map_zero]
        exact hs0rev
    let iUV : ∀ j, f j ⟶ U.unop
      | 0 => i.unop
      | 1 => homOfLE hWle
    have hf : iSup f = V.unop ⊔ W := by
      apply le_antisymm
      · refine iSup_le (fun j => ?_)
        fin_cases j
        · exact le_sup_left
        · exact le_sup_right
      · rw [sup_le_iff]
        exact ⟨le_iSup f 0, le_iSup f 1⟩
    have hcover' : U.unop ≤ iSup f := by
      rw [hf]
      exact hcover
    obtain ⟨t, ht, _⟩ := F.existsUnique_gluing' f U.unop iUV hcover' sf hcomp
    refine ⟨t, ?_⟩
    dsimp [iUV, f, sf] at ht ⊢
    exact ht 0

end GromovWitten.AlgebraicGeometry.SheafCohomology
