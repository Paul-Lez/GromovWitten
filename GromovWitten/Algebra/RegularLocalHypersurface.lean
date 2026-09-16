/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Regular local hypersurfaces

This file proves the cotangent-space criterion for a hypersurface in a regular local ring.  A
nonzerodivisor cuts out a regular local quotient exactly when its class in the cotangent space is
nonzero, equivalently when it does not belong to the square of the maximal ideal.
-/

open IsLocalRing

universe u

namespace IsRegularLocalRing

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- A hypersurface in a regular local ring, cut out by a nonzerodivisor in the maximal ideal, is
regular exactly when its equation has nonzero linear term. -/
theorem quotient_span_singleton_iff {x : A}
    (hreg : IsSMulRegular A x) (hx : x ∈ maximalIdeal A) :
    IsRegularLocalRing (A ⧸ Ideal.span {x}) ↔ x ∉ maximalIdeal A ^ 2 := by
  classical
  let I : Ideal A := Ideal.span {x}
  have hI : I ≤ maximalIdeal A := Ideal.span_le.mpr fun y hy => by
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    exact hyx ▸ hx
  let B := A ⧸ I
  let : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hI
  let : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q : A →+* B := Ideal.Quotient.mk I
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  let : Algebra A B := q.toAlgebra
  let : IsLocalHom q := IsLocalHom.of_surjective q hq
  have hcomap : (maximalIdeal B).comap q = maximalIdeal A :=
    IsLocalRing.maximalIdeal_comap q
  let qbar : ResidueField A →+* ResidueField B :=
    Ideal.quotientMap (maximalIdeal B) q hcomap.ge
  have hqbar_inj : Function.Injective qbar :=
    Ideal.quotientMap_injective' hcomap.le
  have hqbar_surj : Function.Surjective qbar :=
    Ideal.quotientMap_surjective hq
  have hqbar : Function.Bijective qbar := ⟨hqbar_inj, hqbar_surj⟩
  let : Module (ResidueField A) (CotangentSpace B) :=
    Module.compHom (CotangentSpace B) qbar
  have halg : algebraMap A B = q := rfl
  have hker : RingHom.ker (algebraMap A B) = I := by
    rw [halg]
    exact Ideal.mk_ker
  have heq : (maximalIdeal B).comap (algebraMap A B) =
      RingHom.ker (algebraMap A B) ⊔ maximalIdeal A := by
    change (maximalIdeal B).comap q = RingHom.ker q ⊔ maximalIdeal A
    rw [hcomap, Ideal.mk_ker, sup_eq_right.mpr hI]
  let hle : maximalIdeal A ≤ (maximalIdeal B).comap (algebraMap A B) :=
    le_of_le_of_eq le_sup_right heq.symm
  let mapcot : CotangentSpace A →ₗ[A] CotangentSpace B :=
    Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B) hle
  let phi : CotangentSpace A →ₗ[ResidueField A] CotangentSpace B :=
    { mapcot with
      map_smul' := by
        intro c z
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        exact mapcot.map_smul a z }
  have hphi_surj : Function.Surjective phi := by
    exact Ideal.mapCotangent_surjective_of_comap_eq hq heq
  let vx : CotangentSpace A :=
    (maximalIdeal A).toCotangent ⟨x, hx⟩
  have hphi_vx : phi vx = 0 := by
    change (maximalIdeal B).toCotangent
      ⟨(algebraMap A B) x, hle hx⟩ = 0
    have hqx : q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr <|
      Ideal.subset_span (Set.mem_singleton x)
    convert map_zero (maximalIdeal B).toCotangent
    ext
    simp only [halg, hqx, Submodule.coe_zero]
  have hkerphi : LinearMap.ker phi = Submodule.span (ResidueField A) {vx} := by
    apply le_antisymm
    · intro z hz
      have hz' : z ∈ LinearMap.ker mapcot := hz
      rw [Ideal.mapCotangent_ker_of_surjective hq heq] at hz'
      rcases hz' with ⟨w, hw, hwz⟩
      have hw' : (w : A) ∈ I := by
        have hw'' : (w : A) ∈ RingHom.ker (algebraMap A B) ⊓ maximalIdeal A :=
          Submodule.mem_comap.mp hw
        simpa only [hker] using (Ideal.mem_inf.mp hw'').1
      rw [Ideal.mem_span_singleton'] at hw'
      obtain ⟨a, ha⟩ := hw'
      have hvx : vx ∈ Submodule.span (ResidueField A) {vx} :=
        Submodule.subset_span (Set.mem_singleton vx)
      have havx := (Submodule.span (ResidueField A) {vx}).smul_mem
        (Ideal.Quotient.mk (maximalIdeal A) a) hvx
      rw [show z = (maximalIdeal A).toCotangent w from hwz.symm]
      convert havx using 1
      change (maximalIdeal A).toCotangent w =
        (maximalIdeal A).toCotangent ⟨a * x, (maximalIdeal A).mul_mem_left a hx⟩
      apply (maximalIdeal A).toCotangent.congr_arg
      ext
      exact ha.symm
    · rw [Submodule.span_le]
      intro z hz
      have hzv : z = vx := Set.mem_singleton_iff.mp hz
      rw [hzv]
      exact hphi_vx
  have hfinB : Module.finrank (ResidueField A) (CotangentSpace B) =
      Module.finrank (ResidueField B) (CotangentSpace B) := by
    unfold Module.finrank
    apply congrArg Cardinal.toNat
    exact rank_eq_of_equiv_equiv qbar (AddEquiv.refl (CotangentSpace B)) hqbar <| by
      intro c z
      rfl
  have hdim : Module.finrank (ResidueField A) (CotangentSpace B) +
      Module.finrank (ResidueField A) (LinearMap.ker phi) =
      Module.finrank (ResidueField A) (CotangentSpace A) := by
    have h := phi.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hphi_surj, finrank_top] at h
    exact h
  have hvxzero : vx = 0 ↔ x ∈ maximalIdeal A ^ 2 := by
    exact (maximalIdeal A).toCotangent_eq_zero ⟨x, hx⟩
  have hkerdim : Module.finrank (ResidueField A) (LinearMap.ker phi) =
      if x ∈ maximalIdeal A ^ 2 then 0 else 1 := by
    by_cases hx2 : x ∈ maximalIdeal A ^ 2
    · have hvx0 : vx = 0 := hvxzero.mpr hx2
      rw [hkerphi, hvx0, if_pos hx2]
      have hz : Submodule.span (ResidueField A) {(0 : CotangentSpace A)} = ⊥ := by
        simp
      rw [hz, finrank_bot]
    · have hvx0 : vx ≠ 0 := fun h => hx2 (hvxzero.mp h)
      rw [hkerphi, finrank_span_singleton hvx0]
      simp [hx2]
  have hdim' : Module.finrank (ResidueField B) (CotangentSpace B) +
      Module.finrank (ResidueField A) (LinearMap.ker phi) =
      Module.finrank (ResidueField A) (CotangentSpace A) := by
    rw [← hfinB]
    exact hdim
  have hAreg := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp
    (inferInstance : IsRegularLocalRing A)
  have hdrop := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hreg hx
  change ringKrullDim B + 1 = ringKrullDim A at hdrop
  have hBne : ringKrullDim B ≠ ⊥ := by
    intro hbot
    rw [hbot] at hdrop
    have hfalse : (⊥ : WithBot ℕ∞) =
        (Module.finrank (ResidueField A) (CotangentSpace A) : ℕ∞) :=
      hdrop.trans hAreg.symm
    simp at hfalse
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hBne
  have hdropENat : d + 1 =
      (Module.finrank (ResidueField A) (CotangentSpace A) : ℕ∞) := by
    apply WithBot.coe_injective
    calc
      (↑(d + 1) : WithBot ℕ∞) = (↑d : WithBot ℕ∞) + 1 := by simp
      _ = ringKrullDim B + 1 := congrArg (fun e : WithBot ℕ∞ => e + 1) hd
      _ = ringKrullDim A := hdrop
      _ = Module.finrank (ResidueField A) (CotangentSpace A) := hAreg.symm
  have hdtop : d ≠ ⊤ := by
    intro hdtop
    rw [hdtop] at hdropENat
    simp at hdropENat
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hdtop
  have hdropNat : e + 1 = Module.finrank (ResidueField A) (CotangentSpace A) := by
    exact_mod_cast he.symm ▸ hdropENat
  change IsRegularLocalRing B ↔ _
  constructor
  · intro hB hx2
    have hBreg := (IsRegularLocalRing.iff_finrank_cotangentSpace B).mp hB
    have hemb : Module.finrank (ResidueField B) (CotangentSpace B) =
        Module.finrank (ResidueField A) (CotangentSpace A) := by
      have hk : Module.finrank (ResidueField A) (LinearMap.ker phi) = 0 := by
        simpa [hx2] using hkerdim
      omega
    have hBdENat : (Module.finrank (ResidueField B) (CotangentSpace B) : ℕ∞) = d := by
      apply WithBot.coe_injective
      exact hBreg.trans hd.symm
    have hBd : Module.finrank (ResidueField B) (CotangentSpace B) = e := by
      exact_mod_cast hBdENat.trans he.symm
    omega
  · intro hx2
    apply (IsRegularLocalRing.iff_finrank_cotangentSpace B).mpr
    have hk : Module.finrank (ResidueField A) (LinearMap.ker phi) = 1 := by
      simpa [hx2] using hkerdim
    have hBd : Module.finrank (ResidueField B) (CotangentSpace B) = e := by
      omega
    calc
      (↑(Module.finrank (ResidueField B) (CotangentSpace B)) : WithBot ℕ∞) =
          (e : ℕ∞) := by exact_mod_cast hBd
      _ = d := congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) he
      _ = ringKrullDim B := hd

end IsRegularLocalRing
