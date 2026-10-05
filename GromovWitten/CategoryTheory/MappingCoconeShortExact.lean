/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.MappingCoconeFunctor
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Mapping cocones of short exact sequences

The canonical lift from the first term of a short exact sequence of complexes of
modules to the mapping cocone of the second map is a quasi-isomorphism. This
identifies the Mayer–Vietoris augmentation with a derived comparison.
-/

open CategoryTheory Limits HomologicalComplex CochainComplex.HomComplex

universe u v

namespace CochainComplex

variable {R : Type u} [Ring R]

private abbrev CC := CochainComplex (ModuleCat R) ℤ

private noncomputable def q (S : ShortComplex (CC (R := R))) :
    CochainComplex.mappingCocone S.g ⟶ CochainComplex.mappingCocone (𝟙 S.X₃) :=
  (CategoryTheory.shiftFunctor _ (-1)).map
    (CochainComplex.mappingCone.map S.g (𝟙 S.X₃) S.g (𝟙 S.X₃) (by simp))

private noncomputable def i (S : ShortComplex (CC (R := R))) :
    S.X₁ ⟶ CochainComplex.mappingCocone S.g :=
  CochainComplex.mappingCocone.lift S.g S.f 0 (by simp)

private lemma i_factors_inl (S : ShortComplex (CC (R := R))) (n : ℤ) :
    (i S).f n = S.f.f n ≫ (mappingCocone.inl S.g).v n n (add_zero n) :=
  mappingCocone_lift_zero_factors_inl S.g S.f (by simp) n

private lemma cocone_decompose {A B : CC (R := R)} (φ : A ⟶ B) (n : ℤ)
    (x : (CochainComplex.mappingCocone φ).X n) :
    x = (CochainComplex.mappingCocone.inl φ).v n n (add_zero n)
          ((CochainComplex.mappingCocone.fst φ).f n x) +
        (CochainComplex.mappingCocone.inr φ).1.v (n - 1) n (by omega)
          ((CochainComplex.mappingCocone.snd φ).v n (n - 1) (by omega) x) := by
  have h := congrArg
    (fun k : (CochainComplex.mappingCocone φ).X n ⟶
        (CochainComplex.mappingCocone φ).X n => k x)
    (CochainComplex.mappingCocone.id_X φ n (n - 1) (by omega))
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
  exact h.symm

private lemma cocone_fst_inl {A B : CC (R := R)} (φ : A ⟶ B) (n : ℤ) (x : A.X n) :
    (CochainComplex.mappingCocone.fst φ).f n
        ((CochainComplex.mappingCocone.inl φ).v n n (add_zero n) x) = x := by
  have h := congrArg (fun f => f x) (CochainComplex.mappingCocone.inl_v_fst_f φ n)
  simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using h

private lemma cocone_fst_inr {A B : CC (R := R)} (φ : A ⟶ B) (n : ℤ)
    (x : B.X (n - 1)) :
    (CochainComplex.mappingCocone.fst φ).f n
        ((CochainComplex.mappingCocone.inr φ).1.v (n - 1) n (by omega) x) = 0 := by
  have h := congrArg (fun f => f x)
    (CochainComplex.mappingCocone.inr_v_fst_f φ (n - 1) n (by omega))
  simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h

private lemma cocone_snd_inl {A B : CC (R := R)} (φ : A ⟶ B) (n : ℤ) (x : A.X n) :
    (CochainComplex.mappingCocone.snd φ).v n (n - 1) (by omega)
        ((CochainComplex.mappingCocone.inl φ).v n n (add_zero n) x) = 0 := by
  have h := congrArg (fun f => f x)
    (CochainComplex.mappingCocone.inl_v_snd_v φ n (n - 1) (by omega))
  simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h

private lemma cocone_snd_inr {A B : CC (R := R)} (φ : A ⟶ B) (n : ℤ)
    (x : B.X (n - 1)) :
    (CochainComplex.mappingCocone.snd φ).v n (n - 1) (by omega)
        ((CochainComplex.mappingCocone.inr φ).1.v (n - 1) n (by omega) x) = x := by
  have h := congrArg (fun f => f x)
    (CochainComplex.mappingCocone.inr_v_snd_v φ (n - 1) n (by omega))
  simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using h

set_option backward.isDefEq.respectTransparency false in
private lemma canonical_shortExact_of_cocone_map_components
    (S : ShortComplex (CC (R := R))) (hS : S.ShortExact)
    (hqInl : ∀ n : ℤ,
      (CochainComplex.mappingCocone.inl S.g).v n n (add_zero n) ≫ (q S).f n =
        S.g.f n ≫ (CochainComplex.mappingCocone.inl (𝟙 S.X₃)).v n n (add_zero n))
    (hqInr : ∀ n : ℤ,
      (CochainComplex.mappingCocone.inr S.g).1.v (n - 1) n (by omega) ≫ (q S).f n =
        (CochainComplex.mappingCocone.inr (𝟙 S.X₃)).1.v (n - 1) n (by omega)) :
    (ShortComplex.mk (i S) (q S) (by
      apply HomologicalComplex.hom_ext
      intro n
      simp only [HomologicalComplex.comp_f]
      rw [i_factors_inl, Category.assoc, hqInl]
      rw [← Category.assoc, ← HomologicalComplex.comp_f, S.zero]
      simp)).ShortExact := by
  let T : ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
    ShortComplex.mk (i S) (q S) (by
      apply HomologicalComplex.hom_ext
      intro n
      simp only [HomologicalComplex.comp_f]
      rw [i_factors_inl, Category.assoc, hqInl]
      rw [← Category.assoc, ← HomologicalComplex.comp_f, S.zero]
      simp)
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let Tn := T.map (eval (ModuleCat R) (ComplexShape.up ℤ) n)
  let Sn := S.map (eval (ModuleCat R) (ComplexShape.up ℤ) n)
  have hSn : Sn.ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  have hSf : Function.Injective (S.f.f n) := by
    change Function.Injective Sn.f
    exact (ModuleCat.mono_iff_injective _).mp hSn.mono_f
  have hSg : Function.Surjective (S.g.f n) := by
    change Function.Surjective Sn.g
    exact (ModuleCat.epi_iff_surjective _).mp hSn.epi_g
  have hSex : Function.Exact (S.f.f n) (S.g.f n) := by
    change Function.Exact Sn.f Sn.g
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Sn).mp hSn.exact
  have hqInl_apply (b : S.X₂.X n) :
      (q S).f n ((CochainComplex.mappingCocone.inl S.g).v n n (add_zero n) b) =
        (CochainComplex.mappingCocone.inl (𝟙 S.X₃)).v n n (add_zero n) (S.g.f n b) := by
    have h := congrArg (fun f => f b) (hqInl n)
    simpa only [ModuleCat.comp_apply] using h
  have hqInr_apply (c : S.X₃.X (n - 1)) :
      (q S).f n ((CochainComplex.mappingCocone.inr S.g).1.v (n - 1) n (by omega) c) =
        (CochainComplex.mappingCocone.inr (𝟙 S.X₃)).1.v (n - 1) n (by omega) c := by
    have h := congrArg (fun f => f c) (hqInr n)
    simpa only [ModuleCat.comp_apply] using h
  have hTf : Function.Injective ((i S).f n) := by
    intro a b hab
    apply hSf
    calc
      S.f.f n a = ((i S).f n ≫ (CochainComplex.mappingCocone.fst S.g).f n) a := by
        simp [i]
      _ = (CochainComplex.mappingCocone.fst S.g).f n ((i S).f n a) := by simp
      _ = (CochainComplex.mappingCocone.fst S.g).f n ((i S).f n b) := by rw [hab]
      _ = ((i S).f n ≫ (CochainComplex.mappingCocone.fst S.g).f n) b := by simp
      _ = S.f.f n b := by simp [i]
  have hTg : Function.Surjective ((q S).f n) := by
    intro y
    obtain ⟨b, hb⟩ := hSg ((CochainComplex.mappingCocone.fst (𝟙 S.X₃)).f n y)
    refine ⟨(CochainComplex.mappingCocone.inl S.g).v n n (add_zero n) b +
      (CochainComplex.mappingCocone.inr S.g).1.v (n - 1) n (by omega)
        ((CochainComplex.mappingCocone.snd (𝟙 S.X₃)).v n (n - 1) (by omega) y), ?_⟩
    have hy := cocone_decompose (𝟙 S.X₃) n y
    rw [map_add, hqInl_apply, hqInr_apply, hb]
    exact hy.symm
  have hTex : Function.Exact ((i S).f n) ((q S).f n) := by
    intro x
    constructor
    · intro hx
      have hxdec := cocone_decompose S.g n x
      have hfirst := congrArg ((CochainComplex.mappingCocone.fst (𝟙 S.X₃)).f n) hx
      have hsecond := congrArg
        ((CochainComplex.mappingCocone.snd (𝟙 S.X₃)).v n (n - 1) (by omega)) hx
      rw [hxdec] at hfirst hsecond
      rw [map_add, hqInl_apply, hqInr_apply] at hfirst hsecond
      simp only [cocone_fst_inl, cocone_fst_inr, cocone_snd_inl, cocone_snd_inr,
        map_add, zero_add] at hfirst hsecond
      have hgf : S.g.f n ((CochainComplex.mappingCocone.fst S.g).f n x) = 0 := by
        simpa using hfirst
      have hsnd : (CochainComplex.mappingCocone.snd S.g).v n (n - 1) (by omega) x = 0 := by
        simpa using hsecond
      have hmem : (CochainComplex.mappingCocone.fst S.g).f n x ∈
          Set.range (S.f.f n) := (hSex _).mp hgf
      rcases hmem with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [i_factors_inl]
      rw [hxdec]
      simp [ha, hsnd]
    · rintro ⟨a, rfl⟩
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, T.zero]
      simp
  change Tn.ShortExact
  exact ModuleCat.shortComplex_shortExact Tn hTex hTf hTg

set_option backward.isDefEq.respectTransparency false in
private lemma mappingCocone_identity_acyclic
    {B : Type u} [Category.{v} B] [Abelian B]
    (K : CochainComplex B ℤ) :
    (CochainComplex.mappingCocone (𝟙 K)).Acyclic := by
  intro n
  rw [exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have h := ((CochainComplex.mappingCone.homotopyToZeroOfId K).shift (-1)).homologyMap_eq n
  have hi := (CategoryTheory.shiftFunctor (CochainComplex B ℤ) (-1 : ℤ)).map_id
    (CochainComplex.mappingCone (𝟙 K))
  rw [hi, homologyMap_id] at h
  dsimp only [CochainComplex.mappingCocone]
  simpa only [Functor.map_zero, homologyMap_zero] using h

private lemma shortExact_quasiIso_f_of_acyclic_right
    {B : Type u} [Category.{v} B] [Abelian B]
    (T : ShortComplex (CochainComplex B ℤ)) (hT : T.ShortExact)
    (hZ : T.X₃.Acyclic) : QuasiIso T.f := by
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hz₀ : IsZero (T.X₃.homology (n - 1)) :=
    (exactAt_iff_isZero_homology _ _).mp (hZ (n - 1))
  have hz₁ : IsZero (T.X₃.homology n) :=
    (exactAt_iff_isZero_homology _ _).mp (hZ n)
  have _ : Mono (homologyMap T.f n) :=
    (hT.homology_exact₁ (n - 1) n (by simp)).mono_g (hz₀.eq_of_src _ _)
  have _ : Epi (homologyMap T.f n) :=
    (hT.homology_exact₂ n).epi_f (hz₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

set_option backward.isDefEq.respectTransparency false in
private lemma canonical_comp_zero (S : ShortComplex (CC (R := R))) : i S ≫ q S = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f]
  rw [i_factors_inl, Category.assoc]
  have hq := mappingCocone_inl_map S.g (𝟙 S.X₃) S.g (𝟙 S.X₃) (by simp) n
  have hq' :
      (CochainComplex.mappingCocone.inl S.g).v n n (add_zero n) ≫ (q S).f n =
        S.g.f n ≫ (CochainComplex.mappingCocone.inl (𝟙 S.X₃)).v n n (add_zero n) := by
    simpa only [q, mappingCoconeMap] using hq
  rw [hq', ← Category.assoc, ← HomologicalComplex.comp_f, S.zero]
  simp

private lemma canonical_shortExact (S : ShortComplex (CC (R := R))) (hS : S.ShortExact) :
    (ShortComplex.mk (i S) (q S) (canonical_comp_zero S)).ShortExact := by
  apply canonical_shortExact_of_cocone_map_components S hS
  · intro n
    exact mappingCocone_inl_map S.g (𝟙 S.X₃) S.g (𝟙 S.X₃) (by simp) n
  · intro n
    exact mappingCocone_inr_map S.g (𝟙 S.X₃) S.g (𝟙 S.X₃) (by simp)
      (n - 1) n (by omega)

/-- In a short exact sequence of complexes of modules, the first complex maps by a
quasi-isomorphism to the mapping cocone of the second map. -/
theorem mappingCocone_lift_quasiIso_of_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat R) ℤ)) (hS : S.ShortExact) :
    QuasiIso (mappingCocone.lift S.g S.f 0 (by simp)) := by
  let T : ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
    ShortComplex.mk (i S) (q S) (canonical_comp_zero S)
  have hT : T.ShortExact := by
    change (ShortComplex.mk (i S) (q S) (canonical_comp_zero S)).ShortExact
    exact canonical_shortExact S hS
  have hZ : T.X₃.Acyclic := by
    change (CochainComplex.mappingCocone (𝟙 S.X₃)).Acyclic
    exact mappingCocone_identity_acyclic S.X₃
  simpa only [T, i] using shortExact_quasiIso_f_of_acyclic_right T hT hZ


end CochainComplex
