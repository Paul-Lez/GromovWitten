/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.InjectiveLocalization
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Injective modules give flasque sheaves on Noetherian affine schemes

Localization of an injective module permits lifts that preserve a prescribed annihilator.
For a finite family of principal opens, this allows each new lift to be corrected without
changing its restrictions on earlier opens. Compactness of opens in a Noetherian spectrum
then gives surjectivity of every restriction map.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
noncomputable section
universe u
namespace AlgebraicGeometry.AffineFlasque

private def basicToTop {R : Type u} [CommRing R] (r : R) :
    PrimeSpectrum.basicOpen r ⟶ (⊤ : Opens (PrimeSpectrum R)) := homOfLE le_top
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (F : (TopologicalSpace.Opens (PrimeSpectrum R))ᵒᵖ ⥤ ModuleCat.{u} R)
  (hF : ∀ r : R, IsLocalizedModule (.powers r)
    (F.map ((basicToTop r).op)).hom)
  [Module.Injective R (F.obj (op ⊤))]

include hF in
/-- A section vanishing after one further principal localization is killed by a power. -/
lemma pow_smul_eq_zero_of_restrict_basicOpen_eq_zero
    (r s : R) (x : F.obj (op (PrimeSpectrum.basicOpen s)))
    (hx : F.map (homOfLE (PrimeSpectrum.basicOpen_mul_le_right r s)).op x = 0) :
    ∃ n : ℕ, r ^ n • x = 0 := by
  have := hF s
  obtain ⟨m, hm⟩ := Module.Injective.localization_away_surjective s
    (F.map (basicToTop s).op).hom x
  have he : F.map (basicToTop (r * s)).op m = 0 := by
    calc
      _ = F.map (homOfLE (PrimeSpectrum.basicOpen_mul_le_right r s)).op
          (F.map (basicToTop s).op m) := by
        rw [← ConcreteCategory.comp_apply, ← F.map_comp]
        rfl
      _ = 0 := by rw [hm, hx]
  have := hF (r * s)
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (r * s)
    (f := (F.map (basicToTop (r * s)).op).hom)
    (show (F.map (basicToTop (r * s)).op).hom m =
      (F.map (basicToTop (r * s)).op).hom 0 by simpa using he)
  have hn' := congrArg (F.map (basicToTop s).op) hn
  have hu := (IsLocalizedModule.Away.isUnit_algebraMap
    (F.map (basicToTop s).op).hom s).pow n
  refine ⟨n, (Module.End.isUnit_iff _).mp hu |>.1 ?_⟩
  simp only [← map_pow, Module.algebraMap_end_apply]
  have hn'' : (r * s) ^ n • x = 0 := by
    simpa only [map_smul, map_zero, smul_zero, hm] using hn'
  rw [mul_pow, mul_smul] at hn''
  exact (smul_comm (s ^ n) (r ^ n) x).trans (hn''.trans (smul_zero _).symm)


include hF in
/-- Compatible sections on finitely many principal opens extend to a global section. -/
lemma exists_global_section_of_finite_basic_family (s : Finset R)
    (a : ∀ r : s, F.obj (op (PrimeSpectrum.basicOpen r.1)))
    (ha : ∀ r t : s,
      F.map (homOfLE (PrimeSpectrum.basicOpen_mul_le_left r.1 t.1)).op (a r) =
        F.map (homOfLE (PrimeSpectrum.basicOpen_mul_le_right r.1 t.1)).op (a t)) :
    ∃ m : F.obj (op ⊤), ∀ r : s,
      F.map (basicToTop r.1).op m = a r := by
  classical
  revert a
  induction s using Finset.induction_on with
  | empty =>
      intro a ha
      refine ⟨0, fun r => ?_⟩
      exact Finset.notMem_empty r.1 r.2 |>.elim
  | @insert t s ht ih =>
      intro a ha
      let a₀ (r : s) := a ⟨r.1, Finset.mem_insert_of_mem r.2⟩
      obtain ⟨m₀, hm₀⟩ := ih a₀ (fun r v => ha ⟨r.1, Finset.mem_insert_of_mem r.2⟩
        ⟨v.1, Finset.mem_insert_of_mem v.2⟩)
      let t' : (insert t s : Finset R) := ⟨t, Finset.mem_insert_self t s⟩
      let x := a t' - F.map (basicToTop t).op m₀
      have hx (r : s) : F.map
          (homOfLE (PrimeSpectrum.basicOpen_mul_le_right r.1 t)).op x = 0 := by
        rw [map_sub, sub_eq_zero]
        rw [← ha ⟨r.1, Finset.mem_insert_of_mem r.2⟩ t']
        change F.map (homOfLE (PrimeSpectrum.basicOpen_mul_le_left r.1 t)).op (a₀ r) = _
        rw [← hm₀ r]
        simp only [← ConcreteCategory.comp_apply, ← F.map_comp]
        rfl
      choose n hn using fun r : s =>
        pow_smul_eq_zero_of_restrict_basicOpen_eq_zero F hF r.1 t x (hx r)
      let I : Ideal R := Ideal.span (Set.range fun r : s => r.1 ^ n r)
      have hI : ∀ c ∈ I, c • x = 0 := by
        have hle : I ≤ ((LinearMap.id : R →ₗ[R] R).smulRight x).ker := by
          apply Ideal.span_le.mpr
          rintro c ⟨r, rfl⟩
          exact hn r
        exact hle
      have := hF t
      obtain ⟨m₁, hm₁, hmann⟩ := Module.Injective.exists_lift_annihilated t
        (F.map (basicToTop t).op).hom I x hI
      have hzero (r : s) : F.map (basicToTop r.1).op m₁ = 0 := by
        have := hF r.1
        have hkill := hmann (r.1 ^ n r) (Ideal.subset_span (Set.mem_range_self r))
        have hu := (IsLocalizedModule.Away.isUnit_algebraMap
          (F.map (basicToTop r.1).op).hom r.1).pow (n r)
        apply (Module.End.isUnit_iff _).mp hu |>.1
        simp only [← map_pow, Module.algebraMap_end_apply]
        rw [← map_smul, hkill, map_zero]
        simp
      refine ⟨m₀ + m₁, fun r => ?_⟩
      rcases Finset.mem_insert.mp r.2 with hr | hr
      · have he : r = t' := Subtype.ext hr
        subst r
        rw [map_add, hm₁]
        exact add_sub_cancel _ _
      · rw [map_add, hzero ⟨r.1, hr⟩, add_zero]
        exact hm₀ ⟨r.1, hr⟩


/-- A localizing sheaf with injective global sections has surjective global restrictions. -/
lemma global_restriction_surjective
    (G : TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of (PrimeSpectrum R)))
    (hG : ∀ r : R, IsLocalizedModule (.powers r)
      (G.obj.map (basicToTop r).op).hom)
    [Module.Injective R (G.obj.obj (op ⊤))] (U : Opens (PrimeSpectrum R)) :
    Function.Surjective (G.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  classical
  intro x
  obtain ⟨κ, hκ, a, ha⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact
    U (NoetherianSpace.isCompact (U : Set (PrimeSpectrum R)))
  let := Fintype.ofFinite κ
  let s : Finset R := Finset.univ.image a
  have hle (r : s) : PrimeSpectrum.basicOpen r.1 ≤ U := by
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp r.2
    rw [← hk, ha]
    exact le_iSup (fun k : κ => PrimeSpectrum.basicOpen (a k)) k
  have hcover : U ≤ ⨆ r : s, PrimeSpectrum.basicOpen r.1 := by
    rw [ha]
    refine iSup_le fun k => ?_
    exact le_iSup_of_le ⟨a k, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩ le_rfl
  let b (r : s) := G.obj.map (homOfLE (hle r)).op x
  have hb (r t : s) :
      G.obj.map (homOfLE (PrimeSpectrum.basicOpen_mul_le_left r.1 t.1)).op (b r) =
        G.obj.map (homOfLE (PrimeSpectrum.basicOpen_mul_le_right r.1 t.1)).op (b t) := by
    simp only [b, ← ConcreteCategory.comp_apply, ← G.obj.map_comp]
    rfl
  obtain ⟨m, hm⟩ := exists_global_section_of_finite_basic_family G.obj hG s b hb
  refine ⟨m, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' G (fun r : s => PrimeSpectrum.basicOpen r.1) U
    (fun r => homOfLE (hle r)) hcover
  intro r
  rw [← ConcreteCategory.comp_apply, ← G.obj.map_comp]
  exact hm r


/-- A localizing sheaf with injective global sections is flasque. -/
lemma isFlasque_of_injective_globalSections
    (G : TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of (PrimeSpectrum R)))
    (hG : ∀ r : R, IsLocalizedModule (.powers r)
      (G.obj.map (basicToTop r).op).hom)
    [Module.Injective R (G.obj.obj (op ⊤))] : TopCat.Sheaf.IsFlasque G where
  epi {U V} i := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    obtain ⟨m, hm⟩ := global_restriction_surjective G hG V.unop x
    refine ⟨G.obj.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op m, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← G.obj.map_comp]
    exact hm

/-- The sheaf associated to an injective module on a Noetherian affine scheme is flasque. -/
lemma isFlasque_tilde_of_injective (A : CommRingCat.{u}) [IsNoetherianRing A]
    (M : ModuleCat.{u} A) [Module.Injective A M] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (Spec A).ringCatSheaf).obj (tilde M)) := by
  let G := modulesSpecToSheaf.obj (tilde M)
  let hinj : Module.Injective A (G.obj.obj (op ⊤)) :=
    Module.Baer.iff_injective.mp
      (Module.Baer.of_equiv (tilde.isoTop M).toLinearEquiv
        (Module.Baer.of_injective inferInstance))
  let hG : TopCat.Sheaf.IsFlasque G := @isFlasque_of_injective_globalSections A _ _ G
    (isLocalizing_tilde M) hinj
  constructor
  intro U V i
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  exact (ModuleCat.epi_iff_surjective (G.obj.map i)).mp inferInstance
end AlgebraicGeometry.AffineFlasque
