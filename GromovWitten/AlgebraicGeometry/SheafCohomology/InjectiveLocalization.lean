/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.RingTheory.LocalProperties.Injective
import Mathlib.RingTheory.Noetherian.Filter

/-!
# Lifting maps to localizations of injective modules

Over a Noetherian ring, maps from finite modules to a principal localization of
an injective module lift before localization. The proof combines finite
presentation with stabilization of kernels of scalar multiplication.
-/

noncomputable section
universe u
variable {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Maps into an injective module factor whenever the kernel obstruction vanishes. -/
lemma Module.Injective.exists_factor_of_ker_le [Module.Injective R M]
    {P Q : Type u} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (a : P →ₗ[R] Q) (b : P →ₗ[R] M) (h : a.ker ≤ b.ker) :
    ∃ c : Q →ₗ[R] M, c.comp a = b := by
  let d := (a.ker.liftQ b h).comp a.quotKerEquivRange.symm.toLinearMap
  obtain ⟨c, hc⟩ := Module.Injective.extension_property R M a.range Q
    a.range.subtype Subtype.val_injective d
  refine ⟨c, ?_⟩
  ext x
  have he := LinearMap.congr_fun hc (a.rangeRestrict x)
  change c (a x) = (a.ker.liftQ b h)
    (a.quotKerEquivRange.symm ⟨a x, ⟨x, rfl⟩⟩) at he
  exact he.trans (congrArg (a.ker.liftQ b h)
    (a.quotKerEquivRange_symm_apply_image x _))

/-- Maps from a Noetherian finitely presented module lift across principal localization. -/
lemma Module.Injective.exists_lift_localization_away [Module.Injective R M]
    {P : Type u} [AddCommGroup P] [Module R P] [IsNoetherian R P]
    [Module.FinitePresentation R P] (r : R) (f : M →ₗ[R] N)
    [IsLocalizedModule (.powers r) f] (φ : P →ₗ[R] N) :
    ∃ ψ : P →ₗ[R] M, f.comp ψ = φ := by
  let a : P →ₗ[R] P := r • LinearMap.id
  obtain ⟨k, hk⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R P) a.iterateKer
  obtain ⟨g, ⟨_, n, rfl⟩, hg⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule (.powers r) f φ
  change f.comp g = r ^ n • φ at hg
  let b := g.comp (a ^ k)
  have hker : (a ^ (k + n)).ker ≤ b.ker := by
    intro t ht
    have hk' : (a ^ k).ker = (a ^ (k + n)).ker := hk (k + n) (Nat.le_add_right k n)
    have ht' : (a ^ k) t = 0 := by
      change t ∈ (a ^ k).ker
      rw [hk']
      exact ht
    change g ((a ^ k) t) = 0
    rw [ht', map_zero]
  obtain ⟨c, hc⟩ := Module.Injective.exists_factor_of_ker_le (a ^ (k + n)) b hker
  refine ⟨c, ?_⟩
  ext p
  have hp (j : ℕ) (t : P) : (a ^ j) t = r ^ j • t := by
    induction j generalizing t with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Module.End.mul_apply, ih]
      simp [a, pow_succ, mul_smul]
  have he : r ^ (k + n) • c p = r ^ k • g p := by
    simpa only [LinearMap.comp_apply, b, hp, map_smul] using LinearMap.congr_fun hc p
  have he' := congrArg f he
  have hg' : f (g p) = r ^ n • φ p := LinearMap.congr_fun hg p
  have hu := IsLocalizedModule.map_units f (⟨r ^ (k + n), ⟨k + n, rfl⟩⟩ : Submonoid.powers r)
  apply (Module.End.isUnit_iff _).mp hu |>.1
  change r ^ (k + n) • f (c p) = r ^ (k + n) • φ p
  simpa only [map_smul, hg', pow_add, mul_smul] using he'

/-- Principal localization of an injective module over a Noetherian ring is surjective. -/
lemma Module.Injective.localization_away_surjective [IsNoetherianRing R]
    [Module.Injective R M] (r : R) (f : M →ₗ[R] N)
    [IsLocalizedModule (.powers r) f] : Function.Surjective f := by
  intro x
  obtain ⟨g, hg⟩ := Module.Injective.exists_lift_localization_away r f
    ((LinearMap.id : R →ₗ[R] R).smulRight x)
  exact ⟨g 1, by simpa using LinearMap.congr_fun hg 1⟩

/-- A localized element annihilated by an ideal lifts to an element annihilated by that ideal. -/
lemma Module.Injective.exists_lift_annihilated [IsNoetherianRing R] [Module.Injective R M]
    (r : R) (f : M →ₗ[R] N) [IsLocalizedModule (.powers r) f]
    (I : Ideal R) (x : N) (hx : ∀ a ∈ I, a • x = 0) :
    ∃ m : M, f m = x ∧ ∀ a ∈ I, a • m = 0 := by
  let l : R →ₗ[R] N := (LinearMap.id : R →ₗ[R] R).smulRight x
  have hI : I ≤ l.ker := fun a ha => hx a ha
  let φ := I.liftQ l hI
  have : Module.FinitePresentation R (R ⧸ I) := Module.finitePresentation_of_finite R (R ⧸ I)
  obtain ⟨ψ, hψ⟩ := Module.Injective.exists_lift_localization_away r f φ
  refine ⟨ψ (I.mkQ 1), ?_, ?_⟩
  · calc
      f (ψ (I.mkQ 1)) = l 1 := LinearMap.congr_fun hψ (I.mkQ 1)
      _ = x := by simp [l]
  · intro a ha
    rw [← ψ.map_smul, ← I.mkQ.map_smul]
    have he : I.mkQ (a • (1 : R)) = 0 := by
      simpa only [smul_eq_mul, mul_one] using
        (show I.mkQ a = 0 from (Submodule.Quotient.mk_eq_zero I).mpr ha)
    rw [he, map_zero]
