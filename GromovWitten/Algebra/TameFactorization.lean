/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.Algebra.OrderBirational
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyInjective
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Factorizations and admissible overrings (Stacks 42.4)

This file provides the preparation for tame symbols (Stacks Project, Section 42.4), adapted to
the situation where all rings are subrings of one fixed field. Throughout, `K` is a field with a
`D`-algebra structure, and every ring in the construction is a `Subalgebra D K`; for the main
results `D` is a domain with fraction field `K`.

* A family `f : ι → Kˣ` *factors* in a subalgebra `S` (`Factors S f`) if `f i = u i * π ^ e i`
  in `K` for a nonzero `π ∈ S`, integers `e i` and units `u i` of `S`.
* `localizationAt C P` is the localization of `C` at a prime `P`, taken inside `K`; it carries
  an `IsLocalization.AtPrime` instance for the inclusion `C → localizationAt C P`.
* `IsOverring E C` means `E ≤ C` and `C` is a finitely generated `E`-module.
* `Admissible E C f` means that `C` is an overring of `E` and `f` factors in the localization of
  `C` at every maximal ideal of `C`.

## Main results

* `GromovWitten.Algebra.Tame.exists_integral_blowup` (B1, replacing Stacks 42.4.2): in a
  Noetherian local domain `R` of dimension `≤ 1` with unit differences, for nonzero `a, b` in the
  maximal ideal there is `μ` with `a + μ * b ≠ 0` and `b / (a + μ * b)` integral over `R`.
* `GromovWitten.Algebra.Tame.exists_admissible_of_forall_localizationAt` (B2, replacing
  Stacks 42.4.1): admissible overrings of the local rings of an overring `R` of `E` glue (by
  intersection inside `K`) to an admissible overring of `E`. Its ingredients are
  `isOverring_iInf` (B2 (a)–(b)), `le_localizationAt_iInf` (B2 (c)) and
  `Admissible.factors_of_le` (B2 (d)).
* API for later use: `Factors.mono`, `Factors.of_eq_mul_prod`, `isLocalization_localizationAt`,
  `localizationAtEquiv`, `localizationAt_le_localizationAt`, the consequences
  `IsOverring.isNoetherianRing`, `IsOverring.krullDimLE`, `IsOverring.isIntegral`,
  `IsOverring.comap_eq_maximalIdeal`, `IsOverring.finite_maximalSpectrum`, `IsOverring.trans`,
  `IsOverring.sup`, and `Admissible.of_isOverring_right`.
* `GromovWitten.Algebra.Tame.ord_localizationAt_le`: orders do not increase when passing to the
  local rings of an overring (from Fulton's Example A.3.1).
* `GromovWitten.Algebra.Tame.exists_admissible_pair` (B3) and
  `GromovWitten.Algebra.Tame.exists_admissible` (B4, Stacks 42.4.4): for a Noetherian local
  subalgebra `E` of `K` of dimension `≤ 1` with unit differences, every finite family of units
  of `K` has an admissible overring over `E`.

## Implementation notes

The blow-up of Stacks 42.4.2 is replaced by an explicit elementary argument: a length count
produces a homogeneous relation `∑ g j * a ^ j * b ^ (d - j) = 0` with a unit coefficient, and
unit differences provide `μ` for which `b / (a + μ * b)` is a root of a monic polynomial. The
formal gluing of Stacks 42.4.1 is replaced by an intersection of subrings of `K`. The induction of
B3 is on `ord_E a + ord_E b`.
-/

namespace GromovWitten.Algebra.Tame

open IsLocalRing Polynomial

section Factors

variable {D K : Type*} [CommRing D] [Field K] [Algebra D K]

/-- A family `f : ι → Kˣ` *factors* in a subalgebra `S` of `K` if there is a nonzero `π ∈ S`,
integers `e i` and units `u i` of `S` with `f i = u i * π ^ e i` in `K` for all `i`. -/
def Factors {ι : Type*} (S : Subalgebra D K) (f : ι → Kˣ) : Prop :=
  ∃ (π : S) (e : ι → ℤ) (u : ι → Sˣ), (π : K) ≠ 0 ∧
    ∀ i, (f i : K) = ((u i : S) : K) * (π : K) ^ e i

/-- The units of a subalgebra `S` of `K`, viewed as units of `K`. -/
abbrev unitsToK (S : Subalgebra D K) : Sˣ →* Kˣ := Units.map (S.val : S →* K)

variable {ι κ : Type*} {S T : Subalgebra D K} {f : ι → Kˣ}

/-- The unit `unitsToK S u` of `K` has underlying element `u`. -/
@[simp]
theorem coe_unitsToK (u : Sˣ) : ((unitsToK S u : Kˣ) : K) = ((u : S) : K) := rfl

/-- Reformulation of `Factors` inside the group `Kˣ`. -/
theorem factors_iff_units : Factors S f ↔ ∃ (π : S) (hπ : (π : K) ≠ 0) (e : ι → ℤ) (u : ι → Sˣ),
    ∀ i, f i = unitsToK S (u i) * Units.mk0 (π : K) hπ ^ e i := by
  constructor
  · rintro ⟨π, e, u, hπ, h⟩
    exact ⟨π, hπ, e, u, fun i ↦ Units.ext (by simp [h i])⟩
  · rintro ⟨π, hπ, e, u, h⟩
    exact ⟨π, e, u, hπ, fun i ↦ by simp [h i]⟩

/-- Factorizations pass to larger subalgebras. -/
theorem Factors.mono (h : S ≤ T) (hf : Factors S f) : Factors T f := by
  obtain ⟨π, e, u, hπ, hu⟩ := hf
  exact ⟨Subalgebra.inclusion h π, e,
    fun i ↦ Units.map (Subalgebra.inclusion h : S →* T) (u i), hπ, fun i ↦ hu i⟩

/-- Factorizations can be reindexed. -/
theorem Factors.comp (hf : Factors S f) (σ : κ → ι) : Factors S (f ∘ σ) := by
  obtain ⟨π, e, u, hπ, hu⟩ := hf
  exact ⟨π, e ∘ σ, u ∘ σ, hπ, fun k ↦ hu (σ k)⟩

private theorem zpow_finset_sum {G : Type*} [CommGroup G] (a : G) (s : Finset κ) (n : κ → ℤ) :
    a ^ (∑ k ∈ s, n k) = ∏ k ∈ s, a ^ n k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, zpow_add, ih]

/-- **Closure of factorizations.** If `g` factors in `S`, then so does every family whose members
are units of `S` times products of integral powers of the members of `g`. -/
theorem Factors.of_eq_mul_prod [Fintype κ] {g : κ → Kˣ} (hg : Factors S g) (f : ι → Kˣ)
    (w : ι → Sˣ) (n : ι → κ → ℤ) (hf : ∀ i, f i = unitsToK S (w i) * ∏ k, g k ^ n i k) :
    Factors S f := by
  obtain ⟨π, hπ, e, u, hu⟩ := factors_iff_units.1 hg
  refine factors_iff_units.2 ⟨π, hπ, fun i ↦ ∑ k, e k * n i k,
    fun i ↦ w i * ∏ k, u k ^ n i k, fun i ↦ ?_⟩
  rw [hf i, map_mul, map_prod, mul_assoc, zpow_finset_sum, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [hu k, mul_zpow, map_zpow, zpow_mul]

/-- Every family factors in the top subalgebra `K`. -/
theorem factors_top (f : ι → Kˣ) : Factors (⊤ : Subalgebra D K) f := by
  refine ⟨1, fun _ ↦ 0, fun i ↦ Units.map (Subalgebra.topEquiv (R := D) (A := K)).symm (f i),
    by simp, fun i ↦ ?_⟩
  simp

/-- A family indexed by an empty type factors everywhere. -/
theorem factors_of_isEmpty [IsEmpty ι] (S : Subalgebra D K) (f : ι → Kˣ) : Factors S f :=
  ⟨1, isEmptyElim, isEmptyElim, by simp, isEmptyElim⟩

end Factors

section Localization

variable {D K : Type*} [CommRing D] [Field K] [Algebra D K]

/-- The localization of a subalgebra `C` of `K` at a prime ideal `P` of `C`, taken inside `K`:
the elements `x : K` with `s * x ∈ C` for some `s ∈ C \ P`. -/
def localizationAt (C : Subalgebra D K) (P : Ideal C) [P.IsPrime] : Subalgebra D K where
  carrier := {x | ∃ s : C, s ∉ P ∧ (s : K) * x ∈ C}
  mul_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨s', hs', hy⟩
    refine ⟨s * s', fun h ↦ (‹P.IsPrime›.mem_or_mem h).elim hs hs', ?_⟩
    convert C.mul_mem hx hy using 1
    push_cast; ring
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨s', hs', hy⟩
    refine ⟨s * s', fun h ↦ (‹P.IsPrime›.mem_or_mem h).elim hs hs', ?_⟩
    convert C.add_mem (C.mul_mem s'.2 hx) (C.mul_mem s.2 hy) using 1
    push_cast; ring
  algebraMap_mem' r := ⟨1, (Ideal.ne_top_iff_one P).1 ‹P.IsPrime›.ne_top,
    by simp⟩

variable (C : Subalgebra D K) (P : Ideal C) [P.IsPrime]

/-- Membership in `localizationAt C P`, by definition. -/
theorem mem_localizationAt {x : K} :
    x ∈ localizationAt C P ↔ ∃ s : C, s ∉ P ∧ (s : K) * x ∈ C := Iff.rfl

/-- `C` is contained in its localization at `P`. -/
theorem le_localizationAt : C ≤ localizationAt C P :=
  fun x hx ↦ ⟨1, (Ideal.ne_top_iff_one P).1 ‹P.IsPrime›.ne_top, by simpa using hx⟩

/-- `localizationAt C P` is a `C`-algebra through the inclusion `C ≤ localizationAt C P`. -/
instance : Algebra C (localizationAt C P) :=
  (Subalgebra.inclusion (le_localizationAt C P)).toAlgebra

/-- The structure map `C → localizationAt C P` is the inclusion. -/
@[simp]
theorem coe_algebraMap_localizationAt (c : C) :
    ((algebraMap C (localizationAt C P) c : localizationAt C P) : K) = c := rfl

/-- The maps `C → localizationAt C P → K` compose to the inclusion `C → K`. -/
instance : IsScalarTower C (localizationAt C P) K :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- `localizationAt C P` is the localization of `C` at `P`. -/
instance isLocalization_localizationAt :
    IsLocalization.AtPrime (localizationAt C P) P := by
  rw [IsLocalization.AtPrime, isLocalization_iff]
  refine ⟨fun ⟨s, hs⟩ ↦ ?_, fun z ↦ ?_, fun {x y} hxy ↦ ⟨1, ?_⟩⟩
  · have hs0 : (s : K) ≠ 0 := fun h ↦ hs (by
      rw [show s = 0 from Subtype.ext h]; exact P.zero_mem)
    refine IsUnit.of_mul_eq_one ⟨(s : K)⁻¹, s, hs, by simp [hs0]⟩ (Subtype.ext ?_)
    simp [hs0]
  · obtain ⟨s, hs, hz⟩ := z.2
    refine ⟨(⟨_, hz⟩, ⟨s, hs⟩), Subtype.ext ?_⟩
    simp [mul_comm]
  · have : x = y := Subtype.ext (congrArg Subtype.val hxy :)
    rw [this]

/-- `localizationAt C P` is a local ring. -/
instance : IsLocalRing (localizationAt C P) :=
  IsLocalization.AtPrime.isLocalRing (localizationAt C P) P

/-- The localization of a Noetherian subalgebra is Noetherian. -/
instance [IsNoetherianRing C] : IsNoetherianRing (localizationAt C P) :=
  IsLocalization.isNoetherianRing P.primeCompl _ inferInstance

/-- The canonical `C`-algebra isomorphism between Mathlib's `Localization.AtPrime P` and
`localizationAt C P`. -/
noncomputable def localizationAtEquiv : Localization.AtPrime P ≃ₐ[C] localizationAt C P :=
  IsLocalization.algEquiv P.primeCompl _ _

/-- The localization of a subalgebra of dimension `≤ 1` has dimension `≤ 1`. -/
instance [Ring.KrullDimLE 1 C] : Ring.KrullDimLE 1 (localizationAt C P) := by
  rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height P (localizationAt C P)]
  exact (Ideal.height_le_ringKrullDim_of_ne_top ‹P.IsPrime›.ne_top).trans
    (Ring.krullDimLE_iff.1 ‹_›)

/-- The localization at the zero ideal is all of `K`. -/
theorem localizationAt_bot [IsDomain D] [IsFractionRing D K] :
    localizationAt C (⊥ : Ideal C) = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := D) x
  have hb0 : algebraMap D K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  refine ⟨algebraMap D C b, fun h ↦ hb0 ?_, ?_⟩
  · have := congrArg Subtype.val ((Ideal.mem_bot).1 h)
    simpa using this
  · have : algebraMap D K b * (algebraMap D K a / algebraMap D K b) = algebraMap D K a := by
      field_simp
    change algebraMap D K b * _ ∈ C
    rw [this]
    exact C.algebraMap_mem a

/-- An element of `K` lying in the localizations of `C` at all maximal ideals lies in `C`. -/
theorem mem_of_forall_mem_localizationAt {x : K}
    (h : ∀ (P : Ideal C) [P.IsMaximal], x ∈ localizationAt C P) : x ∈ C := by
  let J : Ideal C :=
    { carrier := {c | (c : K) * x ∈ C}
      add_mem' := fun {c d} hc hd ↦ by
        change ((c + d : C) : K) * x ∈ C
        simpa [add_mul] using C.add_mem hc hd
      zero_mem' := by
        change ((0 : C) : K) * x ∈ C
        simp
      smul_mem' := fun c d hd ↦ by
        change ((c * d : C) : K) * x ∈ C
        simpa [mul_assoc] using C.mul_mem c.2 hd }
  by_cases hJ : J = ⊤
  · have : (1 : C) ∈ J := hJ ▸ Submodule.mem_top
    simpa [J] using this
  · obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJ
    obtain ⟨s, hs, hsx⟩ := h P
    exact (hs (hJP hsx)).elim

/-- If `S ≤ T` with `T` local, the localization of `S` at the contraction of the maximal ideal of
`T` is contained in `T`. -/
theorem localizationAt_comap_le {S T : Subalgebra D K} (h : S ≤ T) [IsLocalRing T] :
    localizationAt S ((maximalIdeal T).comap (Subalgebra.inclusion h)) ≤ T := by
  rintro x ⟨s, hs, hsx⟩
  have hu : IsUnit (Subalgebra.inclusion h s) := by
    by_contra hn
    exact hs ((IsLocalRing.mem_maximalIdeal _).2 hn)
  obtain ⟨u, hu⟩ := hu
  have h1 : ((↑u⁻¹ : T) : K) * (s : K) = 1 := by
    have := congrArg Subtype.val u.inv_mul
    rw [hu] at this
    simpa using this
  have : x = ((↑u⁻¹ : T) : K) * ((s : K) * x) := by rw [← mul_assoc, h1, one_mul]
  rw [this]
  exact T.mul_mem (↑u⁻¹ : T).2 (h hsx)

/-- Monotonicity of localizations: if `S ≤ T` and `Q` is a prime of `T`, the localization of `S`
at the contraction of `Q` is contained in the localization of `T` at `Q`. -/
theorem localizationAt_le_localizationAt {S T : Subalgebra D K} (h : S ≤ T) (Q : Ideal T)
    [Q.IsPrime] : localizationAt S (Q.comap (Subalgebra.inclusion h)) ≤ localizationAt T Q := by
  rintro x ⟨s, hs, hsx⟩
  exact ⟨Subalgebra.inclusion h s, hs, h hsx⟩

end Localization

section Overring

variable {D K : Type*} [CommRing D] [Field K] [Algebra D K]

/-- For `E ≤ C`, the subalgebra `C` viewed as an `E`-subalgebra of `K`. -/
def overSubalgebra {E C : Subalgebra D K} (h : E ≤ C) : Subalgebra E K where
  carrier := C
  mul_mem' := C.mul_mem
  add_mem' := C.add_mem
  algebraMap_mem' e := h e.2

/-- `C` is an *overring* of `E` (inside `K`): `E ≤ C` and `C` is a finitely generated
`E`-module (i.e. the `E`-span of `C` in `K`, which is `C` itself, is finitely generated). -/
structure IsOverring (E C : Subalgebra D K) : Prop where
  le : E ≤ C
  fg : (Submodule.span E (C : Set K)).FG

variable {E R C : Subalgebra D K}

/-- For `E ≤ C`, the `E`-span of `C` is `C` itself. -/
theorem span_eq_overSubalgebra (h : E ≤ C) :
    Submodule.span E (C : Set K) = (overSubalgebra h).toSubmodule :=
  Submodule.span_eq (overSubalgebra h).toSubmodule

/-- The identity of `C` as an `E`-linear equivalence onto `overSubalgebra h`, for the
`E`-module structure on `C` given by the inclusion `E ≤ C`. -/
def overLinearEquiv (h : E ≤ C) :
    letI := (Subalgebra.inclusion h).toAlgebra
    C ≃ₗ[E] (overSubalgebra h).toSubmodule :=
  letI := (Subalgebra.inclusion h).toAlgebra
  { toFun := fun c ↦ ⟨c, c.2⟩
    invFun := fun y ↦ ⟨y, y.2⟩
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

/-- `IsOverring E C` means exactly that `C` is a finite `E`-module for the inclusion
`E ≤ C`. -/
theorem isOverring_iff (h : E ≤ C) :
    IsOverring E C ↔ letI := (Subalgebra.inclusion h).toAlgebra; Module.Finite E C := by
  let _ := (Subalgebra.inclusion h).toAlgebra
  constructor
  · rintro ⟨_, hfg⟩
    rw [span_eq_overSubalgebra h] at hfg
    have := Module.Finite.iff_fg.2 hfg
    exact Module.Finite.equiv (overLinearEquiv h).symm
  · intro hfin
    refine ⟨h, ?_⟩
    rw [span_eq_overSubalgebra h]
    exact Module.Finite.iff_fg.1 (Module.Finite.equiv (overLinearEquiv h))

/-- An overring is a finite module for the inclusion algebra structure. -/
theorem IsOverring.moduleFinite (h : IsOverring E C) :
    letI := (Subalgebra.inclusion h.le).toAlgebra; Module.Finite E C :=
  (isOverring_iff h.le).1 h

/-- Every subalgebra is an overring of itself. -/
theorem IsOverring.refl (E : Subalgebra D K) : IsOverring E E := by
  refine ⟨le_rfl, ⟨{1}, le_antisymm ?_ ?_⟩⟩
  · rw [Submodule.span_le, Finset.coe_singleton, Set.singleton_subset_iff]
    exact Submodule.subset_span E.one_mem
  · rw [Submodule.span_le]
    intro x hx
    have : x = (⟨x, hx⟩ : E) • (1 : K) := by simp [Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- Overrings of overrings are overrings. -/
theorem IsOverring.trans (h1 : IsOverring E R) (h2 : IsOverring R C) : IsOverring E C := by
  let _ : Algebra E R := (Subalgebra.inclusion h1.le).toAlgebra
  let _ : Algebra R C := (Subalgebra.inclusion h2.le).toAlgebra
  let _ : Algebra E C := (Subalgebra.inclusion (h1.le.trans h2.le)).toAlgebra
  have : IsScalarTower E R C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have := h1.moduleFinite
  have := h2.moduleFinite
  have : Module.Finite E C := Module.Finite.trans R C
  exact (isOverring_iff (h1.le.trans h2.le)).2 this

/-- Elements of an overring are integral over the base. -/
theorem IsOverring.isIntegral (h : IsOverring E C) {x : K} (hx : x ∈ C) : IsIntegral E x := by
  have hfg : (overSubalgebra h.le).toSubmodule.FG := span_eq_overSubalgebra h.le ▸ h.fg
  exact IsIntegral.of_mem_of_fg (overSubalgebra h.le) hfg x hx

/-- The inclusion of `E` into an overring is integral. -/
theorem IsOverring.ringHom_isIntegral (h : IsOverring E C) :
    ((Subalgebra.inclusion h.le : E →ₐ[D] C) : E →+* C).IsIntegral := by
  intro c
  obtain ⟨p, hp, hpc⟩ := h.isIntegral c.2
  refine ⟨p, hp, Subtype.val_injective ?_⟩
  have e1 := Polynomial.hom_eval₂ p ((Subalgebra.inclusion h.le : E →ₐ[D] C) : E →+* C)
    (C.val : C →+* K) c
  have e2 : (C.val : C →+* K).comp ((Subalgebra.inclusion h.le : E →ₐ[D] C) : E →+* C) =
      algebraMap E K := RingHom.ext fun _ ↦ rfl
  rw [e2] at e1
  simpa [hpc] using e1

/-- An overring of a Noetherian ring is Noetherian. -/
theorem IsOverring.isNoetherianRing [IsNoetherianRing E] (h : IsOverring E C) :
    IsNoetherianRing C := by
  let _ := (Subalgebra.inclusion h.le).toAlgebra
  have := h.moduleFinite
  exact IsNoetherianRing.of_finite E C

/-- An overring of a domain of dimension `≤ 1` has dimension `≤ 1`. -/
theorem IsOverring.krullDimLE [Ring.KrullDimLE 1 E] (h : IsOverring E C) :
    Ring.KrullDimLE 1 C := by
  refine Ring.KrullDimLE.mk₁' fun Q hQ0 hQ ↦ ?_
  have hf := h.ringHom_isIntegral
  obtain ⟨c, hcQ, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  obtain ⟨p, hp, hpc⟩ := hf c
  have hne : Q.comap ((Subalgebra.inclusion h.le : E →ₐ[D] C) : E →+* C) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_root_mem hc0 hcQ hp.ne_zero hpc
  have : (Q.comap ((Subalgebra.inclusion h.le : E →ₐ[D] C) : E →+* C)).IsMaximal :=
    Ideal.IsPrime.isMaximal_of_ne_bot (Ideal.comap_isPrime _ _) hne
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' _ hf Q this

/-- Maximal ideals of an overring of a local ring contract to the maximal ideal. -/
theorem IsOverring.comap_eq_maximalIdeal [IsLocalRing E] (h : IsOverring E C) (Q : Ideal C)
    [Q.IsMaximal] :
    Q.comap ((Subalgebra.inclusion h.le : E →ₐ[D] C) : E →+* C) = maximalIdeal E :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ h.ringHom_isIntegral Q)

/-- An overring of a local ring is semilocal. -/
theorem IsOverring.finite_maximalSpectrum [IsLocalRing E] (h : IsOverring E C) :
    Finite (MaximalSpectrum C) := by
  let _ := (Subalgebra.inclusion h.le).toAlgebra
  have := h.moduleFinite
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := E) (S := C) (maximalIdeal E)
  have : Finite ((maximalIdeal E).primesOver C) := hfin.to_subtype
  refine Finite.of_injective (fun Q : MaximalSpectrum C ↦
    (⟨Q.asIdeal, Q.isMaximal.isPrime,
      ⟨(@IsOverring.comap_eq_maximalIdeal _ _ _ _ _ _ _ _ h Q.asIdeal Q.isMaximal).symm⟩⟩ :
      (maximalIdeal E).primesOver C)) ?_
  intro Q Q' hQQ
  exact MaximalSpectrum.ext (congrArg Subtype.val hQQ)

/-- Elements of an overring have a common denominator from `D`. -/
theorem IsOverring.exists_den [IsDomain D] [IsFractionRing D K] (h : IsOverring E C) :
    ∃ δ : D, algebraMap D K δ ≠ 0 ∧ ∀ c ∈ C, algebraMap D K δ * c ∈ E := by
  classical
  obtain ⟨s, hs⟩ := h.fg
  obtain ⟨⟨b, hb⟩, hbs⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors D) s
  refine ⟨b, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb, fun c hc ↦ ?_⟩
  let N : Submodule E K := (1 : Submodule E K).comap (LinearMap.mulLeft E (algebraMap D K b))
  have hsN : Submodule.span E (s : Set K) ≤ N := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨y, hy⟩ := hbs x hx
    change algebraMap D K b * x ∈ (1 : Submodule E K)
    rw [Submodule.mem_one]
    refine ⟨algebraMap D E y, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, hy, Algebra.smul_def]
  have : c ∈ N := hsN (hs ▸ Submodule.subset_span hc)
  obtain ⟨e, he⟩ := Submodule.mem_one.1 this
  have he' : (e : K) = algebraMap D K b * c := he
  rw [← he']
  exact e.2

/-- The compositum of two overrings is an overring. -/
theorem IsOverring.sup {B B' : Subalgebra D K} (h1 : IsOverring E B) (h2 : IsOverring E B') :
    IsOverring E (B ⊔ B') := by
  have hle : E ≤ B ⊔ B' := h1.le.trans le_sup_left
  refine ⟨hle, ?_⟩
  have hset : ((B ⊔ B' : Subalgebra D K) : Set K) =
      ((overSubalgebra h1.le ⊔ overSubalgebra h2.le : Subalgebra E K) : Set K) := by
    apply le_antisymm
    · have : B ⊔ B' ≤ (overSubalgebra h1.le ⊔ overSubalgebra h2.le).restrictScalars D :=
        sup_le (fun x hx ↦ (Subalgebra.mem_restrictScalars D).2
            (Algebra.mem_sup_left (S := overSubalgebra h1.le) (T := overSubalgebra h2.le) hx))
          (fun x hx ↦ (Subalgebra.mem_restrictScalars D).2
            (Algebra.mem_sup_right (S := overSubalgebra h1.le) (T := overSubalgebra h2.le) hx))
      exact this
    · have : overSubalgebra h1.le ⊔ overSubalgebra h2.le ≤ overSubalgebra hle :=
        sup_le (fun x hx ↦ (le_sup_left : B ≤ B ⊔ B') hx)
          (fun x hx ↦ (le_sup_right : B' ≤ B ⊔ B') hx)
      exact this
  have hfg1 : (overSubalgebra h1.le).toSubmodule.FG := span_eq_overSubalgebra h1.le ▸ h1.fg
  have hfg2 : (overSubalgebra h2.le).toSubmodule.FG := span_eq_overSubalgebra h2.le ▸ h2.fg
  rw [hset]
  have heq : Submodule.span E
      ((overSubalgebra h1.le ⊔ overSubalgebra h2.le : Subalgebra E K) : Set K) =
      (overSubalgebra h1.le ⊔ overSubalgebra h2.le).toSubmodule :=
    Submodule.span_eq (overSubalgebra h1.le ⊔ overSubalgebra h2.le).toSubmodule
  rw [heq, ← Subalgebra.mul_toSubmodule]
  exact hfg1.mul hfg2

end Overring

section Admissible

variable {D K : Type*} [CommRing D] [Field K] [Algebra D K]

/-- `C` is an *admissible overring* of `E` for the family `f`: it is an overring of `E` and `f`
factors in the localization of `C` at every maximal ideal. -/
structure Admissible {ι : Type*} (E C : Subalgebra D K) (f : ι → Kˣ) : Prop where
  isOverring : IsOverring E C
  factors : ∀ (P : Ideal C) [P.IsMaximal], Factors (localizationAt C P) f

variable {ι : Type*} {E R C : Subalgebra D K} {f : ι → Kˣ}

/-- An admissible overring of an overring `R` of `E` is an admissible overring of `E`. -/
theorem Admissible.of_isOverring (h : IsOverring E R) (hC : Admissible R C f) :
    Admissible E C f :=
  ⟨h.trans hC.isOverring, hC.factors⟩

/-- If `f` factors in `E`, then `E` itself is admissible for `f`. -/
theorem admissible_self_of_factors (hf : Factors E f) : Admissible E E f :=
  ⟨IsOverring.refl E, fun P _ ↦ hf.mono (le_localizationAt E P)⟩

/-- An overring of an admissible overring is again admissible. -/
theorem Admissible.of_isOverring_right (hB : Admissible E R f) (hRC : IsOverring R C) :
    Admissible E C f := by
  refine ⟨hB.isOverring.trans hRC, fun Q _ ↦ ?_⟩
  have hP : (Q.comap (Subalgebra.inclusion hRC.le)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hRC.ringHom_isIntegral Q
  exact (hB.factors _).mono (localizationAt_le_localizationAt hRC.le Q)

end Admissible

section Blowup

open GromovWitten.AlgebraicGeometry.IntersectionTheory.VectorBundle (UnitDifferences)

variable {R : Type*} [CommRing R]

/-- The homogeneous form `g ↦ ∑ j, g j * (a ^ j * b ^ (d - j))` of degree `d` in `a, b`. -/
private noncomputable def homForm (a b : R) (d : ℕ) : (Fin (d + 1) → R) →ₗ[R] R :=
  Fintype.linearCombination R (fun j : Fin (d + 1) ↦ a ^ (j : ℕ) * b ^ (d - j))

private theorem homForm_apply (a b : R) (d : ℕ) (g : Fin (d + 1) → R) :
    homForm a b d g = ∑ j, g j * (a ^ (j : ℕ) * b ^ (d - j)) := by
  simp [homForm, Fintype.linearCombination_apply, smul_eq_mul]

private theorem homForm_single (a b : R) (d : ℕ) (j : Fin (d + 1)) (r : R) :
    homForm a b d (Pi.single j r) = r * (a ^ (j : ℕ) * b ^ (d - j)) := by
  classical
  simp [homForm, Fintype.linearCombination_apply_single, smul_eq_mul]

private theorem single_mem_pi [IsLocalRing R] (d : ℕ) (j : Fin (d + 1)) {r : R}
    (hr : r ∈ maximalIdeal R) :
    (Pi.single j r : Fin (d + 1) → R) ∈
      Submodule.pi Set.univ (fun _ : Fin (d + 1) ↦ maximalIdeal R) := by
  classical
  rw [Submodule.mem_pi]
  intro i _
  by_cases hij : i = j
  · subst hij; simpa using hr
  · simp [hij]

private theorem length_residue_eq_one [IsLocalRing R] :
    Module.length R (R ⧸ maximalIdeal R) = 1 := by
  have : IsSimpleModule R (R ⧸ maximalIdeal R) :=
    isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 inferInstance)
  exact Module.length_eq_one R _

/-- **Step (i)–(ii) of the blow-up lemma.** In a Noetherian local domain of dimension `≤ 1`, for
`a, b` in the maximal ideal with `a ≠ 0` there is a homogeneous relation
`∑ j, g j * a ^ j * b ^ (d - j) = 0` with some coefficient `g j` a unit. -/
private theorem exists_homogeneous_relation [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] {a b : R}
    (ha : a ∈ maximalIdeal R) (hb : b ∈ maximalIdeal R) (ha0 : a ≠ 0) :
    ∃ (d : ℕ) (g : Fin (d + 1) → R), homForm a b d g = 0 ∧ ∃ j, g j ∉ maximalIdeal R := by
  classical
  by_contra H
  push Not at H
  let m := maximalIdeal R
  let U : ℕ → Submodule R R := fun d ↦ LinearMap.range (homForm a b d)
  let V : ℕ → Submodule R R := fun d ↦ (Submodule.pi Set.univ fun _ ↦ m).map (homForm a b d)
  have hVU : ∀ d, V d ≤ U d := fun d ↦ LinearMap.map_le_range
  have hUV : ∀ d, U (d + 1) ≤ V d := by
    intro d
    rintro _ ⟨g, rfl⟩
    rw [homForm_apply]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [← smul_eq_mul]
    refine Submodule.smul_mem _ _ ?_
    induction j using Fin.cases with
    | zero =>
      refine ⟨Pi.single 0 b, single_mem_pi d 0 hb, ?_⟩
      rw [homForm_single]
      simp [pow_succ']
    | succ i =>
      refine ⟨Pi.single i a, single_mem_pi d i ha, ?_⟩
      rw [homForm_single]
      simp only [Fin.val_succ]
      rw [show d + 1 - (i + 1 : ℕ) = d - i by omega, pow_succ']
      ring
  have hU0 : U 0 = ⊤ := by
    refine eq_top_iff.2 fun r _ ↦ ⟨fun _ ↦ r, ?_⟩
    simp [homForm_apply]
  have haU : ∀ n, Ideal.span {a ^ n} ≤ U n := by
    intro n
    refine (Ideal.span_le).2 (Set.singleton_subset_iff.2 ⟨Pi.single (Fin.last n) 1, ?_⟩)
    rw [homForm_single]
    simp
  have hker : ∀ d, (V d).comap (homForm a b d) = Submodule.pi Set.univ fun _ ↦ m := by
    intro d
    refine le_antisymm ?_ fun g hg ↦ Submodule.mem_map_of_mem hg
    rintro g ⟨ρ, hρ, hρg⟩
    have h0 : homForm a b d (g - ρ) = 0 := by rw [map_sub, hρg, sub_self]
    rw [SetLike.mem_coe, Submodule.mem_pi] at hρ
    rw [Submodule.mem_pi]
    intro j _
    have := H d (g - ρ) h0 j
    have h2 := m.add_mem this (hρ j (Set.mem_univ j))
    simpa using h2
  have hlen : ∀ d, Module.length R (R ⧸ U d) + ((d + 1 : ℕ) : ℕ∞) ≤
      Module.length R (R ⧸ U (d + 1)) := by
    intro d
    let F := Submodule.factor (hVU d)
    have hFsurj : Function.Surjective F := by
      intro y
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk x, rfl⟩
    have hsplit := Module.length_eq_add_of_exact (LinearMap.ker F).subtype F
      (Submodule.subtype_injective _) hFsurj (LinearMap.exact_subtype_ker_map F)
    let Ψ := (V d).mkQ ∘ₗ homForm a b d
    have hrange : LinearMap.range Ψ = LinearMap.ker F := by
      apply le_antisymm
      · rintro _ ⟨g, rfl⟩
        rw [LinearMap.mem_ker]
        change Submodule.Quotient.mk (homForm a b d g) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact ⟨g, rfl⟩
      · intro y hy
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        rw [LinearMap.mem_ker] at hy
        change Submodule.Quotient.mk x = 0 at hy
        rw [Submodule.Quotient.mk_eq_zero] at hy
        obtain ⟨g, rfl⟩ := hy
        exact ⟨g, rfl⟩
    have hkerΨ : LinearMap.ker Ψ = Submodule.pi Set.univ fun _ ↦ m := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ, hker d]
    have hlenker : Module.length R (LinearMap.ker F) = ((d + 1 : ℕ) : ℕ∞) := by
      rw [← hrange, ← (LinearMap.quotKerEquivRange Ψ).length_eq, hkerΨ,
        (Submodule.quotientPi fun _ ↦ m).length_eq, Module.length_pi_of_fintype]
      simp [m, length_residue_eq_one]
    have hle : Module.length R (R ⧸ V d) ≤ Module.length R (R ⧸ U (d + 1)) :=
      Module.length_le_of_surjective (Submodule.factor (hUV d)) (by
        intro y
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact ⟨Submodule.Quotient.mk x, rfl⟩)
    rw [hsplit, hlenker, add_comm] at hle
    exact hle
  have hsq : ∀ n : ℕ, ((n * n : ℕ) : ℕ∞) ≤ 2 * Module.length R (R ⧸ U n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (((n + 1) * (n + 1) : ℕ) : ℕ∞) ≤ ((n * n + 2 * (n + 1) : ℕ) : ℕ∞) := by
            exact_mod_cast (by nlinarith : (n + 1) * (n + 1) ≤ n * n + 2 * (n + 1))
        _ = ((n * n : ℕ) : ℕ∞) + 2 * ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ 2 * Module.length R (R ⧸ U n) + 2 * ((n + 1 : ℕ) : ℕ∞) := by gcongr
        _ = 2 * (Module.length R (R ⧸ U n) + ((n + 1 : ℕ) : ℕ∞)) := by ring
        _ ≤ 2 * Module.length R (R ⧸ U (n + 1)) := by gcongr; exact hlen n
  have ha0' : a ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero ha0
  have hleord : ∀ n, Module.length R (R ⧸ U n) ≤ n • Ring.ord R a := by
    intro n
    rw [← Ring.ord_pow ha0']
    exact Module.length_le_of_surjective (Submodule.factor (haU n)) (by
      intro y
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk x, rfl⟩)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (Ring.ord_ne_top ha0')
  have key : (((2 * k + 1) * (2 * k + 1) : ℕ) : ℕ∞) ≤ 2 * ((2 * k + 1) • Ring.ord R a) :=
    (hsq (2 * k + 1)).trans (by gcongr; exact hleord (2 * k + 1))
  rw [← hk, nsmul_eq_mul] at key
  have key' : (2 * k + 1) * (2 * k + 1) ≤ 2 * ((2 * k + 1) * k) := by exact_mod_cast key
  nlinarith

/-- **Blow-up lemma (B1, replacing Stacks 42.4.2).** Let `R` be a Noetherian local domain of
Krull dimension `≤ 1` with fraction field `K`, having unit differences. For nonzero `a, b` in the
maximal ideal there is `μ : R` with `a + μ * b ≠ 0` such that `b / (a + μ * b)` is integral
over `R`. -/
theorem exists_integral_blowup [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (hU : UnitDifferences R) {a b : R} (ha : a ∈ maximalIdeal R) (hb : b ∈ maximalIdeal R)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∃ μ : R, a + μ * b ≠ 0 ∧
      IsIntegral R (algebraMap R K b / algebraMap R K (a + μ * b)) := by
  classical
  obtain ⟨d, g, hg0, j₀, hj₀⟩ := exists_homogeneous_relation ha hb ha0
  let gp : R[X] := ∑ j : Fin (d + 1), C (g j) * X ^ (j : ℕ)
  have hcoeff : gp.coeff j₀ = g j₀ := by
    simp only [gp, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Fin.ext h.symm)
    · simp
  have heval : ∀ t : R, gp.eval t = ∑ j : Fin (d + 1), g j * t ^ (j : ℕ) := by
    intro t
    simp [gp, eval_finsetSum]
  have hgbar : gp.map (residue R) ≠ 0 := by
    intro h
    have := congrArg (fun p ↦ p.coeff j₀) h
    simp only [coeff_map, hcoeff, coeff_zero] at this
    exact hj₀ ((residue_eq_zero_iff _).1 this)
  obtain ⟨Λ, hΛinf, hΛ⟩ := hU
  obtain ⟨μ, hG⟩ : ∃ μ : R, IsUnit (gp.eval (-μ)) := by
    let F : Λ → ResidueField R := fun μ ↦ residue R (-(μ : R))
    have hF : Function.Injective F := by
      intro μ ν hμν
      by_contra hne
      have hu := hΛ μ μ.2 ν ν.2 (fun h ↦ hne (Subtype.ext h))
      apply (residue_ne_zero_iff_isUnit _).2 hu
      have : residue R (-(μ : R)) = residue R (-(ν : R)) := hμν
      rw [map_sub, sub_eq_zero]
      simpa using this
    have hfin : (F ⁻¹' {c | (gp.map (residue R)).IsRoot c}).Finite :=
      Set.Finite.preimage hF.injOn (Polynomial.finite_setOfPred_isRoot hgbar)
    have : Infinite Λ := hΛinf.to_subtype
    obtain ⟨μ, hμ⟩ := hfin.infinite_compl.nonempty
    refine ⟨μ, ?_⟩
    rw [← residue_ne_zero_iff_isUnit]
    have h1 : ¬ (gp.map (residue R)).IsRoot (F μ) := hμ
    rwa [IsRoot.def, eval_map, eval₂_hom] at h1
  have hd : ∀ j : Fin (d + 1), (j : ℕ) ≤ d := fun j ↦ Nat.lt_succ_iff.1 j.2
  have hx0 : a + μ * b ≠ 0 := by
    intro hx
    have ha' : a = -μ * b := by linear_combination hx
    have : b ^ d * gp.eval (-μ) = 0 := by
      calc b ^ d * gp.eval (-μ) = homForm a b d g := by
            rw [heval, Finset.mul_sum, homForm_apply]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            have hbj : b ^ (j : ℕ) * b ^ (d - j) = b ^ d := pow_mul_pow_sub b (hd j)
            rw [ha', mul_pow]
            linear_combination (-(g j * (-μ) ^ (j : ℕ))) * hbj
        _ = 0 := hg0
    exact (mul_ne_zero (pow_ne_zero _ hb0) hG.ne_zero) this
  refine ⟨μ, hx0, ?_⟩
  have hinj := IsFractionRing.injective R K
  have hB : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
  have hX : algebraMap R K (a + μ * b) ≠ 0 := (map_ne_zero_iff _ hinj).2 hx0
  set A := algebraMap R K a with hA
  set B := algebraMap R K b with hBdef
  let w := A / B
  have hw : aeval w gp = 0 := by
    have : B ^ d * aeval w gp = algebraMap R K (homForm a b d g) := by
      rw [homForm_apply, map_sum]
      simp only [map_sum, map_mul, map_pow, aeval_C, aeval_X]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hBj : B ^ (j : ℕ) * B ^ (d - j) = B ^ d := pow_mul_pow_sub B (hd j)
      rw [← hBj]
      simp only [w, div_pow]
      field_simp
      ring
    rw [hg0, map_zero] at this
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hB)
  let z := w + algebraMap R K μ
  have hz : z = algebraMap R K (a + μ * b) / B := by
    simp only [z, w, map_add, map_mul]
    field_simp
    rw [← hA, ← hBdef]
    ring
  have hz0 : z ≠ 0 := by
    rw [hz]
    exact div_ne_zero hX hB
  let q := gp.comp (X - C μ)
  have hq : eval₂ (algebraMap R K) z q = 0 := by
    rw [← aeval_def, aeval_comp]
    simpa [z] using hw
  have hq0 : q.coeff 0 = gp.eval (-μ) := by
    rw [coeff_zero_eq_eval_zero, eval_comp]
    simp
  obtain ⟨u, hu⟩ := hG
  have hq0' : q.coeff 0 ≠ 0 := by
    rw [hq0, ← hu]
    exact u.ne_zero
  have hlc : q.reverse.leadingCoeff = u := by
    rw [reverse_leadingCoeff, trailingCoeff, natTrailingDegree_eq_zero.2 (Or.inr hq0'), hq0, hu]
  have hmonic : (C (↑u⁻¹ : R) * q.reverse).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hlc]; simp)
  let _ := invertibleOfNonzero hz0
  have hrev := (eval₂_reverse_eq_zero_iff (algebraMap R K) z q).2 hq
  rw [invOf_eq_inv] at hrev
  have hy : B / algebraMap R K (a + μ * b) = z⁻¹ := by rw [hz, inv_div]
  rw [hy]
  refine ⟨C (↑u⁻¹ : R) * q.reverse, hmonic, ?_⟩
  rw [eval₂_mul, hrev, mul_zero]

end Blowup

section Gluing

/-- In a local domain of dimension `≤ 1`, every element of the maximal ideal has a power in any
nonzero principal ideal. -/
theorem exists_pow_mem_span_of_mem_maximalIdeal {L : Type*} [CommRing L] [IsDomain L]
    [IsLocalRing L] [Ring.KrullDimLE 1 L] {t β : L} (ht : t ∈ maximalIdeal L) (hβ : β ≠ 0) :
    ∃ N : ℕ, t ^ N ∈ Ideal.span {β} := by
  have : t ∈ (Ideal.span {β}).radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.2 fun p ⟨hle, hp⟩ ↦ ?_
    have hp0 : p ≠ ⊥ := fun h ↦ hβ (by
      rw [h] at hle
      exact (Ideal.mem_bot).1 (hle (Ideal.mem_span_singleton_self β)))
    have := hp.isMaximal_of_ne_bot hp0
    rw [IsLocalRing.eq_maximalIdeal this]
    exact ht
  obtain ⟨N, hN⟩ := this
  exact ⟨N, hN⟩

variable {D K : Type*} [CommRing D] [IsDomain D] [Field K] [Algebra D K] [IsFractionRing D K]

/-- **Gluing, B2 (a)–(b).** Let `R` be a Noetherian semilocal subalgebra of `K` and, for every
maximal ideal `P` of `R`, let `Cf P` be an overring of `localizationAt R P`. Then the
intersection `⨅ P, Cf P` is an overring of `R` (it contains `R`, and it lies in `δ⁻¹ R` for a
common denominator `δ`). -/
theorem isOverring_iInf {R : Subalgebra D K} [IsNoetherianRing R] [Finite (MaximalSpectrum R)]
    (Cf : MaximalSpectrum R → Subalgebra D K)
    (hCf : ∀ P : MaximalSpectrum R, IsOverring (localizationAt R P.asIdeal) (Cf P)) :
    IsOverring R (⨅ P, Cf P) := by
  classical
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let C : Subalgebra D K := ⨅ P, Cf P
  have hRC : R ≤ C :=
    le_iInf fun P ↦ (le_localizationAt R P.asIdeal).trans (hCf P).le
  choose δ hδ0 hδ using fun P ↦ (hCf P).exists_den
  let Δ : D := ∏ P, δ P
  have hΔ0 : algebraMap D K Δ ≠ 0 := by
    simp only [Δ, map_prod]
    exact Finset.prod_ne_zero_iff.2 fun P _ ↦ hδ0 P
  have hΔ : ∀ c ∈ C, algebraMap D K Δ * c ∈ R := by
    intro c hc
    apply mem_of_forall_mem_localizationAt
    intro P hP
    let P' : MaximalSpectrum R := ⟨P, hP⟩
    have hcP : c ∈ Cf P' := (iInf_le (fun P ↦ Cf P) P') hc
    have h1 := hδ P' c hcP
    rw [show Δ = δ P' * ∏ Q ∈ Finset.univ.erase P', δ Q from
      (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm, map_mul,
      mul_comm (algebraMap D K (δ P')), mul_assoc]
    exact (localizationAt R P).mul_mem ((localizationAt R P).algebraMap_mem _) h1
  refine ⟨hRC, ?_⟩
  have hfg : (Submodule.span R {(algebraMap D K Δ)⁻¹} : Submodule R K).FG :=
    Submodule.fg_span_singleton _
  refine hfg.of_le (Submodule.span_le.2 fun c hc ↦ ?_)
  rw [SetLike.mem_coe, Submodule.mem_span_singleton]
  refine ⟨⟨_, hΔ c hc⟩, ?_⟩
  rw [Algebra.smul_def]
  change algebraMap D K Δ * c * (algebraMap D K Δ)⁻¹ = c
  field_simp

/-- **Gluing, B2 (c).** Let `R` be a semilocal subalgebra of `K` of dimension `≤ 1`, and let
`Cf P ⊇ localizationAt R P` for every maximal ideal `P` of `R`, with `R ≤ ⨅ P, Cf P`. If `Q` is a
prime of `⨅ P, Cf P` contracting to the maximal ideal `P` of `R`, then `Cf P` is contained in the
localization of `⨅ P, Cf P` at `Q`. -/
theorem le_localizationAt_iInf {R : Subalgebra D K} [Ring.KrullDimLE 1 R]
    [Finite (MaximalSpectrum R)] (Cf : MaximalSpectrum R → Subalgebra D K)
    (hCf : ∀ P : MaximalSpectrum R, localizationAt R P.asIdeal ≤ Cf P) (hRC : R ≤ ⨅ P, Cf P)
    (Q : Ideal (⨅ P, Cf P : Subalgebra D K)) [Q.IsPrime] (P : MaximalSpectrum R)
    (hQP : Q.comap (Subalgebra.inclusion hRC) = P.asIdeal) :
    Cf P ≤ localizationAt (⨅ P, Cf P) Q := by
  classical
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  intro y hy
  obtain ⟨α, β, hβ, rfl⟩ := IsFractionRing.div_surjective (A := D) y
  have hβ0 : algebraMap D K β ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hβ
  have hchoose : ∀ P' : MaximalSpectrum R, ∃ r : R, r ∉ P.asIdeal ∧
      (P' ≠ P → (r : K) / algebraMap D K β ∈ localizationAt R P'.asIdeal) := by
    intro P'
    by_cases hPP : P' = P
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 P.isMaximal.ne_top, fun h ↦ (h hPP).elim⟩
    · obtain ⟨t, htP', htP⟩ : ∃ t ∈ P'.asIdeal, t ∉ P.asIdeal := by
        by_contra hcon
        push Not at hcon
        exact hPP (MaximalSpectrum.ext (P'.isMaximal.eq_of_le P.isMaximal.ne_top hcon))
      let L := localizationAt R P'.asIdeal
      have htm : algebraMap R L t ∈ maximalIdeal L := (IsLocalRing.mem_maximalIdeal _).2
        fun hu ↦ ((IsLocalization.AtPrime.isUnit_to_map_iff L P'.asIdeal t).1 hu) htP'
      have hβL : algebraMap D L β ≠ 0 := fun h0 ↦ hβ0 (congrArg Subtype.val h0 :)
      obtain ⟨N, hN⟩ := exists_pow_mem_span_of_mem_maximalIdeal htm hβL
      obtain ⟨ℓ, hℓ⟩ := Ideal.mem_span_singleton'.1 hN
      refine ⟨t ^ N, fun h ↦ htP (P.isMaximal.isPrime.mem_of_pow_mem N h), fun _ ↦ ?_⟩
      have h2 : (ℓ : K) * algebraMap D K β = ((t ^ N : R) : K) := by
        have := congrArg Subtype.val hℓ
        simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow] at this ⊢
        exact this
      have h3 : ((t ^ N : R) : K) / algebraMap D K β = (ℓ : K) := by
        rw [← h2]
        field_simp
      rw [h3]
      exact ℓ.2
  choose r hrP hr using hchoose
  let s : R := ∏ P', r P'
  have hsP : s ∉ P.asIdeal := by
    intro hmem
    obtain ⟨P', _, h⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isMaximal.isPrime)).1 hmem
    exact hrP P' h
  refine ⟨Subalgebra.inclusion hRC s, fun h ↦ hsP ?_, ?_⟩
  · rw [← hQP]
    exact h
  change (s : K) * (algebraMap D K α / algebraMap D K β) ∈ ⨅ P, Cf P
  refine Algebra.mem_iInf.2 fun P' ↦ ?_
  by_cases hPP : P' = P
  · subst hPP
    exact (Cf _).mul_mem (hCf _ (le_localizationAt _ _ s.2)) hy
  · have hs : s = r P' * ∏ Q' ∈ Finset.univ.erase P', r Q' :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
    have : (s : K) * (algebraMap D K α / algebraMap D K β) =
        ((r P' : K) / algebraMap D K β) *
          (((∏ Q' ∈ Finset.univ.erase P', r Q' : R) : K) * algebraMap D K α) := by
      rw [hs]
      push_cast
      field_simp
    rw [this]
    refine hCf P' ((localizationAt R P'.asIdeal).mul_mem (hr P' hPP)
      ((localizationAt R P'.asIdeal).mul_mem (le_localizationAt _ _ (Subtype.prop _))
        ((localizationAt R P'.asIdeal).algebraMap_mem α)))

/-- **Gluing, B2 (d).** If `S` is admissible for `f` over a subalgebra `E'` of
dimension `≤ 1`, and `S ≤ T` with `T` local, then `f` factors in `T`: `T` contains the
localization of `S` at the contraction of the maximal ideal of `T`, which is either a maximal
ideal of `S` or zero (in which case `T = K`). -/
theorem Admissible.factors_of_le {ι : Type*} {E' S T : Subalgebra D K} {f : ι → Kˣ}
    [Ring.KrullDimLE 1 E'] (hS : Admissible E' S f) (hST : S ≤ T) [IsLocalRing T] :
    Factors T f := by
  have hdim := hS.isOverring.krullDimLE
  let Q'' : Ideal S := (maximalIdeal T).comap (Subalgebra.inclusion hST)
  have hloc : localizationAt S Q'' ≤ T := localizationAt_comap_le hST
  by_cases hQ0 : Q'' = ⊥
  · have htop : T = ⊤ := by
      refine eq_top_iff.2 fun x _ ↦ hloc ?_
      obtain ⟨α, β, hβ, rfl⟩ := IsFractionRing.div_surjective (A := D) x
      have hβ0 : algebraMap D K β ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hβ
      refine ⟨algebraMap D S β, ?_, ?_⟩
      · rw [hQ0, Ideal.mem_bot]
        exact fun h0 ↦ hβ0 (congrArg Subtype.val h0 :)
      · change algebraMap D K β * (algebraMap D K α / algebraMap D K β) ∈ S
        rw [mul_div_cancel₀ _ hβ0]
        exact S.algebraMap_mem α
    rw [htop]
    exact factors_top f
  · have hmax : Q''.IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot inferInstance hQ0
    exact (hS.factors Q'').mono hloc

/-- **Gluing lemma (B2, replacing Stacks 42.4.1).** Let `R` be an overring of a Noetherian local
subalgebra `E` of `K` of dimension `≤ 1`. If for every maximal ideal `P` of `R` the family `f`
has an admissible overring over `localizationAt R P`, then `f` has an admissible overring
over `E`. (The overring is the intersection of the local ones.) -/
theorem exists_admissible_of_forall_localizationAt {ι : Type*} {E R : Subalgebra D K}
    [IsLocalRing E] [IsNoetherianRing E] [Ring.KrullDimLE 1 E] (hER : IsOverring E R)
    {f : ι → Kˣ} (h : ∀ (P : Ideal R) [P.IsMaximal], ∃ C, Admissible (localizationAt R P) C f) :
    ∃ C, Admissible E C f := by
  have := hER.isNoetherianRing
  have := hER.krullDimLE
  have := hER.finite_maximalSpectrum
  choose Cf hCf using fun P : MaximalSpectrum R ↦ h P.asIdeal
  have hC := isOverring_iInf Cf fun P ↦ (hCf P).isOverring
  refine ⟨⨅ P, Cf P, hER.trans hC, fun Q hQ ↦ ?_⟩
  have hP0 : (Q.comap (Subalgebra.inclusion hC.le)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hC.ringHom_isIntegral Q
  let P : MaximalSpectrum R := ⟨Q.comap (Subalgebra.inclusion hC.le), hP0⟩
  have hkey : Cf P ≤ localizationAt (⨅ P, Cf P) Q :=
    le_localizationAt_iInf Cf (fun P ↦ (hCf P).isOverring.le) hC.le Q P rfl
  exact (hCf P).factors_of_le hkey

end Gluing

section Order

/-- A non-unit has nonzero order. -/
theorem ord_ne_zero_of_not_isUnit {A : Type*} [CommRing A] {a : A} (ha : ¬ IsUnit a) :
    Ring.ord A a ≠ 0 := by
  intro h
  rw [Ring.ord, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top] at h
  exact ha h

variable {D K : Type*} [CommRing D] [IsDomain D] [Field K] [Algebra D K] [IsFractionRing D K]

/-- **Orders do not increase in the local rings of an overring.** Let `R` be an overring of a
Noetherian local subalgebra `E` of `K` of dimension `≤ 1`, and `P` a maximal ideal of `R`. For
nonzero `z ∈ E`, `ord_{R_P} z ≤ ord_E z`. This follows from Fulton's Example A.3.1
(`OrderBirational.ord_eq_finsum`), which writes `ord_E z` as a sum over the maximal ideals of
`R` whose `P`-summand is `[κ(P) : κ(E)] * ord_{R_P} z`. -/
theorem ord_localizationAt_le {E R : Subalgebra D K} [IsLocalRing E] [IsNoetherianRing E]
    [Ring.KrullDimLE 1 E] (hER : IsOverring E R) (P : Ideal R) [P.IsMaximal] {z : E}
    (hz : z ≠ 0) :
    Ring.ord (localizationAt R P) (Subalgebra.inclusion (hER.le.trans (le_localizationAt R P)) z)
      ≤ Ring.ord E z := by
  let _ : Algebra E R := (Subalgebra.inclusion hER.le).toAlgebra
  have := hER.moduleFinite
  have := hER.finite_maximalSpectrum
  have hinj : Function.Injective (algebraMap E R) := Subalgebra.inclusion_injective _
  have hrank : ∀ b : R, ∃ (s : E) (a : E), s ≠ 0 ∧ s • b = algebraMap E R a := by
    intro b
    obtain ⟨α, β, hβ, hb⟩ := IsFractionRing.div_surjective (A := D) (b : K)
    have hβ0 : algebraMap D K β ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hβ
    refine ⟨algebraMap D E β, algebraMap D E α, fun h ↦ hβ0 (congrArg Subtype.val h :),
      Subtype.ext ?_⟩
    change algebraMap D K β * (b : K) = algebraMap D K α
    rw [← hb]
    field_simp
  rw [OrderBirational.ord_eq_finsum hinj hrank hz]
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  let P' : MaximalSpectrum R := ⟨P, inferInstance⟩
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ P'))
  have hord : Ring.ord (localizationAt R P)
      (Subalgebra.inclusion (hER.le.trans (le_localizationAt R P)) z) =
      Ring.ord (Localization.AtPrime P) (algebraMap E (Localization.AtPrime P) z) := by
    rw [← GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalOrdSymmetry.ord_ringEquiv
      (localizationAtEquiv R P).toRingEquiv]
    congr 1
    rw [IsScalarTower.algebraMap_apply E R (Localization.AtPrime P)]
    change _ = (localizationAtEquiv R P) (algebraMap R (Localization.AtPrime P) _)
    rw [AlgEquiv.commutes]
    rfl
  rw [hord]
  have hpos : 1 ≤ (Module.finrank (ResidueField E) P'.asIdeal.ResidueField : ℕ∞) := by
    have := Module.finrank_pos (R := ResidueField E) (M := P.ResidueField)
    exact_mod_cast this
  calc _ = 1 * Ring.ord (Localization.AtPrime P) (algebraMap E (Localization.AtPrime P) z) :=
        (one_mul _).symm
    _ ≤ _ := by gcongr

end Order

section Pair

open GromovWitten.AlgebraicGeometry.IntersectionTheory.VectorBundle
  (UnitDifferences unitDifferences_of_injective)

variable {D K : Type*} [CommRing D] [IsDomain D] [Field K] [Algebra D K] [IsFractionRing D K]

omit [IsDomain D] [IsFractionRing D K] in
/-- Rewriting a factorization of a pair into one of another pair. -/
theorem Factors.pair_of_eq {S : Subalgebra D K} {g₀ g₁ f₀ f₁ : Kˣ} (hg : Factors S ![g₀, g₁])
    (v₀ v₁ : Sˣ) (n₀ n₁ : Fin 2 → ℤ) (h₀ : f₀ = unitsToK S v₀ * (g₀ ^ n₀ 0 * g₁ ^ n₀ 1))
    (h₁ : f₁ = unitsToK S v₁ * (g₀ ^ n₁ 0 * g₁ ^ n₁ 1)) : Factors S ![f₀, f₁] := by
  refine hg.of_eq_mul_prod _ ![v₀, v₁] ![n₀, n₁] fun i ↦ ?_
  fin_cases i
  · simpa [Fin.prod_univ_two] using h₀
  · simpa [Fin.prod_univ_two] using h₁

private theorem exists_admissible_pair_aux (N : ℕ) :
    ∀ (E : Subalgebra D K) [IsLocalRing E] [IsNoetherianRing E] [Ring.KrullDimLE 1 E],
      UnitDifferences E → ∀ (x y : Kˣ) (hx : (x : K) ∈ E) (hy : (y : K) ∈ E),
      (Ring.ord E ⟨x, hx⟩).toNat + (Ring.ord E ⟨y, hy⟩).toNat ≤ N →
      ∃ C, Admissible E C ![x, y] := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro E _ _ _ hU x y hx hy hN
  by_cases hau : IsUnit (⟨x, hx⟩ : E)
  · refine ⟨E, admissible_self_of_factors ⟨⟨y, hy⟩, ![0, 1], ![hau.unit, 1], y.ne_zero, ?_⟩⟩
    intro i
    fin_cases i <;> simp
  by_cases hbu : IsUnit (⟨y, hy⟩ : E)
  · refine ⟨E, admissible_self_of_factors ⟨⟨x, hx⟩, ![1, 0], ![1, hbu.unit], x.ne_zero, ?_⟩⟩
    intro i
    fin_cases i <;> simp
  set a : E := ⟨x, hx⟩ with ha_def
  set b : E := ⟨y, hy⟩ with hb_def
  have ha : a ∈ maximalIdeal E := (mem_maximalIdeal _).2 hau
  have hb : b ∈ maximalIdeal E := (mem_maximalIdeal _).2 hbu
  have ha0 : a ≠ 0 := fun h ↦ x.ne_zero (congrArg Subtype.val h :)
  have hb0 : b ≠ 0 := fun h ↦ y.ne_zero (congrArg Subtype.val h :)
  obtain ⟨μ, hw0, hint⟩ := exists_integral_blowup (K := K) hU ha hb ha0 hb0
  set w : E := a + μ * b with hw_def
  have hwK : (w : K) ≠ 0 := fun h ↦ hw0 (Subtype.ext h)
  have hwxy : (w : K) = x + μ * y := rfl
  let yK : K := (y : K) / (w : K)
  have hint' : IsIntegral E yK := hint
  let R' : Subalgebra D K := (Algebra.adjoin E {yK}).restrictScalars D
  have hER' : IsOverring E R' := by
    refine ⟨fun z hz ↦ (Algebra.adjoin E {yK}).algebraMap_mem (⟨z, hz⟩ : E), ?_⟩
    have heq : Submodule.span E (R' : Set K) = (Algebra.adjoin E {yK}).toSubmodule :=
      Submodule.span_eq (Algebra.adjoin E {yK}).toSubmodule
    rw [heq]
    exact hint'.fg_adjoin_singleton
  have hyR' : yK ∈ R' :=
    (Subalgebra.mem_restrictScalars D).2 (Algebra.subset_adjoin (Set.mem_singleton yK))
  refine exists_admissible_of_forall_localizationAt hER' fun P' _ ↦ ?_
  have := hER'.isNoetherianRing
  have := hER'.krullDimLE
  let E' := localizationAt R' P'
  have : IsLocalRing E' := inferInstanceAs (IsLocalRing (localizationAt R' P'))
  have : IsNoetherianRing E' := inferInstanceAs (IsNoetherianRing (localizationAt R' P'))
  have : Ring.KrullDimLE 1 E' := inferInstanceAs (Ring.KrullDimLE 1 (localizationAt R' P'))
  have hEE' : E ≤ E' := hER'.le.trans (le_localizationAt R' P')
  have hU' : UnitDifferences E' :=
    unitDifferences_of_injective (Subalgebra.inclusion hEE' : E →+* E')
      (Subalgebra.inclusion_injective hEE') hU
  let W : Kˣ := Units.mk0 (w : K) hwK
  let Y : Kˣ := Units.mk0 yK (div_ne_zero y.ne_zero hwK)
  let X' : Kˣ := Units.mk0 ((x : K) / w) (div_ne_zero x.ne_zero hwK)
  have hWE' : (W : K) ∈ E' := hEE' w.2
  have hYE' : (Y : K) ∈ E' := le_localizationAt R' P' hyR'
  have hX'eq : (X' : K) = 1 - μ * (Y : K) := by
    simp only [X', Y, yK, Units.val_mk0]
    field_simp
    rw [hwxy]
    ring
  have hX'E' : (X' : K) ∈ E' := by
    rw [hX'eq]
    exact E'.sub_mem E'.one_mem (E'.mul_mem (hEE' μ.2) hYE')
  have hunit : IsUnit (⟨X', hX'E'⟩ : E') ∨ IsUnit (⟨Y, hYE'⟩ : E') := by
    have h1 : (⟨X', hX'E'⟩ : E') + Subalgebra.inclusion hEE' μ * ⟨Y, hYE'⟩ = 1 := by
      apply Subtype.ext
      simp [hX'eq]
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (h1 ▸ isUnit_one) with h | h
    · exact Or.inl h
    · exact Or.inr (isUnit_of_mul_isUnit_right h)
  have hfin : ∀ {z : E'}, z ≠ 0 → Ring.ord E' z ≠ ⊤ :=
    fun hz ↦ Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hz)
  have hfinE : ∀ {z : E}, z ≠ 0 → Ring.ord E z ≠ ⊤ :=
    fun hz ↦ Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hz)
  have hWne : (⟨W, hWE'⟩ : E') ≠ 0 := fun h ↦ W.ne_zero (congrArg Subtype.val h :)
  have hYne : (⟨Y, hYE'⟩ : E') ≠ 0 := fun h ↦ Y.ne_zero (congrArg Subtype.val h :)
  have hX'ne : (⟨X', hX'E'⟩ : E') ≠ 0 := fun h ↦ X'.ne_zero (congrArg Subtype.val h :)
  have hordb := ord_localizationAt_le hER' P' hb0
  have horda := ord_localizationAt_le hER' P' ha0
  have hpos : ∀ {z : E}, z ≠ 0 → ¬ IsUnit z → 1 ≤ (Ring.ord E z).toNat := by
    intro z hz hzu
    have h1 := ord_ne_zero_of_not_isUnit hzu
    have h2 := hfinE hz
    rw [Nat.one_le_iff_ne_zero, Ne, ENat.toNat_eq_zero]
    tauto
  have hapos := hpos ha0 hau
  have hbpos := hpos hb0 hbu
  rcases hunit with hXu | hYu
  · -- `y = W * Y` and `x = X' * W` with `X'` a unit: recurse on the pair `(W, Y)`
    have hmul : Subalgebra.inclusion (hER'.le.trans (le_localizationAt R' P')) b =
        ⟨W, hWE'⟩ * ⟨Y, hYE'⟩ := by
      apply Subtype.ext
      simp only [Subalgebra.coe_inclusion, MulMemClass.coe_mul, W, Y, yK, Units.val_mk0]
      field_simp
      rfl
    have hsum : Ring.ord E' ⟨W, hWE'⟩ + Ring.ord E' ⟨Y, hYE'⟩ ≤ Ring.ord E b := by
      rw [← Ring.ord_mul _ (mem_nonZeroDivisors_of_ne_zero hYne), ← hmul]
      exact hordb
    have hlt : (Ring.ord E' ⟨W, hWE'⟩).toNat + (Ring.ord E' ⟨Y, hYE'⟩).toNat < N := by
      rw [← ENat.toNat_add (hfin hWne) (hfin hYne)]
      have := ENat.toNat_le_toNat hsum (hfinE hb0)
      omega
    obtain ⟨C', hC'⟩ := ih _ hlt E' hU' W Y hWE' hYE' le_rfl
    refine ⟨C', hC'.isOverring, fun Q _ ↦ ?_⟩
    have hE'T : E' ≤ localizationAt C' Q := hC'.isOverring.le.trans (le_localizationAt C' Q)
    refine (hC'.factors Q).pair_of_eq
      (Units.map (Subalgebra.inclusion hE'T : E' →* _) hXu.unit) 1 ![1, 0] ![1, 1] ?_ ?_
    · ext
      simp only [Units.val_mk0, Fin.isValue, Matrix.cons_val_zero, zpow_ofNat, pow_one,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, pow_zero, mul_one, Units.val_mul,
        Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe, Subalgebra.inclusion_mk,
        Subalgebra.coe_val, X', W]
      field_simp
    · ext
      simp only [map_one, Fin.isValue, Matrix.cons_val_zero, zpow_ofNat, pow_one,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, Units.val_mul, Units.val_mk0, W,
        Y, yK]
      field_simp
  · -- `x = X' * W` and `y = Y * W` with `Y` a unit: recurse on the pair `(X', W)`
    have hmul : Subalgebra.inclusion (hER'.le.trans (le_localizationAt R' P')) a =
        ⟨X', hX'E'⟩ * ⟨W, hWE'⟩ := by
      apply Subtype.ext
      simp only [Subalgebra.coe_inclusion, MulMemClass.coe_mul, W, X', Units.val_mk0]
      field_simp
      rfl
    have hsum : Ring.ord E' ⟨X', hX'E'⟩ + Ring.ord E' ⟨W, hWE'⟩ ≤ Ring.ord E a := by
      rw [← Ring.ord_mul _ (mem_nonZeroDivisors_of_ne_zero hWne), ← hmul]
      exact horda
    have hlt : (Ring.ord E' ⟨X', hX'E'⟩).toNat + (Ring.ord E' ⟨W, hWE'⟩).toNat < N := by
      rw [← ENat.toNat_add (hfin hX'ne) (hfin hWne)]
      have := ENat.toNat_le_toNat hsum (hfinE ha0)
      omega
    obtain ⟨C', hC'⟩ := ih _ hlt E' hU' X' W hX'E' hWE' le_rfl
    refine ⟨C', hC'.isOverring, fun Q _ ↦ ?_⟩
    have hE'T : E' ≤ localizationAt C' Q := hC'.isOverring.le.trans (le_localizationAt C' Q)
    refine (hC'.factors Q).pair_of_eq 1
      (Units.map (Subalgebra.inclusion hE'T : E' →* _) hYu.unit) ![1, 1] ![0, 1] ?_ ?_
    · ext
      simp only [map_one, Fin.isValue, Matrix.cons_val_zero, zpow_ofNat, pow_one,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, Units.val_mul, Units.val_mk0, X',
        W]
      field_simp
    · ext
      simp only [Units.val_mk0, Fin.isValue, Matrix.cons_val_zero, zpow_ofNat, pow_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, pow_one, one_mul, Units.val_mul,
        Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe, Subalgebra.inclusion_mk,
        Subalgebra.coe_val, Y, yK, W]
      field_simp

/-- **Two elements (B3, Stacks 42.4.4 for `r = 2`).** Let `E` be a Noetherian local subalgebra of
`K` of dimension `≤ 1` with unit differences. For nonzero `x, y ∈ E` there is an admissible
overring of `E` for the pair `(x, y)`. -/
theorem exists_admissible_pair (E : Subalgebra D K) [IsLocalRing E] [IsNoetherianRing E]
    [Ring.KrullDimLE 1 E] (hU : UnitDifferences E) (x y : Kˣ) (hx : (x : K) ∈ E)
    (hy : (y : K) ∈ E) : ∃ C, Admissible E C ![x, y] :=
  exists_admissible_pair_aux _ E hU x y hx hy le_rfl

end Pair

section Family

open GromovWitten.AlgebraicGeometry.IntersectionTheory.VectorBundle
  (UnitDifferences unitDifferences_of_injective)

universe u

variable {D K : Type*} [CommRing D] [IsDomain D] [Field K] [Algebra D K] [IsFractionRing D K]

/-- B4 for finite families of elements of `E`, by induction on the index type. -/
private theorem exists_admissible_of_mem (ι : Type u) [Finite ι] :
    ∀ (E : Subalgebra D K) [IsLocalRing E] [IsNoetherianRing E] [Ring.KrullDimLE 1 E],
      UnitDifferences E → ∀ f : ι → Kˣ, (∀ i, (f i : K) ∈ E) → ∃ C, Admissible E C f := by
  refine Finite.induction_empty_option (P := fun ι ↦ ∀ (E : Subalgebra D K) [IsLocalRing E]
    [IsNoetherianRing E] [Ring.KrullDimLE 1 E], UnitDifferences E → ∀ f : ι → Kˣ,
      (∀ i, (f i : K) ∈ E) → ∃ C, Admissible E C f) ?_ ?_ ?_ ι
  · intro α β e h E _ _ _ hU f hf
    obtain ⟨C, hC⟩ := h E hU (f ∘ e) (fun i ↦ hf (e i))
    refine ⟨C, hC.isOverring, fun P _ ↦ ?_⟩
    have := (hC.factors P).comp e.symm
    simpa [Function.comp_def] using this
  · intro E _ _ _ _ f _
    exact ⟨E, admissible_self_of_factors (factors_of_isEmpty E f)⟩
  · intro α _ h E _ _ _ hU f hf
    obtain ⟨B, hB⟩ := h E hU (f ∘ some) (fun i ↦ hf (some i))
    refine exists_admissible_of_forall_localizationAt hB.isOverring fun P _ ↦ ?_
    have := hB.isOverring.isNoetherianRing
    have := hB.isOverring.krullDimLE
    let E' := localizationAt B P
    have : IsLocalRing E' := inferInstanceAs (IsLocalRing (localizationAt B P))
    have : IsNoetherianRing E' := inferInstanceAs (IsNoetherianRing (localizationAt B P))
    have : Ring.KrullDimLE 1 E' := inferInstanceAs (Ring.KrullDimLE 1 (localizationAt B P))
    have hEE' : E ≤ E' := hB.isOverring.le.trans (le_localizationAt B P)
    have hU' : UnitDifferences E' :=
      unitDifferences_of_injective (Subalgebra.inclusion hEE' : E →+* E')
        (Subalgebra.inclusion_injective hEE') hU
    obtain ⟨π, hπ, e, u, hu⟩ := factors_iff_units.1 (hB.factors P)
    let πK : Kˣ := Units.mk0 (π : K) hπ
    obtain ⟨C', hC'⟩ := exists_admissible_pair E' hU' πK (f none) π.2 (hEE' (hf none))
    refine ⟨C', hC'.isOverring, fun Q _ ↦ ?_⟩
    have hE'T : E' ≤ localizationAt C' Q := hC'.isOverring.le.trans (le_localizationAt C' Q)
    refine (hC'.factors Q).of_eq_mul_prod f
      (fun o ↦ o.elim 1 fun i ↦ Units.map (Subalgebra.inclusion hE'T : E' →* _) (u i))
      (fun o ↦ o.elim ![0, 1] fun i ↦ ![e i, 0]) fun o ↦ ?_
    cases o with
    | none => simp [Fin.prod_univ_two]
    | some i =>
      have hi := hu i
      simp only [Function.comp_apply] at hi
      rw [hi]
      ext
      simp [Fin.prod_univ_two, πK]

/-- **Finite families (B4, Stacks 42.4.4).** Let `E` be a Noetherian local subalgebra of `K` of
Krull dimension `≤ 1` with unit differences. Every finite family `f : ι → Kˣ` has an admissible
overring over `E`: an overring `C` of `E` such that `f` factors in the localization of `C` at
every maximal ideal. -/
theorem exists_admissible (E : Subalgebra D K) [IsLocalRing E] [IsNoetherianRing E]
    [Ring.KrullDimLE 1 E] (hU : UnitDifferences E) {ι : Type*} [Finite ι] (f : ι → Kˣ) :
    ∃ C, Admissible E C f := by
  classical
  have hnum : ∀ i, ∃ α β : D, algebraMap D K α ≠ 0 ∧ algebraMap D K β ≠ 0 ∧
      (f i : K) = algebraMap D K α / algebraMap D K β := by
    intro i
    obtain ⟨α, β, hβ, h⟩ := IsFractionRing.div_surjective (A := D) (f i : K)
    have hβ0 : algebraMap D K β ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hβ
    refine ⟨α, β, fun h0 ↦ (f i).ne_zero ?_, hβ0, h.symm⟩
    rw [← h, h0, zero_div]
  choose α β hα hβ hf using hnum
  let g : ι ⊕ ι → Kˣ := Sum.elim (fun i ↦ Units.mk0 _ (hα i)) (fun i ↦ Units.mk0 _ (hβ i))
  obtain ⟨C, hC⟩ := exists_admissible_of_mem (ι ⊕ ι) E hU g
    (fun k ↦ by cases k <;> exact E.algebraMap_mem _)
  refine ⟨C, hC.isOverring, fun P _ ↦ ?_⟩
  obtain ⟨π, hπ, e, u, hu⟩ := factors_iff_units.1 (hC.factors P)
  refine factors_iff_units.2 ⟨π, hπ, fun i ↦ e (.inl i) - e (.inr i),
    fun i ↦ u (.inl i) * (u (.inr i))⁻¹, fun i ↦ ?_⟩
  have h1 := Units.ext_iff.1 (hu (.inl i))
  have h2 := Units.ext_iff.1 (hu (.inr i))
  simp only [g, Sum.elim_inl, Sum.elim_inr, Units.val_mk0, Units.val_mul, coe_unitsToK,
    Units.val_zpow_eq_zpow_val] at h1 h2
  ext
  simp only [Units.val_mul, coe_unitsToK, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_mul,
    map_inv, Units.val_inv_eq_inv_val]
  rw [hf i, h1, h2, zpow_sub₀ hπ]
  field_simp

end Family

end GromovWitten.Algebra.Tame
