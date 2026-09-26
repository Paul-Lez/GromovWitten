/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5
-/

import GromovWitten.Algebra.OrderFiniteExtension
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The semilocal decomposition of the order of vanishing (Fulton A.2.3, Part 2)

Let `A` be a Noetherian local domain, `B` a commutative ring, module-finite over `A`. This file
proves the semilocal length formula (*Intersection Theory*, App. A.2, second part of Lemma
A.2.3): for `N` a `B`-module of finite `B`-length,

`Module.length A N = ∑ᶠ q : MaximalSpectrum B, [κ(q) : κ_A] · Module.length (B_q) (N_q)`

(`OrderSemilocal.length_eq_finsum`), where `κ(q) = q.asIdeal.ResidueField` (Mathlib's
`Ideal.ResidueField`, canonically `≃+* B ⧸ q.asIdeal` for `q` maximal), `κ_A =
IsLocalRing.ResidueField A`, `B_q = Localization.AtPrime q.asIdeal`, and `N_q = LocalizedModule
q.asIdeal.primeCompl N`. The sum ranges over `MaximalSpectrum B`, a priori infinite, but is a
genuine `finsum` (finite support, `OrderSemilocal.finite_support_summand`).

## Main declarations

* `OrderSemilocal.summand`: the `q`-summand `[κ(q):κ_A] · length (B_q) (N_q)` of the formula.
* `OrderSemilocal.length_eq_finsum`: the semilocal length formula itself, proved by induction on
  the inductive predicate `IsFiniteLength` (`induction _ using IsFiniteLength.rec`; plain
  `induction hN with` does *not* build a usable inductive hypothesis for this predicate, see the
  comment at `finite_support_summand`), reducing to the case `N` simple (`N ≅ B ⧸ q₀` for a
  maximal ideal `q₀`, `isSimpleModule_iff_quot_maximal`), handled via
  `length_residueField_eq_summand_self` and `summand_quotient_self`/`summand_quotient_ne`.
* `OrderSemilocal.isFiniteLength_smulTop`, `OrderSemilocal.length_eq_residueDegree_mul_length`:
  the two standalone ingredients from Part 1's continuation (still used internally above).

**Not proved in this file**: Fulton's Example A.3.1 (Part 3, the rank-one corollary
`Ring.ord A a = ∑ q, [κ(q):κ] · Ring.ord (B_q) a` when `Frac A = Frac B`), which additionally
needs (a) identifying `n = 1` in `OrderFiniteExtension.exists_length_quotient_smulTop_eq`'s
existential rank from the rank-one hypothesis, and (b) `LocalizedModule q.primeCompl (B ⧸ a • ⊤)
≃ (Localization.AtPrime q) ⧸ (a • ⊤)` (available in principle via
`Submodule.localizedQuotientEquiv`, `Mathlib/Algebra/Module/LocalizedModule/Submodule.lean:310`,
not yet assembled here). See the report for details.
-/

namespace OrderSemilocal

open scoped Pointwise

section Finiteness

variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [CommRing B] [Algebra A B] [Module.Finite A B]

/-- **Part of Fulton A.2.3 (finiteness).** For `B` module-finite over a Noetherian domain `A` of
Krull dimension `≤ 1`, and `a ≠ 0`, the `A`-module `B ⧸ a • B` has finite length. This needs no
torsion-freeness hypothesis on `B`: multiplication by `a` kills `B ⧸ a • B` tautologically, and
`OrderFiniteExtension.isFiniteLength_of_smul_eq_zero` (Part 1) applies directly. -/
theorem isFiniteLength_smulTop {a : A} (ha : a ≠ 0) :
    IsFiniteLength A (B ⧸ (a • (⊤ : Submodule A B))) := by
  refine OrderFiniteExtension.isFiniteLength_of_smul_eq_zero ha fun y => ?_
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective (a • (⊤ : Submodule A B)) y
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_pointwise_smul b a ⊤ Submodule.mem_top

end Finiteness

section ResidueDegree

/-- **Part of Fulton A.2.3 (residue-degree bridge).** For a local `A`-algebra `S` with `A → S` a
local homomorphism (e.g. `S = Localization.AtPrime B q` for a maximal ideal `q` of a module-finite
`A`-algebra `B`, with `A` itself local), the `A`-length of an `S`-module `N` equals its
`S`-length times the residue degree `[κ(S) : κ(A)]`. This is Mathlib's
`IsLocalRing.length_restrictScalars` combined with `Module.length_eq_finrank`. -/
theorem length_eq_residueDegree_mul_length {A S : Type*} [CommRing A] [CommRing S]
    [IsLocalRing A] [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    {N : Type*} [AddCommGroup N] [Module S N] [Module A N] [IsScalarTower A S N]
    [Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField S)] :
    Module.length A N = Module.length S N *
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField S) := by
  rw [IsLocalRing.length_restrictScalars A S N, Module.length_eq_finrank]

end ResidueDegree

section LyingOver

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B]

/-- **Lying over for a local ground ring.** If `q` is a maximal ideal of `B` and `B` is
module-finite (hence integral) over the local ring `A`, then `q` lies over the maximal ideal of
`A`: the composite `A → B → Localization.AtPrime q` is a local ring homomorphism. -/
instance isLocalHom_algebraMap_localizationAtPrime (q : Ideal B) [q.IsMaximal] :
    IsLocalHom (algebraMap A (Localization.AtPrime q)) := by
  have hmax : (q.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) q
  have heq : q.comap (algebraMap A B) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal hmax
  refine ((IsLocalRing.local_hom_TFAE (algebraMap A (Localization.AtPrime q))).out 3 0).mp ?_
  intro a ha
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A B (Localization.AtPrime q)]
  refine (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).mpr ?_
  rw [← Ideal.mem_comap, heq]
  exact ha

end LyingOver

section ResidueFieldFinite

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B]

/-- The `A`-module `B ⧸ q` is finite, for `q` any ideal of `B` (module-finite `A`-algebra):
it is a quotient of the finite `A`-module `B`. -/
instance moduleFinite_quotient (q : Ideal B) : Module.Finite A (B ⧸ q) :=
  Module.Finite.of_surjective (Submodule.mkQ (Submodule.restrictScalars A q))
    (Submodule.Quotient.mk_surjective _)

/-- **Finiteness of the residue degree.** For `q` a maximal ideal of `B` (module-finite over the
local ring `A`), the residue field `κ(q) = q.ResidueField` (Mathlib's `Ideal.ResidueField`,
canonically `≃+* B ⧸ q`) is a finite `A`-module: it is a quotient of `B ⧸ q` (which is itself
finite over `A`) along the (surjective) canonical algebra map `B ⧸ q → q.ResidueField`. -/
instance moduleFinite_residueField (q : Ideal B) [q.IsMaximal] :
    Module.Finite A q.ResidueField :=
  Module.Finite.of_surjective (IsScalarTower.toAlgHom A (B ⧸ q) q.ResidueField).toLinearMap
    (Ideal.bijective_algebraMap_quotient_residueField q).2

/-- **The residue degree `[κ(q) : κ(A)]` is finite.** For `q` a maximal ideal of `B`
(module-finite over the local ring `A`), the residue field `q.ResidueField` is a finite
`ResidueField A`-vector space: it is finite as an `A`-module (`moduleFinite_residueField`), and
finiteness passes to the intermediate ring `ResidueField A` in the scalar tower
`A → ResidueField A → q.ResidueField`. -/
instance moduleFinite_residueField_over_base (q : Ideal B) [q.IsMaximal] :
    Module.Finite (IsLocalRing.ResidueField A) q.ResidueField :=
  Module.Finite.of_restrictScalars_finite A (IsLocalRing.ResidueField A) q.ResidueField

end ResidueFieldFinite

section SimpleModuleLocalization

variable {B : Type*} [CommRing B]

attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- The residue field `q.ResidueField` is simple as a module over `Localization.AtPrime q`:
it is literally the quotient of that local ring by its maximal ideal. -/
instance isSimpleModule_residueField (q : Ideal B) [q.IsMaximal] :
    IsSimpleModule (Localization.AtPrime q) q.ResidueField :=
  isSimpleModule_iff_quot_maximal.mpr
    ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩

/-- **The `q`-localised length of `κ(q)` at itself is `1`.** Localising the residue field
`q.ResidueField` further at `q.primeCompl` changes nothing (every element of `q.primeCompl`
already acts invertibly on the field `q.ResidueField`, `isLocalizedModule_id`), so the localised
module is linearly equivalent to (hence has the same length as) `q.ResidueField` itself, a
simple `Localization.AtPrime q`-module. -/
theorem length_localizedModule_residueField_self (q : Ideal B) [q.IsMaximal] :
    Module.length (Localization.AtPrime q) (LocalizedModule q.primeCompl q.ResidueField) = 1 := by
  have := isLocalizedModule_id q.primeCompl q.ResidueField (Localization.AtPrime q)
  have e : LocalizedModule q.primeCompl q.ResidueField ≃ₗ[Localization.AtPrime q]
      q.ResidueField :=
    (IsLocalizedModule.linearEquiv q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl q.ResidueField)
      (LinearMap.id : q.ResidueField →ₗ[B] q.ResidueField)).extendScalarsOfIsLocalization
      q.primeCompl (Localization.AtPrime q)
  rw [e.length_eq, Module.length_eq_one]

/-- **Vanishing away from `q`.** For `q ≠ q'` both maximal ideals of `B`, localising the residue
field `κ(q)` at `q'.primeCompl` kills everything: distinct maximal ideals are never comparable,
so some element `x ∈ q \ q'` becomes invertible in the localisation while already acting as `0`
on `κ(q)` (`Ideal.algebraMap_residueField_eq_zero`), forcing every localised element to vanish. -/
theorem subsingleton_localizedModule_residueField_of_ne (q q' : Ideal B) [q.IsMaximal]
    [q'.IsMaximal] (h : q ≠ q') :
    Subsingleton (LocalizedModule q'.primeCompl q.ResidueField) := by
  have hnle : ¬ q ≤ q' := fun hle => h (‹q.IsMaximal›.eq_of_le ‹q'.IsMaximal›.ne_top hle)
  simp only [SetLike.le_def, not_forall] at hnle
  obtain ⟨x, hxq, hxq'⟩ := hnle
  have hx0 : algebraMap B q.ResidueField x = 0 := Ideal.algebraMap_residueField_eq_zero.mpr hxq
  have hkill : ∀ y : LocalizedModule q'.primeCompl q.ResidueField, x • y = 0 := by
    intro y
    induction y using LocalizedModule.induction_on with
    | h m s =>
      rw [LocalizedModule.smul'_mk]
      have : x • m = 0 := by rw [Algebra.smul_def, hx0, zero_mul]
      rw [this, LocalizedModule.zero_mk]
  refine ⟨fun y z => ?_⟩
  have hy : y - z = 0 :=
    LocalizedModule.eq_zero_of_smul_eq_zero x hxq' (y - z) (by
      rw [smul_sub, hkill, hkill, sub_zero])
  exact sub_eq_zero.mp hy

end SimpleModuleLocalization

section Devissage

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B]

attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- The `q`-summand of the semilocal length formula (Fulton A.2.3, Part 2):
`[κ(q) : κ_A] · length_{B_q}(N_q)`. -/
noncomputable def summand (N : Type*) [AddCommGroup N] [Module B N] (q : MaximalSpectrum B) :
    ℕ∞ :=
  (Module.finrank (IsLocalRing.ResidueField A) q.asIdeal.ResidueField : ℕ∞) *
    Module.length (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl N)

/-- **Pointwise additivity of `summand` in short exact sequences.** For a short exact sequence
`0 → N' → N → N'' → 0` of `B`-modules, `summand N q = summand N' q + summand N'' q` for every
maximal ideal `q`: localisation is an exact functor (`LocalizedModule.map_injective/_surjective/
_exact`), and `Module.length` is additive on exact sequences (`Module.length_eq_add_of_exact`);
`LocalizedModule.map S (-)` is already `Localization S`-linear (`= Localization.AtPrime q.asIdeal`
by definition) by construction, so no further scalar-extension step is needed. -/
theorem summand_add_of_exact {N' N N'' : Type*} [AddCommGroup N'] [Module B N']
    [AddCommGroup N] [Module B N] [AddCommGroup N''] [Module B N'']
    (f : N' →ₗ[B] N) (g : N →ₗ[B] N'') (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (q : MaximalSpectrum B) :
    summand (A := A) N q = summand (A := A) N' q + summand (A := A) N'' q := by
  unfold summand
  rw [← mul_add]
  congr 1
  set S := q.asIdeal.primeCompl with hS
  set R' := Localization.AtPrime q.asIdeal with hR'
  set F : LocalizedModule S N' →ₗ[R'] LocalizedModule S N :=
    (LocalizedModule.map S f).extendScalarsOfIsLocalization S R' with hF
  set G : LocalizedModule S N →ₗ[R'] LocalizedModule S N'' :=
    (LocalizedModule.map S g).extendScalarsOfIsLocalization S R' with hG
  have hFfun : (F : LocalizedModule S N' → LocalizedModule S N) = LocalizedModule.map S f := rfl
  have hGfun : (G : LocalizedModule S N → LocalizedModule S N'') = LocalizedModule.map S g := rfl
  have hF' : Function.Injective F := hFfun ▸ LocalizedModule.map_injective S f hf
  have hG' : Function.Surjective G := hGfun ▸ LocalizedModule.map_surjective S g hg
  have hex' : Function.Exact F G := by
    rw [Function.Exact, hFfun, hGfun]
    exact LocalizedModule.map_exact S f g hex
  exact Module.length_eq_add_of_exact F G hF' hG' hex'

/-- `summand` only depends on `N` up to `B`-linear equivalence. -/
theorem summand_congr {N N' : Type*} [AddCommGroup N] [Module B N] [AddCommGroup N']
    [Module B N'] (e : N ≃ₗ[B] N') (q : MaximalSpectrum B) :
    summand (A := A) N q = summand (A := A) N' q := by
  unfold summand
  congr 1
  set S := q.asIdeal.primeCompl with hS
  set φ : LocalizedModule S N →ₗ[Localization S] LocalizedModule S N' :=
    LocalizedModule.map S e.toLinearMap with hφ
  have hbij : Function.Bijective φ :=
    ⟨LocalizedModule.map_injective S e.toLinearMap e.injective,
      LocalizedModule.map_surjective S e.toLinearMap e.surjective⟩
  exact (LinearEquiv.ofBijective φ hbij).length_eq

/-- The canonical `B`-linear equivalence `B ⧸ q₀ ≃ₗ[B] q₀.ResidueField`, for `q₀` maximal. -/
noncomputable def quotientResidueFieldEquiv (q₀ : Ideal B) [q₀.IsMaximal] :
    (B ⧸ q₀) ≃ₗ[B] q₀.ResidueField :=
  LinearEquiv.ofBijective (IsScalarTower.toAlgHom B (B ⧸ q₀) q₀.ResidueField).toLinearMap
    (Ideal.bijective_algebraMap_quotient_residueField q₀)

/-- **The simple-quotient case, at the point `q₀` itself.** -/
theorem summand_quotient_self (q₀ : Ideal B) [hq₀ : q₀.IsMaximal] :
    summand (A := A) (B ⧸ q₀) (⟨q₀, hq₀⟩ : MaximalSpectrum B) =
      (Module.finrank (IsLocalRing.ResidueField A) q₀.ResidueField : ℕ∞) := by
  rw [summand_congr (A := A) (quotientResidueFieldEquiv q₀)]
  unfold summand
  rw [length_localizedModule_residueField_self, mul_one]

/-- **The simple-quotient case, away from `q₀`.** -/
theorem summand_quotient_ne (q₀ : Ideal B) [q₀.IsMaximal] (q : MaximalSpectrum B)
    (h : q.asIdeal ≠ q₀) : summand (A := A) (B ⧸ q₀) q = 0 := by
  rw [summand_congr (A := A) (quotientResidueFieldEquiv q₀)]
  have := subsingleton_localizedModule_residueField_of_ne q₀ q.asIdeal h.symm
  unfold summand
  rw [Module.length_eq_zero, mul_zero]

/-- `summand` vanishes identically on a subsingleton module. -/
theorem summand_eq_zero_of_subsingleton {N : Type*} [AddCommGroup N] [Module B N]
    [Subsingleton N] (q : MaximalSpectrum B) : summand (A := A) N q = 0 := by
  unfold summand
  have : Subsingleton (LocalizedModule q.asIdeal.primeCompl N) := by
    refine ⟨fun x y => ?_⟩
    induction x using LocalizedModule.induction_on with
    | h m s =>
      induction y using LocalizedModule.induction_on with
      | h m' s' =>
        have hm : m = 0 := Subsingleton.elim m 0
        have hm' : m' = 0 := Subsingleton.elim m' 0
        rw [hm, hm', LocalizedModule.zero_mk, LocalizedModule.zero_mk]
  rw [Module.length_eq_zero, mul_zero]

/-- **Finiteness of the support of `summand N`, for `N` of finite `B`-length.** By induction on
the inductive `IsFiniteLength` predicate: `N` subsingleton contributes the empty (finite)
support; and for `M` with a submodule `T` such that `M ⧸ T` is simple, `summand M = summand T +
summand (M ⧸ T)` pointwise (`summand_add_of_exact`), and `M ⧸ T ≅ B ⧸ q₀` for a single maximal
ideal `q₀` (`isSimpleModule_iff_quot_maximal`) has support `⊆ {q₀}` (`summand_quotient_ne`), so
`support (summand M) ⊆ support (summand T) ∪ {q₀}` is a union of two finite sets. -/
theorem finite_support_summand {N : Type*} [AddCommGroup N] [Module B N]
    (hN : IsFiniteLength B N) : (Function.support (summand (A := A) (B := B) N)).Finite := by
  induction hN using IsFiniteLength.rec with
  | of_subsingleton =>
    apply Set.Finite.subset Set.finite_empty
    intro q hq
    exact absurd (summand_eq_zero_of_subsingleton (A := A) q) hq
  | @of_simple_quotient M _ _ T hT _ ih =>
    have hkey : ∀ q, summand (A := A) M q = summand (A := A) T q + summand (A := A) (M ⧸ T) q :=
      fun q => summand_add_of_exact (A := A) T.subtype T.mkQ (Submodule.subtype_injective _)
        (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _) q
    obtain ⟨q₀, hq₀, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hT
    have hquot : (Function.support (summand (A := A) (B := B) (M ⧸ T))).Finite := by
      apply Set.Finite.subset (Set.finite_singleton (⟨q₀, hq₀⟩ : MaximalSpectrum B))
      intro q hq
      rw [Set.mem_singleton_iff]
      by_contra hne
      exact hq (by
        rw [summand_congr (A := A) e]
        exact summand_quotient_ne (A := A) q₀ q fun heq => hne (MaximalSpectrum.ext heq))
    apply Set.Finite.subset (ih.union hquot)
    intro q hq
    have hq' : summand (A := A) T q + summand (A := A) (M ⧸ T) q ≠ 0 := hkey q ▸ hq
    rw [Set.mem_union]
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    simp only [Function.mem_support, ne_eq, not_not] at h1 h2
    exact hq' (by rw [h1, h2, add_zero])

/-- **The `A`-length of `κ(q₀)` equals its own `q₀`-summand.** Combines
`length_eq_residueDegree_mul_length` (with `S = Localization.AtPrime q₀`) and the fact that
`q₀.ResidueField` is simple over `Localization.AtPrime q₀` (`isSimpleModule_residueField`,
length `1`) with `length_localizedModule_residueField_self` (also `1`), so both sides reduce to
the residue degree `finrank κ_A κ(q₀)`. -/
theorem length_residueField_eq_summand_self (q₀ : Ideal B) [hq₀ : q₀.IsMaximal] :
    Module.length A q₀.ResidueField =
      summand (A := A) q₀.ResidueField (⟨q₀, hq₀⟩ : MaximalSpectrum B) := by
  have hL := length_eq_residueDegree_mul_length (A := A) (S := Localization.AtPrime q₀)
    (N := q₀.ResidueField)
  rw [Module.length_eq_one (R := Localization.AtPrime q₀) (M := q₀.ResidueField)] at hL
  rw [hL]
  unfold summand
  rw [length_localizedModule_residueField_self, mul_one, one_mul]

/-- `summand N` has finite support when `N` is simple as a `B`-module: it is transported, via
`isSimpleModule_iff_quot_maximal`, to the quotient-by-a-maximal-ideal case
(`summand_quotient_ne`), whose support is contained in the singleton of that maximal ideal. -/
theorem finite_support_summand_of_simple {N : Type*} [AddCommGroup N] [Module B N]
    [IsSimpleModule B N] : (Function.support (summand (A := A) (B := B) N)).Finite := by
  obtain ⟨q₀, hq₀, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule B N›
  apply Set.Finite.subset (Set.finite_singleton (⟨q₀, hq₀⟩ : MaximalSpectrum B))
  intro q hq
  rw [Set.mem_singleton_iff]
  by_contra hne
  exact hq (by
    rw [summand_congr (A := A) e]
    exact summand_quotient_ne (A := A) q₀ q fun heq => hne (MaximalSpectrum.ext heq))

set_option maxHeartbeats 1000000 in
-- The manual `IsScalarTower`/`restrictScalars` bookkeeping in the inductive step below is
-- expensive for the elaborator to unify; raise the heartbeat limit for this one proof.
/-- **Fulton A.2.3, Part 2 (the semilocal length formula).** For `B` module-finite over the
Noetherian local domain `A` and `N` a `B`-module of finite `B`-length (equipped with a
compatible `A`-module structure, `IsScalarTower A B N`),
`Module.length A N = ∑ᶠ q : MaximalSpectrum B, [κ(q) : κ_A] · length_{B_q}(N_q)`.

Proved by induction on the inductive predicate `IsFiniteLength` (`induction _ using
IsFiniteLength.rec`, needed for the tactic to build a genuine inductive hypothesis for the
recursive premise here): `N` subsingleton is the base case (both sides `0`,
`finsum_eq_zero_of_forall_eq_zero`); for `M` with a submodule `T` such that `M ⧸ T` is simple,
`Module.length A M = Module.length A T + Module.length A (M ⧸ T)`
(`Module.length_eq_add_of_exact`, restricting scalars of `T.subtype`/`T.mkQ` to `A` via the
`A`-module structures on `↥T`/`M ⧸ T` induced by `Submodule.restrictScalars A T`), the term for
`T` is the inductive hypothesis, and the term for the simple quotient `M ⧸ T ≃ₗ[B] B ⧸ q₀`
reduces (`length_residueField_eq_summand_self`, `summand_quotient_self`) to a single summand at
`q₀`, matching `∑ᶠ q, summand (M ⧸ T) q` (`finsum_eq_single`, using
`finite_support_summand_of_simple` for finiteness). -/
theorem length_eq_finsum {N : Type*} [AddCommGroup N] [Module B N] (hN : IsFiniteLength B N) :
    ∀ [Module A N] [IsScalarTower A B N],
      Module.length A N = ∑ᶠ q : MaximalSpectrum B, summand (A := A) N q := by
  induction hN using IsFiniteLength.rec with
  | of_subsingleton =>
    intro _ _
    rw [Module.length_eq_zero]
    exact (finsum_eq_zero_of_forall_eq_zero (summand_eq_zero_of_subsingleton (A := A))).symm
  | @of_simple_quotient M _ _ T hT hFT ih =>
    intro _ _
    have hSTT : IsScalarTower A B T :=
      ⟨fun a b x => Subtype.ext (by
        rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower,
          Submodule.coe_smul_of_tower, smul_assoc])⟩
    have hSTQ : IsScalarTower A B (M ⧸ T) :=
      ⟨fun a b x => Submodule.Quotient.induction_on T x fun m => by
        rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
          ← Submodule.Quotient.mk_smul, smul_assoc]⟩
    have hLHS : Module.length A M = Module.length A T + Module.length A (M ⧸ T) :=
      Module.length_eq_add_of_exact (LinearMap.restrictScalars A (Submodule.subtype T))
        (LinearMap.restrictScalars A (Submodule.mkQ T)) (Submodule.subtype_injective _)
        (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ T)
    obtain ⟨q₀, hq₀, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hT
    have hRHS_MT : Module.length A (M ⧸ T) = ∑ᶠ q, summand (A := A) (B := B) (M ⧸ T) q := by
      have h1 : Module.length A (M ⧸ T) = Module.length A (B ⧸ q₀) :=
        (e.restrictScalars A).length_eq
      have h2 : Module.length A (B ⧸ q₀) =
          summand (A := A) q₀.ResidueField (⟨q₀, hq₀⟩ : MaximalSpectrum B) := by
        rw [((quotientResidueFieldEquiv q₀).restrictScalars A).length_eq]
        exact length_residueField_eq_summand_self q₀
      have h3 : summand (A := A) q₀.ResidueField (⟨q₀, hq₀⟩ : MaximalSpectrum B) =
          summand (A := A) (M ⧸ T) (⟨q₀, hq₀⟩ : MaximalSpectrum B) :=
        (summand_congr (A := A) (e.trans (quotientResidueFieldEquiv q₀))
          (⟨q₀, hq₀⟩ : MaximalSpectrum B)).symm
      have h4 : ∑ᶠ q, summand (A := A) (B := B) (M ⧸ T) q =
          summand (A := A) (M ⧸ T) (⟨q₀, hq₀⟩ : MaximalSpectrum B) := by
        apply finsum_eq_single
        intro q hq
        rw [summand_congr (A := A) e]
        exact summand_quotient_ne (A := A) q₀ q fun heq => hq (MaximalSpectrum.ext heq)
      rw [h1, h2, h3, h4]
    have hkey : ∀ q, summand (A := A) M q = summand (A := A) T q + summand (A := A) (M ⧸ T) q :=
      fun q => summand_add_of_exact (A := A) T.subtype T.mkQ (Submodule.subtype_injective _)
        (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ T) q
    rw [hLHS, ih, hRHS_MT,
      ← finsum_add_distrib (finite_support_summand (A := A) hFT)
        finite_support_summand_of_simple]
    exact (finsum_congr hkey).symm

end Devissage

end OrderSemilocal


