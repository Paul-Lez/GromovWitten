/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleSectionGysin
import GromovWitten.AlgebraicGeometry.Cones.NormalConeDimension

/-!
# The symmetric local identity for the Gysin map of a section

This file completes the proof of statement (B) of the injectivity programme for the flat
pullback along a trivial line bundle: it derives the cycle-level identity which was left as an
explicit hypothesis `hident` of
`GromovWitten.AlgebraicGeometry.IntersectionTheory.VectorBundle.sectionGysin_elementGenerator_mem`
from Fulton's symmetric local identity in a two-dimensional local domain,
`VectorBundle.LocalOrdSymmetry`.

## Contents

* `VectorBundle.SectionGysinIdentity`: the commutative-algebra preliminaries.  `Ring.ord` is
  invariant under ring isomorphisms (`ring_ord_ringEquiv`) and under the identifications of
  localisations and of quotients of localisations that occur below (`ring_ord_atPrime`,
  `ring_ord_quotient_atPrime`, `ring_ord_atPrime_congr`, `ring_ord_quot_quot`); the dimension
  formula gives catenarity in the only case needed (`height_eq_two`, `height_eq_two_ambient`)
  and a chain of three primes forces height at least three (`three_le_height_of_chain`).
* `VectorBundle.scheme_ord_eq_localization`: the order of vanishing of a global section of an
  integral Noetherian affine scheme at a codimension-one point is the length-theoretic order of
  vanishing in the localisation of the coordinate ring at that point.
* `VectorBundle.quotPointMap`: the points of a closed subvariety `V(P)` of the total space,
  indexed by the primes of `R[T] ⧸ P`; `VectorBundle.divisor_apply_eq_ringOrd` computes the
  coefficient of the divisor of `a` on `V(P)` at such a point.
* `VectorBundle.symTerm`: the summands of Fulton's symmetric local identity, and
  `VectorBundle.localOrdSymmetry_symTerm`, which restates `LocalOrdSymmetry` with them.
* `VectorBundle.termProduct_eq_zero_of_chain_failure`, `VectorBundle.exists_nat_termProduct`:
  the termwise comparison of the two cycle-level sums with the two sums of the local identity.
* `VectorBundle.sectionGysin_elementGenerator_eq_finsum`: the cycle-level symmetric identity,
  which is the hypothesis `hident` of `VectorBundle.sectionGysin_elementGenerator_mem`.
* `VectorBundle.sectionGysin_elementGenerator_mem'`: statement (B) of the injectivity
  programme, with `hident` discharged.

## Hypotheses taken as arguments

`hsym : VectorBundle.LocalOrdSymmetry` is proved in a companion file which cannot be imported
here (it is written concurrently), so it appears as an explicit hypothesis of the two main
theorems.  `hdim : ∀ P prime, HasDimensionFormula (Polynomial R ⧸ P)` is the dimension formula
for all prime quotients of `R[T]`; it supplies the catenarity used to show that no point
contributes when the local chain condition fails.  No other hypothesis is assumed, and there is
no `sorry` and no new axiom.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace VectorBundle

/-! ## Evaluation of a finite sum of cycles -/

/-- Evaluation of an algebraic cycle at a point, as an additive homomorphism. -/
noncomputable def evalCycleHom (X : Scheme.{u}) (x : X) : AlgebraicCycle X ℚ →+ ℚ where
  toFun z := (z : X → ℚ) x
  map_zero' := rfl
  map_add' z w := by
    change ((z + w : AlgebraicCycle X ℚ) : X → ℚ) x = _
    rw [Function.locallyFinsuppWithin.coe_add]
    rfl

/-- The coefficient of a finite sum of algebraic cycles is the sum of the coefficients. -/
theorem finsum_cycle_apply {X : Scheme.{u}} {ι : Type*} (F : ι → AlgebraicCycle X ℚ)
    (hF : (Function.support F).Finite) (x : X) :
    ((∑ᶠ i, F i : AlgebraicCycle X ℚ) : X → ℚ) x = ∑ᶠ i, ((F i : X → ℚ) x) :=
  (evalCycleHom X x).map_finsum hF

/-! ## Commutative-algebra preliminaries

The order of vanishing `Ring.ord` is invariant under ring isomorphisms and under the
various identifications of localisations that occur below, and the dimension formula
supplies the catenarity statement which controls which points can contribute.
-/

namespace SectionGysinIdentity

/-- `Ring.ord` is invariant under a ring isomorphism. -/
theorem ring_ord_ringEquiv {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) (x : A) :
    Ring.ord B (e x) = Ring.ord A x := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  have hsurj : Function.Surjective (algebraMap A B) := e.surjective
  have hmap : Ideal.map (e : A →+* B) (Ideal.span {x}) = Ideal.span {e x} := by
    rw [Ideal.map_span]; simp
  let f : A ⧸ Ideal.span {x} ≃+* B ⧸ Ideal.span {e x} :=
    Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e hmap.symm
  let fl : (A ⧸ Ideal.span {x}) ≃ₗ[A] (B ⧸ Ideal.span {e x}) :=
    { f with
      map_smul' := by
        intro a y
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
        change f (Ideal.Quotient.mk _ (a * c)) = a • f (Ideal.Quotient.mk _ c)
        simp only [f, Ideal.quotientEquiv_mk, map_mul]
        rfl }
  calc Ring.ord B (e x) = Module.length B (B ⧸ Ideal.span {e x}) := rfl
    _ = Module.length A (B ⧸ Ideal.span {e x}) := (Module.length_eq_of_surjective hsurj).symm
    _ = Module.length A (A ⧸ Ideal.span {x}) := fl.length_eq.symm
    _ = Ring.ord A x := rfl

/-- The order of vanishing computed in an arbitrary localisation at a prime agrees with the one
computed in `Localization.AtPrime`. -/
theorem ring_ord_atPrime {D : Type u} [CommRing D] (q : Ideal D) [q.IsPrime]
    (S : Type u) [CommRing S] [Algebra D S] [IsLocalization.AtPrime S q] (b : D) :
    Ring.ord S (algebraMap D S b) =
      Ring.ord (Localization.AtPrime q) (algebraMap D (Localization.AtPrime q) b) := by
  let e : S ≃ₐ[D] Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl S (Localization.AtPrime q)
  have he : e.toRingEquiv (algebraMap D S b) = algebraMap D (Localization.AtPrime q) b :=
    e.commutes b
  rw [← ring_ord_ringEquiv e.toRingEquiv (algebraMap D S b), he]

/-- The image of a prime `Q` containing `q` under the quotient map by `q` is again prime. -/
theorem map_quotient_isPrime {D : Type u} [CommRing D] (q Q : Ideal D) [Q.IsPrime]
    (hqQ : q ≤ Q) : (Q.map (Ideal.Quotient.mk q)).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])

/-- The image of the complement of a prime `Q` under the quotient by a smaller prime `q` is the
complement of `Q ⧸ q`. -/
theorem map_primeCompl_eq {D : Type u} [CommRing D] (q Q : Ideal D) [Q.IsPrime]
    [(Q.map (Ideal.Quotient.mk q)).IsPrime] (hqQ : q ≤ Q) :
    Submonoid.map (Ideal.Quotient.mk q : D →+* D ⧸ q) Q.primeCompl =
      (Q.map (Ideal.Quotient.mk q)).primeCompl := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · rintro ⟨c, hc, hca⟩
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_quotient_iff_mem hqQ]
    intro ha
    refine hc ?_
    have : a - c ∈ q := Ideal.Quotient.eq.mp hca.symm
    simpa using Q.sub_mem ha (hqQ this)
  · intro hx
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_quotient_iff_mem hqQ] at hx
    exact ⟨a, hx, rfl⟩

/-- The quotient of the localisation of `D` at `Q` by the extension of a smaller prime `q` is a
localisation of `D ⧸ q` at `Q ⧸ q`. -/
theorem isLocalization_quotient_localization {D : Type u} [CommRing D] (q Q : Ideal D)
    [Q.IsPrime] [(Q.map (Ideal.Quotient.mk q)).IsPrime] (hqQ : q ≤ Q) :
    IsLocalization.AtPrime
      (Localization.AtPrime Q ⧸ q.map (algebraMap D (Localization.AtPrime Q)))
      (Q.map (Ideal.Quotient.mk q)) := by
  have h : Algebra.algebraMapSubmonoid (D ⧸ q) Q.primeCompl
      = (Q.map (Ideal.Quotient.mk q)).primeCompl := map_primeCompl_eq q Q hqQ
  change IsLocalization (Q.map (Ideal.Quotient.mk q)).primeCompl _
  rw [← h]
  infer_instance

/-- The key identification: the order of vanishing of the image of `b` in any localisation of
`D ⧸ q` at `Q ⧸ q` equals the order of vanishing in `D_Q ⧸ q D_Q`. -/
theorem ring_ord_quotient_atPrime {D : Type u} [CommRing D] (q Q : Ideal D) [q.IsPrime]
    [Q.IsPrime] [(Q.map (Ideal.Quotient.mk q)).IsPrime] (hqQ : q ≤ Q)
    (S : Type u) [CommRing S] [Algebra (D ⧸ q) S]
    [IsLocalization.AtPrime S (Q.map (Ideal.Quotient.mk q))] (b : D) :
    Ring.ord S (algebraMap (D ⧸ q) S (Ideal.Quotient.mk q b)) =
      Ring.ord (Localization.AtPrime Q ⧸ q.map (algebraMap D (Localization.AtPrime Q)))
        (Ideal.Quotient.mk _ (algebraMap D (Localization.AtPrime Q) b)) := by
  let _ := isLocalization_quotient_localization q Q hqQ
  let e : S ≃ₐ[D ⧸ q]
      (Localization.AtPrime Q ⧸ q.map (algebraMap D (Localization.AtPrime Q))) :=
    IsLocalization.algEquiv (Q.map (Ideal.Quotient.mk q)).primeCompl S _
  have he : e.toRingEquiv (algebraMap (D ⧸ q) S (Ideal.Quotient.mk q b)) =
      Ideal.Quotient.mk _ (algebraMap D (Localization.AtPrime Q) b) :=
    e.commutes (Ideal.Quotient.mk q b)
  rw [← ring_ord_ringEquiv e.toRingEquiv (algebraMap (D ⧸ q) S (Ideal.Quotient.mk q b)), he]

/-- A Noetherian ring satisfying the dimension formula has finite Krull dimension: the formula
at a maximal ideal `m` gives `dim A = ht m`, which is finite by Krull's height theorem. -/
theorem ringKrullDim_ne_top {A : Type u} [CommRing A] [IsNoetherianRing A] [Nontrivial A]
    (hA : HasDimensionFormula A) : ringKrullDim A ≠ ⊤ := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let _ : m.IsPrime := hm.isPrime
  have hfm := hA m inferInstance
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  rw [ringKrullDim_eq_zero_of_field, zero_add] at hfm
  rw [← hfm, ← WithBot.coe_top]
  exact fun h ↦ Ideal.height_ne_top_of_isPrime (I := m) (WithBot.coe_inj.mp h)

/-- Transport of the dimension formula along a ring isomorphism. -/
theorem hasDimensionFormula_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    (hA : HasDimensionFormula A) : HasDimensionFormula B := by
  intro p hp
  let _ : (p.comap e).IsPrime := hp.comap _
  have h := hA (p.comap e) inferInstance
  have hquot : ringKrullDim (A ⧸ p.comap e) = ringKrullDim (B ⧸ p) :=
    ringKrullDim_eq_of_ringEquiv
      (Ideal.quotientEquiv _ _ e (Ideal.map_comap_of_surjective _ e.surjective p).symm)
  rw [hquot, RingEquiv.height_comap, ringKrullDim_eq_of_ringEquiv e] at h
  exact h

/-- Catenarity in the only case we need: if `q < Q` are primes with `ht q = 1` and
`ht (Q ⧸ q) = 1`, and the dimension formula holds for `A` and for `A ⧸ q`, then `ht Q = 2`. -/
theorem height_eq_two {A : Type u} [CommRing A] [IsNoetherianRing A] [Nontrivial A]
    (hA : HasDimensionFormula A) (q Q : Ideal A) [q.IsPrime] [Q.IsPrime]
    (hAq : HasDimensionFormula (A ⧸ q)) (hq : q.height = 1)
    (hQq : (Q.map (Ideal.Quotient.mk q)).height = 1) (hqQ : q ≤ Q) :
    Q.height = 2 := by
  let _ : (Q.map (Ideal.Quotient.mk q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hQ := hA Q inferInstance
  have hqf := hA q inferInstance
  have hquot := hAq (Q.map (Ideal.Quotient.mk q)) inferInstance
  have hiso : ringKrullDim ((A ⧸ q) ⧸ Q.map (Ideal.Quotient.mk q)) = ringKrullDim (A ⧸ Q) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hqQ)
  rw [hq] at hqf
  rw [hQq, hiso] at hquot
  have key : ringKrullDim (A ⧸ Q) + ((1 : ℕ∞) : WithBot ℕ∞) + ((1 : ℕ∞) : WithBot ℕ∞) =
      ringKrullDim A := by rw [hquot]; exact hqf
  let _ : Nontrivial (A ⧸ Q) := Ideal.Quotient.nontrivial_iff.mpr (‹Q.IsPrime›.ne_top)
  obtain ⟨d, hd⟩ : ∃ d : ℕ∞, (d : WithBot ℕ∞) = ringKrullDim (A ⧸ Q) :=
    WithBot.ne_bot_iff_exists.mp (ne_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe _)
      (ringKrullDim_nonneg_of_nontrivial (R := A ⧸ Q))))
  have hle : ringKrullDim (A ⧸ Q) ≤ ringKrullDim A := ringKrullDim_quotient_le Q
  have hdtop : d ≠ ⊤ := by
    intro h
    rw [← hd, h, WithBot.coe_top] at hle
    exact ringKrullDim_ne_top hA (top_le_iff.mp hle)
  have hcancel : d + (1 + 1 : ℕ∞) = d + Q.height := by
    refine WithBot.coe_inj.mp ?_
    rw [WithBot.coe_add, WithBot.coe_add, WithBot.coe_add, hd, ← add_assoc, key, hQ]
  have hfinal := WithTop.add_left_cancel hdtop hcancel
  rw [← hfinal]
  norm_num

/-- A chain of four distinct primes below `Q` forces `3 ≤ ht Q`. -/
theorem three_le_height_of_chain {A : Type u} [CommRing A] [IsDomain A]
    (q' q'' Q : Ideal A) [q'.IsPrime] [q''.IsPrime] [Q.IsPrime]
    (h0 : ⊥ < q') (h1 : q' < q'') (h2 : q'' < Q) : 3 ≤ Q.height := by
  let _ : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  have e0 : (⊥ : Ideal A).height = 0 := Ideal.height_eq_zero_iff_eq_bot.mpr rfl
  have s0 : (1 : ℕ∞) ≤ q'.height := by
    simpa [e0] using Ideal.height_add_one_le_of_lt_of_isPrime h0
  have s1 : (2 : ℕ∞) ≤ q''.height := by
    have hstep : (1 : ℕ∞) + 1 ≤ q'.height + 1 := by gcongr
    exact le_trans (le_trans (by norm_num : (2 : ℕ∞) ≤ 1 + 1) hstep)
      (Ideal.height_add_one_le_of_lt_of_isPrime h1)
  have hstep : (2 : ℕ∞) + 1 ≤ q''.height + 1 := by gcongr
  exact le_trans (le_trans (by norm_num : (3 : ℕ∞) ≤ 2 + 1) hstep)
    (Ideal.height_add_one_le_of_lt_of_isPrime h2)

/-- A ring isomorphism carries the complement of a prime onto the complement of its image. -/
theorem map_primeCompl_ringEquiv {A A' : Type u} [CommRing A] [CommRing A'] (e : A ≃+* A')
    (p : Ideal A) [p.IsPrime] [(p.map (e : A →+* A')).IsPrime] :
    Submonoid.map (e : A →+* A') p.primeCompl = (p.map (e : A →+* A')).primeCompl := by
  have hmem : ∀ a : A, (e a ∈ Ideal.map (e : A →+* A') p) ↔ a ∈ p := by
    intro a
    rw [Ideal.map_comap_of_equiv e]
    simp
  ext x
  obtain ⟨a, rfl⟩ := e.surjective x
  constructor
  · rintro ⟨c, hc, hce⟩
    have hca : c = a := e.injective hce
    subst hca
    exact fun h => hc ((hmem c).mp h)
  · intro ha
    exact ⟨a, fun h => ha ((hmem a).mpr h), rfl⟩

/-- Transport of `Ring.ord` in a localisation at a prime along a ring isomorphism of the base,
in the form where the target prime is given together with an identification. -/
theorem ring_ord_atPrime_congr' {A A' : Type u} [CommRing A] [CommRing A'] (e : A ≃+* A')
    (p : Ideal A) [p.IsPrime] (p' : Ideal A') [p'.IsPrime] (hp : p.map (e : A →+* A') = p')
    (b : A) :
    Ring.ord (Localization.AtPrime p') (algebraMap A' (Localization.AtPrime p') (e b)) =
      Ring.ord (Localization.AtPrime p) (algebraMap A (Localization.AtPrime p) b) := by
  subst hp
  have H : Submonoid.map (e : A ≃* A').toMonoidHom p.primeCompl
      = (p.map (e : A →+* A')).primeCompl := map_primeCompl_ringEquiv e p
  let f : Localization.AtPrime p ≃+* Localization.AtPrime (p.map (e : A →+* A')) :=
    IsLocalization.ringEquivOfRingEquiv _ _ e H
  have hf : f (algebraMap A (Localization.AtPrime p) b) =
      algebraMap A' (Localization.AtPrime (p.map (e : A →+* A'))) (e b) :=
    IsLocalization.ringEquivOfRingEquiv_eq H b
  rw [← hf]
  exact ring_ord_ringEquiv f _

/-- Transport of `Ring.ord` in a localisation at a prime along a ring isomorphism of the base. -/
theorem ring_ord_atPrime_congr {A A' : Type u} [CommRing A] [CommRing A'] (e : A ≃+* A')
    (p : Ideal A) [p.IsPrime] [(p.map (e : A →+* A')).IsPrime] (b : A) :
    Ring.ord (Localization.AtPrime (p.map (e : A →+* A')))
        (algebraMap A' (Localization.AtPrime (p.map (e : A →+* A'))) (e b)) =
      Ring.ord (Localization.AtPrime p) (algebraMap A (Localization.AtPrime p) b) :=
  ring_ord_atPrime_congr' e p _ rfl b

/-- The double-quotient comparison: for primes `P ≤ V ≤ Q` of `A`, the order of vanishing of
`b` at `Q ⧸ V` agrees with its order of vanishing in the quotient of the localisation of
`A ⧸ P` at `Q ⧸ P` by the extension of `V ⧸ P`. -/
theorem ring_ord_quot_quot {A : Type u} [CommRing A] (P V Q : Ideal A) [P.IsPrime] [V.IsPrime]
    [Q.IsPrime] [(Q.map (Ideal.Quotient.mk V)).IsPrime] [(Q.map (Ideal.Quotient.mk P)).IsPrime]
    (hPV : P ≤ V) (hVQ : V ≤ Q) (b : A) :
    Ring.ord (Localization.AtPrime (Q.map (Ideal.Quotient.mk V)))
        (algebraMap (A ⧸ V) (Localization.AtPrime (Q.map (Ideal.Quotient.mk V)))
          (Ideal.Quotient.mk V b)) =
      Ring.ord (Localization.AtPrime (Q.map (Ideal.Quotient.mk P)) ⧸
          Ideal.map (algebraMap (A ⧸ P) (Localization.AtPrime (Q.map (Ideal.Quotient.mk P))))
            (V.map (Ideal.Quotient.mk P)))
        (Ideal.Quotient.mk _
          (algebraMap (A ⧸ P) (Localization.AtPrime (Q.map (Ideal.Quotient.mk P)))
            (Ideal.Quotient.mk P b))) := by
  let _ : (V.map (Ideal.Quotient.mk P)).IsPrime := map_quotient_isPrime P V hPV
  have hq : V.map (Ideal.Quotient.mk P) ≤ Q.map (Ideal.Quotient.mk P) := Ideal.map_mono hVQ
  let _ : ((Q.map (Ideal.Quotient.mk P)).map
      (Ideal.Quotient.mk (V.map (Ideal.Quotient.mk P)))).IsPrime := map_quotient_isPrime _ _ hq
  have key := ring_ord_quotient_atPrime (V.map (Ideal.Quotient.mk P))
      (Q.map (Ideal.Quotient.mk P)) hq
      (Localization.AtPrime ((Q.map (Ideal.Quotient.mk P)).map
        (Ideal.Quotient.mk (V.map (Ideal.Quotient.mk P))))) (Ideal.Quotient.mk P b)
  rw [← key]
  have hideal : Ideal.map
      ((DoubleQuot.quotQuotEquivQuotOfLE hPV :
        ((A ⧸ P) ⧸ V.map (Ideal.Quotient.mk P)) ≃+* A ⧸ V) : _ →+* A ⧸ V)
      ((Q.map (Ideal.Quotient.mk P)).map
        (Ideal.Quotient.mk (V.map (Ideal.Quotient.mk P))))
      = Q.map (Ideal.Quotient.mk V) := by
    rw [Ideal.map_map, Ideal.map_map]
    exact congrArg (Ideal.map · Q) (DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMk hPV)
  have final := ring_ord_atPrime_congr' (DoubleQuot.quotQuotEquivQuotOfLE hPV)
      ((Q.map (Ideal.Quotient.mk P)).map (Ideal.Quotient.mk (V.map (Ideal.Quotient.mk P))))
      (Q.map (Ideal.Quotient.mk V)) hideal
      (Ideal.Quotient.mk (V.map (Ideal.Quotient.mk P)) (Ideal.Quotient.mk P b))
  have helt : (DoubleQuot.quotQuotEquivQuotOfLE hPV)
      (Ideal.Quotient.mk (V.map (Ideal.Quotient.mk P)) (Ideal.Quotient.mk P b))
      = Ideal.Quotient.mk V b := rfl
  rw [helt] at final
  exact final

/-- The ambient form of `height_eq_two`: for primes `P ≤ V ≤ Q` of `A` such that the dimension
formula holds for `A ⧸ P` and `A ⧸ V`, and such that `V` has height one in `A ⧸ P` and `Q` has
height one in `A ⧸ V`, the image of `Q` in `A ⧸ P` has height two. -/
theorem height_eq_two_ambient {A : Type u} [CommRing A] [IsNoetherianRing A]
    (P V Q : Ideal A) [P.IsPrime] [V.IsPrime] [Q.IsPrime] (hPV : P ≤ V) (hVQ : V ≤ Q)
    (hP : HasDimensionFormula (A ⧸ P)) (hV : HasDimensionFormula (A ⧸ V))
    (h1 : (V.map (Ideal.Quotient.mk P)).height = 1)
    (h2 : (Q.map (Ideal.Quotient.mk V)).height = 1) :
    (Q.map (Ideal.Quotient.mk P)).height = 2 := by
  let _ : Nontrivial (A ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr ‹P.IsPrime›.ne_top
  let _ : (V.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  let _ : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hPV.trans hVQ)
  let e := DoubleQuot.quotQuotEquivQuotOfLE hPV
  have hcomp : ((e : ((A ⧸ P) ⧸ V.map (Ideal.Quotient.mk P)) →+* A ⧸ V).comp
      ((Ideal.Quotient.mk (V.map (Ideal.Quotient.mk P))).comp (Ideal.Quotient.mk P))) =
      Ideal.Quotient.mk V :=
    DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMk hPV
  have hid : Ideal.map e (Ideal.map (Ideal.Quotient.mk (V.map (Ideal.Quotient.mk P)))
      (Q.map (Ideal.Quotient.mk P))) = Q.map (Ideal.Quotient.mk V) := by
    rw [← Ideal.map_coe (f := e), Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, hcomp]
  have hQq : (Ideal.map (Ideal.Quotient.mk (V.map (Ideal.Quotient.mk P)))
      (Q.map (Ideal.Quotient.mk P))).height = 1 := by
    rw [← RingEquiv.height_map e, hid, h2]
  exact height_eq_two hP _ _ (hasDimensionFormula_of_ringEquiv e.symm hV) h1 hQq
    (Ideal.map_mono hVQ)

/-- The order of vanishing in a quotient only depends on the ideal through its value. -/
theorem ring_ord_quotient_congr {S : Type u} [CommRing S] (I J : Ideal S) (h : I = J) (y : S) :
    Ring.ord (S ⧸ I) (Ideal.Quotient.mk I y) = Ring.ord (S ⧸ J) (Ideal.Quotient.mk J y) := by
  subst h
  rfl

end SectionGysinIdentity

/-! ## The order of vanishing in the stalk -/

section Ord

variable (B : CommRingCat.{u}) [IsDomain B] [IsNoetherianRing B] (q : ↥(Spec B)) (b : B)

omit [IsDomain B] in
/-- The stalk of an integral Noetherian affine scheme at a point is Noetherian. -/
theorem isNoetherianRing_stalk : IsNoetherianRing ((Spec B).presheaf.stalk q) :=
  IsLocalization.isNoetherianRing (q : PrimeSpectrum B).asIdeal.primeCompl
    ((Spec B).presheaf.stalk q) inferInstance

omit [IsNoetherianRing B] in
/-- The image of a nonzero element of an integral affine scheme in a stalk is nonzero. -/
theorem algebraMap_stalk_ne_zero (hb : b ≠ 0) :
    algebraMap B ((Spec B).presheaf.stalk q) b ≠ 0 := by
  have hinj : Function.Injective (algebraMap B ((Spec B).presheaf.stalk q)) :=
    IsLocalization.injective ((Spec B).presheaf.stalk q)
      (Ideal.primeCompl_le_nonZeroDivisors (q : PrimeSpectrum B).asIdeal)
  exact fun hz => hb (hinj (by rw [hz, map_zero]))

/-- At a codimension-one point the length-theoretic order of vanishing of a nonzero section is
finite. -/
theorem stalk_ord_ne_top (hb : b ≠ 0) (hq : Order.coheight q = 1) :
    Ring.ord ((Spec B).presheaf.stalk q) (algebraMap B ((Spec B).presheaf.stalk q) b) ≠ ⊤ := by
  have hkd : Ring.KrullDimLE 1 ((Spec B).presheaf.stalk q) := krullDimLE_of_coheight_le hq.le
  have hnoeth := isNoetherianRing_stalk B q
  exact Ring.ord_ne_top
    (mem_nonZeroDivisors_iff_ne_zero.mpr (algebraMap_stalk_ne_zero B q b hb))

/-- The order of vanishing of a global section of an integral Noetherian affine scheme at a
codimension-one point is the length-theoretic order of vanishing in the stalk. -/
theorem scheme_ord_eq_stalk_ord (hb : b ≠ 0) (hq : Order.coheight q = 1) (n : ℕ)
    (hn : Ring.ord ((Spec B).presheaf.stalk q)
      (algebraMap B ((Spec B).presheaf.stalk q) b) = n) :
    (Spec B).ord (algebraMap B (Spec B).functionField b) q = n := by
  have hkd : Ring.KrullDimLE 1 ((Spec B).presheaf.stalk q) := krullDimLE_of_coheight_le hq.le
  have hnoeth := isNoetherianRing_stalk B q
  have hu0 := algebraMap_stalk_ne_zero B q b hb
  have hfne : algebraMap B (Spec B).functionField b ≠ 0 := by
    rw [algebraMap_functionField_eq_stalk B q b]
    exact fun hz => hu0 (IsFractionRing.injective ((Spec B).presheaf.stalk q)
      (Spec B).functionField (by rw [hz, map_zero]))
  rw [_root_.AlgebraicGeometry.Scheme.ord_eq_iff hq hfne,
    show (Spec B).ordHom q hq = Ring.ordFrac ((Spec B).presheaf.stalk q) from rfl,
    algebraMap_functionField_eq_stalk B q b,
    Ring.ordFrac_eq_ord ((Spec B).presheaf.stalk q) hu0]
  exact Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_iff_ne_zero.mpr hu0) hn

/-- The order of vanishing of a global section of an integral Noetherian affine scheme at a
codimension-one point, as the natural number underlying the length of the stalk quotient. -/
theorem scheme_ord_eq_toNat (hb : b ≠ 0) (hq : Order.coheight q = 1) :
    (Spec B).ord (algebraMap B (Spec B).functionField b) q =
      ((Ring.ord ((Spec B).presheaf.stalk q)
        (algebraMap B ((Spec B).presheaf.stalk q) b)).toNat : ℤ) :=
  scheme_ord_eq_stalk_ord B q b hb hq _
    (ENat.natCast_toNat (stalk_ord_ne_top B q b hb hq)).symm

/-- The order of vanishing of a global section of an integral Noetherian affine scheme at a
codimension-one point, computed in the localisation of the coordinate ring at that point. -/
theorem scheme_ord_eq_localization (hb : b ≠ 0) (hq : Order.coheight q = 1) :
    (Spec B).ord (algebraMap B (Spec B).functionField b) q =
      ((Ring.ord (Localization.AtPrime (q : PrimeSpectrum B).asIdeal)
        (algebraMap B (Localization.AtPrime (q : PrimeSpectrum B).asIdeal) b)).toNat : ℤ) := by
  have hloc :
      Ring.ord ((Spec B).presheaf.stalk q) (algebraMap B ((Spec B).presheaf.stalk q) b) =
        Ring.ord (Localization.AtPrime (q : PrimeSpectrum B).asIdeal)
          (algebraMap B (Localization.AtPrime (q : PrimeSpectrum B).asIdeal) b) :=
    SectionGysinIdentity.ring_ord_atPrime (q : PrimeSpectrum B).asIdeal _ b
  have hne : Ring.ord (Localization.AtPrime (q : PrimeSpectrum B).asIdeal)
      (algebraMap B (Localization.AtPrime (q : PrimeSpectrum B).asIdeal) b) ≠ ⊤ :=
    hloc ▸ stalk_ord_ne_top B q b hb hq
  refine scheme_ord_eq_stalk_ord B q b hb hq _ ?_
  rw [hloc]
  exact (ENat.natCast_toNat hne).symm

/-- At a codimension-one point the order of vanishing in the localisation is finite. -/
theorem localization_ord_ne_top (hb : b ≠ 0) (hq : Order.coheight q = 1) :
    Ring.ord (Localization.AtPrime (q : PrimeSpectrum B).asIdeal)
      (algebraMap B (Localization.AtPrime (q : PrimeSpectrum B).asIdeal) b) ≠ ⊤ := by
  have hloc :
      Ring.ord ((Spec B).presheaf.stalk q) (algebraMap B ((Spec B).presheaf.stalk q) b) =
        Ring.ord (Localization.AtPrime (q : PrimeSpectrum B).asIdeal)
          (algebraMap B (Localization.AtPrime (q : PrimeSpectrum B).asIdeal) b) :=
    SectionGysinIdentity.ring_ord_atPrime (q : PrimeSpectrum B).asIdeal _ b
  exact hloc ▸ stalk_ord_ne_top B q b hb hq

end Ord

/-! ## Reindexing the points of a subvariety -/

section QuotPoint

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The points of the closed subvariety `V(P)` of the total space, indexed by the primes of
`R[T] ⧸ P`. -/
noncomputable def quotPointMap (P : Ideal (Polynomial R)) :
    PrimeSpectrum (Polynomial R ⧸ P) → ↥(Spec (CommRingCat.of (Polynomial R))) :=
  fun q ↦ (quotImmersion P).base (show ↥(Spec (CommRingCat.of (Polynomial R ⧸ P))) from q)

omit [IsNoetherianRing R] in
/-- The prime attached to a point of `V(P)` is the contraction of the corresponding prime of
the quotient. -/
theorem quotPointMap_asIdeal (P : Ideal (Polynomial R)) (q : PrimeSpectrum (Polynomial R ⧸ P)) :
    (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal =
      q.asIdeal.comap (Ideal.Quotient.mk P) := rfl

omit [IsNoetherianRing R] in
/-- `P` is contained in the prime of any point of `V(P)`. -/
theorem le_quotPointMap_asIdeal (P : Ideal (Polynomial R))
    (q : PrimeSpectrum (Polynomial R ⧸ P)) :
    P ≤ (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal := by
  intro y hy
  change Ideal.Quotient.mk P y ∈ q.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hy]
  exact Ideal.zero_mem _

omit [IsNoetherianRing R] in
/-- The prime of the quotient is recovered by extending the prime of the point. -/
theorem map_quotPointMap_asIdeal (P : Ideal (Polynomial R))
    (q : PrimeSpectrum (Polynomial R ⧸ P)) :
    ((quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal).map
      (Ideal.Quotient.mk P) = q.asIdeal := by
  rw [quotPointMap_asIdeal, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

omit [IsNoetherianRing R] in
/-- Distinct primes of the quotient give distinct points of the total space. -/
theorem quotPointMap_injective (P : Ideal (Polynomial R)) :
    Function.Injective (quotPointMap P) := by
  intro q q' h
  refine PrimeSpectrum.ext ?_
  rw [← map_quotPointMap_asIdeal P q, ← map_quotPointMap_asIdeal P q', h]

omit [IsNoetherianRing R] in
/-- The image of `quotPointMap` consists of the points whose prime contains `P`. -/
theorem mem_range_quotPointMap_iff (P : Ideal (Polynomial R))
    (V : ↥(Spec (CommRingCat.of (Polynomial R)))) :
    V ∈ Set.range (quotPointMap P) ↔ P ≤ (V : PrimeSpectrum (Polynomial R)).asIdeal := by
  constructor
  · rintro ⟨q, rfl⟩
    exact le_quotPointMap_asIdeal P q
  · intro hPV
    exact ⟨quotientPoint P (V : PrimeSpectrum (Polynomial R)).asIdeal
        (V : PrimeSpectrum (Polynomial R)).isPrime hPV,
      PrimeSpectrum.ext (quotImmersion_base_quotientPoint P _ _ hPV)⟩

omit [IsNoetherianRing R] in
/-- `quotPointMap` is monotone and reflects the order. -/
theorem quotPointMap_le_iff (P : Ideal (Polynomial R)) (q q' : PrimeSpectrum (Polynomial R ⧸ P)) :
    (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal ≤
        (quotPointMap P q' : PrimeSpectrum (Polynomial R)).asIdeal ↔ q.asIdeal ≤ q'.asIdeal := by
  constructor
  · intro h
    rw [← map_quotPointMap_asIdeal P q, ← map_quotPointMap_asIdeal P q']
    exact Ideal.map_mono h
  · intro h
    rw [quotPointMap_asIdeal, quotPointMap_asIdeal]
    exact Ideal.comap_mono h

end QuotPoint

/-! ## Heights with no intermediate prime -/

section Height

/-- A nonzero prime of a domain with no prime strictly between it and zero has height one. -/
theorem height_eq_one_of_no_middle {A : Type u} [CommRing A] [IsDomain A] (p : Ideal A)
    [p.IsPrime] (hne : p ≠ ⊥)
    (hmid : ∀ p' : Ideal A, p'.IsPrime → p' < p → p' = ⊥) : p.height = 1 := by
  have hbot : (⊥ : Ideal A).height = 0 := Ideal.height_eq_zero_iff_eq_bot.mpr rfl
  have hlt : (⊥ : Ideal A) < p := lt_of_le_of_ne bot_le (Ne.symm hne)
  refine le_antisymm ?_ ?_
  · have h1 : p.height ≤ ((1 : ℕ) : ℕ∞) := by
      rw [Ideal.height_le_iff]
      intro q hq hqp
      have : q = ⊥ := hmid q hq hqp
      subst this
      rw [hbot]
      norm_num
    simpa using h1
  · have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    simpa [hbot] using this


/-- For an ideal containing `P`, extension and contraction along the quotient map are strictly
monotone. -/
theorem map_lt_map_of_lt {A : Type u} [CommRing A] (P I J : Ideal A) (hPI : P ≤ I) (hIJ : I < J) :
    I.map (Ideal.Quotient.mk P) < J.map (Ideal.Quotient.mk P) := by
  refine lt_of_le_of_ne (Ideal.map_mono hIJ.le) ?_
  intro hcon
  have h1 : Ideal.comap (Ideal.Quotient.mk P) (I.map (Ideal.Quotient.mk P)) = I := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr hPI
  have h2 : Ideal.comap (Ideal.Quotient.mk P) (J.map (Ideal.Quotient.mk P)) = J := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr (hPI.trans hIJ.le)
  exact hIJ.ne (by rw [← h1, ← h2, hcon])

/-- The extension of a strictly larger ideal along a quotient map is nonzero. -/
theorem map_ne_bot_of_lt {A : Type u} [CommRing A] (P I : Ideal A) (hPI : P < I) :
    I.map (Ideal.Quotient.mk P) ≠ ⊥ := by
  intro hcon
  rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hcon
  exact hPI.not_ge hcon

/-- For primes `V < W` of `A` with no prime strictly between them, the image of `W` in `A ⧸ V`
has height one. -/
theorem height_map_eq_one_of_no_middle {A : Type u} [CommRing A] (V W : Ideal A) [V.IsPrime]
    [W.IsPrime] (hVW : V < W)
    (hmid : ∀ W' : Ideal A, W'.IsPrime → V < W' → W' < W → False) :
    (W.map (Ideal.Quotient.mk V)).height = 1 := by
  let _ : (W.map (Ideal.Quotient.mk V)).IsPrime :=
    SectionGysinIdentity.map_quotient_isPrime V W hVW.le
  refine height_eq_one_of_no_middle _ (map_ne_bot_of_lt V W hVW) ?_
  intro p' hp' hlt
  by_contra hne
  refine hmid (p'.comap (Ideal.Quotient.mk V)) (hp'.comap _) ?_ ?_
  · refine lt_of_le_of_ne ?_ ?_
    · intro y hy
      change Ideal.Quotient.mk V y ∈ p'
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hy]
      exact Ideal.zero_mem _
    · intro hcon
      refine hne ?_
      have h0 : Ideal.map (Ideal.Quotient.mk V) (Ideal.comap (Ideal.Quotient.mk V) p') = p' :=
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective p'
      have hp'V : p' = Ideal.map (Ideal.Quotient.mk V) V :=
        h0.symm.trans (congrArg (Ideal.map (Ideal.Quotient.mk V)) hcon.symm)
      rw [hp'V]
      exact (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk V)).mpr Ideal.mk_ker.ge
  · have hle : p'.comap (Ideal.Quotient.mk V) ≤ W := by
      have h2 : Ideal.comap (Ideal.Quotient.mk V) (W.map (Ideal.Quotient.mk V)) = W := by
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
          ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        exact sup_eq_left.mpr hVW.le
      rw [← h2]
      exact Ideal.comap_mono hlt.le
    refine lt_of_le_of_ne hle ?_
    intro hcon
    refine hlt.ne ?_
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective p', hcon]

/-- The zero ideal of a domain does not have height one. -/
theorem height_bot_ne_one {A : Type u} [CommRing A] [IsDomain A] : (⊥ : Ideal A).height ≠ 1 := by
  let _ : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  rw [Ideal.height_eq_zero_iff_eq_bot.mpr rfl]
  norm_num

end Height

/-! ## Coefficients of the divisors of `elementGenerator` -/

section Coefficients

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The coefficient of the divisor of `a` on the subvariety `V(P)` at a point of `V(P)` of
height one is the length-theoretic order of vanishing of `a` in the localisation of
`R[T] ⧸ P` at that point. -/
theorem divisor_apply_eq_ringOrd (P : Ideal (Polynomial R)) [P.IsPrime] (a : Polynomial R)
    (ha : a ∉ P) (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))
    (q : PrimeSpectrum (Polynomial R ⧸ P)) (hht : q.asIdeal.height = 1) :
    ((elementGenerator P a ha).divisor dimE :
        ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ)
      (quotPointMap P q) =
      ((Ring.ord (Localization.AtPrime q.asIdeal)
        (algebraMap (Polynomial R ⧸ P) (Localization.AtPrime q.asIdeal)
          (Ideal.Quotient.mk P a))).toNat : ℚ) := by
  have hco : Order.coheight (show ↥(Spec (CommRingCat.of (Polynomial R ⧸ P))) from q) = 1 := by
    rw [coheight_eq_ideal_height (Polynomial R ⧸ P) q]
    exact hht
  have hord :
      ((Spec (CommRingCat.of (Polynomial R ⧸ P))).ord
          (elementFunction P a ha :
            (Spec (CommRingCat.of (Polynomial R ⧸ P))).functionField)
          (show ↥(Spec (CommRingCat.of (Polynomial R ⧸ P))) from q) : ℤ) =
        ((Ring.ord (Localization.AtPrime q.asIdeal)
          (algebraMap (Polynomial R ⧸ P) (Localization.AtPrime q.asIdeal)
            (Ideal.Quotient.mk P a))).toNat : ℤ) :=
    scheme_ord_eq_localization (CommRingCat.of (Polynomial R ⧸ P))
      (show ↥(Spec (CommRingCat.of (Polynomial R ⧸ P))) from q) (Ideal.Quotient.mk P a)
      (quotientMk_ne_zero P a ha) hco
  simp only [quotPointMap]
  rw [elementGenerator_divisor_apply_image P a ha dimE
    (show ↥(Spec (CommRingCat.of (Polynomial R ⧸ P))) from q), hord]
  norm_num

/-- The coefficient of the divisor of `a` on the subvariety `V(P)` vanishes at a point whose
height is not one, because `Scheme.ord` is junk zero away from codimension one. -/
theorem divisor_apply_eq_zero_of_height_ne (P : Ideal (Polynomial R)) [P.IsPrime]
    (a : Polynomial R) (ha : a ∉ P)
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))
    (q : PrimeSpectrum (Polynomial R ⧸ P)) (hht : q.asIdeal.height ≠ 1) :
    ((elementGenerator P a ha).divisor dimE :
        ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ)
      (quotPointMap P q) = 0 := by
  have hco : Order.coheight (show ↥(Spec (CommRingCat.of (Polynomial R ⧸ P))) from q) ≠ 1 := by
    rw [coheight_eq_ideal_height (Polynomial R ⧸ P) q]
    exact hht
  simp only [quotPointMap]
  rw [elementGenerator_divisor_apply_image P a ha dimE
    (show ↥(Spec (CommRingCat.of (Polynomial R ⧸ P))) from q),
    _root_.AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hco]
  norm_num

/-- The coefficient of the divisor of `a` on the subvariety `V(P)` vanishes at a point whose
prime does not contain `a`. -/
theorem divisor_apply_eq_zero_of_notMem (P : Ideal (Polynomial R)) [P.IsPrime]
    (a : Polynomial R) (ha : a ∉ P)
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))
    (q : PrimeSpectrum (Polynomial R ⧸ P))
    (hmem : Ideal.Quotient.mk P a ∉ q.asIdeal) :
    ((elementGenerator P a ha).divisor dimE :
        ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ)
      (quotPointMap P q) = 0 := by
  have hord : ((Spec (CommRingCat.of (Polynomial R ⧸ P))).ord
      (elementFunction P a ha : (Spec (CommRingCat.of (Polynomial R ⧸ P))).functionField)
      (show ↥(Spec (CommRingCat.of (Polynomial R ⧸ P))) from q)) = 0 :=
    ord_algebraMap_eq_zero_of_notMem (CommRingCat.of (Polynomial R ⧸ P))
      (show ↥(Spec (CommRingCat.of (Polynomial R ⧸ P))) from q) (Ideal.Quotient.mk P a) hmem
  simp only [quotPointMap]
  rw [elementGenerator_divisor_apply_image P a ha dimE
    (show ↥(Spec (CommRingCat.of (Polynomial R ⧸ P))) from q), hord]
  norm_num

/-- The length-theoretic order of vanishing occurring in a divisor coefficient is finite. -/
theorem divisor_ringOrd_ne_top (P : Ideal (Polynomial R)) [P.IsPrime] (a : Polynomial R)
    (ha : a ∉ P) (q : PrimeSpectrum (Polynomial R ⧸ P)) (hht : q.asIdeal.height = 1) :
    Ring.ord (Localization.AtPrime q.asIdeal)
      (algebraMap (Polynomial R ⧸ P) (Localization.AtPrime q.asIdeal)
        (Ideal.Quotient.mk P a)) ≠ ⊤ := by
  have hco : Order.coheight (show ↥(Spec (CommRingCat.of (Polynomial R ⧸ P))) from q) = 1 := by
    rw [coheight_eq_ideal_height (Polynomial R ⧸ P) q]
    exact hht
  exact localization_ord_ne_top (CommRingCat.of (Polynomial R ⧸ P))
    (show ↥(Spec (CommRingCat.of (Polynomial R ⧸ P))) from q) (Ideal.Quotient.mk P a)
    (quotientMk_ne_zero P a ha) hco

end Coefficients

/-! ## The summands of the symmetric local identity -/

open Classical in
/-- The summand of Fulton's symmetric local identity attached to a prime `q` of `D`:
the order of vanishing of `b` along `q` times the order of vanishing of `b'` at `Q` on the
subvariety cut out by `q`. -/
noncomputable def symTerm (D : Type u) [CommRing D] (Q : Ideal D) [Q.IsPrime] (b b' : D)
    (q : PrimeSpectrum D) : ℕ∞ :=
  if q.asIdeal < Q ∧ b ∈ q.asIdeal then
    Ring.ord (Localization.AtPrime q.asIdeal) (algebraMap D _ b) *
      Ring.ord (Localization.AtPrime Q ⧸ q.asIdeal.map (algebraMap D (Localization.AtPrime Q)))
        (Ideal.Quotient.mk _ (algebraMap D (Localization.AtPrime Q) b'))
  else 0

open Classical in
/-- The summand vanishes at a prime which does not contain `b`, or which is not strictly below
`Q`. -/
theorem symTerm_eq_zero {D : Type u} [CommRing D] (Q : Ideal D) [Q.IsPrime] (b b' : D)
    (q : PrimeSpectrum D) (h : ¬ (q.asIdeal < Q ∧ b ∈ q.asIdeal)) :
    symTerm D Q b b' q = 0 := by
  rw [symTerm, if_neg h]

open Classical in
/-- The value of the summand at a prime strictly below `Q` containing `b`. -/
theorem symTerm_of_lt {D : Type u} [CommRing D] (Q : Ideal D) [Q.IsPrime] (b b' : D)
    (q : PrimeSpectrum D) (h : q.asIdeal < Q ∧ b ∈ q.asIdeal) :
    symTerm D Q b b' q =
      Ring.ord (Localization.AtPrime q.asIdeal) (algebraMap D _ b) *
        Ring.ord (Localization.AtPrime Q ⧸ q.asIdeal.map (algebraMap D (Localization.AtPrime Q)))
          (Ideal.Quotient.mk _ (algebraMap D (Localization.AtPrime Q) b')) := by
  rw [symTerm, if_pos h]

/-- Fulton's symmetric local identity, restated with `symTerm`. -/
theorem localOrdSymmetry_symTerm (hsym : LocalOrdSymmetry.{u}) (D : Type u) [CommRing D]
    [IsDomain D] [IsNoetherianRing D] (Q : Ideal D) [Q.IsPrime] (b b' : D) (hb : b ≠ 0)
    (hb' : b' ≠ 0)
    (hchain : ∀ q q' : Ideal D, q.IsPrime → q'.IsPrime → ⊥ < q' → q' < q → q < Q → False)
    (hmin : ∀ q : Ideal D, q.IsPrime → q ≤ Q → b ∈ q → b' ∈ q → q = Q) :
    ∑ᶠ q : PrimeSpectrum D, symTerm D Q b' b q =
      ∑ᶠ q : PrimeSpectrum D, symTerm D Q b b' q :=
  hsym D Q b b' hb hb' hchain hmin

/-- Two finitely supported `ℕ∞`-valued functions with everywhere finite values and equal sums
have equal sums of the underlying natural numbers. -/
theorem finsum_toNat_eq {ι : Type*} (f g : ι → ℕ∞)
    (hf : (Function.support fun i ↦ (f i).toNat).Finite)
    (hg : (Function.support fun i ↦ (g i).toNat).Finite)
    (hft : ∀ i, f i ≠ ⊤) (hgt : ∀ i, g i ≠ ⊤) (h : ∑ᶠ i, f i = ∑ᶠ i, g i) :
    (∑ᶠ i, (f i).toNat) = ∑ᶠ i, (g i).toNat := by
  have hcast : ∀ u : ι → ℕ∞, (∀ i, u i ≠ ⊤) →
      (Function.support fun i ↦ (u i).toNat).Finite →
      (((∑ᶠ i, (u i).toNat : ℕ) : ℕ∞)) = ∑ᶠ i, u i := by
    intro u hut hus
    calc ((∑ᶠ i, (u i).toNat : ℕ) : ℕ∞)
        = ∑ᶠ i, (((u i).toNat : ℕ) : ℕ∞) := (Nat.castAddMonoidHom ℕ∞).map_finsum hus
      _ = ∑ᶠ i, u i := finsum_congr fun i ↦ ENat.natCast_toNat (hut i)
  have hkey : (((∑ᶠ i, (f i).toNat : ℕ) : ℕ∞)) = (((∑ᶠ i, (g i).toNat : ℕ) : ℕ∞)) :=
    (hcast f hft hf).trans (h.trans (hcast g hgt hg).symm)
  exact_mod_cast hkey

/-- Two families of natural numbers with finite support and equal sums in `ℕ∞` have equal sums
in `ℚ`. -/
theorem finsum_natCast_eq_of_enat {ι : Type*} (n m : ι → ℕ)
    (hn : (Function.support n).Finite) (hm : (Function.support m).Finite)
    (h : (∑ᶠ i, ((n i : ℕ∞))) = ∑ᶠ i, ((m i : ℕ∞))) :
    (∑ᶠ i, ((n i : ℚ))) = ∑ᶠ i, ((m i : ℚ)) := by
  have h1 : ((∑ᶠ i, n i : ℕ) : ℕ∞) = ∑ᶠ i, ((n i : ℕ∞)) :=
    (Nat.castAddMonoidHom ℕ∞).map_finsum hn
  have h2 : ((∑ᶠ i, m i : ℕ) : ℕ∞) = ∑ᶠ i, ((m i : ℕ∞)) :=
    (Nat.castAddMonoidHom ℕ∞).map_finsum hm
  have hnat : (∑ᶠ i, n i) = ∑ᶠ i, m i := by
    have := h1.trans (h.trans h2.symm)
    exact_mod_cast this
  have h3 : ((∑ᶠ i, n i : ℕ) : ℚ) = ∑ᶠ i, ((n i : ℚ)) :=
    (Nat.castAddMonoidHom ℚ).map_finsum hn
  have h4 : ((∑ᶠ i, m i : ℕ) : ℚ) = ∑ᶠ i, ((m i : ℚ)) :=
    (Nat.castAddMonoidHom ℚ).map_finsum hm
  rw [← h3, ← h4, hnat]

/-! ## The generalised Gysin summand at a point of the base -/

section Summand

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The generalised Gysin summand vanishes at a point where `b` vanishes identically. -/
theorem sectionGysinTermOf_of_mem (c : R)
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R)))) (b : Polynomial R)
    (V : ↥(Spec (CommRingCat.of (Polynomial R))))
    (h : b ∈ (V : PrimeSpectrum (Polynomial R)).asIdeal) :
    sectionGysinTermOf c dimE b V = 0 := by
  classical
  rw [sectionGysinTermOf, dif_neg (not_not_intro h)]

/-- The Gysin summand of the section is the generalised summand for `b = T - c`. -/
theorem sectionGysinTerm_eq_termOf (c : R)
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))
    (V : ↥(Spec (CommRingCat.of (Polynomial R)))) :
    sectionGysinTerm c dimE V = sectionGysinTermOf c dimE (sectionPoly c) V := rfl

/-- The generalised Gysin sum has finite support. -/
theorem finite_support_termOfSummand (c : R)
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R)))) (b : Polynomial R)
    (z : AlgebraicCycle (Spec (CommRingCat.of (Polynomial R))) ℚ) :
    (Function.support fun V ↦ (z : ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V •
      sectionGysinTermOf c dimE b V).Finite :=
  (AlgebraicCycle.finite_support z).subset fun V hV hz0 ↦ hV (by
    change (z : ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V = 0 at hz0
    change (z : ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V •
      sectionGysinTermOf c dimE b V = 0
    rw [hz0, zero_smul])

omit [IsNoetherianRing R] in
/-- The point of `V(P)` attached to a prime containing `P` maps back to that prime. -/
theorem quotPointMap_quotientPoint (P : Ideal (Polynomial R))
    (W : ↥(Spec (CommRingCat.of (Polynomial R))))
    (hPW : P ≤ (W : PrimeSpectrum (Polynomial R)).asIdeal) :
    quotPointMap P (quotientPoint P (W : PrimeSpectrum (Polynomial R)).asIdeal
      (W : PrimeSpectrum (Polynomial R)).isPrime hPW) = W :=
  PrimeSpectrum.ext (quotImmersion_base_quotientPoint P _ _ hPW)

variable (c : R) (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))
  (b : Polynomial R) (V : ↥(Spec (CommRingCat.of (Polynomial R))))
  (x : ↥(Spec (CommRingCat.of R)))

/-- The coefficient at `x` of the generalised Gysin summand vanishes when `b` vanishes
identically on the subvariety. -/
theorem termOf_apply_eq_zero_of_mem (h : b ∈ (V : PrimeSpectrum (Polynomial R)).asIdeal) :
    ((sectionGysinTermOf c dimE b V : ↥(Spec (CommRingCat.of R)) → ℚ) x) = 0 := by
  rw [sectionGysinTermOf_of_mem c dimE b V h]
  rfl

/-- The coefficient at `x` of the generalised Gysin summand vanishes when the subvariety does
not pass through the corresponding point of the section. -/
theorem termOf_apply_eq_zero_of_not_le (hb : b ∉ (V : PrimeSpectrum (Polynomial R)).asIdeal)
    (hnle : ¬ (V : PrimeSpectrum (Polynomial R)).asIdeal ≤
      (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal) :
    ((sectionGysinTermOf c dimE b V : ↥(Spec (CommRingCat.of R)) → ℚ) x) = 0 := by
  rw [sectionGysinTermOf_of_notMem c dimE b V hb, sectionRestrict_apply]
  exact @elementGenerator_divisor_apply_of_not_le R _ _ (V : PrimeSpectrum (Polynomial R)).asIdeal
    (V : PrimeSpectrum (Polynomial R)).isPrime b hb dimE _ hnle

/-- The coefficient at `x` of the generalised Gysin summand vanishes when the point of the
section is not of height one on the subvariety. -/
theorem termOf_apply_eq_zero_of_height_ne (hb : b ∉ (V : PrimeSpectrum (Polynomial R)).asIdeal)
    (q₁ : PrimeSpectrum (Polynomial R ⧸ (V : PrimeSpectrum (Polynomial R)).asIdeal))
    (hq₁ : quotPointMap (V : PrimeSpectrum (Polynomial R)).asIdeal q₁ = sectionPoint c x)
    (hht : q₁.asIdeal.height ≠ 1) :
    ((sectionGysinTermOf c dimE b V : ↥(Spec (CommRingCat.of R)) → ℚ) x) = 0 := by
  rw [sectionGysinTermOf_of_notMem c dimE b V hb, sectionRestrict_apply, ← hq₁]
  exact @divisor_apply_eq_zero_of_height_ne R _ _ (V : PrimeSpectrum (Polynomial R)).asIdeal
    (V : PrimeSpectrum (Polynomial R)).isPrime b hb dimE q₁ hht

/-- The coefficient at `x` of the generalised Gysin summand at a height-one point of the
subvariety, as a length-theoretic order of vanishing. -/
theorem termOf_apply_eq_ringOrd (hb : b ∉ (V : PrimeSpectrum (Polynomial R)).asIdeal)
    (q₁ : PrimeSpectrum (Polynomial R ⧸ (V : PrimeSpectrum (Polynomial R)).asIdeal))
    (hq₁ : quotPointMap (V : PrimeSpectrum (Polynomial R)).asIdeal q₁ = sectionPoint c x)
    (hht : q₁.asIdeal.height = 1) :
    ((sectionGysinTermOf c dimE b V : ↥(Spec (CommRingCat.of R)) → ℚ) x) =
      ((Ring.ord (Localization.AtPrime q₁.asIdeal)
        (algebraMap (Polynomial R ⧸ (V : PrimeSpectrum (Polynomial R)).asIdeal)
          (Localization.AtPrime q₁.asIdeal) (Ideal.Quotient.mk _ b))).toNat : ℚ) := by
  rw [sectionGysinTermOf_of_notMem c dimE b V hb, sectionRestrict_apply, ← hq₁]
  exact @divisor_apply_eq_ringOrd R _ _ (V : PrimeSpectrum (Polynomial R)).asIdeal
    (V : PrimeSpectrum (Polynomial R)).isPrime b hb dimE q₁ hht

end Summand

/-! ## The termwise form of the symmetric local identity -/

section Termwise

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (c : R)
  (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))
  (P : Ideal (Polynomial R)) [P.IsPrime] (x : ↥(Spec (CommRingCat.of R)))

/-- If there is a chain of three primes below the image of the section point, no point of `V(P)`
contributes to the Gysin sum: a contributing point would make that image have height two. -/
theorem termProduct_eq_zero_of_chain_failure
    (hdim : ∀ P' : Ideal (Polynomial R), P'.IsPrime → HasDimensionFormula (Polynomial R ⧸ P'))
    (hPQ0 : P ≤ (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal)
    (b b' : Polynomial R) (hb : b ∉ P)
    (hchain : ¬ ∀ r r' : Ideal (Polynomial R ⧸ P), r.IsPrime → r'.IsPrime → ⊥ < r' → r' < r →
      r < ((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map (Ideal.Quotient.mk P) →
      False)
    (q : PrimeSpectrum (Polynomial R ⧸ P)) :
    ((elementGenerator P b hb).divisor dimE :
        ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) (quotPointMap P q) *
      ((sectionGysinTermOf c dimE b' (quotPointMap P q) :
        ↥(Spec (CommRingCat.of R)) → ℚ) x) = 0 := by
  classical
  by_cases hht : q.asIdeal.height = 1
  swap
  · rw [divisor_apply_eq_zero_of_height_ne P b hb dimE q hht, zero_mul]
  by_cases hb'V : b' ∈ (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal
  · rw [termOf_apply_eq_zero_of_mem c dimE b' _ x hb'V, mul_zero]
  by_cases hle : (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal ≤
      (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal
  swap
  · rw [termOf_apply_eq_zero_of_not_le c dimE b' _ x hb'V hle, mul_zero]
  by_cases hht2 : (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
      (Ideal.Quotient.mk (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal)).height = 1
  swap
  · rw [termOf_apply_eq_zero_of_height_ne c dimE b' _ x hb'V _
      (quotPointMap_quotientPoint _ _ hle) hht2, mul_zero]
  exfalso
  let _ : (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal.IsPrime :=
    (quotPointMap P q : PrimeSpectrum (Polynomial R)).isPrime
  let _ : (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal.IsPrime :=
    (sectionPoint c x : PrimeSpectrum (Polynomial R)).isPrime
  let _ : (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
      (Ideal.Quotient.mk P)).IsPrime :=
    SectionGysinIdentity.map_quotient_isPrime P _ hPQ0
  have hPV : P ≤ (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal :=
    le_quotPointMap_asIdeal P q
  have hmapV : ((quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal).map
      (Ideal.Quotient.mk P) = q.asIdeal := map_quotPointMap_asIdeal P q
  have h1 : (((quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal).map
      (Ideal.Quotient.mk P)).height = 1 := by rw [hmapV]; exact hht
  have hkey : (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
      (Ideal.Quotient.mk P)).height = 2 :=
    SectionGysinIdentity.height_eq_two_ambient P
      (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal
      (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal hPV hle
      (hdim P inferInstance)
      (hdim (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal
        (quotPointMap P q : PrimeSpectrum (Polynomial R)).isPrime) h1 hht2
  rw [not_forall] at hchain
  obtain ⟨r, hchain⟩ := hchain
  rw [not_forall] at hchain
  obtain ⟨r', hchain⟩ := hchain
  simp only [not_forall] at hchain
  obtain ⟨hr, hr', hbot, hrr, hrQ, -⟩ := hchain
  let _ : r.IsPrime := hr
  let _ : r'.IsPrime := hr'
  have h3 := SectionGysinIdentity.three_le_height_of_chain r' r
    (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map (Ideal.Quotient.mk P))
    hbot hrr hrQ
  rw [hkey] at h3
  norm_num at h3

/-- The key termwise identity: under the chain hypothesis the product of the two divisor
coefficients at a prime `q` of `R[T] ⧸ P` is the corresponding summand of Fulton's symmetric
local identity. -/
theorem exists_nat_termProduct
    (hPQ0 : P ≤ (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal)
    [hQp : (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
      (Ideal.Quotient.mk P)).IsPrime]
    (b b' : Polynomial R) (hb : b ∉ P)
    (hchain : ∀ r r' : Ideal (Polynomial R ⧸ P), r.IsPrime → r'.IsPrime → ⊥ < r' → r' < r →
      r < ((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map (Ideal.Quotient.mk P) →
      False)
    (hnoboth : ∀ r : Ideal (Polynomial R ⧸ P), r.IsPrime →
      r < ((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map (Ideal.Quotient.mk P) →
      Ideal.Quotient.mk P b ∈ r → Ideal.Quotient.mk P b' ∉ r)
    (q : PrimeSpectrum (Polynomial R ⧸ P)) :
    ∃ n : ℕ, symTerm (Polynomial R ⧸ P)
        (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map (Ideal.Quotient.mk P))
        (Ideal.Quotient.mk P b) (Ideal.Quotient.mk P b') q = (n : ℕ∞) ∧
      ((elementGenerator P b hb).divisor dimE :
          ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) (quotPointMap P q) *
        ((sectionGysinTermOf c dimE b' (quotPointMap P q) :
          ↥(Spec (CommRingCat.of R)) → ℚ) x) = (n : ℚ) := by
  classical
  let _ : (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal.IsPrime :=
    (quotPointMap P q : PrimeSpectrum (Polynomial R)).isPrime
  let _ : (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal.IsPrime :=
    (sectionPoint c x : PrimeSpectrum (Polynomial R)).isPrime
  have hPV : P ≤ (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal :=
    le_quotPointMap_asIdeal P q
  have hmapV : ((quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal).map
      (Ideal.Quotient.mk P) = q.asIdeal := map_quotPointMap_asIdeal P q
  by_cases hmem : Ideal.Quotient.mk P b ∈ q.asIdeal
  swap
  · refine ⟨0, symTerm_eq_zero _ _ _ q (fun h ↦ hmem h.2), ?_⟩
    rw [divisor_apply_eq_zero_of_notMem P b hb dimE q hmem, zero_mul, Nat.cast_zero]
  by_cases hlt : q.asIdeal < ((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
      (Ideal.Quotient.mk P)
  swap
  · refine ⟨0, symTerm_eq_zero _ _ _ q (fun h ↦ hlt h.1), ?_⟩
    have hz : ((sectionGysinTermOf c dimE b' (quotPointMap P q) :
        ↥(Spec (CommRingCat.of R)) → ℚ) x) = 0 := by
      by_cases hb'V : b' ∈ (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal
      · exact termOf_apply_eq_zero_of_mem c dimE b' _ x hb'V
      by_cases hle : (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal ≤
          (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal
      swap
      · exact termOf_apply_eq_zero_of_not_le c dimE b' _ x hb'V hle
      have hqQ : q.asIdeal ≤ ((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
          (Ideal.Quotient.mk P) := by
        rw [← hmapV]
        exact Ideal.map_mono hle
      have hqeq : q.asIdeal = ((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
          (Ideal.Quotient.mk P) := by
        rcases eq_or_lt_of_le hqQ with h | h
        · exact h
        · exact absurd h hlt
      have hVQ : (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal =
          (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal := by
        have := congrArg (Ideal.comap (Ideal.Quotient.mk P)) hqeq
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
          ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hPQ0] at this
        exact this
      refine termOf_apply_eq_zero_of_height_ne c dimE b' _ x hb'V _
        (quotPointMap_quotientPoint _ _ hle) ?_
      have hbot : (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
          (Ideal.Quotient.mk
            (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal)) = ⊥ :=
        (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker]; exact hVQ.ge)
      change (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
        (Ideal.Quotient.mk
          (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal)).height ≠ 1
      rw [hbot]
      exact height_bot_ne_one
    rw [hz, mul_zero, Nat.cast_zero]
  -- the main case
  have hb'q : Ideal.Quotient.mk P b' ∉ q.asIdeal := hnoboth q.asIdeal q.isPrime hlt hmem
  have hb'V : b' ∉ (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal := hb'q
  have hqbot : q.asIdeal ≠ ⊥ := by
    intro hcon
    refine quotientMk_ne_zero P b hb ?_
    rw [hcon] at hmem
    simpa using hmem
  have hPltV : P < (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal := by
    refine lt_of_le_of_ne hPV ?_
    intro hcon
    refine hqbot ?_
    rw [← hmapV, ← hcon]
    exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker])
  have hle : (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal ≤
      (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal := by
    have h2 : Ideal.comap (Ideal.Quotient.mk P) q.asIdeal ≤
        Ideal.comap (Ideal.Quotient.mk P)
          (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
            (Ideal.Quotient.mk P)) := Ideal.comap_mono hlt.le
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hPQ0] at h2
    exact h2
  have hltV : (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal <
      (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal := by
    refine lt_of_le_of_ne hle ?_
    intro hcon
    refine hlt.ne ?_
    rw [← hmapV, hcon]
  have hq1 : q.asIdeal.height = 1 := by
    rw [← hmapV]
    refine height_map_eq_one_of_no_middle P _ hPltV ?_
    intro W' hW' hPW' hW'V
    let _ : W'.IsPrime := hW'
    refine hchain q.asIdeal (W'.map (Ideal.Quotient.mk P)) q.isPrime
      (SectionGysinIdentity.map_quotient_isPrime P W' hPW'.le)
      (lt_of_le_of_ne bot_le (Ne.symm (map_ne_bot_of_lt P W' hPW'))) ?_ hlt
    rw [← hmapV]
    exact map_lt_map_of_lt P W' _ hPW'.le hW'V
  have hq2 : (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
      (Ideal.Quotient.mk
        (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal)).height = 1 := by
    refine height_map_eq_one_of_no_middle _ _ hltV ?_
    intro W' hW' hVW' hW'Q
    let _ : W'.IsPrime := hW'
    refine hchain (W'.map (Ideal.Quotient.mk P)) q.asIdeal
      (SectionGysinIdentity.map_quotient_isPrime P W' (hPltV.le.trans hVW'.le)) q.isPrime
      (lt_of_le_of_ne bot_le (Ne.symm hqbot)) ?_ ?_
    · rw [← hmapV]
      exact map_lt_map_of_lt P _ W' hPV hVW'
    · exact map_lt_map_of_lt P W' _ (hPltV.le.trans hVW'.le) hW'Q
  have hfactor1 := divisor_apply_eq_ringOrd P b hb dimE q hq1
  let _ : (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
      (Ideal.Quotient.mk
        (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal)).IsPrime :=
    SectionGysinIdentity.map_quotient_isPrime _ _ hle
  have hfactor2 : ((sectionGysinTermOf c dimE b' (quotPointMap P q) :
        ↥(Spec (CommRingCat.of R)) → ℚ) x) =
      ((Ring.ord (Localization.AtPrime
            (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
              (Ideal.Quotient.mk
                (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal)))
          (algebraMap (Polynomial R ⧸ (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal) _
            (Ideal.Quotient.mk _ b'))).toNat : ℚ) :=
    termOf_apply_eq_ringOrd c dimE b' (quotPointMap P q) x hb'V
      (quotientPoint (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal
        (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal
        (sectionPoint c x : PrimeSpectrum (Polynomial R)).isPrime hle)
      (quotPointMap_quotientPoint _ _ hle) hq2
  have hord2 := @SectionGysinIdentity.ring_ord_quot_quot (Polynomial R) _ P
    (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal
    (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal _ _ _ _ hQp hPV hle b'
  have hideal : Ideal.map (algebraMap (Polynomial R ⧸ P)
        (Localization.AtPrime
          (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
            (Ideal.Quotient.mk P))))
        (((quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal).map
          (Ideal.Quotient.mk P)) =
      Ideal.map (algebraMap (Polynomial R ⧸ P)
        (Localization.AtPrime
          (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
            (Ideal.Quotient.mk P)))) q.asIdeal := congrArg _ hmapV
  have hord2' := hord2.trans (SectionGysinIdentity.ring_ord_quotient_congr _ _ hideal _)
  have hne1 := divisor_ringOrd_ne_top P b hb q hq1
  have hne2 : Ring.ord (Localization.AtPrime
        (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
          (Ideal.Quotient.mk
            (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal)))
      (algebraMap (Polynomial R ⧸ (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal) _
        (Ideal.Quotient.mk _ b')) ≠ ⊤ :=
    divisor_ringOrd_ne_top (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal b' hb'V
      (quotientPoint (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal
        (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal
        (sectionPoint c x : PrimeSpectrum (Polynomial R)).isPrime hle) hq2
  obtain ⟨m₁, hm₁⟩ := ENat.ne_top_iff_exists.mp hne1
  obtain ⟨m₂, hm₂⟩ := ENat.ne_top_iff_exists.mp hne2
  refine ⟨m₁ * m₂, ?_, ?_⟩
  · rw [symTerm_of_lt _ _ _ q ⟨hlt, hmem⟩, ← hord2', ← hm₁, ← hm₂, ← Nat.cast_mul]
  · rw [hfactor1, hfactor2, ← hm₁, ← hm₂]
    simp [Nat.cast_mul]

end Termwise

/-! ## The cycle-level symmetric identity -/

section Identity

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- **The cycle-level symmetric local identity.**  Restricting to the section the divisor of `a`
on the subvariety `V(P)` and then the divisor of `T - c` on its components gives the same cycle
on the base as doing it in the other order.  This is the hypothesis `hident` of
`sectionGysin_elementGenerator_mem`, and it is deduced here from Fulton's symmetric local
identity `LocalOrdSymmetry` together with the dimension formula for the quotients of `R[T]`. -/
theorem sectionGysin_elementGenerator_eq_finsum (hsym : LocalOrdSymmetry.{u})
    (hdim : ∀ P' : Ideal (Polynomial R), P'.IsPrime → HasDimensionFormula (Polynomial R ⧸ P'))
    (c : R) (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))
    (P : Ideal (Polynomial R)) [P.IsPrime] (hP : sectionPoly c ∉ P)
    (a : Polynomial R) (ha : a ∉ P)
    (hgood : ∀ Q : Ideal (Polynomial R), Q.IsPrime → P < Q → sectionPoly c ∈ Q →
      (∀ Q' : Ideal (Polynomial R), Q'.IsPrime → P ≤ Q' → Q' < Q → sectionPoly c ∉ Q') →
      a ∉ Q) :
    sectionGysin c dimE ((elementGenerator P a ha).divisor dimE) =
      ∑ᶠ V : ↥(Spec (CommRingCat.of (Polynomial R))),
        ((elementGenerator P (sectionPoly c) hP).divisor dimE :
          ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V • sectionGysinTermOf c dimE a V := by
  classical
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  -- finiteness of the two families of summands
  have hfin : ∀ (bb : Polynomial R) (hbb : bb ∉ P) (bb' : Polynomial R),
      (Function.support fun V ↦ ((elementGenerator P bb hbb).divisor dimE :
        ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V *
          ((sectionGysinTermOf c dimE bb' V : ↥(Spec (CommRingCat.of R)) → ℚ) x)).Finite := by
    intro bb hbb bb'
    refine (AlgebraicCycle.finite_support ((elementGenerator P bb hbb).divisor dimE)).subset ?_
    intro V hV hz0
    apply hV
    simp only [hz0, zero_mul]
  have hsub : ∀ (bb : Polynomial R) (hbb : bb ∉ P) (bb' : Polynomial R),
      (Function.support fun V ↦ ((elementGenerator P bb hbb).divisor dimE :
        ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V *
          ((sectionGysinTermOf c dimE bb' V : ↥(Spec (CommRingCat.of R)) → ℚ) x)) ⊆
        Set.range (quotPointMap P) := by
    intro bb hbb bb' V hV
    rw [mem_range_quotPointMap_iff]
    by_contra hcon
    apply hV
    simp only [elementGenerator_divisor_apply_of_not_le P bb hbb dimE V hcon, zero_mul]
  have hre : ∀ (bb : Polynomial R) (hbb : bb ∉ P) (bb' : Polynomial R),
      (∑ᶠ V, ((elementGenerator P bb hbb).divisor dimE :
        ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V *
          ((sectionGysinTermOf c dimE bb' V : ↥(Spec (CommRingCat.of R)) → ℚ) x)) =
      ∑ᶠ q : PrimeSpectrum (Polynomial R ⧸ P),
        ((elementGenerator P bb hbb).divisor dimE :
          ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) (quotPointMap P q) *
          ((sectionGysinTermOf c dimE bb' (quotPointMap P q) :
            ↥(Spec (CommRingCat.of R)) → ℚ) x) := by
    intro bb hbb bb'
    rw [← finsum_mem_range (f := fun V ↦ ((elementGenerator P bb hbb).divisor dimE :
        ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V *
          ((sectionGysinTermOf c dimE bb' V : ↥(Spec (CommRingCat.of R)) → ℚ) x))
      (quotPointMap_injective P), finsum_mem_def,
      Set.indicator_eq_self.2 (hsub bb hbb bb')]
  have hL := finsum_cycle_apply (fun V ↦ ((elementGenerator P a ha).divisor dimE :
      ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V • sectionGysinTerm c dimE V)
    (finite_support_sectionGysinSummand c dimE ((elementGenerator P a ha).divisor dimE)) x
  have hR := finsum_cycle_apply (fun V ↦ ((elementGenerator P (sectionPoly c) hP).divisor dimE :
      ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) V • sectionGysinTermOf c dimE a V)
    (finite_support_termOfSummand c dimE a
      ((elementGenerator P (sectionPoly c) hP).divisor dimE)) x
  rw [sectionGysin_apply]
  simp only [hL, hR]
  simp only [Function.locallyFinsuppWithin.coe_rational_smul, Pi.smul_apply, smul_eq_mul,
    sectionGysinTerm_eq_termOf]
  rw [hre a ha (sectionPoly c), hre (sectionPoly c) hP a]
  by_cases hPQ0 : P ≤ (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal
  swap
  · have hz : ∀ (bb : Polynomial R) (hbb : bb ∉ P) (bb' : Polynomial R)
        (q : PrimeSpectrum (Polynomial R ⧸ P)),
        ((elementGenerator P bb hbb).divisor dimE :
          ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) (quotPointMap P q) *
          ((sectionGysinTermOf c dimE bb' (quotPointMap P q) :
            ↥(Spec (CommRingCat.of R)) → ℚ) x) = 0 := by
      intro bb hbb bb' q
      by_cases hb'V : bb' ∈ (quotPointMap P q : PrimeSpectrum (Polynomial R)).asIdeal
      · rw [termOf_apply_eq_zero_of_mem c dimE bb' _ x hb'V, mul_zero]
      · rw [termOf_apply_eq_zero_of_not_le c dimE bb' _ x hb'V
          (fun hle ↦ hPQ0 ((le_quotPointMap_asIdeal P q).trans hle)), mul_zero]
    simp only [hz]
  let _ : (sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal.IsPrime :=
    (sectionPoint c x : PrimeSpectrum (Polynomial R)).isPrime
  let _ : (((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
      (Ideal.Quotient.mk P)).IsPrime := SectionGysinIdentity.map_quotient_isPrime P _ hPQ0
  by_cases hchain : ∀ r r' : Ideal (Polynomial R ⧸ P), r.IsPrime → r'.IsPrime → ⊥ < r' →
      r' < r → r < ((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
        (Ideal.Quotient.mk P) → False
  swap
  · simp only [termProduct_eq_zero_of_chain_failure c dimE P x hdim hPQ0 _ _ _ hchain]
  -- no prime strictly below the section point contains both `a` and `T - c`
  have hnb : ∀ r : Ideal (Polynomial R ⧸ P), r.IsPrime →
      r < ((sectionPoint c x : PrimeSpectrum (Polynomial R)).asIdeal).map
        (Ideal.Quotient.mk P) →
      Ideal.Quotient.mk P a ∈ r → Ideal.Quotient.mk P (sectionPoly c) ∈ r → False := by
    intro r hr hrQ hra hrs
    let _ : r.IsPrime := hr
    have hWp : (Ideal.comap (Ideal.Quotient.mk P) r).IsPrime := hr.comap _
    have hPW : P ≤ Ideal.comap (Ideal.Quotient.mk P) r := by
      intro y hy
      change Ideal.Quotient.mk P y ∈ r
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hy]
      exact Ideal.zero_mem _
    have hmapW : (Ideal.comap (Ideal.Quotient.mk P) r).map (Ideal.Quotient.mk P) = r :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective r
    have hsW : sectionPoly c ∈ Ideal.comap (Ideal.Quotient.mk P) r := hrs
    have haW : a ∈ Ideal.comap (Ideal.Quotient.mk P) r := hra
    have hPltW : P < Ideal.comap (Ideal.Quotient.mk P) r :=
      lt_of_le_of_ne hPW fun hcon ↦ hP (hcon ▸ hsW)
    refine hgood (Ideal.comap (Ideal.Quotient.mk P) r) hWp hPltW hsW ?_ haW
    intro W' hW' hPW' hW'W hsW'
    let _ : W'.IsPrime := hW'
    have hPltW' : P < W' := lt_of_le_of_ne hPW' fun hcon ↦ hP (hcon ▸ hsW')
    refine hchain r (W'.map (Ideal.Quotient.mk P)) hr
      (SectionGysinIdentity.map_quotient_isPrime P W' hPW')
      (lt_of_le_of_ne bot_le (Ne.symm (map_ne_bot_of_lt P W' hPltW'))) ?_ hrQ
    rw [← hmapW]
    exact map_lt_map_of_lt P W' _ hPW' hW'W
  -- the two families of natural numbers
  choose n1 hn1a hn1b using fun q ↦ exists_nat_termProduct c dimE P x hPQ0 a (sectionPoly c) ha
    hchain (fun r hr hrQ hra hrs ↦ hnb r hr hrQ hra hrs) q
  choose n2 hn2a hn2b using fun q ↦ exists_nat_termProduct c dimE P x hPQ0 (sectionPoly c) a hP
    hchain (fun r hr hrQ hrs hra ↦ hnb r hr hrQ hra hrs) q
  have hfin1 : (Function.support n1).Finite := by
    refine Set.Finite.subset (Set.Finite.preimage ((quotPointMap_injective P).injOn)
      (hfin a ha (sectionPoly c))) ?_
    intro q hq hcon
    apply hq
    have hzq : ((n1 q : ℚ)) = 0 := (hn1b q).symm.trans hcon
    exact_mod_cast hzq
  have hfin2 : (Function.support n2).Finite := by
    refine Set.Finite.subset (Set.Finite.preimage ((quotPointMap_injective P).injOn)
      (hfin (sectionPoly c) hP a)) ?_
    intro q hq hcon
    apply hq
    have hzq : ((n2 q : ℚ)) = 0 := (hn2b q).symm.trans hcon
    exact_mod_cast hzq
  simp only [hn1b, hn2b]
  refine finsum_natCast_eq_of_enat n1 n2 hfin1 hfin2 ?_
  simp only [← hn1a, ← hn2a]
  exact (localOrdSymmetry_symTerm hsym (Polynomial R ⧸ P) _ (Ideal.Quotient.mk P a)
    (Ideal.Quotient.mk P (sectionPoly c)) (quotientMk_ne_zero P a ha)
    (quotientMk_ne_zero P (sectionPoly c) hP) hchain
    (fun r hr hrQ hra hrs ↦ by
      rcases eq_or_lt_of_le hrQ with h | h
      · exact h
      · exact (hnb r hr h hra hrs).elim)).symm

/-- **(B)** with the symmetric local identity discharged: the Gysin map of the section takes the
divisor of a polynomial in good position on a subvariety of the total space to a
rational-equivalence relation on the base. -/
theorem sectionGysin_elementGenerator_mem' (hsym : LocalOrdSymmetry.{u})
    (hdim : ∀ P' : Ideal (Polynomial R), P'.IsPrime → HasDimensionFormula (Polynomial R ⧸ P'))
    (c : R) (dimX : DimensionFunction (Spec (CommRingCat.of R)))
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))
    (P : Ideal (Polynomial R)) [P.IsPrime] (hP : sectionPoly c ∉ P)
    (a : Polynomial R) (ha : a ∉ P)
    (hgood : ∀ Q : Ideal (Polynomial R), Q.IsPrime → P < Q → sectionPoly c ∈ Q →
      (∀ Q' : Ideal (Polynomial R), Q'.IsPrime → P ≤ Q' → Q' < Q → sectionPoly c ∉ Q') →
      a ∉ Q) :
    sectionGysin c dimE ((elementGenerator P a ha).divisor dimE) ∈
      totalRationalRelations (Spec (CommRingCat.of R)) dimX :=
  sectionGysin_elementGenerator_mem c dimX dimE P hP a ha hgood
    (sectionGysin_elementGenerator_eq_finsum hsym hdim c dimE P hP a ha hgood)

end Identity

end VectorBundle

end GromovWitten.AlgebraicGeometry.IntersectionTheory
