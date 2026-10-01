/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.KeyFormula
import GromovWitten.Algebra.TameKeyLemma
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FiniteTypeDimension

/-!
# The first Chern class on Chow groups, unconditionally

KeyFormula.lean constructs `c₁(L) : A_{i+1}(X) → A_i(X)` and proves that first Chern classes
commute, for an arbitrary *symbol family* satisfying three hypotheses (`hmul`, `hnorm`, `hkey`).
This file instantiates the symbol family with the tame symbol of TameSymbol.lean and discharges
the three hypotheses: bimultiplicativity (T3), normalisation (T4), and the key lemma (Stacks
42.6.3, TameKeyLemma.lean) transported from the two-dimensional local domain
`pointStalk (w ⤳ Q)` to the scheme.

The setting is a scheme `X` with `[IsLocallyNoetherian X] [NoetherianSpace X]`, a dimension
function `dim` with `hcov : HomogeneityLocal.CovByDimension dim`, and
`hU : ∀ x, UnitDifferences (X.presheaf.stalk x)` (needed to define the tame symbol).  Over an
infinite field both `hU` and `hcov` (for the canonical dimension function) are proved.

## Main results

* `tamePointSymbol hU`: the symbol family `h ↦ ∂_{pointStalk h}` (tame symbol of the point stalk,
  with values in `κ(v)` via `pointStalkResidueEquiv`) at specialisations `h : w ⤳ v` with
  `pointStalk h` of Krull dimension one, and `1` otherwise.
* `tamePointSymbol_isBimultiplicative`, `tamePointSymbol_isNormalized`,
  `tamePointSymbol_satisfiesKeyLemma`: the hypotheses `hmul`, `hnorm`, `hkey` of KeyFormula.lean.
* `pointOrd_tamePointSymbol_eq_ordZ`: for `w ⤳ v ⤳ Q`, the order along `v ⤳ Q` of the tame point
  symbol at `w ⤳ v` is the order on `A ⧸ q_v` of the tame symbol of `A_{q_v}`, where
  `A = pointStalk (w ⤳ Q)` and `q_v = pointStalkPrime (w ⤳ v) (v ⤳ Q)`.
* `heightOnePointStalkPrimeEquiv`: the points `v` between `w` and `Q` of dimension `dim w - 1`
  correspond to the height-one primes of `pointStalk (w ⤳ Q)`.
* `killsRelations_of_unitDifferences`: `c₁(L)` kills rational equivalence, for every `L` and `i`.
* `firstChernClass hU hcov L i : A_{i+1}(X) →ₗ[ℚ] A_i(X)`, with `firstChernClass_quotientMap`
  and the commutativity `firstChernClass_comm` (Stacks 42.28.2, 42.28.3).
* Over an infinite field `k`, for `f : X ⟶ Spec k` locally of finite type with `X` a Noetherian
  topological space: `unitDifferences_stalk_of_infinite`, `covByDimension_finiteTypeDimension`,
  `killsRelations_of_field`, `firstChernClassOfField` and `firstChernClassOfField_comm`, with
  the canonical dimension function `FiniteTypeDimension.dimensionFunction f`.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace IsLocalRing
open GromovWitten.Algebra.Tame

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open VectorBundle (UnitDifferences)

/-! ## The tame symbol family -/

section TameFamily

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **The tame point symbol.** For a specialisation `h : w ⤳ v` with `pointStalk h` of Krull
dimension one, the tame symbol of the one-dimensional Noetherian local domain `pointStalk h`
(with fraction field `κ(w)`), transported to `κ(v)ˣ` by `pointStalkResidueEquiv h`; the junk
value `1` otherwise. -/
noncomputable def tamePointSymbol (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x)) :
    PointSymbolFamily X := fun {w v} h f g ↦
  if hd : ringKrullDim (pointStalk h) = 1 then
    haveI := krullDimLE_one_pointStalk_of_eq_one hd
    Units.map (pointStalkResidueEquiv h).toRingHom.toMonoidHom
      (tameSymbol (pointStalk h) (X.residueField w) (unitDifferences_pointStalk h (hU v)) f g)
  else 1

variable (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x))

/-- In Krull dimension one, `tamePointSymbol` is the transported tame symbol. -/
theorem tamePointSymbol_of_eq_one {w v : X} (h : w ⤳ v) (hd : ringKrullDim (pointStalk h) = 1)
    [Ring.KrullDimLE 1 (pointStalk h)] (f g : (X.residueField w)ˣ) :
    tamePointSymbol hU h f g = Units.map (pointStalkResidueEquiv h).toRingHom.toMonoidHom
      (tameSymbol (pointStalk h) (X.residueField w) (unitDifferences_pointStalk h (hU v)) f g) := by
  rw [tamePointSymbol, dif_pos hd]

/-- `ordZ` of the point stalk is `pointOrd`, in Krull dimension one. -/
theorem ordZ_pointStalk_eq_pointOrd {w v : X} (h : w ⤳ v) (hd : ringKrullDim (pointStalk h) = 1)
    [Ring.KrullDimLE 1 (pointStalk h)] (g : (X.residueField w)ˣ) :
    ordZ (pointStalk h) g = pointOrd h g := by
  rw [ordZ, ← pointOrd_of_eq_one hd]
  rfl

/-- **T3 for the tame point symbol**: `tamePointSymbol hU` is bimultiplicative. -/
theorem tamePointSymbol_isBimultiplicative :
    PointSymbolFamily.IsBimultiplicative (tamePointSymbol hU) := by
  intro w v h hd
  dsimp only
  have := krullDimLE_one_pointStalk_of_eq_one hd
  refine ⟨fun f f' g ↦ ?_, fun f g g' ↦ ?_⟩
  · rw [tamePointSymbol_of_eq_one hU h hd, tamePointSymbol_of_eq_one hU h hd,
      tamePointSymbol_of_eq_one hU h hd, tameSymbol_mul_left, map_mul]
  · rw [tamePointSymbol_of_eq_one hU h hd, tamePointSymbol_of_eq_one hU h hd,
      tamePointSymbol_of_eq_one hU h hd, tameSymbol_mul_right, map_mul]

/-- **T4 for the tame point symbol**: `tamePointSymbol hU` is normalised on point-stalk units. -/
theorem tamePointSymbol_isNormalized :
    PointSymbolFamily.IsNormalized (tamePointSymbol hU) := by
  intro w v h hd u g
  dsimp only
  have := krullDimLE_one_pointStalk_of_eq_one hd
  have hu : pointStalkUnitIncl h u =
      Units.map (algebraMap (pointStalk h) (X.residueField w) :
        pointStalk h →* X.residueField w) u := rfl
  have hr : Units.map (pointStalkResidueEquiv h).toRingHom.toMonoidHom (resUnits _ u) =
      pointStalkResidueUnit h u := rfl
  refine ⟨?_, ?_⟩
  · rw [tamePointSymbol_of_eq_one hU h hd, hu, tameSymbol_units_left, map_zpow, hr,
      ordZ_pointStalk_eq_pointOrd h hd]
  · rw [tamePointSymbol_of_eq_one hU h hd, hu, tameSymbol_units_right, map_zpow, hr,
      ordZ_pointStalk_eq_pointOrd h hd]

end TameFamily

/-! ## Transport between `pointStalk (w ⤳ v)` and the localization of `pointStalk (w ⤳ Q)` -/

section Transport

variable {X : Scheme.{u}} {w v Q : X}

/-- The isomorphism `Localization.AtPrime q_v ≃+* pointStalk (w ⤳ v)`, where
`q_v = pointStalkPrime hwv hvQ` is the prime of `pointStalk (w ⤳ Q)` given by `v`. -/
noncomputable def pointStalkAtPrimeEquiv (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    Localization.AtPrime (pointStalkPrime hwv hvQ) ≃+* pointStalk hwv :=
  letI := pointStalkAlgebra hwv hvQ
  haveI := pointStalk_isLocalization hwv hvQ
  (IsLocalization.algEquiv (pointStalkPrime hwv hvQ).primeCompl
    (Localization.AtPrime (pointStalkPrime hwv hvQ)) (pointStalk hwv)).toRingEquiv

/-- `pointStalkAtPrimeEquiv` is compatible with the maps from `pointStalk (w ⤳ Q)`. -/
theorem pointStalkAtPrimeEquiv_algebraMap (hwv : w ⤳ v) (hvQ : v ⤳ Q)
    (a : pointStalk (hwv.trans hvQ)) :
    pointStalkAtPrimeEquiv hwv hvQ (algebraMap _ (Localization.AtPrime (pointStalkPrime hwv hvQ))
      a) = pointStalkSpecializes hwv hvQ a := by
  let _ := pointStalkAlgebra hwv hvQ
  have := pointStalk_isLocalization hwv hvQ
  exact (IsLocalization.algEquiv (pointStalkPrime hwv hvQ).primeCompl
    (Localization.AtPrime (pointStalkPrime hwv hvQ)) (pointStalk hwv)).commutes a

/-- The isomorphism `κ(q_v) ≃+* κ(v)` of residue fields, where `κ(q_v)` is the residue field of
the prime `q_v = pointStalkPrime hwv hvQ` of `pointStalk (w ⤳ Q)`. -/
noncomputable def pointStalkPrimeResidueEquiv (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    (pointStalkPrime hwv hvQ).ResidueField ≃+* X.residueField v :=
  (ResidueField.mapEquiv (pointStalkAtPrimeEquiv hwv hvQ)).trans (pointStalkResidueEquiv hwv)

/-- **The residue-field square.** `pointStalkPrimeResidueEquiv` carries the canonical map
`A ⧸ q_v → κ(q_v)` to the canonical map `pointStalk (v ⤳ Q) → κ(v)`, via
`pointStalkQuotientEquiv : A ⧸ q_v ≃+* pointStalk (v ⤳ Q)`. -/
theorem pointStalkPrimeResidueEquiv_algebraMap (hwv : w ⤳ v) (hvQ : v ⤳ Q)
    (r : pointStalk (hwv.trans hvQ) ⧸ pointStalkPrime hwv hvQ) :
    pointStalkPrimeResidueEquiv hwv hvQ
        (algebraMap _ (pointStalkPrime hwv hvQ).ResidueField r) =
      algebraMap (pointStalk hvQ) (X.residueField v) (pointStalkQuotientEquiv hwv hvQ r) := by
  have := RingHom.congr_fun (pointStalkResidue_comm hwv hvQ) r
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at this
  rw [← this]
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [pointStalkPrimeResidueEquiv, RingEquiv.trans_apply]
  congr 1
  rw [pointStalkQuotientToResidueField_mk, Ideal.algebraMap_quotient_residueField_mk,
    IsScalarTower.algebraMap_apply (pointStalk (hwv.trans hvQ))
      (Localization.AtPrime (pointStalkPrime hwv hvQ)), ResidueField.mapEquiv_apply]
  erw [ResidueField.map_residue]
  congr 1
  exact pointStalkAtPrimeEquiv_algebraMap hwv hvQ _

/-- The quotient `pointStalk (w ⤳ Q) ⧸ q_v` has the Krull dimension of `pointStalk (v ⤳ Q)`. -/
theorem ringKrullDim_quotient_pointStalkPrime (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    ringKrullDim (pointStalk (hwv.trans hvQ) ⧸ pointStalkPrime hwv hvQ) =
      ringKrullDim (pointStalk hvQ) :=
  ringKrullDim_eq_of_ringEquiv (pointStalkQuotientEquiv hwv hvQ)

/-- The localization `Localization.AtPrime q_v` has the Krull dimension of
`pointStalk (w ⤳ v)`. -/
theorem ringKrullDim_atPrime_pointStalkPrime (hwv : w ⤳ v) (hvQ : v ⤳ Q) :
    ringKrullDim (Localization.AtPrime (pointStalkPrime hwv hvQ)) =
      ringKrullDim (pointStalk hwv) :=
  ringKrullDim_eq_of_ringEquiv (pointStalkAtPrimeEquiv hwv hvQ)

/-- Under `CovByDimension`, if `dim w = dim v + k` then `pointStalk (w ⤳ v)` has Krull
dimension `k`. -/
theorem ringKrullDim_pointStalk_of_dim_eq_add {dim : DimensionFunction X}
    (hcov : HomogeneityLocal.CovByDimension dim) (h : w ⤳ v) {k : ℕ} (hd : dim w = dim v + k) :
    ringKrullDim (pointStalk h) = k := by
  rw [ringKrullDim_pointStalk dim hcov h, hd, add_sub_cancel_left, Int.toNat_natCast]

variable [IsLocallyNoetherian X]

/-- **Transport of the tame symbol and of its order.** Let `w ⤳ v ⤳ Q` with `pointStalk (w ⤳ v)`
and `pointStalk (v ⤳ Q)` of Krull dimension one, write `A = pointStalk (w ⤳ Q)` and
`q = pointStalkPrime hwv hvQ`, and equip `A_q = Localization.AtPrime q` with any `κ(w)`-algebra
structure compatible with `A → κ(w)`.  Then the order along `v ⤳ Q` of the tame point symbol at
`w ⤳ v` is the order `ordZ (A ⧸ q)` of the tame symbol of `A_q`, an element of `κ(q)ˣ`. -/
theorem pointOrd_tamePointSymbol_eq_ordZ (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x))
    (hwv : w ⤳ v) (hvQ : v ⤳ Q) (hd₁ : ringKrullDim (pointStalk hwv) = 1)
    (hd₂ : ringKrullDim (pointStalk hvQ) = 1)
    [Algebra (Localization.AtPrime (pointStalkPrime hwv hvQ)) (X.residueField w)]
    [IsScalarTower (pointStalk (hwv.trans hvQ)) (Localization.AtPrime (pointStalkPrime hwv hvQ))
      (X.residueField w)]
    [IsFractionRing (Localization.AtPrime (pointStalkPrime hwv hvQ)) (X.residueField w)]
    [Ring.KrullDimLE 1 (Localization.AtPrime (pointStalkPrime hwv hvQ))]
    [Ring.KrullDimLE 1 (pointStalk (hwv.trans hvQ) ⧸ pointStalkPrime hwv hvQ)]
    (hUq : UnitDifferences (Localization.AtPrime (pointStalkPrime hwv hvQ)))
    (f g : (X.residueField w)ˣ) :
    pointOrd hvQ (tamePointSymbol hU hwv f g) =
      ordZ (pointStalk (hwv.trans hvQ) ⧸ pointStalkPrime hwv hvQ)
        (tameSymbol (Localization.AtPrime (pointStalkPrime hwv hvQ)) (X.residueField w) hUq
          f g : (pointStalkPrime hwv hvQ).ResidueField ˣ) := by
  have := krullDimLE_one_pointStalk_of_eq_one hd₁
  have := krullDimLE_one_pointStalk_of_eq_one hd₂
  set q := pointStalkPrime hwv hvQ
  set e := pointStalkAtPrimeEquiv hwv hvQ
  have hσ : ∀ d : Localization.AtPrime q, (RingEquiv.refl (X.residueField w))
      (algebraMap (Localization.AtPrime q) _ d) =
        algebraMap (pointStalk hwv) (X.residueField w) (e d) := by
    have hext : (algebraMap (Localization.AtPrime q) (X.residueField w)) =
        (algebraMap (pointStalk hwv) (X.residueField w)).comp e.toRingHom := by
      refine IsLocalization.ringHom_ext q.primeCompl (RingHom.ext fun a ↦ ?_)
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        pointStalkAtPrimeEquiv_algebraMap]
      exact (RingHom.congr_fun (algebraMap_comp_pointStalkSpecializes hwv hvQ) a).symm
    exact fun d ↦ RingHom.congr_fun hext d
  have hT := tameSymbol_ringEquiv e (RingEquiv.refl _) hσ hUq
    (unitDifferences_pointStalk hwv (hU v)) f g
  have e1 : ∀ x : (X.residueField w)ˣ,
      Units.map ((RingEquiv.refl (X.residueField w)) : X.residueField w →* X.residueField w) x =
        x := fun x ↦ Units.ext rfl
  rw [e1, e1] at hT
  rw [tamePointSymbol_of_eq_one hU hwv hd₁, hT]
  apply WithZero.exp_injective
  rw [exp_ordZ]
  change ((Multiplicative.ofAdd (pointOrd hvQ _) : Multiplicative ℤ) :
    WithZero (Multiplicative ℤ)) = _
  rw [pointOrd_of_eq_one hd₂]
  exact ordFrac_ringEquiv (pointStalkQuotientEquiv hwv hvQ) (pointStalkPrimeResidueEquiv hwv hvQ)
    (pointStalkPrimeResidueEquiv_algebraMap hwv hvQ) _

end Transport

/-! ## Reindexing: codimension-one points between `w` and `Q` versus height-one primes -/

section Reindex

variable {X : Scheme.{u}} {w Q : X} (dim : DimensionFunction X)
  (hcov : HomogeneityLocal.CovByDimension dim)

/-- For `w ⤳ Q` and a point `v` with `w ⤳ v ⤳ Q` and `dim w = dim v + 1`, the height-one prime
`pointStalkPrime (w ⤳ v) (v ⤳ Q)` of `pointStalk (w ⤳ Q)`. -/
noncomputable def heightOnePointStalkPrime (hwQ : w ⤳ Q)
    (v : {v : X // w ⤳ v ∧ v ⤳ Q ∧ dim w = dim v + 1}) :
    {q : PrimeSpectrum (pointStalk hwQ) // q.asIdeal.height = 1} :=
  ⟨⟨pointStalkPrime v.2.1 v.2.2.1, inferInstance⟩,
    (height_pointStalkPrime_eq_one_iff dim hcov v.2.1 v.2.2.1).2 v.2.2.2⟩

/-- `heightOnePointStalkPrime` is a bijection. -/
theorem heightOnePointStalkPrime_bijective (hwQ : w ⤳ Q) :
    Function.Bijective (heightOnePointStalkPrime dim hcov hwQ) := by
  refine ⟨fun v₁ v₂ h ↦ Subtype.ext (pointStalkPrime_injective v₁.2.1 v₁.2.2.1 v₂.2.1 v₂.2.2.1
    (congrArg (fun q : {q : PrimeSpectrum (pointStalk hwQ) // q.asIdeal.height = 1} ↦
      q.1.asIdeal) h)), fun q ↦ ?_⟩
  obtain ⟨v, hwv, hvQ, hq⟩ := exists_pointStalkPrime_eq hwQ q.1.asIdeal
  refine ⟨⟨v, hwv, hvQ, (height_pointStalkPrime_eq_one_iff dim hcov hwv hvQ).1 ?_⟩, ?_⟩
  · rw [hq]
    exact q.2
  · exact Subtype.ext (PrimeSpectrum.ext hq)

/-- For `w ⤳ Q`, the points `v` with `w ⤳ v ⤳ Q` and `dim w = dim v + 1` are in bijection with the
height-one primes of `pointStalk (w ⤳ Q)`, via `v ↦ pointStalkPrime (w ⤳ v) (v ⤳ Q)`. -/
noncomputable def heightOnePointStalkPrimeEquiv (hwQ : w ⤳ Q) :
    {v : X // w ⤳ v ∧ v ⤳ Q ∧ dim w = dim v + 1} ≃
      {q : PrimeSpectrum (pointStalk hwQ) // q.asIdeal.height = 1} :=
  Equiv.ofBijective _ (heightOnePointStalkPrime_bijective dim hcov hwQ)

/-- The height-one prime attached to `v` is `pointStalkPrime (w ⤳ v) (v ⤳ Q)`. -/
theorem heightOnePointStalkPrimeEquiv_apply (hwQ : w ⤳ Q)
    (v : {v : X // w ⤳ v ∧ v ⤳ Q ∧ dim w = dim v + 1}) :
    heightOnePointStalkPrimeEquiv dim hcov hwQ v = heightOnePointStalkPrime dim hcov hwQ v :=
  rfl

variable [IsLocallyNoetherian X]

/-- **Reduction of `SatisfiesKeyLemma` to an algebraic key lemma.**  Suppose that for every
`w ⤳ Q` with `dim w = dim Q + 2` a function `T hwQ` on height-one primes of
`pointStalk (w ⤳ Q)` (and pairs `f g`) sums to zero, and that at the prime attached to each `v`
it computes `pointOrd (v ⤳ Q) (symb (w ⤳ v) f g)`.  Then `symb` satisfies the key lemma. -/
theorem PointSymbolFamily.satisfiesKeyLemma_of_heightOne (symb : PointSymbolFamily X)
    (T : ∀ {w Q : X} (hwQ : w ⤳ Q), {q : PrimeSpectrum (pointStalk hwQ) // q.asIdeal.height = 1} →
      (X.residueField w)ˣ → (X.residueField w)ˣ → ℤ)
    (hsum : ∀ {w Q : X} (hwQ : w ⤳ Q), dim w = dim Q + 2 → ∀ f g : (X.residueField w)ˣ,
      ∑ᶠ q, T hwQ q f g = 0)
    (hpt : ∀ {w Q : X} (hwQ : w ⤳ Q), dim w = dim Q + 2 →
      ∀ (v : {v : X // w ⤳ v ∧ v ⤳ Q ∧ dim w = dim v + 1}) (f g : (X.residueField w)ˣ),
        pointOrd v.2.2.1 (symb v.2.1 f g) =
          T hwQ (heightOnePointStalkPrimeEquiv dim hcov hwQ v) f g) :
    symb.SatisfiesKeyLemma dim := by
  intro w Q hwQ hd f g
  rw [finsum_congr (hpt hwQ hd · f g)]
  rw [finsum_comp_equiv (heightOnePointStalkPrimeEquiv dim hcov hwQ)
    (f := fun q ↦ T hwQ q f g)]
  exact hsum hwQ hd f g

end Reindex

/-! ## The key lemma for the tame point symbol -/

section KeyLemma

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **The key lemma for the tame point symbol** (Stacks 42.6.3 transported to `X`): for `w ⤳ Q`
with `dim w = dim Q + 2` and `f, g ∈ κ(w)ˣ`, `∑_v ord_{v ⤳ Q} (∂_{w ⤳ v}(f, g)) = 0`, the sum
over the points `v` with `w ⤳ v ⤳ Q` and `dim v = dim w - 1`.  Proof: reindex by the height-one
primes of the two-dimensional local domain `pointStalk (w ⤳ Q)` and apply
`finsum_tameOrd_eq_zero` of TameKeyLemma.lean, using `pointOrd_tamePointSymbol_eq_ordZ`. -/
theorem tamePointSymbol_satisfiesKeyLemma (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x))
    {dim : DimensionFunction X} (hcov : HomogeneityLocal.CovByDimension dim) :
    PointSymbolFamily.SatisfiesKeyLemma dim (tamePointSymbol hU) := by
  refine PointSymbolFamily.satisfiesKeyLemma_of_heightOne dim hcov _
    (fun {w Q} hwQ q f g ↦ tameOrd (pointStalk hwQ) (X.residueField w)
      (unitDifferences_pointStalk hwQ (hU Q)) q f g)
    (fun {w Q} hwQ hd f g ↦ finsum_tameOrd_eq_zero
      (ringKrullDim_pointStalk_of_dim_eq_add hcov hwQ (k := 2) hd) _ f g)
    (fun {w Q} hwQ hd v f g ↦ ?_)
  obtain ⟨v, hwv, hvQ, hdv⟩ := v
  have hd₁ : ringKrullDim (pointStalk hwv) = 1 :=
    ringKrullDim_pointStalk_of_dim_eq_add hcov hwv (k := 1) hdv
  have hd₂ : ringKrullDim (pointStalk hvQ) = 1 :=
    ringKrullDim_pointStalk_of_dim_eq_add hcov hvQ (k := 1) (by push_cast; omega)
  have hq : Ring.KrullDimLE 1 (pointStalk (hwv.trans hvQ) ⧸ pointStalkPrime hwv hvQ) := by
    rw [Ring.krullDimLE_iff, ringKrullDim_quotient_pointStalkPrime, hd₂]
    rfl
  rw [heightOnePointStalkPrimeEquiv_apply]
  dsimp only
  have hq' : Ring.KrullDimLE 1
    (pointStalk hwQ ⧸ (heightOnePointStalkPrime dim hcov hwQ ⟨v, hwv, hvQ, hdv⟩).1.asIdeal) := hq
  rw [tameOrd, dif_pos hq']
  let _ := atPrimeAlgebra (X.residueField w) (pointStalkPrime hwv hvQ)
  have := atPrime_isScalarTower (X.residueField w) (pointStalkPrime hwv hvQ)
  have := atPrime_isFractionRing (X.residueField w) (pointStalkPrime hwv hvQ)
  have : Ring.KrullDimLE 1 (Localization.AtPrime (pointStalkPrime hwv hvQ)) := by
    rw [Ring.krullDimLE_iff, ringKrullDim_atPrime_pointStalkPrime, hd₁]
    rfl
  exact pointOrd_tamePointSymbol_eq_ordZ hU hwv hvQ hd₁ hd₂ _ f g

end KeyLemma

/-! ## `c₁` on Chow groups -/

section FirstChernClass

open LineBundleInjective

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [NoetherianSpace X]

/-- **`c₁` factors through rational equivalence** (Stacks, Lemma 42.28.2), for every line bundle
`L` and every `i`, on a locally Noetherian scheme whose underlying space is Noetherian, whose
stalks have unit differences, and whose dimension function `dim` satisfies `CovByDimension`. -/
theorem killsRelations_of_unitDifferences (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x))
    {dim : DimensionFunction X} (hcov : HomogeneityLocal.CovByDimension dim)
    (L : LineBundleData X) (i : ℤ) : KillsRelations L dim hcov i :=
  killsRelations_of_symbol (tamePointSymbol hU) (tamePointSymbol_isBimultiplicative hU)
    (tamePointSymbol_isNormalized hU) (tamePointSymbol_satisfiesKeyLemma hU hcov) hcov L i

/-- **The first Chern class on Chow groups**, `c₁(L) : A_{i+1}(X) →ₗ[ℚ] A_i(X)`, for every line
bundle `L`, under the hypotheses of `killsRelations_of_unitDifferences`.  It is `c1` of
FirstChernClass.lean, induced by `c1Cycle L dim i`. -/
noncomputable def firstChernClass (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x))
    {dim : DimensionFunction X} (hcov : HomogeneityLocal.CovByDimension dim)
    (L : LineBundleData X) (i : ℤ) :
    (chowSystem dim (i + 1)).ChowGroup →ₗ[ℚ] (chowSystem dim i).ChowGroup :=
  c1 (killsRelations_of_unitDifferences hU hcov L i)

/-- `firstChernClass` on the class of a cycle is `c1Cycle`. -/
theorem firstChernClass_quotientMap (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x))
    {dim : DimensionFunction X} (hcov : HomogeneityLocal.CovByDimension dim)
    (L : LineBundleData X) (i : ℤ) (α : cyclesOfDimension X dim (i + 1)) :
    firstChernClass hU hcov L i ((chowSystem dim (i + 1)).quotientMap α) = c1Cycle L dim i α :=
  c1_quotientMap_single _ α

/-- **Commutativity of first Chern classes** (Stacks, Lemma 42.28.3): for line bundles `L`, `N`
and `α ∈ A_{i+2}(X)`, `c₁(L) (c₁(N) α) = c₁(N) (c₁(L) α)`. -/
theorem firstChernClass_comm (hU : ∀ x : X, UnitDifferences (X.presheaf.stalk x))
    {dim : DimensionFunction X} (hcov : HomogeneityLocal.CovByDimension dim)
    (L N : LineBundleData X) (i : ℤ) (α : (chowSystem dim (i + 1 + 1)).ChowGroup) :
    firstChernClass hU hcov L i (firstChernClass hU hcov N (i + 1) α) =
      firstChernClass hU hcov N i (firstChernClass hU hcov L (i + 1) α) :=
  c1_comm_of_symbol (tamePointSymbol hU) (tamePointSymbol_isBimultiplicative hU)
    (tamePointSymbol_isNormalized hU) (tamePointSymbol_satisfiesKeyLemma hU hcov) hcov L N _ _ _ _ α

end FirstChernClass

/-! ## Schemes locally of finite type over an infinite field -/

section Field

open LineBundleInjective

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

include f in
/-- Over an infinite field `k`, every stalk of a `k`-scheme has unit differences (the image of
`k` in the stalk). -/
theorem unitDifferences_stalk_of_infinite [Infinite k] (x : X) :
    UnitDifferences (X.presheaf.stalk x) :=
  unitDifferences_of_ringHom ((X.presheaf.germ ⊤ x trivial).hom.comp
    ((Scheme.Hom.appTop f).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom))
    (VectorBundle.unitDifferences_of_field k k)

/-- The canonical dimension function of a scheme locally of finite type over a field satisfies
`CovByDimension`: it is Zariski-local, and on an affine open it follows from the dimension
formula for finitely generated algebras over a field. -/
theorem covByDimension_finiteTypeDimension [LocallyOfFiniteType f] :
    HomogeneityLocal.CovByDimension (FiniteTypeDimension.dimensionFunction f) := by
  have _ : ∀ U : X.affineOpens, IsOpenImmersion U.2.fromSpec := fun U ↦
    U.2.isOpenImmersion_fromSpec
  refine HomogeneityLocal.covByDimension_of_cover (fun U : X.affineOpens ↦ U.2.fromSpec)
    (hopen := fun U ↦ U.2.isOpenImmersion_fromSpec) ?_ (FiniteTypeDimension.dimensionFunction f)
    (fun U ↦ FiniteTypeDimension.dimensionFunction (U.2.fromSpec ≫ f))
    (fun U y ↦ FiniteTypeDimension.dimensionFunction_comp f _ y)
    (fun U ↦ HomogeneityLocal.covByDimension_of_dimensionFormula _ fun P hP ↦
      HomogeneityLocal.hasDimensionFormula_of_universal
        (FiniteTypeDimension.hasUniversalDimensionFormula_sections f U.1 U.2) P hP)
  rw [← AlgebraicGeometry.iSup_affineOpens_eq_top X]
  exact iSup_congr fun U ↦ U.2.opensRange_fromSpec

variable [Infinite k] [LocallyOfFiniteType f] [NoetherianSpace X]

/-- **`c₁` factors through rational equivalence over an infinite field**: for a scheme `X` locally
of finite type over an infinite field `k` whose underlying space is Noetherian, with its canonical
dimension function, `c₁(L)` kills rational equivalence for every line bundle `L` and every `i`. -/
theorem killsRelations_of_field (L : LineBundleData X) (i : ℤ) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian f
    KillsRelations L (FiniteTypeDimension.dimensionFunction f)
      (covByDimension_finiteTypeDimension f) i :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  killsRelations_of_unitDifferences (unitDifferences_stalk_of_infinite f) _ L i

/-- **The first Chern class on Chow groups over an infinite field**,
`c₁(L) : A_{i+1}(X) →ₗ[ℚ] A_i(X)`, for `X` locally of finite type over an infinite field whose
underlying space is Noetherian, graded by the canonical dimension function. -/
noncomputable def firstChernClassOfField (L : LineBundleData X) (i : ℤ) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian f
    (chowSystem (FiniteTypeDimension.dimensionFunction f) (i + 1)).ChowGroup →ₗ[ℚ]
      (chowSystem (FiniteTypeDimension.dimensionFunction f) i).ChowGroup :=
  haveI := LocallyOfFiniteType.isLocallyNoetherian f
  firstChernClass (unitDifferences_stalk_of_infinite f) (covByDimension_finiteTypeDimension f) L i

/-- **Commutativity of first Chern classes over an infinite field.** -/
theorem firstChernClassOfField_comm (L N : LineBundleData X) (i : ℤ)
    (α : (haveI := LocallyOfFiniteType.isLocallyNoetherian f
      chowSystem (FiniteTypeDimension.dimensionFunction f) (i + 1 + 1)).ChowGroup) :
    firstChernClassOfField f L i (firstChernClassOfField f N (i + 1) α) =
      firstChernClassOfField f N i (firstChernClassOfField f L (i + 1) α) :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  firstChernClass_comm (unitDifferences_stalk_of_infinite f) (covByDimension_finiteTypeDimension f)
    L N i α

end Field

end GromovWitten.AlgebraicGeometry.IntersectionTheory
