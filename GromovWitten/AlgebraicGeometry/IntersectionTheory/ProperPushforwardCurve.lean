/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.Algebra.OrdFracIntegral
import GromovWitten.AlgebraicGeometry.IntersectionTheory.GraphClosure
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperPushforwardChow

/-!
# Proper pushforward of a principal divisor when the dimension drops by one

Let `f : X ⟶ Y` be a proper morphism of schemes locally of finite type over a field `k`, and
`(W, φ)` a generator of `X` (an integral closed subscheme with generic point `w` and a nonzero
rational function).  Round 23 treated the cases `dim f(w) = dim w` (`f_* div φ = div (Nm φ)`)
and `dim f(w) ≤ dim w - 2` (`f_* div φ = 0` for dimension reasons).  This file proves the
remaining case of Fulton, *Intersection Theory*, Prop. 1.4 (b) / Stacks, Lemma 42.20.3:
if `dim f(w) = dim w - 1` then `f_* div(φ) = 0`.  Consequently the proper pushforward descends to
rational Chow groups along every proper morphism, and a scheme proper over `k` has a degree map
`A₀(X) → ℚ`.

The integral form (Theorem C') concerns a proper dominant `h : V ⟶ V'` of integral schemes with
`dim V' = dim V - 1`, writing `K = K(V')`, `L = K(V)`.  If `φ` is algebraic over `K`, then `φ`
and `φ⁻¹` are integral over every local ring `𝒪_{V,x}` with `h x` generic, so `ord_x φ = 0` at
every point that can contribute (Case A).  If `φ` is transcendental over `K`, the closure of the
graph of `φ` in `ℙ¹_V` gives (`GraphClosure`) `h_* div(φ) = d • D` with `d ∈ ℕ` and a cycle `D`
independent of `φ`; applying this to `φ⁻¹` as well gives `(d + d') • D = 0`, hence
`h_* div(φ) = 0` (Case B).

## Main results

* `ProperPushforwardCurve.apply_eq_genericPoint_of_coheight_eq_one` (C.1): a codimension-one
  point with the same weight as its image lies over the generic point.
* `ProperPushforwardCurve.ord_eq_zero_of_isAlgebraic` (Lemma A2) and
  `ProperPushforwardCurve.map_principalCycle_eq_zero_of_isAlgebraic` (Case A).
* `ProperPushforwardCurve.map_eq_nsmul_of_square`, `eq_zero_of_eq_nsmul_of_neg_eq_nsmul`: the
  chain of pushforwards (G.7) and the symmetry trick (G.8) in abstract form;
  `ProperPushforwardCurve.exists_map_principalCycle_eq_nsmul` (G.7 via the graph closure) and
  `ProperPushforwardCurve.map_principalCycle_eq_zero_of_transcendental` (Case B).
* `ProperPushforwardCurve.map_principalCycle_eq_zero_of_dim_eq_sub_one` (Theorem C').
* `ProperPushforwardCurve.map_divisor_eq_zero_of_dim_eq_sub_one` (Theorem C) and its graded form
  `ProperPushforwardCurve.properPushforward_divisor_eq_zero_of_dim_eq_sub_one`.
* `properPushforwardHRel_of_isProper` (Corollary C): the relation hypothesis of
  `properPushforwardChow` holds for every proper morphism; `properPushforwardChowOfProper` with
  `_quotientMap`, `_id`, `_comp`, and agreement with `finitePushforwardChow` and the
  closed-immersion pushforward.
* `degreeCycle_divisor_eq_zero`, `degreeChow`, `degreeChow_quotientMap`,
  `degreeChow_properPushforwardChow`: for `X` proper over `k`, divisors of one-dimensional
  generators have degree zero, so the degree descends to `A₀(X) →ₗ[ℚ] ℚ`, and it is invariant
  under proper pushforward over `k`.
-/

-- Concrete `Spec R` / section-ring / residue-field carriers only unify with the generic scheme
-- instances at default transparency; this option is what Mathlib's own affine-scheme API uses.
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Order

open scoped WithZero

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace ProperPushforwardCurve

/-! ## Dimension bookkeeping on an integral scheme -/

/-- On an integral scheme whose dimension function drops by one along covering relations, a
point of coheight one has dimension one less than the generic point. -/
theorem dim_genericPoint_eq_add_one_of_coheight_eq_one {V : Scheme.{u}} [IsIntegral V]
    (dV : DimensionFunction V) (hcov : HomogeneityLocal.CovByDimension dV) {x : V}
    (hx : coheight x = 1) : dV (genericPoint V) = dV x + 1 :=
  (hcov x _ ((HomogeneityLocal.coheight_eq_one_iff_covBy
    (HomogeneityLocal.isTop_genericPoint V)).1 hx)).symm

/-- **Coefficient reduction (C.1).**  Let `h : V ⟶ V'` be a morphism of integral schemes with
`dV' η' = dV η - 1` on generic points, `dV` dropping by one along covering relations.  If a point
`x` of coheight one has the same weight as its image, then it lies over the generic point of
`V'`. -/
theorem apply_eq_genericPoint_of_coheight_eq_one {V V' : Scheme.{u}} [IsIntegral V]
    [IsIntegral V'] (h : V ⟶ V') (dV : DimensionFunction V) (dV' : DimensionFunction V')
    (hcov : HomogeneityLocal.CovByDimension dV)
    (hdim : dV' (genericPoint V') = dV (genericPoint V) - 1) {x : V} (hx : coheight x = 1)
    (hw : dV x = dV' (h.base x)) : h.base x = genericPoint V' := by
  by_contra hne
  have h1 := dim_genericPoint_eq_add_one_of_coheight_eq_one dV hcov hx
  have h2 := ProperPushforwardDivisor.dim_lt_of_specializes dV'
    ((genericPoint_spec V').specializes (Set.mem_univ (h.base x))) (Ne.symm hne)
  omega

/-! ## Case A: an algebraic rational function -/

section CaseA

variable {V V' : Scheme.{u}} [IsIntegral V] [IsIntegral V'] [IsLocallyNoetherian V]
  (h : V ⟶ V') [IsDominant h]
  [Algebra V'.functionField V.functionField]
  (halg : algebraMap V'.functionField V.functionField = Scheme.dominantFunctionFieldMap h)

omit [IsLocallyNoetherian V] in
/-- At a point `y` equal to the generic point, the function field maps back into the stalk. -/
private theorem exists_section_of_eq_genericPoint {y : V'} (e : y = genericPoint V') :
    ∃ ψ : V'.functionField →+* V'.presheaf.stalk y,
      ∀ a, algebraMap (V'.presheaf.stalk y) V'.functionField (ψ a) = a := by
  subst e
  refine ⟨RingHom.id _, fun a ↦ ?_⟩
  simp [RingHom.algebraMap_toAlgebra]

include halg in
/-- **Lemma A2.**  Let `h : V ⟶ V'` be a dominant morphism of integral schemes, `V` locally
Noetherian, and `x ∈ V` a point of coheight one lying over the generic point of `V'`.  Then
every rational function `φ ∈ K(V)` algebraic over `K(V')` has order zero at `x`. -/
theorem ord_eq_zero_of_isAlgebraic {x : V} (hx : coheight x = 1)
    (hhx : h.base x = genericPoint V') {φ : V.functionField}
    (hφ : IsAlgebraic V'.functionField φ) : V.ord φ x = 0 := by
  by_cases h0 : φ = 0
  · subst h0; simp
  obtain ⟨ψ, hψ⟩ := exists_section_of_eq_genericPoint hhx
  let ψ' : V'.functionField →+* V.presheaf.stalk x := (h.stalkMap x).hom.comp ψ
  have hcomp : (algebraMap (V.presheaf.stalk x) V.functionField).comp ψ' =
      (RingHom.id V.functionField).comp (algebraMap V'.functionField V.functionField) := by
    ext a
    simp only [RingHom.comp_apply, RingHom.id_apply, ψ', halg]
    rw [← Scheme.dominantFunctionFieldMap_algebraMap, hψ]
  have hint : ∀ z : V.functionField, IsAlgebraic V'.functionField z →
      IsIntegral (V.presheaf.stalk x) z := fun z hz ↦
    IsIntegral.map_of_comp_eq ψ' (RingHom.id _) hcomp hz.isIntegral
  have _ : Ring.KrullDimLE 1 (V.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rw [Scheme.ord_eq_iff hx h0]
  change Ring.ordFrac (V.presheaf.stalk x) φ = _
  rw [GromovWitten.Algebra.ordFrac_eq_one_of_integral_of_inv_integral _ (hint φ hφ)
    (hint _ (IsAlgebraic.inv_iff.2 hφ)) h0]
  rfl

include halg in
/-- **Case A of Theorem C'.**  Let `h : V ⟶ V'` be a quasi-compact dominant morphism of integral
schemes, `V` locally Noetherian, with dimension functions satisfying `dV' η' = dV η - 1` on the
generic points, `dV` dropping by one along covering relations.  If `φ ∈ K(V)` is algebraic over
`K(V')`, then `h_* div(φ) = 0`. -/
theorem map_principalCycle_eq_zero_of_isAlgebraic [QuasiCompact h] (dV : DimensionFunction V)
    (dV' : DimensionFunction V') (hcov : HomogeneityLocal.CovByDimension dV)
    (hdim : dV' (genericPoint V') = dV (genericPoint V) - 1) {φ : V.functionField}
    (hφ : IsAlgebraic V'.functionField φ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map h dV dV' (V.principalCycle φ) = 0 := by
  classical
  apply Function.locallyFinsuppWithin.coe_injective
  funext s
  change (∑ᶠ x ∈ h.base ⁻¹' {s}, V.principalCycle φ x *
      (_root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff h dV dV' x : ℚ)) = (0 : ℚ)
  apply finsum_mem_of_eqOn_zero
  intro x _
  dsimp only [Pi.zero_apply]
  by_cases hx : coheight x = 1
  · by_cases hw : dV x = dV' (h.base x)
    · rw [Scheme.principalCycle_apply, ord_eq_zero_of_isAlgebraic h halg hx
        (apply_eq_genericPoint_of_coheight_eq_one h dV dV' hcov hdim hx hw) hφ]
      simp
    · simp [_root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff, hw]
  · rw [Scheme.principalCycle_apply, Scheme.ord_eq_zero_of_coheight_neq_one hx]
    simp

end CaseA

/-! ## Case B, abstract part: the chain of pushforwards and the symmetry trick -/

section Chain

/-- The residue-degree pushforward commutes with natural-number multiples (a special case of
`map_nsmul` for `AlgebraicCycle.mapLinear`, kept local). -/
private theorem map_nsmul_cycle {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (wx : X → ℤ)
    (wy : Y → ℤ) (n : ℕ) (c : AlgebraicCycle X ℚ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map f wx wy (n • c) =
      n • _root_.AlgebraicGeometry.AlgebraicCycle.map f wx wy c := by
  induction n with
  | zero => simp [AlgebraicCycle.map_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, AlgebraicCycle.map_add, ih]

/-- **The chain (G.7), abstract form.**  Let `h : V ⟶ S` be proper and suppose it is dominated
by a commutative square of proper morphisms `q : W ⟶ V`, `g : W ⟶ T`, `p : T ⟶ S` with
`q ≫ h = g ≫ p`, all schemes carrying dimension functions.  If a cycle `c` on `W` satisfies
`q_* c = α` and `g_* c = d • β`, then `h_* α = d • p_* β`. -/
theorem map_eq_nsmul_of_square {V S W T : Scheme.{u}} (h : V ⟶ S) [IsProper h]
    (q : W ⟶ V) [IsProper q] (g : W ⟶ T) [IsProper g] (p : T ⟶ S) [IsProper p]
    (hcomm : q ≫ h = g ≫ p) (dV : DimensionFunction V) (dS : DimensionFunction S)
    (dW : DimensionFunction W) (dT : DimensionFunction T) (c : AlgebraicCycle W ℚ)
    (α : AlgebraicCycle V ℚ) (β : AlgebraicCycle T ℚ) (d : ℕ)
    (hq : _root_.AlgebraicGeometry.AlgebraicCycle.map q dW dV c = α)
    (hg : _root_.AlgebraicGeometry.AlgebraicCycle.map g dW dT c = d • β) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map h dV dS α =
      d • _root_.AlgebraicGeometry.AlgebraicCycle.map p dT dS β := by
  have hb1 : ∀ x, dW x = dS ((q ≫ h).base x) → dW x = dV (q.base x) := by
    intro x hx
    have h1 := dW.apply_le_of_isProper dV q x
    have h2 := dV.apply_le_of_isProper dS h (q.base x)
    rw [Scheme.Hom.comp_apply] at hx
    omega
  have hb2 : ∀ x, dW x = dS ((g ≫ p).base x) → dW x = dT (g.base x) := by
    intro x hx
    have h1 := dW.apply_le_of_isProper dT g x
    have h2 := dT.apply_le_of_isProper dS p (g.base x)
    rw [Scheme.Hom.comp_apply] at hx
    omega
  rw [← hq, AlgebraicCycle.map_comp_of_between q h _ _ _ hb1,
    ProperPushforwardDivisor.map_congr_hom hcomm, ← map_nsmul_cycle, ← hg,
    AlgebraicCycle.map_comp_of_between g p _ _ _ hb2]

/-- **The symmetry trick (G.8), abstract form.**  In a `ℚ`-vector space, if `x = a • D`,
`-x = b • D` for natural numbers `a`, `b`, then `x = 0`. -/
theorem eq_zero_of_eq_nsmul_of_neg_eq_nsmul {M : Type*} [AddCommGroup M] [Module ℚ M]
    {D x : M} {a b : ℕ} (hx : x = a • D) (hy : -x = b • D) : x = 0 := by
  have hsum : (a + b) • D = 0 := by rw [add_nsmul, ← hx, ← hy, add_neg_cancel]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_eq_zero] at hsum
  rcases hsum with hab | hD
  · have ha : a = 0 := by
      have : a + b = 0 := by exact_mod_cast hab
      omega
    rw [hx, ha, zero_smul]
  · rw [hx, hD, smul_zero]

end Chain

/-! ## Case B and Theorem C' -/

section TheoremC'

variable {k : Type u} [Field k] {V V' : Scheme.{u}} [IsIntegral V] [IsIntegral V']
  [IsLocallyNoetherian V] [IsLocallyNoetherian V']
  (sV : V ⟶ Spec (CommRingCat.of k)) (sV' : V' ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType sV] [LocallyOfFiniteType sV']
  (h : V ⟶ V') [IsProper h] [IsDominant h]

include sV sV' in
/-- **(G.7)** Let `φ = germ φ₀` be transcendental over `K(V')`, with `φ₀` a section over a
nonempty affine open `U ⊆ V`, and `dim V' = dim V - 1`.  Then `h_* div(φ) = d • D` for some
`d ∈ ℕ`, where `D := (pr_{V'})_* div(t)` is the pushforward of the divisor of the coordinate
function `t` of `ℙ¹_{V'}` (a cycle depending only on `V'`). -/
theorem exists_map_principalCycle_eq_nsmul
    [Algebra V'.functionField V.functionField]
    (halg : algebraMap V'.functionField V.functionField = Scheme.dominantFunctionFieldMap h)
    (dV : DimensionFunction V) (dV' : DimensionFunction V')
    (hdim : dV' (genericPoint V') = dV (genericPoint V) - 1) (U : V.Opens) (hU : IsAffineOpen U)
    [Nonempty U] (φ₀ : Γ(V, U))
    (hφ : Transcendental V'.functionField (V.germToFunctionField U φ₀)) :
    ∃ d : ℕ, _root_.AlgebraicGeometry.AlgebraicCycle.map h dV dV'
        (V.principalCycle (V.germToFunctionField U φ₀)) =
      d • _root_.AlgebraicGeometry.AlgebraicCycle.map (P1.pr V')
        (FiniteTypeDimension.dimensionFunction (P1.pr V' ≫ sV')) dV'
        ((P1.P1S V').principalCycle (P1.coordFn V')) := by
  have _ : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  let dP := FiniteTypeDimension.dimensionFunction (P1.pr V ≫ sV)
  let dT := FiniteTypeDimension.dimensionFunction (P1.pr V' ≫ sV')
  have _ := GraphClosure.isDominant_g U φ₀ h halg sV' hφ
  let _ : Algebra (P1.P1S V').functionField
      (GraphClosure.graphClosure U φ₀).scheme.functionField :=
    (Scheme.dominantFunctionFieldMap (GraphClosure.g U φ₀ h)).toAlgebra
  exact ⟨_, map_eq_nsmul_of_square h (GraphClosure.q U φ₀) (GraphClosure.g U φ₀ h) (P1.pr V')
    (GraphClosure.g_pr U φ₀ h).symm dV dV'
    (DimensionFunction.comapClosedImmersion (GraphClosure.graphClosure U φ₀).inclusion dP) dT
    _ _ _ _ (GraphClosure.map_q_principalCycle U φ₀ sV dV dP)
    (GraphClosure.map_g_principalCycle U φ₀ h halg sV sV' dV dV' dP dT hdim hφ rfl)⟩

include sV sV' in
/-- **Case B of Theorem C'** ((G.7)–(G.8)).  Let `h : V ⟶ V'` be a proper dominant morphism of
integral schemes locally of finite type over a field, with `dV' η' = dV η - 1` on the generic
points.  If `φ ∈ K(V)` is transcendental over `K(V')`, then `h_* div(φ) = 0`: by (G.7) both
`h_* div(φ)` and `h_* div(φ⁻¹) = -h_* div(φ)` are natural multiples of one cycle `D`. -/
theorem map_principalCycle_eq_zero_of_transcendental
    [Algebra V'.functionField V.functionField]
    (halg : algebraMap V'.functionField V.functionField = Scheme.dominantFunctionFieldMap h)
    (dV : DimensionFunction V) (dV' : DimensionFunction V')
    (hdim : dV' (genericPoint V') = dV (genericPoint V) - 1) {φ : V.functionField}
    (hφ : Transcendental V'.functionField φ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map h dV dV' (V.principalCycle φ) = 0 := by
  have key : ∀ ψ : V.functionField, Transcendental V'.functionField ψ →
      ∃ d : ℕ, _root_.AlgebraicGeometry.AlgebraicCycle.map h dV dV' (V.principalCycle ψ) =
        d • _root_.AlgebraicGeometry.AlgebraicCycle.map (P1.pr V')
          (FiniteTypeDimension.dimensionFunction (P1.pr V' ≫ sV')) dV'
          ((P1.P1S V').principalCycle (P1.coordFn V')) := by
    intro ψ hψ
    obtain ⟨U, hU, _, φ₀, rfl⟩ := GraphClosure.exists_affineOpen_germ_eq ψ
    exact exists_map_principalCycle_eq_nsmul sV sV' h halg dV dV' hdim U hU φ₀ hψ
  have hφ0 : φ ≠ 0 := fun h0 ↦ hφ (h0 ▸ isAlgebraic_zero)
  obtain ⟨a, ha⟩ := key φ hφ
  obtain ⟨b, hb⟩ := key φ⁻¹ fun h' ↦ hφ (IsAlgebraic.inv_iff.1 h')
  refine eq_zero_of_eq_nsmul_of_neg_eq_nsmul (b := b) ha ?_
  rw [← hb, Scheme.principalCycle_inv hφ0]
  exact (map_neg (AlgebraicCycle.mapLinear h dV dV') _).symm

include sV sV' in
/-- **Theorem C'** (Fulton, Prop. 1.4 (b), case `dim f(W) = dim W - 1`, for integral schemes).
Let `V`, `V'` be integral schemes locally of finite type over a field `k`, `h : V ⟶ V'` proper
and dominant, and `dV`, `dV'` dimension functions with `dV' η' = dV η - 1` on the generic
points.  Then `h_* div(φ) = 0` for every rational function `φ` on `V`. -/
theorem map_principalCycle_eq_zero_of_dim_eq_sub_one (dV : DimensionFunction V)
    (dV' : DimensionFunction V') (hdim : dV' (genericPoint V') = dV (genericPoint V) - 1)
    (φ : V.functionField) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map h dV dV' (V.principalCycle φ) = 0 := by
  by_cases hφ0 : φ = 0
  · rw [hφ0, Scheme.principalCycle_zero, AlgebraicCycle.map_zero]
  let _ : Algebra V'.functionField V.functionField :=
    (Scheme.dominantFunctionFieldMap h).toAlgebra
  have halg : algebraMap V'.functionField V.functionField = Scheme.dominantFunctionFieldMap h :=
    rfl
  by_cases hφ : IsAlgebraic V'.functionField φ
  · exact map_principalCycle_eq_zero_of_isAlgebraic h halg dV dV'
      (covByDimension_of_locallyOfFiniteType sV dV) hdim hφ
  · exact map_principalCycle_eq_zero_of_transcendental sV sV' h halg dV dV' hdim hφ

end TheoremC'

/-! ## Theorem C: generators of a scheme locally of finite type -/

section Main

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
  (dimX : DimensionFunction X) (dimY : DimensionFunction Y)
  (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]

include sX sY in
/-- **Theorem C** (Fulton, Prop. 1.4 (b); Stacks, Lemma 42.20.3, case `dim f(W) = dim W - 1`).
Let `X`, `Y` be locally of finite type over a field `k`, `f : X ⟶ Y` proper and `(W, φ)` a
generator of `X` whose generic point `w` satisfies `dim f(w) = dim w - 1`.  Then the
residue-degree pushforward of `div(φ)` vanishes. -/
theorem map_divisor_eq_zero_of_dim_eq_sub_one (g : RationalFunctionGenerator X)
    (hdim : dimY (f.base g.subspace.genericPointImage) = dimX g.subspace.genericPointImage - 1) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY (g.divisor dimX) = 0 := by
  have _ := LocallyOfFiniteType.isLocallyNoetherian sY
  let W := g.subspace
  let hW := W.toProperImage f
  let ι' := (W.properImage f).inclusion
  let dW := DimensionFunction.comapClosedImmersion W.inclusion dimX
  let dW' := DimensionFunction.comapClosedImmersion ι' dimY
  have hdim' : dW' (genericPoint (W.properImage f).scheme) = dW (genericPoint W.scheme) - 1 := by
    change dimY (W.properImage f).genericPointImage = dimX W.genericPointImage - 1
    rw [W.genericPointImage_properImage f]
    exact hdim
  have hcore := map_principalCycle_eq_zero_of_dim_eq_sub_one (W.inclusion ≫ sX) (ι' ≫ sY) hW
    dW dW' hdim' (g.function : W.scheme.functionField)
  change _root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY
      (_root_.AlgebraicGeometry.AlgebraicCycle.map W.inclusion
        (fun z => dimX (W.inclusion.base z)) dimX
        (W.scheme.principalCycle (g.function : W.scheme.functionField))) = 0
  rw [AlgebraicCycle.map_comp_of_between W.inclusion f _ dimX dimY (fun _ _ => rfl),
    ProperPushforwardDivisor.map_congr_hom
      (IntegralClosedSubscheme.toProperImage_inclusion W f).symm,
    ← AlgebraicCycle.map_comp_of_between hW ι' _ (fun z => dimY (ι'.base z)) dimY
      (fun _ hx => hx)]
  change _root_.AlgebraicGeometry.AlgebraicCycle.map ι' (fun z => dimY (ι'.base z)) dimY
    (_root_.AlgebraicGeometry.AlgebraicCycle.map hW dW dW'
      (W.scheme.principalCycle (g.function : W.scheme.functionField))) = 0
  rw [hcore, AlgebraicCycle.map_zero]

include sX sY in
/-- **Theorem C** in the graded form: under the hypotheses of
`map_divisor_eq_zero_of_dim_eq_sub_one`, the proper pushforward of the dimension-`i` cycle
`div(φ)` is zero. -/
theorem properPushforward_divisor_eq_zero_of_dim_eq_sub_one (g : RationalFunctionGenerator X)
    (hdim : dimY (f.base g.subspace.genericPointImage) = dimX g.subspace.genericPointImage - 1)
    {i : ℤ} (hg : g.divisor dimX ∈ cyclesOfDimension X dimX i) :
    cyclesOfDimension.properPushforward (dimension := dimX) (dimensionY := dimY) (i := i) f
        ⟨g.divisor dimX, hg⟩ = 0 :=
  Subtype.ext (map_divisor_eq_zero_of_dim_eq_sub_one f dimX dimY sX sY g hdim)

end Main

end ProperPushforwardCurve

/-! ## Proper pushforward on rational Chow groups along every proper morphism -/

section ProperChow

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- **Corollary C (Fulton, Prop. 1.4).**  For `X`, `Y` locally of finite type over a field and
`f : X ⟶ Y` proper, the proper pushforward of the divisor of every generator of `X` is a
rational equivalence on `Y`.  Trichotomy on `dim f(w) ≤ dim w`: equal (Theorem P2), one less
(Theorem C, the pushforward is `0`), at least two less (`0` for dimension reasons). -/
theorem properPushforwardHRel_of_isProper (f : X ⟶ Y) [IsProper f]
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (i : ℤ) :
    ProperPushforwardHRel (dimX := dimX) (dimY := dimY) (f := f) (i := i) (sX := sX) := by
  intro g hg
  have hmem := RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX
    (covByDimension_of_locallyOfFiniteType sX dimX) g hg
  have hle := dimX.apply_le_of_isProper dimY f g.subspace.genericPointImage
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact ProperPushforwardDivisor.properPushforward_divisor_mem_relations_of_dim_eq
      sX sY f dimX dimY g heq hmem
  · rcases eq_or_lt_of_le (Int.le_sub_one_of_lt hlt) with heq1 | hlt2
    · rw [ProperPushforwardCurve.properPushforward_divisor_eq_zero_of_dim_eq_sub_one f dimX dimY
        sX sY g heq1 hmem]
      exact Submodule.zero_mem _
    · have h0 : cyclesOfDimension.properPushforward (dimension := dimX) (dimensionY := dimY)
          (i := i) f ⟨g.divisor dimX, hmem⟩ = 0 :=
        Subtype.ext (properPushforward_divisor_eq_zero_of_dim_le f sX g (by omega))
      rw [h0]
      exact Submodule.zero_mem _

/-- **Proper pushforward on rational Chow groups** along an arbitrary proper morphism of schemes
locally of finite type over a field: `properPushforwardChow` with the relation hypothesis
discharged by `properPushforwardHRel_of_isProper`. -/
noncomputable def properPushforwardChowOfProper (f : X ⟶ Y) [IsProper f]
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (i : ℤ) :
    (RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := i)).ChowGroup →ₗ[ℚ]
      (RationalEquivalenceSystem.canonical (X := Y) (dimension := dimY) (i := i)).ChowGroup :=
  properPushforwardChow f i sX (properPushforwardHRel_of_isProper f sX sY dimX dimY i)

/-- `properPushforwardChowOfProper` is induced by the residue-degree pushforward on
dimension-graded cycles. -/
@[simp]
theorem properPushforwardChowOfProper_quotientMap (f : X ⟶ Y) [IsProper f]
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (i : ℤ)
    (z : cyclesOfDimension X dimX i) :
    properPushforwardChowOfProper f sX sY dimX dimY i
        ((RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := i)).quotientMap
          z) =
      (RationalEquivalenceSystem.canonical (X := Y) (dimension := dimY) (i := i)).quotientMap
        (cyclesOfDimension.properPushforward f z) :=
  rfl

/-- Any `properPushforwardChow f i sX hrel` equals `properPushforwardChowOfProper` (the relation
hypothesis is a proposition). -/
theorem properPushforwardChow_eq_ofProper (f : X ⟶ Y) [IsProper f]
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (i : ℤ)
    (hrel : ProperPushforwardHRel (dimX := dimX) (dimY := dimY) (f := f) (i := i) (sX := sX)) :
    properPushforwardChow f i sX hrel = properPushforwardChowOfProper f sX sY dimX dimY i :=
  rfl

/-- `properPushforwardChowOfProper` along the identity is the identity. -/
@[simp]
theorem properPushforwardChowOfProper_id (sX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sX] (dimX : DimensionFunction X) (i : ℤ) :
    properPushforwardChowOfProper (𝟙 X) sX sX dimX dimX i = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨z⟩
  change (RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := i)).quotientMap
      (cyclesOfDimension.properPushforward (𝟙 X) z) =
    (RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := i)).quotientMap z
  rw [cyclesOfDimension.properPushforward_id]
  rfl

/-- **Functoriality** of `properPushforwardChowOfProper`. -/
theorem properPushforwardChowOfProper_comp {Z : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (g : Y ⟶ Z) [IsProper g]
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sZ]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (dimZ : DimensionFunction Z)
    (i : ℤ) :
    properPushforwardChowOfProper (f ≫ g) sX sZ dimX dimZ i =
      (properPushforwardChowOfProper g sY sZ dimY dimZ i).comp
        (properPushforwardChowOfProper f sX sY dimX dimY i) :=
  properPushforwardChow_comp f g i sX sY _ _

/-- For a finite morphism, `properPushforwardChowOfProper` is `finitePushforwardChow`. -/
theorem properPushforwardChowOfProper_eq_finitePushforwardChow (f : X ⟶ Y) [IsFinite f]
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (i : ℤ) :
    properPushforwardChowOfProper f sX sY dimX dimY i =
      finitePushforwardChow f sX sY dimX dimY i :=
  rfl

/-- For a closed immersion, `properPushforwardChowOfProper` is the closed-immersion
pushforward. -/
theorem properPushforwardChowOfProper_eq_closedImmersionPushforward (f : X ⟶ Y)
    [IsClosedImmersion f]
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (i : ℤ) :
    properPushforwardChowOfProper f sX sY dimX dimY i =
      RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward
        (RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := i)) f
        (RationalEquivalenceSystem.canonical (X := Y) (dimension := dimY) (i := i)) :=
  properPushforwardChow_eq_closedImmersionPushforward f i sX _

end ProperChow

/-! ## The degree of a zero-cycle class on a proper scheme -/

section Degree

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (sX : X ⟶ Spec (CommRingCat.of k)) [IsProper sX] [CompactSpace X]

/-- **The divisor of a one-dimensional generator has degree zero** on a scheme proper over a
field: Theorem C for `sX : X ⟶ Spec k` kills `div(φ)`, and the degree is invariant under
pushforward (`NormPushforward.degreeCycle_map_eq`). -/
theorem degreeCycle_divisor_eq_zero (dimX : DimensionFunction X)
    (g : RationalFunctionGenerator X) (hg : dimX g.subspace.genericPointImage = 1) :
    ZeroCycleDegree.degreeCycle sX (g.divisor dimX) = 0 := by
  have hmap := ProperPushforwardCurve.map_divisor_eq_zero_of_dim_eq_sub_one sX dimX
    (DimensionFunction.specField k) sX (𝟙 _) g
    (by rw [DimensionFunction.specField_apply, hg]; norm_num)
  have hmem := RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX
    (covByDimension_of_locallyOfFiniteType sX dimX) g (i := 0) (by rw [hg]; norm_num)
  have hdeg := NormPushforward.degreeCycle_map_eq (𝟙 (Spec (CommRingCat.of k))) sX dimX
    (DimensionFunction.specField k) (g.divisor dimX) (fun x hx ↦ by
      rw [DimensionFunction.specField_apply]
      by_contra hne
      exact hx (hmem x hne))
  rw [hmap, map_zero, Category.comp_id] at hdeg
  exact hdeg.symm

/-- The degree map on dimension-zero cycles kills the rational-equivalence relations of a scheme
proper over a field. -/
theorem relations_le_ker_degree (dimX : DimensionFunction X) :
    (RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := 0)).relations ≤
      LinearMap.ker (ZeroCycleDegree.degree sX dimX) := by
  intro z hz
  have hz' : (z : AlgebraicCycle X ℚ) ∈ totalRationalRelations X dimX := hz
  let L : AlgebraicCycle X ℚ →ₗ[ℚ] ℚ := ZeroCycleDegree.degreeCycle sX ∘ₗ
    (cyclesOfDimension X dimX 0).subtype ∘ₗ cyclesOfDimension.projectLinear dimX 0
  have hspan : totalRationalRelations X dimX ≤ LinearMap.ker L := by
    rw [totalRationalRelations, Submodule.span_le]
    rintro _ ⟨G, rfl⟩
    change ZeroCycleDegree.degreeCycle sX
      ((cyclesOfDimension.projectLinear dimX 0 (G.divisor dimX) :
        cyclesOfDimension X dimX 0) : AlgebraicCycle X ℚ) = 0
    by_cases hG : dimX G.subspace.genericPointImage = 1
    · have hmem := RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX
        (covByDimension_of_locallyOfFiniteType sX dimX) G (i := 0) (by rw [hG]; norm_num)
      have hproj : cyclesOfDimension.projectLinear dimX 0 (G.divisor dimX) =
          ⟨G.divisor dimX, hmem⟩ := cyclesOfDimension.project_coe ⟨G.divisor dimX, hmem⟩
      rw [hproj]
      exact degreeCycle_divisor_eq_zero sX dimX G hG
    · have hmem : G.divisor dimX ∈
          cyclesOfDimension X dimX (dimX G.subspace.genericPointImage - 1) :=
        RationalFunctionGenerator.divisor_mem_cyclesOfDimension dimX
          (covByDimension_of_locallyOfFiniteType sX dimX) G (by ring)
      have hproj : cyclesOfDimension.projectLinear dimX 0 (G.divisor dimX) = 0 :=
        cyclesOfDimension.project_eq_zero_of_mem_ne hmem (by omega)
      rw [hproj]
      exact map_zero _
  have hL : L (z : AlgebraicCycle X ℚ) = 0 := hspan hz'
  rw [LinearMap.mem_ker]
  change ZeroCycleDegree.degreeCycle sX (z : AlgebraicCycle X ℚ) = 0
  change ZeroCycleDegree.degreeCycle sX
    ((cyclesOfDimension.projectLinear dimX 0 (z : AlgebraicCycle X ℚ) :
      cyclesOfDimension X dimX 0) : AlgebraicCycle X ℚ) = 0 at hL
  rw [show cyclesOfDimension.projectLinear dimX 0 (z : AlgebraicCycle X ℚ) = z from
    cyclesOfDimension.project_coe z] at hL
  exact hL

/-- **The degree of a zero-cycle class** on a scheme proper over a field `k`:
`deg : A₀(X) →ₗ[ℚ] ℚ`, `[x] ↦ [κ(x) : k]`, descended from `ZeroCycleDegree.degree`. -/
noncomputable def degreeChow (dimX : DimensionFunction X) :
    (RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := 0)).ChowGroup →ₗ[ℚ]
      ℚ :=
  (RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := 0)).relations.liftQ
    (ZeroCycleDegree.degree sX dimX) (relations_le_ker_degree sX dimX)

/-- The degree of the class of a zero-cycle is its degree `∑ nₓ [κ(x) : k]`. -/
@[simp]
theorem degreeChow_quotientMap (dimX : DimensionFunction X) (z : cyclesOfDimension X dimX 0) :
    degreeChow sX dimX
        ((RationalEquivalenceSystem.canonical (X := X) (dimension := dimX) (i := 0)).quotientMap
          z) =
      ZeroCycleDegree.degree sX dimX z :=
  rfl

/-- **The degree is invariant under proper pushforward**: for `f : X ⟶ Y` proper over `k`
(`f ≫ sY = sX`), `deg ∘ f_* = deg` on `A₀(X)`. -/
theorem degreeChow_properPushforwardChow (f : X ⟶ Y) [IsProper f]
    (sY : Y ⟶ Spec (CommRingCat.of k)) [IsProper sY] [CompactSpace Y]
    (hf : f ≫ sY = sX) (dimX : DimensionFunction X) (dimY : DimensionFunction Y) :
    (degreeChow sY dimY).comp (properPushforwardChowOfProper f sX sY dimX dimY 0) =
      degreeChow sX dimX := by
  apply LinearMap.ext
  rintro ⟨z⟩
  change ZeroCycleDegree.degreeCycle sY
      (_root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY (z : AlgebraicCycle X ℚ)) =
    ZeroCycleDegree.degreeCycle sX (z : AlgebraicCycle X ℚ)
  rw [NormPushforward.degreeCycle_map_eq sY f dimX dimY _ (fun x hx ↦ ?_), hf]
  have hx0 : dimX x = 0 := by
    by_contra hne
    exact hx (z.2 x hne)
  have h1 := dimX.apply_le_of_isProper dimY f x
  have h2 := dimY.nonnegative (f.base x)
  change dimX x = dimY (f.base x)
  omega

end Degree

end GromovWitten.AlgebraicGeometry.IntersectionTheory
