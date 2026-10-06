/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProjectiveBundleSegre
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalizationExact
import GromovWitten.AlgebraicGeometry.GradedVectorBundleExtend
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProjectiveCompletionOpenPiece

/-!
# Injectivity of the flat pullback along a locally trivial vector bundle

Fulton, *Intersection Theory*, Theorem 3.3(a): for a graded vector bundle `𝓔 : GradedBundleData X ι`
of rank `r = |ι|` over a scheme `X` locally of finite type over an infinite field `k` with
Noetherian underlying space, the flat pullback `p^* : A_i(X) → A_{i+r}(E)` along the total space
`p : E → X` is injective.

The proof follows Fulton with `E ⊕ 1` in place of `E`.  Write `F := E ⊕ 1` (the total space of
`𝓔.extend`), `P' := P(F ⊕ 1)` for its projective completion with projection `q'`, `O(1)` for the
tautological bundle, `P := P(E ⊕ 1) ↪ P'` for the hyperplane at infinity `j` (a closed immersion
whose open complement is `F`), and `θ' : ⨁_{m ≤ r+1} A_{i + m - (r+1)}(X) → A_i(P')` for the
projective bundle map.  If `p_F^* α = 0` then `q'^* α` restricts to zero on `F`, hence is a
pushforward `j_* β` by the localisation sequence; `β = ∑_m c₁(O(1))^m ∩ q^* β_m` by the
surjectivity half of the projective bundle formula on `P`; the projection formula and
`j^* O_{P'}(1) = O_P(1)`, `j_* q^* = c₁(O(1)) ∩ q'^*` give
`j_* β = ∑_m c₁(O(1))^{m+1} ∩ q'^* β_m`, so `θ'(α, -β_0, …, -β_r) = 0` and `α = 0` by the
injectivity half.  Finally `p_E^* α = 0` implies `p_F^* α = 0` since `F → E → X` factors `p_F`.

## Main results

* `chowPullbackBundleGlobal_injective_extend`: injectivity of `p_F^* : A_i(X) → A_{i+r+1}(F)` for
  `F = E ⊕ 1`.
* `chowPullbackBundleGlobal_injective_graded`: injectivity of `p_E^* : A_i(X) → A_{i+r}(E)`, for
  the canonical rational-equivalence systems.
* `chowPullbackBundleGlobal_injective_graded'`: the same for arbitrary rational-equivalence
  systems `RX`, `RE` (there is only one, so this is a reformulation).
-/

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open FiniteTypeDimension GradedBundleData ChartedOverSubscheme
  RationalEquivalenceSystem.DescendingMap

/-! ## Bookkeeping -/

section Bookkeeping

/-- `openImmersionPullback` only depends on the open immersion, not on the proof of the
dimension compatibility or on the instance. -/
theorem openImmersionPullback_congr_hom {X U : Scheme.{u}} {dimX : DimensionFunction X}
    {dimU : DimensionFunction U} {i : ℤ} (R : RationalEquivalenceSystem X dimX i)
    {j j' : U ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j'] (h : j = j')
    (hdim : ∀ u, dimU u = dimX (j.base u)) (hdim' : ∀ u, dimU u = dimX (j'.base u))
    (S : RationalEquivalenceSystem U dimU i) :
    openImmersionPullback R j hdim S = openImmersionPullback R j' hdim' S := by
  subst h
  rfl

/-- `chowPullbackCharted` commutes with `chowCast`. -/
theorem chowPullbackCharted_chowCast {P X : Scheme.{u}} {q : P ⟶ X} {ι : Type u} [Finite ι]
    (𝒞 : AffineCharts q ι) (dimX : DimensionFunction X) (dimP : DimensionFunction P)
    (hshift : ∀ x, dimP (𝒞.fibrePoint x) = dimX x + (Nat.card ι : ℤ)) {i i' : ℤ} (h : i = i')
    (α : (chowSystem dimX i).ChowGroup) :
    chowPullbackCharted 𝒞 dimX dimP hshift i' (chowSystem _ i') (chowSystem _ (i' + Nat.card ι))
        (chowCast h α) =
      chowCast (by rw [h]) (chowPullbackCharted 𝒞 dimX dimP hshift i (chowSystem _ i)
        (chowSystem _ (i + Nat.card ι)) α) := by
  subst h
  rfl

/-- `chowCast` commutes with negation. -/
theorem chowCast_neg {Y : Scheme.{u}} {dim : DimensionFunction Y} {i i' : ℤ} (h : i = i')
    (x : (chowSystem dim i).ChowGroup) : chowCast h (-x) = -chowCast h x :=
  map_neg _ x

/-- **The projection formula for `c1Iter`** along a closed immersion `ι : Z ⟶ Y`, when the
structure morphism of `Z` is given as any morphism `gZ` equal to `ι ≫ g`. -/
theorem closedImmersionPushforward_c1Iter_of_eq {k : Type u} [Field k] [Infinite k]
    {Y Z : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    [NoetherianSpace Y] (L : LineBundleData Y) (ι : Z ⟶ Y) [IsClosedImmersion ι]
    (gZ : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType gZ] [NoetherianSpace Z]
    (hg : ι ≫ g = gZ) (m : ℕ) (i : ℤ)
    (β : (chowSystem (dimensionFunction gZ) (i + m)).ChowGroup) :
    closedImmersionPushforward (chowSystem (dimensionFunction gZ) i) ι
        (chowSystem (dimensionFunction g) i) (c1Iter gZ (L.restrict ι) m i β) =
      c1Iter g L m i (closedImmersionPushforward (chowSystem (dimensionFunction gZ) (i + m)) ι
        (chowSystem (dimensionFunction g) (i + m)) β) := by
  subst hg
  exact closedImmersionPushforward_c1Iter g L ι m i β

end Bookkeeping

/-! ## Placeholders for the results of the concurrent files (to be removed) -/

section Placeholders

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [NoetherianSpace X] {ι : Type u} [Finite ι]
  (𝓔 : GradedBundleData X ι) (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))

/-- PLACEHOLDER (SURJ). -/
theorem projectiveBundleMap_surjective (i : ℤ) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    Function.Surjective (projectiveBundleMap 𝓔.completionCharts f
      (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i) := sorry

/-- PLACEHOLDER (HYP). -/
theorem closedImmersionPushforward_chowPullbackCharted (i : ℤ)
    (α : (chowSystem (dimensionFunction f) i).ChowGroup) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    haveI := 𝓔.extend.noetherianSpace_projectiveCompletion f
    closedImmersionPushforward
        (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) (i + Nat.card ι))
        𝓔.hyperplaneEmbedding
        (chowSystem (dimensionFunction (𝓔.extend.completionToBase ≫ f)) (i + Nat.card ι))
        (chowPullbackCharted 𝓔.completionCharts (dimensionFunction f)
          (dimensionFunction (𝓔.completionToBase ≫ f))
          (𝓔.dimensionFunction_fibrePoint_completionCharts f) i (chowSystem _ i)
          (chowSystem _ (i + Nat.card ι)) α) =
      firstChernClassOfField (𝓔.extend.completionToBase ≫ f) (𝓔.extend.tautological hX)
        (i + Nat.card ι) (chowCast (by simp [Finite.card_option]; ring)
          (chowPullbackCharted 𝓔.extend.completionCharts (dimensionFunction f)
            (dimensionFunction (𝓔.extend.completionToBase ≫ f))
            (𝓔.extend.dimensionFunction_fibrePoint_completionCharts f) i (chowSystem _ i)
            (chowSystem _ (i + Nat.card (Option ι))) α)) := sorry

/-- PLACEHOLDER (HYP). -/
theorem c1Iter_restrict_hyperplaneEmbedding (m : ℕ) (i : ℤ)
    (β : (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) (i + m)).ChowGroup) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    c1Iter (𝓔.completionToBase ≫ f) ((𝓔.extend.tautological hX).restrict 𝓔.hyperplaneEmbedding)
        m i β =
      c1Iter (𝓔.completionToBase ≫ f) (𝓔.tautological hX) m i β := sorry

end Placeholders

/-! ## Fulton 3.3(a) -/

section Main

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [NoetherianSpace X] {ι : Type u} [Finite ι]
  (𝓔 : GradedBundleData X ι) (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))

omit [Infinite k] in
/-- **The localisation step**: if `p_F^* α = 0` for `F = E ⊕ 1`, then `q'^* α` on
`P' = P(F ⊕ 1)` is the pushforward of a class on the hyperplane at infinity `P(E ⊕ 1)`. -/
theorem exists_closedImmersionPushforward_eq_of_extend_eq_zero (i : ℤ)
    (α : (chowSystem (dimensionFunction f) i).ChowGroup)
    (hα : BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.extend.bundle
      (dimensionFunction f) (dimensionFunction (𝓔.extend.bundle.proj ≫ f))
      (dimensionFunction_bundlePoint f 𝓔.extend.bundle) i (chowSystem _ i)
      (chowSystem _ (i + Nat.card (Option ι))) α = 0) :
    ∃ β : (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f))
      (i + Nat.card (Option ι))).ChowGroup,
      closedImmersionPushforward
        (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) (i + Nat.card (Option ι)))
        𝓔.hyperplaneEmbedding
        (chowSystem (dimensionFunction (𝓔.extend.completionToBase ≫ f))
          (i + Nat.card (Option ι))) β =
      chowPullbackCharted 𝓔.extend.completionCharts (dimensionFunction f)
        (dimensionFunction (𝓔.extend.completionToBase ≫ f))
        (𝓔.extend.dimensionFunction_fibrePoint_completionCharts f) i (chowSystem _ i)
        (chowSystem _ (i + Nat.card (Option ι))) α := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := 𝓔.extend.noetherianSpace_projectiveCompletion f
  have := 𝓔.extend.isLocallyNoetherian_projectiveCompletion f
  -- steps 1 and 2: `q'^* α` restricts to zero on the open subscheme `V = range e`, `e : F ↪ P'`
  have h2 := openImmersionPullback_opensRange_chowPullbackCharted_eq_zero_finiteType f 𝓔.extend i
    α hα
  -- step 3: the localisation sequence
  have hrange : ∀ x : 𝓔.extend.projectiveCompletion,
      x ∉ 𝓔.extend.bundleOpenEmbedding.opensRange → x ∈ Set.range 𝓔.hyperplaneEmbedding.base := by
    intro x hx
    have : x ∉ Set.range 𝓔.extend.bundleOpenEmbedding := hx
    rw [range_bundleOpenEmbedding, Set.notMem_compl_iff] at this
    exact this
  obtain ⟨β, hβ⟩ := LinearMap.mem_range.mp
    (ker_openImmersionPullback_le_range_of_homogeneous _ _ _
      (dimensionFunction_opensRange_bundleOpenEmbedding f 𝓔.extend)
      (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) (i + Nat.card (Option ι)))
      𝓔.hyperplaneEmbedding hrange (principalDivisorsHomogeneous (𝓔.extend.completionToBase ≫ f))
      (LinearMap.mem_ker.mpr h2))
  exact ⟨β, hβ⟩

/-- **The pushforward of a summand of the projective bundle map**: for `β ∈ A_n(X)`,
`j_* (c₁(O_P(1))^m ∩ q^* β) = c₁(O_{P'}(1))^{m+1} ∩ q'^* β` in `A_l(P')`, `l = n + r - m`. -/
theorem closedImmersionPushforward_c1Iter_chowPullbackCharted (m : ℕ) (n : ℤ)
    (β : (chowSystem (dimensionFunction f) n).ChowGroup) {l : ℤ}
    (hl : l = n + Nat.card ι - m) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    haveI := 𝓔.extend.noetherianSpace_projectiveCompletion f
    closedImmersionPushforward (chowSystem (dimensionFunction (𝓔.completionToBase ≫ f)) l)
        𝓔.hyperplaneEmbedding
        (chowSystem (dimensionFunction (𝓔.extend.completionToBase ≫ f)) l)
        (c1Iter (𝓔.completionToBase ≫ f) (𝓔.tautological hX) m l (chowCast (by rw [hl]; ring)
          (chowPullbackCharted 𝓔.completionCharts (dimensionFunction f)
            (dimensionFunction (𝓔.completionToBase ≫ f))
            (𝓔.dimensionFunction_fibrePoint_completionCharts f) n (chowSystem _ n)
            (chowSystem _ (n + Nat.card ι)) β))) =
      c1Iter (𝓔.extend.completionToBase ≫ f) (𝓔.extend.tautological hX) (m + 1) l
        (chowCast (by rw [hl, Finite.card_option]; push_cast; ring)
          (chowPullbackCharted 𝓔.extend.completionCharts (dimensionFunction f)
            (dimensionFunction (𝓔.extend.completionToBase ≫ f))
            (𝓔.extend.dimensionFunction_fibrePoint_completionCharts f) n (chowSystem _ n)
            (chowSystem _ (n + Nat.card (Option ι))) β)) := by
  have := 𝓔.noetherianSpace_projectiveCompletion f
  have := 𝓔.extend.noetherianSpace_projectiveCompletion f
  subst hl
  rw [← c1Iter_restrict_hyperplaneEmbedding f 𝓔 hX m,
    closedImmersionPushforward_c1Iter_of_eq (𝓔.extend.completionToBase ≫ f)
      (𝓔.extend.tautological hX) 𝓔.hyperplaneEmbedding (𝓔.completionToBase ≫ f)
      (hyperplaneEmbedding_toBase_assoc 𝓔 f) m,
    closedImmersionPushforward_chowCast, closedImmersionPushforward_chowPullbackCharted f 𝓔 hX n β,
    ← firstChernClassOfField_chowCast (𝓔.extend.completionToBase ≫ f) (𝓔.extend.tautological hX)
      (j := n + Nat.card ι) (j' := n + Nat.card ι - m + m) (by ring)
      (by rw [Finite.card_option]; push_cast; ring),
    c1Iter_succ, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    chowCast_chowCast]

include hX in
/-- **Fulton 3.3(a) for `E ⊕ 1`**: the flat pullback `A_i(X) → A_{i+r+1}(E ⊕ 1)` along the total
space of `𝓔.extend` is injective. -/
theorem chowPullbackBundleGlobal_injective_extend (i : ℤ) :
    Function.Injective (BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.extend.bundle
      (dimensionFunction f) (dimensionFunction (𝓔.extend.bundle.proj ≫ f))
      (dimensionFunction_bundlePoint f 𝓔.extend.bundle) i (chowSystem _ i)
      (chowSystem _ (i + Nat.card (Option ι)))) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := 𝓔.noetherianSpace_projectiveCompletion f
  have := 𝓔.extend.noetherianSpace_projectiveCompletion f
  have hr' : Nat.card (Option ι) = Nat.card ι + 1 := Finite.card_option
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro α hα
  -- `q'^* α = j_* β`, and `β` is in the image of the projective bundle map of `P(E ⊕ 1)`
  obtain ⟨β, hβ⟩ := exists_closedImmersionPushforward_eq_of_extend_eq_zero f 𝓔 i α hα
  obtain ⟨γ, rfl⟩ := projectiveBundleMap_surjective f 𝓔 hX (i + Nat.card (Option ι)) β
  rw [projectiveBundleMap_apply, map_sum, Finset.sum_congr rfl (fun (m : Fin (Nat.card ι + 1)) _ ↦
    closedImmersionPushforward_c1Iter_chowPullbackCharted f 𝓔 hX (m : ℕ)
      (i + Nat.card (Option ι) + ((m : ℕ) : ℤ) - Nat.card ι) (γ m)
      (l := i + Nat.card (Option ι)) (by ring))] at hβ
  -- the tuple `(α, -γ_0, …, -γ_r)` is killed by the projective bundle map of `P((E ⊕ 1) ⊕ 1)`
  obtain ⟨δ, hδ0, hδs⟩ : ∃ δ : ∀ m : Fin (Nat.card (Option ι) + 1),
      (chowSystem (dimensionFunction f)
        (i + Nat.card (Option ι) + ((m : ℕ) : ℤ) - Nat.card (Option ι))).ChowGroup,
      δ 0 = chowCast (by simp) α ∧ ∀ m : Fin (Nat.card (Option ι)),
        δ m.succ = -chowCast (by simp only [Fin.val_cast, Fin.val_succ]; push_cast; omega)
          (γ (Fin.cast hr' m)) :=
    ⟨Fin.cases (chowCast (by simp) α)
      (fun m ↦ -chowCast (by simp only [Fin.val_cast, Fin.val_succ]; push_cast; omega)
        (γ (Fin.cast hr' m))),
      Fin.cases_zero, fun m ↦ Fin.cases_succ m⟩
  have hθ : projectiveBundleMap 𝓔.extend.completionCharts f
      (𝓔.extend.dimensionFunction_fibrePoint_completionCharts f) (𝓔.extend.tautological hX)
      (i + Nat.card (Option ι)) δ = 0 := by
    rw [projectiveBundleMap_apply, Fin.sum_univ_succ, hδ0, chowPullbackCharted_chowCast,
      chowCast_chowCast, c1Iter_congr_exponent _ _ (Fin.val_zero _), c1Iter_zero,
      LinearEquiv.coe_coe, chowCast_chowCast, chowCast_self,
      Finset.sum_congr rfl (fun m _ ↦ by
        rw [hδs, map_neg, map_neg, map_neg, chowPullbackCharted_chowCast, chowCast_chowCast,
          c1Iter_congr_exponent _ _ (Fin.val_succ m)]),
      Finset.sum_neg_distrib, ← hβ, add_neg_eq_zero]
    exact Fintype.sum_equiv (finCongr hr'.symm) _ _ (fun _ ↦ rfl)
  have hδ := projectiveBundleMap_injective f 𝓔.extend hX (i + Nat.card (Option ι))
    (hθ.trans (map_zero _).symm)
  have h0 := congr_fun hδ 0
  rw [hδ0, Pi.zero_apply, LinearEquiv.map_eq_zero_iff] at h0
  exact h0

include hX in
/-- **Fulton, *Intersection Theory*, Theorem 3.3(a)** for a graded vector bundle
`𝓔 : GradedBundleData X ι` of rank `r = |ι|` over a scheme `X` locally of finite type over an
infinite field with Noetherian underlying space (and with `hX`: intersections of affine opens of
`X` are affine, e.g. `X` separated): the flat pullback `p^* : A_i(X) → A_{i+r}(E)` along the total
space is injective. -/
theorem chowPullbackBundleGlobal_injective_graded (i : ℤ) :
    Function.Injective (BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.bundle
      (dimensionFunction f) (dimensionFunction (𝓔.bundle.proj ≫ f))
      (dimensionFunction_bundlePoint f 𝓔.bundle) i (chowSystem _ i)
      (chowSystem _ (i + Nat.card ι))) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro α hα
  exact LinearMap.ker_eq_bot'.mp
    (LinearMap.ker_eq_bot.mpr (chowPullbackBundleGlobal_injective_extend f 𝓔 hX i)) α
    (chowPullbackBundleGlobal_extend_eq_zero_of_eq_zero_finiteType 𝓔 f i α hα)

include hX in
/-- `chowPullbackBundleGlobal_injective_graded` for arbitrary rational-equivalence systems `RX`,
`RE` (there is only one, the canonical one). -/
theorem chowPullbackBundleGlobal_injective_graded' (i : ℤ)
    (RX : RationalEquivalenceSystem X (dimensionFunction f) i)
    (RE : RationalEquivalenceSystem 𝓔.bundle.totalSpace
      (dimensionFunction (𝓔.bundle.proj ≫ f)) (i + Nat.card ι)) :
    Function.Injective (BundleOverSubscheme.chowPullbackBundleGlobal 𝓔.bundle
      (dimensionFunction f) (dimensionFunction (𝓔.bundle.proj ≫ f))
      (dimensionFunction_bundlePoint f 𝓔.bundle) i RX RE) := by
  cases RX
  cases RE
  exact chowPullbackBundleGlobal_injective_graded f 𝓔 hX i

end Main

end GromovWitten.AlgebraicGeometry.IntersectionTheory
