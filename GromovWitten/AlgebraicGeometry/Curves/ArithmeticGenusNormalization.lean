/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenus
import GromovWitten.AlgebraicGeometry.Curves.DualGraph

/-!
# The normalization formula for the arithmetic genus

This file turns the cohomology sequence of the normalization short exact sequence

`0 → 𝒪_X → ν_* 𝒪_X̃ → ⊕_nodes k → 0`

of a nodal curve into the numerical normalization formula `p_a(X) = p_a(X̃) + δ` for the
arithmetic genus of `GromovWitten/AlgebraicGeometry/Curves/ArithmeticGenus.lean`, and compares
the result with the dual-graph genus `DualGraph.arithmeticGenus` of
`GromovWitten/AlgebraicGeometry/Curves/DualGraph.lean`.

The input that is still missing from Mathlib is the long exact cohomology sequence for
`CategoryTheory.Sheaf.H`; the exactness of the five-term sequence therefore appears as an explicit
hypothesis.  Everything else — the Euler-characteristic computation and its comparison with the
graph-theoretic Euler characteristic — is proved.

## Main results

* `alternating_sum_eq_zero_of_exact₅` — the alternating sum of dimensions along a five-term exact
  sequence of finite-dimensional vector spaces vanishes.
* `arithmeticGenus_add_of_normalizationSequence` — `p_a(X) + h⁰(ν_*𝒪_X̃) = p_a(X̃) + δ + 1`.
* `arithmeticGenus_eq_dualGraph_arithmeticGenus` — this numerical formula is exactly the
  dual-graph formula `p_a(X) = Σ_v g(v) + b₁(Γ)`.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X : Scheme.{u}}

/-! ## Euler characteristics and the normalization formula -/

/-- The alternating sum of dimensions along a five-term exact sequence of finite-dimensional
vector spaces vanishes.  This is the Euler-characteristic computation feeding the normalization
formula for the arithmetic genus. -/
theorem alternating_sum_eq_zero_of_exact₅ {k V₁ V₂ V₃ V₄ V₅ : Type*} [Field k]
    [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    [AddCommGroup V₃] [Module k V₃] [FiniteDimensional k V₃]
    [AddCommGroup V₄] [Module k V₄] [FiniteDimensional k V₄]
    [AddCommGroup V₅] [Module k V₅] [FiniteDimensional k V₅]
    (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    (h₁ : LinearMap.ker f₁ = ⊥)
    (h₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (h₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (h₄ : LinearMap.ker f₄ = LinearMap.range f₃)
    (h₅ : LinearMap.range f₄ = ⊤) :
    (Module.finrank k V₁ : ℤ) - Module.finrank k V₂ + Module.finrank k V₃
      - Module.finrank k V₄ + Module.finrank k V₅ = 0 := by
  have n₁ := f₁.finrank_range_add_finrank_ker
  have n₂ := f₂.finrank_range_add_finrank_ker
  have n₃ := f₃.finrank_range_add_finrank_ker
  have n₄ := f₄.finrank_range_add_finrank_ker
  rw [h₁, finrank_bot] at n₁
  rw [h₂] at n₂
  rw [h₃] at n₃
  rw [h₄, h₅, finrank_top] at n₄
  omega

/-- **The normalization formula for the arithmetic genus.**  Suppose the cohomology sequence of
the normalization short exact sequence `0 → 𝒪_X → ν_*𝒪_X̃ → ⊕_nodes k → 0` is available as the
exact five-term sequence

`0 → H⁰(𝒪_X) → H⁰(N) → H⁰(Q) → H¹(𝒪_X) → H¹(N) → 0`

of `k`-vector spaces, where `N = ν_*𝒪_X̃`, `Q` is the skyscraper module at the `δ` nodes with
`h⁰(Q) = δ`, and `X` has a one-dimensional space of global functions.  Then
`p_a(X) + h⁰(N) = h¹(N) + δ + 1`; in particular for a connected normalization (`h⁰(N) = 1`) this
is `p_a(X) = p_a(X̃) + δ`. -/
theorem arithmeticGenus_add_of_normalizationSequence (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (N Q : X.Modules) (δ : ℕ)
    [FiniteDimensional k (cohomologyModuleCat k f (structureModule X) 0)]
    [FiniteDimensional k (cohomologyModuleCat k f N 0)]
    [FiniteDimensional k (cohomologyModuleCat k f Q 0)]
    [FiniteDimensional k (cohomologyModuleCat k f (structureModule X) 1)]
    [FiniteDimensional k (cohomologyModuleCat k f N 1)]
    (f₁ : cohomologyModuleCat k f (structureModule X) 0 →ₗ[k] cohomologyModuleCat k f N 0)
    (f₂ : cohomologyModuleCat k f N 0 →ₗ[k] cohomologyModuleCat k f Q 0)
    (f₃ : cohomologyModuleCat k f Q 0 →ₗ[k] cohomologyModuleCat k f (structureModule X) 1)
    (f₄ : cohomologyModuleCat k f (structureModule X) 1 →ₗ[k] cohomologyModuleCat k f N 1)
    (h₁ : LinearMap.ker f₁ = ⊥)
    (h₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (h₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (h₄ : LinearMap.ker f₄ = LinearMap.range f₃)
    (h₅ : LinearMap.range f₄ = ⊤)
    (hX0 : hDim k f (structureModule X) 0 = 1)
    (hQ0 : hDim k f Q 0 = δ) :
    arithmeticGenus k f + hDim k f N 0 = hDim k f N 1 + δ + 1 := by
  have h := alternating_sum_eq_zero_of_exact₅ f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄ h₅
  rw [show Module.finrank k (cohomologyModuleCat k f (structureModule X) 0) =
      hDim k f (structureModule X) 0 from rfl,
    show Module.finrank k (cohomologyModuleCat k f N 0) = hDim k f N 0 from rfl,
    show Module.finrank k (cohomologyModuleCat k f Q 0) = hDim k f Q 0 from rfl,
    show Module.finrank k (cohomologyModuleCat k f (structureModule X) 1) =
      arithmeticGenus k f from rfl,
    show Module.finrank k (cohomologyModuleCat k f N 1) = hDim k f N 1 from rfl,
    hX0, hQ0] at h
  omega

/-- **Agreement of the cohomological and dual-graph arithmetic genera.**  Let `G` be the dual
graph of a nodal curve `X` over `k`: its vertices are the irreducible components, its edges are
the `δ` nodes, and its vertex genera are the genera of the normalized components, summing to
`h¹(ν_*𝒪_X̃)`.  Then the cohomological arithmetic genus `p_a(X) = dim_k H¹(X, 𝒪_X)` agrees with
the dual-graph genus `Σ_v g(v) + b₁(Γ)`.

The hypothesis `hformula` is the conclusion of `arithmeticGenus_add_of_normalizationSequence`, so
the normalization formula and the dual-graph formula do agree. -/
theorem arithmeticGenus_eq_dualGraph_arithmeticGenus (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (N : X.Modules) (δ : ℕ) (G : DualGraph.{u})
    (hgenus : ∑ v, G.genus v = hDim k f N 1)
    (hedge : Fintype.card G.Edge = δ)
    (hvertex : Fintype.card G.Vertex = hDim k f N 0)
    (hformula : arithmeticGenus k f + hDim k f N 0 = hDim k f N 1 + δ + 1) :
    arithmeticGenus k f = G.arithmeticGenus := by
  have hb := G.firstBetti_add_card_vertex
  rw [DualGraph.arithmeticGenus_eq_sum_add, hgenus]
  omega

end

end GromovWitten.AlgebraicGeometry.Curves
