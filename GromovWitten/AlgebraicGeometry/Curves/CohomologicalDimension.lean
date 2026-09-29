/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.CohomologyVanishing

/-!
# Uniform cohomological dimension from a finite affine cover

Compactness turns the canonical affine cover into a finite affine cover.  The
finite-cover Mayer–Vietoris theorem then gives a uniform eventual vanishing
bound for quasi-coherent cohomology.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X : Scheme.{u}}

private theorem exists_nonempty_finite_affine_cover [CompactSpace X] :
    ∃ Us : List X.Opens,
      (∀ U ∈ Us, IsAffineOpen U) ∧ affineUnion Us = ⊤ ∧ Us ≠ [] := by
  let 𝒰 := X.affineCover.finiteSubcover
  let e := Fintype.equivFin 𝒰.I₀
  let Us : List X.Opens :=
    List.ofFn (fun i : Fin (Fintype.card 𝒰.I₀) => (𝒰.f (e.symm i)).opensRange) ++ [⊥]
  have hmem : ∀ (Ls : List X.Opens) (x : X),
      x ∈ affineUnion Ls ↔ ∃ U ∈ Ls, x ∈ U := by
    intro Ls
    induction Ls with
    | nil => intro x; simp [affineUnion]
    | cons U Ls ih =>
        intro x
        simp only [affineUnion, Opens.mem_sup, List.mem_cons]
        constructor
        · intro hx
          rcases hx with hx | hx
          · exact ⟨U, Or.inl rfl, hx⟩
          · rcases (ih x).mp hx with ⟨V, hV, hxV⟩
            exact ⟨V, Or.inr hV, hxV⟩
        · rintro ⟨V, hV, hxV⟩
          rcases hV with rfl | hV
          · exact Or.inl hxV
          · exact Or.inr ((ih x).mpr ⟨V, hV, hxV⟩)
  have hUs : ∀ U ∈ Us, IsAffineOpen U := by
    intro U hU
    rcases List.mem_append.mp hU with hU | hU
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hU
      exact isAffineOpen_opensRange _
    · simp only [List.mem_singleton] at hU
      subst U
      exact isAffineOpen_bot _
  have hcover : affineUnion Us = ⊤ := by
    apply Opens.ext
    ext x
    constructor
    · intro _
      trivial
    · intro _
      let i := 𝒰.idx x
      obtain ⟨y, hy⟩ := 𝒰.covers x
      apply (hmem Us x).2
      refine ⟨(𝒰.f i).opensRange, ?_, ?_⟩
      · apply List.mem_append.mpr
        exact Or.inl ((List.mem_ofFn' _ _).mpr
          ⟨e i, by
            change (𝒰.f (e.symm (e i))).opensRange = _
            rw [e.symm_apply_apply]⟩)
      · exact ⟨y, hy⟩
  exact ⟨Us, hUs, hcover, by simp [Us]⟩

/-- A compact, separated, locally Noetherian scheme has a finite cohomological bound
for all quasi-coherent modules. -/
theorem exists_cohomologicalDimension_bound
    [CompactSpace X] [IsLocallyNoetherian X] [X.IsSeparated] :
    ∃ d : ℕ, ∀ (M : X.Modules) [M.IsQuasicoherent] (n : ℕ),
      IsZero (cohomology X M (n + d)) := by
  obtain ⟨Us, hUs, hcover, hne⟩ := exists_nonempty_finite_affine_cover (X := X)
  refine ⟨Us.length, ?_⟩
  intro M _ n
  exact isZero_cohomology_finiteAffineCover Us hUs hcover hne M n

end GromovWitten.AlgebraicGeometry.Curves
