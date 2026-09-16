/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Obstruction theories in a derived category

This file packages the cohomological definition of an obstruction theory without replacing its
derived morphism by kernel and cokernel data.  For an object `L`, an obstruction theory is a map
`E ⟶ L` in the derived category which is an isomorphism on `H⁰` and an epimorphism on `H⁻¹`.

Perfectness and the existence of a global two-term resolution are deliberately separate.  The
latter retains an actual complex and an isomorphism from its image in the derived category; it
is not an equality with a chosen representative.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe w v u

namespace DerivedObstructionTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The `i`-th cohomology object of a derived object (Mathlib calls this homology even for
cochain complexes). -/
noncomputable abbrev cohomology (i : ℤ) (E : DerivedCategory C) : C :=
  (DerivedCategory.homologyFunctor C i).obj E

/-- The map on `i`-th cohomology induced by a derived morphism. -/
noncomputable abbrev cohomologyMap {E L : DerivedCategory C} (i : ℤ) (f : E ⟶ L) :
    cohomology i E ⟶ cohomology i L :=
  (DerivedCategory.homologyFunctor C i).map f

/-- A Behrend–Fantechi obstruction theory on the cotangent object `L`.

The morphism `φ` itself is part of the structure, so homotopies, derived isomorphisms, and
transitivity triangles can be expressed by the surrounding derived-category API. -/
structure ObstructionTheory (L : DerivedCategory C) where
  /-- Source of the obstruction-theory morphism. -/
  E : DerivedCategory C
  /-- The derived morphism to the cotangent object. -/
  φ : E ⟶ L
  /-- `H⁰(φ)` is an isomorphism. -/
  h0_isIso : IsIso (cohomologyMap 0 φ)
  /-- `H⁻¹(φ)` is an epimorphism. -/
  hNegOne_epi : Epi (cohomologyMap (-1) φ)

attribute [instance] ObstructionTheory.h0_isIso ObstructionTheory.hNegOne_epi

namespace ObstructionTheory

/-- The identity morphism is the tautological obstruction theory. -/
noncomputable def id (L : DerivedCategory C) : ObstructionTheory L where
  E := L
  φ := 𝟙 L
  h0_isIso := by dsimp only [cohomologyMap]; infer_instance
  hNegOne_epi := by dsimp only [cohomologyMap]; infer_instance

/-- Replace the source of an obstruction theory by an isomorphic derived object. -/
noncomputable def replace {L : DerivedCategory C} (T : ObstructionTheory L)
    {E' : DerivedCategory C} (e : E' ≅ T.E) : ObstructionTheory L where
  E := E'
  φ := e.hom ≫ T.φ
  h0_isIso := by
    change IsIso ((DerivedCategory.homologyFunctor C 0).map (e.hom ≫ T.φ))
    rw [Functor.map_comp]
    infer_instance
  hNegOne_epi := by
    change Epi ((DerivedCategory.homologyFunctor C (-1)).map (e.hom ≫ T.φ))
    rw [Functor.map_comp]
    infer_instance

end ObstructionTheory

/-- Cohomological amplitude contained in `[-1,0]`, expressed intrinsically through the
cohomology functors of the derived category. -/
def HasAmplitudeNegOneZero (E : DerivedCategory C) : Prop :=
  ∀ i : ℤ, i < -1 ∨ 0 < i → IsZero (cohomology i E)

/-
Retired arbitrary-predicate perfectness wrapper.  A caller could instantiate `IsPerfect` by
`True`; concrete examples and the future stack theory must instead use the actual module-sheaf
notion and prove amplitude directly.

/-- Perfectness data used by the obstruction-theory layer.

`isPerfect` is kept as a parameter because its geometric meaning is local finite-locally-free
perfectness in the relevant module category.  The amplitude condition is fixed here and is not
conflated with a global resolution. -/
structure PerfectData (IsPerfect : DerivedCategory C → Prop) (E : DerivedCategory C) : Prop where
  isPerfect : IsPerfect E
  amplitude : HasAmplitudeNegOneZero E

-/

/-
Retired arbitrary-predicate global-resolution wrapper.  A caller could instantiate
`FiniteLocallyFree` with `True`, and its virtual-rank operation accepted an unrelated function
`C → ℕ`.  Concrete module categories must use their actual finite locally free predicate and
intrinsic rank.

/-- A global two-term resolution of `E` by objects satisfying `FiniteLocallyFree`.

The complex may have non-definitional zero objects away from degrees `-1` and `0`; those terms
are required to be zero objects.  Most importantly, `comparison` is an isomorphism in the
derived category. -/
structure GlobalTwoTermResolution
    (FiniteLocallyFree : C → Prop) (E : DerivedCategory C) where
  /-- Chosen cochain complex. -/
  complex : CochainComplex C ℤ
  /-- All terms outside degrees `-1` and `0` vanish. -/
  zero_outside : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (complex.X i)
  /-- The degree `-1` term is finite locally free. -/
  negative_finiteLocallyFree : FiniteLocallyFree (complex.X (-1))
  /-- The degree `0` term is finite locally free. -/
  zero_finiteLocallyFree : FiniteLocallyFree (complex.X 0)
  /-- The chosen complex represents `E`; it is not identified with `E` by equality. -/
  comparison : (DerivedCategory.Q.obj complex) ≅ E

namespace GlobalTwoTermResolution

variable {FiniteLocallyFree : C → Prop} {E : DerivedCategory C}

/-- Transport a global resolution along an isomorphism in the derived category.  The chosen
complex is unchanged; only its comparison with the represented derived object is replaced. -/
noncomputable def replace {E' : DerivedCategory C}
    (F : GlobalTwoTermResolution FiniteLocallyFree E) (e : E ≅ E') :
    GlobalTwoTermResolution FiniteLocallyFree E' where
  complex := F.complex
  zero_outside := F.zero_outside
  negative_finiteLocallyFree := F.negative_finiteLocallyFree
  zero_finiteLocallyFree := F.zero_finiteLocallyFree
  comparison := F.comparison ≪≫ e

/-- Virtual rank uses the cohomological sign convention
`rank(F⁰) - rank(F⁻¹)`. -/
def virtualRank (rank : C → ℕ) (F : GlobalTwoTermResolution FiniteLocallyFree E) : ℤ :=
  (rank (F.complex.X 0) : ℤ) - (rank (F.complex.X (-1)) : ℤ)

@[simp]
theorem replace_virtualRank {E' : DerivedCategory C}
    (rank : C → ℕ) (F : GlobalTwoTermResolution FiniteLocallyFree E)
    (e : E ≅ E') :
    (F.replace e).virtualRank rank = F.virtualRank rank :=
  rfl

end GlobalTwoTermResolution

-/

end DerivedObstructionTheory

end GromovWitten.AlgebraicGeometry
