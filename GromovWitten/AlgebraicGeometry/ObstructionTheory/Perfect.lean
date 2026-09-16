/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.ObstructionTheory.Basic

/-!
# Perfect obstruction theories and global resolutions

Perfectness is local finite-locally-free perfectness with amplitude `[-1,0]`.  It does not choose
a global complex.  This file therefore packages a perfect obstruction theory independently from
the proposition `HasGlobalTwoTermResolution`; the latter is introduced only when the classical
Chow-valued construction needs an actual presentation.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry.DerivedObstructionTheory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-
Retired arbitrary-predicate perfectness layer.  `PerfectData` and
`PerfectObstructionTheory IsPerfect` allowed the caller to choose the meaning of perfectness,
while the resolution predicates similarly accepted an unconstrained notion of finite local
freeness and rank.  The proper-point example instead proves directly that its source has an
actual finite-free two-term resolution and the required amplitude.  A general replacement must
use the concrete module-sheaf notions on the stack site.

/-- An obstruction theory whose source is perfect of amplitude `[-1,0]`.

There is deliberately no global resolution field. -/
structure PerfectObstructionTheory
    (IsPerfect : DerivedCategory C → Prop) (L : DerivedCategory C) where
  /-- The underlying derived obstruction-theory morphism. -/
  toObstructionTheory : ObstructionTheory L
  /-- Local perfectness and the amplitude bound. -/
  perfect : PerfectData IsPerfect toObstructionTheory.E

namespace PerfectObstructionTheory

variable {IsPerfect : DerivedCategory C → Prop} {L : DerivedCategory C}

/-- The derived source of a perfect obstruction theory. -/
abbrev E (T : PerfectObstructionTheory IsPerfect L) : DerivedCategory C :=
  T.toObstructionTheory.E

/-- Its morphism to the cotangent object. -/
abbrev φ (T : PerfectObstructionTheory IsPerfect L) : T.E ⟶ L :=
  T.toObstructionTheory.φ

/-- `H⁰(φ)` is an isomorphism. -/
instance (T : PerfectObstructionTheory IsPerfect L) :
    IsIso (cohomologyMap 0 T.φ) :=
  T.toObstructionTheory.h0_isIso

/-- `H⁻¹(φ)` is an epimorphism. -/
instance (T : PerfectObstructionTheory IsPerfect L) :
    Epi (cohomologyMap (-1) T.φ) :=
  T.toObstructionTheory.hNegOne_epi

/-- The source has cohomological amplitude contained in `[-1,0]`. -/
theorem amplitude (T : PerfectObstructionTheory IsPerfect L) :
    HasAmplitudeNegOneZero T.E :=
  T.perfect.amplitude

end PerfectObstructionTheory

/-- Existence, rather than choice, of a global two-term finite-locally-free resolution. -/
def HasGlobalTwoTermResolution
    (FiniteLocallyFree : C → Prop) (E : DerivedCategory C) : Prop :=
  Nonempty (GlobalTwoTermResolution FiniteLocallyFree E)

namespace HasGlobalTwoTermResolution

variable {FiniteLocallyFree : C → Prop} {E : DerivedCategory C}

/-- A supplied resolution proves the existence predicate. -/
theorem of_resolution (F : GlobalTwoTermResolution FiniteLocallyFree E) :
    HasGlobalTwoTermResolution FiniteLocallyFree E :=
  ⟨F⟩

/-- Choose a resolution only at the point where the Chow construction requires it. -/
noncomputable def choose (h : HasGlobalTwoTermResolution FiniteLocallyFree E) :
    GlobalTwoTermResolution FiniteLocallyFree E :=
  Classical.choice h

/-- Global resolvability is invariant under isomorphism in the derived category. -/
theorem congr {E' : DerivedCategory C} (e : E ≅ E') :
    HasGlobalTwoTermResolution FiniteLocallyFree E ↔
      HasGlobalTwoTermResolution FiniteLocallyFree E' := by
  constructor
  · rintro ⟨F⟩
    exact ⟨F.replace e⟩
  · rintro ⟨F⟩
    exact ⟨F.replace e.symm⟩

end HasGlobalTwoTermResolution

/-- Constant virtual rank is a property of all global resolutions, not a choice of one. -/
def HasConstantVirtualRank
    (FiniteLocallyFree : C → Prop) (rank : C → ℕ)
    (E : DerivedCategory C) (n : ℤ) : Prop :=
  ∀ F : GlobalTwoTermResolution FiniteLocallyFree E, F.virtualRank rank = n

namespace HasConstantVirtualRank

variable {FiniteLocallyFree : C → Prop} {rank : C → ℕ}
  {E : DerivedCategory C} {n : ℤ}

/-- Evaluate the constant-rank property on any supplied global resolution. -/
theorem virtualRank_eq (h : HasConstantVirtualRank FiniteLocallyFree rank E n)
    (F : GlobalTwoTermResolution FiniteLocallyFree E) :
    F.virtualRank rank = n :=
  h F

/-- Constant virtual rank is invariant under replacing a derived object by an isomorphic one. -/
theorem congr {E' : DerivedCategory C} (e : E ≅ E') :
    HasConstantVirtualRank FiniteLocallyFree rank E n ↔
      HasConstantVirtualRank FiniteLocallyFree rank E' n := by
  constructor
  · intro h F
    simpa using h (F.replace e.symm)
  · intro h F
    simpa using h (F.replace e)

end HasConstantVirtualRank

-/

end GromovWitten.AlgebraicGeometry.DerivedObstructionTheory
