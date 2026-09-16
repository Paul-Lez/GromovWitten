/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeLineBundles

/-!
# Proper pushforward and cohomology/base-change data for curves

Mathlib already provides the actual pushforward and pullback functors on sheaves of modules.  This
file constructs the ordinary Beck--Chevalley morphism from the pullback square and the two
pullback--pushforward adjunctions.  The still-missing theorem that this canonical morphism is an
isomorphism is isolated in a typed interface.  Higher-direct-image data carry their own comparison
and explicitly identify its degree-zero instance with the canonical ordinary comparison.  The
degree-zero object is identified with ordinary pushforward, while degrees at least two vanish for
a family of curves.

The structures are proof-bearing theorem packages, not propositions asserted without witnesses.
They allow the stable-reduction layers to consume a locally constructed duality/cohomology proof
without depending on an external package.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X S : Scheme.{u}}

/-- Ordinary proper pushforward of the underlying module of a line bundle. -/
abbrev LineBundle.pushforwardModule (f : X ⟶ S) (L : LineBundle X) : S.Modules :=
  (Scheme.Modules.pushforward f).obj L.obj

/-- The canonical ordinary-pushforward base-change morphism.  Its adjoint is obtained by
identifying the two iterated pullbacks around the Cartesian square and then applying the
pullback of the counit for `f⁎ ⊣ f_*`. -/
def canonicalPushforwardBaseChangeComparison (f : X ⟶ S) (M : X.Modules)
    {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback p).obj M) := by
  refine (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ ?_
  exact
    (Scheme.Modules.pullbackComp g b).hom.app _ ≫
      (Scheme.Modules.pullbackCongr h.w.symm).hom.app _ ≫
      (Scheme.Modules.pullbackComp p f).inv.app _ ≫
      (Scheme.Modules.pullback p).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)

/-- Arbitrary-base-change for ordinary pushforward is the assertion that the canonical
Beck--Chevalley morphism is invertible. -/
structure PushforwardBaseChangeData (f : X ⟶ S) (M : X.Modules) : Prop where
  comparison_isIso : ∀ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b),
      IsIso (canonicalPushforwardBaseChangeComparison f M b p g h)

namespace PushforwardBaseChangeData

variable {f : X ⟶ S} {M : X.Modules}

/-- The comparison attached to the chosen pullback square. -/
def chosenComparison (_B : PushforwardBaseChangeData f M)
    {T : Scheme.{u}} (b : T ⟶ S) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward (pullback.snd f b)).obj
        ((Scheme.Modules.pullback (pullback.fst f b)).obj M) :=
  canonicalPushforwardBaseChangeComparison f M b (pullback.fst f b) (pullback.snd f b)
    (IsPullback.of_hasPullback f b)

instance chosenComparison_isIso (B : PushforwardBaseChangeData f M)
    {T : Scheme.{u}} (b : T ⟶ S) :
    IsIso (chosenComparison B b) :=
  B.comparison_isIso b (pullback.fst f b) (pullback.snd f b)
    (IsPullback.of_hasPullback f b)

end PushforwardBaseChangeData

/-- Higher direct images with arbitrary-base-change comparison.  `onBaseChange` is the higher
direct image constructed on the displayed Cartesian family; `comparison` identifies it with the
pullback of the original higher direct image. -/
structure CurveCohomologyBaseChangeData (f : X ⟶ S) (M : X.Modules) where
  higherDirectImage : ℕ → S.Modules
  onBaseChange : ∀ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T),
    IsPullback p g f b → ℕ → T.Modules
  comparison : ∀ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ),
      (Scheme.Modules.pullback b).obj (higherDirectImage n) ⟶
        onBaseChange b p g h n
  comparison_isIso : ∀ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ), IsIso (comparison b p g h n)
  degreeZeroIso : higherDirectImage 0 ≅ (Scheme.Modules.pushforward f).obj M
  baseChangedDegreeZeroIso : ∀ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X)
    (g : Z ⟶ T) (h : IsPullback p g f b),
      onBaseChange b p g h 0 ≅
        (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback p).obj M)
  degreeZeroComparison : ∀ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X)
    (g : Z ⟶ T) (h : IsPullback p g f b),
      canonicalPushforwardBaseChangeComparison f M b p g h =
        (Scheme.Modules.pullback b).map degreeZeroIso.inv ≫
          comparison b p g h 0 ≫ (baseChangedDegreeZeroIso b p g h).hom
  vanishesAboveOne : ∀ n, 2 ≤ n → IsZero (higherDirectImage n)
  baseChangedVanishesAboveOne : ∀ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X)
    (g : Z ⟶ T) (h : IsPullback p g f b) (n : ℕ),
      2 ≤ n → IsZero (onBaseChange b p g h n)

namespace CurveCohomologyBaseChangeData

variable {f : X ⟶ S} {M : X.Modules} (C : CurveCohomologyBaseChangeData f M)

set_option linter.style.haveILetI false in
/-- Cohomology and base change in degree zero gives ordinary pushforward base change. -/
theorem pushforwardBaseChangeData
    (C : CurveCohomologyBaseChangeData f M) : PushforwardBaseChangeData f M where
  comparison_isIso := by
    intro T Z b p g h
    letI : IsIso (C.comparison b p g h 0) := C.comparison_isIso b p g h 0
    rw [C.degreeZeroComparison b p g h]
    infer_instance

/-- On the chosen base change, every higher comparison is an isomorphism. -/
instance chosenComparison_isIso {T : Scheme.{u}} (b : T ⟶ S) (n : ℕ) :
    IsIso (C.comparison b (pullback.fst f b) (pullback.snd f b)
      (IsPullback.of_hasPullback f b) n) :=
  C.comparison_isIso b (pullback.fst f b) (pullback.snd f b)
    (IsPullback.of_hasPullback f b) n

end CurveCohomologyBaseChangeData

/-- Algebraic upper semicontinuity for a natural-number-valued function: every jumping locus
`{s | m ≤ rank(s)}` is closed. -/
def IsUpperSemicontinuousNat {S : Type*} [TopologicalSpace S] (rank : S → ℕ) : Prop :=
  ∀ m, IsClosed {s | m ≤ rank s}

/-- A rank profile for the fibre cohomology groups of a curve family. -/
structure CohomologyRankProfile (S : Scheme.{u}) where
  rank : ℕ → S → ℕ
  upperSemicontinuous : ∀ n, IsUpperSemicontinuousNat (rank n)

namespace CohomologyRankProfile

/-- Pullback of a rank profile along a scheme morphism. -/
def pullback {T S : Scheme.{u}} (P : CohomologyRankProfile S) (b : T ⟶ S) :
    CohomologyRankProfile T where
  rank n t := P.rank n (b t)
  upperSemicontinuous := by
    intro n m
    have hclosed := P.upperSemicontinuous n m
    have heq : {t : T | m ≤ P.rank n (b t)} = b ⁻¹' {s : S | m ≤ P.rank n s} := rfl
    rw [heq]
    exact hclosed.preimage b.continuous

@[simp]
theorem pullback_rank {T S : Scheme.{u}} (P : CohomologyRankProfile S) (b : T ⟶ S)
    (n : ℕ) (t : T) : (P.pullback b).rank n t = P.rank n (b t) := rfl

end CohomologyRankProfile

end

end GromovWitten.AlgebraicGeometry.Curves
