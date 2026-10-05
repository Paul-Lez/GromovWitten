/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleDerived

/-!
# Cohomology and base-change interfaces for curves

All higher direct-image modules in this interface are the constructed right-derived module
pushforwards, with their proved identification with abelian higher direct images. Callers no
longer supply module structures. Geometric base-change isomorphisms and the curve-specific
vanishing remain hypotheses of the legacy theorem package. Properness and finite presentation
alone do not imply arbitrary degree-zero base change, even for a relatively flat module. A
geometric construction of this package needs additional hypotheses, such as relative flatness
and flat degree-one cohomology. `HigherBaseChange.lean` constructs the comparison for exact
horizontal pullbacks; flat-base-change results do not assert arbitrary-base-change invertibility.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open scoped ZeroObject

namespace GromovWitten.AlgebraicGeometry.Curves

universe u
noncomputable section
variable {X S : Scheme.{u}}

/-- Higher direct images with arbitrary-base-change comparison.

Degree zero is not part of the data: `R⁰ f_* M` is the ordinary pushforward `f_* M`, its base
change is `g_* p^* M`, and the degree-zero comparison is the canonical Beck--Chevalley morphism
`canonicalPushforwardBaseChangeComparison`, whose invertibility is exactly the field
`toPushforwardBaseChangeData`. Positive-degree objects are the canonical module-valued derived
pushforwards. The remaining fields supply their comparison morphisms and geometric
base-change and vanishing assertions. -/
structure CurveCohomologyBaseChangeData (f : X ⟶ S) (M : X.Modules) where
  /-- The base-change comparison morphism in positive degrees. -/
  comparisonSucc : ∀ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (_h : IsPullback p g f b) (n : ℕ),
      (Scheme.Modules.pullback b).obj (higherDirectImageModule f M (n + 1)) ⟶
        (higherDirectImageModule g ((Scheme.Modules.pullback p).obj M) (n + 1))
  /-- Cohomology and base change in positive degrees. -/
  comparisonSucc_isIso : ∀ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ), IsIso (comparisonSucc b p g h n)
  /-- Cohomology and base change in degree zero is ordinary-pushforward base change: the
  canonical Beck--Chevalley morphism is invertible. -/
  toPushforwardBaseChangeData : PushforwardBaseChangeData f M
  /-- Higher direct images of a family of curves vanish in degrees at least two. -/
  vanishesSucc : ∀ n, 1 ≤ n → IsZero (higherDirectImageModule f M (n + 1))

namespace CurveCohomologyBaseChangeData

variable {f : X ⟶ S} {M : X.Modules} (C : CurveCohomologyBaseChangeData f M)

/-- The canonical module structure on the positive higher direct image. -/
def higherDirectImageSucc (_C : CurveCohomologyBaseChangeData f M) (n : ℕ) :
    ModuleStructure S (higherDirectImageModuleAb f M (n + 1)) :=
  higherDirectImageModuleStructure f M (n + 1)

/-- The canonical module structure on a base-changed positive higher direct image. -/
def onBaseChangeSucc (_C : CurveCohomologyBaseChangeData f M) {T Z : Scheme.{u}}
    (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (_h : IsPullback p g f b) (n : ℕ) :
    ModuleStructure T (higherDirectImageModuleAb g ((Scheme.Modules.pullback p).obj M) (n + 1)) :=
  higherDirectImageModuleStructure g ((Scheme.Modules.pullback p).obj M) (n + 1)

/-- The `𝒪_S`-module structure on `Rⁿ f_* M`; in degree zero it is the ordinary pushforward. -/
def higherDirectImageStructure : ∀ n : ℕ, ModuleStructure S (higherDirectImageModuleAb f M n)
  | 0 => pushforwardModuleStructure f M
  | (n + 1) => C.higherDirectImageSucc n

/-- The higher direct image `Rⁿ f_* M` as an `𝒪_S`-module; in degree zero this is the ordinary
pushforward. -/
def higherDirectImage (n : ℕ) : S.Modules := (C.higherDirectImageStructure n).toModule

/-- The higher direct images carried by the data are the actual derived-functor higher direct
images, on underlying sheaves of abelian groups. -/
def higherDirectImageIso (n : ℕ) :
    (moduleToSheafAb S).obj (C.higherDirectImage n) ≅ higherDirectImageModuleAb f M n :=
  (C.higherDirectImageStructure n).underlyingIso

@[simp]
theorem higherDirectImage_zero :
    C.higherDirectImage 0 = (Scheme.Modules.pushforward f).obj M := rfl

@[simp]
theorem higherDirectImage_succ (n : ℕ) :
    C.higherDirectImage (n + 1) = (C.higherDirectImageSucc n).toModule := rfl

/-- The `𝒪_T`-module structure on `Rⁿ g_* p^* M` for a Cartesian base change; in degree zero it is
the ordinary pushforward of the pulled-back module. -/
def onBaseChangeStructure {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    ∀ n : ℕ, ModuleStructure T (higherDirectImageModuleAb g ((Scheme.Modules.pullback p).obj M) n)
  | 0 => pushforwardModuleStructure g ((Scheme.Modules.pullback p).obj M)
  | (n + 1) => C.onBaseChangeSucc b p g h n

/-- The higher direct image `Rⁿ g_* p^* M` of a Cartesian base change, as an `𝒪_T`-module. -/
def onBaseChange {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ) : T.Modules :=
  (C.onBaseChangeStructure b p g h n).toModule

/-- The base-changed higher direct images carried by the data are the actual derived-functor
higher direct images of the base-changed family, on underlying sheaves of abelian groups. -/
def onBaseChangeIso {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ) :
    (moduleToSheafAb T).obj (C.onBaseChange b p g h n) ≅
      higherDirectImageModuleAb g ((Scheme.Modules.pullback p).obj M) n :=
  (C.onBaseChangeStructure b p g h n).underlyingIso

@[simp]
theorem onBaseChange_zero {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    C.onBaseChange b p g h 0 =
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback p).obj M) := rfl

@[simp]
theorem onBaseChange_succ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ) :
    C.onBaseChange b p g h (n + 1) = (C.onBaseChangeSucc b p g h n).toModule := rfl

/-- The base-change comparison morphism; in degree zero it *is* the canonical Beck--Chevalley
morphism of the Cartesian square. -/
def comparison {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    ∀ n, (Scheme.Modules.pullback b).obj (C.higherDirectImage n) ⟶ C.onBaseChange b p g h n
  | 0 => canonicalPushforwardBaseChangeComparison f M b p g h
  | (n + 1) => C.comparisonSucc b p g h n

@[simp]
theorem comparison_zero {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    C.comparison b p g h 0 = canonicalPushforwardBaseChangeComparison f M b p g h := rfl

@[simp]
theorem comparison_succ {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ) :
    C.comparison b p g h (n + 1) = C.comparisonSucc b p g h n := rfl

/-- Cohomology and base change in every degree. -/
theorem comparison_isIso {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) : ∀ n, IsIso (C.comparison b p g h n)
  | 0 => C.toPushforwardBaseChangeData.comparison_isIso b p g h
  | (n + 1) => C.comparisonSucc_isIso b p g h n

/-- Cohomology and base change in degree zero gives ordinary pushforward base change. -/
theorem pushforwardBaseChangeData (C : CurveCohomologyBaseChangeData f M) :
    PushforwardBaseChangeData f M :=
  C.toPushforwardBaseChangeData

/-- The degree-zero higher direct image is the ordinary pushforward, by construction. -/
def degreeZeroIso : C.higherDirectImage 0 ≅ (Scheme.Modules.pushforward f).obj M :=
  Iso.refl _

/-- The base-changed degree-zero higher direct image is the ordinary pushforward of the
pulled-back module, by construction. -/
def baseChangedDegreeZeroIso {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    C.onBaseChange b p g h 0 ≅
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback p).obj M) :=
  Iso.refl _

/-- The degree-zero comparison is the canonical Beck--Chevalley morphism. -/
theorem degreeZeroComparison {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) :
    canonicalPushforwardBaseChangeComparison f M b p g h =
      (Scheme.Modules.pullback b).map C.degreeZeroIso.inv ≫
        C.comparison b p g h 0 ≫ (C.baseChangedDegreeZeroIso b p g h).hom := by
  simp [degreeZeroIso, baseChangedDegreeZeroIso]

/-- Higher direct images of a family of curves vanish in degrees at least two. -/
theorem vanishesAboveOne : ∀ n, 2 ≤ n → IsZero (C.higherDirectImage n)
  | 0, hn => by omega
  | 1, hn => by omega
  | (n + 2), _ => C.vanishesSucc (n + 1) (by omega)

/-- The actual derived-functor higher direct images of a family of curves vanish in degrees at
least two: the vanishing carried by the data transfers to the genuine `Rⁿ f_*` because the data
is a module structure on it. -/
theorem isZero_higherDirectImageModuleAb (C : CurveCohomologyBaseChangeData f M) (n : ℕ)
    (hn : 2 ≤ n) :
    IsZero (higherDirectImageModuleAb f M n) :=
  ((moduleToSheafAb S).map_isZero (C.vanishesAboveOne n hn)).of_iso
    (C.higherDirectImageIso n).symm

/-- The vanishing in degrees at least two is inherited by every base change: this is deduced from
the vanishing upstairs and from cohomology and base change, since pullback of modules is an
additive functor. -/
theorem baseChangedVanishesAboveOne {T Z : Scheme.{u}} (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (n : ℕ) (hn : 2 ≤ n) : IsZero (C.onBaseChange b p g h n) := by
  have hiso : IsIso (C.comparison b p g h n) := C.comparison_isIso b p g h n
  have hzero : IsZero ((Scheme.Modules.pullback b).obj (C.higherDirectImage n)) :=
    (Scheme.Modules.pullback b).map_isZero (C.vanishesAboveOne n hn)
  exact hzero.of_iso (asIso (C.comparison b p g h n)).symm

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

/-- A constant function is upper semicontinuous. -/
theorem isUpperSemicontinuousNat_const {S : Type*} [TopologicalSpace S] (r : ℕ) :
    IsUpperSemicontinuousNat (fun _ : S => r) := by
  intro m
  by_cases hm : m ≤ r
  · have hset : {_s : S | m ≤ r} = Set.univ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hm
    rw [hset]
    exact isClosed_univ
  · have hset : {_s : S | m ≤ r} = ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact hm
    rw [hset]
    exact isClosed_empty

/-- A rank profile for the fibre cohomology groups of a curve family. -/
structure CohomologyRankProfile (S : Scheme.{u}) where
  /-- The rank of the `n`-th fibre cohomology at a point of the base. -/
  rank : ℕ → S → ℕ
  /-- Every jumping locus is closed. -/
  upperSemicontinuous : ∀ n, IsUpperSemicontinuousNat (rank n)

namespace CohomologyRankProfile

/-- The constant rank profile; in particular rank profiles always exist. -/
def const (S : Scheme.{u}) (r : ℕ → ℕ) : CohomologyRankProfile S where
  rank n _ := r n
  upperSemicontinuous n := isUpperSemicontinuousNat_const (r n)

instance (S : Scheme.{u}) : Inhabited (CohomologyRankProfile S) :=
  ⟨const S fun _ => 0⟩

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
