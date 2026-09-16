/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.LineBundles
import GromovWitten.AlgebraicGeometry.Curves.Nodal

/-!
# Relative line bundles on families of curves

A relative line bundle carries an actual line bundle on the total space and an integer degree on
every irreducible component of every chosen geometric fibre.  Canonical isomorphisms between
iterated pullbacks transport these components, so the degree and positivity data pull back along
arbitrary morphisms without allowing unrelated values on two presentations of the same fibre.

This is deliberately a curve-specific ampleness interface: positivity on every irreducible
component is the numerical criterion consumed by stable reduction.  It does not assert a general
scheme-theoretic ampleness API that Mathlib does not yet provide.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X S T : Scheme.{u}}

/-- An isomorphism of schemes transports irreducible components by its underlying
homeomorphism. -/
def irreducibleComponentsEquivOfSchemeIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    irreducibleComponents X ≃ irreducibleComponents Y :=
  (irreducibleComponentsEquivOfIsPreirreducibleFiber e.hom
    e.hom.homeomorph.continuous e.hom.homeomorph.isOpenMap
    (fun _ ↦
      (Set.subsingleton_singleton.preimage e.hom.homeomorph.injective).isPreirreducible)
    e.hom.homeomorph.surjective).symm.toEquiv

/-- Membership in the inverse-transported component is detected after applying the
isomorphism. -/
@[simp]
theorem mem_irreducibleComponentsEquivOfSchemeIso_symm {X Y : Scheme.{u}}
    (e : X ≅ Y) (C : irreducibleComponents Y) (x : X) :
    x ∈ ((irreducibleComponentsEquivOfSchemeIso e).symm C : Set X) ↔
      e.hom x ∈ (C : Set Y) :=
  Iff.rfl

/-- A line bundle on the total space together with component degrees on each chosen geometric
fibre.  Recording one value per actual component, rather than one value per Cartesian
presentation, makes invariance under the unique comparison isomorphism intrinsic. -/
structure RelativeLineBundle (f : X ⟶ S) where
  line : LineBundle X
  componentDegree : ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
    (_component : irreducibleComponents
      (CategoryTheory.Limits.pullback f y : Scheme.{u})), ℤ

namespace RelativeLineBundle

variable {f : X ⟶ S} (L : RelativeLineBundle f)

/-- Degree on a component of the chosen geometric fibre product. -/
def degree {K : Type u} [Field K] (y : Spec (.of K) ⟶ S)
    (C : irreducibleComponents
      (CategoryTheory.Limits.pullback f y : Scheme.{u})) : ℤ :=
  L.componentDegree K y C

/-- Pull a relative line bundle back along an arbitrary base morphism. -/
def pullback (b : T ⟶ S) :
    RelativeLineBundle (CategoryTheory.Limits.pullback.snd f b) where
  line := L.line.pullback (CategoryTheory.Limits.pullback.fst f b)
  componentDegree := by
    intro K _ y C
    exact L.degree (y ≫ b)
      (irreducibleComponentsEquivOfSchemeIso
        (pullbackLeftPullbackSndIso f b y) C)

/-- Tensor product of relative line bundles.  Its component degree is the sum of the two
component degrees. -/
def tensor (L M : RelativeLineBundle f) : RelativeLineBundle f where
  line := L.line.tensor M.line
  componentDegree := fun _ _ y C ↦ L.degree y C + M.degree y C

/-- The trivial relative line bundle, with zero degree on every geometric component. -/
def trivial (f : X ⟶ S) : RelativeLineBundle f where
  line := LineBundle.trivial X
  componentDegree := fun _ _ _ _ ↦ 0

@[simp]
theorem trivial_line (f : X ⟶ S) : (trivial f).line = LineBundle.trivial X := rfl

@[simp]
theorem trivial_degree (f : X ⟶ S) {K : Type u} [Field K]
    (y : Spec (.of K) ⟶ S)
    (C : irreducibleComponents (CategoryTheory.Limits.pullback f y : Scheme.{u})) :
    (trivial f).degree y C = 0 := rfl

@[simp]
theorem tensor_line (L M : RelativeLineBundle f) :
    (L.tensor M).line = L.line.tensor M.line := rfl

@[simp]
theorem tensor_degree (L M : RelativeLineBundle f) {K : Type u} [Field K]
    (y : Spec (.of K) ⟶ S)
    (C : irreducibleComponents (CategoryTheory.Limits.pullback f y : Scheme.{u})) :
    (L.tensor M).degree y C = L.degree y C + M.degree y C := rfl

/-- The dual relative line bundle, with the expected negation of every geometric component
degree. -/
def dual (L : RelativeLineBundle f) : RelativeLineBundle f where
  line := L.line.dual
  componentDegree := fun _ _ y C ↦ -L.degree y C

@[simp]
theorem dual_line (L : RelativeLineBundle f) : L.dual.line = L.line.dual := rfl

@[simp]
theorem dual_degree (L : RelativeLineBundle f) {K : Type u} [Field K]
    (y : Spec (.of K) ⟶ S)
    (C : irreducibleComponents (CategoryTheory.Limits.pullback f y : Scheme.{u})) :
    L.dual.degree y C = -L.degree y C := rfl

/-- The nonnegative tensor powers of a relative line bundle. -/
def tensorPow (L : RelativeLineBundle f) : ℕ → RelativeLineBundle f
  | 0 => trivial f
  | n + 1 => (tensorPow L n).tensor L

@[simp]
theorem tensorPow_line (L : RelativeLineBundle f) (n : ℕ) :
    (L.tensorPow n).line = L.line.tensorPow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (L.tensorPow n).line.tensor L.line =
        (L.line.tensorPow n).tensor L.line
      rw [ih]

@[simp]
theorem tensorPow_degree (L : RelativeLineBundle f) (n : ℕ)
    {K : Type u} [Field K] (y : Spec (.of K) ⟶ S)
    (C : irreducibleComponents (CategoryTheory.Limits.pullback f y : Scheme.{u})) :
    (L.tensorPow n).degree y C = n • L.degree y C := by
  induction n with
  | zero => simp [tensorPow, degree, trivial]
  | succ n ih => simp [tensorPow, ih, add_mul]

/-- Integer tensor powers of a relative line bundle.  Negative powers use the genuine dual
line bundle and negate all component degrees. -/
def tensorIntPow (L : RelativeLineBundle f) : ℤ → RelativeLineBundle f
  | .ofNat n => L.tensorPow n
  | .negSucc n => L.dual.tensorPow (n + 1)

@[simp]
theorem tensorIntPow_line (L : RelativeLineBundle f) (n : ℤ) :
    (L.tensorIntPow n).line = L.line.tensorIntPow n := by
  cases n <;>
    simp only [tensorIntPow, LineBundle.tensorIntPow, tensorPow_line, dual_line]

@[simp]
theorem tensorIntPow_degree (L : RelativeLineBundle f) (n : ℤ)
    {K : Type u} [Field K] (y : Spec (.of K) ⟶ S)
    (C : irreducibleComponents (CategoryTheory.Limits.pullback f y : Scheme.{u})) :
    (L.tensorIntPow n).degree y C = n • L.degree y C := by
  cases n with
  | ofNat n => simp [tensorIntPow, tensorPow_degree]
  | negSucc n =>
      change (L.dual.tensorPow (n + 1)).degree y C =
        Int.negSucc n • L.degree y C
      rw [tensorPow_degree, dual_degree, neg_nsmul]
      exact (negSucc_zsmul (L.degree y C) n).symm

/-- The Picard class underlying a relative line bundle. -/
def picardClass (L : RelativeLineBundle f) : PicardClass X := ⟦L.line⟧

@[simp]
theorem tensor_picardClass (L M : RelativeLineBundle f) :
    (L.tensor M).picardClass = L.picardClass * M.picardClass := rfl

@[simp]
theorem dual_picardClass (L : RelativeLineBundle f) :
    L.dual.picardClass = L.picardClass⁻¹ := by
  change (⟦L.line.dual⟧ : PicardClass X) = (⟦L.line⟧ : PicardClass X)⁻¹
  calc
    (⟦L.line.dual⟧ : PicardClass X) =
        PicardClass.dual (⟦L.line⟧ : PicardClass X) :=
      (PicardClass.dual_mk L.line).symm
    _ = (⟦L.line⟧ : PicardClass X)⁻¹ := PicardClass.dual_eq_inv _

@[simp]
theorem tensorPow_picardClass (L : RelativeLineBundle f) (n : ℕ) :
    (L.tensorPow n).picardClass = L.picardClass ^ n := by
  change ⟦(L.tensorPow n).line⟧ = (⟦L.line⟧ : PicardClass X) ^ n
  rw [tensorPow_line]
  exact (PicardClass.tensorPow_mk L.line n).symm

@[simp]
theorem tensorIntPow_picardClass (L : RelativeLineBundle f) (n : ℤ) :
    (L.tensorIntPow n).picardClass = L.picardClass ^ n := by
  change ⟦(L.tensorIntPow n).line⟧ = (⟦L.line⟧ : PicardClass X) ^ n
  rw [tensorIntPow_line]
  exact (PicardClass.zpow_mk L.line n).symm

/-- Two relative line bundles are isomorphic when their genuine module sheaves are isomorphic
and all their geometric component degrees agree. -/
def Isomorphic (L N : RelativeLineBundle f) : Prop :=
  Nonempty (L.line.Iso N.line) ∧ L.componentDegree = N.componentDegree

theorem isomorphic_refl (L : RelativeLineBundle f) : L.Isomorphic L :=
  ⟨⟨Iso.refl L.line.obj⟩, rfl⟩

theorem isomorphic_symm {L M : RelativeLineBundle f} (h : L.Isomorphic M) :
    M.Isomorphic L := by
  rcases h with ⟨⟨e⟩, hdegree⟩
  exact ⟨⟨e.symm⟩, hdegree.symm⟩

theorem isomorphic_trans {L M N : RelativeLineBundle f}
    (hLM : L.Isomorphic M) (hMN : M.Isomorphic N) : L.Isomorphic N := by
  rcases hLM with ⟨⟨e⟩, hdegree⟩
  rcases hMN with ⟨⟨e'⟩, hdegree'⟩
  exact ⟨⟨e.trans e'⟩, hdegree.trans hdegree'⟩

/-- Actual relative-line-bundle isomorphism is an equivalence relation. -/
instance isomorphicSetoid (f : X ⟶ S) : Setoid (RelativeLineBundle f) where
  r := Isomorphic
  iseqv :=
    { refl := isomorphic_refl
      symm := isomorphic_symm
      trans := isomorphic_trans }

/-- Tensor product of relative line bundles is associative up to an actual line-bundle
isomorphism and equality of all component degrees. -/
theorem tensorAssoc_isomorphic (L M N : RelativeLineBundle f) :
    ((L.tensor M).tensor N).Isomorphic (L.tensor (M.tensor N)) := by
  refine ⟨⟨LineBundle.tensorAssocIso L.line M.line N.line⟩, ?_⟩
  funext K hK y C
  exact add_assoc _ _ _

/-- Tensor product of relative line bundles is symmetric up to an actual line-bundle
isomorphism and equality of all component degrees. -/
theorem tensorComm_isomorphic (L M : RelativeLineBundle f) :
    (L.tensor M).Isomorphic (M.tensor L) := by
  refine ⟨⟨LineBundle.tensorCommIso L.line M.line⟩, ?_⟩
  funext K hK y C
  exact add_comm _ _

/-- The trivial relative line bundle is a left tensor unit up to actual isomorphism. -/
theorem trivialTensor_isomorphic : ((trivial f).tensor L).Isomorphic L := by
  refine ⟨⟨LineBundle.trivialTensorIso L.line⟩, ?_⟩
  funext K hK y C
  exact zero_add _

/-- The trivial relative line bundle is a right tensor unit up to actual isomorphism. -/
theorem tensorTrivial_isomorphic : (L.tensor (trivial f)).Isomorphic L := by
  refine ⟨⟨LineBundle.tensorTrivialIso L.line⟩, ?_⟩
  funext K hK y C
  exact add_zero _

/-- Tensoring a relative line bundle with its dual gives the trivial relative line bundle up to
an actual isomorphism. -/
theorem tensorDual_isomorphic : (L.tensor L.dual).Isomorphic (trivial f) := by
  refine ⟨⟨LineBundle.tensorDualIso L.line⟩, ?_⟩
  funext K hK y C
  exact add_neg_cancel _

/-- The dual tensored with the original relative line bundle gives the trivial relative line
bundle up to an actual isomorphism. -/
theorem dualTensor_isomorphic : (L.dual.tensor L).Isomorphic (trivial f) := by
  refine ⟨⟨LineBundle.dualTensorIso L.line⟩, ?_⟩
  funext K hK y C
  exact neg_add_cancel _

/-- Base change commutes with tensor product of relative line bundles, including their stored
component degrees. -/
theorem pullbackTensor_isomorphic (M : RelativeLineBundle f) (b : T ⟶ S) :
    ((L.tensor M).pullback b).Isomorphic ((L.pullback b).tensor (M.pullback b)) := by
  refine ⟨⟨LineBundle.pullbackTensorIso (pullback.fst f b) L.line M.line⟩, ?_⟩
  funext K hK y C
  rfl

/-- Base change preserves the trivial relative line bundle, including all component degrees. -/
theorem pullbackTrivial_isomorphic (b : T ⟶ S) :
    ((trivial f).pullback b).Isomorphic (trivial (pullback.snd f b)) := by
  refine ⟨⟨LineBundle.pullbackTrivialIso (pullback.fst f b)⟩, ?_⟩
  funext K hK y C
  rfl

/-- A relative line bundle is isomorphic to its double dual, including equality of every
component degree. -/
theorem dualDual_isomorphic : L.dual.dual.Isomorphic L := by
  refine ⟨⟨LineBundle.dualDualIso L.line⟩, ?_⟩
  funext K hK y C
  exact neg_neg _

/-- Base change commutes with relative duality, including the stored component degrees. -/
theorem pullbackDual_isomorphic (b : T ⟶ S) :
    (L.dual.pullback b).Isomorphic (L.pullback b).dual := by
  refine ⟨⟨LineBundle.pullbackDualIso (pullback.fst f b) L.line⟩, ?_⟩
  funext K hK y C
  rfl

/-- Base change commutes with every integer tensor power of a relative line bundle, including
the stored component degrees. -/
theorem pullbackIntPow_isomorphic (b : T ⟶ S) (n : ℤ) :
    ((L.tensorIntPow n).pullback b).Isomorphic ((L.pullback b).tensorIntPow n) := by
  refine ⟨⟨?w⟩, ?_⟩
  · change ((L.tensorIntPow n).line.pullback (pullback.fst f b)).Iso
      ((L.pullback b).tensorIntPow n).line
    rw [tensorIntPow_line, tensorIntPow_line]
    exact LineBundle.pullbackIntPowIso (pullback.fst f b) L.line n
  funext K hK y C
  change (L.tensorIntPow n).degree (y ≫ b)
      (irreducibleComponentsEquivOfSchemeIso
        (pullbackLeftPullbackSndIso f b y) C) =
    ((L.pullback b).tensorIntPow n).degree y C
  rw [tensorIntPow_degree, tensorIntPow_degree]
  rfl

/-- Degree on every geometric component is strictly positive.  For proper curves this is the
componentwise numerical ampleness criterion. -/
def FiberwiseAmple : Prop :=
  ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
    (C : irreducibleComponents
      (CategoryTheory.Limits.pullback f y : Scheme.{u})),
    0 < L.degree y C

/-- Degree on every geometric component is nonnegative. -/
def FiberwiseNef : Prop :=
  ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
    (C : irreducibleComponents
      (CategoryTheory.Limits.pullback f y : Scheme.{u})),
    0 ≤ L.degree y C

/-- Fibrewise ampleness implies fibrewise nefness. -/
theorem fiberwiseNef_of_fiberwiseAmple (h : L.FiberwiseAmple) : L.FiberwiseNef := by
  intro K _ y C
  exact (h K y C).le

/-- The tensor product of two fibrewise nef relative line bundles is fibrewise nef. -/
theorem tensor_fiberwiseNef (M : RelativeLineBundle f)
    (hL : L.FiberwiseNef) (hM : M.FiberwiseNef) : (L.tensor M).FiberwiseNef := by
  intro K _ y C
  exact add_nonneg (hL K y C) (hM K y C)

/-- Tensoring a fibrewise ample relative line bundle with a fibrewise nef one remains
fibrewise ample. -/
theorem tensor_fiberwiseAmple_of_fiberwiseNef (M : RelativeLineBundle f)
    (hL : L.FiberwiseAmple) (hM : M.FiberwiseNef) : (L.tensor M).FiberwiseAmple := by
  intro K _ y C
  exact add_pos_of_pos_of_nonneg (hL K y C) (hM K y C)

/-- Every positive tensor power of a fibrewise ample relative line bundle is fibrewise ample. -/
theorem tensorPow_fiberwiseAmple (n : ℕ) (hn : 0 < n) (h : L.FiberwiseAmple) :
    (L.tensorPow n).FiberwiseAmple := by
  intro K _ y C
  rw [tensorPow_degree]
  exact nsmul_pos (h K y C) (Nat.ne_of_gt hn)

/-- Arbitrary base change preserves positivity on every geometric component. -/
theorem pullback_fiberwiseAmple (b : T ⟶ S) (h : L.FiberwiseAmple) :
    (L.pullback b).FiberwiseAmple := by
  intro K _ y C
  exact h K (y ≫ b)
    (irreducibleComponentsEquivOfSchemeIso
      (pullbackLeftPullbackSndIso f b y) C)

/-- Arbitrary base change preserves nonnegative component degrees. -/
theorem pullback_fiberwiseNef (b : T ⟶ S) (h : L.FiberwiseNef) :
    (L.pullback b).FiberwiseNef := by
  intro K _ y C
  exact h K (y ≫ b)
    (irreducibleComponentsEquivOfSchemeIso
      (pullbackLeftPullbackSndIso f b y) C)

/-- Actual sheaf cohomology of the restriction of a relative line bundle to an arbitrary
geometric fibre square. -/
abbrev FiberCohomology {K : Type u} [Field K] (y : Spec (.of K) ⟶ S)
    (Z : Scheme.{u}) (fst : Z ⟶ X) (snd : Z ⟶ Spec (.of K))
    (_h : IsPullback fst snd f y) (n : ℕ)
    [CategoryTheory.HasExt.{u}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})] :=
  SheafCohomology ((L.line.pullback fst).obj) n

end RelativeLineBundle

/-- A base-change-stable relative dualizing line package.  Consumers use its actual module sheaf,
its component degrees, and the unconditional relative-line pullback operation. -/
structure RelativeDualizingSheaf (f : X ⟶ S) where
  omega : RelativeLineBundle f

namespace RelativeDualizingSheaf

variable {f : X ⟶ S} (D : RelativeDualizingSheaf f)

/-- Relative dualizing data after arbitrary base change. -/
def pullback (b : T ⟶ S) :
    RelativeDualizingSheaf (CategoryTheory.Limits.pullback.snd f b) :=
  ⟨D.omega.pullback b⟩

/-- Stability of a proper nodal family, expressed by positivity of its dualizing line on every
geometric irreducible component. -/
def IsStable : Prop :=
  AtWorstNodal f ∧ IsProper f ∧ D.omega.FiberwiseAmple

/-- Semistability of a proper nodal family, expressed by nonnegative dualizing degree. -/
def IsSemistable : Prop :=
  AtWorstNodal f ∧ IsProper f ∧ D.omega.FiberwiseNef

/-- A stable family is semistable. -/
theorem isSemistable_of_isStable (h : D.IsStable) : D.IsSemistable :=
  ⟨h.1, h.2.1, D.omega.fiberwiseNef_of_fiberwiseAmple h.2.2⟩

/-- Stability is preserved by arbitrary base change whenever properness is pulled back through
Mathlib's proper-morphism instance. -/
theorem pullback_isStable (b : T ⟶ S) (h : D.IsStable) :
    (D.pullback b).IsStable := by
  let sq := IsPullback.of_hasPullback f b
  refine ⟨AtWorstNodal.of_isPullback sq h.1, ?_,
    D.omega.pullback_fiberwiseAmple b h.2.2⟩
  exact MorphismProperty.of_isPullback (P := @IsProper) sq h.2.1

/-- Semistability is preserved by arbitrary base change. -/
theorem pullback_isSemistable (b : T ⟶ S) (h : D.IsSemistable) :
    (D.pullback b).IsSemistable := by
  let sq := IsPullback.of_hasPullback f b
  refine ⟨AtWorstNodal.of_isPullback sq h.1, ?_, D.omega.pullback_fiberwiseNef b h.2.2⟩
  exact MorphismProperty.of_isPullback (P := @IsProper) sq h.2.1

end RelativeDualizingSheaf

end


end GromovWitten.AlgebraicGeometry.Curves
