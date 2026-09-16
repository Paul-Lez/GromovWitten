/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Sites.Stack
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Module sheaves and vector bundles on stack sites

The predicates below use Mathlib's actual sheaves of modules.  Constant rank is witnessed by
local free presentations whose indexing sets are equivalent to `Fin r`; it is not a numerical
tag detached from a module.  Operations are functors on the module categories and carry the
preservation and rank identities needed by cone and obstruction-theory constructions.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.BraidedCategory

namespace GromovWitten.AlgebraicGeometry.Modules

universe w v u

variable {C : Type u} [Category.{v} C]
  [UnivLE.{max u v, w}]
  (S : Sites.RingedSite.{w} C)
  [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Quasi-coherence is Mathlib's local-presentation predicate on sheaves of modules. -/
abbrev IsQuasiCoherent (M : S.Modules) : Prop :=
  SheafOfModules.IsQuasicoherent M

/-- Finite presentation is Mathlib's finite local-presentation predicate. -/
abbrev IsFinitePresentation (M : S.Modules) : Prop :=
  SheafOfModules.IsFinitePresentation M

/-- A coherent module is quasi-coherent and finitely presented. -/
def IsCoherent (M : S.Modules) : Prop :=
  IsQuasiCoherent S M ∧ IsFinitePresentation S M

/-- Chosen local trivializations of a finite locally free sheaf of constant rank `r`.  Each
local basis is explicitly identified with `Fin r`. -/
structure FiniteLocallyFreeOfRankData (M : S.Modules) (r : ℕ) where
  trivialization : M.LocalGeneratorsData.{u}
  locallyFreeData : trivialization.IsLocallyFreeData
  finitePresentation : M.IsFinitePresentation
  rank (i : trivialization.I) : Nonempty ((trivialization.generators i).I ≃ Fin r)

/-- A finite locally free sheaf of constant rank `r`, with no preferred trivialization in the
public proposition. -/
def IsFiniteLocallyFreeOfRank (M : S.Modules) (r : ℕ) : Prop :=
  Nonempty (FiniteLocallyFreeOfRankData S M r)

namespace IsFiniteLocallyFreeOfRank

variable {S} {M : S.Modules} {r : ℕ}

/-- Constant finite rank supplies Mathlib's intrinsic local-freeness predicate. -/
theorem isLocallyFree (h : IsFiniteLocallyFreeOfRank S M r) : M.IsLocallyFree :=
  let d := Classical.choice h
  let _ : d.trivialization.IsLocallyFreeData := d.locallyFreeData
  d.trivialization.isLocallyFree

/-- Constant finite rank supplies quasi-coherence. -/
theorem isQuasiCoherent (h : IsFiniteLocallyFreeOfRank S M r) : M.IsQuasicoherent := by
  let d := Classical.choice h
  let _ : M.IsFinitePresentation := d.finitePresentation
  infer_instance

/-- A finite locally free module is coherent. -/
theorem isCoherent (h : IsFiniteLocallyFreeOfRank S M r) : IsCoherent S M :=
  let d := Classical.choice h
  ⟨isQuasiCoherent h, d.finitePresentation⟩

end IsFiniteLocallyFreeOfRank

/-- Invertible modules are finite locally free modules of rank one. -/
abbrev IsInvertible (M : S.Modules) : Prop :=
  IsFiniteLocallyFreeOfRank S M 1

/-! ## Tensor product -/

section Tensor

variable [HasWeakSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Tensor product of module sheaves.  It is constructed by taking the pointwise tensor product
of the underlying presheaves over the retained commutative structure presheaf and then applying
Mathlib's module sheafification functor. -/
noncomputable def tensor : (S.Modules × S.Modules) ⥤ S.Modules := by
  letI : Presheaf.IsLocallyInjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  let sh := PresheafOfModules.sheafification
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)
  exact Functor.prod (SheafOfModules.forget S.ringStructureSheaf)
      (SheafOfModules.forget S.ringStructureSheaf) ⋙
    MonoidalCategory.tensor
      (PresheafOfModules
        (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat)) ⋙
    sh

/-- The tensor unit is the structure sheaf regarded as a module over itself. -/
noncomputable abbrev tensorUnit : S.Modules :=
  SheafOfModules.unit S.ringStructureSheaf

/-- The constructed tensor has the structure sheaf as a left unit.  The comparison is the
pointwise module unitor followed by the counit of genuine module sheafification. -/
noncomputable def tensorLeftUnitIso (M : S.Modules) :
    (tensor S).obj (tensorUnit S, M) ≅ M := by
  letI : Presheaf.IsLocallyInjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
  let sh := PresheafOfModules.sheafification
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)
  letI : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  change sh.obj (_ ⊗ (SheafOfModules.forget S.ringStructureSheaf).obj M) ≅ M
  exact sh.mapIso
      (λ_ ((SheafOfModules.forget S.ringStructureSheaf).obj M)) ≪≫
    (asIso adj.counit).app M

/-- The constructed tensor has the structure sheaf as a right unit. -/
noncomputable def tensorRightUnitIso (M : S.Modules) :
    (tensor S).obj (M, tensorUnit S) ≅ M := by
  letI : Presheaf.IsLocallyInjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
  let sh := PresheafOfModules.sheafification
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)
  letI : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  change sh.obj ((SheafOfModules.forget S.ringStructureSheaf).obj M ⊗ _) ≅ M
  exact sh.mapIso
      (ρ_ ((SheafOfModules.forget S.ringStructureSheaf).obj M)) ≪≫
    (asIso adj.counit).app M

/-- Tensor product is symmetric, by sheafifying the pointwise symmetry of tensor products of
modules over the commutative structure presheaf. -/
noncomputable def tensorSymmetry (M N : S.Modules) :
    (tensor S).obj (M, N) ≅ (tensor S).obj (N, M) := by
  letI : Presheaf.IsLocallyInjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
  letI : SymmetricCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.symmetricCategory (R := S.structureSheaf.obj)
  let sh := PresheafOfModules.sheafification
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)
  change sh.obj (_ ⊗ _) ≅ sh.obj (_ ⊗ _)
  exact sh.mapIso (β_ _ _)

end Tensor

/-! ## Constructed finite free modules and direct sums -/

section DirectSum

variable [HasWeakSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The direct sum bifunctor on sheaves of modules, constructed as the categorical binary
coproduct in Mathlib's abelian category of module sheaves. -/
noncomputable def directSum : (S.Modules × S.Modules) ⥤ S.Modules :=
  Functor.uncurry.obj (Limits.coprod.functor (C := S.Modules))

/-- The zero module sheaf, constructed as the initial object. -/
noncomputable abbrev zero : S.Modules := ⊥_ S.Modules

/-- Direct sum is associative by the canonical coproduct associator. -/
noncomputable def directSumAssociator (L M N : S.Modules) :
    (directSum S).obj ((directSum S).obj (L, M), N) ≅
      (directSum S).obj (L, (directSum S).obj (M, N)) :=
  Limits.coprod.associator L M N

/-- Direct sum is symmetric by the canonical coproduct braiding. -/
noncomputable def directSumSymmetry (L M : S.Modules) :
    (directSum S).obj (L, M) ≅ (directSum S).obj (M, L) :=
  Limits.coprod.braiding L M

/-- The zero sheaf is a left unit for direct sum. -/
noncomputable def zeroDirectSumIso (M : S.Modules) :
    (directSum S).obj (zero S, M) ≅ M :=
  Limits.coprod.leftUnitor M

/-- The zero sheaf is a right unit for direct sum. -/
noncomputable def directSumZeroIso (M : S.Modules) :
    (directSum S).obj (M, zero S) ≅ M :=
  Limits.coprod.rightUnitor M

/-- An equivalence of bases induces an isomorphism of the corresponding free module sheaves. -/
noncomputable def freeEquiv {I J : Type w} (e : I ≃ J) :
    SheafOfModules.free (R := S.ringStructureSheaf) I ≅
      SheafOfModules.free (R := S.ringStructureSheaf) J where
  hom := SheafOfModules.freeMap e
  inv := SheafOfModules.freeMap e.symm
  hom_inv_id := by
    apply (SheafOfModules.freeHomEquiv _).injective
    ext i
    rw [SheafOfModules.freeHomEquiv_comp_apply,
      SheafOfModules.freeHomEquiv_freeMap]
    simp only [Function.comp_apply,
      SheafOfModules.sectionMap_freeMap_freeSection, Equiv.symm_apply_apply]
  inv_hom_id := by
    apply (SheafOfModules.freeHomEquiv _).injective
    ext i
    rw [SheafOfModules.freeHomEquiv_comp_apply,
      SheafOfModules.freeHomEquiv_freeMap]
    simp only [Function.comp_apply,
      SheafOfModules.sectionMap_freeMap_freeSection, Equiv.apply_symm_apply]

/-- The canonical free sheaf of rank `r`.  The universe lift changes only the carrier universe;
its basis is still explicitly equivalent to `Fin r`. -/
noncomputable abbrev freeOfRank (r : ℕ) : S.Modules :=
  SheafOfModules.free (R := S.ringStructureSheaf) (ULift.{w} (Fin r))

/-- The canonical rank-one free sheaf is the tensor unit. -/
noncomputable def freeOfRankOneIsoTensorUnit :
    freeOfRank S 1 ≅ tensorUnit S :=
  Limits.coproductUniqueIso
    (fun (_ : ULift.{w} (Fin 1)) ↦ tensorUnit S)

/-- Binary direct sum of the constructed rank-`r` and rank-`s` free sheaves is the constructed
rank-`r+s` free sheaf. -/
noncomputable def freeOfRankDirectSumIso (r s : ℕ) :
    (directSum S).obj (freeOfRank S r, freeOfRank S s) ≅
      freeOfRank S (r + s) :=
  SheafOfModules.freeSumIso (R := S.ringStructureSheaf)
      (ULift.{w} (Fin r)) (ULift.{w} (Fin s)) ≪≫
    freeEquiv S
      ((Equiv.sumCongr (Equiv.ulift.{w, 0}) (Equiv.ulift.{w, 0})).trans
        (finSumFinEquiv.trans (Equiv.ulift.{w, 0}).symm))

end DirectSum

section FreeRank

variable [HasSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ X, HasSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [HasBinaryProducts C]

/-- The canonical free sheaf really is finite locally free of its displayed rank.  The proof
uses Mathlib's local generators, the no-relations presentation of a free sheaf, and the actual
basis equivalence with `Fin r`. -/
noncomputable def freeOfRankData (r : ℕ) :
    FiniteLocallyFreeOfRankData S (freeOfRank S r) r := by
  let q := (SheafOfModules.free.generatingSections
    (R := S.ringStructureSheaf) (ULift.{w} (Fin r))).localGeneratorsData
  refine {
    trivialization := q
    locallyFreeData := inferInstance
    finitePresentation := ?_
    rank := ?_ }
  · refine ⟨q.quasiCoherentData, ?_⟩
    refine { isFinite_presentation := fun i => ?_ }
    refine {
      isFiniteType_generators := ?_
      isFiniteType_relations := ?_ }
    · constructor
      change Finite (ULift.{w} (Fin r))
      infer_instance
    · constructor
      change Finite (ULift.{w} Empty)
      infer_instance
  · intro i
    change Nonempty (ULift.{w} (Fin r) ≃ Fin r)
    exact ⟨Equiv.ulift⟩

/-- The constructed rank-`r` free sheaf satisfies the public finite-locally-free predicate. -/
theorem freeOfRank_isFiniteLocallyFreeOfRank (r : ℕ) :
    IsFiniteLocallyFreeOfRank S (freeOfRank S r) r :=
  ⟨freeOfRankData S r⟩

/-- Transport concrete finite-local-free rank data across an actual module-sheaf isomorphism. -/
noncomputable def FiniteLocallyFreeOfRankData.ofIso
    {M N : S.Modules} {r : ℕ}
    (d : FiniteLocallyFreeOfRankData S M r) (e : M ≅ N) :
    FiniteLocallyFreeOfRankData S N r := by
  let q : N.LocalGeneratorsData.{u} := {
    I := d.trivialization.I
    X := d.trivialization.X
    coversTop := d.trivialization.coversTop
    generators := fun i =>
      SheafOfModules.GeneratingSections.equivOfIso
        ((SheafOfModules.overFunctor S.ringStructureSheaf
          (d.trivialization.X i)).mapIso e) (d.trivialization.generators i) }
  refine {
    trivialization := q
    locallyFreeData := ?_
    finitePresentation :=
      (SheafOfModules.isFinitePresentation S.ringStructureSheaf).prop_of_iso
        e d.finitePresentation
    rank := ?_ }
  · refine { isIso := fun i => ?_ }
    let piIso := @asIso _ _ _ _ (d.trivialization.generators i).π
      (d.locallyFreeData.isIso i)
    let mappedIso := (SheafOfModules.overFunctor S.ringStructureSheaf
      (d.trivialization.X i)).mapIso e
    change IsIso ((d.trivialization.generators i).ofEpi mappedIso.hom).π
    rw [SheafOfModules.GeneratingSections.ofEpi_π]
    exact (piIso ≪≫ mappedIso).isIso_hom
  · intro i
    exact d.rank i

omit [HasSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasBinaryProducts C] in
/-- Constant finite-local-free rank is invariant under isomorphism. -/
theorem IsFiniteLocallyFreeOfRank.ofIso
    {M N : S.Modules} {r : ℕ}
    (h : IsFiniteLocallyFreeOfRank S M r) (e : M ≅ N) :
    IsFiniteLocallyFreeOfRank S N r :=
  ⟨(FiniteLocallyFreeOfRankData.ofIso S (Classical.choice h) e)⟩

/-- The actual tensor unit is finite locally free of rank one. -/
theorem tensorUnit_isFiniteLocallyFreeOfRank :
    IsFiniteLocallyFreeOfRank S (tensorUnit S) 1 :=
  IsFiniteLocallyFreeOfRank.ofIso S
    (freeOfRank_isFiniteLocallyFreeOfRank S 1)
    (freeOfRankOneIsoTensorUnit S)

omit [HasBinaryProducts C] in
/-- Tensoring a finite locally free module with the structure sheaf on the left preserves its
actual rank. -/
theorem tensorUnit_left_isFiniteLocallyFreeOfRank
    {M : S.Modules} {r : ℕ} (h : IsFiniteLocallyFreeOfRank S M r) :
    IsFiniteLocallyFreeOfRank S ((tensor S).obj (tensorUnit S, M)) r :=
  IsFiniteLocallyFreeOfRank.ofIso S h (tensorLeftUnitIso S M).symm

omit [HasBinaryProducts C] in
/-- Tensoring a finite locally free module with the structure sheaf on the right preserves its
actual rank. -/
theorem tensorUnit_right_isFiniteLocallyFreeOfRank
    {M : S.Modules} {r : ℕ} (h : IsFiniteLocallyFreeOfRank S M r) :
    IsFiniteLocallyFreeOfRank S ((tensor S).obj (M, tensorUnit S)) r :=
  IsFiniteLocallyFreeOfRank.ofIso S h (tensorRightUnitIso S M).symm

/-- The direct sum rank formula is constructed for the canonical finite free modules. -/
theorem freeOfRank_directSum_isFiniteLocallyFreeOfRank (r s : ℕ) :
    IsFiniteLocallyFreeOfRank S
      ((directSum S).obj (freeOfRank S r, freeOfRank S s)) (r + s) :=
  IsFiniteLocallyFreeOfRank.ofIso S
    (freeOfRank_isFiniteLocallyFreeOfRank S (r + s))
    (freeOfRankDirectSumIso S r s).symm

end FreeRank

/-
Retired provisional module-operation and atlas-descent packages.  Their tensor/dual/symmetric
functors, preservation theorems, rank formulas, and descent equivalence were supplied as fields.
The concrete Mathlib-based predicates `IsCoherent` and `IsFiniteLocallyFreeOfRank` above remain
active; the operations must be constructed from the sheaf-of-modules API.

/-- Tensor, dual, symmetric, and exterior operations on stack modules.  All operations are
honest functors; the displayed isomorphisms express their algebraic laws. -/
structure Operations where
  tensor : (S.Modules × S.Modules) ⥤ S.Modules
  unit : S.Modules
  leftUnit (M : S.Modules) : tensor.obj (unit, M) ≅ M
  rightUnit (M : S.Modules) : tensor.obj (M, unit) ≅ M
  associator (L M N : S.Modules) :
    tensor.obj (tensor.obj (L, M), N) ≅ tensor.obj (L, tensor.obj (M, N))
  symmetry (M N : S.Modules) : tensor.obj (M, N) ≅ tensor.obj (N, M)
  dual : S.Modulesᵒᵖ ⥤ S.Modules
  evaluation (M : S.Modules) : tensor.obj (dual.obj (.op M), M) ⟶ unit
  bidual (M : S.Modules) : M ⟶ dual.obj (.op (dual.obj (.op M)))
  symmetricPower (n : ℕ) : S.Modules ⥤ S.Modules
  exteriorPower (n : ℕ) : S.Modules ⥤ S.Modules
  directSum : (S.Modules × S.Modules) ⥤ S.Modules
  tensor_quasiCoherent (M N : S.Modules)
    (hM : IsQuasiCoherent S M) (hN : IsQuasiCoherent S N) :
    IsQuasiCoherent S (tensor.obj (M, N))
  dual_quasiCoherent (M : S.Modules) (hM : IsQuasiCoherent S M) :
    IsQuasiCoherent S (dual.obj (.op M))
  symmetric_quasiCoherent (n : ℕ) (M : S.Modules) (hM : IsQuasiCoherent S M) :
    IsQuasiCoherent S ((symmetricPower n).obj M)
  exterior_quasiCoherent (n : ℕ) (M : S.Modules) (hM : IsQuasiCoherent S M) :
    IsQuasiCoherent S ((exteriorPower n).obj M)
  tensor_rank {M N : S.Modules} {r s : ℕ}
    (hM : IsFiniteLocallyFreeOfRank S M r)
    (hN : IsFiniteLocallyFreeOfRank S N s) :
    IsFiniteLocallyFreeOfRank S (tensor.obj (M, N)) (r * s)
  dual_rank {M : S.Modules} {r : ℕ}
    (hM : IsFiniteLocallyFreeOfRank S M r) :
    IsFiniteLocallyFreeOfRank S (dual.obj (.op M)) r
  directSum_rank {M N : S.Modules} {r s : ℕ}
    (hM : IsFiniteLocallyFreeOfRank S M r)
    (hN : IsFiniteLocallyFreeOfRank S N s) :
    IsFiniteLocallyFreeOfRank S (directSum.obj (M, N)) (r + s)

namespace Operations

variable {S} (O : Operations S)

/-- Dualization preserves vector-bundle rank. -/
theorem dual_isFiniteLocallyFreeOfRank {M : S.Modules} {r : ℕ}
    (hM : IsFiniteLocallyFreeOfRank S M r) :
    IsFiniteLocallyFreeOfRank S (O.dual.obj (.op M)) r :=
  O.dual_rank hM

/-- Tensor-product ranks multiply. -/
theorem tensor_isFiniteLocallyFreeOfRank {M N : S.Modules} {r s : ℕ}
    (hM : IsFiniteLocallyFreeOfRank S M r)
    (hN : IsFiniteLocallyFreeOfRank S N s) :
    IsFiniteLocallyFreeOfRank S (O.tensor.obj (M, N)) (r * s) :=
  O.tensor_rank hM hN

/-- Direct-sum ranks add, giving the sign convention used by virtual rank. -/
theorem directSum_isFiniteLocallyFreeOfRank {M N : S.Modules} {r s : ℕ}
    (hM : IsFiniteLocallyFreeOfRank S M r)
    (hN : IsFiniteLocallyFreeOfRank S N s) :
    IsFiniteLocallyFreeOfRank S (O.directSum.obj (M, N)) (r + s) :=
  O.directSum_rank hM hN

end Operations

/-- Effective descent of modules along an atlas.  The descent category retains its two
projections and cocycle condition through the comparison equivalence. -/
structure AtlasDescent (A : S.Modules → Prop) where
  descentCategory : Type (max u w)
  descentCategory_inst : Category.{max v w} descentCategory
  restrict : S.Modules ⥤ descentCategory
  equivalence : S.Modules ≌ descentCategory
  equivalenceFunctorIso : equivalence.functor ≅ restrict
  descentProperty : descentCategory → Prop
  property_local (M : S.Modules) : A M ↔ descentProperty (restrict.obj M)

attribute [instance] AtlasDescent.descentCategory_inst

/-- Descent is effective: restricting and reconstructing a module returns it up to canonical
isomorphism. -/
def AtlasDescent.reconstructIso {A : S.Modules → Prop} (D : AtlasDescent S A)
    (M : S.Modules) : D.equivalence.inverse.obj (D.restrict.obj M) ≅ M :=
  D.equivalence.inverse.mapIso ((D.equivalenceFunctorIso.app M).symm) ≪≫
  D.equivalence.unitIso.symm.app M

-/

end GromovWitten.AlgebraicGeometry.Modules
