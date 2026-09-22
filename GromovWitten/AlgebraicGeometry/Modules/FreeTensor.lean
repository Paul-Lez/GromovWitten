/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Modules.TensorCoherence

/-!
# Tensor products of finite free module sheaves

Finite coproduct preservation and the tensor unit comparison construct the isomorphism
between the tensor of free sheaves of ranks `r`, `s` and the free sheaf of rank `r * s`.
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

section FreeTensor

variable [HasWeakSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]

private noncomputable def freeTensorCoproductIso (r s : ℕ) :
    (∐ fun (_ : ULift.{w} (Fin s)) => freeOfRank S r) ≅
      (tensor S).obj (freeOfRank S r, freeOfRank S s) := by
  let I := ULift.{w} (Fin s)
  let F := tensorRightFunctor S (freeOfRank S r)
  let eUnit : freeOfRank S r ≅ F.obj (tensorUnit S) :=
    (tensorRightUnitIso S (freeOfRank S r)).symm
  let w : Discrete.functor (fun (_ : I) => freeOfRank S r) ≅
      (Discrete.functor (fun (_ : I) => tensorUnit S)) ⋙ F :=
    Discrete.natIso (fun _ => eUnit)
  letI : PreservesFiniteCoproducts F := by
    dsimp [F]
    exact tensorRightFunctor_preservesFiniteCoproducts S (freeOfRank S r)
  let P : IsColimit (Cofan.mk
      (∐ fun (_ : I) => freeOfRank S r)
      (fun i => Sigma.ι (fun (_ : I) => freeOfRank S r) i)) :=
    coproductIsCoproduct _
  let Q : IsColimit (F.mapCocone
      (SheafOfModules.freeCofan (R := S.ringStructureSheaf) I)) :=
    isColimitOfPreserves F
      (SheafOfModules.isColimitFreeCofan (R := S.ringStructureSheaf) I)
  change (∐ fun (_ : I) => freeOfRank S r) ≅ F.obj (freeOfRank S s)
  exact IsColimit.coconePointsIsoOfNatIso P Q w

noncomputable def freeOfRankTensorIso (r s : ℕ) :
    (tensor S).obj (freeOfRank S r, freeOfRank S s) ≅
      freeOfRank S (r * s) := by
  let I := ULift.{w} (Fin s)
  let J := ULift.{w} (Fin r)
  let nested :
      (∐ fun (_ : I) => freeOfRank S r) ≅
        SheafOfModules.free (R := S.ringStructureSheaf) (Σ _ : I, J) := by
    change (∐ fun (_ : I) => ∐ fun (_ : J) => tensorUnit S) ≅
      ∐ fun (_ : Σ _ : I, J) => tensorUnit S
    exact sigmaSigmaIso (fun (_ : I) => J) (fun _ _ => tensorUnit S)
  let eIndex : (Σ _ : I, J) ≃ ULift.{w} (Fin (r * s)) :=
    (Equiv.sigmaEquivProd I J).trans
      ((Equiv.ulift : I ≃ Fin s).prodCongr (Equiv.ulift : J ≃ Fin r)) |>.trans
      (finProdFinEquiv.trans (Equiv.cast (by rw [Nat.mul_comm s r]))) |>.trans
      (Equiv.ulift.symm)
  exact (freeTensorCoproductIso S r s).symm ≪≫ nested ≪≫ freeEquiv S eIndex

theorem freeOfRankTensor_isFiniteLocallyFreeOfRank
    [HasSheafify S.topology AddCommGrpCat.{w}]
    [∀ X, HasSheafify (S.topology.over X) AddCommGrpCat.{w}]
    [HasBinaryProducts C]
    (r s : ℕ) :
    IsFiniteLocallyFreeOfRank S ((tensor S).obj (freeOfRank S r, freeOfRank S s)) (r * s) :=
  IsFiniteLocallyFreeOfRank.ofIso S
    (freeOfRank_isFiniteLocallyFreeOfRank S (r * s))
    (freeOfRankTensorIso S r s).symm

end FreeTensor

end GromovWitten.AlgebraicGeometry.Modules
