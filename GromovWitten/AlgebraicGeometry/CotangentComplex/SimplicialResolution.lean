/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Iterated cotriple maps for a commutative algebra

For a commutative ring `R`, the multivariable polynomial algebra gives the free
commutative `R`-algebra functor.  Its adjunction with the underlying-set functor
has a comonad on `CommAlgCat R`.  This file defines its iterated powers, the
elementary face and degeneracy maps, their naturality, the face-face identity,
and the two counit cancellations.  It also constructs the iterated-counit augmentation
and proves its naturality and compatibility with every face.

These declarations are the proved algebraic core used by later constructions of
the augmented resolution and its alternating-face complex.  The file does not
claim a `SimplicialObject`: Mathlib currently does not provide an equivalence
between `SimplexCategoryGenRel` and `SimplexCategory`, so no transport through
that presentation is asserted here.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

open CategoryTheory CategoryTheory.Limits
open Opposite
open scoped Simplicial

universe u

namespace SimplicialResolution

noncomputable section

variable (R : Type u) [CommRing R]

/-! ## The free commutative algebra adjunction -/

/-- The free commutative `R`-algebra on a type. -/
def free : Type u ⥤ CommAlgCat.{u} R where
  obj X := CommAlgCat.of R (MvPolynomial X R)
  map {X Y} f := CommAlgCat.ofHom (MvPolynomial.rename (f : X → Y))

@[simp]
theorem free_obj_carrier (X : Type u) : ((free R).obj X : Type u) = MvPolynomial X R :=
  rfl

@[simp]
theorem free_map_apply {X Y : Type u} (f : X ⟶ Y) (x : MvPolynomial X R) :
    (free R).map f x = MvPolynomial.rename f x :=
  rfl

/-- The free/forgetful adjunction for commutative `R`-algebras. -/
def freeForgetAdjunction : free R ⊣ (CategoryTheory.forget (CommAlgCat.{u} R)) :=
  Adjunction.mkOfHomEquiv
      { homEquiv := fun X A =>
        { toFun := fun f => TypeCat.ofHom (fun x => f.hom (MvPolynomial.X x))
          invFun := fun f => CommAlgCat.ofHom (MvPolynomial.aeval f)
          left_inv := by
            intro f
            apply CommAlgCat.hom_ext
            apply MvPolynomial.algHom_ext
            intro x
            change MvPolynomial.aeval (fun x => f.hom (MvPolynomial.X x))
                (MvPolynomial.X x) = f.hom (MvPolynomial.X x)
            rw [MvPolynomial.aeval_X]
          right_inv := by
            intro f
            apply ConcreteCategory.hom_ext
            intro x
            change MvPolynomial.aeval (fun x => f x) (MvPolynomial.X x) = f x
            rw [MvPolynomial.aeval_X] }
        homEquiv_naturality_left_symm := by
          intro X Y A f g
          apply CommAlgCat.hom_ext
          apply MvPolynomial.algHom_ext
          intro x
          change MvPolynomial.aeval (fun y => g (f y)) (MvPolynomial.X x) =
            MvPolynomial.aeval (fun y => g y) (MvPolynomial.rename f (MvPolynomial.X x))
          rw [MvPolynomial.aeval_X, MvPolynomial.rename_X, MvPolynomial.aeval_X] }

/-- The canonical comonad on commutative `R`-algebras. -/
abbrev comonad : Comonad (CommAlgCat.{u} R) :=
  (freeForgetAdjunction R).toComonad

/-! ## Iterated comonad and its elementary simplicial maps -/

variable {R}

/-- Iterated application of the cotriple endofunctor. -/
def power (G : Comonad (CommAlgCat.{u} R)) : ℕ → CommAlgCat.{u} R ⥤ CommAlgCat.{u} R
  | 0 => 𝟭 _
  | n + 1 => power G n ⋙ (G : CommAlgCat.{u} R ⥤ CommAlgCat.{u} R)

@[simp]
theorem power_zero (G : Comonad (CommAlgCat.{u} R)) : power G 0 = 𝟭 _ :=
  rfl

@[simp]
theorem power_succ (G : Comonad (CommAlgCat.{u} R)) (n : ℕ) :
    power G (n + 1) = power G n ⋙ (G : CommAlgCat.{u} R ⥤ CommAlgCat.{u} R) :=
  rfl

section ElementaryMaps

variable (G : Comonad (CommAlgCat.{u} R))

/-- The `i`th face map `G^(n+1) X ⟶ G^n X`.  Index `0` is the outermost
factor; the remaining faces are obtained by mapping the previous face through
the outer comonad. -/
def facePower (G : Comonad (CommAlgCat.{u} R)) : (n : ℕ) → Fin (n + 1) →
    (X : CommAlgCat.{u} R) →
    (power G (n + 1)).obj X ⟶ (power G n).obj X
  | 0, _, X => G.ε.app X
  | n + 1, i, X => Fin.cases
      (G.ε.app ((power G (n + 1)).obj X))
      (fun j => G.map (facePower G n j X)) i

/-- The `i`th degeneracy map `G^(n+1) X ⟶ G^(n+2) X`, obtained from the
comultiplication on the `i`th factor. -/
def degeneracyPower (G : Comonad (CommAlgCat.{u} R)) : (n : ℕ) → Fin (n + 1) →
    (X : CommAlgCat.{u} R) →
    (power G (n + 1)).obj X ⟶ (power G (n + 2)).obj X
  | 0, _, X => G.δ.app X
  | n + 1, i, X => Fin.cases
      (G.δ.app ((power G (n + 1)).obj X))
      (fun j => G.map (degeneracyPower G n j X)) i

@[simp]
theorem facePower_zero (G : Comonad (CommAlgCat.{u} R)) (X : CommAlgCat.{u} R)
    (i : Fin 1) : facePower G 0 i X = G.ε.app X := by
  rfl

@[simp]
theorem facePower_succ_zero (G : Comonad (CommAlgCat.{u} R)) (n : ℕ)
    (X : CommAlgCat.{u} R) :
    facePower G (n + 1) 0 X = G.ε.app ((power G (n + 1)).obj X) := by
  rfl

@[simp]
theorem facePower_succ_succ (G : Comonad (CommAlgCat.{u} R)) (n : ℕ)
    (i : Fin (n + 1)) (X : CommAlgCat.{u} R) :
    facePower G (n + 1) i.succ X = G.map (facePower G n i X) := by
  rfl

@[simp]
theorem degeneracyPower_zero (G : Comonad (CommAlgCat.{u} R)) (X : CommAlgCat.{u} R)
    (i : Fin 1) : degeneracyPower G 0 i X = G.δ.app X := by
  rfl

@[simp]
theorem degeneracyPower_succ_zero (G : Comonad (CommAlgCat.{u} R)) (n : ℕ)
    (X : CommAlgCat.{u} R) :
    degeneracyPower G (n + 1) 0 X = G.δ.app ((power G (n + 1)).obj X) := by
  rfl

@[simp]
theorem degeneracyPower_succ_succ (G : Comonad (CommAlgCat.{u} R)) (n : ℕ)
    (i : Fin (n + 1)) (X : CommAlgCat.{u} R) :
    degeneracyPower G (n + 1) i.succ X = G.map (degeneracyPower G n i X) := by
  rfl

/-! ## Naturality and the two counit cancellations -/

theorem facePower_naturality (G : Comonad (CommAlgCat.{u} R)) (n : ℕ)
    (i : Fin (n + 1)) {X Y : CommAlgCat.{u} R} (f : X ⟶ Y) :
    (power G (n + 1)).map f ≫ facePower G n i Y =
      facePower G n i X ≫ (power G n).map f := by
  induction n with
  | zero =>
      change G.map f ≫ G.ε.app Y = G.ε.app X ≫ f
      exact G.ε.naturality f
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · dsimp [facePower, power]
        exact G.ε.naturality ((power G (n + 1)).map f)
      · dsimp [facePower, power]
        change G.map ((power G (n + 1)).map f) ≫ G.map (facePower G n j Y) =
          G.map (facePower G n j X) ≫ G.map ((power G n).map f)
        rw [← Functor.map_comp, ih, Functor.map_comp]

theorem degeneracyPower_naturality (G : Comonad (CommAlgCat.{u} R)) (n : ℕ)
    (i : Fin (n + 1)) {X Y : CommAlgCat.{u} R} (f : X ⟶ Y) :
    (power G (n + 1)).map f ≫ degeneracyPower G n i Y =
      degeneracyPower G n i X ≫ (power G (n + 2)).map f := by
  induction n with
  | zero =>
      change G.map f ≫ G.δ.app Y = G.δ.app X ≫ G.map (G.map f)
      exact G.δ.naturality f
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · dsimp [degeneracyPower, power]
        exact G.δ.naturality ((power G (n + 1)).map f)
      · dsimp [degeneracyPower, power]
        change G.map ((power G (n + 1)).map f) ≫ G.map (degeneracyPower G n j Y) =
          G.map (degeneracyPower G n j X) ≫ G.map ((power G (n + 2)).map f)
        rw [← Functor.map_comp, ih, Functor.map_comp]

/-! ### The face-face identity and counit cancellations -/

/-- The face maps satisfy the first simplicial identity. -/
theorem facePower_facePower (G : Comonad (CommAlgCat.{u} R)) (n : ℕ)
    (i j : Fin (n + 1)) (H : i ≤ j) (X : CommAlgCat.{u} R) :
    facePower G (n + 1) j.succ X ≫ facePower G n i X =
      facePower G (n + 1) i.castSucc X ≫ facePower G n j X := by
  induction n with
  | zero =>
      fin_cases i
      fin_cases j
      change G.map (G.ε.app X) ≫ G.ε.app X = G.ε.app (G.obj X) ≫ G.ε.app X
      exact G.counit_naturality (f := G.ε.app X)
  | succ n ih =>
      revert H
      refine Fin.cases ?_ (fun i => ?_) i
      · intro H
        change G.map (facePower G (n + 1) j X) ≫
            G.ε.app ((power G (n + 1)).obj X) =
          G.ε.app ((power G (n + 2)).obj X) ≫ facePower G (n + 1) j X
        exact G.counit_naturality (f := facePower G (n + 1) j X)
      · intro H
        revert H
        refine Fin.cases ?_ (fun j => ?_) j
        · intro H
          change i.succ ≤ (0 : Fin (n + 2)) at H
          exact (not_lt_of_ge H (Fin.succ_pos i)).elim
        · intro H
          change i.succ ≤ j.succ at H
          change G.map (facePower G (n + 1) j.succ X) ≫
              G.map (facePower G n i X) =
            G.map (facePower G (n + 1) i.castSucc X) ≫
              G.map (facePower G n j X)
          have hij : i ≤ j := Fin.succ_le_succ_iff.mp H
          rw [← Functor.map_comp, ih i j hij, Functor.map_comp]

/-- The two counit cancellations with a degeneracy. -/
theorem degeneracyPower_facePower_castSucc (G : Comonad (CommAlgCat.{u} R))
    (n : ℕ) (i : Fin (n + 1)) (X : CommAlgCat.{u} R) :
    degeneracyPower G n i X ≫ facePower G (n + 1) i.castSucc X = 𝟙 _ := by
  induction n with
  | zero =>
      fin_cases i
      change G.δ.app X ≫ G.ε.app (G.obj X) = 𝟙 _
      exact G.left_counit X
  | succ n ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · change G.δ.app ((power G (n + 1)).obj X) ≫
          G.ε.app (G.obj ((power G (n + 1)).obj X)) = 𝟙 _
        exact G.left_counit _
      · change G.map (degeneracyPower G n i X) ≫
          G.map (facePower G (n + 1) i.castSucc X) = 𝟙 _
        rw [← Functor.map_comp, ih]
        simp

theorem degeneracyPower_facePower_succ (G : Comonad (CommAlgCat.{u} R))
    (n : ℕ) (i : Fin (n + 1)) (X : CommAlgCat.{u} R) :
    degeneracyPower G n i X ≫ facePower G (n + 1) i.succ X = 𝟙 _ := by
  induction n with
  | zero =>
      fin_cases i
      change G.δ.app X ≫ G.map (G.ε.app X) = 𝟙 _
      exact G.right_counit X
  | succ n ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · change G.δ.app ((power G (n + 1)).obj X) ≫
          G.map (G.ε.app ((power G (n + 1)).obj X)) = 𝟙 _
        exact G.right_counit _
      · change G.map (degeneracyPower G n i X) ≫
          G.map (facePower G (n + 1) i.succ X) = 𝟙 _
        rw [← Functor.map_comp, ih]
        simp

/-! ### The iterated counit augmentation -/

/-- The iterated counit from an iterated comonad power to the original algebra. -/
def augmentationPower : (n : ℕ) → (X : CommAlgCat.{u} R) →
    (power G (n + 1)).obj X ⟶ X
  | 0, X => G.ε.app X
  | n + 1, X => facePower G (n + 1) 0 X ≫ augmentationPower n X

/-- The iterated counit is natural in the algebra. -/
theorem augmentationPower_naturality (G : Comonad (CommAlgCat.{u} R)) (n : ℕ)
    {X Y : CommAlgCat.{u} R} (f : X ⟶ Y) :
    (power G (n + 1)).map f ≫ augmentationPower G n Y =
      augmentationPower G n X ≫ f := by
  induction n with
  | zero =>
      change G.map f ≫ G.ε.app Y = G.ε.app X ≫ f
      exact G.counit_naturality (f := f)
  | succ n ih =>
      change (power G (n + 1 + 1)).map f ≫ facePower G (n + 1) 0 Y ≫
          augmentationPower G n Y =
        facePower G (n + 1) 0 X ≫ augmentationPower G n X ≫ f
      rw [← Category.assoc, facePower_naturality G (n + 1) 0 f,
        Category.assoc, ih]

/-- Every face is compatible with the iterated counit augmentation. -/
theorem facePower_augmentationPower (G : Comonad (CommAlgCat.{u} R)) (n : ℕ)
    (i : Fin (n + 2)) (X : CommAlgCat.{u} R) :
    facePower G (n + 1) i X ≫ augmentationPower G n X =
      augmentationPower G (n + 1) X := by
  induction n with
  | zero =>
      fin_cases i
      · change G.ε.app (G.obj X) ≫ G.ε.app X =
          G.ε.app (G.obj X) ≫ G.ε.app X
        rfl
      · change G.map (G.ε.app X) ≫ G.ε.app X =
          G.ε.app (G.obj X) ≫ G.ε.app X
        exact G.counit_naturality (f := G.ε.app X)
  | succ n ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · simp only [facePower_succ_succ, augmentationPower]
        change facePower G (n + 2) i.succ X ≫ facePower G (n + 1) 0 X ≫
            augmentationPower G n X =
          facePower G (n + 2) 0 X ≫ facePower G (n + 1) 0 X ≫
            augmentationPower G n X
        rw [← Category.assoc,
          facePower_facePower G (n + 1) 0 i (by simp), Category.assoc, ih]
        simp [augmentationPower]

end ElementaryMaps

end
end SimplicialResolution
end GromovWitten.AlgebraicGeometry.CotangentComplex
