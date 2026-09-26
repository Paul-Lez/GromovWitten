/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Cones.GlobalContraction

/-!
# A concrete global graded cone

The polynomial algebra of the structure sheaf gives a graded cone over every scheme.  This is a
genuine global example: the local coactions are the polynomial comultiplications and their
compatibility with restriction is proved coefficientwise, rather than supplied as an action law.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

open RelativeSpec GradedCone GlobalBlowup VectorBundleTotalSpace

universe u

noncomputable section

namespace ConeAlgebraData

variable (X : Scheme.{u})

set_option backward.isDefEq.respectTransparency false

/-- The affine-line coaction on the polynomial algebra of the structure sheaf. -/
def affineLine : ConeAlgebraData X where
  toAlgebraData := (structureData X).polynomial
  coaction U := comul (R := Γ(X, U.1)) (S := Γ(X, U.1))
  vertex U := evalHom (AlgHom.id Γ(X, U.1) Γ(X, U.1)) (0 : Γ(X, U.1))
  coaction_law U := isConeCoaction_comul Γ(X, U.1)
  vertex_law U := by
    change contraction (comul (R := Γ(X, U.1)) (S := Γ(X, U.1))) 0 =
      (Algebra.ofId Γ(X, U.1) (Polynomial Γ(X, U.1))).comp
        (evalHom (AlgHom.id Γ(X, U.1) Γ(X, U.1)) (0 : Γ(X, U.1)))
    apply Polynomial.algHom_ext'
    · apply AlgHom.ext
      intro a
      simp [contraction, scale, comul, evalHom]
    · simp [contraction, scale, comul, evalHom]
  coaction_natural {U V} h a := by
    change Polynomial.map (Polynomial.mapRingHom (res X h))
          (comul (R := Γ(X, V.1)) (S := Γ(X, V.1)) a) =
      comul (R := Γ(X, U.1)) (S := Γ(X, U.1))
        (Polynomial.map (res X h) a)
    induction a using Polynomial.induction_on' with
    | add p q hp hq =>
        simp only [Polynomial.map_add, map_add]
        exact congrArg₂ (· + ·) hp hq
    | monomial n b =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        change Polynomial.map (Polynomial.mapRingHom (res X h))
            (comul (R := Γ(X, V.1)) (S := Γ(X, V.1))
              (Polynomial.C b * Polynomial.X ^ n)) =
          comul (R := Γ(X, U.1)) (S := Γ(X, U.1))
            (Polynomial.map (res X h) (Polynomial.C b * Polynomial.X ^ n))
        simp [comul, evalHom]
  vertex_natural {U V} h := by
    change (evalHom (AlgHom.id Γ(X, U.1) Γ(X, U.1)) (0 : Γ(X, U.1))).toRingHom.comp
          (Polynomial.mapRingHom (res X h)) =
      (res X h).comp
        (evalHom (AlgHom.id Γ(X, V.1) Γ(X, V.1)) (0 : Γ(X, V.1))).toRingHom
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp

theorem affineLine_coaction (U : X.affineOpens) :
    (affineLine X).coaction U =
      comul (R := Γ(X, U.1)) (S := Γ(X, U.1)) := rfl

theorem affineLine_vertex (U : X.affineOpens) :
    (affineLine X).vertex U =
      evalHom (AlgHom.id Γ(X, U.1) Γ(X, U.1)) (0 : Γ(X, U.1)) := rfl

theorem affineLine_zero_factorization :
    contractionMap (affineLine X) (0 : Γ(X, ⊤)) =
      toBase X (affineLine X).toAlgebraData ≫ vertexMap (affineLine X) :=
  contractionMap_zero (affineLine X)

theorem affineLine_action_unit :
    actionUnitMap (affineLine X) ≫ actionMap (affineLine X) = 𝟙 _ :=
  actionUnitMap_comp_actionMap (affineLine X)

end ConeAlgebraData

end
end GromovWitten.AlgebraicGeometry
