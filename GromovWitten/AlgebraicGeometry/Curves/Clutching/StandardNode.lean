/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.Clutching.Topology
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNodeNodal

/-!
# The standard node as a pinched pair of affine lines

For any commutative base ring, the standard node `R[x,y]/(xy)` is the affine pinching of two
affine lines along their origins. The ring equivalence below is explicit and records the branch
coordinates, the scheme isomorphism over the base, and the resulting nodal family.
-/

open _root_.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits

namespace GromovWitten
namespace AlgebraicGeometry
namespace Curves
namespace Clutching

universe u

noncomputable section

open StableReduction LocalNode
open scoped Polynomial

variable (R : Type u) [CommRing R]

local notation "N" => LocalNode.Ring R 0 1
local notation "ε" => LocalNode.affineLineOrigin R
local notation "P" => fiberProduct ε ε

/-- The polynomial evaluations at the two node coordinates. -/
def nodeEvalX : R[X] →ₐ[R] N := Polynomial.aeval (LocalNode.x R 0 1)

def nodeEvalY : R[X] →ₐ[R] N := Polynomial.aeval (LocalNode.y R 0 1)

private def branchConst : R[X] →ₐ[R] R[X] :=
  Polynomial.CAlgHom.comp (LocalNode.affineLineOrigin R)

@[simp] private theorem branchConst_apply (p : R[X]) :
    branchConst R p = Polynomial.C (LocalNode.affineLineOrigin R p) := rfl

@[simp] theorem nodeEvalX_X : nodeEvalX R Polynomial.X = LocalNode.x R 0 1 := by
  simp [nodeEvalX]

@[simp] theorem nodeEvalY_X : nodeEvalY R Polynomial.X = LocalNode.y R 0 1 := by
  simp [nodeEvalY]

@[simp] theorem nodeEvalX_C (r : R) : nodeEvalX R (Polynomial.C r) = algebraMap R N r := by
  simp [nodeEvalX]

@[simp] theorem nodeEvalY_C (r : R) : nodeEvalY R (Polynomial.C r) = algebraMap R N r := by
  simp [nodeEvalY]

private theorem nodeEval_cross (p q : R[X]) :
    nodeEvalX R p * nodeEvalY R q =
      algebraMap R N (p.coeff 0) * nodeEvalY R q +
        nodeEvalX R p * algebraMap R N (q.coeff 0) -
          algebraMap R N (p.coeff 0 * q.coeff 0) := by
  have hp : LocalNode.x R 0 1 * nodeEvalX R p.divX +
      algebraMap R N (p.coeff 0) = nodeEvalX R p := by
    have h := congrArg (nodeEvalX R) (Polynomial.X_mul_divX_add p)
    rw [map_add, map_mul] at h
    simpa only [nodeEvalX_X, nodeEvalX_C] using h
  have hq : LocalNode.y R 0 1 * nodeEvalY R q.divX +
      algebraMap R N (q.coeff 0) = nodeEvalY R q := by
    have h := congrArg (nodeEvalY R) (Polynomial.X_mul_divX_add q)
    rw [map_add, map_mul] at h
    simpa only [nodeEvalY_X, nodeEvalY_C] using h
  have hxy : (LocalNode.x R 0 1) * (LocalNode.y R 0 1) = 0 := by
    rw [LocalNode.x_mul_y]
    simp
  rw [show nodeEvalX R p =
      LocalNode.x R 0 1 * nodeEvalX R p.divX + algebraMap R N (p.coeff 0) by
        exact hp.symm]
  rw [show nodeEvalY R q =
      LocalNode.y R 0 1 * nodeEvalY R q.divX + algebraMap R N (q.coeff 0) by
        exact hq.symm]
  have hfirst :
      (LocalNode.x R 0 1 * nodeEvalX R p.divX) *
          (LocalNode.y R 0 1 * nodeEvalY R q.divX) = 0 := by
    calc
      _ = (LocalNode.x R 0 1 * LocalNode.y R 0 1) *
          (nodeEvalX R p.divX * nodeEvalY R q.divX) := by ring
      _ = 0 := by rw [hxy, zero_mul]
  rw [mul_add, add_mul, mul_add, add_mul, hfirst]
  rw [map_mul]
  ring

/-- The map from the pinched affine lines to the standard node.

On a pair `(p,q)` with equal constant terms this is `p(x)+q(y)-p(0)`. -/
def pinchedToNode : P →ₐ[R] N where
  toFun p := nodeEvalX R p.1.1 + nodeEvalY R p.1.2 - algebraMap R N (ε p.1.1)
  map_one' := by
    simp [LocalNode.affineLineOrigin, nodeEvalX, nodeEvalY]
  map_zero' := by
    simp [LocalNode.affineLineOrigin, nodeEvalX, nodeEvalY]
  map_add' p q := by
    simp only [Subalgebra.coe_add, Prod.fst_add, Prod.snd_add, map_add, sub_add_sub_comm]
    ring
  map_mul' p q := by
    let p₁ : R[X] := p.1.1
    let p₂ : R[X] := p.1.2
    let q₁ : R[X] := q.1.1
    let q₂ : R[X] := q.1.2
    have hp : ε p₁ = ε p₂ := p.2
    have hq : ε q₁ = ε q₂ := q.2
    have hp' : p₁.coeff 0 = p₂.coeff 0 := by
      rw [show LocalNode.affineLineOrigin R p₁ = Polynomial.eval 0 p₁ by
        rfl, show LocalNode.affineLineOrigin R p₂ = Polynomial.eval 0 p₂ by rfl] at hp
      exact (Polynomial.coeff_zero_eq_eval_zero p₁).trans
        (hp.trans (Polynomial.coeff_zero_eq_eval_zero p₂).symm)
    have hq' : q₁.coeff 0 = q₂.coeff 0 := by
      rw [show LocalNode.affineLineOrigin R q₁ = Polynomial.eval 0 q₁ by
        rfl, show LocalNode.affineLineOrigin R q₂ = Polynomial.eval 0 q₂ by rfl] at hq
      exact (Polynomial.coeff_zero_eq_eval_zero q₁).trans
        (hq.trans (Polynomial.coeff_zero_eq_eval_zero q₂).symm)
    change nodeEvalX R (p₁ * q₁) + nodeEvalY R (p₂ * q₂) -
      algebraMap R N (LocalNode.affineLineOrigin R (p₁ * q₁)) =
        (nodeEvalX R p₁ + nodeEvalY R p₂ -
          algebraMap R N (LocalNode.affineLineOrigin R p₁)) *
        (nodeEvalX R q₁ + nodeEvalY R q₂ -
          algebraMap R N (LocalNode.affineLineOrigin R q₁))
    have heval₁ : LocalNode.affineLineOrigin R (p₁ * q₁) =
        p₁.coeff 0 * q₁.coeff 0 := by
      rw [show LocalNode.affineLineOrigin R (p₁ * q₁) =
          Polynomial.eval 0 (p₁ * q₁) by rfl, Polynomial.eval_mul]
      rw [← Polynomial.coeff_zero_eq_eval_zero p₁,
        ← Polynomial.coeff_zero_eq_eval_zero q₁]
    have heval₂ : LocalNode.affineLineOrigin R p₁ = p₁.coeff 0 := by
      rw [LocalNode.affineLineOrigin]
      exact Polynomial.coeff_zero_eq_eval_zero p₁ |>.symm
    have heval₃ : LocalNode.affineLineOrigin R q₁ = q₁.coeff 0 := by
      rw [LocalNode.affineLineOrigin]
      exact Polynomial.coeff_zero_eq_eval_zero q₁ |>.symm
    rw [map_mul, map_mul, heval₁, heval₂, heval₃]
    have hcross₁₂ := nodeEval_cross R p₁ q₂
    have hcross₂₁ := nodeEval_cross R q₁ p₂
    have hexpand :
        (nodeEvalX R p₁ + nodeEvalY R p₂ - algebraMap R N (p₁.coeff 0)) *
            (nodeEvalX R q₁ + nodeEvalY R q₂ - algebraMap R N (q₁.coeff 0)) =
          nodeEvalX R p₁ * nodeEvalX R q₁ +
            nodeEvalX R p₁ * nodeEvalY R q₂ +
            nodeEvalY R p₂ * nodeEvalX R q₁ +
            nodeEvalY R p₂ * nodeEvalY R q₂ -
            algebraMap R N (p₁.coeff 0) * nodeEvalX R q₁ -
            algebraMap R N (p₁.coeff 0) * nodeEvalY R q₂ -
            nodeEvalX R p₁ * algebraMap R N (q₁.coeff 0) -
            nodeEvalY R p₂ * algebraMap R N (q₁.coeff 0) +
            algebraMap R N (p₁.coeff 0) * algebraMap R N (q₁.coeff 0) := by ring
    rw [hexpand]
    rw [hcross₁₂]
    have hcross₂₁' : nodeEvalY R p₂ * nodeEvalX R q₁ =
        algebraMap R N (p₂.coeff 0) * nodeEvalX R q₁ +
          nodeEvalY R p₂ * algebraMap R N (q₁.coeff 0) -
            algebraMap R N (p₂.coeff 0 * q₁.coeff 0) := by
      rw [mul_comm (nodeEvalY R p₂) (nodeEvalX R q₁), hcross₂₁]
      ring_nf
    rw [hcross₂₁']
    rw [hp', hq']
    simp only [map_mul]
    ring
  commutes' r := by
    change nodeEvalX R (Polynomial.C r) + nodeEvalY R (Polynomial.C r) -
      algebraMap R N (LocalNode.affineLineOrigin R (Polynomial.C r)) =
      algebraMap R N r
    simp [LocalNode.affineLineOrigin, nodeEvalX, nodeEvalY]

@[simp] theorem pinchedToNode_apply (p : P) :
    pinchedToNode R p = nodeEvalX R p.1.1 + nodeEvalY R p.1.2 -
      algebraMap R N (LocalNode.affineLineOrigin R p.1.1) := rfl

theorem pinchedToNode_apply_pair (p q : R[X]) (h :
    LocalNode.affineLineOrigin R p = LocalNode.affineLineOrigin R q) :
    pinchedToNode R ⟨(p, q), h⟩ =
      nodeEvalX R p + nodeEvalY R q -
        algebraMap R N (LocalNode.affineLineOrigin R p) := rfl

@[simp] theorem pinchedToNode_fst_X :
    pinchedToNode R ⟨(Polynomial.X, 0), by simp [LocalNode.affineLineOrigin]⟩ =
      LocalNode.x R 0 1 := by
  simp [pinchedToNode]

@[simp] theorem pinchedToNode_snd_X :
    pinchedToNode R ⟨(0, Polynomial.X), by simp [LocalNode.affineLineOrigin]⟩ =
      LocalNode.y R 0 1 := by
  simp [pinchedToNode]

private theorem nodeToPinched_agreement :
    (LocalNode.affineLineOrigin R).comp (LocalNode.xBranch R 1 one_ne_zero) =
      (LocalNode.affineLineOrigin R).comp (LocalNode.yBranch R 1 one_ne_zero) := by
  exact (LocalNode.xBranch_comp_affineLineOrigin R 1 one_ne_zero).trans
    (LocalNode.yBranch_comp_affineLineOrigin R 1 one_ne_zero).symm

/-- The map from the standard node to the affine fibre product of its two branches. -/
def nodeToPinched : N →ₐ[R] P :=
  fiberProduct.lift (LocalNode.affineLineOrigin R) (LocalNode.affineLineOrigin R)
    (LocalNode.xBranch R 1 one_ne_zero)
    (LocalNode.yBranch R 1 one_ne_zero) (nodeToPinched_agreement R)

@[simp] theorem nodeToPinched_x :
    nodeToPinched R (LocalNode.x R 0 1) =
      ⟨(Polynomial.X, 0), by simp [LocalNode.affineLineOrigin]⟩ := by
  apply Subtype.ext
  change (LocalNode.xBranch R 1 one_ne_zero (LocalNode.x R 0 1),
      LocalNode.yBranch R 1 one_ne_zero (LocalNode.x R 0 1)) =
    (Polynomial.X, 0)
  simp

@[simp] theorem nodeToPinched_y :
    nodeToPinched R (LocalNode.y R 0 1) =
      ⟨(0, Polynomial.X), by simp [LocalNode.affineLineOrigin]⟩ := by
  apply Subtype.ext
  change (LocalNode.xBranch R 1 one_ne_zero (LocalNode.y R 0 1),
      LocalNode.yBranch R 1 one_ne_zero (LocalNode.y R 0 1)) =
    (0, Polynomial.X)
  simp

/-- The pinching ring is the standard node ring. -/
def standardNodeRingEquiv : N ≃ₐ[R] P := by
  refine AlgEquiv.ofAlgHom (nodeToPinched R) (pinchedToNode R) ?_ ?_
  · apply AlgHom.ext
    intro p
    apply Subtype.ext
    apply Prod.ext
    · change LocalNode.xBranch R 1 one_ne_zero (pinchedToNode R p) = p.1.1
      have hx : (LocalNode.xBranch R 1 one_ne_zero).comp (nodeEvalX R) =
          AlgHom.id R R[X] := by
        apply Polynomial.algHom_ext
        simp [nodeEvalX]
      have hy : (LocalNode.xBranch R 1 one_ne_zero).comp (nodeEvalY R) =
          branchConst R := by
        apply Polynomial.algHom_ext
        simp [nodeEvalY, LocalNode.affineLineOrigin]
      rw [pinchedToNode_apply]
      simp only [map_add, map_sub]
      have hx'' : LocalNode.xBranch R 1 one_ne_zero (nodeEvalX R p.1.1) = p.1.1 := by
        change ((LocalNode.xBranch R 1 one_ne_zero).comp (nodeEvalX R)) p.1.1 = _
        rw [hx]
        rfl
      have hy'' : LocalNode.xBranch R 1 one_ne_zero (nodeEvalY R p.1.2) =
          Polynomial.C (LocalNode.affineLineOrigin R p.1.2) := by
        change ((LocalNode.xBranch R 1 one_ne_zero).comp (nodeEvalY R)) p.1.2 = _
        rw [hy]
        rfl
      rw [hx'', hy'']
      have hp := p.2
      change LocalNode.affineLineOrigin R p.1.1 =
        LocalNode.affineLineOrigin R p.1.2 at hp
      rw [hp]
      simp [LocalNode.affineLineOrigin]
    · change LocalNode.yBranch R 1 one_ne_zero (pinchedToNode R p) = p.1.2
      have hx : (LocalNode.yBranch R 1 one_ne_zero).comp (nodeEvalX R) =
          branchConst R := by
        apply Polynomial.algHom_ext
        simp [nodeEvalX, LocalNode.affineLineOrigin]
      have hy : (LocalNode.yBranch R 1 one_ne_zero).comp (nodeEvalY R) =
          AlgHom.id R R[X] := by
        apply Polynomial.algHom_ext
        simp [nodeEvalY]
      rw [pinchedToNode_apply]
      simp only [map_add, map_sub]
      have hx'' : LocalNode.yBranch R 1 one_ne_zero (nodeEvalX R p.1.1) =
          Polynomial.C (LocalNode.affineLineOrigin R p.1.1) := by
        change ((LocalNode.yBranch R 1 one_ne_zero).comp (nodeEvalX R)) p.1.1 = _
        rw [hx]
        rfl
      have hy'' : LocalNode.yBranch R 1 one_ne_zero (nodeEvalY R p.1.2) = p.1.2 := by
        change ((LocalNode.yBranch R 1 one_ne_zero).comp (nodeEvalY R)) p.1.2 = _
        rw [hy]
        rfl
      rw [hx'', hy'']
      have hp := p.2
      change LocalNode.affineLineOrigin R p.1.1 =
        LocalNode.affineLineOrigin R p.1.2 at hp
      rw [hp]
      simp [LocalNode.affineLineOrigin]
  · apply LocalNode.algHom_ext (R := R) 0 1
    · rw [AlgHom.comp_apply, nodeToPinched_x]
      simp [pinchedToNode]
    · rw [AlgHom.comp_apply, nodeToPinched_y]
      simp [pinchedToNode]

@[simp] theorem standardNodeRingEquiv_apply_x :
    standardNodeRingEquiv R (LocalNode.x R 0 1) =
      ⟨(Polynomial.X, 0), by simp [LocalNode.affineLineOrigin]⟩ := by
  change nodeToPinched R (LocalNode.x R 0 1) = _
  exact nodeToPinched_x R

@[simp] theorem standardNodeRingEquiv_apply_y :
    standardNodeRingEquiv R (LocalNode.y R 0 1) =
      ⟨(0, Polynomial.X), by simp [LocalNode.affineLineOrigin]⟩ := by
  change nodeToPinched R (LocalNode.y R 0 1) = _
  exact nodeToPinched_y R

@[simp] theorem standardNodeRingEquiv_symm_apply (p : P) :
    (standardNodeRingEquiv R).symm p =
      nodeEvalX R p.1.1 + nodeEvalY R p.1.2 -
        algebraMap R N (LocalNode.affineLineOrigin R p.1.1) := by
  change pinchedToNode R p = _
  rfl

theorem standardNodeRingEquiv_fst :
    (fiberProduct.fst (LocalNode.affineLineOrigin R)
      (LocalNode.affineLineOrigin R)).comp (standardNodeRingEquiv R).toAlgHom =
      LocalNode.xBranch R 1 one_ne_zero := by
  apply LocalNode.algHom_ext (R := R) 0 1
  · change fiberProduct.fst (LocalNode.affineLineOrigin R)
      (LocalNode.affineLineOrigin R) (standardNodeRingEquiv R (LocalNode.x R 0 1)) = _
    simp
  · change fiberProduct.fst (LocalNode.affineLineOrigin R)
      (LocalNode.affineLineOrigin R) (standardNodeRingEquiv R (LocalNode.y R 0 1)) = _
    simp

theorem standardNodeRingEquiv_snd :
    (fiberProduct.snd (LocalNode.affineLineOrigin R)
      (LocalNode.affineLineOrigin R)).comp (standardNodeRingEquiv R).toAlgHom =
      LocalNode.yBranch R 1 one_ne_zero := by
  apply LocalNode.algHom_ext (R := R) 0 1
  · change fiberProduct.snd (LocalNode.affineLineOrigin R)
      (LocalNode.affineLineOrigin R) (standardNodeRingEquiv R (LocalNode.x R 0 1)) = _
    simp
  · change fiberProduct.snd (LocalNode.affineLineOrigin R)
      (LocalNode.affineLineOrigin R) (standardNodeRingEquiv R (LocalNode.y R 0 1)) = _
    simp

theorem standardNodeRingEquiv_augmentation :
    (fiberProduct.augmentation (LocalNode.affineLineOrigin R)
      (LocalNode.affineLineOrigin R)).comp (standardNodeRingEquiv R).toAlgHom =
      LocalNode.nodeOrigin R 1 one_ne_zero := by
  rw [fiberProduct.augmentation, AlgHom.comp_assoc, standardNodeRingEquiv_fst]
  exact LocalNode.xBranch_comp_affineLineOrigin R 1 one_ne_zero

/-- The affine scheme isomorphism induced by the pinching equivalence. -/
noncomputable def standardNodePinchedIso :
    Spec (.of P) ≅ Spec (.of N) :=
  Scheme.Spec.mapIso (standardNodeRingEquiv R).toRingEquiv.toCommRingCatIso.op

/-- The structural morphism of the affine pinched node. -/
def pinchedToBaseSpec : Spec (.of P) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R P))

/-- Over a domain, the two affine lines are connected and their pinching is connected. -/
theorem pinchedSpectrum_connected [IsDomain R] : ConnectedSpace (Spec (.of P)) :=
  fiberProduct.connectedSpace_spec (LocalNode.affineLineOrigin R) (LocalNode.affineLineOrigin R)

instance pinchedRing_flat : Module.Flat R P := by
  apply fiberProduct.flat

instance pinchedToBaseSpec_flat : Flat (pinchedToBaseSpec R) := by
  rw [pinchedToBaseSpec, Flat.SpecMap_iff]
  change (algebraMap R P).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

@[reassoc (attr := simp)] theorem standardNodePinchedIso_overBase :
    (standardNodePinchedIso R).hom ≫ LocalNode.toBaseSpec R 0 1 =
      pinchedToBaseSpec R := by
  dsimp only [standardNodePinchedIso]
  simp only [Functor.mapIso_hom, Scheme.Spec_map]
  rw [LocalNode.toBaseSpec, pinchedToBaseSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change (standardNodeRingEquiv R).toRingEquiv (algebraMap R N r) =
    algebraMap R P r
  exact (standardNodeRingEquiv R).commutes r

/-- The pinched affine node is an at-worst-nodal family over the base. -/
theorem pinchedToBaseSpec_atWorstNodal :
    GromovWitten.AlgebraicGeometry.Curves.AtWorstNodal (pinchedToBaseSpec R) := by
  let hlocal := LocalNode.toBaseSpec_atWorstNodal R 0 1
  refine
    { flat := by
        rw [← standardNodePinchedIso_overBase R]
        infer_instance
      locallyOfFinitePresentation := by
        rw [← standardNodePinchedIso_overBase R]
        infer_instance
      geometricPureRelativeDimension := by
        rw [← standardNodePinchedIso_overBase R]
        exact GeometricPureRelativeDimension.precomp_iso
          (standardNodePinchedIso R) (LocalNode.toBaseSpec R 0 1)
          hlocal.geometricPureRelativeDimension
      geometricFibers := ?_ }
  intro K _ y Z fst snd hsquare
  have hlocalSquare : IsPullback
      (fst ≫ (standardNodePinchedIso R).hom) snd
      (LocalNode.toBaseSpec R 0 1) y :=
    hsquare.of_iso (Iso.refl Z) (standardNodePinchedIso R)
      (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by
        exact (standardNodePinchedIso_overBase R).symm) (by simp)
  exact hlocal.geometricFibers K y Z
    (fst ≫ (standardNodePinchedIso R).hom) snd hlocalSquare

instance pinchedToBaseSpec_instAtWorstNodal :
    GromovWitten.AlgebraicGeometry.Curves.AtWorstNodal (pinchedToBaseSpec R) :=
  pinchedToBaseSpec_atWorstNodal R

end
end Clutching
end Curves
end AlgebraicGeometry
end GromovWitten
