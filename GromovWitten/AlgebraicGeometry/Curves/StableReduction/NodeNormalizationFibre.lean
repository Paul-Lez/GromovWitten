/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.NodeNormalization
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
import GromovWitten.AlgebraicGeometry.Curves.TotalNormalization
/-!
# The two points over a standard node

The explicit normalization by two affine axes identifies the fibre above the node origin
with `Fin 2`. The same fibre description is preserved by base change with unchanged residue
field at the chosen point.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

noncomputable section
variable (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0)

def branchPairMap :
    (Spec (.of R[X]) ⊕ Spec (.of R[X])) → Spec (.of (Ring R 0 n)) :=
  Sum.elim (xBranchSpec R n hn) (yBranchSpec R n hn)

theorem xBranch_originPoint (r : Spec (.of R)) :
    xBranchSpec R n hn (affineLineOriginSpec R r) = nodeOriginSpec R n hn r := by
  change (affineLineOriginSpec R ≫ xBranchSpec R n hn) r = _
  rw [affineLineOriginSpec_xBranchSpec]

theorem yBranch_originPoint (r : Spec (.of R)) :
    yBranchSpec R n hn (affineLineOriginSpec R r) = nodeOriginSpec R n hn r := by
  change (affineLineOriginSpec R ≫ yBranchSpec R n hn) r = _
  rw [affineLineOriginSpec_yBranchSpec]

def branchPairFibreEquiv (r : Spec (.of R)) :
    {p // branchPairMap R n hn p = nodeOriginSpec R n hn r} ≃ Fin 2 where
  toFun p := Sum.elim (fun _ => 0) (fun _ => 1) p.1
  invFun j := if j = 0 then
      ⟨Sum.inl (affineLineOriginSpec R r), xBranch_originPoint R n hn r⟩
    else ⟨Sum.inr (affineLineOriginSpec R r), yBranch_originPoint R n hn r⟩
  left_inv p := by
    rcases p with ⟨p, hp⟩
    cases p with
    | inl p =>
      apply Subtype.ext
      change Sum.inl (affineLineOriginSpec R r) = Sum.inl p
      congr 1
      apply (xBranchSpec R n hn).isClosedEmbedding.injective
      exact (xBranch_originPoint R n hn r).trans hp.symm
    | inr p =>
      apply Subtype.ext
      change Sum.inr (affineLineOriginSpec R r) = Sum.inr p
      congr 1
      apply (yBranchSpec R n hn).isClosedEmbedding.injective
      exact (yBranch_originPoint R n hn r).trans hp.symm
  right_inv j := by
    fin_cases j <;> rfl

end
end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

open CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme
variable {X Y Z : Scheme.{u}}

noncomputable def coprodFibreEquiv (f : X ⟶ Z) (g : Y ⟶ Z) (z : Z) :
    {p : (X ⨿ Y : Scheme.{u}) // coprod.desc f g p = z} ≃
      {p : X ⊕ Y // Sum.elim f g p = z} where
  toFun p := ⟨(coprodMk X Y).symm p, by
    have h (q : X ⊕ Y) : coprod.desc f g (coprodMk X Y q) = Sum.elim f g q := by
      cases q <;> simp only [coprodMk_inl, coprodMk_inr, ← Scheme.Hom.comp_apply,
        coprod.inl_desc, coprod.inr_desc, Sum.elim_inl, Sum.elim_inr]
    rw [← h, Homeomorph.apply_symm_apply]
    exact p.2⟩
  invFun p := ⟨coprodMk X Y p, by
    rcases p with ⟨p, hp⟩
    cases p <;> simpa only [coprodMk_inl, coprodMk_inr, ← Scheme.Hom.comp_apply,
      coprod.inl_desc, coprod.inr_desc, Sum.elim_inl, Sum.elim_inr] using hp⟩
  left_inv p := Subtype.ext (Homeomorph.apply_symm_apply _ _)
  right_inv p := Subtype.ext (Homeomorph.symm_apply_apply _ _)

end AlgebraicGeometry.Scheme

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
noncomputable def schemeBranchPairFibreEquiv
    (R : Type u) [CommRing R] (n : ℕ) (hn : n ≠ 0) (r : Spec (.of R)) :
    {p : (Spec (.of (Polynomial R)) ⨿ Spec (.of (Polynomial R)) : Scheme.{u}) //
      coprod.desc (xBranchSpec R n hn) (yBranchSpec R n hn) p = nodeOriginSpec R n hn r} ≃
      Fin 2 :=
  (Scheme.coprodFibreEquiv (xBranchSpec R n hn) (yBranchSpec R n hn)
    (nodeOriginSpec R n hn r)).trans (branchPairFibreEquiv R n hn r)
end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

open CategoryTheory Limits AlgebraicGeometry



namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction
open LocalNode
noncomputable section
variable (K : Type u) [Field K]

def standardNodeNormalizationFibreEquiv (r : Spec (.of K)) :
    {p : (standardNodeBranchPairMap K).normalization //
      (standardNodeBranchPairMap K).fromNormalization p = nodeOriginSpec K 1 one_ne_zero r} ≃
      Fin 2 :=
  (Scheme.fibreEquivOfIso (standardNodeNormalizationIso K)
    (standardNodeAxesMap K) (standardNodeBranchPairMap K).fromNormalization
    (standardNodeNormalizationIso_hom_fromNormalization K) _).symm.trans
      (schemeBranchPairFibreEquiv K 1 one_ne_zero r)

def standardNodeNormalizationPullbackFibreEquiv
    {U : Scheme.{u}} (g : U ⟶ branchNode K) [Smooth g] (y : U)
    [IsIso (g.residueFieldMap y)]
    (r : Spec (.of K)) (hy : g y = nodeOriginSpec K 1 one_ne_zero r) :
    {p : (pullback.snd (standardNodeBranchPairMap K) g).normalization //
      (pullback.snd (standardNodeBranchPairMap K) g).fromNormalization p = y} ≃ Fin 2 := by
  let f := standardNodeBranchPairMap K
  let a := asIso (f.normalizationPullback g)
  let e₁ := Scheme.fibreEquivOfIso a (pullback.snd f g).fromNormalization
    (pullback.snd f.fromNormalization g) (f.normalizationPullback_snd g) y
  let e₂ := Scheme.Hom.fibrePullbackEquiv (IsPullback.of_hasPullback f.fromNormalization g) y
  have e₃ : {x : f.normalization // f.fromNormalization x = g y} ≃
      {x : f.normalization // f.fromNormalization x = nodeOriginSpec K 1 one_ne_zero r} :=
    Equiv.setCongr (by rw [hy])
  exact e₁.trans (e₂.trans (e₃.trans (standardNodeNormalizationFibreEquiv K r)))

end
end GromovWitten.AlgebraicGeometry.Curves.StableReduction
