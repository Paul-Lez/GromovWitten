/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.Clutching.AffineScheme
import Mathlib.Topology.Constructions.SumProd

/-!
# Topological gluing for affine pinching

The disjoint union of the two closed branches maps onto the pinched spectrum by a quotient
map. Compatible continuous maps on the branches therefore descend uniquely. This is the
topological universal property; it does not assert gluing of structure sheaves or a scheme
pushout.
-/

open _root_.AlgebraicGeometry CategoryTheory Topology

namespace GromovWitten.AlgebraicGeometry.Curves.Clutching.fiberProduct

universe u v

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (εA : A →ₐ[R] R) (εB : B →ₐ[R] R)

/-- The map from the disjoint union of the closed branches onto the pinched spectrum. -/
noncomputable def branchCover :
    (Spec (.of A) ⊕ Spec (.of B)) → Spec (.of (fiberProduct εA εB)) :=
  Sum.elim (specFst εA εB).base (specSnd εA εB).base

theorem branchCover_surjective : Function.Surjective (branchCover εA εB) := by
  intro p
  have hp : p ∈ Set.range (specFst εA εB).base ∪ Set.range (specSnd εA εB).base := by
    rw [scheme_branch_ranges_cover]
    trivial
  rcases hp with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact ⟨Sum.inl a, rfl⟩
  · exact ⟨Sum.inr b, rfl⟩

/-- The topology of the pinched spectrum is the quotient topology from its two branches. -/
theorem branchCover_isQuotientMap : IsQuotientMap (branchCover εA εB) :=
  ((specFst εA εB).isClosedEmbedding.isClosedMap.sumElim
    (specSnd εA εB).isClosedEmbedding.isClosedMap).isQuotientMap
      ((specFst εA εB).continuous.sumElim (specSnd εA εB).continuous)
      (branchCover_surjective εA εB)

/-- Connected branches meeting along a nonempty base have connected pinching. -/
theorem connectedSpace_spec [Nontrivial R]
    [ConnectedSpace (Spec (.of A))] [ConnectedSpace (Spec (.of B))] :
    ConnectedSpace (Spec (.of (fiberProduct εA εB))) := by
  classical
  let r : Spec (.of R) := Classical.choice inferInstance
  have hmeet : (Set.range (specFst εA εB).base ∩
      Set.range (specSnd εA εB).base).Nonempty := by
    refine ⟨(specAugmentation εA εB).base r, ?_, ?_⟩
    · exact ⟨(sectionA εA).base r,
        congrArg (fun h => h.base r) (sectionA_specFst εA εB)⟩
    · exact ⟨(sectionB εB).base r,
        congrArg (fun h => h.base r) (sectionB_specSnd εA εB)⟩
  apply connectedSpace_iff_univ.mpr
  rw [← scheme_branch_ranges_cover εA εB]
  exact IsConnected.union hmeet
    (isConnected_range (specFst εA εB).continuous)
    (isConnected_range (specSnd εA εB).continuous)

private theorem compatible_values {Y : Type v}
    (f : Spec (.of A) → Y) (g : Spec (.of B) → Y)
    (hfg : ∀ r : Spec (.of R), f ((sectionA εA).base r) = g ((sectionB εB).base r))
    {a : Spec (.of A)} {b : Spec (.of B)}
    (hab : (specFst εA εB).base a = (specSnd εA εB).base b) : f a = g b := by
  have hp : (specFst εA εB).base a ∈ Set.range (specAugmentation εA εB).base := by
    change (PrimeSpectrum.comap (fst εA εB).toRingHom a) ∈
      Set.range (PrimeSpectrum.comap (augmentation εA εB).toRingHom)
    rw [← branch_ranges_intersect_eq_common_section]
    exact ⟨⟨a, rfl⟩, ⟨b, hab.symm⟩⟩
  obtain ⟨r, hr⟩ := hp
  have hA : (specFst εA εB).base ((sectionA εA).base r) =
      (specAugmentation εA εB).base r :=
    congrArg (fun h => h.base r) (sectionA_specFst εA εB)
  have hB : (specSnd εA εB).base ((sectionB εB).base r) =
      (specAugmentation εA εB).base r :=
    congrArg (fun h => h.base r) (sectionB_specSnd εA εB)
  have hra : (sectionA εA).base r = a :=
    (specFst εA εB).isClosedEmbedding.injective (hA.trans hr)
  have hrb : (sectionB εB).base r = b :=
    (specSnd εA εB).isClosedEmbedding.injective (hB.trans (hr.trans hab))
  simpa only [hra, hrb] using hfg r

/-- Compatible continuous maps on the branches extend uniquely to the pinched spectrum. -/
theorem existsUnique_continuous_gluing {Y : Type v} [TopologicalSpace Y]
    (f : Spec (.of A) → Y) (g : Spec (.of B) → Y)
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ r : Spec (.of R), f ((sectionA εA).base r) = g ((sectionB εB).base r)) :
    ∃! h : Spec (.of (fiberProduct εA εB)) → Y,
      Continuous h ∧ h ∘ (specFst εA εB).base = f ∧
        h ∘ (specSnd εA εB).base = g := by
  classical
  let q := branchCover εA εB
  let k := Sum.elim f g
  have hq : Function.Surjective q := branchCover_surjective εA εB
  have hk : Function.FactorsThrough k q := by
    intro x y hxy
    cases x with
    | inl a =>
      cases y with
      | inl a' => exact congrArg f ((specFst εA εB).isClosedEmbedding.injective hxy)
      | inr b => exact compatible_values εA εB f g hfg hxy
    | inr b =>
      cases y with
      | inl a => exact (compatible_values εA εB f g hfg hxy.symm).symm
      | inr b' => exact congrArg g ((specSnd εA εB).isClosedEmbedding.injective hxy)
  let h := fun p => k (Classical.choose (hq p))
  have hh : ∀ x, h (q x) = k x := by
    intro x
    exact hk (Classical.choose_spec (hq (q x)))
  have hcomp : h ∘ q = k := funext hh
  have hcont : Continuous h := (branchCover_isQuotientMap εA εB).continuous_iff.mpr (by
    change Continuous (h ∘ q)
    rw [hcomp]
    exact hf.sumElim hg)
  refine ⟨h, ⟨hcont, funext (fun a => hh (.inl a)),
    funext (fun b => hh (.inr b))⟩, ?_⟩
  intro h' hh'
  funext p
  obtain ⟨x, rfl⟩ := hq p
  rw [hh]
  cases x with
  | inl a => exact congrFun hh'.2.1 a
  | inr b => exact congrFun hh'.2.2 b

end GromovWitten.AlgebraicGeometry.Curves.Clutching.fiberProduct
