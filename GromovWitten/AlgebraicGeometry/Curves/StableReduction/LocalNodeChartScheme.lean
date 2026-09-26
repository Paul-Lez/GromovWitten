/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNodeChartInvariance

/-!
# Scheme comparison for ramified local-node charts

The algebra equivalence obtained by rescaling a branch of a node induces an actual affine-scheme
isomorphism.  Composing it with the existing fibre-product comparison gives the base-changed
standard chart, together with its structure-map square over the coefficient scheme.  The ring
maps on the two node coordinates are recorded separately so the scheme construction does not
hide the coordinate normalization.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct Polynomial

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

universe u

noncomputable section

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-! ## The affine comparison after a ramified coefficient extension -/

/-- The contravariant `Spec` image of the powered-unit coordinate equivalence, composed with the
existing coefficient base-change comparison. -/
noncomputable def ramifiedNodeBaseChangeSpecIso
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    baseChangedNodeSpec R S π n ≅
      Spec (.of (Ring S ϖ (e * n))) := by
  dsimp [baseChangedNodeSpec]
  exact baseChangeSpecIso R S π n ≪≫
    (Scheme.Spec.mapIso
      (ramifiedNodeEquiv R S π ϖ e n v hπ).toRingEquiv.toCommRingCatIso.op).symm

private theorem ramifiedSpecIso_hom_toBaseSpec
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    ((Scheme.Spec.mapIso
      (ramifiedNodeEquiv R S π ϖ e n v hπ).toRingEquiv.toCommRingCatIso.op).symm).hom ≫
        toBaseSpec S ϖ (e * n) =
      toBaseSpec S (algebraMap R S π) n := by
  change Spec.map (CommRingCat.ofHom
      (ramifiedNodeEquiv R S π ϖ e n v hπ).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (Ring S ϖ (e * n)))) =
    Spec.map (CommRingCat.ofHom (algebraMap S (Ring S (algebraMap R S π) n)))
  rw [← Spec.map_comp, AlgebraicGeometry.Spec.map_inj]
  apply CommRingCat.hom_ext
  ext s
  exact (ramifiedNodeEquiv R S π ϖ e n v hπ).symm.commutes s

/-- The ramified normalized node comparison is an isomorphism over `Spec S`. -/
theorem ramifiedNodeBaseChangeSpecIso_hom_toBaseSpec
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    (ramifiedNodeBaseChangeSpecIso R S π ϖ e n v hπ).hom ≫
        toBaseSpec S ϖ (e * n) =
      baseChangedNodeToBaseSpec R S π n := by
  change (baseChangeSpecIso R S π n ≪≫
      (Scheme.Spec.mapIso
        (ramifiedNodeEquiv R S π ϖ e n v hπ).toRingEquiv.toCommRingCatIso.op).symm).hom ≫
      toBaseSpec S ϖ (e * n) =
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  rw [Iso.trans_hom, Category.assoc,
    ramifiedSpecIso_hom_toBaseSpec R S π ϖ e n v hπ]
  rw [baseChangeSpecIso_hom_toBaseSpec R S π n]

/-! ## Coordinate maps visible on the affine comparison -/

@[simp] theorem ramifiedNodeBaseChangeSpecIso_coordinate_x
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    (ramifiedNodeEquiv R S π ϖ e n v hπ).toRingHom
        (x S (algebraMap R S π) n) =
      algebraMap S (Ring S ϖ (e * n)) ((v : S) ^ n) * x S ϖ (e * n) := by
  exact ramifiedNodeMap_x R S π ϖ e n v hπ

@[simp] theorem ramifiedNodeBaseChangeSpecIso_coordinate_y
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    (ramifiedNodeEquiv R S π ϖ e n v hπ).toRingHom
        (y S (algebraMap R S π) n) = y S ϖ (e * n) := by
  exact ramifiedNodeMap_y R S π ϖ e n v hπ

/-! ## The square with the original node chart -/

theorem ramifiedNodeBaseChangeSpecIso_hom_comp_coefficientMap
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    (π : R) (ϖ : S) (e n : ℕ) (v : Sˣ)
    (hπ : algebraMap R S π = (v : S) * ϖ ^ e) :
    (ramifiedNodeBaseChangeSpecIso R S π ϖ e n v hπ).hom ≫
        Spec.map (CommRingCat.ofHom
          ((ramifiedNodeEquiv R S π ϖ e n v hπ).toRingHom.comp
            (coefficientMap R S π n))) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  dsimp [ramifiedNodeBaseChangeSpecIso, baseChangedNodeSpec]
  rw [Category.assoc, ← Spec.map_comp]
  have he : (CommRingCat.ofHom (coefficientMap R S π n) ≫
        CommRingCat.ofHom (ramifiedNodeEquiv R S π ϖ e n v hπ).toRingHom) ≫
      (ramifiedNodeEquiv R S π ϖ e n v hπ).toRingEquiv.toCommRingCatIso.op.inv.unop =
      CommRingCat.ofHom (coefficientMap R S π n) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    simp
  change (baseChangeSpecIso R S π n).hom ≫
      Spec.map ((CommRingCat.ofHom (coefficientMap R S π n) ≫
        CommRingCat.ofHom (ramifiedNodeEquiv R S π ϖ e n v hπ).toRingHom) ≫
        (ramifiedNodeEquiv R S π ϖ e n v hπ).toRingEquiv.toCommRingCatIso.op.inv.unop) = _
  rw [he, baseChangeSpecIso_hom_coefficientMap R S π n]

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
