/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Veronese
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Veronese homogeneous localization

This file constructs the distinguished Veronese chart element and the map of its
homogeneous fractions into the ordinary localization of the original graded ring.
Restricting this map to homogeneous localization and proving bijectivity remain to be done.
The inclusion of the Veronese multiplies degrees by `d`, so the
construction uses homogeneous localization representatives directly instead of pretending that
the inclusion is a same-index `GradedRingHom`.
-/

open DirectSum SetLike

namespace GromovWitten.AlgebraicGeometry

open HomogeneousLocalization

universe u

noncomputable section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]

instance veroneseAddSubgroupClass (d : ℕ) :
    AddSubgroupClass (Submodule R (Veronese d 𝒜)) (Veronese d 𝒜) :=
  @Submodule.addSubgroupClass R (Veronese d 𝒜) inferInstance inferInstance inferInstance


/-! ## The distinguished Veronese chart element -/

/-- The element of the Veronese corresponding to `s^d`, where `s` has degree `e`. -/
def veronesePower (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e) : Veronese d 𝒜 :=
  DirectSum.of (fun n => veronesePiece d 𝒜 n) e
    ⟨s ^ d, by simpa [veronesePiece, smul_eq_mul] using SetLike.pow_mem_graded d hs⟩

@[simp]
theorem veronesePower_mem_component (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e) :
    veronesePower (𝒜 := 𝒜) d e s hs ∈ veroneseComponent d 𝒜 e :=
  veroneseComponent_mem d e _

@[simp]
theorem veronesePower_to_original (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e) :
    veroneseToOriginal (𝒜 := 𝒜) d (veronesePower d e s hs) = s ^ d := by
  simp [veronesePower]


private theorem veronese_mem_original {d n : ℕ} {x : Veronese d 𝒜}
    (hx : x ∈ veroneseComponent d 𝒜 n) :
    veroneseToOriginal d x ∈ 𝒜 (d * n) := by
  rcases hx with ⟨y, rfl⟩
  rw [DirectSum.lof_eq_of]
  rw [veroneseToOriginal_of]
  exact y.property

private theorem powers_veronese_le_comap_powers_original
    (e : ℕ) (s : A) (hs : s ∈ 𝒜 e) :
    Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs) ≤
      (Submonoid.powers s).comap (veroneseToOriginal (𝒜 := 𝒜) d).toRingHom := by
  rintro z ⟨k, rfl⟩
  refine ⟨d * k, ?_⟩
  simp [veronesePower_to_original, pow_mul]

/-! ## The canonical map on homogeneous fractions -/

private def forwardNumDen (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (hlocal : Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs) ≤
      (Submonoid.powers s).comap (veroneseToOriginal (𝒜 := 𝒜) d).toRingHom)
    (c : NumDenSameDeg (veroneseComponent d 𝒜)
      (Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs))) :
    NumDenSameDeg 𝒜 (Submonoid.powers s) :=
  { deg := d * c.deg
    num := ⟨veroneseToOriginal d c.num, veronese_mem_original c.num.property⟩
    den := ⟨veroneseToOriginal d c.den, veronese_mem_original c.den.property⟩
    den_mem := hlocal c.den_mem }

private def forwardMapAux (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (hlocal : Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs) ≤
      (Submonoid.powers s).comap (veroneseToOriginal (𝒜 := 𝒜) d).toRingHom) :
    HomogeneousLocalization.Away (veroneseComponent d 𝒜)
        (veronesePower (𝒜 := 𝒜) d e s hs) →+*
      Localization (Submonoid.powers s) := by
  let φ : Localization (Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs)) →+*
      Localization (Submonoid.powers s) :=
    IsLocalization.map (R := Veronese d 𝒜)
      (M := Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs))
      (S := Localization (Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs)))
      (P := A) (T := Submonoid.powers s)
      (Localization (Submonoid.powers s)) (veroneseToOriginal d).toRingHom hlocal
  exact φ.comp (algebraMap (HomogeneousLocalization.Away (veroneseComponent d 𝒜)
    (veronesePower (𝒜 := 𝒜) d e s hs))
    (Localization (Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs))))

private theorem forwardMapAux_mk (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (hlocal : Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs) ≤
      (Submonoid.powers s).comap (veroneseToOriginal (𝒜 := 𝒜) d).toRingHom)
    (c : NumDenSameDeg (veroneseComponent d 𝒜)
      (Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs))) :
    forwardMapAux d e s hs hlocal (HomogeneousLocalization.mk c) =
      HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 (Submonoid.powers s)
        (forwardNumDen d e s hs hlocal c) := by
  simp only [forwardMapAux, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk]
  rw [Localization.mk_eq_mk', IsLocalization.map_mk',
    HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk']
  rfl

private theorem range_forwardMapAux_subset (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (hlocal : Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs) ≤
      (Submonoid.powers s).comap (veroneseToOriginal (𝒜 := 𝒜) d).toRingHom) :
    Set.range (forwardMapAux d e s hs hlocal) ⊆
      Set.range (HomogeneousLocalization.val (𝒜 := 𝒜) (x := Submonoid.powers s)) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  exact ⟨HomogeneousLocalization.mk (forwardNumDen d e s hs hlocal c),
    (forwardMapAux_mk d e s hs hlocal c).symm⟩

end
end GromovWitten.AlgebraicGeometry
