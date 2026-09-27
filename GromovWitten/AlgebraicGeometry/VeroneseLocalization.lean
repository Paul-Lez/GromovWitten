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
The restriction to homogeneous localization is bijective for positive `d`, and is packaged as a
ring equivalence.  The inclusion of the Veronese multiplies degrees by `d`, so the construction
uses homogeneous localization representatives directly instead of pretending that the inclusion
is a same-index `GradedRingHom`.
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

private def veroneseLocalizationMapAux (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (hlocal : Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs) ≤
      (Submonoid.powers s).comap (veroneseToOriginal d).toRingHom) :
    HomogeneousLocalization.Away (veroneseComponent d 𝒜)
        (veronesePower (𝒜 := 𝒜) d e s hs) →+*
      HomogeneousLocalization.Away 𝒜 s := by
  let f := forwardMapAux d e s hs hlocal
  let e' := RingEquiv.ofLeftInverse
    (f := algebraMap (HomogeneousLocalization.Away 𝒜 s) (Localization (Submonoid.powers s)))
    (h := (HomogeneousLocalization.val_injective _).hasLeftInverse.choose_spec)
  have hf : ∀ z, f z ∈ (algebraMap (HomogeneousLocalization.Away 𝒜 s)
      (Localization (Submonoid.powers s))).range := by
    intro z
    exact range_forwardMapAux_subset d e s hs hlocal ⟨z, rfl⟩
  exact e'.symm.toRingHom.comp (f.codRestrict _ hf)

private def veroneseInverseNumDen (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e) (hd : 0 < d)
    (m : ℕ) (b : A) (hb : b ∈ 𝒜 (m • e)) :
    NumDenSameDeg (veroneseComponent d 𝒜)
      (Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs) ) :=
  { deg := m * e
    num := ⟨DirectSum.of (fun n => veronesePiece d 𝒜 n) (m * e)
      ⟨b * s ^ ((d - 1) * m), by
        change b * s ^ ((d - 1) * m) ∈ 𝒜 (d * (m * e))
        have h := SetLike.mul_mem_graded hb (SetLike.pow_mem_graded ((d - 1) * m) hs)
        simp only [nsmul_eq_mul] at h
        have hle : m * e ≤ d * (m * e) := Nat.le_mul_of_pos_left (m * e) hd
        convert h using 1
        congr 1
        calc
          d * (m * e) = d * m * e := by ring
          _ = m * e + (d * m * e - m * e) := by
            have hle' : m * e ≤ d * m * e := by
              simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hle
            rw [Nat.add_sub_of_le hle']
          _ = m * e + ((d - 1) * m) * e := by
            rw [Nat.mul_sub_right_distrib, Nat.sub_mul]
            simp⟩,
      veroneseComponent_mem d (m * e) _⟩
    den := ⟨(veronesePower (𝒜 := 𝒜) d e s hs) ^ m,
      SetLike.pow_mem_graded m (veronesePower_mem_component d e s hs)⟩
    den_mem := ⟨m, rfl⟩ }

def veroneseLocalizationMap (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e) :
    HomogeneousLocalization.Away (veroneseComponent d 𝒜)
        (veronesePower (𝒜 := 𝒜) d e s hs) →+*
      HomogeneousLocalization.Away 𝒜 s :=
  veroneseLocalizationMapAux d e s hs
    (powers_veronese_le_comap_powers_original (𝒜 := 𝒜) e s hs)

private theorem veroneseLocalizationMapAux_val (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (hlocal : Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs) ≤
      (Submonoid.powers s).comap (veroneseToOriginal d).toRingHom)
    (z : HomogeneousLocalization.Away (veroneseComponent d 𝒜)
      (veronesePower (𝒜 := 𝒜) d e s hs)) :
    (veroneseLocalizationMapAux d e s hs hlocal z).val =
      forwardMapAux d e s hs hlocal z := by
  let f := forwardMapAux d e s hs hlocal
  let e' := RingEquiv.ofLeftInverse
    (f := algebraMap (HomogeneousLocalization.Away 𝒜 s) (Localization (Submonoid.powers s)))
    (h := (HomogeneousLocalization.val_injective _).hasLeftInverse.choose_spec)
  have hf : ∀ z, f z ∈ (algebraMap (HomogeneousLocalization.Away 𝒜 s)
      (Localization (Submonoid.powers s))).range := by
    intro z
    exact range_forwardMapAux_subset d e s hs hlocal ⟨z, rfl⟩
  change (e' (e'.symm ⟨f z, hf z⟩)).val = f z
  rw [e'.apply_symm_apply]

private theorem veroneseLocalizationMapAux_Away_mk_val (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (hlocal : Submonoid.powers (veronesePower (𝒜 := 𝒜) d e s hs) ≤
      (Submonoid.powers s).comap (veroneseToOriginal d).toRingHom)
    (m : ℕ) (a : Veronese d 𝒜)
    (ha : a ∈ veroneseComponent d 𝒜 (m • e)) :
    (veroneseLocalizationMapAux d e s hs hlocal
      (HomogeneousLocalization.Away.mk (veroneseComponent d 𝒜)
        (veronesePower_mem_component d e s hs) m a ha)).val =
      Localization.mk (veroneseToOriginal d a)
        ⟨(s ^ d) ^ m, by
          simpa [veronesePower_to_original, pow_mul] using hlocal ⟨m, rfl⟩⟩ := by
  rw [veroneseLocalizationMapAux_val]
  simp only [HomogeneousLocalization.Away.mk, forwardMapAux_mk,
    HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk']
  simp [forwardNumDen, veronesePower_to_original]

private theorem veroneseLocalizationMap_val (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (z : HomogeneousLocalization.Away (veroneseComponent d 𝒜)
      (veronesePower (𝒜 := 𝒜) d e s hs)) :
    (veroneseLocalizationMap d e s hs z).val =
      forwardMapAux d e s hs (powers_veronese_le_comap_powers_original (𝒜 := 𝒜) e s hs) z := by
  exact veroneseLocalizationMapAux_val d e s hs _ z

theorem veroneseLocalizationMap_Away_mk_val (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (m : ℕ) (a : Veronese d 𝒜)
    (ha : a ∈ veroneseComponent d 𝒜 (m • e)) :
    (veroneseLocalizationMap d e s hs
      (HomogeneousLocalization.Away.mk (veroneseComponent d 𝒜)
        (veronesePower_mem_component d e s hs) m a ha)).val =
      Localization.mk (veroneseToOriginal d a)
        ⟨(s ^ d) ^ m, by
          simpa [veronesePower_to_original, pow_mul] using
            (powers_veronese_le_comap_powers_original (𝒜 := 𝒜) e s hs) ⟨m, rfl⟩⟩ := by
  exact veroneseLocalizationMapAux_Away_mk_val d e s hs
    (powers_veronese_le_comap_powers_original (𝒜 := 𝒜) e s hs) m a ha

/-- The explicit homogeneous fraction used to lift `b / s ^ m` to the Veronese chart. -/
def veroneseLocalizationInverseFraction (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (hd : 0 < d) (m : ℕ) (b : A) (hb : b ∈ 𝒜 (m • e)) :
    HomogeneousLocalization.Away (veroneseComponent d 𝒜)
      (veronesePower (𝒜 := 𝒜) d e s hs) :=
  HomogeneousLocalization.mk (veroneseInverseNumDen d e s hs hd m b hb)

private theorem veroneseLocalizationMap_inverseFraction (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (hd : 0 < d) (m : ℕ) (b : A) (hb : b ∈ 𝒜 (m • e)) :
    veroneseLocalizationMap d e s hs
        (veroneseLocalizationInverseFraction d e s hs hd m b hb) =
      HomogeneousLocalization.Away.mk 𝒜 hs m b hb := by
  let c := veroneseInverseNumDen d e s hs hd m b hb
  change veroneseLocalizationMap d e s hs (HomogeneousLocalization.mk c) = _
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  rw [veroneseLocalizationMap_val]
  rw [forwardMapAux_mk, HomogeneousLocalization.Away.val_mk]
  have hcnum : veroneseToOriginal d (c.num : Veronese d 𝒜) =
      b * s ^ ((d - 1) * m) := by
    simp [c, veroneseInverseNumDen]
  have hcden : veroneseToOriginal d (c.den : Veronese d 𝒜) =
      (s ^ d) ^ m := by
    simp [c, veroneseInverseNumDen]
  change Localization.mk (veroneseToOriginal d (c.num : Veronese d 𝒜)) _ = _
  rw [hcnum]
  change Localization.mk (b * s ^ ((d - 1) * m))
      ⟨veroneseToOriginal d (c.den : Veronese d 𝒜), _⟩ = _
  simp only [hcden]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul]
  rw [← pow_mul]
  have hm : m + (d - 1) * m = d * m := by
    rw [Nat.sub_mul]
    simpa using Nat.add_sub_of_le (Nat.le_mul_of_pos_left m hd)
  calc
    s ^ m * (b * s ^ ((d - 1) * m)) = b * (s ^ m * s ^ ((d - 1) * m)) := by ac_rfl
    _ = b * s ^ (m + (d - 1) * m) := by rw [← pow_add]
    _ = b * s ^ (d * m) := by rw [hm]
    _ = s ^ (d * m) * b := by ac_rfl

theorem veroneseLocalizationMap_surjective (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (hd : 0 < d) :
    Function.Surjective (veroneseLocalizationMap (𝒜 := 𝒜) d e s hs) := by
  intro z
  obtain ⟨m, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hs z
  exact ⟨veroneseLocalizationInverseFraction d e s hs hd m b hb,
    veroneseLocalizationMap_inverseFraction d e s hs hd m b hb⟩

theorem veroneseLocalizationMap_injective (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (hd : 0 < d) :
    Function.Injective (veroneseLocalizationMap (𝒜 := 𝒜) d e s hs) := by
  intro x y hxy
  obtain ⟨m, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (veroneseComponent d 𝒜) (veronesePower_mem_component d e s hs) x
  obtain ⟨n, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (veroneseComponent d 𝒜) (veronesePower_mem_component d e s hs) y
  have hxy' := congrArg HomogeneousLocalization.val hxy
  rw [veroneseLocalizationMap_Away_mk_val, veroneseLocalizationMap_Away_mk_val] at hxy'
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hxy'
  obtain ⟨c, hc⟩ := hxy'
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (c : A) s).mp c.property
  rw [← hk] at hc
  change s ^ k * ((s ^ d) ^ n * veroneseToOriginal d a) =
    s ^ k * ((s ^ d) ^ m * veroneseToOriginal d b) at hc
  simp only [← pow_mul] at hc
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨(veronesePower (𝒜 := 𝒜) d e s hs) ^ k, ⟨k, rfl⟩⟩, ?_⟩
  apply veroneseToOriginal_injective (𝒜 := 𝒜) hd
  have hscaled := congrArg (fun z : A => s ^ ((d - 1) * k) * z) hc
  have hdk : (d - 1) * k + k = d * k := by
    rw [Nat.sub_mul]
    simpa using (Nat.sub_add_cancel (Nat.le_mul_of_pos_left k hd))
  calc
    veroneseToOriginal d ((veronesePower (𝒜 := 𝒜) d e s hs) ^ k *
        ((veronesePower (𝒜 := 𝒜) d e s hs) ^ n * a)) =
        s ^ (d * k) * (s ^ (d * n) * veroneseToOriginal d a) := by
          simp only [map_mul, map_pow, veronesePower_to_original, ← pow_mul]
    _ = s ^ ((d - 1) * k) * (s ^ k * (s ^ (d * n) * veroneseToOriginal d a)) := by
          rw [← hdk, pow_add]
          ac_rfl
    _ = s ^ ((d - 1) * k) * (s ^ k * (s ^ (d * m) * veroneseToOriginal d b)) := hscaled
    _ = s ^ (d * k) * (s ^ (d * m) * veroneseToOriginal d b) := by
          rw [← hdk, pow_add]
          ac_rfl
    _ = veroneseToOriginal d ((veronesePower (𝒜 := 𝒜) d e s hs) ^ k *
        ((veronesePower (𝒜 := 𝒜) d e s hs) ^ m * b)) := by
          simp only [map_mul, map_pow, veronesePower_to_original, ← pow_mul]

/-- The positive-index Veronese homogeneous chart at `s ^ d` is canonically the original
homogeneous chart at `s`.  The map is induced by the inclusion into the ordinary localization;
its representative formula is given by `veroneseLocalizationMap_Away_mk_val`. -/
def veroneseLocalizationEquiv (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e) (hd : 0 < d) :
    HomogeneousLocalization.Away (veroneseComponent d 𝒜)
        (veronesePower (𝒜 := 𝒜) d e s hs) ≃+*
      HomogeneousLocalization.Away 𝒜 s :=
  RingEquiv.ofBijective (veroneseLocalizationMap (𝒜 := 𝒜) d e s hs)
    ⟨veroneseLocalizationMap_injective d e s hs hd,
      veroneseLocalizationMap_surjective d e s hs hd⟩

@[simp]
theorem veroneseLocalizationEquiv_apply (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e) (hd : 0 < d)
    (z : HomogeneousLocalization.Away (veroneseComponent d 𝒜)
      (veronesePower (𝒜 := 𝒜) d e s hs)) :
    veroneseLocalizationEquiv (𝒜 := 𝒜) d e s hs hd z =
      veroneseLocalizationMap d e s hs z := rfl

/-- The inverse chart map sends a fraction to the explicit Veronese fraction with numerator
`b * s ^ ((d - 1) * m)` and denominator `(s ^ d) ^ m`. -/
theorem veroneseLocalizationEquiv_symm_Away_mk (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e)
    (hd : 0 < d) (m : ℕ) (b : A) (hb : b ∈ 𝒜 (m • e)) :
    (veroneseLocalizationEquiv (𝒜 := 𝒜) d e s hs hd).symm
        (HomogeneousLocalization.Away.mk 𝒜 hs m b hb) =
      veroneseLocalizationInverseFraction d e s hs hd m b hb := by
  apply (veroneseLocalizationEquiv (𝒜 := 𝒜) d e s hs hd).injective
  rw [(veroneseLocalizationEquiv (𝒜 := 𝒜) d e s hs hd).apply_symm_apply]
  rw [veroneseLocalizationEquiv_apply]
  exact (veroneseLocalizationMap_inverseFraction d e s hs hd m b hb).symm

end
end GromovWitten.AlgebraicGeometry
