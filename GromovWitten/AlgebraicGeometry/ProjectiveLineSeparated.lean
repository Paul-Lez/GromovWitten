/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks
import GromovWitten.AlgebraicGeometry.ProjectiveLineCharts

/-!
# Separatedness of the projective line

The standard chart cover of the projective line exhibits its diagonal as a closed immersion over
any commutative base ring.
-/

open CategoryTheory Limits AlgebraicGeometry TensorProduct

universe u

namespace GromovWitten.AlgebraicGeometry
section Separated

/-! ## Separatedness of a scheme glued from two affine charts

The diagonal of a morphism `w : Z ⟶ Spec R` is a closed immersion as soon as `Z` has an affine
open cover `Spec Sᵢ ⟶ Z` with affine pairwise intersections over which the multiplication maps
`Sᵢ ⊗[R] Sⱼ → Γ(Spec Sᵢ ∩ Spec Sⱼ)` are surjective.  The next lemma is the local input of this
criterion (the pieces of `IsZariskiLocalAtTarget.of_openCover` applied to the cover of
`Z ×_{Spec R} Z` by the products `Spec Sᵢ ×_{Spec R} Spec Sⱼ`), in the form in which the goals
of that reduction actually appear.  It is the affine-diagonal argument used by Mathlib for
`Proj`, phrased for an arbitrary gluing. -/

/-- **The affine-diagonal criterion, one piece.**  Let `u : Spec S ⟶ Z` and `v : Spec T ⟶ Z` be
two members of an open cover of a scheme `Z` over `Spec R`, and suppose that their intersection is
`Spec A`, i.e. that the square with sides `Spec.map φ`, `Spec.map ψ`, `u`, `v` is cartesian.  If
the induced ring map `F : S ⊗[R] T → A` is surjective, then the restriction of the diagonal of
`w : Z ⟶ Spec R` to `Spec S ×_{Spec R} Spec T` is a closed immersion. -/
lemma isClosedImmersion_pullback_snd_diagonal
    {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra R T] {Z : Scheme.{u}} {w : Z ⟶ Spec (CommRingCat.of R)}
    {u : Spec (CommRingCat.of S) ⟶ Z} {v : Spec (CommRingCat.of T) ⟶ Z}
    (hu : u ≫ w = Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (hv : v ≫ w = Spec.map (CommRingCat.ofHom (algebraMap R T)))
    {φ : S →+* A} {ψ : T →+* A}
    (hsq : IsPullback (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom ψ)) u v)
    (F : S ⊗[R] T →+* A) (hF : Function.Surjective F)
    (hFl : F.comp Algebra.TensorProduct.includeLeftRingHom = φ)
    (hFr : F.comp (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom = ψ) :
    IsClosedImmersion (pullback.snd (pullback.diagonal w)
      (pullback.map (u ≫ w) (v ≫ w) w w u v (𝟙 _)
        (Category.comp_id _) (Category.comp_id _))) := by
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (f := (pullbackDiagonalMapIdIso u v w).inv) _).mp ?_
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    hsq.isoPullback.hom]
  set ι : Spec (CommRingCat.of (S ⊗[R] T)) ⟶ pullback (u ≫ w) (v ≫ w) :=
    (pullbackSpecIso R S T).inv ≫ (pullback.congrHom hu hv).inv with hιdef
  have hι1 : ι ≫ pullback.fst (u ≫ w) (v ≫ w) =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
    rw [hιdef, Category.assoc, pullback.congrHom_inv, pullback.lift_fst, Category.comp_id,
      pullbackSpecIso_inv_fst]
  have hι2 : ι ≫ pullback.snd (u ≫ w) (v ≫ w) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom) := by
    rw [hιdef, Category.assoc, pullback.congrHom_inv, pullback.lift_snd, Category.comp_id,
      pullbackSpecIso_inv_snd]
    rfl
  have hIso : IsIso ι := by rw [hιdef]; infer_instance
  have key : hsq.isoPullback.hom ≫ (pullbackDiagonalMapIdIso u v w).inv ≫
      pullback.snd (pullback.diagonal w) (pullback.map (u ≫ w) (v ≫ w) w w u v (𝟙 _)
        (Category.comp_id _) (Category.comp_id _)) =
      Spec.map (CommRingCat.ofHom F) ≫ ι := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hι1, pullbackDiagonalMapIdIso_inv_snd_fst, hsq.isoPullback_hom_fst, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hFl]
    · simp only [Category.assoc]
      rw [hι2, pullbackDiagonalMapIdIso_inv_snd_snd, hsq.isoPullback_hom_snd, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hFr]
  rw [key]
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ ι).mpr
    (IsClosedImmersion.spec_of_surjective _ hF)

namespace ProjectiveLine

noncomputable section

variable (k : Type u) [CommRing k]

/-! ### The three surjective multiplication maps -/

/-- The transition map `k[s] → k[t,t⁻¹]` is a map of `k`-algebras. -/
lemma flipHom_algebraMap (a : k) :
    flipHom k (algebraMap k (Polynomial k) a) = algebraMap k (overlapRing k) a := by
  rw [IsScalarTower.algebraMap_apply k (Polynomial k) (overlapRing k), Polynomial.algebraMap_eq,
    flipHom_C]

/-- The transition map `k[s] → k[t,t⁻¹]`, `s ↦ t⁻¹`, as a `k`-algebra homomorphism. -/
def flipAlgHom : Polynomial k →ₐ[k] overlapRing k :=
  { flipHom k with commutes' := flipHom_algebraMap k }

/-- `flipAlgHom` is `flipHom`. -/
@[simp] lemma flipAlgHom_apply (p : Polynomial k) : flipAlgHom k p = flipHom k p := rfl

/-- Every element of `k[t,t⁻¹]` is of the form `p · (t⁻¹)ⁿ` with `p ∈ k[t]`. -/
lemma exists_eq_algebraMap_mul_tInv_pow (z : overlapRing k) :
    ∃ (p : Polynomial k) (n : ℕ),
      z = algebraMap (Polynomial k) (overlapRing k) p * (tInv k) ^ n := by
  obtain ⟨p, m, hm⟩ := IsLocalization.exists_mk'_eq (M := Submonoid.powers
    (Polynomial.X : Polynomial k)) (S := overlapRing k) z
  obtain ⟨n, hn⟩ := m.2
  have hn' : (m : Polynomial k) = (Polynomial.X : Polynomial k) ^ n := hn.symm
  refine ⟨p, n, ?_⟩
  have h1 : algebraMap (Polynomial k) (overlapRing k) ((Polynomial.X : Polynomial k) ^ n) *
      (tInv k) ^ n = 1 := by
    rw [map_pow, ← mul_pow, algebraMap_X_mul_tInv, one_pow]
  calc z = IsLocalization.mk' (overlapRing k) p m := hm.symm
    _ = IsLocalization.mk' (overlapRing k) p m *
        (algebraMap (Polynomial k) (overlapRing k) ((Polynomial.X : Polynomial k) ^ n) *
          (tInv k) ^ n) := by rw [h1, mul_one]
    _ = (algebraMap (Polynomial k) (overlapRing k) m *
        IsLocalization.mk' (overlapRing k) p m) * (tInv k) ^ n := by rw [hn']; ring
    _ = algebraMap (Polynomial k) (overlapRing k) p * (tInv k) ^ n := by
        rw [IsLocalization.mk'_spec']

/-- The multiplication map `k[t] ⊗_k k[t] → k[t]`, the comultiplication of the diagonal of a
single chart. -/
def diagHom : Polynomial k ⊗[k] Polynomial k →+* Polynomial k :=
  (Algebra.TensorProduct.lift (AlgHom.id k (Polynomial k)) (AlgHom.id k (Polynomial k))
    (fun _ _ => Commute.all _ _)).toRingHom

/-- The map `k[t] ⊗_k k[s] → k[t,t⁻¹]` given by `t ↦ t`, `s ↦ t⁻¹`. -/
def overlapHomLeft : Polynomial k ⊗[k] Polynomial k →+* overlapRing k :=
  (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k (Polynomial k) (overlapRing k))
    (flipAlgHom k) (fun _ _ => Commute.all _ _)).toRingHom

/-- The map `k[s] ⊗_k k[t] → k[t,t⁻¹]` given by `s ↦ t⁻¹`, `t ↦ t`. -/
def overlapHomRight : Polynomial k ⊗[k] Polynomial k →+* overlapRing k :=
  (Algebra.TensorProduct.lift (flipAlgHom k)
    (IsScalarTower.toAlgHom k (Polynomial k) (overlapRing k))
    (fun _ _ => Commute.all _ _)).toRingHom

/-- The multiplication map of a chart with itself is surjective. -/
lemma diagHom_surjective : Function.Surjective (diagHom k) :=
  fun a => ⟨a ⊗ₜ 1, by simp [diagHom]⟩

/-- `k[t,t⁻¹]` is generated over `k` by `t` and `t⁻¹`. -/
lemma overlapHomLeft_surjective : Function.Surjective (overlapHomLeft k) := by
  intro z
  obtain ⟨p, n, hz⟩ := exists_eq_algebraMap_mul_tInv_pow k z
  refine ⟨p ⊗ₜ ((Polynomial.X : Polynomial k) ^ n), ?_⟩
  rw [hz, overlapHomLeft]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
    IsScalarTower.coe_toAlgHom', flipAlgHom_apply, map_pow, flipHom_X]

/-- The mirror image of `overlapHomLeft_surjective`. -/
lemma overlapHomRight_surjective : Function.Surjective (overlapHomRight k) := by
  intro z
  obtain ⟨p, n, hz⟩ := exists_eq_algebraMap_mul_tInv_pow k z
  refine ⟨((Polynomial.X : Polynomial k) ^ n) ⊗ₜ p, ?_⟩
  rw [hz, overlapHomRight]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
    IsScalarTower.coe_toAlgHom', flipAlgHom_apply, map_pow, flipHom_X]
  rw [mul_comm]

/-- `diagHom` restricted to the left factor is the identity. -/
lemma diagHom_comp_includeLeft :
    (diagHom k).comp Algebra.TensorProduct.includeLeftRingHom = RingHom.id (Polynomial k) :=
  RingHom.ext fun p => by simp [diagHom]

/-- `diagHom` restricted to the right factor is the identity. -/
lemma diagHom_comp_includeRight :
    (diagHom k).comp (Algebra.TensorProduct.includeRight :
      Polynomial k →ₐ[k] Polynomial k ⊗[k] Polynomial k).toRingHom =
      RingHom.id (Polynomial k) :=
  RingHom.ext fun p => by simp [diagHom]

/-- `overlapHomLeft` restricted to the left factor is the localisation map. -/
lemma overlapHomLeft_comp_includeLeft :
    (overlapHomLeft k).comp Algebra.TensorProduct.includeLeftRingHom =
      algebraMap (Polynomial k) (overlapRing k) :=
  RingHom.ext fun p => by simp [overlapHomLeft]

/-- `overlapHomLeft` restricted to the right factor is the transition map. -/
lemma overlapHomLeft_comp_includeRight :
    (overlapHomLeft k).comp (Algebra.TensorProduct.includeRight :
      Polynomial k →ₐ[k] Polynomial k ⊗[k] Polynomial k).toRingHom = flipHom k :=
  RingHom.ext fun p => by simp [overlapHomLeft]

/-- `overlapHomRight` restricted to the left factor is the transition map. -/
lemma overlapHomRight_comp_includeLeft :
    (overlapHomRight k).comp Algebra.TensorProduct.includeLeftRingHom = flipHom k :=
  RingHom.ext fun p => by simp [overlapHomRight]

/-- `overlapHomRight` restricted to the right factor is the localisation map. -/
lemma overlapHomRight_comp_includeRight :
    (overlapHomRight k).comp (Algebra.TensorProduct.includeRight :
      Polynomial k →ₐ[k] Polynomial k ⊗[k] Polynomial k).toRingHom =
      algebraMap (Polynomial k) (overlapRing k) :=
  RingHom.ext fun p => by simp [overlapHomRight]

/-- **The projective line is separated over its base ring.**  The diagonal of
`ℙ¹_k ⟶ Spec k` is a closed immersion because on each of the four products of charts the
comparison map of coordinate rings — `k[t] ⊗_k k[t] → k[t]` on the two diagonal pieces and
`k[t] ⊗_k k[s] → k[t,t⁻¹]`, `s ↦ t⁻¹`, on the two off-diagonal ones — is surjective. -/
instance instIsSeparatedStructureMap : IsSeparated (structureMap k) := by
  refine ⟨AlgebraicGeometry.IsZariskiLocalAtTarget.of_openCover
    (Scheme.Pullback.openCoverOfLeftRight (chartCover k) (chartCover k) _ _) ?_⟩
  rintro ⟨i, j⟩
  cases i <;> cases j
  · exact isClosedImmersion_pullback_snd_diagonal (chartMap_comp_structureMap k false)
      (chartMap_comp_structureMap k false) (isPullback_chart_self k false) (diagHom k)
      (diagHom_surjective k) (diagHom_comp_includeLeft k) (diagHom_comp_includeRight k)
  · exact isClosedImmersion_pullback_snd_diagonal (chartMap_comp_structureMap k false)
      (chartMap_comp_structureMap k true) (isPullback_chartZero_chartOne k) (overlapHomLeft k)
      (overlapHomLeft_surjective k) (overlapHomLeft_comp_includeLeft k)
      (overlapHomLeft_comp_includeRight k)
  · exact isClosedImmersion_pullback_snd_diagonal (chartMap_comp_structureMap k true)
      (chartMap_comp_structureMap k false) (isPullback_chartOne_chartZero k) (overlapHomRight k)
      (overlapHomRight_surjective k) (overlapHomRight_comp_includeLeft k)
      (overlapHomRight_comp_includeRight k)
  · exact isClosedImmersion_pullback_snd_diagonal (chartMap_comp_structureMap k true)
      (chartMap_comp_structureMap k true) (isPullback_chart_self k true) (diagHom k)
      (diagHom_surjective k) (diagHom_comp_includeLeft k) (diagHom_comp_includeRight k)

end

end ProjectiveLine

end Separated

end GromovWitten.AlgebraicGeometry
