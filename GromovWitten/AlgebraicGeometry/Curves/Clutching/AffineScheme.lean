/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.Clutching.Affine
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# The affine geometry of clutching

Let `P = A ×_R B` be the fibre product defined by two augmentations to `R`.  This
file records the geometric consequences needed for pinching: the two affine branch
maps are closed immersions which cover `Spec P`, their branch ideals have the expected
intersection and common-section sum, and their scheme-theoretic intersection is
identified by an actual `IsPullback` square with `Spec R`.  Maps from `Spec P` to an
affine target glue uniquely.  The last statement is deliberately scoped to affine
targets; it does not assert a pushout in all schemes.
-/

open _root_.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open TopologicalSpace

namespace GromovWitten
namespace AlgebraicGeometry
namespace Curves
namespace Clutching

universe u

noncomputable section

variable {R A B Q : Type u}
variable [CommRing R] [CommRing A] [CommRing B] [CommRing Q]
variable [Algebra R A] [Algebra R B] [Algebra R Q]

namespace fiberProduct

variable (εA : A →ₐ[R] R) (εB : B →ₐ[R] R)

local notation "P" => fiberProduct εA εB

/-! ## The two branch ideals and the common section -/

/-- The ideal cut out by the first branch `Spec A → Spec P`. -/
def fstIdeal : Ideal P := RingHom.ker (fst εA εB).toRingHom

/-- The ideal cut out by the second branch `Spec B → Spec P`. -/
def sndIdeal : Ideal P := RingHom.ker (snd εA εB).toRingHom

/-- The augmentation of the pinching ring to the common base ring. -/
def augmentation : P →ₐ[R] R := (εA.comp (fst εA εB))

/-- The ideal of the common section in the pinching ring. -/
def augmentationIdeal : Ideal P := RingHom.ker (augmentation εA εB).toRingHom

/-- The common section as a morphism into the pinched affine scheme. -/
def specAugmentation : Spec (.of R) ⟶ Spec (.of P) :=
  Scheme.Spec.map (CommRingCat.ofHom (augmentation εA εB).toRingHom).op

theorem augmentation_surjective : Function.Surjective (augmentation εA εB) := by
  intro r
  refine ⟨algebraMap R P r, ?_⟩
  simp [augmentation, fst]

instance specAugmentation_isClosedImmersion : IsClosedImmersion (specAugmentation εA εB) :=
  IsClosedImmersion.spec_of_surjective _ (augmentation_surjective εA εB)

/-! The two branch sections factor through the common section. -/

def sectionA : Spec (.of R) ⟶ Spec (.of A) :=
  Scheme.Spec.map (CommRingCat.ofHom εA.toRingHom).op

def sectionB : Spec (.of R) ⟶ Spec (.of B) :=
  Scheme.Spec.map (CommRingCat.ofHom εB.toRingHom).op

def fstRingMap : CommRingCat.of P ⟶ CommRingCat.of A :=
  CommRingCat.ofHom (fst εA εB).toRingHom

def sndRingMap : CommRingCat.of P ⟶ CommRingCat.of B :=
  CommRingCat.ofHom (snd εA εB).toRingHom

def augmentationRingMapA : CommRingCat.of A ⟶ CommRingCat.of R :=
  CommRingCat.ofHom εA.toRingHom

def augmentationRingMapB : CommRingCat.of B ⟶ CommRingCat.of R :=
  CommRingCat.ofHom εB.toRingHom

/-! ## The ring pushout underlying the scheme-theoretic intersection -/

theorem branchRingSquare_isPushout :
    IsPushout (fstRingMap εA εB) (sndRingMap εA εB)
      (augmentationRingMapA εA) (augmentationRingMapB εB) := by
  let w : fstRingMap εA εB ≫ augmentationRingMapA εA =
      sndRingMap εA εB ≫ augmentationRingMapB εB := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (condition_hom εA εB)
  refine { w := w, isColimit' := ⟨PushoutCocone.IsColimit.mk w
    (fun s => CommRingCat.ofHom (s.inl.hom.comp (algebraMap R A))) ?_ ?_ ?_⟩ }
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    let hp : P := ⟨(a, algebraMap R B (εA a)), by simp⟩
    have hs := congrArg (fun k : CommRingCat.of P ⟶ s.pt => k.hom hp) s.condition
    let hp0 : P :=
      ⟨(algebraMap R A (εA a), algebraMap R B (εA a)), by simp⟩
    have hs0 := congrArg (fun k : CommRingCat.of P ⟶ s.pt => k.hom hp0) s.condition
    have hs0' : (s.inl.hom) (algebraMap R A (εA a)) =
        (s.inr.hom) (algebraMap R B (εA a)) := by
      simpa [fstRingMap, sndRingMap, hp0] using hs0
    have hs' : (s.inl.hom) a = (s.inr.hom) (algebraMap R B (εA a)) := by
      simpa [fstRingMap, sndRingMap, hp] using hs
    exact hs0'.trans hs'.symm
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    let hp : P := ⟨(algebraMap R A (εB b), b), by simp⟩
    have hs := congrArg (fun k : CommRingCat.of P ⟶ s.pt => k.hom hp) s.condition
    have hs' : (s.inl.hom) (algebraMap R A (εB b)) = (s.inr.hom) b := by
      simpa [fstRingMap, sndRingMap, hp] using hs
    exact hs'
  · intro s m hm _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    have hm' := congrArg
      (fun k : CommRingCat.of A ⟶ s.pt => k.hom (algebraMap R A r)) hm
    simpa [augmentationRingMapA] using hm'

theorem branch_isPullback :
    IsPullback (sectionA εA) (sectionB εB)
      (specFst εA εB) (specSnd εA εB) := by
  exact isPullback_SpecMap_of_isPushout
    (fstRingMap εA εB) (sndRingMap εA εB)
    (augmentationRingMapA εA) (augmentationRingMapB εB)
    (branchRingSquare_isPushout εA εB)

@[reassoc (attr := simp)]
theorem sectionA_specFst :
    sectionA εA ≫ specFst εA εB = specAugmentation εA εB := by
  change Scheme.Spec.map (CommRingCat.ofHom εA.toRingHom).op ≫
      Scheme.Spec.map (CommRingCat.ofHom (fst εA εB).toRingHom).op = _
  rw [← Scheme.Spec.map_comp]
  congr 1

@[reassoc (attr := simp)]
theorem sectionB_specSnd :
    sectionB εB ≫ specSnd εA εB = specAugmentation εA εB := by
  change Scheme.Spec.map (CommRingCat.ofHom εB.toRingHom).op ≫
      Scheme.Spec.map (CommRingCat.ofHom (snd εA εB).toRingHom).op = _
  rw [← Scheme.Spec.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommRingCat.hom_ext
  change εB.toRingHom.comp (snd εA εB).toRingHom =
    (augmentation εA εB).toRingHom
  exact (congrArg AlgHom.toRingHom (condition_hom εA εB)).symm

@[simp]
theorem mem_fstIdeal {p : P} : p ∈ fstIdeal εA εB ↔ fst εA εB p = 0 :=
  Iff.rfl

@[simp]
theorem mem_sndIdeal {p : P} : p ∈ sndIdeal εA εB ↔ snd εA εB p = 0 :=
  Iff.rfl

@[simp]
theorem mem_augmentationIdeal {p : P} : p ∈ augmentationIdeal εA εB ↔
    εA (fst εA εB p) = 0 :=
  Iff.rfl

theorem fstIdeal_mul_sndIdeal : fstIdeal εA εB * sndIdeal εA εB = ⊥ := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro p hp q hq
    change p * q = 0
    apply Subtype.ext
    apply Prod.ext
    · have hp' : fst εA εB p = 0 := hp
      simpa [fst_apply] using congrArg (fun x => x * fst εA εB q) hp'
    · have hq' : snd εA εB q = 0 := hq
      simpa [snd_apply] using congrArg (fun x => snd εA εB p * x) hq'
  · exact bot_le

theorem fstIdeal_inf_sndIdeal : fstIdeal εA εB ⊓ sndIdeal εA εB = ⊥ := by
  apply le_antisymm
  · intro p hp
    change p = 0
    apply Subtype.ext
    apply Prod.ext
    · exact hp.1
    · exact hp.2
  · exact bot_le

theorem augmentationIdeal_eq_sup :
    augmentationIdeal εA εB = fstIdeal εA εB ⊔ sndIdeal εA εB := by
  apply le_antisymm
  · intro p hp
    have hA : εA p.1.1 = 0 := hp
    have hB : εB p.1.2 = 0 := by
      calc
        εB p.1.2 = εA p.1.1 :=
          (show εA p.1.1 = εB p.1.2 from condition εA εB p).symm
        _ = 0 := hA
    let pA : P := ⟨(p.1.1, 0), by simp [hA]⟩
    let pB : P := ⟨(0, p.1.2), by simp [hB]⟩
    have hpA : pA ∈ sndIdeal εA εB := by
      change snd εA εB pA = 0
      simp [pA]
    have hpB : pB ∈ fstIdeal εA εB := by
      change fst εA εB pB = 0
      simp [pB]
    have hdecomp : p = pA + pB := by
      apply Subtype.ext
      apply Prod.ext <;> simp [pA, pB]
    rw [hdecomp]
    exact add_mem (Ideal.mem_sup_right hpA) (Ideal.mem_sup_left hpB)
  · apply sup_le
    · intro p hp
      have hp' : fst εA εB p = 0 := hp
      change εA (fst εA εB p) = 0
      rw [hp']
      exact map_zero _
    · intro p hp
      have hp' : snd εA εB p = 0 := hp
      change εA p.1.1 = 0
      calc
        εA p.1.1 = εB p.1.2 := condition εA εB p
        _ = 0 := by
          have hzero : p.1.2 = 0 := by simpa [snd_apply] using hp'
          rw [hzero]
          exact map_zero _

theorem prime_mem_fstIdeal_or_sndIdeal (p : PrimeSpectrum P) :
    fstIdeal εA εB ≤ p.asIdeal ∨ sndIdeal εA εB ≤ p.asIdeal := by
  apply (Ideal.IsPrime.mul_le p.2).mp
  rw [fstIdeal_mul_sndIdeal]
  exact bot_le

/-! ## Closed branch images and their cover -/

theorem range_specFst :
    Set.range (PrimeSpectrum.comap (fst εA εB).toRingHom) =
      PrimeSpectrum.zeroLocus (fstIdeal εA εB : Set P) := by
  exact range_comap_of_surjective _ (fst εA εB).toRingHom (fst_surjective εA εB)

theorem range_specSnd :
    Set.range (PrimeSpectrum.comap (snd εA εB).toRingHom) =
      PrimeSpectrum.zeroLocus (sndIdeal εA εB : Set P) := by
  exact range_comap_of_surjective _ (snd εA εB).toRingHom (snd_surjective εA εB)

theorem range_specAugmentation :
    Set.range (PrimeSpectrum.comap (augmentation εA εB).toRingHom) =
      PrimeSpectrum.zeroLocus (augmentationIdeal εA εB : Set P) := by
  exact range_comap_of_surjective _ (augmentation εA εB).toRingHom
    (augmentation_surjective εA εB)

theorem branch_ranges_cover :
    Set.range (PrimeSpectrum.comap (fst εA εB).toRingHom) ∪
      Set.range (PrimeSpectrum.comap (snd εA εB).toRingHom) = Set.univ := by
  rw [range_specFst, range_specSnd, ← PrimeSpectrum.zeroLocus_inf,
    fstIdeal_inf_sndIdeal, PrimeSpectrum.zeroLocus_bot]

theorem scheme_branch_ranges_cover :
    Set.range (specFst εA εB).base ∪ Set.range (specSnd εA εB).base = Set.univ := by
  change Set.range (PrimeSpectrum.comap (fst εA εB).toRingHom) ∪
      Set.range (PrimeSpectrum.comap (snd εA εB).toRingHom) = Set.univ
  exact branch_ranges_cover εA εB

theorem branch_ranges_intersect :
    Set.range (PrimeSpectrum.comap (fst εA εB).toRingHom) ∩
      Set.range (PrimeSpectrum.comap (snd εA εB).toRingHom) =
      PrimeSpectrum.zeroLocus (augmentationIdeal εA εB : Set P) := by
  rw [range_specFst, range_specSnd, ← PrimeSpectrum.zeroLocus_sup,
    augmentationIdeal_eq_sup]

theorem scheme_branch_ranges_intersect :
    Set.range (specFst εA εB).base ∩ Set.range (specSnd εA εB).base =
      PrimeSpectrum.zeroLocus (augmentationIdeal εA εB : Set P) := by
  change Set.range (PrimeSpectrum.comap (fst εA εB).toRingHom) ∩
      Set.range (PrimeSpectrum.comap (snd εA εB).toRingHom) = _
  exact branch_ranges_intersect εA εB

theorem branch_ranges_intersect_eq_common_section :
    Set.range (PrimeSpectrum.comap (fst εA εB).toRingHom) ∩
      Set.range (PrimeSpectrum.comap (snd εA εB).toRingHom) =
      Set.range (PrimeSpectrum.comap (augmentation εA εB).toRingHom) := by
  rw [branch_ranges_intersect, range_specAugmentation]

/-! ## Affine-target gluing -/

/-- The affine morphism induced by a compatible pair of maps to the two branches. -/
def specGluedMap (f : Q →ₐ[R] A) (g : Q →ₐ[R] B)
    (h : εA.comp f = εB.comp g) :
    Spec (.of P) ⟶ Spec (.of Q) :=
  Scheme.Spec.map (CommRingCat.ofHom (lift εA εB f g h).toRingHom).op

@[reassoc (attr := simp)]
theorem specGluedMap_fst (f : Q →ₐ[R] A) (g : Q →ₐ[R] B)
    (h : εA.comp f = εB.comp g) :
      specFst εA εB ≫ specGluedMap εA εB f g h =
      Scheme.Spec.map (CommRingCat.ofHom f.toRingHom).op := by
  change Scheme.Spec.map (CommRingCat.ofHom (fst εA εB).toRingHom).op ≫
      Scheme.Spec.map (CommRingCat.ofHom (lift εA εB f g h).toRingHom).op = _
  rw [← Scheme.Spec.map_comp]
  congr 1

@[reassoc (attr := simp)]
theorem specGluedMap_snd (f : Q →ₐ[R] A) (g : Q →ₐ[R] B)
    (h : εA.comp f = εB.comp g) :
      specSnd εA εB ≫ specGluedMap εA εB f g h =
      Scheme.Spec.map (CommRingCat.ofHom g.toRingHom).op := by
  change Scheme.Spec.map (CommRingCat.ofHom (snd εA εB).toRingHom).op ≫
      Scheme.Spec.map (CommRingCat.ofHom (lift εA εB f g h).toRingHom).op = _
  rw [← Scheme.Spec.map_comp]
  congr 1

theorem specGluedMap_unique (f : Q →ₐ[R] A) (g : Q →ₐ[R] B)
    (h : εA.comp f = εB.comp g) (u : Spec (.of P) ⟶ Spec (.of Q))
    (huA : specFst εA εB ≫ u = Scheme.Spec.map (CommRingCat.ofHom f.toRingHom).op)
    (huB : specSnd εA εB ≫ u = Scheme.Spec.map (CommRingCat.ofHom g.toRingHom).op) :
    u = specGluedMap εA εB f g h := by
  rw [← Scheme.Spec.map_preimage u]
  change Scheme.Spec.map (Scheme.Spec.preimage u) =
    Scheme.Spec.map (CommRingCat.ofHom (lift εA εB f g h).toRingHom).op
  congr 1
  have hA := congrArg Scheme.Spec.preimage huA
  have hB := congrArg Scheme.Spec.preimage huB
  have hA' : (CommRingCat.ofHom (fst εA εB).toRingHom).op ≫
      Scheme.Spec.preimage u = (CommRingCat.ofHom f.toRingHom).op := by
    simpa only [specFst, Scheme.Spec.preimage_comp, Scheme.Spec.preimage_map] using hA
  have hB' : (CommRingCat.ofHom (snd εA εB).toRingHom).op ≫
      Scheme.Spec.preimage u = (CommRingCat.ofHom g.toRingHom).op := by
    simpa only [specSnd, Scheme.Spec.preimage_comp, Scheme.Spec.preimage_map] using hB
  have hA'' := congrArg Quiver.Hom.unop hA'
  have hB'' := congrArg Quiver.Hom.unop hB'
  apply Quiver.Hom.unop_inj
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  have hpair := congrArg (fun k => k q) hA''
  have hpair' := congrArg (fun k => k q) hB''
  apply Subtype.ext
  apply Prod.ext
  · exact hpair
  · exact hpair'

end fiberProduct
end
end Clutching
end Curves
end AlgebraicGeometry
end GromovWitten
