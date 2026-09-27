/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.Curves.Clutching.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The affine-local model of contracting one branch of a clutched curve

Let `P = A ×_R B` be the affine pinching ring of two `R`-algebras equipped with augmentations
`εA : A →ₐ[R] R` and `εB : B →ₐ[R] R` (`Curves/Clutching/Affine.lean`,
`Curves/Clutching/AffineScheme.lean`). This file constructs the morphism
`contractBranchB εA εB : Spec P ⟶ Spec A` that is the identity on the `A`-branch and collapses
the `B`-branch onto the augmentation point of `Spec A`, and records the theorems that make it the
affine-local model of the fields of `Curves.StableMaps.Contraction`
(`Curves/StableMaps/Geometry.lean:802`):

* `contractBranchB_specFst` models the isomorphism away from the contracted locus, applied to the
  branch that survives untouched.
* `contractBranchB_contracts` models the `contracts` field: the exceptional `B`-branch is mapped
  into the augmentation locus of `Spec A`.
* `contractBranchB_fiber_augmentation` computes the exceptional fibre exactly (rather than only
  proving it is connected, as `Contraction.connectedFibers` does): the preimage of the
  augmentation locus is exactly the `B`-branch.
* `contractBranchBRestrictHomeomorph` models `complementIso` at the level of underlying spaces:
  a homeomorphism between the open complement of the `B`-branch and the open complement of the
  augmentation locus, inverse to the restriction of `specFst`.
* `isIso_stalkMap_contractBranchB_of_notMem` upgrades this to stalks: away from the `B`-branch
  (`sndIdeal εA εB ⊄ p`), `contractBranchB`'s stalk map at `p` is an isomorphism. The algebraic
  key is `fstIdeal εA εB * sndIdeal εA εB = ⊥` (`fstIdeal_mul_sndIdeal`): some `k` in the
  `B`-branch's defining ideal but not in `p` annihilates the `A`-branch's defining ideal, which
  forces the localization of `liftA` at `p` to be bijective (`liftALocal_bijective`).
* `isIso_morphismRestrict_contractBranchB` assembles the previous two into the full scheme-level
  statement: `contractBranchB` restricted to the open complement of the `B`-branch
  (`contractBranchB ∣_ augmentationOpen`) is an isomorphism of schemes onto `augmentationOpen`,
  the open complement of the augmentation locus. This is `complementIso` as an actual isomorphism
  of open subschemes, completing the affine-local model of `Contraction`'s geometric fields.

This is a purely affine, local statement, and it stops short of `Contraction` in two ways that
are not attempted here: (1) properness of `contractBranchB` is not addressed; (2) `connectedFibers`
for points other than the augmentation locus, and any global gluing/stabilization statement for
actual marked stable maps, are out of scope. `contractBranchB_bijOn` records the same bijection as
`contractBranchBRestrictHomeomorph`, phrased directly as a `Set.BijOn` on `Spec P`/`Spec A`.
-/

open _root_.AlgebraicGeometry
open CategoryTheory

namespace GromovWitten
namespace AlgebraicGeometry
namespace Curves
namespace Clutching
namespace fiberProduct

universe u

noncomputable section

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (εA : A →ₐ[R] R) (εB : B →ₐ[R] R)

local notation "P" => fiberProduct εA εB

/-- The algebra map used to collapse the `B`-branch onto the augmentation point: precompose the
constant section `Algebra.ofId R B` with `εA`. -/
def collapseB : A →ₐ[R] B := (Algebra.ofId R B).comp εA

@[simp]
theorem collapseB_apply (a : A) : collapseB εA a = algebraMap R B (εA a) := rfl

/-- The compatibility condition needed to glue the identity on `A` with `collapseB` into a map
out of the pinching ring. -/
theorem contractBranchB_compat :
    εA.comp (AlgHom.id R A) = εB.comp (collapseB εA) := by
  ext a
  simp [collapseB_apply, εB.commutes]

/-- The affine-local contraction of the `B`-branch: the morphism `Spec P ⟶ Spec A` that restricts
to the identity on the `A`-branch and sends the `B`-branch to the augmentation point. -/
def contractBranchB : Spec (.of P) ⟶ Spec (.of A) :=
  specGluedMap εA εB (AlgHom.id R A) (collapseB εA) (contractBranchB_compat εA εB)

/-- The underlying algebra map of `contractBranchB`, used for the stalk-level computations below:
identity on `A`'s image, `collapseB` on the rest. -/
abbrev liftA : A →ₐ[R] P :=
  lift εA εB (AlgHom.id R A) (collapseB εA) (contractBranchB_compat εA εB)

/-- `contractBranchB` is literally `Spec.map` of its underlying ring map `liftA`. -/
theorem contractBranchB_eq_specMap :
    contractBranchB εA εB = Spec.map (CommRingCat.ofHom (liftA εA εB).toRingHom) :=
  rfl

/-- `liftA` is a one-sided inverse of `fst` up to `fstIdeal`: for every `x : P`,
`liftA (fst x) - x` lies in `fstIdeal εA εB`. This is the algebraic key fact driving the
stalk-level isomorphism away from the `B`-branch. -/
theorem sub_mem_fstIdeal (x : P) : liftA εA εB (fst εA εB x) - x ∈ fstIdeal εA εB := by
  have h : fst εA εB (liftA εA εB (fst εA εB x)) = fst εA εB x :=
    DFunLike.congr_fun (lift_fst εA εB (AlgHom.id R A) (collapseB εA)
      (contractBranchB_compat εA εB)) (fst εA εB x)
  change fst εA εB (liftA εA εB (fst εA εB x) - x) = 0
  rw [map_sub, h, sub_self]

/-- `contractBranchB` restricts to the identity on the surviving `A`-branch: this is the
affine-local analogue of a `Contraction`'s isomorphism away from the contracted locus applied to
the trivial case of the whole branch that is not contracted. -/
@[simp]
theorem contractBranchB_specFst :
    specFst εA εB ≫ contractBranchB εA εB = 𝟙 (Spec (.of A)) := by
  rw [contractBranchB, specGluedMap_fst]
  rw [show (AlgHom.id R A).toRingHom = RingHom.id A from AlgHom.id_toRingHom R A]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from CommRingCat.ofHom_id]
  rw [show (𝟙 (CommRingCat.of A) : CommRingCat.of A ⟶ CommRingCat.of A).op
      = 𝟙 (Opposite.op (CommRingCat.of A)) from rfl]
  exact Scheme.Spec.map_id _

/-- `contractBranchB` sends the contracted `B`-branch to the ring map `collapseB εA`, i.e. through
`Spec R` into the augmentation point of `Spec A`. -/
theorem contractBranchB_specSnd :
    specSnd εA εB ≫ contractBranchB εA εB =
      Scheme.Spec.map (CommRingCat.ofHom (collapseB εA).toRingHom).op := by
  rw [contractBranchB, specGluedMap_snd]

/-- `contractBranchB` maps the exceptional `B`-branch into the augmentation locus of `Spec A`:
the affine-local analogue of the `contracts` field of `Curves.StableMaps.Contraction`. -/
theorem contractBranchB_contracts :
    Set.MapsTo (contractBranchB εA εB).base
      (Set.range (specSnd εA εB).base) (Set.range (sectionA εA).base) := by
  rintro _ ⟨b, rfl⟩
  rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, contractBranchB_specSnd]
  exact ⟨PrimeSpectrum.comap (algebraMap R B) b,
    PrimeSpectrum.comap_comp_apply εA.toRingHom (algebraMap R B) b⟩

/-- Every augmentation is surjective, since it splits the structure map. -/
theorem εA_surjective : Function.Surjective εA.toRingHom :=
  fun r => ⟨algebraMap R A r, εA.commutes r⟩

/-- The lift ring map sends `ker εA` onto `sndIdeal εA εB` exactly. -/
theorem image_ker_eq_sndIdeal :
    (lift εA εB (AlgHom.id R A) (collapseB εA) (contractBranchB_compat εA εB)).toRingHom
        '' (RingHom.ker εA.toRingHom : Set A)
      = (sndIdeal εA εB : Set P) := by
  set φ := lift εA εB (AlgHom.id R A) (collapseB εA) (contractBranchB_compat εA εB)
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ha, rfl⟩
    have ha' : εA a = 0 := ha
    change snd εA εB (φ a) = 0
    have hsnd : snd εA εB (φ a) = collapseB εA a :=
      DFunLike.congr_fun (lift_snd εA εB (AlgHom.id R A) (collapseB εA)
        (contractBranchB_compat εA εB)) a
    rw [hsnd, collapseB_apply, ha', map_zero]
  · intro q hq
    have hq' : snd εA εB q = 0 := hq
    refine ⟨fst εA εB q, ?_, ?_⟩
    · change εA (fst εA εB q) = 0
      rw [condition εA εB q, hq', map_zero]
    · have hfst : fst εA εB (φ (fst εA εB q)) = fst εA εB q :=
        DFunLike.congr_fun (lift_fst εA εB (AlgHom.id R A) (collapseB εA)
          (contractBranchB_compat εA εB)) (fst εA εB q)
      have hsnd : snd εA εB (φ (fst εA εB q)) = collapseB εA (fst εA εB q) :=
        DFunLike.congr_fun (lift_snd εA εB (AlgHom.id R A) (collapseB εA)
          (contractBranchB_compat εA εB)) (fst εA εB q)
      have hsnd0 : snd εA εB (φ (fst εA εB q)) = 0 := by
        rw [hsnd, collapseB_apply]
        rw [condition εA εB q, hq', map_zero, map_zero]
      exact Subtype.ext (Prod.ext hfst (hsnd0.trans hq'.symm))

/-- The fibre of `contractBranchB` over the augmentation locus of `Spec A` is exactly the
contracted `B`-branch: the affine-local analogue of computing the exceptional fibre of a
`Contraction` exactly (rather than only its connectedness). -/
theorem contractBranchB_fiber_augmentation :
    (contractBranchB εA εB).base ⁻¹' Set.range (sectionA εA).base
      = Set.range (specSnd εA εB).base := by
  change PrimeSpectrum.comap
      (lift εA εB (AlgHom.id R A) (collapseB εA) (contractBranchB_compat εA εB)).toRingHom ⁻¹'
      Set.range (PrimeSpectrum.comap εA.toRingHom)
    = Set.range (PrimeSpectrum.comap (snd εA εB).toRingHom)
  rw [range_comap_of_surjective _ εA.toRingHom (εA_surjective εA),
    PrimeSpectrum.preimage_comap_zeroLocus, image_ker_eq_sndIdeal]
  exact (range_specSnd εA εB).symm

/-- The `fst` ring map sends `sndIdeal εA εB` onto `ker εA` exactly: the mirror image computation
to `image_ker_eq_sndIdeal`, needed to invert `contractBranchB` away from the two loci. -/
theorem image_sndIdeal_eq_ker :
    (fst εA εB).toRingHom '' (sndIdeal εA εB : Set P)
      = (RingHom.ker εA.toRingHom : Set A) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : snd εA εB q = 0 := hq
    change εA (fst εA εB q) = 0
    rw [condition εA εB q, hq', map_zero]
  · intro a ha
    have ha' : εA a = 0 := ha
    have hcond : εA a = εB (algebraMap R B (εA a)) := by rw [ha', map_zero, map_zero]
    refine ⟨⟨(a, algebraMap R B (εA a)), hcond⟩, ?_, rfl⟩
    change algebraMap R B (εA a) = 0
    rw [ha', map_zero]

/-- `specFst` sends the preimage of the exceptional `B`-branch into the augmentation locus of
`Spec A`; equivalently, the augmentation locus is exactly where `specFst` lands inside the
`B`-branch's preimage. The mirror image statement to `contractBranchB_fiber_augmentation`. -/
theorem specFst_fiber_branch :
    (specFst εA εB).base ⁻¹' Set.range (specSnd εA εB).base
      = Set.range (sectionA εA).base := by
  change PrimeSpectrum.comap (fst εA εB).toRingHom ⁻¹'
      Set.range (PrimeSpectrum.comap (snd εA εB).toRingHom)
    = Set.range (PrimeSpectrum.comap εA.toRingHom)
  rw [range_specSnd, PrimeSpectrum.preimage_comap_zeroLocus, image_sndIdeal_eq_ker]
  exact (range_comap_of_surjective _ εA.toRingHom (εA_surjective εA)).symm

/-- `contractBranchB` maps the open complement of the `B`-branch into the open complement of the
augmentation locus. -/
theorem contractBranchB_mapsTo_compl :
    Set.MapsTo (contractBranchB εA εB).base
      (Set.range (specSnd εA εB).base)ᶜ (Set.range (sectionA εA).base)ᶜ := by
  intro p hp hmem
  apply hp
  rw [← contractBranchB_fiber_augmentation]
  exact hmem

/-- `specFst` maps the open complement of the augmentation locus into the open complement of the
`B`-branch. -/
theorem specFst_mapsTo_compl :
    Set.MapsTo (specFst εA εB).base
      (Set.range (sectionA εA).base)ᶜ (Set.range (specSnd εA εB).base)ᶜ := by
  intro a ha hmem
  apply ha
  rw [← specFst_fiber_branch εA εB]
  exact hmem

/-- `contractBranchB`, restricted to the underlying topological space of the open complement of
the `B`-branch, is a homeomorphism onto the open complement of the augmentation locus of `Spec A`,
with inverse the restriction of `specFst`: the topological-space-level model of a `Contraction`'s
isomorphism away from the exceptional locus. (This is a homeomorphism of underlying spaces, not
an isomorphism of schemes: upgrading it further would additionally require matching the induced
maps on stalks/structure sheaves on the two open loci, which is not attempted here.) -/
def contractBranchBRestrictHomeomorph :
    ↥(Set.range (specSnd εA εB).base)ᶜ ≃ₜ ↥(Set.range (sectionA εA).base)ᶜ where
  toFun := (contractBranchB_mapsTo_compl εA εB).restrict _ _ _
  invFun := (specFst_mapsTo_compl εA εB).restrict _ _ _
  left_inv p := by
    apply Subtype.ext
    simp only [Set.MapsTo.restrict, Subtype.map]
    have hcover : p.1 ∈ Set.range (specFst εA εB).base ∪ Set.range (specSnd εA εB).base := by
      rw [scheme_branch_ranges_cover]; trivial
    rcases hcover with ⟨a, ha⟩ | h
    · have hpt : (contractBranchB εA εB).base ((specFst εA εB).base a) = a := by
        rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, contractBranchB_specFst]
        rfl
      rw [← ha, hpt]
    · exact absurd h p.2
  right_inv a := by
    apply Subtype.ext
    simp only [Set.MapsTo.restrict, Subtype.map]
    rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, contractBranchB_specFst]
    rfl
  continuous_toFun :=
    Continuous.restrict (contractBranchB_mapsTo_compl εA εB) (contractBranchB εA εB).continuous
  continuous_invFun :=
    Continuous.restrict (specFst_mapsTo_compl εA εB) (specFst εA εB).continuous

/-! ## Upgrading the homeomorphism to a stalk isomorphism away from the two loci

For `p : PrimeSpectrum P` off the `B`-branch (`sndIdeal εA εB ⊄ p.asIdeal`), some `k` in
`sndIdeal εA εB` is not in `p`; since `fstIdeal εA εB * sndIdeal εA εB = ⊥`
(`fstIdeal_mul_sndIdeal`), `k` annihilates `fstIdeal εA εB`, which drives an isomorphism of local
rings `P_p ≅ A_{p'}` where `p' := comap liftA p`, matching the stalk map of `contractBranchB`. -/

/-- Off the `B`-branch, `p` contains `fstIdeal εA εB`. -/
theorem fstIdeal_le_of_notMem {p : PrimeSpectrum P} (hp : ¬ sndIdeal εA εB ≤ p.asIdeal) :
    fstIdeal εA εB ≤ p.asIdeal :=
  (prime_mem_fstIdeal_or_sndIdeal εA εB p).resolve_right hp

/-- Off the `B`-branch, `p` is exactly the preimage under `fst` of the point `liftA`
associates to it: the `hIJ`-shaped equality needed to localize `fst` at `(p, comap liftA p)`. -/
theorem comap_fst_eq_of_notMem {p : PrimeSpectrum P} (hp : ¬ sndIdeal εA εB ≤ p.asIdeal) :
    p.asIdeal = (PrimeSpectrum.comap (liftA εA εB).toRingHom p).asIdeal.comap
      (fst εA εB).toRingHom := by
  have hJ := fstIdeal_le_of_notMem εA εB hp
  apply le_antisymm
  · intro x hx
    change liftA εA εB (fst εA εB x) ∈ p.asIdeal
    have hd := sub_mem_fstIdeal εA εB x
    have := Ideal.add_mem p.asIdeal (hJ hd) hx
    rwa [sub_add_cancel] at this
  · intro x hx
    change liftA εA εB (fst εA εB x) ∈ p.asIdeal at hx
    have hd := sub_mem_fstIdeal εA εB x
    have := Ideal.sub_mem p.asIdeal hx (hJ hd)
    rwa [sub_sub_cancel] at this

/-- The image prime of `p` in `Spec A`, i.e. the point `contractBranchB` sends `p` to. -/
abbrev imagePrime {p : PrimeSpectrum P} (_hp : ¬ sndIdeal εA εB ≤ p.asIdeal) :
    PrimeSpectrum A :=
  PrimeSpectrum.comap (liftA εA εB).toRingHom p

/-- Localizing `liftA` at `(imagePrime hp, p)`. -/
noncomputable abbrev liftALocal {p : PrimeSpectrum P} (hp : ¬ sndIdeal εA εB ≤ p.asIdeal) :
    Localization.AtPrime (imagePrime εA εB hp).asIdeal →+* Localization.AtPrime p.asIdeal :=
  Localization.localRingHom (imagePrime εA εB hp).asIdeal p.asIdeal (liftA εA εB).toRingHom rfl

/-- Localizing `fst` at `(p, imagePrime hp)`. -/
noncomputable abbrev fstLocal {p : PrimeSpectrum P} (hp : ¬ sndIdeal εA εB ≤ p.asIdeal) :
    Localization.AtPrime p.asIdeal →+* Localization.AtPrime (imagePrime εA εB hp).asIdeal :=
  Localization.localRingHom p.asIdeal (imagePrime εA εB hp).asIdeal (fst εA εB).toRingHom
    (comap_fst_eq_of_notMem εA εB hp)

/-- Away from the `B`-branch, `fstLocal` retracts `liftALocal`: this holds for every `p`, with no
further hypothesis on `p` beyond well-definedness, since it comes from the global identity
`fst.comp liftA = id` (`lift_fst`). -/
theorem fstLocal_comp_liftALocal {p : PrimeSpectrum P} (hp : ¬ sndIdeal εA εB ≤ p.asIdeal) :
    (fstLocal εA εB hp).comp (liftALocal εA εB hp) = RingHom.id _ := by
  have hcompat : ∀ x : A,
      ((fstLocal εA εB hp).comp (liftALocal εA εB hp)) (algebraMap A _ x)
        = algebraMap A _ (RingHom.id A x) := by
    intro x
    have h1 : liftALocal εA εB hp (algebraMap A _ x) =
        algebraMap P _ (liftA εA εB x) :=
      Localization.localRingHom_to_map (imagePrime εA εB hp).asIdeal p.asIdeal
        (liftA εA εB).toRingHom rfl x
    have h2 : fstLocal εA εB hp (algebraMap P _ (liftA εA εB x)) =
        algebraMap A _ (fst εA εB (liftA εA εB x)) :=
      Localization.localRingHom_to_map p.asIdeal (imagePrime εA εB hp).asIdeal
        (fst εA εB).toRingHom (comap_fst_eq_of_notMem εA εB hp) (liftA εA εB x)
    rw [RingHom.comp_apply, h1, h2, RingHom.id_apply]
    congr 1
  have hu := Localization.localRingHom_unique (imagePrime εA εB hp).asIdeal
    (imagePrime εA εB hp).asIdeal (RingHom.id A) (Ideal.comap_id _).symm hcompat
  rw [Localization.localRingHom_id] at hu
  exact hu.symm

/-- Off the B-branch, `fstLocal` is injective: this is the genuinely new content, using that
some `k` in `sndIdeal εA εB`, not in `p`, annihilates `fstIdeal εA εB`
(via `fstIdeal_mul_sndIdeal`). -/
theorem fstLocal_injective {p : PrimeSpectrum P} (hp : ¬ sndIdeal εA εB ≤ p.asIdeal) :
    Function.Injective (fstLocal εA εB hp) := by
  rcases SetLike.not_le_iff_exists.mp hp with ⟨k, hkK, hkp⟩
  rw [injective_iff_map_eq_zero]
  intro y hy
  rcases IsLocalization.mk'_surjective p.asIdeal.primeCompl y with ⟨⟨x, s⟩, rfl⟩
  rw [fstLocal, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hy
  obtain ⟨⟨c, hc⟩, hcx⟩ := hy
  have hcp : liftA εA εB c ∉ p.asIdeal := by
    intro hcontra
    exact hc (Ideal.mem_comap.mpr hcontra)
  have hj : liftA εA εB (fst εA εB x) - x ∈ fstIdeal εA εB := sub_mem_fstIdeal εA εB x
  have hkj : k * (liftA εA εB (fst εA εB x) - x) = 0 := by
    have hmem : k * (liftA εA εB (fst εA εB x) - x) ∈ fstIdeal εA εB * sndIdeal εA εB :=
      Ideal.mul_mem_mul_rev hj hkK
    rw [fstIdeal_mul_sndIdeal] at hmem
    exact Ideal.mem_bot.mp hmem
  have h0 : liftA εA εB c * liftA εA εB (fst εA εB x) = 0 := by
    have hz := congrArg (liftA εA εB) hcx
    rwa [map_mul, map_zero] at hz
  have hux : (k * liftA εA εB c) * x = 0 := by
    linear_combination k * h0 - liftA εA εB c * hkj
  exact (IsLocalization.mk'_eq_zero_iff x s).mpr
    ⟨⟨k * liftA εA εB c, p.2.mul_notMem hkp hcp⟩, hux⟩

/-- Off the B-branch, `liftALocal` is bijective: injective because it has a left inverse
(`fstLocal_comp_liftALocal`), and surjective because `fstLocal`'s injectivity
(`fstLocal_injective`) lets the retraction identity be inverted at the point `fstLocal y`. -/
theorem liftALocal_bijective {p : PrimeSpectrum P} (hp : ¬ sndIdeal εA εB ≤ p.asIdeal) :
    Function.Bijective (liftALocal εA εB hp) := by
  have hinj : Function.Injective (liftALocal εA εB hp) := by
    refine Function.LeftInverse.injective (g := fstLocal εA εB hp) (fun z => ?_)
    have hz := DFunLike.congr_fun (fstLocal_comp_liftALocal εA εB hp) z
    rw [RingHom.comp_apply, RingHom.id_apply] at hz
    exact hz
  refine ⟨hinj, fun y => ⟨fstLocal εA εB hp y, ?_⟩⟩
  apply fstLocal_injective εA εB hp
  exact DFunLike.congr_fun (fstLocal_comp_liftALocal εA εB hp) (fstLocal εA εB hp y)

/-- Off the B-branch, `contractBranchB`'s stalk map is an isomorphism: the affine-local model of
the `complementIso` field of `Curves.StableMaps.Contraction` at the level of stalks, upgrading
`contractBranchBRestrictHomeomorph`; combined with `isIso_iff_isIso_stalkMap` it gives the
scheme-level isomorphism `isIso_morphismRestrict_contractBranchB` below. -/
theorem isIso_stalkMap_contractBranchB_of_notMem {p : PrimeSpectrum P}
    (hp : ¬ sndIdeal εA εB ≤ p.asIdeal) :
    IsIso ((contractBranchB εA εB).stalkMap p) := by
  have hbij : Function.Bijective (Localization.localRingHom
      (PrimeSpectrum.comap (liftA εA εB).toRingHom p).asIdeal p.asIdeal
      (liftA εA εB).toRingHom rfl) :=
    liftALocal_bijective εA εB hp
  have hiso : IsIso (CommRingCat.ofHom (Localization.localRingHom
      (PrimeSpectrum.comap (liftA εA εB).toRingHom p).asIdeal p.asIdeal
      (liftA εA εB).toRingHom rfl)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hstalk : (contractBranchB εA εB).stalkMap p =
      (Spec.stalkIso (CommRingCat.of A) (PrimeSpectrum.comap (liftA εA εB).toRingHom p)).hom ≫
        CommRingCat.ofHom (Localization.localRingHom
          (PrimeSpectrum.comap (liftA εA εB).toRingHom p).asIdeal p.asIdeal
          (liftA εA εB).toRingHom rfl) ≫
        (Spec.stalkIso (CommRingCat.of P) p).inv :=
    (Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom (liftA εA εB).toRingHom) p).symm
  exact hstalk ▸ (inferInstance :
    IsIso ((Spec.stalkIso (CommRingCat.of A) (PrimeSpectrum.comap (liftA εA εB).toRingHom p)).hom ≫
      CommRingCat.ofHom (Localization.localRingHom
        (PrimeSpectrum.comap (liftA εA εB).toRingHom p).asIdeal p.asIdeal
        (liftA εA εB).toRingHom rfl) ≫
      (Spec.stalkIso (CommRingCat.of P) p).inv))

/-! ## Packaging as a scheme isomorphism away from the two loci -/

instance sectionA_isClosedImmersion : IsClosedImmersion (sectionA εA) :=
  IsClosedImmersion.spec_of_surjective _ (εA_surjective εA)

/-- The open complement of the augmentation locus in `Spec A`. -/
def augmentationOpen : (Spec (.of A)).Opens :=
  ⟨(Set.range (sectionA εA).base)ᶜ, (sectionA εA).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The open complement of the `B`-branch in `Spec P`. -/
def branchOpen : (Spec (.of P)).Opens :=
  ⟨(Set.range (specSnd εA εB).base)ᶜ, (specSnd εA εB).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The preimage of `augmentationOpen` under `contractBranchB` is exactly `branchOpen`. -/
theorem preimage_augmentationOpen :
    contractBranchB εA εB ⁻¹ᵁ augmentationOpen εA = branchOpen εA εB := by
  apply TopologicalSpace.Opens.ext
  change (contractBranchB εA εB).base ⁻¹' (Set.range (sectionA εA).base)ᶜ
      = (Set.range (specSnd εA εB).base)ᶜ
  rw [Set.preimage_compl, contractBranchB_fiber_augmentation]

/-- `contractBranchB` restricts to a genuine bijection of *sets* from `branchOpen` onto
`augmentationOpen`: the same content as `contractBranchBRestrictHomeomorph`, phrased as a
`Set.BijOn` on `Spec P`/`Spec A` themselves rather than on the corresponding subtypes (the
scheme-level isomorphism below is assembled directly from the homeomorphism instead). -/
theorem contractBranchB_bijOn :
    Set.BijOn (contractBranchB εA εB).base (branchOpen εA εB).1 (augmentationOpen εA).1 := by
  refine ⟨contractBranchB_mapsTo_compl εA εB, ?_, ?_⟩
  · intro p hp q hq hpq
    have hcoverp : p ∈ Set.range (specFst εA εB).base ∪ Set.range (specSnd εA εB).base := by
      rw [scheme_branch_ranges_cover]; trivial
    have hcoverq : q ∈ Set.range (specFst εA εB).base ∪ Set.range (specSnd εA εB).base := by
      rw [scheme_branch_ranges_cover]; trivial
    rcases hcoverp with ⟨a, ha⟩ | h
    · rcases hcoverq with ⟨b, hb⟩ | h
      · have hpta : (contractBranchB εA εB).base ((specFst εA εB).base a) = a := by
          rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, contractBranchB_specFst]; rfl
        have hptb : (contractBranchB εA εB).base ((specFst εA εB).base b) = b := by
          rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, contractBranchB_specFst]; rfl
        rw [← ha, ← hb, hpta, hptb] at hpq
        rw [← ha, ← hb, hpq]
      · exact absurd h hq
    · exact absurd h hp
  · intro y hy
    refine ⟨(specFst εA εB).base y, ?_, ?_⟩
    · intro hmem
      exact hy ((specFst_fiber_branch εA εB ▸ hmem :
        y ∈ Set.range (sectionA εA).base))
    · rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, contractBranchB_specFst]; rfl

/-- The preimage of `augmentationOpen` under `contractBranchB`, at the level of sets: the same
fact as `preimage_augmentationOpen`, one level down (needed to transport
`contractBranchBRestrictHomeomorph`). -/
theorem preimage_augmentationOpen_coe :
    (contractBranchB εA εB).base ⁻¹' (augmentationOpen εA).1 = (branchOpen εA εB).1 := by
  change (contractBranchB εA εB).base ⁻¹' (Set.range (sectionA εA).base)ᶜ
      = (Set.range (specSnd εA εB).base)ᶜ
  rw [Set.preimage_compl, contractBranchB_fiber_augmentation]

/-- The homeomorphism between the preimage of `augmentationOpen` and `augmentationOpen` itself,
transported from `contractBranchBRestrictHomeomorph` along `preimage_augmentationOpen_coe`. -/
noncomputable def contractBranchBPreimageHomeomorph :
    ↥((contractBranchB εA εB).base ⁻¹' (augmentationOpen εA).1) ≃ₜ ↥(augmentationOpen εA).1 :=
  (Homeomorph.setCongr (preimage_augmentationOpen_coe εA εB)).trans
    (contractBranchBRestrictHomeomorph εA εB)

theorem coe_contractBranchBPreimageHomeomorph
    (x : ↥((contractBranchB εA εB).base ⁻¹' (augmentationOpen εA).1)) :
    (contractBranchBPreimageHomeomorph εA εB x).1 =
      (contractBranchB εA εB).base x.1 := rfl

/-- The restriction of `contractBranchB` to the open complement of the `B`-branch is a
homeomorphism onto `augmentationOpen`, at the level of `.base`. -/
theorem isIso_morphismRestrict_contractBranchB_base :
    IsIso (contractBranchB εA εB ∣_ augmentationOpen εA).base := by
  have heq : ⇑(contractBranchB εA εB ∣_ augmentationOpen εA) =
      ⇑(contractBranchBPreimageHomeomorph εA εB) := by
    rw [morphismRestrict_base]
    funext x
    exact Subtype.ext (coe_contractBranchBPreimageHomeomorph εA εB x).symm
  rw [TopCat.isIso_iff_isHomeomorph]
  exact heq ▸ (contractBranchBPreimageHomeomorph εA εB).isHomeomorph

/-- A point lies off the `B`-branch iff it lies in `branchOpen`. -/
theorem notMem_branchOpen_iff {q : PrimeSpectrum P} :
    q ∈ (branchOpen εA εB).1 ↔ ¬ sndIdeal εA εB ≤ q.asIdeal := by
  change q ∉ Set.range (PrimeSpectrum.comap (snd εA εB).toRingHom) ↔ _
  rw [range_specSnd, PrimeSpectrum.mem_zeroLocus]
  exact Iff.rfl

/-- `contractBranchB`, restricted to the open complement of the `B`-branch, is a genuine
isomorphism of schemes onto `augmentationOpen`: the full scheme-level model of the
`complementIso` field of `Curves.StableMaps.Contraction`. -/
theorem isIso_morphismRestrict_contractBranchB :
    IsIso (contractBranchB εA εB ∣_ augmentationOpen εA) := by
  rw [isIso_iff_isIso_stalkMap]
  refine ⟨isIso_morphismRestrict_contractBranchB_base εA εB, fun x => ?_⟩
  have hmem : x.1 ∈ (branchOpen εA εB).1 := by
    rw [← preimage_augmentationOpen_coe]
    exact x.2
  have hx : ¬ sndIdeal εA εB ≤ x.1.asIdeal := (notMem_branchOpen_iff εA εB).mp hmem
  have hiso : IsIso ((contractBranchB εA εB).stalkMap x.1) :=
    isIso_stalkMap_contractBranchB_of_notMem εA εB hx
  have e := Scheme.Hom.resLEStalkMap (contractBranchB εA εB)
    (U := augmentationOpen εA) (e := le_rfl) x
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) e).mpr hiso

end

end fiberProduct
end Clutching
end Curves
end AlgebraicGeometry
end GromovWitten
