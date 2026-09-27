/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.SquareZeroSource
import Mathlib.CategoryTheory.Equivalence

/-!
# Functoriality of square-zero lifting groupoids

Restriction along a compatible map of source algebras preserves the automorphism of the fixed
square-zero extension and precomposes its intertwining equation.  It is faithful for every source
map, full for a surjective source map, and an equivalence for an isomorphism of source algebras.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace SquareZero

open CategoryTheory

universe u v w w' w''

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
variable (M : Ideal B) [IsSquareZero M]

section Source

variable {A : Type w} {A' : Type w'} {A'' : Type w''}
variable [CommRing A] [CommRing A'] [CommRing A'']
variable [Algebra R A] [Algebra R A'] [Algebra R A'']
variable [Algebra A (B ⧸ M)] [Algebra A' (B ⧸ M)] [Algebra A'' (B ⧸ M)]
variable [IsScalarTower R A (B ⧸ M)] [IsScalarTower R A' (B ⧸ M)]
  [IsScalarTower R A'' (B ⧸ M)]

namespace SourceMap

/-- The algebra equivalence determined by a bijective compatible source map. -/
noncomputable def algEquivOfBijective (f : SourceMap R M A A')
    (hf : Function.Bijective f.hom) : A ≃ₐ[R] A' :=
  AlgEquiv.ofBijective f.hom hf

/-- The inverse compatible source map determined by a bijective source map. -/
noncomputable def inverse (f : SourceMap R M A A') (hf : Function.Bijective f.hom) :
    SourceMap R M A' A where
  hom := (algEquivOfBijective M f hf).symm.toAlgHom
  commutes := by
    ext a'
    obtain ⟨a, ha⟩ := hf.2 a'
    rw [← ha]
    change algebraMap A (B ⧸ M) ((algEquivOfBijective M f hf).symm (f.hom a)) =
      algebraMap A' (B ⧸ M) (f.hom a)
    have he : (algEquivOfBijective M f hf).symm (f.hom a) = a := by
      change (algEquivOfBijective M f hf).symm (algEquivOfBijective M f hf a) = a
      exact (algEquivOfBijective M f hf).symm_apply_apply a
    rw [he]
    exact (congrArg (fun k => k a) f.commutes).symm

omit [IsSquareZero M] [IsScalarTower R A (B ⧸ M)] [IsScalarTower R A' (B ⧸ M)] in
@[simp]
theorem inverse_hom (f : SourceMap R M A A') (hf : Function.Bijective f.hom) :
    (inverse M f hf).hom = (algEquivOfBijective M f hf).symm.toAlgHom :=
  rfl

omit [IsSquareZero M] [IsScalarTower R A (B ⧸ M)] [IsScalarTower R A' (B ⧸ M)] in
@[simp]
theorem inverse_comp (f : SourceMap R M A A') (hf : Function.Bijective f.hom) :
    (inverse M f hf).comp f = SourceMap.id (R := R) (M := M) (A := A) := by
  apply SourceMap.ext
  ext a
  exact (algEquivOfBijective M f hf).symm_apply_apply a

omit [IsSquareZero M] [IsScalarTower R A (B ⧸ M)] [IsScalarTower R A' (B ⧸ M)] in
@[simp]
theorem comp_inverse (f : SourceMap R M A A') (hf : Function.Bijective f.hom) :
    f.comp (inverse M f hf) = SourceMap.id (R := R) (M := M) (A := A') := by
  apply SourceMap.ext
  ext a'
  exact (algEquivOfBijective M f hf).apply_symm_apply a'

end SourceMap

/-- Restriction of the square-zero lifting groupoid along a compatible source map. -/
def restrictFunctor (f : SourceMap R M A A') : Lift R M A' ⥤ Lift R M A where
  obj F := SourceMap.restrictLift f F
  map {F G} α :=
    { aut := α.aut
      aut_hom := fun a => by
        change α.aut.hom (F.hom (f.hom a)) = G.hom (f.hom a)
        exact α.aut_hom (f.hom a) }
  map_id _ := by
    apply LiftHom.ext
    rfl
  map_comp _ _ := by
    apply LiftHom.ext
    rfl

@[simp]
theorem restrictFunctor_obj (f : SourceMap R M A A') (F : Lift R M A') :
    (restrictFunctor M f).obj F = SourceMap.restrictLift f F :=
  rfl

@[simp]
theorem restrictFunctor_map_aut (f : SourceMap R M A A') {F G : Lift R M A'}
    (α : F ⟶ G) : ((restrictFunctor M f).map α).aut = α.aut :=
  rfl

@[simp]
theorem lift_eqToHom_aut {F G : Lift R M A} (h : F = G) :
    (eqToHom h : F ⟶ G).aut = 1 := by
  cases h
  rfl

@[simp]
theorem restrictFunctor_map_hom (f : SourceMap R M A A') {F G : Lift R M A'}
    (α : F ⟶ G) (a : A) :
    ((restrictFunctor M f).map α).aut.hom (((restrictFunctor M f).obj F).hom a) =
      ((restrictFunctor M f).obj G).hom a := by
  exact α.aut_hom (f.hom a)

/-- Restriction is faithful because it leaves the extension automorphism unchanged. -/
instance restrictFunctor_faithful (f : SourceMap R M A A') :
    (restrictFunctor M f).Faithful where
  map_injective {F G} α β h := by
    apply LiftHom.ext
    exact congrArg (fun γ : (restrictFunctor M f).obj F ⟶ (restrictFunctor M f).obj G => γ.aut) h

/-- Restriction is full when the source algebra map is surjective. -/
theorem restrictFunctor_full (f : SourceMap R M A A') (hf : Function.Surjective f.hom) :
    (restrictFunctor M f).Full where
  map_surjective {F G} α := by
    let β : F ⟶ G :=
      { aut := α.aut
        aut_hom := fun a' => by
          obtain ⟨a, rfl⟩ := hf a'
          exact α.aut_hom a }
    refine ⟨β, ?_⟩
    apply LiftHom.ext
    rfl

/-- Restriction along the identity source map is naturally isomorphic to the identity functor. -/
noncomputable def restrictFunctor_idIso :
    restrictFunctor M (SourceMap.id (R := R) (M := M) (A := A)) ≅ 𝟭 (Lift R M A) :=
  NatIso.ofComponents (fun F =>
    eqToIso (SourceMap.restrictLift_id (M := M) F)) (by
      intro F G α
      apply LiftHom.ext
      rfl)

/-- Restriction is compatible with composition of source maps. -/
noncomputable def restrictFunctor_compIso (f : SourceMap R M A A')
    (g : SourceMap R M A' A'') :
    restrictFunctor M g ⋙ restrictFunctor M f ≅
      restrictFunctor M (g.comp f) :=
  NatIso.ofComponents (fun F =>
    eqToIso (SourceMap.restrictLift_comp (M := M) g f F)) (by
      intro F G α
      apply LiftHom.ext
      rfl)

/-- A bijective compatible source map gives essential surjectivity by restricting with its
inverse source map. -/
theorem restrictFunctor_essSurj (f : SourceMap R M A A')
    (hf : Function.Bijective f.hom) :
    (restrictFunctor M f).EssSurj where
  mem_essImage F := by
    refine ⟨SourceMap.restrictLift (SourceMap.inverse M f hf) F, ?_⟩
    exact ⟨eqToIso (by
      calc
        SourceMap.restrictLift f
            (SourceMap.restrictLift (SourceMap.inverse M f hf) F) =
            SourceMap.restrictLift ((SourceMap.inverse M f hf).comp f) F := by
              exact SourceMap.restrictLift_comp (M := M)
                (SourceMap.inverse M f hf) f F
        _ = SourceMap.restrictLift (SourceMap.id (R := R) (M := M) (A := A)) F := by
              rw [SourceMap.inverse_comp M f hf]
        _ = F := SourceMap.restrictLift_id (M := M) F)⟩

/-- A compatible source algebra isomorphism induces an equivalence of lifting groupoids. -/
theorem restrictFunctor_isEquivalence (f : SourceMap R M A A')
    (hf : Function.Bijective f.hom) :
    (restrictFunctor M f).IsEquivalence := by
  let : (restrictFunctor M f).Full := restrictFunctor_full M f hf.2
  let : (restrictFunctor M f).EssSurj := restrictFunctor_essSurj M f hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The equivalence induced by an isomorphism of compatible source algebras. -/
noncomputable def restrictEquivalence (f : SourceMap R M A A')
    (hf : Function.Bijective f.hom) : Lift R M A' ≌ Lift R M A := by
  letI := restrictFunctor_isEquivalence M f hf
  exact (restrictFunctor M f).asEquivalence

/-- The derivation describing an extension automorphism restricts compatibly with the source. -/
theorem autDerivationMap_restrict (f : SourceMap R M A A')
    (d : Derivation R (B ⧸ M) (Coeff M)) :
    SourceMap.restrictDer f (autDerivationMap R M A' d) = autDerivationMap R M A d := by
  apply Derivation.ext
  intro a
  change d (algebraMap A' (B ⧸ M) (f.hom a)) = d (algebraMap A (B ⧸ M) a)
  exact congrArg d (congrArg (fun k => k a) f.commutes)

/-- Restriction embeds the kernel describing lift automorphisms into the source kernel. -/
def restrictAutKernel (f : SourceMap R M A A') :
    (autDerivationMap R M A').ker →+ (autDerivationMap R M A).ker where
  toFun d := ⟨d.1, by
    rw [AddMonoidHom.mem_ker, ← autDerivationMap_restrict M f d.1]
    have hd : autDerivationMap R M A' d.1 = 0 := d.2
    rw [hd]
    apply Derivation.ext
    intro a
    rfl⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The automorphism-kernel description commutes with the actual restriction functor. -/
theorem endEquivKer_restrict (f : SourceMap R M A A') (F : Lift R M A') (α : F ⟶ F) :
    endEquivKer M ((restrictFunctor M f).obj F) ((restrictFunctor M f).map α) =
      restrictAutKernel M f (endEquivKer M F α) := rfl

end Source

end SquareZero

end GromovWitten.AlgebraicGeometry.CotangentComplex
