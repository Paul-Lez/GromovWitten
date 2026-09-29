/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeOpenFiniteAffineBaseChange
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechQuasiIsoBaseChange
import GromovWitten.AlgebraicGeometry.FiniteAffineCover

/-!
# Canonical base change for finite affine covers

The fixed-resolution open-complex comparison on a finite affine cover gives
the canonical higher direct-image comparison in every degree.  The cover is
used only through its union being the whole source; the flat statement is a
specialization obtained by deriving exactness of the pullback along `p`.
-/

open CategoryTheory Limits AlgebraicGeometry HomologicalComplex
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
open Scheme.Modules
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The canonical higher direct-image base-change map is an isomorphism in
every degree for a finite affine-open cover of a separated locally Noetherian
source over an affine base. -/
lemma moduleHigherBaseChange_isIso_of_finiteAffineCover
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology]
    [IsAffine S] [X.IsSeparated] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent]
    (Us : List X.Opens) (hUs : ∀ U ∈ Us, IsAffineOpen U)
    (hcover : affineUnion Us = ⊤) (n : ℕ) :
    IsIso ((moduleHigherBaseChangeNatTrans s b p g h n).app M) := by
  let L := Scheme.Modules.pullback p
  let I := injectiveResolution M
  let J := injectiveResolution (L.obj M)
  let a : (CochainComplex.single₀ Y.Modules).obj (L.obj M) ⟶
      (L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
    (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι
  have ha : QuasiIso a := by
    dsimp only [a]
    infer_instance
  obtain ⟨φ, hφ, _⟩ := J.exists_desc_of_quasiIso a
  have hφ' : (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι ≫ φ = J.ι := by
    simpa only [a, Category.assoc] using hφ
  let _ : QuasiIso
      (relativeOpenComplexBaseChangeMap s b p g h.w φ (affineUnion Us)) :=
    relativeOpenComplexBaseChangeMap_quasiIso_of_finiteAffine
      s b p g h M φ hφ' Us hUs
  let _ : IsAffine (⊥ : X.Opens).toScheme := isAffineOpen_bot X
  let _ : QuasiIso
      (relativeOpenComplexBaseChangeMap s b p g h.w φ (⊥ : X.Opens)) :=
    relativeOpenComplexBaseChangeMap_quasiIso_of_affine
      s b p g h M φ hφ' (⊥ : X.Opens)
  let _ : QuasiIso
      (relativeOpenComplexBaseChangeMap s b p g h.w φ
        (affineUnion Us ⊓ (⊥ : X.Opens))) := by
    rw [inf_bot_eq]
    infer_instance
  have hcover' : affineUnion Us ⊔ (⊥ : X.Opens) = ⊤ := by
    simp [hcover]
  exact moduleHigherBaseChange_isIso_of_threeQuasiIso
    s b p g h M φ hφ' (affineUnion Us) (⊥ : X.Opens) hcover' n

set_option backward.isDefEq.respectTransparency false in
/-- The flat higher direct-image base-change map is an isomorphism in every
degree for a finite affine-open cover of a separated locally Noetherian
source over an affine base. -/
theorem moduleFlatHigherBaseChange_isIso_of_finiteAffineCover
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b) [Flat b]
    [IsAffine S] [X.IsSeparated] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent]
    (Us : List X.Opens) (hUs : ∀ U ∈ Us, IsAffineOpen U)
    (hcover : affineUnion Us = ⊤) (n : ℕ) :
    IsIso ((moduleFlatHigherBaseChangeNatTrans s b p g h n).app M) := by
  let _ : Flat p := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  exact moduleHigherBaseChange_isIso_of_finiteAffineCover
    s b p g h M Us hUs hcover n

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison is invertible for a compact separated source, using the
finite affine cover supplied by compactness. -/
lemma moduleHigherBaseChange_isIso_of_compactSource
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology]
    [IsAffine S] [CompactSpace X] [X.IsSeparated] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso ((moduleHigherBaseChangeNatTrans s b p g h n).app M) := by
  obtain ⟨m, U, hU, hcover⟩ := exists_fin_affine_cover (X := X)
  let Us : List X.Opens := List.ofFn U
  have hUs : ∀ W ∈ Us, IsAffineOpen W := by
    intro W hW
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' U W).mp hW
    exact hU i
  have hcover' : affineUnion Us = ⊤ := by
    dsimp only [Us]
    rw [affineUnion_ofFn]
    exact hcover
  exact moduleHigherBaseChange_isIso_of_finiteAffineCover
    s b p g h M Us hUs hcover' n

set_option backward.isDefEq.respectTransparency false in
/-- The flat comparison is invertible for a compact separated source, using the
finite affine cover supplied by compactness. -/
theorem moduleFlatHigherBaseChange_isIso_of_compactSource
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b) [Flat b] [IsAffine S] [CompactSpace X]
    [X.IsSeparated] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso ((moduleFlatHigherBaseChangeNatTrans s b p g h n).app M) := by
  let _ : Flat p := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  exact moduleHigherBaseChange_isIso_of_compactSource s b p g h M n

end GromovWitten.AlgebraicGeometry.Curves
