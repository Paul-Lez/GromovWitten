/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.TorsorStackCover

/-!
# Towards the Mathlib bridge for the quotient stack `[U/G]`

`Stacks/TorsorStackEffective.lean` and `Stacks/TorsorStackCover.lean` prove that the quotient
prestack `[U/G] = ActionTorsor.pullbackPseudofunctor G U` is a stack in the repository-level
formulation with explicit data (`ActionTorsor.TorsorStack'`).  Identifying this with Mathlib's
`CategoryTheory.Pseudofunctor.IsStack Scheme.fppfTopology` was previously blocked by a Lean
*kernel* wall: the defeq test between two copies of the compatibility equation of
`Pseudofunctor.DescentData.Hom` at this pseudofunctor did not terminate.

This file removes that wall and records the identifications which make the bridge tractable.

## The wall, and how it is avoided

The measured failure is the following.  With `D = Pseudofunctor.DescentData.ofObj M` at
`pullbackPseudofunctor G U`, the two terms

```
D.hom q f₁ f₂ h₁ h₂     and     D.hom q f₁ f₂ h₁' h₂'
```

(where `h₁ h₁' : f₁ ≫ f i₁ = q` and `h₂ h₂' : f₂ ≫ f i₂ = q` are *different* proofs of the same
equations) are not identified by the kernel in any reasonable time: `ofObj` uses its
factorisation arguments computationally, through `Pseudofunctor.mapComp'`, so the kernel unfolds
`ofObj`, `mapComp'`, `pullbackPseudofunctor` and `LocallyDiscrete.mkPseudofunctor` on both sides
instead of applying proof irrelevance.  (With *identical* proof arguments the same `rfl` succeeds
in milliseconds, so the problem is exactly the comparison of the proof arguments.)

`descentData_hom_congr_proofs` below is that identification, proved **generically** — for an
arbitrary pseudofunctor `F` and an arbitrary descent datum `D` — by `proof_irrel`.  At that level
nothing can unfold, so the proof is instantaneous; and instantiating the generic lemma at
`pullbackPseudofunctor G U` is a pure substitution, which the kernel also accepts instantaneously.
`descentData_comm_of_proofs` packages the same trick for the compatibility equation of
`Pseudofunctor.DescentData.Hom`, which is what descent-of-arrows arguments actually use.

## The fibrewise identifications

The remaining ingredients of the bridge are the identifications of Mathlib's generic constructions
at `pullbackPseudofunctor G U` with the repository's explicit base-change operations.  All of them
hold by `rfl` and were measured to typecheck in milliseconds:

* `ActionTorsor.pullbackPseudofunctor_map_obj` — `(F.map p.op.toLoc).toFunctor.obj M` is
  `ActionTorsor.pullbackObj p M`;
* `ActionTorsor.presheafHom_obj` — the value of Mathlib's presheaf of morphisms
  `F.presheafHom M N` on `Over.mk p` is the hom-type of the base changes;
* `ActionTorsor.pullHom_eq` — Mathlib's restriction map `pullHom` on that presheaf is the
  repository's `pullbackFunctor` together with the comparison isomorphism
  `ActionTorsor.pullbackFunctorCompIso`;
* `ActionTorsor.descentData_ofObj_obj` — the objects of `DescentData.ofObj M`.

Together with `Pseudofunctor.isPrestackFor_iff_isSheafFor` (which expresses `IsPrestackFor`
purely through the sheaf condition for `presheafHom`, with no mention of `DescentData.Hom`),
these reduce `Pseudofunctor.IsPrestack Scheme.fppfTopology (pullbackPseudofunctor G U)` to
`ActionTorsor.torsorPrestack` (`Stacks/TorsorStackDescent.lean`) transported along
`Sieve.overEquiv`.  That transport, and the corresponding treatment of
`IsStack.essSurj_of_sieve` from `ActionTorsor.exists_torsor_of_torsorDescentDatum'`, are not
carried out here; `Pseudofunctor.IsStack` is therefore still not concluded and `[U/G]` and `BG`
are still not bundled as `FppfStack`s.

## Main declarations

* `GromovWitten.AlgebraicGeometry.descentData_hom_congr_proofs`
* `GromovWitten.AlgebraicGeometry.descentData_comm_of_proofs`
* `GromovWitten.AlgebraicGeometry.ActionTorsor.pullbackPseudofunctor_map_obj`
* `GromovWitten.AlgebraicGeometry.ActionTorsor.presheafHom_obj`
* `GromovWitten.AlgebraicGeometry.ActionTorsor.pullHom_eq`
* `GromovWitten.AlgebraicGeometry.ActionTorsor.descentData_ofObj_obj`
-/

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace GromovWitten.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

section Generic

variable {C : Type*} [Category* C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u}}
  {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- **The factorisation proofs of `Pseudofunctor.DescentData.hom` are irrelevant.**

This is trivially true by proof irrelevance, but it must be proved *generically*, as here: at
`ActionTorsor.pullbackPseudofunctor` and `Pseudofunctor.DescentData.ofObj` the corresponding
`rfl` makes the Lean kernel diverge, because `DescentData.ofObj` uses its factorisation arguments
computationally inside `Pseudofunctor.mapComp'`.  Instantiating this lemma is a substitution and
costs nothing. -/
theorem descentData_hom_congr_proofs (D : F.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (h₁ h₁' : f₁ ≫ f i₁ = q) (h₂ h₂' : f₂ ≫ f i₂ = q) :
    D.hom q f₁ f₂ h₁ h₂ = D.hom q f₁ f₂ h₁' h₂' := by
  rw [proof_irrel h₁ h₁', proof_irrel h₂ h₂']

/-- **The compatibility equation of a morphism of descent data, with unrelated factorisation
proofs on the two sides.**  This is the form in which the equation is used when the two
factorisations are produced by different tactics; stating it generically (rather than
instantiating `Pseudofunctor.DescentData.Hom.comm` at a concrete pseudofunctor and then
comparing the two copies) is what keeps the kernel check cheap. -/
theorem descentData_comm_of_proofs {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂) ⦃Y : C⦄ (q : Y ⟶ S)
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (h₁ h₁' : f₁ ≫ f i₁ = q)
    (h₂ h₂' : f₂ ≫ f i₂ = q) :
    (F.map f₁.op.toLoc).toFunctor.map (φ.hom i₁) ≫ D₂.hom q f₁ f₂ h₁ h₂ =
      D₁.hom q f₁ f₂ h₁' h₂' ≫ (F.map f₂.op.toLoc).toFunctor.map (φ.hom i₂) := by
  rw [descentData_hom_congr_proofs D₁ q f₁ f₂ h₁' h₁ h₂' h₂]
  exact φ.comm q f₁ f₂ h₁ h₂

end Generic

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G}

/-- Base change along `p` in Mathlib's pseudofunctorial notation is `ActionTorsor.pullbackObj`. -/
theorem pullbackPseudofunctor_map_obj {S X : Scheme.{u}} (p : X ⟶ S) (M : ActionTorsor G U S) :
    ((pullbackPseudofunctor G U).map p.op.toLoc).toFunctor.obj M = pullbackObj p M :=
  rfl

/-- The presheaf of morphisms of `[U/G]` over `S`, evaluated at `Over.mk p`, is the type of
arrows between the base changes along `p`. -/
theorem presheafHom_obj {S X : Scheme.{u}} (p : X ⟶ S) (M N : ActionTorsor G U S) :
    ((pullbackPseudofunctor G U).presheafHom M N).obj (op (Over.mk p)) =
      (pullbackObj p M ⟶ pullbackObj p N) :=
  rfl

/-- **Mathlib's restriction map on the presheaf of morphisms of `[U/G]` is the repository's base
change of arrows**, conjugated by the comparison isomorphism `pullbackFunctorCompIso`. -/
theorem pullHom_eq {S X Y : Scheme.{u}} (p : X ⟶ S) (g : Y ⟶ X) (M N : ActionTorsor G U S)
    (φ : (pullbackFunctor (U := U) p).obj M ⟶ (pullbackFunctor (U := U) p).obj N) :
    pullHom (F := pullbackPseudofunctor G U) φ g (g ≫ p) (g ≫ p) rfl rfl =
      (pullbackFunctorCompIso (U := U) g p).hom.app M ≫
        (pullbackFunctor (U := U) g).map φ ≫
          (pullbackFunctorCompIso (U := U) g p).inv.app N :=
  rfl

/-- The objects of the descent datum obtained by pulling back a single equivariant torsor. -/
theorem descentData_ofObj_obj {ι : Type u} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    (fam : ∀ i, X i ⟶ S) (M : ActionTorsor G U S) (i : ι) :
    (Pseudofunctor.DescentData.ofObj (F := pullbackPseudofunctor G U) (f := fam) M).obj i =
      pullbackObj (fam i) M :=
  rfl

end ActionTorsor

end GromovWitten.AlgebraicGeometry
