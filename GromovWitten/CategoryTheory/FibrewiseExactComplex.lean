/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.BoundedFlatComplex
import GromovWitten.Algebra.ModuleCatScalarExtension
import GromovWitten.Algebra.ModuleFibreVanishing

/-!
# Fibrewise detection of exact tails

For a bounded-above complex of flat modules with finite homology in a tail,
exactness of every residue-field fibre implies exactness of that tail.
Descending induction makes the outgoing cokernel flat, so the canonical
homology comparison identifies each fibre before applying Nakayama's lemma.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u
noncomputable section

namespace CochainComplex

/-- A bounded flat complex with finite homology is exact in a tail if all its
residue-field fibres are exact in that tail. -/
theorem bounded_flat_fibrewise_exact_tail
    {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (d : ℕ)
    (hfinite : ∀ n : ℕ, d ≤ n → Module.Finite R (K.homology (n : ℤ)))
    (hfibres : ∀ p : PrimeSpectrum R, ∀ n : ℕ, d ≤ n →
      (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).ExactAt (n : ℤ)) :
    ∀ n : ℕ, d ≤ n → K.ExactAt (n : ℤ) := by
  have hdesc : ∀ k n, N - n = k → d ≤ n → K.ExactAt (n : ℤ) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n hkn hdn
      by_cases hnN : N ≤ n
      · exact HomologicalComplex.ExactAt.of_isZero (K := K) (i := (n : ℤ)) (htail n hnN)
      · have hexactAbove : ∀ m : ℕ, n + 1 ≤ m → K.ExactAt (m : ℤ) := by
          intro m hnm
          by_cases hmN : N ≤ m
          · exact HomologicalComplex.ExactAt.of_isZero (K := K) (i := (m : ℤ))
              (htail m hmN)
          · have hmeasure : N - m < k := by omega
            exact ih (N - m) hmeasure m rfl (by omega)
        have hfiniteN : Module.Finite R (K.homology (n : ℤ)) := hfinite n hdn
        have hsub : Subsingleton (K.homology (n : ℤ)) :=
          @Module.subsingleton_of_residueField_tensorProduct R inferInstance
            (K.homology (n : ℤ)) inferInstance inferInstance hfiniteN (by
              intro p
              let E := ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)
              let L := (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
              have hcmp : IsIso (K.homologyComparison E (n : ℤ)) :=
                bounded_int_tail_homologyComparison_isIso
                  (algebraMap R p.asIdeal.ResidueField) K hflat N htail n hexactAbove n le_rfl
              have hzeroL : IsZero (L.homology (n : ℤ)) :=
                (L.exactAt_iff_isZero_homology (n : ℤ)).mp (hfibres p n hdn)
              have hcmpIso : E.obj (K.homology (n : ℤ)) ≅ L.homology (n : ℤ) := by
                letI : IsIso (K.homologyComparison E (n : ℤ)) := hcmp
                exact asIso (K.homologyComparison E (n : ℤ))
              have hzeroE : IsZero (E.obj (K.homology (n : ℤ))) :=
                IsZero.of_iso hzeroL hcmpIso
              have hzeroTensor : IsZero
                  (ModuleCat.of p.asIdeal.ResidueField
                    (p.asIdeal.ResidueField ⊗[R] K.homology (n : ℤ))) :=
                IsZero.of_iso hzeroE
                  (ModuleCat.extendScalarsAlgebraIso
                    (C := p.asIdeal.ResidueField) (K.homology (n : ℤ))).symm
              exact (ModuleCat.isZero_iff_subsingleton.mp hzeroTensor))
        have hzero : IsZero (K.homology (n : ℤ)) :=
          ModuleCat.isZero_iff_subsingleton.mpr hsub
        exact (K.exactAt_iff_isZero_homology (n : ℤ)).mpr hzero
  intro n hdn
  exact hdesc (N - n) n rfl hdn

end CochainComplex
