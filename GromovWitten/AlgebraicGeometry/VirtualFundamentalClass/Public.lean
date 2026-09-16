/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Examples

/-!
# Public Behrend--Fantechi interface

Only completed constructions are exported here.  In particular, this module deliberately does
not expose the former `ClassicalInput` and `RelativeInput` records: those records accepted the
intrinsic normal cone, its geometric realization, and resolution independence as fields, so
their apparent virtual-class constructors merely returned hard theorems supplied by the caller.

The currently exported acceptance test is the represented proper point.  Starting with the
identity closed immersion of `Spec(k)`, it constructs the Rees normal cone, the affine cotangent
presentation and its derived localization, the identity perfect obstruction theory, the actual
global two-term resolution, the rank-zero bundle Gysin map, and the resulting rational Chow
class.  `Examples.properPoint_virtual_eq_fundamental` proves that this class is the ordinary
fundamental class, while `Examples.properPoint_virtual_degree_one` computes its degree.

The general absolute and relative entry points will be restored only after their intrinsic-cone,
Chow/Gysin, and resolution-independence constructions are available as definitions and theorems,
not as fields of an input package.
-/

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Public

open CategoryTheory
open Examples

universe u


noncomputable section

variable (k : Type u) [Field k]

/-- Public, fully constructed proper-scheme acceptance test: the virtual class of `Spec(k)` for
its identity obstruction theory agrees with its ordinary fundamental class. -/
theorem properPoint_virtual_eq_fundamental :
    ProperPoint.virtualClass k = ProperPoint.fundamentalClass k :=
  Examples.properPoint_virtual_eq_fundamental k

/-- The virtual degree of the constructed proper-point class is one. -/
@[simp] theorem properPoint_virtual_degree_one :
    Examples.properPointChowEquiv k (ProperPoint.virtualClass k) = 1 :=
  Examples.properPoint_virtual_degree_one k

/-- The example really is proper over its ground point. -/
theorem properPoint_isProper :
    (@_root_.AlgebraicGeometry.IsProper : MorphismProperty
      _root_.AlgebraicGeometry.Scheme.{u})
      (𝟙 (_root_.AlgebraicGeometry.Spec (.of k))) :=
  Examples.properPoint_isProper k

end


end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Public
