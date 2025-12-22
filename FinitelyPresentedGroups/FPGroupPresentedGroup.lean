/-
Copyright (c) 2025 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Riccardo Brasca, Stefano Francaviglia, Hang Lu Su,
Francesco Milizia, Valerio Proietti, Lawrence Wu
-/

import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# (Finite) presentations of a group

This file defines “chosen” generating systems and presentations of a group, in a way that
integrates with `Mathlib.GroupTheory.PresentedGroup`.

Key points:

* `Group.GeneratingSystem G` is a type of abstract generators `ι` with a map `ι → G` whose
  range generates `G` (via `Subgroup.closure`).

* `Group.Presentation G` extends `GeneratingSystem G` by a set of relators
  `rels : Set (FreeGroup ι)` and a kernel condition saying that the induced map
  `FreeGroup ι →* G` has kernel equal to `Subgroup.normalClosure rels`.

* Any `Group.Presentation G` yields an isomorphism `PresentedGroup P.rels ≃* G`
  via the first isomorphism theorem.

* `Group.FinitelyPresented` is equivalent to “isomorphic to a `PresentedGroup rels` with finitely
  many generators and relators”.
-/

namespace Group

/-!
## Chosen generating systems and presentations
-/

section

variable (G : Type*) [Group G]

/-- A (chosen) generating system for a group `G`: a type of abstract generators together with a map
to `G` whose range generates `G`. -/
structure GeneratingSystem where
  /-- The type of abstract generators. -/
  ι : Type*
  /-- The assignment of each abstract generator to an element of `G`. -/
  val : ι → G
  /-- The images of the generators generate `G`. -/
  closure_range_val : Subgroup.closure (Set.range val) = ⊤

/-- A presentation of a group `G`: a generating system together with a set of relators in the free
group on the generators, such that the kernel of the induced map is the normal closure of the
relators. -/
structure Presentation extends GeneratingSystem G where
  /-- The relations (relators), as a subset of the free group on the generators. -/
  rels : Set (FreeGroup ι)
  /-- The kernel of the induced map from the free group is the normal closure of the relators. -/
  ker_eq_normalClosure : (FreeGroup.lift val).ker = Subgroup.normalClosure rels

end

namespace GeneratingSystem

/-!
### Finiteness and basic API for generating systems
-/

variable {G : Type*} [Group G]

/-- A generating system is finite if the type of generators is finite. -/
def IsFinite (X : Group.GeneratingSystem (G := G)) : Prop :=
  Finite X.ι

/--
If the range of `X.val` generates `G`, then the induced homomorphism
`FreeGroup X.ι →* G` is surjective.
-/
theorem lift_surjective (X : Group.GeneratingSystem (G := G)) :
    Function.Surjective (FreeGroup.lift X.val) := by
  have hrange : (FreeGroup.lift X.val).range = ⊤ := by
    simp [FreeGroup.range_lift_eq_closure, X.closure_range_val]
  exact MonoidHom.range_eq_top.mp hrange

end GeneratingSystem

namespace Presentation

/-!
### Finiteness and basic API for presentations
-/

variable {G : Type*} [Group G]

/-- A presentation is finite if it has finitely many generators and finitely many relators. -/
def IsFinite (P : Group.Presentation (G := G)) : Prop :=
  P.toGeneratingSystem.IsFinite ∧ P.rels.Finite

/-- A convenient abbreviation: the `PresentedGroup` attached to a `Group.Presentation`. -/
abbrev presentedGroup (P : Group.Presentation (G := G)) : Type* :=
  PresentedGroup (α := P.ι) P.rels

/-- Each relator maps to `1` under the induced map `FreeGroup P.ι →* G`. -/
theorem lift_eq_one_of_mem_rels (P : Group.Presentation (G := G)) {r : FreeGroup P.ι}
    (hr : r ∈ P.rels) :
    FreeGroup.lift P.val r = 1 := by
  have : r ∈ (FreeGroup.lift P.val).ker := by
    simpa [P.ker_eq_normalClosure] using (Subgroup.subset_normalClosure hr)
  simpa using MonoidHom.mem_ker.mp this

/--
Given a `Group.Presentation G`, we obtain the canonical map
`PresentedGroup P.rels →* G` (sending generators to `P.val`).
-/
def toGroup (P : Group.Presentation (G := G)) :
    P.presentedGroup →* G :=
  PresentedGroup.toGroup (rels := P.rels)
    (f := P.val) (by
      intro r hr
      simpa using (P.lift_eq_one_of_mem_rels (r := r) hr))

@[simp]
theorem toGroup_of (P : Group.Presentation (G := G)) (x : P.ι) :
    P.toGroup (PresentedGroup.of (rels := P.rels) x) = P.val x := by
  simp [Presentation.toGroup]

/--
From a `Group.Presentation G`, build a group isomorphism
`PresentedGroup P.rels ≃* G`.
-/
noncomputable def equivPresentedGroup (P : Group.Presentation (G := G)) :
    P.presentedGroup ≃* G :=
by
  let φ : FreeGroup P.ι →* G := FreeGroup.lift P.val
  have hsurj : Function.Surjective φ := P.toGeneratingSystem.lift_surjective
  have e₁ :
      (FreeGroup P.ι ⧸ Subgroup.normalClosure P.rels) ≃*
        (FreeGroup P.ι ⧸ φ.ker) :=
    QuotientGroup.quotientMulEquivOfEq (G := FreeGroup P.ι)
      (M := Subgroup.normalClosure P.rels) (N := φ.ker) (by
        simpa [φ] using P.ker_eq_normalClosure.symm)
  have e₂ : (FreeGroup P.ι ⧸ φ.ker) ≃* G :=
    QuotientGroup.quotientKerEquivOfSurjective φ hsurj
  simpa [Presentation.presentedGroup, PresentedGroup] using e₁.trans e₂

end Presentation

/-!
## Finitely presented groups
-/

universe u

/-- A group is finitely presented if it admits a presentation with finitely many generators and
finitely many relators.

We require the generator type `ι` to live in the same universe as `G` to avoid universe mismatches
when repackaging existentials.
-/
def FinitelyPresented (G : Type u) [Group G] : Prop :=
  ∃ (ι : Type u) (val : ι → G) (rels : Set (FreeGroup ι)),
    Subgroup.closure (Set.range val) = ⊤ ∧
      (FreeGroup.lift val).ker = Subgroup.normalClosure rels ∧
      Finite ι ∧ rels.Finite

/-!
### Characterization in terms of `PresentedGroup rels`
-/

section

variable {G : Type u} [Group G]

/--
If `G` is finitely presented, then `G` is isomorphic to some `PresentedGroup rels` with
finitely many generators and finitely many relators.
-/
theorem finitelyPresented_exists_presentedGroup :
    Group.FinitelyPresented (G := G) →
      ∃ (α : Type u) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G) := by
  rintro ⟨ι, val, rels, hclosure, hker, hfinite, hrels⟩
  let P : Group.Presentation (G := G) :=
    { ι := ι
      val := val
      closure_range_val := hclosure
      rels := rels
      ker_eq_normalClosure := hker }
  refine ⟨ι, rels, hfinite, hrels, ?_⟩
  exact ⟨P.equivPresentedGroup⟩

/--
Conversely, if `G` is isomorphic to some `PresentedGroup rels` with finite `α` and finite `rels`,
then `G` is finitely presented.

This uses `PresentedGroup.toPresentation` (defined below) and transports the presentation
along the given isomorphism.
-/
theorem finitelyPresented_of_exists_presentedGroup :
    (∃ (α : Type _) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G)) →
      Group.FinitelyPresented (G := G) := by
  rintro ⟨α, rels, hα, hrels, ⟨e⟩⟩
  classical
  -- Install `Finite α` as an instance for convenient use.
  haveI : Finite α := hα
  -- Use the canonical presentation of `PresentedGroup rels`, then transport it across `e`.
  let P0 : Group.Presentation (G := PresentedGroup rels) :=
    PresentedGroup.toPresentation (rels := rels)
  let P : Group.Presentation (G := G) := Group.Presentation.mapMulEquiv (P := P0) e
  refine ⟨P, ?_⟩
  -- `P` has generator type `α` and relators `rels`, hence is finite.
  refine ⟨?_, ?_⟩
  · -- finitely many generators
    -- By construction, `P.ι = α`.
    -- This is definitional, so `simp` solves it.
    simpa [Group.GeneratingSystem.IsFinite, P, P0, Group.Presentation.mapMulEquiv,
      PresentedGroup.toPresentation]
  · -- finitely many relators
    simpa [Group.Presentation.IsFinite, P, P0, Group.Presentation.mapMulEquiv,
      PresentedGroup.toPresentation] using hrels

/--
A convenient combined statement: `G` is finitely presented iff it is isomorphic to a finite
`PresentedGroup rels`.
-/
theorem finitelyPresented_iff_exists_presentedGroup :
    Group.FinitelyPresented (G := G) ↔
      ∃ (α : Type _) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G) := by
  constructor
  · exact finitelyPresented_exists_presentedGroup (G := G)
  · intro h
    exact finitelyPresented_of_exists_presentedGroup (G := G) h

end

end Group

/-!
## The canonical presentation of a `PresentedGroup`
-/

namespace PresentedGroup

variable {α : Type w} (rels : Set (FreeGroup α))

/--
The canonical `Group.Presentation` of `PresentedGroup rels`:

* generators are `α` via `PresentedGroup.of`,
* relations are `rels`,
* the kernel of the induced map is exactly the normal closure of `rels` (by `mk_eq_one_iff`).
-/
def toPresentation : Group.Presentation (G := PresentedGroup rels) :=
{ ι := α
  val := (PresentedGroup.of : α → PresentedGroup rels)
  closure_range_val := by
    -- This is exactly `PresentedGroup.closure_range_of`.
    simpa using PresentedGroup.closure_range_of (rels := rels)
  rels := rels
  ker_eq_normalClosure := by
    -- Identify `FreeGroup.lift (PresentedGroup.of)` with `PresentedGroup.mk`.
    have h :
        FreeGroup.lift (PresentedGroup.of (rels := rels))
          = PresentedGroup.mk rels := by
      ext a
      -- `FreeGroup.lift` agrees with the function on generators.
      simp [PresentedGroup.of]
    -- Kernel membership is `mk rels x = 1`, which is `mk_eq_one_iff`.
    ext x
    simp [h, MonoidHom.mem_ker, PresentedGroup.mk_eq_one_iff] }

section

/-
If `α` and `rels` are finite, then `PresentedGroup rels` is finitely presented in the sense above.
This is an easy corollary of the canonical presentation.
-/
theorem finitelyPresented_of_finite
    [Finite α] (hrels : rels.Finite) :
    Group.FinitelyPresented (G := PresentedGroup rels) := by
  refine ⟨PresentedGroup.toPresentation (rels := rels), ?_⟩
  refine ⟨?_, hrels⟩
  -- Finite generators are immediate since `ι = α`.
  simpa [Group.GeneratingSystem.IsFinite, PresentedGroup.toPresentation] using
    (show Finite α from (inferInstance : Finite α))

end

end PresentedGroup
