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

namespace MonoidHom

universe u v w

/-- Composing with an injective hom does not change the kernel. -/
theorem ker_comp_of_injective {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    (e : H →* G) (he : Function.Injective e) (φ : K →* H) :
    (e.comp φ).ker = φ.ker := by
  ext x
  constructor
  · intro hx
    -- `e (φ x) = 1` implies `φ x = 1` by injectivity.
    have : e (φ x) = 1 := by
      simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hx
    have : φ x = 1 := by
      apply he
      simpa [e.map_one] using this
    simpa [MonoidHom.mem_ker] using this
  · intro hx
    have : φ x = 1 := by
      simpa [MonoidHom.mem_ker] using hx
    simp [MonoidHom.mem_ker, MonoidHom.comp_apply, this]

end MonoidHom

namespace Group

universe u

/-!
## Chosen generating systems and presentations
-/

section

variable (G : Type u) [Group G]

/-- A (chosen) generating system for a group `G`: a type of abstract generators together with a map
to `G` whose range generates `G`. -/
structure GeneratingSystem where
  /-- The type of abstract generators. -/
  ι : Type u
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

variable {G : Type u} [Group G]

/-- A generating system is finite if the type of generators is finite. -/
def IsFinite (X : Group.GeneratingSystem (G := G)) : Prop :=
  Finite X.ι

/-- If the range of `X.val` generates `G`, then `FreeGroup.lift X.val` is surjective. -/
theorem lift_surjective (X : Group.GeneratingSystem (G := G)) :
    Function.Surjective (FreeGroup.lift X.val) := by
  have hrange : (FreeGroup.lift X.val).range = ⊤ := by
    simp [FreeGroup.range_lift_eq_closure, X.closure_range_val]
  exact MonoidHom.range_eq_top.mp hrange

end GeneratingSystem

namespace Presentation

variable {G : Type u} [Group G]

/-- A presentation is finite if it has finitely many generators and finitely many relators. -/
def IsFinite (P : Group.Presentation (G := G)) : Prop :=
  Finite P.ι ∧ P.rels.Finite

/-- Each relator maps to `1` under the induced map `FreeGroup P.ι →* G`. -/
theorem lift_eq_one_of_mem_rels (P : Group.Presentation (G := G)) {r : FreeGroup P.ι}
    (hr : r ∈ P.rels) :
    FreeGroup.lift P.val r = 1 := by
  have : r ∈ (FreeGroup.lift P.val).ker := by
    simpa [P.ker_eq_normalClosure] using
      (Subgroup.subset_normalClosure hr :
        r ∈ Subgroup.normalClosure P.rels)
  simpa [MonoidHom.mem_ker] using this

/--
Given a `Group.Presentation G`, we obtain the canonical map
`PresentedGroup P.rels →* G` (sending generators to `P.val`).
-/
def toGroup (P : Group.Presentation (G := G)) :
    PresentedGroup (α := P.ι) P.rels →* G :=
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
    (PresentedGroup (α := P.ι) P.rels) ≃* G := by
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
  simpa [PresentedGroup] using e₁.trans e₂

end Presentation

/-!
## Finitely presented groups
-/

/-- A group is finitely presented if it admits a finite presentation. -/
def FinitelyPresented (G : Type u) [Group G] : Prop :=
  ∃ P : Group.Presentation (G := G), P.IsFinite

/-!
### Characterization in terms of `PresentedGroup rels`
-/

section

variable {G : Type u} [Group G]

theorem finitelyPresented_exists_presentedGroup :
    Group.FinitelyPresented (G := G) →
      ∃ (α : Type u) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G) := by
  rintro ⟨P, hP⟩
  refine ⟨P.ι, P.rels, hP.1, hP.2, ?_⟩
  exact ⟨P.equivPresentedGroup⟩

theorem finitelyPresented_of_exists_presentedGroup :
    (∃ (α : Type u) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G)) →
      Group.FinitelyPresented (G := G) := by
  rintro ⟨α, rels, hα, hrels, ⟨e⟩⟩
  classical
  let val : α → G := fun a => e (PresentedGroup.of (rels := rels) a)

  have hlift : FreeGroup.lift val = e.toMonoidHom.comp (PresentedGroup.mk rels) := by
    ext a
    simp [val, PresentedGroup.of]

  have hker_mk : (PresentedGroup.mk rels).ker = Subgroup.normalClosure rels := by
    ext x
    simp [MonoidHom.mem_ker, PresentedGroup.mk_eq_one_iff]

  have hclosure : Subgroup.closure (Set.range val) = (⊤ : Subgroup G) := by
    have hsurj : Function.Surjective (FreeGroup.lift val) := by
      have hmk : Function.Surjective (PresentedGroup.mk rels) :=
        PresentedGroup.mk_surjective rels
      have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, by simp⟩
      simpa [hlift] using (he.comp hmk)
    have : (FreeGroup.lift val).range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
    simpa [FreeGroup.range_lift_eq_closure] using this

  have hker : (FreeGroup.lift val).ker = Subgroup.normalClosure rels := by
    calc
      (FreeGroup.lift val).ker
          = (e.toMonoidHom.comp (PresentedGroup.mk rels)).ker := by
              simp [hlift]
      _ = (PresentedGroup.mk rels).ker := by
            simpa using
              (MonoidHom.ker_comp_of_injective (e := e.toMonoidHom) (he := e.injective)
                (φ := PresentedGroup.mk rels))
      _ = Subgroup.normalClosure rels := hker_mk

  let P : Group.Presentation (G := G) :=
    { ι := α
      val := val
      closure_range_val := hclosure
      rels := rels
      ker_eq_normalClosure := hker }

  exact ⟨P, And.intro (by simpa [P] using hα) (by simpa [P] using hrels)⟩

theorem finitelyPresented_iff_exists_presentedGroup :
    Group.FinitelyPresented (G := G) ↔
      ∃ (α : Type u) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G) := by
  constructor
  · exact finitelyPresented_exists_presentedGroup (G := G)
  · exact finitelyPresented_of_exists_presentedGroup (G := G)

end

end Group

/-!
## The canonical presentation of a `PresentedGroup`
-/

namespace PresentedGroup

universe v
variable {α : Type v} (rels : Set (FreeGroup α))

@[simp]
theorem lift_of_eq_mk :
    FreeGroup.lift (PresentedGroup.of (rels := rels)) = PresentedGroup.mk rels := by
  ext a
  simp [PresentedGroup.of]

/-- The canonical `Group.Presentation` of `PresentedGroup rels`. -/
noncomputable def toPresentation : Group.Presentation (G := PresentedGroup rels) :=
{ ι := α
  val := (PresentedGroup.of (rels := rels))
  closure_range_val := by
    simp only [closure_range_of]
  rels := rels
  ker_eq_normalClosure := by
    have hker_mk : (PresentedGroup.mk rels).ker = Subgroup.normalClosure rels := by
      ext x
      simp [MonoidHom.mem_ker, PresentedGroup.mk_eq_one_iff]
    simpa [lift_of_eq_mk (rels := rels)] using hker_mk }

@[simp] lemma toPresentation_val (rels : Set (FreeGroup α)) :
    (toPresentation (rels := rels)).val = PresentedGroup.of (rels := rels) := rfl

@[simp] lemma toPresentation_rels (rels : Set (FreeGroup α)) :
    (toPresentation (rels := rels)).rels = rels := rfl

theorem finitelyPresented_of_finite
    [Finite α] (hrels : rels.Finite) :
    Group.FinitelyPresented (G := PresentedGroup rels) := by
  refine ⟨toPresentation (rels := rels), ?_⟩
  exact And.intro (by simpa [toPresentation] using (inferInstance : Finite α))
    (by simpa [toPresentation] using hrels)

end PresentedGroup
