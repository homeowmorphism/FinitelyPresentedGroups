/-
Copyright (c) 2025 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Riccardo Brasca, Stefano Francaviglia, Hang Lu Su,
Francesco Milizia, Valerio Proietti, Lawrence Wu
-/

import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Finiteness

/-!
# Presentations of a group and finitely presented groups
-/

namespace MonoidHom

universe u v w

/-- Composing with an injective hom does not change the kernel.
I couldn't find a similar result in Mathlib so I am proving it here, as it will
be used later. Obviously this has nothing to do with presentations. -/
theorem ker_comp_of_injective {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    (e : H →* G) (he : Function.Injective e) (φ : K →* H) :
    (e.comp φ).ker = φ.ker := by
  ext x
  constructor
  · intro hx
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

/-- A (chosen) generating system for a group `G`. -/
structure GeneratingSystem where
  /-- The type of abstract generators. -/
  ι : Type u
  /-- The assignment of each abstract generator to an element of `G`. -/
  val : ι → G
  /-- The images of the generators generate `G`. -/
  closure_range_val : Subgroup.closure (Set.range val) = ⊤

/-- A presentation of a group `G`. -/
structure Presentation extends GeneratingSystem G where
  /-- The relations (relators). -/
  rels : Set (FreeGroup ι)
  /-- Kernel of the induced map is the normal closure of the relators. -/
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

/-- The `PresentedGroup` attached to a `Group.Presentation`. -/
abbrev presentedGroup (P : Group.Presentation (G := G)) : Type u :=
  PresentedGroup (α := P.ι) P.rels

@[simp]
lemma presentedGroup_def (P : Group.Presentation (G := G)) :
    P.presentedGroup = PresentedGroup (α := P.ι) P.rels := rfl

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
Transport a presentation across a group isomorphism.
If `P` is a presentation of `H` and `e : H ≃* G`, we get a presentation of `G`
with the same generators/relators and generator map composed with `e`.
-/
def mapMulEquiv {H : Type u} [Group H]
    (P : Group.Presentation (G := H)) (e : H ≃* G) :
    Group.Presentation (G := G) := by
  refine
    { ι := P.ι
      val := fun i => e (P.val i)
      closure_range_val := ?_
      rels := P.rels
      ker_eq_normalClosure := ?_ }
  · -- closure_range_val
    have hrange :
        Set.range (fun i : P.ι => e (P.val i)) = e '' Set.range P.val := by
      simpa [Function.comp] using
        (Set.range_comp (f := P.val) (g := fun x : H => e x))
    calc
      Subgroup.closure (Set.range fun i : P.ι => e (P.val i))
          = Subgroup.closure (e '' Set.range P.val) := by simp [hrange]
      _ = Subgroup.map e.toMonoidHom (Subgroup.closure (Set.range P.val)) := by
            simpa using
              (MonoidHom.map_closure (e.toMonoidHom) (Set.range P.val)).symm
      _ = Subgroup.map e.toMonoidHom ⊤ := by simp [P.closure_range_val]
      _ = ⊤ := by simp
  · -- ker_eq_normalClosure
    have hlift :
        FreeGroup.lift (fun i : P.ι => e (P.val i))
          = e.toMonoidHom.comp (FreeGroup.lift P.val) := by
      ext i
      simp
    calc
      (FreeGroup.lift (fun i : P.ι => e (P.val i))).ker
          = (e.toMonoidHom.comp (FreeGroup.lift P.val)).ker := by
              simp [hlift]
      _ = (FreeGroup.lift P.val).ker := by
            simpa using
              (MonoidHom.ker_comp_of_injective (e := e.toMonoidHom) (he := e.injective)
                (φ := FreeGroup.lift P.val))
      _ = Subgroup.normalClosure P.rels := P.ker_eq_normalClosure

/--
From a `Group.Presentation G`, build a group isomorphism
`PresentedGroup P.rels ≃* G`.
-/
noncomputable def equivPresentedGroup (P : Group.Presentation (G := G)) :
    P.presentedGroup ≃* G := by
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

/-- A group is finitely presented if it admits a finite presentation. -/
def FinitelyPresented (G : Type u) [Group G] : Prop :=
  ∃ P : Group.Presentation (G := G), P.IsFinite

/-!
### Consequences and characterizations
-/

section

variable {G : Type u} [Group G]

theorem finitelyPresented_exists_presentedGroup :
    Group.FinitelyPresented (G := G) →
      ∃ (α : Type u) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G) := by
  rintro ⟨P, hP⟩
  refine ⟨P.ι, P.rels, hP.1, hP.2, ?_⟩
  refine ⟨?_⟩
  -- convert `P.presentedGroup` to `PresentedGroup P.rels`
  simpa [Presentation.presentedGroup] using P.equivPresentedGroup

/-- Finitely presented groups are finitely generated. -/
theorem fg_of_finitelyPresented :
    Group.FinitelyPresented (G := G) → Group.FG G := by
  rintro ⟨P, hP⟩
  classical
  refine (Group.fg_iff).2 ?_
  haveI : Finite P.ι := hP.1
  refine ⟨Set.range P.val, ?_, ?_⟩
  · simpa using P.closure_range_val
  · simpa using (Set.finite_range P.val)

/-- `FinitelyPresented` is invariant under group isomorphism. -/
theorem finitelyPresented_congr {H : Type u} [Group H] (e : G ≃* H) :
    Group.FinitelyPresented (G := G) ↔ Group.FinitelyPresented (G := H) := by
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨Group.Presentation.mapMulEquiv (G := H) (P := P) e, ?_⟩
    simpa [Group.Presentation.IsFinite, Group.Presentation.mapMulEquiv] using hP
  · rintro ⟨P, hP⟩
    refine ⟨Group.Presentation.mapMulEquiv (G := G) (P := P) e.symm, ?_⟩
    simpa [Group.Presentation.IsFinite, Group.Presentation.mapMulEquiv] using hP

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
def toPresentation : Group.Presentation (G := PresentedGroup rels) :=
{ ι := α
  val := (PresentedGroup.of (rels := rels))
  closure_range_val := by
    simp only [closure_range_of]
  rels := rels
  ker_eq_normalClosure := by
    ext x
    simp [MonoidHom.mem_ker, PresentedGroup.mk_eq_one_iff, lift_of_eq_mk (rels := rels)] }

theorem finitelyPresented_of_finite
    [Finite α] (hrels : rels.Finite) :
    Group.FinitelyPresented (G := PresentedGroup rels) := by
  refine ⟨toPresentation (rels := rels), ?_⟩
  exact And.intro (inferInstance : Finite α) hrels

end PresentedGroup

namespace Group

universe u

section

variable {G : Type u} [Group G]

theorem finitelyPresented_of_exists_presentedGroup :
    (∃ (α : Type u) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G)) →
      Group.FinitelyPresented (G := G) := by
  rintro ⟨α, rels, hα, hrels, ⟨e⟩⟩
  classical
  haveI : Finite α := hα
  have hPG : Group.FinitelyPresented (G := PresentedGroup rels) :=
    PresentedGroup.finitelyPresented_of_finite (rels := rels) hrels
  exact (Group.finitelyPresented_congr (G := PresentedGroup rels) (H := G) e).1 hPG

theorem finitelyPresented_iff_exists_presentedGroup :
    Group.FinitelyPresented (G := G) ↔
      ∃ (α : Type u) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G) := by
  constructor
  · exact finitelyPresented_exists_presentedGroup (G := G)
  · exact finitelyPresented_of_exists_presentedGroup (G := G)

end

end Group
