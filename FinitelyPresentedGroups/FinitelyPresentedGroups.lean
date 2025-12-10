import Mathlib

/- variable (α : Type)

#check FreeGroup α

#synth (Group (FreeGroup α))

variable (s: Set (FreeGroup α)) (x: FreeGroup α)

example : 1 ∈ s := by
  sorry
  -- notice the type of 1 can be inferred!  -/

def Subgroup.NormalFG {G : Type*} [Group G] (P : Subgroup G) : Prop :=
  ∃ S : Finset G, Subgroup.normalClosure S = P

open Subgroup

class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out : ∃ (n : ℕ) (f : (FreeGroup (Fin n)) →* G),
    Function.Surjective f ∧ (MonoidHom.ker f).NormalFG


/- class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out : ∃ (S: Finset G) (f : (FreeGroup (S)) →* G),
    Function.Surjective f ∧ (MonoidHom.ker f).NormalFG
-/

variable (G : Type) [Group G] (g : G)

lemma isFinitelyPresented_iff {G : Type*} [Group G] : IsFinitelyPresented G ↔
    ∃ (S : Finset G) (f : FreeGroup S →* G), Function.Surjective f ∧ (MonoidHom.ker f).NormalFG := by
  sorry

instance [h : IsFinitelyPresented G] : Group.FG G := by
  rw [isFinitelyPresented_iff] at h
  rw [Group.fg_iff_exists_freeGroup_hom_surjective]
  obtain ⟨S, f, hfsurj, hkernel⟩ := h
  use S
  constructor
  · use f
    exact hfsurj
  · exact Finset.finite_toSet S

  lemma fpGroup_is_fgGroup (G: Type*) [Group G] (h: IsFinitelyPresented G) : Group.FG G := by
  rw [Group.fg_iff_exists_freeGroup_hom_surjective]
  apply isFinitelyPresented_iff at G
  --constructor
  sorry


lemma isFinitelyPresented_stupid (α : Type) [Finite α] (s : Finset (FreeGroup α)) :
    IsFinitelyPresented ((FreeGroup α) ⧸ normalClosure s) := by
    constructor
    sorry
