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




namespace Group
/-
variable {α : Type*} [Fintype α]

def FinitelyPresentedGroup [Fintype α] (rels : Finset (FreeGroup α)) :=
  FreeGroup α ⧸ Subgroup.normalClosure rels

lemma aa (rels : Finset (FreeGroup α)) :
    PresentedGroup (SetLike.coe rels) = FinitelyPresentedGroup rels := rfl
 -/
variable (G : Type*) [Group G] (ι : Type w)

structure Generators where
  /-- The assignment of each variable to a value in `G`. -/
  val : ι → G
  gen : Subgroup.closure (Set.range val) = ⊤

structure Presentation extends Generators G ι where
  /-- The relations on the generators. -/
  rels : Set (FreeGroup ι)
  /-- The normal closure of `rels` is the kernel of the induced map. -/
  ker_eq : MonoidHom.ker (FreeGroup.lift val) = Subgroup.normalClosure rels

structure FinitePresentation' (ι : Type*) [Fintype ι] extends Presentation G ι where
  h_fin : Finite rels

structure FinitePresentation (ι : Type*) [Fintype ι] extends Generators G ι where
  /-- The relations on the generators. -/
  rels : Finset (FreeGroup ι)
  /-- The normal closure of `rels` is the kernel of the induced map. -/
  ker_eq : MonoidHom.ker (FreeGroup.lift val) = Subgroup.normalClosure rels

def expe (ι : Type*) [Fintype ι] : FinitePresentation G ι → Presentation G ι :=
  fun P ↦
    { val := P.val
      gen := P.gen
      rels := SetLike.coe P.rels
      ker_eq := P.ker_eq }


def isFinitelyPresented' : Prop :=
  ∃ (ι : Type*) (_ : Fintype ι) (g : Presentation G ι), Finite g.rels

def isFinitelyPresented : Prop :=
  ∃ (ι : Type*) (_ : Fintype ι) (_ : FinitePresentation G ι), True

variable (α : Type*)

def presZ : Presentation (Multiplicative ℤ) (Fin 1) :=
  { val := fun _ ↦ Multiplicative.ofAdd 1
    gen := by


      sorry
    rels := ∅
    ker_eq := sorry}


section aa

variable {G : Type*} [Group G] (ι : Type w) (P : Presentation G ι)

def isomorph : G ≃* PresentedGroup P.rels where
  toFun g := by
    simp [PresentedGroup]

    sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry


end aa



end Group
