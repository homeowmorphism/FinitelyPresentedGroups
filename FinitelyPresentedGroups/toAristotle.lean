import Mathlib

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
      rels := P.rels.toSet
      ker_eq := P.ker_eq }


def isFinitelyPresented' : Prop :=
  ∃ (ι : Type*) (_ : Fintype ι) (g : Presentation G ι), Finite g.rels

variable (α : Type*)

def presZ : Presentation (Multiplicative ℤ) (Fin 1) :=
  { val := fun _ ↦ Multiplicative.ofAdd 1
    gen := sorry
    rels := ∅
    ker_eq := sorry}
