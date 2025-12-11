import Mathlib

variable (G : Type*) [Group G]

structure GeneratingSystem where
  /-- The abstract generators. -/
  ι : Type
  /-- The assignment of each abstract generator to a value in `G`. -/
  val : ι → G
  gen : Subgroup.closure (Set.range val) = ⊤

structure Presentation extends GeneratingSystem G where
  /-- The relations on the generators. -/
  rels : Set (FreeGroup ι)
  /-- The normal closure of `rels` is the kernel of the induced map. -/
  ker_eq : MonoidHom.ker (FreeGroup.lift val) = Subgroup.normalClosure rels

def IsFiniteGeneratingSystem {G : Type*} [Group G] (X : GeneratingSystem G) : Prop :=
  Finite X.ι

def IsFinitePresentation {G : Type*} [Group G] (P : Presentation G) : Prop :=
  IsFiniteGeneratingSystem P.toGeneratingSystem ∧ Finite P.rels

def FinitelyPresentableGroup : Prop :=
  ∃ (G_pres : Presentation G), IsFinitePresentation G_pres

/-
This constructs the “canonical” presentation of `PresentedGroup rels`:
generators are `α`, relations are `rels`, and the kernel of the induced map
is exactly the normal closure of `rels`.
-/
--- noncomputable def?
def PresentedGroup.toPresentation
    (rels : Set (FreeGroup α)) :
    Presentation (PresentedGroup rels) :=
{ ι   := α,
  val := (PresentedGroup.of : α → PresentedGroup rels),

  -- The generators of a presented group generate the whole group.
  gen := by
    -- `PresentedGroup.closure_range_of` says exactly this.
    simp [PresentedGroup.closure_range_of (rels := rels)]

  rels := rels,

  ker_eq := by
    -- First show that `FreeGroup.lift` of the generators is the canonical map `mk`.
    have h_lift_eq :
        FreeGroup.lift (PresentedGroup.of (rels := rels))
          = PresentedGroup.mk rels := by
      ext a
      -- On generators, `FreeGroup.lift` just evaluates the function,
      -- and `PresentedGroup.of` is defined via `PresentedGroup.mk`.
      simp [PresentedGroup.of]

    -- Now identify the kernel using `PresentedGroup.mk_eq_one_iff`.
    ext x
    -- membership in the kernel is `f x = 1`
    -- and `PresentedGroup.mk_eq_one_iff` says when that happens.
    simp [MonoidHom.mem_ker, h_lift_eq, PresentedGroup.mk_eq_one_iff]
}
