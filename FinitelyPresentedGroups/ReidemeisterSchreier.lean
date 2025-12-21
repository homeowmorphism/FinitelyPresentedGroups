import Mathlib

variable (G : Type*) [Group G]

structure GeneratingSystem where
  /-- The abstract generators. -/
  ι : Type
  /-- The assignment of each abstract generator to a value in `G`. -/
  val : ι → G
  gen : Subgroup.closure (Set.range val) = G

structure Presentation extends GeneratingSystem G where
  /-- The relations on the generators. -/
  rels : Set (FreeGroup ι)
  /-- The normal closure of `rels` is the kernel of the induced map. -/
  ker_eq : MonoidHom.ker (FreeGroup.lift val) = Subgroup.normalClosure rels

def IsFiniteGeneratingSystem {G : Type*} [Group G] (X : GeneratingSystem G) : Prop :=
  Finite X.ι

def IsFinitePresentation {G : Type*} [Group G] (P : Presentation G) : Prop :=
  IsFiniteGeneratingSystem P.toGeneratingSystem ∧ Finite P.rels

structure FiniteGeneratingSystem extends GeneratingSystem G where
  gen_finite : Fintype ι

structure FinitePresentation extends FiniteGeneratingSystem G where
  /-- The relations on the generators. -/
  rels : Finset (FreeGroup ι)
  /-- The normal closure of `rels` is the kernel of the induced map. -/
  ker_eq : MonoidHom.ker (FreeGroup.lift val) = Subgroup.normalClosure rels

def FinitelyPresentableGroup : Prop :=
  ∃ (G_pres : Presentation G), IsFinitePresentation G_pres

def IsSchreierTransversal {G : Type*} [Group G] (H : Subgroup G) (T : Finset G) : Prop :=
  sorry

def ReidemeisterSchreierMethod {G : Type u} [Group G]
    (H : Subgroup G)
    (P : FinitePresentation G)
    (T : Finset G)
    (hT : IsSchreierTransversal H T)
    : FinitePresentation H := by
  sorry

/- theorem ReidemeisterSchreierFinite
{G_pres : Presentation G} (G_fin_pres : IsFinitePresentation G_pres)
{H : Subgroup G} (H_fi : Subgroup.FiniteIndex H) :
  IsFinitePresentation (ReidemeisterSchreierMethod G G_fin_pres T) := by
  sorry -/


theorem FiniteIndex_in_FP_is_FP
(G_fp : FinitelyPresentableGroup G) {H : Subgroup G} (H_fp : Subgroup.FiniteIndex H) :
  FinitelyPresentableGroup H := by
  sorry
