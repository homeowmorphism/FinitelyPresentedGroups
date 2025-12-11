import Mathlib

#check Group

variable (G : Type*) [Group G]

structure GeneratingSystem where
  /-- The abstract generators -/
  ι : Type w
  /-- The assignment of each abstract generator to a value in `G`. -/
  val : ι → G
  gen : Subgroup.closure (Set.range val) = G

structure Presentation extends GeneratingSystem G where
  /-- The relations on the generators. -/
  rels : Set (FreeGroup ι)
  /-- The normal closure of `rels` is the kernel of the induced map. -/
  ker_eq : MonoidHom.ker (FreeGroup.lift val) = Subgroup.normalClosure rels

def IsFiniteGeneratingSystem (X : GeneratingSystem G) : Prop :=
  Finite X.ι

def IsFinitePresentation (P : Presentation G) : Prop :=
  IsFiniteGeneratingSystem G P.toGeneratingSystem ∧ Finite P.rels

/-structure FiniteGeneratingSystem extends GeneratingSystem G where
  gen_finite : Fintype ι

structure FinitePresentation extends FiniteGeneratingSystem G where
  /-- The relations on the generators. -/
  rels : Finset (FreeGroup ι)
  /-- The normal closure of `rels` is the kernel of the induced map. -/
  ker_eq : MonoidHom.ker (FreeGroup.lift val) = Subgroup.normalClosure rels

def expe (ι : Type*) [Fintype ι] : FinitePresentation G → Presentation G :=
  fun P ↦
    { ι := P.ι
      val := P.val
      gen := P.gen
      rels := P.rels.toSet
      ker_eq := P.ker_eq }-/


def IsFinitelyPresented : Prop :=
  ∃ (P : Presentation G), IsFinitePresentation G P


def ReidemeisterSchreierMethod
{G_pres : Presentation G} (G_fin_pres : IsFinitePresentation G G_pres)
{H : Subgroup G} (H_fi : Subgroup.FiniteIndex H) :
Presentation H :=
  sorry

variable {G_pres : Presentation G} (G_fin_pres : IsFinitePresentation G G_pres) {H : Subgroup G} (H_fi : Subgroup.FiniteIndex H)

def H_p := ReidemeisterSchreierMethod G G_fin_pres H_fi
#check ReidemeisterSchreierMethod

#check ReidemeisterSchreierMethod
theorem ReidemeisterSchreierFinite
{G_pres : Presentation G} (G_fin_pres : IsFinitePresentation G G_pres)
{H : Subgroup G} (H_fi : Subgroup.FiniteIndex H) : Prop :=
  let H_p := ReidemeisterSchreierMethod G G_fin_pres H_fi
  IsFinitePresentation ↑H H_p

theorem FiniteIndex_in_FP_is_FP
(G_fp : FinitelyPresented G) {H : Subgroup G} (H_fp : Subgroup.FiniteIndex H) :
  FinitelyPresented H := by
  sorry
