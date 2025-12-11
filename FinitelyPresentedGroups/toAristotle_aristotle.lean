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
    gen := by
      simp ( config := { decide := Bool.true } ) [ Subgroup.eq_top_iff' ];
      intro a;
      induction a using Int.induction_on <;> aesop
    rels := ∅
    ker_eq := by
      ext;
      aesop
      generalize_proofs at *;
      · -- Since the free group on one generator is isomorphic to the integers, any element x can be written as a power of the generator.
        have h_iso : ∀ x : FreeGroup (Fin 1), ∃ n : ℤ, x = FreeGroup.of 0 ^ n := by
          intro x
          induction' x using FreeGroup.induction_on with x ih;
          · exact ⟨ 0, by simp +decide ⟩;
          · exact ⟨ 1, by fin_cases x; simp +decide ⟩;
          · rcases ‹_› with ⟨ n, hn ⟩ ; exact ⟨ -n, by rw [ hn, zpow_neg ] ⟩;
          · aesop;
            exact ⟨ w + w_1, by rw [ zpow_add ] ⟩;
        -- Since the lift of x is 1, n must be zero. Therefore, x is the identity element.
        obtain ⟨n, hn⟩ := h_iso x
        have hn_zero : n = 0 := by
          replace a := congr_arg Multiplicative.toAdd a ; aesop;
        aesop;
      · simp_all +decide [ Subgroup.normalClosure ];
        simp_all +decide [ Subgroup.closure, Group.conjugatesOfSet ]}

open scoped Pointwise

def IsFinitelyPresented.{u} (G : Type u) [Group G] : Prop :=
  Nonempty ((ι : Type u) × (_ : Fintype ι) × (FinitePresentation G ι))

/-
TODO: fix and fill in the def, then dispatch the theorem to the ATP.

def IsFinitelyPresented.{u} (G : Type u) [Group G] : Prop :=
  Nonempty ((ι : Type u) × (_ : Fintype ι) × (FinitePresentation G ι))

def ReidemeisterSchreierMethod.{u} {ι : Type u} [Fintype ι] {G : Type u} [Group G]
    (H : Subgroup G)
    (P : FinitePresentation G ι) -- G is presented by generators ι
    (T : Finset G) -- The transversal
    -- These are from `Subgroup.closure_mul_image_mul_eq_top`
    (hT : Subgroup.IsComplement H (T : Set G)) -- T is a right transversal
    -- TODO: should be Hg, not gH?
    (hT_covers : ⋃ g ∈ T, (g : G) • (H : Set G) = ⊤) -- T covers H
    (hT1 : (1 : G) ∈ T) -- 1 is in T
    -- Definition: T is a Schreier transversal if it is prefix-closed with respect to generators of P.
    -- TODO: we need some order relation to prevent cycles, i.e. t' < t.
    (hT_is_schreier : ∀ t ∈ T, t ≠ 1 → ∃ t' ∈ T, ∃ i : ι, t = t' * P.val i ∨ t = t' * (P.val i)⁻¹)
    : FinitePresentation H (T × ι) := by -- H is presented by T × ι
  sorry

theorem reidemeister_schreier {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    (hG : IsFinitelyPresented G) : IsFinitelyPresented H := by
  -- obtain a *Finset* *Schreier* right transversal somehow
  -- and then call ReidemeisterSchreierMethod
  sorry

-/
