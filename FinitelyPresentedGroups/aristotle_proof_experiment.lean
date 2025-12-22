--- experiment with Aristotle, slightly cleaned up
def presZ : Presentation (Multiplicative ℤ) (Fin 1) :=
  { val := fun _ ↦ Multiplicative.ofAdd 1
    gen := by
      simp [ Subgroup.eq_top_iff' ]
      --- simp ( config := { decide := Bool.true } ) [ Subgroup.eq_top_iff' ];
      intro a;
      induction a using Int.induction_on <;> aesop
    rels := ∅
    ker_eq := by
      ext;
      aesop
      --- generalize_proofs at *;
      · -- Since the free group on one generator is isomorphic to the integers, any element x can be written as a power of the generator.
        have h_iso : ∀ x : FreeGroup (Fin 1), ∃ n : ℤ, x = FreeGroup.of 0 ^ n := by
          intro x
          induction' x using FreeGroup.induction_on with x ih;
          · exact ⟨ 0, by simp ⟩;
          · exact ⟨ 1, by fin_cases x; simp ⟩;
          · rcases ‹_› with ⟨ n, hn ⟩ ; exact ⟨ -n, by rw [ hn, zpow_neg ] ⟩;
          · aesop;
            exact ⟨ w + w_1, by rw [ zpow_add ] ⟩;
        -- Since the lift of x is 1, n must be zero. Therefore, x is the identity element.
        obtain ⟨n, hn⟩ := h_iso x
        have hn_zero : n = 0 := by
          replace a := congr_arg Multiplicative.toAdd a ; aesop;
        aesop;
      · simp_all [ Subgroup.normalClosure, Subgroup.closure, Group.conjugatesOfSet ];
        }
       --- simp_all [ Subgroup.closure, Group.conjugatesOfSet ]}
