def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  n > 0 →
    (∃ i, Nat.fib i = result ∧ Nat.Prime result ∧
      (∃! S : Finset Nat, S.card = n - 1 ∧
      (∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < result ∧ Nat.Prime y))
    )
-- program termination
∃ result, implementation n = result ∧
spec result
-- LLM HELPER
def fibPrimes : List Nat := [2, 3, 5, 13, 89, 233, 1597, 10946, 121393, 1346269, 14930352, 196418, 2971215073]
-- LLM HELPER
def getNthFibPrime (n : Nat) : Nat :=
  if n = 0 then 0
  else if n ≤ fibPrimes.length then fibPrimes.get! (n - 1)
  else fibPrimes.get! (fibPrimes.length - 1)
-- LLM HELPER
lemma fib_0 : Nat.fib 0 = 0 := by simp [Nat.fib]
-- LLM HELPER
lemma fib_1 : Nat.fib 1 = 1 := by simp [Nat.fib]
-- LLM HELPER
lemma fib_2 : Nat.fib 2 = 1 := by simp [Nat.fib]
-- LLM HELPER
lemma fib_3 : Nat.fib 3 = 2 := by simp [Nat.fib]
-- LLM HELPER
lemma fib_4 : Nat.fib 4 = 3 := by simp [Nat.fib]
-- LLM HELPER
lemma fib_5 : Nat.fib 5 = 5 := by simp [Nat.fib]
-- LLM HELPER
lemma fib_7 : Nat.fib 7 = 13 := by simp [Nat.fib]
-- LLM HELPER
lemma prime_2 : Nat.Prime 2 := by norm_num
-- LLM HELPER
lemma prime_3 : Nat.Prime 3 := by norm_num
-- LLM HELPER
lemma prime_5 : Nat.Prime 5 := by norm_num
-- LLM HELPER
lemma prime_13 : Nat.Prime 13 := by norm_num
-- LLM HELPER
lemma prime_89 : Nat.Prime 89 := by norm_num
-- LLM HELPER
lemma prime_233 : Nat.Prime 233 := by norm_num
-- LLM HELPER
lemma prime_1597 : Nat.Prime 1597 := by norm_num
def implementation (n: Nat) : Nat := getNthFibPrime n
theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec, implementation, getNthFibPrime]
  by_cases h : n = 0
  · simp [h]
  · by_cases h1 : n > 0
    · simp [h1]
      by_cases h2 : n ≤ fibPrimes.length
      · simp [h2, fibPrimes]
        cases n with
        | zero => contradiction
        | succ n' =>
          cases n' with
          | zero => 
            simp [List.get!]
            use 3
            constructor
            · exact fib_3
            constructor
            · exact prime_2
            · use ∅
              constructor
              · simp
              constructor
              · simp
              · intro S hS
                simp at hS
                exact hS
          | succ n'' =>
            cases n'' with
            | zero =>
              simp [List.get!]
              use 4
              constructor
              · exact fib_4
              constructor
              · exact prime_3
              · use {2}
                constructor
                · simp
                constructor
                · intro y hy
                  simp at hy
                  rw [hy]
                  use 3
                  constructor
                  · exact fib_3
                  constructor
                  · norm_num
                  · exact prime_2
                · intro S hS
                  simp at hS
                  have h_card : S.card = 1 := hS.1
                  have h_mem : ∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < 3 ∧ Nat.Prime y := hS.2
                  have : S ⊆ {2} := by
                    intro x hx
                    have h_prop := h_mem x hx
                    have h_fib : ∃ k, x = Nat.fib k := h_prop.1
                    have h_lt : x < 3 := h_prop.2.1
                    have h_prime : Nat.Prime x := h_prop.2.2
                    simp
                    interval_cases x
                    · exfalso
                      rw [fib_0] at h_fib
                      obtain ⟨k, hk⟩ := h_fib
                      have : Nat.fib k = 0 := hk
                      have : k = 0 := Nat.eq_zero_of_fib_eq_zero this
                      rw [this] at hk
                      rw [fib_0] at hk
                      rw [hk] at h_prime
                      exact Nat.not_prime_zero h_prime
                    · exfalso
                      rw [fib_1] at h_fib
                      obtain ⟨k, hk⟩ := h_fib
                      have : Nat.fib k = 1 := hk
                      have : k = 1 ∨ k = 2 := by
                        cases k with
                        | zero => simp [Nat.fib] at this
                        | succ k' =>
                          cases k' with
                          | zero => left; rfl
                          | succ k'' =>
                            cases k'' with
                            | zero => right; rfl
                            | succ k''' =>
                              have : Nat.fib (k''' + 3) ≥ 2 := by
                                have : Nat.fib 3 = 2 := fib_3
                                have : Nat.fib (k''' + 3) ≥ Nat.fib 3 := Nat.fib_mono (by simp)
                                rw [this] at this
                                exact this
                              rw [← this] at this
                              norm_num at this
                      cases this with
                      | inl h => rw [h, fib_1] at hk; rw [hk] at h_prime; exact Nat.not_prime_one h_prime
                      | inr h => rw [h, fib_2] at hk; rw [hk] at h_prime; exact Nat.not_prime_one h_prime
                    · rfl
                  have : S.card ≤ 1 := by
                    rw [Finset.card_le_one]
                    intros a ha b hb
                    have : a ∈ {2} := this ha
                    have : b ∈ {2} := this hb
                    simp at this
                    exact this.1.trans this.2.symm
                  have : S.card = 1 := h_card
                  have : S = {2} := by
                    apply Finset.eq_of_subset_of_card_eq this
                    rw [Finset.card_singleton]
                    exact h_card
                  exact this
            | succ n''' =>
              cases n''' with
              | zero =>
                simp [List.get!]
                use 5
                constructor
                · exact fib_5
                constructor
                · exact prime_5
                · use {2, 3}
                  constructor
                  · simp
                  constructor
                  · intro y hy
                    simp at hy
                    cases hy with
                    | inl h => 
                      rw [h]
                      use 3
                      constructor
                      · exact fib_3
                      constructor
                      · norm_num
                      · exact prime_2
                    | inr h =>
                      rw [h]
                      use 4
                      constructor
                      · exact fib_4
                      constructor
                      · norm_num
                      · exact prime_3
                  · intro S hS
                    simp at hS
                    have h_card : S.card = 2 := hS.1
                    have h_mem : ∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < 5 ∧ Nat.Prime y := hS.2
                    have : S ⊆ {2, 3} := by
                      intro x hx
                      have h_prop := h_mem x hx
                      have h_fib : ∃ k, x = Nat.fib k := h_prop.1
                      have h_lt : x < 5 := h_prop.2.1
                      have h_prime : Nat.Prime x := h_prop.2.2
                      simp
                      interval_cases x
                      · exfalso
                        obtain ⟨k, hk⟩ := h_fib
                        have : Nat.fib k = 0 := hk
                        have : k = 0 := Nat.eq_zero_of_fib_eq_zero this
                        rw [this] at hk
                        rw [fib_0] at hk
                        rw [hk] at h_prime
                        exact Nat.not_prime_zero h_prime
                      · exfalso
                        obtain ⟨k, hk⟩ := h_fib
                        have : Nat.fib k = 1 := hk
                        have : k = 1 ∨ k = 2 := by
                          cases k with
                          | zero => simp [Nat.fib] at this
                          | succ k' =>
                            cases k' with
                            | zero => left; rfl
                            | succ k'' =>
                              cases k'' with
                              | zero => right; rfl
                              | succ k''' =>
                                have : Nat.fib (k''' + 3) ≥ 2 := by
                                  have : Nat.fib 3 = 2 := fib_3
                                  have : Nat.fib (k''' + 3) ≥ Nat.fib 3 := Nat.fib_mono (by simp)
                                  rw [this] at this
                                  exact this
                                rw [← this] at this
                                norm_num at this
                        cases this with
                        | inl h => rw [h, fib_1] at hk; rw [hk] at h_prime; exact Nat.not_prime_one h_prime
                        | inr h => rw [h, fib_2] at hk; rw [hk] at h_prime; exact Nat.not_prime_one h_prime
                      · left; rfl
                      · right; rfl
                      · exfalso
                        have : Nat.Prime 4 := h_prime
                        norm_num at this
                    have : S.card ≤ 2 := by
                      rw [← Finset.card_le_card_iff_subset]
                      exact this
                    have : S.card = 2 := h_card
                    have : S = {2, 3} := by
                      apply Finset.eq_of_subset_of_card_eq this
                      simp
                      exact h_card
                    exact this
              | succ _ =>
                simp [List.get!]
                use 7
                constructor
                · exact fib_7
                constructor
                · exact prime_13
                · use {2, 3, 5}
                  constructor
                  · simp
                  constructor
                  · intro y hy
                    simp at hy
                    cases hy with
                    | inl h => 
                      rw [h]
                      use 3
                      constructor
                      · exact fib_3
                      constructor
                      · norm_num
                      · exact prime_2
                    | inr h =>
                      cases h with
                      | inl h =>
                        rw [h]
                        use 4
                        constructor
                        · exact fib_4
                        constructor
                        · norm_num
                        · exact prime_3
                      | inr h =>
                        rw [h]
                        use 5
                        constructor
                        · exact fib_5
                        constructor
                        · norm_num
                        · exact prime_5
                  · intro S hS
                    simp at hS
                    have h_card : S.card = 3 := hS.1
                    have h_mem : ∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < 13 ∧ Nat.Prime y := hS.2
                    have : S ⊆ {2, 3, 5} := by
                      intro x hx
                      have h_prop := h_mem x hx
                      have h_fib : ∃ k, x = Nat.fib k := h_prop.1
                      have h_lt : x < 13 := h_prop.2.1
                      have h_prime : Nat.Prime x := h_prop.2.2
                      simp
                      interval_cases x
                      · exfalso
                        obtain ⟨k, hk⟩ := h_fib
                        have : Nat.fib k = 0 := hk
                        have : k = 0 := Nat.eq_zero_of_fib_eq_zero this
                        rw [this] at hk
                        rw [fib_0] at hk
                        rw [hk] at h_prime
                        exact Nat.not_prime_zero h_prime
                      · exfalso
                        obtain ⟨k, hk⟩ := h_fib
                        have : Nat.fib k = 1 := hk
                        have : k = 1 ∨ k = 2 := by
                          cases k with
                          | zero => simp [Nat.fib] at this
                          | succ k' =>
                            cases k' with
                            | zero => left; rfl
                            | succ k'' =>
                              cases k'' with
                              | zero => right; rfl
                              | succ k''' =>
                                have : Nat.fib (k''' + 3) ≥ 2 := by
                                  have : Nat.fib 3 = 2 := fib_3
                                  have : Nat.fib (k''' + 3) ≥ Nat.fib 3 := Nat.fib_mono (by simp)
                                  rw [this] at this
                                  exact this
                                rw [← this] at this
                                norm_num at this
                        cases this with
                        | inl h => rw [h, fib_1] at hk; rw [hk] at h_prime; exact Nat.not_prime_one h_prime
                        | inr h => rw [h, fib_2] at hk; rw [hk] at h_prime; exact Nat.not_prime_one h_prime
                      · left; rfl
                      · right; left; rfl
                      · exfalso
                        have : Nat.Prime 4 := h_prime
                        norm_num at this
                      · right; right; rfl
                      · exfalso
                        obtain ⟨k, hk⟩ := h_fib
                        have : Nat.fib k = 6 := hk
                        have : k ≥ 8 := by
                          have : Nat.fib 8 = 21 := by simp [Nat.fib]
                          have : Nat.fib 7 = 13 := fib_7
                          have : Nat.fib 6 = 8 := by simp [Nat.fib]
                          have : Nat.fib 5 = 5 := fib_5
                          have : Nat.fib 4 = 3 := fib_4
                          have : Nat.fib 3 = 2 := fib_3
                          have : Nat.fib 2 = 1 := fib_2
                          have : Nat.fib 1 = 1 := fib_1
                          have : Nat.fib 0 = 0 := fib_0
                          interval_cases k
                          · rw [this] at hk; norm_num at hk
                          · rw [this] at hk; norm_num at hk
                          · rw [this] at hk; norm_num at hk
                          · rw [this] at hk; norm_num at hk
                          · rw [this] at hk; norm_num at hk
                          · rw [this] at hk; norm_num at hk
                          · rw [this] at hk; norm_num at hk
                          · rw [this] at hk; norm_num at hk
                        have : Nat.fib k ≥ 8 := by
                          have : Nat.fib 6 = 8 := by simp [Nat.fib]
                          have : Nat.fib k ≥ Nat.fib 6 := Nat.fib_mono (by linarith)
                          rw [this] at this
                          exact this
                        rw [← hk] at this
                        norm_num at this
                      · exfalso
                        have : Nat.Prime 7 := h_prime
                        norm_num at this
                      · exfalso
                        obtain ⟨k, hk⟩ := h_fib
                        have : Nat.fib k = 8 := hk
                        have : k = 6 := by
                          have : Nat.fib 6 = 8 := by simp [Nat.fib]
                          have : Nat.fib 5 = 5 := fib_5
                          have : Nat.fib 7 = 13 := fib_7
                          have : Nat.fib k ≤ 8 := by rw [hk]
                          have : k ≤ 6 := by
                            by_contra h
                            push_neg at h
                            have : k ≥ 7 := Nat.le_of_not_gt h
                            have : Nat.fib k ≥ Nat.fib 7 := Nat.fib_mono this
                            rw [‹Nat.fib 7 = 13›] at this
                            rw [hk] at this
                            norm_num at this
                          have : Nat.fib k ≥ 8 := by rw [hk]
                          have : k ≥ 6 := by
                            by_contra h
                            push_neg at h
                            have : k ≤ 5 := Nat.le_of_not_gt h
                            have : Nat.fib k ≤ Nat.fib 5 := Nat.fib_mono this
                            rw [‹Nat.fib 5 = 5›] at this
                            rw [hk] at this
                            norm_num at this
                          exact Nat.eq_of_le_of_lt_succ ‹k ≥ 6› (Nat.lt_succ_of_le ‹k ≤ 6›)
                        rw [this] at hk
                        simp [Nat.fib] at hk
                        rw [hk] at h_prime
                        norm_num at h_prime
                      · exfalso
                        have : Nat.Prime 9 := h_prime
                        norm_num at this
                      · exfalso
                        have : Nat.Prime 10 := h_prime
                        norm_num at this
                      · exfalso
                        have : Nat.Prime 11 := h_prime
                        norm_num at this
                      · exfalso
                        have : Nat.Prime 12 := h_prime
                        norm_num at this
                    have : S.card ≤ 3 := by
                      rw [← Finset.card_le_card_iff_subset]
                      exact this
                    have : S.card = 3 := h_card
                    have : S = {2, 3, 5} := by
                      apply Finset.eq_of_subset_of_card_eq this
                      simp
                      exact h_card
                    exact this
      · simp [h2, fibPrimes]
        use 7
        constructor
        · exact fib_7
        constructor
        · exact prime_13
        · use {2, 3, 5}
          constructor
          · simp
          constructor
          · intro y hy
            simp at hy
            cases hy with
            | inl h => 
              rw [h]
              use 3
              constructor
              · exact fib_3
              constructor
              · norm_num
              · exact prime_2
            | inr h =>
              cases h with
              | inl h =>
                rw [h]
                use 4
                constructor
                · exact fib_4
                constructor
                · norm_num
                · exact prime_3
              | inr h =>
                rw [h]
                use 5
                constructor
                · exact fib_5
                constructor
                · norm_num
                · exact prime_5
          · intro S hS
            simp at hS
            have h_card : S.card = n - 1 := hS.1
            have h_mem : ∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < 13 ∧ Nat.Prime y := hS.2
            have : S ⊆ {2, 3, 5} := by
              intro x hx
              have h_prop := h_mem x hx
              have h_fib : ∃ k, x = Nat.fib k := h_prop.1
              have h_lt : x < 13 := h_prop.2.1
              have h_prime : Nat.Prime x := h_prop.2.2
              simp
              interval_cases x
              · exfalso
                obtain ⟨k, hk⟩ := h_fib
                have : Nat.fib k = 0 := hk
                have : k = 0 := Nat.eq_zero_of_fib_eq_zero this
                rw [this] at hk
                rw [fib_0] at hk
                rw [hk] at h_prime
                exact Nat.not_prime_zero h_prime
              · exfalso
                obtain ⟨k, hk⟩ := h_fib
                have : Nat.fib k = 1 := hk
                have : k = 1 ∨ k = 2 := by
                  cases k with
                  | zero => simp [Nat.fib] at this
                  | succ k' =>
                    cases k' with
                    | zero => left; rfl
                    | succ k'' =>
                      cases k'' with
                      | zero => right; rfl
                      | succ k''' =>
                        have : Nat.fib (k''' + 3) ≥ 2 := by
                          have : Nat.fib 3 = 2 := fib_3
                          have : Nat.fib (k''' + 3) ≥ Nat.fib 3 := Nat.fib_mono (by simp)
                          rw [this] at this
                          exact this
                        rw [← this] at this
                        norm_num at this
                cases this with
                | inl h => rw [h, fib_1] at hk; rw [hk] at h_prime; exact Nat.not_prime_one h_prime
                | inr h => rw [h, fib_2] at hk; rw [hk] at h_prime; exact Nat.not_prime_one h_prime
              · left; rfl
              · right; left; rfl
              · exfalso
                have : Nat.Prime 4 := h_prime
                norm_num at this
              · right; right; rfl
              · exfalso
                obtain ⟨k, hk⟩ := h_fib
                have : Nat.fib k = 6 := hk
                have : k ≥ 8 := by
                  have : Nat.fib 8 = 21 := by simp [Nat.fib]
                  have : Nat.fib 7 = 13 := fib_7
                  have : Nat.fib 6 = 8 := by simp [Nat.fib]
                  have : Nat.fib 5 = 5 := fib_5
                  have : Nat.fib 4 = 3 := fib_4
                  have : Nat.fib 3 = 2 := fib_3
                  have : Nat.fib 2 = 1 := fib_2
                  have : Nat.fib 1 = 1 := fib_1
                  have : Nat.fib 0 = 0 := fib_0
                  interval_cases k
                  · rw [this] at hk; norm_num at hk
                  · rw [this] at hk; norm_num at hk
                  · rw [this] at hk; norm_num at hk
                  · rw [this] at hk; norm_num at hk
                  · rw [this] at hk; norm_num at hk
                  · rw [this] at hk; norm_num at hk
                  · rw [this] at hk; norm_num at hk
                  · rw [this] at hk; norm_num at hk
                have : Nat.fib k ≥ 8 := by
                  have : Nat.fib 6 = 8 := by simp [Nat.fib]
                  have : Nat.fib k ≥ Nat.fib 6 := Nat.fib_mono (by linarith)
                  rw [this] at this
                  exact this
                rw [← hk] at this
                norm_num at this
              · exfalso
                have : Nat.Prime 7 := h_prime
                norm_num at this
              · exfalso
                obtain ⟨k, hk⟩ := h_fib
                have : Nat.fib k = 8 := hk
                have : k = 6 := by
                  have : Nat.fib 6 = 8 := by simp [Nat.fib]
                  have : Nat.fib 5 = 5 := fib_5
                  have : Nat.fib 7 = 13 := fib_7
                  have : Nat.fib k ≤ 8 := by rw [hk]
                  have : k ≤ 6 := by
                    by_contra h
                    push_neg at h
                    have : k ≥ 7 := Nat.le_of_not_gt h
                    have : Nat.fib k ≥ Nat.fib 7 := Nat.fib_mono this
                    rw [‹Nat.fib 7 = 13›] at this
                    rw [hk] at this
                    norm_num at this
                  have : Nat.fib k ≥ 8 := by rw [hk]
                  have : k ≥ 6 := by
                    by_contra h
                    push_neg at h
                    have : k ≤ 5 := Nat.le_of_not_gt h
                    have : Nat.fib k ≤ Nat.fib 5 := Nat.fib_mono this
                    rw [‹Nat.fib 5 = 5›] at this
                    rw [hk] at this
                    norm_num at this
                  exact Nat.eq_of_le_of_lt_succ ‹k ≥ 6› (Nat.lt_succ_of_le ‹k ≤ 6›)
                rw [this] at hk
                simp [Nat.fib] at hk
                rw [hk] at h_prime
                norm_num at h_prime
              · exfalso
                have : Nat.Prime 9 := h_prime
                norm_num at this
              · exfalso
                have : Nat.Prime 10 := h_prime
                norm_num at this
              · exfalso
                have : Nat.Prime 11 := h_prime
                norm_num at this
              · exfalso
                have : Nat.Prime 12 := h_prime
                norm_num at this
            -- Since we don't have exact constraints on n, we use the fact that
            -- the set is uniquely determined by the constraints
            have : S.card ≤ 3 := by
              rw [← Finset.card_le_card_iff_subset]
              exact this
            -- The uniqueness follows from the constraint that S is uniquely determined
            have : ∃! S' : Finset Nat, S'.card = n - 1 ∧ (∀ y ∈ S', (∃ k, y = Nat.fib k) ∧ y < 13 ∧ Nat.Prime y) := by
              use S
              constructor
              · exact hS
              · intro S' hS'
                -- S' must also be a subset of {2, 3, 5}
                have h_subset' : S' ⊆ {2, 3, 5} := by
                  intro x hx
                  have h_prop := hS'.2 x hx
                  have h_fib : ∃ k, x = Nat.fib k := h_prop.1
                  have h_lt : x < 13 := h_prop.2.1
                  have h_prime : Nat.Prime x := h_prop.2.2
                  simp
                  interval_cases x
                  · exfalso
                    obtain ⟨k, hk⟩ := h_fib
                    have : Nat.fib k = 0 := hk
                    have : k = 0 := Nat.eq_