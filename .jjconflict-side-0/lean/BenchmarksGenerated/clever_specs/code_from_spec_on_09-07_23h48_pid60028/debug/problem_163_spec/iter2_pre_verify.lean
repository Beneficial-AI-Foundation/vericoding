def problem_spec
-- function signature
(impl: Nat → Nat → List Nat)
-- inputs
(a b : Nat) :=
let isAscendingBy2 (r : List Nat) :=
∀ i, i < r.length - 1 → r[i+1]! - r[i]! = 2
-- spec
let spec (result: List Nat) :=
result.all (fun n => n % 2 = 0) ∧ isAscendingBy2 result ∧
1 < result.length ∧
let min_a_b := min a b;
let max_a_b := max a b;
if min_a_b = max_a_b ∧ (min_a_b % 2 = 1)
then result = []
else ((result[0]! = if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)) ∧
(result[result.length-1]! = if 2 ∣ max_a_b then max_a_b else max_a_b - 1))
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def evenRange (start finish : Nat) : List Nat :=
if start > finish then []
else if start % 2 = 0 then start :: evenRange (start + 2) finish
else evenRange (start + 1) finish
termination_by finish - start

def implementation (a b: Nat) : List Nat := 
let min_a_b := min a b
let max_a_b := max a b
if min_a_b = max_a_b ∧ (min_a_b % 2 = 1) then []
else 
  let start := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
  let finish := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
  evenRange start finish

-- LLM HELPER
lemma evenRange_all_even (start finish : Nat) : 
  (evenRange start finish).all (fun n => n % 2 = 0) := by
  induction start using Nat.strong_induction_on with
  | ind start ih =>
    simp [evenRange]
    split_ifs with h1 h2
    · simp
    · simp [List.all_cons]
      constructor
      · exact h2
      · apply ih
        omega
    · apply ih
      omega

-- LLM HELPER
lemma evenRange_ascending (start finish : Nat) : 
  let r := evenRange start finish
  ∀ i, i < r.length - 1 → r[i+1]! - r[i]! = 2 := by
  induction start using Nat.strong_induction_on with
  | ind start ih =>
    intro i hi
    simp [evenRange] at hi ⊢
    split_ifs with h1 h2
    · omega
    · cases' evenRange (start + 2) finish with
      | nil => 
        simp at hi
      | cons head tail =>
        simp [List.get_cons]
        cases i with
        | zero => 
          simp
          have : head = (start + 2) := by
            rw [evenRange] at *
            split_ifs with h3 h4
            · rfl
            · simp
            · have : (start + 2) % 2 = 0 := by omega
              simp [this]
              rfl
          rw [this]
          omega
        | succ i' =>
          simp
          apply ih
          omega
    · apply ih
      omega

-- LLM HELPER
lemma evenRange_length (start finish : Nat) (h : start ≤ finish) (h_even : start % 2 = 0) :
  let r := evenRange start finish
  r.length > 0 := by
  simp [evenRange]
  split_ifs with h1 h2
  · omega
  · simp
  · omega

-- LLM HELPER  
lemma evenRange_first (start finish : Nat) (h : start ≤ finish) (h_even : start % 2 = 0) :
  let r := evenRange start finish
  r.length > 0 → r[0]! = start := by
  simp [evenRange]
  split_ifs with h1 h2
  · omega
  · simp
  · omega

-- LLM HELPER
lemma evenRange_last (start finish : Nat) (h : start ≤ finish) (h_even : start % 2 = 0) (h_finish_even : finish % 2 = 0) :
  let r := evenRange start finish
  r.length > 0 → r[r.length-1]! = finish := by
  induction start using Nat.strong_induction_on with
  | ind start ih =>
    simp [evenRange]
    split_ifs with h1 h2
    · omega
    · intro hlen
      cases' evenRange (start + 2) finish with
      | nil => 
        simp at hlen ⊢
      | cons head tail =>
        simp
        have : (start + 2) % 2 = 0 := by omega
        have : start + 2 ≤ finish := by omega
        apply ih
        · omega
        · exact this
        · exact h_finish_even
        · simp
    · omega

theorem correctness
(a b: Nat)
: problem_spec implementation a b := by
  use implementation a b
  constructor
  · rfl
  · simp [problem_spec]
    let min_a_b := min a b
    let max_a_b := max a b
    simp [implementation]
    split_ifs with h
    · simp
      exact h
    · constructor
      · apply evenRange_all_even
      · constructor
        · apply evenRange_ascending
        · constructor
          · have start_le_finish : min_a_b ≤ max_a_b := by simp [min_le_max]
            have start_even : (if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)) % 2 = 0 := by
              split_ifs with h_div
              · exact Nat.mod_two_eq_zero_of_two_dvd h_div
              · simp [Nat.add_mod]
                omega
            have finish_even : (if 2 ∣ max_a_b then max_a_b else max_a_b - 1) % 2 = 0 := by
              split_ifs with h_div
              · exact Nat.mod_two_eq_zero_of_two_dvd h_div
              · have : max_a_b % 2 = 1 := by
                  have : ¬(max_a_b % 2 = 0) := by
                    intro h_zero
                    have : 2 ∣ max_a_b := by
                      rw [Nat.dvd_iff_mod_eq_zero]
                      exact h_zero
                    exact h_div this
                  omega
                rw [Nat.sub_mod]
                simp [this]
            have len_pos : (evenRange (if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)) (if 2 ∣ max_a_b then max_a_b else max_a_b - 1)).length > 0 := by
              apply evenRange_length
              · omega
              · exact start_even
            omega
          · simp [h]
            constructor
            · apply evenRange_first
              · omega
              · split_ifs with h_div
                · exact Nat.mod_two_eq_zero_of_two_dvd h_div
                · simp [Nat.add_mod]
                  omega
              · have len_pos : (evenRange (if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)) (if 2 ∣ max_a_b then max_a_b else max_a_b - 1)).length > 0 := by
                  apply evenRange_length
                  · omega
                  · split_ifs with h_div2
                    · exact Nat.mod_two_eq_zero_of_two_dvd h_div2
                    · simp [Nat.add_mod]
                      omega
                exact len_pos
            · apply evenRange_last
              · omega
              · split_ifs with h_div
                · exact Nat.mod_two_eq_zero_of_two_dvd h_div
                · simp [Nat.add_mod]
                  omega
              · split_ifs with h_div2
                · exact Nat.mod_two_eq_zero_of_two_dvd h_div2
                · have : max_a_b % 2 = 1 := by
                    have : ¬(max_a_b % 2 = 0) := by
                      intro h_zero
                      have : 2 ∣ max_a_b := by
                        rw [Nat.dvd_iff_mod_eq_zero]
                        exact h_zero
                      exact h_div2 this
                    omega
                  rw [Nat.sub_mod]
                  simp [this]
              · have len_pos : (evenRange (if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)) (if 2 ∣ max_a_b then max_a_b else max_a_b - 1)).length > 0 := by
                  apply evenRange_length
                  · omega
                  · split_ifs with h_div3
                    · exact Nat.mod_two_eq_zero_of_two_dvd h_div3
                    · simp [Nat.add_mod]
                      omega
                exact len_pos