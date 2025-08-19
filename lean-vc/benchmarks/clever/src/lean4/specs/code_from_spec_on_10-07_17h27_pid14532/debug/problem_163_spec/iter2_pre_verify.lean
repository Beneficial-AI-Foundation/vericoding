import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def range_evens (start stop : Nat) : List Nat :=
  if start > stop then []
  else if start = stop then [start]
  else start :: range_evens (start + 2) stop
termination_by stop - start

def implementation (a b: Nat) : List Nat := 
  let min_a_b := min a b
  let max_a_b := max a b
  if min_a_b = max_a_b ∧ (min_a_b % 2 = 1) then []
  else
    let start := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
    let stop := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
    range_evens start stop

-- LLM HELPER
lemma range_evens_all_even (start stop : Nat) (h : start % 2 = 0) : 
  (range_evens start stop).all (fun n => n % 2 = 0) := by
  induction' start, stop using range_evens.induct with
  | case1 start stop h1 => simp [range_evens, h1]
  | case2 start stop h1 h2 => simp [range_evens, h1, h2, h]
  | case3 start stop h1 h2 ih =>
    simp [range_evens, h1, h2]
    constructor
    · exact h
    · apply ih
      simp [Nat.add_mod]
      exact h

-- LLM HELPER
lemma range_evens_ascending (start stop : Nat) (h : start % 2 = 0) :
  ∀ i, i < (range_evens start stop).length - 1 → 
    (range_evens start stop)[i+1]! - (range_evens start stop)[i]! = 2 := by
  induction' start, stop using range_evens.induct with
  | case1 start stop h1 => simp [range_evens, h1]
  | case2 start stop h1 h2 => simp [range_evens, h1, h2]
  | case3 start stop h1 h2 ih =>
    simp [range_evens, h1, h2]
    intro i hi
    cases' i with i
    · simp
      ring
    · simp
      apply ih
      simp [Nat.add_mod]
      exact h
      simp at hi
      exact hi

-- LLM HELPER
lemma range_evens_length (start stop : Nat) (h1 : start % 2 = 0) (h2 : start < stop) :
  1 < (range_evens start stop).length := by
  induction' start, stop using range_evens.induct with
  | case1 start stop h3 => 
    simp at h3
    omega
  | case2 start stop h3 h4 => 
    simp at h4
    omega
  | case3 start stop h3 h4 ih =>
    simp [range_evens, h3, h4]
    by_cases h5 : start + 2 > stop
    · simp [range_evens, h5]
    · by_cases h6 : start + 2 = stop
      · simp [range_evens, h5, h6]
      · simp [range_evens, h5, h6]
        apply Nat.succ_lt_succ
        apply ih
        simp [Nat.add_mod]
        exact h1
        omega

-- LLM HELPER
lemma range_evens_first_last (start stop : Nat) (h1 : start % 2 = 0) (h2 : start ≤ stop) :
  (range_evens start stop).length > 0 →
  (range_evens start stop)[0]! = start ∧ 
  (range_evens start stop)[(range_evens start stop).length - 1]! = stop := by
  induction' start, stop using range_evens.induct with
  | case1 start stop h3 => 
    simp [range_evens, h3]
    omega
  | case2 start stop h3 h4 => 
    simp [range_evens, h3, h4]
    intro
    constructor
    · rfl
    · simp
  | case3 start stop h3 h4 ih =>
    simp [range_evens, h3, h4]
    intro h5
    constructor
    · rfl
    · simp
      apply ih
      simp [Nat.add_mod]
      exact h1
      omega
      omega

theorem correctness
(a b: Nat)
: problem_spec implementation a b := by
  simp [problem_spec, implementation]
  let min_a_b := min a b
  let max_a_b := max a b
  by_cases h : min_a_b = max_a_b ∧ (min_a_b % 2 = 1)
  · simp [h]
    use []
    simp
  · simp [h]
    let start := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
    let stop := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
    use range_evens start stop
    constructor
    · rfl
    · constructor
      · apply range_evens_all_even
        simp [start]
        by_cases h1 : 2 ∣ min_a_b
        · simp [h1]
          exact Nat.mod_two_eq_zero_iff.mpr h1
        · simp [h1]
          simp [Nat.add_mod]
          rw [Nat.mod_two_eq_zero_iff] at h1
          simp [h1]
      · constructor
        · apply range_evens_ascending
          simp [start]
          by_cases h1 : 2 ∣ min_a_b
          · simp [h1]
            exact Nat.mod_two_eq_zero_iff.mpr h1
          · simp [h1]
            simp [Nat.add_mod]
            rw [Nat.mod_two_eq_zero_iff] at h1
            simp [h1]
        · constructor
          · apply range_evens_length
            simp [start]
            by_cases h1 : 2 ∣ min_a_b
            · simp [h1]
              exact Nat.mod_two_eq_zero_iff.mpr h1
            · simp [h1]
              simp [Nat.add_mod]
              rw [Nat.mod_two_eq_zero_iff] at h1
              simp [h1]
            · simp [start, stop]
              push_neg at h
              cases' h with h h
              · by_cases h1 : 2 ∣ min_a_b
                · by_cases h2 : 2 ∣ max_a_b
                  · simp [h1, h2]
                    exact Nat.lt_of_le_of_ne (Nat.min_le_max a b) h
                  · simp [h1, h2]
                    omega
                · by_cases h2 : 2 ∣ max_a_b
                  · simp [h1, h2]
                    omega
                  · simp [h1, h2]
                    omega
              · omega
          · have h_pos : (range_evens start stop).length > 0 := by
              apply Nat.lt_trans
              · norm_num
              · apply range_evens_length
                simp [start]
                by_cases h1 : 2 ∣ min_a_b
                · simp [h1]
                  exact Nat.mod_two_eq_zero_iff.mpr h1
                · simp [h1]
                  simp [Nat.add_mod]
                  rw [Nat.mod_two_eq_zero_iff] at h1
                  simp [h1]
                · simp [start, stop]
                  push_neg at h
                  cases' h with h h
                  · by_cases h1 : 2 ∣ min_a_b
                    · by_cases h2 : 2 ∣ max_a_b
                      · simp [h1, h2]
                        exact Nat.lt_of_le_of_ne (Nat.min_le_max a b) h
                      · simp [h1, h2]
                        omega
                    · by_cases h2 : 2 ∣ max_a_b
                      · simp [h1, h2]
                        omega
                      · simp [h1, h2]
                        omega
                  · omega
            apply range_evens_first_last
            · simp [start]
              by_cases h1 : 2 ∣ min_a_b
              · simp [h1]
                exact Nat.mod_two_eq_zero_iff.mpr h1
              · simp [h1]
                simp [Nat.add_mod]
                rw [Nat.mod_two_eq_zero_iff] at h1
                simp [h1]
            · simp [start, stop]
              push_neg at h
              cases' h with h h
              · by_cases h1 : 2 ∣ min_a_b
                · by_cases h2 : 2 ∣ max_a_b
                  · simp [h1, h2]
                    exact Nat.min_le_max a b
                  · simp [h1, h2]
                    omega
                · by_cases h2 : 2 ∣ max_a_b
                  · simp [h1, h2]
                    omega
                  · simp [h1, h2]
                    omega
              · omega
            · exact h_pos