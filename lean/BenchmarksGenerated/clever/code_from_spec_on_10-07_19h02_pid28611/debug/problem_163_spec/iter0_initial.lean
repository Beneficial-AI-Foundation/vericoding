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
def evenRange (start_even last_even : Nat) : List Nat :=
if start_even > last_even then []
else if start_even % 2 = 0 ∧ last_even % 2 = 0 then
  List.range ((last_even - start_even) / 2 + 1) |>.map (fun i => start_even + 2 * i)
else []

def implementation (a b: Nat) : List Nat := 
let min_a_b := min a b
let max_a_b := max a b
if min_a_b = max_a_b ∧ (min_a_b % 2 = 1) then []
else
  let start_even := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
  let last_even := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
  evenRange start_even last_even

-- LLM HELPER
lemma evenRange_spec (start_even last_even : Nat) (h1 : start_even % 2 = 0) (h2 : last_even % 2 = 0) (h3 : start_even ≤ last_even) :
  let result := evenRange start_even last_even
  result.all (fun n => n % 2 = 0) ∧ 
  (∀ i, i < result.length - 1 → result[i+1]! - result[i]! = 2) ∧
  (result.length > 0 → result[0]! = start_even) ∧
  (result.length > 0 → result[result.length-1]! = last_even) ∧
  (start_even < last_even → result.length > 1) := by
  simp [evenRange]
  split_ifs with h4
  · simp at h4
    omega
  · simp [h1, h2]
    constructor
    · -- all elements are even
      simp [List.all_eq_true]
      intro x hx
      simp [List.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx
      simp [Nat.add_mod, h1]
    constructor
    · -- ascending by 2
      intro i hi
      simp [List.length_map, List.length_range] at hi
      simp [List.getElem_map, List.getElem_range]
      ring
    constructor
    · -- first element
      intro h_len
      simp [List.length_map, List.length_range] at h_len
      simp [List.getElem_map, List.getElem_range]
    constructor
    · -- last element
      intro h_len
      simp [List.length_map, List.length_range] at h_len
      simp [List.getElem_map, List.getElem_range]
      have : (last_even - start_even) / 2 + 1 - 1 = (last_even - start_even) / 2 := by
        have : (last_even - start_even) / 2 + 1 ≥ 1 := by
          simp
        omega
      rw [this]
      have : start_even + 2 * ((last_even - start_even) / 2) = last_even := by
        have : start_even ≤ last_even := h3
        have : last_even - start_even = 2 * ((last_even - start_even) / 2) := by
          rw [Nat.mul_comm]
          exact Nat.two_mul_div_two_of_even (by
            rw [Nat.even_sub h3]
            simp [h1, h2])
        omega
      rw [this]
    · -- length > 1 when start_even < last_even
      intro h_lt
      simp [List.length_map, List.length_range]
      have : last_even - start_even ≥ 2 := by
        have : start_even + 2 ≤ last_even := by
          have : start_even < last_even := h_lt
          have : ∃ k, last_even = start_even + 2 * k ∧ k > 0 := by
            use (last_even - start_even) / 2
            constructor
            · have : last_even - start_even = 2 * ((last_even - start_even) / 2) := by
                rw [Nat.mul_comm]
                exact Nat.two_mul_div_two_of_even (by
                  rw [Nat.even_sub (le_of_lt h_lt)]
                  simp [h1, h2])
              omega
            · have : last_even - start_even > 0 := Nat.sub_pos_of_lt h_lt
              have : (last_even - start_even) / 2 > 0 := by
                have : last_even - start_even ≥ 2 := by
                  have : start_even + 1 < last_even := by
                    have : start_even < last_even := h_lt
                    have : start_even + 1 ≤ last_even := by
                      by_cases h : start_even + 1 ≤ last_even
                      · exact h
                      · simp at h
                        have : last_even ≤ start_even := by omega
                        have : start_even = last_even := by omega
                        omega
                    omega
                  omega
                exact Nat.div_pos this (by norm_num)
              exact this
          obtain ⟨k, hk1, hk2⟩ := this
          have : k ≥ 1 := by omega
          have : 2 * k ≥ 2 := by omega
          omega
        omega
      have : (last_even - start_even) / 2 ≥ 1 := by
        exact Nat.div_pos this (by norm_num)
      omega

-- LLM HELPER
lemma dvd_iff_mod_eq_zero (a b : Nat) : 2 ∣ a ↔ a % 2 = 0 := by
  constructor
  · intro h
    exact Nat.mod_eq_zero_of_dvd h
  · intro h
    exact Nat.dvd_of_mod_eq_zero h

theorem correctness
(a b: Nat)
: problem_spec implementation a b := by
  simp [problem_spec]
  use implementation a b
  constructor
  · rfl
  · simp [implementation]
    let min_a_b := min a b
    let max_a_b := max a b
    split_ifs with h
    · simp
      exact h.2
    · simp
      have h_not : ¬(min_a_b = max_a_b ∧ min_a_b % 2 = 1) := h
      simp at h_not
      cases' h_not with h_neq h_even
      · -- min_a_b ≠ max_a_b
        have h_lt : min_a_b < max_a_b := by
          have : min_a_b ≤ max_a_b := min_le_max
          omega
        let start_even := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
        let last_even := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
        have h_start_even : start_even % 2 = 0 := by
          simp [start_even]
          split_ifs with h_div
          · rw [dvd_iff_mod_eq_zero] at h_div
            exact h_div
          · rw [dvd_iff_mod_eq_zero] at h_div
            simp at h_div
            cases' Nat.mod_two_eq_zero_or_one min_a_b with h0 h1
            · contradiction
            · simp [h1]
        have h_last_even : last_even % 2 = 0 := by
          simp [last_even]
          split_ifs with h_div
          · rw [dvd_iff_mod_eq_zero] at h_div
            exact h_div
          · rw [dvd_iff_mod_eq_zero] at h_div
            simp at h_div
            cases' Nat.mod_two_eq_zero_or_one max_a_b with h0 h1
            · contradiction
            · simp [h1]
              cases' max_a_b with n
              · simp at h1
              · simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
        have h_le : start_even ≤ last_even := by
          simp [start_even, last_even]
          split_ifs with h1 h2
          · exact le_of_lt h_lt
          · have : min_a_b + 1 ≤ max_a_b := by omega
            exact this
          · have : min_a_b ≤ max_a_b - 1 := by omega
            exact this
          · have : min_a_b + 1 ≤ max_a_b - 1 := by omega
            exact this
        have h_lt_even : start_even < last_even := by
          simp [start_even, last_even]
          split_ifs with h1 h2
          · exact h_lt
          · have : min_a_b + 1 ≤ max_a_b := by omega
            have : min_a_b + 1 < max_a_b := by
              by_contra h_not
              simp at h_not
              have : min_a_b + 1 = max_a_b := by omega
              rw [dvd_iff_mod_eq_zero] at h2
              simp at h2
              cases' Nat.mod_two_eq_zero_or_one max_a_b with h0 h1_case
              · contradiction
              · have : max_a_b = min_a_b + 1 := by omega
                rw [this] at h1_case
                cases' Nat.mod_two_eq_zero_or_one min_a_b with h0_min h1_min
                · simp [h0_min] at h1_case
                · simp [h1_min] at h1_case
            exact this
          · have : min_a_b < max_a_b - 1 := by
              rw [dvd_iff_mod_eq_zero] at h2
              simp at h2
              cases' Nat.mod_two_eq_zero_or_one max_a_b with h0 h1_case
              · contradiction
              · have : max_a_b ≥ 1 := by
                  cases' max_a_b with n
                  · simp at h1_case
                  · simp
                have : max_a_b - 1 + 1 = max_a_b := by omega
                rw [← this]
                have : min_a_b + 1 ≤ max_a_b := by omega
                omega
            exact this
          · have : min_a_b + 1 < max_a_b - 1 := by
              have : min_a_b + 2 ≤ max_a_b := by
                rw [dvd_iff_mod_eq_zero] at h1 h2
                simp at h1 h2
                cases' Nat.mod_two_eq_zero_or_one min_a_b with h0_min h1_min
                · contradiction
                · cases' Nat.mod_two_eq_zero_or_one max_a_b with h0_max h1_max
                  · contradiction
                  · have : min_a_b < max_a_b := h_lt
                    have : min_a_b + 1 < max_a_b := by omega
                    have : min_a_b + 2 ≤ max_a_b := by omega
                    exact this
              have : max_a_b ≥ 1 := by omega
              omega
            exact this
        have spec_result := evenRange_spec start_even last_even h_start_even h_last_even h_le
        cases' spec_result with h_all h_rest
        cases' h_rest with h_asc h_rest2
        cases' h_rest2 with h_first h_rest3
        cases' h_rest3 with h_last h_len
        constructor
        · exact h_all
        constructor
        · exact h_asc
        constructor
        · have : start_even < last_even := h_lt_even
          have : evenRange start_even last_even |>.length > 1 := h_len this
          omega
        · constructor
          · have : evenRange start_even last_even |>.length > 0 := by
              have : start_even < last_even := h_lt_even
              have : evenRange start_even last_even |>.length > 1 := h_len this
              omega
            exact h_first this
          · have : evenRange start_even last_even |>.length > 0 := by
              have : start_even < last_even := h_lt_even
              have : evenRange start_even last_even |>.length > 1 := h_len this
              omega
            exact h_last this
      · -- min_a_b = max_a_b ∧ min_a_b % 2 = 0
        have h_eq : min_a_b = max_a_b := by
          have : min_a_b ≤ max_a_b := min_le_max
          have : max_a_b ≤ min_a_b := by
            cases' min_le_max with h_le h_le
            · have : min_a_b = max_a_b := by omega
              omega
            · omega
          omega
        have h_even_min : min_a_b % 2 = 0 := h_even
        let start_even := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
        let last_even := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
        have h_start : start_even = min_a_b := by
          simp [start_even]
          rw [dvd_iff_mod_eq_zero, h_even_min]
          simp
        have h_last : last_even = max_a_b := by
          simp [last_even]
          rw [dvd_iff_mod_eq_zero, h_eq, h_even_min]
          simp
        have h_eq_start_last : start_even = last_even := by
          rw [h_start, h_last, h_eq]
        have h_start_even : start_even % 2 = 0 := by
          rw [h_start, h_even_min]
        have h_last_even : last_even % 2 = 0 := by
          rw [h_last, h_eq, h_even_min]
        have h_le : start_even ≤ last_even := by
          rw [h_eq_start_last]
        have spec_result := evenRange_spec start_even last_even h_start_even h_last_even h_le
        cases' spec_result with h_all h_rest
        cases' h_rest with h_asc h_rest2
        cases' h_rest2 with h_first h_rest3
        cases' h_rest3 with h_last_elem h_len
        constructor
        · exact h_all
        constructor
        · exact h_asc
        constructor
        · have : evenRange start_even last_even = [start_even] := by
            simp [evenRange, h_eq_start_last]
            split_ifs with h_gt
            · simp at h_gt
            · simp [h_start_even, h_last_even]
              simp [List.range_succ]
          rw [this]
          simp
        · constructor
          · have : evenRange start_even last_even = [start_even] := by
              simp [evenRange, h_eq_start_last]
              split_ifs with h_gt
              · simp at h_gt
              · simp [h_start_even, h_last_even]
                simp [List.range_succ]
            rw [this]
            simp [h_start]
          · have : evenRange start_even last_even = [start_even] := by
              simp [evenRange, h_eq_start_last]
              split_ifs with h_gt
              · simp at h_gt
              · simp [h_start_even, h_last_even]
                simp [List.range_succ]
            rw [this]
            simp [h_last]