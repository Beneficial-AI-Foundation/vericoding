import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def build_tri_list (n : Nat) : List Int :=
  let rec aux (i : Nat) (acc : List Int) : List Int :=
    if i ≥ n then acc
    else 
      let next_val := if i = 0 then 1
                     else if i = 1 then 3
                     else if i % 2 = 0 then 1 + Int.natCast i / 2
                     else 
                       let val_i_minus_2 := if i ≥ 2 ∧ i - 2 < acc.length then acc[i - 2]! else 0
                       let val_i_minus_1 := if i ≥ 1 ∧ i - 1 < acc.length then acc[i - 1]! else 0
                       let val_i_plus_1 := 1 + Int.natCast (i + 1) / 2
                       val_i_minus_2 + val_i_minus_1 + val_i_plus_1
      aux (i + 1) (acc ++ [next_val])
  aux 0 []

def implementation (n: Nat) : List Int :=
  build_tri_list n

def problem_spec
-- function signature
(impl: Nat → List Int)
-- inputs
(n: Nat) :=
-- spec
let spec (result: List Int) :=
  0 < result.length ∧
  result.length = n ∧
  let i := result.length-1;
  (i = 0 → result[0]! = 1) ∧ -- base case
  (i = 1 → result[1]! = 3) ∧
  (2 ≤ i ∧ i % 2 = 0 → result[i]! = 1 + i / 2) ∧
  (2 ≤ i ∧ i % 2 = 1 → result[i]! = result[i-2]! + result[i-1]! + (1 + (i+1) / 2)) ∧
  if i = 0 then true else result.take i = impl (i-1)
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma build_tri_list_zero : build_tri_list 0 = [] := by
  rfl

-- LLM HELPER
lemma build_tri_list_one : build_tri_list 1 = [1] := by
  rfl

-- LLM HELPER
lemma build_tri_list_two : build_tri_list 2 = [1, 3] := by
  rfl

-- LLM HELPER
lemma build_tri_list_length (n : Nat) : (build_tri_list n).length = n := by
  unfold build_tri_list
  have h : ∀ i acc, i ≤ n → (build_tri_list.aux n i acc).length = acc.length + (n - i) := by
    intro i acc hi
    induction' n - i using Nat.strong_induction_on with k ih generalizing i acc
    simp only [build_tri_list.aux]
    split_ifs with h_ge
    · simp [Nat.le_antisymm hi h_ge]
    · push_neg at h_ge
      have : n - (i + 1) < k := by
        have : i < n := h_ge
        simp [k, Nat.sub_sub, Nat.add_sub_cancel]
        exact Nat.sub_lt (Nat.zero_lt_sub_of_lt this) (by norm_num)
      rw [ih (n - (i + 1)) this (i + 1) (acc ++ [_]) (Nat.le_of_lt h_ge)]
      simp [List.length_append]
      ring
  exact h 0 [] (Nat.zero_le n)

-- LLM HELPER
lemma build_tri_list_nonempty (n : Nat) (h : n > 0) : 0 < (build_tri_list n).length := by
  rw [build_tri_list_length]
  exact h

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  cases' n with n
  · simp [build_tri_list_zero]
  · use build_tri_list (n + 1)
    constructor
    · rfl
    · simp only [build_tri_list_length]
      constructor
      · exact Nat.zero_lt_succ n
      · constructor
        · rfl
        · simp only [Nat.add_sub_cancel]
          cases' n with n
          · simp [build_tri_list_one]
          · cases' n with n
            · simp [build_tri_list_two]
            · simp only [true_and]
              constructor
              · intro h_eq
                simp at h_eq
              · constructor
                · intro h_eq
                  simp at h_eq
                · constructor
                  · intro h_ge h_even
                    simp only [Nat.succ_succ_ne_one, false_implies] at *
                  · constructor
                    · intro h_ge h_odd
                      simp only [Nat.succ_succ_ne_one, false_implies] at *
                    · simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
                      cases' n with n <;> simp [build_tri_list_one, build_tri_list_two]