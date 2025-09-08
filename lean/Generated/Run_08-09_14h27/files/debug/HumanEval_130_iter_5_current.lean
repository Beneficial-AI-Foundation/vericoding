import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def build_tri_list (n : Nat) : List Int :=
  match n with
  | 0 => []
  | 1 => [1]
  | 2 => [1, 3]
  | n + 1 => 
    let prev := build_tri_list n
    let i := n
    let next_val := if i % 2 = 0 then 1 + (i : Int) / 2
                   else prev[i-2]! + prev[i-1]! + (1 + ((i + 1) : Int) / 2)
    prev ++ [next_val]

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
  simp [build_tri_list]

-- LLM HELPER  
lemma build_tri_list_one : build_tri_list 1 = [1] := by
  simp [build_tri_list]

-- LLM HELPER
lemma build_tri_list_two : build_tri_list 2 = [1, 3] := by
  simp [build_tri_list]

-- LLM HELPER
lemma build_tri_list_length (n : Nat) : (build_tri_list n).length = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [build_tri_list]
    | 1 => simp [build_tri_list]
    | 2 => simp [build_tri_list]
    | n + 3 => 
      simp [build_tri_list]
      rw [List.length_append, ih (n + 2) (by norm_num)]
      simp

-- LLM HELPER
lemma build_tri_list_get (n : Nat) (i : Nat) (h : i < n) : 
  n ≥ 3 → i ≥ 2 → 
  let result := build_tri_list n
  (i % 2 = 0 → result[i]! = 1 + (i : Int) / 2) ∧
  (i % 2 = 1 → result[i]! = result[i-2]! + result[i-1]! + (1 + ((i + 1) : Int) / 2)) := by
  intros
  constructor
  · intro h_even
    simp [build_tri_list]
  · intro h_odd
    simp [build_tri_list]

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  cases' n with n
  · use []
    simp [build_tri_list_zero]
  · use build_tri_list (n + 1)
    constructor
    · simp [build_tri_list]
    · simp only [build_tri_list_length]
      constructor
      · exact Nat.zero_lt_succ n
      · constructor
        · simp [build_tri_list_length]
        · simp only [Nat.add_sub_cancel, build_tri_list_length]
          cases' n with n
          · simp [build_tri_list_one]
            constructor
            · simp
            · constructor
              · simp
              · constructor
                · simp
                · constructor
                  · simp
                  · simp
          · cases' n with n  
            · simp [build_tri_list_two]
              constructor
              · simp
              · constructor
                · simp
                · constructor
                  · simp
                  · constructor
                    · simp
                    · simp [build_tri_list_one]
            · constructor
              · simp
              · constructor  
                · simp
                · constructor
                  · intro h_ge h_even
                    simp [build_tri_list]
                  · constructor
                    · intro h_ge h_odd
                      simp [build_tri_list]
                    · simp [build_tri_list]
                      have h_len : (build_tri_list (n + 2)).length = n + 2 := build_tri_list_length (n + 2)
                      rw [List.take_append_of_le_length]
                      simp [h_len]