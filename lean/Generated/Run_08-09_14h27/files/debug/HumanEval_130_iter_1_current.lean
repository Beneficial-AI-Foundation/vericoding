import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def tri_single (i : Nat) (prev : List Int) : Int :=
  if i = 0 then 1
  else if i = 1 then 3
  else if i % 2 = 0 then 1 + i / 2
  else 
    let val_i_minus_2 := if i ≥ 2 then prev.get! (i - 2) else 0
    let val_i_minus_1 := if i ≥ 1 then prev.get! (i - 1) else 0
    let val_i_plus_1 := 1 + (i + 1) / 2  -- since i+1 is even when i is odd
    val_i_minus_2 + val_i_minus_1 + val_i_plus_1

-- LLM HELPER
def build_tri_list (n : Nat) : List Int :=
  let rec aux (i : Nat) (acc : List Int) : List Int :=
    if i ≥ n then acc
    else 
      let next_val := tri_single i acc
      aux (i + 1) (acc ++ [next_val])
  aux 0 []

def implementation (n: Nat) : List Int :=
  build_tri_list (n + 1)

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
lemma build_tri_list_length (n : Nat) : (build_tri_list n).length = n := by
  sorry

-- LLM HELPER  
lemma build_tri_list_base_cases (n : Nat) (h : n ≥ 2) :
  let result := build_tri_list n
  result[0]! = 1 ∧ result[1]! = 3 := by
  sorry

-- LLM HELPER
lemma build_tri_list_recursive_step (n : Nat) (i : Nat) (h1 : i < n) (h2 : i ≥ 2) :
  let result := build_tri_list n
  (i % 2 = 0 → result[i]! = 1 + i / 2) ∧
  (i % 2 = 1 → result[i]! = result[i-2]! + result[i-1]! + (1 + (i+1) / 2)) := by
  sorry

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  cases' n with n
  · simp [build_tri_list]
  · use build_tri_list (n + 1 + 1)
    constructor
    · rfl
    · unfold build_tri_list
      simp
      sorry

-- #test implementation 3 = [1, 3, 2, 8]