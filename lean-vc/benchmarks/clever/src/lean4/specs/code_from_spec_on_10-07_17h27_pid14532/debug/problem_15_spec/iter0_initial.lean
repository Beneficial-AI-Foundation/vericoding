import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(n: Nat) :=
-- spec
let spec (result: String) :=
let result_nums := result.splitOn " ";
result_nums.length = n + 1 ∧
∀ i, i < n + 1 → result_nums[i]! = i.repr;
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def nat_range_string (n: Nat) : String :=
  (List.range (n + 1)).map Nat.repr |>.foldl (fun acc s => if acc.isEmpty then s else acc ++ " " ++ s) ""

def implementation (n: Nat) : String := nat_range_string n

-- LLM HELPER  
lemma list_range_length (n: Nat) : (List.range (n + 1)).length = n + 1 := by
  simp [List.length_range]

-- LLM HELPER
lemma list_range_get (n: Nat) (i: Nat) (h: i < n + 1) : (List.range (n + 1))[i]! = i := by
  rw [List.getElem!_eq_getElem]
  rw [List.getElem_range]
  exact h

-- LLM HELPER
lemma map_repr_get (n: Nat) (i: Nat) (h: i < n + 1) : 
  ((List.range (n + 1)).map Nat.repr)[i]! = i.repr := by
  rw [List.getElem!_eq_getElem]
  rw [List.getElem_map]
  rw [List.getElem_range]
  exact h

-- LLM HELPER
lemma foldl_join_splitOn (l: List String) : 
  (l.foldl (fun acc s => if acc.isEmpty then s else acc ++ " " ++ s) "").splitOn " " = l := by
  sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation nat_range_string
  use (List.range (n + 1)).map Nat.repr |>.foldl (fun acc s => if acc.isEmpty then s else acc ++ " " ++ s) ""
  constructor
  · rfl
  · constructor
    · sorry -- Need to prove the splitOn gives the right length
    · sorry -- Need to prove the elements are correct