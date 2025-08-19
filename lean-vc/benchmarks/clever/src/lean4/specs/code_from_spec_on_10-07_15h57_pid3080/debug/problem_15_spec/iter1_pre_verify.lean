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
def nat_sequence_string (n : Nat) : String :=
  String.intercalate " " (List.map Nat.repr (List.range (n + 1)))

def implementation (n: Nat) : String := nat_sequence_string n

-- LLM HELPER
lemma list_range_length (n : Nat) : (List.range (n + 1)).length = n + 1 := by
  simp [List.length_range]

-- LLM HELPER
lemma list_range_get (n : Nat) (i : Nat) (h : i < n + 1) : (List.range (n + 1))[i] = i := by
  simp [List.get_range h]

-- LLM HELPER
lemma map_repr_range (n : Nat) : List.map Nat.repr (List.range (n + 1)) = List.map Nat.repr (List.range (n + 1)) := by
  rfl

-- LLM HELPER
lemma intercalate_split (l : List String) : (String.intercalate " " l).splitOn " " = l := by
  sorry

-- LLM HELPER
lemma get_map_repr_range (n : Nat) (i : Nat) (h : i < n + 1) : 
  (List.map Nat.repr (List.range (n + 1)))[i] = i.repr := by
  simp [List.get_map, List.get_range h]

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation nat_sequence_string
  use String.intercalate " " (List.map Nat.repr (List.range (n + 1)))
  constructor
  · rfl
  · unfold problem_spec
    simp
    sorry