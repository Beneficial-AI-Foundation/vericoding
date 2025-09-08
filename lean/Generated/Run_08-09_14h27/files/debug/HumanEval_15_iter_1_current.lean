import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def nat_range (n : Nat) : List Nat :=
  List.range (n + 1)

-- LLM HELPER
def join_with_spaces (l : List String) : String :=
  String.intercalate " " l

def implementation (n: Nat) : String :=
  join_with_spaces (nat_range n).map Nat.repr

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
lemma list_range_length (n : Nat) : (List.range (n + 1)).length = n + 1 := by
  simp [List.length_range]

-- LLM HELPER
lemma list_range_get (n i : Nat) (h : i < n + 1) : (List.range (n + 1))[i] = i := by
  simp [List.get_range h]

-- LLM HELPER
lemma map_repr_length (l : List Nat) : (l.map Nat.repr).length = l.length := by
  simp [List.length_map]

-- LLM HELPER
lemma intercalate_splitOn_id (l : List String) : 
  (String.intercalate " " l).splitOn " " = l := by
  sorry

-- LLM HELPER
lemma get_map_repr (l : List Nat) (i : Nat) (h : i < l.length) :
  (l.map Nat.repr)[i]! = l[i]!.repr := by
  simp [List.get!_map]

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation join_with_spaces nat_range
  use String.intercalate " " ((List.range (n + 1)).map Nat.repr)
  constructor
  · rfl
  · unfold spec
    simp only [intercalate_splitOn_id]
    constructor
    · rw [map_repr_length, list_range_length]
    · intro i hi
      rw [get_map_repr, list_range_get n i hi]