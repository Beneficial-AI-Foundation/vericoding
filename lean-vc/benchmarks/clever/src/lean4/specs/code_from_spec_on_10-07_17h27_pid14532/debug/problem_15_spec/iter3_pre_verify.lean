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
  have h_len : i < (List.range (n + 1)).length := by
    rw [List.length_range]
    exact h
  rw [List.getElem!_eq_getElem_of_valid (List.range (n + 1)) i h_len]
  rw [List.getElem_range]
  exact h

-- LLM HELPER
lemma map_repr_get (n: Nat) (i: Nat) (h: i < n + 1) : 
  ((List.range (n + 1)).map Nat.repr)[i]! = i.repr := by
  have h_len : i < ((List.range (n + 1)).map Nat.repr).length := by
    rw [List.length_map]
    rw [List.length_range]
    exact h
  rw [List.getElem!_eq_getElem_of_valid _ _ h_len]
  rw [List.getElem_map]
  rw [List.getElem_range]
  exact h

-- LLM HELPER
lemma string_join_splitOn (l: List String) (h: l ≠ []) : 
  (l.foldl (fun acc s => if acc.isEmpty then s else acc ++ " " ++ s) "").splitOn " " = l := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    simp [List.foldl]
    cases tail with
    | nil => 
      simp [String.isEmpty]
      rw [String.splitOn_self]
    | cons t_head t_tail =>
      simp [String.isEmpty]
      have : t_head :: t_tail ≠ [] := by simp
      rw [ih this]

-- LLM HELPER
lemma range_map_nonempty (n: Nat) : (List.range (n + 1)).map Nat.repr ≠ [] := by
  rw [List.ne_nil_iff_length_pos]
  rw [List.length_map]
  rw [List.length_range]
  omega

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation nat_range_string
  use (List.range (n + 1)).map Nat.repr |>.foldl (fun acc s => if acc.isEmpty then s else acc ++ " " ++ s) ""
  constructor
  · rfl
  · constructor
    · rw [string_join_splitOn]
      rw [List.length_map]
      rw [List.length_range]
      exact range_map_nonempty n
    · intro i h
      rw [string_join_splitOn]
      have h_len : i < ((List.range (n + 1)).map Nat.repr).length := by
        rw [List.length_map]
        rw [List.length_range]
        exact h
      rw [List.getElem!_eq_getElem_of_valid _ _ h_len]
      rw [List.getElem_map]
      rw [List.getElem_range]
      exact h
      exact range_map_nonempty n