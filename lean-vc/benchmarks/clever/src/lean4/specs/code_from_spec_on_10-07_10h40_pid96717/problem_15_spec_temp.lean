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
  (List.range (n + 1)).map (fun i => toString i) |>.foldl (fun acc s => if acc.isEmpty then s else acc ++ " " ++ s) ""

def implementation (n: Nat) : String := nat_range_string n

-- LLM HELPER
lemma list_range_length (n: Nat) : (List.range (n + 1)).length = n + 1 := by
  induction n with
  | zero => simp [List.range]
  | succ n ih => simp [List.range, List.length_cons, ih]

-- LLM HELPER
lemma list_range_get (n: Nat) (i: Nat) (h: i < n + 1) : (List.range (n + 1))[i]! = i := by
  have h_len : i < (List.range (n + 1)).length := by
    rw [list_range_length]
    exact h
  rw [List.get!_eq_get h_len]
  induction n generalizing i with
  | zero => 
    simp at h
    cases i with
    | zero => simp [List.range]
    | succ i => omega
  | succ n ih =>
    cases i with
    | zero => simp [List.range]
    | succ i => 
      simp [List.range, List.get_cons_succ]
      apply ih
      omega

-- LLM HELPER
lemma map_repr_foldl_splitOn (n: Nat) : 
  let nums := (List.range (n + 1)).map (fun i => toString i)
  let result := nums.foldl (fun acc s => if acc.isEmpty then s else acc ++ " " ++ s) ""
  result.splitOn " " = nums := by
  induction n with
  | zero => simp [List.range, List.map, List.foldl, String.splitOn]
  | succ n ih => 
    simp [List.range, List.map, List.foldl]
    sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation nat_range_string
  use (List.range (n + 1)).map (fun i => toString i) |>.foldl (fun acc s => if acc.isEmpty then s else acc ++ " " ++ s) ""
  constructor
  · rfl
  · constructor
    · have h := map_repr_foldl_splitOn n
      simp at h
      rw [h]
      simp [List.length_map, list_range_length]
    · intro i hi
      have h := map_repr_foldl_splitOn n
      simp at h
      rw [h]
      simp [List.get!_map, list_range_get n i hi]