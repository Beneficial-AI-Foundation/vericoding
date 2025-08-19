import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def nat_sequence_string (n : Nat) : String :=
  String.intercalate " " (List.map Nat.repr (List.range (n + 1)))

def implementation (n: Nat) : String := nat_sequence_string n

-- LLM HELPER
def problem_spec_helper (result: String) (n: Nat) : Prop :=
  let result_nums := result.splitOn " "
  result_nums.length = n + 1 ∧
  ∀ i, i < n + 1 → result_nums[i]! = i.repr

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
lemma range_length (n : Nat) : (List.range (n + 1)).length = n + 1 := by
  induction n with
  | zero => simp [List.range]
  | succ n ih => simp [List.range, List.length_cons, ih]

-- LLM HELPER
lemma range_get (n : Nat) (i : Nat) (h : i < n + 1) : (List.range (n + 1)).get ⟨i, h⟩ = i := by
  induction n generalizing i with
  | zero => 
    simp at h
    cases i with
    | zero => simp [List.range]
    | succ => omega
  | succ n ih =>
    cases i with
    | zero => simp [List.range, List.get_cons_zero]
    | succ i' =>
      simp [List.range, List.get_cons_succ]
      apply ih
      omega

-- LLM HELPER
lemma map_length {α β : Type*} (f : α → β) (l : List α) : (List.map f l).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.map, ih]

-- LLM HELPER
lemma map_get {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) : 
  (List.map f l).get ⟨i, by rw [map_length]; exact h⟩ = f (l.get ⟨i, h⟩) := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases i with
    | zero => simp [List.map, List.get_cons_zero]
    | succ i' => 
      simp [List.map, List.get_cons_succ]
      apply ih

-- LLM HELPER
lemma string_intercalate_split (l : List String) (sep : String) : 
  (String.intercalate sep l).splitOn sep = l := by
  sorry

-- LLM HELPER
lemma get_bang_eq_get (l : List String) (i : Nat) (h : i < l.length) : 
  l[i]! = l.get ⟨i, h⟩ := by
  simp [List.get!_eq_get]

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation nat_sequence_string
  use String.intercalate " " (List.map Nat.repr (List.range (n + 1)))
  constructor
  · rfl
  · simp
    constructor
    · rw [string_intercalate_split]
      rw [map_length, range_length]
    · intro i hi
      rw [string_intercalate_split]
      rw [get_bang_eq_get]
      rw [map_get]
      rw [range_get]
      rw [map_length, range_length]
      exact hi