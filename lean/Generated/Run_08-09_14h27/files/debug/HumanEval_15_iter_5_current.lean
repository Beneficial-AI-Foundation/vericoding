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
  join_with_spaces ((nat_range n).map Nat.repr)

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
lemma splitOn_space_single : 
  ("0").splitOn " " = ["0"] := by
  rfl

-- LLM HELPER
lemma splitOn_space_two : 
  ("0 1").splitOn " " = ["0", "1"] := by
  rfl

-- LLM HELPER
lemma intercalate_splitOn_inverse (l : List String) (h : l ≠ []) : 
  (String.intercalate " " l).splitOn " " = l := by
  induction l with
  | nil => contradiction
  | cons a l' ih =>
    cases l' with
    | nil => simp [String.intercalate]
    | cons b l'' =>
      simp [String.intercalate]
      have : b :: l'' ≠ [] := by simp
      have ih' := ih this
      rw [String.splitOn_intercalate]

-- LLM HELPER
lemma nat_repr_inj : ∀ i j : Nat, i.repr = j.repr → i = j := by
  intro i j h
  exact Nat.cast_injective h

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation join_with_spaces nat_range
  use String.intercalate " " ((List.range (n + 1)).map Nat.repr)
  constructor
  · rfl
  · simp [String.splitOn_intercalate]
    constructor
    · rw [List.length_map, List.length_range]
    · intro i hi
      simp [List.get!, List.get?_map, List.get?_range]
      split
      · simp at *
      · rfl