import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → Nat → String)
-- inputs
(x shift: Nat) :=
let isReverse (s: String) : Bool :=
  let n := s.length;
  ∀ i, i < n / 2 → s.get! ⟨i⟩ = s.get! ⟨n - 1 - i⟩;
-- spec
let spec (result: String) :=
let x_str := Nat.repr x;
result.length = x_str.length ∧
(x_str.length < shift → isReverse x_str) ∧
(shift ≤ x_str.length →
  x_str.take shift = result.drop (x_str.length - shift) ∧
  x_str.drop shift = result.take (x_str.length - shift));
-- program termination
∃ result, implementation x shift = result ∧
spec result

-- LLM HELPER
def reverse_string (s: String) : String :=
  String.mk (s.data.reverse)

-- LLM HELPER
def rotate_left (s: String) (shift: Nat) : String :=
  if shift ≤ s.length then
    s.drop shift ++ s.take shift
  else
    s

def implementation (x shift: Nat) : String := 
  let x_str := Nat.repr x
  if x_str.length < shift then
    reverse_string x_str
  else
    rotate_left x_str shift

-- LLM HELPER
lemma reverse_string_correct (s: String) : 
  let n := s.length
  ∀ i, i < n / 2 → (reverse_string s).get! ⟨i⟩ = (reverse_string s).get! ⟨n - 1 - i⟩ := by
  intro i hi
  simp [reverse_string]
  rfl

-- LLM HELPER
lemma reverse_string_length (s: String) : (reverse_string s).length = s.length := by
  simp [reverse_string, String.length_mk]

-- LLM HELPER
lemma rotate_left_length (s: String) (shift: Nat) : (rotate_left s shift).length = s.length := by
  simp [rotate_left]
  split_ifs with h
  · simp [String.length_append]
    rw [Nat.min_def]
    split_ifs
    · omega
    · omega
  · rfl

-- LLM HELPER
lemma rotate_left_correct (s: String) (shift: Nat) (h: shift ≤ s.length) :
  s.take shift = (rotate_left s shift).drop (s.length - shift) ∧
  s.drop shift = (rotate_left s shift).take (s.length - shift) := by
  simp [rotate_left, h]
  constructor
  · have h1 : s.length - shift = (s.drop shift).length := by
      simp [String.length_drop]
      omega
    rw [h1]
    simp [String.drop_append]
    rw [String.length_drop]
    simp
  · have h1 : s.length - shift = (s.drop shift).length := by
      simp [String.length_drop] 
      omega
    rw [h1]
    simp [String.take_append]

theorem correctness
(x shift: Nat)
: problem_spec implementation x shift := by
  simp [problem_spec]
  use implementation x shift
  constructor
  · rfl
  · simp [implementation]
    let x_str := Nat.repr x
    split_ifs with h
    · -- Case: x_str.length < shift
      simp [Bool.decide_eq_true]
      constructor
      · exact reverse_string_length x_str
      · constructor
        · intro h_len
          exact reverse_string_correct x_str
        · intro h_shift
          exfalso
          exact h h_shift
    · -- Case: ¬x_str.length < shift
      constructor
      · exact rotate_left_length x_str shift
      · constructor
        · intro h_len
          exfalso
          exact h h_len
        · intro h_shift
          exact rotate_left_correct x_str shift h_shift