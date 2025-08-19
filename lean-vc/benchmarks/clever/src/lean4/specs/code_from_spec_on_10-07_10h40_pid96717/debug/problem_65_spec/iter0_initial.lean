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
def string_reverse (s: String) : String :=
  String.mk (s.data.reverse)

def implementation (x shift: Nat) : String := 
  let x_str := Nat.repr x
  if x_str.length < shift then 
    string_reverse x_str
  else 
    x_str.drop shift ++ x_str.take shift

-- LLM HELPER
lemma string_reverse_length (s: String) : (string_reverse s).length = s.length := by
  simp [string_reverse]

-- LLM HELPER
lemma string_reverse_get (s: String) (i: Nat) (hi: i < s.length) : 
  (string_reverse s).get! ⟨i⟩ = s.get! ⟨s.length - 1 - i⟩ := by
  simp [string_reverse]
  sorry

-- LLM HELPER
lemma isReverse_string_reverse (s: String) : 
  let isReverse (s: String) : Bool :=
    let n := s.length;
    ∀ i, i < n / 2 → s.get! ⟨i⟩ = s.get! ⟨n - 1 - i⟩;
  isReverse (string_reverse s) = true := by
  simp [string_reverse]
  sorry

-- LLM HELPER
lemma string_take_drop_length (s: String) (n: Nat) : 
  (s.take n ++ s.drop n).length = s.length := by
  simp [String.length_take_add_length_drop]

-- LLM HELPER
lemma string_drop_take_eq (s: String) (n: Nat) (hn: n ≤ s.length) :
  (s.drop n ++ s.take n).take (s.length - n) = s.drop n := by
  simp [String.take_append_of_le_length]

-- LLM HELPER
lemma string_drop_take_eq2 (s: String) (n: Nat) (hn: n ≤ s.length) :
  (s.drop n ++ s.take n).drop (s.length - n) = s.take n := by
  simp [String.drop_append_of_le_length]

theorem correctness
(x shift: Nat)
: problem_spec implementation x shift
:= by
  simp [problem_spec, implementation]
  let x_str := Nat.repr x
  let isReverse (s: String) : Bool :=
    let n := s.length;
    ∀ i, i < n / 2 → s.get! ⟨i⟩ = s.get! ⟨n - 1 - i⟩;
  let spec (result: String) :=
    result.length = x_str.length ∧
    (x_str.length < shift → isReverse x_str) ∧
    (shift ≤ x_str.length →
      x_str.take shift = result.drop (x_str.length - shift) ∧
      x_str.drop shift = result.take (x_str.length - shift));
  
  split_ifs with h
  · -- Case: x_str.length < shift
    use string_reverse x_str
    constructor
    · rfl
    · constructor
      · rw [string_reverse_length]
      · constructor
        · intro h_len
          simp [isReverse_string_reverse]
        · intro h_shift
          exfalso
          exact not_le.mpr h h_shift
  · -- Case: shift ≤ x_str.length  
    use x_str.drop shift ++ x_str.take shift
    constructor
    · rfl
    · constructor
      · rw [string_take_drop_length]
      · constructor
        · intro h_len
          exfalso
          exact h (not_le.mp h_len)
        · intro h_shift
          constructor
          · rw [string_drop_take_eq2]
            exact h_shift
          · rw [string_drop_take_eq]
            exact h_shift