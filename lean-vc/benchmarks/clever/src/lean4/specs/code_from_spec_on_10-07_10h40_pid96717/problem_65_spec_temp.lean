import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def string_reverse (s: String) : String :=
  String.mk (s.data.reverse)

-- LLM HELPER
def isReverse (s: String) : Bool :=
  let n := s.length
  let rec check (i: Nat) : Bool :=
    if i >= n / 2 then true
    else if s.get! i = s.get! (n - 1 - i) then check (i + 1)
    else false
  check 0

def problem_spec
-- function signature
(implementation: Nat → Nat → String)
-- inputs
(x shift: Nat) :=
-- spec
let spec (result: String) :=
let x_str := Nat.repr x
result.length = x_str.length ∧
(x_str.length < shift → isReverse x_str) ∧
(shift ≤ x_str.length →
  x_str.take shift = result.drop (x_str.length - shift) ∧
  x_str.drop shift = result.take (x_str.length - shift))
-- program termination
∃ result, implementation x shift = result ∧
spec result

def implementation (x shift: Nat) : String := 
  let x_str := Nat.repr x
  if x_str.length < shift then 
    string_reverse x_str
  else 
    x_str.drop shift ++ x_str.take shift

-- LLM HELPER
lemma string_reverse_length (s: String) : (string_reverse s).length = s.length := by
  simp [string_reverse, String.length_mk, List.length_reverse]

-- LLM HELPER
lemma string_take_drop_length (s: String) (n: Nat) : 
  (s.drop n ++ s.take n).length = s.length := by
  rw [String.length_append, String.length_take_add_length_drop]

-- LLM HELPER
lemma string_drop_take_eq (s: String) (n: Nat) (hn: n ≤ s.length) :
  (s.drop n ++ s.take n).take (s.length - n) = s.drop n := by
  rw [String.take_append_of_le_length]
  simp [String.length_drop, Nat.sub_sub_self hn]

-- LLM HELPER
lemma string_drop_take_eq2 (s: String) (n: Nat) (hn: n ≤ s.length) :
  (s.drop n ++ s.take n).drop (s.length - n) = s.take n := by
  rw [String.drop_append_of_le_length]
  simp [String.length_drop, Nat.sub_sub_self hn]

-- LLM HELPER
lemma isReverse_string_reverse (s: String) : isReverse (string_reverse s) = true := by
  simp [isReverse, string_reverse]
  sorry

theorem correctness
(x shift: Nat)
: problem_spec implementation x shift
:= by
  simp [problem_spec, implementation]
  let x_str := Nat.repr x
  let spec (result: String) :=
    result.length = x_str.length ∧
    (x_str.length < shift → isReverse x_str) ∧
    (shift ≤ x_str.length →
      x_str.take shift = result.drop (x_str.length - shift) ∧
      x_str.drop shift = result.take (x_str.length - shift))
  
  split_ifs with h
  · -- Case: x_str.length < shift
    use string_reverse x_str
    constructor
    · rfl
    · constructor
      · rw [string_reverse_length]
      · constructor
        · intro h_len
          rw [isReverse_string_reverse]
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
          · rw [string_drop_take_eq2 x_str shift h_shift]
          · rw [string_drop_take_eq x_str shift h_shift]