/- 
function_signature: "def is_happy(s: str) -> bool"
docstring: |
    You are given a string s.
    Your task is to check if the string is happy or not.
    A string is happy if its length is at least 3 and every 3 consecutive letters are distinct
test_cases:
  - input: "a"
    output: False
  - input: "aa"
    output: False
  - input: "abcd"
    output: True
  - input: "aabb"
    output: False
  - input: "adb"
    output: True
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def all_consecutive_triples_distinct (s: String) : Bool :=
  if s.length < 3 then true
  else
    let chars := s.data
    let rec check_from (i: Nat) : Bool :=
      if i + 2 >= chars.length then true
      else
        let c1 := chars[i]!
        let c2 := chars[i+1]!
        let c3 := chars[i+2]!
        if c1 = c2 ∨ c1 = c3 ∨ c2 = c3 then false
        else check_from (i + 1)
    check_from 0

def implementation (s: String) : Bool :=
  s.length ≥ 3 ∧ all_consecutive_triples_distinct s

def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(s: String) :=
-- spec
let spec (result : Bool) :=
  result ↔
  (3 ≤ s.length) ∧
  ¬ (∃ i j, i < j ∧ j < s.length ∧ j - i ≤ 2 ∧ s.data[i]! = s.data[j]!)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec, implementation]
  use (s.length ≥ 3 ∧ all_consecutive_triples_distinct s)
  constructor
  · rfl
  · simp only [Bool.and_eq_true]
    constructor
    · intro ⟨hlen, _⟩
      exact Nat.le_of_ble_eq_true hlen
    · intro hlen
      exact Nat.ble_eq_true_of_le hlen