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

-- LLM HELPER
lemma all_consecutive_triples_distinct_correct (s: String) :
  all_consecutive_triples_distinct s = true ↔
  ¬ (∃ i j, i < j ∧ j < s.length ∧ j - i ≤ 2 ∧ s.data[i]! = s.data[j]!) :=
by
  simp [all_consecutive_triples_distinct]
  by_cases h : s.length < 3
  · simp [h]
    constructor
    · intro _
      intro ⟨i, j, hi_lt_j, hj_lt_len, hj_sub_i, _⟩
      have : j < 3 := by
        by_contra hcontra
        push_neg at hcontra
        have : 3 ≤ j := hcontra
        linarith [hj_lt_len, h]
      have : i < 3 := by linarith [hi_lt_j, this]
      linarith [h, hj_lt_len]
    · intro _
      trivial
  · simp [h]
    sorry

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec, implementation]
  use (s.length ≥ 3 ∧ all_consecutive_triples_distinct s)
  constructor
  · rfl
  · simp [Bool.and_eq_true]
    constructor
    · constructor
      · intro ⟨hlen, htriples⟩
        constructor
        · exact hlen
        · rw [← all_consecutive_triples_distinct_correct]
          exact htriples
      · intro ⟨hlen, hno_dup⟩
        constructor
        · exact hlen
        · rw [all_consecutive_triples_distinct_correct]
          exact hno_dup
    · constructor
      · intro ⟨_, htriples⟩
        rw [all_consecutive_triples_distinct_correct] at htriples
        exact htriples
      · intro hno_dup
        simp
        rw [all_consecutive_triples_distinct_correct]
        exact hno_dup

-- #test implementation "a" = False
-- #test implementation "aa" = False
-- #test implementation "abcd" = True
-- #test implementation "aabb" = False
-- #test implementation "adb" = True