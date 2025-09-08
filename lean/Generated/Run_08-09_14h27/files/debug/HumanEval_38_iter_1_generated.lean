/- 
function_signature: "def encode_cyclic(s: str) -> str"
docstring: |
  Returns an encoded string by cycling each group of three consecutive characters.
  Specifically, each group of exactly three characters 'abc' is transformed to 'bca'.
  Groups of fewer than three characters at the end of the string remain unchanged.
test_cases:
  - input: "abcdef"
    expected_output: "bcaefd"
  - input: "abcde"
    expected_output: "bcade"
  - input: "ab"
    expected_output: "ab"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def cycleThree (chars: List Char) : List Char :=
  match chars with
  | [a, b, c] => [b, c, a]
  | _ => chars

-- LLM HELPER  
def processChunks (chars: List Char) : List Char :=
  match chars with
  | [] => []
  | a :: b :: c :: rest => cycleThree [a, b, c] ++ processChunks rest
  | remaining => remaining

def implementation (s: String) : String :=
  String.mk (processChunks s.toList)

def problem_spec
(impl: String → String)
(s: String) :=
let n := s.length;
let extract (chars: List Char) (start_index: ℕ) (end_index: ℕ) :=
  (chars.drop start_index).take (end_index - start_index + 1);
let spec (result: String) :=
  let encoded_chars := result.toList;
  let original_chars := s.toList;
  encoded_chars.length = n ∧
  (∀ i : ℕ, i * 3 + 3 ≤ n →
    extract encoded_chars (i * 3) (i * 3 + 2) =
      [original_chars[i * 3 + 1]!, original_chars[i * 3 + 2]!, original_chars[i * 3]!]) ∧
  (n % 3 ≠ 0 → extract encoded_chars (n - n % 3) (n - 1) =
    extract original_chars (n - n % 3) (n - 1));
-- program termination
∃ result,
  impl s = result ∧
  spec result

-- LLM HELPER
lemma processChunks_length (chars: List Char) : (processChunks chars).length = chars.length := by
  induction chars using processChunks.induct with
  | case1 => simp [processChunks]
  | case2 a b c rest ih =>
    simp [processChunks, cycleThree]
    rw [List.length_append]
    simp
    exact ih
  | case3 a => simp [processChunks]
  | case4 a b => simp [processChunks]

-- LLM HELPER
lemma extract_def (chars: List Char) (start_index end_index: ℕ) :
  extract chars start_index end_index = (chars.drop start_index).take (end_index - start_index + 1) := by
  rfl

-- LLM HELPER
lemma processChunks_cycle_property (chars: List Char) (i: ℕ) 
  (h: i * 3 + 3 ≤ chars.length) :
  let result := processChunks chars
  let extract (cs: List Char) (start_index end_index: ℕ) := (cs.drop start_index).take (end_index - start_index + 1)
  extract result (i * 3) (i * 3 + 2) = [chars[i * 3 + 1]!, chars[i * 3 + 2]!, chars[i * 3]!] := by
  sorry

-- LLM HELPER  
lemma processChunks_remainder_property (chars: List Char) 
  (h: chars.length % 3 ≠ 0) :
  let n := chars.length
  let result := processChunks chars
  let extract (cs: List Char) (start_index end_index: ℕ) := (cs.drop start_index).take (end_index - start_index + 1)
  extract result (n - n % 3) (n - 1) = extract chars (n - n % 3) (n - 1) := by
  sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use String.mk (processChunks s.toList)
  constructor
  · rfl
  · simp [String.toList_mk]
    constructor
    · rw [processChunks_length]
      simp
    · constructor
      · intro i h
        have h' : i * 3 + 3 ≤ s.toList.length := by
          rwa [← String.length_toList] at h
        exact processChunks_cycle_property s.toList i h'
      · intro h
        have h' : s.toList.length % 3 ≠ 0 := by
          rwa [String.length_toList] at h
        exact processChunks_remainder_property s.toList h'

-- #test implementation "abcdef" = "bcaefd"
-- #test implementation "abcde" = "bcade"
-- #test implementation "ab" = "ab"