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
  String.mk (processChunks s.data)

def problem_spec
(impl: String → String)
(s: String) :=
let n := s.length;
let extract (chars: List Char) (start_index: ℕ) (end_index: ℕ) :=
  (chars.drop start_index).take (end_index - start_index + 1);
let spec (result: String) :=
  let encoded_chars := result.data;
  let original_chars := s.data;
  encoded_chars.length = n ∧
  (∀ i : ℕ, i * 3 + 3 ≤ n →
    List.take 3 (List.drop (i * 3) encoded_chars) =
      [original_chars[i * 3 + 1]?.getD 'A', original_chars[i * 3 + 2]?.getD 'A', original_chars[i * 3]?.getD 'A']) ∧
  (n % 3 ≠ 0 → extract encoded_chars (n - n % 3) (n - 1) =
    extract original_chars (n - n % 3) (n - 1));
-- program termination
∃ result,
  impl s = result ∧
  spec result

-- LLM HELPER
lemma processChunks_length (chars: List Char) : (processChunks chars).length = chars.length := by
  induction chars using List.length_induction with
  | h chars ih =>
    cases chars with
    | nil => simp [processChunks]
    | cons a rest =>
      cases rest with
      | nil => simp [processChunks]
      | cons b rest2 =>
        cases rest2 with
        | nil => simp [processChunks]
        | cons c rest3 =>
          simp [processChunks, cycleThree]
          rw [List.length_append]
          simp
          have h : rest3.length < (a :: b :: c :: rest3).length := by simp [Nat.lt_add_left]
          rw [ih rest3 h]

-- LLM HELPER
lemma processChunks_cycle_property (chars: List Char) (i: ℕ) 
  (h: i * 3 + 3 ≤ chars.length) :
  List.take 3 (List.drop (i * 3) (processChunks chars)) =
    [chars[i * 3 + 1]?.getD 'A', chars[i * 3 + 2]?.getD 'A', chars[i * 3]?.getD 'A'] := by
  induction i generalizing chars with
  | zero =>
    cases chars with
    | nil => simp at h
    | cons a rest =>
      cases rest with
      | nil => simp at h
      | cons b rest2 =>
        cases rest2 with
        | nil => simp at h
        | cons c rest3 =>
          simp [processChunks, cycleThree]
          simp [List.take_append, List.drop]
  | succ i ih =>
    cases' chars with a chars'
    · simp at h
    cases' chars' with b chars''
    · simp at h
    cases' chars'' with c chars'''
    · simp at h
    have h' : i * 3 + 3 ≤ chars'''.length := by
      simp at h
      omega
    simp [processChunks, cycleThree]
    have : (i + 1) * 3 = 3 + i * 3 := by ring
    rw [this]
    simp [List.take_drop]
    exact ih chars''' h'

-- LLM HELPER  
lemma processChunks_remainder_property (chars: List Char) 
  (h: chars.length % 3 ≠ 0) :
  let n := chars.length
  let extract (cs: List Char) (start_index end_index: ℕ) := (cs.drop start_index).take (end_index - start_index + 1)
  extract (processChunks chars) (n - n % 3) (n - 1) = extract chars (n - n % 3) (n - 1) := by
  unfold extract
  have len_eq : (processChunks chars).length = chars.length := processChunks_length chars
  induction chars using List.length_induction generalizing h with
  | h chars ih =>
    cases chars with
    | nil => simp at h
    | cons a rest =>
      cases rest with
      | nil => 
        simp [processChunks]
        simp at h
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          simp [processChunks]
          simp at h
        | cons c rest3 =>
          simp [processChunks, cycleThree]
          have len_rest3 : rest3.length < (a :: b :: c :: rest3).length := by simp [Nat.lt_add_left]
          by_cases hr : rest3.length % 3 = 0
          · simp [hr] at h
            have : (a :: b :: c :: rest3).length = 3 + rest3.length := by simp
            rw [this]
            simp [Nat.add_mod, hr]
          · have h_rest3 : rest3.length % 3 ≠ 0 := hr
            have IH := ih rest3 len_rest3 h_rest3
            simp at IH
            have len_abc_rest3 : (a :: b :: c :: rest3).length = 3 + rest3.length := by simp
            rw [len_abc_rest3]
            simp [Nat.add_mod]
            cases' h_mod : rest3.length % 3 with
            | zero => contradiction
            | succ k =>
              simp [h_mod]
              rw [List.drop_append_of_le_length, List.take_append_of_le_length]
              · exact IH
              · simp; omega
              · simp; omega

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use String.mk (processChunks s.data)
  constructor
  · simp [String.mk]
  · constructor
    · exact processChunks_length s.data
    constructor
    · exact processChunks_cycle_property s.data
    · exact processChunks_remainder_property s.data

-- #test implementation "abcdef" = "bcaefd"
-- #test implementation "abcde" = "bcade"
-- #test implementation "ab" = "ab"