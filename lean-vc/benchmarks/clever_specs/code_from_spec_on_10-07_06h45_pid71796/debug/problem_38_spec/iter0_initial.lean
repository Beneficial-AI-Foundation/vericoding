import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

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
      [original_chars.get! (i * 3 + 1), original_chars.get! (i * 3 + 2), original_chars.get! (i * 3)]) ∧
  (n % 3 ≠ 0 → extract encoded_chars (n - n % 3) (n - 1) =
    extract original_chars (n - n % 3) (n - 1));
-- program termination
∃ result,
  impl s = result ∧
  spec result

-- LLM HELPER
def encode_triplet (chars: List Char) (i: ℕ) : List Char :=
  if i + 2 < chars.length then
    [chars.get! (i + 1), chars.get! (i + 2), chars.get! i]
  else
    []

-- LLM HELPER
def encode_chars_aux (chars: List Char) (i: ℕ) (acc: List Char) : List Char :=
  if i + 2 < chars.length then
    let triplet := encode_triplet chars i
    encode_chars_aux chars (i + 3) (acc ++ triplet)
  else
    acc ++ chars.drop i

-- LLM HELPER
def encode_chars (chars: List Char) : List Char :=
  encode_chars_aux chars 0 []

def implementation (s: String) : String := 
  String.mk (encode_chars s.toList)

-- LLM HELPER
lemma encode_chars_aux_length (chars: List Char) (i: ℕ) (acc: List Char) :
  (encode_chars_aux chars i acc).length = acc.length + (chars.length - i) := by
  sorry

-- LLM HELPER
lemma encode_chars_length (chars: List Char) :
  (encode_chars chars).length = chars.length := by
  unfold encode_chars
  simp [encode_chars_aux_length]

-- LLM HELPER
lemma extract_encode_chars_aux (chars: List Char) (i j: ℕ) (acc: List Char) :
  j * 3 + 3 ≤ chars.length →
  i ≤ j * 3 →
  let extract (cs: List Char) (start_index: ℕ) (end_index: ℕ) :=
    (cs.drop start_index).take (end_index - start_index + 1);
  extract (encode_chars_aux chars i acc) (acc.length + j * 3 - i) (acc.length + j * 3 - i + 2) =
    [chars.get! (j * 3 + 1), chars.get! (j * 3 + 2), chars.get! (j * 3)] := by
  sorry

-- LLM HELPER
lemma extract_encode_chars (chars: List Char) (i: ℕ) :
  i * 3 + 3 ≤ chars.length →
  let extract (cs: List Char) (start_index: ℕ) (end_index: ℕ) :=
    (cs.drop start_index).take (end_index - start_index + 1);
  extract (encode_chars chars) (i * 3) (i * 3 + 2) =
    [chars.get! (i * 3 + 1), chars.get! (i * 3 + 2), chars.get! (i * 3)] := by
  sorry

-- LLM HELPER
lemma extract_remainder (chars: List Char) :
  chars.length % 3 ≠ 0 →
  let extract (cs: List Char) (start_index: ℕ) (end_index: ℕ) :=
    (cs.drop start_index).take (end_index - start_index + 1);
  extract (encode_chars chars) (chars.length - chars.length % 3) (chars.length - 1) =
    extract chars (chars.length - chars.length % 3) (chars.length - 1) := by
  sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation
  let n := s.length
  let extract (chars: List Char) (start_index: ℕ) (end_index: ℕ) :=
    (chars.drop start_index).take (end_index - start_index + 1)
  let spec (result: String) :=
    let encoded_chars := result.toList
    let original_chars := s.toList
    encoded_chars.length = n ∧
    (∀ i : ℕ, i * 3 + 3 ≤ n →
      extract encoded_chars (i * 3) (i * 3 + 2) =
        [original_chars.get! (i * 3 + 1), original_chars.get! (i * 3 + 2), original_chars.get! (i * 3)]) ∧
    (n % 3 ≠ 0 → extract encoded_chars (n - n % 3) (n - 1) =
      extract original_chars (n - n % 3) (n - 1))
  
  use String.mk (encode_chars s.toList)
  constructor
  · rfl
  · simp only [String.toList_mk]
    constructor
    · exact encode_chars_length s.toList
    · constructor
      · intro i h
        exact extract_encode_chars s.toList i h
      · intro h
        exact extract_remainder s.toList h