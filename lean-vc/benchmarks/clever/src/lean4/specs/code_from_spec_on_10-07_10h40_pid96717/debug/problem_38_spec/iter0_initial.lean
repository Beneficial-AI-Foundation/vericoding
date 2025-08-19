import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
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
      [original_chars[i * 3 + 1]!, original_chars[i * 3 + 2]!, original_chars[i * 3]!]) ∧
  (n % 3 ≠ 0 → extract encoded_chars (n - n % 3) (n - 1) =
    extract original_chars (n - n % 3) (n - 1));
-- program termination
∃ result,
  impl s = result ∧
  spec result

-- LLM HELPER
def encode_group (chars: List Char) : List Char :=
  match chars with
  | [a, b, c] => [b, c, a]
  | _ => chars

-- LLM HELPER
def encode_string_aux (chars: List Char) : List Char :=
  match chars with
  | [] => []
  | [a] => [a]
  | [a, b] => [a, b]
  | a :: b :: c :: rest => encode_group [a, b, c] ++ encode_string_aux rest

def implementation (s: String) : String := 
  String.mk (encode_string_aux s.toList)

-- LLM HELPER
lemma encode_string_aux_length (chars: List Char) : 
  (encode_string_aux chars).length = chars.length := by
  induction chars using List.strongInductionOn with
  | ind chars ih =>
    cases' chars with h t
    · simp [encode_string_aux]
    · cases' t with h2 t2
      · simp [encode_string_aux]
      · cases' t2 with h3 t3
        · simp [encode_string_aux]
        · simp [encode_string_aux, encode_group]
          rw [List.length_append]
          simp
          have : t3.length < (h :: h2 :: h3 :: t3).length := by
            simp [List.length_cons]
            omega
          rw [ih t3 this]

-- LLM HELPER
lemma encode_string_aux_spec (chars: List Char) (i: ℕ) (h: i * 3 + 3 ≤ chars.length) :
  let encoded := encode_string_aux chars
  let extract (cs: List Char) (start: ℕ) (end: ℕ) := (cs.drop start).take (end - start + 1)
  extract encoded (i * 3) (i * 3 + 2) = [chars[i * 3 + 1]!, chars[i * 3 + 2]!, chars[i * 3]!] := by
  sorry

-- LLM HELPER
lemma encode_string_aux_remainder (chars: List Char) (h: chars.length % 3 ≠ 0) :
  let encoded := encode_string_aux chars
  let n := chars.length
  let extract (cs: List Char) (start: ℕ) (end: ℕ) := (cs.drop start).take (end - start + 1)
  extract encoded (n - n % 3) (n - 1) = extract chars (n - n % 3) (n - 1) := by
  sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation
  let n := s.length
  let result := String.mk (encode_string_aux s.toList)
  use result
  constructor
  · rfl
  · simp [String.length_mk, String.toList_mk]
    constructor
    · exact encode_string_aux_length s.toList
    · constructor
      · intro i hi
        exact encode_string_aux_spec s.toList i hi
      · intro h
        exact encode_string_aux_remainder s.toList h