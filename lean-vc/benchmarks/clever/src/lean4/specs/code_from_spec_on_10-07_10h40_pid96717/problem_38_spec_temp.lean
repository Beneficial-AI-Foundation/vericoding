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
    cases chars with
    | nil => simp [encode_string_aux]
    | cons h t =>
      cases t with
      | nil => simp [encode_string_aux]
      | cons h2 t2 =>
        cases t2 with
        | nil => simp [encode_string_aux]
        | cons h3 t3 =>
          simp [encode_string_aux, encode_group]
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
  induction i using Nat.strongInductionOn generalizing chars with
  | ind i ih =>
    cases i with
    | zero => 
      simp [extract]
      have h_len : 3 ≤ chars.length := by omega
      cases chars with
      | nil => simp at h_len
      | cons a rest =>
        cases rest with
        | nil => simp at h_len
        | cons b rest2 =>
          cases rest2 with
          | nil => simp at h_len
          | cons c rest3 =>
            simp [encode_string_aux, encode_group]
            simp [List.drop, List.take]
            rfl
    | succ j =>
      have h_len : (j + 1) * 3 + 3 ≤ chars.length := h
      have h_chars : 3 * (j + 1) + 3 ≤ chars.length := by omega
      have h_drop : 3 ≤ chars.length := by omega
      cases chars with
      | nil => simp at h_drop
      | cons a rest =>
        cases rest with
        | nil => simp at h_drop
        | cons b rest2 =>
          cases rest2 with
          | nil => simp at h_drop
          | cons c rest3 =>
            simp [encode_string_aux, encode_group]
            simp [extract, List.drop, List.take]
            have h_rec : j * 3 + 3 ≤ rest3.length := by
              have : (j + 1) * 3 + 3 = j * 3 + 6 := by omega
              rw [this] at h_chars
              simp at h_chars
              omega
            have h_lt : j < j + 1 := by omega
            have rec_call := ih j h_lt rest3 h_rec
            simp [extract] at rec_call
            rw [rec_call]
            congr
            · simp [List.get_cons_succ]
              omega
            · simp [List.get_cons_succ]
              omega
            · simp [List.get_cons_succ]
              omega

-- LLM HELPER
lemma encode_string_aux_remainder (chars: List Char) (h: chars.length % 3 ≠ 0) :
  let encoded := encode_string_aux chars
  let n := chars.length
  let extract (cs: List Char) (start: ℕ) (end: ℕ) := (cs.drop start).take (end - start + 1)
  extract encoded (n - n % 3) (n - 1) = extract chars (n - n % 3) (n - 1) := by
  induction chars using List.strongInductionOn with
  | ind chars ih =>
    cases chars with
    | nil => simp at h
    | cons a rest =>
      cases rest with
      | nil => 
        simp [encode_string_aux, extract]
        rfl
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          simp [encode_string_aux, extract]
          rfl
        | cons c rest3 =>
          simp [encode_string_aux, encode_group, extract]
          have h_len : rest3.length < (a :: b :: c :: rest3).length := by
            simp [List.length_cons]
            omega
          cases Nat.mod_two_eq_zero_or_one rest3.length with
          | inl h_even =>
            cases h_even with
            | inl h_zero => 
              simp [extract]
              congr
            | inr h_one =>
              simp [extract]
              congr
          | inr h_odd =>
            simp [extract]
            congr

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