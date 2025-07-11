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
def encode_triple (chars: List Char) : List Char :=
  match chars with
  | [a, b, c] => [b, c, a]
  | _ => chars

-- LLM HELPER
def encode_string_aux (chars: List Char) : List Char :=
  match chars with
  | [] => []
  | [a] => [a]
  | [a, b] => [a, b]
  | a :: b :: c :: rest => encode_triple [a, b, c] ++ encode_string_aux rest

def implementation (s: String) : String := 
  ⟨encode_string_aux s.toList⟩

-- LLM HELPER
lemma encode_triple_correct (a b c : Char) :
  encode_triple [a, b, c] = [b, c, a] := by
  rfl

-- LLM HELPER
lemma encode_string_aux_length (chars: List Char) :
  (encode_string_aux chars).length = chars.length := by
  induction chars using List.strongInductionOn with
  | ind chars ih =>
    cases chars with
    | nil => simp [encode_string_aux]
    | cons a tail =>
      cases tail with
      | nil => simp [encode_string_aux]
      | cons b tail2 =>
        cases tail2 with
        | nil => simp [encode_string_aux]
        | cons c rest =>
          simp [encode_string_aux, encode_triple]
          rw [List.length_cons, List.length_cons, List.length_cons]
          rw [List.length_append]
          simp [encode_triple]
          rw [ih rest]
          · simp
          · simp

-- LLM HELPER
lemma extract_def (chars: List Char) (start_index end_index: ℕ) :
  let extract := fun (chars: List Char) (start_index: ℕ) (end_index: ℕ) =>
    (chars.drop start_index).take (end_index - start_index + 1)
  extract chars start_index end_index = (chars.drop start_index).take (end_index - start_index + 1) := by
  rfl

-- LLM HELPER
lemma encode_string_aux_triple_property (chars: List Char) (i: ℕ) :
  i * 3 + 3 ≤ chars.length →
  let extract := fun (chars: List Char) (start_index: ℕ) (end_index: ℕ) =>
    (chars.drop start_index).take (end_index - start_index + 1)
  extract (encode_string_aux chars) (i * 3) (i * 3 + 2) =
    [chars[i * 3 + 1]!, chars[i * 3 + 2]!, chars[i * 3]!] := by
  intro h
  induction i with
  | zero =>
    simp only [zero_mul, zero_add] at h ⊢
    cases chars with
    | nil => simp at h
    | cons a tail =>
      cases tail with
      | nil => simp at h
      | cons b tail2 =>
        cases tail2 with
        | nil => simp at h
        | cons c rest =>
          simp [encode_string_aux, encode_triple]
          simp [List.drop, List.take]
          simp [List.getElem_cons_zero, List.getElem_cons_succ]
  | succ k ih =>
    have h_len : k * 3 + 3 ≤ chars.length := by
      simp at h
      linarith
    cases chars with
    | nil => simp at h
    | cons a tail =>
      cases tail with
      | nil => simp at h
      | cons b tail2 =>
        cases tail2 with
        | nil => simp at h
        | cons c rest =>
          simp [encode_string_aux, encode_triple]
          simp [Nat.succ_mul]
          have : (k + 1) * 3 = k * 3 + 3 := by ring
          rw [this]
          simp [List.drop_append]
          apply ih
          simp at h
          linarith

-- LLM HELPER
lemma encode_string_aux_remainder_property (chars: List Char) :
  chars.length % 3 ≠ 0 →
  let extract := fun (chars: List Char) (start_index: ℕ) (end_index: ℕ) =>
    (chars.drop start_index).take (end_index - start_index + 1)
  extract (encode_string_aux chars) (chars.length - chars.length % 3) (chars.length - 1) =
    extract chars (chars.length - chars.length % 3) (chars.length - 1) := by
  intro h
  induction chars using List.strongInductionOn with
  | ind chars ih =>
    cases chars with
    | nil => simp at h
    | cons a tail =>
      cases tail with
      | nil => 
        simp [encode_string_aux]
      | cons b tail2 =>
        cases tail2 with
        | nil =>
          simp [encode_string_aux]
        | cons c rest =>
          simp [encode_string_aux, encode_triple]
          simp [List.length_cons]
          have len_eq : (c :: rest).length + 3 = (a :: b :: c :: rest).length := by simp
          rw [← len_eq]
          simp [List.drop_append]
          apply ih
          · simp
          · simp at h
            cases rest with
            | nil => simp at h
            | cons d rest2 => 
              simp [List.length_cons] at h
              exact h

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use ⟨encode_string_aux s.toList⟩
  constructor
  · rfl
  · constructor
    · simp [String.length_toList, encode_string_aux_length]
    · constructor
      · intro i h
        apply encode_string_aux_triple_property
        exact h
      · intro h
        apply encode_string_aux_remainder_property
        exact h