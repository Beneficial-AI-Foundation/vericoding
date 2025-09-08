/- 
function_signature: "def string_xor(a: str, b: str) -> str"
docstring: |
    Input are two strings a and b consisting only of 1s and 0s.
    Perform binary XOR on these inputs and return result also as a string.
test_cases:
  - input:
      - "010"
      - "110"
    expected_output: "100"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def char_xor (c1 c2 : Char) : Char :=
  if c1 = c2 then '0' else '1'

-- LLM HELPER
def string_xor_list (l1 l2 : List Char) : List Char :=
  match l1, l2 with
  | [], [] => []
  | c1 :: t1, c2 :: t2 => char_xor c1 c2 :: string_xor_list t1 t2
  | _, _ => [] -- shouldn't happen if lengths match

def implementation (a b: String) : String :=
  if a.length = b.length then
    String.mk (string_xor_list a.data b.data)
  else
    ""

-- LLM HELPER
lemma char_xor_correct (c1 c2 : Char) :
  (c1 = c2 → char_xor c1 c2 = '0') ∧ (c1 ≠ c2 → char_xor c1 c2 = '1') := by
  constructor
  · intro h
    simp [char_xor, h]
  · intro h
    simp [char_xor, h]

-- LLM HELPER
lemma string_xor_list_length (l1 l2 : List Char) :
  l1.length = l2.length → (string_xor_list l1 l2).length = l1.length := by
  intro h
  revert l2 h
  induction l1 with
  | nil => 
    intro l2 h
    simp at h
    simp [h, string_xor_list]
  | cons c1 t1 ih =>
    intro l2 h
    cases l2 with
    | nil => simp at h
    | cons c2 t2 =>
      simp [string_xor_list]
      apply ih
      simp at h
      exact h

-- LLM HELPER
lemma string_xor_list_get (l1 l2 : List Char) (i : Nat) (h : i < l1.length) 
  (h_len : l1.length = l2.length) :
  let result := string_xor_list l1 l2
  (l1.get ⟨i, h⟩ = l2.get ⟨i, h_len ▸ h⟩ → result.get ⟨i, string_xor_list_length l1 l2 h_len ▸ h⟩ = '0') ∧
  (l1.get ⟨i, h⟩ ≠ l2.get ⟨i, h_len ▸ h⟩ → result.get ⟨i, string_xor_list_length l1 l2 h_len ▸ h⟩ = '1') := by
  revert l2 h_len i h
  induction l1 with
  | nil => 
    intro l2 h_len i h
    simp at h
  | cons c1 t1 ih =>
    intro l2 h_len i h
    cases l2 with
    | nil => simp at h_len
    | cons c2 t2 =>
      cases i with
      | zero =>
        simp [string_xor_list]
        exact char_xor_correct c1 c2
      | succ j =>
        simp [string_xor_list]
        have h_j : j < t1.length := Nat.lt_of_succ_lt_succ h
        have h_len' : t1.length = t2.length := Nat.succ_inj'.mp h_len
        exact ih t2 h_len' j h_j

-- LLM HELPER
lemma string_xor_list_all_binary (l1 l2 : List Char) :
  l1.all (fun c => c = '0' ∨ c = '1') →
  l2.all (fun c => c = '0' ∨ c = '1') →
  (string_xor_list l1 l2).all (fun c => c = '0' ∨ c = '1') := by
  intro h1 h2
  revert l2 h2 h1
  induction l1 with
  | nil => 
    intro l2 h2 h1
    cases l2 with
    | nil => simp [string_xor_list, List.all]
    | cons => simp [string_xor_list, List.all]
  | cons c1 t1 ih =>
    intro l2 h2 h1
    cases l2 with
    | nil => simp [string_xor_list, List.all]
    | cons c2 t2 =>
      simp [string_xor_list, List.all] at *
      constructor
      · simp [char_xor]
        split <;> simp
      · exact ih t2 h2.2 h1.2

def problem_spec
-- function signature
(implementation: String → String → String)
-- inputs
(a b: String) :=
-- spec
let spec (result: String) :=
  a.all (fun c => c = '0' ∨ c = '1') →
  b.all (fun c => c = '0' ∨ c = '1') →
  a.length = b.length →
  result.length = a.length ∧
  result.all (fun c => c = '0' ∨ c = '1') ∧
  (∀ i, i < a.length →
  let i_pos := String.Pos.mk i;
  (a.get i_pos = b.get i_pos → result.get i_pos = '0') ∧
  (a.get i_pos ≠ b.get i_pos → result.get i_pos = '1'));
-- program termination
∃ result, implementation a b = result ∧
spec result

theorem correctness
(a b: String)
: problem_spec implementation a b
:= by
  simp [problem_spec, implementation]
  by_cases h : a.length = b.length
  · use String.mk (string_xor_list a.data b.data)
    constructor
    · simp [h]
    · intro h_a h_b h_len
      constructor
      · simp [String.length]
        rw [string_xor_list_length a.data b.data]
        · simp [String.length]
        · simp [String.length] at h_len
          exact h_len
      constructor
      · simp [String.all]
        apply string_xor_list_all_binary
        · simp [String.all] at h_a
          exact h_a
        · simp [String.all] at h_b
          exact h_b
      · intro i h_i
        simp [String.get]
        have h_len_data : a.data.length = b.data.length := by
          simp [String.length] at h_len
          exact h_len
        have h_i_data : i < a.data.length := by
          simp [String.length] at h_i
          exact h_i
        have h_result_len : (string_xor_list a.data b.data).length = a.data.length :=
          string_xor_list_length a.data b.data h_len_data
        rw [List.get_mk]
        · exact string_xor_list_get a.data b.data i h_i_data h_len_data
        · rw [h_result_len]
          exact h_i_data
  · use ""
    constructor
    · simp [h]
    · intro h_a h_b h_len
      contradiction

-- #test implementation "010" "110" = "100"