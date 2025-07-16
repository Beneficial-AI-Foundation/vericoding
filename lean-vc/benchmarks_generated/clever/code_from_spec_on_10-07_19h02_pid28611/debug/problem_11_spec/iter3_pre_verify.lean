import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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

-- LLM HELPER
def xor_bit (c1 c2: Char) : Char :=
  if c1 = c2 then '0' else '1'

-- LLM HELPER
def string_xor_aux (s1 s2: String) (i: Nat) : String :=
  if i >= s1.length then ""
  else 
    let pos := String.Pos.mk i
    let c1 := s1.get pos
    let c2 := s2.get pos
    let xor_c := xor_bit c1 c2
    String.mk [xor_c] ++ string_xor_aux s1 s2 (i + 1)
  termination_by s1.length - i

def implementation (a b: String) : String := 
  string_xor_aux a b 0

-- LLM HELPER
lemma string_xor_aux_length (s1 s2: String) (i: Nat) :
  (string_xor_aux s1 s2 i).length = if i >= s1.length then 0 else s1.length - i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rw [string_xor_aux]
    split_ifs with h1
    · simp
    · simp [String.length_append, String.length_mk]
      rw [ih (i + 1)]
      simp
      · omega
      · omega

-- LLM HELPER
lemma string_xor_aux_get (s1 s2: String) (i j: Nat) (h: j < s1.length - i) (hi: i < s1.length) :
  let result := string_xor_aux s1 s2 i
  result.get (String.Pos.mk j) = xor_bit (s1.get (String.Pos.mk (i + j))) (s2.get (String.Pos.mk (i + j))) := by
  induction j, s1.length - i using Nat.strong_induction_on with
  | h j ih =>
    rw [string_xor_aux]
    split_ifs with h_ge
    · omega
    · simp only [String.get_append]
      by_cases h_eq: j = 0
      · simp [h_eq]
        rw [String.get_mk_zero]
        simp [Nat.zero_add]
      · have j_pos: j > 0 := Nat.pos_of_ne_zero h_eq
        have j_ge_one: j ≥ 1 := j_pos
        simp [String.get_mk_cons j_ge_one]
        have : j - 1 < s1.length - (i + 1) := by omega
        rw [ih (j - 1)]
        congr 1
        omega
        exact this
        omega

-- LLM HELPER
lemma string_xor_aux_all_binary (s1 s2: String) (i: Nat) 
  (h1: s1.all (fun c => c = '0' ∨ c = '1'))
  (h2: s2.all (fun c => c = '0' ∨ c = '1')) :
  (string_xor_aux s1 s2 i).all (fun c => c = '0' ∨ c = '1') := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rw [string_xor_aux]
    split_ifs with h_ge
    · simp
    · simp [String.all_append]
      constructor
      · simp [String.all_mk, xor_bit]
        split_ifs
        · left; rfl
        · right; rfl
      · apply ih (i + 1)
        omega

-- LLM HELPER
lemma xor_bit_eq_iff (c1 c2: Char) :
  xor_bit c1 c2 = '0' ↔ c1 = c2 := by
  simp [xor_bit]

-- LLM HELPER
lemma xor_bit_ne_iff (c1 c2: Char) :
  xor_bit c1 c2 = '1' ↔ c1 ≠ c2 := by
  simp [xor_bit]
  split_ifs with h
  · simp [h]
  · simp [h]

theorem correctness
(a b: String)
: problem_spec implementation a b := by
  simp [problem_spec, implementation]
  use string_xor_aux a b 0
  constructor
  · rfl
  intro ha hb hab
  constructor
  · rw [string_xor_aux_length]
    simp
    rw [hab]
  constructor
  · apply string_xor_aux_all_binary
    exact ha
    exact hb
  · intro i hi
    constructor
    · intro h_eq
      rw [string_xor_aux_get]
      rw [xor_bit_eq_iff]
      rw [Nat.zero_add]
      exact h_eq
      rw [string_xor_aux_length]
      simp
      omega
      omega
    · intro h_ne
      rw [string_xor_aux_get]
      rw [xor_bit_ne_iff]
      rw [Nat.zero_add]
      exact h_ne
      rw [string_xor_aux_length]
      simp
      omega
      omega