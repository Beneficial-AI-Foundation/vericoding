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
lemma string_mk_length (l: List Char) : (String.mk l).length = l.length := by
  rfl

-- LLM HELPER
lemma string_data_length (s: String) : s.data.length = s.length := by
  rfl

-- LLM HELPER
lemma list_zipWith_length (l1 l2: List Char) : 
  (List.zipWith xor_bit l1 l2).length = min l1.length l2.length := by
  exact List.length_zipWith

-- LLM HELPER
lemma string_all_iff_list_all (s: String) (p: Char → Prop) [DecidablePred p] :
  s.all (fun c => decide (p c)) = s.data.all (fun c => decide (p c)) := by
  rfl

-- LLM HELPER
lemma list_all_zipWith_xor_bit (l1 l2: List Char) 
  (h1: l1.all (fun c => decide (c = '0' ∨ c = '1')))
  (h2: l2.all (fun c => decide (c = '0' ∨ c = '1'))) :
  (List.zipWith xor_bit l1 l2).all (fun c => decide (c = '0' ∨ c = '1')) := by
  induction l1, l2 using List.zipWith.induction with
  | nil => simp
  | cons h1 h2 _ ih =>
    simp [List.zipWith, List.all_cons]
    constructor
    · simp [xor_bit]
      split_ifs <;> simp
    · apply ih
      · simp [List.all_cons] at h1
        exact h1.2
      · simp [List.all_cons] at h2
        exact h2.2

-- LLM HELPER
lemma string_get_mk_nth (l: List Char) (i: Nat) (h: i < l.length) :
  (String.mk l).get (String.Pos.mk i) = l[i] := by
  rfl

-- LLM HELPER
lemma list_get_zipWith_xor_bit (l1 l2: List Char) (i: Nat) 
  (h1: i < l1.length) (h2: i < l2.length) :
  (List.zipWith xor_bit l1 l2)[i]'(by rw [List.length_zipWith]; omega) = 
  xor_bit l1[i] l2[i] := by
  exact List.getElem_zipWith xor_bit l1 l2 i

-- LLM HELPER
lemma string_get_data (s: String) (i: Nat) (h: i < s.length) :
  s.get (String.Pos.mk i) = s.data[i] := by
  rfl

-- LLM HELPER
lemma xor_bit_eq_iff (c1 c2: Char) :
  xor_bit c1 c2 = '0' ↔ c1 = c2 := by
  simp [xor_bit]
  split_ifs with h
  · simp [h]
  · simp [h]

-- LLM HELPER
lemma xor_bit_ne_iff (c1 c2: Char) :
  xor_bit c1 c2 = '1' ↔ c1 ≠ c2 := by
  simp [xor_bit]
  split_ifs with h
  · simp [h]
  · simp [h]

def implementation (a b: String) : String := 
  String.mk (List.zipWith xor_bit a.data b.data)

theorem correctness
(a b: String)
: problem_spec implementation a b := by
  simp [problem_spec, implementation]
  use String.mk (List.zipWith xor_bit a.data b.data)
  constructor
  · rfl
  intro ha hb hab
  constructor
  · rw [string_mk_length, list_zipWith_length]
    rw [string_data_length, string_data_length, hab]
    simp
  constructor
  · rw [string_all_iff_list_all]
    simp [String.mk]
    apply list_all_zipWith_xor_bit
    · rw [← string_all_iff_list_all]
      exact ha
    · rw [← string_all_iff_list_all] 
      exact hb
  · intro i hi
    constructor
    · intro h_eq
      rw [string_get_mk_nth]
      rw [list_get_zipWith_xor_bit]
      rw [xor_bit_eq_iff]
      rw [← string_get_data, ← string_get_data]
      exact h_eq
      · rw [string_data_length]; exact hi
      · rw [string_data_length, hab]; exact hi
      · rw [list_zipWith_length, string_data_length, string_data_length, hab]
        simp [hi]
    · intro h_ne
      rw [string_get_mk_nth]
      rw [list_get_zipWith_xor_bit]
      rw [xor_bit_ne_iff]
      rw [← string_get_data, ← string_get_data]
      exact h_ne
      · rw [string_data_length]; exact hi
      · rw [string_data_length, hab]; exact hi
      · rw [list_zipWith_length, string_data_length, string_data_length, hab]
        simp [hi]