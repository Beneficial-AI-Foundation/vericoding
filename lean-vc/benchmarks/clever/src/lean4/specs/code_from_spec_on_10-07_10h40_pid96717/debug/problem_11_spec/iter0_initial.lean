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
def xor_char (c1 c2: Char) : Char :=
  if c1 = c2 then '0' else '1'

-- LLM HELPER
def xor_strings_helper (a b: String) (i: Nat) (acc: List Char) : List Char :=
  if i ≥ a.length then acc.reverse
  else
    let i_pos := String.Pos.mk i
    let c := xor_char (a.get i_pos) (b.get i_pos)
    xor_strings_helper a b (i + 1) (c :: acc)

def implementation (a b: String) : String := 
  ⟨xor_strings_helper a b 0 []⟩

-- LLM HELPER
lemma xor_strings_helper_length (a b: String) (i: Nat) (acc: List Char) :
  i ≤ a.length → a.length = b.length →
  (xor_strings_helper a b i acc).length = (a.length - i) + acc.length := by
  intro h_le h_eq
  generalize h : a.length - i = k
  induction k using Nat.strong_induction_on generalizing i acc with
  | ind k ih =>
    unfold xor_strings_helper
    simp only [ge_iff_le]
    by_cases h_ge : i ≥ a.length
    · simp [h_ge]
      have : i = a.length := by
        cases' Nat.eq_or_lt_of_le h_le with h_eq h_lt
        · exact h_eq
        · contradiction
      rw [this]
      simp
    · simp [h_ge]
      have h_lt : i < a.length := Nat.lt_of_not_ge h_ge
      have : a.length - (i + 1) < k := by
        rw [← h]
        rw [Nat.sub_sub]
        simp [h_lt]
        rw [Nat.add_sub_cancel]
        exact Nat.sub_lt (Nat.sub_pos_of_lt h_lt) (by norm_num)
      rw [ih (a.length - (i + 1)) this (i + 1) _ (Nat.le_refl _) h_eq]
      simp [Nat.add_assoc, Nat.add_comm 1]
      rw [Nat.sub_sub, Nat.add_comm 1, ← Nat.sub_sub]
      simp [h_lt]

-- LLM HELPER
lemma xor_strings_helper_get (a b: String) (i j: Nat) (acc: List Char) :
  i ≤ a.length → a.length = b.length → j < a.length - i →
  let result := xor_strings_helper a b i acc
  let j_pos := String.Pos.mk (i + j)
  let result_pos := ⟨result.length - (a.length - i) + j⟩
  result.get result_pos = xor_char (a.get j_pos) (b.get j_pos) := by
  intro h_le h_eq h_j
  generalize h : a.length - i = k
  induction k using Nat.strong_induction_on generalizing i j acc with
  | ind k ih =>
    unfold xor_strings_helper
    simp only [ge_iff_le]
    by_cases h_ge : i ≥ a.length
    · have : a.length - i = 0 := Nat.sub_eq_zero_of_le h_ge
      rw [this] at h_j
      exact False.elim (Nat.not_lt_zero j h_j)
    · simp [h_ge]
      have h_lt : i < a.length := Nat.lt_of_not_ge h_ge
      by_cases h_zero : j = 0
      · subst h_zero
        simp
        rw [xor_strings_helper_length]
        · simp [h_lt]
          rfl
        · exact Nat.le_refl _
        · exact h_eq
      · have h_pos : j > 0 := Nat.pos_of_ne_zero h_zero
        have : a.length - (i + 1) < k := by
          rw [← h]
          rw [Nat.sub_sub]
          simp [h_lt]
          rw [Nat.add_sub_cancel]
          exact Nat.sub_lt (Nat.sub_pos_of_lt h_lt) (by norm_num)
        rw [ih (a.length - (i + 1)) this (i + 1) (j - 1) _ (Nat.le_refl _) h_eq]
        · simp [Nat.add_sub_cancel, Nat.add_assoc]
          rw [Nat.add_comm 1, ← Nat.add_assoc]
          rw [Nat.sub_add_cancel h_pos]
        · rw [Nat.sub_sub, Nat.add_comm 1, ← Nat.sub_sub]
          simp [h_lt]
          rw [Nat.sub_lt_iff_lt_add]
          · rw [Nat.add_comm]
            exact h_j
          · exact Nat.sub_pos_of_lt h_lt

-- LLM HELPER
lemma xor_char_binary (c1 c2: Char) :
  (c1 = '0' ∨ c1 = '1') → (c2 = '0' ∨ c2 = '1') → (xor_char c1 c2 = '0' ∨ xor_char c1 c2 = '1') := by
  intro h1 h2
  unfold xor_char
  by_cases h : c1 = c2
  · simp [h]
  · simp [h]

theorem correctness
(a b: String)
: problem_spec implementation a b
:= by
  unfold problem_spec
  simp
  use (implementation a b)
  constructor
  · rfl
  · intro h_a h_b h_eq
    unfold implementation
    simp
    constructor
    · rw [xor_strings_helper_length]
      · simp
      · exact Nat.le_refl _
      · exact h_eq
    constructor
    · intro c h_mem
      simp at h_mem
      obtain ⟨i, h_i, h_c⟩ := h_mem
      rw [← h_c]
      have h_len : (xor_strings_helper a b 0 []).length = a.length := by
        rw [xor_strings_helper_length]
        · simp
        · exact Nat.le_refl _
        · exact h_eq
      have h_i_bound : i < a.length := by
        rw [← h_len]
        exact h_i
      have : ∃ j, j < a.length ∧ (xor_strings_helper a b 0 []).get ⟨i, h_i⟩ = 
        xor_char (a.get (String.Pos.mk j)) (b.get (String.Pos.mk j)) := by
        use i
        constructor
        · exact h_i_bound
        · rw [xor_strings_helper_get]
          · simp
          · exact Nat.le_refl _
          · exact h_eq
          · simp
            exact h_i_bound
      obtain ⟨j, h_j, h_char⟩ := this
      rw [h_char]
      apply xor_char_binary
      · exact h_a (a.get (String.Pos.mk j)) (String.mem_iff.mpr ⟨String.Pos.mk j, rfl⟩)
      · exact h_b (b.get (String.Pos.mk j)) (String.mem_iff.mpr ⟨String.Pos.mk j, rfl⟩)
    · intro i h_i
      simp
      constructor
      · intro h_same
        rw [xor_strings_helper_get]
        · simp
          unfold xor_char
          simp [h_same]
        · exact Nat.le_refl _
        · exact h_eq
        · simp
          exact h_i
      · intro h_diff
        rw [xor_strings_helper_get]
        · simp
          unfold xor_char
          simp [h_diff]
        · exact Nat.le_refl _
        · exact h_eq
        · simp
          exact h_i