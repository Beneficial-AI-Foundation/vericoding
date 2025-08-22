import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(str: String) :=
-- spec
let spec (result : String) :=
  result.data.all (fun c => c.isLower) →
  result.length = str.length ∧
  (∀ i, i < str.length →
    let c := str.data[i]!
    let c' := result.data[i]!
    ((c'.toNat - 97) + 2 * 2) % 26 = (c.toNat - 97))
-- program termination
∃ result,
  implementation str = result ∧
  spec result

-- LLM HELPER
def shift_char (c : Char) : Char :=
  if c.isLower then
    let offset := c.toNat - 97
    let shifted := (offset + 22) % 26
    Char.ofNat (shifted + 97)
  else c

-- LLM HELPER
def shift_string (str : String) : String :=
  String.mk (str.data.map shift_char)

def implementation (str: String) : String := shift_string str

-- LLM HELPER
lemma shift_char_isLower (c : Char) : c.isLower → (shift_char c).isLower := by
  intro h
  simp [shift_char]
  rw [if_pos h]
  have h1 : c.toNat ≥ 97 := by
    rw [Char.isLower] at h
    cases h with
    | mk h_left h_right => exact h_left
  have h2 : c.toNat ≤ 122 := by
    rw [Char.isLower] at h
    cases h with
    | mk h_left h_right => exact h_right
  have h3 : (c.toNat - 97) < 26 := by
    rw [Nat.sub_lt_iff_lt_add h1]
    linarith
  have h4 : ((c.toNat - 97) + 22) % 26 < 26 := Nat.mod_lt _ (by norm_num)
  have h5 : ((c.toNat - 97) + 22) % 26 + 97 ≥ 97 := by
    simp [Nat.add_comm]
    norm_num
  have h6 : ((c.toNat - 97) + 22) % 26 + 97 ≤ 122 := by
    have : ((c.toNat - 97) + 22) % 26 ≤ 25 := by
      exact Nat.mod_lt _ (by norm_num)
    linarith
  rw [Char.isLower]
  exact ⟨h5, h6⟩

-- LLM HELPER
lemma shift_string_length (str : String) : (shift_string str).length = str.length := by
  simp [shift_string, String.length]

-- LLM HELPER
lemma shift_string_data (str : String) : (shift_string str).data = str.data.map shift_char := by
  simp [shift_string]

-- LLM HELPER
lemma shift_char_property (c : Char) : c.isLower → ((shift_char c).toNat - 97 + 4) % 26 = (c.toNat - 97) := by
  intro h
  simp [shift_char]
  rw [if_pos h]
  have h1 : c.toNat ≥ 97 := by
    rw [Char.isLower] at h
    cases h with
    | mk h_left h_right => exact h_left
  have h2 : c.toNat ≤ 122 := by
    rw [Char.isLower] at h
    cases h with
    | mk h_left h_right => exact h_right
  have h3 : (c.toNat - 97) < 26 := by
    rw [Nat.sub_lt_iff_lt_add h1]
    linarith
  have h4 : ((c.toNat - 97) + 22) % 26 + 97 ≥ 97 := by
    have : ((c.toNat - 97) + 22) % 26 ≤ 25 := Nat.mod_lt _ (by norm_num)
    linarith
  have h5 : ((c.toNat - 97) + 22) % 26 + 97 ≤ 122 := by
    have : ((c.toNat - 97) + 22) % 26 ≤ 25 := Nat.mod_lt _ (by norm_num)
    linarith
  simp [Char.toNat, Char.ofNat]
  have valid : ((c.toNat - 97) + 22) % 26 + 97 < 256 := by
    have : ((c.toNat - 97) + 22) % 26 ≤ 25 := Nat.mod_lt _ (by norm_num)
    linarith
  rw [dif_pos valid]
  simp [Char.val]
  rw [Nat.add_sub_cancel' h4]
  rw [Nat.add_mod]
  norm_num
  rw [Nat.mod_mod]

theorem correctness
(str: String)
: problem_spec implementation str
:= by
  simp [problem_spec]
  use shift_string str
  constructor
  · simp [implementation]
  · intro h
    constructor
    · exact shift_string_length str
    · intro i hi
      simp [shift_string_data]
      have h1 : i < str.data.length := by
        rw [← String.length] at hi
        exact hi
      rw [List.get_map]
      have h2 : str.data[i]!.isLower := by
        rw [String.all_iff] at h
        exact h _ (List.get_mem _ _ _)
      exact shift_char_property _ h2