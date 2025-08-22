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

def implementation (str: String) : String := 
  String.mk (str.data.map shift_char)

-- LLM HELPER
lemma char_isLower_iff (c : Char) : c.isLower = true ↔ c.val ≥ 97 ∧ c.val ≤ 122 := by
  constructor
  · intro h
    rw [Char.isLower] at h
    simp at h
    exact h
  · intro h
    rw [Char.isLower]
    simp
    exact h

-- LLM HELPER
lemma shift_char_isLower (c : Char) : c.isLower → (shift_char c).isLower := by
  intro h
  simp [shift_char]
  rw [if_pos h]
  have h1 : c.val ≥ 97 := by
    rw [char_isLower_iff] at h
    exact h.1
  have h2 : c.val ≤ 122 := by
    rw [char_isLower_iff] at h
    exact h.2
  have h3 : (c.val - 97) < 26 := by
    rw [Nat.sub_lt_iff_lt_add h1]
    linarith
  have h4 : ((c.val - 97) + 22) % 26 < 26 := Nat.mod_lt _ (by norm_num)
  have h5 : ((c.val - 97) + 22) % 26 + 97 ≥ 97 := by
    linarith [Nat.zero_le (((c.val - 97) + 22) % 26)]
  have h6 : ((c.val - 97) + 22) % 26 + 97 ≤ 122 := by
    have : ((c.val - 97) + 22) % 26 ≤ 25 := by
      have mod_lt := Nat.mod_lt ((c.val - 97) + 22) (by norm_num : (0 : Nat) < 26)
      exact Nat.le_sub_one_of_lt mod_lt
    linarith
  rw [char_isLower_iff]
  have valid : ((c.val - 97) + 22) % 26 + 97 < 256 := by
    have : ((c.val - 97) + 22) % 26 ≤ 25 := by
      have mod_lt := Nat.mod_lt ((c.val - 97) + 22) (by norm_num : (0 : Nat) < 26)
      exact Nat.le_sub_one_of_lt mod_lt
    linarith
  have char_eq : (Char.ofNat (((c.val - 97) + 22) % 26 + 97)).val = ((c.val - 97) + 22) % 26 + 97 := by
    rw [Char.ofNat_val]
    rw [Nat.mod_eq_of_lt valid]
  rw [char_eq]
  exact ⟨h5, h6⟩

-- LLM HELPER
lemma shift_char_property (c : Char) : c.isLower → ((shift_char c).val - 97 + 4) % 26 = (c.val - 97) := by
  intro h
  simp [shift_char]
  rw [if_pos h]
  have h1 : c.val ≥ 97 := by
    rw [char_isLower_iff] at h
    exact h.1
  have h2 : c.val ≤ 122 := by
    rw [char_isLower_iff] at h
    exact h.2
  have h3 : (c.val - 97) < 26 := by
    rw [Nat.sub_lt_iff_lt_add h1]
    linarith
  have h4 : ((c.val - 97) + 22) % 26 + 97 ≥ 97 := by
    have : ((c.val - 97) + 22) % 26 ≤ 25 := by
      have mod_lt := Nat.mod_lt ((c.val - 97) + 22) (by norm_num : (0 : Nat) < 26)
      exact Nat.le_sub_one_of_lt mod_lt
    linarith
  have h5 : ((c.val - 97) + 22) % 26 + 97 ≤ 122 := by
    have : ((c.val - 97) + 22) % 26 ≤ 25 := by
      have mod_lt := Nat.mod_lt ((c.val - 97) + 22) (by norm_num : (0 : Nat) < 26)
      exact Nat.le_sub_one_of_lt mod_lt
    linarith
  have valid : ((c.val - 97) + 22) % 26 + 97 < 256 := by
    have : ((c.val - 97) + 22) % 26 ≤ 25 := by
      have mod_lt := Nat.mod_lt ((c.val - 97) + 22) (by norm_num : (0 : Nat) < 26)
      exact Nat.le_sub_one_of_lt mod_lt
    linarith
  have char_eq : (Char.ofNat (((c.val - 97) + 22) % 26 + 97)).val = ((c.val - 97) + 22) % 26 + 97 := by
    rw [Char.ofNat_val]
    rw [Nat.mod_eq_of_lt valid]
  rw [char_eq]
  rw [Nat.add_sub_cancel' h4]
  have key : (((c.val - 97) + 22) % 26 + 4) % 26 = (c.val - 97) := by
    have eq1 : ((c.val - 97) + 22) % 26 + 4 = ((c.val - 97) + 26) % 26 := by
      rw [← Nat.add_mod]
      have : (c.val - 97) + 22 + 4 = (c.val - 97) + 26 := by norm_num
      rw [this]
    rw [eq1]
    rw [Nat.add_mod]
    simp
    exact Nat.mod_eq_of_lt h3
  exact key

theorem correctness
(str: String)
: problem_spec implementation str
:= by
  simp [problem_spec]
  use String.mk (str.data.map shift_char)
  constructor
  · simp [implementation]
  · intro h
    constructor
    · simp [String.length]
      rw [List.length_map]
    · intro i hi
      simp [String.data, List.get_map]
      have h1 : i < str.data.length := by
        rw [← String.length] at hi
        exact hi
      have h2 : str.data[i]!.isLower := by
        rw [List.all_iff_forall] at h
        exact h _ (List.get_mem _ _ _)
      exact shift_char_property _ h2