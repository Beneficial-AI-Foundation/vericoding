import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: String → String)
-- inputs
(text: String) :=
-- spec
let spec (result: String) :=
  (result = "" → text = "") ∧
  (result ≠ "" → (
    (∃ pref s, text = pref ++ s
      ∧ pref.length = 1
      ∧ pref ≠ " "
      ∧ result = pref ++ impl s)
    ∨
    (∃ pref s : String, text = pref ++ s ∧ pref ≠ "" ∧ (∀ ch, ch ∈ pref.toList → ch = ' ')
      ∧ let k := pref.length;
        (k ≤ 2 → result = (String.replicate k '_') ++ (impl (text.drop k)))
      ∧ (2 < k → result = "-" ++ (impl (text.drop k)))) )
  )
-- program termination
∃ result, impl text = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def count_leading_spaces (s: String) : Nat :=
  s.toList.takeWhile (· = ' ') |>.length

-- LLM HELPER
def all_spaces (s: String) : Prop :=
  ∀ ch, ch ∈ s.toList → ch = ' '

-- LLM HELPER
lemma all_spaces_takeWhile (s: String) : all_spaces (String.mk (s.toList.takeWhile (· = ' '))) := by
  intro ch h
  simp [String.mk] at h
  exact List.mem_takeWhile.mp h

-- LLM HELPER
lemma takeWhile_spaces_eq (s: String) : 
  String.mk (s.toList.takeWhile (· = ' ')) = s.take (count_leading_spaces s) := by
  simp [count_leading_spaces, String.take]

-- LLM HELPER
lemma string_decomp_spaces (s: String) : 
  s = s.take (count_leading_spaces s) ++ s.drop (count_leading_spaces s) := by
  rw [String.take_append_drop]

def implementation (text: String) : String := 
  if text = "" then ""
  else if text.get? 0 = some ' ' then
    let k := count_leading_spaces text
    if k ≤ 2 then
      String.replicate k '_' ++ implementation (text.drop k)
    else
      "-" ++ implementation (text.drop k)
  else
    let first_char := text.take 1
    first_char ++ implementation (text.drop 1)

theorem correctness
(text: String)
: problem_spec implementation text := by
  unfold problem_spec
  use implementation text
  constructor
  · rfl
  · intro result h
    subst h
    constructor
    · intro h
      unfold implementation at h
      split_ifs at h
      · assumption
      · simp at h
      · simp at h
    · intro h
      unfold implementation at h
      split_ifs at h with h1 h2
      · contradiction
      · -- Case: first character is space
        right
        let k := count_leading_spaces text
        use text.take k, text.drop k
        constructor
        · exact string_decomp_spaces text
        constructor
        · -- pref ≠ ""
          simp [String.take_pos_iff]
          constructor
          · simp [count_leading_spaces]
            have : text.get? 0 = some ' ' := h2
            rw [String.get?_zero_eq_head?] at this
            cases' text.toList with hd tl
            · simp at this
            · simp at this
              subst this
              simp [List.takeWhile]
          · exact Nat.zero_lt_of_ne_zero h1
        constructor
        · -- all chars in pref are spaces
          rw [takeWhile_spaces_eq]
          exact all_spaces_takeWhile text
        · constructor
          · -- k ≤ 2 case
            intro hk
            simp [k] at hk ⊢
            split_ifs at h with h3
            · exact h
            · omega
          · -- 2 < k case
            intro hk
            simp [k] at hk ⊢
            split_ifs at h with h3
            · omega
            · exact h
      · -- Case: first character is not space
        left
        use text.take 1, text.drop 1
        constructor
        · rw [String.take_append_drop]
        constructor
        · simp
          exact String.length_take_le_one text
        constructor
        · -- pref ≠ " "
          have : text.get? 0 ≠ some ' ' := h2
          by_contra h_contra
          have : text.take 1 = " " := h_contra
          have : text.get? 0 = some ' ' := by
            cases' ht : text.toList with hd tl
            · simp [String.get?_zero_eq_head?, ht]
            · simp [String.take, String.get?_zero_eq_head?, ht] at this
              exact this.symm
          contradiction
        · exact h