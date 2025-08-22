import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
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
def countLeadingSpaces (s : String) : Nat :=
  let rec aux (chars : List Char) (count : Nat) : Nat :=
    match chars with
    | [] => count
    | c :: rest => if c = ' ' then aux rest (count + 1) else count
  aux s.toList 0

-- LLM HELPER
def isAllSpaces (s : String) : Bool :=
  s.toList.all (· = ' ')

def implementation (text: String) : String :=
  if text = "" then ""
  else
    let firstChar := text.get ⟨0⟩
    if firstChar ≠ ' ' then
      let rest := text.drop 1
      String.mk [firstChar] ++ implementation rest
    else
      let leadingSpaces := countLeadingSpaces text
      if leadingSpaces = text.length then ""
      else
        let rest := text.drop leadingSpaces
        if leadingSpaces ≤ 2 then
          String.replicate leadingSpaces '_' ++ implementation rest
        else
          "-" ++ implementation rest

-- LLM HELPER
lemma countLeadingSpaces_correct (s : String) :
  let n := countLeadingSpaces s
  (∀ i : Nat, i < n → s.get? i = some ' ') ∧
  (n < s.length → s.get? n ≠ some ' ') ∧
  n ≤ s.length := by
  sorry

-- LLM HELPER
lemma string_split_at_spaces (text : String) (n : Nat) (h : n ≤ text.length) :
  ∃ pref suff, text = pref ++ suff ∧ pref.length = n ∧ suff = text.drop n := by
  use text.take n, text.drop n
  constructor
  · exact String.take_append_drop n text
  constructor
  · exact String.length_take n text
  · rfl

-- LLM HELPER
lemma isAllSpaces_correct (s : String) :
  isAllSpaces s = true ↔ ∀ ch, ch ∈ s.toList → ch = ' ' := by
  sorry

theorem correctness
(text: String)
: problem_spec implementation text := by
  unfold problem_spec
  use implementation text
  constructor
  · rfl
  · intro result h_eq
    unfold implementation at h_eq
    rw [← h_eq]
    constructor
    · intro h_empty
      split_ifs at h_empty with h_text_empty
      · exact h_text_empty
      · simp at h_empty
    · intro h_nonempty
      split_ifs with h_text_empty h_first_not_space
      · contradiction
      · -- Case: first character is not a space
        left
        have h_text_nonempty : text ≠ "" := h_text_empty
        have h_text_pos : 0 < text.length := by
          rw [String.length_pos_iff_ne_empty]
          exact h_text_nonempty
        let firstChar := text.get ⟨0⟩
        let rest := text.drop 1
        use String.mk [firstChar], rest
        constructor
        · simp [String.mk_one_char_append_drop]
        constructor
        · simp [String.length_mk]
        constructor
        · exact h_first_not_space
        · simp [String.mk_one_char]
      · -- Case: first character is a space
        right
        let n := countLeadingSpaces text
        have h_spaces : ∀ i : Nat, i < n → text.get? i = some ' ' := by
          exact (countLeadingSpaces_correct text).1
        have h_bound : n ≤ text.length := (countLeadingSpaces_correct text).2.2
        cases' Nat.lt_or_eq_of_le h_bound with h_lt h_eq
        · -- n < text.length
          have h_not_all_spaces : ¬(n = text.length) := by
            linarith
          let pref := text.take n
          let suff := text.drop n
          use pref, suff
          constructor
          · exact String.take_append_drop n text
          constructor
          · rw [String.length_take]
            exact min_eq_left h_bound
          constructor
          · sorry -- prove all chars in pref are spaces
          · simp [pref]
            split_ifs with h_le_2
            · constructor
              · intro
                congr 1
                simp [String.length_take]
                rw [min_eq_left h_bound]
              · intro
                rfl
            · constructor
              · intro h_contra
                linarith
              · intro
                rfl
        · -- n = text.length (all spaces)
          exfalso
          apply h_nonempty
          simp [implementation]
          split_ifs
          · rfl
          · simp at h_first_not_space
            have : text.get ⟨0⟩ = ' ' := by
              have h_pos : 0 < text.length := by
                rw [String.length_pos_iff_ne_empty]
                exact h_text_empty
              rw [← h_eq] at h_pos
              have : 0 < n := h_pos
              have : text.get? 0 = some ' ' := h_spaces 0 this
              rw [String.get?_eq_some_get] at this
              simp at this
              exact this.2
            contradiction
          · have h_all_spaces : countLeadingSpaces text = text.length := h_eq
            simp [h_all_spaces]