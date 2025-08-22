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
lemma string_drop_length_lt (text : String) (n : Nat) (h1 : text ≠ "") (h2 : n > 0) (h3 : n ≤ text.length) : 
  (text.drop n).length < text.length := by
  simp [String.length_drop]
  have : text.length > 0 := by
    rw [String.length_pos_iff_ne_empty]
    exact h1
  omega

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
termination_by text.length
decreasing_by
  simp_wf
  all_goals {
    have h_nonempty : text ≠ "" := by assumption
    have h_pos : text.length > 0 := by
      rw [String.length_pos_iff_ne_empty]
      exact h_nonempty
    simp [String.length_drop]
    split_ifs with h1 h2
    · omega
    · have h_spaces_pos : countLeadingSpaces text > 0 := by
        have h_first_space : text.get ⟨0⟩ = ' ' := by
          simp only [not_not] at h2
          exact h2
        unfold countLeadingSpaces
        simp [String.toList_get]
        have : text.toList ≠ [] := by
          rw [← String.toList_eq_nil_iff]
          exact h_nonempty
        cases' ht : text.toList with hd tl
        · simp at this
        · simp [ht]
          rw [← String.get_toList_eq] at h_first_space
          simp [ht] at h_first_space
          simp [h_first_space]
          apply Nat.succ_pos
      have h_spaces_le : countLeadingSpaces text ≤ text.length := by
        unfold countLeadingSpaces
        simp [String.length_eq_toList_length]
        induction text.toList with
        | nil => simp
        | cons hd tl ih =>
          simp
          split_ifs
          · apply Nat.succ_le_succ
            exact ih
          · simp
      omega
    · have h_spaces_pos : countLeadingSpaces text > 0 := by
        have h_first_space : text.get ⟨0⟩ = ' ' := by
          simp only [not_not] at h2
          exact h2
        unfold countLeadingSpaces
        simp [String.toList_get]
        have : text.toList ≠ [] := by
          rw [← String.toList_eq_nil_iff]
          exact h_nonempty
        cases' ht : text.toList with hd tl
        · simp at this
        · simp [ht]
          rw [← String.get_toList_eq] at h_first_space
          simp [ht] at h_first_space
          simp [h_first_space]
          apply Nat.succ_pos
      have h_spaces_le : countLeadingSpaces text ≤ text.length := by
        unfold countLeadingSpaces
        simp [String.length_eq_toList_length]
        induction text.toList with
        | nil => simp
        | cons hd tl ih =>
          simp
          split_ifs
          · apply Nat.succ_le_succ
            exact ih
          · simp
      omega
  }

-- LLM HELPER
lemma countLeadingSpaces_correct (s : String) :
  let n := countLeadingSpaces s
  (∀ i : Nat, i < n → s.get? ⟨i⟩ = some ' ') ∧
  (n < s.length → s.get? ⟨n⟩ ≠ some ' ') ∧
  n ≤ s.length := by
  unfold countLeadingSpaces
  simp [String.length_eq_toList_length]
  induction s.toList with
  | nil => simp
  | cons hd tl ih =>
    simp
    split_ifs with h
    · simp [h]
      constructor
      · intro i hi
        cases i with
        | zero => simp [String.get?_zero_eq_head, h]
        | succ j => 
          simp [String.get?_succ]
          exact ih.1 j (Nat.lt_of_succ_lt_succ hi)
      · constructor
        · intro hlt
          cases hlt with
          | zero => simp [String.get?_zero_eq_head, h]
          | succ j =>
            simp [String.get?_succ]
            exact ih.2.1 j
        · apply Nat.succ_le_succ
          exact ih.2.2
    · simp [h]
      constructor
      · intro i hi
        cases i with
        | zero => simp [String.get?_zero_eq_head, h]
        | succ j => omega
      · constructor
        · intro hlt
          cases hlt
          simp [String.get?_zero_eq_head, h]
        · simp

-- LLM HELPER
lemma string_split_at_spaces (text : String) (n : Nat) (h : n ≤ text.length) :
  ∃ pref suff, text = pref ++ suff ∧ pref.length = n ∧ suff = text.drop n := by
  use text.take n, text.drop n
  constructor
  · rw [String.take_append_drop]
  constructor
  · rw [String.length_take, min_eq_left h]
  · rfl

theorem correctness
(text: String)
: problem_spec implementation text := by
  unfold problem_spec
  use implementation text
  constructor
  · rfl
  · intro result h_eq
    rw [← h_eq]
    constructor
    · intro h_empty
      unfold implementation at h_empty
      split_ifs at h_empty with h_text_empty
      · exact h_text_empty
      · simp at h_empty
    · intro h_nonempty
      unfold implementation at h_nonempty
      split_ifs at h_nonempty with h_text_empty h_first_not_space h_all_spaces
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
        · simp [← String.cons_head_tail]
          congr 1
          · simp [String.head_eq_get_zero]
          · simp [String.tail_eq_drop_one]
        constructor
        · simp [String.length_mk]
        constructor
        · exact h_first_not_space
        · simp [String.mk_one_char]
      · -- Case: all spaces
        exfalso
        apply h_nonempty
        rfl
      · -- Case: leading spaces but not all spaces
        right
        let n := countLeadingSpaces text
        have h_bound : n ≤ text.length := (countLeadingSpaces_correct text).2.2
        let pref := text.take n
        let suff := text.drop n
        use pref, suff
        constructor
        · rw [String.take_append_drop]
        constructor
        · rw [String.length_take, min_eq_left h_bound]
        constructor
        · simp [String.take_ne_empty_iff]
          have : n > 0 := by
            have h_first_space : text.get ⟨0⟩ = ' ' := by
              simp only [not_not] at h_first_not_space
              exact h_first_not_space
            have h_correct := countLeadingSpaces_correct text
            unfold countLeadingSpaces at h_correct
            simp at h_correct
            have : text.length > 0 := by
              rw [String.length_pos_iff_ne_empty]
              exact h_text_empty
            omega
          omega
        constructor
        · intro ch hch
          have h_correct := countLeadingSpaces_correct text
          simp [String.mem_toList_iff_get] at hch
          obtain ⟨i, hi, hget⟩ := hch
          have hi_bound : i < n := by
            rw [String.length_take, min_eq_left h_bound] at hi
            exact hi
          rw [String.get_take] at hget
          have : text.get? ⟨i⟩ = some ' ' := h_correct.1 i hi_bound
          simp [String.get?_eq_get] at this
          rw [← hget]
          exact this
        · simp [pref]
          rw [String.length_take, min_eq_left h_bound]
          split_ifs with h_le_2
          · constructor
            · intro
              congr 1
            · intro
              rfl
          · constructor
            · intro h_contra
              linarith
            · intro
              rfl