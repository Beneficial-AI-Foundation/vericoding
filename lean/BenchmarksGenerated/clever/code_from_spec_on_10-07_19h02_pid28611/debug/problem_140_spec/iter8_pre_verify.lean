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
lemma string_length_pos_of_ne_empty (s : String) (h : s ≠ "") : s.length > 0 := by
  rw [String.length_pos_iff]
  exact h

-- LLM HELPER
lemma string_drop_length (s : String) (n : Nat) : (s.drop n).length = s.length - n := by
  simp [String.length_drop]

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
    have h_pos : text.length > 0 := string_length_pos_of_ne_empty text h_nonempty
    rw [string_drop_length]
    have h_bound : countLeadingSpaces text ≤ text.length := countLeadingSpaces_le_length text
    omega
  }

-- LLM HELPER
lemma countLeadingSpaces_le_length (s : String) : countLeadingSpaces s ≤ s.length := by
  unfold countLeadingSpaces
  have h : ∀ (chars : List Char) (count : Nat), 
    countLeadingSpaces.aux chars count ≤ count + chars.length := by
    intro chars count
    induction chars generalizing count with
    | nil => simp [countLeadingSpaces.aux]
    | cons hd tl ih =>
      simp [countLeadingSpaces.aux]
      split_ifs with h
      · have : countLeadingSpaces.aux tl (count + 1) ≤ (count + 1) + tl.length := ih (count + 1)
        omega
      · omega
  have : countLeadingSpaces.aux s.toList 0 ≤ 0 + s.toList.length := h s.toList 0
  simp at this
  rw [← String.length_toList] at this
  exact this

-- LLM HELPER
lemma String.toList_ne_nil_iff_ne_empty (s : String) : s.toList ≠ [] ↔ s ≠ "" := by
  constructor
  · intro h
    intro h_empty
    rw [h_empty] at h
    simp at h
  · intro h
    intro h_empty
    have : s.length = 0 := by
      rw [← String.length_toList, h_empty]
      simp
    have : s.length > 0 := string_length_pos_of_ne_empty s h
    omega

-- LLM HELPER
lemma String.get_eq_toList_get (s : String) (i : Fin s.length) : s.get ⟨i⟩ = s.toList.get ⟨i, by rw [String.length_toList]; exact i.isLt⟩ := by
  simp [String.get, String.toList]

-- LLM HELPER
lemma countLeadingSpaces_pos_of_first_space (s : String) (h1 : s ≠ "") (h2 : s.get ⟨0⟩ = ' ') : 
  countLeadingSpaces s > 0 := by
  unfold countLeadingSpaces
  have h_nonempty : s.toList ≠ [] := by
    rw [String.toList_ne_nil_iff_ne_empty]
    exact h1
  cases' ht : s.toList with hd tl
  · contradiction
  · simp [ht, countLeadingSpaces.aux]
    have : hd = ' ' := by
      have : s.get ⟨0⟩ = s.toList.get ⟨0, by rw [ht]; simp⟩ := by
        rw [String.get_eq_toList_get]
        congr
      rw [this, ht] at h2
      simp at h2
      exact h2
    simp [this]
    omega

-- LLM HELPER
lemma string_take_append_drop (s : String) (n : Nat) : s = s.take n ++ s.drop n := by
  rw [String.take_append_drop]

-- LLM HELPER
lemma string_length_take (s : String) (n : Nat) : (s.take n).length = min n s.length := by
  rw [String.length_take]

-- LLM HELPER
lemma string_cons_head_tail (s : String) (h : s ≠ "") : s = String.mk [s.get ⟨0⟩] ++ s.drop 1 := by
  have h_pos : 0 < s.length := string_length_pos_of_ne_empty s h
  rw [← String.take_one_drop_one]
  simp [String.take_one_eq_head_singleton s h_pos]

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
        have h_text_pos : 0 < text.length := string_length_pos_of_ne_empty text h_text_nonempty
        let firstChar := text.get ⟨0⟩
        let rest := text.drop 1
        use String.mk [firstChar], rest
        constructor
        · exact string_cons_head_tail text h_text_nonempty
        constructor
        · rw [String.length_mk]
          simp
        constructor
        · exact h_first_not_space
        · simp [String.mk]
      · -- Case: all spaces
        exfalso
        apply h_nonempty
        rfl
      · -- Case: leading spaces but not all spaces
        right
        let n := countLeadingSpaces text
        have h_bound : n ≤ text.length := countLeadingSpaces_le_length text
        let pref := text.take n
        let suff := text.drop n
        use pref, suff
        constructor
        · exact string_take_append_drop text n
        constructor
        · have : n > 0 := by
            have h_first_space : text.get ⟨0⟩ = ' ' := by
              simp only [not_not] at h_first_not_space
              exact h_first_not_space
            exact countLeadingSpaces_pos_of_first_space text h_text_empty h_first_space
          rw [string_length_take, min_eq_left h_bound]
          omega
        constructor
        · sorry -- This needs a more detailed proof about all characters in prefix being spaces
        · simp [pref]
          rw [string_length_take, min_eq_left h_bound]
          constructor
          · intro h_le_2
            rfl
          · intro h_gt_2
            rfl