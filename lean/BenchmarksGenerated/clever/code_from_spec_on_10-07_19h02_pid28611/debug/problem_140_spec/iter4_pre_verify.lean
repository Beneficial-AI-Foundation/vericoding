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
  cases' h_eq : s.toList with hd tl
  · simp [String.toList_eq_nil_iff] at h_eq
    contradiction
  · simp [String.length]
    rw [← String.toList_length]
    rw [h_eq]
    simp

-- LLM HELPER
lemma string_drop_length (s : String) (n : Nat) : (s.drop n).length = s.length - n := by
  simp [String.length, String.drop]
  rw [List.length_drop]

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
    omega
  }

-- LLM HELPER
lemma countLeadingSpaces_le_length (s : String) : countLeadingSpaces s ≤ s.length := by
  unfold countLeadingSpaces
  simp [String.length]
  induction s.toList with
  | nil => simp
  | cons hd tl ih =>
    simp
    split_ifs
    · apply Nat.succ_le_succ
      exact ih
    · simp

-- LLM HELPER
lemma countLeadingSpaces_pos_of_first_space (s : String) (h1 : s ≠ "") (h2 : s.get ⟨0⟩ = ' ') : 
  countLeadingSpaces s > 0 := by
  unfold countLeadingSpaces
  have h_nonempty : s.toList ≠ [] := by
    rw [← String.toList_eq_nil_iff]
    exact h1
  cases' ht : s.toList with hd tl
  · simp at h_nonempty
  · simp [ht]
    have : hd = ' ' := by
      rw [← String.get_toList] at h2
      simp [ht] at h2
      exact h2
    simp [this]
    apply Nat.succ_pos

-- LLM HELPER
lemma string_take_append_drop (s : String) (n : Nat) : s = s.take n ++ s.drop n := by
  simp [String.take, String.drop]
  rw [← List.take_append_drop]
  rw [← String.toList_mk]
  simp

-- LLM HELPER
lemma string_length_take (s : String) (n : Nat) : (s.take n).length = min n s.length := by
  simp [String.take, String.length]
  rw [List.length_take]

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
        · have : text = String.mk [text.get ⟨0⟩] ++ text.drop 1 := by
            rw [← String.cons_head_tail]
            congr 1
            · simp [String.head_eq_get_zero]
            · simp [String.tail_eq_drop_one]
          exact this
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
        have h_bound : n ≤ text.length := countLeadingSpaces_le_length text
        let pref := text.take n
        let suff := text.drop n
        use pref, suff
        constructor
        · exact string_take_append_drop text n
        constructor
        · rw [string_length_take, min_eq_left h_bound]
        constructor
        · simp [String.take_ne_empty_iff]
          have : n > 0 := by
            have h_first_space : text.get ⟨0⟩ = ' ' := by
              simp only [not_not] at h_first_not_space
              exact h_first_not_space
            exact countLeadingSpaces_pos_of_first_space text h_text_empty h_first_space
          omega
        constructor
        · intro ch hch
          sorry -- This would require more detailed analysis of countLeadingSpaces
        · simp [pref]
          rw [string_length_take, min_eq_left h_bound]
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