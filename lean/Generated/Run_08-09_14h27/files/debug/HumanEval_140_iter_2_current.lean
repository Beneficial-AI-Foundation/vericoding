/- 
function_signature: "def fix_spaces(text: str) -> str"
docstring: |
    Given a string text, replace all spaces in it with underscores,
    and if a string has more than 2 consecutive spaces,
    then replace all consecutive spaces with -
test_cases:
  - input: "Example"
    expected_output: "Example"
  - input: "Example 1"
    expected_output: "Example_1"
  - input: " Example 2"
    expected_output: "_Example_2"
  - input: " Example   3"
    expected_output: "_Example-3"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def count_leading_spaces (text: String) : Nat :=
  let chars := text.toList
  chars.takeWhile (· = ' ') |>.length

def implementation (text: String) : String :=
  if text = "" then ""
  else
    let chars := text.toList
    let leading_spaces := chars.takeWhile (· = ' ') |>.length
    if leading_spaces = 0 then
      match chars with
      | [] => ""
      | c :: cs => String.mk [c] ++ implementation (String.mk cs)
    else if leading_spaces ≤ 2 then
      String.replicate leading_spaces '_' ++ implementation (text.drop leading_spaces)
    else
      "-" ++ implementation (text.drop leading_spaces)
termination_by text.length
decreasing_by
  all_goals simp_wf
  all_goals {
    have h : text.drop leading_spaces |>.length < text.length := by
      rw [String.length_drop]
      simp only [gt_iff_lt]
      omega
    exact h
  }

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
lemma count_leading_spaces_correct (text: String) :
  let n := count_leading_spaces text
  (n = 0 → text.toList.head?.map (· = ' ') = some false ∨ text = "") ∧
  (n > 0 → ∃ pref s, text = pref ++ s ∧ pref.length = n ∧ 
    (∀ ch, ch ∈ pref.toList → ch = ' ') ∧ 
    (s.toList.head?.map (· = ' ') = some false ∨ s = "")) := by
  constructor
  · intro h_zero
    unfold count_leading_spaces at h_zero
    simp at h_zero
    by_cases h_empty : text = ""
    · right; exact h_empty
    · left
      have : text.toList.takeWhile (· = ' ') = [] := by
        rw [List.takeWhile_eq_nil_iff]
        cases h : text.toList with
        | nil => simp [String.toList_eq] at h; contradiction
        | cons head tail => 
          use head
          constructor
          · simp [h]
          · rw [List.length_cons, List.length_takeWhile] at h_zero
            simp at h_zero
            exact h_zero
      cases h : text.toList with
      | nil => simp [String.toList_eq] at h; contradiction
      | cons head tail => 
        simp [List.head?_cons]
        rw [List.takeWhile_eq_nil_iff] at this
        obtain ⟨a, ha1, ha2⟩ := this
        rw [h] at ha1
        simp at ha1
        rw [ha1]
        exact ha2
  · intro h_pos
    unfold count_leading_spaces at h_pos
    simp at h_pos
    let n := text.toList.takeWhile (· = ' ') |>.length
    use String.mk (text.toList.takeWhile (· = ' ')), String.mk (text.toList.dropWhile (· = ' '))
    constructor
    · rw [← String.mk_toList text]
      simp [String.mk_append]
      rw [List.takeWhile_append_dropWhile]
    constructor
    · simp [String.length_mk]
    constructor
    · intro ch h_mem
      rw [String.mk_toList] at h_mem
      exact List.mem_takeWhile.mp h_mem
    · by_cases h_empty_drop : text.toList.dropWhile (· = ' ') = []
      · right; simp [String.mk, h_empty_drop]
      · left
        simp [List.head?_dropWhile_of_ne_nil h_empty_drop]
        exact List.head_dropWhile_not_property h_empty_drop

theorem correctness
(text: String)
: problem_spec implementation text := by
  unfold problem_spec
  use implementation text
  constructor
  · rfl
  · simp only [and_imp]
    constructor
    · intro h
      by_cases h_empty : text = ""
      · simp [h_empty]
      · simp [implementation, h_empty] at h
        cases h
    · intro h
      by_cases h_empty : text = ""
      · simp [h_empty] at h
      · simp [implementation, h_empty]
        let n := count_leading_spaces text
        by_cases h_zero : n = 0
        · left
          obtain ⟨h1, h2⟩ := (count_leading_spaces_correct text).1 h_zero
          cases h1 with
          | inl h_first =>
            cases h_text : text.toList with
            | nil => simp [String.toList_eq] at h_text; rw [h_text] at h_empty; contradiction
            | cons head tail =>
              use String.mk [head], String.mk tail
              constructor
              · rw [← String.mk_toList text, h_text]
                simp [String.mk_append, String.mk]
              constructor
              · simp [String.length_mk]
              constructor
              · simp [List.head?_cons] at h_first
                rw [h_text] at h_first
                simp at h_first
                exact h_first
              · simp [count_leading_spaces] at h_zero
                rw [h_text] at h_zero
                simp at h_zero
                rfl
          | inr h_empty_case => contradiction
        · right
          obtain ⟨pref, s, h_split, h_len, h_all_space, h_next⟩ := (count_leading_spaces_correct text).2 (Nat.pos_of_ne_zero h_zero)
          use pref, s
          constructor
          · exact h_split
          constructor
          · rw [h_len]; exact Nat.pos_of_ne_zero h_zero
          constructor
          · exact h_all_space
          constructor
          · intro h_small
            simp [count_leading_spaces, h_len] at h_small
            rw [h_split] at h_small ⊢
            simp [String.drop_append_of_le_length]
            rfl
          · intro h_large
            simp [count_leading_spaces, h_len] at h_large
            rw [h_split] at h_large ⊢
            simp [String.drop_append_of_le_length]
            rfl

-- #test implementation "Example" = "Example"
-- #test implementation "Example 1" = "Example_1"
-- #test implementation " Example 2" = "_Example_2"
-- #test implementation " Example   3" = "_Example-3"