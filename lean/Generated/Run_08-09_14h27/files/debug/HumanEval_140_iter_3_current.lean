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
      | c :: cs => 
        if c = ' ' then "_" ++ implementation (String.mk cs)
        else String.mk [c] ++ implementation (String.mk cs)
    else if leading_spaces ≤ 2 then
      String.replicate leading_spaces '_' ++ implementation (text.drop leading_spaces)
    else
      "-" ++ implementation (text.drop leading_spaces)
termination_by text.length
decreasing_by
  all_goals simp_wf
  all_goals {
    simp [String.length_drop, String.length_mk]
    omega
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
lemma string_nonempty_of_pos_length (s : String) (h : 0 < s.length) : s ≠ "" := by
  intro h_empty
  rw [h_empty] at h
  simp at h

-- LLM HELPER
lemma list_takewhile_length_pos {α : Type*} (p : α → Bool) (l : List α) 
  (h : 0 < (l.takeWhile p).length) : l ≠ [] := by
  intro h_empty
  rw [h_empty] at h
  simp at h

theorem correctness
(text: String)
: problem_spec implementation text := by
  unfold problem_spec
  use implementation text
  constructor
  · rfl
  · constructor
    · intro h
      by_cases h_empty : text = ""
      · exact h_empty
      · simp [implementation, h_empty] at h
    · intro h
      by_cases h_empty : text = ""
      · exfalso
        simp [implementation, h_empty] at h
      · simp [implementation, h_empty]
        let n := text.toList.takeWhile (· = ' ') |>.length
        by_cases h_zero : n = 0
        · left
          cases h_chars : text.toList with
          | nil => 
            simp [String.toList] at h_chars
            rw [← String.length_pos] at h_empty
            rw [String.length, h_chars] at h_empty
            simp at h_empty
          | cons head tail =>
            use String.mk [head], String.mk tail
            constructor
            · rw [← String.toList_inj]
              rw [String.toList_append, String.toList_mk, String.toList_mk]
              simp [h_chars]
            constructor
            · simp [String.length_mk]
            constructor
            · simp at h_zero
              rw [h_chars] at h_zero
              simp [List.takeWhile] at h_zero
              by_cases h_head_space : head = ' '
              · simp [h_head_space] at h_zero
              · exact h_head_space
            · rfl
        · right
          have h_pos : 0 < n := Nat.pos_of_ne_zero h_zero
          have h_nonempty : text.toList ≠ [] := list_takewhile_length_pos (· = ' ') text.toList h_pos
          let pref := String.mk (text.toList.takeWhile (· = ' '))
          let suff := String.mk (text.toList.dropWhile (· = ' '))
          use pref, suff
          constructor
          · rw [← String.toList_inj]
            rw [String.toList_append, String.toList_mk, String.toList_mk]
            exact List.takeWhile_append_dropWhile (· = ' ') text.toList
          constructor
          · simp [pref, String.length_mk]
            exact h_pos
          constructor
          · intro ch h_mem
            simp [pref, String.toList_mk] at h_mem
            exact List.mem_takeWhile.mp h_mem
          constructor
          · intro h_small
            simp [pref, String.length_mk] at h_small
            rw [String.drop_mk]
            simp [List.drop_takeWhile_dropWhile]
            rfl
          · intro h_large
            simp [pref, String.length_mk] at h_large
            rw [String.drop_mk] 
            simp [List.drop_takeWhile_dropWhile]
            rfl

-- #test implementation "Example" = "Example"
-- #test implementation "Example 1" = "Example_1"
-- #test implementation " Example 2" = "_Example_2"
-- #test implementation " Example   3" = "_Example-3"