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

def implementation (text: String) : String :=
  if text = "" then ""
  else if text.length = 1 then 
    if text = " " then "_"
    else text
  else
    let first_char := text.get! 0
    if first_char ≠ ' ' then
      String.mk [first_char] ++ implementation (text.drop 1)
    else
      -- Count leading spaces
      let rec countSpaces (s : String) (pos : Nat) : Nat :=
        if pos >= s.length then pos
        else if s.get! pos = ' ' then countSpaces s (pos + 1)
        else pos
      let k := countSpaces text 0
      if k ≤ 2 then
        String.replicate k '_' ++ implementation (text.drop k)
      else
        "-" ++ implementation (text.drop k)

-- LLM HELPER
lemma implementation_empty : implementation "" = "" := by
  simp [implementation]

-- LLM HELPER
lemma implementation_single_space : implementation " " = "_" := by
  simp [implementation]

-- LLM HELPER
lemma implementation_single_non_space (c : Char) (h : c ≠ ' ') : 
  implementation (String.mk [c]) = String.mk [c] := by
  simp [implementation]
  split_ifs with h1 h2
  · contradiction
  · rfl
  · simp at h2
    exact h2 h

-- LLM HELPER
lemma string_get_first (s : String) (h : s ≠ "") : 
  s = String.mk [s.get! 0] ++ s.drop 1 := by
  cases' s with data
  simp [String.get!, String.drop]
  cases data with
  | nil => simp at h
  | cons head tail => simp [String.mk]

-- LLM HELPER
lemma countSpaces_spec (s : String) (pos : Nat) : 
  let rec countSpaces (s : String) (pos : Nat) : Nat :=
    if pos >= s.length then pos
    else if s.get! pos = ' ' then countSpaces s (pos + 1)
    else pos
  let k := countSpaces s pos
  (∀ i, pos ≤ i → i < k → s.get! i = ' ') ∧ 
  (k < s.length → s.get! k ≠ ' ') := by
  sorry

theorem correctness
(text: String)
: problem_spec implementation text := by
  simp [problem_spec]
  use implementation text
  constructor
  · rfl
  · simp only [implementation]
    split_ifs with h1 h2 h3
    · simp [h1]
    · simp [h1, h2]
      by_cases h : text = " "
      · simp [h, implementation_single_space]
      · right
        use " ", ""
        simp [h]
        use 1
        simp
    · simp [h1]
      right
      left
      let first_char := text.get! 0
      use String.mk [first_char], text.drop 1
      simp
      constructor
      · exact string_get_first text h1
      · simp [h3]
    · simp [h1]
      right
      right
      let rec countSpaces (s : String) (pos : Nat) : Nat :=
        if pos >= s.length then pos
        else if s.get! pos = ' ' then countSpaces s (pos + 1)
        else pos
      let k := countSpaces text 0
      let leading_spaces := text.take k
      use leading_spaces, text.drop k
      simp
      constructor
      · simp [String.take_append_drop]
      · constructor
        · simp [String.take_eq_empty_iff]
          simp [h3]
        · constructor
          · intro ch h_mem
            simp [String.take] at h_mem
            exact ch.eq_of_mem_take_spaces h_mem
          · simp [leading_spaces]