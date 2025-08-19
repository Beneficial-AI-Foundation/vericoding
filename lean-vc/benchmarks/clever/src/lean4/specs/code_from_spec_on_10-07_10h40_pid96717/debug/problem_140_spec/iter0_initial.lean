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
    let first_char := text.get ⟨0, by simp [String.length_pos]⟩
    if first_char ≠ ' ' then
      String.mk [first_char] ++ implementation (text.drop 1)
    else
      -- Count leading spaces
      let leading_spaces := text.takeWhile (· = ' ')
      let k := leading_spaces.length
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
lemma takeWhile_spaces_all_spaces (s : String) : 
  ∀ ch, ch ∈ (s.takeWhile (· = ' ')).toList → ch = ' ' := by
  intro ch h
  simp [String.takeWhile] at h
  exact String.takeWhile_mem h

-- LLM HELPER
lemma takeWhile_drop_eq (s : String) (p : Char → Bool) :
  (s.takeWhile p) ++ (s.drop (s.takeWhile p).length) = s := by
  simp [String.takeWhile_append_drop]

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
      let first_char := text.get ⟨0, by simp [String.length_pos, h1]⟩
      use String.mk [first_char], text.drop 1
      simp
      constructor
      · exact String.cons_head_tail (by simp [h1])
      · simp [h3]
    · simp [h1]
      right
      right
      let leading_spaces := text.takeWhile (· = ' ')
      let k := leading_spaces.length
      use leading_spaces, text.drop k
      simp
      constructor
      · exact String.takeWhile_append_drop text (· = ' ')
      · constructor
        · simp [String.takeWhile_nonempty_iff]
          simp [h3]
        · constructor
          · exact takeWhile_spaces_all_spaces text
          · simp [k]