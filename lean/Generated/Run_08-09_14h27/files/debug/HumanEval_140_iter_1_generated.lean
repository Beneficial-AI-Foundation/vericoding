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
  match text.toList with
  | [] => 0
  | c :: cs => if c = ' ' then 1 + count_leading_spaces (String.mk cs) else 0

def implementation (text: String) : String :=
  if text = "" then ""
  else
    let leading_spaces := count_leading_spaces text
    if leading_spaces = 0 then
      match text.toList with
      | [] => ""
      | c :: cs => String.mk [c] ++ implementation (String.mk cs)
    else if leading_spaces ≤ 2 then
      String.replicate leading_spaces '_' ++ implementation (text.drop leading_spaces)
    else
      "-" ++ implementation (text.drop leading_spaces)

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
  sorry

theorem correctness
(text: String)
: problem_spec implementation text := by
  unfold problem_spec
  use implementation text
  constructor
  · rfl
  · unfold implementation
    simp only [and_imp]
    constructor
    · intro h
      by_cases h_empty : text = ""
      · simp [h_empty]
      · simp [h_empty] at h
    · intro h
      by_cases h_empty : text = ""
      · simp [h_empty] at h
      · simp [h_empty]
        let n := count_leading_spaces text
        by_cases h_zero : n = 0
        · simp [h_zero]
          left
          sorry -- Need to show the case where first character is not a space
        · by_cases h_small : n ≤ 2
          · simp [h_zero, h_small]
            right
            sorry -- Need to show the case with ≤2 spaces
          · simp [h_zero, h_small]
            right
            sorry -- Need to show the case with >2 spaces

-- #test implementation "Example" = "Example"
-- #test implementation "Example 1" = "Example_1"
-- #test implementation " Example 2" = "_Example_2"
-- #test implementation " Example   3" = "_Example-3"