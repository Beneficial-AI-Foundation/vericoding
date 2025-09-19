-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def justifyText (words : List String) (maxWidth : Nat) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem justify_text_width_correct
  (words : List String)
  (maxWidth : Nat)
  (h1 : maxWidth ≥ 5)
  (h2 : maxWidth ≤ 100)
  (result : List String := justifyText words maxWidth)
  : ∀ line ∈ result, String.length line = maxWidth :=
sorry

theorem justify_text_min_lines
  (words : List String)
  (maxWidth : Nat)
  (h1 : maxWidth ≥ 5) 
  (h2 : maxWidth ≤ 100)
  (h3 : words ≠ [])
  (totalChars : Nat := (words.filter (fun w => String.length w ≤ maxWidth)).foldr (fun s acc => String.length s + acc) 0)
  (h4 : totalChars > 0)
  (result : List String := justifyText words maxWidth)
  : result.length ≥ totalChars / maxWidth :=
sorry

theorem justify_text_empty_input
  (maxWidth : Nat)
  (h1 : maxWidth ≥ 5)
  (h2 : maxWidth ≤ 100)
  : justifyText [] maxWidth = [] :=
sorry
-- </vc-theorems>