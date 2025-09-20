-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def palindrome (n : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem palindrome_outputs_int {x : Int} (h : x ≥ 0) :
  ∃ y : Int, palindrome x = y :=
  sorry

theorem palindrome_negative_rejects (x : Int) (h : x < 0) :
  palindrome x = -1 := -- assuming -1 represents 'Not valid'
  sorry

theorem palindrome_single_digit {x : Int} (h1 : x ≥ 0) (h2 : x ≤ 9) :
  palindrome x = 0 :=
  sorry

theorem palindrome_output_non_negative {x : Int} (h : x ≥ 0) :
  palindrome x ≥ 0 :=
  sorry

theorem palindrome_detects_basic {x : Int} (h : x = 1221) :
  palindrome x > 0 :=
  sorry
-- </vc-theorems>