-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def slogans (pattern : String) (text : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem slogans_basic_static_cases :
  (slogans "abc" "abc" ≥ 1) ∧
  (slogans "abc" "" = 0) ∧
  (slogans "test" "testtest" ≥ 2) :=
sorry

theorem slogans_nonnegative (pattern text : String) :
  slogans pattern text ≥ 0 :=
sorry

theorem slogans_bounded_by_text_length (pattern text : String) :
  slogans pattern text ≤ text.length :=
sorry

theorem slogans_repeated_pattern (pattern : String) (n : Nat) :
  n > 0 → slogans pattern (String.join (List.replicate n pattern)) ≥ n :=
sorry

theorem slogans_empty_repeat (pattern : String) :
  slogans pattern (String.join (List.replicate 0 pattern)) ≥ 0 :=
sorry
-- </vc-theorems>