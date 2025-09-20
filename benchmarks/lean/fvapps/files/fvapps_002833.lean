-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_age : String → Except String Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_age_single_digit_extracts_first {n : Nat} (h : n < 10) :
  get_age s!"${n} years old" = .ok n :=
  sorry

theorem get_age_non_digit_first (s : String) (h: !s.front.isDigit) :
  ∃ e, get_age s = .error e :=
  sorry
-- </vc-theorems>