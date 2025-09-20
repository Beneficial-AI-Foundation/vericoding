-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stringEndsWith (s ending : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem stringEndsWith_matches_endsWith (s ending : String) :
  stringEndsWith s ending = String.endsWith s ending := by
  sorry

theorem empty_ending_always_true (s : String) :
  stringEndsWith s "" = true := by
  sorry

theorem string_ends_with_itself (s : String) :
  stringEndsWith s s = true := by
  sorry

theorem longer_ending_is_false {s ending : String} :
  ending.length > s.length → stringEndsWith s ending = false := by
  sorry

theorem ends_with_last_n_chars (s : String) (n : Nat) :
  n ≤ s.length →
  stringEndsWith s (s.drop (s.length - n)) = true := by
  sorry
-- </vc-theorems>