-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_alternating_substrings (n : Nat) (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_non_negative {n : Nat} {s : String} :
  find_alternating_substrings n s ≥ 0 :=
  sorry

theorem result_bounded {n : Nat} {s : String} :
  find_alternating_substrings n s ≤ s.length * (s.length - 1) / 2 :=
  sorry

theorem empty_or_single_char {n : Nat} {s : String} :
  s.length ≤ 1 → find_alternating_substrings n s = 0 :=
  sorry

theorem zero_edge_case {n : Nat} :
  find_alternating_substrings n "0" = 0 :=
  sorry

theorem one_edge_case {n : Nat} :
  find_alternating_substrings n "1" = 0 :=
  sorry
-- </vc-theorems>