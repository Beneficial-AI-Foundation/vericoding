-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_pretty_substrings (s: String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_non_negative (s: String) : 
  count_pretty_substrings s ≥ 0 :=
  sorry

theorem count_bounded_by_length (s: String) :
  let n := s.length
  count_pretty_substrings s ≤ n * (n + 1) / 2 :=
  sorry 

theorem balanced_parens_pretty (n: Nat) :
  n > 0 → 
  let s := String.mk (List.replicate n '(' ++ List.replicate n ')')
  count_pretty_substrings s ≥ 1 := 
  sorry
-- </vc-theorems>