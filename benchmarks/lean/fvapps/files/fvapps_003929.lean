-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (xs : List String) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_empty : solve [] = [] :=
  sorry

theorem solve_single : solve ["abc"] = [] :=
  sorry

theorem solve_pairs : solve ["abc", "cba"] = [1] :=
  sorry

theorem solve_basic : solve ["abc", "abbc", "ab", "xyz", "xy", "zzyx"] = [1, 8] :=
  sorry

theorem solve_no_matches : solve ["a", "b", "c"] = [] :=
  sorry

theorem solve_multiple_matches :
  solve ["wkskkkkkk", "fokoo", "wkskk", "uizzzz", "fokooff", "wkskkkk", "uizzzzzzz"] = [5, 7, 9] :=
  sorry
-- </vc-theorems>