-- <vc-helpers>
-- </vc-helpers>

def solve (xs : List String) : List Nat :=
  sorry

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

-- Apps difficulty: introductory
-- Assurance level: guarded