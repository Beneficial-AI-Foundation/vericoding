-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_adjacent_pairs (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_adjacent_pairs_nonnegative (s : String) :
  count_adjacent_pairs s ≥ 0 :=
  sorry

theorem count_adjacent_pairs_max_bound (words : List String) :
  count_adjacent_pairs (String.join (List.intersperse " " words)) ≤ words.length / 2 :=
  sorry

theorem count_adjacent_pairs_empty_or_single (words : List String) :
  words.length ≤ 1 → count_adjacent_pairs (String.join (List.intersperse " " words)) = 0 :=
  sorry

theorem count_adjacent_pairs_case_insensitive (s : String) :
  count_adjacent_pairs s = count_adjacent_pairs (s.toUpper) ∧
  count_adjacent_pairs s = count_adjacent_pairs (s.toLower) :=
  sorry
-- </vc-theorems>