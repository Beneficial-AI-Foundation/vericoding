-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_ands (s : String) : Nat := sorry

theorem count_ands_nonnegative {words : List String} : 
  count_ands (String.join (List.intersperse " " words)) ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_ands_upper_bound {words : List String} :
  count_ands (String.join (List.intersperse " " words)) ≤ words.length := sorry

theorem count_ands_repetition {n : Nat} :
  count_ands (String.join (List.replicate n " and ")) = n := sorry

theorem count_ands_case_insensitive (s : String) :
  count_ands (s.toLower) = count_ands (s.toUpper) := sorry

theorem count_ands_empty :
  count_ands "" = 0 := sorry
-- </vc-theorems>