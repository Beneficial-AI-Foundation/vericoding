-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_count_bases_starting_with_1 (n: Int) : String := sorry

theorem non_negative_count (n: Int) (h: n ≥ 2) (h': n ≤ 1000) : 
  match find_count_bases_starting_with_1 n with
  | "INFINITY" => True 
  | count => count.all (·.isDigit) ∧ count.toNat! ≥ 0
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem special_cases_zero :
  find_count_bases_starting_with_1 0 = "0" := sorry

theorem special_cases_one :
  find_count_bases_starting_with_1 1 = "INFINITY" := sorry

theorem count_less_than_input (n: Int) (h: n ≥ 2) (h': n ≤ 1000) :
  find_count_bases_starting_with_1 n ≠ "INFINITY" ∧ 
  (find_count_bases_starting_with_1 n).toNat! ≤ n := sorry

theorem result_is_valid_string (n: Int) (h: n ≥ 2) (h': n ≤ 1000) :
  (find_count_bases_starting_with_1 n).all (·.isDigit) := sorry

theorem base_2_property (n: Int) (h: n ≥ 2) (h': n ≤ 100) :
  (find_count_bases_starting_with_1 n).toNat! ≥ 1 := sorry
-- </vc-theorems>