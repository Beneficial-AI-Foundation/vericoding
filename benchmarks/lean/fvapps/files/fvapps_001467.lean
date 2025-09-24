-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_w_string (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_type_and_range 
  (s : String)
  (h : ∀ c ∈ s.toList, (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ c = '#') :
  solve_w_string s ≥ 0 :=
sorry

theorem insufficient_hashes_returns_zero
  (s : String) 
  (h : ∀ c ∈ s.toList, (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ c = '#')
  (h_count : (s.toList.filter (· = '#')).length < 3) :
  solve_w_string s = 0 :=
sorry

theorem consecutive_hashes_property
  (s : String)
  (h : ∀ c ∈ s.toList, (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ c = '#')
  (h_count : (s.toList.filter (· = '#')).length ≥ 2) :
  solve_w_string (s ++ "##") = solve_w_string (s ++ "#") :=
sorry

theorem binary_alphabet_with_hashes
  (s : String)
  (h : ∀ c ∈ s.toList, c = 'a' ∨ c = 'b') :
  solve_w_string (s ++ "###") ≤ (s ++ "###").length :=
sorry
-- </vc-theorems>