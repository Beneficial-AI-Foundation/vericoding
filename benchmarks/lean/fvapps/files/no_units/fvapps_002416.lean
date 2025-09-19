-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxScore (s: String) : Nat := sorry

theorem maxScore_non_negative (s: String) (h: s.length >= 2) : 
  maxScore s >= 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxScore_upper_bound (s: String) (h: s.length >= 2) : 
  maxScore s ≤ s.length := sorry

theorem maxScore_bounded_by_chars (s: String) (h: s.length >= 2) :
  maxScore s ≤ (s.replace "1" "").length + (s.replace "0" "").length := sorry

theorem maxScore_all_ones (s: String) (h₁: s.length >= 2) 
  (h₂: ∀ c ∈ s.data, c = '1') :
  maxScore s = s.length - 1 := sorry

theorem maxScore_all_zeros (s: String) (h₁: s.length >= 2)
  (h₂: ∀ c ∈ s.data, c = '0') :
  maxScore s = s.length - 1 := sorry

theorem maxScore_first_char_lower_bound (s: String) (h: s.length >= 2) :
  let zeroes := if s.data[0]! = '0' then 1 else 0
  let ones := (s.data.drop 1).filter (· = '1') |>.length
  maxScore s ≥ zeroes + ones := sorry

theorem maxScore_alternating_pattern (n: Nat) (h: n ≥ 1) :
  let s := String.join (List.replicate n "01")
  maxScore s ≥ n := sorry

theorem maxScore_min_length_strings (s: String) (h₁: s.length = 2)
  (h₂: ∀ c ∈ s.data, c = '0' ∨ c = '1') :
  0 ≤ maxScore s ∧ maxScore s ≤ 2 := sorry
-- </vc-theorems>