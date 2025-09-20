-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_inscribed_circles (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_inscribed_circles_non_negative (s : String) :
  count_inscribed_circles s ≥ 0 :=
sorry

theorem no_leading_ones_implies_zero (s : String) :
  (∀ c ∈ s.data, c ≠ '1') ∨ (s.length > 0 ∧ s.data.get? 0 = some '0') →
  count_inscribed_circles s = 0 :=
sorry 

theorem result_bounded_by_zeros_after_first_one (s : String) 
  (h1 : s.length > 0) (h2 : ∃ i < s.length, s.data.get? i = some '1') :
  let first_one := (s.data.findIdx (· = '1'))
  let zeros_after := (s.data.drop first_one).filter (· = '0') |>.length
  count_inscribed_circles s ≤ zeros_after :=
sorry

theorem all_ones_gives_zero (s : String) :
  (∀ c ∈ s.data, c = '1') →
  count_inscribed_circles s = 0 :=
sorry

theorem ones_then_zeros_pattern (n : Nat) (h : n > 0) :
  count_inscribed_circles (String.mk ((List.replicate 1 '1') ++ (List.replicate n '0'))) = n :=
sorry

theorem many_ones_then_zeros_pattern (n : Nat) (h : n > 0) :
  count_inscribed_circles (String.mk ((List.replicate n '1') ++ (List.replicate n '0'))) = n :=
sorry
-- </vc-theorems>