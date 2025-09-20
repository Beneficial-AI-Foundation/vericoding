-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nth_floyd (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nth_floyd_is_positive (n : Nat) (h : n > 0) : nth_floyd n > 0 := 
  sorry

theorem nth_floyd_in_line_bounds (n : Nat) (h : n > 0) : 
  let result := nth_floyd n
  let line_start := 1 + (result-1)*result/2
  let line_end := line_start + result - 1
  line_start ≤ n ∧ n ≤ line_end :=
  sorry

theorem nth_floyd_same_line (line_num : Nat) (h : line_num > 0) (i : Nat) 
  (hi : i < line_num) :
  let start := 1 + (line_num-1)*line_num/2
  nth_floyd (start + i) = line_num :=
  sorry

theorem nth_floyd_small_cases : 
  nth_floyd 1 = 1 ∧ 
  nth_floyd 2 = 2 ∧
  nth_floyd 3 = 2 ∧ 
  nth_floyd 4 = 3 :=
  sorry
-- </vc-theorems>