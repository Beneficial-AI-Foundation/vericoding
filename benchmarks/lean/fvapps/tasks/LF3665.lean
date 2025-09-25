-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def how_many_apples (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem apples_always_positive {n: Nat} (h: n ≥ 2) :
  how_many_apples n > 0 :=
  sorry 

theorem apples_increases (n: Nat) (h: n ≥ 2) :  
  how_many_apples n > how_many_apples (n-1) :=
  sorry

theorem minimum_case :
  how_many_apples 2 = 7 :=
  sorry
-- </vc-theorems>