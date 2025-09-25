-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def five_by_2n (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem five_by_2n_positive (n : Nat) : 
  n > 0 → five_by_2n n > 0 :=
  sorry

theorem five_by_2n_bounded (n : Nat) :
  n > 0 → five_by_2n n < 12345787 :=
  sorry 

theorem five_by_2n_deterministic (n : Nat) :
  five_by_2n n = five_by_2n n :=
  sorry

theorem five_by_2n_sequential (n : Nat) :
  n > 0 → True :=
  sorry
-- </vc-theorems>