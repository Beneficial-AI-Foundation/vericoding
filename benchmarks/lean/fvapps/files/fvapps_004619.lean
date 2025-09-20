-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def recaman (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem recaman_nonnegative (n : Nat) :
  recaman n ≥ 0 :=
  sorry

theorem recaman_consecutive_diff (n : Nat) :
  n > 0 → (if recaman n ≥ recaman (n-1) 
           then recaman n - recaman (n-1)
           else recaman (n-1) - recaman n) = n :=
  sorry

theorem recaman_zero :
  recaman 0 = 0 :=
  sorry

theorem recaman_one :
  recaman 1 = 1 :=
  sorry
-- </vc-theorems>