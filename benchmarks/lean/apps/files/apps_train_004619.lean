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

/-
info: 3
-/
-- #guard_msgs in
-- #eval recaman 2

/-
info: 6
-/
-- #guard_msgs in
-- #eval recaman 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval recaman 4
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible