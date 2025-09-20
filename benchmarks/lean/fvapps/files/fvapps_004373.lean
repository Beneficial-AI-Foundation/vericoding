-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def powers_of_two (n : Nat) : List Nat := sorry

theorem powers_of_two_length (n : Nat) :
  (powers_of_two n).length = n + 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem powers_of_two_first_one (n : Nat) :
  (powers_of_two n).head! = 1 := sorry
-- </vc-theorems>