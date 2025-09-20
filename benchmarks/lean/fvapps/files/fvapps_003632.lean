-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cycle (n : Nat) : Int := sorry

theorem cycle_invalid_input (n : Nat)
  (h : n % 2 = 0 ∨ n % 5 = 0) : cycle n = -1 := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>