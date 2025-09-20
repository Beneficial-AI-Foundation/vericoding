-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smallest (n: Nat) : Nat := sorry

theorem divides_up_to_n (n: Nat) (h: n > 0) :
  ∀ i, i > 0 → i ≤ n → (smallest n) % i = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>