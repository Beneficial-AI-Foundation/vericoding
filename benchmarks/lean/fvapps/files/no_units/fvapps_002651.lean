-- <vc-preamble>
def String.replicate (n : Nat) (s : String) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def spam (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spam_multiplication (n : Nat) : n ≤ 1000 → spam n = String.replicate n "hue" :=
  sorry
-- </vc-theorems>