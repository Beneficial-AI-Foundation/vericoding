-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rule30 (initial : List Nat) (n : Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rule30_binary (initial : List Nat) (n : Nat) :
  ∀ x ∈ rule30 initial n, x = 0 ∨ x = 1 :=
  sorry

theorem rule30_zero_step (initial : List Nat) :
  rule30 initial 0 = initial :=
  sorry

theorem rule30_growth (initial : List Nat) (n : Nat) :
  n > 0 → List.length (rule30 initial n) = List.length initial + 2*n :=
  sorry
-- </vc-theorems>