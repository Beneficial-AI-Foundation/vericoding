-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Nat) (stones : List Nat) : List Nat := sorry

theorem solve_length {N : Nat} {stones : List Nat} :
  stones.length = N → (solve N stones).length = N := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_nonnegative {N : Nat} {stones : List Nat} :
  stones.length = N → ∀ x ∈ solve N stones, x ≥ 0 := sorry

theorem solve_repeated_stones {N : Nat} {stones : List Nat} :
  stones.length = N →
  ∀ i j : Nat,
    i < j → 
    j < stones.length →
    stones[i]! = stones[j]! →
    (solve N stones)[j]! = 0 := sorry
-- </vc-theorems>