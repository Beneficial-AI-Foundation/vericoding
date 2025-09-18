-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (wealths : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_basic_properties {n : Nat} {wealths : List Nat} 
  (h : wealths.length > 0) (h2 : wealths.length ≤ 100) :
  let ranks := solve n wealths
  -- Length of output matches input
  ranks.length = wealths.length ∧ 
  -- All ranks are positive
  (∀ r ∈ ranks, r > 0) ∧
  -- Rank never exceeds position+1
  (∀ (i : Nat), i < ranks.length → ranks[i]! ≤ i + 1) :=
  sorry

theorem solve_first_rank {n : Nat} {wealths : List Nat}
  (h : wealths.length > 0) :
  (solve n wealths)[0]! = 1 :=
  sorry

theorem solve_relative_ranks {n : Nat} {wealths : List Nat}
  (h : wealths.length ≥ 2) :
  let ranks := solve n wealths
  ∀ (i : Nat), i > 0 → i < wealths.length →
    wealths[i]! > wealths[i-1]! → ranks[i]! ≤ ranks[i-1]! + 1 :=
  sorry
-- </vc-theorems>