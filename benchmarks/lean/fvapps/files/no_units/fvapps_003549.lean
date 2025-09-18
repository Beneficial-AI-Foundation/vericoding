-- <vc-preamble>
def sim (k n : Nat) (p : Float) : Float :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compute (k n m x : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sim_monotonic (k n : Nat) 
  (h1 : k ≥ 1) (h2 : n ≥ 2) : 
  sim k n 0 ≤ sim k n 1 :=
sorry 

theorem compute_result_valid (k n x m : Nat)
  (h1 : k ≥ 1) (h2 : n ≥ 2) (h3 : x ≥ 1)
  (h4 : m ≥ 0)
-- </vc-theorems>