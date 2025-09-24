-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_max_score (n k : Nat) (games : String) : Nat := sorry

theorem non_negative_result {n k : Nat} {games : String} :
  n > 0 → calculate_max_score n k games ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem score_monotonic_with_k {n k : Nat} {games : String} :
  n > 0 → k > 0 → calculate_max_score n k games ≥ calculate_max_score n (k-1) games := sorry

theorem all_losses {n k : Nat} :
  n > 0 → 
  let games := String.mk (List.replicate n 'L') 
  calculate_max_score n k games = max (if k > 0 then min n k * 2 - 1 else 0) 0 := sorry

theorem all_wins {n k : Nat} :
  n > 0 → 
  let games := String.mk (List.replicate n 'W')
  calculate_max_score n k games = 2 * n - 1 := sorry
-- </vc-theorems>