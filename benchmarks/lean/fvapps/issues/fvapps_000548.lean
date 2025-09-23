-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sum (l : List Nat) : Nat := l.foldl (·+·) 0

def solveIslandRewards (N : Nat) (coins : List Nat) (queries : List (Nat × Nat)) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem island_rewards_result_length 
  (N : Nat) (coins : List Nat) (queries : List (Nat × Nat))  
  (h1 : N > 0) (h2 : coins.length = N)
  (h3 : ∀ q ∈ queries, q.1 ≤ N ∧ q.2 ≤ N) :
  (solveIslandRewards N coins queries).length = queries.length := sorry

theorem island_rewards_sum_correct
  (N : Nat) (coins : List Nat) (queries : List (Nat × Nat))
  (h1 : N > 0) (h2 : coins.length = N)
  (h3 : ∀ q ∈ queries, q.1 ≤ N ∧ q.2 ≤ N)
  (h4 : ∀ c ∈ coins, c ≥ 0)
  (i : Nat) (hi : i < queries.length) :
  let q := queries.get ⟨i, hi⟩
  let result := (solveIslandRewards N coins queries).get ⟨i, by rw [island_rewards_result_length N coins queries h1 h2 h3]; exact hi⟩
  result = List.sum ((coins.take q.2).drop (q.1 - 1)) := sorry

theorem island_rewards_non_negative
  (N : Nat) (coins : List Nat) (queries : List (Nat × Nat))
  (h1 : N > 0) (h2 : coins.length = N)
  (h3 : ∀ q ∈ queries, q.1 ≤ N ∧ q.2 ≤ N)
  (h4 : ∀ c ∈ coins, c ≥ 0) :
  ∀ r ∈ solveIslandRewards N coins queries, r ≥ 0 := sorry

theorem island_rewards_empty_range
  (N : Nat) (coins : List Nat) (queries : List (Nat × Nat))
  (h1 : N > 0) (h2 : coins.length = N)
  (h3 : ∀ q ∈ queries, q.1 ≤ N ∧ q.2 ≤ N)
  (i : Nat) (hi : i < queries.length) :
  let q := queries.get ⟨i, hi⟩
  q.1 > q.2 → (solveIslandRewards N coins queries).get ⟨i, by rw [island_rewards_result_length N coins queries h1 h2 h3]; exact hi⟩ = 0 := sorry

theorem island_rewards_deterministic
  (N : Nat) (coins : List Nat) (queries : List (Nat × Nat))
  (h1 : N > 0) (h2 : coins.length = N)
  (h3 : ∀ q ∈ queries, q.1 ≤ N ∧ q.2 ≤ N) :
  solveIslandRewards N coins queries = solveIslandRewards N coins queries := sorry
-- </vc-theorems>