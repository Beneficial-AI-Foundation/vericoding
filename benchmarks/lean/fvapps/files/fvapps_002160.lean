-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def allocate_stadium_games (n m k : Nat) (games : List (Nat × Nat)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem stadium_balance {n k : Nat} {games : List (Nat × Nat)} {allocation : List Nat}
  (h1 : n ≥ 2)
  (h2 : k ≥ 1)
  (h3 : allocation = allocate_stadium_games n games.length k games)
  (h4 : ∀ g, g ∈ games → g.1 ≤ n ∧ g.2 ≤ n ∧ g.1 < g.2)
  (h5 : ∀ s, s ∈ allocation → s ≥ 1 ∧ s ≤ k) :
  ∀ t, t ≤ n →
    ∀ s1 s2, s1 ≤ k → s2 ≤ k →
      Nat.sub ((games.zip allocation).filter (λ p => (p.1.1 = t ∨ p.1.2 = t) ∧ p.2 = s1) |>.length)
              ((games.zip allocation).filter (λ p => (p.1.1 = t ∨ p.1.2 = t) ∧ p.2 = s2) |>.length) ≤ 2 :=
sorry

theorem allocation_length_eq_games {n k : Nat} {games : List (Nat × Nat)}
  (h1 : n ≥ 2)
  (h2 : k ≥ 1) :
  (allocate_stadium_games n games.length k games).length = games.length :=
sorry

theorem empty_games_empty_allocation {n k : Nat}
  (h1 : n ≥ 2)
  (h2 : k ≥ 1) :
  allocate_stadium_games n 0 k [] = [] :=
sorry

theorem minimum_viable_case :
  allocate_stadium_games 2 1 1 [(1, 2)] = [1] :=
sorry
-- </vc-theorems>