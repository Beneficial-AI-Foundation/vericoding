-- <vc-preamble>
def countOnes (s : String) : Nat :=
  s.data.filter (· = '1') |>.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_virus_spread (N : Nat) (init_pop : String) (D : Nat) (isolations : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_virus_spread_type (N : Nat) (init_pop : String) (D : Nat) (isolations : List Nat) :
  Nat.le 0 (solve_virus_spread N init_pop D isolations) ∧
  Nat.le (solve_virus_spread N init_pop D isolations) N :=
sorry

theorem solve_virus_spread_no_infected (N : Nat) (init_pop : String) (D : Nat) (isolations : List Nat) :
  (∀ c, c ∈ init_pop.data → c ≠ '1') →
  solve_virus_spread N init_pop D isolations = 0 :=
sorry

theorem solve_virus_spread_no_isolation (N : Nat) (init_pop : String) (D : Nat) (isolations : List Nat) :
  D = 0 →
  solve_virus_spread N init_pop D isolations = countOnes init_pop :=
sorry

theorem solve_virus_spread_monotonic (N : Nat) (init_pop : String) (D : Nat) (isolations : List Nat) :
  Nat.le (countOnes init_pop) (solve_virus_spread N init_pop D isolations) :=
sorry
-- </vc-theorems>