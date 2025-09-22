-- <vc-preamble>
def abs (n : Int) : Int :=
  if n ≥ 0 then n else -n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_max_diagonal_moves (n m k : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_bound (n m k : Int) (h: -1000 <= n ∧ n <= 1000) (h2: -1000 <= m ∧ m <= 1000) (h3: 0 <= k ∧ k <= 2000) :
  let r := solve_max_diagonal_moves n m k
  r = -1 ∨ r ≤ k :=
sorry

theorem result_parity (n m k : Int) (h: -1000 <= n ∧ n <= 1000) (h2: -1000 <= m ∧ m <= 1000) (h3: 0 <= k ∧ k <= 2000) :
  let r := solve_max_diagonal_moves n m k
  let max_dist := max (abs n) (abs m)
  r ≠ -1 → (r % 2 = max_dist % 2 ∨ r % 2 = (max_dist - 1) % 2) :=
sorry

theorem insufficient_moves (n : Int) (h: 1 <= n ∧ n <= 1000) :
  let k := abs n - 1
  solve_max_diagonal_moves n n k = -1 :=
sorry

theorem symmetry (n m : Int) (h: -1000 <= n ∧ n <= 1000) (h2: -1000 <= m ∧ m <= 1000) :
  let k := max (abs n) (abs m) * 2
  let r1 := solve_max_diagonal_moves n m k
  let r2 := solve_max_diagonal_moves (-n) m k
  let r3 := solve_max_diagonal_moves n (-m) k
  let r4 := solve_max_diagonal_moves (-n) (-m) k
  r1 = r2 ∧ r2 = r3 ∧ r3 = r4 :=
sorry
-- </vc-theorems>