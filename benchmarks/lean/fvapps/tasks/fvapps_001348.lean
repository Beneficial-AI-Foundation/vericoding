-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_matrix_power (n : Nat) (k : Nat) (a : List Int) (l r : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identity_power {n : Nat} {a : List Int} {l r : List Int} (h1 : n > 0)
  (h2 : n ≤ a.length) (h3 : l.length = n) (h4 : r.length = n)
  (h5 : ∀ i, i < n → l.get! i = i) (h6 : ∀ i, i < n → r.get! i = i + 1) :
  solve_matrix_power n 1 a l r = a := sorry

theorem powers_composition (n k1 k2 : Nat) (a l r : List Int) 
  (h1 : n = 3) (h2 : a = [1,2,3]) (h3 : l = [0,0,0]) (h4 : r = [3,3,3]) :
  solve_matrix_power n (k1 + k2) a l r = 
    solve_matrix_power n k2 (solve_matrix_power n k1 a l r) l r := sorry

theorem diagonal_idempotence (n k : Nat) (a l r : List Int)
  (h1 : n > 0) (h2 : k > 0)
  (h3 : l.length = n) (h4 : r.length = n)
  (h5 : ∀ i, i < n → l.get! i = i) (h6 : ∀ i, i < n → r.get! i = i + 1) :
  solve_matrix_power n k a l r = solve_matrix_power n 1 a l r := sorry
-- </vc-theorems>