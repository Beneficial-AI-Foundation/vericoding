-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_pipernet (n a b x y z : Nat) (contributions : List Nat) : Nat ⊕ String := sorry 

theorem solve_pipernet_valid_output
  (n a b x y z : Nat) (contributions : List Nat) 
  (h1 : 0 < n ∧ n ≤ 100)
  (h2 : a ≤ 1000000)
  (h3 : b ≤ 1000000) 
  (h4 : x ≤ 1000)
  (h5 : 0 < y ∧ y ≤ 1000)
  (h6 : 0 < z ∧ z ≤ 1000000)
  (h7 : z > b)
  (h8 : ∀ c ∈ contributions, c ≤ 1000000)
  (h9 : contributions.length ≤ n) :
  match solve_pipernet n a b x y z contributions with
  | Sum.inr "RIP" => 
    let max_contrib := contributions.foldr (· + ·) 0
    let max_users := a + ((z - b - 1) / y) * x + max_contrib
    max_users < z
  | Sum.inl val => 0 ≤ val
  | _ => False
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_pipernet_zero_contributions
  (n : Nat)
  (h1 : 0 < n ∧ n ≤ 100) :
  solve_pipernet n 10 15 5 10 100 (List.replicate n 0) = Sum.inr "RIP" := sorry
-- </vc-theorems>