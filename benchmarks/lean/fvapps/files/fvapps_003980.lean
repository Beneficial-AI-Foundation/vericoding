-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def squares (x n : Int) : List Int := sorry

theorem squares_length_nonpositive {x n : Int} (h : n ≤ 0) :
  squares x n = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem squares_length_positive {x n : Int} (h : n > 0) :
  (squares x n).length = n := sorry

theorem squares_powers {x n : Nat} (h1 : 1 ≤ x) (h2 : x ≤ 5) (h3 : 1 ≤ n) (h4 : n ≤ 5) :
  ∀ i : Nat, i < n → (squares x n).get ⟨i, sorry⟩ = x ^ (2 : Nat) ^ i := sorry

theorem squares_basic_values :
  squares 2 1 = [2] ∧
  squares 1 5 = [1, 1, 1, 1, 1] ∧ 
  squares (-2) 2 = [-2, 4] := sorry
-- </vc-theorems>