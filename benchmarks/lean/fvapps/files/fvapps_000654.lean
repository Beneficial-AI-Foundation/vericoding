-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_santa_gifts (n m a d : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem range_validity (n m a d : Nat) (h₁ : n > 0) (h₂ : m > 0) (h₃ : a > 0) (h₄ : d > 0) 
  (h₅ : n ≤ m) :
  let result := count_santa_gifts n m a d
  result ≥ 0 ∧ result ≤ m - n + 1 :=
sorry

theorem monotonicity (n m a d : Nat) (h₁ : n > 0) (h₂ : m > 0) (h₃ : a > 0) (h₄ : d > 0)
  (h₅ : n ≤ m) :
  count_santa_gifts n m a d ≤ count_santa_gifts n (m+1) a d :=
sorry

theorem single_number (n a d : Nat) (h₁ : n > 0) (h₂ : a > 0) (h₃ : d > 0) :
  let result := count_santa_gifts n n a d
  result = 0 ∨ result = 1 :=
sorry
-- </vc-theorems>