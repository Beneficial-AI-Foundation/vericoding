-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumMul (n m : Int) : Int ⊕ String := sorry

theorem sumMul_valid_output (n m : Int)
  (h1 : n > 0)
  (h2 : m > 0)
  (h3 : m > n) :
  match sumMul n m with
  | Sum.inl result => result ≥ 0
  | Sum.inr _ => False
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sumMul_all_divisible (n m : Int)
  (h1 : n > 0)
  (h2 : m > 0)
  (h3 : m > n)
  (k : Int)
  (hk : n ≤ k ∧ k < m ∧ k % n = 0) :
  match sumMul n m with
  | Sum.inl _ => k % n = 0
  | Sum.inr _ => False
  := sorry

theorem sumMul_invalid_n (n m : Int)
  (h : n ≤ 0) :
  sumMul n m = Sum.inr "INVALID"
  := sorry

theorem sumMul_invalid_m (n m : Int)
  (h : m ≤ 0) :
  sumMul n m = Sum.inr "INVALID"
  := sorry
-- </vc-theorems>