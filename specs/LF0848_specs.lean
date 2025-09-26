-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_win (n a b k : Nat) : String := sorry

theorem check_win_returns_valid_result 
  (n a b k : Nat) 
  (h1 : 0 < n) (h2 : a ≤ n) (h3 : b ≤ n) (h4 : k ≤ n) (h5 : 0 < a) (h6 : 0 < b) :
  check_win n a b k = "Win" ∨ check_win n a b k = "Lose" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_win_is_deterministic 
  (n a b k : Nat) 
  (h1 : 0 < n) (h2 : a ≤ n) (h3 : b ≤ n) (h4 : k ≤ n) (h5 : 0 < a) (h6 : 0 < b) :
  check_win n a b k = check_win n a b k := sorry

theorem check_win_same_divisor 
  (n a : Nat) 
  (h1 : 0 < n) (h2 : 0 < a) (h3 : a ≤ n) :
  check_win n a a 1 = "Lose" := sorry

theorem check_win_symmetry 
  (n a b k : Nat)
  (h1 : 0 < n) (h2 : a ≤ n) (h3 : b ≤ n) (h4 : k ≤ n) (h5 : 0 < a) (h6 : 0 < b) :
  check_win n a b k = check_win n b a k := sorry

theorem check_win_k_zero 
  (n a b : Nat)
  (h1 : 0 < n) (h2 : a ≤ n) (h3 : b ≤ n) (h4 : 0 < a) (h5 : 0 < b) :
  check_win n a b 0 = "Win" := sorry

theorem check_win_k_too_large 
  (n a b : Nat)
  (h1 : 0 < n) (h2 : a ≤ n) (h3 : b ≤ n) (h4 : 0 < a) (h5 : 0 < b) :
  check_win n a b (n + 1) = "Lose" := sorry
-- </vc-theorems>