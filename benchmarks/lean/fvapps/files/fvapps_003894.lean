-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def self_converge (n : Nat) : Int := sorry

theorem self_converge_properties (n : Nat) 
  (h : n ≥ 1 ∧ n ≤ 999999) : 
  let result := self_converge n
  -- Result is non-negative or -1
  (result ≥ -1) ∧
  -- Result length is bounded
  (result ≠ -1 → result ≤ (Nat.toDigits 10 n).length * 20) ∧
  -- Function is deterministic 
  (self_converge n = result) ∧
  -- Leading zeros don't affect result
  (self_converge (n * 10) = result) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_same_digits_converge (n d : Nat)
  (h1 : d ≥ 0 ∧ d ≤ 9)
  (h2 : ∃ k, n = d * (10^k - 1)/(10-1) ∧ k = 4) :
  self_converge n = -1 := sorry

theorem single_digit_converge (n : Nat)
  (h : n ≥ 1 ∧ n ≤ 9) :
  self_converge n = -1 := sorry
-- </vc-theorems>