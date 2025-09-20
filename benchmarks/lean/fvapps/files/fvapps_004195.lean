-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isMultiple (a b n : Nat) : Bool := sorry

theorem isMultiple_deterministic {a b n : Nat} (h1 : 0 < a) (h2 : a ≤ 1000) 
    (h3 : 0 < b) (h4 : b ≤ 1000) (h5 : 0 < n) (h6 : n ≤ 9) :
  isMultiple a b n = isMultiple a b n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isMultiple_exact_division {a b n : Nat} (h1 : 0 < a) (h2 : a ≤ 1000)
    (h3 : 0 < b) (h4 : b ≤ 1000) (h5 : 0 < n) (h6 : n ≤ 9)
    (h7 : a % b = 0) :
  isMultiple a b n = false := sorry

theorem isMultiple_remainder_bounded {a b : Nat} (h1 : 0 < a) (h2 : a ≤ 1000)
    (h3 : 0 < b) (h4 : b ≤ 1000) :
  let remainder := ((a / b) * 10) % 10
  0 ≤ remainder ∧ remainder ≤ 9 := sorry

theorem isMultiple_div_by_one {a n : Nat} (h1 : 0 < a) (h2 : a ≤ 1000)
    (h3 : 0 < n) (h4 : n ≤ 9) :
  isMultiple a 1 n = false := sorry

theorem isMultiple_zero {b n : Nat} (h1 : 0 < b) (h2 : b ≤ 1000) 
    (h3 : 0 < n) (h4 : n ≤ 9) :
  isMultiple 0 b n = false := sorry
-- </vc-theorems>