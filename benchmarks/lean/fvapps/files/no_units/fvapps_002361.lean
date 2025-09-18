-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def add_digits (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem add_digits_range (n : Nat) (h : n ≤ 10^6) :
  0 ≤ add_digits n ∧ add_digits n ≤ 9 :=
  sorry

partial def digit_sum (x : Nat) : Nat :=
  if x = 0 then 0
  else 
    let sum := digit_sum (x / 10) + x % 10
    if sum > 9 then digit_sum sum else sum

theorem add_digits_zero : 
  add_digits 0 = 0 :=
  sorry

theorem add_digits_nonzero (n : Nat) (h₁ : n ≤ 10^6) (h₂ : n > 0) :
  add_digits n > 0 :=
  sorry
-- </vc-theorems>