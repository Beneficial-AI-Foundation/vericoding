-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factorial (n : Int) : Option Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem factorial_nonnegative {n : Int} (h : n ≥ 0) (h2 : n ≤ 10) : 
  match factorial n with
  | some x => x > 0
  | none => False :=
  sorry

theorem factorial_divides {n : Int} (h : n > 0) (h2 : n ≤ 10) :
  match factorial n with
  | some x => x % n = 0 ∧ x / n = (factorial (n-1)).get!
  | none => False :=
  sorry

theorem factorial_negative {n : Int} (h : n < 0) :
  factorial n = none :=
  sorry

theorem factorial_zero :
  factorial 0 = some 1 :=
  sorry
-- </vc-theorems>