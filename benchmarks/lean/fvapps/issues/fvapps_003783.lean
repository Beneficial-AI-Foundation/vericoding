-- <vc-preamble>
def solution (n : Nat) : Nat :=
  sorry

def summ (n d : Nat) : Nat :=
  sorry

def list_sum (l : List Nat) : Nat :=
  l.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def filter_sum (l : List Nat) (f : Nat → Bool) : Nat :=
  list_sum (l.filter f)
-- </vc-definitions>

-- <vc-theorems>
theorem solution_positive (n : Nat) (h : n ≥ 1) :
  solution n ≥ 0 :=
  sorry

theorem summ_nonneg (n d : Nat) (h₁ : n ≥ 1) (h₂ : d ≥ 1) :
  summ n d ≥ 0 :=
  sorry

theorem solution_inclusion_exclusion (n : Nat) (h : n ≥ 1) :
  solution n = summ n 3 + summ n 5 - summ n 15 :=
  sorry

end Ex

/-
info: 23
-/
-- #guard_msgs in
-- #eval solution 10

/-
info: 78
-/
-- #guard_msgs in
-- #eval solution 20

/-
info: 2318
-/
-- #guard_msgs in
-- #eval solution 100
-- </vc-theorems>