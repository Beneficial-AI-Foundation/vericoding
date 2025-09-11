-- <vc-preamble>
def trotter (n: Int) : Int := sorry

-- Define the special case
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isInsomnia (n: Int) : Bool := sorry

theorem trotter_positive_multiple {n : Int} (h : n > 0) :
  ∃ k : Int, trotter n = n * k ∧ k > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem trotter_zero :
  isInsomnia (trotter 0) = true := sorry

theorem trotter_nonzero {n : Int} (h : n > 0) :
  trotter n > 0 := sorry

theorem trotter_grows {n : Int} (h : n > 0) :
  trotter n ≥ n := sorry

/-
info: 5076
-/
-- #guard_msgs in
-- #eval trotter 1692

/-
info: 90
-/
-- #guard_msgs in
-- #eval trotter 2

/-
info: 'INSOMNIA'
-/
-- #guard_msgs in
-- #eval trotter 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded