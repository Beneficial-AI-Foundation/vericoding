-- <vc-preamble>
def solution (n : Int) : Int := sorry

theorem solution_nonnegative (n : Int) : 
  solution n ≥ 0 ∧ (n ≤ 0 → solution n = 0) := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumMultiples (n : Nat) : Int :=
  (List.range n).map Int.ofNat
  |>.filter (fun x => x % 3 = 0 ∨ x % 5 = 0)
  |>.foldl (· + ·) 0
-- </vc-definitions>

-- <vc-theorems>
theorem multiples_property {n : Nat} : 
  0 < n →
  solution (Int.ofNat n) = sumMultiples n := sorry

theorem result_smaller_than_input_squared {n : Int} :
  n > 0 → solution n < n * n := sorry

theorem negative_inputs :
  ∀ n : Int, n < 0 → solution n = 0 := sorry

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
info: 0
-/
-- #guard_msgs in
-- #eval solution 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded