-- <vc-preamble>
def solve_array_zeroes (n : Nat) (arr : List Int) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | h :: t => h + sum t
-- </vc-definitions>

-- <vc-theorems>
theorem solve_array_zeroes_nonnegative (n : Nat) (arr : List Int) :
  solve_array_zeroes n arr ≥ 0 :=
sorry

theorem solve_array_zeroes_all_positives (n : Nat) (arr : List Int) :
  (List.all arr (fun x => x ≥ 0)) → solve_array_zeroes n arr = 0 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_array_zeroes 4 [-3, 5, -3, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_array_zeroes 2 [1, -1]

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_array_zeroes 4 [-3, 2, -3, 4]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible