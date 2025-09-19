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
-- </vc-theorems>