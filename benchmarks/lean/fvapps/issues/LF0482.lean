-- <vc-preamble>
def List.sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | h :: t => h + List.sum t

def Int.abs (n : Int) : Int :=
  if n ≥ 0 then n else -n

def List.sort (xs : List Nat) : List Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_target_sum_ways (nums : List Nat) (target : Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_bounds_nonnegative {nums : List Nat} {target : Int} :
  find_target_sum_ways nums target ≥ 0 := sorry

theorem output_bounds_impossible {nums : List Nat} {target : Int} :
  ((nums.sum : Int) < target.abs) → find_target_sum_ways nums target = 0 := sorry

theorem invariant_permutation {nums : List Nat} {target : Int} :
  find_target_sum_ways nums target = find_target_sum_ways (List.sort nums) target := sorry

theorem invariant_odd_sum {nums : List Nat} {target : Int} :
  ((nums.sum : Int) + target) % 2 = 1 → find_target_sum_ways nums target = 0 := sorry

theorem all_ones_symmetric {n : Nat} {nums : List Nat} :
  (∀ x ∈ nums, x = 1) →
  find_target_sum_ways nums (n / 2) = find_target_sum_ways nums (-n / 2) := sorry
-- </vc-theorems>