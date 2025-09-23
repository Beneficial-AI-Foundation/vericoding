-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_candy_distribution (n k : Nat) : Nat × Nat := sorry

theorem candy_distribution_non_negative (n k : Nat) :
  let (candies_per_student, remaining) := solve_candy_distribution n k
  candies_per_student ≥ 0 ∧ remaining ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remaining_less_than_students {n k : Nat} (h : k > 0) :
  let (candies_per_student, remaining) := solve_candy_distribution n k
  remaining < k := sorry

theorem total_candies_preserved {n k : Nat} (h : k > 0) :
  let (candies_per_student, remaining) := solve_candy_distribution n k
  n = candies_per_student * k + remaining := sorry

theorem zero_students_case (n : Nat) :
  let (candies_per_student, remaining) := solve_candy_distribution n 0
  candies_per_student = 0 ∧ remaining = n := sorry

theorem perfect_division (n k : Nat) (h : k > 0) :
  let (candies_per_student, remaining) := solve_candy_distribution (n * k) k
  candies_per_student = n ∧ remaining = 0 := sorry
-- </vc-theorems>