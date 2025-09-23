-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_animals_count (legs heads horns : Nat) : AnimalCounts := sorry

theorem animal_counts_sum_to_heads {legs heads horns : Nat} :
  let result := get_animals_count legs heads horns
  result.cows + result.rabbits + result.chickens = heads := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>