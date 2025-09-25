-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def LRShoe := Nat × Nat  -- (left/right, size)

def pair_of_shoes (shoes : List LRShoe) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pair_of_shoes_valid (shoes : List LRShoe) :
  (∀ s ∈ shoes, s.1 ≤ 1) →
  ∀ result, result = pair_of_shoes shoes → result = true ∨ result = false
  := by sorry

theorem pair_of_shoes_count_matches (shoes : List LRShoe) :
  let left_count := fun size => (shoes.filter (fun s => s.1 = 0 ∧ s.2 = size)).length
  let right_count := fun size => (shoes.filter (fun s => s.1 = 1 ∧ s.2 = size)).length
  pair_of_shoes shoes = true ↔ ∀ size, left_count size = right_count size
  := by sorry

theorem pair_of_shoes_symmetry (shoes : List LRShoe) :
  let swapped := shoes.map (fun s => (1 - s.1, s.2))
  pair_of_shoes shoes = pair_of_shoes swapped
  := by sorry
-- </vc-theorems>