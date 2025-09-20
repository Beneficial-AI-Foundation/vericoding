-- <vc-preamble>
def check_perfect_number (n : Int) : Bool :=
  sorry

def perfect_numbers : List Int := [6, 28, 496, 8128, 33550336, 8589869056]

theorem known_perfect_numbers (n : Int) (h : n ∈ perfect_numbers) :
  check_perfect_number n = true :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def small_perfect_numbers : List Int := [6, 28, 496, 8128]

theorem most_numbers_not_perfect {n : Int} (h₁ : n ≥ 1) (h₂ : n ≤ 1000000)
  (h₃ : n ∉ small_perfect_numbers) :
  check_perfect_number n = false :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_positive_not_perfect {n : Int} (h : n ≤ 0) : 
  check_perfect_number n = false :=
  sorry
-- </vc-theorems>