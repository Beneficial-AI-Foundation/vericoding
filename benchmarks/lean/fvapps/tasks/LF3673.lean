-- <vc-preamble>
def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def closest_sum (nums : List Int) (target : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem closest_sum_is_sum_of_three (nums : List Int) (target : Int)
    (h : nums.length ≥ 3) :
  ∃ a b c, a ∈ nums ∧ b ∈ nums ∧ c ∈ nums ∧ 
    closest_sum nums target = a + b + c :=
  sorry

theorem closest_sum_is_minimal (nums : List Int) (target : Int) 
    (h : nums.length ≥ 3) :
  ∀ a b c, a ∈ nums → b ∈ nums → c ∈ nums →
    abs (target - closest_sum nums target) ≤ abs (target - (a + b + c)) :=
  sorry

theorem closest_sum_three_elements (a b c target : Int) :
  closest_sum [a,b,c] target = a + b + c :=
  sorry

theorem closest_sum_returns_int (nums : List Int) (target : Int)
    (h : nums.length ≥ 3) :
  ∃ n : Int, closest_sum nums target = n :=
  sorry
-- </vc-theorems>