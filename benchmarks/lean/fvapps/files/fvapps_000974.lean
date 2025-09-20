-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def split_hoverboard (n : Nat) : (Nat × List Nat) := sorry

theorem split_hoverboard_count_even_odd (n : Nat) (h : n ≥ 2) :
  let (count, _) := split_hoverboard n
  count = if n % 2 = 0 then 4 else 6 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem split_hoverboard_squares_length (n : Nat) (h : n ≥ 2) :
  let (count, squares) := split_hoverboard n  
  squares.length = count := sorry

theorem split_hoverboard_dimensions_near_half (n : Nat) (h : n ≥ 2) :
  let (_, squares) := split_hoverboard n
  ∀ x, x ∈ squares → (x : Int) - n/2 ≤ 1 ∧ (x : Int) - n/2 ≥ -1 := sorry

theorem split_hoverboard_positive_squares (n : Nat) (h : n ≥ 2) :
  let (_, squares) := split_hoverboard n
  ∀ x, x ∈ squares → x > 0 := sorry

theorem split_hoverboard_even_case (n : Nat) (h : n ≥ 2) (h2 : n % 2 = 0) :
  let (_, squares) := split_hoverboard n
  ∀ x, x ∈ squares → x = n/2 := sorry
-- </vc-theorems>