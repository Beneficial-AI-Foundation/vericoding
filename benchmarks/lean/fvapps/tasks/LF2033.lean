-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_dance_positions (n w h : Nat) (dancers : List (Nat × Nat × Nat)) : List (Nat × Nat) := sorry

theorem single_vertical_dancer (w h : Nat) :
  let n := 1
  let dancers := [(1, 2, 0)]
  let result := solve_dance_positions n w h dancers
  result.length = 1 ∧ (result.head!).2 = h := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_horizontal_dancer (w h : Nat) :  
  let n := 1
  let dancers := [(2, 3, 0)]
  let result := solve_dance_positions n w h dancers 
  result.length = 1 ∧ (result.head!).1 = w := sorry

theorem two_dancers (w h : Nat) :
  let n := 2
  let dancers := [(1, 2, 0), (2, 3, 0)]
  let result := solve_dance_positions n w h dancers
  result.length = 2 ∧ 
  (result.head!).2 = h ∧
  (result.get! 1).1 = w := sorry

theorem single_dancer_edge_cases {w h : Nat} (hw : w ≥ 2) (hh : h ≥ 2) :
  let dancers₁ := [(1, 1, 0)]
  let result₁ := solve_dance_positions 1 w h dancers₁
  let dancers₂ := [(2, 1, 0)]
  let result₂ := solve_dance_positions 1 w h dancers₂
  result₁ = [(1, h)] ∧ 
  result₂ = [(w, 1)] := sorry
-- </vc-theorems>