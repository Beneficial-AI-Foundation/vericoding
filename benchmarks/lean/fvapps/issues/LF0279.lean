-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (h :: t) => h + sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_probability (balls : List Nat) : Float := sorry

theorem probability_bounds {balls : List Nat} 
  (h1 : balls.length ≥ 2)
  (h2 : balls.length ≤ 4) 
  (h3 : ∀ x ∈ balls, 1 ≤ x ∧ x ≤ 3)
  (h4 : (List.sum balls) % 2 = 0) :
  0 ≤ get_probability balls ∧ get_probability balls ≤ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem symmetric_cases {balls : List Nat}
  (h1 : balls.length ≥ 2)
  (h2 : balls.length ≤ 4)
  (h3 : ∀ x ∈ balls, 1 ≤ x ∧ x ≤ 3) 
  (h4 : (List.sum balls) % 2 = 0) :
  get_probability balls = get_probability balls.reverse := sorry

theorem edge_cases_one :
  get_probability [1, 1] = 1 := sorry

theorem edge_cases_two :
  get_probability [2, 2] = 1 := sorry
-- </vc-theorems>