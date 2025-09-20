-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ball_probability (bag : List String) (target : List String) (replace : Bool) : Float := sorry

theorem probability_bounds {bag : List String} {target : List String} {replace : Bool}
  (h1 : target.length = 2)
  (h2 : bag.length ≥ 2) :
  let prob := ball_probability bag target replace;
  0 ≤ prob ∧ prob ≤ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem impossible_cases {bag : List String} {target : List String} {replace : Bool}
  (h1 : target.length = 2) 
  (h2 : ¬(∃ x ∈ bag, x = target[0]!)) 
  (h3 : ¬(∃ x ∈ bag, x = target[1]!)) :
  ball_probability bag target replace = 0 := sorry

theorem replacement_vs_no_replacement {bag : List String} {target : List String}
  (h1 : target.length = 2)
  (h2 : bag.length ≥ 2)
  (h3 : target[0]! = target[1]!) :
  ball_probability bag target true ≥ ball_probability bag target false := sorry
-- </vc-theorems>