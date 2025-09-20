-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bouncing_ball (initial : Int) (proportion : Float) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bouncing_ball_positive 
  (initial : Int) (proportion : Float)
  (h1 : initial ≥ 2) (h2 : initial ≤ 1000)
  (h3 : proportion > 0.001) (h4 : proportion < 0.999) :
  bouncing_ball initial proportion > 0 :=
  sorry

theorem bouncing_ball_is_int
  (initial : Int) (proportion : Float)
  (h1 : initial ≥ 2) (h2 : initial ≤ 1000) 
  (h3 : proportion > 0.001) (h4 : proportion < 0.999) :
  ∃ n : Int, bouncing_ball initial proportion = n :=
  sorry

theorem bouncing_ball_final_height
  (initial : Int) (proportion : Float)
  (h1 : initial ≥ 2) (h2 : initial ≤ 1000)
  (h3 : proportion > 0.001) (h4 : proportion < 0.999) :
  let result := bouncing_ball initial proportion
  let final_height := Float.ofInt initial * Float.pow proportion (Float.ofInt result)
  final_height ≤ 1 :=
  sorry

theorem bouncing_ball_previous_height
  (initial : Int) (proportion : Float)
  (h1 : initial ≥ 2) (h2 : initial ≤ 1000)
  (h3 : proportion > 0.001) (h4 : proportion < 0.999) :
  let result := bouncing_ball initial proportion
  let previous_height := Float.ofInt initial * Float.pow proportion (Float.ofInt result - 1)
  previous_height > 1 :=
  sorry
-- </vc-theorems>