-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def robot_walk (lst : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem robot_walk_output_type (lst : List Int) (h : lst.length ≥ 3) :
  robot_walk lst = true ∨ robot_walk lst = false :=
sorry

theorem robot_walk_deterministic (lst : List Int) (h : lst.length ≥ 3) :
  robot_walk lst = robot_walk lst :=
sorry

theorem robot_walk_strictly_decreasing (lst : List Int) (h : lst.length ≥ 3)
  (decrease : ∀ (i j : Fin lst.length), i < j → lst.get i > lst.get j) :
  robot_walk lst = false :=
sorry
-- </vc-theorems>