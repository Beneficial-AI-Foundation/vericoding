-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def odd_ball {α} [BEq α] (xs : List (Sum α String)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_ball_property (base : List (Sum Nat String)) (insert_pos : Nat) (h : insert_pos ≤ base.length) :
  let test_list := (base.take insert_pos) ++ [Sum.inr "odd"] ++ (base.drop insert_pos)
  odd_ball test_list = test_list.contains (Sum.inl insert_pos)
  := sorry

theorem odd_ball_no_odd {α} [BEq α] (xs : List (Sum α String)) (h : ¬xs.contains (Sum.inr "odd")) :
  odd_ball xs = false := sorry
-- </vc-theorems>