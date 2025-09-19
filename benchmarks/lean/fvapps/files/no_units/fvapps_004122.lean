-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def are_equally_strong (your_left right friends_left friends_right : Int) : Bool := sorry

-- Symmetry property
-- </vc-definitions>

-- <vc-theorems>
theorem are_equally_strong_symmetric 
  (your_left your_right friends_left friends_right : Int) :
  are_equally_strong your_left your_right friends_left friends_right =
  are_equally_strong your_right your_left friends_left friends_right ∧
  are_equally_strong your_left your_right friends_right friends_left := sorry

-- Reflexivity property 

theorem are_equally_strong_reflexive (left right : Int) :
  are_equally_strong left right left right = true := sorry

-- Transitivity property

theorem are_equally_strong_transitive (a1 a2 b1 b2 : Int) :
  are_equally_strong a1 a2 b1 b2 → are_equally_strong b1 b2 b1 b2 →
  are_equally_strong a1 a2 b1 b2 := sorry
-- </vc-theorems>