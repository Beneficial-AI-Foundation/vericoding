-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isCard (c : String) : Bool := sorry

def snap (flashPile : List String) (turtlePile : List String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem snap_output_basic {flashPile turtlePile : List String} 
  (h1 : flashPile.length > 0)
  (h2 : turtlePile.length > 0)
  (h3 : ∀ c ∈ flashPile, isCard c)
  (h4 : ∀ c ∈ turtlePile, isCard c) :
  snap flashPile turtlePile ≥ 0 := sorry

theorem snap_empty_piles :
  snap [] [] = 0 ∧ 
  (∀ c, isCard c → snap [c] [] = 0) ∧
  (∀ c, isCard c → snap [] [c] = 0) := sorry
-- </vc-theorems>