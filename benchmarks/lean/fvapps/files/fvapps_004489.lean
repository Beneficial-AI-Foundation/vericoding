-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum (l : List Int) : Int :=
sorry

def maximum? (l : List Int) : Option Int :=
sorry

def filterWithIndex (l : List Int) (f : Nat → Int → Bool) : List Int :=
sorry

def target_game (vals : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem target_game_nonneg (vals : List Int)
  (h : vals ≠ []) :
  target_game vals ≥ 0 :=
sorry
-- </vc-theorems>