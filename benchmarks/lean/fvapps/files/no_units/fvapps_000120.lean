-- <vc-preamble>
def abs (n : Int) : Int :=
  sorry

def sum (l : List Int) : Int := 
  sorry

def take (n : Nat) (l : List Int) : List Int :=
  sorry

def drop (n : Nat) (l : List Int) : List Int :=
  sorry

def map (f : Int → Int) (l : List Int) : List Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxScore (cards : List Int) (k : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxScore_invalid_inputs_empty 
  (k : Nat) :
  maxScore [] k = 0 := -- should fail
  sorry
-- </vc-theorems>