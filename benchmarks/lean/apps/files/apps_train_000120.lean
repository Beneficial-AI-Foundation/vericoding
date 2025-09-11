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
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: 12
-/
-- #guard_msgs in
-- #eval maxScore [1, 2, 3, 4, 5, 6, 1] 3

/-
info: 4
-/
-- #guard_msgs in
-- #eval maxScore [2, 2, 2] 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval maxScore [1, 1000, 1] 1
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible