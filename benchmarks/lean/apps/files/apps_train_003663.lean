-- <vc-preamble>
def unscramble_eggs (s : String) : String := sorry 

def containsEgg (s : String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countSpaces (s : String) : Nat := sorry

theorem no_eggs_in_result (s : String) : 
  containsEgg (unscramble_eggs s) = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem preserves_space_count (s : String) :
  countSpaces s = countSpaces (unscramble_eggs s) := sorry

/-
info: 'code here'
-/
-- #guard_msgs in
-- #eval unscramble_eggs "ceggodegge heggeregge"

/-
info: 'FUN KATA'
-/
-- #guard_msgs in
-- #eval unscramble_eggs "FeggUNegg KeggATeggA"

/-
info: 'vegymite on toast'
-/
-- #guard_msgs in
-- #eval unscramble_eggs "veggegeggyeggmeggitegge onegg teggoaseggtegg"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded