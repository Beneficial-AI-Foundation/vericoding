/-
Unscramble the eggs.

The string given to your function has had an "egg" inserted directly after each consonant.  You need to return the string before it became eggcoded.

## Example

Kata is supposed to be for beginners to practice regular expressions, so commenting would be appreciated.
-/

def unscramble_eggs (s : String) : String := sorry 

def containsEgg (s : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def countSpaces (s : String) : Nat := sorry

theorem no_eggs_in_result (s : String) : 
  containsEgg (unscramble_eggs s) = false := sorry

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

-- Apps difficulty: introductory
-- Assurance level: unguarded