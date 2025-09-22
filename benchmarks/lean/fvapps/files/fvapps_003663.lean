-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unscramble_eggs (s : String) : String :=
sorry

def containsEgg (s : String) : Bool :=
sorry

def countSpaces (s : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_eggs_in_result (s : String) :
  containsEgg (unscramble_eggs s) = false :=
sorry

theorem preserves_space_count (s : String) :
  countSpaces s = countSpaces (unscramble_eggs s) :=
sorry
-- </vc-theorems>