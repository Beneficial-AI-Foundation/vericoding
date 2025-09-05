Implement a data structure supporting the following operations:

Inc(Key) - Inserts a new key  with value 1. Or increments an existing key by 1. Key is guaranteed to be a non-empty string.
Dec(Key) - If Key's value is 1, remove it from the data structure. Otherwise decrements an existing key by 1. If the key does not exist, this function does nothing. Key is guaranteed to be a non-empty string.
GetMaxKey() - Returns one of the keys with maximal value. If no element exists, return an empty string "".
GetMinKey() - Returns one of the keys with minimal value. If no element exists, return an empty string "".

Challenge: Perform all these in O(1) time complexity.

def AllOne.inc (a : AllOne) (key : String) : Unit := sorry
def AllOne.dec (a : AllOne) (key : String) : Unit := sorry

def AllOne.getMaxKey (a : AllOne) : String := sorry
def AllOne.getMinKey (a : AllOne) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded