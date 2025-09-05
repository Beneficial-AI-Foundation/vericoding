Implement a class/function, which should parse time expressed as `HH:MM:SS`, or `null/nil/None` otherwise.

Any extra characters, or minutes/seconds higher than 59 make the input invalid, and so should return `null/nil/None`.

def toString (h : String) (m : String) (s : String) : String := sorry

def isDigit (s : String) : Bool := sorry

def toSeconds (s : String) : Option Nat := sorry

def fromNat (n : Nat) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
