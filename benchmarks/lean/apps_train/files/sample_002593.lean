Given an integer, if the length of it's digits is a perfect square, return a square block of sqroot(length) * sqroot(length). If not, simply return "Not a perfect square!".

Examples:

1212 returns:

>1212  

Note: 4 digits so 2 squared (2x2 perfect square). 2 digits on each line.

123123123 returns: 
>123123123

Note: 9 digits so 3 squared (3x3 perfect square). 3 digits on each line.

def squareIt (n : Nat) : String := sorry

def isPerfectSquare (n : Nat) : Bool := sorry

def hasEqualRows (s : String) : Bool := sorry

def isqrt (n : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
