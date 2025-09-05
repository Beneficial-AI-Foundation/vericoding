Your job is to write function last_digits(n,d) which return the last `d` digits of an integer `n` as a list.
`n` will be from 0 to 10^10

Examples:

`last_digits(1,1)     --> [1]`

`last_digits(1234,2)   --> [3,4]`

`last_digits(637547,6) --> [6,3,7,5,4,7]`

Special cases:

If `d` > the number of digits, just return the number's digits as a list.

If `d` <= 0, then return an empty list.

This is the first kata I have made, so please report any issues.

def last_digits (n : Nat) (d : Int) : List Nat := sorry

def list_to_string (l : List Nat) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded