You are given a string of numbers between 0-9. Find the average of these numbers and return it as a floored whole number (ie: no decimal places) written out as a string. Eg:

"zero nine five two" -> "four"

If the string is empty or includes a number greater than 9, return "n/a"

def numToWord (n : Nat) : String := sorry 
def wordToNum (s : String) : Option Nat := sorry

def average_string (s : String) : String := sorry

def numWordsList := ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded