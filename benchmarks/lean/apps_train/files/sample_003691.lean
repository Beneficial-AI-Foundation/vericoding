< PREVIOUS KATA
NEXT KATA >

###Task:

You have to write a function `pattern` which returns the following Pattern(See Examples) upto (3n-2) rows, where n is parameter.

* Note:`Returning` the pattern is not the same as `Printing` the pattern.

####Rules/Note:
* The pattern should be created using only unit digits.
* If `n < 1` then it should return "" i.e. empty string.
* `The length of each line is same`, and is equal to the length of longest line in the pattern i.e. `length = (3n-2)`.
* Range of Parameters (for the sake of CW Compiler) :
  + `n ∈ (-∞,50]`

###Examples:

  + pattern(5) :

            11111    
            22222    
            33333    
            44444    
        1234555554321
        1234555554321
        1234555554321
        1234555554321
        1234555554321
            44444    
            33333    
            22222    
            11111    

  + pattern(11):

                  11111111111          
                  22222222222          
                  33333333333          
                  44444444444          
                  55555555555          
                  66666666666          
                  77777777777          
                  88888888888          
                  99999999999          
                  00000000000          
        1234567890111111111110987654321
        1234567890111111111110987654321
        1234567890111111111110987654321
        1234567890111111111110987654321
        1234567890111111111110987654321
        1234567890111111111110987654321
        1234567890111111111110987654321
        1234567890111111111110987654321
        1234567890111111111110987654321
        1234567890111111111110987654321
        1234567890111111111110987654321
                  00000000000          
                  99999999999          
                  88888888888          
                  77777777777          
                  66666666666          
                  55555555555          
                  44444444444          
                  33333333333          
                  22222222222          
                  11111111111          

>>>LIST OF ALL MY KATAS<<<

def pattern (n : Nat) : String := sorry 

def isSingleDigit (c: Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

def stringContainsSubstr (s : String) (substr : String) : Bool := sorry
def stringContainsChar (s : String) (c : Char) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded