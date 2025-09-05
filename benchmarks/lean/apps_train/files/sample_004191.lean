Welcome

This kata is inspired by This Kata

We have a string s

We have a number n

Here is a function that takes your string, concatenates the even-indexed chars to the front, odd-indexed chars to the back.

Examples

    s = "Wow Example!"
    result = "WwEapeo xml!"
    s = "I'm JomoPipi"
    result = "ImJm ii' ooPp"

The Task:

return the result of the string after applying the function to it n times.

example where s = "qwertyuio" and n = 2:

    after 1 iteration  s = "qetuowryi"
    after 2 iterations s = "qtorieuwy"
    return "qtorieuwy"

 Note 

there's a lot of tests, big strings,
and n is greater than a billion

so be ready to optimize.

after doing this: do it's best friend!

# Check out my other kata!

Matrix Diagonal Sort OMG
String -> N iterations -> String
String -> X iterations -> String
ANTISTRING
Array - squareUp b!
Matrix - squareUp b!
Infinitely Nested Radical Expressions
pipi Numbers!

def jumbledString (s : String) (n : Int) : String := sorry

theorem jumbledString_length_preserved (s : String) (n : Int) (h : s.length > 0) :
  (jumbledString s n).length = s.length := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
