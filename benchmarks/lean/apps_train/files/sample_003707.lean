In this Kata, you will be given a string of numbers in sequence and your task will be to return the missing number. If there is no number
missing or there is an error in the sequence, return `-1`.

For example:
```Haskell
missing("123567") = 4 
missing("899091939495") = 92
missing("9899101102") = 100
missing("599600601602") = -1 -- no number missing
missing("8990919395") = -1 -- error in sequence. Both 92 and 94 missing.
```
The sequence will always be in ascending order.

More examples in the test cases. 

Good luck!

def String.isDigit : String → Bool :=
  sorry

def missing : String → Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded