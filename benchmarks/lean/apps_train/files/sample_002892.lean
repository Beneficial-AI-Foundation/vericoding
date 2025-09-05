Given some positive integers, I wish to print the integers such that all take up the same width by adding a minimum number of leading zeroes. No leading zeroes shall be added to the largest integer.

For example, given `1, 23, 2, 17, 102`, I wish to print out these numbers as follows:

```python
001
023
002
017
102
```

Write a function `print_nums(n1, n2, n3, ...)` that takes a variable number of arguments and returns the string to be printed out.

def List.max (l: List Nat) : Nat :=
  sorry

def intToStr (n: Nat) : String :=
  sorry

def strLen (s: String) : Nat :=
  sorry

def splitLines (s: String) : List String :=
  sorry

def stringToNat (s: String) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible