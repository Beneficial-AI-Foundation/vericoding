In this kata, we want to discover a small property of numbers. 
We say that a number is a **dd** number if it contains d occurences of a digit d, (d is in [1,9]).

## Examples

* 664444309 is a **dd** number, as it contains 4 occurences of the number 4
* 30313, 122 are **dd** numbers as they respectively contain 3 occurences of the number 3, and (1 occurence of the number 1 AND 2 occurences of the number 2)
* 123109, 0, 56542 are not **dd** numbers

## Task 

Your task is to implement a function called `is_dd` (`isDd` in javascript) that takes a **positive** number (type depends on the language) and returns a boolean corresponding to whether the number is a **dd** number or not.

def is_dd (n : Nat) : Bool := sorry 

def countDigit (n : Nat) (d : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
