We define the Perfect Number is a positive integer that is equal to the sum of all its positive divisors except itself. 

Now, given an integer n, write a function that returns true when it is a perfect number and false when it is not.

Example:

Input: 28
Output: True
Explanation: 28 = 1 + 2 + 4 + 7 + 14

Note:
The input number n will not exceed 100,000,000. (1e8)

def check_perfect_number (n : Int) : Bool :=
  sorry

def perfect_numbers : List Int := [6, 28, 496, 8128, 33550336, 8589869056]

theorem known_perfect_numbers (n : Int) (h : n ∈ perfect_numbers) :
  check_perfect_number n = true :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded