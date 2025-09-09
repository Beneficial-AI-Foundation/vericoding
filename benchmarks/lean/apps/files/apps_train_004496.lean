/-
For a given two numbers your mission is to derive a function that evaluates whether two given numbers are **abundant**, **deficient** or **perfect** and whether together they are **amicable**.

### Abundant Numbers
An abundant number or excessive number is a number for which the sum of its proper divisors is greater than the number itself.

The integer 12 is the first abundant number. Its proper divisors are 1, 2, 3, 4 and 6 for a total of 16 (> 12).

### Deficient Numbers
A deficient number is a number for which the sum of its proper divisors is less than the number itself.

The first few deficient numbers are: 1, 2, 3, 4, 5, 7, 8, 9.

### Perfect Numbers
A perfect number is a positive integer that is equal to the sum of its proper positive divisors, that is, the sum of its positive divisors excluding the number itself. 

The first perfect number is 6, because 1, 2, and 3 are its proper positive divisors, and 1 + 2 + 3 = 6.

### Amicable Numbers
Amicable numbers are two different numbers so related that the sum of the proper divisors of each is equal to the other number. (A proper divisor of a number is a positive factor of that number other than the number itself. For example, the proper divisors of 6 are 1, 2, and 3.)

For example, the smallest pair of amicable numbers is (220, 284); for the proper divisors of 220 are 1, 2, 4, 5, 10, 11, 20, 22, 44, 55 and 110, of which the sum is 284; and the proper divisors of 284 are 1, 2, 4, 71 and 142, of which the sum is 220.

### The Function

For a given two numbers, derive function `deficientlyAbundantAmicableNumbers(num1, num2)` which returns a string with first and second word either abundant or deficient depending on whether `num1` or `num2` are abundant, deficient or perfect. The string should finish with either amicable or not amicable depending on the relationship between `num1` and `num2`.

e.g. `deficientlyAbundantAmicableNumbers(220, 284)` returns `"abundant deficient amicable"` as 220 is an abundant number, 284 is a deficient number and amicable because 220 and 284 are an amicable number pair. 

See Part 1 - [Excessively Abundant Numbers](http://www.codewars.com/kata/56a75b91688b49ad94000015)

See Part 2 - [The Most Amicable of Numbers](http://www.codewars.com/kata/56b5ebaa26fd54188b000018)
-/

def sumOfDivs (n : Nat) : Nat := sorry

def kind (n : Nat) (sum : Nat) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

def deficientlyAbundantAmicableNumbers (n1 n2 : Nat) : String := sorry

/- The kind function only outputs "abundant", "deficient", or "perfect" -/

theorem kind_outputs {n : Nat} (h : n > 0) : 
  let sum := sumOfDivs n
  let k := kind n sum
  (k = "abundant" ∨ k = "deficient" ∨ k = "perfect") := sorry

/- Properties of deficiently abundant amicable numbers output -/

theorem deficientlyabundant_properties {n1 n2 : Nat} (h1 : n1 > 0) (h2 : n2 > 0) :
  let result := deficientlyAbundantAmicableNumbers n1 n2 
  let sum1 := sumOfDivs n1
  let sum2 := sumOfDivs n2
  let is_amicable := sum1 = n2 ∧ sum2 = n1 ∧ n1 ≠ n2
  result.contains 'n' = !is_amicable := sorry

/- Symmetric property of amicable numbers -/

theorem symmetric_property {n1 n2 : Nat} (h1 : n1 > 0) (h2 : n2 > 0) :
  let result1 := deficientlyAbundantAmicableNumbers n1 n2
  let result2 := deficientlyAbundantAmicableNumbers n2 n1
  result1.contains 'n' = result2.contains 'n' := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded