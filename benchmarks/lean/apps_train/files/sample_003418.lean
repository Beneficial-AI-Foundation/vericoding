This kata is based on a [variation](https://www.codewars.com/kata/happy-numbers-5) of *Happy Numbers* by TySlothrop. It is advisable to complete it first to grasp the idea and then move on to this one.

___

Hello, my dear friend, and welcome to another *Happy Numbers* kata! What? You're not interested in them anymore? They are all the same? But what if I say that this one is a *performance version*...  

___

# Your task:

Write a function `performant_numbers` which takes a number `n` as an argument and returns a list of all *happy numbers* from `1` to `n` inclusive. For example:

```
performant_numbers(10)   =>  [1, 7, 10]
performant_numbers(50)   =>  [1, 7, 10, 13, 19, 23, 28, 31, 32, 44, 49]
performant_numbers(100)  =>  [1, 7, 10, 13, 19, 23, 28, 31, 32, 44, 49, 68, 70, 79, 82, 86, 91, 94, 97, 100]
```

# Test suite:

* `5000` tests with number `n` being up to `300000`
* The reference solution takes around `4.9` seconds to calculate the result
* you are not allowed to hardcode the sequence: you'll have to compute it (max length of the code: 1700 characters)

___

Will you take up the challenge?

def sum_dig (n: Nat) : Nat := sorry
def is_happy (n: Nat) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded