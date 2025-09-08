/-
Alice, Samantha, and Patricia are relaxing on the porch, when Alice suddenly says: _"I'm thinking of two numbers, both greater than or equal to 2. I shall tell Samantha the sum of the two numbers and Patricia the product of the two numbers."_ 

She takes Samantha aside and whispers in her ear the sum so that Patricia cannot hear it. Then she takes Patricia aside and whispers in her ear the product so that Samantha cannot hear it.

After a moment of reflection, Samantha says:

 **Statement 1:** _"Patricia cannot know what the two numbers are."_

After which Patricia says:

 **Statement 2:**  _"In that case, I do know what the two numbers are."_

To which Samantha replies:

 **Statement 3:**  _"Then I too know what the two numbers are."_

Your first task is to write a function `statement1(s)` that takes an `int` argument `s` and returns `True` if and only if Samantha could have made statement 1 if given the number `s`. You may assume that `s` is the sum of two numbers both greater than or equal to 2.  

Your second task is to write a function `statement2(p)` that takes an `int` argument `p` and returns `True` if and only if Patricia, when given the number `p`, could have made statement 2 after hearing Samantha make statement 1. You may assume that `p` is the product of two numbers both greater than or equal to 2 and that Patricia would not have been able to determine the two numbers by looking at `p` alone.

Your third task is to write a function `statement3(s)` that takes an `int` argument `s` and returns `True` if and only if Samantha, when given the number `s`, could have made statement 3 after hearing Patricia make statement 2.

Finally, it is to you to figure out what two numbers Alice was thinking of. Since there are multiple solutions, you must write a function `is_solution(a, b)` that returns `True` if and only if `a` and `b` could have been two numbers that Alice was thinking of.

Hint: To get you started, think of what Samantha's first statement implies. Samantha knows that Patricia was not given the product of two primes. That means that the sum that Samantha was given cannot be written as the sum of two primes. Goldbach's conjecture stipulates that every even number greater than 3 can be written as the sum of two primes. Although Goldbach's conjecture has not yet been proven, you may assume that it has been verified for all numbers involved in the test cases here. So we know that the sum that Samantha was given must be odd. The only way to write an odd number as the sum of two primes is when one of the primes is 2, the only even prime. This means that the number given to Samantha is not the sum of 2 and a prime.
-/

def is_prime (n : Nat) : Bool :=
  sorry

def statement1 (s : Nat) : Bool :=
  sorry

def statement2 (p : Nat) : Bool := 
  sorry

def statement3 (s : Nat) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def is_solution (a b : Nat) : Bool :=
  sorry

theorem small_numbers_not_prime {n : Nat} (h : n ≤ 1) : 
  is_prime n = false := sorry

theorem prime_divisibility {n : Nat} (h₁ : n ≥ 2) (h₂ : n ≤ 1000) : 
  is_prime n = true → ∀ i : Nat, 2 ≤ i ∧ i ≤ n^(1/2) → n % i ≠ 0 := sorry

theorem statement1_even {s : Nat} (h : s % 2 = 0) :
  statement1 s = false := sorry

theorem statement1_prime_diff {s : Nat} (h : is_prime (s - 2)) :
  statement1 s = false := sorry

theorem statement2_type {p : Nat} (h₁ : p ≥ 4) (h₂ : p ≤ 100) :
  statement2 p = true ∨ statement2 p = false := sorry

theorem statement2_composite {p : Nat} (h₁ : p ≥ 4) (h₂ : p ≤ 100) :
  statement2 p = true → ∃ i : Nat, 2 ≤ i ∧ i ≤ p^(1/2) ∧ p % i = 0 := sorry

theorem statement3_type {s : Nat} (h₁ : s ≥ 4) (h₂ : s ≤ 100) :
  statement3 s = true ∨ statement3 s = false := sorry

theorem statement3_small {s : Nat} (h : s ≤ 3) :
  statement3 s = false := sorry

theorem is_solution_type {a b : Nat} (h₁ : a ≥ 2) (h₂ : a ≤ 50) (h₃ : b ≥ 2) (h₄ : b ≤ 50) :
  is_solution a b = true ∨ is_solution a b = false := sorry

theorem is_solution_constraints {a b : Nat} (h₁ : (a + b) % 2 = 0 ∨ is_prime (a * b)) :
  is_solution a b = false := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval statement1 6

/-
info: False
-/
-- #guard_msgs in
-- #eval statement2 15

/-
info: False
-/
-- #guard_msgs in
-- #eval is_solution 5 4

-- Apps difficulty: interview
-- Assurance level: unguarded