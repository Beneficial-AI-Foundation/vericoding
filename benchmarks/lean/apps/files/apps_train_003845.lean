/-
You will be given the prime factors of a number as an array.
E.g: ```[2,2,2,3,3,5,5,13]```

You need to find the number, n, to which that prime factorization belongs.
It will be:
```
n = 2³.3².5².13 = 23400
```
Then, generate the divisors of this number.

Your function ```get_num() or getNum()``` will receive an array with potentially unordered prime factors and should output: an array with the found integer n at index 0, the amount of total divisors (both prime and compound numbers) at index 1, followed the smallest factor (index 2, and the biggest one (last element)

We will see the example given above with the only difference that the array of the prime factors is unordered.

The list of divisors for that number (23400) is:
```
2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 15, 18, 20, 24, 25, 26, 30, 36, 39, 40, 45, 50, 52, 60, 65, 72, 75, 78, 90, 100, 104, 117, 120, 130, 150, 156, 180, 195, 200, 225, 234, 260, 300, 312, 325, 360, 390, 450, 468, 520, 585, 600, 650, 780, 900, 936, 975, 1170, 1300, 1560, 1800, 1950, 2340, 2600, 2925, 3900, 4680, 5850, 7800, 11700 (not considering the integer 23400 itself)
```
There is a total amount of ```71``` divisors. The smallest divisor is ```2``` and the highest ```11700```.
So the expected output will be: 
```
get_num([2,13,2,5,2,5,3,3]) == [23400, 71, 2, 11700]
```
Enjoy!
-/

def get_num (arr : List Nat) : List Nat := sorry
def is_prime (n : Nat) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def minimum (l : List Nat) (h : l.length > 0) : Nat := sorry
def product (l : List Nat) : Nat := sorry

theorem get_num_basic_properties {arr : List Nat} (h1 : arr.length > 0) 
  (h2 : ∀ x ∈ arr, 2 ≤ x ∧ x ≤ 20) :
  let result := get_num arr
  result.length = 4 ∧ 
  result[0]! = product arr ∧
  result[2]! = minimum arr h1 ∧
  result[3]! = result[0]! / result[2]! := sorry

theorem get_num_small_factors {arr : List Nat}
  (h1 : 2 ≤ arr.length ∧ arr.length ≤ 3)
  (h2 : ∀ x ∈ arr, 2 ≤ x ∧ x ≤ 7) :
  let result := get_num arr
  result[0]! > 0 ∧
  result[1]! ≥ 0 ∧
  result[2]! ≤ minimum arr (by exact Nat.zero_lt_of_lt h1.left) ∧ 
  result[0]! % result[2]! = 0 := sorry

/-
info: [150, 11, 2, 75]
-/
-- #guard_msgs in
-- #eval get_num [2, 3, 5, 5]

/-
info: [378, 15, 2, 189]
-/
-- #guard_msgs in
-- #eval get_num [2, 3, 3, 3, 7]

/-
info: [23400, 71, 2, 11700]
-/
-- #guard_msgs in
-- #eval get_num [2, 13, 2, 5, 2, 5, 3, 3]

-- Apps difficulty: introductory
-- Assurance level: guarded