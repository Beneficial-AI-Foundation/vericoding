/-
We have the integer `9457`. 

We distribute its digits in two buckets having the following possible distributions (we put the generated numbers as strings and we add the corresponding formed integers for each partition):
```
- one bucket with one digit and the other with three digits 
[['9'], ['4','5','7']] --> ['9','457'] --> 9 + 457 = 466
[['9','5','7'], ['4']] --> ['957','4'] --> 957 + 4 = 961
[['9','4','7'], ['5']] --> ['947','5'] --> 947 + 5 = 952
[['9','4','5'], ['7']] --> ['945','7'] --> 945 + 7 = 952

- two buckets with 2 digits each:
[['9','4'], ['5','7']] --> ['94','57'] --> 94 + 57 = 151
[['9','5'], ['4','7']] --> ['95','47'] --> 95 + 47 = 142
[['9','7'], ['4','5']] --> ['97','45'] --> 97 + 45 = 142
```

Now we distribute the digits of that integer in three buckets, and we do the same presentation as above:
```
one bucket of two digits and two buckets with one digit each:
[['9'], ['4'], ['5','7']] --> ['9','4','57'] --> 9 + 4 + 57 = 70
[['9','4'], ['5'], ['7']] --> ['94','5','7'] --> 94 + 5 + 7 = 106
[['9'], ['4', '5'], ['7']] --> ['9','45','7'] --> 9 + 45 + 7 = 61
[['9'], ['5'], ['4','7']] --> ['9','5','47'] --> 9 + 5 + 47 = 61
[['9','5'], ['4'], ['7']] --> ['95','4','7'] --> 95 + 4 + 7 = 106
[['9','7'], ['4'], ['5']] --> ['97','4','5'] --> 97 + 4 + 5 = 106
```
Finally we distribute the digits in the maximum possible amount of buckets for this integer, four buckets, with an unique distribution:
```
One digit in each bucket.
[['9'], ['4'], ['5'], ['7']] --> ['9','4','5','7'] --> 9 + 4 + 5 + 7 = 25
```
In the distribution we can observe the following aspects:

- the order of the buckets does not matter

- the order of the digits in each bucket matters; the available digits have the same order than in the original number.

- the amount of buckets varies from two up to the amount of digits

The function, `f =` `bucket_digit_distributions_total_sum`, gives for each integer, the result of the big sum of the total addition of generated numbers for each distribution of digits.
```python
bucket_digit_distributions_total_sum(9457) === 4301 # 466 + 961 + 952 + 952 + 151 + 142 + 142 + 70 + 106 + 61 + 61 + 106 + 106 + 25 = 4301
```
It is interesting to see the value of this function for a number that has one or more zeroes as digits, for example:
```python
bucket_digit_distributions_total_sum(10001) === 5466
```
Given an integer `n`, with its corresponding value of the above function, `f(n)`, and another integer `z`, find the closest and higher integer to n, `nf`, such `f(nf) > f(n) + z`.

Example:
```python
find(10001,100) === 10003
find(30000, 1000) === 30046
``` 
Features of the random tests:
```
100 <= n <= 1500000
50 <= z <= 6000
```
-/

-- <vc-helpers>
-- </vc-helpers>

def find (n : Nat) (z : Nat) : Nat := sorry

def bucket_digit_distributions_total_sum (n : Nat) : Int := sorry

theorem find_result_larger_than_input (n : Nat) (z : Nat) (h1 : n > 0) (h2 : n ≤ 10000) (h3 : z ≤ 1000) :
  find n z > n := sorry

theorem find_is_minimal_solution (n : Nat) (z : Nat) (h1 : n > 0) (h2 : n ≤ 10000) (h3 : z ≤ 1000) :
  let result := find n z
  bucket_digit_distributions_total_sum (result - 1) ≤ bucket_digit_distributions_total_sum n + z ∧
  bucket_digit_distributions_total_sum result > bucket_digit_distributions_total_sum n + z := sorry

theorem bucket_digit_distributions_properties (n : Nat) (h1 : n > 0) (h2 : n ≤ 10000) :
  bucket_digit_distributions_total_sum n ≥ -n := sorry

/-
info: 888
-/
-- #guard_msgs in
-- #eval find 500 200

/-
info: 10003
-/
-- #guard_msgs in
-- #eval find 10001 100

/-
info: 30046
-/
-- #guard_msgs in
-- #eval find 30000 1000

-- Apps difficulty: introductory
-- Assurance level: unguarded