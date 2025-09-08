/-
The Collatz conjecture (also known as 3n+1 conjecture) is a conjecture that applying the following algorithm to any number we will always eventually reach one:

```
[This is writen in pseudocode]
if(number is even) number = number / 2
if(number is odd) number = 3*number + 1
```

#Task

Your task is to make a function ```hotpo``` that takes a positive ```n``` as input and returns the number of times you need to perform this algorithm to get ```n = 1```.

#Examples

```
hotpo(1) returns 0
(1 is already 1)

hotpo(5) returns 5
5 -> 16 -> 8 -> 4 -> 2 -> 1

hotpo(6) returns 8
6 -> 3 -> 10 -> 5 -> 16 -> 8 -> 4 -> 2 -> 1

hotpo(23) returns 15
23 -> 70 -> 35 -> 106 -> 53 -> 160 -> 80 -> 40 -> 20 -> 10 -> 5 -> 16 -> 8 -> 4 -> 2 -> 1
```

#References
- Collatz conjecture wikipedia page: https://en.wikipedia.org/wiki/Collatz_conjecture
-/

-- <vc-helpers>
-- </vc-helpers>

def hotpo (n : Nat) : Nat := sorry

theorem hotpo_terminates_at_one (n : Nat) (h : n > 0) : 
  hotpo n ≥ 0 := sorry

theorem hotpo_base_case :
  hotpo 1 = 0 := sorry

theorem hotpo_positive_for_greater_than_one (n : Nat) (h : n > 1) :
  hotpo n > 0 := sorry

theorem hotpo_even_numbers (n : Nat) (h : n > 0) (heven : n % 2 = 0) :
  hotpo n = hotpo (n / 2) + 1 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval hotpo 1

/-
info: 5
-/
-- #guard_msgs in
-- #eval hotpo 5

/-
info: 8
-/
-- #guard_msgs in
-- #eval hotpo 6

/-
info: 15
-/
-- #guard_msgs in
-- #eval hotpo 23

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible