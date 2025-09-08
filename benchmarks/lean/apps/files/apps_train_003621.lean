/-
Two integers are coprimes if the their only greatest common divisor is 1.

## Task
In this kata you'll be given a number ```n >= 2``` and output a list with all positive integers less than ```gcd(n, k) == 1```, with ```k``` being any of the output numbers.

The list cannot include duplicated entries and has to be sorted.

## Examples
```
2 -> [1]
3 -> [1, 2]
6 -> [1, 5]
10 -> [1, 3, 7, 9]
20 -> [1, 3, 7, 9, 11, 13, 17, 19]
25 -> [1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13, 14, 16, 17, 18, 19, 21, 22, 23, 24]
30 -> [1, 7, 11, 13, 17, 19, 23, 29]
```
-/

def coprimes (n : Nat) : List Nat := sorry

def gcd (a b : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def countCoprimes (n : Nat) : Nat :=
  (List.range n).filter (fun x => gcd x n = 1) |>.length

theorem coprimes_all_less (n : Nat) (h : n ≥ 2) :
  ∀ x ∈ coprimes n, x > 0 ∧ x < n := sorry

/-
info: [1]
-/
-- #guard_msgs in
-- #eval coprimes 2

/-
info: [1, 2]
-/
-- #guard_msgs in
-- #eval coprimes 3

/-
info: [1, 3, 7, 9]
-/
-- #guard_msgs in
-- #eval coprimes 10

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible