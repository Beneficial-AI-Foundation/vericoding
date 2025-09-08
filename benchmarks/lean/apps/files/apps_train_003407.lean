/-
Given an `x` and `y` find the smallest and greatest numbers **above** and **below** a given `n` that are divisible by both `x` and `y`.

### Examples
```python
greatest(2, 3, 20) => 18   # 18 is the greatest number under 20 that is divisible by both 2 and 3
smallest(2, 3, 20) => 24   # 24 is the smallest number above 20 that is divisible by both 2 and 3

greatest(5, 15, 100) => 90
smallest(5, 15, 100) => 105

greatest(123, 456, 789) => 0   # there are no numbers under 789 that are divisible by both 123 and 456
smallest(123, 456, 789) => 18696
```

**Notes:** 

1. you should never return `n` even if it is divisible by `x` and `y` always the number above or below it
2. `greatest` should return 0 if there are no numbers under `n` that are divisible by both `x` and `y`
3. and all arguments will be valid (integers greater than 0).

### Note for Haskell users

>Please take a look at [bkaes comment](http://www.codewars.com/kata/when-greatest-is-less-than-smallest/discuss#56418f0fbf1f44834d000050) and give us your opinion
-/

def greatest (x y n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def smallest (x y n : Nat) : Nat :=
  sorry

theorem divisible_by_inputs {x y n : Nat} (hx : x > 0) (hy : y > 0) :
  let g := greatest x y (max x y * 2)
  let s := smallest x y (max x y * 2)
  g % x = 0 ∧ g % y = 0 ∧ s % x = 0 ∧ s % y = 0 :=
  sorry

theorem bounds {x y n : Nat} (hx : x > 0) (hy : y > 0) (hn : n > 0) :
  let g := greatest x y n
  let s := smallest x y n  
  g < n ∧ s > n ∧ s > g :=
  sorry

/-
info: 18
-/
-- #guard_msgs in
-- #eval greatest 2 3 20

/-
info: 24
-/
-- #guard_msgs in
-- #eval smallest 2 3 20

/-
info: 90
-/
-- #guard_msgs in
-- #eval greatest 5 15 100

/-
info: 105
-/
-- #guard_msgs in
-- #eval smallest 5 15 100

/-
info: 0
-/
-- #guard_msgs in
-- #eval greatest 123 456 789

/-
info: 18696
-/
-- #guard_msgs in
-- #eval smallest 123 456 789

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible