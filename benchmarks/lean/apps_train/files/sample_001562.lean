/-
This kata generalizes [Twice Linear](https://www.codewars.com/kata/5672682212c8ecf83e000050). You may want to attempt that kata first.

## Sequence

Consider an integer sequence `U(m)` defined as:

1. `m` is a given non-empty set of positive integers.
2. `U(m)[0] = 1`, the first number is always 1.
3. For each `x` in `U(m)`, and each `y` in `m`, `x * y + 1` must also be in `U(m)`.
4. No other numbers are in `U(m)`.
5. `U(m)` is sorted, with no duplicates.

### Sequence Examples

#### `U(2, 3) = [1, 3, 4, 7, 9, 10, 13, 15, 19, 21, 22, 27, ...]`

1 produces 3 and 4, since `1 * 2 + 1 = 3`, and `1 * 3 + 1 = 4`.

3 produces 7 and 10, since `3 * 2 + 1 = 7`, and `3 * 3 + 1 = 10`.

#### `U(5, 7, 8) = [1, 6, 8, 9, 31, 41, 43, 46, 49, 57, 64, 65, 73, 156, 206, ...]`

1 produces 6, 8, and 9.

6 produces 31, 43, and 49.

## Task:

Implement `n_linear` or `nLinear`: given a set of postive integers `m`, and an index `n`, find `U(m)[n]`, the `n`th value in the `U(m)` sequence.

### Tips

* Tests use large n values. Slow algorithms may time-out.
* Tests use large values in the m set. Algorithms which multiply further than neccessary may overflow.
* Linear run time and memory usage is possible.
* How can you build the sequence iteratively, without growing extra data structures?
-/

-- <vc-helpers>
-- </vc-helpers>

def n_linear (multipliers : List Nat) (n : Nat) : Nat :=
  sorry

theorem n_linear_positive (multipliers : List Nat) (n : Nat)
  (h1 : multipliers.length > 0) 
  (h2 : ∀ x ∈ multipliers, x ≥ 2)
  (h3 : n ≥ 1) :
  n_linear multipliers n > 0 :=
sorry

theorem n_linear_monotonic (multipliers : List Nat) (n : Nat)
  (h1 : multipliers.length > 0)
  (h2 : ∀ x ∈ multipliers, x ≥ 2) 
  (h3 : n > 1) :
  n_linear multipliers (n-1) < n_linear multipliers n :=
sorry

theorem n_linear_strictly_increasing (multipliers : List Nat)
  (h1 : multipliers.length > 0)
  (h2 : ∀ x ∈ multipliers, x ≥ 2) :
  ∀ i, i < 2 → n_linear multipliers (i+1) < n_linear multipliers (i+2) :=
sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval n_linear [2, 3] 5

/-
info: 64
-/
-- #guard_msgs in
-- #eval n_linear [5, 7, 8] 10

/-
info: 46
-/
-- #guard_msgs in
-- #eval n_linear [2, 3, 4, 5] 33

-- Apps difficulty: interview
-- Assurance level: guarded