# History

This kata is a sequel of my [Mixbonacci](https://www.codewars.com/kata/mixbonacci/python) kata. Zozonacci is a special integer sequence named after [**ZozoFouchtra**](https://www.codewars.com/users/ZozoFouchtra), who came up with this kata idea in the [Mixbonacci discussion](https://www.codewars.com/kata/mixbonacci/discuss/python). 

This sequence combines the rules for computing the n-th elements of fibonacci, jacobstal, pell, padovan, tribonacci and tetranacci sequences according to a given pattern.

# Task

Compute the first `n` elements of the Zozonacci sequence for a given pattern `p`.

## Rules

1. `n` is given as integer and `p` is given as a list of as abbreviations as strings (e.g. `["fib", "jac", "pad"]`)
2. When `n` is 0 or `p` is empty return an empty list.
3. The first four elements of the sequence are determined by the first abbreviation in the pattern (see the table below).
4. Compute the fifth element using the formula corespoding to the first element of the pattern, the sixth element using the formula for the second element and so on. (see the table below and the examples)
5. If `n` is more than the length of `p` repeat the pattern.

```
+------------+--------------+------------------------------------------+---------------------+
|  sequence  | abbreviation |         formula for n-th element         | first four elements |
+------------|--------------+------------------------------------------|---------------------|
| fibonacci  |     fib      | a[n] = a[n-1] + a[n-2]                   |     0, 0, 0, 1      |
| jacobsthal |     jac      | a[n] = a[n-1] + 2 * a[n-2]               |     0, 0, 0, 1      |
| padovan    |     pad      | a[n] = a[n-2] + a[n-3]                   |     0, 1, 0, 0      |
| pell       |     pel      | a[n] = 2 * a[n-1] + a[n-2]               |     0, 0, 0, 1      |
| tetranacci |     tet      | a[n] = a[n-1] + a[n-2] + a[n-3] + a[n-4] |     0, 0, 0, 1      |
| tribonacci |     tri      | a[n] = a[n-1] + a[n-2] + a[n-3]          |     0, 0, 0, 1      |
+------------+--------------+------------------------------------------+---------------------+
```

## Example

```
zozonacci(["fib", "tri"], 7) == [0, 0, 0, 1, 1, 2, 3]

Explanation: 

          b     d
       /-----\/----\
[0, 0, 0, 1, 1, 2, 3]
 \--------/  
     | \--------/
     a     c

a - [0, 0, 0, 1] as "fib" is the first abbreviation
b - 5th element is 1 as the 1st element of the pattern is "fib": 1 = 0 + 1
c - 6th element is 2 as the 2nd element of the pattern is "tri": 2 = 0 + 1 + 1
d - 7th element is 3 as the 3rd element of the pattern is "fib" (see rule no. 5): 3 = 2 + 1
```

## Sequences

* [fibonacci](https://oeis.org/A000045) : 0, 1, 1, 2, 3 ...
* [padovan](https://oeis.org/A000931): 1, 0, 0, 1, 0 ...
* [jacobsthal](https://oeis.org/A001045): 0, 1, 1, 3, 5 ...
* [pell](https://oeis.org/A000129): 0, 1, 2, 5, 12 ...
* [tribonacci](https://oeis.org/A000073): 0, 0, 1, 1, 2 ...
* [tetranacci](https://oeis.org/A000078): 0, 0, 0, 1, 1 ...

def zozonacci (pattern : List String) (n : Nat) : List Nat := sorry

def isNonNegative (l : List Nat) : Prop := 
  ∀ x ∈ l, x ≥ 0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible