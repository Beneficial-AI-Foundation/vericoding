Create a function that finds the largest palindromic number made from the product of **at least 2** of the given arguments.

### Notes

* Only non-negative numbers will be given in the argument
* You don't need to use all the digits of the products
* Single digit numbers are considered palindromes
* Optimization is needed: dealing with ones and zeros in a smart way will help a lot

## Examples

```
[937, 113] --> 81518
```
As `937 * 113 = 105881` and the largest palindromic number that can be arranged from the digits of result is: `81518`

Another one:

```
[57, 62, 23] --> 82128

             product     palindrome
57 * 62      = 3534   -->  353
57 * 23      = 1311   -->  131
62 * 23      = 1426   -->  6
57 * 62 * 23 = 81282  -->  82128
```

One more:
```
[15, 125, 8] --> 8

             product     palindrome
15 * 125     = 1875   -->  8
15 * 8       = 120    -->  2
125 * 8      = 1000   -->  1
15 * 125 * 8 = 15000  -->  5
```

def largest_palindrom_from (n : Nat) : Nat := sorry

def numeric_palindrome (arr : List Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
