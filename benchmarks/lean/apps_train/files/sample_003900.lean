Write a function that takes an integer and returns an array `[A, B, C]`, where `A` is the number of multiples of 3 (but not 5) below the given integer, `B` is the number of multiples of 5 (but not 3) below the given integer and `C` is the number of multiples of 3 and 5 below the given integer. 

For example, `solution(20)` should return `[5, 2, 1]`

~~~if:r
```r
# in R, returns a numeric vector
solution(20)
[1] 5 2 1

class(solution(20))
[1] "numeric"
```
~~~

def solution (n : Nat) : Array Nat := sorry

def isMultipleOf3 (x : Nat) : Bool := x % 3 == 0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded