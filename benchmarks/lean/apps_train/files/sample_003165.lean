>When no more interesting kata can be resolved, I just choose to create the new kata, to solve their own, to enjoy the process  --myjinxin2015 said

# Description:
 Give you two number `m` and `n`(two positive integer, m < n), make a triangle pattern with number sequence `m to n`. The order is clockwise, starting from the top corner, like this:

```
 When m=1 n=10  triangle is:
    1
   9 2
  8 0 3
 7 6 5 4
```
 Note: The pattern only uses the last digit of each number; Each row separated by "\n"; Each digit separated by a space; Left side may need pad some spaces, but don't pad the right side; If `m to n` can not make the triangle, return `""`.

# Some examples:

```
makeTriangle(1,3) should return:
 1
3 2

makeTriangle(6,20) should return: 

    6
   7 7
  6 8 8
 5 0 9 9
4 3 2 1 0

makeTriangle(1,12) should return ""

```

def make_triangle (m n : Nat) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded