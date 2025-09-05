In this Kata, you will be given a string and two indexes (`a` and `b`). Your task is to reverse the portion of that string between those two indices inclusive. 

~~~if-not:fortran
```
solve("codewars",1,5) = "cawedors" -- elements at index 1 to 5 inclusive are "odewa". So we reverse them.
solve("cODEWArs", 1,5) = "cAWEDOrs" -- to help visualize.
```
~~~
~~~if:fortran
```
solve("codewars",2,6) = "cawedors" -- elements at indices 2 to 6 inclusive are "odewa". So we reverse them.
solve("cODEWArs", 2,6) = "cAWEDOrs" -- to help visualize.
```
~~~

Input will be lowercase and uppercase letters only. 

The first index `a` will always be lower that than the string length; the second index `b` can be greater than the string length. More examples in the test cases. Good luck!

Please also try:

[Simple time difference](https://www.codewars.com/kata/5b76a34ff71e5de9db0000f2)

[Simple remove duplicates](https://www.codewars.com/kata/5ba38ba180824a86850000f7)

~~~if:fortran
*NOTE: You may assume that all input strings will* **not** *contain any (redundant) trailing whitespace.  In return, your returned string is* **not** *permitted to contain any (redundant) trailing whitespace.*
~~~

def solve (s : String) (a b : Nat) : String := sorry

def length (s : String) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
