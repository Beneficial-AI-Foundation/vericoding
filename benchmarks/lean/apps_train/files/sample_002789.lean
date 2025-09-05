# Summation

Write a program that finds the summation of every number from 1 to num. The number will always be a positive integer greater than 0.

For example:
```if-not:racket
~~~
summation(2) -> 3
1 + 2

summation(8) -> 36
1 + 2 + 3 + 4 + 5 + 6 + 7 + 8
~~~
```
```if:racket
~~~racket
(summation 2) ; 3  (+ 1 2)
(summation 8) ; 36 (+ 1 2 3 4 5 6 7 8)
~~~
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible