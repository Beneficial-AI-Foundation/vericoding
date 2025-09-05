Given a set of numbers, return the additive inverse of each. Each positive becomes negatives, and the negatives become positives.

~~~if-not:racket
```
invert([1,2,3,4,5]) == [-1,-2,-3,-4,-5]
invert([1,-2,3,-4,5]) == [-1,2,-3,4,-5]
invert([]) == []
```
~~~

```if:javascript,python,ruby,php,elixir,dart
You can assume that all values are integers. Do not mutate the input array/list.
```

```if:c
### Notes:
- All values are greater than `INT_MIN`
- The input should be modified, not returned.
```
~~~if:racket
```racket
(invert '(1 2 3 4 5))   ; '(-1 -2 -3 -4 -5)
(invert '(1 -2 3 -4 5)) ; '(-1 2 -3 4 -5)
(invert '())            ; '()
```
~~~

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible