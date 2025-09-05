The number ```1331``` is the first positive perfect cube,  higher than ```1```, having all its digits odd (its cubic root is ```11```).

The next one is ```3375```.

In the interval [-5000, 5000] there are six pure odd digit perfect cubic numbers and are: ```[-3375,-1331, -1, 1, 1331, 3375]```

Give the numbers of this sequence that are in the range ```[a,b] ```(both values inclusive)

Examples:
``` python
odd_dig_cubic(-5000, 5000) == [-3375,-1331, -1, 1, 1331, 3375] # the output should be sorted.
odd_dig_cubic(0, 5000) == [1, 1331, 3375]
odd_dig_cubic(-1, 5000) == [-1, 1, 1331, 3375]
odd_dig_cubic(-5000, -2) == [-3375,-1331]

```
Features of the random tests for python:
```
number of Tests = 94
minimum value for a = -1e17
maximum value for b = 1e17
```
You do not have to check the entries, ```a``` and ```b``` always integers and ```a < b``` 

Working well in Python 2 and Python 3.
Translation into Ruby is coming soon.

def odd_dig_cubic (a b : Int) : List Int :=
  sorry

-- Helper function to check if a number's digits are all odd

def hasAllOddDigits (n : Int) : Bool :=
  sorry

-- Helper function to check if a number is a perfect cube

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded