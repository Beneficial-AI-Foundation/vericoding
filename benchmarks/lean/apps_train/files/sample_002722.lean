Two strings ```a``` and b are called isomorphic if there is a one to one mapping possible for every character of ```a``` to every character of ```b```. And all occurrences of every character in ```a``` map to same character in ```b```.

## Task

In this kata you will create a function that return ```True``` if two given strings are isomorphic to each other, and ```False``` otherwise. Remember that order is important.

Your solution must be able to handle words with more than 10 characters.

## Example
True:
```
CBAABC DEFFED
XXX YYY
RAMBUNCTIOUSLY THERMODYNAMICS
```

False:
```
AB CC
XXY XYY
ABAB CD
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded