Integral numbers can be even or odd.

Even numbers satisfy `n = 2m` ( with `m` also integral ) and we will ( completely arbitrarily ) think of odd numbers as `n = 2m + 1`.  
Now, some odd numbers can be more odd than others: when for some `n`, `m` is more odd than for another's. Recursively. :]  
Even numbers are just not odd.

# Task

Given a finite list of integral ( not necessarily non-negative ) numbers, determine the number that is _odder than the rest_.  
If there is no single such number, no number is odder than the rest; return `Nothing`, `null` or a similar empty value.

# Examples

```python
oddest([1,2]) => 1
oddest([1,3]) => 3
oddest([1,5]) => None
```

# Hint

Do you _really_ want one? Point or tap here.

def get_oddity (n : Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
