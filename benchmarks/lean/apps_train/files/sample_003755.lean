Implement a function which behaves like the 'uniq -c' command in UNIX. 

It takes as input a sequence and returns a sequence in which all duplicate elements following each other have been reduced to one instance together with the number of times a duplicate elements occurred in the original array.

Example:

```python
['a','a','b','b','c','a','b','c'] --> [('a',2),('b',2),('c',1),('a',1),('b',1),('c',1)]
```

def uniq_c {α : Type u} (xs : List α) : List (α × Nat) :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded