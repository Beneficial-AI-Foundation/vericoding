In this kata you have to create all permutations of an input string and remove duplicates, if present. This means, you have to shuffle all letters from the input in all possible orders.

Examples:

```python
permutations('a'); # ['a']
permutations('ab'); # ['ab', 'ba']
permutations('aabb'); # ['aabb', 'abab', 'abba', 'baab', 'baba', 'bbaa']
```

The order of the permutations doesn't matter.

def permutations (s : String) : List String := sorry

def factorial (n : Nat) : Nat := sorry

def noDups {α} [BEq α] (as : List α) : List α :=
  as.foldl (fun acc a => if acc.contains a then acc else a::acc) []

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
