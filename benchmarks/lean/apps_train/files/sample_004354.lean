Write a function that takes a number or a string and gives back the number of **permutations without repetitions** that can generated using all of its element.; more on permutations [here](https://en.wikipedia.org/wiki/Permutation).

For example, starting with:
```
1
45
115
"abc"
```

You could respectively generate:
```
1
45,54
115,151,511
"abc","acb","bac","bca","cab","cba"
```

So you should have, in turn:
```python
perms(1)==1
perms(45)==2
perms(115)==3
perms("abc")==6
```

def perms (s : String) : Nat := sorry

def listPerms (l : List α) : List (List α) := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
