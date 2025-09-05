Write a function groupIn10s which takes any number of arguments, and groups them into sets of 10s and sorts each group in ascending order.

The return value should be an array of arrays, so that numbers between 0-9 inclusive are in position 0 and numbers 10-19 are in position 1, etc. 

Here's an example of the required output:

```python
grouped = group_in_10s(8, 12, 38, 3, 17, 19, 25, 35, 50) 

grouped[0]     # [3, 8]
grouped[1]     # [12, 17, 19]
grouped[2]     # [25]
grouped[3]     # [35, 38]
grouped[4]     # None
grouped[5]     # [50]
```
``` haskell
groupIn10s [8, 12, 3, 17, 19, 24, 35, 50] `shouldBe`  [[3,8],[12,17,19],[24],[35],[],[50]]
```

def group_in_10s (nums : List Nat) : List (Option (List Nat)) := sorry

theorem group_in_10s_empty (nums : List Nat) :
  nums = [] → group_in_10s nums = [] := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded