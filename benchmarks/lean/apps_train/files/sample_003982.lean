An Arithmetic Progression is defined as one in which there is a constant difference between the consecutive terms of a given series of numbers. You are provided with consecutive elements of an Arithmetic Progression. There is however one hitch: exactly one term from the original series is missing from the set of numbers which have been given to you. The rest of the given series is the same as the original AP.  Find the missing term.  

You have to write a function that receives a list, list size will always be at least 3 numbers. The missing term will never be the first or last one.

## Example
```python
find_missing([1, 3, 5, 9, 11]) == 7
```

PS: This is a sample question of the facebook engineer challenge on interviewstreet.
I found it quite fun to solve on paper using math, derive the algo that way.
Have fun!

def find_missing (seq : List Int) : Int :=
  sorry

def list_range_int (n : Nat) : List Int :=
  (List.range n).map Int.ofNat

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded