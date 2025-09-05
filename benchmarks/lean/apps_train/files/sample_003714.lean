Given an array containing only integers, add all the elements and return the binary equivalent of that sum.

If the array contains any non-integer element (e.g. an object, a float, a string and so on), return false.

**Note:** The sum of an empty array is zero.

```python
arr2bin([1,2]) == '11'
arr2bin([1,2,'a']) == False
```

def arr2bin (arr : List α) : String := sorry

def sumList (l : List Int) : Int := sorry

def toBinaryString (n : Int) : String := sorry

theorem arr2bin_all_ints {arr : List Int} :
  arr2bin arr = toBinaryString (sumList arr) := sorry

def allBinary (s : String) : Bool := sorry
def stringToNat (s : String) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded