A function receives a certain numbers of integers ```n1, n2, n3 ..., np```(all positive and different from 0) and a factor ```k, k > 0```

The function rearranges the numbers ```n1, n2, ..., np``` in such order that generates the minimum number concatenating the digits and this number should be divisible by ```k```.

The order that the function receives their arguments is:
```python
rearranger(k, n1, n2, n3,....,np)
```

## Examples

```python
rearranger(4, 32, 3, 34, 7, 12)  == "Rearrangement: 12, 3, 34, 7, 32 generates: 12334732 divisible by 4"

rearranger(10, 32, 3, 34, 7, 12) == "There is no possible rearrangement"
```
If there are more than one possible arrengement for the same minimum number, your code should be able to handle those cases:
```python
rearranger(6, 19, 32, 2, 124, 20, 22) == "Rearrangements: 124, 19, 20, 2, 22, 32 and 124, 19, 20, 22, 2, 32 generates: 124192022232 divisible by 6"
```

The arrangements should be in sorted order, as you see: `124, 19, 20, 2, 22, 32` comes first than `124, 19, 20, 22, 2, 32`.

Have an enjoyable time!

(Thanks to `ChristianE.Cooper` for his contribution to this kata)

def rearranger (k : Nat) (nums : List Nat) : String := sorry

def splitString (s : String) (sep : String) : List String := sorry

def trim (s : String) : String := sorry
def toNat! (s : String) : Nat := sorry

def getFirst (l : List α) : α := sorry
def replace (s : String) (target : String) (replacement : String) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
