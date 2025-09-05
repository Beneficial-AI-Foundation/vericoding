You get an array of different numbers to sum up. But there is one problem, those numbers all have different bases.
For example:
```python
You get an array of numbers with their base as an input:

[["101",16],["7640",8],["1",9]]
```

The output should be the sum as an integer value with a base of 10, so according to the example this would be:

4258
```python
A few more examples:
[["101",2], ["10",8]] --> 13
[["ABC",16], ["11",2]] --> 2751
```
Bases can be between 2 and 36 (2<=base<=36)

def toBase (num base : Nat) : String :=
  sorry

def sumItUp (nums : List (String × Nat)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
