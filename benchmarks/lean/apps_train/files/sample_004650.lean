Given an array `A` and an integer `x`, map each element in the array to `F(A[i],x)` then return the xor sum of the resulting array.

where F(n,x) is defined as follows:

F(n, x) = ^(x)Cx **+** ^(x+1)Cx **+** ^(x+2)Cx **+** ... **+** ^(n)Cx

and ^(n)Cx represents [Combination](https://en.m.wikipedia.org/wiki/Combination) in mathematics

### Example

```python
a = [7, 4, 11, 6, 5]
x = 3

# after mapping, `a` becomes [F(7,3), F(4,3), F(11,3), F(6,3), F(5,3)]

return F(7,3) ^ F(4,3) ^ F(11,3) ^ F(6,3) ^ F(5,3)
#=> 384
```
##### e.g
F(7, 3) = ^(3)C3 + ^(4)C3 + ^(5)C3  + ^(6)C3 + ^(7)C3

## Constraints

**1 <= x <= 10**

**x <= A[i] <= 10^(4)**

**5 <= |A| <= 10^(3)**

def Nat.choose (n k : Nat) : Nat := sorry

def List.sort (l : List Nat) : List Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded