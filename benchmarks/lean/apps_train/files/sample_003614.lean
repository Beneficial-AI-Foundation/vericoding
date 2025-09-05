Write
```python
smaller(arr)
```
that given an array ```arr```, you have to return the amount of numbers that are smaller than ```arr[i]``` to the right.

For example:
```python
smaller([5, 4, 3, 2, 1]) == [4, 3, 2, 1, 0]
smaller([1, 2, 0]) == [1, 1, 0]
```
``` haskell
smaller [5,4,3,2,1]  `shouldBe` [4,3,2,1,0]
smaller [1,2,3]      `shouldBe` [0,0,0]
smaller [1, 2, 0]    `shouldBe` [1, 1, 0]
```
If you've completed this one and you feel like testing your performance tuning of this same kata, head over to the much tougher version How many are smaller than me II?

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible