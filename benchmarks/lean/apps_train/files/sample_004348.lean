Complete the solution. It should try to retrieve the value of the array at the index provided. If the index is out of the array's max bounds then it should return the default value instead. 

Example:
```Haskell
solution [1..3] 1 1000 `shouldBe` 2
solution [1..5] (10) 1000 `shouldBe` 1000
-- negative values work as long as they are not out of the length bounds
solution [1..3] (-1) 1000 `shouldBe` 3
solution [1..3] (-5) 1000 `shouldBe` 1000
solution [1..3] (-3) 1000 `shouldBe` 1
solution [1..5] (-3) 1000 `shouldBe` 3
-- for Haskell default value will always be a (random) number, not a character.
```

```python
data = ['a', 'b', 'c']
solution(data, 1, 'd') # should == 'b'
solution(data, 5, 'd') # should == 'd'

# negative values work as long as they aren't out of the length bounds
solution(data, -1, 'd') # should == 'c'
solution(data, -5, 'd') # should == 'd'
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
