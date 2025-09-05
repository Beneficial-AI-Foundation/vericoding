Write a function that rearranges an integer into its largest possible value. 

```python
super_size(123456) # 654321
super_size(105)    # 510
super_size(12)     # 21
```
``` haskell
superSize 123456 `shouldBe` 654321
superSize    105 `shouldBe`    510
superSize     12 `shouldBe`     21
```

If the argument passed through is single digit or is already the maximum possible integer, your function should simply return it.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
