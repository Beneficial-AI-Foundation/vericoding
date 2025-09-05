As the title suggests, this is the hard-core version of  another neat kata.

The task is simple to explain: simply sum all the numbers from the first parameter being the beginning to the second parameter being the upper limit (possibly included), going in steps expressed by the third parameter:

```python
sequence_sum(2, 2, 2) # 2
sequence_sum(2, 6, 2) # 12 (= 2 + 4 + 6)
sequence_sum(1, 5, 1) # (= 1 + 2 + 3 + 4 + 5)
sequence_sum(1, 5, 3) # 5 (= 1 + 4)
```

If it is an impossible sequence (with the beginning being larger the end and a positive step or the other way around), just return `0`. See the provided test cases for further examples :)

**Note:** differing from the other base kata, much larger ranges are going to be tested, so you should hope to get your algo optimized and to avoid brute-forcing your way through the solution.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible