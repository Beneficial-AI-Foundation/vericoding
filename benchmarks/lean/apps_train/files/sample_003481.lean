We define the sequence ```SF``` in the following way in terms of four previous sequences: ```S1```, ```S2```, ```S3``` and ```ST```

We are interested in collecting the terms of SF that are multiple of ten.

The first term multiple of ten of this sequence is  ```60```

Make the function ```find_mult10_SF()``` that you introduce the ordinal number of a term multiple of 10 of SF and gives us the value of this term.

Let's see some cases: 
```python
find_mult10_SF(1) == 60

find_mult10_SF(2) == 70080

find_mult10_SF(3) ==  90700800
```
``` haskell
findMult10SF 1 `shouldBe` 60
findMult10SF 2 `shouldBe` 70080
findMult10SF 3 `shouldBe` 90700800
```
Memoization is advisable to have a more agile code for tests.

Your code will be tested up to the 300-th term, multiple of 10.

Happy coding!!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible