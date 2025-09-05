We are given a certain number ```n``` and we do the product partitions of it.
```[59, 3, 2, 2, 2]``` is a product partition of ```1416``` because:
```
59 * 3 * 2 * 2 * 2 = 1416
```
We form a score, ```sc``` for each partition in the following way:
- if ```d1, d2, ...., dk``` are the prime factors of ```n```, and ```f1, f2, ...., fk```, the corresponding frequencies for each factor, we calculate:

Suposse that we have that ```n = 1416``` 
The product partitions of this number with a corresponding special score are as follows:
```
Product Partition           Score(sc)
[59, 3, 2, 2, 2]             350    # equals to: (59^1 + 3^1 + 2^3) * 5
[177, 2, 2, 2]               740    # equals to: (177^1 + 2^3) * 4
[118, 3, 2, 2]               500
[59, 6, 2, 2]                276
[354, 2, 2]                 1074
[59, 4, 3, 2]                272
[236, 3, 2]                  723
[177, 4, 2]                  549
[118, 6, 2]                  378
[59, 12, 2]                  219
[708, 2]                    1420  <---- maximum value
[118, 4, 3]                  375
[59, 8, 3]                   210
[472, 3]                     950
[59, 6, 4]                   207
[354, 4]                     716
[236, 6]                     484
[177, 8]                     370
[118, 12]                    260
[59, 24]                     166  <---- minimum value
```
So we need a function that may give us the product partition with maximum or minimum score.

The function ```find_spec_prod_part()``` will receive two arguments:

- an integer ```n, n > 0```
- a command as a string, one of the following ones: ```'max' or 'min'```

The function should output a list with two elements: the found product partition (as a list sorted in descendin order) with its corresponding score.
```
find_spec_prod_part(n, com) ---> [prod_partition, score]
```
Let'see some cases:
```python
find_spec_prod_part(1416, 'max') == [[708, 2], 1420]

find_spec_prod_part(1416, 'min') == [[59, 24], 166]
```

The function should reject prime numbers:
```python
find_spec_prod_part(10007 , 'max') == "It is a prime number"
```
Enjoy it!

Hint: In this kata, optimization is one of the purposes or tags. The algorithm to produce the product partition is a key factor in terms of speed. Your code will be tested for an ```n``` value up to ```500000```.

def primeFactors (n : Nat) : List Nat :=
  sorry

def find_spec_prod_part (n : Nat) (mode : String) : String ⊕ (List Nat × Nat) :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
