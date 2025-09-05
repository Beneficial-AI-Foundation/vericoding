This the second part part of the kata:

https://www.codewars.com/kata/the-sum-and-the-rest-of-certain-pairs-of-numbers-have-to-be-perfect-squares

In this part we will have to create a faster algorithm because the tests will be more challenging.

The function ```n_closestPairs_tonum()```, (Javascript: ```nClosestPairsToNum()```), will accept two arguments, ```upper_limit``` and ```k```.

The function should return the ```k``` largest pair of numbers [m, n] and the closest to ```upper_limit```. Expressing it in code:

```python
n_closestPairs_tonum(upper_limit, k) #-> [[m1, n1], [m2, n2], ...., [mk, nk]]
```
Such that:
```
upper_limit >= m1 >= m2 >= ....>= mk > 0
```
Examples:
```python
upper_limit = 1000; k = 4
n_closestPairs_tonum(upper_limit, k) == [[997, 372], [986, 950], [986, 310], [985, 864]]

upper_limit = 10000; k = 8
n_closestPairs_tonum(upper_limit, k) == [[9997, 8772], [9997, 2772], [9992, 6392], [9986, 5890], [9985, 7176], [9985, 4656], [9981, 9900], [9973, 9348]]
```
Features of the tests:
```
1000 ≤ upper_limit ≤ 200000
2 ≤ k ≤ 20
```

Enjoy it!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible