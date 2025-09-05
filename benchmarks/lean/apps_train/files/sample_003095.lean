Let's take an integer number, ``` start``` and let's do the iterative process described below:

- we take its digits and raise each of them to a certain power, ```n```, and add all those values up. (result = ```r1```)

- we repeat the same process with the value ```r1``` and so on, ```k``` times.

Let's do it with ```start = 420, n = 3, k = 5```

```
420 ---> 72 (= 4³ + 2³ + 0³) ---> 351 (= 7³ + 2³) ---> 153 ---> 153 ----> 153
```

We can observe that it took ```3``` steps to reach a cyclical pattern ```[153]```(```h = 3```). The length of this cyclical pattern is ```1```, ```patt_len```. The last term of our k operations is 153, ```last_term```

Now, ```start = 420, n = 4, k = 30```

```
420 ---> 272 ---> 2433 ---> 434 ---> 593 ---> 7267 --->
6114 ---> 1554 ---> 1507 ---> 3027 ---> 2498 ---> 10929 --->
13139 ---> 6725 ---> 4338 ---> 4514 ---> 1138 ---> 4179 ---> 9219 ---> 
13139 ---> 6725 ---> 4338 ---> 4514 ---> 1138 ---> 4179 ---> 9219 ---> 
13139 ---> 6725 ---> 4338 ---> 4514 ---> 1138 ---> 4179 ---> 9219......
```

In this example we can observe that the cyclical pattern (```cyc_patt_arr```) is ```[13139, 6725, 4338, 4514, 1138, 4179, 9219]``` with a length of ```7```, (```patt_len = 7```), and it took ```12``` steps (```h = 12```) to reach the cyclical pattern. The last term after doing ```30``` operations is ```1138```

Make the function ```sum_pow_dig_seq()```, that receives the arguments in the order shown below with the corresponding output:
```python
sum_pow_dig_seq(start, n, k) ---> [h, cyc_patt_arr, patt_len, last_term]
```

For our given examples, 
```python
sum_pow_dig_seq(420, 3, 5) == [3, [153], 1, 153]

sum_pow_dig_seq(420, 4, 30) == [12, [13139, 6725, 4338, 4514, 1138, 4179, 9219], 7, 1138]
```

Constraints for tests:
```
500 ≤ start ≤ 8000
2 ≤ n ≤ 9
100 * n ≤ k ≤ 200 * n
```
Do your best!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded