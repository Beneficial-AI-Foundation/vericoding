/-
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
-/

-- <vc-helpers>
-- </vc-helpers>

def sum_pow_dig_seq (num exp k : Nat) : Nat × List Nat × Nat × Nat :=
  sorry

theorem sum_pow_dig_seq_result_structure 
  (num exp k : Nat)
  (h1 : num > 0)
  (h2 : num ≤ 100000)
  (h3 : exp > 0)
  (h4 : exp ≤ 5)
  (h5 : k > 0)
  (h6 : k ≤ 100) :
  let result := sum_pow_dig_seq num exp k
  result.1 ≥ 0 ∧ 
  result.2.2.1 = result.2.1.length ∧
  (result.2.1 ≠ [] → 
    (List.elem result.2.2.2 result.2.1 ∧
     result.1 + result.2.2.1 ≤ k ∧
     ∀ (x y : Nat), List.elem x result.2.1 → List.elem y result.2.1 → x = y → x = y)) :=
  sorry

theorem sum_pow_dig_seq_consistent
  (num exp : Nat)
  (h1 : num > 0)
  (h2 : num ≤ 1000)
  (h3 : exp > 0)
  (h4 : exp ≤ 3) :
  let r1 := sum_pow_dig_seq num exp 100
  let r2 := sum_pow_dig_seq num exp 200
  r1.2.1 ≠ [] →
    (r1.2.1 = r2.2.1 ∧
     r1.1 = r2.1 ∧
     r1.2.2.1 = r2.2.2.1) :=
  sorry

theorem sum_pow_dig_seq_power_one
  (num : Nat)
  (h1 : num > 0)
  (h2 : num ≤ 1000) :
  let result := sum_pow_dig_seq num 1 20
  result.2.1 ≠ [] →
    ∀ x, List.elem x result.2.1 → x < 10 :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded