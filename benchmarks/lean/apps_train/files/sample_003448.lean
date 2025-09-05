Every  positive integer number, that is not prime, may be decomposed in prime factors. For example the prime factors of 20, are:
```
2, 2, and 5, because: 20 = 2 . 2 . 5
```
The first prime factor (the smallest one) of ```20``` is ```2``` and the last one (the largest one) is ```5```. The sum of the first and the last prime factors, ```sflpf``` of 20 is: ```sflpf = 2 + 5 = 7```

The number ```998 ```is the only integer in the range ```[4, 1000]``` that has a value of ```501``` , so its ```sflpf``` equals to 501, but in the range ```[4, 5000]``` we will have more integers with ```sflpf = 501``` and are: ```998, 1996, 2994, 3992, 4990```.

We need a function ```sflpf_data()``` (javascript: ```sflpfData()```that receives two arguments, ```val``` as the value of sflpf and ```nMax``` as a limit, and the function will output a sorted list of the numbers between ```4``` to ```nMax```(included) that have the same value of sflpf equals to ```val```.

Let's see some cases:
```python
sflpf_data(10, 100) == [21, 25, 63]
/// the prime factorization of these numbers are:
Number  Prime Factorization     Sum First and Last Prime Factor
21       = 3 . 7      ---->                 3 + 7 = 10
25       = 5 . 5      ---->                 5 + 5 = 10
63       = 3 . 3 . 7  ---->                 3 + 7 = 10
```
```python
sflpf_data(10, 200) == [21, 25, 63, 105, 125, 147, 189]
sflpf_data(15, 150) == [26, 52, 78, 104, 130]
```
(Advice:Try to discard primes in a fast way to have a more agile code)

Enjoy it!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
