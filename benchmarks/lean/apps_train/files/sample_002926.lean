Given a certain integer ```n```, we need a function ```big_primefac_div()```, that give an array with the highest prime factor and the highest divisor (not equal to n).

Let's see some cases:
```python
big_primefac_div(100) == [5, 50]
big_primefac_div(1969) == [179, 179]
```
If n is a prime number the function will output an empty list:
```python
big_primefac_div(997) == []
```
If ```n``` is an negative integer number, it should be considered the division with tha absolute number of the value.
```python
big_primefac_div(-1800) == [5, 900]
```
If ```n``` is a float type, will be rejected if it has a decimal part with some digits different than 0. The output "The number has a decimal part. No Results". But  ```n ``` will be converted automatically to an integer if all the digits of the decimal part are 0.

```python
big_primefac_div(-1800.00) == [5, 900]
big_primefac_div(-1800.1) == "The number has a decimal part. No Results"
```
Optimization and fast algorithms are a key factor to solve this kata.
Happy coding and enjoy it!

def isPrime (n : Nat) : Bool := sorry

def sqrt (n : Int) : Int := sorry

def big_primefac_div (n : Int) : Option (Int × Int) := sorry

def abs (n : Int) : Int := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded