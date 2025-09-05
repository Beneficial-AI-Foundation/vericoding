Just like in the ["father" kata](http://www.codewars.com/kata/find-fibonacci-last-digit/), you will have to return the last digit of the nth element in the Fibonacci sequence (starting with 1,1, to be extra clear, not with 0,1 or other numbers).

You will just get much bigger numbers, so good luck bruteforcing your way through it ;)
```python
last_fib_digit(1) == 1
last_fib_digit(2) == 1
last_fib_digit(3) == 2
last_fib_digit(1000) == 5
last_fib_digit(1000000) == 5
```
``` haskell
lastFibDigit       1 == 1
lastFibDigit       2 == 1
lastFibDigit       3 == 2
lastFibDigit    1000 == 5
lastFibDigit 1000000 == 5
```

def fibNaive (n : Nat) : Nat := 
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let rec fib_iter (i : Nat) (a b : Nat) : Nat :=
      match i with
      | 0 => b
      | i + 1 => fib_iter i b (a + b)
    fib_iter (n) 0 1

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded