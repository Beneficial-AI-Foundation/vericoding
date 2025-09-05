The number ```89``` is the first positive integer that has a particular, curious property:

The square of ```89``` is ```7921```; ```89² = 7921```

The reverse of ```7921``` is ```1297```, and ```1297``` is a prime number.

The cube of ```89``` is ```704969```; ```89³ = 704969```

The reverse of ```704969``` is ```969407```, and ```969407``` is a prime number.

The first four terms of this sequence having this special property are:
```
n-th term      term value
    1               89 
    2              271
    3              325
    4              328
```

Create a function ```sq_cub_rev_prime()```, that receives the ordinal number of the sequence and outputs its correspoding value.

Use the above table to show how the function should work:
```python 
sq_cub_rev_prime(1) == 89 
sq_cub_rev_prime(2) == 271
sq_cub_rev_prime(3) == 325
sq_cub_rev_prime(4) == 328
```
Your code will be tested up to the 250th term

This is not a registered sequence of OESIS, so if you are one of the first ten people that solve this kata, you may have the privilege to register the sequence at https://oeis.org, with your name. If you do so, please, mention in your biography that you are a Codewarrior.

Memoize your results to pass the tests.

Enjoy it!

def is_prime (n : Int) : Bool := sorry
def reverse_num (n : Int) : Int := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded