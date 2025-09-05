You will receive an uncertain amount of integers in a certain order ```k1, k2, ..., kn```.

You form a new number of n digits in the following way:
you take one of the possible digits of the first given number, ```k1```, then the same with the given number ```k2```, repeating the same process up to ```kn``` and you concatenate these obtained digits(in the order that were taken) obtaining the new number. As you can see, we have many possibilities.

Let's see the process above explained with three given numbers:
```
k1 = 23, k2 = 17, k3 = 89
Digits Combinations   Obtained Number
  ('2', '1', '8')           218    <---- Minimum
  ('2', '1', '9')           219
  ('2', '7', '8')           278
  ('2', '7', '9')           279
  ('3', '1', '8')           318
  ('3', '1', '9')           319
  ('3', '7', '8')           378
  ('3', '7', '9')           379    <---- Maximum
             Total Sum =   2388   (8 different values)
```
We need the function that may work in this way:

```python
proc_seq(23, 17, 89) == [8, 218, 379, 2388]
```

See this special case and deduce how the function should handle the cases which have many repetitions.

```python
proc_seq(22, 22, 22, 22) == [1, 2222] # we have only one obtained number, the minimum, maximum and total sum coincide
```

The sequence of numbers will have numbers of n digits only. Numbers formed by leading zeroes will be discarded.

```python
proc_seq(230, 15, 8) == [4, 218, 358, 1152]
```

Enjoy it!!

You will never receive the number 0 and all the numbers will be in valid format.

def proc_seq : List Nat → List Nat 
  | xs => sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded