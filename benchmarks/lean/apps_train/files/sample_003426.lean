A country has coins with denominations
```python
coins_list = d1 < d2 < · · · < dn.
```
You want to make change for n cents, using the smallest number of coins.

```python
# Example 1: U.S. coins
d1 = 1 d2 = 5 d3 = 10 d4 = 25

## Optimal change for 37 cents – 1 quarter, 1 dime, 2 pennies.

# Example 2: Alien Planet Z coins
Z_coin_a = 1 Z_coin_b = 3 Z_coin_c = 4

## Optimal change for 6 cents - 2 Z_coin_b's
```

Write a function that will take a list of coin denominations and a desired amount and provide the least amount of coins needed.

def looseChange (coins: List Nat) (amount: Nat) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded