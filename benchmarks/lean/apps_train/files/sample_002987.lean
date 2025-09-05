# Task
John is an orchard worker. 

There are `n` piles of fruits waiting to be transported. Each pile of fruit has a corresponding weight. John's job is to combine the fruits into a pile and wait for the truck to take them away.

Every time, John can combine any two piles(`may be adjacent piles, or not`), and the energy he costs is equal to the weight of the two piles of fruit.

For example, if there are two piles, pile1's weight is `1` and pile2's weight is `2`. After merging, the new pile's weight is `3`, and he consumed 3 units of energy.

John wants to combine all the fruits into 1 pile with the least energy.

Your task is to help John, calculate the minimum energy he costs.

# Input

- `fruits`: An array of positive integers. Each element represents the weight of a pile of fruit.

  Javascript:
  - 1 <= fruits.length <= 10000
  - 1 <= fruits[i] <= 10000

  Python:
  - 1 <= len(fruits) <= 5000
  - 1 <= fruits[i] <= 10000

# Output

An integer. the minimum energy John costs.

# Examples

For `fruits = [1,2,9]`, the output should be `15`.

```
3 piles:  1  2  9
combine 1 and 2 to 3, cost 3 units of energy.
2 piles:  3  9
combine 3 and 9 to 12, cost 12 units of energy.
1 pile:  12

The total units of energy is 3 + 12 = 15 units
```

For `fruits = [100]`, the output should be `0`.

There's only 1 pile. So no need combine it.

def List.minimum (l : List Nat) : Option Nat :=
  sorry

def List.maximum (l : List Nat) : Option Nat :=
  sorry

def List.sum (l : List Nat) : Nat :=
  sorry

def List.log2 (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
