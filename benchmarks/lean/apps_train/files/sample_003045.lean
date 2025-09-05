# Let's play Psychic 

A box contains green, red, and blue balls. The total number of balls is given by `n` (`0 < n < 50`).

Each ball has a mass that depends on the ball color. Green balls weigh `5kg`, red balls weigh `4kg`, and blue balls weigh `3kg`.

Given the total number of balls in the box, `n`, and a total mass, `m`, your task is to craft a program that will determine the quantities of each colored ball. Return a list of these quantities as the answer.

Don't forget that some combinations of `n` and `m` may have more than one possibility!

# Examples

## Python
```python
>>> Guess_it(3, 12)
[[0,3,0], [1,1,1]]
```

## Elixir

*Note: Order of the returned elements is unimportant in the Elixir version.*

# Assumptions

1. You can assume that all inputs are of the correct type
2. You can assume that the range of `n` will be `[1, 50]`
3. Each element of the returned list should return the quantities in the order of `g`, `r`, `b`. 

## Python
```python
[[green, red, blue]]
```

## Elixir

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible