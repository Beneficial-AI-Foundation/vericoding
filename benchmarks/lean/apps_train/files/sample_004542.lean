# Task
Follow the instructions in each failing test case to write logic that calculates the total price when ringing items up at a cash register.

# Purpose
Practice writing maintainable and extendable code. 

# Intent
This kata is meant to emulate the real world where requirements change over time. This kata does not provide a specification for the final end-state up front. Instead, it walks you through a series of requirements, modifying and extending them via test cases as you go. This kata is about the journey, not the destination. Your ability to write maintainable and extendable code will affect how difficult this kata is. 

# Provided Utility Function
You may use the following preloaded function:
```python
get_price(item)
"""Accepts a str specifying an item. Returns the price of
the item (float) or raises a KeyError if no price is available.

Example: 

    >>> get_price(apple)
    0.4
"""
```

# Acknowledgement
Inspired by http://codekata.com/kata/kata01-supermarket-pricing/. To get the most benefit from this kata, I would recommend visiting that page only after completing, not before.

def get_price : Item → Float 
| Item.apple => 0.5
| Item.banana => 0.5  
| Item.orange => 0.7

def ring_up (items : List (Item × Nat)) (promos : List String := []) : Float :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded