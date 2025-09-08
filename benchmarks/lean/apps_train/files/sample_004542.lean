/-
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
-/

def get_price : Item → Float 
| Item.apple => 0.5
| Item.banana => 0.5  
| Item.orange => 0.7

def ring_up (items : List (Item × Nat)) (promos : List String := []) : Float :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def list_sum (l : List Float) : Float :=
  match l with
  | [] => 0
  | h :: t => h + list_sum t

theorem ring_up_nonnegative (items : List (Item × Nat)) (promos : List String) :
  ring_up items promos ≥ 0 :=
sorry

theorem ring_up_equals_sum_when_no_promos (items : List (Item × Nat)) :
  ring_up items [] = list_sum (items.map (fun (i,q) => get_price i * q.toFloat)) :=
sorry

theorem ring_up_empty_is_zero :
  ring_up [] [] = 0 :=
sorry

theorem ring_up_zero_quantities (items : List (Item × Nat)) (h: ∀ p ∈ items, p.2 = 0) :
  ring_up items [] = 0 :=
sorry

theorem ring_up_three_for_one_apple :
  ring_up [(Item.apple, 3)] ["3 for 1.00"] = 1.00 :=
sorry

theorem ring_up_bogo_banana :
  ring_up [(Item.banana, 2)] ["buy 1 get 1"] = 0.50 :=
sorry

/-
info: 0.8
-/
-- #guard_msgs in
-- #eval ring_up {"apple": 2}

/-
info: 1.0
-/
-- #guard_msgs in
-- #eval ring_up {"apple": 3} {"apple": "3 for 1.00"}

/-
info: 0.5
-/
-- #guard_msgs in
-- #eval ring_up {"banana": 2} {"banana": "buy 1 get 1"}

-- Apps difficulty: introductory
-- Assurance level: unguarded