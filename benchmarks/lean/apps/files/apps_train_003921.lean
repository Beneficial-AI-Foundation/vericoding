/-
You've purchased a ready-meal from the supermarket.

The packaging says that you should microwave it for 4 minutes and 20 seconds, based on a 600W microwave.

Oh no, your microwave is 800W! How long should you cook this for?!

___

# Input

You'll be given 4 arguments:

## 1. needed power
The power of the needed microwave.  
Example: `"600W"`

## 2. minutes
The number of minutes shown on the package.  
Example: `4`

## 3. seconds
The number of seconds shown on the package.  
Example: `20`

## 4. power
The power of your microwave.  
Example: `"800W"`

___

# Output
The amount of time you should cook the meal for formatted as a string.  
Example: `"3 minutes 15 seconds"`

Note: the result should be rounded up.
```
59.2 sec  -->  60 sec  -->  return "1 minute 0 seconds"
```

___

## All comments/feedback/translations appreciated.
-/

-- <vc-helpers>
-- </vc-helpers>

def cooking_time (needed_power : String) (minutes : Nat) (seconds : Nat) (power : String) : String := sorry

theorem cooking_time_format (needed_power : String) (minutes : Nat) 
  (seconds : Nat) (power : String) (h1 : minutes ≤ 60) (h2 : seconds < 60) :
  ∃ result_mins result_secs : Nat,
    cooking_time needed_power minutes seconds power = 
      s!"{result_mins} minutes {result_secs} seconds" := sorry

theorem cooking_time_time_bounds (needed_power : String) (minutes : Nat)
  (seconds : Nat) (power : String) (h1 : minutes ≤ 60) (h2 : seconds < 60) :
  let result := cooking_time needed_power minutes seconds power
  ∃ result_mins result_secs : Nat,
    result = s!"{result_mins} minutes {result_secs} seconds" ∧
    result_secs < 60 ∧ 
    result_mins ≥ 0 := sorry

theorem cooking_time_power_conservation (needed_power : String) (minutes : Nat)
  (seconds : Nat) (power : String) (h1 : minutes ≤ 60) (h2 : seconds < 60) :
  let result := cooking_time needed_power minutes seconds power
  ∃ result_mins result_secs input_watts output_watts : Nat,
    result = s!"{result_mins} minutes {result_secs} seconds" ∧
    input_watts * (minutes * 60 + seconds) ≤ 
    output_watts * (result_mins * 60 + result_secs) + output_watts := sorry

theorem cooking_time_zero :
  cooking_time "100W" 0 0 "100W" = "0 minutes 0 seconds" := sorry

theorem cooking_time_same_power :
  cooking_time "800W" 5 30 "800W" = "5 minutes 30 seconds" := sorry

/-
info: '3 minutes 15 seconds'
-/
-- #guard_msgs in
-- #eval cooking_time "600W" 4 20 "800W"

/-
info: '2 minutes 0 seconds'
-/
-- #guard_msgs in
-- #eval cooking_time "800W" 3 0 "1200W"

/-
info: '17 minutes 30 seconds'
-/
-- #guard_msgs in
-- #eval cooking_time "100W" 8 45 "50W"

-- Apps difficulty: introductory
-- Assurance level: unguarded