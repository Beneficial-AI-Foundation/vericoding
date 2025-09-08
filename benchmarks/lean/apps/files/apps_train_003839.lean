/-
# Explanation

It's your first day in the robot factory and your supervisor thinks that you should start with an easy task. So you are responsible for purchasing raw materials needed to produce the robots.

A complete robot weights `50` kilogram. Iron is the only material needed to create a robot. All iron is inserted in the first machine; the output of this machine is the input for the next one, and so on. The whole process is sequential. Unfortunately not all machines are first class, so a given percentage of their inputs are destroyed during processing.

# Task

You need to figure out how many kilograms of iron you need to buy to build the requested number of robots.

# Example

Three machines are used to create a robot. Each of them produces `10%` scrap. Your target is to deliver `90` robots.  
The method will be called with the following parameters:

```
CalculateScrap(scrapOfTheUsedMachines, numberOfRobotsToProduce)
CalculateScrap(int[] { 10, 10, 10 }, 90)
```

# Assumptions

* The scrap is less than `100%`.
* The scrap is never negative.
* There is at least one machine in the manufacturing line.
* Except for scrap there is no material lost during manufacturing.
* The number of produced robots is always a positive number.
* You can only buy full kilograms of iron.
-/

-- <vc-helpers>
-- </vc-helpers>

def calculate_scrap (rates: List Float) (n: Nat) : Nat :=
  sorry

theorem scrap_result_is_at_least_base (rates: List Float) (n: Nat) : calculate_scrap rates n ≥ n * 50 := 
  sorry

theorem scrap_monotonic_with_rates (rates: List Float) (n: Nat) (i: Nat) (hi: i < rates.length) :
  calculate_scrap (rates.take i) n ≤ calculate_scrap rates n :=
  sorry

theorem zero_scrap_is_base (rates: List Float) (n: Nat) (h: ∀ r ∈ rates, r = 0) :
  calculate_scrap rates n = n * 50 :=
  sorry

theorem empty_rates_is_base (n: Nat) :
  calculate_scrap [] n = n * 50 :=
  sorry

/-
info: 5000
-/
-- #guard_msgs in
-- #eval calculate_scrap [10] 90

/-
info: 3820
-/
-- #guard_msgs in
-- #eval calculate_scrap [20, 10] 55

/-
info: 4500
-/
-- #guard_msgs in
-- #eval calculate_scrap [0, 0, 0] 90

-- Apps difficulty: introductory
-- Assurance level: guarded