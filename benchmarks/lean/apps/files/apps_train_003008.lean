/-
Introduction

It's been more than 20 minutes since the negligent waiter has taken your order for the house special prime tofu steak with a side of chili fries.

Out of boredom, you start fiddling around with the condiments tray. To be efficient, you want to be familiar with the choice of sauces and spices before your order is finally served.

You also examine the toothpick holder and try to analyze its inner workings when - yikes - the holder's lid falls off and all 23 picks lay scattered on the table.

Being a good and hygiene oriented citizen, you decide not to just put them back in the holder. Instead of letting all the good wood go to waste, you start playing around with the picks.

In the first "round", you lay down one toothpick vertically. You've used a total of one toothpick.

In the second "round", at each end of the first toothpick, you add a perpendicular toothpick at its center point. You added two additional toothpicks for a total of three toothpicks.

In the next rounds, you continue to add perpendicular toothpicks to each free end of toothpicks already on the table.

With your 23 toothpicks, you can complete a total of six rounds:

You wonder if you'd be able to implement this sequence in your favorite programming language. Because your food still hasn't arrived, you decide to take out your laptop and start implementing...

Challenge
Implement a script that returns the amount of toothpicks needed to complete n amount of rounds of the toothpick sequence.

```
0 <= n <= 5000
```

Hint
You can attempt this brute force or get some inspiration from the math department.
-/

-- <vc-helpers>
-- </vc-helpers>

def toothpick (n : Nat) : Nat :=
  sorry

theorem toothpick_non_negative (n : Nat) :
  toothpick n ≥ 0 :=
  sorry

theorem toothpick_monotonic {n : Nat} (h : n > 0) : 
  toothpick n > toothpick (n-1) :=
  sorry

theorem toothpick_doubles {n : Nat} (h : n > 0) :
  toothpick (2^n) > 2 * toothpick (2^(n-1)) :=
  sorry

theorem toothpick_zero :
  toothpick 0 = 0 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval toothpick 0

/-
info: 7
-/
-- #guard_msgs in
-- #eval toothpick 3

/-
info: 171
-/
-- #guard_msgs in
-- #eval toothpick 16

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible