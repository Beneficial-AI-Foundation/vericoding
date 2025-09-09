/-
This program tests the life of an
evaporator containing a gas. 

We know the content of the evaporator (content in ml),
the percentage of foam or gas lost every day (evap_per_day)
and the threshold (threshold) in percentage beyond which
the evaporator is no longer useful.
All numbers are strictly positive.

The program reports the nth day (as an integer)
on which the evaporator will be out of use.

**Note** : Content is in fact not necessary in the body of the function "evaporator", you can use it or not use it, as you wish. Some people might prefer to reason with content, some other with percentages only. It's up to you but you must keep it as a parameter because the tests have it as an argument.
-/

-- <vc-helpers>
-- </vc-helpers>

def evaporator (content : Float) (evap_rate : Float) (threshold : Float) : Int :=
  sorry

theorem evaporator_positive 
  (content evap_rate threshold : Float)
  (hc : content > 0.1 ∧ content ≤ 1000)
  (he : evap_rate > 0.1 ∧ evap_rate < 99.9)
  (ht : threshold > 0.1 ∧ threshold < 99.9) :
  evaporator content evap_rate threshold > 0 := 
  sorry

theorem evaporator_higher_rate_fewer_days
  (content evap_rate threshold : Float)
  (hc : content > 0.1 ∧ content ≤ 1000)
  (he : evap_rate > 0.1 ∧ evap_rate < 98.9)
  (ht : threshold > 0.1 ∧ threshold < 99.9) :
  evaporator content (evap_rate + 1) threshold ≤ evaporator content evap_rate threshold :=
  sorry

theorem evaporator_higher_threshold_fewer_days
  (content evap_rate threshold : Float) 
  (hc : content > 0.1 ∧ content ≤ 1000)
  (he : evap_rate > 0.1 ∧ evap_rate < 99.9)
  (ht : threshold > 0.1 ∧ threshold < 98.9) :
  evaporator content evap_rate (threshold + 1) ≤ evaporator content evap_rate threshold :=
  sorry

/-
info: 22
-/
-- #guard_msgs in
-- #eval evaporator 10 10 10

/-
info: 37
-/
-- #guard_msgs in
-- #eval evaporator 50 12 1

/-
info: 31
-/
-- #guard_msgs in
-- #eval evaporator 47.5 8 8

-- Apps difficulty: introductory
-- Assurance level: guarded