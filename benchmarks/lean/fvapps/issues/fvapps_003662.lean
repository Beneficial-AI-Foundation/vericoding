-- <vc-preamble>
def lose_weight (gender : Gender) (weight : Float) (duration : Nat) : String ⊕ Float := sorry

theorem weight_always_decreases
  (gender : Gender) (weight : Float) (duration : Nat)
  (h1 : weight > 0)
  (h2 : duration > 0) :
  match lose_weight gender weight duration with
  | Sum.inr result => result ≤ weight
  | Sum.inl _ => True
  := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lose_weight_string (gender : String) (weight : Float) (duration : Nat) : String := sorry

theorem invalid_gender
  (gender : String) (weight : Float) (duration : Nat)
  (h : gender ≠ "M" ∧ gender ≠ "F")
  (h1 : weight > 0)
  (h2 : duration > 0) :
  lose_weight_string gender weight duration = "Invalid gender" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem weight_loss_proportional_to_duration
  (gender : Gender) (weight : Float) (duration : Nat)
  (h1 : weight > 0)
  (h2 : duration > 0) :
  match lose_weight gender weight duration, lose_weight gender weight (2 * duration) with
  | Sum.inr result1, Sum.inr result2 => result2 ≤ result1
  | _, _ => True
  := sorry

theorem invalid_weight
  (gender : Gender) (weight : Float) (duration : Nat)
  (h : weight ≤ 0)
  (h2 : duration > 0) :
  match lose_weight gender weight duration with
  | Sum.inl s => s = "Invalid weight"
  | _ => False
  := sorry

theorem invalid_duration
  (gender : Gender) (weight : Float) (duration : Nat)
  (h : duration = 0)
  (h1 : weight > 0) :
  match lose_weight gender weight duration with
  | Sum.inl s => s = "Invalid duration"
  | _ => False
  := sorry

end LoseWeight

/-
info: 231.8
-/
-- #guard_msgs in
-- #eval lose_weight "M" 250 5

/-
info: 172.5
-/
-- #guard_msgs in
-- #eval lose_weight "F" 190 8

/-
info: 'Invalid gender'
-/
-- #guard_msgs in
-- #eval lose_weight "X" 200 10

/-
info: 'Invalid weight'
-/
-- #guard_msgs in
-- #eval lose_weight "M" -5 10

/-
info: 'Invalid duration'
-/
-- #guard_msgs in
-- #eval lose_weight "F" 160 0
-- </vc-theorems>