/-
# Situation
You have been hired by a company making electric garage doors. Accidents with the present product line have resulted in numerous damaged cars, broken limbs and several killed pets. Your mission is to write a safer version of their controller software.

# Specification
We always start with a closed door. The remote control has exactly one button, with the following behaviour.

+ If the door is closed, a push starts opening the door, and vice-versa
+ It takes 5 seconds for the door to open or close completely
+ While the door is moving, one push pauses movement, another push resumes movement in the same direction

In order to make the door safer, it has been equiped with resistance-based obstacle detection. When the door detects an obstacle, it must immediately reverse the direction of movement.

# Input
A string where each character represents one second, with the following possible values.

* ```'.'``` No event
* ```'P'``` Button has been pressed
* ```'O'``` Obstacle has been detected (supersedes P)

As an example, ```'..P....'``` means that nothing happens for two seconds, then the button is pressed, then no further events.

# Output
A string where each character represents one second and indicates the position of the door (0 if fully closed and 5 fully open). The door starts moving immediately, hence its position changes at the same second as the event.

# Example
```..P...O.....``` as input should yield
```001234321000``` as output
-/

-- <vc-helpers>
-- </vc-helpers>

def controller (s : String) : String := sorry

theorem controller_output_length (s : String) :
  (controller s).length = s.length := sorry

theorem controller_output_digits (s : String) :
  ∀ c ∈ (controller s).data, c = '0' ∨ c = '1' ∨ c = '2' ∨ c = '3' ∨ c = '4' ∨ c = '5' := sorry

theorem controller_sequential_moves (s : String) :
  ∀ i, i > 0 → i < (controller s).length → 
    let nums := (controller s).data.map (fun c => c.toNat - '0'.toNat);
    nums[i]! ≤ nums[i-1]! + 1 ∧ nums[i-1]! ≤ nums[i]! + 1 := sorry

theorem controller_boundaries (s : String) :
  ∀ c ∈ (controller s).data, 
    '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '5'.toNat := sorry

theorem controller_stops_at_limits (s : String) :
  ∀ i, i > 0 → i < (controller s).length - 1 →
    let nums := (controller s).data.map (fun c => c.toNat - '0'.toNat);
    (nums[i]! = 0 ∧ nums[i+1]! ≠ nums[i]! → nums[i+1]! > nums[i]!) ∧
    (nums[i]! = 5 ∧ nums[i+1]! ≠ nums[i]! → nums[i+1]! < nums[i]!) := sorry

/-
info: '12345'
-/
-- #guard_msgs in
-- #eval controller "P...."

/-
info: '1222234555'
-/
-- #guard_msgs in
-- #eval controller "P.P..P...."

/-
info: '001234321000'
-/
-- #guard_msgs in
-- #eval controller "..P...O....."

-- Apps difficulty: introductory
-- Assurance level: unguarded