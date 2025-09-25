-- <vc-preamble>
def PlayerMovement.PREC : List Nat := [2, 4, 6, 8]

def PlayerMovement.new (x y : Int) : PlayerMovement := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def PlayerMovement.update (pm : PlayerMovement) : PlayerMovement := sorry

def Input.set_states (states : List (Nat × Bool)) : Unit := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem player_movement_initialization (x y : Int) :
  let pm := PlayerMovement.new x y
  pm.position.x = x ∧
  pm.position.y = y ∧
  pm.direction = 8 ∧
  pm.pressed = [false, false, false, false] ∧
  pm.stack = [] := sorry

theorem movement_preserves_invariants (states : List (Nat × Bool)) :
  let pm := PlayerMovement.new 0 0
  let _ := Input.set_states states
  let pm' := pm.update
  List.length pm'.pressed = 4 ∧
  (∀ x ∈ pm'.pressed, x = true ∨ x = false) ∧
  (pm'.direction = 2 ∨ pm'.direction = 4 ∨ pm'.direction = 6 ∨ pm'.direction = 8) ∧
  (∀ x ∈ pm'.stack, x = 2 ∨ x = 4 ∨ x = 6 ∨ x = 8) ∧
  List.Nodup pm'.stack := sorry

theorem precedence (pressed_keys : List (Nat × Bool)) 
  (h1 : ∀ k ∈ pressed_keys, k.1 ∈ PlayerMovement.PREC)
  (h2 : ∀ k ∈ pressed_keys, k.2 = true)
  (h3 : pressed_keys.length > 0) :
  let pm := PlayerMovement.new 0 0
  let _ := Input.set_states pressed_keys
  let pm' := pm.update
  pm'.direction ∈ PlayerMovement.PREC ∧
  ∀ k ∈ pressed_keys, 
    ∃ i j : Nat, 
      PlayerMovement.PREC.get? i = some pm'.direction ∧
      PlayerMovement.PREC.get? j = some k.1 ∧
      i ≤ j := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval len player.stack

/-
info: 4
-/
-- #guard_msgs in
-- #eval len player.stack

/-
info: 1
-/
-- #guard_msgs in
-- #eval len player.stack
-- </vc-theorems>