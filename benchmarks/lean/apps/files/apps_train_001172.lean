def track_rakesh (m n rx ry : Nat) (moves : String) : String := sorry

def countChar (s : String) (c : Char) : Nat := 
  s.toList.filter (· == c) |>.length

-- <vc-helpers>
-- </vc-helpers>

def stringReverse (s : String) : String :=
  String.mk (s.toList.reverse)

theorem track_rakesh_result_type (m n rx ry : Nat) (moves : String) :
  track_rakesh m n rx ry moves = "DANGER" ∨ 
  track_rakesh m n rx ry moves = "REACHED" ∨
  track_rakesh m n rx ry moves = "SOMEWHERE" := sorry

theorem track_rakesh_danger_condition (m n rx ry : Nat) (moves : String) :
  let net_x := countChar moves 'R' - countChar moves 'L'
  let net_y := countChar moves 'U' - countChar moves 'D'
  (net_x < 0 ∨ net_x > m ∨ net_y < 0 ∨ net_y > n) →
  track_rakesh m n rx ry moves = "DANGER" := sorry

theorem track_rakesh_reached_condition (m n rx ry : Nat) (moves : String) :
  let net_x := countChar moves 'R' - countChar moves 'L'
  let net_y := countChar moves 'U' - countChar moves 'D'
  (net_x = rx ∧ net_y = ry) →
  track_rakesh m n rx ry moves = "REACHED" := sorry

theorem track_rakesh_somewhere_condition (m n rx ry : Nat) (moves : String) :
  let net_x := countChar moves 'R' - countChar moves 'L'
  let net_y := countChar moves 'U' - countChar moves 'D'
  (¬(net_x < 0 ∨ net_x > m ∨ net_y < 0 ∨ net_y > n)) →
  (¬(net_x = rx ∧ net_y = ry)) →
  track_rakesh m n rx ry moves = "SOMEWHERE" := sorry

theorem track_rakesh_no_movement (m n : Nat) :
  track_rakesh m n 0 0 "" = "REACHED" ∧
  track_rakesh m n 1 1 "" = "SOMEWHERE" := sorry

theorem track_rakesh_inverse_movement (m n : Nat) (moves : String) :
  moves ≠ "" →
  track_rakesh m n 0 0 (moves ++ stringReverse moves) = "REACHED" := sorry

/-
info: 'REACHED'
-/
-- #guard_msgs in
-- #eval track_rakesh 20 20 4 5 "LLUUUUURRRRRR"

/-
info: 'DANGER'
-/
-- #guard_msgs in
-- #eval track_rakesh 10 10 3 4 "UDUDDRR"

/-
info: 'SOMEWHERE'
-/
-- #guard_msgs in
-- #eval track_rakesh 5 5 2 2 "RRU"

-- Apps difficulty: interview
-- Assurance level: unguarded