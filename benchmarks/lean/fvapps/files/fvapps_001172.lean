-- <vc-preamble>
def countChar (s : String) (c : Char) : Nat :=
  s.toList.filter (· == c) |>.length

def stringReverse (s : String) : String :=
  String.mk (s.toList.reverse)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def track_rakesh (m n rx ry : Nat) (moves : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem track_rakesh_result_type (m n rx ry : Nat) (moves : String) :
  track_rakesh m n rx ry moves = "DANGER" ∨
  track_rakesh m n rx ry moves = "REACHED" ∨
  track_rakesh m n rx ry moves = "SOMEWHERE" :=
sorry

theorem track_rakesh_danger_condition (m n rx ry : Nat) (moves : String) :
  let net_x := countChar moves 'R' - countChar moves 'L'
  let net_y := countChar moves 'U' - countChar moves 'D'
  (net_x < 0 ∨ net_x > m ∨ net_y < 0 ∨ net_y > n) →
  track_rakesh m n rx ry moves = "DANGER" :=
sorry

theorem track_rakesh_reached_condition (m n rx ry : Nat) (moves : String) :
  let net_x := countChar moves 'R' - countChar moves 'L'
  let net_y := countChar moves 'U' - countChar moves 'D'
  (net_x = rx ∧ net_y = ry) →
  track_rakesh m n rx ry moves = "REACHED" :=
sorry

theorem track_rakesh_somewhere_condition (m n rx ry : Nat) (moves : String) :
  let net_x := countChar moves 'R' - countChar moves 'L'
  let net_y := countChar moves 'U' - countChar moves 'D'
  (¬(net_x < 0 ∨ net_x > m ∨ net_y < 0 ∨ net_y > n)) →
  (¬(net_x = rx ∧ net_y = ry)) →
  track_rakesh m n rx ry moves = "SOMEWHERE" :=
sorry

theorem track_rakesh_no_movement (m n : Nat) :
  track_rakesh m n 0 0 "" = "REACHED" ∧
  track_rakesh m n 1 1 "" = "SOMEWHERE" :=
sorry

theorem track_rakesh_inverse_movement (m n : Nat) (moves : String) :
  moves ≠ "" →
  track_rakesh m n 0 0 (moves ++ stringReverse moves) = "REACHED" :=
sorry
-- </vc-theorems>