-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_guest_assignment (n: Nat) (moves: List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_guest_assignment_cyclic_shifts {n: Nat} {moves: List Int}
  (h: moves.length = n) (h_pos: 0 < n) :
  check_guest_assignment n moves = check_guest_assignment n (moves.rotateLeft 1) :=
sorry

theorem check_guest_assignment_mod_n {n: Nat} {moves: List Int} {i: Nat}
  (h: moves.length = n) (h_pos: 0 < n) (h_idx: i < moves.length) :
  check_guest_assignment n moves = 
  check_guest_assignment n (moves.set i (moves[i]! + n)) :=
sorry

theorem check_guest_assignment_unique_positions {n: Nat} {moves: List Int}
  (h: moves.length = n) (h_pos: 0 < n)
  (h_valid: check_guest_assignment n moves = true) :
  ∀ i j, i < n → j < n → i ≠ j →
    (moves[i]! + i) % n ≠ (moves[j]! + j) % n :=
sorry
-- </vc-theorems>