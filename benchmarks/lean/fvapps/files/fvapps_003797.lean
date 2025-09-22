-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def possible_positions (pos : String) : List String := sorry

theorem knight_move_distance
  (pos : String)
  (h_valid : pos.length = 2 ∧ pos.get ⟨0⟩ ∈ ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'] ∧ 
            pos.get ⟨1⟩ ∈ ['1', '2', '3', '4', '5', '6', '7', '8']) :
  let src_x := (Char.toNat (pos.get ⟨0⟩)) - 96
  let src_y := String.toNat! ⟨[pos.get ⟨1⟩]⟩
  ∀ move ∈ possible_positions pos,
    let dst_x := (Char.toNat (move.get ⟨0⟩)) - 96
    let dst_y := String.toNat! ⟨[move.get ⟨1⟩]⟩
    let dx := Nat.max (src_x) (dst_x) - Nat.min (src_x) (dst_x)
    let dy := Nat.max (src_y) (dst_y) - Nat.min (src_y) (dst_y)
    (dx = 1 ∧ dy = 2) ∨ (dx = 2 ∧ dy = 1) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem positions_within_board
  (pos : String)
  (h_valid : pos.length = 2 ∧ pos.get ⟨0⟩ ∈ ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'] ∧ 
            pos.get ⟨1⟩ ∈ ['1', '2', '3', '4', '5', '6', '7', '8']) :
  ∀ p ∈ possible_positions pos,
    1 ≤ ((Char.toNat (p.get ⟨0⟩)) - 96) ∧ ((Char.toNat (p.get ⟨0⟩)) - 96) ≤ 8 ∧
    1 ≤ String.toNat! ⟨[p.get ⟨1⟩]⟩ ∧ String.toNat! ⟨[p.get ⟨1⟩]⟩ ≤ 8 := sorry

theorem max_moves
  (pos : String)
  (h_valid : pos.length = 2 ∧ pos.get ⟨0⟩ ∈ ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'] ∧ 
            pos.get ⟨1⟩ ∈ ['1', '2', '3', '4', '5', '6', '7', '8']) :
  (possible_positions pos).length ≤ 8 := sorry
-- </vc-theorems>