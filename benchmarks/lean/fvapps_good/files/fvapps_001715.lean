-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_all_points (n : Nat) : List (Nat × Nat) := sorry

instance : LE (Nat × Nat) where
  le := λ a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)
-- </vc-definitions>

-- <vc-theorems>
theorem no_duplicates {n : Nat} (h : n > 0) :
  let points := find_all_points n
  List.Nodup points := sorry

theorem grid_size_one :
  find_all_points 1 = [(0,0)] := sorry

theorem grid_size_two :
  find_all_points 2 = [(0,0), (0,1), (1,0), (1,1)] := sorry
-- </vc-theorems>