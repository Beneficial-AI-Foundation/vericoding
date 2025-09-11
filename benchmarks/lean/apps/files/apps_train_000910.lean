-- <vc-preamble>
def Array2D (α : Type) := Array (Array α)

def Grid := Array2D Int

def isValidGrid (g : Grid) : Bool :=
  let n := g.size
  n > 0 ∧
  (g.all (fun row => row.size = n)) ∧
  true -- skipping int check since Lean types handle this
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minTransposeOps (g : Grid) : Nat := sorry

theorem already_sorted_needs_zero_ops (n : Nat) (h : n > 0):
  let grid := sorry -- construction of sorted grid
  minTransposeOps grid = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem transposed_sorted_needs_at_most_n_ops (n : Nat) (h : n > 1):  
  let grid := sorry -- construction of transposed sorted grid
  minTransposeOps grid ≤ n := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_transpose_ops #[[1, 2, 9, 13], [5, 6, 10, 14], [3, 7, 11, 15], [4, 8, 12, 16]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_transpose_ops #[[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12], [13, 14, 15, 16]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_transpose_ops #[[1, 5, 9, 13], [2, 6, 10, 14], [3, 7, 11, 15], [4, 8, 12, 16]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded