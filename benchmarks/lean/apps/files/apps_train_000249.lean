-- <vc-preamble>
def sum (l : List Nat) : Nat := sorry
def listMax (l : List Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findMinMoves (machines : List Nat) : Int := sorry 

theorem find_min_moves_non_negative 
  {machines : List Nat}
  (h : findMinMoves machines ≠ -1) :
  findMinMoves machines ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_moves_preserves_sum
  {machines : List Nat}
  (h : findMinMoves machines ≠ -1) :
  sum machines = machines.length * (sum machines / machines.length) := sorry

theorem find_min_moves_lower_bound
  {machines : List Nat}
  (h : findMinMoves machines ≠ -1) :
  findMinMoves machines ≥ 
    max (listMax machines - sum machines / machines.length) 0 := sorry

theorem find_min_moves_negative_one
  {machines : List Nat}
  (h : findMinMoves machines = -1) :
  sum machines % machines.length ≠ 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_min_moves [1, 0, 5]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_moves [0, 3, 0]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_min_moves [0, 2, 0]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded