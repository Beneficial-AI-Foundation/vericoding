-- <vc-helpers>
-- </vc-helpers>

def solve_necklace (n : Nat) (beads : List Nat) : Nat × String := sorry

theorem single_bead_type_cuts {count : Nat} (h : count > 0) :
  let n := 1
  let beads := [count]
  (solve_necklace n beads).1 = count := sorry

theorem single_bead_type_necklace {count : Nat} (h : count > 0) :
  let n := 1
  let beads := [count]
  (solve_necklace n beads).2 = String.mk (List.replicate count 'a') := sorry

/-
info: sum(beads1)
-/
-- #guard_msgs in
-- #eval len necklace1

/-
info: 2
-/
-- #guard_msgs in
-- #eval len necklace3

-- Apps difficulty: competition
-- Assurance level: unguarded