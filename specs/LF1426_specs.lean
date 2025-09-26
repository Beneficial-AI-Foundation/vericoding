-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_periodic_sequence (n: Nat) (sequence: List Int) : String := sorry

def List.sum (l: List Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_zero (sequence: List Int) :
  solve_periodic_sequence 0 sequence = "0" := sorry

theorem cycle_repetition {n: Nat} {sequence: List Int} 
  (h: sequence.length > 0) :
  let cycled := List.join (List.replicate (n / sequence.length + 1) sequence)
  String.toInt! (solve_periodic_sequence n sequence) = 
    (List.take n cycled).sum := sorry

theorem cycle_consistency {n: Nat} {sequence: List Int}
  (h1: sequence.length > 0)
  (h2: n ≥ sequence.length) :
  String.toInt! (solve_periodic_sequence (n + sequence.length) sequence) - 
  String.toInt! (solve_periodic_sequence n sequence) = 
  sequence.sum := sorry

/-
info: '0'
-/
-- #guard_msgs in
-- #eval solve_periodic_sequence 0 [1, 2, 3]

/-
info: '1'
-/
-- #guard_msgs in
-- #eval solve_periodic_sequence 1 [1, 2, 3]

/-
info: '3'
-/
-- #guard_msgs in
-- #eval solve_periodic_sequence 2 [1, 2, 3]

/-
info: '7'
-/
-- #guard_msgs in
-- #eval solve_periodic_sequence 4 [1, 2, 3]

/-
info: '-2'
-/
-- #guard_msgs in
-- #eval solve_periodic_sequence 3 [-1, 2, -3]

/-
info: '-4'
-/
-- #guard_msgs in
-- #eval solve_periodic_sequence 6 [-1, 2, -3]

/-
info: '4'
-/
-- #guard_msgs in
-- #eval solve_periodic_sequence 5 [1, -1, -1, 4, 1]
-- </vc-theorems>