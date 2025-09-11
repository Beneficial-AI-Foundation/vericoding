-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binary_simulation (s : String) (ops : List (List Nat)) : List Char := sorry

def simple_simulate (s : String) (ops : List (List Nat)) : List Char := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binary_simulation_matches_reference (s : String) (ops : List (List Nat)) :
  binary_simulation s ops = simple_simulate s ops := sorry

theorem queries_only_match_original (s : String) (queries : List (List Nat)) 
  (h : ∀ q ∈ queries, q.head! = 2 → q.length = 2) :
  binary_simulation s queries = simple_simulate s queries := sorry

theorem double_inversion_cancels (s : String) :
  let i := 1
  let j := s.length 
  let ops := [[0, i, j], [0, i, j], [1, 1]]
  binary_simulation s ops = [s.get 0] := sorry

/-
info: ['0', '1', '1', '0']
-/
-- #guard_msgs in
-- #eval binary_simulation "0011001100" [["I", 1, 10], ["I", 2, 7], ["Q", 2], ["Q", 1], ["Q", 7], ["Q", 5]]

/-
info: ['0', '0', '0', '1']
-/
-- #guard_msgs in
-- #eval binary_simulation "1011110111" [["I", 1, 10], ["I", 2, 7], ["Q", 2], ["Q", 1], ["Q", 7], ["Q", 5]]

/-
info: ['1']
-/
-- #guard_msgs in
-- #eval binary_simulation "0000000000" [["I", 1, 10], ["Q", 2]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded